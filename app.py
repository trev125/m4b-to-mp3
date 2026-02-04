"""
M4B to MP3 Converter
A web application that converts M4B/M4A audiobook files into chapter-split MP3 files.
"""

VERSION = "1.0.0"

import os
import re
import json
import logging
import secrets
import shutil
import subprocess
import tempfile
import threading
import time
import uuid
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta
from functools import wraps
from queue import Queue

import requests
from flask import (
    Flask, Response, jsonify, redirect, render_template, 
    request, send_file, session, url_for
)
from werkzeug.utils import secure_filename

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 2 * 1024 * 1024 * 1024  # 2GB max
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=30)  # Remember me duration
app.secret_key = os.environ.get('SECRET_KEY', secrets.token_hex(32))

# Auth credentials - override with environment variables in production
APP_USERNAME = os.environ.get('APP_USERNAME', 'admin')
APP_PASSWORD = os.environ.get('APP_PASSWORD', 'changeme')

# Audiobookshelf integration
AUDIOBOOKSHELF_URL = os.environ.get('AUDIOBOOKSHELF_URL', '')
AUDIOBOOKSHELF_TOKEN = os.environ.get('AUDIOBOOKSHELF_TOKEN', '')

# Custom temp directory (defaults to system temp)
TEMP_DIR = os.environ.get('TEMP_DIR', '')
if TEMP_DIR and not os.path.exists(TEMP_DIR):
    os.makedirs(TEMP_DIR, exist_ok=True)

ALLOWED_EXTENSIONS = {'m4b', 'm4a'}

# Store active jobs and their progress
jobs = {}
jobs_lock = threading.Lock()

# Job queue for sequential processing
job_queue = Queue()
worker_thread = None

# Cleanup old jobs after 48 hours
JOB_EXPIRY_HOURS = 48

# Parallel conversion settings
PARALLEL_WORKERS = 4  # Number of chapters to convert simultaneously

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not session.get('logged_in'):
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

class Job:
    def __init__(self, job_id, filename):
        self.id = job_id
        self.filename = filename
        self.status = 'queued'
        self.progress = []
        self.error = None
        self.zip_path = None
        self.temp_dir = None
        self.input_path = None
        self.base_name = None
        self.created_at = datetime.now()
        self.started_at = None
        self.completed_at = None
        self.total_chapters = 0
        self.current_chapter = 0
        self.queue_position = 0
        self.metadata = {}
        self.cover_path = None
        self.cancelled = False
        self.current_process = None  # Track running ffmpeg process
        self.abs_item_id = None  # Audiobookshelf item ID for retry
        
    def log(self, message, level='info'):
        timestamp = datetime.now().strftime('%H:%M:%S')
        self.progress.append({'time': timestamp, 'message': message, 'level': level})
        log_func = getattr(logger, level, logger.info)
        log_func(f"[Job {self.id[:8]}] {message}")
    
    def to_dict(self):
        return {
            'id': self.id,
            'filename': self.filename,
            'status': self.status,
            'created_at': self.created_at.isoformat(),
            'started_at': self.started_at.isoformat() if self.started_at else None,
            'completed_at': self.completed_at.isoformat() if self.completed_at else None,
            'total_chapters': self.total_chapters,
            'current_chapter': self.current_chapter,
            'queue_position': self.queue_position,
            'error': self.error,
            'metadata': self.metadata,
            'has_cover': self.cover_path is not None and os.path.exists(self.cover_path) if self.cover_path else False,
            'abs_item_id': self.abs_item_id
        }

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

def cleanup_old_jobs():
    """Remove jobs older than JOB_EXPIRY_HOURS"""
    now = datetime.now()
    with jobs_lock:
        expired = [jid for jid, job in jobs.items() 
                   if now - job.created_at > timedelta(hours=JOB_EXPIRY_HOURS)]
        for jid in expired:
            job = jobs.pop(jid)
            if job.temp_dir and os.path.exists(job.temp_dir):
                shutil.rmtree(job.temp_dir, ignore_errors=True)
                logger.info(f"[Job {jid[:8]}] Cleaned up expired job")

def update_queue_positions():
    """Update queue position for all queued jobs"""
    with jobs_lock:
        queued_jobs = [(jid, j) for jid, j in jobs.items() if j.status == 'queued']
        queued_jobs.sort(key=lambda x: x[1].created_at)
        for pos, (jid, job) in enumerate(queued_jobs, 1):
            job.queue_position = pos

def extract_metadata_quick(job):
    """Quick metadata extraction right after upload (no logging to progress)"""
    filepath = job.input_path
    
    cmd = [
        'ffprobe', '-i', filepath,
        '-print_format', 'json',
        '-show_chapters', '-show_format',
        '-loglevel', 'error'
    ]
    
    result = subprocess.run(cmd, capture_output=True, text=True)
    
    if result.returncode != 0:
        return
    
    data = json.loads(result.stdout)
    chapters = data.get('chapters', [])
    format_info = data.get('format', {})
    tags = format_info.get('tags', {})
    tags = {k.lower(): v for k, v in tags.items()}
    
    duration = float(format_info.get('duration', 0))
    duration_str = f"{int(duration // 3600)}h {int((duration % 3600) // 60)}m {int(duration % 60)}s"
    
    bitrate = format_info.get('bit_rate')
    bitrate_kbps = int(bitrate) // 1000 if bitrate else None
    
    job.metadata = {
        'title': tags.get('title') or tags.get('album') or job.base_name,
        'author': tags.get('artist') or tags.get('author') or tags.get('album_artist'),
        'narrator': tags.get('composer') or tags.get('narrator') or tags.get('album_artist'),
        'album': tags.get('album'),
        'year': tags.get('date', '')[:4] if tags.get('date') else tags.get('year'),
        'genre': tags.get('genre'),
        'publisher': tags.get('publisher') or tags.get('copyright'),
        'description': tags.get('description') or tags.get('comment'),
        'duration': duration_str,
        'duration_secs': duration,
        'bitrate': f"{bitrate_kbps} kbps" if bitrate_kbps else None,
        'chapters_count': len(chapters),
        'file_size_mb': round(os.path.getsize(filepath) / (1024 * 1024), 1)
    }
    
    job.total_chapters = len(chapters)
    
    # Extract cover art
    cover_path = os.path.join(job.temp_dir, 'cover.jpg')
    cover_cmd = [
        'ffmpeg', '-i', filepath,
        '-an', '-vcodec', 'copy',
        '-y', cover_path
    ]
    cover_result = subprocess.run(cover_cmd, capture_output=True)
    
    if cover_result.returncode == 0 and os.path.exists(cover_path) and os.path.getsize(cover_path) > 0:
        job.cover_path = cover_path
    
    logger.info(f"[Job {job.id[:8]}] Quick metadata: {job.metadata.get('title')} by {job.metadata.get('author')}, {len(chapters)} chapters")

def extract_metadata(filepath, job):
    """Extract metadata and cover art using ffprobe"""
    job.log("Extracting audiobook metadata...")
    
    cmd = [
        'ffprobe', '-i', filepath,
        '-print_format', 'json',
        '-show_chapters', '-show_format', '-show_streams',
        '-loglevel', 'error'
    ]
    
    result = subprocess.run(cmd, capture_output=True, text=True)
    
    if result.returncode != 0:
        logger.error(f"ffprobe error: {result.stderr}")
        job.log(f"ffprobe error: {result.stderr}", 'error')
        return [], {}
    
    data = json.loads(result.stdout)
    chapters = data.get('chapters', [])
    format_info = data.get('format', {})
    tags = format_info.get('tags', {})
    
    # Normalize tag keys to lowercase
    tags = {k.lower(): v for k, v in tags.items()}
    
    # Extract duration
    duration = float(format_info.get('duration', 0))
    duration_str = f"{int(duration // 3600)}h {int((duration % 3600) // 60)}m {int(duration % 60)}s"
    
    # Extract bitrate
    bitrate = format_info.get('bit_rate')
    if bitrate:
        bitrate_kbps = int(bitrate) // 1000
    else:
        bitrate_kbps = None
    
    # Build metadata dict
    job.metadata = {
        'title': tags.get('title') or tags.get('album') or job.base_name,
        'author': tags.get('artist') or tags.get('author') or tags.get('album_artist'),
        'narrator': tags.get('composer') or tags.get('narrator') or tags.get('album_artist'),
        'album': tags.get('album'),
        'year': tags.get('date', '')[:4] if tags.get('date') else tags.get('year'),
        'genre': tags.get('genre'),
        'publisher': tags.get('publisher') or tags.get('copyright'),
        'description': tags.get('description') or tags.get('comment'),
        'duration': duration_str,
        'duration_secs': duration,
        'bitrate': f"{bitrate_kbps} kbps" if bitrate_kbps else None,
        'chapters_count': len(chapters),
        'file_size_mb': round(os.path.getsize(filepath) / (1024 * 1024), 1)
    }
    
    # Log metadata found
    if job.metadata['title']:
        job.log(f"Title: {job.metadata['title']}")
    if job.metadata['author']:
        job.log(f"Author: {job.metadata['author']}")
    if job.metadata['narrator'] and job.metadata['narrator'] != job.metadata['author']:
        job.log(f"Narrator: {job.metadata['narrator']}")
    job.log(f"Duration: {duration_str} | Chapters: {len(chapters)} | {job.metadata['file_size_mb']}MB")
    
    # Extract cover art
    cover_path = os.path.join(job.temp_dir, 'cover.jpg')
    cover_cmd = [
        'ffmpeg', '-i', filepath,
        '-an', '-vcodec', 'copy',
        '-y', cover_path
    ]
    cover_result = subprocess.run(cover_cmd, capture_output=True)
    
    if cover_result.returncode == 0 and os.path.exists(cover_path) and os.path.getsize(cover_path) > 0:
        job.cover_path = cover_path
        job.log("Cover art extracted")
    else:
        job.cover_path = None
    
    logger.info(f"Metadata extracted - Title: {job.metadata.get('title')}, "
                f"Author: {job.metadata.get('author')}, Duration: {duration_str}, "
                f"Chapters: {len(chapters)}")
    
    return chapters, format_info

def build_metadata_args(job, chapter_title=None, track_num=None, total_tracks=None):
    """Build ffmpeg metadata arguments"""
    args = []
    meta = job.metadata
    
    if meta.get('title'):
        album = meta['title']
        args.extend(['-metadata', f'album={album}'])
    
    if chapter_title:
        args.extend(['-metadata', f'title={chapter_title}'])
    elif meta.get('title'):
        args.extend(['-metadata', f'title={meta["title"]}'])
    
    if meta.get('author'):
        args.extend(['-metadata', f'artist={meta["author"]}'])
        args.extend(['-metadata', f'album_artist={meta["author"]}'])
    
    if meta.get('year'):
        args.extend(['-metadata', f'date={meta["year"]}'])
    
    if meta.get('genre'):
        args.extend(['-metadata', f'genre={meta["genre"]}'])
    
    if track_num and total_tracks:
        args.extend(['-metadata', f'track={track_num}/{total_tracks}'])
    
    # Always mark as audiobook
    args.extend(['-metadata', 'genre=Audiobook'])
    
    return args

def convert_single_chapter(args):
    """Convert a single chapter - used by parallel executor"""
    filepath, chapter_info, output_file, cover_path, meta_args = args
    i, total, title, start_time_pos, duration = chapter_info
    
    # Build command with input seeking (-ss before -i) for speed
    cover_input = []
    cover_map = []
    if cover_path and os.path.exists(cover_path):
        cover_input = ['-i', cover_path]
        cover_map = ['-map', '0:a', '-map', '1:0', '-c:v', 'copy', '-id3v2_version', '3',
                     '-metadata:s:v', 'title=Album cover', '-metadata:s:v', 'comment=Cover (front)']
    
    # Input seeking: -ss before -i, then -t for duration (faster than output seeking)
    cmd = ['ffmpeg', '-ss', start_time_pos, '-i', filepath] + cover_input + [
        '-t', str(duration),
        '-vn', '-acodec', 'libmp3lame', '-b:a', '128k'
    ] + (cover_map if cover_input else []) + meta_args + ['-y', output_file]
    
    start_time = time.time()
    result = subprocess.run(cmd, capture_output=True)
    elapsed = time.time() - start_time
    
    success = result.returncode == 0
    file_size = os.path.getsize(output_file) / (1024 * 1024) if success and os.path.exists(output_file) else 0
    
    return {
        'index': i,
        'total': total,
        'title': title,
        'success': success,
        'elapsed': elapsed,
        'file_size': file_size,
        'output_file': output_file
    }

def split_to_mp3(filepath, chapters, output_dir, base_name, job):
    """Split file into MP3s by chapter with embedded metadata and cover (parallel)"""
    files = []
    
    if not chapters:
        job.log("No chapters found - converting entire file to single MP3")
        job.total_chapters = 1
        job.current_chapter = 1
        
        output_file = os.path.join(output_dir, f"{base_name}.mp3")
        meta_args = build_metadata_args(job)
        
        cover_input = []
        cover_map = []
        if job.cover_path and os.path.exists(job.cover_path):
            cover_input = ['-i', job.cover_path]
            cover_map = ['-map', '0:a', '-map', '1:0', '-c:v', 'copy', '-id3v2_version', '3',
                         '-metadata:s:v', 'title=Album cover', '-metadata:s:v', 'comment=Cover (front)']
        
        cmd = ['ffmpeg', '-i', filepath] + cover_input + [
            '-vn', '-acodec', 'libmp3lame', '-b:a', '128k'
        ] + (cover_map if cover_input else []) + meta_args + ['-y', output_file]
        
        logger.info(f"Converting entire file: {base_name}")
        start_time = time.time()
        
        process = subprocess.Popen(cmd, stderr=subprocess.PIPE, universal_newlines=True)
        job.current_process = process
        last_update = time.time()
        
        while process.poll() is None:
            if job.cancelled:
                process.terminate()
                return []
            time.sleep(1)
            if time.time() - last_update >= 10:
                elapsed = int(time.time() - start_time)
                job.log(f"Still converting... ({elapsed}s elapsed)")
                last_update = time.time()
        
        job.current_process = None
        elapsed = time.time() - start_time
        job.log(f"Conversion complete ({elapsed:.1f}s)")
        files.append(output_file)
    else:
        job.total_chapters = len(chapters)
        job.log(f"Converting {len(chapters)} chapters using {PARALLEL_WORKERS} parallel workers")
        
        # Prepare all chapter conversion tasks
        tasks = []
        for i, chapter in enumerate(chapters, 1):
            title = chapter.get('tags', {}).get('title', f'Chapter {i}')
            safe_title = "".join(c for c in title if c.isalnum() or c in ' -_').strip()
            output_file = os.path.join(output_dir, f"{i:03d} - {safe_title}.mp3")
            
            start = float(chapter['start_time'])
            end = float(chapter['end_time'])
            duration = end - start
            
            meta_args = build_metadata_args(job, chapter_title=title, track_num=i, total_tracks=len(chapters))
            
            chapter_info = (i, len(chapters), title, chapter['start_time'], duration)
            tasks.append((filepath, chapter_info, output_file, job.cover_path, meta_args))
            files.append(output_file)
        
        # Process chapters in parallel
        completed = 0
        conversion_start = time.time()
        
        with ThreadPoolExecutor(max_workers=PARALLEL_WORKERS) as executor:
            futures = {executor.submit(convert_single_chapter, task): task for task in tasks}
            
            for future in as_completed(futures):
                if job.cancelled:
                    executor.shutdown(wait=False, cancel_futures=True)
                    return []
                
                result = future.result()
                completed += 1
                job.current_chapter = completed
                
                if result['success']:
                    job.log(f"[{completed}/{result['total']}] {result['title']} ({result['elapsed']:.1f}s, {result['file_size']:.1f}MB)")
                else:
                    job.log(f"[{completed}/{result['total']}] Warning: {result['title']} may have issues", 'warning')
                
                logger.info(f"Chapter {result['index']}/{result['total']} complete: {result['elapsed']:.1f}s")
        
        total_elapsed = time.time() - conversion_start
        job.log(f"All chapters converted in {total_elapsed:.1f}s")
    
    return files

def process_job(job):
    """Process a single conversion job"""
    try:
        if job.cancelled:
            return
        
        job.status = 'processing'
        job.started_at = job.started_at or datetime.now()  # Keep existing if set during upload/download
        job.queue_position = 0
        update_queue_positions()
        
        job.log(f"Starting processing of: {job.filename}")
        logger.info(f"[Job {job.id[:8]}] Processing started for: {job.filename}")
        
        output_dir = os.path.join(job.temp_dir, 'output')
        os.makedirs(output_dir)
        
        if job.cancelled:
            raise Exception("Job cancelled")
        
        job.log("Analyzing file structure...")
        chapters, format_info = extract_metadata(job.input_path, job)
        
        # Log metadata if not already logged during quick extract
        if job.metadata.get('title'):
            job.log(f"Book: {job.metadata['title']}")
        if job.metadata.get('author'):
            job.log(f"Author: {job.metadata['author']}")
        
        if job.cancelled:
            raise Exception("Job cancelled")
        
        job.log("Beginning audio conversion...")
        mp3_files = split_to_mp3(job.input_path, chapters, output_dir, job.base_name, job)
        
        if job.cancelled or not mp3_files:
            raise Exception("Job cancelled" if job.cancelled else "No files produced")
        
        job.log(f"Creating ZIP archive with {len(mp3_files)} files...")
        zip_path = os.path.join(job.temp_dir, f"{job.base_name}.zip")
        
        start_time = time.time()
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zf:
            for i, mp3 in enumerate(mp3_files, 1):
                if job.cancelled:
                    raise Exception("Job cancelled")
                zf.write(mp3, os.path.basename(mp3))
                if i % 10 == 0:
                    job.log(f"Zipping: {i}/{len(mp3_files)} files added")
        
        elapsed = time.time() - start_time
        zip_size = os.path.getsize(zip_path) / (1024 * 1024)
        job.log(f"ZIP created ({zip_size:.1f}MB) in {elapsed:.1f}s")
        logger.info(f"[Job {job.id[:8]}] ZIP complete: {zip_size:.2f}MB")
        
        # Clean up intermediate files (keep ZIP and cover)
        if job.input_path and os.path.exists(job.input_path):
            os.remove(job.input_path)
        if os.path.exists(output_dir):
            shutil.rmtree(output_dir, ignore_errors=True)
        
        job.zip_path = zip_path
        job.status = 'complete'
        job.completed_at = datetime.now()
        job.log("Processing complete! Ready for download.", 'success')
        logger.info(f"[Job {job.id[:8]}] Job completed successfully")
        
    except Exception as e:
        if job.cancelled:
            job.status = 'cancelled'
        else:
            job.status = 'error'
            job.error = str(e)
            job.log(f"Error: {str(e)}", 'error')
            logger.exception(f"[Job {job.id[:8]}] Job failed with exception")
        job.completed_at = datetime.now()
        
        # Clean up temp files on error/cancel
        if job.temp_dir and os.path.exists(job.temp_dir):
            shutil.rmtree(job.temp_dir, ignore_errors=True)

def job_worker():
    """Worker thread that processes jobs from the queue one at a time"""
    logger.info("Job worker started")
    while True:
        job_id = job_queue.get()
        
        with jobs_lock:
            job = jobs.get(job_id)
        
        if job and job.status == 'queued':
            process_job(job)
        
        job_queue.task_done()

def start_worker():
    """Start the job worker thread if not already running"""
    global worker_thread
    if worker_thread is None or not worker_thread.is_alive():
        worker_thread = threading.Thread(target=job_worker, daemon=True)
        worker_thread.start()

@app.route('/login', methods=['GET', 'POST'])
def login():
    error = None
    if request.method == 'POST':
        username = request.form.get('username', '')
        password = request.form.get('password', '')
        remember = request.form.get('remember', False)
        
        if username == APP_USERNAME and password == APP_PASSWORD:
            session['logged_in'] = True
            if remember:
                session.permanent = True  # Use PERMANENT_SESSION_LIFETIME (30 days)
            logger.info(f"User logged in: {username} (remember: {bool(remember)})")
            return redirect(url_for('index'))
        else:
            error = 'Invalid credentials'
            logger.warning(f"Failed login attempt for user: {username}")
    
    return render_template('login.html', error=error)

@app.route('/logout')
def logout():
    session.pop('logged_in', None)
    return redirect(url_for('login'))

@app.route('/')
@login_required
def index():
    cleanup_old_jobs()
    return render_template('index.html')

@app.route('/upload', methods=['POST'])
@login_required
def upload():
    if 'file' not in request.files:
        return jsonify({'error': 'No file provided'}), 400
    
    file = request.files['file']
    if file.filename == '':
        return jsonify({'error': 'No file selected'}), 400
    
    if not allowed_file(file.filename):
        return jsonify({'error': 'Invalid file type. Use .m4b or .m4a'}), 400
    
    job_id = str(uuid.uuid4())
    filename = secure_filename(file.filename)
    job = Job(job_id, filename)
    job.temp_dir = tempfile.mkdtemp(dir=TEMP_DIR or None)
    job.base_name = os.path.splitext(filename)[0]
    job.input_path = os.path.join(job.temp_dir, filename)
    job.started_at = datetime.now()  # Start timer from upload
    
    logger.info(f"[Job {job_id[:8]}] New upload started: {filename}")
    job.log(f"Upload received: {filename}")
    
    job.log("Saving uploaded file...")
    file.save(job.input_path)
    file_size = os.path.getsize(job.input_path) / (1024 * 1024)
    job.log(f"File saved ({file_size:.1f}MB)")
    logger.info(f"[Job {job_id[:8]}] File saved: {file_size:.2f}MB")
    
    # Extract metadata immediately (quick operation)
    job.log("Reading audiobook metadata...")
    extract_metadata_quick(job)
    
    with jobs_lock:
        jobs[job_id] = job
    
    # Add to queue
    job_queue.put(job_id)
    update_queue_positions()
    
    if job.queue_position > 0:
        job.log(f"Added to queue (position {job.queue_position})")
    
    # Ensure worker is running
    start_worker()
    
    return jsonify({'job_id': job_id})

@app.route('/status/<job_id>')
@login_required
def job_status(job_id):
    """SSE endpoint for job progress"""
    def generate():
        last_progress_count = 0
        
        while True:
            with jobs_lock:
                job = jobs.get(job_id)
            
            if not job:
                yield f"data: {json.dumps({'status': 'not_found'})}\n\n"
                break
            
            current_count = len(job.progress)
            if current_count > last_progress_count or last_progress_count == 0:
                new_messages = job.progress[last_progress_count:]
                last_progress_count = current_count
                
                data = {
                    'status': job.status,
                    'filename': job.filename,
                    'messages': new_messages,
                    'total_chapters': job.total_chapters,
                    'current_chapter': job.current_chapter,
                    'queue_position': job.queue_position,
                    'started_at': job.started_at.isoformat() if job.started_at else None,
                    'elapsed_seconds': int(((job.completed_at or datetime.now()) - job.started_at).total_seconds()) if job.started_at else None,
                    'metadata': job.metadata,
                    'has_cover': job.cover_path is not None and os.path.exists(job.cover_path) if job.cover_path else False
                }
                yield f"data: {json.dumps(data)}\n\n"
            
            if job.status in ('complete', 'error'):
                final_data = {
                    'status': job.status,
                    'error': job.error
                }
                yield f"data: {json.dumps(final_data)}\n\n"
                break
            
            time.sleep(1)
    
    return Response(generate(), mimetype='text/event-stream',
                    headers={'Cache-Control': 'no-cache', 'X-Accel-Buffering': 'no'})

@app.route('/cancel/<job_id>', methods=['POST'])
@login_required
def cancel_job(job_id):
    """Cancel a running or queued job"""
    with jobs_lock:
        job = jobs.get(job_id)
    
    if not job:
        return jsonify({'error': 'Job not found'}), 404
    
    if job.status in ('complete', 'error', 'cancelled'):
        return jsonify({'error': 'Job already finished'}), 400
    
    was_processing = job.status == 'processing'
    job.cancelled = True
    job.status = 'cancelled'
    job.log("Job cancelled by user", 'warning')
    logger.info(f"[Job {job_id[:8]}] Cancelled by user")
    
    # Kill any running ffmpeg process
    if job.current_process:
        try:
            job.current_process.terminate()
            job.current_process.wait(timeout=5)
        except:
            try:
                job.current_process.kill()
            except:
                pass
    
    # Only clean up temp files if not processing (let process_job handle cleanup)
    if not was_processing and job.temp_dir and os.path.exists(job.temp_dir):
        shutil.rmtree(job.temp_dir, ignore_errors=True)
    
    return jsonify({'success': True})

@app.route('/download/<job_id>')
@login_required
def download(job_id):
    """Download completed job"""
    with jobs_lock:
        job = jobs.get(job_id)
    
    if not job:
        return jsonify({'error': 'Job not found'}), 404
    
    if job.status != 'complete':
        return jsonify({'error': 'Job not complete'}), 400
    
    if not job.zip_path or not os.path.exists(job.zip_path):
        return jsonify({'error': 'File not found'}), 404
    
    logger.info(f"[Job {job_id[:8]}] Download requested")
    base_name = os.path.splitext(job.filename)[0]
    
    return send_file(
        job.zip_path,
        mimetype='application/zip',
        as_attachment=True,
        download_name=f"{base_name}.zip"
    )

@app.route('/cover/<job_id>')
@login_required
def get_cover(job_id):
    """Get cover art for a job"""
    with jobs_lock:
        job = jobs.get(job_id)
    
    if not job or not job.cover_path or not os.path.exists(job.cover_path):
        return '', 404
    
    return send_file(job.cover_path, mimetype='image/jpeg')

@app.route('/jobs')
@login_required
def list_jobs():
    """Get all active jobs"""
    with jobs_lock:
        job_list = [job.to_dict() for job in jobs.values()]
    job_list.sort(key=lambda x: x['created_at'], reverse=True)
    return jsonify(job_list)

# ============== Audiobookshelf Integration ==============

def abs_request(endpoint, method='GET', **kwargs):
    """Make a request to Audiobookshelf API"""
    if not AUDIOBOOKSHELF_URL or not AUDIOBOOKSHELF_TOKEN:
        return None
    
    url = f"{AUDIOBOOKSHELF_URL.rstrip('/')}{endpoint}"
    headers = {'Authorization': f'Bearer {AUDIOBOOKSHELF_TOKEN}'}
    
    try:
        response = requests.request(method, url, headers=headers, timeout=30, **kwargs)
        response.raise_for_status()
        return response
    except Exception as e:
        logger.error(f"Audiobookshelf API error: {e}")
        return None

@app.route('/abs/status')
@login_required
def abs_status():
    """Check if Audiobookshelf is configured and reachable"""
    if not AUDIOBOOKSHELF_URL or not AUDIOBOOKSHELF_TOKEN:
        return jsonify({'configured': False})
    
    response = abs_request('/api/libraries')
    if response:
        return jsonify({'configured': True, 'url': AUDIOBOOKSHELF_URL})
    return jsonify({'configured': False, 'error': 'Could not connect'})

@app.route('/abs/libraries')
@login_required
def abs_libraries():
    """List all libraries from Audiobookshelf"""
    response = abs_request('/api/libraries')
    if not response:
        return jsonify({'error': 'Could not fetch libraries'}), 500
    
    data = response.json()
    libraries = [{'id': lib['id'], 'name': lib['name']} for lib in data.get('libraries', [])]
    return jsonify(libraries)

@app.route('/abs/libraries/<library_id>/items')
@login_required
def abs_library_items(library_id):
    """List all items in a library"""
    # ABS supports: title, authorName, addedAt, duration, etc. with desc for descending
    sort = request.args.get('sort', 'media.metadata.title')
    desc = request.args.get('desc', '0')
    response = abs_request(f'/api/libraries/{library_id}/items?expanded=1&sort={sort}&desc={desc}')
    if not response:
        return jsonify({'error': 'Could not fetch items'}), 500
    
    data = response.json()
    items = []
    authors_set = set()
    series_set = set()
    
    for item in data.get('results', []):
        media = item.get('media', {})
        metadata = media.get('metadata', {})
        
        # Get author - list endpoint has authorName, can be comma-separated
        author_raw = metadata.get('authorName', '')
        item_authors = [a.strip() for a in author_raw.split(',') if a.strip()] if author_raw else []
        
        # Get series - list endpoint has seriesName like "The Cosmere, Mistborn #1"
        # Can be comma-separated for multiple series
        series_name_raw = metadata.get('seriesName', '')
        item_series = []
        if series_name_raw:
            for s in series_name_raw.split(','):
                # Clean up each series name - remove "#1", "#2", "Book 3" etc
                cleaned = re.sub(r'\s*(#|Book\s*)\d+(\.\d+)?\s*$', '', s.strip(), flags=re.IGNORECASE).strip()
                if cleaned:
                    item_series.append(cleaned)
        
        for a in item_authors:
            authors_set.add(a)
        for s in item_series:
            series_set.add(s)
        
        items.append({
            'id': item.get('id'),
            'title': metadata.get('title', 'Unknown'),
            'authors': item_authors,
            'narrator': metadata.get('narratorName', ''),
            'series': item_series,  # List of series names
            'duration': media.get('duration', 0),
            'has_cover': bool(media.get('coverPath'))
        })
    
    return jsonify({
        'items': items,
        'authors': sorted(list(authors_set)),
        'series': sorted(list(series_set))
    })

@app.route('/abs/items/<item_id>/cover')
@login_required
def abs_item_cover(item_id):
    """Proxy cover image from Audiobookshelf"""
    response = abs_request(f'/api/items/{item_id}/cover', stream=True)
    if not response:
        return '', 404
    
    return Response(response.content, mimetype=response.headers.get('content-type', 'image/jpeg'))

def download_from_audiobookshelf(job, item_id, file_ino):
    """Background task to download file from Audiobookshelf"""
    try:
        download_response = abs_request(f'/api/items/{item_id}/file/{file_ino}/download', stream=True)
        if not download_response:
            job.status = 'error'
            job.log("Error: Could not connect to Audiobookshelf")
            return
        
        total_size = int(download_response.headers.get('content-length', 0))
        downloaded = 0
        last_log_pct = -10
        
        if total_size > 0:
            job.log(f"Downloading: 0% of {total_size / (1024*1024):.1f}MB")
        
        logger.info(f"[Job {job.id[:8]}] Starting download, size: {total_size / (1024*1024):.1f}MB")
        
        with open(job.input_path, 'wb') as f:
            for chunk in download_response.iter_content(chunk_size=65536):
                if job.cancelled:
                    logger.info(f"[Job {job.id[:8]}] Download cancelled")
                    shutil.rmtree(job.temp_dir, ignore_errors=True)
                    return
                
                f.write(chunk)
                downloaded += len(chunk)
                
                # Log progress every 10%
                if total_size > 0:
                    pct = int(downloaded * 100 / total_size)
                    if pct >= last_log_pct + 10:
                        last_log_pct = pct
                        job.log(f"Downloading: {pct}% ({downloaded / (1024*1024):.1f}MB / {total_size / (1024*1024):.1f}MB)")
                        logger.info(f"[Job {job.id[:8]}] Download progress: {pct}%")
        
        file_size = os.path.getsize(job.input_path) / (1024 * 1024)
        job.log(f"Download complete ({file_size:.1f}MB)")
        logger.info(f"[Job {job.id[:8]}] Download complete: {file_size:.2f}MB")
        
        # Extract metadata
        job.log("Reading audiobook metadata...")
        extract_metadata_quick(job)
        
        # Set status to queued so worker will process it
        job.status = 'queued'
        
        # Add to processing queue
        job_queue.put(job.id)
        update_queue_positions()
        
        if job.queue_position > 0:
            job.log(f"Added to queue (position {job.queue_position})")
        else:
            job.log("Starting conversion...")
        
        start_worker()
        
    except Exception as e:
        job.status = 'error'
        job.log(f"Download failed: {str(e)}")
        logger.error(f"[Job {job.id[:8]}] Download failed: {e}")
        shutil.rmtree(job.temp_dir, ignore_errors=True)

@app.route('/abs/items/<item_id>/convert', methods=['POST'])
@login_required
def abs_convert_item(item_id):
    """Download an item from Audiobookshelf and start conversion"""
    # Get item details
    response = abs_request(f'/api/items/{item_id}')
    if not response:
        return jsonify({'error': 'Could not fetch item details'}), 500
    
    item_data = response.json()
    media = item_data.get('media', {})
    metadata = media.get('metadata', {})
    audio_files = media.get('audioFiles', [])
    
    if not audio_files:
        return jsonify({'error': 'No audio files found'}), 400
    
    # Find the best file to download (prefer m4b/m4a)
    best_file = None
    for af in audio_files:
        ext = af.get('metadata', {}).get('ext', '').lower().lstrip('.')
        if ext in ('m4b', 'm4a'):
            best_file = af
            break
    
    if not best_file:
        best_file = audio_files[0]
    
    file_ino = best_file.get('ino')
    file_ext = best_file.get('metadata', {}).get('ext', '.m4b').lstrip('.')
    
    if not file_ino:
        return jsonify({'error': 'Could not determine file to download'}), 400
    
    # Create job
    title = metadata.get('title', 'Unknown')
    safe_title = "".join(c for c in title if c.isalnum() or c in ' -_').strip()
    filename = f"{safe_title}.{file_ext}"
    
    job_id = str(uuid.uuid4())
    job = Job(job_id, filename)
    job.temp_dir = tempfile.mkdtemp(dir=TEMP_DIR or None)
    job.base_name = safe_title
    job.input_path = os.path.join(job.temp_dir, filename)
    job.status = 'downloading'
    job.abs_item_id = item_id  # Store for retry
    job.started_at = datetime.now()  # Start timer from download
    
    # Pre-populate metadata from Audiobookshelf
    # Duration can be at media.duration or media.audioFiles[0].duration
    duration_secs = media.get('duration', 0)
    if not duration_secs and audio_files:
        duration_secs = audio_files[0].get('duration', 0)
    
    hours, remainder = divmod(int(duration_secs), 3600)
    minutes, seconds = divmod(remainder, 60)
    if hours > 0:
        duration_str = f"{hours}h {minutes}m"
    else:
        duration_str = f"{minutes}m {seconds}s"
    
    # Get author - try authorName first, then authors array
    author_str = metadata.get('authorName', '')
    if not author_str:
        authors = metadata.get('authors', [])
        if authors:
            author_str = ', '.join(a.get('name', '') if isinstance(a, dict) else str(a) for a in authors)
    
    # Get narrator
    narrators = metadata.get('narrators', [])
    narrator_str = ', '.join(narrators) if narrators else metadata.get('narratorName', '')
    
    job.metadata = {
        'title': title,
        'author': author_str,
        'narrator': narrator_str,
        'duration': duration_str,
        'chapters_count': len(media.get('chapters', [])),
        'file_size_mb': round(best_file.get('metadata', {}).get('size', 0) / (1024 * 1024), 1)
    }
    
    # Download cover image from Audiobookshelf
    if media.get('coverPath'):
        try:
            cover_response = abs_request(f'/api/items/{item_id}/cover', stream=True)
            if cover_response:
                job.cover_path = os.path.join(job.temp_dir, 'cover.jpg')
                with open(job.cover_path, 'wb') as f:
                    f.write(cover_response.content)
        except:
            pass
    
    logger.info(f"[Job {job_id[:8]}] Starting Audiobookshelf download: {title}")
    job.log(f"Downloading from Audiobookshelf: {title}")
    
    # Register job immediately so client can connect to SSE
    with jobs_lock:
        jobs[job_id] = job
    
    # Start download in background thread
    download_thread = threading.Thread(
        target=download_from_audiobookshelf, 
        args=(job, item_id, file_ino),
        daemon=True
    )
    download_thread.start()
    
    return jsonify({'job_id': job_id})

if __name__ == '__main__':
    logger.info("=" * 60)
    logger.info("M4B to MP3 Converter starting up")
    logger.info(f"Max upload size: 2GB")
    logger.info(f"Job expiry: {JOB_EXPIRY_HOURS} hour(s)")
    logger.info(f"Auth enabled - Username: {APP_USERNAME}")
    logger.info("Jobs will be processed sequentially (one at a time)")
    logger.info("=" * 60)
    start_worker()
    app.run(host='0.0.0.0', port=5000, debug=True, threaded=True)
