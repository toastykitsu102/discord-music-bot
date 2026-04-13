import os
import sys
import stat
import json
import gzip
import shutil
import glob
import subprocess
import logging
import asyncio
import threading
import functools
import inspect
import platform
import urllib.request
import urllib.parse
import tarfile
from http.server import HTTPServer, BaseHTTPRequestHandler
from logging.handlers import TimedRotatingFileHandler
from dotenv import load_dotenv
from mutagen.mp3 import MP3
from pyngrok import ngrok
import cgi
import secrets, time
from urllib.parse import urlparse, parse_qs

# Active tokens mapping (guild_id -> {"token": str, "expires": float})
active_tokens = {}

# Rate limiting storage: ip -> {"count": int, "first_seen": float, "blocked_until": float}
ip_failures = {}

# Tunable limits
MAX_FAILED_PER_WINDOW = 10     # allow this many failed attempts
WINDOW_SECONDS = 10           # within this many seconds
BLOCK_SECONDS = 900            # block IP for this many seconds (15 minutes)

import discord
from discord.ext import commands
from discord import PCMVolumeTransformer

import tkinter as tk
from tkinter.scrolledtext import ScrolledText
from tkinter import filedialog, messagebox

public_url = None

def resource_path(relative_path):
    if hasattr(sys, '_MEIPASS'):
        return os.path.join(sys._MEIPASS, relative_path)
    return os.path.abspath(relative_path)

# Load environment variables
load_dotenv(resource_path('.env'))

# Ensure folders
os.makedirs(resource_path('logs'), exist_ok=True)
os.makedirs(resource_path('music'), exist_ok=True)

# Logger setup
logger = logging.getLogger('discord_bot')
logger.setLevel(logging.DEBUG if os.getenv("DEBUG", "false").lower() == "true" else logging.INFO)
logger.propagate = False
formatter = logging.Formatter('%(asctime)s [%(levelname)s] %(message)s')

file_handler = TimedRotatingFileHandler(
    filename=resource_path('logs/discord_bot.log'),
    when='midnight', interval=1, backupCount=10, encoding='utf-8'
)
file_handler.setLevel(logging.DEBUG)
file_handler.setFormatter(formatter)
console_handler = logging.StreamHandler()
console_handler.setLevel(logging.ERROR)
console_handler.setFormatter(formatter)
logger.addHandler(file_handler)
logger.addHandler(console_handler)

MAX_LOG_SIZE = 10 * 1024 * 1024  # 10 MB


def compress_log_file(src, dst):
    with open(src, 'rb') as f_in, gzip.open(dst, 'wb') as f_out:
        shutil.copyfileobj(f_in, f_out)
    os.remove(src)

def decompress_log_file(src, dst):
    with gzip.open(src, 'rb') as f_in, open(dst, 'wb') as f_out:
        shutil.copyfileobj(f_in, f_out)
    os.remove(src)

# Restore or compress logs
log_dir = resource_path('logs')
for fn in os.listdir(log_dir):
    log_path = os.path.join(log_dir, fn)
    if fn.endswith('.log.gz') and not os.path.exists(log_path[:-3]):
        try:
            decompress_log_file(log_path, log_path[:-3])
        except Exception as e:
            logger.error(f"Failed to decompress {log_path}: {e}")
    elif fn.endswith('.log') and os.path.getsize(log_path) > MAX_LOG_SIZE:
        try:
            backup = log_path + '.gz'
            compress_log_file(log_path, backup)
            os.remove(log_path)
        except Exception as e:
            logger.error(f"Failed to compress {log_path}: {e}")


# Exception logging decorator
def log_exceptions(func):
    if inspect.iscoroutinefunction(func):

        @functools.wraps(func)
        async def async_wrapper(*args, **kwargs):
            try:
                return await func(*args, **kwargs)
            except Exception as e:
                logger.error(f"Exception in async '{func.__name__}': {e}",
                             exc_info=True)
                raise

        return async_wrapper
    else:

        @functools.wraps(func)
        def sync_wrapper(*args, **kwargs):
            try:
                return func(*args, **kwargs)
            except Exception as e:
                logger.error(f"Exception in '{func.__name__}': {e}",
                             exc_info=True)
                raise

        return sync_wrapper


# Command execution logging decorator
def log_command_execution(func):
    if inspect.iscoroutinefunction(func):

        @functools.wraps(func)
        async def wrapper(ctx, *args, **kwargs):
            user = f"{ctx.author} ({ctx.author.id})"
            command = ctx.command.name if ctx.command else func.__name__
            logger.info(f"Command '{command}' issued by {user}")
            try:
                result = await func(ctx, *args, **kwargs)
                logger.info(f"Command '{command}' by {user} succeeded.")
                return result
            except Exception as e:
                logger.error(
                    f"Command '{command}' by {user} failed with error: {e}",
                    exc_info=True)
                await ctx.send(
                    "An error occurred while processing the command.")
                raise

        return wrapper
    else:
        raise TypeError(
            "log_command_execution should only be used on async command functions."
        )
    
def get_settings_file(guild_id: int) -> str:
    folder = get_guild_music_folder(guild_id)
    return os.path.join(folder, "settings.json")

def save_settings(guild_id: int, settings: dict):
    path = get_settings_file(guild_id)
    # Ensure the folder exists before saving
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(settings, f, indent=4)
    logger.info(f"Settings saved for guild {guild_id} at {path}")

def load_settings(guild_id: int) -> dict:
    path = get_settings_file(guild_id)
    if not os.path.exists(path):
        # Always create the file if missing, so settings persist
        save_settings(guild_id, {})
        return {}
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def get_guild_volume(guild_id: int) -> float:
    """Return saved guild volume (0.0–2.0), default 1.0"""
    settings = load_settings(guild_id)
    return settings.get("volume", 1.0)

def set_guild_volume(guild_id: int, volume: float):
    """Save guild volume (0.0–2.0)"""
    settings = load_settings(guild_id)
    settings["volume"] = volume
    save_settings(guild_id, settings)


    
async def has_command_permission(ctx, command_name: str) -> bool:
    # Admins always have access
    if ctx.author.guild_permissions.administrator:
        return True

    settings = load_settings(ctx.guild.id)
    command_roles = settings.get("command_roles", {})

    # If command has no restriction, allow all
    if command_name not in command_roles:
        return True

    # Restriction exists → check roles
    allowed_roles = command_roles[command_name]
    user_role_ids = [role.id for role in ctx.author.roles]
    return any(role_id in user_role_ids for role_id in allowed_roles)

def command_requires_permission(command_name: str):
    def decorator(func):
        @functools.wraps(func)
        async def wrapper(ctx, *args, **kwargs):
            if not await has_command_permission(ctx, command_name.lower()):
                await ctx.send("You don't have permission to use this command.")
                return
            return await func(ctx, *args, **kwargs)
        return wrapper
    return decorator


# if os.name is linux then load libopus.so.0 elif os.name is windows then load opus.dll
from threading import Lock

songs_lock = Lock()

songs_json_path = resource_path("songs.json")

def get_guild_music_folder(guild_id: int) -> str:
    folder = os.path.join(resource_path("music"), str(guild_id))
    os.makedirs(folder, exist_ok=True)
    return folder

def get_songs_file(guild_id: int) -> str:
    return os.path.join(get_guild_music_folder(guild_id), "songs.json")

def load_songs(guild_id: int) -> list:
    path = get_songs_file(guild_id)
    if not os.path.exists(path):
        return []
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def save_songs(guild_id: int, songs: list):
    path = get_songs_file(guild_id)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(songs, f, indent=4)

def add_song_to_json(guild_id: int, filename: str):
    songs = load_songs(guild_id)

    # Extract title and duration
    name = os.path.splitext(os.path.basename(filename))[0]
    try:
        audio = MP3(filename)
        dur_sec = int(audio.info.length)
        duration = f"{dur_sec // 60}:{dur_sec % 60:02d}"
    except Exception:
        duration = "?:??"

    # Avoid duplicates
    if any(song["title"].lower() == name.lower() for song in songs):
        return

    song_entry = {
        "title": name,
        "filename": os.path.basename(filename),
        "duration": duration,
        "url": f"/music/{guild_id}/{os.path.basename(filename)}"
    }
    songs.append(song_entry)
    save_songs(guild_id, songs)


def generate_song_list_html(guild_id: int):
    songs = load_songs(guild_id)
    guild_folder = get_guild_music_folder(guild_id)
    html_path = os.path.join(guild_folder, "song_list.html")


    import urllib.parse

    song_items = ""
    for song in songs:
        song_items += f'''
        <div class="song-card">
            <img class="album-art" alt="Album Art" />
            <div class="song-info">
                <div class="song-title">{song["title"]}</div>
                <div class="song-duration">{song["duration"]}</div>
                <audio controls preload="none" style="width:100%;margin-top:6px;">
                    <source src="{song["url"]}" type="audio/mpeg">
                    Your browser does not support the audio element.
                </audio>
            </div>
        </div>
        '''

    html_content = f"""<!DOCTYPE html>
<html lang='en'>
<head>
    <meta charset='UTF-8'>
    <meta name='viewport' content='width=device-width, initial-scale=1.0'>
    <title>Song List - Guild {guild_id}</title>
    <style>
        body {{
            font-family: 'Segoe UI', Arial, sans-serif;
            background: #f7f7f7;
            color: #222;
            margin: 0;
            padding: 0;
        }}
        .container {{
            max-width: 900px;
            margin: 32px auto;
            background: #fff;
            border-radius: 12px;
            box-shadow: 0 2px 12px rgba(0,0,0,0.08);
            padding: 24px 12px;
        }}
        h1 {{
            color: #222;
            text-align: center;
            margin-bottom: 24px;
            font-size: 2em;
        }}
        .song-list {{
            display: flex;
            flex-wrap: wrap;
            gap: 16px;
            justify-content: center;
        }}
        .song-card {{
            background: #f3f3f3;
            border-radius: 8px;
            box-shadow: 0 1px 4px rgba(0,0,0,0.06);
            padding: 10px 8px;
            width: 160px;
            display: flex;
            flex-direction: column;
            align-items: center;
        }}
        .album-art {{
            width: 48px;
            height: 48px;
            border-radius: 6px;
            margin-bottom: 8px;
            background: #e0e0e0;
            object-fit: cover;
        }}
        .song-info {{
            width: 100%;
            text-align: center;
        }}
        .song-title {{
            color: #222;
            font-size: 1em;
            font-weight: 500;
            margin-bottom: 2px;
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
        }}
        .song-duration {{
            color: #666;
            font-size: 0.95em;
            margin-bottom: 2px;
        }}
        audio {{
            width: 100%;
        }}
        @media (max-width: 600px) {{
            .container {{
                padding: 8px 2px;
            }}
            .song-card {{
                width: 98vw;
                min-width: 0;
            }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <h1>Song List - Guild {guild_id}</h1>
        <div class="song-list">
            {song_items if song_items else '<div style="text-align:center;color:#bbb;font-size:1.1em;">No songs yet.</div>'}
        </div>
    </div>
</body>
</html>
"""
    with open(html_path, "w", encoding="utf-8") as f:
        f.write(html_content)
    return html_path


import os
import platform
import urllib.request
import tarfile

def download_file(url, dest_path):
    if not os.path.exists(dest_path):
        print(f"Downloading {os.path.basename(dest_path)}...")
        try:
            urllib.request.urlretrieve(url, dest_path)
            print(f"Saved to {dest_path}")
        except Exception as e:
            print(f"[ERROR] Failed to download {dest_path}: {e}")
            raise

def extract_ffmpeg_tar(archive_path, extract_dir):
    print(f"Extracting {archive_path} to {extract_dir}")
    with tarfile.open(archive_path, 'r:xz') as tar:
        tar.extractall(path=extract_dir)
    print("Extraction complete.")

# Platform check
system_platform = platform.system().lower()  # 'windows', 'linux', 'darwin'
ffmpeg_dir = resource_path("ffmpeg-7.1.1")
os.makedirs(ffmpeg_dir, exist_ok=True)

if system_platform == "windows":
    ffmpeg_exec = "ffmpeg.exe"
    ffprobe_exec = "ffprobe.exe"
    ffmpeg_url = "https://github.com/ToastyKitsu/equired_dlls/releases/download/dlls/ffmpeg.exe"
    ffprobe_url = "https://github.com/ToastyKitsu/equired_dlls/releases/download/dlls/ffprobe.exe"

    ffmpeg_path = os.path.join(ffmpeg_dir, ffmpeg_exec)
    ffprobe_path = os.path.join(ffmpeg_dir, ffprobe_exec)

    download_file(ffmpeg_url, ffmpeg_path)
    download_file(ffprobe_url, ffprobe_path)


else:  # Assume Linux
    ffmpeg_exec = "ffmpeg"
    ffprobe_exec = "ffprobe"
    ffmpeg_tar_url = "https://johnvansickle.com/ffmpeg/releases/ffmpeg-release-amd64-static.tar.xz"
    ffmpeg_tar_path = os.path.join(ffmpeg_dir, "ffmpeg.tar.xz")

    download_file(ffmpeg_tar_url, ffmpeg_tar_path)
    extract_ffmpeg_tar(ffmpeg_tar_path, ffmpeg_dir)

    # Locate extracted ffmpeg & ffprobe
    extracted_bin_dir = None
    for root, dirs, files in os.walk(ffmpeg_dir):
        if ffmpeg_exec in files and ffprobe_exec in files:
            extracted_bin_dir = root
            break

    if not extracted_bin_dir:
        raise FileNotFoundError("Could not find ffmpeg binaries in extracted archive.")

    ffmpeg_path = os.path.join(extracted_bin_dir, ffmpeg_exec)
    ffprobe_path = os.path.join(extracted_bin_dir, ffprobe_exec)

# Make binaries executable
for f in (ffmpeg_path, ffprobe_path):
    os.chmod(f, os.stat(f).st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)

# Bot setup
TOKEN = os.getenv('DISCORD_TOKEN')
if not TOKEN:
    raise ValueError("DISCORD_TOKEN not found in environment")

intents = discord.Intents.default()
intents.message_content = True
intents.guilds = True
bot = commands.Bot(command_prefix='!', intents=intents)
queues = {}

class AudioTrack:
    def __init__(self, source, title, duration, filename=None):
        self.source = source
        self.title = title
        self.duration = duration
        self.filename = filename if filename else (title + ".mp3")

class MusicPlayer:
    def __init__(self, ctx):
        self.ctx = ctx
        self.queue = []        # Tracks waiting to play
        self.current = None
        self.status_task = None
        self.start_time = None
        self.preloaded = {}    # guild_id → AudioTrack source cache
        queues[ctx.guild.id] = self

    async def preload_next(self):
        """Preload the next track in the queue."""
        if not self.queue:
            return  # nothing to preload

        next_track = self.queue[0]  # peek at the next track

        # Try to get a valid file path attribute
        track_path_attr = getattr(next_track, 'file_path', None) or getattr(next_track, 'filename', None)
        if not track_path_attr:
            raise AttributeError("Next track object has no valid file path ('file_path' or 'filename')")

        # Construct the full path in the guild's music folder
        music_folder = get_guild_music_folder(self.ctx.guild.id)
        full_path = os.path.join(music_folder, track_path_attr)

        # Check if file exists before preloading
        if not os.path.isfile(full_path):
            raise FileNotFoundError(f"Audio file not found: {full_path}")

        # Preload logic (depends on your bot's player)
        self.next_audio_source = full_path  # for example, store the path for next playback
        logging.info(f"Preloaded next track: {full_path}")


    async def update_status(self):
        while self.ctx.voice_client and self.ctx.voice_client.is_playing():
            if self.current and self.start_time:
                elapsed = (discord.utils.utcnow() - self.start_time).total_seconds()
                mins, secs = divmod(int(elapsed), 60)
                await bot.change_presence(activity=discord.Game(name=f"{self.current.title} [{mins}:{secs:02d}/{self.current.duration}]"))
            await asyncio.sleep(1)

    async def play_next(self):
        if not self.queue or not self.ctx.voice_client:
            await bot.change_presence(activity=None)
            return

        # Use preloaded track if available
        next_track = self.queue.pop(0)
        self.current = self.preloaded.pop(next_track.title, next_track)
        self.start_time = discord.utils.utcnow()

        logger.info(f"Now playing: '{self.current.title}' | Duration: {self.current.duration} | Guild: {self.ctx.guild.name} ({self.ctx.guild.id})")

        if self.status_task:
            self.status_task.cancel()
        self.status_task = asyncio.create_task(self.update_status())

        def after_playing(error):
            if error:
                logger.error(f"Error playing '{self.current.title}': {error}")
            try:
                asyncio.run_coroutine_threadsafe(self.play_next(), bot.loop)
            except RuntimeError as e:
                logger.error(f"Async error: {e}")

        self.ctx.voice_client.play(self.current.source, after=after_playing)

        # Preload next track automatically
        await self.preload_next()


import string
import random
import json
import os

# File to store activation codes and activated servers
ACTIVATION_FILE = resource_path("activations.json")

# Load or create activations data
if not os.path.exists(ACTIVATION_FILE):
    with open(ACTIVATION_FILE, "w") as f:
        json.dump({"codes": {}, "servers": {}}, f)

def load_activations():
    with open(ACTIVATION_FILE, "r", encoding="utf-8") as f:
        return json.load(f)

def save_activations(data):
    with open(ACTIVATION_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=4)

def generate_activation_code(length=8):
    chars = string.ascii_uppercase + string.digits
    return "-".join("".join(random.choices(chars, k=4)) for _ in range(length // 4))

# --- Storage Limit (20 GB per guild) ---
MAX_STORAGE_BYTES = 20 * 1024 * 1024 * 1024  # 20 GB

def get_guild_storage_used(guild_id: int) -> int:
    """Return total size in bytes of all files in the guild's music folder."""
    total = 0
    music_dir = get_guild_music_folder(guild_id)
    for root, _, files in os.walk(music_dir):
        for f in files:
            try:
                total += os.path.getsize(os.path.join(root, f))
            except FileNotFoundError:
                continue
    return total


# Command categories and descriptions
command_categories = {
    'General': {
        'on': 'Activate the bot for this server using a code.',
        'help2': 'Shows this help message.',
        'tech': 'Send a message to tech support.'
    },
    'Music': {
        'join': 'Join your voice channel.',
        'leave': 'Leave the voice channel.',
        'play': 'Play a song by name.',
        'pause': 'Pause the current song.',
        'resume': 'Resume paused playback.',
        'stop': 'Stop playback and disconnect.',
        'skip': 'Skip the current song.',
        'np': 'Show the currently playing song.',
        'volume': 'Set or show the playback volume (0-100).',
        'queue': 'Show the current music queue.',
        'clear': 'Clear the current music queue.',
        'shuffle': 'Shuffle the current queue.',
        'add': 'Add MP3 songs by attaching files.',
        'rmsong': 'Remove a song from the server.',
        'songs': 'List all available songs.',
        'storage': 'Show current storage usage vs. limit.'
    },
    'Playlists': {
        'savepl': 'Save the current queue as a playlist.',
        'loadpl': 'Load a playlist into the queue.',
        'playlists': 'List all saved playlists.',
        'delpl': 'Delete a saved playlist.'
    },
    'Permissions': {
        'custom': 'Customize command permissions for roles.',
        'rmrole': 'Remove a role from command permissions.',
        'perms': 'Show custom command permissions.',
        'gencode': 'Generate activation codes (admin only).'
    },
    'Queue': {
        'rmq': 'Remove a song from the queue by index.'
    },
    'Moderation': {
        'muteduration': 'Change mute duration for AutoMod.',
        'banword': 'Add, remove, or list banned words for AutoMod.',
        'spam': 'Enable or disable spam protection.',
        'automoda': 'Enable or disable AutoMod entirely.',
        'automodstatus': 'Show current AutoMod settings.',
        'setmodlog': 'Set the moderation log channel.'
    }
}



# Events & Commands
@bot.event
@log_exceptions
async def on_ready():
    print(f"Logged in as {bot.user}")
    logger.info(f"Logged in as {bot.user}")


@bot.command(name='join')
@log_exceptions
@log_command_execution
@command_requires_permission("join")
async def join_command(ctx):
    if ctx.author.voice:
        await ctx.author.voice.channel.connect()
    else:
        await ctx.send("You must be in a voice channel.")


@bot.command(name='leave')
@log_exceptions
@log_command_execution
@command_requires_permission("leave")
async def leave_command(ctx):
    vc = ctx.voice_client
    if vc:
        await vc.disconnect()
        queues.pop(ctx.guild.id, None)
        await ctx.send("Disconnected.")
    else:
        await ctx.send("Not connected.")

@bot.command(name="help2")
async def help2_command(ctx):
    embed = discord.Embed(title="Bot Commands", color=0x00ffcc)
    for category, commands_dict in command_categories.items():
        desc = ""
        for cmd, help_text in commands_dict.items():
            desc += f"!{cmd}: {help_text}\n"
        if desc:
            embed.add_field(name=category, value=desc, inline=False)
    await ctx.send(embed=embed)

@bot.command(name='play')
@log_exceptions
@log_command_execution
@command_requires_permission("play")
async def play_command(ctx, filename: str = None):

    if not ctx.author.voice:
        return await ctx.send("You must be in a voice channel.")

    # Ensure a MusicPlayer exists
    if ctx.guild.id not in queues:
        queues[ctx.guild.id] = MusicPlayer(ctx)
    player = queues[ctx.guild.id]

    music_dir = get_guild_music_folder(ctx.guild.id)

    # If no filename provided, try default song
    if not filename:
        default_song = "test108.mp3"  # change as needed
        path = os.path.join(music_dir, default_song)
        if not os.path.exists(path):
            return await ctx.send("No song specified, and default song not found.")
        files = [default_song]
    else:
        files = [f for f in os.listdir(music_dir)
                 if f.lower().endswith('.mp3') and filename.lower() in f.lower()]
        if not files:
            return await ctx.send("No match.")
        path = os.path.join(music_dir, files[0])

    # Get duration
    try:
        res = subprocess.run([ffprobe_path, '-v', 'error', '-show_entries', 'format=duration',
                              '-of', 'default=noprint_wrappers=1:nokey=1', path],
                             capture_output=True, text=True)
        duration_sec = float(res.stdout.strip())
        mins, secs = divmod(int(duration_sec), 60)
        dur = f"{mins}:{secs:02d}"
    except Exception:
        dur = "?:??"

# Example inside play_command:
    source = discord.FFmpegPCMAudio(
        path,
        executable=ffmpeg_path,
        before_options='-nostdin',
        options='-f s16le -ar 48000 -ac 2 -loglevel quiet'
    )

    # Apply guild volume
    volume = get_guild_volume(ctx.guild.id)
    source = PCMVolumeTransformer(source, volume=volume)


    track = AudioTrack(source, os.path.splitext(files[0])[0], dur, filename=files[0])

    # Connect if not connected
    if not ctx.voice_client:
        await ctx.author.voice.channel.connect()

    # Queue the track
    player.queue.append(track)
    await player.preload_next()  # preload next track

    # Play if nothing is playing
    if not ctx.voice_client.is_playing():
        await player.play_next()

    await ctx.send(f"Queued {track.title}")

@bot.command(name="on")
@log_exceptions
@log_command_execution
async def activate_command(ctx, code: str):
    activations = load_activations()
    code = code.upper()
    
    if code not in activations["codes"]:
        return await ctx.send(" Invalid activation code.")
    
    if activations["codes"][code]:
        return await ctx.send(" This code has already been used.")
    
    # Link this server to the code
    activations["codes"][code] = ctx.guild.id
    activations["servers"][str(ctx.guild.id)] = code
    save_activations(activations)
    
    await ctx.send(f" Bot successfully activated for this server with code `{code}`!")

def activated_only(func):
    @functools.wraps(func)
    async def wrapper(ctx, *args, **kwargs):
        activations = load_activations()
        if str(ctx.guild.id) not in activations["servers"]:
            return await ctx.send(
                " Your server is not activated. Use `!activate <code>` from your purchase."
            )
        return await func(ctx, *args, **kwargs)
    return wrapper

# --- Direct-to-tech messaging ---
SUPPORT_USER_IDS = [1285025702231670795, 640466353991581697]  # multiple support users

@bot.command(name="tech")
@log_exceptions
@log_command_execution
async def tech_support(ctx, *, message: str = None):
    if not message:
        return await ctx.send(" Please provide a message to send to tech support.")

    forwarded_line = f"{ctx.author} ({ctx.author.id}) - {message}"

    sent_to = []
    failed_to = []

    for support_id in SUPPORT_USER_IDS:
        try:
            tech_user = await bot.fetch_user(int(support_id))
            if not tech_user:
                failed_to.append(str(support_id))
                continue

            await tech_user.send(forwarded_line)
            sent_to.append(str(support_id))
        except discord.Forbidden:
            failed_to.append(str(support_id))
        except Exception as e:
            failed_to.append(f"{support_id} ({type(e).__name__}: {e})")

    if sent_to:
        await ctx.send(f" Message sent to support tech support")
    if failed_to:
        await ctx.send(f" Could not deliver to tech support")
        
@bot.command(name="songs")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("songs")
async def songs_command(ctx):
    music_dir = get_guild_music_folder(ctx.guild.id)
    files = [f for f in os.listdir(music_dir) if f.endswith(".mp3")]
    if not files:
        return await ctx.send(" No songs available.")

    # Generate secure token
    token = secrets.token_urlsafe(16)
    active_tokens[ctx.guild.id] = {"token": token, "expires": time.time() + 300}  # 5 min expiry

    await ctx.send(
        f"{len(files)} songs available.\n"
        f"View here: {public_url}/music/{ctx.guild.id}/song_list.html?token={token}\n"
        f"(link expires in 5 minutes)"
    )



@bot.command(name='add')
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("add")
async def addsong_command(ctx):

    if not ctx.message.attachments:
        return await ctx.send("Please attach MP3 files.")

    music_dir = get_guild_music_folder(ctx.guild.id)
    added, skipped = [], []

    for attachment in ctx.message.attachments:
        if not attachment.filename.lower().endswith(".mp3"):
            skipped.append(attachment.filename)
            continue

        dest_path = os.path.join(music_dir, attachment.filename)

        # Check storage before saving
        current_size = get_guild_storage_used(ctx.guild.id)
        if current_size + attachment.size > MAX_STORAGE_BYTES:
            await ctx.send(f"Cannot add `{attachment.filename}` – "
                           f"20 GB storage limit reached for this server.")
            skipped.append(attachment.filename)
            continue

        try:
            await attachment.save(dest_path)
            add_song_to_json(ctx.guild.id, dest_path)
            added.append(attachment.filename)
        except Exception as e:
            logger.error(f"Failed to save {attachment.filename}: {e}")
            skipped.append(attachment.filename)

    # Regenerate HTML
    generate_song_list_html(ctx.guild.id)

    msg = ""
    if added:
        msg += f"Added songs: {', '.join(added)}\n🔗 {public_url}/music/{ctx.guild.id}/song_list.html"
    if skipped:
        msg += f"\n Skipped: {', '.join(skipped)}"
    if not msg:
        msg = "No songs were added."
    await ctx.send(msg)

@bot.command(name="storage")
@activated_only
@log_exceptions
@log_command_execution
async def storage_command(ctx):
    """Show current guild storage usage vs. limit."""
    used = get_guild_storage_used(ctx.guild.id)
    limit = MAX_STORAGE_BYTES

    # Convert to GB with 2 decimal places
    used_gb = used / (1024**3)
    limit_gb = limit / (1024**3)

    percent = (used / limit) * 100 if limit > 0 else 0

    await ctx.send(
        f"Storage used: **{used_gb:.2f} GB** / {limit_gb:.0f} GB "
        f"({percent:.1f}%)"
    )

@bot.command(name='rmsong')
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("rmsong")
async def remove_song_command(ctx, *, partial_title: str):
    guild_id = ctx.guild.id
    songs = load_songs(guild_id)
    matches = [s for s in songs if partial_title.lower() in s['title'].lower()]

    if not matches:
        return await ctx.send(f"No songs found matching `{partial_title}`.")

    # If only one match, remove it directly
    if len(matches) == 1:
        song = matches[0]
        file_path = os.path.join(get_guild_music_folder(guild_id), song['filename'])
        if os.path.exists(file_path):
            os.remove(file_path)

        songs = [s for s in songs if s['title'] != song['title']]
        save_songs(guild_id, songs)
        generate_song_list_html(guild_id)

        await ctx.send(f"Removed `{song['title']}`.\n🔗 {public_url}/music/{guild_id}/song_list.html")
        return

    # Multiple matches: list them
    msg = "Multiple songs found:\n"
    for i, s in enumerate(matches, 1):
        msg += f"{i}. {s['title']}\n"
    msg += "Reply with the number of the song to remove (within 30s)."
    await ctx.send(msg)

    def check(m):
        return m.author == ctx.author and m.channel == ctx.channel

    try:
        reply = await bot.wait_for('message', check=check, timeout=30.0)
        choice = int(reply.content)
        if 1 <= choice <= len(matches):
            song = matches[choice - 1]
            file_path = os.path.join(get_guild_music_folder(guild_id), song['filename'])
            if os.path.exists(file_path):
                os.remove(file_path)

            songs = [s for s in songs if s['title'] != song['title']]
            save_songs(guild_id, songs)
            generate_song_list_html(guild_id)

            await ctx.send(f"Removed `{song['title']}`.\n🔗 {public_url}/music/{guild_id}/song_list.html")
        else:
            await ctx.send("Invalid selection.")
    except (asyncio.TimeoutError, ValueError):
        await ctx.send("Cancelled removal.")

@bot.command(name="custom")
@activated_only
@log_exceptions
@log_command_execution
async def customize_command(ctx, role: discord.Role, command_name: str):
    if not ctx.author.guild_permissions.administrator:
        return await ctx.send("Only admins can customize command roles.")

    command_name = command_name.lower()
    guild_id = ctx.guild.id
    settings = load_settings(guild_id)

    if "command_roles" not in settings:
        settings["command_roles"] = {}

    if command_name not in settings["command_roles"]:
        settings["command_roles"][command_name] = []

    if role.id in settings["command_roles"][command_name]:
        return await ctx.send(f" `{role.name}` already has permission for `{command_name}`.")

    settings["command_roles"][command_name].append(role.id)
    save_settings(guild_id, settings)

    await ctx.send(f" Role `{role.name}` **added** to allowed list for `{command_name}`.")

@bot.command(name="rmrole")
@activated_only
@log_exceptions
@log_command_execution
async def remove_role_command(ctx, role: discord.Role, command_name: str):
    if not ctx.author.guild_permissions.administrator:
        return await ctx.send(" Only admins can remove command roles.")

    command_name = command_name.lower()
    guild_id = ctx.guild.id
    settings = load_settings(guild_id)

    roles = settings.get("command_roles", {}).get(command_name)
    if not roles or role.id not in roles:
        return await ctx.send(f" `{role.name}` does not have permission for `{command_name}`.")

    settings["command_roles"][command_name] = [r for r in roles if r != role.id]
    if not settings["command_roles"][command_name]:
        del settings["command_roles"][command_name]  # Optional: remove key if empty

    save_settings(guild_id, settings)
    await ctx.send(f" Removed `{role.name}` from `{command_name}` permission list.")


@bot.command(name="perms")
@activated_only
@log_exceptions
@log_command_execution
async def show_permissions(ctx):
    settings = load_settings(ctx.guild.id)
    command_roles = settings.get("command_roles", {})
    if not command_roles:
        return await ctx.send("No command permissions customized.")

    lines = []
    for cmd, role_ids in command_roles.items():
        roles = [ctx.guild.get_role(rid).mention for rid in role_ids if ctx.guild.get_role(rid)]
        lines.append(f"`{cmd}` → {', '.join(roles) if roles else ' Unknown role(s)'}")

    await ctx.send(" **Custom Command Permissions:**\n" + "\n".join(lines))

@bot.command(name='pause')
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("pause")
async def pause_command(ctx):
    vc = ctx.voice_client
    if vc and vc.is_playing():
        vc.pause()
        await ctx.send("Paused playback.")
    else:
        await ctx.send("Nothing is playing.")



@bot.command(name='resume')
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("resume")
async def resume_command(ctx):
    vc = ctx.voice_client
    if vc and vc.is_paused():
        vc.resume()
        await ctx.send("Resumed playback.")
    else:
        await ctx.send("Nothing is paused.")

@bot.command(name="skip")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("skip")
async def skip_command(ctx):
    player = queues.get(ctx.guild.id)
    if player and ctx.voice_client and ctx.voice_client.is_playing():
        ctx.voice_client.stop()
        await ctx.send("Skipping song...")
    else:
        await ctx.send("Nothing is playing.")


@bot.command(name='stop')
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("stop")
async def stop_command(ctx): 
    player = queues.get(ctx.guild.id)
    if player and ctx.voice_client:
        player.queue.clear()
        player.current = None
        if player.status_task:
            player.status_task.cancel()
        await bot.change_presence(activity=None)
        await ctx.voice_client.disconnect()
        await ctx.send(" Music stopped and bot disconnected.")
    else:
        await ctx.send("Nothing is playing.")

@bot.command(name="gencode")
@log_exceptions
@log_command_execution
async def generate_code(ctx, number: int = 1):
    # Only allow you or specific IDs to generate codes
    ADMIN_IDS = [1285025702231670795]  # Replace with your Discord ID
    if ctx.author.id not in ADMIN_IDS:
        return await ctx.send(" You are not allowed to generate codes.")

    activations = load_activations()
    codes = []

    for _ in range(number):
        code = generate_activation_code()
        activations["codes"][code] = None
        codes.append(code)

    save_activations(activations)
    await ctx.send(f" Generated code(s): `{', '.join(codes)}`")

@bot.command(name="volume")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("volume")
async def volume_command(ctx, vol: int = None):
    """Set or view playback volume (0–200%)."""
    if not ctx.voice_client:
        return await ctx.send(" Bot is not connected to a voice channel.")

    # Show current
    if vol is None:
        current = int(get_guild_volume(ctx.guild.id) * 100)
        return await ctx.send(f" Current volume: {current}%")

    # Validate
    if not 0 <= vol <= 100:
        return await ctx.send(" Volume must be between 0 and 100.")

    new_volume = vol / 100.0
    set_guild_volume(ctx.guild.id, new_volume)

    # Apply live if something is playing
    if ctx.voice_client.source and isinstance(ctx.voice_client.source, PCMVolumeTransformer):
        ctx.voice_client.source.volume = new_volume

    await ctx.send(f" Volume set to {vol}%")

# =====================
# Moderation Logging & AutoMod
# =====================

MODLOG_CHANNEL_NAME = None
AUTOMOD_MUTE_ROLE = "Muted"

# Ensure intents
intents.members = True
intents.guilds = True
intents.messages = True
intents.message_content = True

# ---------------------
# Helpers
# ---------------------
async def get_modlog_channel(guild: discord.Guild):
    """Get or create the guild's mod-log channel (configurable)."""
    settings = load_settings(guild.id)
    channel_id = settings.get("modlog_channel")

    # Try configured channel first
    if channel_id:
        channel = guild.get_channel(channel_id)
        if channel:
            return channel

    # If no default name is set, just stop
    if MODLOG_CHANNEL_NAME is None:
        return None

    # Fallback: default channel by name
    channel = discord.utils.get(guild.text_channels, name=MODLOG_CHANNEL_NAME)
    if channel is None:
        overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=False),
            guild.me: discord.PermissionOverwrite(view_channel=True)
        }
        channel = await guild.create_text_channel(MODLOG_CHANNEL_NAME, overwrites=overwrites)

    # Save channel ID to settings
    settings["modlog_channel"] = channel.id
    save_settings(guild.id, settings)
    return channel


def get_automod_settings(guild_id: int) -> dict:
    settings = load_settings(guild_id)
    automod = settings.get("automod")

    # Always enforce dict structure
    if not isinstance(automod, dict):
        automod = {}

    # Fill defaults if missing
    automod.setdefault("enabled", False)
    automod.setdefault("spam_protection", False)
    automod.setdefault("banned_words", [])
    automod.setdefault("mute_duration", 60)

    # Save back in case it was corrupted
    settings["autmodlog_channel"] = automod
    save_settings(guild_id, settings)

    return automod
    settings = load_settings(guild_id)
    automod = settings.get("automod")

    # Fix if automod is missing or corrupted
    if not isinstance(automod, dict):
        automod = {
            "enabled": False,
            "spam_protection": False,
            "banned_words": [],
            "mute_duration": 60
        }
        settings["automod"] = automod
        save_settings(guild_id, settings)

    return automod


def save_automod_settings(guild_id: int, automod_settings: dict):
    settings = load_settings(guild_id)
    settings["automod"] = automod_settings
    save_settings(guild_id, settings)

# ---------------------
# Command to set mod-log channel
# ---------------------
@bot.command(name="setmodlog")
async def set_modlog(ctx, channel: discord.TextChannel):
    if not ctx.author.guild_permissions.administrator:
        return await ctx.send(" Admin only.")
    settings = load_settings(ctx.guild.id)
    settings["modlog_channel"] = channel.id  # <-- FIXED
    save_settings(ctx.guild.id, settings)
    await ctx.send(f"Moderation logs will now be sent to {channel.mention}")

# =====================
# Moderation Logging (Dyno-style plain text)
# =====================

# --- Member events ---
# =====================
# Moderation Logging (Dyno-style, no emojis)
# =====================

# =====================
# Moderation Logging (Dyno-style)
# =====================

async def fetch_audit(guild, action, target_id=None):
    """Fetch the latest audit log entry for a given action and optional target."""
    await asyncio.sleep(2)  # wait for audit logs to update
    try:
        async for entry in guild.audit_logs(action=action, limit=5):
            if target_id is None or entry.target.id == target_id:
                return entry
    except Exception:
        return None
    return None

# --- Member join/leave ---
@bot.event
async def on_member_join(member):
    channel = await get_modlog_channel(member.guild)
    await channel.send(f"{member} joined the server.")

@bot.event
async def on_member_remove(member):
    guild = member.guild
    channel = await get_modlog_channel(guild)

    # Check if kicked
    entry = await fetch_audit(guild, discord.AuditLogAction.kick, member.id)
    if entry:
        return await channel.send(f"{member} was kicked by {entry.user}. Reason: {entry.reason or 'No reason provided'}")

    await channel.send(f"{member} left the server.")

# --- Nickname, roles, timeout ---
@bot.event
async def on_member_update(before, after):
    channel = await get_modlog_channel(after.guild)

    # Timeout changes
    if before.communication_disabled_until != after.communication_disabled_until:
        entry = await fetch_audit(after.guild, discord.AuditLogAction.member_update, after.id)
        if after.communication_disabled_until:  # timeout added
            await channel.send(
                f"{after} was timed out by {entry.user if entry else 'Unknown'} "
                f"until {after.communication_disabled_until}. "
                f"Reason: {entry.reason if entry else 'No reason provided'}"
            )
        else:
            await channel.send(f"{after}'s timeout was removed.")

    # Nickname changes
    if before.nick != after.nick:
        old_nick = before.nick or before.name
        new_nick = after.nick or after.name
        entry = await fetch_audit(after.guild, discord.AuditLogAction.member_update, after.id)
        if entry:
            await channel.send(
                f"Nickname changed for {after}: {old_nick} → {new_nick} "
                f"(by {entry.user}; Reason: {entry.reason or 'No reason provided'})"
            )
        else:
            await channel.send(f"Nickname changed for {after}: {old_nick} → {new_nick}")

    # Role changes
    if before.roles != after.roles:
        added = [r.name for r in after.roles if r not in before.roles]
        removed = [r.name for r in before.roles if r not in after.roles]
        entry = await fetch_audit(after.guild, discord.AuditLogAction.member_role_update, after.id)
        if added:
            await channel.send(f"{after} gained role(s): {', '.join(added)} (by {entry.user if entry else 'Unknown'})")
        if removed:
            await channel.send(f"{after} lost role(s): {', '.join(removed)} (by {entry.user if entry else 'Unknown'})")

# --- Bans / Unbans ---
@bot.event
async def on_member_ban(guild, user):
    channel = await get_modlog_channel(guild)
    entry = await fetch_audit(guild, discord.AuditLogAction.ban, user.id)
    if entry:
        await channel.send(f"{user} was banned by {entry.user}. Reason: {entry.reason or 'No reason provided'}")
    else:
        await channel.send(f"{user} was banned from the server.")

@bot.event
async def on_member_unban(guild, user):
    channel = await get_modlog_channel(guild)
    entry = await fetch_audit(guild, discord.AuditLogAction.unban, user.id)
    if entry:
        await channel.send(f"{user} was unbanned by {entry.user}.")
    else:
        await channel.send(f"{user} was unbanned from the server.")

# --- Channel changes ---
@bot.event
async def on_guild_channel_create(channel):
    log = await get_modlog_channel(channel.guild)
    entry = await fetch_audit(channel.guild, discord.AuditLogAction.channel_create, channel.id)
    if entry:
        await log.send(f"Channel created: {channel.mention} (by {entry.user})")
    else:
        await log.send(f"Channel created: {channel.mention}")

@bot.event
async def on_guild_channel_delete(channel):
    log = await get_modlog_channel(channel.guild)
    entry = await fetch_audit(channel.guild, discord.AuditLogAction.channel_delete, channel.id)
    if entry:
        await log.send(f"Channel deleted: {channel.name} (by {entry.user})")
    else:
        await log.send(f"Channel deleted: {channel.name}")

@bot.event
async def on_guild_channel_update(before, after):
    log = await get_modlog_channel(after.guild)
    changes = []
    if before.name != after.name:
        changes.append(f"Name: {before.name} → {after.name}")
    if before.overwrites != after.overwrites:
        changes.append("Permissions updated")
    if hasattr(before, "topic") and before.topic != after.topic:
        changes.append(f"Topic: {before.topic} → {after.topic}")
    if changes:
        entry = await fetch_audit(after.guild, discord.AuditLogAction.channel_update, after.id)
        if entry:
            await log.send("Channel updated by {}:\n{}".format(entry.user, "\n".join(changes)))
        else:
            await log.send("Channel updated:\n" + "\n".join(changes))

    channel = await get_modlog_channel(after.guild)

    # Timeout changes
    if before.communication_disabled_until != after.communication_disabled_until:
        entry = await fetch_audit(after.guild, discord.AuditLogAction.member_update, target_id=after.id)
        if after.communication_disabled_until:  # new timeout
            await channel.send(
                f"{after} was timed out by {entry.user if entry else 'Unknown'} "
                f"until {after.communication_disabled_until}. "
                f"Reason: {entry.reason if entry else 'No reason provided'}"
            )
        else:
            await channel.send(f"{after}'s timeout was removed.")

    # Nickname changes
    if before.nick != after.nick:
        try:
            entry = await after.guild.audit_logs(
                action=discord.AuditLogAction.member_update,
                limit=1
            ).find(lambda e: e.target.id == after.id and e.changes.before.get("nick") != e.changes.after.get("nick"))
        except Exception:
            entry = None

        old_nick = before.nick or before.name
        new_nick = after.nick or after.name

        if entry:
            await channel.send(
                f"Nickname changed for {after}: {old_nick} → {new_nick} "
                f"(by {entry.user}; Reason: {entry.reason or 'No reason provided'})"
            )
        else:
            await channel.send(f"Nickname changed for {after}: {old_nick} → {new_nick}")

    # Role changes
    if before.roles != after.roles:
        added = [r.name for r in after.roles if r not in before.roles]
        removed = [r.name for r in before.roles if r not in after.roles]
        entry = await fetch_audit(after.guild, discord.AuditLogAction.member_role_update, target_id=after.id)
        if added:
            await channel.send(f"{after} gained role(s): {', '.join(added)} (by {entry.user if entry else 'Unknown'})")
        if removed:
            await channel.send(f"{after} lost role(s): {', '.join(removed)} (by {entry.user if entry else 'Unknown'})")

# --- Ban / unban ---
@bot.event
async def on_member_ban(guild, user):
    channel = await get_modlog_channel(guild)
    entry = await fetch_audit(guild, discord.AuditLogAction.ban, target_id=user.id)
    await channel.send(
        f"{user} was banned by {entry.user if entry else 'Unknown'}. "
        f"Reason: {entry.reason if entry else 'No reason provided'}"
    )

@bot.event
async def on_member_unban(guild, user):
    channel = await get_modlog_channel(guild)
    entry = await fetch_audit(guild, discord.AuditLogAction.unban, target_id=user.id)
    await channel.send(
        f"{user} was unbanned by {entry.user if entry else 'Unknown'}."
    )

# --- Role events ---
@bot.event
async def on_guild_role_create(role):
    channel = await get_modlog_channel(role.guild)
    entry = await fetch_audit(role.guild, discord.AuditLogAction.role_create, target_id=role.id)
    await channel.send(
        f"Role created: {role.name} (by {entry.user if entry else 'Unknown'})"
    )

@bot.event
async def on_guild_role_delete(role):
    channel = await get_modlog_channel(role.guild)
    entry = await fetch_audit(role.guild, discord.AuditLogAction.role_delete, target_id=role.id)
    await channel.send(
        f"Role deleted: {role.name} (by {entry.user if entry else 'Unknown'})"
    )

@bot.event
async def on_guild_role_update(before, after):
    channel = await get_modlog_channel(after.guild)
    entry = await fetch_audit(after.guild, discord.AuditLogAction.role_update, target_id=after.id)
    changes = []
    if before.name != after.name:
        changes.append(f"Name: {before.name} → {after.name}")
    if before.permissions != after.permissions:
        changes.append("Permissions updated")
    if before.color != after.color:
        changes.append(f"Color: {before.color} → {after.color}")
    if changes:
        await channel.send(
            "Role updated:\n" + "\n".join(changes) +
            f"\n(by {entry.user if entry else 'Unknown'})"
        )

# --- Channel events ---
@bot.event
async def on_guild_channel_create(channel_obj):
    channel = await get_modlog_channel(channel_obj.guild)
    entry = await fetch_audit(channel_obj.guild, discord.AuditLogAction.channel_create, target_id=channel_obj.id)
    await channel.send(
        f"Channel created: {channel_obj.name} (by {entry.user if entry else 'Unknown'})"
    )

@bot.event
async def on_guild_channel_delete(channel_obj):
    channel = await get_modlog_channel(channel_obj.guild)
    entry = await fetch_audit(channel_obj.guild, discord.AuditLogAction.channel_delete, target_id=channel_obj.id)
    await channel.send(
        f"Channel deleted: {channel_obj.name} (by {entry.user if entry else 'Unknown'})"
    )

@bot.event
async def on_guild_channel_update(before, after):
    channel = await get_modlog_channel(after.guild)
    entry = await fetch_audit(after.guild, discord.AuditLogAction.channel_update, target_id=after.id)
    changes = []
    if before.name != after.name:
        changes.append(f"Name: {before.name} → {after.name}")
    if before.overwrites != after.overwrites:
        changes.append("Permissions updated")
    if hasattr(before, "topic") and before.topic != after.topic:
        changes.append(f"Topic: {before.topic} → {after.topic}")
    if changes:
        await channel.send(
            "Channel updated:\n" + "\n".join(changes) +
            f"\n(by {entry.user if entry else 'Unknown'})"
        )


# --- Emoji / sticker events ---
@bot.event
async def on_guild_emojis_update(guild, before, after):
    channel = await get_modlog_channel(guild)
    added = [e for e in after if e not in before]
    removed = [e for e in before if e not in after]
    if added:
        await channel.send("Emoji(s) added: " + ", ".join(str(e) for e in added))
    if removed:
        await channel.send("Emoji(s) removed: " + ", ".join(str(e) for e in removed))

@bot.event
async def on_guild_stickers_update(guild, before, after):
    channel = await get_modlog_channel(guild)
    added = [s for s in after if s not in before]
    removed = [s for s in before if s not in after]
    if added:
        await channel.send("Sticker(s) added: " + ", ".join(s.name for s in added))
    if removed:
        await channel.send("Sticker(s) removed: " + ", ".join(s.name for s in removed))

# --- Ban / unban events ---
@bot.event
async def on_member_ban(guild, user):
    channel = await get_modlog_channel(guild)
    await channel.send(f"{user} was banned from the server.")

@bot.event
async def on_member_unban(guild, user):
    channel = await get_modlog_channel(guild)
    await channel.send(f"{user} was unbanned from the server.")




# ---------------------
# AutoMod system
# ---------------------
spam_tracker = {}  # user_id -> [timestamps]

async def automod_mute(member: discord.Member, reason="AutoMod mute", duration=60):
    guild = member.guild
    role = discord.utils.get(guild.roles, name=AUTOMOD_MUTE_ROLE)
    if role is None:
        role = await guild.create_role(name=AUTOMOD_MUTE_ROLE)
        for channel in guild.channels:
            await channel.set_permissions(role, send_messages=False, speak=False)
    await member.add_roles(role, reason=reason)
    channel = await get_modlog_channel(guild)
    await channel.send(f"{member} muted for {duration}s ({reason}).")
    # Auto-unmute
    await asyncio.sleep(duration)
    if role in member.roles:
        await member.remove_roles(role, reason="Auto unmute")
        await channel.send(f" {member} has been unmuted.")

@bot.event
async def on_message(message):
    if message.author.bot:
        return

    #  Bypass AutoMod if user is mod/admin (Manage Messages or higher)
    if message.author.guild_permissions.manage_messages:
        return await bot.process_commands(message)

    s = get_automod_settings(message.guild.id)

    # Safety: force dict
    if not isinstance(s, dict):
        print(f"AutoMod settings corrupted for guild {message.guild.id}, repairing...")
        s = get_automod_settings(message.guild.id)  # This will rebuild defaults

    if not s.get("enabled", False):
        return await bot.process_commands(message)

    # Banned word filter
    if any(word in message.content.lower() for word in s.get("banned_words", [])):
        await message.delete()
        channel = await get_modlog_channel(message.guild)
        if channel:
            await channel.send(f"{message.author} used a banned word and was muted.")
        await automod_mute(message.author, reason="Banned word", duration=s.get("mute_duration", 60))
        return

    # Spam filter
    if s.get("spam_protection", False):
        now = time.time()
        history = spam_tracker.get(message.author.id, [])
        history = [t for t in history if now - t < 10]  # 10s window
        history.append(now)
        spam_tracker[message.author.id] = history

        if len(history) > 5:  # >5 messages in 10s
            channel = await get_modlog_channel(message.guild)
            if channel:
                await channel.send(f"{message.author} triggered spam detection and was muted.")
            await automod_mute(message.author, reason="Spam", duration=s.get("mute_duration", 60))
            spam_tracker[message.author.id] = []

    await bot.process_commands(message)

# ---------------------
# Admin Commands for AutoMod
# ---------------------
@bot.command(name="automoda")
async def automod_toggle(ctx, option: str):
    if not ctx.author.guild_permissions.administrator:
        return await ctx.send("Admin only.")
    s = get_automod_settings(ctx.guild.id)
    if option.lower() == "enable":
        s["enabled"] = True
        await ctx.send("AutoMod enabled.")
    elif option.lower() == "disable":
        s["enabled"] = False
        await ctx.send("AutoMod disabled.")
    else:
        return await ctx.send("Usage: `!automoda enable|disable`")
    save_automod_settings(ctx.guild.id, s)

@bot.command(name="spam")
async def spam_toggle(ctx, option: str):
    if not ctx.author.guild_permissions.administrator:
        return await ctx.send("Admin only.")
    s = get_automod_settings(ctx.guild.id)
    if option.lower() == "enable":
        s["spam_protection"] = True
        await ctx.send("Spam protection enabled.")
    elif option.lower() == "disable":
        s["spam_protection"] = False
        await ctx.send("Spam protection disabled.")
    else:
        return await ctx.send("Usage: `!spam enable|disable`")
    save_automod_settings(ctx.guild.id, s)

@bot.command(name="banword")
async def banword_command(ctx, action: str = None, word: str = None):
    if not ctx.author.guild_permissions.administrator:
        return await ctx.send("Admin only.")
    s = get_automod_settings(ctx.guild.id)

    if action == "add" and word:
        if word.lower() not in s["banned_words"]:
            s["banned_words"].append(word.lower())
            await ctx.send(f"Added banned word: `{word}`")
        else:
            await ctx.send(f"`{word}` already in banned list.")
    elif action == "remove" and word:
        if word.lower() in s["banned_words"]:
            s["banned_words"].remove(word.lower())
            await ctx.send(f"Removed banned word: `{word}`")
        else:
            await ctx.send(f"`{word}` not found in banned list.")
    elif action == "list":
        if not s["banned_words"]:
            await ctx.send("No banned words set.")
        else:
            await ctx.send(" **Banned words:** " + ", ".join(s["banned_words"]))
    else:
        return await ctx.send("Usage: `!banword add <word> | remove <word> | list`")

    save_automod_settings(ctx.guild.id, s)

@bot.command(name="muteduration")
async def mute_duration_command(ctx, seconds: int = None):
    if not ctx.author.guild_permissions.administrator:
        return await ctx.send(" Admin only.")
    if seconds is None or seconds <= 0:
        return await ctx.send("Usage: `!muteduration <seconds>`")
    s = get_automod_settings(ctx.guild.id)
    s["mute_duration"] = seconds
    save_automod_settings(ctx.guild.id, s)
    await ctx.send(f" Mute duration set to {seconds} seconds.")

@bot.command(name="automodstatus")
async def automod_status(ctx):
    """Show current AutoMod settings."""
    s = get_automod_settings(ctx.guild.id)
    banned = ", ".join(s["banned_words"]) if s["banned_words"] else "None"
    await ctx.send(
        f"🔧 **AutoMod Settings:**\n"
        f"Enabled: {s['enabled']}\n"
        f"Spam protection: {s['spam_protection']}\n"
        f"Mute duration: {s['mute_duration']}s\n"
        f"Banned words: {banned}"
    )




def start_gui():
    root = tk.Tk()
    root.title("Discord Bot Control Panel")
    frame = tk.LabelFrame(root, text="Logs")
    frame.pack(fill='both', expand=True, padx=5, pady=5)
    text = ScrolledText(frame, height=20, font=('Arial', 10))
    text.pack(fill='both', expand=True)

    log_path = resource_path('logs/discord_bot.log')
    last_log_content = ""

    def refresh_logs_periodically():
        nonlocal last_log_content
        try:
            with open(log_path, 'r', encoding='utf-8') as f:
                data = f.read()
            if data != last_log_content:
                text.delete('1.0', tk.END)
                text.insert(tk.END, data)
                text.see(tk.END)
                last_log_content = data
        except Exception as e:
            messagebox.showerror("Log Error", str(e))
        root.after(1000, refresh_logs_periodically)
    refresh_logs_periodically()
    root.mainloop()
    
# Start GUI and run bot
threading.Thread(target=start_gui, daemon=True).start()

# --- Start restricted web server and expose via Ngrok ---

# --- User authentication for /edit ---
UPLOAD_PATH = "/Music-Bot/main.py"
RESTART_SCRIPT = "/Music-Bot/restart.sh"

AUTHORIZED_USERS = {
    "admin": "ijwfo"  # example
}

class MyHandler(BaseHTTPRequestHandler):
    def _remote_ip(self):
        # self.client_address is (host, port)
        try:
            return self.client_address[0]
        except Exception:
            return "unknown"

    def _is_blocked(self, ip):
        entry = ip_failures.get(ip)
        if not entry:
            return False
        blocked_until = entry.get("blocked_until", 0)
        return time.time() < blocked_until

    def _record_failure(self, ip):
        now = time.time()
        entry = ip_failures.get(ip)
        if not entry:
            ip_failures[ip] = {"count": 1, "first_seen": now, "blocked_until": 0}
            return

        # reset window if window passed
        if now - entry["first_seen"] > WINDOW_SECONDS:
            entry["count"] = 1
            entry["first_seen"] = now
            entry["blocked_until"] = 0
        else:
            entry["count"] = entry.get("count", 0) + 1
            # Block if exceeded
            if entry["count"] > MAX_FAILED_PER_WINDOW:
                entry["blocked_until"] = now + BLOCK_SECONDS

    def _reset_failures(self, ip):
        if ip in ip_failures:
            del ip_failures[ip]

    def do_GET(self):
        decoded_path = urllib.parse.unquote(self.path)
        remote_ip = self._remote_ip()

        # If IP is currently blocked, return 429
        if self._is_blocked(remote_ip):
            self.send_response(429)
            self.send_header("Content-type", "text/plain")
            self.end_headers()
            self.wfile.write(b"Too many requests. Try again later.")
            return

        # === Login page ===
        if decoded_path == "/edit":
            self.send_response(200)
            self.send_header("Content-type", "text/html")
            self.end_headers()
            html = """
            <html>
            <head><title>Login</title></head>
            <body>
                <h2>Bot Control Login</h2>
                <form method="POST" action="/edit">
                    <label>User ID: <input type="text" name="userid" /></label><br><br>
                    <label>Password: <input type="password" name="password" /></label><br><br>
                    <input type="submit" value="Login" />
                </form>
            </body>
            </html>
            """
            self.wfile.write(html.encode("utf-8"))
            return

        # === Upload page ===
        elif decoded_path == "/upload":
            self.send_response(200)
            self.send_header("Content-type", "text/html")
            self.end_headers()
            html = """
            <html>
            <head><title>Upload main.py</title></head>
            <body>
                <h2>Upload New main.py</h2>
                <form method="POST" action="/upload" enctype="multipart/form-data">
                    <input type="file" name="file" /><br><br>
                    <input type="submit" value="Upload and Restart" />
                </form>
            </body>
            </html>
            """
            self.wfile.write(html.encode("utf-8"))
            return

        # === Serve music song list ONLY with token ===
        elif decoded_path.startswith("/music/"):
            try:
                parsed = urlparse(self.path)
                parts = parsed.path.strip("/").split("/")
                # Require exactly /music/<guild_id>/song_list.html
                if len(parts) < 3 or parts[2] != "song_list.html":
                    # Record failure and forbid any other music paths
                    self._record_failure(remote_ip)
                    self.send_error(403, "Forbidden")
                    return

                # parse guild id
                guild_id = int(parts[1])

                # Token validation
                params = parse_qs(parsed.query)
                token = params.get("token", [None])[0]
                entry = active_tokens.get(guild_id)

                if not entry or entry.get("token") != token or time.time() > entry.get("expires", 0):
                    # invalid/expired token → record failure and forbid
                    self._record_failure(remote_ip)
                    self.send_error(403, "Forbidden")
                    return

                # valid token → serve the file and reset failures for this IP
                file_path = os.path.normpath(os.path.join(get_guild_music_folder(guild_id), "song_list.html"))
                if not os.path.exists(file_path):
                    self.send_error(404, "Not Found")
                    return

                with open(file_path, "rb") as f:
                    self.send_response(200)
                    self.send_header("Content-type", "text/html")
                    self.send_header("ngrok-skip-browser-warning", "true")
                    self.end_headers()
                    self.wfile.write(f.read())

                # Optional: if you want tokens to be single-use, remove it after a successful serve:
                # del active_tokens[guild_id]

                # reset failure counters for the IP on success
                self._reset_failures(remote_ip)

            except ValueError:
                # guild id parse failed
                self._record_failure(remote_ip)
                self.send_error(403, "Forbidden")
            except FileNotFoundError:
                self.send_error(404, "File Not Found")
            except Exception as e:
                print("[ERROR] Serving music file failed:", e)
                self.send_error(500, "Internal Server Error")
            return

        # === All other paths ===
        else:
            self.send_error(404, "Not Found")

    def do_POST(self):
        decoded_path = urllib.parse.unquote(self.path)

        # Parse form data
        form = cgi.FieldStorage(
            fp=self.rfile,
            headers=self.headers,
            environ={'REQUEST_METHOD': 'POST',
                     'CONTENT_TYPE': self.headers.get('Content-Type')}
        )

        # === Handle login ===
        if decoded_path == "/edit":
            userid = form.getvalue("userid")
            password = form.getvalue("password")
            if not userid or not password or AUTHORIZED_USERS.get(userid) != password:
                self.send_response(401)
                self.send_header("Content-type", "text/html")
                self.end_headers()
                self.wfile.write(b"<h3>Invalid credentials</h3>")
                return

            # Login successful → redirect to /upload
            self.send_response(302)
            self.send_header("Location", "/upload")
            self.end_headers()
            return

        # === Handle file upload ===
        elif decoded_path == "/upload":
            if "file" not in form:
                self.send_error(400, "No file field provided")
                return
            file_item = form["file"]
            if not file_item.filename:
                self.send_error(400, "No file uploaded")
                return

            try:
                with open(UPLOAD_PATH, "wb") as f:
                    f.write(file_item.file.read())

                # Restart bot
                subprocess.Popen(["bash", RESTART_SCRIPT])

                self.send_response(200)
                self.send_header("Content-type", "text/html")
                self.end_headers()
                self.wfile.write(b"<h3>main.py uploaded successfully, bot restarting...</h3>")

            except Exception as e:
                self.send_error(500, f"Internal Server Error: {e}")
            return

        else:
            self.send_error(404, "Not Found")


PORT = 8000

def start_server():
    with HTTPServer(("0.0.0.0", PORT), MyHandler) as httpd:
        print("Serving restricted content on port", PORT)
        httpd.serve_forever()

# Start HTTP server in the background
threading.Thread(target=start_server, daemon=True).start()

# Start Ngrok tunnel and capture the public URL
public_url = ngrok.connect(PORT).public_url
print("Public URL:", public_url)

# Run the bot


# =====================
# Queue Management
# =====================
@bot.command(name="queue")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("queue")
async def queue_command(ctx):
    player = queues.get(ctx.guild.id)
    if not player or not player.queue:
        return await ctx.send("Queue is empty.")
    lines = []
    for i, track in enumerate(player.queue, start=1):
        lines.append(f"{i}. {track.title} ({track.duration})")
    await ctx.send("**Current Queue:**\n" + "\n".join(lines[:15]) + (f"\n… and {len(lines)-15} more." if len(lines) > 15 else ""))

@bot.command(name="np")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("np")
async def nowplaying_command(ctx):
    player = queues.get(ctx.guild.id)
    if not player or not player.current:
        return await ctx.send("Nothing is playing.")
    await ctx.send(f"Now playing: **{player.current.title}** ({player.current.duration})")

@bot.command(name="rmq")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("rmq")
async def removefromqueue_command(ctx, index: int):
    player = queues.get(ctx.guild.id)
    if not player or not player.queue:
        return await ctx.send(" Queue is empty.")
    if 1 <= index <= len(player.queue):
        removed = player.queue.pop(index-1)
        await ctx.send(f"Removed **{removed.title}** from queue.")
    else:
        await ctx.send("Invalid index.")

@bot.command(name="clear")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("clear")
async def clearqueue_command(ctx):
    player = queues.get(ctx.guild.id)
    if not player:
        return await ctx.send("Queue is already empty.")
    player.queue.clear()
    await ctx.send(" Cleared the queue.")

@bot.command(name="shuffle")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("shuffle")
async def shufflequeue_command(ctx):
    import random
    player = queues.get(ctx.guild.id)
    if not player or not player.queue:
        return await ctx.send(" Queue is empty.")
    random.shuffle(player.queue)
    await ctx.send("Queue shuffled.")

# =====================
# Playlist System
# =====================
def get_playlists_file(guild_id: int) -> str:
    return os.path.join(get_guild_music_folder(guild_id), "playlists.json")

def load_playlists(guild_id: int) -> dict:
    path = get_playlists_file(guild_id)
    if not os.path.exists(path):
        return {}
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def save_playlists(guild_id: int, playlists: dict):
    path = get_playlists_file(guild_id)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(playlists, f, indent=4)

@bot.command(name="savepl")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("savepl")
async def saveplaylist_command(ctx, name: str):
    player = queues.get(ctx.guild.id)
    if not player or not player.queue:
        return await ctx.send("Queue is empty, nothing to save.")
    playlists = load_playlists(ctx.guild.id)
    playlists[name] = [{"title": t.title, "duration": t.duration, "filename": t.title + ".mp3"} for t in player.queue]
    save_playlists(ctx.guild.id, playlists)
    await ctx.send(f"Saved current queue as playlist **{name}**.")

@bot.command(name="loadpl")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("loadpl")
async def loadplaylist_command(ctx, name: str):
    playlists = load_playlists(ctx.guild.id)
    if name not in playlists:
        return await ctx.send(f"No playlist named `{name}`.")
    music_dir = get_guild_music_folder(ctx.guild.id)
    tracks = []

    # Get saved guild volume (default 1.0 = 100%)
    volume = get_guild_volume(ctx.guild.id)

    for entry in playlists[name]:
        path = os.path.join(music_dir, entry["filename"])
        if not os.path.exists(path):
            continue
        try:
            res = subprocess.run(
                [ffprobe_path, '-v', 'error', '-show_entries', 'format=duration',
                 '-of', 'default=noprint_wrappers=1:nokey=1', path],
                capture_output=True, text=True
            )
            duration_sec = float(res.stdout.strip())
            mins, secs = divmod(int(duration_sec), 60)
            dur = f"{mins}:{secs:02d}"
        except Exception:
            dur = "?:??"

        # Create FFmpeg source and wrap in PCMVolumeTransformer
        raw_source = discord.FFmpegPCMAudio(
            path,
            executable=ffmpeg_path,
            before_options='-nostdin',
            options='-f s16le -ar 48000 -ac 2 -loglevel quiet'
        )
        source = discord.PCMVolumeTransformer(raw_source, volume=volume)

        tracks.append(AudioTrack(source, entry["title"], dur, filename=entry["filename"]))

    if ctx.guild.id not in queues:
        queues[ctx.guild.id] = MusicPlayer(ctx)
    player = queues[ctx.guild.id]
    player.queue.extend(tracks)

    await ctx.send(f" Loaded playlist **{name}** with {len(tracks)} track(s).")

    if not ctx.voice_client and tracks:
        await ctx.author.voice.channel.connect()
        await player.play_next()


@bot.command(name="playlists")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("playlists")
async def listplaylists_command(ctx):
    playlists = load_playlists(ctx.guild.id)
    if not playlists:
        return await ctx.send(" No playlists saved.")
    await ctx.send(" **Playlists:**\n" + ", ".join(playlists.keys()))

@bot.command(name="delpl")
@activated_only
@log_exceptions
@log_command_execution
@command_requires_permission("delpl")
async def deleteplaylist_command(ctx, name: str):
    playlists = load_playlists(ctx.guild.id)
    if name not in playlists:
        return await ctx.send(f" No playlist named `{name}`.")
    del playlists[name]
    save_playlists(ctx.guild.id, playlists)
    await ctx.send(f" Deleted playlist **{name}**.")

bot.run(TOKEN)
