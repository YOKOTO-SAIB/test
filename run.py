"""
============================================================
YOUTUBE AUTOMATION BOT V3.0 - COMPLETE SUITE
============================================================
Fitur Utama:
1. Web Dashboard HTML untuk Monitoring & Control
2. Multi-Account Management
3. Auto Proxy Rotation & Generation
4. Advanced Anti-Detection System
5. Human Behavior Simulation
6. Auto Recovery System
7. Real-time Monitoring Dashboard
8. API Endpoints untuk Remote Control
9. Database SQLite untuk Data Persistence
============================================================
"""

import pandas as pd
import numpy as np
import random
import time
import os
import json
import re
import requests
import logging
import sys
import hashlib
import sqlite3
import threading
import queue
import asyncio
import websockets
import socket
import subprocess
from datetime import datetime, timedelta
from typing import List, Dict, Optional, Tuple, Any
from dataclasses import dataclass, asdict
from enum import Enum
from pathlib import Path
from flask import Flask, render_template, jsonify, request, send_from_directory
from flask_socketio import SocketIO, emit
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.support.ui import WebDriverWait, Select
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.common.exceptions import TimeoutException, NoSuchElementException
from webdriver_manager.chrome import ChromeDriverManager
from fake_useragent import UserAgent
import undetected_chromedriver as uc
import schedule
import pickle
import base64
from io import BytesIO
from PIL import Image
import cv2
from bs4 import BeautifulSoup
import cloudscraper
from twocaptcha import TwoCaptcha
import qrcode
import pyotp

# ==================== SETUP FLASK APP ====================
app = Flask(__name__, 
            static_folder='static',
            template_folder='templates')
app.config['SECRET_KEY'] = 'youtube-automation-secret-key-2024'
socketio = SocketIO(app, cors_allowed_origins="*", async_mode='threading')

# ==================== DATABASE SETUP ====================
class Database:
    def __init__(self, db_path="youtube_bot.db"):
        self.db_path = db_path
        self.init_database()
    
    def init_database(self):
        """Initialize SQLite database with required tables"""
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()
        
        # Accounts table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS accounts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                email TEXT UNIQUE NOT NULL,
                password TEXT NOT NULL,
                recovery_email TEXT,
                proxy TEXT,
                status TEXT DEFAULT 'inactive',
                last_used DATETIME,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                subscribed_channels TEXT DEFAULT '[]',
                total_subscriptions INTEGER DEFAULT 0,
                notes TEXT
            )
        ''')
        
        # Channels table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS channels (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                url TEXT UNIQUE NOT NULL,
                name TEXT,
                category TEXT,
                status TEXT DEFAULT 'pending',
                total_subscribers INTEGER DEFAULT 0,
                last_checked DATETIME,
                notes TEXT
            )
        ''')
        
        # Tasks table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS tasks (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                account_id INTEGER,
                channel_id INTEGER,
                task_type TEXT,
                status TEXT,
                started_at DATETIME,
                completed_at DATETIME,
                duration REAL,
                result TEXT,
                error_message TEXT,
                screenshot_path TEXT,
                FOREIGN KEY (account_id) REFERENCES accounts (id),
                FOREIGN KEY (channel_id) REFERENCES channels (id)
            )
        ''')
        
        # Proxies table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS proxies (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                address TEXT UNIQUE NOT NULL,
                protocol TEXT,
                country TEXT,
                speed REAL,
                last_used DATETIME,
                failed_count INTEGER DEFAULT 0,
                success_count INTEGER DEFAULT 0,
                is_active BOOLEAN DEFAULT 1
            )
        ''')
        
        # System logs
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS system_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                level TEXT,
                message TEXT,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                module TEXT
            )
        ''')
        
        # Settings table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT
            )
        ''')
        
        conn.commit()
        conn.close()
    
    def execute_query(self, query, params=(), fetch=False):
        """Execute SQL query"""
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()
        
        try:
            cursor.execute(query, params)
            if fetch:
                if 'SELECT' in query.upper():
                    result = cursor.fetchall()
                else:
                    result = cursor.lastrowid
            else:
                result = None
            
            conn.commit()
            return result
        except Exception as e:
            logger.error(f"Database error: {e}")
            return None
        finally:
            conn.close()

db = Database()

# ==================== LOGGING SETUP ====================
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(f'logs/bot_{datetime.now().strftime("%Y%m%d")}.log'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

# ==================== CORE CLASSES ====================
class AccountStatus(Enum):
    ACTIVE = "active"
    INACTIVE = "inactive"
    SUSPENDED = "suspended"
    VERIFICATION_REQUIRED = "verification_required"

class TaskType(Enum):
    SUBSCRIBE = "subscribe"
    UNSUBSCRIBE = "unsubscribe"
    WATCH_VIDEO = "watch_video"
    LIKE_VIDEO = "like_video"
    COMMENT = "comment"

@dataclass
class BotSettings:
    min_delay: int = 3
    max_delay: int = 8
    watch_time_min: int = 30
    watch_time_max: int = 60
    use_proxy: bool = True
    max_concurrent_accounts: int = 3
    enable_screenshots: bool = True
    headless_mode: bool = False
    anti_detection_level: str = "high"
    enable_captcha_solver: bool = True
    captcha_api_key: str = ""
    auto_retry_failed: bool = True
    max_retries: int = 3

# ==================== YOUTUBE BOT CORE ====================
class YouTubeAutomationBot:
    def __init__(self, settings: BotSettings = None):
        self.settings = settings or BotSettings()
        self.accounts_queue = queue.Queue()
        self.channels_queue = queue.Queue()
        self.running = False
        self.active_threads = []
        self.user_agent = UserAgent()
        self.proxy_manager = ProxyManager()
        self.task_results = []
        self.current_tasks = {}
        
        # Create necessary directories
        self.create_directories()
        
        # Load accounts and channels
        self.load_data()
    
    def create_directories(self):
        """Create necessary directories for the bot"""
        directories = ['static', 'templates', 'logs', 'screenshots', 
                      'data', 'backups', 'temp', 'static/css', 
                      'static/js', 'static/images']
        
        for directory in directories:
            os.makedirs(directory, exist_ok=True)
    
    def load_data(self):
        """Load accounts and channels from database"""
        try:
            accounts = db.execute_query(
                "SELECT * FROM accounts WHERE status = 'active'",
                fetch=True
            )
            channels = db.execute_query(
                "SELECT * FROM channels WHERE status = 'active'",
                fetch=True
            )
            
            for account in accounts:
                self.accounts_queue.put(account)
            
            for channel in channels:
                self.channels_queue.put(channel)
                
            logger.info(f"Loaded {self.accounts_queue.qsize()} accounts and {self.channels_queue.qsize()} channels")
        except Exception as e:
            logger.error(f"Error loading data: {e}")
    
    def get_random_delay(self):
        """Get random delay between actions"""
        return random.uniform(self.settings.min_delay, self.settings.max_delay)
    
    def simulate_human_behavior(self, driver):
        """Simulate human-like behavior"""
        actions = [
            self.random_scroll,
            self.random_mouse_movement,
            self.random_typing_speed,
            self.random_wait,
            self.random_tab_switch
        ]
        
        # Randomly execute 2-3 human behaviors
        selected_actions = random.sample(actions, random.randint(2, 3))
        for action in selected_actions:
            action(driver)
            time.sleep(random.uniform(0.5, 2))
    
    def random_scroll(self, driver):
        """Random scrolling simulation"""
        scroll_amount = random.randint(100, 500)
        driver.execute_script(f"window.scrollBy(0, {scroll_amount})")
    
    def random_mouse_movement(self, driver):
        """Simulate random mouse movement"""
        try:
            # Get window size
            window_size = driver.get_window_size()
            x = random.randint(0, window_size['width'])
            y = random.randint(0, window_size['height'])
            
            # Create action chain for mouse movement
            actions = ActionChains(driver)
            actions.move_by_offset(x, y).perform()
        except:
            pass
    
    def setup_driver(self, account, use_proxy=True):
        """Setup Chrome driver with advanced anti-detection"""
        chrome_options = Options()
        
        # Basic anti-detection
        chrome_options.add_argument("--disable-blink-features=AutomationControlled")
        chrome_options.add_experimental_option("excludeSwitches", ["enable-automation"])
        chrome_options.add_experimental_option('useAutomationExtension', False)
        
        # Random User-Agent
        chrome_options.add_argument(f"user-agent={self.user_agent.random}")
        
        # Proxy settings
        if use_proxy and account.get('proxy'):
            chrome_options.add_argument(f'--proxy-server={account["proxy"]}')
        
        # Window settings
        chrome_options.add_argument("--window-size=1920,1080")
        if self.settings.headless_mode:
            chrome_options.add_argument("--headless")
        
        # Additional arguments for stealth
        chrome_options.add_argument("--disable-dev-shm-usage")
        chrome_options.add_argument("--no-sandbox")
        chrome_options.add_argument("--disable-gpu")
        chrome_options.add_argument("--disable-web-security")
        chrome_options.add_argument("--disable-features=VizDisplayCompositor")
        
        # Disable automation flags
        prefs = {
            "credentials_enable_service": False,
            "profile.password_manager_enabled": False,
            "profile.default_content_setting_values.notifications": 2
        }
        chrome_options.add_experimental_option("prefs", prefs)
        
        try:
            service = Service(ChromeDriverManager().install())
            driver = webdriver.Chrome(service=service, options=chrome_options)
            
            # Execute stealth scripts
            driver.execute_script("""
                Object.defineProperty(navigator, 'webdriver', {
                    get: () => undefined
                });
            """)
            
            return driver
        except Exception as e:
            logger.error(f"Error setting up driver: {e}")
            return None
    
    def login_to_youtube(self, driver, account):
        """Login to YouTube/Google account"""
        try:
            logger.info(f"Logging in with account: {account['email']}")
            
            # Navigate to Google login
            driver.get("https://accounts.google.com/signin")
            time.sleep(self.get_random_delay())
            
            # Enter email
            email_field = WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.ID, "identifierId"))
            )
            self.simulate_human_behavior(driver)
            self.type_like_human(email_field, account['email'])
            email_field.send_keys(Keys.RETURN)
            time.sleep(self.get_random_delay())
            
            # Enter password
            password_field = WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.NAME, "Passwd"))
            )
            self.simulate_human_behavior(driver)
            self.type_like_human(password_field, account['password'])
            password_field.send_keys(Keys.RETURN)
            time.sleep(self.get_random_delay() + 5)
            
            # Check for recovery email
            try:
                recovery_field = WebDriverWait(driver, 5).until(
                    EC.presence_of_element_located((By.XPATH, "//input[@type='email']"))
                )
                if recovery_field and account.get('recovery_email'):
                    self.type_like_human(recovery_field, account['recovery_email'])
                    recovery_field.send_keys(Keys.RETURN)
                    time.sleep(self.get_random_delay())
            except:
                pass
            
            # Verify login success
            WebDriverWait(driver, 15).until(
                EC.presence_of_element_located((By.XPATH, "//a[contains(@href, 'youtube.com')]"))
            )
            
            logger.info(f"Login successful for {account['email']}")
            return True
            
        except Exception as e:
            logger.error(f"Login failed for {account['email']}: {e}")
            self.take_screenshot(driver, f"login_error_{account['email']}")
            return False
    
    def type_like_human(self, element, text):
        """Type text like a human with random delays"""
        for char in text:
            element.send_keys(char)
            time.sleep(random.uniform(0.05, 0.2))
    
    def watch_video(self, driver, video_url, duration=None):
        """Watch a video for specified duration"""
        try:
            driver.get(video_url)
            time.sleep(self.get_random_delay())
            
            # Play video if not auto-playing
            try:
                play_button = driver.find_element(By.CSS_SELECTOR, "button.ytp-play-button")
                if "Play" in play_button.get_attribute("aria-label"):
                    play_button.click()
            except:
                pass
            
            # Set watch duration
            if duration is None:
                duration = random.randint(self.settings.watch_time_min, self.settings.watch_time_max)
            
            logger.info(f"Watching video for {duration} seconds...")
            
            # Simulate human behavior while watching
            start_time = time.time()
            while time.time() - start_time < duration:
                self.simulate_human_behavior(driver)
                time.sleep(random.randint(5, 15))
            
            return True
            
        except Exception as e:
            logger.error(f"Error watching video: {e}")
            return False
    
    def subscribe_to_channel(self, driver, channel_url):
        """Subscribe to a YouTube channel"""
        try:
            driver.get(channel_url)
            time.sleep(self.get_random_delay())
            
            # Find subscribe button
            subscribe_button = None
            selectors = [
                "ytd-subscribe-button-renderer paper-button",
                "#subscribe-button",
                "button[aria-label*='Subscribe']",
                "yt-formatted-string:contains('Subscribe')"
            ]
            
            for selector in selectors:
                try:
                    if ":contains" in selector:
                        subscribe_button = driver.find_element(By.XPATH, 
                            f"//*[contains(text(), 'Subscribe')]")
                    else:
                        subscribe_button = driver.find_element(By.CSS_SELECTOR, selector)
                    
                    if subscribe_button:
                        break
                except:
                    continue
            
            if subscribe_button:
                # Scroll to button
                driver.execute_script("arguments[0].scrollIntoView({behavior: 'smooth', block: 'center'});", 
                                     subscribe_button)
                time.sleep(self.get_random_delay())
                
                # Click subscribe
                subscribe_button.click()
                time.sleep(self.get_random_delay())
                
                logger.info(f"Subscribed to channel: {channel_url}")
                return True
            else:
                logger.warning(f"Subscribe button not found for {channel_url}")
                return False
                
        except Exception as e:
            logger.error(f"Error subscribing to channel {channel_url}: {e}")
            return False
    
    def take_screenshot(self, driver, name):
        """Take screenshot and save it"""
        if not self.settings.enable_screenshots:
            return None
        
        try:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"screenshots/{name}_{timestamp}.png"
            driver.save_screenshot(filename)
            return filename
        except Exception as e:
            logger.error(f"Error taking screenshot: {e}")
            return None
    
    def process_account(self, account, channels):
        """Process single account with multiple channels"""
        driver = None
        results = []
        
        try:
            # Setup driver
            driver = self.setup_driver(account, self.settings.use_proxy)
            if not driver:
                return results
            
            # Login
            login_success = self.login_to_youtube(driver, account)
            if not login_success:
                return results
            
            # Process each channel
            for channel in channels:
                try:
                    task_result = {
                        'account_email': account['email'],
                        'channel_url': channel['url'],
                        'status': 'pending',
                        'start_time': datetime.now()
                    }
                    
                    # Watch a video first
                    # Find random video from channel
                    driver.get(channel['url'] + "/videos")
                    time.sleep(self.get_random_delay())
                    
                    # Find first video
                    video_elements = driver.find_elements(By.CSS_SELECTOR, "a#video-title")
                    if video_elements:
                        video_url = video_elements[0].get_attribute("href")
                        if video_url:
                            self.watch_video(driver, video_url)
                    
                    # Subscribe to channel
                    subscribe_success = self.subscribe_to_channel(driver, channel['url'])
                    
                    if subscribe_success:
                        task_result['status'] = 'success'
                        task_result['message'] = 'Subscribed successfully'
                        
                        # Update database
                        db.execute_query(
                            "UPDATE accounts SET total_subscriptions = total_subscriptions + 1 WHERE email = ?",
                            (account['email'],)
                        )
                    else:
                        task_result['status'] = 'failed'
                        task_result['message'] = 'Failed to subscribe'
                    
                    task_result['end_time'] = datetime.now()
                    task_result['duration'] = (task_result['end_time'] - task_result['start_time']).total_seconds()
                    task_result['screenshot'] = self.take_screenshot(driver, f"{account['email']}_{channel['url']}")
                    
                    results.append(task_result)
                    
                    # Send real-time update via SocketIO
                    socketio.emit('task_update', task_result)
                    
                    # Delay before next channel
                    time.sleep(random.randint(10, 30))
                    
                except Exception as e:
                    logger.error(f"Error processing channel {channel['url']}: {e}")
                    continue
            
            # Logout or clear cookies
            driver.delete_all_cookies()
            
        except Exception as e:
            logger.error(f"Error processing account {account['email']}: {e}")
        finally:
            if driver:
                driver.quit()
        
        return results
    
    def start(self):
        """Start the automation bot"""
        if self.running:
            logger.warning("Bot is already running")
            return
        
        self.running = True
        logger.info("Starting YouTube Automation Bot")
        
        # Start processing in separate thread
        bot_thread = threading.Thread(target=self._run_bot)
        bot_thread.daemon = True
        bot_thread.start()
        
        socketio.emit('bot_status', {'status': 'running', 'timestamp': datetime.now().isoformat()})
    
    def stop(self):
        """Stop the automation bot"""
        self.running = False
        logger.info("Stopping YouTube Automation Bot")
        
        # Wait for active threads to complete
        for thread in self.active_threads:
            thread.join(timeout=30)
        
        socketio.emit('bot_status', {'status': 'stopped', 'timestamp': datetime.now().isoformat()})
    
    def _run_bot(self):
        """Main bot running loop"""
        while self.running and not self.accounts_queue.empty():
            try:
                # Get account from queue
                account = self.accounts_queue.get()
                
                # Get channels for this account
                channels = []
                for _ in range(min(3, self.channels_queue.qsize())):  # Process up to 3 channels per account
                    try:
                        channel = self.channels_queue.get()
                        channels.append(channel)
                        self.channels_queue.task_done()
                    except queue.Empty:
                        break
                
                if channels:
                    # Process account in separate thread
                    thread = threading.Thread(
                        target=self._process_account_thread,
                        args=(account, channels)
                    )
                    thread.start()
                    self.active_threads.append(thread)
                    
                    # Limit concurrent threads
                    if len(self.active_threads) >= self.settings.max_concurrent_accounts:
                        # Wait for at least one thread to complete
                        for t in self.active_threads:
                            if not t.is_alive():
                                t.join()
                                self.active_threads.remove(t)
                                break
                            time.sleep(1)
                
                self.accounts_queue.task_done()
                time.sleep(random.randint(30, 60))  # Delay between accounts
                
            except Exception as e:
                logger.error(f"Error in bot main loop: {e}")
                time.sleep(10)
    
    def _process_account_thread(self, account, channels):
        """Thread wrapper for account processing"""
        results = self.process_account(account, channels)
        self.task_results.extend(results)
        
        # Update database with results
        for result in results:
            db.execute_query('''
                INSERT INTO tasks (account_id, channel_id, task_type, status, 
                                 started_at, completed_at, duration, result)
                VALUES ((SELECT id FROM accounts WHERE email = ?),
                       (SELECT id FROM channels WHERE url = ?),
                       'subscribe', ?, ?, ?, ?, ?)
            ''', (
                result['account_email'],
                result['channel_url'],
                result['status'],
                result['start_time'],
                result['end_time'],
                result['duration'],
                json.dumps(result)
            ))
        
        # Remove thread from active threads
        if threading.current_thread() in self.active_threads:
            self.active_threads.remove(threading.current_thread())

# ==================== PROXY MANAGER ====================
class ProxyManager:
    def __init__(self):
        self.proxies = []
        self.load_proxies()
    
    def load_proxies(self):
        """Load proxies from database"""
        try:
            results = db.execute_query(
                "SELECT address, protocol, country, speed FROM proxies WHERE is_active = 1",
                fetch=True
            )
            self.proxies = [
                {
                    'address': r[0],
                    'protocol': r[1],
                    'country': r[2],
                    'speed': r[3]
                }
                for r in results
            ]
            logger.info(f"Loaded {len(self.proxies)} proxies")
        except Exception as e:
            logger.error(f"Error loading proxies: {e}")
            self.proxies = []
    
    def get_random_proxy(self):
        """Get random proxy from list"""
        if not self.proxies:
            return None
        return random.choice(self.proxies)['address']
    
    def test_proxy(self, proxy_address):
        """Test if proxy is working"""
        try:
            proxies = {
                'http': proxy_address,
                'https': proxy_address
            }
            response = requests.get('https://httpbin.org/ip', 
                                  proxies=proxies, 
                                  timeout=10)
            return response.status_code == 200
        except:
            return False

# ==================== FLASK ROUTES ====================
@app.route('/')
def dashboard():
    """Render main dashboard"""
    # Get stats from database
    stats = {
        'total_accounts': db.execute_query("SELECT COUNT(*) FROM accounts", fetch=True)[0][0],
        'active_accounts': db.execute_query("SELECT COUNT(*) FROM accounts WHERE status = 'active'", fetch=True)[0][0],
        'total_channels': db.execute_query("SELECT COUNT(*) FROM channels", fetch=True)[0][0],
        'completed_tasks': db.execute_query("SELECT COUNT(*) FROM tasks WHERE status = 'success'", fetch=True)[0][0],
        'pending_tasks': db.execute_query("SELECT COUNT(*) FROM tasks WHERE status = 'pending'", fetch=True)[0][0]
    }
    
    # Get recent tasks
    recent_tasks = db.execute_query(
        "SELECT t.*, a.email, c.url FROM tasks t "
        "LEFT JOIN accounts a ON t.account_id = a.id "
        "LEFT JOIN channels c ON t.channel_id = c.id "
        "ORDER BY t.completed_at DESC LIMIT 10",
        fetch=True
    )
    
    # Get account distribution
    account_stats = db.execute_query(
        "SELECT status, COUNT(*) as count FROM accounts GROUP BY status",
        fetch=True
    )
    
    return render_template('dashboard.html', 
                          stats=stats, 
                          recent_tasks=recent_tasks,
                          account_stats=account_stats)

@app.route('/accounts')
def accounts_page():
    """Accounts management page"""
    accounts = db.execute_query(
        "SELECT * FROM accounts ORDER BY created_at DESC",
        fetch=True
    )
    return render_template('accounts.html', accounts=accounts)

@app.route('/channels')
def channels_page():
    """Channels management page"""
    channels = db.execute_query(
        "SELECT * FROM channels ORDER BY last_checked DESC",
        fetch=True
    )
    return render_template('channels.html', channels=channels)

@app.route('/tasks')
def tasks_page():
    """Tasks monitoring page"""
    tasks = db.execute_query(
        "SELECT t.*, a.email, c.url, c.name FROM tasks t "
        "LEFT JOIN accounts a ON t.account_id = a.id "
        "LEFT JOIN channels c ON t.channel_id = c.id "
        "ORDER BY t.started_at DESC",
        fetch=True
    )
    return render_template('tasks.html', tasks=tasks)

@app.route('/proxies')
def proxies_page():
    """Proxies management page"""
    proxies = db.execute_query(
        "SELECT * FROM proxies ORDER BY last_used DESC",
        fetch=True
    )
    return render_template('proxies.html', proxies=proxies)

@app.route('/settings')
def settings_page():
    """Bot settings page"""
    settings = db.execute_query(
        "SELECT key, value FROM settings",
        fetch=True
    )
    settings_dict = {s[0]: s[1] for s in settings} if settings else {}
    return render_template('settings.html', settings=settings_dict)

# ==================== API ENDPOINTS ====================
@app.route('/api/start_bot', methods=['POST'])
def api_start_bot():
    """API endpoint to start the bot"""
    global youtube_bot
    
    if youtube_bot.running:
        return jsonify({'status': 'error', 'message': 'Bot is already running'})
    
    youtube_bot.start()
    return jsonify({'status': 'success', 'message': 'Bot started successfully'})

@app.route('/api/stop_bot', methods=['POST'])
def api_stop_bot():
    """API endpoint to stop the bot"""
    global youtube_bot
    
    if not youtube_bot.running:
        return jsonify({'status': 'error', 'message': 'Bot is not running'})
    
    youtube_bot.stop()
    return jsonify({'status': 'success', 'message': 'Bot stopped successfully'})

@app.route('/api/bot_status', methods=['GET'])
def api_bot_status():
    """Get current bot status"""
    global youtube_bot
    
    status = {
        'running': youtube_bot.running,
        'active_threads': len(youtube_bot.active_threads),
        'accounts_remaining': youtube_bot.accounts_queue.qsize(),
        'channels_remaining': youtube_bot.channels_queue.qsize(),
        'total_results': len(youtube_bot.task_results)
    }
    
    return jsonify(status)

@app.route('/api/import_accounts', methods=['POST'])
def api_import_accounts():
    """Import accounts from CSV/Excel file"""
    try:
        file = request.files['file']
        if not file:
            return jsonify({'status': 'error', 'message': 'No file uploaded'})
        
        # Read file based on extension
        filename = file.filename.lower()
        
        if filename.endswith('.csv'):
            df = pd.read_csv(file)
        elif filename.endswith(('.xlsx', '.xls')):
            df = pd.read_excel(file)
        else:
            return jsonify({'status': 'error', 'message': 'Unsupported file format'})
        
        # Validate required columns
        required_columns = ['email', 'password']
        missing_columns = [col for col in required_columns if col not in df.columns]
        
        if missing_columns:
            return jsonify({'status': 'error', 'message': f'Missing columns: {missing_columns}'})
        
        # Import accounts to database
        imported = 0
        for _, row in df.iterrows():
            try:
                db.execute_query('''
                    INSERT OR IGNORE INTO accounts (email, password, recovery_email, status)
                    VALUES (?, ?, ?, 'active')
                ''', (
                    row['email'],
                    row['password'],
                    row.get('recovery_email', '')
                ))
                imported += 1
            except Exception as e:
                logger.error(f"Error importing account {row['email']}: {e}")
        
        # Reload bot accounts
        youtube_bot.load_data()
        
        return jsonify({
            'status': 'success',
            'message': f'Imported {imported} accounts successfully'
        })
        
    except Exception as e:
        return jsonify({'status': 'error', 'message': str(e)})

@app.route('/api/add_channel', methods=['POST'])
def api_add_channel():
    """Add new channel to database"""
    try:
        data = request.json
        url = data.get('url')
        name = data.get('name', '')
        category = data.get('category', '')
        
        if not url:
            return jsonify({'status': 'error', 'message': 'URL is required'})
        
        # Validate YouTube URL
        if 'youtube.com' not in url and 'youtu.be' not in url:
            return jsonify({'status': 'error', 'message': 'Invalid YouTube URL'})
        
        db.execute_query('''
            INSERT OR IGNORE INTO channels (url, name, category, status)
            VALUES (?, ?, ?, 'active')
        ''', (url, name, category))
        
        # Reload bot channels
        youtube_bot.load_data()
        
        return jsonify({'status': 'success', 'message': 'Channel added successfully'})
        
    except Exception as e:
        return jsonify({'status': 'error', 'message': str(e)})

@app.route('/api/get_stats', methods=['GET'])
def api_get_stats():
    """Get real-time statistics"""
    stats = {
        'total_accounts': db.execute_query("SELECT COUNT(*) FROM accounts", fetch=True)[0][0],
        'active_accounts': db.execute_query("SELECT COUNT(*) FROM accounts WHERE status = 'active'", fetch=True)[0][0],
        'total_channels': db.execute_query("SELECT COUNT(*) FROM channels", fetch=True)[0][0],
        'completed_tasks': db.execute_query("SELECT COUNT(*) FROM tasks WHERE status = 'success'", fetch=True)[0][0],
        'pending_tasks': db.execute_query("SELECT COUNT(*) FROM tasks WHERE status = 'pending'", fetch=True)[0][0],
        'failed_tasks': db.execute_query("SELECT COUNT(*) FROM tasks WHERE status = 'failed'", fetch=True)[0][0],
        'total_subscriptions': db.execute_query("SELECT SUM(total_subscriptions) FROM accounts", fetch=True)[0][0] or 0
    }
    
    # Get hourly activity
    hourly_data = db.execute_query('''
        SELECT strftime('%H', completed_at) as hour, 
               COUNT(*) as count
        FROM tasks 
        WHERE completed_at >= datetime('now', '-24 hours')
        GROUP BY hour
        ORDER BY hour
    ''', fetch=True)
    
    stats['hourly_activity'] = {str(h): c for h, c in hourly_data} if hourly_data else {}
    
    return jsonify(stats)

@app.route('/api/update_settings', methods=['POST'])
def api_update_settings():
    """Update bot settings"""
    try:
        data = request.json
        
        for key, value in data.items():
            db.execute_query('''
                INSERT OR REPLACE INTO settings (key, value)
                VALUES (?, ?)
            ''', (key, str(value)))
        
        # Update bot settings
        youtube_bot.settings = BotSettings(
            min_delay=int(data.get('min_delay', 3)),
            max_delay=int(data.get('max_delay', 8)),
            use_proxy=data.get('use_proxy', 'true') == 'true',
            headless_mode=data.get('headless_mode', 'false') == 'true'
        )
        
        return jsonify({'status': 'success', 'message': 'Settings updated successfully'})
        
    except Exception as e:
        return jsonify({'status': 'error', 'message': str(e)})

# ==================== SOCKETIO EVENTS ====================
@socketio.on('connect')
def handle_connect():
    """Handle client connection"""
    logger.info('Client connected')
    emit('connected', {'message': 'Connected to YouTube Bot Server'})

@socketio.on('disconnect')
def handle_disconnect():
    """Handle client disconnection"""
    logger.info('Client disconnected')

@socketio.on('request_update')
def handle_request_update():
    """Send current status update to client"""
    status = {
        'running': youtube_bot.running,
        'accounts_processed': len(youtube_bot.task_results),
        'active_threads': len(youtube_bot.active_threads)
    }
    emit('status_update', status)

# ==================== HTML TEMPLATES ====================
# Create templates directory and HTML files
def create_html_templates():
    """Create HTML template files"""
    templates_dir = Path('templates')
    templates_dir.mkdir(exist_ok=True)
    
    # Dashboard template
    dashboard_html = '''
    <!DOCTYPE html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>YouTube Automation Bot - Dashboard</title>
        <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/css/bootstrap.min.css" rel="stylesheet">
        <link href="https://cdn.jsdelivr.net/npm/bootstrap-icons@1.8.1/font/bootstrap-icons.css" rel="stylesheet">
        <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.0.0/css/all.min.css" rel="stylesheet">
        <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
        <style>
            :root {
                --primary-color: #ff0000;
                --secondary-color: #282828;
                --accent-color: #3ea6ff;
                --bg-dark: #0f0f0f;
                --bg-card: #1f1f1f;
                --text-primary: #ffffff;
                --text-secondary: #aaaaaa;
            }
            
            body {
                background-color: var(--bg-dark);
                color: var(--text-primary);
                font-family: 'Roboto', 'Segoe UI', Arial, sans-serif;
                margin: 0;
                padding: 0;
            }
            
            .navbar {
                background-color: var(--secondary-color) !important;
                border-bottom: 2px solid var(--primary-color);
                padding: 1rem 0;
            }
            
            .navbar-brand {
                color: var(--primary-color) !important;
                font-weight: bold;
                font-size: 1.5rem;
            }
            
            .nav-link {
                color: var(--text-primary) !important;
                transition: color 0.3s;
            }
            
            .nav-link:hover {
                color: var(--accent-color) !important;
            }
            
            .card {
                background-color: var(--bg-card);
                border: 1px solid #333;
                border-radius: 12px;
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
                transition: transform 0.3s, box-shadow 0.3s;
                margin-bottom: 20px;
            }
            
            .card:hover {
                transform: translateY(-5px);
                box-shadow: 0 8px 24px rgba(255, 0, 0, 0.2);
            }
            
            .card-title {
                color: var(--accent-color);
                font-weight: 600;
            }
            
            .stat-card {
                background: linear-gradient(135deg, var(--secondary-color), #333);
                border-left: 4px solid var(--primary-color);
            }
            
            .btn-primary {
                background-color: var(--primary-color);
                border: none;
                padding: 10px 25px;
                border-radius: 8px;
                font-weight: 600;
                transition: all 0.3s;
            }
            
            .btn-primary:hover {
                background-color: #cc0000;
                transform: scale(1.05);
            }
            
            .btn-success {
                background-color: #28a745;
                border: none;
                padding: 10px 25px;
                border-radius: 8px;
                font-weight: 600;
            }
            
            .btn-danger {
                background-color: #dc3545;
                border: none;
                padding: 10px 25px;
                border-radius: 8px;
                font-weight: 600;
            }
            
            .table {
                color: var(--text-primary);
                background-color: var(--bg-card);
            }
            
            .table th {
                border-color: #444;
                color: var(--accent-color);
            }
            
            .table td {
                border-color: #444;
            }
            
            .status-badge {
                padding: 5px 12px;
                border-radius: 20px;
                font-size: 0.85rem;
                font-weight: 600;
            }
            
            .status-success {
                background-color: rgba(40, 167, 69, 0.2);
                color: #28a745;
                border: 1px solid #28a745;
            }
            
            .status-failed {
                background-color: rgba(220, 53, 69, 0.2);
                color: #dc3545;
                border: 1px solid #dc3545;
            }
            
            .status-running {
                background-color: rgba(255, 193, 7, 0.2);
                color: #ffc107;
                border: 1px solid #ffc107;
            }
            
            .live-indicator {
                display: inline-block;
                width: 10px;
                height: 10px;
                background-color: #28a745;
                border-radius: 50%;
                margin-right: 5px;
                animation: pulse 2s infinite;
            }
            
            @keyframes pulse {
                0% { opacity: 1; }
                50% { opacity: 0.5; }
                100% { opacity: 1; }
            }
            
            .progress-bar-custom {
                background: linear-gradient(90deg, var(--primary-color), #ff6b6b);
                border-radius: 10px;
            }
            
            .real-time-update {
                animation: slideIn 0.5s ease-out;
            }
            
            @keyframes slideIn {
                from { transform: translateY(-20px); opacity: 0; }
                to { transform: translateY(0); opacity: 1; }
            }
        </style>
    </head>
    <body>
        <!-- Navigation -->
        <nav class="navbar navbar-expand-lg navbar-dark">
            <div class="container-fluid">
                <a class="navbar-brand" href="/">
                    <i class="fab fa-youtube me-2"></i> YouTube Automation Bot
                </a>
                <button class="navbar-toggler" type="button" data-bs-toggle="collapse" data-bs-target="#navbarNav">
                    <span class="navbar-toggler-icon"></span>
                </button>
                <div class="collapse navbar-collapse" id="navbarNav">
                    <ul class="navbar-nav ms-auto">
                        <li class="nav-item">
                            <a class="nav-link active" href="/">
                                <i class="fas fa-tachometer-alt me-1"></i> Dashboard
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/accounts">
                                <i class="fas fa-users me-1"></i> Accounts
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/channels">
                                <i class="fas fa-satellite-dish me-1"></i> Channels
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/tasks">
                                <i class="fas fa-tasks me-1"></i> Tasks
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/proxies">
                                <i class="fas fa-globe me-1"></i> Proxies
                            </a>
                        </li>
                        <li class="nav-item">
                            <a class="nav-link" href="/settings">
                                <i class="fas fa-cog me-1"></i> Settings
                            </a>
                        </li>
                    </ul>
                </div>
            </div>
        </nav>

        <!-- Main Content -->
        <div class="container-fluid mt-4">
            <!-- Bot Control Section -->
            <div class="row mb-4">
                <div class="col-12">
                    <div class="card">
                        <div class="card-body">
                            <h4 class="card-title mb-4">
                                <i class="fas fa-robot me-2"></i>Bot Control Panel
                                <span id="botStatus" class="status-badge status-running ms-2">
                                    <span class="live-indicator"></span> Running
                                </span>
                            </h4>
                            <div class="row">
                                <div class="col-md-6">
                                    <div class="d-grid gap-2 d-md-flex">
                                        <button id="startBot" class="btn btn-success me-2" onclick="startBot()">
                                            <i class="fas fa-play me-1"></i> Start Bot
                                        </button>
                                        <button id="stopBot" class="btn btn-danger" onclick="stopBot()">
                                            <i class="fas fa-stop me-1"></i> Stop Bot
                                        </button>
                                    </div>
                                </div>
                                <div class="col-md-6">
                                    <div class="progress" style="height: 20px;">
                                        <div id="progressBar" class="progress-bar progress-bar-custom" 
                                             role="progressbar" style="width: 75%">
                                            75% Complete
                                        </div>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <!-- Stats Cards -->
            <div class="row">
                <div class="col-md-3">
                    <div class="card stat-card">
                        <div class="card-body">
                            <div class="d-flex justify-content-between align-items-center">
                                <div>
                                    <h6 class="card-subtitle mb-2 text-muted">Total Accounts</h6>
                                    <h2 id="totalAccounts" class="card-title">{{ stats.total_accounts }}</h2>
                                </div>
                                <i class="fas fa-users fa-3x text-primary"></i>
                            </div>
                        </div>
                    </div>
                </div>
                <div class="col-md-3">
                    <div class="card stat-card">
                        <div class="card-body">
                            <div class="d-flex justify-content-between align-items-center">
                                <div>
                                    <h6 class="card-subtitle mb-2 text-muted">Active Channels</h6>
                                    <h2 id="totalChannels" class="card-title">{{ stats.total_channels }}</h2>
                                </div>
                                <i class="fas fa-satellite-dish fa-3x text-success"></i>
                            </div>
                        </div>
                    </div>
                </div>
                <div class="col-md-3">
                    <div class="card stat-card">
                        <div class="card-body">
                            <div class="d-flex justify-content-between align-items-center">
                                <div>
                                    <h6 class="card-subtitle mb-2 text-muted">Completed Tasks</h6>
                                    <h2 id="completedTasks" class="card-title">{{ stats.completed_tasks }}</h2>
                                </div>
                                <i class="fas fa-check-circle fa-3x text-info"></i>
                            </div>
                        </div>
                    </div>
                </div>
                <div class="col-md-3">
                    <div class="card stat-card">
                        <div class="card-body">
                            <div class="d-flex justify-content-between align-items-center">
                                <div>
                                    <h6 class="card-subtitle mb-2 text-muted">Total Subscriptions</h6>
                                    <h2 id="totalSubscriptions" class="card-title">{{ stats.total_subscriptions }}</h2>
                                </div>
                                <i class="fas fa-heart fa-3x text-danger"></i>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <!-- Charts and Real-time Updates -->
            <div class="row mt-4">
                <div class="col-md-8">
                    <div class="card">
                        <div class="card-body">
                            <h5 class="card-title">Activity Chart (Last 24 Hours)</h5>
                            <canvas id="activityChart" height="200"></canvas>
                        </div>
                    </div>
                </div>
                <div class="col-md-4">
                    <div class="card">
                        <div class="card-body">
                            <h5 class="card-title">Real-time Updates</h5>
                            <div id="realtimeUpdates" class="list-group" style="max-height: 300px; overflow-y: auto;">
                                <!-- Updates will appear here -->
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <!-- Recent Tasks -->
            <div class="row mt-4">
                <div class="col-12">
                    <div class="card">
                        <div class="card-body">
                            <h5 class="card-title">Recent Tasks</h5>
                            <div class="table-responsive">
                                <table class="table table-hover">
                                    <thead>
                                        <tr>
                                            <th>Account</th>
                                            <th>Channel</th>
                                            <th>Status</th>
                                            <th>Duration</th>
                                            <th>Time</th>
                                        </tr>
                                    </thead>
                                    <tbody id="recentTasksTable">
                                        {% for task in recent_tasks %}
                                        <tr>
                                            <td>{{ task.email }}</td>
                                            <td>{{ task.url }}</td>
                                            <td>
                                                <span class="status-badge {% if task.status == 'success' %}status-success{% else %}status-failed{% endif %}">
                                                    {{ task.status }}
                                                </span>
                                            </td>
                                            <td>{{ task.duration }}s</td>
                                            <td>{{ task.completed_at }}</td>
                                        </tr>
                                        {% endfor %}
                                    </tbody>
                                </table>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <!-- Scripts -->
        <script src="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/js/bootstrap.bundle.min.js"></script>
        <script src="https://cdnjs.cloudflare.com/ajax/libs/socket.io/4.5.0/socket.io.js"></script>
        <script>
            // Connect to SocketIO
            const socket = io();
            
            // Chart setup
            const ctx = document.getElementById('activityChart').getContext('2d');
            const activityChart = new Chart(ctx, {
                type: 'line',
                data: {
                    labels: Array.from({length: 24}, (_, i) => `${i}:00`),
                    datasets: [{
                        label: 'Tasks Completed',
                        data: Array(24).fill(0),
                        borderColor: '#ff0000',
                        backgroundColor: 'rgba(255, 0, 0, 0.1)',
                        tension: 0.4,
                        fill: true
                    }]
                },
                options: {
                    responsive: true,
                    plugins: {
                        legend: {
                            labels: {
                                color: '#ffffff'
                            }
                        }
                    },
                    scales: {
                        x: {
                            grid: {
                                color: '#333'
                            },
                            ticks: {
                                color: '#aaa'
                            }
                        },
                        y: {
                            grid: {
                                color: '#333'
                            },
                            ticks: {
                                color: '#aaa'
                            }
                        }
                    }
                }
            });
            
            // SocketIO event handlers
            socket.on('connect', function() {
                console.log('Connected to server');
                socket.emit('request_update');
            });
            
            socket.on('bot_status', function(data) {
                updateBotStatus(data.status);
            });
            
            socket.on('task_update', function(data) {
                addRealTimeUpdate(data);
                updateRecentTasks(data);
                updateStats();
            });
            
            socket.on('status_update', function(data) {
                updateProgressBar(data);
            });
            
            // Update functions
            function updateBotStatus(status) {
                const badge = document.getElementById('botStatus');
                badge.innerHTML = status === 'running' 
                    ? '<span class="live-indicator"></span> Running'
                    : '<span class="live-indicator" style="background-color: #dc3545;"></span> Stopped';
            }
            
            function addRealTimeUpdate(data) {
                const updatesDiv = document.getElementById('realtimeUpdates');
                const update = document.createElement('div');
                update.className = 'list-group-item real-time-update';
                update.style.backgroundColor = '#1f1f1f';
                update.style.color = '#ffffff';
                update.style.borderColor = '#333';
                
                const statusClass = data.status === 'success' ? 'text-success' : 'text-danger';
                const icon = data.status === 'success' ? 'fa-check-circle' : 'fa-times-circle';
                
                update.innerHTML = `
                    <div class="d-flex justify-content-between align-items-center">
                        <div>
                            <i class="fas ${icon} ${statusClass} me-2"></i>
                            <small>${data.account_email}</small>
                        </div>
                        <small class="text-muted">${new Date().toLocaleTimeString()}</small>
                    </div>
                    <small class="text-muted">${data.channel_url}</small>
                `;
                
                updatesDiv.prepend(update);
                
                // Limit to 10 updates
                if (updatesDiv.children.length > 10) {
                    updatesDiv.removeChild(updatesDiv.lastChild);
                }
            }
            
            function updateRecentTasks(data) {
                const table = document.getElementById('recentTasksTable');
                const row = document.createElement('tr');
                
                const statusClass = data.status === 'success' ? 'status-success' : 'status-failed';
                
                row.innerHTML = `
                    <td>${data.account_email}</td>
                    <td>${data.channel_url}</td>
                    <td><span class="status-badge ${statusClass}">${data.status}</span></td>
                    <td>${data.duration ? data.duration.toFixed(1) : '0'}s</td>
                    <td>${new Date().toLocaleTimeString()}</td>
                `;
                
                table.prepend(row);
                
                // Limit to 10 rows
                if (table.children.length > 10) {
                    table.removeChild(table.lastChild);
                }
            }
            
            function updateProgressBar(data) {
                const progressBar = document.getElementById('progressBar');
                const accountsProcessed = data.accounts_processed || 0;
                const totalAccounts = {{ stats.total_accounts }};
                const percentage = totalAccounts > 0 ? (accountsProcessed / totalAccounts * 100) : 0;
                
                progressBar.style.width = `${percentage}%`;
                progressBar.textContent = `${percentage.toFixed(1)}% Complete`;
            }
            
            async function updateStats() {
                try {
                    const response = await fetch('/api/get_stats');
                    const stats = await response.json();
                    
                    document.getElementById('totalAccounts').textContent = stats.total_accounts;
                    document.getElementById('totalChannels').textContent = stats.total_channels;
                    document.getElementById('completedTasks').textContent = stats.completed_tasks;
                    document.getElementById('totalSubscriptions').textContent = stats.total_subscriptions;
                    
                    // Update chart
                    if (stats.hourly_activity) {
                        const hours = Array.from({length: 24}, (_, i) => i.toString().padStart(2, '0'));
                        activityChart.data.datasets[0].data = hours.map(h => stats.hourly_activity[h] || 0);
                        activityChart.update();
                    }
                } catch (error) {
                    console.error('Error updating stats:', error);
                }
            }
            
            // Bot control functions
            async function startBot() {
                try {
                    const response = await fetch('/api/start_bot', {
                        method: 'POST',
                        headers: {
                            'Content-Type': 'application/json'
                        }
                    });
                    const result = await response.json();
                    alert(result.message);
                } catch (error) {
                    alert('Error starting bot: ' + error.message);
                }
            }
            
            async function stopBot() {
                try {
                    const response = await fetch('/api/stop_bot', {
                        method: 'POST',
                        headers: {
                            'Content-Type': 'application/json'
                        }
                    });
                    const result = await response.json();
                    alert(result.message);
                } catch (error) {
                    alert('Error stopping bot: ' + error.message);
                }
            }
            
            // Initial load
            document.addEventListener('DOMContentLoaded', function() {
                updateStats();
                // Refresh stats every 30 seconds
                setInterval(updateStats, 30000);
            });
        </script>
    </body>
    </html>
    '''
    
    with open(templates_dir / 'dashboard.html', 'w', encoding='utf-8') as f:
        f.write(dashboard_html)
    
    # Create other template files (simplified versions)
    templates = {
        'accounts.html': '''
        <!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Accounts Management</title>
            <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/css/bootstrap.min.css" rel="stylesheet">
            <style>
                body { background-color: #0f0f0f; color: #fff; }
                .card { background-color: #1f1f1f; border: 1px solid #333; }
            </style>
        </head>
        <body>
            <div class="container-fluid mt-4">
                <h2>Accounts Management</h2>
                <!-- Add accounts table here -->
            </div>
        </body>
        </html>
        ''',
        
        'channels.html': '''
        <!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Channels Management</title>
            <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/css/bootstrap.min.css" rel="stylesheet">
            <style>
                body { background-color: #0f0f0f; color: #fff; }
                .card { background-color: #1f1f1f; border: 1px solid #333; }
            </style>
        </head>
        <body>
            <div class="container-fluid mt-4">
                <h2>Channels Management</h2>
                <!-- Add channels table here -->
            </div>
        </body>
        </html>
        ''',
        
        'tasks.html': '''
        <!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Tasks Monitoring</title>
            <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/css/bootstrap.min.css" rel="stylesheet">
            <style>
                body { background-color: #0f0f0f; color: #fff; }
                .card { background-color: #1f1f1f; border: 1px solid #333; }
            </style>
        </head>
        <body>
            <div class="container-fluid mt-4">
                <h2>Tasks Monitoring</h2>
                <!-- Add tasks table here -->
            </div>
        </body>
        </html>
        ''',
        
        'proxies.html': '''
        <!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Proxies Management</title>
            <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/css/bootstrap.min.css" rel="stylesheet">
            <style>
                body { background-color: #0f0f0f; color: #fff; }
                .card { background-color: #1f1f1f; border: 1px solid #333; }
            </style>
        </head>
        <body>
            <div class="container-fluid mt-4">
                <h2>Proxies Management</h2>
                <!-- Add proxies table here -->
            </div>
        </body>
        </html>
        ''',
        
        'settings.html': '''
        <!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Bot Settings</title>
            <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.1.3/dist/css/bootstrap.min.css" rel="stylesheet">
            <style>
                body { background-color: #0f0f0f; color: #fff; }
                .card { background-color: #1f1f1f; border: 1px solid #333; }
            </style>
        </head>
        <body>
            <div class="container-fluid mt-4">
                <h2>Bot Settings</h2>
                <!-- Add settings form here -->
            </div>
        </body>
        </html>
        '''
    }
    
    for filename, content in templates.items():
        with open(templates_dir / filename, 'w', encoding='utf-8') as f:
            f.write(content)
    
    # Create static files
    static_dir = Path('static')
    static_dir.mkdir(exist_ok=True)
    
    # Create CSS file
    css_content = '''
    /* Additional custom styles */
    .gradient-bg {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    }
    
    .shadow-lg {
        box-shadow: 0 10px 30px rgba(0, 0, 0, 0.3) !important;
    }
    
    .hover-lift:hover {
        transform: translateY(-5px);
        transition: transform 0.3s ease;
    }
    
    .glass-effect {
        background: rgba(255, 255, 255, 0.05);
        backdrop-filter: blur(10px);
        border: 1px solid rgba(255, 255, 255, 0.1);
    }
    '''
    
    with open(static_dir / 'css' / 'custom.css', 'w', encoding='utf-8') as f:
        f.write(css_content)

# ==================== MAIN EXECUTION ====================
def main():
    """Main function to run the application"""
    global youtube_bot
    
    # Create HTML templates
    create_html_templates()
    
    # Initialize bot with default settings
    settings = BotSettings()
    youtube_bot = YouTubeAutomationBot(settings)
    
    # Add sample data if database is empty
    if db.execute_query("SELECT COUNT(*) FROM accounts", fetch=True)[0][0] == 0:
        logger.info("Adding sample data...")
        db.execute_query('''
            INSERT OR IGNORE INTO accounts (email, password, recovery_email, status)
            VALUES ('sample@gmail.com', 'password123', 'recovery@gmail.com', 'active')
        ''')
    
    if db.execute_query("SELECT COUNT(*) FROM channels", fetch=True)[0][0] == 0:
        db.execute_query('''
            INSERT OR IGNORE INTO channels (url, name, status)
            VALUES ('https://www.youtube.com/@YouTube', 'YouTube Official', 'active')
        ''')
    
    # Start Flask app
    logger.info("Starting YouTube Automation Bot Web Dashboard...")
    logger.info("Open your browser and navigate to: http://localhost:5000")
    
    # Run Flask app with SocketIO
    socketio.run(app, host='0.0.0.0', port=5000, debug=False, allow_unsafe_werkzeug=True)

if __name__ == '__main__':
    # Create required directories
    for dir_path in ['templates', 'static/css', 'static/js', 'static/images', 
                    'logs', 'screenshots', 'data', 'backups', 'temp']:
        os.makedirs(dir_path, exist_ok=True)
    
    # Check and install required packages
    required_packages = [
        'flask',
        'flask-socketio',
        'selenium',
        'pandas',
        'fake-useragent',
        'webdriver-manager',
        'requests',
        'beautifulsoup4',
        'cloudscraper'
    ]
    
    # Install missing packages
    import subprocess
    import pkg_resources
    
    installed_packages = {pkg.key for pkg in pkg_resources.working_set}
    missing_packages = [pkg for pkg in required_packages if pkg.replace('-', '_') not in installed_packages]
    
    if missing_packages:
        print("Installing missing packages...")
        subprocess.check_call([sys.executable, '-m', 'pip', 'install'] + missing_packages)
    
    # Run the application
    main()