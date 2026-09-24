import argparse
import ast
import hashlib
import importlib.util
import json
import os
import re
import secrets
import socket
import subprocess
import sys
import threading
import time
import types
import ctypes
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse

# V6.2 STABLE: keep the GUI/agent process lightweight. Trading libraries are
# bundled by PyInstaller but are imported only by the child engine process.

APP_VERSION = "6.3"
AGENT_NAME = "Viju_Trade PC Dhan Agent"
HOST = "0.0.0.0"
PORT = 8765
MAX_BODY = 3 * 1024 * 1024
PROJECT_DIR = Path.home() / "NiftyMonitor"
ACTIVE_ENGINE = PROJECT_DIR / "active_engine.py"
PREVIOUS_ENGINE = PROJECT_DIR / "previous_engine.py"
ENGINE_META = PROJECT_DIR / "engine_meta.json"
SECRETS_FILE = PROJECT_DIR / ".secrets.env"
BROKER_SELECTION_FILE = PROJECT_DIR / "broker_selection.json"
APP_UI_FILE = PROJECT_DIR / "app_ui.json"
BROKER_STATUS_FILE = PROJECT_DIR / "broker_status.json"
TOKEN_FILE = PROJECT_DIR / "pc_remote_token.txt"
LOG_FILE = PROJECT_DIR / "viju_pc_agent.log"
LEGACY_MIGRATION_FILE = PROJECT_DIR / "legacy_v5_migrated.json"
SIGNALS_TEXT_FILE = PROJECT_DIR / "signals_today.txt"
NOTIFICATIONS_TEXT_FILE = PROJECT_DIR / "notifications_today.txt"

MANUAL_REFRESH_FILE = PROJECT_DIR / "manual_refresh.request"
WARNING_ACCEPT_FILE = PROJECT_DIR / "warning_accept.request"
WARNING_DECLINE_FILE = PROJECT_DIR / "warning_decline.request"
MANUAL_EXIT_FILE = PROJECT_DIR / "manual_exit.request"
CLOSE_ALL_TRANSITS_FILE = PROJECT_DIR / "close_all_transits.request"
STOP_REQUEST_FILE = PROJECT_DIR / "stop.request"

DHAN_KEYS = [
    "DHAN_CLIENT_ID", "DHAN_API_KEY", "DHAN_API_SECRET", "DHAN_REDIRECT_URL",
    "DHAN_PIN", "DHAN_TOTP_SECRET", "DHAN_ACCESS_TOKEN", "DHAN_TOKEN_EXPIRY",
    "OPENAI_API_KEY", "TELEGRAM_BOT_TOKEN", "TELEGRAM_CHAT_ID",
]
REQUIRED_KEYS = ["DHAN_CLIENT_ID", "DHAN_API_KEY", "DHAN_API_SECRET", "DHAN_REDIRECT_URL"]
SENSITIVE_KEYS = {"DHAN_API_SECRET", "DHAN_PIN", "DHAN_TOTP_SECRET", "DHAN_ACCESS_TOKEN", "OPENAI_API_KEY", "TELEGRAM_BOT_TOKEN"}

_state_lock = threading.RLock()
_engine_process = None
_engine_started_at = 0.0
_engine_last_error = ""
_last_mobile_seen = 0.0
_last_mobile_device = ""
_last_mobile_engine_status = "UNKNOWN"
_requested_host = ""
_handoff_status = ""
_handoff_request_time = 0.0
_handoff_thread = None
_server = None
_server_thread = None
_gui = None
_tailscale_ip_cache = "UNKNOWN"
_tailscale_ip_cache_at = 0.0
_tailscale_lock = threading.Lock()


def log(message):
    PROJECT_DIR.mkdir(parents=True, exist_ok=True)
    line = f"{datetime.now().isoformat(timespec='seconds')} | {message}\n"
    try:
        with LOG_FILE.open("a", encoding="utf-8") as f:
            f.write(line)
    except Exception:
        pass


def atomic_write(path: Path, text: str):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def atomic_json(path: Path, data):
    atomic_write(path, json.dumps(data, ensure_ascii=False, indent=2))


def read_json(path: Path, default=None):
    try:
        v = json.loads(path.read_text(encoding="utf-8"))
        return v if isinstance(v, dict) else (default if default is not None else {})
    except Exception:
        return default if default is not None else {}


def load_env_file(path: Path):
    out = {}
    if not path.exists():
        return out
    for raw in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        k, v = line.split("=", 1)
        k = k.strip()
        v = v.strip().strip('"').strip("'")
        if k:
            out[k] = v
    return out


def save_env(values):
    old = load_env_file(SECRETS_FILE)
    for k in DHAN_KEYS:
        if k in values:
            old[k] = str(values[k] or "").replace("\n", "").replace("\r", "")
    lines = [f"{k}={old.get(k, '')}" for k in DHAN_KEYS if old.get(k, "") != ""]
    atomic_write(SECRETS_FILE, "\n".join(lines) + ("\n" if lines else ""))
    _restrict_file(SECRETS_FILE)


def save_synced_credentials(payload):
    if not isinstance(payload, dict):
        raise ValueError("Invalid credential payload")
    values = {}
    allowed = set(DHAN_KEYS)
    for key in allowed:
        if key in payload:
            values[key] = str(payload.get(key) or "")
    if not values.get("DHAN_CLIENT_ID", "").strip():
        raise ValueError("Dhan client ID missing")
    save_env(values)
    atomic_json(BROKER_SELECTION_FILE, {
        "schema": 1,
        "broker_selected": "DHAN",
        "selection_id": str(payload.get("selection_id") or "android-sync"),
    })
    log("DHAN CREDENTIALS SYNCED FROM ANDROID")
    return credentials_ready()


def credentials_ready():
    env = load_env_file(SECRETS_FILE)
    if not all(str(env.get(k, "")).strip() for k in REQUIRED_KEYS):
        return False
    token = str(env.get("DHAN_ACCESS_TOKEN", "")).strip()
    pin = str(env.get("DHAN_PIN", "")).strip()
    totp = str(env.get("DHAN_TOTP_SECRET", "")).strip()
    return bool(token or (pin and totp))


def _restrict_file(path: Path):
    if os.name != "nt" or not path.exists():
        return
    try:
        user = os.environ.get("USERNAME", "")
        if user:
            subprocess.run(["icacls", str(path), "/inheritance:r", "/grant:r", f"{user}:F"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=5, check=False)
    except Exception:
        pass


def _migrate_old_token():
    candidates = [
        Path(r"C:\VijuTradeV5\pc_remote_token.txt"),
        Path(r"C:\VijuTradeV5\pc_token.txt"),
        Path(r"C:\VijuTradeV5\token.txt"),
        Path.home() / "VijuTradeV5" / "pc_remote_token.txt",
    ]
    for p in candidates:
        try:
            if p.exists():
                t = p.read_text(encoding="utf-8").strip()
                if len(t) >= 16:
                    return t
        except Exception:
            pass
    config_candidates = [Path(r"C:\VijuTradeV5\config.json"), Path.home() / "VijuTradeV5" / "config.json"]
    for p in config_candidates:
        try:
            obj = read_json(p, {})
            for key in ("token", "pc_token", "api_token", "auth_token"):
                t = str(obj.get(key, "")).strip()
                if len(t) >= 16:
                    return t
        except Exception:
            pass
    return ""


def get_token():
    PROJECT_DIR.mkdir(parents=True, exist_ok=True)
    # One-time compatibility migration: keep the token already stored in the
    # Android APK for Agent 5.0 so V6.2 replaces the old agent without forcing
    # the user to re-enter PC credentials.
    if not LEGACY_MIGRATION_FILE.exists():
        legacy = _migrate_old_token()
        if legacy:
            atomic_write(TOKEN_FILE, legacy + "\n")
            _restrict_file(TOKEN_FILE)
        atomic_json(LEGACY_MIGRATION_FILE, {"done": True, "legacy_token_found": bool(legacy)})
    try:
        if TOKEN_FILE.exists():
            t = TOKEN_FILE.read_text(encoding="utf-8").strip()
            if len(t) >= 16:
                return t
    except Exception:
        pass
    t = os.environ.get("VIJU_PC_TOKEN", "").strip() or secrets.token_urlsafe(32)
    atomic_write(TOKEN_FILE, t + "\n")
    _restrict_file(TOKEN_FILE)
    return t


def set_token(value):
    value = str(value or "").strip()
    if len(value) < 16:
        raise ValueError("PC token must be at least 16 characters")
    atomic_write(TOKEN_FILE, value + "\n")
    _restrict_file(TOKEN_FILE)


def _listening_pid_on_port(port):
    if os.name != "nt":
        return None
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    try:
        r = subprocess.run(["netstat", "-ano", "-p", "tcp"], capture_output=True, text=True,
                           timeout=4, check=False, creationflags=flags)
        want = ":" + str(int(port))
        for raw in r.stdout.splitlines():
            line = raw.strip()
            if not line or "LISTENING" not in line.upper():
                continue
            parts = line.split()
            if len(parts) < 5:
                continue
            local = parts[1]
            if local.endswith(want):
                try:
                    return int(parts[-1])
                except Exception:
                    pass
    except Exception:
        pass
    return None


def _process_commandline(pid):
    if os.name != "nt" or not pid:
        return ""
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    try:
        ps = (
            "$p=Get-CimInstance Win32_Process -Filter \"ProcessId=" + str(int(pid)) + "\";"
            "if($p){$p.CommandLine}"
        )
        r = subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
                           capture_output=True, text=True, timeout=5, check=False,
                           creationflags=flags)
        return (r.stdout or "").strip()
    except Exception:
        return ""


def retire_legacy_agent():
    """Retire the old V5 scheduled agent and reclaim port 8765.

    V5 was installed as a scheduled task and can remain alive even after the task
    is disabled.  The V6.x GUI must own the same IP/port so the Android app keeps
    using its existing connection settings.
    """
    if os.name != "nt":
        return
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)

    # Stop, disable and remove the known legacy task. Ignore failures because the
    # current user may not have permission to change a task created differently.
    for args in (
        ["schtasks", "/End", "/TN", "VijuTradeV5Agent"],
        ["schtasks", "/Change", "/TN", "VijuTradeV5Agent", "/Disable"],
        ["schtasks", "/Delete", "/TN", "VijuTradeV5Agent", "/F"],
    ):
        try:
            subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=5, check=False, creationflags=flags)
        except Exception:
            pass

    # Give the scheduled task a moment to exit.
    deadline = time.time() + 2.5
    while time.time() < deadline:
        pid = _listening_pid_on_port(PORT)
        if not pid or pid == os.getpid():
            return
        time.sleep(0.15)

    # If V5 is still holding 8765, kill only a process that looks like the old
    # Viju agent. This avoids terminating an unrelated application accidentally.
    pid = _listening_pid_on_port(PORT)
    if not pid or pid == os.getpid():
        return
    cmd = _process_commandline(pid).lower()
    known_legacy = (
        "vijutradev5" in cmd
        or "viju_trade_v5" in cmd
        or "viju trade v5" in cmd
        or ("python" in cmd and ("8765" in cmd or "agent" in cmd or "main.py" in cmd))
    )
    if known_legacy:
        try:
            subprocess.run(["taskkill", "/PID", str(pid), "/F"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=5, check=False, creationflags=flags)
            log(f"LEGACY AGENT TERMINATED pid={pid}")
        except Exception:
            pass

    # Wait briefly for Windows to release the listening socket.
    deadline = time.time() + 5.0
    while time.time() < deadline:
        pid2 = _listening_pid_on_port(PORT)
        if not pid2 or pid2 == os.getpid():
            return
        time.sleep(0.20)


def ensure_project():
    PROJECT_DIR.mkdir(parents=True, exist_ok=True)
    selection = read_json(BROKER_SELECTION_FILE, {})
    selection.update({"schema": 1, "broker_selected": "DHAN"})
    selection.setdefault("selection_id", "windows-dhan")
    atomic_json(BROKER_SELECTION_FILE, selection)
    get_token()


def _discover_tailscale_ip():
    if os.name == "nt":
        try:
            r = subprocess.run(["tailscale", "ip", "-4"], capture_output=True, text=True,
                               timeout=2, check=False, creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            for line in r.stdout.splitlines():
                ip = line.strip()
                if re.fullmatch(r"100\.(?:6[4-9]|[7-9]\d|1[01]\d|12[0-7])\.\d{1,3}\.\d{1,3}", ip):
                    return ip
        except Exception:
            pass
        try:
            r = subprocess.run(["ipconfig"], capture_output=True, text=True, timeout=2, check=False,
                               creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            for ip in re.findall(r"IPv4[^:]*:\s*([0-9.]+)", r.stdout):
                parts = ip.split(".")
                if len(parts) == 4 and parts[0] == "100" and 64 <= int(parts[1]) <= 127:
                    return ip
        except Exception:
            pass
    try:
        return socket.gethostbyname(socket.gethostname())
    except Exception:
        return "UNKNOWN"


def tailscale_ip(force=False):
    global _tailscale_ip_cache, _tailscale_ip_cache_at
    now = time.time()
    if not force and _tailscale_ip_cache_at and now - _tailscale_ip_cache_at < 60:
        return _tailscale_ip_cache
    if not _tailscale_lock.acquire(blocking=False):
        return _tailscale_ip_cache
    try:
        now = time.time()
        if force or not _tailscale_ip_cache_at or now - _tailscale_ip_cache_at >= 60:
            _tailscale_ip_cache = _discover_tailscale_ip()
            _tailscale_ip_cache_at = time.time()
        return _tailscale_ip_cache
    finally:
        _tailscale_lock.release()


def engine_running():
    global _engine_process
    with _state_lock:
        p = _engine_process
        if p is not None and p.poll() is not None:
            _engine_process = None
            p = None
        return p is not None


def _install_fcntl_compat():
    if os.name != "nt" or "fcntl" in sys.modules:
        return
    import msvcrt
    m = types.ModuleType("fcntl")
    m.LOCK_EX = 2
    m.LOCK_NB = 4
    m.LOCK_UN = 8
    m.LOCK_SH = 1

    def flock(fd, op):
        try:
            os.lseek(fd, 0, os.SEEK_SET)
        except Exception:
            pass
        try:
            if op & m.LOCK_UN:
                mode = msvcrt.LK_UNLCK
            elif op & m.LOCK_NB:
                mode = msvcrt.LK_NBLCK
            else:
                mode = msvcrt.LK_LOCK
            msvcrt.locking(fd, mode, 1)
        except OSError as exc:
            if op & m.LOCK_NB:
                raise BlockingIOError(str(exc)) from exc
            raise
    m.flock = flock
    sys.modules["fcntl"] = m


def engine_runner(path):
    ensure_project()
    _install_fcntl_compat()
    os.environ["VIJU_BROKER"] = "DHAN"
    os.environ["BROKER_SELECTED"] = "DHAN"
    os.environ["VIJU_BROKER_SELECTION_FILE"] = str(BROKER_SELECTION_FILE)
    os.environ["VIJU_WINDOWS_HOST"] = "1"
    sys.path.insert(0, str(PROJECT_DIR))
    spec = importlib.util.spec_from_file_location("viju_synced_engine", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Could not load synced engine")
    module = importlib.util.module_from_spec(spec)
    sys.modules["viju_synced_engine"] = module
    spec.loader.exec_module(module)
    # V8.6 host handoff: make the unchanged APK engine's stop hook also watch
    # the Windows stop-request file, so Dhan logout can finish before takeover.
    original_stop_hook = getattr(module, "_android_host_stop_requested", None)
    def _windows_host_stop_requested():
        file_stop = STOP_REQUEST_FILE.exists()
        try:
            return file_stop or (bool(original_stop_hook()) if callable(original_stop_hook) else False)
        except Exception:
            return file_stop
    module._android_host_stop_requested = _windows_host_stop_requested
    fn = getattr(module, "engine_main", None)
    if not callable(fn):
        raise RuntimeError("Synced engine has no engine_main()")
    fn()


def start_engine():
    global _engine_process, _engine_started_at, _engine_last_error
    ensure_project()
    with _state_lock:
        if engine_running():
            return True, "already running"
        if not ACTIVE_ENGINE.exists():
            return False, "Engine not synced yet. Open the PC page in Android once and press REFRESH."
        if not credentials_ready():
            return False, "Dhan credentials not synced yet. Open the PC page in Android once and press REFRESH."
        try:
            try:
                STOP_REQUEST_FILE.unlink(missing_ok=True)
            except Exception:
                pass
            if getattr(sys, "frozen", False):
                cmd = [sys.executable, "--engine-runner", str(ACTIVE_ENGINE)]
            else:
                cmd = [sys.executable, str(Path(__file__).resolve()), "--engine-runner", str(ACTIVE_ENGINE)]
            env = os.environ.copy()
            env.update({
                "VIJU_BROKER": "DHAN",
                "BROKER_SELECTED": "DHAN",
                "VIJU_BROKER_SELECTION_FILE": str(BROKER_SELECTION_FILE),
                "VIJU_WINDOWS_HOST": "1",
            })
            flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
            _engine_process = subprocess.Popen(cmd, cwd=str(PROJECT_DIR), env=env, creationflags=flags)
            _engine_started_at = time.time()
            _engine_last_error = ""
            log(f"ENGINE START pid={_engine_process.pid}")
            return True, "started"
        except Exception as exc:
            _engine_last_error = f"{type(exc).__name__}: {exc}"
            log("ENGINE START ERROR " + _engine_last_error)
            _engine_process = None
            return False, _engine_last_error


def stop_engine():
    global _engine_process
    with _state_lock:
        p = _engine_process
        if p is None:
            return True, "already stopped"
        try:
            STOP_REQUEST_FILE.touch(exist_ok=True)
        except Exception:
            pass

    # Do not kill the Dhan engine immediately. The synced Python engine sees the
    # stop-request file, leaves its loop and performs its normal logout/cleanup.
    deadline = time.time() + 20.0
    while p.poll() is None and time.time() < deadline:
        time.sleep(0.20)
    if p.poll() is None:
        try:
            p.terminate()
            p.wait(timeout=5)
        except Exception:
            try:
                p.kill()
                p.wait(timeout=3)
            except Exception:
                pass
    with _state_lock:
        log(f"ENGINE STOP pid={getattr(p, 'pid', '?')}")
        if _engine_process is p:
            _engine_process = None
    return True, "stopped"


def validate_engine_text(text):
    if not isinstance(text, str) or not text.strip():
        raise ValueError("Empty engine")
    if len(text.encode("utf-8")) > 2_500_000:
        raise ValueError("Engine file is too large")
    compile(text, "active_engine.py", "exec")
    tree = ast.parse(text, "active_engine.py")
    version = "unknown"
    interface = ""
    brokers = []
    has_main = False
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == "engine_main":
            has_main = True
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in {"VERSION", "ENGINE_INTERFACE", "SUPPORTED_BROKERS"}:
                    try:
                        value = ast.literal_eval(node.value)
                    except Exception:
                        continue
                    if target.id == "VERSION":
                        version = str(value)
                    elif target.id == "ENGINE_INTERFACE":
                        interface = str(value)
                    elif target.id == "SUPPORTED_BROKERS":
                        if isinstance(value, (tuple, list, set)):
                            brokers = [str(x).upper() for x in value]
    if not has_main:
        raise ValueError("Engine must contain engine_main()")
    if not interface.startswith("ANDROID_"):
        raise ValueError("Engine interface is not Android-compatible")
    if "DHAN" not in brokers:
        raise ValueError("Windows PC accepts only Dhan-capable engines")
    return version, interface


def install_synced_engine(text, filename="active_engine.py", supplied_version="", supplied_sha=""):
    global _engine_last_error
    version, interface = validate_engine_text(text)
    digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
    if supplied_sha and supplied_sha.lower() != digest.lower():
        raise ValueError("Engine SHA-256 mismatch")
    was_running = engine_running()
    if ACTIVE_ENGINE.exists():
        try:
            atomic_write(PREVIOUS_ENGINE, ACTIVE_ENGINE.read_text(encoding="utf-8"))
        except Exception:
            pass
    atomic_write(ACTIVE_ENGINE, text)
    atomic_json(ENGINE_META, {
        "installed_filename": filename or "active_engine.py",
        "version": supplied_version or version,
        "validated_version": version,
        "engine_interface": interface,
        "sha256": digest,
        "source": "ANDROID_APK_SYNC",
        "synced_at": datetime.now().isoformat(timespec="seconds"),
    })
    _engine_last_error = ""
    log(f"ENGINE SYNC version={version} sha256={digest[:12]}")
    restarting = False
    if was_running:
        restarting = True
        def _restart_synced():
            try:
                stop_engine()
                time.sleep(0.25)
                start_engine()
            except Exception as exc:
                log("ENGINE SYNC RESTART ERROR " + str(exc))
        threading.Thread(target=_restart_synced, name="VijuPC-engine-sync-restart", daemon=True).start()
    return {"version": version, "sha256": digest, "restarting": restarting}


def write_request(path: Path, payload=None):
    if payload is None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.touch(exist_ok=True)
    else:
        atomic_json(path, payload)


def mobile_engine_recent(seconds=12):
    return (time.time() - _last_mobile_seen) <= float(seconds)


def request_pc_host():
    global _requested_host, _handoff_status, _handoff_request_time, _handoff_thread
    with _state_lock:
        if engine_running():
            _requested_host = ""
            _handoff_status = "PC RUNNING"
            return True, "PC engine already running"
        if _handoff_thread is not None and _handoff_thread.is_alive():
            return True, "Host handoff already in progress"
        _requested_host = "PC"
        _handoff_status = "WAITING FOR MOBILE ENGINE TO STOP"
        _handoff_request_time = time.time()

        def worker():
            global _requested_host, _handoff_status
            deadline = time.time() + 60.0
            while time.time() < deadline:
                # Require an explicit STOPPED heartbeat received after this claim.
                if (_last_mobile_engine_status == "STOPPED"
                        and _last_mobile_seen >= _handoff_request_time):
                    _handoff_status = "MOBILE STOPPED • STARTING PC"
                    ok, msg = start_engine()
                    _handoff_status = "PC RUNNING" if ok else ("PC START FAILED: " + str(msg))
                    _requested_host = ""
                    log("HOST HANDOFF MOBILE->PC | " + _handoff_status)
                    return
                time.sleep(0.25)
            _handoff_status = "HANDOFF FAILED • MOBILE STOP NOT CONFIRMED"
            _requested_host = ""
            log("HOST HANDOFF TIMEOUT | mobile stop not confirmed")

        _handoff_thread = threading.Thread(target=worker, name="VijuHostHandoff", daemon=True)
        _handoff_thread.start()
        return True, "Waiting for mobile engine to stop before PC login"


def command(action, body=None):
    body = body or {}
    action = str(action or "").strip().upper()
    if action == "ENGINE_START":
        # Remote Android start is accepted only after Mobile has explicitly
        # reported STOPPED. This prevents duplicate Dhan sessions.
        if _last_mobile_engine_status in ("RUNNING", "STOPPING") and mobile_engine_recent():
            return False, "Mobile engine has not confirmed STOPPED yet"
        ok, msg = start_engine()
        return ok, msg
    if action == "REQUEST_PC_HOST":
        return request_pc_host()
    if action == "ENGINE_STOP":
        if engine_running():
            threading.Thread(target=stop_engine, name="VijuRemoteStop", daemon=True).start()
            return True, "stop requested"
        return True, "already stopped"
    if action == "ENGINE_RESTART":
        stop_engine(); return start_engine()
    if action in ("REFRESH", "MANUAL_REFRESH"):
        write_request(MANUAL_REFRESH_FILE)
        return True, "refresh requested"
    if action == "ACCEPT":
        write_request(WARNING_ACCEPT_FILE, {
            "signal_no": int(body.get("signal_no") or 0),
            "warning_type": str(body.get("warning_type") or ""),
            "premium": float(body.get("premium") or 0),
            "source": "WINDOWS_OR_ANDROID_REMOTE",
            "requested_at": datetime.now().isoformat(timespec="seconds"),
        })
        return True, "accept requested"
    if action == "DECLINE":
        write_request(WARNING_DECLINE_FILE, {
            "signal_no": int(body.get("signal_no") or 0),
            "warning_type": str(body.get("warning_type") or ""),
            "source": "WINDOWS_OR_ANDROID_REMOTE",
            "requested_at": datetime.now().isoformat(timespec="seconds"),
        })
        return True, "decline requested"
    if action == "EXIT_SIGNAL":
        write_request(MANUAL_EXIT_FILE, {
            "signal_no": int(body.get("signal_no") or 0),
            "source": "WINDOWS_OR_ANDROID_REMOTE",
            "requested_at": datetime.now().isoformat(timespec="seconds"),
        })
        return True, "exit requested"
    if action == "CLOSE_ALL":
        write_request(CLOSE_ALL_TRANSITS_FILE)
        return True, "close all requested"
    if action == "PC_UI_START":
        return True, "PC UI already running"
    if action == "PC_UI_STOP":
        try:
            if _gui is not None:
                _gui.after(0, _gui.iconify)
        except Exception:
            pass
        return True, "PC UI minimized"
    if action == "PC_DISPLAY_OFF":
        try:
            ctypes.windll.user32.SendMessageW(0xFFFF, 0x0112, 0xF170, 2)
            return True, "display off requested"
        except Exception as exc:
            return False, str(exc)
    if action == "PC_DISPLAY_ON":
        try:
            ctypes.windll.user32.SendMessageW(0xFFFF, 0x0112, 0xF170, -1)
            return True, "display on requested"
        except Exception as exc:
            return False, str(exc)
    if action == "PC_SHUTDOWN":
        try:
            subprocess.Popen(["shutdown", "/s", "/t", "5"], creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            return True, "shutdown requested"
        except Exception as exc:
            return False, str(exc)
    if action == "PC_RESTART":
        try:
            subprocess.Popen(["shutdown", "/r", "/t", "5"], creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            return True, "restart requested"
        except Exception as exc:
            return False, str(exc)
    return False, "unsupported action"


def read_text_file(path: Path, default=""):
    try:
        return path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return default


def _sanitize_dhan_text(value):
    s = str(value or "")
    s = re.sub(r"ANGEL(?: ONE)? LOGIN:", "DHAN LOGIN:", s, flags=re.I)
    s = re.sub(r"\bANGEL ONE\b", "DHAN", s, flags=re.I)
    return s


def current_state():
    ui = read_json(APP_UI_FILE, {})
    broker = read_json(BROKER_STATUS_FILE, {})
    eng = engine_running()
    login = str(broker.get("login_status") or ui.get("login_status") or "LOGGED OUT").upper()
    if broker.get("broker_selected") and str(broker.get("broker_selected")).upper() != "DHAN":
        login = "LOGGED OUT"
    remote = (time.time() - _last_mobile_seen) < 15
    meta = read_json(ENGINE_META, {})
    if eng:
        active_host = "PC"
    elif remote and _last_mobile_engine_status == "RUNNING":
        active_host = "MOBILE"
    elif _requested_host:
        active_host = "SWITCHING_TO_" + _requested_host
    else:
        active_host = "NONE"
    service = "\n".join([
        "Broker: DHAN",
        f"Login: {login}",
        f"Monitor: {'RUNNING' if eng else 'STOPPED'}",
        f"Credentials: {'READY' if credentials_ready() else 'NOT READY'}",
        "PC Agent: RUNNING",
        f"Remote mobile: {'CONNECTED' if remote else 'DISCONNECTED'}",
        f"Engine source: APK sync{(' V' + str(meta.get('version'))) if meta.get('version') else ''}",
    ])
    state = {
        "ok": True,
        "version": APP_VERSION,
        "agent_status": "RUNNING",
        "engine_status": "RUNNING" if eng else "STOPPED",
        "market_status": str(ui.get("market_state") or "LOGIN"),
        "tailscale_ip": tailscale_ip(),
        "broker": "DHAN",
        "broker_selected": "DHAN",
        "login_status": login,
        "credentials_ready": credentials_ready(),
        "remote_mobile_connected": remote,
        "remote_mobile_device": _last_mobile_device,
        "remote_mobile_engine_status": _last_mobile_engine_status,
        "requested_host": _requested_host,
        "handoff_status": _handoff_status,
        "active_host": active_host,
        "service_text": service,
        "market_text": _sanitize_dhan_text(ui.get("live_text") or ("LOGGING IN" if eng else "ENGINE STOPPED")),
        "live_text": _sanitize_dhan_text(ui.get("live_text") or ""),
        "transit_text": str(ui.get("transit_text") or "NO ACTIVE TRANSIT"),
        "stats_text": str(ui.get("stats_text") or "No signals yet."),
        "warning_pending": bool(ui.get("warning_pending", False)),
        "warning_signal_no": int(ui.get("warning_signal_no") or 0),
        "warning_type": str(ui.get("warning_type") or ""),
        "warning_reason": str(ui.get("warning_reason") or ""),
        "warning_current_premium": float(ui.get("warning_current_premium") or 0),
        "warning_accept_label": str(ui.get("warning_accept_label") or "ACCEPT"),
        "warning_decline_label": str(ui.get("warning_decline_label") or "DECLINE"),
        "active_transits_ui": ui.get("active_transits_ui") if isinstance(ui.get("active_transits_ui"), list) else [],
        "engine_version": str(ui.get("engine_version") or meta.get("version") or "--"),
        "engine_sha256": str(meta.get("sha256") or ""),
        "engine_sync_source": str(meta.get("source") or ""),
        "last_engine_error": _engine_last_error,
        "signals_text": read_text_file(SIGNALS_TEXT_FILE, ""),
        "notifications_text": read_text_file(NOTIFICATIONS_TEXT_FILE, ""),
    }
    return state


class AgentHandler(BaseHTTPRequestHandler):
    server_version = "VijuTradePC/6.3"

    def log_message(self, fmt, *args):
        return

    def _json(self, status, obj):
        raw = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(raw)

    def _authorized(self):
        auth = self.headers.get("Authorization", "")
        expected = "Bearer " + get_token()
        return secrets.compare_digest(auth, expected)

    def _body(self):
        try:
            n = int(self.headers.get("Content-Length", "0") or "0")
        except Exception:
            n = 0
        if n < 0 or n > MAX_BODY:
            raise ValueError("request too large")
        data = self.rfile.read(n) if n else b"{}"
        obj = json.loads(data.decode("utf-8")) if data else {}
        if not isinstance(obj, dict):
            raise ValueError("JSON object required")
        return obj

    def _guard(self):
        if not self._authorized():
            self._json(401, {"ok": False, "error": "unauthorized"})
            return False
        return True

    def do_GET(self):
        if not self._guard():
            return
        path = urlparse(self.path).path
        if path in ("/", "/api/v1/health"):
            self._json(200, {"ok": True, "version": APP_VERSION, "agent": "RUNNING", "broker": "DHAN"})
            return
        if path == "/api/v1/state":
            self._json(200, current_state())
            return
        self._json(404, {"ok": False, "error": "not found"})

    def do_POST(self):
        global _last_mobile_seen, _last_mobile_device, _last_mobile_engine_status
        if not self._guard():
            return
        path = urlparse(self.path).path
        try:
            body = self._body()
            if path == "/api/v1/mobile-heartbeat":
                _last_mobile_seen = time.time()
                _last_mobile_device = str(body.get("device") or "Android")[:80]
                status = str(body.get("mobile_engine_status") or "UNKNOWN").strip().upper()
                if status in ("RUNNING", "STOPPING", "STOPPED"):
                    _last_mobile_engine_status = status
                self._json(200, {
                    "ok": True,
                    "remote_mobile": "CONNECTED",
                    "requested_host": _requested_host,
                    "handoff_status": _handoff_status,
                    "pc_engine_status": "RUNNING" if engine_running() else "STOPPED",
                })
                return
            if path == "/api/v1/command":
                ok, msg = command(body.get("action"), body)
                self._json(200 if ok else 400, {"ok": ok, "message": msg, "state": current_state()})
                return
            if path == "/api/v1/engine-sync":
                result = install_synced_engine(
                    str(body.get("engine_text") or ""),
                    str(body.get("filename") or "active_engine.py"),
                    str(body.get("version") or ""),
                    str(body.get("sha256") or ""),
                )
                self._json(200, {"ok": True, "installed": result})
                return
            if path == "/api/v1/credentials-sync":
                ready = save_synced_credentials(body.get("secrets") if isinstance(body.get("secrets"), dict) else body)
                self._json(200, {"ok": True, "credentials_ready": ready})
                return
            self._json(404, {"ok": False, "error": "not found"})
        except Exception as exc:
            log("HTTP ERROR " + type(exc).__name__ + ": " + str(exc))
            self._json(400, {"ok": False, "error": str(exc)[:300]})


def start_server():
    global _server, _server_thread
    if _server is not None:
        return
    ensure_project()
    _server = ThreadingHTTPServer((HOST, PORT), AgentHandler)
    _server.daemon_threads = True
    _server_thread = threading.Thread(target=_server.serve_forever, name="VijuPC-HTTP", daemon=True)
    _server_thread.start()
    log(f"AGENT START {HOST}:{PORT}")


def stop_server():
    global _server
    s = _server
    _server = None
    if s is not None:
        try:
            s.shutdown(); s.server_close()
        except Exception:
            pass


def build_gui():
    import tkinter as tk
    from tkinter import messagebox, ttk

    class App(tk.Tk):
        def __init__(self):
            super().__init__()
            self.title("Viju_Trade PC - Dhan")
            self.geometry("920x760")
            self.minsize(760, 620)
            self.protocol("WM_DELETE_WINDOW", self.on_close)
            self.status_var = tk.StringVar()
            self.market_var = tk.StringVar(value="Waiting for engine data...")
            self.transit_var = tk.StringVar(value="NO ACTIVE TRANSIT")
            self.stats_var = tk.StringVar(value="No stats yet.")
            self.engine_source_var = tk.StringVar(value="Engine source: APK sync only")
            self.warning_var = tk.StringVar(value="No pending warning")
            self.signal_var = tk.StringVar()
            self._build()
            self.after(250, self.refresh)

        def _build(self):
            outer = ttk.Frame(self, padding=14)
            outer.pack(fill="both", expand=True)
            top = ttk.Frame(outer); top.pack(fill="x")
            ttk.Label(top, text="Viju_Trade PC • DHAN", font=("Segoe UI", 20, "bold")).pack(side="left")
            ttk.Button(top, text="Dhan Credentials", command=self.credentials).pack(side="right", padx=4)
            ttk.Button(top, text="PC Connection", command=self.connection).pack(side="right", padx=4)

            svc = ttk.LabelFrame(outer, text="SERVICE", padding=10); svc.pack(fill="x", pady=(12, 8))
            ttk.Label(svc, textvariable=self.status_var, font=("Segoe UI", 11)).pack(anchor="w")
            buttons = ttk.Frame(svc); buttons.pack(fill="x", pady=(8, 0))
            ttk.Button(buttons, text="START ENGINE", command=self.start_engine_safe).pack(side="left", expand=True, fill="x", padx=2)
            ttk.Button(buttons, text="STOP ENGINE", command=lambda: self.run_cmd("ENGINE_STOP")).pack(side="left", expand=True, fill="x", padx=2)
            ttk.Button(buttons, text="REFRESH DATA", command=lambda: self.run_cmd("REFRESH")).pack(side="left", expand=True, fill="x", padx=2)

            ttk.Label(outer, textvariable=self.engine_source_var).pack(anchor="w", pady=(0, 8))

            market = ttk.LabelFrame(outer, text="MARKET DATA", padding=10); market.pack(fill="x", pady=5)
            ttk.Label(market, textvariable=self.market_var, justify="left", wraplength=840).pack(anchor="w")

            transit = ttk.LabelFrame(outer, text="TRANSIT / INPUT", padding=10); transit.pack(fill="both", expand=True, pady=5)
            ttk.Label(transit, textvariable=self.transit_var, justify="left", wraplength=840).pack(anchor="w")
            ttk.Separator(transit).pack(fill="x", pady=8)
            ttk.Label(transit, textvariable=self.warning_var).pack(anchor="w")
            wr = ttk.Frame(transit); wr.pack(fill="x", pady=5)
            ttk.Button(wr, text="ACCEPT WARNING", command=self.accept_warning).pack(side="left", padx=2)
            ttk.Button(wr, text="DECLINE WARNING", command=self.decline_warning).pack(side="left", padx=2)
            ttk.Label(wr, text="Signal #").pack(side="left", padx=(18, 3))
            ttk.Entry(wr, textvariable=self.signal_var, width=8).pack(side="left")
            ttk.Button(wr, text="EXIT SIGNAL", command=self.exit_signal).pack(side="left", padx=3)
            ttk.Button(wr, text="CLOSE ALL", command=lambda: self.run_cmd("CLOSE_ALL")).pack(side="left", padx=3)

            stats = ttk.LabelFrame(outer, text="TODAY STATS", padding=10); stats.pack(fill="x", pady=5)
            ttk.Label(stats, textvariable=self.stats_var, justify="left", wraplength=840).pack(anchor="w")

        def run_cmd(self, action, extra=None):
            body = dict(extra or {}); body["action"] = action
            ok, msg = command(action, body)
            if not ok:
                messagebox.showerror("Viju_Trade", msg)
            self.refresh()

        def start_engine_safe(self):
            st = current_state()
            mobile_status = st.get("remote_mobile_engine_status", "UNKNOWN")
            mobile_connected = bool(st.get("remote_mobile_connected", False))
            if mobile_status == "RUNNING":
                if not mobile_connected:
                    messagebox.showwarning(
                        "Viju_Trade",
                        "Mobile was last known RUNNING, but the phone is not reachable now.\n\n"
                        "PC engine will NOT start because Dhan duplicate login cannot be ruled out."
                    )
                    return
                yes = messagebox.askyesno(
                    "Switch engine host to PC?",
                    "Mobile engine is currently RUNNING.\n\n"
                    "If you continue, Mobile will be told to stop first. "
                    "PC will wait for the Mobile engine to finish logout and report STOPPED. "
                    "Only then will the PC engine log in.\n\nContinue?"
                )
                if not yes:
                    return
                ok, msg = request_pc_host()
                if not ok:
                    messagebox.showerror("Viju_Trade", msg)
                self.refresh()
                return
            if mobile_status == "STOPPING":
                messagebox.showinfo("Viju_Trade", "Mobile engine is still stopping. PC will not log in yet.")
                return
            self.run_cmd("ENGINE_START")

        def accept_warning(self):
            st = current_state()
            if not st["warning_pending"]:
                messagebox.showinfo("Viju_Trade", "No pending Guardian warning")
                return
            self.run_cmd("ACCEPT", {"signal_no": st["warning_signal_no"], "warning_type": st["warning_type"], "premium": st["warning_current_premium"]})

        def decline_warning(self):
            st = current_state()
            if not st["warning_pending"]:
                messagebox.showinfo("Viju_Trade", "No pending Guardian warning")
                return
            self.run_cmd("DECLINE", {"signal_no": st["warning_signal_no"], "warning_type": st["warning_type"]})

        def exit_signal(self):
            try:
                n = int(self.signal_var.get().strip())
                if n <= 0: raise ValueError
            except Exception:
                messagebox.showerror("Viju_Trade", "Enter a valid signal number")
                return
            self.run_cmd("EXIT_SIGNAL", {"signal_no": n})

        def credentials(self):
            win = tk.Toplevel(self); win.title("Dhan Credentials"); win.geometry("640x620"); win.transient(self)
            env = load_env_file(SECRETS_FILE)
            vars_ = {}
            frame = ttk.Frame(win, padding=14); frame.pack(fill="both", expand=True)
            labels = {
                "DHAN_CLIENT_ID": "Dhan Client ID", "DHAN_API_KEY": "Dhan API Key", "DHAN_API_SECRET": "Dhan API Secret",
                "DHAN_REDIRECT_URL": "Redirect URL", "DHAN_PIN": "Dhan PIN", "DHAN_TOTP_SECRET": "TOTP Secret",
                "DHAN_ACCESS_TOKEN": "Access Token (optional)", "DHAN_TOKEN_EXPIRY": "Token Expiry (optional)",
                "OPENAI_API_KEY": "OpenAI API Key", "TELEGRAM_BOT_TOKEN": "Telegram Bot Token", "TELEGRAM_CHAT_ID": "Telegram Chat ID",
            }
            for i, key in enumerate(DHAN_KEYS):
                ttk.Label(frame, text=labels.get(key, key)).grid(row=i, column=0, sticky="w", pady=4)
                v = tk.StringVar(value=env.get(key, "")); vars_[key] = v
                e = ttk.Entry(frame, textvariable=v, width=52, show="•" if key in SENSITIVE_KEYS else "")
                e.grid(row=i, column=1, sticky="ew", pady=4)
            frame.columnconfigure(1, weight=1)
            def save():
                try:
                    save_env({k: v.get() for k, v in vars_.items()})
                    atomic_json(BROKER_SELECTION_FILE, {"schema": 1, "broker_selected": "DHAN", "selection_id": "windows-dhan"})
                    messagebox.showinfo("Viju_Trade", "Dhan credentials saved on this Windows PC")
                    win.destroy(); self.refresh()
                except Exception as exc:
                    messagebox.showerror("Viju_Trade", str(exc))
            ttk.Button(frame, text="SAVE DHAN CREDENTIALS", command=save).grid(row=len(DHAN_KEYS), column=0, columnspan=2, sticky="ew", pady=14)

        def connection(self):
            win = tk.Toplevel(self); win.title("PC Connection"); win.geometry("650x330"); win.transient(self)
            frame = ttk.Frame(win, padding=16); frame.pack(fill="both", expand=True)
            token_var = tk.StringVar(value=get_token())
            ttk.Label(frame, text=f"Server: http://{tailscale_ip()}:{PORT}", font=("Segoe UI", 12, "bold")).pack(anchor="w", pady=5)
            ttk.Label(frame, text="Use this server address and token in Android → PC Connection Credentials.").pack(anchor="w", pady=5)
            ttk.Label(frame, text="PC token").pack(anchor="w", pady=(12, 2))
            ttk.Entry(frame, textvariable=token_var, width=70).pack(fill="x")
            def save():
                try:
                    set_token(token_var.get())
                    messagebox.showinfo("Viju_Trade", "PC token saved. Use the same token in Android.")
                except Exception as exc:
                    messagebox.showerror("Viju_Trade", str(exc))
            ttk.Button(frame, text="SAVE TOKEN", command=save).pack(fill="x", pady=12)
            ttk.Label(frame, text="Engine .py selection is intentionally not available here. Update it only from the Android APK; the APK will sync the validated engine to this PC.", wraplength=600).pack(anchor="w", pady=8)

        def refresh(self):
            try:
                st = current_state()
                self.status_var.set(st["service_text"] + f"\nPC Tailscale IP: {st['tailscale_ip']}\nAgent: {st['version']}")
                self.market_var.set(st["market_text"])
                self.transit_var.set(st["transit_text"])
                self.stats_var.set(st["stats_text"])
                host = st.get("active_host", "NONE")
                handoff = st.get("handoff_status", "")
                self.engine_source_var.set(
                    f"Engine source: APK sync only | Engine V{st['engine_version']} | ACTIVE HOST: {host}"
                    + (f" | {handoff}" if handoff and "RUNNING" not in handoff else "")
                )
                if st["warning_pending"]:
                    self.warning_var.set(f"WARNING #{st['warning_signal_no']} {st['warning_type']} | Premium {st['warning_current_premium']:.2f} | {st['warning_reason']}")
                    self.signal_var.set(str(st["warning_signal_no"]))
                else:
                    self.warning_var.set("No pending warning")
            except Exception as exc:
                self.status_var.set("Agent error: " + str(exc))
            self.after(3000, self.refresh)

        def on_close(self):
            if engine_running():
                yes = messagebox.askyesno(
                    "Close Viju_Trade PC?",
                    "PC engine is RUNNING. Closing the PC app will first stop the engine and complete its Dhan logout.\n\nContinue?"
                )
                if not yes:
                    return
                stop_engine()
            try: stop_server()
            except Exception: pass
            self.destroy()

    return App()


def main():
    # Take ownership of the legacy V5 port before opening the GUI.
    retire_legacy_agent()
    ensure_project()
    tailscale_ip(force=True)
    try:
        start_server()
    except OSError as exc:
        # One extra reclaim attempt covers the case where V5 restarted while the
        # new app was launching.
        retire_legacy_agent()
        try:
            start_server()
        except OSError as exc2:
            import tkinter as tk
            from tkinter import messagebox
            root = tk.Tk(); root.withdraw()
            pid = _listening_pid_on_port(PORT)
            messagebox.showerror(
                "Viju_Trade PC",
                f"Port {PORT} is still occupied"
                + (f" by PID {pid}" if pid else "")
                + ".\n\nClose the old VijuTradeV5 agent/process once, then reopen this app.\n\n"
                + str(exc2)
            )
            root.destroy()
            return 2
    global _gui
    _gui = build_gui()
    _gui.mainloop()
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--engine-runner")
    args, _ = parser.parse_known_args()
    if args.engine_runner:
        try:
            engine_runner(args.engine_runner)
        except BaseException as exc:
            log("ENGINE RUNNER ERROR " + type(exc).__name__ + ": " + str(exc))
            raise
    else:
        raise SystemExit(main())
