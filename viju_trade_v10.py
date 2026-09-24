import csv
import atexit
import fcntl
import json
import logging
import math
import os
import re
import subprocess
import sys
import threading
import time
from collections import defaultdict, deque
from datetime import datetime, timedelta
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path
from zoneinfo import ZoneInfo

import pyotp
import pandas as pd
import requests
from logzero import logger
from openai import OpenAI
SmartConnect = SmartWebSocketV2 = None  # Imported only when ANGEL is selected.


# ============================================================================
# INDEX SIGNAL MONITOR V8.3.1 — DHAN PRIMARY
# ============================================================================
# SIGNALS/PAPER ACCOUNTING ONLY. No broker order execution.
# V8.8: persistent APK lot selector + full user-specified options round-trip charges in every live/final Net P/L.
# V8.3.1: AMD+POC exact state-machine/log/UI completion; explicit CE/PE, outcome dots, Transit Hit, and total active capital.
# V8.2: adds EXPERIMENTAL LIQUIDITY_SWEEP_IFVG_CISD as one independent strategy; existing strategies unchanged.
# V8.1: Dhan-only runtime; adds strategy/Guardian effectiveness and 09:00-15:00 engine downtime measurement.
# V7.5: persistent broker selection, Dhan auth/REST/history/Greeks/full WebSocket.
# Existing V7.1 strategy, signal, Guardian and P/L calculations are retained.
# V3.6.1: explicit LOGIN -> MARKET CONFIRMATION -> CLOSED/LIVE phase pipeline with staged data readiness.
# V3.7.1: single-engine lock + liquidity/market-structure opportunity layer + FVG timing support.
# V3.8.0: independent multi-strategy learning engine; any valid strategy can trigger without requiring other strategies to agree.
# V4.0: one-lot paper-money accounting. Every signal uses exactly one exchange lot,
# shows premium capital used, target profit, SL loss and Angel One F&O brokerage.
# V4.1: deterministic 5-minute candlestick-pattern sub-engine. Standard single-,
# double- and triple-candle patterns are recognised from completed OHLC bars and
# used only as a small confirmation bonus / research field; they never create a
# standalone TRANSIT and never override the existing safety gates.
# V4.1.1: Android presentation/data bridge fix. Full one-lot rupee economics are
# rendered from Python-owned signal data, and every Python notification is persisted
# for a same-day Notifications screen. No trading gate, strategy or order logic changed.
# V4.4: multiple strategy signals may remain active simultaneously. Each signal is
# exactly 1 lot and independently tracks live premium, target, SL, Guardian, warning
# acceptance and terminal P/L. One signal resolving never closes another signal.
# V4.4.1: accepting a TRANSIT/IMMEDIATE-EXIT warning financially closes that signal
# at the accepted premium, but a silent post-exit monitor keeps watching the original
# target/SL for research. The silent result never changes the locked P/L or emits an alert.
# Daily stats show gross paper P/L, brokerage and net-after-brokerage P/L.
# V8.9: outcome dots are exit-type only; signal/card NET and Today Positive/Negative are classified strictly by final P/L after full charges.
# V10.0 BASELINE: same proven V8.9-derived DHAN runtime; version frozen for the V10 Mobile + PC architecture.
# V8.0.3: Active-transit compact display is signal number + live NET P&L only (example: #30 | +₹3.00).\n# V8.0.2: Signals compact active row exposes live NET P&L + green/red state; Transit-warning exits expose blue UI color hint.\n# V8.0.1: TEMP mode — every Guardian TRANSIT/IMMEDIATE EXIT warning is shown, then automatically accepted/exited via the existing warning settlement path.\n# V8.0: Adds 8 independent research strategies: RVOL momentum, RVOL retest, volume exhaustion, NR7, Bollinger squeeze, ADX/DI expansion, inside-bar volume breakout, EMA+ADX pullback.\n# V7.9.1: Android/app notifications allow-listed to SIGNAL, TRANSIT/EXIT WARNING, SL, TARGET, connection loss, and engine stopped/error only.\n# V7.9: Reason display now identifies the exact strategy/setup before the brief approval reason.\n# V7.8: Signals menu unresolved trades read _current_option_snapshot() on every UI frame, matching first-page live TRANSIT pricing.
# V7.7: Signals menu overlays active in-memory WebSocket LTP/P&L onto persistent CSV history for live updates.\n# V7.6: active TRANSIT cards include a brief stored entry reason (final review reason / setup fallback).\n# V7.0 UI P/L traffic-light state: RED for negative gross P/L; AMBER when gross
# profit is positive but does not cover round-trip brokerage; GREEN when net P/L is positive.
# Applied consistently to active TRANSIT display and Today Signals history. No trade gates changed.
# V3.4 RESEARCH MODE: no daily signal cap and no CE/PE blocking from prior losses.
# V4.4 MULTI-TRANSIT: every independently approved strategy signal gets its own 1-lot TRANSIT and lifecycle.
# V4.4 decision order remains TECH -> FUNDAMENTAL -> OPTION/GREEKS -> LUNA -> independent TRANSIT.
# V6.8: persistent Angel login-state line in startup/CLOSED/LIVE UI; login/logout events are
# persisted to Notifications, and engine STOP performs best-effort Angel logout + local token clear.
# V3.4 makes FUNDAMENTAL direction deterministic after TECH: LONG->CE, SHORT->PE, BOTH->either.
# Opening-range breakout is now a fresh completed-candle crossing event, not merely price remaining outside OR.
# Re-arm protection prevents re-issuing the same completed-candle setup after a TRANSIT resolves.
# The 30-minute fundamental/news refresh stays active as a background cache.
# V3.4 keeps SHADOW learning: it learns per-strategy factor weights from outcomes,
# but NEVER applies those learned weights to live signals in this version.
#
# Android/Termux build: local monitor + Telegram alerts. The monitor SENDS only;
# telegram_controller_android.py is the sole Telegram getUpdates poller. No Windows
# Credential Manager, remote deployer, or Windows supervisor is used.
# ============================================================================

VERSION = "10.0"
SUPPORTED_BROKERS = ("DHAN",)
ENGINE_INTERFACE = "ANDROID_V31_COMPAT"
IST = ZoneInfo("Asia/Kolkata")

PROJECT_DIR = Path.home() / "NiftyMonitor"

def _selection_at_import():
    path = Path(os.environ.get("VIJU_BROKER_SELECTION_FILE") or PROJECT_DIR / "broker_selection.json")
    selected = os.environ.get("VIJU_BROKER") or os.environ.get("BROKER_SELECTED")
    if path.exists():
        value = json.loads(path.read_text(encoding="utf-8"))
        chosen = value.get("broker_selected")
        if selected and selected != chosen:
            raise RuntimeError("Broker selection file and environment disagree; restart engine")
        selected = chosen
    selected = selected or "DHAN"  # V8.1: Dhan is the final/primary broker.
    if selected not in SUPPORTED_BROKERS:
        raise RuntimeError("This engine is Dhan-only. Select Dhan in Credentials")
    return selected

BROKER_SELECTED = _selection_at_import()
BROKER_LABEL = "DHAN"

MASTER_FILE = PROJECT_DIR / "OpenAPIScripMaster.json"
CACHE_FILE = PROJECT_DIR / "nifty_5m_cache.csv"
SIGNAL_LOG_FILE = PROJECT_DIR / "index_v31_signals.csv"
HEARTBEAT_FILE = PROJECT_DIR / "index_v31_heartbeat.json"
RUNTIME_LOG_FILE = PROJECT_DIR / "index_v31_runtime.log"
SHADOW_LEARNING_STATE_FILE = PROJECT_DIR / "index_v29_shadow_learning.json"
LIVE_STATUS_FILE = PROJECT_DIR / "index_live_status.json"
APP_UI_FILE = PROJECT_DIR / "app_ui.json"
FUNDAMENTAL_CACHE_FILE = PROJECT_DIR / "fundamental_news_cache.json"
MANUAL_REFRESH_FILE = PROJECT_DIR / "manual_refresh.request"
WARNING_ACCEPT_FILE = PROJECT_DIR / "warning_accept.request"
WARNING_DECLINE_FILE = PROJECT_DIR / "warning_decline.request"
MANUAL_EXIT_FILE = PROJECT_DIR / "manual_exit.request"
CLOSE_ALL_TRANSITS_FILE = PROJECT_DIR / "close_all_transits.request"
REJECTED_SETUP_LOG_FILE = PROJECT_DIR / "index_v371_rejected_setups.csv"
ENGINE_LOCK_FILE = PROJECT_DIR / "viju_trade_engine.lock"
NOTIFICATION_LOG_FILE = PROJECT_DIR / "index_v411_notifications.jsonl"
NOTIFICATIONS_TODAY_FILE = PROJECT_DIR / "notifications_today.txt"
SIGNALS_TODAY_FILE = PROJECT_DIR / "signals_today.txt"
LOT_SETTINGS_FILE = PROJECT_DIR / "lot_settings.json"
# V8.2 experimental Sweep + iFVG + CISD strategy research/state files.
SWEEP_IFVG_STATE_FILE = PROJECT_DIR / "liquidity_sweep_ifvg_cisd_state.json"
SWEEP_IFVG_EVENT_LOG_FILE = PROJECT_DIR / "liquidity_sweep_ifvg_cisd_events.csv"
# V8.3 experimental AMD + Volume Profile POC retest strategy.
AMD_POC_STATE_FILE = PROJECT_DIR / "amd_volume_poc_retest_state.json"
AMD_POC_EVENT_LOG_FILE = PROJECT_DIR / "amd_volume_poc_retest_events.csv"
# V8.1 measurement layer: Dhan-first reliability + Guardian/strategy research.
DAILY_RESEARCH_REPORT_FILE = PROJECT_DIR / "daily_research_report.json"
STRATEGY_DAILY_REPORT_FILE = PROJECT_DIR / "strategy_daily_report.csv"
ENGINE_DOWNTIME_FILE = PROJECT_DIR / "engine_downtime.csv"
ENGINE_DOWNTIME_STATE_FILE = PROJECT_DIR / "engine_downtime_state.json"
DOWNTIME_WINDOW_START = (9, 0)
DOWNTIME_WINDOW_END = (15, 0)

MASTER_URLS = (
    "https://margincalculator.angelone.in/OpenAPI_File/files/OpenAPIScripMaster.json",
    "https://margincalculator.angelbroking.com/OpenAPI_File/files/OpenAPIScripMaster.json",
)

# Angel / market constants
# SmartAPI WebSocket exchange types:
# 1=nse_cm, 2=nse_fo, 3=bse_cm, 4=bse_fo
NSE_INDEX_EXCHANGE_TYPE = 1
NFO_EXCHANGE_TYPE = 2
BSE_INDEX_EXCHANGE_TYPE = 3
BFO_EXCHANGE_TYPE = 4

SPOT_EXCHANGE_BY_DERIVATIVE = {"NFO": "NSE", "BFO": "BSE"}
SPOT_WS_TYPE_BY_EXCHANGE = {"NSE": NSE_INDEX_EXCHANGE_TYPE, "BSE": BSE_INDEX_EXCHANGE_TYPE}
DERIV_WS_TYPE_BY_EXCHANGE = {"NFO": NFO_EXCHANGE_TYPE, "BFO": BFO_EXCHANGE_TYPE}

# Known SmartAPI AMXIDX spot-token fallbacks for NSE only. BSE indices are
# resolved from the daily Angel instrument master so stale BSE tokens are never hard-coded.
INDEX_SPOT_FALLBACKS = {
    "NIFTY": ("99926000", "Nifty 50"),
    "BANKNIFTY": ("99926009", "Nifty Bank"),
    "FINNIFTY": ("99926037", "Nifty Fin Service"),
    "MIDCPNIFTY": ("99926074", "NIFTY MID SELECT"),
}
INDEX_ALIASES = {
    "NIFTY": ("NIFTY", "NIFTY 50", "NIFTY50"),
    "BANKNIFTY": ("BANKNIFTY", "NIFTY BANK", "NIFTYBANK"),
    "FINNIFTY": ("FINNIFTY", "NIFTY FIN SERVICE", "NIFTYFINSERVICE"),
    "MIDCPNIFTY": ("MIDCPNIFTY", "NIFTY MID SELECT", "NIFTYMIDSELECT"),
    "NIFTYNXT50": ("NIFTYNXT50", "NIFTY NEXT 50", "NIFTYNEXT50"),
    "NIFTYFPI": ("NIFTYFPI", "NIFTY INDIA FPI 150", "NIFTYINDIAFPI150"),
    "SENSEX": ("SENSEX", "BSE SENSEX", "S&P BSE SENSEX"),
    "BANKEX": ("BANKEX", "BSE BANKEX", "S&P BSE BANKEX"),
    "SENSEX50": ("SENSEX50", "SENSEX 50", "BSE SENSEX 50", "S&P BSE SENSEX 50"),
}

# V3.4 scans both NSE/NFO and BSE/BFO index-option families.
# Only contracts actually present in Angel's daily instrument master are eligible.
SUPPORTED_NSE_INDEX_ROOTS = ("NIFTY", "BANKNIFTY", "FINNIFTY", "MIDCPNIFTY", "NIFTYNXT50", "NIFTYFPI")
SUPPORTED_BSE_INDEX_ROOTS = ("SENSEX", "BANKEX", "SENSEX50")

# OpenAI models
BACKGROUND_MODEL = "gpt-5.6-luna"
FINAL_MODEL = "gpt-5.6-luna"

# Schedule
PROGRAM_START_HOUR = 9
PROGRAM_START_MINUTE = 15
TRADE_START_HOUR = 9
TRADE_START_MINUTE = 15
SIGNAL_CUTOFF_HOUR = 15
SIGNAL_CUTOFF_MINUTE = 0
ENGINE_STOP_HOUR = 15
ENGINE_STOP_MINUTE = 30

# Fundamental engine
FUNDAMENTAL_REFRESH_SECONDS = 30 * 60
FUNDAMENTAL_ERROR_RETRY_SECONDS = 2 * 60

# TRANSIT Guardian (Luna)
TRANSIT_GUARDIAN_INTERVAL_SECONDS = 120
TRANSIT_GUARDIAN_FAST_RECHECK_SECONDS = 45
TRANSIT_GUARDIAN_MIN_AGE_SECONDS = 75
TRANSIT_GUARDIAN_EXIT_CONFIDENCE = 75
AUTO_ACCEPT_ALL_TRANSIT_WARNINGS = True  # TEMP V8.0.1: warning pops, then paper TRANSIT auto-exits
TRANSIT_GUARDIAN_WARNING_CONFIDENCE = 70
TRANSIT_TIME_STOP_SECONDS = 12 * 60

# Angel REST discipline
ANGEL_REST_MIN_GAP_SECONDS = 1.25
# Historical candles are deliberately much slower than other REST calls. Angel's
# getCandleData endpoint proved rate-limit sensitive during full-day testing.
HISTORICAL_MIN_GAP_SECONDS = 5.0
HISTORICAL_RATE_LIMIT_BACKOFF_SECONDS = (15, 30, 60, 120)
HISTORICAL_SEED_ATTEMPTS = 2
HISTORICAL_SEED_RETRY_SECONDS = 15
# LIVE history repair is low priority: WebSocket builds new candles; REST history
# only seeds the baseline or repairs a proven completed-candle gap.
HISTORICAL_RECOVERY_COOLDOWN_SECONDS = 600
HISTORICAL_BACKFILL_LOOKBACK_DAYS = 7
GREEKS_REFRESH_SECONDS = 60

# Option selection / risk geometry
ACCOUNT_CAPITAL = 100000.0
# V8.8: APK writes lot_settings.json. The selected value is used for every NEW signal
# until the user changes it. Existing transits keep the lots stored at their entry.
DEFAULT_LOTS_PER_SIGNAL = 1
MIN_LOTS_PER_SIGNAL = 1
MAX_LOTS_PER_SIGNAL = 100
# Backward-compatible fallback for legacy rows/code paths. Do not use this as the
# live selector; current_lots_per_signal() is authoritative for new signals.
LOTS_PER_SIGNAL = DEFAULT_LOTS_PER_SIGNAL
# Allow the selected quantity only while the premium outlay fits configured capital.
MAX_POSITION_COST = ACCOUNT_CAPITAL

# V8.8 user-specified 2026 options round-trip charge model.
# Brokerage: Rs20 buy order + Rs20 sell order, independent of quantity.
# STT: 0.15% sell turnover only. NSE exchange charge: 0.03503% total turnover.
# Stamp: 0.003% buy turnover only. SEBI: Rs10/crore = 0.0001% total turnover.
# GST: 18% of Brokerage + Exchange Transaction Charge only, exactly as requested.
ANGEL_FO_BROKERAGE_PER_EXECUTED_ORDER = 20.0
OPTIONS_STT_SELL_RATE = Decimal("0.0015")
OPTIONS_NSE_EXCHANGE_RATE = Decimal("0.0003503")
OPTIONS_STAMP_BUY_RATE = Decimal("0.00003")
OPTIONS_SEBI_RATE = Decimal("0.000001")
OPTIONS_GST_RATE = Decimal("0.18")
CHARGE_MODEL = "USER_SPECIFIED_ANGEL_OPTIONS_2026"
ANGEL_BROKERAGE_SOURCE = "USER_SPECIFIED_2026_RATE_CARD"
MONEY_MODEL = "MULTI_LOT_PAPER_PNL_FULL_ROUND_TRIP_CHARGES"

MAX_REFERENCE_RISK_RUPEES = 800.0
# V3.7.3: give the option premium more breathing room, but do not solve poor
# entry timing by simply doubling loss size. Risk is volatility-adaptive and
# capped by rupee risk, premium points, and 10% of the option entry premium.
OPTION_RISK_MIN_POINTS = 7.0
OPTION_RISK_MAX_POINTS = 12.0
OPTION_RISK_MAX_ENTRY_PCT = 10.0
OPTION_VOL_WINDOW_SECONDS = 60
OPTION_VOL_RANGE_MULTIPLIER = 1.00
MIN_OPTION_SCORE = 57.0
MAX_SPREAD_PCT = 1.50
MAX_ENTRY_DRIFT_PCT = 1.50

# V3.7.4 learning mode: no post-trade re-entry cooldown.
# If a fresh completed-candle setup satisfies all normal technical, option,
# fundamental/Luna and safety gates, it may generate another signal immediately.
REENTRY_COOLDOWN_AFTER_LOSS_SECONDS = 0
REENTRY_COOLDOWN_AFTER_TARGET_SECONDS = 0
REENTRY_COOLDOWN_AFTER_SESSION_EXIT_SECONDS = 0
PREMIUM_ACCEPTANCE_CONTINUATION_30S = 0.20
PREMIUM_ACCEPTANCE_STRONG_30S = 0.00
POST_REVIEW_TIMING_RECHECK_SECONDS = 15

# V3.7.0 learning-phase quality gates. These are only slightly looser than V3.6.8;
# live WebSocket health, Futures VWAP direction, anti-chase, hard fundamental conflict,
# Greeks/liquidity and final review remain mandatory.
MIN_TECH_SCORE = 65.0
MIN_COMBINED_SCORE = 65.0
MIN_ADX = 18.0
MIN_ADX_B_GRADE = 21.0
MIN_ADX_INSIDE_OR = 23.0
MIN_DI_GAP_B_GRADE = 4.0
WEBSOCKET_SIGNAL_BLOCK_SECONDS = 20
FUNDAMENTAL_SUPPORT_NEUTRAL = 50.0

# Sustained-trend recognition + anti-chase. Trend recognition is slightly easier,
# but the 1.50 ATR anti-chase protection is deliberately unchanged.
STRONG_TREND_MIN_ADX = 28.0
STRONG_TREND_MIN_DI_GAP = 10.0
STRONG_TREND_MAX_EMA20_DISTANCE_PCT = 1.40
ANTI_CHASE_CANDLE_ATR_MULT = 1.50

# Luna WAIT is temporary in learning mode: the same completed-candle setup may be
# reviewed two more times if it is still technically valid and timing improves.
LUNA_WAIT_REVIEW_DELAY_SECONDS = 30
LUNA_WAIT_MAX_RECHECKS = 2

# Diagnostics are logged on state changes and periodically while LIVE.
DATA_HEALTH_LOG_INTERVAL_SECONDS = 30
API_HEALTH_SUMMARY_INTERVAL_SECONDS = 15 * 60
API_HEALTH_ISSUE_REPEAT_SECONDS = 5 * 60
REJECTED_SETUP_OUTCOME_HORIZONS = (5, 10, 15)

# V3.7.1 liquidity/structure layer. These are EXTRA opportunities/bonuses only.
# Absence of a sweep/FVG never blocks an existing V3.7.0 setup.
LIQUIDITY_LOOKBACK_CANDLES = 6
LIQUIDITY_SWEEP_ATR_BUFFER = 0.04
LIQUIDITY_RECLAIM_MIN_ADX = 18.0
LIQUIDITY_BREAK_MIN_ADX = 21.0
LIQUIDITY_CONFIRM_BONUS = 4.0
FVG_CONFIRM_BONUS = 3.0
FVG_MAX_AGE_CANDLES = 8
FVG_MIN_SIZE_ATR = 0.05
FVG_RETEST_MIN_ADX = 21.0

# V8.2 EXPERIMENTAL — independent Liquidity Sweep -> HTF FVG -> LTF iFVG -> CISD.
# These constants affect only the new strategy. No existing strategy reads them.
SWEEP_IFVG_STRATEGY_ID = "LIQUIDITY_SWEEP_IFVG_CISD"
SWEEP_IFVG_SETUP_NAME = "LIQUIDITY SWEEP + IFVG + CISD"
SWEEP_IFVG_SHORT_NAME = "SWEEP + IFVG"
SWEEP_IFVG_STATUS = "EXPERIMENTAL"
SWEEP_IFVG_HTF_MINUTES = 60
SWEEP_IFVG_EXECUTION_MINUTES = 5  # parameterized so a future 1m data engine can set this to 1
SWEEP_IFVG_PIVOT_LEFT = 2
SWEEP_IFVG_PIVOT_RIGHT = 2
SWEEP_IFVG_PIVOT_LOOKBACK_BARS = 72
SWEEP_IFVG_HTF_LOOKBACK_BARS = 24
SWEEP_IFVG_HTF_NEAR_RANGE_FRACTION = 0.20
SWEEP_IFVG_LTF_MIN_GAP_ATR = 0.05
SWEEP_IFVG_MAX_SETUP_BARS = 36
SWEEP_IFVG_TARGET_LOOKBACK_BARS = 72
SWEEP_IFVG_TECH_SCORE = 88.0

# V8.3 EXPERIMENTAL — independent Accumulation -> Manipulation -> Futures Volume POC -> Retest.
# These parameters are isolated to AMD_VOLUME_POC_RETEST and do not alter existing strategies.
AMD_POC_STRATEGY_ID = "AMD_VOLUME_POC_RETEST"
AMD_POC_SETUP_NAME = "AMD + POC RETEST"
AMD_POC_SHORT_NAME = "AMD + POC RETEST"
AMD_POC_STATUS = "EXPERIMENTAL"
AMD_POC_MIN_RANGE_CANDLES = 8
AMD_POC_MAX_RANGE_CANDLES = 18
AMD_POC_MAX_RANGE_WIDTH_PCT = 0.60
AMD_POC_MAX_RANGE_ATR_MULT = 3.00
AMD_POC_MIN_HIGH_TOUCHES = 2
AMD_POC_MIN_LOW_TOUCHES = 2
AMD_POC_TOUCH_TOLERANCE_ATR = 0.20
# Minimum sweep excursion must satisfy BOTH market structure and a configurable
# percentage/ATR floor. Percentage values in this AMD section are percent units:
# 0.05 means 0.05%, 0.10 means 0.10%, etc.
AMD_POC_MIN_MANIPULATION_ATR = 0.10
AMD_POC_MIN_MANIPULATION_PCT = 0.05
# A sweep wick is allowed outside the range, but a close beyond this distance is
# treated as a true breakout and invalidates the setup before manipulation.
AMD_POC_MAX_BREAKOUT_BEFORE_MANIP_PCT = 0.10
AMD_POC_MAX_BREAKOUT_BEFORE_MANIP_ATR = 0.20
AMD_POC_RETEST_TOLERANCE_ATR = 0.18
AMD_POC_RETEST_TOLERANCE_PCT = 0.06
AMD_POC_CONFIRM_BODY_MIN_RATIO = 0.35
AMD_POC_MAX_SETUP_BARS = 24
AMD_POC_PROFILE_BINS = 24
AMD_POC_MIN_BIN_POINTS = 1.0
AMD_POC_SL_BUFFER_ATR = 0.05
AMD_POC_SL_BUFFER_PCT = 0.02
AMD_POC_TECH_SCORE = 87.0
# Structural target metadata only. Existing option premium target/Guardian/SL
# management remains unchanged and continues to own the final option trade.
AMD_POC_TARGET_MODE = "OPPOSITE_RANGE"  # OPPOSITE_RANGE / PREVIOUS_SWING / LIQUIDITY_ZONE / FIXED_RR / EXTERNAL
AMD_POC_FIXED_RR = 2.0
AMD_POC_TARGET_LOOKBACK_BARS = 24

# V3.8.0 additional independent strategy engines. These do not need confirmation
# from the other named strategies; each can create its own technical opportunity.
WEAPON15_MIN_ADX = 18.0
WEAPON15_RSI_BULL_MIN = 52.0
WEAPON15_RSI_BULL_MAX = 72.0
WEAPON15_RSI_BEAR_MIN = 28.0
WEAPON15_RSI_BEAR_MAX = 48.0
WEAPON15_MIN_BODY_ATR = 0.10
VWAP_EVENT_MIN_ADX = 18.0
VWAP_EVENT_MIN_DI_GAP = 2.0
MAX_TECH_STRATEGY_VARIANTS = 24

# V8.0 additional strategy-lab candidates (completed 5-minute candles only).
# These are deliberately conservative starting hypotheses; shadow/backtest results
# should decide later tuning, not a claimed universal "best" parameter set.
VOLUME_RVOL_LOOKBACK = 20
VOLUME_RVOL_MIN = 1.50
VOLUME_BODY_RATIO_MIN = 0.60
VOLUME_BREAK_LOOKBACK = 6
VOLUME_EXHAUST_RVOL_MIN = 2.20
VOLUME_EXHAUST_WICK_RATIO_MIN = 0.45
NR_LOOKBACK = 7
NR_BREAK_VOLUME_RVOL_MIN = 1.20
BB_LENGTH = 20
BB_STD = 2.0
BB_SQUEEZE_LOOKBACK = 20
BB_SQUEEZE_RATIO = 0.75
ADX_EXPANSION_MIN_RISE = 2.0
DI_EXPANSION_MIN_GAP = 5.0
INSIDE_BAR_VOLUME_RVOL_MIN = 1.20

# V4.1 deterministic candlestick-pattern recognition (completed 5-minute bars).
# Confirmation only: a detected pattern can add a small score bonus to an already
# valid CE/PE setup. It NEVER creates a setup by itself and never hard-blocks one.
CANDLE_PATTERN_ENGINE_VERSION = "1.0"
CANDLE_DOJI_BODY_MAX_RATIO = 0.10
CANDLE_SMALL_BODY_MAX_RATIO = 0.30
CANDLE_LONG_BODY_MIN_RATIO = 0.55
CANDLE_MARUBOZU_BODY_MIN_RATIO = 0.85
CANDLE_MARUBOZU_WICK_MAX_RATIO = 0.08
CANDLE_SINGLE_CONFIRM_BONUS = 1.50
CANDLE_DOUBLE_CONFIRM_BONUS = 2.50
CANDLE_TRIPLE_CONFIRM_BONUS = 3.50
CANDLE_MAX_CONFIRM_BONUS = 3.50


# V3.4 research mode: no loss-count, side, or daily signal cap.

# Weighted score passed to Luna final review
TECH_SCORE_WEIGHT = 0.45
OPTION_SCORE_WEIGHT = 0.40
FUNDAMENTAL_SCORE_WEIGHT = 0.15


# V3.4 SHADOW LEARNING
# This learner NEVER changes a live signal in V3.4. It only observes resolved
# TRANSITs, estimates per-strategy factor usefulness, and writes suggested weights
# for later review. A future version may use them only after explicit approval.
SHADOW_REVIEW_AFTER_RESOLVED = 50
SHADOW_MIN_STRATEGY_SAMPLES = 10
SHADOW_PRIOR_STRENGTH = 20.0
SHADOW_MAX_RELATIVE_SHIFT = 0.15

SHADOW_BASE_WEIGHTS = {
    "OPENING RANGE BREAKOUT": {
        "adx_di": 0.22,
        "ema_structure": 0.12,
        "opening_range": 0.20,
        "futures_vwap": 0.14,
        "option_momentum": 0.14,
        "option_quality": 0.12,
        "fundamental": 0.06,
    },
    "OPENING RANGE RETEST": {
        "adx_di": 0.18,
        "ema_structure": 0.12,
        "opening_range": 0.24,
        "futures_vwap": 0.14,
        "option_momentum": 0.12,
        "option_quality": 0.14,
        "fundamental": 0.06,
    },
    "EMA20 PULLBACK CONTINUATION": {
        "adx_di": 0.18,
        "ema_structure": 0.25,
        "opening_range": 0.05,
        "futures_vwap": 0.14,
        "option_momentum": 0.14,
        "option_quality": 0.14,
        "fundamental": 0.10,
    },
    "DAY HIGH CONTINUATION": {
        "adx_di": 0.20,
        "ema_structure": 0.14,
        "opening_range": 0.08,
        "futures_vwap": 0.16,
        "option_momentum": 0.16,
        "option_quality": 0.16,
        "fundamental": 0.10,
    },
    "DAY LOW CONTINUATION": {
        "adx_di": 0.20,
        "ema_structure": 0.14,
        "opening_range": 0.08,
        "futures_vwap": 0.16,
        "option_momentum": 0.16,
        "option_quality": 0.16,
        "fundamental": 0.10,
    },
    "STRONG TREND CONTINUATION": {
        "adx_di": 0.26,
        "ema_structure": 0.20,
        "opening_range": 0.04,
        "futures_vwap": 0.18,
        "option_momentum": 0.10,
        "option_quality": 0.12,
        "fundamental": 0.10,
    },
    "LIQUIDITY SWEEP REVERSAL": {
        "adx_di": 0.20, "ema_structure": 0.10, "opening_range": 0.05,
        "futures_vwap": 0.18, "option_momentum": 0.17,
        "option_quality": 0.16, "fundamental": 0.14,
    },
    "LIQUIDITY BREAK CONTINUATION": {
        "adx_di": 0.22, "ema_structure": 0.14, "opening_range": 0.06,
        "futures_vwap": 0.18, "option_momentum": 0.16,
        "option_quality": 0.14, "fundamental": 0.10,
    },
    "FVG RETEST CONTINUATION": {
        "adx_di": 0.20, "ema_structure": 0.18, "opening_range": 0.04,
        "futures_vwap": 0.18, "option_momentum": 0.15,
        "option_quality": 0.15, "fundamental": 0.10,
    },
    "WEAPON CANDLE 15M": {
        "adx_di": 0.16, "ema_structure": 0.20, "opening_range": 0.04,
        "futures_vwap": 0.18, "option_momentum": 0.16,
        "option_quality": 0.16, "fundamental": 0.10,
    },
    "VWAP RECLAIM": {
        "adx_di": 0.16, "ema_structure": 0.12, "opening_range": 0.04,
        "futures_vwap": 0.26, "option_momentum": 0.16,
        "option_quality": 0.16, "fundamental": 0.10,
    },
    "VWAP REJECTION": {
        "adx_di": 0.16, "ema_structure": 0.12, "opening_range": 0.04,
        "futures_vwap": 0.26, "option_momentum": 0.16,
        "option_quality": 0.16, "fundamental": 0.10,
    },
    "HIGH VOLUME MOMENTUM": {
        "adx_di": 0.18, "ema_structure": 0.12, "opening_range": 0.04,
        "futures_vwap": 0.18, "option_momentum": 0.20,
        "option_quality": 0.18, "fundamental": 0.10,
    },
    "HIGH VOLUME BREAKOUT RETEST": {
        "adx_di": 0.16, "ema_structure": 0.12, "opening_range": 0.05,
        "futures_vwap": 0.20, "option_momentum": 0.17,
        "option_quality": 0.20, "fundamental": 0.10,
    },
    "VOLUME EXHAUSTION REVERSAL": {
        "adx_di": 0.10, "ema_structure": 0.10, "opening_range": 0.04,
        "futures_vwap": 0.20, "option_momentum": 0.20,
        "option_quality": 0.20, "fundamental": 0.16,
    },
    "NR7 COMPRESSION BREAKOUT": {
        "adx_di": 0.18, "ema_structure": 0.12, "opening_range": 0.04,
        "futures_vwap": 0.18, "option_momentum": 0.18,
        "option_quality": 0.18, "fundamental": 0.12,
    },
    "BOLLINGER SQUEEZE BREAKOUT": {
        "adx_di": 0.16, "ema_structure": 0.10, "opening_range": 0.04,
        "futures_vwap": 0.18, "option_momentum": 0.20,
        "option_quality": 0.20, "fundamental": 0.12,
    },
    "ADX DI EXPANSION": {
        "adx_di": 0.30, "ema_structure": 0.16, "opening_range": 0.03,
        "futures_vwap": 0.18, "option_momentum": 0.13,
        "option_quality": 0.12, "fundamental": 0.08,
    },
    "INSIDE BAR VOLUME BREAKOUT": {
        "adx_di": 0.16, "ema_structure": 0.12, "opening_range": 0.04,
        "futures_vwap": 0.18, "option_momentum": 0.20,
        "option_quality": 0.18, "fundamental": 0.12,
    },
    "EMA ADX PULLBACK CONFIRMATION": {
        "adx_di": 0.24, "ema_structure": 0.24, "opening_range": 0.03,
        "futures_vwap": 0.17, "option_momentum": 0.14,
        "option_quality": 0.10, "fundamental": 0.08,
    },
    "DEFAULT": {
        "adx_di": 0.18,
        "ema_structure": 0.18,
        "opening_range": 0.10,
        "futures_vwap": 0.15,
        "option_momentum": 0.15,
        "option_quality": 0.14,
        "fundamental": 0.10,
    },
}

# Health / watchdog
HEARTBEAT_SECONDS = 5
HEARTBEAT_STALE_SECONDS = 35
WEBSOCKET_STALE_SECONDS = 25
TECHNICAL_STALE_SECONDS = 8 * 60
FUNDAMENTAL_STALE_SECONDS = 40 * 60
GREEKS_STALE_SECONDS = 3 * 60
FUTURES_STALE_SECONDS = 25
MARKET_PROBE_TRADE_FRESH_SECONDS = 180
MARKET_PROBE_FEED_FRESH_SECONDS = 120
MARKET_PROBE_CANDLE_FRESH_MINUTES = 12
HEALTH_ALERT_COOLDOWN_SECONDS = 5 * 60

# V3.6 phase/readiness timing
LOGIN_RETRY_SECONDS = 10
MARKET_CONFIRM_TIMEOUT_SECONDS = 60
MARKET_CONFIRM_INTERVAL_SECONDS = 4
MARKET_CONFIRM_CONSECUTIVE = 2
LIVE_CANDLE_RETRY_SECONDS = 5
LIVE_CANDLE_DUE_GRACE_SECONDS = 60
LIVE_GREEKS_GRACE_SECONDS = 60

# V3.6.2 WebSocket self-healing.  A stale feed blocks entries immediately,
# attempts REST verification + socket reconnect + fresh Angel login silently,
# and notifies only if the full recovery window fails.
WEBSOCKET_RECOVERY_WARN_SECONDS = 60
WEBSOCKET_RECONNECT_WAIT_SECONDS = 15
WEBSOCKET_RECOVERY_RETRY_COOLDOWN_SECONDS = 45
WEBSOCKET_HEALTHY_TICKS_REQUIRED = 3
WEBSOCKET_RECOVERY_POLL_SECONDS = 0.5

# Android secrets are loaded from ~/NiftyMonitor/.secrets.env (chmod 600).
# Never hard-code credentials in this Python file.
SECRETS_FILE = PROJECT_DIR / ".secrets.env"

# Suppress verbose SmartAPI output that may expose request headers.
logger.setLevel(logging.CRITICAL)
for _h in list(getattr(logger, "handlers", [])):
    try:
        _h.setLevel(100)
    except Exception:
        pass


# ============================================================================
# LOGGING
# ============================================================================

PROJECT_DIR.mkdir(parents=True, exist_ok=True)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
    handlers=[
        # V8.0.4: one cumulative report file. Never truncate it at startup/day change.
        # Each new day's runtime/network/API diagnostics are appended to the same
        # index_v31_runtime.log, so Export Data carries Day 1 -> current date history.
        logging.FileHandler(RUNTIME_LOG_FILE, mode="a", encoding="utf-8"),
        logging.StreamHandler(sys.stdout),
    ],
)
log = logging.getLogger("index_v35_android")

_ENGINE_LOCK_HANDLE = None
_ENGINE_INSTANCE_ID = f"{os.getpid()}-{int(time.time())}"

def acquire_single_engine_lock():
    """Allow exactly one Viju_Trade Python engine process at a time."""
    global _ENGINE_LOCK_HANDLE
    fh = open(ENGINE_LOCK_FILE, "a+", encoding="utf-8")
    try:
        fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        fh.seek(0)
        owner = fh.read().strip() or "UNKNOWN"
        log.error(
            "DUPLICATE ENGINE BLOCKED | new_pid=%s | existing=%s",
            os.getpid(), owner
        )
        fh.close()
        return False

    fh.seek(0)
    fh.truncate()
    fh.write(
        f"pid={os.getpid()} instance={_ENGINE_INSTANCE_ID} "
        f"started_ist={now_ist().isoformat() if 'now_ist' in globals() else datetime.now().isoformat()}\n"
    )
    fh.flush()
    os.fsync(fh.fileno())
    _ENGINE_LOCK_HANDLE = fh
    log.info(
        "ENGINE INSTANCE STARTED | pid=%s | instance=%s | LOCK ACQUIRED",
        os.getpid(), _ENGINE_INSTANCE_ID
    )
    return True

def release_single_engine_lock():
    global _ENGINE_LOCK_HANDLE
    fh = _ENGINE_LOCK_HANDLE
    if fh is None:
        return
    try:
        log.info(
            "ENGINE INSTANCE STOPPED | pid=%s | instance=%s | LOCK RELEASED",
            os.getpid(), _ENGINE_INSTANCE_ID
        )
        fcntl.flock(fh.fileno(), fcntl.LOCK_UN)
        fh.close()
    except Exception:
        pass
    _ENGINE_LOCK_HANDLE = None

atexit.register(release_single_engine_lock)


# ============================================================================
# COMMON HELPERS
# ============================================================================

def now_ist():
    return datetime.now(IST)


def today_at(hour, minute):
    n = now_ist()
    return n.replace(hour=hour, minute=minute, second=0, microsecond=0)


def before_signal_start():
    return now_ist() < today_at(TRADE_START_HOUR, TRADE_START_MINUTE)


def after_signal_cutoff():
    return now_ist() >= today_at(SIGNAL_CUTOFF_HOUR, SIGNAL_CUTOFF_MINUTE)


def after_engine_stop():
    return now_ist() >= today_at(ENGINE_STOP_HOUR, ENGINE_STOP_MINUTE)


def market_continuous_session():
    n = now_ist()
    start = n.replace(hour=9, minute=15, second=0, microsecond=0)
    end = n.replace(hour=15, minute=30, second=0, microsecond=0)
    return start <= n <= end


def safe_float(value, default=None):
    try:
        return float(value)
    except Exception:
        return default


def safe_int(value, default=0):
    try:
        return int(value)
    except Exception:
        try:
            return int(float(value))
        except Exception:
            return default


def tick_round(value):
    return round(round(float(value) / 0.05) * 0.05, 2)


def contract_label(item):
    """Compact nearest-expiry option label, e.g. 23500 PE."""
    try:
        strike = int(round(float(item.get("strike"))))
        side = str(item.get("side", "")).upper().strip()
        return f"{strike} {side}".strip()
    except Exception:
        return str(item.get("symbol", "OPTION"))


def rupee(value):
    """Compact rupee formatting for the Android/notification text."""
    try:
        return f"₹{float(value):,.2f}"
    except Exception:
        return "₹--"


def rupee_signed(value):
    """Accounting-style signed rupee formatting, e.g. +₹325.00 / -₹365.00."""
    try:
        v = float(value)
        sign = "+" if v > 0 else "-" if v < 0 else ""
        return f"{sign}₹{abs(v):,.2f}"
    except Exception:
        return "₹--"


def pnl_traffic_state(gross_pnl, brokerage, net_pnl=None):
    """V7.0 display-only traffic light for live and locked paper P/L.

    RED   : gross P/L < 0 (trade itself is losing)
    AMBER : gross P/L >= 0 but does not cover round-trip brokerage
    GREEN : net P/L > 0 after brokerage
    This helper never changes entry/exit/risk decisions.
    """
    gross = safe_float(gross_pnl, 0.0) or 0.0
    fees = max(0.0, safe_float(brokerage, 0.0) or 0.0)
    net = safe_float(net_pnl)
    if net is None:
        net = gross - fees

    if gross < 0:
        return "RED", "🔴"
    if net <= 0:
        return "AMBER", "🟠"
    return "GREEN", "🟢"


def net_amount_marker(net_pnl):
    """V8.9 NET colour rule: profit green; loss/non-profit red.

    The card/header NET amount must never use amber or blue. Exact zero is not
    a profit, so it uses the red presentation colour while statistics still
    classify an exact zero result as FLAT.
    """
    net = safe_float(net_pnl, 0.0) or 0.0
    if net > 0:
        return "🟢", "green"
    return "🔴", "red"


def _money_decimal(value):
    return Decimal(str(value))


def _money_2(value):
    return float(Decimal(value).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))


def current_lots_per_signal():
    """Read the APK's persistent lot selector. Missing/invalid file safely means 1 lot."""
    try:
        if LOT_SETTINGS_FILE.exists():
            obj = json.loads(LOT_SETTINGS_FILE.read_text(encoding="utf-8"))
            value = safe_int(obj.get("lots_per_signal"), DEFAULT_LOTS_PER_SIGNAL)
        else:
            value = DEFAULT_LOTS_PER_SIGNAL
    except Exception:
        value = DEFAULT_LOTS_PER_SIGNAL
    return max(MIN_LOTS_PER_SIGNAL, min(MAX_LOTS_PER_SIGNAL, int(value)))


def option_round_trip_charges(buy_premium, sell_premium, quantity):
    """Calculate the requested complete options round-trip charge breakdown.

    Assumption: all selected lots are bought in ONE order and sold in ONE order.
    The flat brokerage is therefore Rs20 + Rs20 even when lot count increases.
    """
    qty = Decimal(max(1, int(quantity)))
    buy = _money_decimal(buy_premium)
    sell = _money_decimal(sell_premium)
    buy_turnover = qty * buy
    sell_turnover = qty * sell
    total_turnover = buy_turnover + sell_turnover
    brokerage = _money_decimal(ANGEL_FO_BROKERAGE_PER_EXECUTED_ORDER) * Decimal("2")
    stt = sell_turnover * OPTIONS_STT_SELL_RATE
    exchange = total_turnover * OPTIONS_NSE_EXCHANGE_RATE
    stamp = buy_turnover * OPTIONS_STAMP_BUY_RATE
    sebi = total_turnover * OPTIONS_SEBI_RATE
    gst = (brokerage + exchange) * OPTIONS_GST_RATE
    total = brokerage + stt + exchange + stamp + sebi + gst
    return {
        "buy_turnover": _money_2(buy_turnover),
        "sell_turnover": _money_2(sell_turnover),
        "total_turnover": _money_2(total_turnover),
        "brokerage_only": _money_2(brokerage),
        "stt": _money_2(stt),
        "exchange_transaction_charges": _money_2(exchange),
        "stamp_duty": _money_2(stamp),
        "sebi_charges": _money_2(sebi),
        "gst": _money_2(gst),
        "total_charges": _money_2(total),
        "charge_model": CHARGE_MODEL,
        # exact unrounded value retained internally for final net arithmetic
        "_total_charges_exact": float(total),
    }


def one_lot_money(entry, target, sl, lot_size, exit_price=None, lots=None):
    """Backward-compatible money helper, now multi-lot and full-charge aware.

    `lots` is frozen into each signal at entry. When omitted (new signal path),
    the current APK lot selector is used. Final/live net P/L uses the actual or
    hypothetical sell premium, so STT/exchange/SEBI/GST update with the exit price.
    """
    entry = float(entry)
    target = float(target)
    sl = float(sl)
    lot_size = max(1, int(float(lot_size)))
    lots = current_lots_per_signal() if lots is None else max(MIN_LOTS_PER_SIGNAL, min(MAX_LOTS_PER_SIGNAL, int(lots)))
    quantity = lot_size * lots
    amount_used = entry * quantity
    target_gross = (target - entry) * quantity
    sl_gross = (sl - entry) * quantity

    entry_charges = option_round_trip_charges(entry, entry, quantity)
    target_charges = option_round_trip_charges(entry, target, quantity)
    sl_charges = option_round_trip_charges(entry, sl, quantity)

    target_net = target_gross - float(target_charges["_total_charges_exact"])
    sl_net = sl_gross - float(sl_charges["_total_charges_exact"])

    data = {
        "lots": lots,
        "quantity": quantity,
        "amount_used": round(amount_used, 2),
        "target_profit_gross": round(max(0.0, target_gross), 2),
        "sl_loss_gross": round(max(0.0, -sl_gross), 2),
        "brokerage_buy": round(float(ANGEL_FO_BROKERAGE_PER_EXECUTED_ORDER), 2),
        "brokerage_exit": round(float(ANGEL_FO_BROKERAGE_PER_EXECUTED_ORDER), 2),
        # Existing UI/statistics read brokerage_round_trip. From V8.8 this field is
        # intentionally the COMPLETE round-trip charge, not only the Rs40 broker fee.
        "brokerage_round_trip": entry_charges["total_charges"],
        "brokerage_only": entry_charges["brokerage_only"],
        "stt": entry_charges["stt"],
        "exchange_transaction_charges": entry_charges["exchange_transaction_charges"],
        "stamp_duty": entry_charges["stamp_duty"],
        "sebi_charges": entry_charges["sebi_charges"],
        "gst": entry_charges["gst"],
        "total_charges": entry_charges["total_charges"],
        "target_total_charges": target_charges["total_charges"],
        "sl_total_charges": sl_charges["total_charges"],
        "target_profit_after_brokerage": round(target_net, 2),
        "sl_loss_after_brokerage": round(max(0.0, -sl_net), 2),
        "money_model": MONEY_MODEL,
        "charge_model": CHARGE_MODEL,
    }
    if exit_price is not None:
        px = float(exit_price)
        gross = (px - entry) * quantity
        charges = option_round_trip_charges(entry, px, quantity)
        net = gross - float(charges["_total_charges_exact"])
        data.update({
            "paper_exit_price": round(px, 2),
            "gross_pnl_rupees": round(gross, 2),
            "brokerage_only": charges["brokerage_only"],
            "stt": charges["stt"],
            "exchange_transaction_charges": charges["exchange_transaction_charges"],
            "stamp_duty": charges["stamp_duty"],
            "sebi_charges": charges["sebi_charges"],
            "gst": charges["gst"],
            "total_charges": charges["total_charges"],
            "brokerage_round_trip": charges["total_charges"],
            "total_brokerage_rupees": charges["total_charges"],
            "net_pnl_after_brokerage": round(net, 2),
        })
    return data

def short_reason(text, max_chars=72):
    """Keep alert reasons short and scannable."""
    clean = " ".join(str(text or "").replace("\n", " ").split()).strip()
    if not clean:
        return "No extra reason"
    # Prefer the first sentence/phrase.
    first = re.split(r"(?<=[.!?])\s+", clean, maxsplit=1)[0].strip()
    if len(first) <= max_chars:
        return first.rstrip(" .")
    return first[: max_chars - 1].rstrip(" ,.;:-") + "…"


def compact(value):
    try:
        value = float(value)
        if abs(value) >= 10_000_000:
            return f"{value / 10_000_000:.2f}Cr"
        if abs(value) >= 100_000:
            return f"{value / 100_000:.2f}L"
        if abs(value) >= 1_000:
            return f"{value / 1_000:.1f}K"
        return f"{value:.0f}"
    except Exception:
        return "--"


def _clip_to_downtime_window(start_dt, end_dt):
    """Clip an interruption to 09:00-15:00 IST; return None when outside."""
    if start_dt.tzinfo is None: start_dt=start_dt.replace(tzinfo=IST)
    if end_dt.tzinfo is None: end_dt=end_dt.replace(tzinfo=IST)
    day=end_dt.astimezone(IST).date()
    ws=datetime.combine(day, datetime.min.time(), tzinfo=IST).replace(hour=DOWNTIME_WINDOW_START[0], minute=DOWNTIME_WINDOW_START[1])
    we=datetime.combine(day, datetime.min.time(), tzinfo=IST).replace(hour=DOWNTIME_WINDOW_END[0], minute=DOWNTIME_WINDOW_END[1])
    a=max(start_dt.astimezone(IST),ws); b=min(end_dt.astimezone(IST),we)
    return (a,b) if b>a else None

def _record_engine_gap_on_start():
    """Detect app/process downtime from the last persistent heartbeat on every engine start."""
    try:
        now=now_ist(); prior=None
        if HEARTBEAT_FILE.exists():
            prior=json.loads(HEARTBEAT_FILE.read_text(encoding="utf-8"))
        if not prior or not prior.get("ts"): return
        prev=datetime.fromtimestamp(float(prior["ts"]),IST)
        if (now-prev).total_seconds() <= max(15, HEARTBEAT_SECONDS*2+5): return
        clipped=_clip_to_downtime_window(prev,now)
        if not clipped:return
        a,b=clipped; reason="ENGINE/APP NOT RUNNING"
        phase=str(prior.get("phase") or "").upper()
        if phase=="STOPPED": reason="ENGINE STOPPED / APP EXIT"
        exists=ENGINE_DOWNTIME_FILE.exists()
        with ENGINE_DOWNTIME_FILE.open("a",newline="",encoding="utf-8") as f:
            w=csv.DictWriter(f,fieldnames=["date","stop_time","restart_time","duration_seconds","reason","previous_phase"])
            if not exists:w.writeheader()
            w.writerow({"date":b.date().isoformat(),"stop_time":a.isoformat(),"restart_time":b.isoformat(),"duration_seconds":round((b-a).total_seconds(),1),"reason":reason,"previous_phase":phase})
    except Exception as exc:
        log.warning("Downtime gap detection skipped: %s", short_reason(exc,100))

def _daily_measurement_report(rows=None):
    """Write observational strategy, Guardian and engine-downtime reports. Never changes trading decisions."""
    try:
        day=now_ist().date().isoformat()
        if rows is None:
            rows=[]
            if SIGNAL_LOG_FILE.exists():
                with SIGNAL_LOG_FILE.open("r",newline="",encoding="utf-8") as f: rows=[r for r in csv.DictReader(f) if str(r.get("date"))==day]
        else: rows=[r for r in rows if str(r.get("date"))==day]
        strategies={}; warnings=accepted=denied=silent_sl=silent_target=0
        guardian_saved=guardian_missed=0.0
        for r in rows:
            st=str(r.get("technical_setup") or r.get("shadow_strategy") or "DEFAULT").strip() or "DEFAULT"
            d=strategies.setdefault(st,{"strategy":st,"signals":0,"ce_signals":0,"pe_signals":0,"target":0,"sl":0,"guardian_exits":0,"transit_exits":0,"silent_target":0,"silent_sl":0,"wins":0,"closed":0,"rr_sum":0.0,"rr_count":0,"gross_pnl":0.0,"brokerage":0.0,"net_pnl":0.0,"time_of_day":{}})
            d["signals"]+=1
            side=str(r.get("side") or "").upper()
            if side=="CE": d["ce_signals"]+=1
            if side=="PE": d["pe_signals"]+=1
            out=str(r.get("outcome") or "").upper(); sil=str(r.get("silent_monitor_outcome") or "").upper()
            if "TARGET" in out:d["target"]+=1
            if "SL" in out:d["sl"]+=1
            rr=safe_float(r.get("target_r"))
            if rr is not None: d["rr_sum"]+=rr; d["rr_count"]+=1
            if r.get("pending_warning_time") or r.get("warning_accept_time") or r.get("warning_decline_time"): warnings+=1
            if r.get("warning_accept_time"):
                accepted+=1; d["guardian_exits"]+=1
                if str(r.get("warning_accept_type") or "").upper()=="TRANSIT_ALERT": d["transit_exits"]+=1
                if "TARGET" in sil: silent_target+=1; d["silent_target"]+=1
                if "SL" in sil: silent_sl+=1; d["silent_sl"]+=1
                entry=safe_float(r.get("entry")); sl=safe_float(r.get("sl")); target=safe_float(r.get("target")); gx=safe_float(r.get("guardian_exit_price") or r.get("warning_accept_price")); qty=max(1,safe_int(r.get("quantity"),safe_int(r.get("lot"),1)))
                if None not in (entry,gx):
                    actual=(gx-entry)*qty
                    if "SL" in sil and sl is not None: guardian_saved += actual-((sl-entry)*qty)
                    elif "TARGET" in sil and target is not None: guardian_missed += ((target-entry)*qty)-actual
            if r.get("warning_decline_time"): denied+=1
            g=safe_float(r.get("gross_pnl_rupees"),0) or 0; b=safe_float(r.get("total_brokerage_rupees"),0) or 0; n=safe_float(r.get("net_pnl_after_brokerage"),0) or 0
            d["gross_pnl"]+=g; d["brokerage"]+=b; d["net_pnl"]+=n
            if str(r.get("status") or "").upper()!="TRANSIT" and str(r.get("outcome") or "").strip():
                d["closed"]+=1
                if n>0:d["wins"]+=1
            try:
                et=pd.to_datetime(r.get("entry_time"))
                hour=int(et.hour)
                bucket=f"{hour:02d}:00-{hour+1:02d}:00"
                tb=d["time_of_day"].setdefault(bucket,{"signals":0,"target":0,"sl":0,"guardian_exits":0,"net_pnl":0.0})
                tb["signals"]+=1; tb["net_pnl"]+=n
                if "TARGET" in out:tb["target"]+=1
                if "SL" in out:tb["sl"]+=1
                if r.get("warning_accept_time"):tb["guardian_exits"]+=1
            except Exception:
                pass
        for d in strategies.values():
            for k in ("gross_pnl","brokerage","net_pnl"):d[k]=round(d[k],2)
            d["net_per_signal"]=round(d["net_pnl"]/d["signals"],2) if d["signals"] else 0
            rr_count=d.pop("rr_count"); rr_sum=d.pop("rr_sum"); d["average_rr"]=round(rr_sum/rr_count,2) if rr_count else None
            d["win_pct"]=round(100*d["wins"]/d["closed"],2) if d["closed"] else None
            d["strategy_status"] = "EXPERIMENTAL" if d["strategy"].upper() in (SWEEP_IFVG_SETUP_NAME, AMD_POC_SETUP_NAME) else "ACTIVE"
            for tb in d["time_of_day"].values():tb["net_pnl"]=round(tb["net_pnl"],2)
        downtime=[]
        if ENGINE_DOWNTIME_FILE.exists():
            with ENGINE_DOWNTIME_FILE.open("r",newline="",encoding="utf-8") as f:downtime=[r for r in csv.DictReader(f) if str(r.get("date"))==day]
        total_down=sum(safe_float(x.get("duration_seconds"),0) or 0 for x in downtime); longest=max([safe_float(x.get("duration_seconds"),0) or 0 for x in downtime] or [0])
        report={"date":day,"broker":"DHAN","engine_version":VERSION,"signals":len(rows),"guardian":{"warnings":warnings,"accepted":accepted,"denied":denied,"silent_target":silent_target,"silent_sl":silent_sl,"sl_avoidance_rate_pct":round(100*silent_sl/(silent_sl+silent_target),2) if silent_sl+silent_target else None,"estimated_gross_loss_saved_rupees":round(guardian_saved,2),"estimated_gross_profit_missed_rupees":round(guardian_missed,2),"estimated_guardian_net_value_rupees":round(guardian_saved-guardian_missed,2)},"engine_downtime_09_00_to_15_00":{"stop_count":len(downtime),"events":downtime,"total_duration_seconds":round(total_down,1),"longest_duration_seconds":round(longest,1),"effective_running_seconds":round(max(0,6*3600-total_down),1)},"strategies":sorted(strategies.values(),key=lambda x:x["net_pnl"],reverse=True)}
        atomic_json_write(DAILY_RESEARCH_REPORT_FILE,report)
        fields=["date","strategy","strategy_status","signals","ce_signals","pe_signals","target","sl","guardian_exits","transit_exits","silent_target","silent_sl","wins","closed","win_pct","average_rr","gross_pnl","brokerage","net_pnl","net_per_signal","time_of_day"]
        old=[]
        if STRATEGY_DAILY_REPORT_FILE.exists():
            with STRATEGY_DAILY_REPORT_FILE.open("r",newline="",encoding="utf-8") as f:old=[r for r in csv.DictReader(f) if str(r.get("date"))!=day]
        with STRATEGY_DAILY_REPORT_FILE.open("w",newline="",encoding="utf-8") as f:
            w=csv.DictWriter(f,fieldnames=fields);w.writeheader()
            for r in old:w.writerow({k:r.get(k,"") for k in fields})
            for d in report["strategies"]:
                row={"date":day,**{k:d.get(k,"") for k in fields if k!="date"}}
                row["time_of_day"]=json.dumps(d.get("time_of_day") or {},separators=(",",":"),sort_keys=True)
                w.writerow(row)
        return report
    except Exception as exc:
        log.warning("Daily measurement report skipped: %s",short_reason(exc,120)); return None


def load_secrets_file():
    """Load Android-local secrets from a mode-600 env file."""
    if not SECRETS_FILE.exists():
        raise RuntimeError(f"Missing secrets file: {SECRETS_FILE}")
    for raw in SECRETS_FILE.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip()
        if key and key not in os.environ:
            os.environ[key] = value


def telegram_send(text, timeout=8):
    """Send through the configured Telegram bot. Never reads Telegram updates."""
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "").strip()
    if not token or not chat_id:
        return False
    try:
        r = requests.post(
            f"https://api.telegram.org/bot{token}/sendMessage",
            json={"chat_id": chat_id, "text": str(text or "")[:3900]},
            timeout=timeout,
        )
        return bool(r.ok and r.json().get("ok"))
    except Exception:
        return False


_NOTIFICATION_HISTORY_LOCK = threading.RLock()


def _today_file_is_current(path: Path, date_text: str) -> bool:
    try:
        if not path.exists():
            return False
        with path.open("r", encoding="utf-8") as f:
            return f.readline().strip() == f"DATE={date_text}"
    except Exception:
        return False


def _prepare_today_notification_file():
    """Ensure the Android notification page can never show yesterday's alerts."""
    try:
        day = now_ist().date().isoformat()
        with _NOTIFICATION_HISTORY_LOCK:
            if not _today_file_is_current(NOTIFICATIONS_TODAY_FILE, day):
                NOTIFICATIONS_TODAY_FILE.parent.mkdir(parents=True, exist_ok=True)
                NOTIFICATIONS_TODAY_FILE.write_text(
                    f"DATE={day}\nNo notifications generated today.\n",
                    encoding="utf-8",
                )
    except Exception:
        pass


def _record_notification_history(text):
    """Persist every Python-generated user notification for the current IST day."""
    raw = str(text or "").strip()
    if not raw:
        return
    try:
        n = now_ist()
        day = n.date().isoformat()
        record = {
            "timestamp": time.time(),
            "time_ist": n.isoformat(),
            "date": day,
            "text": raw,
        }
        with _NOTIFICATION_HISTORY_LOCK:
            NOTIFICATION_LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
            with NOTIFICATION_LOG_FILE.open("a", encoding="utf-8") as f:
                f.write(json.dumps(record, ensure_ascii=False) + "\n")

            current = _today_file_is_current(NOTIFICATIONS_TODAY_FILE, day)
            if current:
                try:
                    old = NOTIFICATIONS_TODAY_FILE.read_text(encoding="utf-8")
                except Exception:
                    old = f"DATE={day}\n"
                # Remove the placeholder once the first real notification arrives.
                old = old.replace("No notifications generated today.\n", "")
            else:
                old = f"DATE={day}\n"

            stamp = n.strftime("%H:%M:%S")
            block = f"\n{stamp}\n{raw}\n"
            NOTIFICATIONS_TODAY_FILE.write_text(old.rstrip() + block + "\n", encoding="utf-8")
    except Exception:
        # Notification history is observational only and must never disturb trading.
        pass


def notifications_today_text():
    _prepare_today_notification_file()
    try:
        text = NOTIFICATIONS_TODAY_FILE.read_text(encoding="utf-8")
        lines = text.splitlines()
        if lines and lines[0].startswith("DATE="):
            lines = lines[1:]
        body = "\n".join(lines).strip()
        return body or "No notifications generated today."
    except Exception:
        return "No notifications generated today."


def _v791_notification_allowed(text):
    """V7.9.1 Android/app notification allow-list.

    Allowed only:
      - new SIGNAL
      - TRANSIT / IMMEDIATE EXIT warning
      - SL HIT
      - TARGET HIT
      - connection/live-data lost
      - engine stopped/error

    Everything else remains available in logs/UI but is silent.
    """
    upper = str(text or "").upper()

    allowed_markers = (
        "SIGNAL #",
        "TRANSIT ALERT #",
        "TRANSIT HIT #",
        "IMMEDIATE EXIT WARNING #",
        "IMMEDIATE EXIT ACCEPTED #",
        "SL HIT #",
        "TARGET HIT #",
        "LIVE DATA RECOVERY FAILED",
        "CONNECTION LOST",
        "WEBSOCKET CONNECTION",
        "WEBSOCKET DISCONNECTED",
        "LIVE ENGINE ERROR",
        "ENGINE STOPPED",
        " STOPPED",
    )
    return any(marker in upper for marker in allowed_markers)


def local_notify(text, timeout=5):
    """Send only V7.9.1-approved Android/app notifications."""
    raw = str(text or "")
    if not _v791_notification_allowed(raw):
        log.debug("V7.9.1 notification suppressed: %s", short_reason(raw, 100))
        return True
    _record_notification_history(raw)
    clean = " ".join(raw.split())
    local_ok = False
    try:
        subprocess.run(
            [
                "termux-notification",
                "--id", "nifty-monitor",
                "--title", f"NIFTY Monitor V{VERSION}",
                "--content", clean[:700],
                "--priority", "high",
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=timeout,
            check=False,
        )
        local_ok = True
    except Exception:
        local_ok = False

    # The monitor only SENDS. telegram_controller_android.py is the sole getUpdates poller.
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "").strip()
    if token and chat_id:
        return telegram_send(raw)
    return local_ok

def persist_angel_login_state(logged_in, reason="", notify=False):
    """Persist Angel session state so Android refresh/background never loses it."""
    logged_in = bool(logged_in)
    status = "LOGGED IN" if logged_in else "LOGGED OUT"
    line = f"{BROKER_LABEL} LOGIN: {status}"
    if BROKER_SELECTED == "DHAN":
        _dhan_status(logged_in, _broker_text(reason))
    reason_text = short_reason(reason, 120) if reason else ""

    # Record the state change in the same notification history used by the app.
    if notify:
        note = f"🔐 {line}" if logged_in else f"🔓 {line}"
        if reason_text:
            note += f"\n{reason_text}"
        local_notify(note)

    try:
        old = {}
        if APP_UI_FILE.exists():
            try:
                old = json.loads(APP_UI_FILE.read_text(encoding="utf-8"))
                if not isinstance(old, dict):
                    old = {}
            except Exception:
                old = {}

        live_lines = [
            str(x).strip()
            for x in str(old.get("live_text") or "").splitlines()
            if str(x).strip() and not str(x).strip().upper().startswith(("ANGEL LOGIN:", "ANGEL ONE LOGIN:", "DHAN LOGIN:"))
        ]
        if live_lines and live_lines[0] in ("🔒 CLOSED", "📡 LIVE"):
            live_lines.insert(1, line)
        else:
            live_lines.insert(0, line)

        old.update({
            "schema": max(5, safe_int(old.get("schema"), 5)),
            "engine_version": VERSION,
            "angel_logged_in": logged_in,
            "login_status": status,
            "login_line": line,
            "login_reason": reason_text,
            "login_updated_ist": now_ist().isoformat(),
            "live_text": "\n".join(live_lines),
            "notifications_text": notifications_today_text(),
        })
        atomic_json_write(APP_UI_FILE, old)
    except Exception as exc:
        log.debug("Login UI state write skipped: %s", short_reason(exc, 100))


def load_angel_credentials():
    api_key = os.environ.get("ANGEL_API_KEY", "").strip()
    client_code = os.environ.get("ANGEL_CLIENT_CODE", "").strip()
    pin = os.environ.get("ANGEL_PIN", "").strip()
    if not api_key or not client_code or not pin:
        raise RuntimeError(
            "Angel credentials missing from ~/NiftyMonitor/.secrets.env"
        )
    return api_key, client_code, pin


def atomic_json_write(path: Path, payload):
    """Atomic-ish JSON writer used by the local heartbeat."""
    import threading as _threading

    path = Path(path)
    if path in (APP_UI_FILE, LIVE_STATUS_FILE) and isinstance(payload, dict):
        payload = _broker_text(payload)
        payload["broker_selected"] = BROKER_SELECTED
        if path == APP_UI_FILE:
            logged = payload.get("login_status") == "LOGGED IN"
            payload["angel_logged_in"] = logged and BROKER_SELECTED == "ANGEL"
            payload["dhan_logged_in"] = logged and BROKER_SELECTED == "DHAN"
            payload["login_line"] = BROKER_LABEL + " LOGIN: " + ("LOGGED IN" if logged else "LOGGED OUT")
            payload["engine_version"] = VERSION
    path.parent.mkdir(parents=True, exist_ok=True)

    tmp = Path(
        f"{path}.{os.getpid()}.{_threading.get_ident()}.{time.time_ns()}.tmp"
    )
    encoded = json.dumps(
        payload,
        ensure_ascii=False,
        default=lambda o: o.isoformat() if hasattr(o, "isoformat") else str(o),
    )

    try:
        tmp.write_text(encoded, encoding="utf-8")
        last_error = None

        # Retry transient filesystem replacement failures.
        for _ in range(30):
            try:
                os.replace(tmp, path)
                return
            except PermissionError as exc:
                last_error = exc
                try:
                    if path.exists():
                        os.chmod(path, 0o666)
                except OSError:
                    pass
                time.sleep(0.10)
            except OSError as exc:
                last_error = exc
                time.sleep(0.10)

        # Fallback: direct write. Supervisor tolerates a transient read failure.
        try:
            path.write_text(encoded, encoding="utf-8")
            return
        except Exception:
            if last_error:
                raise last_error
            raise
    finally:
        try:
            tmp.unlink(missing_ok=True)
        except Exception:
            pass



def write_phase_ui(phase, step="", details=None, progress_text="", market_state=None):
    """Write a compact startup/market-state screen.

    During LOGIN and MARKET_CHECK, keep the same startup window visible and
    show every completed/current step one per line.  Only after Angel confirms
    LIVE/CLOSED does the normal market dashboard replace this progress window.
    """
    phase = str(phase or "LOGIN").upper()
    details = [str(x).strip() for x in (details or []) if str(x).strip()]

    label_map = {
        "LOGIN": "🔐 LOGIN",
        "MARKET_CHECK": "⏳ MARKET CHECK",
        "CLOSED": "🔒 CLOSED",
        "LIVE": "📡 LIVE",
    }

    index_map = {
        "LOGIN": "LOGGING IN",
        "MARKET_CHECK": "CHECKING MARKET STATUS",
        "CLOSED": "MARKET: CLOSED",
        "LIVE": "MARKET: LIVE",
    }

    try:
        old = {}
        if APP_UI_FILE.exists():
            try:
                old = json.loads(APP_UI_FILE.read_text(encoding="utf-8"))
                if not isinstance(old, dict):
                    old = {}
            except Exception:
                old = {}

        # V6.8: startup/CLOSED/LIVE refresh must never erase Angel login state.
        login_status = str(old.get("login_status") or "LOGGED OUT").upper().strip()
        if login_status not in ("LOGGED IN", "LOGGED OUT"):
            login_status = "LOGGED OUT"
        login_line = f"{BROKER_LABEL} LOGIN: {login_status}"
        visible_lines = [
            str(x).strip() for x in details
            if str(x).strip() and not str(x).strip().upper().startswith(("ANGEL LOGIN:", "ANGEL ONE LOGIN:", "DHAN LOGIN:"))
        ]
        visible_lines.insert(0, login_line)

        old.update({
            "schema": 5,
            "engine_version": VERSION,
            "angel_logged_in": login_status == "LOGGED IN",
            "login_status": login_status,
            "login_line": login_line,
            "index_line": index_map.get(phase, phase),
            "price_line": "",
            "live_text": "\n".join(visible_lines),
            "service_text": "",
            "market_state": market_state or phase,
            "market_section_label": label_map.get(phase, phase),
        })

        old.setdefault("transit_text", "NO ACTIVE TRANSIT")
        old.setdefault("stats_text", f"📊 V{VERSION} STATS\nNo signals yet.")
        old["notifications_text"] = notifications_today_text()
        # A restart/startup screen must never carry a stale warning-accept button.
        old["warning_pending"] = False
        old["warning_signal_no"] = 0
        old["warning_type"] = ""
        old["warning_reason"] = ""
        old["warning_current_premium"] = 0.0
        old["warning_accept_label"] = ""
        old["active_transits_ui"] = old.get("active_transits_ui", [])
        # Never carry an old Shadow Learning card across startup/restart.
        # This is a generic Python-owned frame; the host only renders it.
        old["dynamic_panel_title"] = "ENGINE PANEL"
        old["dynamic_panel_text"] = "Python engine is starting."
        # Backward compatibility for older hosts that still read learning_text.
        old["learning_text"] = old["dynamic_panel_text"]

        atomic_json_write(APP_UI_FILE, old)

    except Exception as exc:
        log.debug("Phase UI write skipped: %s", short_reason(exc, 100))



# ============================================================================
# LOCAL TECHNICAL CACHE ENGINE
# ============================================================================

class LocalTechnicalEngine:
    """5-minute selected-index technical engine with 6-attempt startup seed.

    Historical data is used only as a startup seed/gap fill. After startup,
    all new 5-minute candles are built from live selected-index WebSocket ticks.
    """

    def __init__(self, cache_file, symbol_token, exchange="NSE", tz_name="Asia/Kolkata"):
        cache_path = Path(cache_file)
        if BROKER_SELECTED == "DHAN":
            cache_path = cache_path.with_name("dhan_" + cache_path.name)
        self.cache_file = str(cache_path)
        self.symbol_token = str(symbol_token)
        self.exchange = str(exchange or "NSE").upper()
        self.tz_name = tz_name
        self.lock = threading.RLock()
        self.df = pd.DataFrame(columns=["time", "open", "high", "low", "close", "volume"])
        self.forming = None
        self.seed_attempted = False
        self.seed_error = None
        self.seed_source = "NONE"
        # V3.4.1 history recovery state. The SmartAPI historical endpoint is the
        # authoritative source for candles which had already closed before this
        # process started. WebSocket ticks are still used for the forming candle.
        self.smart = None
        self.angel_rest_call = None
        self.backfill_running = False
        self.last_backfill_attempt_wallclock = 0.0
        self.last_backfill_success_wallclock = 0.0
        self.last_backfill_reason = None
        self.last_closed_wallclock = 0.0
        self.snapshot = self._empty_snapshot("Technical cache not initialised")
        # V8.2: completely separate state for the experimental Sweep+iFVG+CISD strategy.
        self.sweep_ifvg_states = self._load_sweep_ifvg_state()
        # V8.3: independent AMD + futures-volume POC strategy state/provider.
        self.amd_poc_states = self._load_amd_poc_state()
        self.futures_profile_provider = None

    def _now(self):
        return pd.Timestamp.now(tz=self.tz_name)

    def _empty_snapshot(self, error=None):
        return {
            "ok": False,
            "candle_time": None,
            "price": None,
            "ema20": None,
            "ema50": None,
            "ema20_slope": 0.0,
            "ema50_slope": 0.0,
            "atr14": None,
            "adx14": None,
            "plus_di14": None,
            "minus_di14": None,
            "day_high": None,
            "day_low": None,
            "or_high": None,
            "or_low": None,
            "trend": "UNKNOWN",
            "momentum": "UNKNOWN",
            "structure": "UNKNOWN",
            "or_status": "NOT READY",
            "bias": "WAIT",
            "entry_ready": False,
            "direction": None,
            "setup": "NONE",
            "setup_grade": "NONE",
            "tech_score": 0.0,
            "setup_candidates": [],
            "strategy_event_time": None,
            "strategy_id": "",
            "strategy_short_name": "",
            "strategy_status": "",
            "strategy_reason": "",
            "setup_invalidation_level": None,
            "target_liquidity": None,
            "candlestick_engine": CANDLE_PATTERN_ENGINE_VERSION,
            "candlestick_primary": "NONE",
            "candlestick_family": "NONE",
            "candlestick_direction": "NEUTRAL",
            "candlestick_bias": "NEUTRAL",
            "candlestick_patterns": [],
            "candlestick_bonus_ce": 0.0,
            "candlestick_bonus_pe": 0.0,
            "candlestick_conflict": False,
            "weapon15_time": None,
            "weapon15_ema9": None,
            "weapon15_macd": None,
            "weapon15_macd_signal": None,
            "weapon15_rsi14": None,
            "source": "LOCAL CACHE + ANGEL WEBSOCKET",
            "cache_rows": 0,
            "error": error,
        }
    # ------------------------------------------------------------------
    # V8.2 EXPERIMENTAL: LIQUIDITY_SWEEP_IFVG_CISD
    # ------------------------------------------------------------------
    @staticmethod
    def _sweep_ifvg_blank_state(direction):
        return {
            "direction": direction,
            "stage": "IDLE",
            "setup_uid": "",
            "liquidity_level": None,
            "liquidity_time": "",
            "sweep_price": None,
            "sweep_time": "",
            "htf_fvg_lower": None,
            "htf_fvg_upper": None,
            "htf_fvg_time": "",
            "ltf_fvg_lower": None,
            "ltf_fvg_upper": None,
            "ltf_fvg_time": "",
            "ltf_fvg_type": "",
            "ifvg_confirmation_time": "",
            "cisd_reference_open": None,
            "cisd_reference_time": "",
            "cisd_confirmation_time": "",
            "entry_underlying_price": None,
            "setup_invalidation_level": None,
            "target_liquidity": None,
            "target_liquidity_time": "",
            "target_liquidity_type": "",
            "strategy_reason": "",
            "last_processed_candle": "",
            "complete_time": "",
            "rejection_reason": "",
        }

    def _load_sweep_ifvg_state(self):
        states = {
            "BULLISH": self._sweep_ifvg_blank_state("BULLISH"),
            "BEARISH": self._sweep_ifvg_blank_state("BEARISH"),
        }
        try:
            if not SWEEP_IFVG_STATE_FILE.exists():
                return states
            raw = json.loads(SWEEP_IFVG_STATE_FILE.read_text(encoding="utf-8"))
            if str(raw.get("date") or "") != now_ist().date().isoformat():
                return states
            if str(raw.get("symbol_token") or "") != str(self.symbol_token):
                return states
            saved = raw.get("states") or {}
            for direction in ("BULLISH", "BEARISH"):
                if isinstance(saved.get(direction), dict):
                    merged = self._sweep_ifvg_blank_state(direction)
                    merged.update(saved[direction])
                    states[direction] = merged
        except Exception as exc:
            log.warning("SWEEP+IFVG state load skipped: %s", short_reason(exc, 100))
        return states

    def _persist_sweep_ifvg_state(self):
        try:
            atomic_json_write(SWEEP_IFVG_STATE_FILE, {
                "schema": 1,
                "strategy": SWEEP_IFVG_STRATEGY_ID,
                "status": SWEEP_IFVG_STATUS,
                "date": now_ist().date().isoformat(),
                "symbol_token": str(self.symbol_token),
                "execution_timeframe_minutes": SWEEP_IFVG_EXECUTION_MINUTES,
                "htf_minutes": SWEEP_IFVG_HTF_MINUTES,
                "states": self.sweep_ifvg_states,
                "updated_at": now_ist().isoformat(),
            })
        except Exception as exc:
            log.warning("SWEEP+IFVG state save skipped: %s", short_reason(exc, 100))

    def _log_sweep_ifvg_event(self, state, event, rejection_reason="", **extra):
        """Append an auditable state/rejection row; never changes trading decisions."""
        try:
            fields = [
                "time_ist", "strategy_id", "strategy", "short_name", "strategy_status",
                "event", "state", "direction", "setup_uid",
                "liquidity_level", "sweep_price", "sweep_time",
                "htf_fvg_lower", "htf_fvg_upper", "htf_fvg_time",
                "ltf_fvg_lower", "ltf_fvg_upper", "ltf_fvg_time", "ltf_fvg_type",
                "ifvg_confirmation_time", "cisd_reference_open", "cisd_reference_time",
                "cisd_confirmation_time", "entry_underlying_price",
                "option_selected", "option_entry_premium", "signal_no",
                "structural_sl", "target_liquidity", "target_liquidity_time",
                "target_liquidity_type", "reason", "rejection_reason",
            ]
            row = {
                "time_ist": now_ist().isoformat(),
                "strategy_id": SWEEP_IFVG_STRATEGY_ID,
                "strategy": SWEEP_IFVG_SETUP_NAME,
                "short_name": SWEEP_IFVG_SHORT_NAME,
                "strategy_status": SWEEP_IFVG_STATUS,
                "event": event,
                "state": state.get("stage", ""),
                "direction": state.get("direction", ""),
                "setup_uid": state.get("setup_uid", ""),
                "liquidity_level": state.get("liquidity_level", ""),
                "sweep_price": state.get("sweep_price", ""),
                "sweep_time": state.get("sweep_time", ""),
                "htf_fvg_lower": state.get("htf_fvg_lower", ""),
                "htf_fvg_upper": state.get("htf_fvg_upper", ""),
                "htf_fvg_time": state.get("htf_fvg_time", ""),
                "ltf_fvg_lower": state.get("ltf_fvg_lower", ""),
                "ltf_fvg_upper": state.get("ltf_fvg_upper", ""),
                "ltf_fvg_time": state.get("ltf_fvg_time", ""),
                "ltf_fvg_type": state.get("ltf_fvg_type", ""),
                "ifvg_confirmation_time": state.get("ifvg_confirmation_time", ""),
                "cisd_reference_open": state.get("cisd_reference_open", ""),
                "cisd_reference_time": state.get("cisd_reference_time", ""),
                "cisd_confirmation_time": state.get("cisd_confirmation_time", ""),
                "entry_underlying_price": state.get("entry_underlying_price", ""),
                "structural_sl": state.get("setup_invalidation_level", ""),
                "target_liquidity": state.get("target_liquidity", ""),
                "target_liquidity_time": state.get("target_liquidity_time", ""),
                "target_liquidity_type": state.get("target_liquidity_type", ""),
                "reason": state.get("strategy_reason", ""),
                "rejection_reason": rejection_reason or state.get("rejection_reason", ""),
            }
            row.update(extra)
            exists = SWEEP_IFVG_EVENT_LOG_FILE.exists()
            with SWEEP_IFVG_EVENT_LOG_FILE.open("a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
                if not exists:
                    w.writeheader()
                w.writerow({k: row.get(k, "") for k in fields})
            log.info(
                "SWEEP+IFVG | %s | %s | %s | liq=%s | %s",
                state.get("direction"), event, state.get("stage"),
                state.get("liquidity_level"), rejection_reason or state.get("strategy_reason", ""),
            )
        except Exception as exc:
            log.warning("SWEEP+IFVG event log skipped: %s", short_reason(exc, 100))

    @staticmethod
    def _sweep_ifvg_confirmed_pivots(frame):
        """Objective 2-left/2-right confirmed fractals; no subjective swing selection."""
        out = {"highs": [], "lows": []}
        if frame is None or len(frame) < SWEEP_IFVG_PIVOT_LEFT + SWEEP_IFVG_PIVOT_RIGHT + 1:
            return out
        d = frame.reset_index(drop=True)
        left = SWEEP_IFVG_PIVOT_LEFT
        right = SWEEP_IFVG_PIVOT_RIGHT
        for i in range(left, len(d) - right):
            h = float(d.iloc[i]["high"]); l = float(d.iloc[i]["low"])
            lh = [float(x) for x in d.iloc[i-left:i]["high"]]
            rh = [float(x) for x in d.iloc[i+1:i+1+right]["high"]]
            ll = [float(x) for x in d.iloc[i-left:i]["low"]]
            rl = [float(x) for x in d.iloc[i+1:i+1+right]["low"]]
            t = str(d.iloc[i]["time"])
            if h > max(lh) and h >= max(rh):
                out["highs"].append({"time": t, "price": h})
            if l < min(ll) and l <= min(rl):
                out["lows"].append({"time": t, "price": l})
        return out

    def _sweep_ifvg_htf_fvgs(self, df):
        """Return still-valid normal 3-candle FVGs from completed HTF candles."""
        if df is None or df.empty:
            return [], pd.DataFrame()
        src = df.copy().sort_values("time").tail(1200)
        src["time"] = pd.to_datetime(src["time"], errors="coerce")
        src = src.dropna(subset=["time"]).set_index("time")
        tf = f"{int(SWEEP_IFVG_HTF_MINUTES)}min"
        resampler = src.resample(tf, origin="start_day", offset="15min", label="left", closed="left")
        htf = resampler.agg({"open":"first", "high":"max", "low":"min", "close":"last", "volume":"sum"})
        counts = resampler["close"].count()
        expected = max(1, int(SWEEP_IFVG_HTF_MINUTES // max(1, SWEEP_IFVG_EXECUTION_MINUTES)))
        htf = htf[counts >= expected].dropna(subset=["open","high","low","close"]).reset_index()
        if len(htf) < 3:
            return [], htf
        zones = []
        start = max(0, len(htf) - SWEEP_IFVG_HTF_LOOKBACK_BARS - 2)
        for i in range(start, len(htf)-2):
            c1 = htf.iloc[i]; c3 = htf.iloc[i+2]
            # Bullish FVG: candle 3 low above candle 1 high.
            if float(c3["low"]) > float(c1["high"]):
                lo, hi = float(c1["high"]), float(c3["low"])
                after = htf.iloc[i+3:]
                valid = after.empty or not bool((after["close"].astype(float) < lo).any())
                if valid:
                    zones.append({"type":"BULLISH", "lower":lo, "upper":hi, "time":str(c3["time"])})
            # Bearish FVG: candle 3 high below candle 1 low.
            if float(c3["high"]) < float(c1["low"]):
                lo, hi = float(c3["high"]), float(c1["low"])
                after = htf.iloc[i+3:]
                valid = after.empty or not bool((after["close"].astype(float) > hi).any())
                if valid:
                    zones.append({"type":"BEARISH", "lower":lo, "upper":hi, "time":str(c3["time"])})
        return zones, htf

    def _sweep_ifvg_match_htf_zone(self, direction, sweep_price, df):
        zones, htf = self._sweep_ifvg_htf_fvgs(df)
        wanted = "BULLISH" if direction == "BULLISH" else "BEARISH"
        if htf is None or htf.empty:
            return None
        avg_range = float((htf["high"].astype(float) - htf["low"].astype(float)).tail(14).mean())
        tol = max(float(sweep_price) * 0.0005, avg_range * SWEEP_IFVG_HTF_NEAR_RANGE_FRACTION)
        matches = []
        for z in zones:
            if z["type"] != wanted:
                continue
            px = float(sweep_price); lo=float(z["lower"]); hi=float(z["upper"])
            dist = 0.0 if lo <= px <= hi else min(abs(px-lo), abs(px-hi))
            if dist <= tol:
                matches.append((dist, z))
        if not matches:
            return None
        matches.sort(key=lambda x: (x[0], x[1]["time"]), reverse=False)
        return matches[0][1]

    @staticmethod
    def _sweep_ifvg_find_ltf_fvg(after_sweep, direction, atr14):
        """For a bearish setup invert a bullish FVG; bullish setup mirrors it."""
        if after_sweep is None or len(after_sweep) < 3:
            return None
        d = after_sweep.reset_index(drop=True)
        min_gap = max((safe_float(atr14, 0.0) or 0.0) * SWEEP_IFVG_LTF_MIN_GAP_ATR, 0.01)
        for i in range(len(d)-2):
            c1=d.iloc[i]; c3=d.iloc[i+2]
            if direction == "BEARISH":
                lo, hi = float(c1["high"]), float(c3["low"])
                if hi-lo >= min_gap:
                    return {"type":"BULLISH_FVG_TO_BEARISH_IFVG", "lower":lo, "upper":hi, "time":str(c3["time"])}
            else:
                lo, hi = float(c3["high"]), float(c1["low"])
                if hi-lo >= min_gap:
                    return {"type":"BEARISH_FVG_TO_BULLISH_IFVG", "lower":lo, "upper":hi, "time":str(c3["time"])}
        return None

    def _sweep_ifvg_target_liquidity(self, df, direction, entry_price, before_time):
        scope = df[pd.to_datetime(df["time"]) < pd.to_datetime(before_time)].tail(SWEEP_IFVG_TARGET_LOOKBACK_BARS)
        piv = self._sweep_ifvg_confirmed_pivots(scope)
        if direction == "BEARISH":
            choices=[x for x in piv["lows"] if float(x["price"]) < float(entry_price)]
            if choices:
                x=choices[-1]; return x["price"], x["time"], "CONFIRMED SWING LOW"
            if not scope.empty:
                idx=scope["low"].astype(float).idxmin(); px=float(scope.loc[idx,"low"])
                if px < float(entry_price): return px, str(scope.loc[idx,"time"]), "RECENT SIGNIFICANT LOW"
        else:
            choices=[x for x in piv["highs"] if float(x["price"]) > float(entry_price)]
            if choices:
                x=choices[-1]; return x["price"], x["time"], "CONFIRMED SWING HIGH"
            if not scope.empty:
                idx=scope["high"].astype(float).idxmax(); px=float(scope.loc[idx,"high"])
                if px > float(entry_price): return px, str(scope.loc[idx,"time"]), "RECENT SIGNIFICANT HIGH"
        return None, "", "NOT FOUND"

    def _sweep_ifvg_reset(self, direction, reason="", prior=None):
        if prior is not None and reason:
            prior["rejection_reason"] = reason
            prior["stage"] = "INVALIDATED"
            self._log_sweep_ifvg_event(prior, "INVALIDATED", rejection_reason=reason)
        self.sweep_ifvg_states[direction] = self._sweep_ifvg_blank_state(direction)
        self._persist_sweep_ifvg_state()

    def _sweep_ifvg_candidate_locked(self, df, atr14):
        """Advance both bullish/bearish machines using only completed execution candles."""
        candidates=[]
        if df is None or len(df) < 10:
            return candidates
        d=df.copy().sort_values("time").reset_index(drop=True)
        latest=d.iloc[-1]; latest_time=str(latest["time"])
        pivot_scope=d.tail(SWEEP_IFVG_PIVOT_LOOKBACK_BARS + SWEEP_IFVG_PIVOT_LEFT + SWEEP_IFVG_PIVOT_RIGHT + 4)
        piv=self._sweep_ifvg_confirmed_pivots(pivot_scope)

        for direction in ("BULLISH","BEARISH"):
            state=self.sweep_ifvg_states.get(direction) or self._sweep_ifvg_blank_state(direction)
            pivot_list=piv["lows"] if direction=="BULLISH" else piv["highs"]
            pivot=pivot_list[-1] if pivot_list else None

            # COMPLETE waits for a newer confirmed liquidity pivot before a fresh setup.
            if state.get("stage") == "COMPLETE":
                if not pivot or str(pivot.get("time")) <= str(state.get("liquidity_time") or ""):
                    continue
                state=self._sweep_ifvg_blank_state(direction)
                self.sweep_ifvg_states[direction]=state

            # Keep CISD-confirmed candidate available to the existing pipeline until
            # it is issued or invalidated; setup_signature prevents duplicate signals.
            if state.get("stage") == "CISD_CONFIRMED":
                pass
            elif state.get("last_processed_candle") == latest_time:
                continue
            state["last_processed_candle"] = latest_time

            if state.get("stage") in ("IDLE","LIQUIDITY_FOUND"):
                if not pivot:
                    continue
                if state.get("liquidity_time") != str(pivot["time"]):
                    state=self._sweep_ifvg_blank_state(direction)
                    state.update({
                        "stage":"LIQUIDITY_FOUND",
                        "setup_uid":f"{direction}-{str(pivot['time'])}",
                        "liquidity_level":round(float(pivot["price"]),2),
                        "liquidity_time":str(pivot["time"]),
                    })
                    self.sweep_ifvg_states[direction]=state
                    self._log_sweep_ifvg_event(state,"LIQUIDITY_FOUND")

                level=float(state["liquidity_level"])
                swept=(float(latest["low"]) < level) if direction=="BULLISH" else (float(latest["high"]) > level)
                after_pivot = pd.to_datetime(latest["time"]) > pd.to_datetime(state["liquidity_time"])
                if swept and after_pivot:
                    sweep_px=float(latest["low"] if direction=="BULLISH" else latest["high"])
                    state.update({
                        "stage":"SWEEP_DETECTED",
                        "sweep_price":round(sweep_px,2),
                        "sweep_time":latest_time,
                        "setup_invalidation_level":round(sweep_px,2),
                    })
                    self._log_sweep_ifvg_event(state,"SWEEP_DETECTED")
                    zone=self._sweep_ifvg_match_htf_zone(direction,sweep_px,d)
                    if not zone:
                        self._sweep_ifvg_reset(direction, f"SWEEP WITHOUT {SWEEP_IFVG_HTF_MINUTES}M {direction} FVG", prior=state)
                        continue
                    state.update({
                        "stage":"WAITING_FOR_LTF_FVG",
                        "htf_fvg_lower":round(float(zone["lower"]),2),
                        "htf_fvg_upper":round(float(zone["upper"]),2),
                        "htf_fvg_time":zone["time"],
                    })
                    self._log_sweep_ifvg_event(state,"HTF_FVG_CONFIRMED")

            if state.get("stage") in ("WAITING_FOR_LTF_FVG","LTF_FVG_FOUND","IFVG_CONFIRMED","CISD_CONFIRMED"):
                sweep_time=state.get("sweep_time")
                if not sweep_time:
                    self._sweep_ifvg_reset(direction,"MISSING SWEEP TIME",prior=state); continue
                later=d[pd.to_datetime(d["time"]) > pd.to_datetime(sweep_time)].copy()
                if len(later) > SWEEP_IFVG_MAX_SETUP_BARS:
                    self._sweep_ifvg_reset(direction, f"SETUP TIMEOUT > {SWEEP_IFVG_MAX_SETUP_BARS} EXECUTION BARS", prior=state); continue
                # Structural invalidation uses candle CLOSE; sweep wick itself is allowed.
                if not later.empty:
                    c=float(later.iloc[-1]["close"]); inv=float(state["setup_invalidation_level"])
                    invalid=(c < inv) if direction=="BULLISH" else (c > inv)
                    if invalid:
                        self._sweep_ifvg_reset(direction,"STRUCTURAL INVALIDATION CLOSE BEYOND SWEEP EXTREME",prior=state); continue

            if state.get("stage") == "WAITING_FOR_LTF_FVG":
                later=d[pd.to_datetime(d["time"]) > pd.to_datetime(state["sweep_time"])].copy()
                fvg=self._sweep_ifvg_find_ltf_fvg(later,direction,atr14)
                if fvg:
                    state.update({
                        "stage":"LTF_FVG_FOUND",
                        "ltf_fvg_lower":round(float(fvg["lower"]),2),
                        "ltf_fvg_upper":round(float(fvg["upper"]),2),
                        "ltf_fvg_time":fvg["time"],
                        "ltf_fvg_type":fvg["type"],
                    })
                    self._log_sweep_ifvg_event(state,"LTF_FVG_FOUND")

            if state.get("stage") == "LTF_FVG_FOUND":
                after_fvg=d[pd.to_datetime(d["time"]) > pd.to_datetime(state["ltf_fvg_time"])].copy()
                if not after_fvg.empty:
                    confirm=None
                    for _,row in after_fvg.iterrows():
                        close=float(row["close"])
                        if direction=="BEARISH" and close < float(state["ltf_fvg_lower"]): confirm=row; break
                        if direction=="BULLISH" and close > float(state["ltf_fvg_upper"]): confirm=row; break
                    if confirm is not None:
                        # CLOSE confirmation only: wick penetration never reaches this state.
                        state["ifvg_confirmation_time"]=str(confirm["time"])
                        state["stage"]="IFVG_CONFIRMED"
                        self._log_sweep_ifvg_event(state,"IFVG_CONFIRMED")

            if state.get("stage") == "IFVG_CONFIRMED":
                ifvg_t=pd.to_datetime(state["ifvg_confirmation_time"])
                sweep_t=pd.to_datetime(state["sweep_time"])
                pre=d[(pd.to_datetime(d["time"]) >= sweep_t) & (pd.to_datetime(d["time"]) < ifvg_t)].copy()
                if direction=="BEARISH":
                    opp=pre[pre["close"].astype(float) > pre["open"].astype(float)]
                else:
                    opp=pre[pre["close"].astype(float) < pre["open"].astype(float)]
                if opp.empty:
                    # Objective CISD requires a reference delivery candle; wait rather than guess.
                    pass
                else:
                    ref=opp.iloc[-1]
                    state["cisd_reference_open"]=round(float(ref["open"]),2)
                    state["cisd_reference_time"]=str(ref["time"])
                    scan=d[pd.to_datetime(d["time"]) >= ifvg_t].copy()
                    cisd=None
                    for _,row in scan.iterrows():
                        close=float(row["close"]); ref_open=float(state["cisd_reference_open"])
                        if direction=="BEARISH" and close < ref_open: cisd=row; break
                        if direction=="BULLISH" and close > ref_open: cisd=row; break
                    if cisd is not None:
                        entry_px=float(cisd["close"])
                        target_px,target_t,target_type=self._sweep_ifvg_target_liquidity(d,direction,entry_px,str(cisd["time"]))
                        state.update({
                            "stage":"CISD_CONFIRMED",
                            "cisd_confirmation_time":str(cisd["time"]),
                            "entry_underlying_price":round(entry_px,2),
                            "target_liquidity":round(float(target_px),2) if target_px is not None else None,
                            "target_liquidity_time":target_t,
                            "target_liquidity_type":target_type,
                            "strategy_reason":(
                                "SELL-SIDE LIQUIDITY SWEPT → 1H BULLISH FVG → 5M IFVG → BULLISH CISD"
                                if direction=="BULLISH" else
                                "BUY-SIDE LIQUIDITY SWEPT → 1H BEARISH FVG → 5M IFVG → BEARISH CISD"
                            ),
                        })
                        self._log_sweep_ifvg_event(state,"CISD_CONFIRMED")

            if state.get("stage") == "CISD_CONFIRMED":
                side="CE" if direction=="BULLISH" else "PE"
                candidates.append({
                    "setup":SWEEP_IFVG_SETUP_NAME,
                    "direction":side,
                    "tech_score":SWEEP_IFVG_TECH_SCORE,
                    "setup_grade":"A",
                    "entry_ready":True,
                    "entry_block_reason":"",
                    "strategy_event_time":state.get("cisd_confirmation_time") or latest_time,
                    "strategy_id":SWEEP_IFVG_STRATEGY_ID,
                    "strategy_short_name":SWEEP_IFVG_SHORT_NAME,
                    "strategy_status":SWEEP_IFVG_STATUS,
                    "strategy_reason":state.get("strategy_reason"),
                    "liquidity_level":state.get("liquidity_level"),
                    "sweep_price":state.get("sweep_price"),
                    "sweep_time":state.get("sweep_time"),
                    "htf_fvg_lower":state.get("htf_fvg_lower"),
                    "htf_fvg_upper":state.get("htf_fvg_upper"),
                    "htf_fvg_time":state.get("htf_fvg_time"),
                    "ltf_fvg_lower":state.get("ltf_fvg_lower"),
                    "ltf_fvg_upper":state.get("ltf_fvg_upper"),
                    "ltf_fvg_time":state.get("ltf_fvg_time"),
                    "ifvg_confirmation_time":state.get("ifvg_confirmation_time"),
                    "cisd_reference_open":state.get("cisd_reference_open"),
                    "cisd_reference_time":state.get("cisd_reference_time"),
                    "cisd_confirmation_time":state.get("cisd_confirmation_time"),
                    "setup_invalidation_level":state.get("structural_sl", state.get("setup_invalidation_level")),
                    "target_liquidity":state.get("target_liquidity"),
                    "target_liquidity_time":state.get("target_liquidity_time"),
                    "target_liquidity_type":state.get("target_liquidity_type"),
                })
            self.sweep_ifvg_states[direction]=state

        self._persist_sweep_ifvg_state()
        return candidates

    def mark_sweep_ifvg_complete(self, tech, candidate, entry_premium, signal_no):
        if str(tech.get("strategy_id") or "") != SWEEP_IFVG_STRATEGY_ID:
            return
        direction="BULLISH" if str(tech.get("direction") or "").upper()=="CE" else "BEARISH"
        state=self.sweep_ifvg_states.get(direction)
        if not state or state.get("stage") != "CISD_CONFIRMED":
            return
        state["stage"]="COMPLETE"
        state["complete_time"]=now_ist().isoformat()
        self._log_sweep_ifvg_event(
            state,"SIGNAL", option_selected=str(candidate.get("symbol") or ""),
            option_entry_premium=entry_premium, signal_no=signal_no,
        )
        self._persist_sweep_ifvg_state()


    # ------------------------------------------------------------------
    # V8.3 EXPERIMENTAL: AMD + Futures Volume Profile POC Retest
    # ------------------------------------------------------------------
    @staticmethod
    def _amd_poc_blank_state(direction):
        return {
            "stage": "IDLE",
            "direction": direction,
            "setup_uid": "",
            "last_processed_candle": "",
            "accumulation_start": "",
            "accumulation_end": "",
            "range_high": None,
            "range_low": None,
            "range_candles": 0,
            "poc_price": None,
            "profile_total_volume": 0.0,
            "profile_bin_size": None,
            "profile_source": "",
            "profile_distribution": "",
            "futures_poc_price": None,
            "futures_index_basis": None,
            "manipulation_price": None,
            "manipulation_high": None,
            "manipulation_low": None,
            "manipulation_time": "",
            "poc_cross_time": "",
            "poc_retest_time": "",
            "entry_time": "",
            "entry_underlying_price": None,
            "setup_invalidation_level": None,
            "structural_sl": None,
            "target_liquidity": None,
            "target_type": "",
            "strategy_reason": "",
            "rejection_reason": "",
            "complete_time": "",
        }

    def _load_amd_poc_state(self):
        states = {x: self._amd_poc_blank_state(x) for x in ("BULLISH", "BEARISH")}
        try:
            if AMD_POC_STATE_FILE.exists():
                obj = json.loads(AMD_POC_STATE_FILE.read_text(encoding="utf-8"))
                if obj.get("date") == now_ist().date().isoformat():
                    saved = obj.get("states") or {}
                    for direction in states:
                        if isinstance(saved.get(direction), dict):
                            merged = self._amd_poc_blank_state(direction)
                            merged.update(saved[direction])
                            states[direction] = merged
        except Exception as exc:
            log.warning("AMD+POC state load skipped: %s", short_reason(exc, 100))
        return states

    def _persist_amd_poc_state(self):
        try:
            atomic_json_write(AMD_POC_STATE_FILE, {
                "schema": 1,
                "strategy": AMD_POC_STRATEGY_ID,
                "status": AMD_POC_STATUS,
                "date": now_ist().date().isoformat(),
                "states": self.amd_poc_states,
                "updated_at": now_ist().isoformat(),
            })
        except Exception as exc:
            log.warning("AMD+POC state save skipped: %s", short_reason(exc, 100))

    def _log_amd_poc_event(self, state, event, rejection_reason="", **extra):
        try:
            fields = [
                "time_ist","strategy_id","strategy","short_name","strategy_status",
                "event","state","direction","setup_uid",
                "accumulation_start","accumulation_end","range_high","range_low","range_candles",
                "poc_price","profile_total_volume","profile_bin_size","profile_source","profile_distribution",
                "futures_poc_price","futures_index_basis",
                "manipulation_price","manipulation_high","manipulation_low","manipulation_time",
                "poc_cross_time","poc_retest_time","entry_time","entry_underlying_price",
                "option_type","option_selected","option_entry_premium","signal_no","structural_sl","target","target_type",
                "reason","rejection_reason",
            ]
            row = {
                "time_ist": now_ist().isoformat(),
                "strategy_id": AMD_POC_STRATEGY_ID,
                "strategy": AMD_POC_SETUP_NAME,
                "short_name": AMD_POC_SHORT_NAME,
                "strategy_status": AMD_POC_STATUS,
                "event": event,
                "state": state.get("stage",""),
                "direction": state.get("direction",""),
                "setup_uid": state.get("setup_uid",""),
                "accumulation_start": state.get("accumulation_start",""),
                "accumulation_end": state.get("accumulation_end",""),
                "range_high": state.get("range_high",""),
                "range_low": state.get("range_low",""),
                "range_candles": state.get("range_candles",""),
                "poc_price": state.get("poc_price",""),
                "profile_total_volume": state.get("profile_total_volume",""),
                "profile_bin_size": state.get("profile_bin_size",""),
                "profile_source": state.get("profile_source",""),
                "profile_distribution": state.get("profile_distribution",""),
                "futures_poc_price": state.get("futures_poc_price",""),
                "futures_index_basis": state.get("futures_index_basis",""),
                "manipulation_price": state.get("manipulation_price",""),
                "manipulation_high": state.get("manipulation_high",""),
                "manipulation_low": state.get("manipulation_low",""),
                "manipulation_time": state.get("manipulation_time",""),
                "poc_cross_time": state.get("poc_cross_time",""),
                "poc_retest_time": state.get("poc_retest_time",""),
                "entry_time": state.get("entry_time") or state.get("poc_retest_time",""),
                "entry_underlying_price": state.get("entry_underlying_price",""),
                "option_type": "CE" if str(state.get("direction") or "").upper()=="BULLISH" else ("PE" if str(state.get("direction") or "").upper()=="BEARISH" else ""),
                "structural_sl": state.get("structural_sl", state.get("setup_invalidation_level","")),
                "target": state.get("target_liquidity",""),
                "target_type": state.get("target_type",""),
                "reason": state.get("strategy_reason",""),
                "rejection_reason": rejection_reason or state.get("rejection_reason",""),
            }
            row.update(extra)
            exists = AMD_POC_EVENT_LOG_FILE.exists()
            with AMD_POC_EVENT_LOG_FILE.open("a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
                if not exists:
                    w.writeheader()
                w.writerow({k: row.get(k,"") for k in fields})
            log.info("AMD+POC | %s | %s | %s | POC=%s | %s",
                     state.get("direction"), event, state.get("stage"),
                     state.get("poc_price"), rejection_reason or state.get("strategy_reason",""))
        except Exception as exc:
            log.warning("AMD+POC event log skipped: %s", short_reason(exc, 100))

    def _amd_poc_reset(self, direction, reason="", prior=None):
        if prior is not None:
            prior["stage"] = "INVALIDATED"
            prior["rejection_reason"] = reason
            if reason:
                self._log_amd_poc_event(prior, "INVALIDATED", rejection_reason=reason)
            self.amd_poc_states[direction] = prior
        else:
            self.amd_poc_states[direction] = self._amd_poc_blank_state(direction)
        self._persist_amd_poc_state()

    def _amd_find_accumulation(self, d, atr14):
        """Objective fixed range ending before the current completed candle."""
        if d is None or len(d) < AMD_POC_MIN_RANGE_CANDLES + 1:
            return None
        base = d.iloc[:-1].copy()
        atr = max(0.01, float(atr14 or 0.0))
        # Prefer the longest qualifying recent range: more observations make the
        # fixed-range volume profile less sensitive to one candle.
        for n in range(min(AMD_POC_MAX_RANGE_CANDLES, len(base)), AMD_POC_MIN_RANGE_CANDLES - 1, -1):
            w = base.tail(n).copy()
            hi = float(w["high"].astype(float).max())
            lo = float(w["low"].astype(float).min())
            mid = max(1.0, (hi + lo) / 2.0)
            width = hi - lo
            width_pct = 100.0 * width / mid
            if width <= 0 or width_pct > AMD_POC_MAX_RANGE_WIDTH_PCT:
                continue
            if atr > 0 and width > atr * AMD_POC_MAX_RANGE_ATR_MULT:
                continue
            touch_tol = max(atr * AMD_POC_TOUCH_TOLERANCE_ATR, width * 0.10, 0.5)
            hi_touches = int((w["high"].astype(float) >= hi - touch_tol).sum())
            lo_touches = int((w["low"].astype(float) <= lo + touch_tol).sum())
            if hi_touches < AMD_POC_MIN_HIGH_TOUCHES or lo_touches < AMD_POC_MIN_LOW_TOUCHES:
                continue
            return {
                "frame": w,
                "start": str(w.iloc[0]["time"]),
                "end": str(w.iloc[-1]["time"]),
                "high": hi, "low": lo, "candles": n,
                "uid": f"{str(w.iloc[0]['time'])}|{str(w.iloc[-1]['time'])}|{hi:.2f}|{lo:.2f}",
            }
        return None

    def _amd_volume_profile(self, acc):
        """Build fixed-range POC from NIFTY Futures traded volume when available.

        Futures POC is translated to index space with the median futures-index
        basis over aligned 5-minute closes, so retests are evaluated on NIFTY spot.
        """
        idx = acc["frame"].copy()
        futures = pd.DataFrame()
        if callable(self.futures_profile_provider):
            try:
                futures = self.futures_profile_provider(acc["start"], acc["end"])
            except Exception as exc:
                log.warning("AMD+POC futures profile fetch skipped: %s", short_reason(exc, 100))
        source = "NIFTY FUTURES"
        profile = futures.copy() if isinstance(futures, pd.DataFrame) else pd.DataFrame()
        basis = 0.0
        if not profile.empty:
            for col in ("open","high","low","close","volume"):
                if col not in profile.columns:
                    profile = pd.DataFrame()
                    break
        if not profile.empty:
            profile["time"] = pd.to_datetime(profile["time"], errors="coerce", utc=True).dt.tz_convert(self.tz_name)
            for col in ("open","high","low","close","volume"):
                profile[col] = pd.to_numeric(profile[col], errors="coerce")
            profile = profile.dropna(subset=["time","high","low","close","volume"])
            profile = profile[profile["volume"] > 0].sort_values("time")
            try:
                ix = idx[["time","close"]].copy()
                ix["time"] = pd.to_datetime(ix["time"], errors="coerce", utc=True).dt.tz_convert(self.tz_name)
                ix["close"] = pd.to_numeric(ix["close"], errors="coerce")
                aligned = pd.merge_asof(
                    profile[["time","close"]].sort_values("time"),
                    ix.dropna().sort_values("time"),
                    on="time", suffixes=("_fut","_idx"),
                    direction="nearest", tolerance=pd.Timedelta("3min"),
                ).dropna()
                if not aligned.empty:
                    basis = float((aligned["close_fut"] - aligned["close_idx"]).median())
            except Exception:
                basis = 0.0

        # Safe fallback exists for non-NIFTY/testing feeds only when index volume
        # is genuinely populated; empty index volume is never fabricated.
        if profile.empty or float(profile["volume"].sum()) <= 0:
            iv = idx.copy()
            iv["volume"] = pd.to_numeric(iv.get("volume"), errors="coerce").fillna(0.0)
            if float(iv["volume"].sum()) <= 0:
                return None
            profile = iv
            source = "INDEX VOLUME FALLBACK"
            basis = 0.0

        typical = (profile["high"].astype(float) + profile["low"].astype(float) + profile["close"].astype(float)) / 3.0
        lo = float(profile["low"].min())
        hi = float(profile["high"].max())
        if not math.isfinite(lo) or not math.isfinite(hi) or hi <= lo:
            return None
        bin_size = max(AMD_POC_MIN_BIN_POINTS, (hi - lo) / max(4, AMD_POC_PROFILE_BINS))
        bins = {}
        total = 0.0
        for px, vol in zip(typical.tolist(), profile["volume"].astype(float).tolist()):
            if not math.isfinite(px) or not math.isfinite(vol) or vol <= 0:
                continue
            k = int(math.floor((px - lo) / bin_size))
            bins[k] = bins.get(k, 0.0) + vol
            total += vol
        if not bins or total <= 0:
            return None
        poc_bin = max(bins.items(), key=lambda kv: kv[1])[0]
        futures_poc = lo + (poc_bin + 0.5) * bin_size
        index_poc = futures_poc - basis
        # The translated POC must stay plausibly near the detected index range.
        range_pad = max((acc["high"] - acc["low"]) * 0.35, 5.0)
        index_poc = max(acc["low"] - range_pad, min(acc["high"] + range_pad, index_poc))
        distribution = {
            f"{(lo + (k + 0.5) * bin_size - basis):.2f}": round(float(v), 2)
            for k, v in sorted(bins.items())
        }
        return {
            "poc": round(float(index_poc), 2),
            "total_volume": round(total, 2),
            "bin_size": round(float(bin_size), 4),
            "source": source,
            "distribution": distribution,
            "futures_poc": round(float(futures_poc), 2),
            "basis": round(float(basis), 2),
        }

    def _amd_structural_target(self, d, confirm, state, direction, entry, structural_sl):
        """Resolve only the AMD underlying structural target metadata.

        This does NOT replace Viju_Trade's existing option-premium target logic.
        """
        mode = str(AMD_POC_TARGET_MODE or "OPPOSITE_RANGE").upper().strip()
        if mode == "EXTERNAL":
            return None, "EXTERNAL / EXISTING TARGET ENGINE"
        if mode == "FIXED_RR":
            risk = abs(float(entry) - float(structural_sl))
            if risk <= 0:
                return None, "FIXED_RR INVALID RISK"
            target = entry + risk * AMD_POC_FIXED_RR if direction == "BULLISH" else entry - risk * AMD_POC_FIXED_RR
            return float(target), f"FIXED {AMD_POC_FIXED_RR:.2f}R"
        if mode == "PREVIOUS_SWING":
            prior = d[pd.to_datetime(d["time"]) < pd.to_datetime(confirm["time"])].tail(AMD_POC_TARGET_LOOKBACK_BARS)
            if prior.empty:
                return None, "PREVIOUS SWING UNAVAILABLE"
            target = float(prior["high"].max()) if direction == "BULLISH" else float(prior["low"].min())
            return target, "PREVIOUS SWING HIGH" if direction == "BULLISH" else "PREVIOUS SWING LOW"
        if mode == "LIQUIDITY_ZONE":
            prior = d[pd.to_datetime(d["time"]) < pd.to_datetime(confirm["time"])].tail(AMD_POC_TARGET_LOOKBACK_BARS).copy()
            if len(prior) >= 5:
                highs = prior["high"].astype(float).tolist(); lows = prior["low"].astype(float).tolist()
                piv_hi=[]; piv_lo=[]
                for i in range(2, len(prior)-2):
                    if highs[i] == max(highs[i-2:i+3]): piv_hi.append(highs[i])
                    if lows[i] == min(lows[i-2:i+3]): piv_lo.append(lows[i])
                if direction == "BULLISH":
                    valid = sorted(x for x in piv_hi if x > entry)
                    if valid: return float(valid[0]), "NEAREST PRIOR LIQUIDITY HIGH"
                else:
                    valid = sorted((x for x in piv_lo if x < entry), reverse=True)
                    if valid: return float(valid[0]), "NEAREST PRIOR LIQUIDITY LOW"
            return None, "LIQUIDITY ZONE UNAVAILABLE"
        target = float(state["range_high"] if direction == "BULLISH" else state["range_low"])
        return target, "OPPOSITE SIDE OF ACCUMULATION"

    def _amd_poc_candidate_locked(self, df, atr14):
        candidates = []
        if df is None or len(df) < AMD_POC_MIN_RANGE_CANDLES + 2:
            return candidates
        d = df.copy().sort_values("time").reset_index(drop=True)
        latest = d.iloc[-1]
        latest_time = str(latest["time"])
        acc = self._amd_find_accumulation(d, atr14)
        profile = None
        if acc is not None:
            needs_profile = any(
                (self.amd_poc_states.get(direction) or {}).get("stage") in ("IDLE","INVALIDATED")
                and (self.amd_poc_states.get(direction) or {}).get("setup_uid") != acc["uid"]
                for direction in ("BULLISH","BEARISH")
            )
            if needs_profile:
                profile = self._amd_volume_profile(acc)

        for direction in ("BULLISH","BEARISH"):
            state = self.amd_poc_states.get(direction) or self._amd_poc_blank_state(direction)

            if state.get("stage") == "COMPLETE":
                if not acc or str(acc["end"]) <= str(state.get("accumulation_end") or ""):
                    continue
                state = self._amd_poc_blank_state(direction)
                self.amd_poc_states[direction] = state

            if state.get("stage") == "RETEST_CONFIRMED":
                pass
            elif state.get("last_processed_candle") == latest_time:
                continue
            state["last_processed_candle"] = latest_time

            # Lock a qualifying accumulation and its fixed POC.
            if state.get("stage") in ("IDLE","INVALIDATED"):
                if not acc:
                    continue
                if state.get("setup_uid") == acc["uid"] and state.get("stage") == "INVALIDATED":
                    continue
                if not profile:
                    peer = self.amd_poc_states.get("BEARISH" if direction=="BULLISH" else "BULLISH") or {}
                    if peer.get("setup_uid") == acc["uid"] and peer.get("poc_price") is not None:
                        profile = {
                            "poc": peer.get("poc_price"),
                            "total_volume": peer.get("profile_total_volume",0.0),
                            "bin_size": peer.get("profile_bin_size"),
                            "source": peer.get("profile_source","FUTURES"),
                            "distribution": json.loads(peer.get("profile_distribution") or "{}"),
                            "futures_poc": peer.get("futures_poc_price"),
                            "basis": peer.get("futures_index_basis"),
                        }
                if not profile:
                    tmp = self._amd_poc_blank_state(direction)
                    tmp.update({
                        "stage":"INVALIDATED","setup_uid":acc["uid"],
                        "accumulation_start":acc["start"],"accumulation_end":acc["end"],
                        "range_high":round(acc["high"],2),"range_low":round(acc["low"],2),
                        "range_candles":acc["candles"],
                    })
                    self._log_amd_poc_event(tmp, "INVALIDATED", "ACCUMULATION FOUND BUT NO RELIABLE VOLUME PROFILE")
                    self.amd_poc_states[direction] = tmp
                    continue
                state = self._amd_poc_blank_state(direction)
                state.update({
                    "stage":"ACCUMULATION_FOUND",
                    "setup_uid":acc["uid"],
                    "accumulation_start":acc["start"],"accumulation_end":acc["end"],
                    "range_high":round(acc["high"],2),"range_low":round(acc["low"],2),
                    "range_candles":acc["candles"],
                })
                self.amd_poc_states[direction] = state
                self._log_amd_poc_event(state,"ACCUMULATION_FOUND")
                state.update({
                    "stage":"POC_CALCULATED",
                    "poc_price":profile["poc"],
                    "profile_total_volume":profile["total_volume"],
                    "profile_bin_size":profile["bin_size"],
                    "profile_source":profile["source"],
                    "profile_distribution":json.dumps(profile.get("distribution") or {}, separators=(",", ":"), sort_keys=True),
                    "futures_poc_price":profile.get("futures_poc"),
                    "futures_index_basis":profile.get("basis"),
                })
                self._log_amd_poc_event(state,"POC_CALCULATED")

            # Current event must occur after the fixed accumulation window.
            if pd.to_datetime(latest["time"]) <= pd.to_datetime(state.get("accumulation_end") or latest["time"]):
                continue

            atr = max(0.01, float(atr14 or 0.0))
            latest_close = float(latest["close"])
            manip_min = max(
                0.5,
                atr * AMD_POC_MIN_MANIPULATION_ATR,
                latest_close * AMD_POC_MIN_MANIPULATION_PCT / 100.0,
            )
            if state.get("stage") == "POC_CALCULATED":
                lo=float(state["range_low"]); hi=float(state["range_high"])
                max_pre_break = max(
                    0.5,
                    atr * AMD_POC_MAX_BREAKOUT_BEFORE_MANIP_ATR,
                    latest_close * AMD_POC_MAX_BREAKOUT_BEFORE_MANIP_PCT / 100.0,
                )
                if latest_close < lo - max_pre_break or latest_close > hi + max_pre_break:
                    self._amd_poc_reset(direction, "DECISIVE BREAKOUT BEFORE MANIPULATION", state)
                    continue
                if direction=="BULLISH" and float(latest["low"]) < lo - manip_min:
                    m=float(latest["low"])
                elif direction=="BEARISH" and float(latest["high"]) > hi + manip_min:
                    m=float(latest["high"])
                else:
                    m=None
                if m is not None:
                    state.update({
                        "stage":"MANIPULATION_DETECTED",
                        "manipulation_price":round(m,2),
                        "manipulation_low":round(float(latest["low"]),2),
                        "manipulation_high":round(float(latest["high"]),2),
                        "manipulation_time":latest_time,
                        "setup_invalidation_level":round(m,2),
                    })
                    self._log_amd_poc_event(state,"MANIPULATION_DETECTED")

            if state.get("stage") in ("MANIPULATION_DETECTED","POC_CROSSED","WAITING_FOR_RETEST","RETEST_CONFIRMED"):
                mt=state.get("manipulation_time")
                later=d[pd.to_datetime(d["time"]) > pd.to_datetime(mt)].copy() if mt else pd.DataFrame()
                if len(later) > AMD_POC_MAX_SETUP_BARS:
                    self._amd_poc_reset(direction, f"SETUP TIMEOUT > {AMD_POC_MAX_SETUP_BARS} BARS", state)
                    continue
                if not later.empty:
                    close=float(later.iloc[-1]["close"]); inv=float(state["setup_invalidation_level"])
                    if (direction=="BULLISH" and close < inv) or (direction=="BEARISH" and close > inv):
                        self._amd_poc_reset(direction,"STRUCTURAL INVALIDATION BEYOND MANIPULATION EXTREME",state)
                        continue

            if state.get("stage") == "MANIPULATION_DETECTED":
                after=d[pd.to_datetime(d["time"]) > pd.to_datetime(state["manipulation_time"])].copy()
                poc=float(state["poc_price"])
                cross=None
                for _,row in after.iterrows():
                    c=float(row["close"])
                    if direction=="BULLISH" and c > poc: cross=row; break
                    if direction=="BEARISH" and c < poc: cross=row; break
                if cross is not None:
                    state["poc_cross_time"]=str(cross["time"])
                    state["stage"]="POC_CROSSED"
                    self._log_amd_poc_event(state,"POC_CROSSED")
                    state["stage"]="WAITING_FOR_RETEST"
                    self._log_amd_poc_event(state,"WAITING_FOR_RETEST")

            if state.get("stage") == "WAITING_FOR_RETEST":
                after=d[pd.to_datetime(d["time"]) > pd.to_datetime(state["poc_cross_time"])].copy()
                poc=float(state["poc_price"])
                tol=max(poc * AMD_POC_RETEST_TOLERANCE_PCT/100.0,
                        max(0.01,float(atr14 or 0.0))*AMD_POC_RETEST_TOLERANCE_ATR, 0.5)
                confirm=None
                for _,row in after.iterrows():
                    op=float(row["open"]); hi=float(row["high"]); lo=float(row["low"]); cl=float(row["close"])
                    rng=max(1e-9,hi-lo); body=abs(cl-op)/rng
                    touched=(lo <= poc + tol and hi >= poc - tol)
                    if direction=="BULLISH":
                        if cl < poc - tol:
                            self._amd_poc_reset(direction,"POC LOST BEFORE BULLISH RETEST HOLD",state)
                            state=self.amd_poc_states[direction]; break
                        if touched and cl >= poc and cl > op and body >= AMD_POC_CONFIRM_BODY_MIN_RATIO:
                            confirm=row; break
                    else:
                        if cl > poc + tol:
                            self._amd_poc_reset(direction,"POC RECLAIMED BEFORE BEARISH RETEST REJECTION",state)
                            state=self.amd_poc_states[direction]; break
                        if touched and cl <= poc and cl < op and body >= AMD_POC_CONFIRM_BODY_MIN_RATIO:
                            confirm=row; break
                if confirm is not None:
                    entry=float(confirm["close"])
                    sl_buffer=max(
                        0.5,
                        max(0.01,float(atr14 or 0.0))*AMD_POC_SL_BUFFER_ATR,
                        entry*AMD_POC_SL_BUFFER_PCT/100.0,
                    )
                    if direction=="BULLISH":
                        structural_sl=min(float(state.get("manipulation_low") or confirm["low"]), float(confirm["low"])) - sl_buffer
                    else:
                        structural_sl=max(float(state.get("manipulation_high") or confirm["high"]), float(confirm["high"])) + sl_buffer
                    target, target_type = self._amd_structural_target(
                        d, confirm, state, direction, entry, structural_sl
                    )
                    state.update({
                        "stage":"RETEST_CONFIRMED",
                        "poc_retest_time":str(confirm["time"]),
                        "entry_underlying_price":round(entry,2),
                        "structural_sl":round(float(structural_sl),2),
                        "setup_invalidation_level":round(float(structural_sl),2),
                        "target_liquidity":round(float(target),2) if target is not None else None,
                        "target_type":target_type,
                        "strategy_reason":(
                            "ACCUMULATION → BELOW-RANGE MANIPULATION → POC RECLAIM → POC RETEST HELD → BULLISH"
                            if direction=="BULLISH" else
                            "ACCUMULATION → ABOVE-RANGE MANIPULATION → POC BREAK BELOW → POC RETEST REJECTED → BEARISH"
                        ),
                    })
                    self._log_amd_poc_event(state,"RETEST_CONFIRMED")

            if state.get("stage") == "RETEST_CONFIRMED":
                candidates.append({
                    "setup":AMD_POC_SETUP_NAME,
                    "direction":"CE" if direction=="BULLISH" else "PE",
                    "tech_score":AMD_POC_TECH_SCORE,
                    "setup_grade":"A",
                    "entry_ready":True,
                    "entry_block_reason":"",
                    "strategy_event_time":state.get("poc_retest_time") or latest_time,
                    "strategy_id":AMD_POC_STRATEGY_ID,
                    "strategy_short_name":AMD_POC_SHORT_NAME,
                    "strategy_status":AMD_POC_STATUS,
                    "strategy_reason":state.get("strategy_reason"),
                    "amd_accumulation_start":state.get("accumulation_start"),
                    "amd_accumulation_end":state.get("accumulation_end"),
                    "amd_range_high":state.get("range_high"),
                    "amd_range_low":state.get("range_low"),
                    "amd_poc_price":state.get("poc_price"),
                    "amd_profile_total_volume":state.get("profile_total_volume"),
                    "amd_profile_bin_size":state.get("profile_bin_size"),
                    "amd_profile_source":state.get("profile_source"),
                    "amd_profile_distribution":state.get("profile_distribution"),
                    "amd_futures_poc_price":state.get("futures_poc_price"),
                    "amd_futures_index_basis":state.get("futures_index_basis"),
                    "amd_manipulation_price":state.get("manipulation_price"),
                    "amd_manipulation_time":state.get("manipulation_time"),
                    "amd_poc_cross_time":state.get("poc_cross_time"),
                    "amd_poc_retest_time":state.get("poc_retest_time"),
                    "setup_invalidation_level":state.get("setup_invalidation_level"),
                    "target_liquidity":state.get("target_liquidity"),
                    "target_liquidity_type":state.get("target_type"),
                })
            self.amd_poc_states[direction]=state

        self._persist_amd_poc_state()
        return candidates

    def mark_amd_poc_complete(self, tech, candidate, entry_premium, signal_no, underlying_entry_price=None):
        if str(tech.get("strategy_id") or "") != AMD_POC_STRATEGY_ID:
            return
        direction="BULLISH" if str(tech.get("direction") or "").upper()=="CE" else "BEARISH"
        state=self.amd_poc_states.get(direction)
        if not state or state.get("stage") != "RETEST_CONFIRMED":
            return
        state["entry_time"]=now_ist().isoformat()
        if underlying_entry_price is not None:
            state["entry_underlying_price"]=round(float(underlying_entry_price),2)
        state["stage"]="SIGNAL"
        self._log_amd_poc_event(
            state,"SIGNAL",
            option_type="CE" if direction=="BULLISH" else "PE",
            option_selected=str(candidate.get("symbol") or ""),
            option_entry_premium=entry_premium, signal_no=signal_no,
        )
        state["stage"]="COMPLETE"
        state["complete_time"]=now_ist().isoformat()
        self._log_amd_poc_event(state,"COMPLETE")
        self._persist_amd_poc_state()

    def _normalize_df_locked(self, df):
        if df is None or df.empty:
            return pd.DataFrame(
                columns=["time", "open", "high", "low", "close", "volume"]
            )

        out = df.copy()
        out["time"] = pd.to_datetime(out["time"], errors="coerce", utc=True)
        out["time"] = out["time"].dt.tz_convert(self.tz_name)

        for col in ["open", "high", "low", "close", "volume"]:
            out[col] = pd.to_numeric(out[col], errors="coerce")

        out = out.dropna(subset=["time", "open", "high", "low", "close"])
        out["volume"] = out["volume"].fillna(0)

        # Hard OHLC sanity: malformed rows must never enter EMA/ATR/ADX.
        valid_ohlc = (
            (out["open"] > 0)
            & (out["high"] > 0)
            & (out["low"] > 0)
            & (out["close"] > 0)
            & (out["high"] >= out[["open", "close", "low"]].max(axis=1))
            & (out["low"] <= out[["open", "close", "high"]].min(axis=1))
        )
        if (~valid_ohlc).any():
            bad = out.loc[~valid_ohlc, ["time", "open", "high", "low", "close"]]
            for _, row in bad.tail(5).iterrows():
                log.warning(
                    "DATA MISSING/CORRUPT | 5M OHLC quarantined | %s O=%s H=%s L=%s C=%s",
                    row.get("time"), row.get("open"), row.get("high"), row.get("low"), row.get("close"),
                )
            out = out.loc[valid_ohlc].copy()

        out = (
            out.sort_values("time")
            .drop_duplicates(subset=["time"], keep="last")
            .reset_index(drop=True)
        )

        # Conservative spike quarantine. A row is removed only when its range is
        # extreme relative to recent candles AND both neighbouring prices remain
        # continuous. This is intended for isolated corrupt historical/cache rows,
        # not genuine directional moves.
        if len(out) >= 25:
            ranges = (out["high"] - out["low"]).abs()
            med = ranges.rolling(20, min_periods=10).median().shift(1)
            prev_close = out["close"].shift(1)
            next_open = out["open"].shift(-1)
            price_ref = prev_close.abs().replace(0, pd.NA)
            extreme_range = ranges > pd.concat(
                [med * 8.0, price_ref * 0.015], axis=1
            ).max(axis=1)
            neighbour_continuity = (
                ((out["open"] - prev_close).abs() / price_ref <= 0.006)
                & ((next_open - out["close"]).abs() / out["close"].abs().replace(0, pd.NA) <= 0.006)
            )
            suspicious = extreme_range & neighbour_continuity & med.notna() & next_open.notna()
            if suspicious.any():
                bad = out.loc[suspicious, ["time", "open", "high", "low", "close"]]
                for _, row in bad.iterrows():
                    log.warning(
                        "DATA MISSING/CORRUPT | suspicious 5M spike quarantined pending broker repair | "
                        "%s O=%.2f H=%.2f L=%.2f C=%.2f",
                        row["time"], row["open"], row["high"], row["low"], row["close"],
                    )
                out = out.loc[~suspicious].reset_index(drop=True)

        return out.tail(1200).reset_index(drop=True)

    def _load_cache_locked(self):
        if not os.path.exists(self.cache_file):
            return
        try:
            df = pd.read_csv(self.cache_file)
            if df.empty:
                return
            required = {"time", "open", "high", "low", "close", "volume"}
            if not required.issubset(df.columns):
                self.seed_error = "Local technical cache has invalid columns"
                return
            df = self._normalize_df_locked(df)
            current_bucket = self._now().floor("5min")
            self.df = df[df["time"] < current_bucket].reset_index(drop=True)
            if not self.df.empty:
                self.seed_source = "LOCAL CACHE"
        except Exception as exc:
            self.seed_error = f"Cache load failed: {exc}"

    def _save_cache_locked(self):
        try:
            Path(self.cache_file).parent.mkdir(parents=True, exist_ok=True)
            out = self.df.copy().tail(1200)
            if not out.empty:
                out["time"] = out["time"].apply(lambda x: x.isoformat())
            out.to_csv(self.cache_file, index=False)
        except Exception as exc:
            self.seed_error = f"Cache save failed: {exc}"

    def _opening_rows_locked(self):
        if self.df.empty:
            return self.df
        self.df = self._normalize_df_locked(self.df)
        today = self._now().date()
        d = self.df[self.df["time"].dt.date == today]
        return d[
            (d["time"].dt.hour == 9)
            & (d["time"].dt.minute.isin([15, 20, 25]))
        ]

    def _needs_seed_locked(self):
        if not self.df.empty:
            self.df = self._normalize_df_locked(self.df)

        if len(self.df) < 55:
            return True

        now = self._now()
        current_bucket = now.floor("5min")
        latest = self.df["time"].max() if not self.df.empty else None

        if latest is None or latest < (current_bucket - pd.Timedelta(minutes=5)):
            return True

        boundary = now.normalize() + pd.Timedelta(hours=9, minutes=30)
        if now >= boundary and len(self._opening_rows_locked()) < 3:
            return True

        return False

    def initialize(self, smart, angel_rest_call):
        # Keep these references so a late start / temporary Angel history failure can
        # self-heal later. V3.4 only attempted history once at startup.
        self.smart = smart
        self.angel_rest_call = angel_rest_call

        with self.lock:
            self._load_cache_locked()
            needs_seed = self._needs_seed_locked()

        if needs_seed:
            self._try_historical_seed_with_retries(smart, angel_rest_call)

        with self.lock:
            self._compute_snapshot_locked()
            return dict(self.snapshot)

    def _history_recovery_needed(self):
        """Return (needed, reason) for already-completed broker candles.

        The key V3.4.1 rule is that a process started/restarted at 09:41 must not
        wait until 09:45 to create its own first candle. 09:15..09:35 are already
        closed at the broker, so they are backfilled immediately.
        """
        with self.lock:
            if not self.df.empty:
                self.df = self._normalize_df_locked(self.df)

            if len(self.df) < 55:
                return True, f"baseline has only {len(self.df)} closed candles"

            now = self._now()
            if now.weekday() >= 5:
                return False, None

            session_start = now.normalize() + pd.Timedelta(hours=9, minutes=15)
            session_end = now.normalize() + pd.Timedelta(hours=15, minutes=30)
            current_bucket = now.floor("5min")
            latest_expected = current_bucket - pd.Timedelta(minutes=5)

            # Before the first 5-minute candle has closed, prior-session history is
            # sufficient. There is no current-day completed candle to backfill yet.
            if latest_expected < session_start:
                return False, None

            if now > session_end + pd.Timedelta(minutes=5):
                latest_expected = session_end - pd.Timedelta(minutes=5)

            today_df = self.df[self.df["time"].dt.date == now.date()]
            if today_df.empty:
                return True, "no completed candles for today"

            latest_today = today_df["time"].max()
            if latest_today < latest_expected:
                return True, (
                    f"latest today candle {latest_today.strftime('%H:%M')} is behind "
                    f"broker-completed {latest_expected.strftime('%H:%M')}"
                )

            # Detect isolated gaps even when the newest candle exists.
            expected_recent = [
                latest_expected - pd.Timedelta(minutes=10),
                latest_expected - pd.Timedelta(minutes=5),
                latest_expected,
            ]
            present_recent = set(today_df["time"].dt.floor("min").tolist())
            missing_recent = [
                t for t in expected_recent
                if pd.Timestamp(t).floor("min") not in present_recent and t >= session_start
            ]
            if missing_recent:
                return True, "missing completed 5m candles: " + ",".join(
                    t.strftime("%H:%M") for t in missing_recent
                )

            opening = today_df[
                (today_df["time"].dt.hour == 9)
                & (today_df["time"].dt.minute.isin([15, 20, 25]))
            ]
            boundary = now.normalize() + pd.Timedelta(hours=9, minutes=30)
            if now >= boundary and len(opening) < 3:
                return True, "09:15/09:20/09:25 opening-range candles are missing"

            return False, None

    def _history_fetch_window(self, reason="recovery"):
        """Choose the smallest useful SmartAPI historical request window.

        Startup with an insufficient indicator baseline may request several days.
        Normal LIVE recovery asks only for the missing/recent part of today's session,
        reducing SmartAPI rate-limit pressure.
        """
        now = self._now()
        reason_text = str(reason or "").lower()
        with self.lock:
            rows = len(self.df)
            latest_cached = self.df["time"].max() if not self.df.empty else None

        session_start = now.normalize() + pd.Timedelta(hours=9, minutes=15)
        baseline_recent = bool(
            rows >= 55
            and latest_cached is not None
            and latest_cached >= now - pd.Timedelta(days=HISTORICAL_BACKFILL_LOOKBACK_DAYS)
        )

        if (not baseline_recent) or "baseline has only" in reason_text or "startup" in reason_text:
            return now - timedelta(days=HISTORICAL_BACKFILL_LOOKBACK_DAYS), now

        if "09:15/09:20/09:25" in reason_text or "opening" in reason_text:
            return session_start, min(now, session_start + pd.Timedelta(minutes=30))

        # If the reason names specific missing HH:MM slots, request only around
        # the earliest slot plus a small overlap.
        times = re.findall(r"\b([01]\d|2[0-3]):([0-5]\d)\b", reason_text)
        if times:
            hh, mm = map(int, times[0])
            requested = now.normalize() + pd.Timedelta(hours=hh, minutes=mm)
            return max(session_start, requested - pd.Timedelta(minutes=5)), min(now, requested + pd.Timedelta(minutes=15))

        if latest_cached is not None and latest_cached.date() == now.date():
            from_time = max(session_start, latest_cached - pd.Timedelta(minutes=15))
        else:
            from_time = session_start
        return from_time, now

    def _historical_backfill_once(self, smart, angel_rest_call, reason="recovery"):
        with self.lock:
            if self.backfill_running:
                return False, "historical backfill already running"
            self.backfill_running = True
            self.last_backfill_attempt_wallclock = time.time()
            self.last_backfill_reason = reason

        try:
            from_time, to_time = self._history_fetch_window(reason)
            params = {
                "exchange": self.exchange,
                "symboltoken": self.symbol_token,
                "interval": "FIVE_MINUTE",
                "fromdate": from_time.strftime("%Y-%m-%d %H:%M"),
                "todate": to_time.strftime("%Y-%m-%d %H:%M"),
            }
            log.info(
                "Historical backfill (%s): %s -> %s",
                reason,
                params["fromdate"],
                params["todate"],
            )

            result = angel_rest_call(smart.getCandleData, params)
            if not result or not result.get("status") or not result.get("data"):
                raise RuntimeError(f"Historical data unavailable: {result}")

            raw = pd.DataFrame(
                result["data"],
                columns=["time", "open", "high", "low", "close", "volume"],
            )

            with self.lock:
                seed = self._normalize_df_locked(raw)
                current_bucket = self._now().floor("5min")
                seed = seed[seed["time"] < current_bucket]
                if seed.empty:
                    raise RuntimeError("Historical response contained no completed 5m candles")

                merged = pd.concat([self.df, seed], ignore_index=True)
                self.df = self._normalize_df_locked(merged)
                self.seed_error = None
                self.seed_source = "ANGEL HISTORICAL BACKFILL + LOCAL/WEBSOCKET"
                self.last_backfill_success_wallclock = time.time()
                self._save_cache_locked()
                self._compute_snapshot_locked()
                merged_rows = len(self.df)

            log.info(
                "Historical backfill SUCCESS (%s): received=%s merged_cache=%s",
                reason,
                len(seed),
                merged_rows,
            )
            return True, None

        except Exception as exc:
            err = f"{type(exc).__name__}: {short_reason(exc, 180)}"
            with self.lock:
                self.seed_error = f"Historical backfill failed: {err}"
            log.warning("Historical backfill FAILED (%s): %s", reason, err)
            return False, err
        finally:
            with self.lock:
                self.backfill_running = False

    def _try_historical_seed_with_retries(self, smart, angel_rest_call):
        with self.lock:
            if self.seed_attempted:
                return
            self.seed_attempted = True

        last_error = None
        for attempt in range(1, HISTORICAL_SEED_ATTEMPTS + 1):
            log.info("Historical seed attempt %s/%s", attempt, HISTORICAL_SEED_ATTEMPTS)
            ok, err = self._historical_backfill_once(
                smart,
                angel_rest_call,
                reason=f"startup {attempt}/{HISTORICAL_SEED_ATTEMPTS}",
            )
            if ok:
                still_needed, why = self._history_recovery_needed()
                if not still_needed:
                    return
                last_error = f"history merged but still incomplete: {why}"
                log.warning("Historical seed incomplete after merge: %s", why)
            else:
                last_error = err

            if attempt < HISTORICAL_SEED_ATTEMPTS:
                time.sleep(HISTORICAL_SEED_RETRY_SECONDS)

        with self.lock:
            self.seed_error = (
                f"Historical seed incomplete after {HISTORICAL_SEED_ATTEMPTS} attempts: "
                f"{last_error}"
            )
            if self.seed_source == "NONE" and not self.df.empty:
                self.seed_source = "LOCAL CACHE"

        log.warning("Historical seed exhausted; live recovery will keep retrying")

    def maybe_recover_history_async(self):
        """Continuously self-heal missing completed candles without blocking ticks."""
        if self.smart is None or self.angel_rest_call is None:
            return False

        needed, reason = self._history_recovery_needed()
        if not needed:
            return False

        now_ts = time.time()
        with self.lock:
            if self.backfill_running:
                return False
            if now_ts - self.last_backfill_attempt_wallclock < HISTORICAL_RECOVERY_COOLDOWN_SECONDS:
                return False
            # Reserve the cooldown before the thread starts to prevent duplicate workers.
            self.last_backfill_attempt_wallclock = now_ts

        def worker():
            self._historical_backfill_once(
                self.smart,
                self.angel_rest_call,
                reason=reason or "technical history recovery",
            )

        threading.Thread(target=worker, daemon=True, name="technical-history-backfill").start()
        return True

    def on_tick(self, price):
        try:
            price = float(price)
        except Exception:
            return False

        now = self._now()
        bucket = now.floor("5min")

        with self.lock:
            if self.forming is None:
                self.forming = {
                    "time": bucket,
                    "open": price,
                    "high": price,
                    "low": price,
                    "close": price,
                    "volume": 0,
                }
                return False

            forming_time = self.forming["time"]

            if bucket == forming_time:
                self.forming["high"] = max(self.forming["high"], price)
                self.forming["low"] = min(self.forming["low"], price)
                self.forming["close"] = price
                return False

            if bucket < forming_time:
                return False

            row = pd.DataFrame([self.forming])
            self.df = pd.concat([self.df, row], ignore_index=True)
            self.df = self._normalize_df_locked(self.df)

            self.forming = {
                "time": bucket,
                "open": price,
                "high": price,
                "low": price,
                "close": price,
                "volume": 0,
            }
            self.seed_source = "LOCAL CACHE + ANGEL WEBSOCKET"
            self.last_closed_wallclock = time.time()
            self._save_cache_locked()
            self._compute_snapshot_locked()
            return True

    @staticmethod
    def _candle_metrics(row):
        """Return deterministic OHLC geometry for one completed candle."""
        o = float(row["open"])
        h = float(row["high"])
        l = float(row["low"])
        c = float(row["close"])
        rng = max(1e-9, h - l)
        body = abs(c - o)
        upper = max(0.0, h - max(o, c))
        lower = max(0.0, min(o, c) - l)
        body_lo = min(o, c)
        body_hi = max(o, c)
        return {
            "o": o, "h": h, "l": l, "c": c, "range": rng, "body": body,
            "upper": upper, "lower": lower, "body_lo": body_lo, "body_hi": body_hi,
            "body_ratio": body / rng,
            "upper_ratio": upper / rng,
            "lower_ratio": lower / rng,
            "bull": c > o,
            "bear": c < o,
            "doji": (body / rng) <= CANDLE_DOJI_BODY_MAX_RATIO,
            "small": (body / rng) <= CANDLE_SMALL_BODY_MAX_RATIO,
            "long": (body / rng) >= CANDLE_LONG_BODY_MIN_RATIO,
        }

    def _detect_candlestick_patterns_locked(self, today_df, trend, atr14):
        """Recognise standard 1/2/3-candle patterns on completed 5-minute bars.

        Definitions are deterministic OHLC rules. Context-sensitive names such as
        Hammer/Hanging Man and Inverted Hammer/Shooting Star use the current EMA
        trend as the prior-market context. Gap-dependent patterns remain strict and
        therefore may be rare on an intraday index feed.

        The engine returns every pattern ending on the latest completed 5m candle,
        but only the strongest same-direction family bonus is applied to a strategy.
        Overlapping names are intentionally not stacked for score inflation.
        """
        result = {
            "engine": CANDLE_PATTERN_ENGINE_VERSION,
            "patterns": [],
            "primary": "NONE",
            "primary_family": "NONE",
            "primary_direction": "NEUTRAL",
            "bias": "NEUTRAL",
            "bonus_ce": 0.0,
            "bonus_pe": 0.0,
            "best_bullish": "NONE",
            "best_bullish_family": "NONE",
            "best_bearish": "NONE",
            "best_bearish_family": "NONE",
            "conflict": False,
        }
        if today_df is None or len(today_df) < 1:
            return result

        d = today_df.tail(4).reset_index(drop=True)
        bars = [self._candle_metrics(d.iloc[i]) for i in range(len(d))]
        b3 = bars[-1]
        b2 = bars[-2] if len(bars) >= 2 else None
        b1 = bars[-3] if len(bars) >= 3 else None

        atr = float(atr14 or 0.0)
        recent_avg_range = sum(x["range"] for x in bars) / max(1, len(bars))
        tol = max(0.05, atr * 0.03, recent_avg_range * 0.05)

        fam_rank = {"SINGLE": 1, "DOUBLE": 2, "TRIPLE": 3}
        fam_bonus = {
            "SINGLE": CANDLE_SINGLE_CONFIRM_BONUS,
            "DOUBLE": CANDLE_DOUBLE_CONFIRM_BONUS,
            "TRIPLE": CANDLE_TRIPLE_CONFIRM_BONUS,
        }
        seen = set()

        def add(name, family, direction="NEUTRAL", strength=1.0, reason=""):
            key = (name, family, direction)
            if key in seen:
                return
            seen.add(key)
            result["patterns"].append({
                "name": name,
                "family": family,
                "direction": direction,
                "strength": round(float(strength), 2),
                "reason": reason,
            })

        # ------------------------------------------------------------------
        # SINGLE-CANDLE PATTERNS
        # ------------------------------------------------------------------
        # Marubozu: very large real body with minimal shadows.
        if (
            b3["body_ratio"] >= CANDLE_MARUBOZU_BODY_MIN_RATIO
            and b3["upper_ratio"] <= CANDLE_MARUBOZU_WICK_MAX_RATIO
            and b3["lower_ratio"] <= CANDLE_MARUBOZU_WICK_MAX_RATIO
        ):
            if b3["bull"]:
                add("BULLISH MARUBOZU", "SINGLE", "BULLISH", 1.00, "large bullish body, tiny wicks")
            elif b3["bear"]:
                add("BEARISH MARUBOZU", "SINGLE", "BEARISH", 1.00, "large bearish body, tiny wicks")

        # Doji family. Specific doji variants replace generic Doji.
        if b3["doji"]:
            if b3["lower_ratio"] >= 0.60 and b3["upper_ratio"] <= 0.10:
                direction = "BULLISH" if trend == "BEARISH" else "NEUTRAL"
                add("DRAGONFLY DOJI", "SINGLE", direction, 0.90, "doji near high with long lower shadow")
            elif b3["upper_ratio"] >= 0.60 and b3["lower_ratio"] <= 0.10:
                direction = "BEARISH" if trend == "BULLISH" else "NEUTRAL"
                add("GRAVESTONE DOJI", "SINGLE", direction, 0.90, "doji near low with long upper shadow")
            elif b3["upper_ratio"] >= 0.30 and b3["lower_ratio"] >= 0.30:
                add("LONG-LEGGED DOJI", "SINGLE", "NEUTRAL", 0.75, "small body with long two-sided shadows")
            else:
                add("DOJI", "SINGLE", "NEUTRAL", 0.65, "real body <= 10% of candle range")
        elif (
            b3["body_ratio"] <= CANDLE_SMALL_BODY_MAX_RATIO
            and b3["body_ratio"] > CANDLE_DOJI_BODY_MAX_RATIO
            and b3["upper_ratio"] >= 0.20
            and b3["lower_ratio"] >= 0.20
        ):
            add("SPINNING TOP", "SINGLE", "NEUTRAL", 0.60, "small body with meaningful upper/lower wicks")

        # Hammer / Hanging Man share geometry; trend context gives the name.
        hammer_shape = (
            0.06 <= b3["body_ratio"] <= 0.45
            and b3["lower"] >= max(2.0 * b3["body"], 0.50 * b3["range"])
            and b3["upper_ratio"] <= 0.15
        )
        if hammer_shape:
            if trend == "BEARISH":
                add("HAMMER", "SINGLE", "BULLISH", 0.95, "long lower wick after bearish context")
            elif trend == "BULLISH":
                add("HANGING MAN", "SINGLE", "BEARISH", 0.85, "long lower wick after bullish context")
            else:
                add("HAMMER / HANGING-MAN SHAPE", "SINGLE", "NEUTRAL", 0.60, "long lower wick; mixed trend context")

        inverted_shape = (
            0.06 <= b3["body_ratio"] <= 0.45
            and b3["upper"] >= max(2.0 * b3["body"], 0.50 * b3["range"])
            and b3["lower_ratio"] <= 0.15
        )
        if inverted_shape:
            if trend == "BEARISH":
                add("INVERTED HAMMER", "SINGLE", "BULLISH", 0.85, "long upper wick after bearish context")
            elif trend == "BULLISH":
                add("SHOOTING STAR", "SINGLE", "BEARISH", 0.95, "long upper wick after bullish context")
            else:
                add("INVERTED-HAMMER / SHOOTING-STAR SHAPE", "SINGLE", "NEUTRAL", 0.60, "long upper wick; mixed trend context")

        # ------------------------------------------------------------------
        # DOUBLE-CANDLE PATTERNS
        # ------------------------------------------------------------------
        bull_engulf = bear_engulf = False
        bull_harami = bear_harami = False
        if b2 is not None:
            bull_engulf = bool(
                b2["bear"] and b3["bull"]
                and b3["body_lo"] <= b2["body_lo"] + tol
                and b3["body_hi"] >= b2["body_hi"] - tol
                and b3["body"] >= 0.90 * max(b2["body"], 1e-9)
            )
            bear_engulf = bool(
                b2["bull"] and b3["bear"]
                and b3["body_lo"] <= b2["body_lo"] + tol
                and b3["body_hi"] >= b2["body_hi"] - tol
                and b3["body"] >= 0.90 * max(b2["body"], 1e-9)
            )
            if bull_engulf:
                add("BULLISH ENGULFING", "DOUBLE", "BULLISH", 1.00, "bullish body engulfs prior bearish real body")
            if bear_engulf:
                add("BEARISH ENGULFING", "DOUBLE", "BEARISH", 1.00, "bearish body engulfs prior bullish real body")

            inside_body = (
                b3["body_lo"] >= b2["body_lo"] - tol
                and b3["body_hi"] <= b2["body_hi"] + tol
            )
            bull_harami = bool(b2["bear"] and b2["long"] and inside_body and (b3["bull"] or b3["doji"]))
            bear_harami = bool(b2["bull"] and b2["long"] and inside_body and (b3["bear"] or b3["doji"]))
            if bull_harami:
                if b3["doji"]:
                    add("BULLISH HARAMI CROSS", "DOUBLE", "BULLISH", 0.90, "doji contained inside prior bearish body")
                else:
                    add("BULLISH HARAMI", "DOUBLE", "BULLISH", 0.80, "small bullish body inside prior bearish body")
            if bear_harami:
                if b3["doji"]:
                    add("BEARISH HARAMI CROSS", "DOUBLE", "BEARISH", 0.90, "doji contained inside prior bullish body")
                else:
                    add("BEARISH HARAMI", "DOUBLE", "BEARISH", 0.80, "small bearish body inside prior bullish body")

            midpoint2 = (b2["o"] + b2["c"]) / 2.0
            if (
                b2["bear"] and b2["long"] and b3["bull"]
                and b3["o"] <= b2["c"] + tol
                and b3["c"] > midpoint2
                and b3["c"] < b2["o"] + tol
            ):
                add("PIERCING LINE", "DOUBLE", "BULLISH", 0.90, "bull candle closes above midpoint of prior long bear candle")
            if (
                b2["bull"] and b2["long"] and b3["bear"]
                and b3["o"] >= b2["c"] - tol
                and b3["c"] < midpoint2
                and b3["c"] > b2["o"] - tol
            ):
                add("DARK CLOUD COVER", "DOUBLE", "BEARISH", 0.90, "bear candle closes below midpoint of prior long bull candle")

            if b2["bear"] and b3["bull"] and abs(b3["l"] - b2["l"]) <= tol:
                add("TWEEZER BOTTOM", "DOUBLE", "BULLISH", 0.80, "two-candle rejection from nearly equal lows")
            if b2["bull"] and b3["bear"] and abs(b3["h"] - b2["h"]) <= tol:
                add("TWEEZER TOP", "DOUBLE", "BEARISH", 0.80, "two-candle rejection from nearly equal highs")

            # Kicker requires two strong opposite bodies with a real gap between bodies.
            if (
                b2["bear"] and b2["long"] and b3["bull"] and b3["long"]
                and b3["body_lo"] > b2["body_hi"] + tol
            ):
                add("BULLISH KICKER", "DOUBLE", "BULLISH", 1.00, "strong bullish body gaps above prior bearish body")
            if (
                b2["bull"] and b2["long"] and b3["bear"] and b3["long"]
                and b3["body_hi"] < b2["body_lo"] - tol
            ):
                add("BEARISH KICKER", "DOUBLE", "BEARISH", 1.00, "strong bearish body gaps below prior bullish body")

        # ------------------------------------------------------------------
        # TRIPLE-CANDLE PATTERNS
        # ------------------------------------------------------------------
        if b1 is not None and b2 is not None:
            midpoint1 = (b1["o"] + b1["c"]) / 2.0
            morning_core = bool(
                b1["bear"] and b1["long"] and b2["small"]
                and b3["bull"] and b3["body_ratio"] >= 0.45
                and b3["c"] > midpoint1
            )
            evening_core = bool(
                b1["bull"] and b1["long"] and b2["small"]
                and b3["bear"] and b3["body_ratio"] >= 0.45
                and b3["c"] < midpoint1
            )
            if morning_core:
                if b2["doji"]:
                    add("MORNING DOJI STAR", "TRIPLE", "BULLISH", 1.00, "long bear, doji pause, strong bullish recovery")
                else:
                    add("MORNING STAR", "TRIPLE", "BULLISH", 0.95, "long bear, small pause, strong bullish recovery")
            if evening_core:
                if b2["doji"]:
                    add("EVENING DOJI STAR", "TRIPLE", "BEARISH", 1.00, "long bull, doji pause, strong bearish reversal")
                else:
                    add("EVENING STAR", "TRIPLE", "BEARISH", 0.95, "long bull, small pause, strong bearish reversal")

            three_white = bool(
                b1["bull"] and b2["bull"] and b3["bull"]
                and b1["body_ratio"] >= 0.45 and b2["body_ratio"] >= 0.45 and b3["body_ratio"] >= 0.45
                and b1["c"] < b2["c"] < b3["c"]
                and b2["o"] >= b1["body_lo"] - tol and b2["o"] <= b1["body_hi"] + tol
                and b3["o"] >= b2["body_lo"] - tol and b3["o"] <= b2["body_hi"] + tol
                and b1["upper_ratio"] <= 0.30 and b2["upper_ratio"] <= 0.30 and b3["upper_ratio"] <= 0.30
            )
            three_black = bool(
                b1["bear"] and b2["bear"] and b3["bear"]
                and b1["body_ratio"] >= 0.45 and b2["body_ratio"] >= 0.45 and b3["body_ratio"] >= 0.45
                and b1["c"] > b2["c"] > b3["c"]
                and b2["o"] >= b1["body_lo"] - tol and b2["o"] <= b1["body_hi"] + tol
                and b3["o"] >= b2["body_lo"] - tol and b3["o"] <= b2["body_hi"] + tol
                and b1["lower_ratio"] <= 0.30 and b2["lower_ratio"] <= 0.30 and b3["lower_ratio"] <= 0.30
            )
            if three_white:
                add("THREE WHITE SOLDIERS", "TRIPLE", "BULLISH", 1.00, "three strong rising bullish candles")
            if three_black:
                add("THREE BLACK CROWS", "TRIPLE", "BEARISH", 1.00, "three strong falling bearish candles")

            # Three Inside: candle 2 is a harami inside candle 1; candle 3 confirms.
            inside12 = (
                b2["body_lo"] >= b1["body_lo"] - tol
                and b2["body_hi"] <= b1["body_hi"] + tol
            )
            if b1["bear"] and b1["long"] and inside12 and (b2["bull"] or b2["doji"]) and b3["bull"] and b3["c"] > b1["o"]:
                add("THREE INSIDE UP", "TRIPLE", "BULLISH", 0.95, "bullish harami followed by upside confirmation")
            if b1["bull"] and b1["long"] and inside12 and (b2["bear"] or b2["doji"]) and b3["bear"] and b3["c"] < b1["o"]:
                add("THREE INSIDE DOWN", "TRIPLE", "BEARISH", 0.95, "bearish harami followed by downside confirmation")

            # Three Outside: candle 2 engulfs candle 1; candle 3 confirms continuation.
            bull_engulf12 = bool(
                b1["bear"] and b2["bull"]
                and b2["body_lo"] <= b1["body_lo"] + tol
                and b2["body_hi"] >= b1["body_hi"] - tol
            )
            bear_engulf12 = bool(
                b1["bull"] and b2["bear"]
                and b2["body_lo"] <= b1["body_lo"] + tol
                and b2["body_hi"] >= b1["body_hi"] - tol
            )
            if bull_engulf12 and b3["bull"] and b3["c"] > b2["c"]:
                add("THREE OUTSIDE UP", "TRIPLE", "BULLISH", 0.95, "bullish engulfing followed by higher bullish close")
            if bear_engulf12 and b3["bear"] and b3["c"] < b2["c"]:
                add("THREE OUTSIDE DOWN", "TRIPLE", "BEARISH", 0.95, "bearish engulfing followed by lower bearish close")

            # Abandoned Baby / Tri-Star are strict gap patterns and intentionally rare intraday.
            if (
                b1["bear"] and b1["long"] and b2["doji"] and b3["bull"]
                and b2["h"] < b1["l"] - tol
                and b3["l"] > b2["h"] + tol
                and b3["c"] > midpoint1
            ):
                add("BULLISH ABANDONED BABY", "TRIPLE", "BULLISH", 1.00, "isolated doji gap followed by bullish recovery")
            if (
                b1["bull"] and b1["long"] and b2["doji"] and b3["bear"]
                and b2["l"] > b1["h"] + tol
                and b3["h"] < b2["l"] - tol
                and b3["c"] < midpoint1
            ):
                add("BEARISH ABANDONED BABY", "TRIPLE", "BEARISH", 1.00, "isolated doji gap followed by bearish reversal")

            if b1["doji"] and b2["doji"] and b3["doji"]:
                if b2["h"] < min(b1["l"], b3["l"]) - tol:
                    add("BULLISH TRI-STAR", "TRIPLE", "BULLISH", 0.90, "three doji with middle star gapped lower")
                if b2["l"] > max(b1["h"], b3["h"]) + tol:
                    add("BEARISH TRI-STAR", "TRIPLE", "BEARISH", 0.90, "three doji with middle star gapped higher")

        # Strongest pattern first: triple > double > single, then geometry strength.
        result["patterns"].sort(
            key=lambda x: (fam_rank.get(x["family"], 0), float(x.get("strength", 0.0))),
            reverse=True,
        )
        if result["patterns"]:
            primary = result["patterns"][0]
            result["primary"] = primary["name"]
            result["primary_family"] = primary["family"]
            result["primary_direction"] = primary["direction"]

        bull = [x for x in result["patterns"] if x["direction"] == "BULLISH"]
        bear = [x for x in result["patterns"] if x["direction"] == "BEARISH"]
        result["conflict"] = bool(bull and bear)
        if bull:
            result["best_bullish"] = bull[0]["name"]
            result["best_bullish_family"] = bull[0]["family"]
        if bear:
            result["best_bearish"] = bear[0]["name"]
            result["best_bearish_family"] = bear[0]["family"]
        if bull and not bear:
            result["bias"] = "BULLISH"
        elif bear and not bull:
            result["bias"] = "BEARISH"
        elif bull and bear:
            result["bias"] = "MIXED"
        else:
            result["bias"] = "NEUTRAL"

        if bull:
            result["bonus_ce"] = min(
                CANDLE_MAX_CONFIRM_BONUS,
                max(fam_bonus.get(x["family"], 0.0) for x in bull),
            )
        if bear:
            result["bonus_pe"] = min(
                CANDLE_MAX_CONFIRM_BONUS,
                max(fam_bonus.get(x["family"], 0.0) for x in bear),
            )
        return result

    def _compute_snapshot_locked(self):
        base = self._empty_snapshot()
        base["source"] = self.seed_source or "LOCAL CACHE + ANGEL WEBSOCKET"
        base["cache_rows"] = len(self.df)

        if len(self.df) < 55:
            msg = f"Need at least 55 closed 5m candles; cache has {len(self.df)}"
            if self.seed_error:
                msg += f". {self.seed_error}"
            base["error"] = msg
            self.snapshot = base
            return

        self.df = self._normalize_df_locked(self.df)
        df = self.df.copy().sort_values("time").reset_index(drop=True)
        current_bucket = self._now().floor("5min")
        df = df[df["time"] < current_bucket].copy()
        if len(df) < 55:
            base["error"] = "Not enough completed cached candles"
            self.snapshot = base
            return

        df["ema20"] = df["close"].ewm(span=20, adjust=False).mean()
        df["ema50"] = df["close"].ewm(span=50, adjust=False).mean()

        prev_close = df["close"].shift(1)
        tr = pd.concat([
            (df["high"] - df["low"]).abs(),
            (df["high"] - prev_close).abs(),
            (df["low"] - prev_close).abs(),
        ], axis=1).max(axis=1)
        df["atr14"] = tr.ewm(alpha=1/14, adjust=False, min_periods=14).mean()

        up_move = df["high"].diff()
        down_move = -df["low"].diff()
        plus_dm = up_move.where((up_move > down_move) & (up_move > 0), 0.0)
        minus_dm = down_move.where((down_move > up_move) & (down_move > 0), 0.0)
        atr_w = tr.ewm(alpha=1/14, adjust=False, min_periods=14).mean().replace(0, pd.NA)
        plus_di = 100 * plus_dm.ewm(alpha=1/14, adjust=False, min_periods=14).mean() / atr_w
        minus_di = 100 * minus_dm.ewm(alpha=1/14, adjust=False, min_periods=14).mean() / atr_w
        dx = 100 * (plus_di - minus_di).abs() / (plus_di + minus_di).replace(0, pd.NA)
        df["plus_di14"] = plus_di
        df["minus_di14"] = minus_di
        df["adx14"] = dx.ewm(alpha=1/14, adjust=False, min_periods=14).mean()

        latest = df.iloc[-1]
        previous = df.iloc[-2]
        previous2 = df.iloc[-3]
        today = self._now().date()
        today_df = df[df["time"].dt.date == today].copy()
        if today_df.empty:
            base["error"] = "No completed candles for today yet"
            self.snapshot = base
            return

        opening = today_df[(today_df["time"].dt.hour == 9) & (today_df["time"].dt.minute.isin([15,20,25]))]
        if len(opening) < 3:
            msg = "Today's 09:15/09:20/09:25 opening-range candles are missing"
            if self.seed_error:
                msg += f". {self.seed_error}"
            base["error"] = msg
            self.snapshot = base
            return

        price = float(latest["close"])
        ema20 = float(latest["ema20"])
        ema50 = float(latest["ema50"])
        prev_ema20 = float(previous["ema20"])
        atr14 = safe_float(latest.get("atr14"))
        adx14 = safe_float(latest.get("adx14"))
        plus_di14 = safe_float(latest.get("plus_di14"))
        minus_di14 = safe_float(latest.get("minus_di14"))
        ema20_slope = ema20 - float(previous2["ema20"])
        ema50_slope = ema50 - float(previous2["ema50"])
        day_high = float(today_df["high"].max())
        day_low = float(today_df["low"].min())
        or_high = float(opening["high"].max())
        or_low = float(opening["low"].min())

        if price > ema20 > ema50:
            trend = "BULLISH"
        elif price < ema20 < ema50:
            trend = "BEARISH"
        else:
            trend = "MIXED"

        if latest["close"] > previous["close"]:
            momentum = "UP"
        elif latest["close"] < previous["close"]:
            momentum = "DOWN"
        else:
            momentum = "FLAT"

        if latest["high"] > previous["high"] and latest["low"] > previous["low"]:
            structure = "HIGHER HIGH / HIGHER LOW"
        elif latest["high"] < previous["high"] and latest["low"] < previous["low"]:
            structure = "LOWER HIGH / LOWER LOW"
        else:
            structure = "MIXED"

        if price > or_high:
            or_status = "ABOVE OPENING RANGE"
        elif price < or_low:
            or_status = "BELOW OPENING RANGE"
        else:
            or_status = "INSIDE OPENING RANGE"

        patterns = []
        ema_sep_pct = abs(ema20 - ema50) / price * 100 if price else 0.0
        sep_bonus = min(6.0, ema_sep_pct * 20.0)
        bullish_structure = structure == "HIGHER HIGH / HIGHER LOW"
        bearish_structure = structure == "LOWER HIGH / LOWER LOW"

        # Indicator gate first: trend strength + directional movement must agree.
        if adx14 is None or plus_di14 is None or minus_di14 is None:
            indicator_ok_ce = indicator_ok_pe = False
        else:
            indicator_ok_ce = adx14 >= MIN_ADX and plus_di14 > minus_di14
            indicator_ok_pe = adx14 >= MIN_ADX and minus_di14 > plus_di14

        # 1) Opening-range breakout -- V3.4 requires a FRESH completed-candle crossing.
        # Merely remaining above/below the opening range hours later is not a new breakout event.
        prev_price = float(previous["close"])
        fresh_or_break_up = prev_price <= or_high and price > or_high
        fresh_or_break_down = prev_price >= or_low and price < or_low
        if indicator_ok_ce and trend == "BULLISH" and momentum == "UP" and fresh_or_break_up and not bearish_structure:
            score = 84.0 + (6.0 if bullish_structure else 2.0) + sep_bonus + min(5.0, max(0.0, adx14-20)/4)
            patterns.append((min(100.0, score), "CE", "OPENING RANGE BREAKOUT"))
        if indicator_ok_pe and trend == "BEARISH" and momentum == "DOWN" and fresh_or_break_down and not bullish_structure:
            score = 84.0 + (6.0 if bearish_structure else 2.0) + sep_bonus + min(5.0, max(0.0, adx14-20)/4)
            patterns.append((min(100.0, score), "PE", "OPENING RANGE BREAKOUT"))

        # 2) Opening-range break + retest
        recent_before_latest = today_df.iloc[:-1].tail(4)
        prior_break_up = not recent_before_latest.empty and (recent_before_latest["close"] > or_high).any()
        prior_break_down = not recent_before_latest.empty and (recent_before_latest["close"] < or_low).any()
        retest_tol = max((atr14 or 0) * 0.15, price * 0.0006)
        if indicator_ok_ce and trend == "BULLISH" and momentum == "UP" and prior_break_up and float(latest["low"]) <= or_high + retest_tol and price > or_high and not bearish_structure:
            score = 88.0 + (5.0 if bullish_structure else 1.0) + sep_bonus
            patterns.append((min(100.0, score), "CE", "OPENING RANGE RETEST"))
        if indicator_ok_pe and trend == "BEARISH" and momentum == "DOWN" and prior_break_down and float(latest["high"]) >= or_low - retest_tol and price < or_low and not bullish_structure:
            score = 88.0 + (5.0 if bearish_structure else 1.0) + sep_bonus
            patterns.append((min(100.0, score), "PE", "OPENING RANGE RETEST"))

        # 3) EMA20 pullback continuation. Inside OR requires stronger ADX.
        ema_tol = max((atr14 or 0) * 0.18, price * 0.0010)
        bullish_pullback_touched = float(previous["low"]) <= prev_ema20 + ema_tol or float(latest["low"]) <= ema20 + ema_tol
        bearish_pullback_touched = float(previous["high"]) >= prev_ema20 - ema_tol or float(latest["high"]) >= ema20 - ema_tol
        inside_or_ok = adx14 is not None and adx14 >= MIN_ADX_INSIDE_OR

        if indicator_ok_ce and trend == "BULLISH" and momentum == "UP" and price > ema20 and bullish_pullback_touched and not bearish_structure and (or_status != "INSIDE OPENING RANGE" or inside_or_ok):
            score = 76.0 + (7.0 if bullish_structure else 2.0) + sep_bonus + min(4.0, max(0.0, adx14-20)/5)
            patterns.append((min(95.0, score), "CE", "EMA20 PULLBACK CONTINUATION"))
        if indicator_ok_pe and trend == "BEARISH" and momentum == "DOWN" and price < ema20 and bearish_pullback_touched and not bullish_structure and (or_status != "INSIDE OPENING RANGE" or inside_or_ok):
            score = 76.0 + (7.0 if bearish_structure else 2.0) + sep_bonus + min(4.0, max(0.0, adx14-20)/5)
            patterns.append((min(95.0, score), "PE", "EMA20 PULLBACK CONTINUATION"))

        # 4) Day high / low continuation after 10:15
        current_minutes = self._now().hour * 60 + self._now().minute
        prior_today = today_df.iloc[:-1]
        if current_minutes >= 615 and not prior_today.empty:
            prior_high = float(prior_today["high"].max())
            prior_low = float(prior_today["low"].min())
            if indicator_ok_ce and trend == "BULLISH" and momentum == "UP" and price > prior_high and not bearish_structure:
                patterns.append((min(100.0, 84.0 + (6.0 if bullish_structure else 2.0) + sep_bonus), "CE", "DAY HIGH CONTINUATION"))
            if indicator_ok_pe and trend == "BEARISH" and momentum == "DOWN" and price < prior_low and not bullish_structure:
                patterns.append((min(100.0, 84.0 + (6.0 if bearish_structure else 2.0) + sep_bonus), "PE", "DAY LOW CONTINUATION"))

        # 5) Fallback continuation only when ADX is solid and structure agrees.
        distance_from_ema20_pct = abs(price - ema20) / price * 100 if price else 999.0
        if indicator_ok_ce and bullish_structure and trend == "BULLISH" and momentum == "UP" and price > ema20 and distance_from_ema20_pct <= 0.45 and adx14 >= MIN_ADX_B_GRADE:
            patterns.append((min(84.0, 72.0 + sep_bonus + min(6.0,(adx14-20)/3)), "CE", "TREND CONTINUATION"))
        if indicator_ok_pe and bearish_structure and trend == "BEARISH" and momentum == "DOWN" and price < ema20 and distance_from_ema20_pct <= 0.45 and adx14 >= MIN_ADX_B_GRADE:
            patterns.append((min(84.0, 72.0 + sep_bonus + min(6.0,(adx14-20)/3)), "PE", "TREND CONTINUATION"))

        # 6) Sustained strong-trend continuation for directional days.
        di_gap_ce = (plus_di14 or 0.0) - (minus_di14 or 0.0)
        di_gap_pe = (minus_di14 or 0.0) - (plus_di14 or 0.0)
        strong_ce = (
            trend == "BULLISH" and momentum == "UP"
            and price > ema20 > ema50
            and adx14 is not None and adx14 >= STRONG_TREND_MIN_ADX
            and di_gap_ce >= STRONG_TREND_MIN_DI_GAP
            and ema20_slope > 0 and ema50_slope >= 0
            and distance_from_ema20_pct <= STRONG_TREND_MAX_EMA20_DISTANCE_PCT
            and not bearish_structure
        )
        strong_pe = (
            trend == "BEARISH" and momentum == "DOWN"
            and price < ema20 < ema50
            and adx14 is not None and adx14 >= STRONG_TREND_MIN_ADX
            and di_gap_pe >= STRONG_TREND_MIN_DI_GAP
            and ema20_slope < 0 and ema50_slope <= 0
            and distance_from_ema20_pct <= STRONG_TREND_MAX_EMA20_DISTANCE_PCT
            and not bullish_structure
        )
        if strong_ce:
            patterns.append((
                min(96.0, 84.0 + sep_bonus + min(6.0, (adx14-30.0)/3.0)),
                "CE", "STRONG TREND CONTINUATION"
            ))
        if strong_pe:
            patterns.append((
                min(96.0, 84.0 + sep_bonus + min(6.0, (adx14-30.0)/3.0)),
                "PE", "STRONG TREND CONTINUATION"
            ))

        # 7) V3.7.1 LIQUIDITY / MARKET-STRUCTURE OPPORTUNITY LAYER
        # This layer NEVER rejects an existing setup. It can:
        #   a) add a small confirmation bonus to an existing same-direction setup, or
        #   b) create a new setup when a sweep/break/FVG retest is independently valid.
        liquidity_event = "NONE"
        liquidity_level = None
        fvg_event = "NONE"
        fvg_zone_low = None
        fvg_zone_high = None

        prior_liq = today_df.iloc[:-1].tail(LIQUIDITY_LOOKBACK_CANDLES)
        liq_buffer = max((atr14 or 0.0) * LIQUIDITY_SWEEP_ATR_BUFFER, price * 0.00015)
        bull_sweep = bear_sweep = bull_break = bear_break = False

        if len(prior_liq) >= 3:
            prior_liq_high = float(prior_liq["high"].max())
            prior_liq_low = float(prior_liq["low"].min())
            latest_high = float(latest["high"])
            latest_low = float(latest["low"])

            # Sell-side liquidity sweep then reclaim -> bullish/CE reversal opportunity.
            bull_sweep = (
                latest_low < prior_liq_low - liq_buffer
                and price > prior_liq_low
                and momentum == "UP"
                and adx14 is not None and adx14 >= LIQUIDITY_RECLAIM_MIN_ADX
                and plus_di14 is not None and minus_di14 is not None
                and plus_di14 >= minus_di14
            )
            # Buy-side liquidity sweep then rejection -> bearish/PE reversal opportunity.
            bear_sweep = (
                latest_high > prior_liq_high + liq_buffer
                and price < prior_liq_high
                and momentum == "DOWN"
                and adx14 is not None and adx14 >= LIQUIDITY_RECLAIM_MIN_ADX
                and plus_di14 is not None and minus_di14 is not None
                and minus_di14 >= plus_di14
            )

            # Fresh acceptance through a recent liquidity pool in the established trend.
            bull_break = (
                prev_price <= prior_liq_high and price > prior_liq_high + liq_buffer
                and trend == "BULLISH" and momentum == "UP"
                and adx14 is not None and adx14 >= LIQUIDITY_BREAK_MIN_ADX
                and plus_di14 is not None and minus_di14 is not None
                and plus_di14 > minus_di14
            )
            bear_break = (
                prev_price >= prior_liq_low and price < prior_liq_low - liq_buffer
                and trend == "BEARISH" and momentum == "DOWN"
                and adx14 is not None and adx14 >= LIQUIDITY_BREAK_MIN_ADX
                and plus_di14 is not None and minus_di14 is not None
                and minus_di14 > plus_di14
            )

            if bull_sweep:
                liquidity_event, liquidity_level = "SELL-SIDE SWEEP + RECLAIM", prior_liq_low
                patterns.append((82.0 + min(8.0, max(0.0, adx14-18.0)/2.5), "CE", "LIQUIDITY SWEEP REVERSAL"))
            elif bear_sweep:
                liquidity_event, liquidity_level = "BUY-SIDE SWEEP + REJECTION", prior_liq_high
                patterns.append((82.0 + min(8.0, max(0.0, adx14-18.0)/2.5), "PE", "LIQUIDITY SWEEP REVERSAL"))
            elif bull_break:
                liquidity_event, liquidity_level = "BUY-SIDE LIQUIDITY BREAK", prior_liq_high
                patterns.append((80.0 + min(8.0, max(0.0, adx14-21.0)/2.5), "CE", "LIQUIDITY BREAK CONTINUATION"))
            elif bear_break:
                liquidity_event, liquidity_level = "SELL-SIDE LIQUIDITY BREAK", prior_liq_low
                patterns.append((80.0 + min(8.0, max(0.0, adx14-21.0)/2.5), "PE", "LIQUIDITY BREAK CONTINUATION"))

        # Recent 3-candle Fair Value Gap / imbalance. FVG alone never creates a trade:
        # a retest must agree with the established EMA trend, ADX/DI and candle direction.
        recent = today_df.tail(FVG_MAX_AGE_CANDLES + 3).reset_index(drop=True)
        recent_fvgs = []
        if len(recent) >= 3 and atr14 is not None and atr14 > 0:
            min_gap = float(atr14) * FVG_MIN_SIZE_ATR
            for i in range(len(recent) - 2):
                c1 = recent.iloc[i]
                c3 = recent.iloc[i + 2]
                bull_lo, bull_hi = float(c1["high"]), float(c3["low"])
                bear_lo, bear_hi = float(c3["high"]), float(c1["low"])
                if bull_hi - bull_lo >= min_gap:
                    recent_fvgs.append(("BULLISH", bull_lo, bull_hi, i + 2))
                if bear_hi - bear_lo >= min_gap:
                    recent_fvgs.append(("BEARISH", bear_lo, bear_hi, i + 2))

        latest_low = float(latest["low"])
        latest_high = float(latest["high"])
        for side_fvg, zone_lo, zone_hi, formed_at in reversed(recent_fvgs):
            # Only use reasonably recent zones and require the current candle to touch them.
            age = (len(recent) - 1) - formed_at
            if age < 0 or age > FVG_MAX_AGE_CANDLES:
                continue
            touched = latest_low <= zone_hi and latest_high >= zone_lo
            if not touched:
                continue
            if (
                side_fvg == "BULLISH" and trend == "BULLISH" and momentum == "UP"
                and price > zone_hi and adx14 is not None and adx14 >= FVG_RETEST_MIN_ADX
                and plus_di14 is not None and minus_di14 is not None and plus_di14 > minus_di14
            ):
                fvg_event, fvg_zone_low, fvg_zone_high = "BULLISH FVG RETEST", zone_lo, zone_hi
                patterns.append((79.0 + min(8.0, max(0.0, adx14-21.0)/3.0), "CE", "FVG RETEST CONTINUATION"))
                break
            if (
                side_fvg == "BEARISH" and trend == "BEARISH" and momentum == "DOWN"
                and price < zone_lo and adx14 is not None and adx14 >= FVG_RETEST_MIN_ADX
                and plus_di14 is not None and minus_di14 is not None and minus_di14 > plus_di14
            ):
                fvg_event, fvg_zone_low, fvg_zone_high = "BEARISH FVG RETEST", zone_lo, zone_hi
                patterns.append((79.0 + min(8.0, max(0.0, adx14-21.0)/3.0), "PE", "FVG RETEST CONTINUATION"))
                break

        # V8.2/V8.3: advance independent experimental state machines. They do not
        # modify or confirm/reject any pre-existing strategy.
        sweep_ifvg_candidates = self._sweep_ifvg_candidate_locked(df, atr14)
        amd_poc_candidates = self._amd_poc_candidate_locked(df, atr14)

        # V8.0 ADDITIONAL RESEARCHED 5M STRATEGIES.
        # All use completed candles. They create independent candidates and still pass
        # the existing option-quality, premium-momentum, fundamental and risk gates.
        try:
            vol_now = max(0.0, safe_float(latest.get("volume"), 0.0) or 0.0)
            vol_hist = pd.to_numeric(today_df.iloc[:-1]["volume"], errors="coerce").dropna().tail(VOLUME_RVOL_LOOKBACK)
            vol_base = float(vol_hist.mean()) if len(vol_hist) >= 5 else 0.0
            rvol = (vol_now / vol_base) if vol_base > 0 else 0.0

            candle_range = max(1e-9, float(latest["high"]) - float(latest["low"]))
            candle_body = abs(float(latest["close"]) - float(latest["open"]))
            body_ratio = candle_body / candle_range
            upper_wick_ratio = (float(latest["high"]) - max(float(latest["open"]), float(latest["close"]))) / candle_range
            lower_wick_ratio = (min(float(latest["open"]), float(latest["close"])) - float(latest["low"])) / candle_range

            break_ref = today_df.iloc[:-1].tail(VOLUME_BREAK_LOOKBACK)
            break_high = float(break_ref["high"].max()) if not break_ref.empty else None
            break_low = float(break_ref["low"].min()) if not break_ref.empty else None

            # 9) High-volume momentum / RVOL breakout.
            if break_high is not None and rvol >= VOLUME_RVOL_MIN and body_ratio >= VOLUME_BODY_RATIO_MIN:
                if indicator_ok_ce and float(latest["close"]) > float(latest["open"]) and price > break_high and momentum == "UP":
                    score = min(97.0, 82.0 + min(8.0, (rvol - VOLUME_RVOL_MIN) * 6.0) + min(5.0, body_ratio * 5.0))
                    patterns.append((score, "CE", "HIGH VOLUME MOMENTUM"))
                if indicator_ok_pe and float(latest["close"]) < float(latest["open"]) and price < break_low and momentum == "DOWN":
                    score = min(97.0, 82.0 + min(8.0, (rvol - VOLUME_RVOL_MIN) * 6.0) + min(5.0, body_ratio * 5.0))
                    patterns.append((score, "PE", "HIGH VOLUME MOMENTUM"))

            # 10) High-volume breakout followed by a completed-candle retest.
            if len(today_df) >= VOLUME_BREAK_LOOKBACK + 3:
                prev = today_df.iloc[-2]
                pre_prev = today_df.iloc[:-2].tail(VOLUME_BREAK_LOOKBACK)
                if not pre_prev.empty:
                    ref_hi = float(pre_prev["high"].max())
                    ref_lo = float(pre_prev["low"].min())
                    prev_vol_hist = pd.to_numeric(today_df.iloc[:-2]["volume"], errors="coerce").dropna().tail(VOLUME_RVOL_LOOKBACK)
                    prev_vol_base = float(prev_vol_hist.mean()) if len(prev_vol_hist) >= 5 else 0.0
                    prev_rvol = (float(prev["volume"]) / prev_vol_base) if prev_vol_base > 0 else 0.0
                    tol = max((atr14 or 0.0) * 0.15, price * 0.0005)
                    if prev_rvol >= VOLUME_RVOL_MIN and float(prev["close"]) > ref_hi and float(latest["low"]) <= ref_hi + tol and price > ref_hi and momentum == "UP" and indicator_ok_ce:
                        patterns.append((88.0 + min(7.0, (prev_rvol - VOLUME_RVOL_MIN) * 4.0), "CE", "HIGH VOLUME BREAKOUT RETEST"))
                    if prev_rvol >= VOLUME_RVOL_MIN and float(prev["close"]) < ref_lo and float(latest["high"]) >= ref_lo - tol and price < ref_lo and momentum == "DOWN" and indicator_ok_pe:
                        patterns.append((88.0 + min(7.0, (prev_rvol - VOLUME_RVOL_MIN) * 4.0), "PE", "HIGH VOLUME BREAKOUT RETEST"))

            # 11) Volume exhaustion reversal: extreme participation + rejection wick.
            # Unlike momentum breakout, direction follows the rejection, not the volume bar colour alone.
            if rvol >= VOLUME_EXHAUST_RVOL_MIN and len(break_ref) >= 3:
                if float(latest["low"]) < float(break_ref["low"].min()) and lower_wick_ratio >= VOLUME_EXHAUST_WICK_RATIO_MIN and price > float(latest["low"]) + 0.55 * candle_range and plus_di14 is not None and minus_di14 is not None and plus_di14 >= minus_di14:
                    patterns.append((84.0 + min(8.0, (rvol - VOLUME_EXHAUST_RVOL_MIN) * 3.0), "CE", "VOLUME EXHAUSTION REVERSAL"))
                if float(latest["high"]) > float(break_ref["high"].max()) and upper_wick_ratio >= VOLUME_EXHAUST_WICK_RATIO_MIN and price < float(latest["high"]) - 0.55 * candle_range and plus_di14 is not None and minus_di14 is not None and minus_di14 >= plus_di14:
                    patterns.append((84.0 + min(8.0, (rvol - VOLUME_EXHAUST_RVOL_MIN) * 3.0), "PE", "VOLUME EXHAUSTION REVERSAL"))

            # 12) NR7 compression breakout. Previous completed candle must be the
            # narrowest of its seven-bar window; current candle supplies the breakout.
            if len(today_df) >= NR_LOOKBACK + 1:
                nr_window = today_df.iloc[-(NR_LOOKBACK + 1):-1].copy()
                nr_ranges = (nr_window["high"] - nr_window["low"]).astype(float)
                nr = nr_window.iloc[-1]
                nr_is_narrowest = float(nr_ranges.iloc[-1]) <= float(nr_ranges.min()) + 1e-9
                if nr_is_narrowest and rvol >= NR_BREAK_VOLUME_RVOL_MIN:
                    if price > float(nr["high"]) and momentum == "UP" and indicator_ok_ce:
                        patterns.append((86.0 + min(7.0, (rvol - 1.0) * 4.0), "CE", "NR7 COMPRESSION BREAKOUT"))
                    if price < float(nr["low"]) and momentum == "DOWN" and indicator_ok_pe:
                        patterns.append((86.0 + min(7.0, (rvol - 1.0) * 4.0), "PE", "NR7 COMPRESSION BREAKOUT"))

            # 13) Bollinger squeeze release + volume confirmation.
            if len(today_df) >= BB_LENGTH + BB_SQUEEZE_LOOKBACK + 1:
                closes = pd.to_numeric(today_df["close"], errors="coerce")
                mid = closes.rolling(BB_LENGTH).mean()
                std = closes.rolling(BB_LENGTH).std(ddof=0)
                upper = mid + BB_STD * std
                lower = mid - BB_STD * std
                width = (upper - lower) / mid.replace(0, float("nan"))
                prev_width = safe_float(width.iloc[-2])
                width_baseline = safe_float(width.iloc[-(BB_SQUEEZE_LOOKBACK + 2):-2].mean())
                squeeze_prev = prev_width is not None and width_baseline is not None and width_baseline > 0 and prev_width <= width_baseline * BB_SQUEEZE_RATIO
                if squeeze_prev and rvol >= NR_BREAK_VOLUME_RVOL_MIN:
                    if price > float(upper.iloc[-1]) and momentum == "UP" and plus_di14 is not None and minus_di14 is not None and plus_di14 > minus_di14:
                        patterns.append((88.0 + min(6.0, (rvol - 1.0) * 4.0), "CE", "BOLLINGER SQUEEZE BREAKOUT"))
                    if price < float(lower.iloc[-1]) and momentum == "DOWN" and plus_di14 is not None and minus_di14 is not None and minus_di14 > plus_di14:
                        patterns.append((88.0 + min(6.0, (rvol - 1.0) * 4.0), "PE", "BOLLINGER SQUEEZE BREAKOUT"))

            # 14) ADX/+DI/-DI expansion: fresh acceleration of an established trend.
            prev_adx = safe_float(previous.get("adx14"))
            prev_plus = safe_float(previous.get("plus_di14"))
            prev_minus = safe_float(previous.get("minus_di14"))
            if None not in (adx14, plus_di14, minus_di14, prev_adx, prev_plus, prev_minus):
                if adx14 >= MIN_ADX and adx14 - prev_adx >= ADX_EXPANSION_MIN_RISE:
                    if plus_di14 - minus_di14 >= DI_EXPANSION_MIN_GAP and plus_di14 > prev_plus and trend == "BULLISH" and momentum == "UP":
                        patterns.append((84.0 + min(8.0, adx14 - prev_adx), "CE", "ADX DI EXPANSION"))
                    if minus_di14 - plus_di14 >= DI_EXPANSION_MIN_GAP and minus_di14 > prev_minus and trend == "BEARISH" and momentum == "DOWN":
                        patterns.append((84.0 + min(8.0, adx14 - prev_adx), "PE", "ADX DI EXPANSION"))

            # 15) Inside-bar compression then volume-confirmed breakout.
            if len(today_df) >= 3:
                mother = today_df.iloc[-3]
                inside = today_df.iloc[-2]
                is_inside = float(inside["high"]) < float(mother["high"]) and float(inside["low"]) > float(mother["low"])
                if is_inside and rvol >= INSIDE_BAR_VOLUME_RVOL_MIN:
                    if price > float(mother["high"]) and momentum == "UP" and indicator_ok_ce:
                        patterns.append((86.0 + min(7.0, (rvol - 1.0) * 4.0), "CE", "INSIDE BAR VOLUME BREAKOUT"))
                    if price < float(mother["low"]) and momentum == "DOWN" and indicator_ok_pe:
                        patterns.append((86.0 + min(7.0, (rvol - 1.0) * 4.0), "PE", "INSIDE BAR VOLUME BREAKOUT"))

            # 16) EMA pullback with explicit ADX expansion confirmation.
            if prev_adx is not None and adx14 is not None and adx14 > prev_adx and adx14 >= MIN_ADX_B_GRADE:
                if bullish_pullback_touched and price > ema20 > ema50 and momentum == "UP" and plus_di14 is not None and minus_di14 is not None and plus_di14 > minus_di14:
                    patterns.append((87.0 + min(6.0, adx14 - prev_adx), "CE", "EMA ADX PULLBACK CONFIRMATION"))
                if bearish_pullback_touched and price < ema20 < ema50 and momentum == "DOWN" and plus_di14 is not None and minus_di14 is not None and minus_di14 > plus_di14:
                    patterns.append((87.0 + min(6.0, adx14 - prev_adx), "PE", "EMA ADX PULLBACK CONFIRMATION"))
        except Exception as exc:
            log.debug("V8 additional strategy calculation skipped: %s", short_reason(exc, 100))

        # 8) V3.8.0 WEAPON CANDLE 15M (independent strategy engine).
        # The 5m feed is resampled locally; only fully completed 15m bars (3 x 5m)
        # are used. The setup is an adapted, testable implementation built around
        # the published EMA9/MACD/RSI idea. Futures-VWAP confirmation remains a
        # separate common market-data check in the signal engine.
        weapon15_time = None
        weapon15_ema9 = None
        weapon15_macd = None
        weapon15_macd_signal = None
        weapon15_rsi14 = None
        try:
            d15_src = df[["time", "open", "high", "low", "close", "volume"]].copy()
            d15_src["bucket15"] = d15_src["time"].dt.floor("15min")
            d15 = (
                d15_src.groupby("bucket15", as_index=False)
                .agg(
                    open=("open", "first"), high=("high", "max"),
                    low=("low", "min"), close=("close", "last"),
                    volume=("volume", "sum"), bars=("close", "size"),
                )
            )
            d15 = d15[d15["bars"] >= 3].copy().sort_values("bucket15").reset_index(drop=True)
            if len(d15) >= 30:
                d15["ema9"] = d15["close"].ewm(span=9, adjust=False).mean()
                ema12 = d15["close"].ewm(span=12, adjust=False).mean()
                ema26 = d15["close"].ewm(span=26, adjust=False).mean()
                d15["macd"] = ema12 - ema26
                d15["macd_signal"] = d15["macd"].ewm(span=9, adjust=False).mean()
                delta15 = d15["close"].diff()
                gain15 = delta15.clip(lower=0.0)
                loss15 = (-delta15.clip(upper=0.0))
                avg_gain15 = gain15.ewm(alpha=1/14, adjust=False, min_periods=14).mean()
                avg_loss15 = loss15.ewm(alpha=1/14, adjust=False, min_periods=14).mean()
                rs15 = avg_gain15 / avg_loss15.replace(0, 1e-12)
                d15["rsi14"] = 100.0 - (100.0 / (1.0 + rs15))
                pc15 = d15["close"].shift(1)
                tr15 = pd.concat([
                    (d15["high"] - d15["low"]).abs(),
                    (d15["high"] - pc15).abs(),
                    (d15["low"] - pc15).abs(),
                ], axis=1).max(axis=1)
                d15["atr14"] = tr15.ewm(alpha=1/14, adjust=False, min_periods=14).mean()

                w = d15.iloc[-1]
                wp = d15.iloc[-2]
                weapon15_time = str(w["bucket15"])
                weapon15_ema9 = safe_float(w.get("ema9"))
                weapon15_macd = safe_float(w.get("macd"))
                weapon15_macd_signal = safe_float(w.get("macd_signal"))
                weapon15_rsi14 = safe_float(w.get("rsi14"))
                w_atr = safe_float(w.get("atr14"), 0.0) or 0.0
                w_body = abs(float(w["close"]) - float(w["open"]))
                body_ok = (w_atr <= 0) or (w_body >= WEAPON15_MIN_BODY_ATR * w_atr)

                bull_weapon = (
                    safe_float(wp.get("ema9")) is not None
                    and float(wp["close"]) <= float(wp["ema9"])
                    and float(w["close"]) > float(w["ema9"])
                    and float(w["close"]) > float(w["open"])
                    and float(w["macd"]) > float(w["macd_signal"])
                    and float(w["macd"]) >= float(wp["macd"])
                    and weapon15_rsi14 is not None
                    and WEAPON15_RSI_BULL_MIN <= weapon15_rsi14 <= WEAPON15_RSI_BULL_MAX
                    and body_ok
                )
                bear_weapon = (
                    safe_float(wp.get("ema9")) is not None
                    and float(wp["close"]) >= float(wp["ema9"])
                    and float(w["close"]) < float(w["ema9"])
                    and float(w["close"]) < float(w["open"])
                    and float(w["macd"]) < float(w["macd_signal"])
                    and float(w["macd"]) <= float(wp["macd"])
                    and weapon15_rsi14 is not None
                    and WEAPON15_RSI_BEAR_MIN <= weapon15_rsi14 <= WEAPON15_RSI_BEAR_MAX
                    and body_ok
                )
                if bull_weapon:
                    score = 82.0 + min(8.0, max(0.0, weapon15_rsi14 - 52.0) / 2.0)
                    patterns.append((min(94.0, score), "CE", "WEAPON CANDLE 15M"))
                if bear_weapon:
                    score = 82.0 + min(8.0, max(0.0, 48.0 - weapon15_rsi14) / 2.0)
                    patterns.append((min(94.0, score), "PE", "WEAPON CANDLE 15M"))
        except Exception as exc:
            log.debug("Weapon 15m calculation skipped: %s", short_reason(exc, 100))

        # V4.1 completed-5m candlestick sub-engine. Pattern recognition is
        # confirmation-only; it does not create a standalone strategy candidate.
        try:
            candlestick_state = self._detect_candlestick_patterns_locked(today_df, trend, atr14)
        except Exception as exc:
            log.debug("Candlestick pattern calculation skipped: %s", short_reason(exc, 100))
            candlestick_state = {
                "engine": CANDLE_PATTERN_ENGINE_VERSION, "patterns": [], "primary": "NONE",
                "primary_family": "NONE", "primary_direction": "NEUTRAL", "bias": "NEUTRAL",
                "bonus_ce": 0.0, "bonus_pe": 0.0,
                "best_bullish": "NONE", "best_bullish_family": "NONE",
                "best_bearish": "NONE", "best_bearish_family": "NONE",
                "conflict": False,
            }

        # Bonus only: liquidity/FVG/candlestick confirmation can strengthen existing setups.
        # It never subtracts points and never blocks another independent strategy.
        confirmed_direction = None
        if bull_sweep or bull_break:
            confirmed_direction = "CE"
        elif bear_sweep or bear_break:
            confirmed_direction = "PE"
        fvg_direction = "CE" if fvg_event.startswith("BULLISH") else ("PE" if fvg_event.startswith("BEARISH") else None)

        boosted = []
        for p_score, p_dir, p_name in patterns:
            bonus = 0.0
            if confirmed_direction == p_dir and not p_name.startswith("LIQUIDITY"):
                bonus += LIQUIDITY_CONFIRM_BONUS
            if fvg_direction == p_dir and p_name != "FVG RETEST CONTINUATION":
                bonus += FVG_CONFIRM_BONUS
            if p_dir == "CE":
                bonus += safe_float(candlestick_state.get("bonus_ce"), 0.0) or 0.0
            elif p_dir == "PE":
                bonus += safe_float(candlestick_state.get("bonus_pe"), 0.0) or 0.0
            boosted.append((min(100.0, p_score + bonus), p_dir, p_name))
        patterns = boosted

        patterns.sort(key=lambda x: x[0], reverse=True)
        bias = "WAIT"
        direction = None
        setup = "NONE"
        setup_grade = "NONE"
        tech_score = 0.0
        entry_ready = False
        entry_block_reason = ""
        latest_range = abs(float(latest["high"]) - float(latest["low"]))
        impulse_atr_mult = (
            latest_range / float(atr14)
            if atr14 is not None and float(atr14) > 0
            else 0.0
        )

        if trend == "BULLISH" and momentum == "UP":
            bias = "CE FAVOURED"
        elif trend == "BEARISH" and momentum == "DOWN":
            bias = "PE FAVOURED"

        # Keep every independently valid setup, not only the highest-scoring one.
        # The main engine can try these one by one. This is the key V3.8 learning-mode
        # change: ORB, EMA, liquidity, FVG, Weapon Candle, etc. do not have to agree.
        setup_candidates = []
        di_gap = abs((plus_di14 or 0) - (minus_di14 or 0))
        for p_score, p_dir, p_name in patterns[:MAX_TECH_STRATEGY_VARIANTS]:
            p_grade = "A" if p_score >= 82.0 else "B"
            p_grade_gate = True
            if p_grade == "B":
                p_grade_gate = bool(
                    adx14 is not None and adx14 >= MIN_ADX_B_GRADE
                    and di_gap >= MIN_DI_GAP_B_GRADE
                )
            p_ready = bool(p_score >= MIN_TECH_SCORE and p_grade_gate)
            p_block = ""
            if p_ready and impulse_atr_mult >= ANTI_CHASE_CANDLE_ATR_MULT:
                p_ready = False
                p_block = (
                    f"ANTI-CHASE: 5M IMPULSE {impulse_atr_mult:.2f} ATR >= "
                    f"{ANTI_CHASE_CANDLE_ATR_MULT:.2f}"
                )
            p_event_time = weapon15_time if p_name == "WEAPON CANDLE 15M" else str(latest["time"])
            setup_candidates.append({
                "setup": p_name,
                "direction": p_dir,
                "tech_score": round(float(p_score), 1),
                "setup_grade": p_grade,
                "entry_ready": p_ready,
                "entry_block_reason": p_block,
                "strategy_event_time": p_event_time,
                "candlestick_bonus": round(
                    float(candlestick_state.get("bonus_ce", 0.0) if p_dir == "CE" else candlestick_state.get("bonus_pe", 0.0)), 2
                ),
                "candlestick_primary": (
                    candlestick_state.get("best_bullish", "NONE") if p_dir == "CE"
                    else candlestick_state.get("best_bearish", "NONE")
                ),
                "candlestick_family": (
                    candlestick_state.get("best_bullish_family", "NONE") if p_dir == "CE"
                    else candlestick_state.get("best_bearish_family", "NONE")
                ),
                "candlestick_direction": (
                    "BULLISH" if p_dir == "CE" and candlestick_state.get("best_bullish", "NONE") != "NONE"
                    else "BEARISH" if p_dir == "PE" and candlestick_state.get("best_bearish", "NONE") != "NONE"
                    else "NEUTRAL"
                ),
                "candlestick_bias": candlestick_state.get("bias", "NEUTRAL"),
            })

        # Insert fully-confirmed experimental candidates without changing the
        # score/order relationship among any pre-existing strategy candidates.
        for exp in (sweep_ifvg_candidates + amd_poc_candidates):
            item = dict(exp)
            if item.get("entry_ready") and impulse_atr_mult >= ANTI_CHASE_CANDLE_ATR_MULT:
                item["entry_ready"] = False
                item["entry_block_reason"] = (
                    f"ANTI-CHASE: 5M IMPULSE {impulse_atr_mult:.2f} ATR >= "
                    f"{ANTI_CHASE_CANDLE_ATR_MULT:.2f}"
                )
            item.update({
                "candlestick_bonus": 0.0,
                "candlestick_primary": (
                    candlestick_state.get("best_bullish", "NONE") if item.get("direction") == "CE"
                    else candlestick_state.get("best_bearish", "NONE")
                ),
                "candlestick_family": (
                    candlestick_state.get("best_bullish_family", "NONE") if item.get("direction") == "CE"
                    else candlestick_state.get("best_bearish_family", "NONE")
                ),
                "candlestick_direction": "NEUTRAL",
                "candlestick_bias": candlestick_state.get("bias", "NEUTRAL"),
            })
            pos = next((i for i,x in enumerate(setup_candidates) if safe_float(x.get("tech_score"),0.0) < safe_float(item.get("tech_score"),0.0)), len(setup_candidates))
            setup_candidates.insert(pos, item)
        setup_candidates = setup_candidates[:MAX_TECH_STRATEGY_VARIANTS]

        if setup_candidates:
            top = setup_candidates[0]
            tech_score = float(top["tech_score"])
            direction = top["direction"]
            setup = top["setup"]
            setup_grade = top["setup_grade"]
            entry_ready = bool(top["entry_ready"])
            entry_block_reason = str(top.get("entry_block_reason") or "")
            bias = f"{direction} FAVOURED"

        self.snapshot = {
            "ok": True,
            "candle_time": str(latest["time"]),
            "price": price,
            "ema20": ema20,
            "ema50": ema50,
            "ema20_slope": round(ema20_slope, 4),
            "ema50_slope": round(ema50_slope, 4),
            "atr14": round(float(atr14), 4) if atr14 is not None else None,
            "adx14": round(float(adx14), 2) if adx14 is not None else None,
            "plus_di14": round(float(plus_di14), 2) if plus_di14 is not None else None,
            "minus_di14": round(float(minus_di14), 2) if minus_di14 is not None else None,
            "day_high": day_high,
            "day_low": day_low,
            "or_high": or_high,
            "or_low": or_low,
            "trend": trend,
            "momentum": momentum,
            "structure": structure,
            "or_status": or_status,
            "bias": bias,
            "entry_ready": entry_ready,
            "entry_block_reason": entry_block_reason,
            "impulse_atr_mult": round(float(impulse_atr_mult), 2),
            "distance_from_ema20_pct": round(float(distance_from_ema20_pct), 3),
            "direction": direction,
            "setup": setup,
            "setup_grade": setup_grade,
            "tech_score": round(float(tech_score), 1),
            "setup_candidates": setup_candidates,
            "strategy_event_time": (setup_candidates[0].get("strategy_event_time") if setup_candidates else str(latest["time"])),
            "candlestick_engine": candlestick_state.get("engine", CANDLE_PATTERN_ENGINE_VERSION),
            "candlestick_primary": candlestick_state.get("primary", "NONE"),
            "candlestick_family": candlestick_state.get("primary_family", "NONE"),
            "candlestick_direction": candlestick_state.get("primary_direction", "NEUTRAL"),
            "candlestick_bias": candlestick_state.get("bias", "NEUTRAL"),
            "candlestick_patterns": candlestick_state.get("patterns", []),
            "candlestick_bonus_ce": round(float(candlestick_state.get("bonus_ce", 0.0) or 0.0), 2),
            "candlestick_bonus_pe": round(float(candlestick_state.get("bonus_pe", 0.0) or 0.0), 2),
            "candlestick_conflict": bool(candlestick_state.get("conflict", False)),
            "weapon15_time": weapon15_time,
            "weapon15_ema9": round(float(weapon15_ema9), 2) if weapon15_ema9 is not None else None,
            "weapon15_macd": round(float(weapon15_macd), 4) if weapon15_macd is not None else None,
            "weapon15_macd_signal": round(float(weapon15_macd_signal), 4) if weapon15_macd_signal is not None else None,
            "weapon15_rsi14": round(float(weapon15_rsi14), 2) if weapon15_rsi14 is not None else None,
            "liquidity_event": liquidity_event,
            "liquidity_level": round(float(liquidity_level), 2) if liquidity_level is not None else None,
            "fvg_event": fvg_event,
            "fvg_zone_low": round(float(fvg_zone_low), 2) if fvg_zone_low is not None else None,
            "fvg_zone_high": round(float(fvg_zone_high), 2) if fvg_zone_high is not None else None,
            "source": self.seed_source or "LOCAL CACHE + ANGEL WEBSOCKET",
            "cache_rows": len(df),
            "error": None,
        }
    def get_snapshot(self):
        with self.lock:
            self._compute_snapshot_locked()
            return dict(self.snapshot)


# ============================================================================
# INDEX V3.4 ENGINE
# ============================================================================

# V7.5 broker boundary: data/authentication only. No order execution endpoints.
# Protocol references: https://dhanhq.co/docs/v2/{authentication,instruments,
# market-quote,historical-data,option-chain,live-market-feed,annexure}/
DHAN_MASTER_URL = 'https://images.dhan.co/api-data/api-scrip-master-detailed.csv'
DHAN_SEGMENTS = {0: 'IDX_I', 2: 'NSE_FNO', 8: 'BSE_FNO'}


def _broker_text(value):
    if BROKER_SELECTED != 'DHAN':
        return value
    if isinstance(value, str):
        return value.replace('ANGEL', 'DHAN').replace('Angel', 'Dhan')
    if isinstance(value, list):
        return [_broker_text(x) for x in value]
    if isinstance(value, dict):
        return {k: (v if k in ('notifications_text', 'signals_text') else _broker_text(v)) for k, v in value.items()}
    return value


def _assert_broker_selection():
    if _selection_at_import() != BROKER_SELECTED:
        raise RuntimeError('Broker selection changed: STOP ENGINE BEFORE CHANGING BROKER')


def _dhan_status(logged, message='', data_api_status=''):
    selection_path = Path(os.environ.get('VIJU_BROKER_SELECTION_FILE') or PROJECT_DIR / 'broker_selection.json')
    selection = json.loads(selection_path.read_text()) if selection_path.exists() else {'broker_selected': BROKER_SELECTED}
    if selection.get('broker_selected') != BROKER_SELECTED:
        raise RuntimeError('Broker selection changed while engine running')
    selection.update(login_status='LOGGED IN' if logged else 'LOGGED OUT',
                     message=message, data_api_status=data_api_status, updated_at=time.time())
    atomic_json_write(PROJECT_DIR / 'broker_status.json', selection)


class DhanDataError(RuntimeError):
    def __init__(self, message, auth=False):
        super().__init__(message)
        self.auth = auth


class DhanDataClient:
    """Translate Dhan read-only data into the existing engine's data contract.

    Internal tokens include segment + security ID to avoid cross-exchange collisions.
    Prices are rupees in REST/history; websocket values are paise for legacy consumers.
    """
    def __init__(self, engine):
        self.engine = engine
        self.client_id = os.environ.get('DHAN_CLIENT_ID', '')
        self.token = ''
        self.auth_lock = threading.RLock()
        self.locks = {x: threading.Lock() for x in ('quote', 'history', 'chain')}
        self.last_call = {x: 0.0 for x in self.locks}
        self.blocked_until = {x: 0.0 for x in self.locks}
        self.auth_failed = False
        self.data_status = 'NOT CHECKED'

    def _wait(self, seconds):
        if self.engine.stop_event.wait(max(0, seconds)) or _android_host_stop_requested():
            raise DhanDataError('Engine stopped')

    @staticmethod
    def token_for(segment, security_id):
        return 'DHAN:' + segment + ':' + str(int(security_id))

    @staticmethod
    def split_token(token):
        parts = str(token).split(':')
        if len(parts) != 3 or parts[0] != 'DHAN' or parts[1] not in DHAN_SEGMENTS.values():
            raise DhanDataError('Invalid Dhan instrument token; no Angel token fallback allowed')
        return parts[1], str(int(parts[2]))

    @staticmethod
    def normalize_master(text):
        import io
        rows = []
        reader = csv.DictReader(io.StringIO(text.lstrip('\ufeff')))
        required = {'EXCH_ID', 'SEGMENT', 'SECURITY_ID', 'INSTRUMENT', 'SYMBOL_NAME'}
        if not required.issubset(reader.fieldnames or []):
            raise DhanDataError('Dhan detailed master has an unsupported schema')
        for raw in reader:
            exchange = raw.get('EXCH_ID', '').strip().upper()
            instrument = raw.get('INSTRUMENT', '').strip().upper()
            segment = raw.get('SEGMENT', '').strip().upper()
            if exchange not in ('NSE', 'BSE') or instrument not in ('INDEX', 'FUTIDX', 'OPTIDX'):
                continue
            if instrument == 'INDEX':
                dhan_segment, legacy_exchange = 'IDX_I', exchange
                name = raw.get('SYMBOL_NAME', '').strip()
                symbol, expiry, strike, lot = name, '', 0, 1
                legacy_instrument = 'AMXIDX'
            else:
                if segment != 'D':
                    continue
                dhan_segment = 'NSE_FNO' if exchange == 'NSE' else 'BSE_FNO'
                legacy_exchange = 'NFO' if exchange == 'NSE' else 'BFO'
                name = (raw.get('UNDERLYING_SYMBOL') or raw.get('SYMBOL_NAME') or '').strip().upper()
                if name not in SUPPORTED_NSE_INDEX_ROOTS + SUPPORTED_BSE_INDEX_ROOTS:
                    continue
                expiry_dt = pd.to_datetime(raw.get('SM_EXPIRY_DATE'), errors='coerce')
                if pd.isna(expiry_dt):
                    continue
                expiry = expiry_dt.strftime('%d%b%Y').upper()
                lot = safe_int(raw.get('LOT_SIZE'), 0)
                if lot <= 0:
                    continue
                side = raw.get('OPTION_TYPE', '').strip().upper()
                strike_rupees = safe_float(raw.get('STRIKE_PRICE'), None)
                if instrument == 'OPTIDX' and (side not in ('CE', 'PE') or strike_rupees is None or strike_rupees <= 0):
                    continue
                strike = (strike_rupees or 0) * 100.0
                # Same canonical contract symbol across brokers; never use Dhan DISPLAY_NAME
                # for CE/PE suffix detection in the strategy engine.
                symbol = name + expiry + (f'{strike_rupees:g}' + side if instrument == 'OPTIDX' else 'FUT')
                legacy_instrument = instrument
            try:
                token = DhanDataClient.token_for(dhan_segment, raw['SECURITY_ID'])
            except (ValueError, TypeError):
                continue
            rows.append(dict(name=name, symbol=symbol, expiry=expiry, strike=strike,
                             lotsize=lot, token=token, exch_seg=legacy_exchange,
                             instrumenttype=legacy_instrument, dhan_segment=dhan_segment,
                             security_id=str(int(raw['SECURITY_ID'])), dhan_instrument=instrument))
        if not rows or not any(x['instrumenttype'] == 'OPTIDX' for x in rows):
            raise DhanDataError('Dhan master contains no supported index options')
        return pd.DataFrame(rows).drop_duplicates(subset=['token'])

    def load_master(self):
        path = PROJECT_DIR / 'dhan_scrip_master_detailed.csv'
        fresh = path.exists() and datetime.fromtimestamp(path.stat().st_mtime, IST).date() == now_ist().date()
        if fresh:
            try:
                return self.normalize_master(path.read_text(encoding='utf-8'))
            except Exception:
                pass
        _assert_broker_selection()
        try:
            response = requests.get(DHAN_MASTER_URL, timeout=(15, 120))
            if response.status_code != 200:
                raise DhanDataError('Dhan instrument master HTTP ' + str(response.status_code))
            result = self.normalize_master(response.text)
        except DhanDataError:
            raise
        except Exception:
            raise DhanDataError('Dhan instrument master download failed; retry when online') from None
        tmp = path.with_suffix('.installing')
        tmp.write_text(response.text, encoding='utf-8'); os.replace(tmp, path)
        return result

    def _auth_request(self, token):
        try:
            r = requests.get('https://api.dhan.co/v2/profile',
                             headers={'access-token': token, 'client-id': self.client_id}, timeout=(10, 20))
            if r.status_code in (401, 403):
                raise DhanDataError('Dhan session expired or rejected', auth=True)
            if r.status_code != 200:
                raise DhanDataError('Dhan profile HTTP ' + str(r.status_code))
            p = r.json()
            if not isinstance(p, dict) or not p or p.get('status') == 'failure':
                raise DhanDataError('Dhan profile rejected session', auth=True)
            if p.get('dhanClientId') and str(p['dhanClientId']) != self.client_id:
                raise DhanDataError('Dhan session client ID does not match credentials', auth=True)
            return p
        except DhanDataError:
            raise
        except Exception:
            raise DhanDataError('Dhan profile connection/response failed') from None

    def login(self, force=False):
        with self.auth_lock:
            _assert_broker_selection()
            if not self.client_id:
                raise DhanDataError('DHAN_CLIENT_ID is missing')
            session_path = PROJECT_DIR / 'dhan_session.json'
            candidates = []
            if self.token and not self.auth_failed:
                candidates.append(self.token)
            if session_path.exists() and not force:
                try:
                    old = json.loads(session_path.read_text())
                    if str(old.get('dhanClientId', '')) == self.client_id:
                        candidates.append(str(old.get('accessToken') or ''))
                except Exception:
                    pass
            # Do not repeatedly retry the rejected token during recovery.
            if not force:
                candidates.append(os.environ.get('DHAN_ACCESS_TOKEN', ''))
            profile = None
            for token in dict.fromkeys(x for x in candidates if x):
                try:
                    profile = self._auth_request(token)
                    self.token = token
                    break
                except DhanDataError as exc:
                    if not exc.auth:
                        raise
            if profile is None:
                pin = os.environ.get('DHAN_PIN', '')
                secret = os.environ.get('DHAN_TOTP_SECRET', '')
                if not pin or not secret:
                    raise DhanDataError('Dhan session unavailable/expired. Import a current session, or provide DHAN_PIN + DHAN_TOTP_SECRET', auth=True)
                try:
                    otp = pyotp.TOTP(secret).now()
                    r = requests.post('https://auth.dhan.co/app/generateAccessToken',
                        params={'dhanClientId': self.client_id, 'pin': pin, 'totp': otp}, timeout=(10, 20))
                    if r.status_code != 200:
                        raise DhanDataError('Dhan TOTP login HTTP ' + str(r.status_code), auth=True)
                    session = r.json()
                    token = str(session.get('accessToken') or '')
                    if not token:
                        raise DhanDataError('Dhan login returned no access token', auth=True)
                    if session.get('dhanClientId') and str(session['dhanClientId']) != self.client_id:
                        raise DhanDataError('Dhan generated session client mismatch', auth=True)
                except DhanDataError:
                    raise
                except Exception:
                    # requests exceptions can include PIN/TOTP query strings: never relay them.
                    raise DhanDataError('Dhan TOTP login failed; check credentials and phone clock', auth=True) from None
                profile = self._auth_request(token)
                self.token = token
                payload = {'dhanClientId': self.client_id, 'accessToken': token,
                           'expiryTime': session.get('expiryTime', '')}
                import tempfile
                fd, temp = tempfile.mkstemp(dir=PROJECT_DIR, prefix='dhan_session.')
                try:
                    with os.fdopen(fd, 'w') as f: json.dump(payload, f)
                    os.chmod(temp, 0o600); os.replace(temp, session_path)
                finally:
                    if os.path.exists(temp): os.unlink(temp)
            self.auth_failed = False
            self.engine.auth_token = self.token
            self.engine.feed_token = self.token  # Legacy lifecycle only; Dhan has one token.
            self.engine._set_angel_login_state(True, 'Dhan profile/session verified', notify=False)
            _dhan_status(True, 'Dhan session verified', self.data_status)
            return True

    def _request(self, endpoint, payload, lane):
        _assert_broker_selection()
        if not self.token:
            raise DhanDataError('Dhan is logged out', auth=True)
        with self.locks[lane]:
            gap = 3.1 if lane == 'chain' else 1.1
            self._wait(max(self.last_call[lane] + gap, self.blocked_until[lane]) - time.monotonic())
            self.last_call[lane] = time.monotonic()
            try:
                r = requests.post('https://api.dhan.co/v2/' + endpoint,
                    headers={'access-token': self.token, 'client-id': self.client_id,
                             'Content-Type': 'application/json', 'Accept': 'application/json'},
                    json=payload, timeout=(10, 25))
                try: data = r.json()
                except Exception: raise DhanDataError('Dhan returned an invalid data response') from None
                error = data.get('errorCode') or data.get('error_code') or ''
                if r.status_code == 401 or str(error) in ('901', '807', '808', '809'):
                    self.auth_failed = True
                    self.engine._set_angel_login_state(False, 'Dhan session expired/rejected', notify=False)
                    raise DhanDataError('Dhan session expired/rejected', auth=True)
                if r.status_code == 429 or str(error) == '805':
                    self.blocked_until[lane] = time.monotonic() + 10
                    raise DhanDataError('Dhan rate limit; backing off')
                if r.status_code != 200 or data.get('status') in ('failure', 'failed') or error:
                    self.data_status = 'NOT READY'
                    _dhan_status(not self.auth_failed, 'Dhan data unavailable: check session/data API access', self.data_status)
                    raise DhanDataError('Dhan data API HTTP ' + str(r.status_code) + (' error ' + str(error) if error else ''))
                self.data_status = 'AVAILABLE'
                _dhan_status(not self.auth_failed, 'Dhan market data received', self.data_status)
                return data
            except DhanDataError:
                raise
            except Exception:
                self.data_status = 'NOT READY'
                _dhan_status(not self.auth_failed, 'Dhan data connection failed', self.data_status)
                raise DhanDataError('Dhan data connection/response failed') from None

    def getMarketData(self, mode, exchange_tokens):
        grouped, requested = {}, {}
        for exchange, tokens in exchange_tokens.items():
            for token in tokens:
                segment, sid = self.split_token(token)
                grouped.setdefault(segment, []).append(int(sid))
                requested[(segment, sid)] = str(token)
        data = self._request('marketfeed/' + ('ltp' if mode == 'LTP' else 'quote'), grouped, 'quote')
        fetched = []
        for segment, values in (data.get('data') or {}).items():
            for sid, quote in values.items():
                token = requested.get((segment, str(sid)))
                if token is None or not isinstance(quote, dict) or safe_float(quote.get('last_price'), 0) <= 0:
                    continue
                trade_time = quote.get('last_trade_time')
                if isinstance(trade_time, str):
                    try: trade_time = datetime.strptime(trade_time, '%d/%m/%Y %H:%M:%S').replace(tzinfo=IST).isoformat()
                    except ValueError: pass
                fetched.append({'symbolToken': token, 'ltp': quote['last_price'],
                    'exchTradeTime': trade_time, 'depth': quote.get('depth') or {},
                    'tradeVolume': quote.get('volume'), 'opnInterest': quote.get('oi'),
                    'totBuyQuan': quote.get('buy_quantity'), 'totSellQuan': quote.get('sell_quantity'),
                    **{k: v for k, v in (quote.get('ohlc') or {}).items()}})
        return {'status': bool(fetched), 'data': {'fetched': fetched}}

    def getCandleData(self, params):
        segment, sid = self.split_token(params['symboltoken'])
        matches = self.engine.instrument_df[self.engine.instrument_df['token'] == params['symboltoken']]
        if matches.empty: raise DhanDataError('Dhan history instrument not found in master')
        if params['interval'] != 'FIVE_MINUTE': raise DhanDataError('Unsupported candle interval')
        payload = {'securityId': sid, 'exchangeSegment': segment,
                   'instrument': matches.iloc[0]['dhan_instrument'], 'interval': '5', 'oi': False,
                   'fromDate': str(params['fromdate']) + (':00' if len(str(params['fromdate'])) == 16 else ''),
                   'toDate': str(params['todate']) + (':00' if len(str(params['todate'])) == 16 else '')}
        data = self._request('charts/intraday', payload, 'history')
        columns = [data.get(k) for k in ('timestamp', 'open', 'high', 'low', 'close', 'volume')]
        if any(not isinstance(x, list) for x in columns) or len({len(x) for x in columns}) != 1:
            raise DhanDataError('Dhan historical candle columns missing/misaligned')
        rows = []
        for timestamp, op, hi, lo, cl, vol in zip(*columns):
            values = [float(v) for v in (op, hi, lo, cl, vol)]
            if not all(math.isfinite(v) for v in values) or min(values[:4]) <= 0 or values[4] < 0:
                continue
            rows.append([datetime.fromtimestamp(float(timestamp), IST).isoformat(), *values])
        return {'status': bool(rows), 'data': sorted(rows, key=lambda r: r[0])}

    def optionGreek(self, params):
        segment, sid = self.split_token(self.engine.spot_token)
        expiry = datetime.strptime(params['expirydate'], '%d%b%Y').strftime('%Y-%m-%d')
        data = self._request('optionchain', {'UnderlyingScrip': int(sid), 'UnderlyingSeg': segment, 'Expiry': expiry}, 'chain')
        rows = []
        for strike, sides in ((data.get('data') or {}).get('oc') or {}).items():
            for side in ('ce', 'pe'):
                option = sides.get(side) or {}; greeks = option.get('greeks') or {}
                if not greeks: continue
                # Guard contract identity, not just strike, before using a broker Greek.
                contract = self.engine.contracts.get((int(float(strike)), side.upper()))
                if contract and str(option.get('security_id')) != self.split_token(contract['token'])[1]:
                    continue
                rows.append({'strikePrice': strike, 'optionType': side.upper(),
                             **{k: greeks.get(k) for k in ('delta','gamma','theta','vega')},
                             'impliedVolatility': option.get('implied_volatility'), 'tradeVolume': option.get('volume')})
        return {'status': bool(rows), 'data': rows}


class DhanFeed:
    """Dhan binary full feed, normalized for the unchanged tick/strategy consumers."""
    def __init__(self, client):
        self.client = client
        self.ws = None
        self.closed = threading.Event()
        self.send_lock = threading.Lock()
        self.on_open = self.on_data = self.on_error = self.on_close = lambda *a: None

    @staticmethod
    def decode(message):
        import struct
        output = []
        offset = 0
        while offset < len(message):
            if len(message) - offset < 8: raise DhanDataError('Truncated Dhan feed header')
            code, size, segment_id, sid = struct.unpack_from('<BHBI', message, offset)
            if size < 8 or offset + size > len(message): raise DhanDataError('Invalid Dhan feed length')
            b = message[offset:offset+size]; offset += size
            if code == 50:
                reason = struct.unpack_from('<H', b, 8)[0] if size >= 10 else 0
                raise DhanDataError('Dhan feed disconnected, code ' + str(reason), auth=reason in (807,808,809))
            segment = DHAN_SEGMENTS.get(segment_id)
            if segment is None or code not in (2, 4, 8): continue
            minimum = {2:16,4:50,8:162}[code]
            if size < minimum: raise DhanDataError('Truncated Dhan price packet')
            ltp = struct.unpack_from('<f', b, 8)[0]
            if not math.isfinite(ltp) or ltp <= 0: continue
            row = {'token': DhanDataClient.token_for(segment, sid), 'last_traded_price': ltp * 100.0}
            if code in (4, 8):
                row.update(volume_trade_for_the_day=struct.unpack_from('<I', b, 22)[0],
                           total_sell_quantity=struct.unpack_from('<I', b, 26)[0],
                           total_buy_quantity=struct.unpack_from('<I', b, 30)[0])
            if code == 8:
                row['open_interest'] = struct.unpack_from('<I', b, 34)[0]
                row['best_5_buy_data'], row['best_5_sell_data'] = [], []
                for i in range(5):
                    bq, aq, bo, ao, bp, ap = struct.unpack_from('<IIHHff', b, 62+i*20)
                    row['best_5_buy_data'].append({'flag':1,'price':bp*100,'quantity':bq,'no of orders':bo})
                    row['best_5_sell_data'].append({'flag':0,'price':ap*100,'quantity':aq,'no of orders':ao})
            # Futures/options require full depth/volume packets; never replace with a ticker.
            if segment == 'IDX_I' or code == 8:
                output.append(row)
        return output

    def subscribe(self, correlation, mode, token_list):
        _assert_broker_selection()
        if self.closed.is_set(): raise DhanDataError('Dhan feed is stopped')
        items = []
        for group in token_list:
            for token in group['tokens']:
                segment, sid = DhanDataClient.split_token(token)
                items.append({'ExchangeSegment': segment, 'SecurityId': sid})
        with self.send_lock:
            for i in range(0, len(items), 100):
                batch = items[i:i+100]
                self.ws.send(json.dumps({'RequestCode':15 if mode==1 else 21,
                    'InstrumentCount':len(batch),'InstrumentList':batch}))

    def connect(self):
        import websocket
        from urllib.parse import urlencode
        if self.closed.is_set(): return
        _assert_broker_selection()
        url = 'wss://api-feed.dhan.co?' + urlencode({'version':'2', 'token':self.client.token,
                                                   'clientId':self.client.client_id, 'authType':'2'})
        def opened(ws):
            if self.closed.is_set(): ws.close(); return
            self.on_open(ws)
        def message(ws, raw):
            if self.closed.is_set() or not isinstance(raw, (bytes, bytearray)): return
            try:
                for row in self.decode(raw): self.on_data(ws, row)
            except DhanDataError as exc:
                if exc.auth:
                    self.client.auth_failed = True
                    self.client.engine._set_angel_login_state(False, 'Dhan feed session rejected', notify=False)
                self.on_error(ws, str(exc)); ws.close()
        def failed(ws, error):
            # websocket exceptions may contain the URL with the access token.
            self.on_error(ws, 'Dhan WebSocket connection failed')
        self.ws = websocket.WebSocketApp(url, on_open=opened, on_message=message,
            on_error=failed, on_close=lambda ws,*a:self.on_close(ws))
        if self.closed.is_set(): self.ws.close(); return
        try: self.ws.run_forever(ping_interval=0)
        except Exception: failed(self.ws, None)

    def close_connection(self):
        self.closed.set()
        if self.ws is not None:
            self.ws.close()


class IndexSignalEngineV31:
    def __init__(self, totp):
        self.totp = str(totp).strip()
        _assert_broker_selection()
        if BROKER_SELECTED == "ANGEL":
            global SmartConnect, SmartWebSocketV2
            from SmartApi import SmartConnect
            from SmartApi.smartWebSocketV2 import SmartWebSocketV2
            self.api_key, self.client_code, self.pin = load_angel_credentials()
        else:
            self.api_key = os.environ.get("DHAN_API_KEY", "")
            self.client_code = os.environ.get("DHAN_CLIENT_ID", "")
            self.pin = os.environ.get("DHAN_PIN", "")
        self.dhan_client = DhanDataClient(self) if BROKER_SELECTED == "DHAN" else None
        self.openai = OpenAI(timeout=90, max_retries=0)

        self.state_lock = threading.RLock()
        self.rest_lock = threading.Lock()
        self.rest_last_call = 0.0
        self.historical_rest_lock = threading.Lock()
        self.historical_rest_last_call = 0.0
        self.historical_rate_limit_count = 0
        self.historical_block_until = 0.0
        self.stop_event = threading.Event()

        self.smart = None
        self.sws = None
        self.auth_token = None
        self.feed_token = None
        # Persistent UI-facing Angel session state. App refresh/background must not
        # make the UI look logged out while this Python engine is still authenticated.
        self.angel_logged_in = False

        self.instrument_df = None
        self.index_candidates = []
        self.index_root = None
        self.index_display_name = None
        self.spot_token = None
        self.spot_exchange = "NSE"
        self.derivative_exchange = "NFO"
        self.spot_exchange_type = NSE_INDEX_EXCHANGE_TYPE
        self.derivative_exchange_type = NFO_EXCHANGE_TYPE
        self.nifty_options_df = None
        self.nearest_expiry = None
        self.available_strikes = []
        self.current_atm = None
        self.wanted_strikes = []
        self.contracts = {}
        self.token_contract = {}
        self.subscribed_option_tokens = set()

        self.futures_token = None
        self.futures_symbol = None
        self.futures_expiry = None
        self.futures_ltp = 0.0
        self.futures_vwap = None
        self.futures_pv = 0.0
        self.futures_volume = 0.0
        self.futures_last_cum_volume = None
        self.futures_last_tick_ts = 0.0
        self.futures_vwap_source = "NOT READY"
        # V3.8.0 real-time VWAP reclaim/rejection event detector.
        self.last_futures_vwap_relation = None
        self.last_futures_vwap_event_ts = 0.0

        self.nifty_live = 0.0
        self.last_nifty_tick_ts = 0.0
        self.latest_options = {}
        self.price_history = {}

        self.technical = None
        self.technical_state = {
            "ok": False, "entry_ready": False, "direction": None, "setup": "NONE",
            "setup_grade": "NONE", "tech_score": 0.0, "error": "Index not selected"
        }
        self.technical_last_update = 0.0

        self.fundamental_state = {
            "running": False, "filter": "WAIT", "market_bias": "UNKNOWN",
            "news_risk": "UNKNOWN", "confidence": 0, "risk_gate": "OPEN",
            "direction_score": 0, "hard_block_reason": "", "text": "",
            "ce_probability": 0, "pe_probability": 0, "sideways_probability": 100,
            "last_update": 0.0, "last_attempt": 0.0, "error": None,
        }
        # Preserve the latest verified news scan across Android engine restarts/off-market cycles.
        try:
            if FUNDAMENTAL_CACHE_FILE.exists():
                cached_fund = json.loads(FUNDAMENTAL_CACHE_FILE.read_text(encoding="utf-8"))
                if isinstance(cached_fund, dict):
                    for k in list(self.fundamental_state):
                        if k in cached_fund and k != "running":
                            self.fundamental_state[k] = cached_fund[k]
        except Exception as exc:
            log.debug("Fundamental cache load skipped: %s", short_reason(exc, 80))
        self.greeks_state = {"running": False, "data": {}, "last_update": 0.0, "error": None}
        self.final_review_state = {
            "running": False, "last_signature": None, "decision": "NONE",
            "confidence": 0, "reason": "", "error": None,
            "wait_retries": 0, "next_retry_ts": 0.0, "last_review_ts": 0.0,
        }

        self.active_transits = {}  # signal_no -> live TRANSIT dict
        self.silent_monitors = {}  # signal_no -> accepted/closed signal still watched to original T/SL
        self.signal_history = []
        self.signal_counter = 0
        # V3.8 re-arm: one signal max per exact strategy event. Keep a set rather
        # than only the last signature so two different strategies cannot alternate
        # and accidentally re-issue an older setup from the same candle.
        self.last_issued_setup_signature = None
        self.issued_setup_signatures = set()
        self.last_health_alert = {}
        self.last_heartbeat = 0.0
        self.cutoff_message_sent = False
        self.guardian_running_signals = set()
        self.signal_events_sent = set()

        # V3.6 explicit runtime phase state.
        # LOGIN/CLOSED phases never emit health-warning notifications.
        # LIVE warnings are armed only after the relevant startup grace period.
        self.runtime_phase = "LOGIN"
        self.phase_started_ts = time.time()
        self.live_confirmed_ts = 0.0
        self.health_enabled_after = float("inf")
        self.greeks_check_started_ts = 0.0
        self.greeks_grace_deadline = 0.0
        self.live_candle_bootstrap_error = None

        # V3.6.2 live-feed health/recovery state.  These fields are Python-owned,
        # so future recovery tuning remains a .py-only update.
        self.ws_lock = threading.RLock()
        self.websocket_state = "CONNECTING"
        self.websocket_generation = 0
        self.websocket_connected = False
        self.websocket_healthy_ticks = 0
        self.websocket_recovery_running = False
        self.websocket_recovery_started_ts = 0.0
        self.websocket_last_recovery_end_ts = 0.0
        self.websocket_last_reason = "STARTUP"
        self.websocket_last_rest_probe_ts = 0.0
        self.websocket_last_rest_probe_price = None
        self.websocket_last_rest_probe_ok = False
        self.websocket_option_tokens = set()
        self.websocket_reconnect_attempts = 0

        # V3.6.3 manual data-refresh bridge. The Android menu writes a tiny
        # request file in the app-private NiftyMonitor directory; the Python
        # engine consumes it without restarting the monitor or disturbing an
        # active TRANSIT.
        self.manual_refresh_lock = threading.RLock()
        self.manual_refresh_running = False
        self.manual_refresh_last_ts = 0.0
        self.manual_refresh_last_result = "NEVER"

        # V3.7.0 diagnostic/rejected-setup research state.
        self.last_data_health_log_ts = 0.0
        self.last_data_health_signature = None

        # V3.7.0 API/source diagnostics. These are intentionally NOT shown on
        # the Android live screen. They are written to index_v31_runtime.log,
        # which is already included in the app's Export Data ZIP.
        self.api_health_stats = {}
        self.api_health_last_state = {}
        self.api_health_last_issue_log = {}
        self.last_api_health_summary_ts = 0.0

        self.rejected_setup_rows = []
        self.rejected_setup_keys = set()
        self.last_rejected_tracker_update_ts = 0.0
        self._load_rejected_setup_log()

        # V3.7.4 learning mode: no post-trade same-direction cooldown and no
        # daily signal cap. Fresh valid completed-candle setups are allowed to signal.
        # Shadow learning remains observational only.
        self.shadow_lock = threading.RLock()
        self.shadow_learning_state = self._load_shadow_learning_state()

        self._load_previous_signal_log_for_stats()
        self._write_signals_today_file()

    @staticmethod
    def _classify_transport_issue(value):
        """Classify network/API failures for export-log diagnosis."""
        text = short_reason(value, 500).lower()
        if any(x in text for x in (
            "exceeding access rate", "too many requests", "rate limit", "ab1021", "429"
        )):
            return "RATE_LIMIT"
        if any(x in text for x in (
            "no address associated with hostname", "name or service not known",
            "temporary failure in name resolution", "nodename nor servname",
            "failed to resolve", "dns"
        )):
            return "DNS"
        if any(x in text for x in (
            "read timed out", "connect timeout", "connection timed out", "timed out", "timeout"
        )):
            return "TIMEOUT"
        if any(x in text for x in (
            "connection reset", "connection refused", "connection aborted",
            "remote end closed", "network is unreachable", "connection error"
        )):
            return "CONNECTION"
        return "OTHER"

    def _record_transport_issue(self, func_name, issue_kind, detail, is_history=False):
        source_map = {
            "DNS": ("NETWORK_DNS", ["DNS_RESOLUTION"]),
            "TIMEOUT": ("NETWORK_TIMEOUT", ["HTTP_RESPONSE"]),
            "CONNECTION": ("NETWORK_CONNECTION", ["HTTP_CONNECTION"]),
            "RATE_LIMIT": (
                "ANGEL_HISTORICAL_RATE_LIMIT" if is_history else "ANGEL_API_RATE_LIMIT",
                ["GET_CANDLE_DATA_RATE_LIMIT" if is_history else "REST_RATE_LIMIT"],
            ),
        }
        source, missing = source_map.get(
            issue_kind,
            ("ANGEL_REST_OTHER_FAILURE", [str(func_name or "REST_CALL").upper()]),
        )
        try:
            self._api_health_record(
                source,
                "FAILED",
                missing,
                f"func={func_name} | {short_reason(detail, 220)}",
                time.time(),
            )
        except Exception:
            log.warning(
                "API TRANSPORT ISSUE | source=%s | func=%s | detail=%s",
                source, func_name, short_reason(detail, 220),
            )

    def _activate_historical_rate_limit_backoff(self, detail):
        with self.state_lock:
            self.historical_rate_limit_count = min(
                self.historical_rate_limit_count + 1,
                len(HISTORICAL_RATE_LIMIT_BACKOFF_SECONDS),
            )
            idx = max(0, self.historical_rate_limit_count - 1)
            delay = HISTORICAL_RATE_LIMIT_BACKOFF_SECONDS[idx]
            self.historical_block_until = max(
                float(self.historical_block_until or 0.0),
                time.time() + float(delay),
            )
        log.warning(
            "ANGEL HISTORICAL RATE LIMIT | backoff=%ss | detail=%s",
            delay, short_reason(detail, 180),
        )
        return delay

    def angel_rest_call(self, func, *args, **kwargs):
        """REST wrapper with a separate conservative lane for getCandleData.

        Historical calls never block quote/Greeks/recovery REST calls behind a long
        rate-limit cooldown. All transport failures are classified into the exported
        runtime log so end-of-day analysis can separate phone/DNS problems from Angel.
        """
        func_name = str(getattr(func, "__name__", "REST_CALL") or "REST_CALL")
        is_history = func_name.lower() == "getcandledata"
        lock = self.historical_rest_lock if is_history else self.rest_lock

        with lock:
            if is_history:
                elapsed = time.monotonic() - float(self.historical_rest_last_call or 0.0)
                gap_wait = max(0.0, HISTORICAL_MIN_GAP_SECONDS - elapsed)
                block_wait = max(0.0, float(self.historical_block_until or 0.0) - time.time())
                wait = max(gap_wait, block_wait)
                if wait > 0:
                    log.info("Historical API throttle wait %.1fs before %s", wait, func_name)
                    time.sleep(wait)
            else:
                elapsed = time.monotonic() - float(self.rest_last_call or 0.0)
                wait = max(0.0, ANGEL_REST_MIN_GAP_SECONDS - elapsed)
                if wait > 0:
                    time.sleep(wait)

            try:
                result = func(*args, **kwargs)
                issue = self._classify_transport_issue(result)
                if issue == "RATE_LIMIT":
                    if is_history:
                        self._activate_historical_rate_limit_backoff(result)
                    self._record_transport_issue(func_name, issue, result, is_history=is_history)
                elif issue in ("DNS", "TIMEOUT", "CONNECTION"):
                    self._record_transport_issue(func_name, issue, result, is_history=is_history)
                elif is_history:
                    # A successful non-rate-limited response clears progressive backoff.
                    with self.state_lock:
                        had_limit = self.historical_rate_limit_count > 0
                        self.historical_rate_limit_count = 0
                        self.historical_block_until = 0.0
                    if had_limit:
                        try:
                            self._api_health_record(
                                "ANGEL_HISTORICAL_RATE_LIMIT", "OK", [],
                                "getCandleData recovered after backoff", time.time(),
                            )
                        except Exception:
                            pass
                return result

            except Exception as exc:
                issue = self._classify_transport_issue(exc)
                if issue == "RATE_LIMIT" and is_history:
                    self._activate_historical_rate_limit_backoff(exc)
                self._record_transport_issue(func_name, issue, exc, is_history=is_history)
                raise
            finally:
                if is_history:
                    self.historical_rest_last_call = time.monotonic()
                else:
                    self.rest_last_call = time.monotonic()

    # ----------------------------------------------------------------------
    # Login / instruments
    # ----------------------------------------------------------------------

    def _set_angel_login_state(self, logged_in, reason="", notify=False):
        with self.state_lock:
            self.angel_logged_in = bool(logged_in)
        persist_angel_login_state(bool(logged_in), reason=reason, notify=notify)

    def login(self):
        if BROKER_SELECTED == "DHAN":
            self._set_angel_login_state(False, "Dhan login pending", notify=False)
            self.smart = self.dhan_client
            try:
                return self.dhan_client.login()
            except Exception:
                self._set_angel_login_state(False, "Dhan login failed; check session/PIN/TOTP", notify=False)
                raise
        self._set_angel_login_state(False, reason="Angel login pending", notify=False)
        self.smart = SmartConnect(self.api_key)
        session = self.smart.generateSession(self.client_code, self.pin, self.totp)
        if not session or not session.get("status"):
            self._set_angel_login_state(False, reason="Angel login failed", notify=False)
            raise RuntimeError("Angel login failed. Check stored client/PIN/TOTP and retry.")
        self.auth_token = session["data"]["jwtToken"]
        self.feed_token = self.smart.getfeedToken()
        logged_in = bool(self.auth_token and self.feed_token)
        self._set_angel_login_state(logged_in, reason="Angel session verified", notify=logged_in)
        log.info("Angel login success")

    def logout(self, reason="Engine stopped", notify=True):
        """Best-effort Angel logout, followed by unconditional local session clear."""
        if BROKER_SELECTED == "DHAN":
            self._close_websocket_quiet()
            with self.state_lock:
                self.auth_token = self.feed_token = None
                self.dhan_client.token = ""
            self._set_angel_login_state(False, reason + " | Local Dhan session stopped", notify=notify)
            return True  # Cached session is reusable; no unsupported broker logout API.
        with self.state_lock:
            smart = self.smart
            was_logged_in = bool(self.angel_logged_in or self.auth_token or self.feed_token)

        api_logout_ok = False
        if smart is not None and was_logged_in:
            try:
                terminate = getattr(smart, "terminateSession", None)
                if callable(terminate):
                    result = terminate(self.client_code)
                    api_logout_ok = not isinstance(result, dict) or bool(result.get("status", True))
            except Exception as exc:
                log.warning("Angel logout API failed: %s", short_reason(exc, 120))

        with self.state_lock:
            self.angel_logged_in = False
            self.auth_token = None
            self.feed_token = None

        suffix = "Angel session closed" if api_logout_ok else "Local Angel session cleared"
        self._set_angel_login_state(False, reason=f"{reason} | {suffix}", notify=notify)
        log.info("Angel logout complete | api=%s | reason=%s", api_logout_ok, reason)
        return api_logout_ok

    def _read_master_file(self):
        self.instrument_df = pd.read_json(MASTER_FILE)

    def load_instrument_master(self):
        if BROKER_SELECTED == "DHAN":
            self.instrument_df = self.dhan_client.load_master()
            if not self._prepare_active_options(allow_fail=False):
                raise RuntimeError("No supported active Dhan index options in current master")
            return
        if not MASTER_FILE.exists():
            self._download_master()
        self._read_master_file()

        if not self._prepare_active_options(allow_fail=True):
            log.warning("Local instrument master has no supported active NSE/BSE index options; refreshing once")
            self._download_master()
            self._read_master_file()
            if not self._prepare_active_options(allow_fail=False):
                raise RuntimeError("No supported active NSE/BSE index options found after master refresh")
    def _download_master(self):
        log.info("Downloading Angel instrument master once")
        last_error = None
        for url in MASTER_URLS:
            try:
                r = requests.get(url, timeout=120, headers={"User-Agent": "Mozilla/5.0"})
                r.raise_for_status()
                MASTER_FILE.write_bytes(r.content)
                log.info("Instrument master saved (%.1f MB)", len(r.content) / 1024 / 1024)
                return
            except Exception as exc:
                last_error = exc
                issue = self._classify_transport_issue(exc)
                self._record_transport_issue("instrument_master_download", issue, exc, is_history=False)
                log.warning("Instrument-master endpoint unavailable: %s", short_reason(exc, 80))
        raise RuntimeError(f"Unable to download Angel instrument master: {short_reason(last_error,80)}")

    def _prepare_active_options(self, allow_fail):
        if self.instrument_df is None or self.instrument_df.empty:
            return False

        df = self.instrument_df.copy()
        required = {"name", "exch_seg", "instrumenttype", "expiry", "strike", "symbol", "token", "lotsize"}
        if not required.issubset(df.columns):
            if allow_fail:
                return False
            raise RuntimeError("Instrument master missing required columns")

        exch = df["exch_seg"].astype(str).str.upper().str.strip()
        inst = df["instrumenttype"].astype(str).str.upper().str.strip()
        opt = df[exch.isin(["NFO", "BFO"]) & (inst == "OPTIDX")].copy()
        opt["derivative_exchange"] = opt["exch_seg"].astype(str).str.upper().str.strip()
        opt["root"] = opt["name"].astype(str).str.upper().str.strip()

        allowed_nse = (opt["derivative_exchange"] == "NFO") & opt["root"].isin(SUPPORTED_NSE_INDEX_ROOTS)
        allowed_bse = (opt["derivative_exchange"] == "BFO") & opt["root"].isin(SUPPORTED_BSE_INDEX_ROOTS)
        opt = opt[allowed_nse | allowed_bse].copy()

        opt["expiry_dt"] = pd.to_datetime(opt["expiry"], format="%d%b%Y", errors="coerce")
        opt["strike_num"] = pd.to_numeric(opt["strike"], errors="coerce") / 100.0
        today = pd.Timestamp.now(tz="Asia/Kolkata").tz_localize(None).normalize()
        opt = opt[opt["expiry_dt"].notna() & (opt["expiry_dt"] >= today)]

        if opt.empty:
            return False

        candidates = []
        for (deriv_exchange, root), g in opt.groupby(["derivative_exchange", "root"]):
            candidates.append({
                "root": root,
                "expiry": g["expiry_dt"].min(),
                "derivative_exchange": deriv_exchange,
                "spot_exchange": SPOT_EXCHANGE_BY_DERIVATIVE[deriv_exchange],
            })

        # Priority 1: earliest option expiry date, irrespective of NSE or BSE.
        candidates.sort(key=lambda x: (x["expiry"], x["root"], x["derivative_exchange"]))
        self.index_candidates = candidates
        return bool(candidates)

    @staticmethod
    def _norm_index_name(value):
        return re.sub(r"[^A-Z0-9]", "", str(value).upper())

    def _resolve_spot_token(self, root, derivative_exchange):
        df = self.instrument_df.copy()
        spot_exchange = SPOT_EXCHANGE_BY_DERIVATIVE.get(str(derivative_exchange).upper())
        if not spot_exchange:
            return None, None

        exch = df["exch_seg"].astype(str).str.upper().str.strip()
        inst = df["instrumenttype"].astype(str).str.upper().str.strip()
        cash = df[exch == spot_exchange].copy()

        # Prefer AMXIDX rows. Some master revisions may leave instrumenttype blank
        # for a cash index, so an exact alias fallback within the same cash exchange
        # is allowed if no AMXIDX alias match exists.
        preferred = cash[inst.loc[cash.index] == "AMXIDX"].copy() if not cash.empty else cash

        aliases = {self._norm_index_name(x) for x in INDEX_ALIASES.get(root, (root,))}
        aliases.add(self._norm_index_name(root))

        def scan(frame):
            for _, row in frame.iterrows():
                vals = [row.get("name", ""), row.get("symbol", "")]
                norm = {self._norm_index_name(v) for v in vals}
                if aliases & norm:
                    return str(row["token"]), str(row.get("symbol") or root)
            return None

        hit = scan(preferred)
        if hit:
            return hit
        hit = scan(cash)
        if hit:
            return hit

        # Static fallbacks are used only for known NSE indices.
        if spot_exchange == "NSE" and BROKER_SELECTED == "ANGEL":
            fallback = INDEX_SPOT_FALLBACKS.get(root)
            if fallback:
                return fallback
        return None, None

    def _fetch_spot_map(self, candidate_rows):
        # Key all maps by (root, derivative_exchange) so NSE and BSE can coexist.
        token_meta_by_spot_exchange = defaultdict(dict)
        display = {}

        for item in candidate_rows:
            root = item["root"]
            deriv_exchange = item["derivative_exchange"]
            spot_exchange = item["spot_exchange"]
            tok, name = self._resolve_spot_token(root, deriv_exchange)
            key = (root, deriv_exchange)

            if not tok:
                log.warning("No %s spot token found for %s; skipping it", spot_exchange, root)
                continue

            token_meta_by_spot_exchange[spot_exchange][str(tok)] = key
            display[key] = (str(tok), name or root, spot_exchange)

        spots = {}
        for spot_exchange, token_to_key in token_meta_by_spot_exchange.items():
            if not token_to_key:
                continue
            try:
                result = self.angel_rest_call(
                    self.smart.getMarketData,
                    "LTP",
                    {spot_exchange: list(token_to_key.keys())},
                )
                for row in ((result or {}).get("data") or {}).get("fetched", []) or []:
                    tok = str(row.get("symbolToken", ""))
                    key = token_to_key.get(tok)
                    if key:
                        val = safe_float(row.get("ltp"))
                        if val:
                            spots[key] = val
            except Exception as exc:
                log.warning("%s spot scan unavailable: %s", spot_exchange, short_reason(exc, 80))

        return spots, display


    def _nearest_available_strike_for(self, options_df, spot):
        strikes = sorted({int(round(float(x))) for x in options_df["strike_num"].dropna().tolist()})
        if not strikes:
            return None
        return min(strikes, key=lambda x: abs(x - spot))

    def choose_index_for_day(self):
        if not self.index_candidates:
            raise RuntimeError("Index candidates not prepared")

        df = self.instrument_df.copy()
        selected = None

        # STRICT PRIORITIES:
        # 1) Earliest active option expiry across every eligible NSE + BSE index.
        # 2) If multiple indices share that exact expiry date, choose the LOWER
        #    live ATM option premium. One-lot cost is only a third tie-breaker.
        expiry_dates = sorted({x["expiry"] for x in self.index_candidates})

        for expiry in expiry_dates:
            tied = [x for x in self.index_candidates if x["expiry"] == expiry]
            spots, display = self._fetch_spot_map(tied)
            valid = [
                x for x in tied
                if (x["root"], x["derivative_exchange"]) in spots
                and (x["root"], x["derivative_exchange"]) in display
            ]
            if not valid:
                continue

            metrics = {}
            tokens_by_exchange = defaultdict(list)
            token_meta = {}

            for item in valid:
                root = item["root"]
                deriv_exchange = item["derivative_exchange"]
                key = (root, deriv_exchange)

                g = df[
                    (df["name"].astype(str).str.upper().str.strip() == root)
                    & (df["exch_seg"].astype(str).str.upper().str.strip() == deriv_exchange)
                    & (df["instrumenttype"].astype(str).str.upper().str.strip() == "OPTIDX")
                ].copy()
                g["expiry_dt"] = pd.to_datetime(g["expiry"], format="%d%b%Y", errors="coerce")
                g["strike_num"] = pd.to_numeric(g["strike"], errors="coerce") / 100.0
                g = g[g["expiry_dt"] == expiry]

                spot = spots.get(key)
                if not spot or g.empty:
                    continue

                atm = self._nearest_available_strike_for(g, spot)
                if atm is None:
                    continue

                rows = g[g["strike_num"].round().astype("Int64") == int(atm)]
                for _, row in rows.iterrows():
                    symbol = str(row["symbol"])
                    if not (symbol.endswith("CE") or symbol.endswith("PE")):
                        continue
                    tok = str(row["token"])
                    lot = max(1, int(float(row["lotsize"])))
                    tokens_by_exchange[deriv_exchange].append(tok)
                    token_meta[(deriv_exchange, tok)] = (key, lot)

            premiums_by_key = defaultdict(list)
            costs_by_key = defaultdict(list)

            for deriv_exchange, request_tokens in tokens_by_exchange.items():
                if not request_tokens:
                    continue
                try:
                    r = self.angel_rest_call(
                        self.smart.getMarketData,
                        "LTP",
                        {deriv_exchange: request_tokens},
                    )
                    for row in ((r or {}).get("data") or {}).get("fetched", []) or []:
                        tok = str(row.get("symbolToken", ""))
                        meta = token_meta.get((deriv_exchange, tok))
                        if not meta:
                            continue
                        key, lot = meta
                        ltp = safe_float(row.get("ltp"))
                        if ltp and ltp > 0:
                            premiums_by_key[key].append(float(ltp))
                            costs_by_key[key].append(float(ltp) * lot)
                except Exception as exc:
                    log.warning("%s ATM tie-break premium scan unavailable: %s",
                                deriv_exchange, short_reason(exc, 80))

            for item in valid:
                key = (item["root"], item["derivative_exchange"])
                premiums = premiums_by_key.get(key, [])
                costs = costs_by_key.get(key, [])
                # Mean of available ATM CE/PE LTP values. If only one side is
                # available, use that one rather than discarding the index.
                atm_premium = sum(premiums) / len(premiums) if premiums else float("inf")
                one_lot_cost = sum(costs) / len(costs) if costs else float("inf")
                metrics[key] = (atm_premium, one_lot_cost)

            valid_keys = [
                (x["root"], x["derivative_exchange"])
                for x in valid
                if math.isfinite(metrics.get((x["root"], x["derivative_exchange"]), (float("inf"),))[0])
            ]
            if not valid_keys:
                # If the earliest-expiry family has no usable live ATM premium,
                # do not silently choose by alphabet; try the next expiry family.
                continue

            # Priority 2: lowest ATM premium. Priority 3: lowest one-lot outlay.
            best_key = min(
                valid_keys,
                key=lambda k: (metrics[k][0], metrics[k][1], k[0], k[1]),
            )

            item = next(
                x for x in valid
                if (x["root"], x["derivative_exchange"]) == best_key
            )
            tok, disp, spot_exchange = display[best_key]
            atm_premium, one_lot_cost = metrics[best_key]

            selected = (
                item["root"], expiry, tok, disp, spot_exchange,
                item["derivative_exchange"], atm_premium, one_lot_cost
            )
            break

        if selected is None:
            raise RuntimeError(
                "No eligible NSE/BSE index had an active option, live spot, and usable ATM premium"
            )

        (
            root, earliest, tok, disp, spot_exchange,
            deriv_exchange, atm_premium, one_lot_cost
        ) = selected

        self.index_root = root
        self.index_display_name = disp
        self.spot_token = str(tok)
        self.spot_exchange = spot_exchange
        self.derivative_exchange = deriv_exchange
        self.spot_exchange_type = SPOT_WS_TYPE_BY_EXCHANGE[spot_exchange]
        self.derivative_exchange_type = DERIV_WS_TYPE_BY_EXCHANGE[deriv_exchange]
        self.nearest_expiry = earliest

        opt = df[
            (df["name"].astype(str).str.upper().str.strip() == root)
            & (df["exch_seg"].astype(str).str.upper().str.strip() == deriv_exchange)
            & (df["instrumenttype"].astype(str).str.upper().str.strip() == "OPTIDX")
        ].copy()
        opt["expiry_dt"] = pd.to_datetime(opt["expiry"], format="%d%b%Y", errors="coerce")
        opt["strike_num"] = pd.to_numeric(opt["strike"], errors="coerce") / 100.0
        today = pd.Timestamp.now(tz="Asia/Kolkata").tz_localize(None).normalize()
        opt = opt[opt["expiry_dt"].notna() & (opt["expiry_dt"] >= today)]
        self.nifty_options_df = opt
        self.available_strikes = sorted({
            int(round(float(x))) for x in
            opt[opt["expiry_dt"] == earliest]["strike_num"].dropna().tolist()
        })

        # Nearest FUTIDX for the selected root/exchange, used for traded-volume VWAP.
        fut = df[
            (df["name"].astype(str).str.upper().str.strip() == root)
            & (df["exch_seg"].astype(str).str.upper().str.strip() == deriv_exchange)
            & (df["instrumenttype"].astype(str).str.upper().str.strip() == "FUTIDX")
        ].copy()
        if not fut.empty:
            fut["expiry_dt"] = pd.to_datetime(fut["expiry"], format="%d%b%Y", errors="coerce")
            fut = fut[
                fut["expiry_dt"].notna() & (fut["expiry_dt"] >= today)
            ].sort_values("expiry_dt")

        if not fut.empty:
            row = fut.iloc[0]
            self.futures_token = str(row["token"])
            self.futures_symbol = str(row["symbol"])
            self.futures_expiry = row["expiry_dt"]
        else:
            self.futures_token = None

        log.info(
            "V3.4 selected %s/%s %s expiry %s; ATM premium %.2f; est one-lot %.0f",
            self.spot_exchange,
            self.derivative_exchange,
            self.index_root,
            self.nearest_expiry.date(),
            atm_premium,
            one_lot_cost,
        )

    def initial_spot(self):
        if not self.spot_token:
            raise RuntimeError("Selected index spot token is missing")
        result = self.angel_rest_call(
            self.smart.getMarketData,
            "LTP",
            {self.spot_exchange: [self.spot_token]},
        )
        try:
            value = float(result["data"]["fetched"][0]["ltp"])
        except Exception as exc:
            raise RuntimeError(
                f"Unable to obtain {self.spot_exchange} {self.index_root} spot"
            ) from exc
        with self.state_lock:
            self.nifty_live = value
        return value
    @staticmethod
    def classify_option(strike, side, atm):
        if strike == atm:
            return "ATM"
        if side == "CE":
            return "ITM" if strike < atm else "OTM"
        return "ITM" if strike > atm else "OTM"

    def build_option_universe(self, atm):
        e = self.nifty_options_df[self.nifty_options_df["expiry_dt"] == self.nearest_expiry]
        strikes_all = sorted({int(round(float(x))) for x in e["strike_num"].dropna().tolist()})
        if not strikes_all:
            return []
        atm = min(strikes_all, key=lambda x: abs(x - atm))
        idx = strikes_all.index(atm)
        lo = max(0, idx - 2)
        hi = min(len(strikes_all), idx + 3)
        strikes = strikes_all[lo:hi]
        rows = e[e["strike_num"].round().astype("Int64").isin(strikes)]

        new_tokens = []
        with self.state_lock:
            self.current_atm = atm
            self.wanted_strikes = strikes
            for _, row in rows.iterrows():
                symbol = str(row["symbol"])
                token = str(row["token"])
                strike = int(round(float(row["strike_num"])))
                side = "CE" if symbol.endswith("CE") else "PE" if symbol.endswith("PE") else None
                if side is None:
                    continue
                info = {"symbol": symbol, "token": token, "strike": strike, "side": side,
                        "lot": int(float(row["lotsize"])), "type": self.classify_option(strike, side, atm)}
                self.contracts[(strike, side)] = info
                self.token_contract[token] = info
                self.price_history.setdefault(token, deque(maxlen=600))
                if token not in self.subscribed_option_tokens:
                    new_tokens.append(token)
                    self.subscribed_option_tokens.add(token)
        return new_tokens
    @staticmethod
    def ws_price(value):
        try:
            return float(value) / 100.0
        except Exception:
            return None

    def extract_depth(self, message):
        combined = []
        combined.extend(message.get("best_5_buy_data", []) or [])
        combined.extend(message.get("best_5_sell_data", []) or [])

        bids, asks = [], []
        for item in combined:
            try:
                flag = int(item.get("flag", -1))
                price = self.ws_price(item.get("price"))
                qty = safe_int(item.get("quantity"))
                orders = safe_int(item.get("no of orders"))
                if price is None or price <= 0:
                    continue
                level = {"price": price, "qty": qty, "orders": orders}
                if flag == 1:       # BUY / BID
                    bids.append(level)
                elif flag == 0:     # SELL / ASK
                    asks.append(level)
            except Exception:
                continue

        bids.sort(key=lambda x: x["price"], reverse=True)
        asks.sort(key=lambda x: x["price"])
        return bids[:5], asks[:5]

    def update_option_tick(self, token, message):
        ltp = self.ws_price(message.get("last_traded_price"))
        if ltp is None:
            return

        bids, asks = self.extract_depth(message)
        bid = bids[0]["price"] if bids else None
        ask = asks[0]["price"] if asks else None

        if bid is not None and ask is not None and bid > ask:
            bid, ask = ask, bid

        spread = (ask - bid) if bid is not None and ask is not None else None
        now_ts = time.time()

        with self.state_lock:
            self.latest_options[token] = {
                "ltp": ltp,
                "bid": bid,
                "ask": ask,
                "spread": spread,
                "volume": safe_int(message.get("volume_trade_for_the_day")),
                "oi": safe_int(message.get("open_interest")),
                "buy_qty": safe_int(message.get("total_buy_quantity")),
                "sell_qty": safe_int(message.get("total_sell_quantity")),
                "timestamp": now_ts,
            }
            self.price_history[token].append((now_ts, ltp))

    def seed_futures_vwap(self):
        if not self.futures_token:
            self.futures_vwap_source = "NO FUTIDX"
            return
        n = now_ist()
        session_start = n.replace(hour=9, minute=15, second=0, microsecond=0)
        if n <= session_start:
            self.futures_vwap_source = "LIVE FROM OPEN"
            return
        params = {
            "exchange": self.derivative_exchange,
            "symboltoken": self.futures_token,
            "interval": "FIVE_MINUTE",
            "fromdate": session_start.strftime("%Y-%m-%d %H:%M"),
            "todate": n.strftime("%Y-%m-%d %H:%M"),
        }
        try:
            result = self.angel_rest_call(self.smart.getCandleData, params)
            if not result or not result.get("status") or not result.get("data"):
                self.futures_vwap_source = "LIVE ONLY"
                return
            rows = result.get("data") or []
            pv = 0.0
            vol = 0.0
            current_bucket = pd.Timestamp.now(tz="Asia/Kolkata").floor("5min")
            for row in rows:
                if len(row) < 6:
                    continue
                try:
                    ts = pd.to_datetime(row[0], utc=True).tz_convert("Asia/Kolkata")
                    if ts >= current_bucket:
                        continue
                    h, l, c, v = float(row[2]), float(row[3]), float(row[4]), max(0.0, float(row[5]))
                    tp = (h + l + c) / 3.0
                    pv += tp * v
                    vol += v
                except Exception:
                    continue
            if vol > 0:
                with self.state_lock:
                    self.futures_pv = pv
                    self.futures_volume = vol
                    self.futures_vwap = pv / vol
                    self.futures_last_cum_volume = vol
                    self.futures_vwap_source = "HISTORICAL + LIVE"
        except Exception as exc:
            self.futures_vwap_source = "LIVE ONLY"
            log.warning("Futures VWAP seed unavailable: %s", short_reason(exc, 80))


    def _amd_futures_profile_candles(self, start_time, end_time):
        """Return completed 5-minute futures OHLCV for AMD volume profile.

        Uses the already-selected nearest FUTIDX and the same broker REST wrapper.
        No order endpoint is involved.
        """
        if not self.futures_token or self.smart is None:
            return pd.DataFrame(columns=["time","open","high","low","close","volume"])
        try:
            start=pd.to_datetime(start_time)
            end=pd.to_datetime(end_time)
            if start.tzinfo is None: start=start.tz_localize(IST)
            else: start=start.tz_convert(IST)
            if end.tzinfo is None: end=end.tz_localize(IST)
            else: end=end.tz_convert(IST)
            params={
                "exchange": self.derivative_exchange,
                "symboltoken": self.futures_token,
                "interval": "FIVE_MINUTE",
                "fromdate": start.strftime("%Y-%m-%d %H:%M"),
                "todate": (end + pd.Timedelta(minutes=5)).strftime("%Y-%m-%d %H:%M"),
            }
            result=self.angel_rest_call(self.smart.getCandleData, params)
            rows=(result or {}).get("data") or []
            out=[]
            for row in rows:
                if len(row)<6: continue
                try:
                    ts=pd.to_datetime(row[0], utc=True).tz_convert("Asia/Kolkata")
                    op,hi,lo,cl,vol=[float(x) for x in row[1:6]]
                    if vol<0 or min(op,hi,lo,cl)<=0: continue
                    out.append({"time":ts,"open":op,"high":hi,"low":lo,"close":cl,"volume":vol})
                except Exception:
                    continue
            return pd.DataFrame(out).sort_values("time").reset_index(drop=True) if out else pd.DataFrame(columns=["time","open","high","low","close","volume"])
        except Exception as exc:
            log.warning("AMD+POC futures candles unavailable: %s", short_reason(exc,100))
            return pd.DataFrame(columns=["time","open","high","low","close","volume"])

    def update_futures_tick(self, message):
        raw = message.get("last_traded_price")
        if raw is None:
            return
        ltp = float(raw) / 100.0
        cum_vol = max(0.0, safe_float(message.get("volume_trade_for_the_day"), 0.0) or 0.0)
        now_ts = time.time()
        with self.state_lock:
            self.futures_ltp = ltp
            self.futures_last_tick_ts = now_ts
            if self.futures_last_cum_volume is None:
                if self.futures_volume <= 0 and cum_vol > 0:
                    self.futures_pv = ltp * cum_vol
                    self.futures_volume = cum_vol
                    self.futures_vwap = ltp
                self.futures_last_cum_volume = cum_vol
            else:
                delta = cum_vol - float(self.futures_last_cum_volume)
                if delta < 0:
                    # New session / exchange counter reset.
                    self.futures_pv = ltp * cum_vol
                    self.futures_volume = cum_vol
                elif delta > 0:
                    self.futures_pv += ltp * delta
                    self.futures_volume += delta
                self.futures_last_cum_volume = cum_vol
                if self.futures_volume > 0:
                    self.futures_vwap = self.futures_pv / self.futures_volume
            if self.futures_vwap_source in ("NOT READY", "NO FUTIDX"):
                self.futures_vwap_source = "LIVE"

    def futures_vwap_confirms(self, direction):
        with self.state_lock:
            ltp = safe_float(self.futures_ltp)
            vwap = safe_float(self.futures_vwap)
            ts = safe_float(self.futures_last_tick_ts, 0.0) or 0.0
        if not self.futures_token or ltp is None or vwap is None or not ts:
            return False
        if time.time() - ts > FUTURES_STALE_SECONDS:
            return False
        if direction == "CE":
            return ltp > vwap
        if direction == "PE":
            return ltp < vwap
        return False

    def _set_websocket_state(self, state, reason=None):
        state = str(state or "UNKNOWN").upper()
        with self.state_lock:
            old_state = str(getattr(self, "websocket_state", "UNKNOWN") or "UNKNOWN").upper()
            self.websocket_state = state
            if reason:
                self.websocket_last_reason = short_reason(reason, 180)
            reason_text = self.websocket_last_reason
        if state != old_state or reason:
            level = log.info if state == "HEALTHY" else log.warning
            level("WEBSOCKET STATE | %s -> %s | %s", old_state, state, short_reason(reason_text, 120))

    def _websocket_status_snapshot(self):
        with self.state_lock:
            state = str(getattr(self, "websocket_state", "UNKNOWN") or "UNKNOWN").upper()
            last_tick = float(self.last_nifty_tick_ts or 0.0)
            ticks = int(getattr(self, "websocket_healthy_ticks", 0) or 0)
            reason = str(getattr(self, "websocket_last_reason", "") or "")
            rest_ok = bool(getattr(self, "websocket_last_rest_probe_ok", False))
            rest_price = getattr(self, "websocket_last_rest_probe_price", None)
        age = None if not last_tick else max(0.0, time.time() - last_tick)
        return {
            "state": state, "last_tick": last_tick, "age": age,
            "healthy_ticks": ticks, "reason": reason,
            "rest_ok": rest_ok, "rest_price": rest_price,
        }

    def _close_websocket_quiet(self):
        # Invalidate old callbacks before asking the SDK to close.  This prevents an
        # intentional recovery close from being mistaken for another feed failure.
        with self.ws_lock:
            old = getattr(self, "sws", None)
            self.websocket_generation += 1
            self.websocket_connected = False
            self.sws = None
        if old is not None:
            try:
                old.close_connection()
            except Exception as exc:
                log.debug("Quiet WebSocket close skipped: %s", short_reason(exc, 80))

    def start_websocket(self, initial_option_tokens):
        tokens = [str(x) for x in (initial_option_tokens or []) if str(x)]
        with self.ws_lock:
            self.websocket_option_tokens.update(tokens)
            self.websocket_generation += 1
            generation = self.websocket_generation
            self.websocket_connected = False
            self.websocket_healthy_ticks = 0
            if not self.websocket_recovery_running:
                self.websocket_state = "CONNECTING"
            sws = DhanFeed(self.dhan_client) if BROKER_SELECTED == "DHAN" else SmartWebSocketV2(
                self.auth_token, self.api_key, self.client_code, self.feed_token
            )
            self.sws = sws

        def is_current():
            with self.ws_lock:
                return generation == self.websocket_generation and self.sws is sws

        def on_open(wsapp):
            if not is_current():
                return
            log.info("Angel WebSocket connected (generation %s)", generation)
            with self.state_lock:
                self.websocket_connected = True
                if self.websocket_state != "RECOVERING":
                    self.websocket_state = "CONNECTING"
                    self.websocket_last_reason = "CONNECTED / VERIFYING LIVE TICKS"
            try:
                sws.subscribe(
                    f"selectedspot{generation}", 1,
                    [{"exchangeType": self.spot_exchange_type, "tokens": [self.spot_token]}],
                )
                if self.futures_token:
                    sws.subscribe(
                        f"selectedfuture{generation}", 3,
                        [{"exchangeType": self.derivative_exchange_type, "tokens": [self.futures_token]}],
                    )
                option_tokens = sorted(self.websocket_option_tokens)
                if option_tokens:
                    sws.subscribe(
                        f"selectedopts{generation}", 3,
                        [{"exchangeType": self.derivative_exchange_type, "tokens": option_tokens}],
                    )
            except Exception as exc:
                log.warning("WebSocket subscription failed: %s", short_reason(exc, 100))
                self._request_websocket_recovery("SUBSCRIPTION FAILED: " + short_reason(exc, 100))

        def on_data(wsapp, message):
            if not is_current():
                return
            try:
                token = str(message.get("token", ""))
                if token == self.spot_token:
                    raw = message.get("last_traded_price")
                    if raw is None:
                        return
                    spot = float(raw) / 100.0
                    now_tick = time.time()
                    with self.state_lock:
                        self.nifty_live = spot
                        self.last_nifty_tick_ts = now_tick
                        self.websocket_healthy_ticks = min(
                            WEBSOCKET_HEALTHY_TICKS_REQUIRED,
                            int(self.websocket_healthy_ticks or 0) + 1,
                        )
                        if self.websocket_healthy_ticks >= WEBSOCKET_HEALTHY_TICKS_REQUIRED:
                            self.websocket_state = "HEALTHY"
                            self.websocket_last_reason = "LIVE TICKS VERIFIED"
                    if self.technical is not None:
                        closed = self.technical.on_tick(spot)
                        if closed:
                            with self.state_lock:
                                self.technical_state = self.technical.get_snapshot()
                                self.technical_last_update = time.time()
                elif self.futures_token and token == self.futures_token:
                    self.update_futures_tick(message)
                elif token in self.token_contract:
                    self.update_option_tick(token, message)
            except Exception as exc:
                log.exception("WebSocket data handler error: %s", short_reason(exc, 100))

        def on_error(wsapp, error):
            if not is_current():
                return
            msg = f"Angel WebSocket error: {short_reason(error,100)}"
            log.error(msg)
            issue = self._classify_transport_issue(error)
            if issue in ("DNS", "TIMEOUT", "CONNECTION", "RATE_LIMIT"):
                self._record_transport_issue("angel_websocket", issue, error, is_history=False)
            else:
                try:
                    self._api_health_record(
                        "ANGEL_WEBSOCKET_ERROR", "FAILED", ["LIVE_FEED"],
                        short_reason(error, 180), time.time(),
                    )
                except Exception:
                    pass
            # Errors first trigger silent recovery. Do not notify merely because one SDK callback fired.
            self._request_websocket_recovery(msg)

        def on_close(wsapp, *args):
            if not is_current():
                return
            log.warning("Angel WebSocket closed (generation %s)", generation)
            with self.state_lock:
                self.websocket_connected = False
            if not self.stop_event.is_set() and not after_engine_stop():
                self._request_websocket_recovery("ANGEL WEBSOCKET CLOSED")

        sws.on_open = on_open
        sws.on_data = on_data
        sws.on_error = on_error
        sws.on_close = on_close

        try:
            original_sdk_close = sws._on_close
            def safe_sdk_close(wsapp, *args):
                return original_sdk_close(wsapp)
            sws._on_close = safe_sdk_close
        except Exception:
            pass

        threading.Thread(target=sws.connect, daemon=True).start()

    def _rest_probe_selected_index(self):
        """Verify Angel REST is alive and refresh the displayed index price.

        REST never counts as a healthy WebSocket tick and therefore never bypasses
        the signal safety gate.
        """
        if not self.smart or not self.spot_token:
            return False, None, "REST PROBE NOT READY"
        try:
            result = self.angel_rest_call(
                self.smart.getMarketData,
                "LTP",
                {self.spot_exchange: [self.spot_token]},
            )
            fetched = ((result or {}).get("data") or {}).get("fetched") or []
            if not fetched:
                raise RuntimeError(f"No REST quote returned: {result}")
            value = safe_float(fetched[0].get("ltp"), None)
            if value is None or value <= 0:
                raise RuntimeError("REST quote did not contain a usable LTP")
            with self.state_lock:
                self.nifty_live = float(value)
                self.websocket_last_rest_probe_ts = time.time()
                self.websocket_last_rest_probe_price = float(value)
                self.websocket_last_rest_probe_ok = True
            return True, float(value), "ANGEL REST QUOTE OK"
        except Exception as exc:
            reason = short_reason(exc, 120)
            with self.state_lock:
                self.websocket_last_rest_probe_ts = time.time()
                self.websocket_last_rest_probe_ok = False
            return False, None, reason

    def _manual_refresh_requested(self):
        try:
            return MANUAL_REFRESH_FILE.exists()
        except Exception:
            return False

    def _consume_manual_refresh_request(self):
        try:
            if not MANUAL_REFRESH_FILE.exists():
                return False
            try:
                MANUAL_REFRESH_FILE.unlink()
            except Exception:
                # If deletion temporarily fails, truncate so one press still maps to
                # one refresh cycle rather than an endless refresh loop.
                try:
                    MANUAL_REFRESH_FILE.write_text("", encoding="utf-8")
                    MANUAL_REFRESH_FILE.unlink(missing_ok=True)
                except Exception:
                    pass
            return True
        except Exception:
            return False

    def _request_manual_data_refresh(self):
        """Start a non-blocking user-requested refresh of live market inputs.

        This does not restart the trading engine and never changes/ends an active
        TRANSIT. REST may refresh the displayed index price, but entry safety still
        requires a healthy WebSocket just as in normal operation.
        """
        with self.manual_refresh_lock:
            if self.manual_refresh_running:
                return False
            self.manual_refresh_running = True
        threading.Thread(target=self._manual_data_refresh_worker, daemon=True).start()
        return True

    def _manual_data_refresh_worker(self):
        result_parts = []
        try:
            # 1) Immediate selected-index REST quote refresh.
            ok, price, reason = self._rest_probe_selected_index()
            if ok:
                result_parts.append(f"INDEX {price:.2f}")
            else:
                result_parts.append("INDEX REST FAILED: " + short_reason(reason, 70))

            # 2) Ask Angel again for any already-completed 5-minute history.
            try:
                if self.technical is not None:
                    self.technical.maybe_recover_history_async()
                    with self.state_lock:
                        self.technical_state = self.technical.get_snapshot()
                        self.technical_last_update = time.time()
                    result_parts.append("5M CHECKED")
            except Exception as exc:
                result_parts.append("5M: " + short_reason(exc, 60))

            # 3) Refresh futures seed/baseline where possible.
            try:
                self.seed_futures_vwap()
                result_parts.append("FUTURES CHECKED")
            except Exception as exc:
                result_parts.append("FUTURES: " + short_reason(exc, 60))

            # 4) Refresh Greeks immediately when the exchange is live. This runs in
            # this background worker so the main signal loop remains responsive.
            try:
                if market_continuous_session():
                    with self.state_lock:
                        greek_running = bool(self.greeks_state.get("running"))
                    if not greek_running:
                        self.greeks_worker()
                    result_parts.append("GREEKS CHECKED")
            except Exception as exc:
                result_parts.append("GREEKS: " + short_reason(exc, 60))

            # 5) Fundamental/news refresh only when older than two minutes. A user
            # can press Refresh repeatedly without creating repeated OpenAI calls.
            try:
                with self.state_lock:
                    fund_running = bool(self.fundamental_state.get("running"))
                    fund_last = float(self.fundamental_state.get("last_update") or 0.0)
                if (not fund_running) and (not fund_last or time.time() - fund_last >= 120):
                    self.fundamental_worker()
                    result_parts.append("NEWS CHECKED")
                else:
                    result_parts.append("NEWS CACHE FRESH")
            except Exception as exc:
                result_parts.append("NEWS: " + short_reason(exc, 60))

            # 6) A manual refresh never treats REST as live-feed health. If the
            # WebSocket is stale/connecting, invoke the existing safe self-heal.
            try:
                snap = self._websocket_status_snapshot()
                if (
                    snap.get("state") != "HEALTHY"
                    or snap.get("age") is None
                    or float(snap.get("age") or 999999) > WEBSOCKET_SIGNAL_BLOCK_SECONDS
                ):
                    self._request_websocket_recovery("MANUAL REFRESH / LIVE FEED VERIFY")
                    result_parts.append("WEBSOCKET VERIFYING")
                else:
                    result_parts.append("WEBSOCKET HEALTHY")
            except Exception as exc:
                result_parts.append("WEBSOCKET: " + short_reason(exc, 60))

            with self.manual_refresh_lock:
                self.manual_refresh_last_ts = time.time()
                self.manual_refresh_last_result = " | ".join(result_parts[:8]) or "COMPLETE"
        finally:
            with self.manual_refresh_lock:
                self.manual_refresh_running = False
            try:
                self.write_live_status(None)
                self.write_app_ui(None, market_state="LIVE")
            except Exception:
                pass

    def _wait_for_websocket_healthy(self, timeout_seconds):
        deadline = time.time() + max(0.0, float(timeout_seconds))
        while time.time() < deadline:
            if self.stop_event.is_set() or _android_host_stop_requested() or after_engine_stop():
                return False
            snap = self._websocket_status_snapshot()
            if (
                snap["state"] == "HEALTHY"
                and snap["healthy_ticks"] >= WEBSOCKET_HEALTHY_TICKS_REQUIRED
                and snap["age"] is not None
                and snap["age"] <= WEBSOCKET_SIGNAL_BLOCK_SECONDS
            ):
                return True
            time.sleep(WEBSOCKET_RECOVERY_POLL_SECONDS)
        return False

    def _fresh_angel_login_for_websocket(self):
        """Refresh JWT/feed token without resetting trading state."""
        if BROKER_SELECTED == "DHAN":
            self.smart = self.dhan_client
            return self.dhan_client.login(force=self.dhan_client.auth_failed)
        fresh_totp = _fresh_totp_from_android_secret()
        smart = SmartConnect(self.api_key)
        session = smart.generateSession(self.client_code, self.pin, fresh_totp)
        if not session or not session.get("status"):
            raise RuntimeError("Angel re-login failed during WebSocket recovery")
        auth_token = session["data"]["jwtToken"]
        feed_token = smart.getfeedToken()
        with self.state_lock:
            self.totp = fresh_totp
            self.smart = smart
            self.auth_token = auth_token
            self.feed_token = feed_token
            self.angel_logged_in = bool(auth_token and feed_token)
        persist_angel_login_state(bool(auth_token and feed_token), reason="Angel session refreshed", notify=False)
        return True

    def _request_websocket_recovery(self, reason):
        if str(getattr(self, "runtime_phase", "")).upper() != "LIVE":
            return False
        if self.stop_event.is_set() or after_engine_stop():
            return False
        now_ts = time.time()
        with self.state_lock:
            if self.websocket_recovery_running:
                if reason:
                    self.websocket_last_reason = short_reason(reason, 180)
                return False
            last_end = float(self.websocket_last_recovery_end_ts or 0.0)
            # After a failed cycle, allow the SDK/network a brief settling period before
            # another self-heal cycle.  Signal entry remains blocked throughout.
            if last_end and now_ts - last_end < WEBSOCKET_RECOVERY_RETRY_COOLDOWN_SECONDS:
                return False
            self.websocket_recovery_running = True
            self.websocket_recovery_started_ts = now_ts
            self.websocket_state = "RECOVERING"
            self.websocket_last_reason = short_reason(reason or "LIVE FEED STALE", 180)
            self.websocket_healthy_ticks = 0
        threading.Thread(target=self._websocket_recovery_worker, daemon=True).start()
        return True

    def _websocket_recovery_worker(self):
        started = time.time()
        deadline = started + WEBSOCKET_RECOVERY_WARN_SECONDS
        success = False
        final_reason = "RECOVERY WINDOW EXPIRED"
        try:
            log.warning("V%s WebSocket self-heal started: %s", VERSION, self.websocket_last_reason)

            # STEP A: verify account/REST reachability and refresh the price shown in UI.
            rest_ok, _, rest_reason = self._rest_probe_selected_index()
            final_reason = rest_reason
            try:
                self.write_app_ui(None, market_state="LIVE")
            except Exception:
                pass

            # STEP B: rebuild only the WebSocket first.
            with self.state_lock:
                self.websocket_reconnect_attempts += 1
                self.websocket_last_reason = (
                    "REST OK / RECONNECTING WEBSOCKET" if rest_ok
                    else "REST CHECK FAILED / RECONNECTING WEBSOCKET"
                )
            tokens = sorted(self.websocket_option_tokens or set(self.token_contract.keys()))
            self._close_websocket_quiet()
            self.start_websocket(tokens)
            with self.state_lock:
                self.websocket_state = "RECOVERING"
            wait1 = min(WEBSOCKET_RECONNECT_WAIT_SECONDS, max(0.0, deadline - time.time()))
            if self._wait_for_websocket_healthy(wait1):
                success = True
                final_reason = "WEBSOCKET RECONNECTED"
                return

            # STEP C: if socket-only recovery failed, obtain fresh JWT/feed token and
            # create a completely new socket.
            if time.time() < deadline:
                try:
                    with self.state_lock:
                        self.websocket_last_reason = "RECONNECT FAILED / REFRESHING ANGEL SESSION"
                    self._fresh_angel_login_for_websocket()
                    self._rest_probe_selected_index()
                    self._close_websocket_quiet()
                    self.start_websocket(tokens)
                    with self.state_lock:
                        self.websocket_state = "RECOVERING"
                        self.websocket_last_reason = "FRESH LOGIN / VERIFYING WEBSOCKET TICKS"
                    wait2 = max(0.0, deadline - time.time())
                    if self._wait_for_websocket_healthy(wait2):
                        success = True
                        final_reason = "FRESH LOGIN + WEBSOCKET RECOVERED"
                        return
                    final_reason = "NO VERIFIED LIVE TICKS AFTER RECONNECT AND RE-LOGIN"
                except Exception as exc:
                    final_reason = "RE-LOGIN/RECONNECT FAILED: " + short_reason(exc, 120)
        finally:
            with self.state_lock:
                self.websocket_recovery_running = False
                self.websocket_last_recovery_end_ts = time.time()
                if success:
                    self.websocket_state = "HEALTHY"
                    self.websocket_last_reason = final_reason
                    self.websocket_healthy_ticks = max(
                        self.websocket_healthy_ticks, WEBSOCKET_HEALTHY_TICKS_REQUIRED
                    )
                else:
                    self.websocket_state = "STALE"
                    self.websocket_last_reason = final_reason
            try:
                self.write_app_ui(None, market_state="LIVE")
            except Exception:
                pass
            if success:
                log.info("V%s WebSocket self-heal successful: %s", VERSION, final_reason)
            else:
                # This is the first user warning: only after the full recovery window.
                self.health_alert(
                    "ws_recovery_failed",
                    "⚠️ LIVE DATA RECOVERY FAILED\n"
                    f"{self.index_root or 'INDEX'} WebSocket did not recover within "
                    f"{WEBSOCKET_RECOVERY_WARN_SECONDS} seconds.\n"
                    f"Reason: {short_reason(final_reason, 120)}\n"
                    "New entries remain blocked; automatic retry continues.",
                    cooldown=5 * 60,
                )

    def maybe_expand_option_universe(self):
        with self.state_lock:
            spot = self.nifty_live
            old_atm = self.current_atm
        if not spot or not self.available_strikes:
            return
        new_atm = min(self.available_strikes, key=lambda x: abs(x - spot))
        if new_atm == old_atm:
            return
        new_tokens = self.build_option_universe(new_atm)
        if not new_tokens:
            return
        self.websocket_option_tokens.update(str(x) for x in new_tokens)
        try:
            sws = self.sws
            if sws is None:
                raise RuntimeError("WebSocket is not connected")
            sws.subscribe(f"opts{new_atm}{int(time.time())}", 3,
                          [{"exchangeType": self.derivative_exchange_type, "tokens": new_tokens}])
            log.info("Expanded %s option universe around ATM %s", self.index_root, new_atm)
        except Exception as exc:
            # Subscription failure is treated like a feed-health event first.
            self._request_websocket_recovery("OPTION SUBSCRIPTION FAILED: " + short_reason(exc,80))
    def fundamental_prompt(self):
        n = now_ist()
        root = self.index_root or "SELECTED INDEX"
        return f"""
You are the FUNDAMENTAL AND BREAKING-NEWS probability layer for an intraday
{root} options-buying SIGNAL system in India.

CURRENT INDIA TIME: {n.strftime('%d-%m-%Y %H:%M:%S IST')}
Search the current web now.

SOURCE PRIORITY:
1. Reuters India / Reuters Markets
2. NSE / BSE official sources as applicable
3. RBI official sources
4. Federal Reserve and official economic sources
5. Other reliable financial sources only when required

CHECK the latest verified market-moving information: India VIX, Brent, USD/INR,
FII/DII, Asian/US markets, RBI/Fed/economic events, geopolitical/energy risk,
and important {root} constituent/index news.

OPTIONS BUYING ONLY.
Estimate three NEWS/FUNDAMENTAL probabilities which MUST total exactly 100:
- CE PROBABILITY = bullish/upside environment
- PE PROBABILITY = bearish/downside environment
- SIDEWAYS PROBABILITY = mixed/range/uncertain environment
These are directional probabilities, not guaranteed trade success rates.

Fundamentals are normally a SOFT score. HARD BLOCK only for exceptional breaking
risk, imminent discontinuous-volatility events, market disruption, or information
too unreliable to assess current risk.

DIRECTION SCORE: +100 strongly bullish, 0 neutral/mixed, -100 strongly bearish.
FILTER: LONG ALLOWED / SHORT ALLOWED / BOTH ALLOWED / WAIT.
If data cannot be verified, use UNKNOWN. Never invent market facts.

RETURN EXACTLY:
MARKET BIAS: BULLISH / BEARISH / NEUTRAL
NEWS RISK: LOW / MEDIUM / HIGH
BRENT: UP / DOWN / FLAT / UNKNOWN
USDINR: UP / DOWN / FLAT / UNKNOWN
INDIA VIX: value or UNKNOWN
GLOBAL: POSITIVE / NEGATIVE / MIXED
FII: BUY / SELL / NEUTRAL / UNKNOWN
DII: BUY / SELL / NEUTRAL / UNKNOWN
NEXT 2H EVENT: short text or NONE
BREAKING INDEX NEWS: short text or NONE
RISK GATE: OPEN / HARD BLOCK
HARD BLOCK REASON: short text or NONE
DIRECTION SCORE: integer -100 to +100
FILTER: LONG ALLOWED / SHORT ALLOWED / BOTH ALLOWED / WAIT
CE PROBABILITY: integer 0-100
PE PROBABILITY: integer 0-100
SIDEWAYS PROBABILITY: integer 0-100
CONFIDENCE: integer 0-100
"""
    def parse_fundamental(self, text):
        result = {
            "filter": "WAIT",
            "market_bias": "UNKNOWN",
            "news_risk": "UNKNOWN",
            "confidence": 0,
            "risk_gate": "OPEN",
            "direction_score": 0,
            "hard_block_reason": "",
            "ce_probability": None,
            "pe_probability": None,
            "sideways_probability": None,
        }

        m = re.search(r"MARKET BIAS:\s*(BULLISH|BEARISH|NEUTRAL)", text, re.I)
        if m:
            result["market_bias"] = m.group(1).upper()
        m = re.search(r"NEWS RISK:\s*(LOW|MEDIUM|HIGH)", text, re.I)
        if m:
            result["news_risk"] = m.group(1).upper()
        m = re.search(r"FILTER:\s*(LONG ALLOWED|SHORT ALLOWED|BOTH ALLOWED|WAIT)", text, re.I)
        if m:
            result["filter"] = m.group(1).upper()
        m = re.search(r"RISK GATE:\s*(OPEN|HARD BLOCK)", text, re.I)
        if m:
            result["risk_gate"] = m.group(1).upper()
        m = re.search(r"DIRECTION SCORE:\s*([+-]?\d+)", text, re.I)
        if m:
            result["direction_score"] = max(-100, min(100, int(m.group(1))))
        else:
            if result["filter"] == "LONG ALLOWED":
                result["direction_score"] = 50
            elif result["filter"] == "SHORT ALLOWED":
                result["direction_score"] = -50

        m = re.search(r"HARD BLOCK REASON:\s*(.+)", text, re.I)
        if m:
            reason = m.group(1).strip()
            if reason.upper() not in ("NONE", "UNKNOWN"):
                result["hard_block_reason"] = reason[:240]

        for key, label in (
            ("ce_probability", "CE PROBABILITY"),
            ("pe_probability", "PE PROBABILITY"),
            ("sideways_probability", "SIDEWAYS PROBABILITY"),
        ):
            m = re.search(rf"{label}:\s*(\d+)", text, re.I)
            if m:
                result[key] = max(0, min(100, int(m.group(1))))

        m = re.search(r"CONFIDENCE:\s*(\d+)", text, re.I)
        if m:
            result["confidence"] = max(0, min(100, int(m.group(1))))

        probs = [result["ce_probability"], result["pe_probability"], result["sideways_probability"]]
        if all(v is not None for v in probs) and sum(probs) > 0:
            total = float(sum(probs))
            ce = int(round(100.0 * probs[0] / total))
            pe = int(round(100.0 * probs[1] / total))
            side = max(0, 100 - ce - pe)
        else:
            # Compatibility fallback for a model response which omits explicit probabilities.
            confidence = max(0, min(100, int(result.get("confidence") or 0)))
            score = max(-100, min(100, int(result.get("direction_score") or 0)))
            side = max(10, min(80, 100 - confidence))
            directional = 100 - side
            bullish_share = (score + 100.0) / 200.0
            ce = int(round(directional * bullish_share))
            pe = max(0, directional - ce)
        result["ce_probability"] = ce
        result["pe_probability"] = pe
        result["sideways_probability"] = side
        return result
    def fundamental_worker(self):
        with self.state_lock:
            if self.fundamental_state["running"]:
                return
            self.fundamental_state["running"] = True
            self.fundamental_state["last_attempt"] = time.time()
            self.fundamental_state["error"] = None

        try:
            response = self.openai.responses.create(
                model=BACKGROUND_MODEL,
                reasoning={"effort": "low"},
                tools=[{"type": "web_search", "search_context_size": "low"}],
                input=self.fundamental_prompt(),
            )
            text = response.output_text.strip()
            parsed = self.parse_fundamental(text)
            with self.state_lock:
                self.fundamental_state.update(parsed)
                self.fundamental_state["text"] = text
                self.fundamental_state["last_update"] = time.time()
                self.fundamental_state["error"] = None
                cache_payload = dict(self.fundamental_state)
                cache_payload["running"] = False
            try:
                atomic_json_write(FUNDAMENTAL_CACHE_FILE, cache_payload)
            except Exception as exc:
                log.debug("Fundamental cache write skipped: %s", short_reason(exc, 80))
            log.info(
                "Luna fundamental: CE %s / PE %s / SIDEWAYS %s / confidence %s",
                parsed.get("ce_probability"), parsed.get("pe_probability"),
                parsed.get("sideways_probability"), parsed.get("confidence"),
            )
        except Exception as exc:
            with self.state_lock:
                # Keep a previously valid cached scan visible, but mark it stale/error.
                if not self.fundamental_state.get("last_update"):
                    self.fundamental_state["filter"] = "WAIT"
                    self.fundamental_state["risk_gate"] = "HARD BLOCK"
                    self.fundamental_state["hard_block_reason"] = "Fundamental/news scan unavailable"
                self.fundamental_state["error"] = f"{type(exc).__name__}: {exc}"
            issue = self._classify_transport_issue(exc)
            if issue in ("DNS", "TIMEOUT", "CONNECTION", "RATE_LIMIT"):
                self._record_transport_issue("openai_fundamental_scan", issue, exc, is_history=False)
            self.health_alert(
                "fundamental_error",
                "⚠️ FUNDAMENTAL ENGINE ERROR\n"
                f"{type(exc).__name__}: {exc}\n"
                "New signals are blocked until a valid refresh.",
                cooldown=120,
            )
        finally:
            with self.state_lock:
                self.fundamental_state["running"] = False
    @staticmethod
    def parse_greeks_rows(rows):
        output = {}
        source_fields = {
            "delta": "delta",
            "gamma": "gamma",
            "theta": "theta",
            "vega": "vega",
            "iv": "impliedVolatility",
        }
        for row in rows or []:
            strike = safe_float(row.get("strikePrice"))
            if strike is None:
                continue
            strike = int(strike)
            side = str(row.get("optionType", "")).upper()
            if side not in ("CE", "PE"):
                continue
            present = [k for k, src in source_fields.items() if safe_float(row.get(src), None) is not None]
            output[(strike, side)] = {
                "delta": safe_float(row.get("delta"), 0.0),
                "gamma": safe_float(row.get("gamma"), 0.0),
                "theta": safe_float(row.get("theta"), 0.0),
                "vega": safe_float(row.get("vega"), 0.0),
                "iv": safe_float(row.get("impliedVolatility"), 0.0),
                "greek_volume": safe_float(row.get("tradeVolume"), 0.0),
                "_present_fields": present,
            }
        return output
    @staticmethod
    def _norm_cdf(x):
        return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))

    @staticmethod
    def _norm_pdf(x):
        return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)

    def _bs_price(self, spot, strike, years, sigma, side, rate=0.065, div_yield=0.012):
        if spot <= 0 or strike <= 0 or years <= 0 or sigma <= 0:
            return 0.0
        root_t = math.sqrt(years)
        d1 = (
            math.log(spot / strike)
            + (rate - div_yield + 0.5 * sigma * sigma) * years
        ) / (sigma * root_t)
        d2 = d1 - sigma * root_t
        disc_r = math.exp(-rate * years)
        disc_q = math.exp(-div_yield * years)
        if side == "CE":
            return spot * disc_q * self._norm_cdf(d1) - strike * disc_r * self._norm_cdf(d2)
        return strike * disc_r * self._norm_cdf(-d2) - spot * disc_q * self._norm_cdf(-d1)

    def _infer_iv(self, spot, strike, years, premium, side):
        intrinsic = max(0.0, spot - strike) if side == "CE" else max(0.0, strike - spot)
        if premium <= intrinsic + 0.01 or years <= 0:
            return 0.05
        lo, hi = 0.01, 4.0
        for _ in range(45):
            mid = (lo + hi) / 2.0
            px = self._bs_price(spot, strike, years, mid, side)
            if px < premium:
                lo = mid
            else:
                hi = mid
        return max(0.01, min(4.0, (lo + hi) / 2.0))

    def _local_bfo_greeks(self):
        """Approximate BSE option Greeks locally because SmartAPI optionGreek
        does not provide BSE Greeks. Used only for BFO candidate ranking/risk context.
        """
        with self.state_lock:
            spot = safe_float(self.nifty_live, 0.0) or 0.0
            contracts = list(self.contracts.values())
            option_data = dict(self.latest_options)

        if spot <= 0 or self.nearest_expiry is None:
            return {}

        n = now_ist()
        expiry_close = datetime.combine(
            self.nearest_expiry.date(),
            datetime.min.time(),
            tzinfo=IST,
        ).replace(hour=15, minute=30)
        seconds = max(60.0, (expiry_close - n).total_seconds())
        years = seconds / (365.0 * 24.0 * 3600.0)
        rate = 0.065
        div_yield = 0.012
        root_t = math.sqrt(years)
        disc_q = math.exp(-div_yield * years)

        output = {}
        seen = set()
        for c in contracts:
            strike = int(c["strike"])
            side = str(c["side"]).upper()
            key = (strike, side)
            if key in seen:
                continue
            seen.add(key)

            d = option_data.get(str(c["token"])) or {}
            ltp = safe_float(d.get("ltp"))
            bid = safe_float(d.get("bid"))
            ask = safe_float(d.get("ask"))
            premium = None
            if bid is not None and ask is not None and bid > 0 and ask >= bid:
                premium = (bid + ask) / 2.0
            elif ltp is not None and ltp > 0:
                premium = ltp
            if premium is None:
                continue

            sigma = self._infer_iv(spot, strike, years, premium, side)
            if sigma <= 0 or root_t <= 0:
                continue

            d1 = (
                math.log(spot / strike)
                + (rate - div_yield + 0.5 * sigma * sigma) * years
            ) / (sigma * root_t)
            d2 = d1 - sigma * root_t
            pdf = self._norm_pdf(d1)

            delta = disc_q * self._norm_cdf(d1) if side == "CE" else disc_q * (self._norm_cdf(d1) - 1.0)
            gamma = disc_q * pdf / (spot * sigma * root_t)
            vega = spot * disc_q * pdf * root_t / 100.0

            first = -(spot * disc_q * pdf * sigma) / (2.0 * root_t)
            if side == "CE":
                theta_annual = (
                    first
                    - rate * strike * math.exp(-rate * years) * self._norm_cdf(d2)
                    + div_yield * spot * disc_q * self._norm_cdf(d1)
                )
            else:
                theta_annual = (
                    first
                    + rate * strike * math.exp(-rate * years) * self._norm_cdf(-d2)
                    - div_yield * spot * disc_q * self._norm_cdf(-d1)
                )

            output[key] = {
                "delta": float(delta),
                "gamma": float(gamma),
                "theta": float(theta_annual / 365.0),
                "vega": float(vega),
                "iv": float(sigma * 100.0),
                "greek_volume": 0.0,
            }
        return output

    def greeks_worker(self):
        """Refresh Greeks without directly notifying.

        V3.6 centralises all warning policy in internal_health_worker so LOGIN and
        CLOSED phases stay silent, and LIVE Greeks get a full 60-second grace period
        before any warning can be emitted.
        """
        with self.state_lock:
            if self.greeks_state["running"]:
                return
            self.greeks_state["running"] = True
        try:
            if self.derivative_exchange == "BFO" and BROKER_SELECTED == "ANGEL":
                mapped = self._local_bfo_greeks()
                if not mapped:
                    raise RuntimeError("Local BFO Greek proxy not ready")
                with self.state_lock:
                    self.greeks_state["data"] = mapped
                    self.greeks_state["last_update"] = time.time()
                    self.greeks_state["error"] = None
                log.info("BFO local proxy Greeks ready for %s", self.index_root)
            else:
                expiry = self.nearest_expiry.strftime("%d%b%Y").upper()
                result = self.angel_rest_call(
                    self.smart.optionGreek,
                    {"name": self.index_root, "expirydate": expiry},
                )
                if not result or not result.get("status"):
                    raise RuntimeError("Greeks unavailable")
                mapped = self.parse_greeks_rows(result.get("data", []))
                if not mapped:
                    raise RuntimeError("Greeks response empty")
                with self.state_lock:
                    self.greeks_state["data"] = mapped
                    self.greeks_state["last_update"] = time.time()
                    self.greeks_state["error"] = None
        except Exception as exc:
            with self.state_lock:
                self.greeks_state["error"] = short_reason(exc, 100)
            log.warning("Greeks refresh unavailable: %s", short_reason(exc, 100))
        finally:
            with self.state_lock:
                self.greeks_state["running"] = False

    def premium_momentum(self, token, seconds=10):
        with self.state_lock:
            hist = list(self.price_history.get(token, []))
        if len(hist) < 2:
            return 0.0
        now_ts = time.time()
        current = hist[-1][1]
        older = hist[0][1]
        for ts, price in hist:
            if now_ts - ts <= seconds:
                older = price
                break
        return current - older

    def premium_volatility_range(self, token, seconds=OPTION_VOL_WINDOW_SECONDS):
        """Recent option premium range used only to size SL/target breathing room."""
        with self.state_lock:
            hist = list(self.price_history.get(token, []))
        if len(hist) < 2:
            return 0.0
        cutoff = time.time() - max(10, int(seconds))
        prices = [safe_float(p) for ts, p in hist if ts >= cutoff]
        prices = [float(p) for p in prices if p is not None and p > 0]
        if len(prices) < 2:
            return 0.0
        return max(prices) - min(prices)

    def select_best_option(self, direction):
        with self.state_lock:
            atm = self.current_atm
            strikes = list(self.wanted_strikes)
            contracts = dict(self.contracts)
            option_data = dict(self.latest_options)
            greek_data = dict(self.greeks_state["data"])
            tech_now = dict(self.technical_state)

        strong_trend = str(tech_now.get("setup") or "").upper() == "STRONG TREND CONTINUATION"
        grade_a = (
            str(tech_now.get("setup_grade") or "").upper() == "A"
            or safe_float(tech_now.get("tech_score"), 0.0) >= 82.0
        )
        eligible, volumes, ois = [], [], []
        for strike in strikes:
            c = contracts.get((strike, direction))
            if not c:
                continue
            d = option_data.get(c["token"])
            g = greek_data.get((strike, direction))
            if not d or not g or time.time() - d.get("timestamp", 0) > 10:
                continue
            bid, ask, ltp = d.get("bid"), d.get("ask"), d.get("ltp")
            if bid is None or ask is None or ltp is None or ask <= 0:
                continue
            cost = ask * c["lot"] * current_lots_per_signal()
            if cost > MAX_POSITION_COST:
                continue
            spread = ask - bid
            spread_pct = spread / ask * 100
            if spread < 0 or spread_pct > MAX_SPREAD_PCT:
                continue
            mom10 = self.premium_momentum(c["token"], 10)
            # Learning mode: do not discard an excellent underlying setup because
            # 10-second option momentum is merely flat. Clearly negative premium
            # momentum still fails this deterministic gate.
            if strong_trend:
                momentum_floor = -0.05
            elif grade_a:
                momentum_floor = 0.00
            else:
                momentum_floor = 0.02
            if mom10 <= momentum_floor:
                continue
            eligible.append((strike, c, d, g, mom10))
            volumes.append(max(0, d.get("volume", 0)))
            ois.append(max(0, d.get("oi", 0)))

        if not eligible:
            return None
        max_volume = max(volumes) if volumes else 1
        max_oi = max(ois) if ois else 1
        candidates = []
        for strike, c, d, g, momentum in eligible:
            bid, ask, ltp = d["bid"], d["ask"], d["ltp"]
            spread = ask - bid
            spread_pct = spread / ask * 100
            abs_delta = abs(g.get("delta", 0.0))
            iv = g.get("iv", 0.0)
            volume, oi = d.get("volume", 0), d.get("oi", 0)
            mom30 = self.premium_momentum(c["token"], 30)
            score = 0.0
            score += 25 if spread_pct <= .25 else 20 if spread_pct <= .5 else 12 if spread_pct <= 1 else 6
            score += 25 if .45 <= abs_delta <= .65 else 18 if .35 <= abs_delta <= .75 else 10 if .25 <= abs_delta <= .80 else 3
            score += 15 * (volume / max_volume)
            score += 10 * (oi / max_oi)
            option_type = self.classify_option(strike, direction, atm)
            try:
                distance = abs(strikes.index(strike) - strikes.index(atm))
            except Exception:
                distance = 9
            if option_type == "ATM": score += 10
            elif option_type == "ITM" and distance == 1: score += 9
            elif option_type == "OTM" and distance == 1: score += 6
            elif option_type == "ITM": score += 6
            else: score += 2
            score += 10 if momentum >= .50 else 7 if momentum >= .10 else 4 if momentum >= 0 else 1
            if mom30 > 0:
                score += 3
            elif strong_trend and mom30 >= -0.10:
                score += 1
            if iv is not None and 3 <= iv <= 40: score += 5
            candidates.append({
                "symbol": c["symbol"], "token": c["token"], "strike": strike,
                "side": direction, "type": option_type, "lot": c["lot"],
                "ltp": ltp, "bid": bid, "ask": ask, "spread": spread,
                "spread_pct": spread_pct, "volume": volume, "oi": oi,
                "buy_qty": d.get("buy_qty",0), "sell_qty": d.get("sell_qty",0),
                "delta": g.get("delta",0.0), "gamma": g.get("gamma",0.0),
                "theta": g.get("theta",0.0), "vega": g.get("vega",0.0),
                "iv": iv, "premium_momentum_10s": momentum,
                "premium_momentum_30s": mom30, "cost": ask*c["lot"]*current_lots_per_signal(),
                "score": round(min(100.0, score),1),
            })
        if not candidates:
            return None
        candidates.sort(key=lambda x: (x["score"], x["premium_momentum_10s"]), reverse=True)
        return candidates[0]
    def fundamental_support(self, direction):
        """Return (support_score 0..100, hard_blocked, reason)."""
        with self.state_lock:
            fund = dict(self.fundamental_state)

        now_ts = time.time()
        last = float(fund.get("last_update") or 0.0)

        if fund.get("error") and not last:
            return 0.0, True, "No valid fundamental/news scan"

        if not last or now_ts - last > FUNDAMENTAL_STALE_SECONDS:
            return 0.0, True, "Fundamental/news data is stale"

        if str(fund.get("risk_gate", "OPEN")).upper() == "HARD BLOCK":
            reason = fund.get("hard_block_reason") or "Luna risk gate HARD BLOCK"
            return 0.0, True, reason

        # V3.4 deterministic direction gate. TECH still triggers first, but once
        # fundamentals are consulted they must explicitly allow that direction.
        f = str(fund.get("filter", "WAIT")).upper().strip()
        # Learning phase: a fresh, non-HARD-BLOCK WAIT is uncertainty, not a veto.
        # Explicit opposite-direction filters still block exactly as before.
        if f not in ("WAIT", "LONG ALLOWED", "SHORT ALLOWED", "BOTH ALLOWED"):
            return 0.0, True, f"Unknown fundamental filter: {f or 'EMPTY'}"
        if direction == "CE" and f in ("SHORT ALLOWED",):
            return 0.0, True, f"{f} does not allow CE"
        if direction == "PE" and f in ("LONG ALLOWED",):
            return 0.0, True, f"{f} does not allow PE"

        directional = max(-100, min(100, safe_int(fund.get("direction_score"), 0)))
        if direction == "CE":
            support = FUNDAMENTAL_SUPPORT_NEUTRAL + directional * 0.50
        else:
            support = FUNDAMENTAL_SUPPORT_NEUTRAL - directional * 0.50

        if direction == "CE":
            if f == "LONG ALLOWED":
                support += 10
            elif f == "SHORT ALLOWED":
                support -= 12
        else:
            if f == "SHORT ALLOWED":
                support += 10
            elif f == "LONG ALLOWED":
                support -= 12

        bias = str(fund.get("market_bias", "UNKNOWN")).upper()
        if direction == "CE":
            if bias == "BULLISH":
                support += 5
            elif bias == "BEARISH":
                support -= 5
        else:
            if bias == "BEARISH":
                support += 5
            elif bias == "BULLISH":
                support -= 5

        news = str(fund.get("news_risk", "UNKNOWN")).upper()
        if news == "LOW":
            support += 8
        elif news == "HIGH":
            support -= 8

        if f == "WAIT":
            support -= 5  # uncertainty penalty, but not a hard block in learning mode

        return max(0.0, min(100.0, support)), False, ""

    def setup_signature(self, tech, direction=None):
        """Identity of one independent strategy event for de-duplication.

        5m strategies use the completed 5m candle time. Weapon Candle uses its
        completed 15m event time. Real-time VWAP events get their own event time.
        """
        d = str(direction or tech.get("direction") or "").upper()
        event_time = tech.get("strategy_event_time") or tech.get("candle_time") or ""
        return (
            str(self.index_root or ""),
            str(event_time),
            str(tech.get("setup") or "NONE").upper(),
            d,
        )

    def _consume_vwap_strategy_event(self, tech):
        """Create one independent Futures-VWAP reclaim/rejection opportunity.

        This is event-based, not a permanent condition: it triggers only when the
        live futures price crosses the running session VWAP and the current ADX/DI
        direction is at least coherent. It does not require EMA/ORB/FVG agreement.
        """
        with self.state_lock:
            fltp = safe_float(self.futures_ltp)
            fvwap = safe_float(self.futures_vwap)
        if fltp is None or fvwap is None or fltp <= 0 or fvwap <= 0:
            return None

        diff = float(fltp) - float(fvwap)
        # Ignore sub-tick/noise equality; only a real side change is an event.
        relation = 1 if diff > 0.05 else (-1 if diff < -0.05 else 0)
        prev = self.last_futures_vwap_relation
        if relation != 0:
            self.last_futures_vwap_relation = relation
        if prev is None or relation == 0 or relation == prev:
            return None

        adx = safe_float(tech.get("adx14"), 0.0) or 0.0
        plus_di = safe_float(tech.get("plus_di14"), 0.0) or 0.0
        minus_di = safe_float(tech.get("minus_di14"), 0.0) or 0.0
        if adx < VWAP_EVENT_MIN_ADX:
            return None

        if relation > 0 and prev < 0:
            di_gap = plus_di - minus_di
            if di_gap < VWAP_EVENT_MIN_DI_GAP:
                return None
            direction, setup = "CE", "VWAP RECLAIM"
        elif relation < 0 and prev > 0:
            di_gap = minus_di - plus_di
            if di_gap < VWAP_EVENT_MIN_DI_GAP:
                return None
            direction, setup = "PE", "VWAP REJECTION"
        else:
            return None

        self.last_futures_vwap_event_ts = time.time()
        score = min(94.0, 82.0 + min(7.0, max(0.0, adx - 18.0) / 2.0) + min(5.0, max(0.0, di_gap) / 3.0))
        v = dict(tech)
        v.update({
            "direction": direction,
            "setup": setup,
            "setup_grade": "A" if score >= 82.0 else "B",
            "tech_score": round(score, 1),
            "entry_ready": True,
            "entry_block_reason": "",
            "strategy_event_time": now_ist().replace(microsecond=0).isoformat(),
            "vwap_event_futures_ltp": round(float(fltp), 2),
            "vwap_event_futures_vwap": round(float(fvwap), 2),
        })
        return v

    def technical_strategy_variants(self, tech):
        """Return every independent technical strategy currently eligible to be tried."""
        variants = []
        raw = tech.get("setup_candidates") or []
        if isinstance(raw, list):
            for item in raw[:MAX_TECH_STRATEGY_VARIANTS]:
                if not isinstance(item, dict):
                    continue
                v = dict(tech)
                v["setup"] = str(item.get("setup") or "NONE")
                v["direction"] = str(item.get("direction") or "").upper()
                v["tech_score"] = safe_float(item.get("tech_score"), 0.0) or 0.0
                v["setup_grade"] = str(item.get("setup_grade") or "NONE")
                v["entry_ready"] = bool(item.get("entry_ready"))
                v["entry_block_reason"] = str(item.get("entry_block_reason") or "")
                v["strategy_event_time"] = item.get("strategy_event_time") or tech.get("candle_time")
                v["candlestick_bonus"] = safe_float(item.get("candlestick_bonus"), 0.0) or 0.0
                v["candlestick_primary"] = item.get("candlestick_primary") or "NONE"
                v["candlestick_family"] = item.get("candlestick_family") or "NONE"
                v["candlestick_direction"] = item.get("candlestick_direction") or "NEUTRAL"
                v["candlestick_bias"] = item.get("candlestick_bias") or tech.get("candlestick_bias") or "NEUTRAL"
                for key in (
                    "strategy_id","strategy_short_name","strategy_status","strategy_reason",
                    "liquidity_level","sweep_price","sweep_time",
                    "htf_fvg_lower","htf_fvg_upper","htf_fvg_time",
                    "ltf_fvg_lower","ltf_fvg_upper","ltf_fvg_time",
                    "ifvg_confirmation_time","cisd_reference_open","cisd_reference_time",
                    "cisd_confirmation_time","setup_invalidation_level",
                    "target_liquidity","target_liquidity_time","target_liquidity_type",
                    "amd_accumulation_start","amd_accumulation_end",
                    "amd_range_high","amd_range_low","amd_poc_price",
                    "amd_profile_total_volume","amd_profile_bin_size","amd_profile_source",
                    "amd_manipulation_price","amd_manipulation_time",
                    "amd_poc_cross_time","amd_poc_retest_time",
                ):
                    if key in item:
                        v[key] = item.get(key)
                variants.append(v)

        if not variants and tech.get("setup") and str(tech.get("setup")).upper() != "NONE":
            variants.append(dict(tech))

        vwap_event = self._consume_vwap_strategy_event(tech)
        if vwap_event is not None:
            variants.append(vwap_event)

        # Highest local quality is tried first, but a failed local gate on one strategy
        # does not invalidate the others. De-duplicate identical strategy events.
        variants.sort(key=lambda x: safe_float(x.get("tech_score"), 0.0) or 0.0, reverse=True)
        out = []
        seen = set()
        for v in variants:
            key = self.setup_signature(v, v.get("direction"))
            if key in seen:
                continue
            seen.add(key)
            out.append(v)
        return out[:MAX_TECH_STRATEGY_VARIANTS]

    def market_data_fresh(self):
        # A REST quote can refresh the displayed price during recovery, but it must
        # never make a signal eligible.  Entry requires a verified healthy WebSocket.
        with self.state_lock:
            last_tick = float(self.last_nifty_tick_ts or 0.0)
            ws_state = str(getattr(self, "websocket_state", "UNKNOWN") or "UNKNOWN").upper()
            healthy_ticks = int(getattr(self, "websocket_healthy_ticks", 0) or 0)
        if ws_state != "HEALTHY" or healthy_ticks < WEBSOCKET_HEALTHY_TICKS_REQUIRED:
            return False
        if not last_tick:
            return False
        return (time.time() - last_tick) <= WEBSOCKET_SIGNAL_BLOCK_SECONDS

    def completed_candle_fresh(self, tech):
        try:
            ts = pd.to_datetime(tech.get("candle_time"), utc=True).tz_convert("Asia/Kolkata")
            age = (pd.Timestamp.now(tz="Asia/Kolkata") - ts).total_seconds()
            # A completed 5m candle should normally be <10 minutes old.
            return 0 <= age <= 10 * 60
        except Exception:
            return False

    def live_technical_confirmation(self, direction, tech_override=None):
        """Final live-price sanity check for the selected independent strategy.

        V3.8 does not force every strategy through the same EMA20/ADX/OR template.
        Each setup keeps its own technical logic; this function only checks that the
        live price has not already invalidated the event while Luna/options are reviewed.
        """
        with self.state_lock:
            spot = float(self.nifty_live or 0.0)
            base_tech = dict(self.technical_state)
        tech = dict(tech_override) if isinstance(tech_override, dict) else base_tech
        if not spot or not self.completed_candle_fresh(tech):
            return False

        setup = str(tech.get("setup", "NONE")).upper()
        ema20 = safe_float(tech.get("ema20"))
        or_high = safe_float(tech.get("or_high"))
        or_low = safe_float(tech.get("or_low"))
        liq_level = safe_float(tech.get("liquidity_level"))
        fvg_lo = safe_float(tech.get("fvg_zone_low"))
        fvg_hi = safe_float(tech.get("fvg_zone_high"))
        weapon_ema9 = safe_float(tech.get("weapon15_ema9"))

        if direction == "CE":
            if setup == SWEEP_IFVG_SETUP_NAME:
                inv = safe_float(tech.get("setup_invalidation_level"))
                ifvg_hi = safe_float(tech.get("ltf_fvg_upper"))
                cisd_open = safe_float(tech.get("cisd_reference_open"))
                return bool(
                    (inv is None or spot > inv)
                    and (ifvg_hi is None or spot > ifvg_hi)
                    and (cisd_open is None or spot > cisd_open)
                )
            if setup == AMD_POC_SETUP_NAME:
                inv = safe_float(tech.get("setup_invalidation_level"))
                poc = safe_float(tech.get("amd_poc_price"))
                tol = max((poc or 0.0) * AMD_POC_RETEST_TOLERANCE_PCT / 100.0, 0.5)
                return bool(
                    (inv is None or spot > inv)
                    and (poc is None or spot >= poc - tol)
                )
            if setup == "WEAPON CANDLE 15M":
                return weapon_ema9 is not None and spot > weapon_ema9
            if setup == "VWAP RECLAIM":
                return self.futures_vwap_confirms("CE")
            if "OPENING RANGE" in setup:
                return or_high is not None and spot > or_high
            if setup == "LIQUIDITY SWEEP REVERSAL" and liq_level is not None:
                return spot > liq_level
            if setup == "LIQUIDITY BREAK CONTINUATION" and liq_level is not None:
                return spot > liq_level
            if setup == "FVG RETEST CONTINUATION" and fvg_hi is not None:
                return spot > fvg_hi
            return ema20 is not None and spot > ema20

        if direction == "PE":
            if setup == SWEEP_IFVG_SETUP_NAME:
                inv = safe_float(tech.get("setup_invalidation_level"))
                ifvg_lo = safe_float(tech.get("ltf_fvg_lower"))
                cisd_open = safe_float(tech.get("cisd_reference_open"))
                return bool(
                    (inv is None or spot < inv)
                    and (ifvg_lo is None or spot < ifvg_lo)
                    and (cisd_open is None or spot < cisd_open)
                )
            if setup == AMD_POC_SETUP_NAME:
                inv = safe_float(tech.get("setup_invalidation_level"))
                poc = safe_float(tech.get("amd_poc_price"))
                tol = max((poc or 0.0) * AMD_POC_RETEST_TOLERANCE_PCT / 100.0, 0.5)
                return bool(
                    (inv is None or spot < inv)
                    and (poc is None or spot <= poc + tol)
                )
            if setup == "WEAPON CANDLE 15M":
                return weapon_ema9 is not None and spot < weapon_ema9
            if setup == "VWAP REJECTION":
                return self.futures_vwap_confirms("PE")
            if "OPENING RANGE" in setup:
                return or_low is not None and spot < or_low
            if setup == "LIQUIDITY SWEEP REVERSAL" and liq_level is not None:
                return spot < liq_level
            if setup == "LIQUIDITY BREAK CONTINUATION" and liq_level is not None:
                return spot < liq_level
            if setup == "FVG RETEST CONTINUATION" and fvg_lo is not None:
                return spot < fvg_lo
            return ema20 is not None and spot < ema20
        return False

    @staticmethod
    def _shadow_clamp(value, low=0.0, high=1.0):
        try:
            return max(low, min(high, float(value)))
        except Exception:
            return low

    @staticmethod
    def _shadow_strategy_key(setup):
        setup = str(setup or "DEFAULT").upper().strip()
        return setup if setup in SHADOW_BASE_WEIGHTS else "DEFAULT"

    def _shadow_base_weights(self, setup):
        key = self._shadow_strategy_key(setup)
        return dict(SHADOW_BASE_WEIGHTS.get(key, SHADOW_BASE_WEIGHTS["DEFAULT"]))

    def _load_shadow_learning_state(self):
        blank = {
            "schema": 1,
            "mode": "SHADOW_ONLY",
            "resolved_total": 0,
            "processed": [],
            "strategies": {},
            "last_updated": "",
        }
        try:
            if not SHADOW_LEARNING_STATE_FILE.exists():
                return blank
            raw = json.loads(SHADOW_LEARNING_STATE_FILE.read_text(encoding="utf-8"))
            if not isinstance(raw, dict):
                return blank
            raw.setdefault("schema", 1)
            raw["mode"] = "SHADOW_ONLY"
            raw.setdefault("resolved_total", 0)
            raw.setdefault("processed", [])
            raw.setdefault("strategies", {})
            raw.setdefault("last_updated", "")
            return raw
        except Exception as exc:
            log.warning("Shadow learning state load failed: %s", short_reason(exc, 80))
            return blank

    def _save_shadow_learning_state(self):
        try:
            with self.shadow_lock:
                payload = json.loads(json.dumps(self.shadow_learning_state))
            atomic_json_write(SHADOW_LEARNING_STATE_FILE, payload)
        except Exception as exc:
            log.warning("Shadow learning state save failed: %s", short_reason(exc, 80))

    def _shadow_current_weights(self, setup):
        base = self._shadow_base_weights(setup)
        key = self._shadow_strategy_key(setup)
        with self.shadow_lock:
            strat = dict(self.shadow_learning_state.get("strategies", {}).get(key, {}))
        suggested = strat.get("suggested_weights")
        if isinstance(suggested, dict) and all(k in suggested for k in base):
            try:
                vals = {k: max(0.001, float(suggested[k])) for k in base}
                total = sum(vals.values())
                if total > 0:
                    return {k: vals[k] / total for k in base}
            except Exception:
                pass
        return base

    def _shadow_factor_scores(self, candidate, tech, fund, risk_per_unit):
        """Build 0..1 support scores for factors already used by V3.0.

        These scores are recorded only AFTER Luna has approved a live signal.
        They cannot create, reject, or alter a V3.0 signal.
        """
        side = str(candidate.get("side", "")).upper()
        direction_sign = 1.0 if side == "CE" else -1.0
        spot = max(1.0, safe_float(self.nifty_live, 0.0) or 0.0)

        adx = safe_float(tech.get("adx14"), 0.0) or 0.0
        plus_di = safe_float(tech.get("plus_di14"), 0.0) or 0.0
        minus_di = safe_float(tech.get("minus_di14"), 0.0) or 0.0
        di_gap = (plus_di - minus_di) if side == "CE" else (minus_di - plus_di)
        adx_part = self._shadow_clamp((adx - MIN_ADX) / 20.0)
        di_part = self._shadow_clamp(di_gap / 20.0)
        adx_di = self._shadow_clamp(0.45 + 0.30 * adx_part + 0.25 * di_part)

        ema20_slope = safe_float(tech.get("ema20_slope"), 0.0) or 0.0
        ema50_slope = safe_float(tech.get("ema50_slope"), 0.0) or 0.0
        s20_bp = direction_sign * ema20_slope / spot * 10000.0
        s50_bp = direction_sign * ema50_slope / spot * 10000.0
        s20 = self._shadow_clamp(s20_bp / 2.0)
        s50 = self._shadow_clamp(s50_bp / 1.0)
        structure = str(tech.get("structure", "")).upper()
        structure_good = (
            (side == "CE" and "HIGHER HIGH / HIGHER LOW" in structure)
            or (side == "PE" and "LOWER HIGH / LOWER LOW" in structure)
        )
        structure_bad = (
            (side == "CE" and "LOWER HIGH / LOWER LOW" in structure)
            or (side == "PE" and "HIGHER HIGH / HIGHER LOW" in structure)
        )
        structure_score = 1.0 if structure_good else 0.15 if structure_bad else 0.55
        ema_structure = self._shadow_clamp(
            0.30 + 0.30 * s20 + 0.20 * s50 + 0.20 * structure_score
        )

        setup = str(tech.get("setup", "")).upper()
        or_status = str(tech.get("or_status", "")).upper()
        if "OPENING RANGE RETEST" in setup:
            opening_range = 1.0
        elif "OPENING RANGE BREAKOUT" in setup:
            opening_range = 0.90
        elif "DAY HIGH" in setup or "DAY LOW" in setup:
            opening_range = 0.80
        elif (side == "CE" and "ABOVE OPENING RANGE" in or_status) or (
            side == "PE" and "BELOW OPENING RANGE" in or_status
        ):
            opening_range = 0.72
        elif "INSIDE OPENING RANGE" in or_status:
            opening_range = 0.50
        else:
            opening_range = 0.30

        with self.state_lock:
            fltp = safe_float(self.futures_ltp)
            fvwap = safe_float(self.futures_vwap)
        atr = max(0.0, safe_float(tech.get("atr14"), 0.0) or 0.0)
        if fltp is None or fvwap is None or fltp <= 0 or fvwap <= 0:
            futures_vwap = 0.50
        else:
            directional_gap = (fltp - fvwap) if side == "CE" else (fvwap - fltp)
            scale = max(atr, spot * 0.0010, 0.01)
            gap_strength = self._shadow_clamp(directional_gap / scale)
            futures_vwap = self._shadow_clamp(0.50 + 0.50 * gap_strength)

        risk = max(0.05, safe_float(risk_per_unit, 0.05) or 0.05)
        mom10 = safe_float(candidate.get("premium_momentum_10s"), 0.0) or 0.0
        mom30 = safe_float(candidate.get("premium_momentum_30s"), 0.0) or 0.0
        mom10_strength = self._shadow_clamp(mom10 / max(0.05, 0.20 * risk))
        mom30_strength = self._shadow_clamp(mom30 / max(0.05, 0.40 * risk))
        option_momentum = self._shadow_clamp(
            0.45 + 0.35 * mom10_strength + 0.20 * mom30_strength
        )

        option_quality = self._shadow_clamp(
            (safe_float(candidate.get("score"), 0.0) or 0.0) / 100.0
        )
        fundamental = self._shadow_clamp(
            (safe_float(candidate.get("fundamental_support"), 50.0) or 50.0) / 100.0
        )

        return {
            "adx_di": round(adx_di, 4),
            "ema_structure": round(ema_structure, 4),
            "opening_range": round(opening_range, 4),
            "futures_vwap": round(futures_vwap, 4),
            "option_momentum": round(option_momentum, 4),
            "option_quality": round(option_quality, 4),
            "fundamental": round(fundamental, 4),
        }

    @staticmethod
    def _shadow_weighted_score(weights, scores):
        total = 0.0
        denom = 0.0
        for name, weight in weights.items():
            w = max(0.0, safe_float(weight, 0.0) or 0.0)
            s = max(0.0, min(1.0, safe_float(scores.get(name), 0.5) or 0.5))
            total += w * s
            denom += w
        return round(100.0 * total / denom, 2) if denom > 0 else 0.0

    def _shadow_signal_snapshot(self, candidate, tech, fund, risk_per_unit):
        setup = str(tech.get("setup", "DEFAULT")).upper()
        base = self._shadow_base_weights(setup)
        suggested = self._shadow_current_weights(setup)
        scores = self._shadow_factor_scores(candidate, tech, fund, risk_per_unit)
        return {
            "strategy": self._shadow_strategy_key(setup),
            "factor_scores": scores,
            "base_weights": base,
            "suggested_weights": suggested,
            "base_score": self._shadow_weighted_score(base, scores),
            "adaptive_score": self._shadow_weighted_score(suggested, scores),
        }

    @staticmethod
    def _shadow_outcome_r(terminal):
        entry = safe_float(terminal.get("entry"))
        sl = safe_float(terminal.get("sl"))
        if entry is None or sl is None:
            return None
        risk = max(0.05, entry - sl)
        outcome = str(terminal.get("outcome", "")).upper()

        if outcome == "IMMEDIATE EXIT":
            final = safe_float(
                terminal.get("guardian_exit_price"),
                safe_float(terminal.get("last_ltp")),
            )
        else:
            final = safe_float(terminal.get("last_ltp"))

        if final is None:
            if outcome == "TARGET HIT":
                final = safe_float(terminal.get("target"))
            elif outcome == "SL HIT":
                final = sl

        if final is None:
            return None

        r_value = (final - entry) / risk
        return round(max(-2.0, min(2.0, r_value)), 4)

    def _shadow_recompute_suggested_weights(self, strategy_key, strat):
        base = self._shadow_base_weights(strategy_key)
        resolved = safe_int(strat.get("resolved"), 0)
        if resolved < SHADOW_MIN_STRATEGY_SAMPLES:
            return base

        raw = {}
        for factor, base_weight in base.items():
            fs = (strat.get("factors") or {}).get(factor, {})
            n = max(0, safe_int(fs.get("n"), 0))
            if n < SHADOW_MIN_STRATEGY_SAMPLES:
                raw[factor] = base_weight
                continue

            sx = safe_float(fs.get("sum_x"), 0.0) or 0.0
            sx2 = safe_float(fs.get("sum_x2"), 0.0) or 0.0
            sr = safe_float(fs.get("sum_r"), 0.0) or 0.0
            sxr = safe_float(fs.get("sum_xr"), 0.0) or 0.0

            mean_x = sx / n
            mean_r = sr / n
            var_x = max(0.0, sx2 / n - mean_x * mean_x)
            cov_xr = sxr / n - mean_x * mean_r

            if var_x <= 1e-5:
                edge = 0.0
            else:
                slope = cov_xr / var_x
                # tanh prevents a small noisy sample from producing a huge shift.
                edge = math.tanh(slope / 2.0)

            shrink = n / (n + SHADOW_PRIOR_STRENGTH)
            relative_shift = max(
                -SHADOW_MAX_RELATIVE_SHIFT,
                min(SHADOW_MAX_RELATIVE_SHIFT, edge * shrink * SHADOW_MAX_RELATIVE_SHIFT),
            )
            raw[factor] = max(0.001, base_weight * (1.0 + relative_shift))

        total = sum(raw.values())
        if total <= 0:
            return base
        return {k: round(v / total, 6) for k, v in raw.items()}

    def record_terminal_risk_state(self, terminal):
        """Record outcome into the V3.4 shadow learner.

        Important: this function does not block future CE/PE signals and does not
        modify live scoring. It only updates research statistics and suggestions.
        """
        try:
            signal_no = safe_int(terminal.get("signal_no"), -1)
            date_key = str(terminal.get("date") or now_ist().date().isoformat())
            processed_key = f"{date_key}:{signal_no}"
            if signal_no < 0:
                return

            r_value = self._shadow_outcome_r(terminal)
            if r_value is None:
                return

            strategy = self._shadow_strategy_key(terminal.get("technical_setup"))
            try:
                scores = json.loads(str(terminal.get("shadow_factor_scores") or "{}"))
            except Exception:
                scores = {}
            if not isinstance(scores, dict) or not scores:
                return

            with self.shadow_lock:
                state = self.shadow_learning_state
                processed = list(state.setdefault("processed", []))
                if processed_key in processed:
                    return

                strategies = state.setdefault("strategies", {})
                strat = strategies.setdefault(
                    strategy,
                    {
                        "resolved": 0,
                        "sum_r": 0.0,
                        "positive": 0,
                        "negative": 0,
                        "flat": 0,
                        "factors": {},
                        "suggested_weights": self._shadow_base_weights(strategy),
                        "last_updated": "",
                    },
                )

                strat["resolved"] = safe_int(strat.get("resolved"), 0) + 1
                strat["sum_r"] = round((safe_float(strat.get("sum_r"), 0.0) or 0.0) + r_value, 6)
                if r_value > 0.025:
                    strat["positive"] = safe_int(strat.get("positive"), 0) + 1
                elif r_value < -0.025:
                    strat["negative"] = safe_int(strat.get("negative"), 0) + 1
                else:
                    strat["flat"] = safe_int(strat.get("flat"), 0) + 1

                factor_stats = strat.setdefault("factors", {})
                for factor, x_raw in scores.items():
                    if factor not in self._shadow_base_weights(strategy):
                        continue
                    x = self._shadow_clamp(x_raw)
                    fs = factor_stats.setdefault(
                        factor,
                        {"n": 0, "sum_x": 0.0, "sum_x2": 0.0, "sum_r": 0.0, "sum_xr": 0.0},
                    )
                    fs["n"] = safe_int(fs.get("n"), 0) + 1
                    fs["sum_x"] = round((safe_float(fs.get("sum_x"), 0.0) or 0.0) + x, 6)
                    fs["sum_x2"] = round((safe_float(fs.get("sum_x2"), 0.0) or 0.0) + x * x, 6)
                    fs["sum_r"] = round((safe_float(fs.get("sum_r"), 0.0) or 0.0) + r_value, 6)
                    fs["sum_xr"] = round((safe_float(fs.get("sum_xr"), 0.0) or 0.0) + x * r_value, 6)

                suggested_after = self._shadow_recompute_suggested_weights(strategy, strat)
                strat["suggested_weights"] = suggested_after
                strat["mean_r"] = round(
                    (safe_float(strat.get("sum_r"), 0.0) or 0.0) / max(1, safe_int(strat.get("resolved"), 1)),
                    4,
                )
                strat["last_updated"] = now_ist().isoformat()

                state["resolved_total"] = safe_int(state.get("resolved_total"), 0) + 1
                processed.append(processed_key)
                # Bound processed IDs so this file never grows without limit.
                state["processed"] = processed[-5000:]
                state["mode"] = "SHADOW_ONLY"
                state["last_updated"] = now_ist().isoformat()

            terminal["shadow_outcome_r"] = r_value
            terminal["shadow_learning_recorded"] = True
            terminal["shadow_suggested_weights_after"] = json.dumps(
                suggested_after, separators=(",", ":"), sort_keys=True
            )

            # signal_history contains the original live-transit dict; mirror the
            # learning fields into it so the main CSV carries the full research row.
            with self.state_lock:
                for row in reversed(self.signal_history):
                    if safe_int(row.get("signal_no"), -2) == signal_no:
                        row["shadow_outcome_r"] = terminal["shadow_outcome_r"]
                        row["shadow_learning_recorded"] = True
                        row["shadow_suggested_weights_after"] = terminal["shadow_suggested_weights_after"]
                        break

            self._save_shadow_learning_state()

        except Exception as exc:
            log.warning("Shadow learning update failed: %s", short_reason(exc, 100))

    def shadow_learning_text(self):
        with self.shadow_lock:
            state = json.loads(json.dumps(self.shadow_learning_state))

        total = safe_int(state.get("resolved_total"), 0)
        readiness = (
            "READY FOR REVIEW"
            if total >= SHADOW_REVIEW_AFTER_RESOLVED
            else f"COLLECTING {total}/{SHADOW_REVIEW_AFTER_RESOLVED}"
        )
        lines = [
            "🧠 V3.4 SHADOW LEARNING",
            "Live adaptive weights: OFF",
            f"Status: {readiness}",
        ]

        strategies = state.get("strategies", {}) or {}
        ranked = sorted(
            strategies.items(),
            key=lambda kv: safe_int((kv[1] or {}).get("resolved"), 0),
            reverse=True,
        )
        for name, info in ranked[:5]:
            n = safe_int((info or {}).get("resolved"), 0)
            mean_r = safe_float((info or {}).get("mean_r"), 0.0) or 0.0
            lines.append(f"{name}: n={n}, mean {mean_r:+.2f}R")

        if not ranked:
            lines.append("No resolved signals yet.")

        return "\n".join(lines)

    @staticmethod
    def _parse_signal_time(value):
        try:
            dt = datetime.fromisoformat(str(value))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=IST)
            return dt.astimezone(IST)
        except Exception:
            return None

    def reentry_cooldown_gate(self, direction):
        """V3.7.4 learning mode: post-trade cooldown is deliberately disabled.

        A fresh valid setup may signal in the same direction after the previous transit
        resolves. Exact duplicate emission from the *same completed-candle event* is still
        de-duplicated separately by setup_signature(), so the UI is not spammed every scan.
        """
        direction = str(direction or "").upper()
        if direction not in ("CE", "PE"):
            return False, "INVALID DIRECTION"
        return True, ""

    def entry_timing_gate(self, candidate, tech):
        """Price-action timing gate applied after an option candidate is selected.

        V3.8.0 keeps the entry-timing protections while allowing independent strategies:
        repeated EMA/trend continuation inside the opening range, and continuation/retest
        entries while the selected option's 30-second premium momentum is negative/flat.
        Liquidity-sweep reversals are allowed to turn earlier and therefore do not use the
        same 30-second threshold.
        """
        if not candidate:
            return False, "NO OPTION CANDIDATE"
        setup = str(tech.get("setup") or "").upper()
        or_status = str(tech.get("or_status") or "").upper()
        mom30 = safe_float(candidate.get("premium_momentum_30s"), 0.0) or 0.0
        mom10 = safe_float(candidate.get("premium_momentum_10s"), 0.0) or 0.0

        if "INSIDE OPENING RANGE" in or_status and setup in (
            "EMA20 PULLBACK CONTINUATION",
            "TREND CONTINUATION",
        ):
            return False, "INSIDE OPENING RANGE: WAIT FOR BREAK/RETEST"

        strong_like = setup in (
            "STRONG TREND CONTINUATION",
            "OPENING RANGE BREAKOUT",
            "LIQUIDITY BREAK CONTINUATION",
            "WEAPON CANDLE 15M",
            "HIGH VOLUME MOMENTUM",
            "NR7 COMPRESSION BREAKOUT",
            "BOLLINGER SQUEEZE BREAKOUT",
            "ADX DI EXPANSION",
            "INSIDE BAR VOLUME BREAKOUT",
        )
        continuation_like = setup in (
            "EMA20 PULLBACK CONTINUATION",
            "TREND CONTINUATION",
            "OPENING RANGE RETEST",
            "DAY HIGH CONTINUATION",
            "DAY LOW CONTINUATION",
            "FVG RETEST CONTINUATION",
            "VWAP RECLAIM",
            "VWAP REJECTION",
            "HIGH VOLUME BREAKOUT RETEST",
            "VOLUME EXHAUSTION REVERSAL",
            "EMA ADX PULLBACK CONFIRMATION",
        )

        if continuation_like and mom30 < PREMIUM_ACCEPTANCE_CONTINUATION_30S:
            return False, (
                f"PREMIUM NOT ACCEPTED: 30S {mom30:+.2f} < "
                f"{PREMIUM_ACCEPTANCE_CONTINUATION_30S:+.2f}"
            )
        if strong_like and mom30 < PREMIUM_ACCEPTANCE_STRONG_30S:
            return False, f"PREMIUM NOT ACCEPTED: 30S {mom30:+.2f}"

        # Candidate selection already requires non-negative/positive short momentum,
        # but re-check here so a stale candidate cannot bypass the timing layer.
        if setup != "LIQUIDITY SWEEP REVERSAL" and mom10 <= 0:
            return False, f"PREMIUM 10S NOT POSITIVE: {mom10:+.2f}"
        return True, ""

    def _set_timing_wait_after_review(self, reason):
        """Turn a post-Luna timing deterioration into a temporary WAIT/recheck."""
        with self.state_lock:
            self.final_review_state["decision"] = "WAIT"
            self.final_review_state["reason"] = short_reason(reason, 80)
            waits = int(self.final_review_state.get("wait_retries") or 0) + 1
            self.final_review_state["wait_retries"] = waits
            if waits <= LUNA_WAIT_MAX_RECHECKS:
                self.final_review_state["next_retry_ts"] = time.time() + POST_REVIEW_TIMING_RECHECK_SECONDS
            else:
                self.final_review_state["next_retry_ts"] = 0.0

    def score_candidate_v31(self, candidate, tech, fund):
        direction = candidate["side"]
        support, blocked, block_reason = self.fundamental_support(direction)

        if blocked:
            return None, support, block_reason

        tech_score = safe_float(tech.get("tech_score"), 0.0) or 0.0
        option_score = safe_float(candidate.get("score"), 0.0) or 0.0

        combined = (
            TECH_SCORE_WEIGHT * tech_score
            + OPTION_SCORE_WEIGHT * option_score
            + FUNDAMENTAL_SCORE_WEIGHT * support
        )

        candidate["technical_score"] = round(tech_score, 1)
        candidate["fundamental_support"] = round(support, 1)
        candidate["combined_score"] = round(combined, 1)
        candidate["setup"] = tech.get("setup", "NONE")
        candidate["setup_grade"] = tech.get("setup_grade", "NONE")

        return round(combined, 1), support, ""

    # ----------------------------------------------------------------------
    # Luna final review (high reasoning)
    # ----------------------------------------------------------------------

    @staticmethod
    def extract_json(text):
        text = (text or "").strip()
        try:
            return json.loads(text)
        except Exception:
            pass
        m = re.search(r"\{.*\}", text, re.S)
        if not m:
            return None
        try:
            return json.loads(m.group(0))
        except Exception:
            return None

    def final_review_prompt(self, candidate, tech, fund):
        with self.state_lock:
            fvwap = self.futures_vwap
            fltp = self.futures_ltp
        return f"""
You are the FINAL RISK REVIEWER for INDEX SIGNAL MONITOR V{VERSION}.
Python has already enforced the deterministic fundamental direction gate; do not override it.
No broker order is placed. Decide only whether one local signal is issued.
Selected index: {self.index_root}. Earliest option expiry: {self.nearest_expiry.date()}.

Python already selected one option. Do not change strike and do not calculate entry/SL/target.
This is a learning-phase signal monitor, so do not demand perfection. APPROVE a coherent
setup when the hard gates already passed even if one SOFT factor is only neutral. WAIT only
for genuinely weak current timing; REJECT only for a real conflict. High news risk by itself
is a confidence penalty, not an automatic veto. Flat/slightly weak short-term option premium
momentum is a soft timing penalty for A-grade and STRONG TREND setups; clearly negative
momentum can justify WAIT. Never override Python's live-data, Futures-VWAP, hard fundamental,
liquidity/Greeks, or anti-chase protections.

FUTURES: LTP={fltp} VWAP={fvwap}
FUNDAMENTAL: {fund}
TECHNICAL: {tech}
OPTION: {candidate}

Return JSON only:
{{"decision":"APPROVE"|"REJECT"|"WAIT","confidence":0-100,"reason":"3-8 words only"}}
"""
    def final_review_worker(self, candidate, tech_snapshot, fund_snapshot, signature):
        with self.state_lock:
            if self.final_review_state["running"]:
                return
            same_signature = tuple(self.final_review_state.get("last_signature") or ()) == tuple(signature)
            if not same_signature:
                self.final_review_state["wait_retries"] = 0
                self.final_review_state["next_retry_ts"] = 0.0
            self.final_review_state["running"] = True
            self.final_review_state["last_signature"] = signature
            self.final_review_state["last_review_ts"] = time.time()
            self.final_review_state["error"] = None

        try:
            response = self.openai.responses.create(
                model=FINAL_MODEL,
                reasoning={"effort": "high"},
                input=self.final_review_prompt(candidate, tech_snapshot, fund_snapshot),
            )
            parsed = self.extract_json(response.output_text)
            if not parsed:
                raise RuntimeError("Luna did not return valid JSON")

            decision = str(parsed.get("decision", "WAIT")).upper()
            if decision not in ("APPROVE", "REJECT", "WAIT"):
                decision = "WAIT"
            confidence = max(0, min(100, safe_int(parsed.get("confidence", 0))))
            reason = short_reason(parsed.get("reason", ""))

            with self.state_lock:
                self.final_review_state["decision"] = decision
                self.final_review_state["confidence"] = confidence
                self.final_review_state["reason"] = reason
                if decision == "WAIT":
                    waits = int(self.final_review_state.get("wait_retries") or 0) + 1
                    self.final_review_state["wait_retries"] = waits
                    # Initial WAIT + up to two additional reviews of the same candle/setup.
                    if waits <= LUNA_WAIT_MAX_RECHECKS:
                        self.final_review_state["next_retry_ts"] = (
                            time.time() + LUNA_WAIT_REVIEW_DELAY_SECONDS
                        )
                    else:
                        self.final_review_state["next_retry_ts"] = 0.0
                else:
                    self.final_review_state["next_retry_ts"] = 0.0

            if decision == "APPROVE":
                self.issue_signal(candidate, confidence, reason, tech_snapshot, fund_snapshot)
            else:
                with self.state_lock:
                    waits = int(self.final_review_state.get("wait_retries") or 0)
                    next_retry = float(self.final_review_state.get("next_retry_ts") or 0.0)
                retry_text = (
                    f" | retry_in={max(0,int(next_retry-time.time()))}s wait_count={waits}"
                    if decision == "WAIT" and next_retry else ""
                )
                log.info(
                    "REJECTED SETUP | LUNA %s | %s | setup=%s score=%s | reason=%s%s",
                    decision, candidate["symbol"], tech_snapshot.get("setup"),
                    tech_snapshot.get("tech_score"), reason, retry_text,
                )
                try:
                    self.record_rejected_setup(candidate)
                except Exception:
                    pass

        except Exception as exc:
            with self.state_lock:
                self.final_review_state["decision"] = "WAIT"
                self.final_review_state["error"] = f"{type(exc).__name__}: {exc}"
                waits = int(self.final_review_state.get("wait_retries") or 0) + 1
                self.final_review_state["wait_retries"] = waits
                self.final_review_state["next_retry_ts"] = (
                    time.time() + LUNA_WAIT_REVIEW_DELAY_SECONDS
                    if waits <= LUNA_WAIT_MAX_RECHECKS else 0.0
                )
            # External/model connectivity errors are export-log diagnostics only.
            log.warning(
                "LUNA REVIEW API ISSUE (LOG ONLY) | %s: %s",
                type(exc).__name__, short_reason(exc, 180),
            )
            issue = self._classify_transport_issue(exc)
            if issue in ("DNS", "TIMEOUT", "CONNECTION", "RATE_LIMIT"):
                self._record_transport_issue("openai_final_review", issue, exc, is_history=False)
        finally:
            with self.state_lock:
                self.final_review_state["running"] = False

    # ----------------------------------------------------------------------
    # Signal / TRANSIT
    # ----------------------------------------------------------------------

    def send_signal_event_once(self, signal_no, event_type, text):
        """Send one lifecycle event at most once per signal.

        If a local Android notification temporarily fails, the reservation is released so a
        later retry can still deliver the event.
        """
        key = (safe_int(signal_no, -1), str(event_type).upper())
        with self.state_lock:
            if key in self.signal_events_sent:
                return False
            self.signal_events_sent.add(key)
        ok = local_notify(text)
        if not ok:
            with self.state_lock:
                self.signal_events_sent.discard(key)
        return ok

    def _current_option_snapshot(self, token):
        with self.state_lock:
            d = dict(self.latest_options.get(token, {}))
        return d

    def _active_transit_snapshots(self):
        """Return independent active TRANSIT snapshots, newest signal first."""
        with self.state_lock:
            rows = [dict(v) for v in self.active_transits.values()]
        rows.sort(key=lambda x: safe_int(x.get("signal_no"), 0), reverse=True)
        return rows

    def _pending_warning_snapshot(self):
        """Return the warning currently exposed to the APK ACCEPT button.

        The existing APK has one ACCEPT button. With multiple active TRANSITs we expose
        one pending warning at a time: IMMEDIATE EXIT first, then the oldest pending
        TRANSIT alert. After it is accepted/resolved, the next warning is exposed.
        """
        with self.state_lock:
            pending = [
                dict(v) for v in self.active_transits.values()
                if str(v.get("pending_warning_type") or "").strip()
            ]
        if not pending:
            return None
        def key(row):
            typ = str(row.get("pending_warning_type") or "").upper()
            priority = 0 if typ == "IMMEDIATE_EXIT" else 1
            return (priority, safe_int(row.get("signal_no"), 0))
        pending.sort(key=key)
        return pending[0]

    def issue_signal(self, candidate, confidence, reason, tech, fund):
        # Final deterministic re-check immediately before creating TRANSIT. Luna review
        # can take several seconds, so option momentum may have changed since selection.
        candidate = dict(candidate)
        candidate["premium_momentum_10s"] = self.premium_momentum(candidate["token"], 10)
        candidate["premium_momentum_30s"] = self.premium_momentum(candidate["token"], 30)
        timing_ok, timing_reason = self.entry_timing_gate(candidate, tech)
        cooldown_ok, cooldown_reason = self.reentry_cooldown_gate(candidate.get("side"))
        if not timing_ok or not cooldown_ok:
            hold_reason = timing_reason or cooldown_reason
            log.info("POST-REVIEW ENTRY HOLD | %s | %s", candidate.get("symbol"), hold_reason)
            self._set_timing_wait_after_review(hold_reason)
            return

        setup_sig = self.setup_signature(tech, candidate.get("side"))
        with self.state_lock:
            if setup_sig in self.issued_setup_signatures:
                log.info("V%s re-arm blocked duplicate strategy event: %s", VERSION, setup_sig)
                return
        current = self._current_option_snapshot(candidate["token"])
        current_ask = safe_float(current.get("ask"))
        if current_ask is None or current_ask <= 0:
            return
        initial_ask = float(candidate["ask"])
        drift_pct = (current_ask - initial_ask) / initial_ask * 100 if initial_ask else 0
        if drift_pct > MAX_ENTRY_DRIFT_PCT:
            local_notify(f"🟠 MISSED ENTRY\n{contract_label(candidate)}\nReason: Premium ran away")
            return

        lot = int(candidate["lot"])
        selected_lots = current_lots_per_signal()
        quantity = max(1, lot * selected_lots)
        entry = tick_round(current_ask)
        rupee_cap_points = MAX_REFERENCE_RISK_RUPEES / quantity
        premium_pct_cap_points = max(0.05, entry * OPTION_RISK_MAX_ENTRY_PCT / 100.0)
        max_risk_unit = min(OPTION_RISK_MAX_POINTS, rupee_cap_points, premium_pct_cap_points)
        min_risk_unit = min(OPTION_RISK_MIN_POINTS, max_risk_unit)
        atr = safe_float(tech.get("atr14"), 0.0) or 0.0
        delta = abs(safe_float(candidate.get("delta"), 0.5) or 0.5)
        atr_option_risk = atr * max(0.25, delta) * 0.40
        premium_range_60s = self.premium_volatility_range(candidate["token"], OPTION_VOL_WINDOW_SECONDS)
        volatility_risk = premium_range_60s * OPTION_VOL_RANGE_MULTIPLIER
        risk_per_unit = max(min_risk_unit, atr_option_risk, volatility_risk)
        risk_per_unit = min(max_risk_unit, risk_per_unit)
        risk_per_unit = max(0.05, math.floor(risk_per_unit / 0.05) * 0.05)
        adx = safe_float(tech.get("adx14"), 0.0) or 0.0
        # Preserve positive reward/risk when we give the premium more breathing room.
        target_r = 1.50 if adx >= 30 else 1.40 if adx >= 25 else 1.30
        sl = tick_round(max(0.05, entry - risk_per_unit))
        target = tick_round(entry + target_r * risk_per_unit)
        money = one_lot_money(entry, target, sl, lot, lots=selected_lots)

        # SHADOW ONLY: calculate what the adaptive learner currently thinks.
        # These values are logged after Luna approval and never feed back into
        # the live V3.4 signal gate.
        shadow = self._shadow_signal_snapshot(candidate, tech, fund, risk_per_unit)

        with self.state_lock:
            self.signal_counter += 1
            signal_no = self.signal_counter
            spot = float(self.nifty_live)
            fvwap = safe_float(self.futures_vwap)
            fltp = safe_float(self.futures_ltp)

        transit = {
            "signal_no": signal_no,
            "signal_uid": f"{now_ist().date().strftime('%Y%m%d')}-{signal_no:03d}-{now_ist().strftime('%H%M%S')}",
            "legacy_signal_no": "",
            "date": now_ist().date().isoformat(), "entry_time": now_ist().isoformat(),
            "index_root": self.index_root, "expiry": self.nearest_expiry.date().isoformat(),
            "symbol": candidate["symbol"], "token": candidate["token"], "side": candidate["side"],
            "strike": candidate["strike"], "type": candidate["type"], "lot": lot,
            "lots": money["lots"], "quantity": money["quantity"], "spot_at_entry": spot,
            "entry": entry, "sl": sl, "target": target, "risk_per_unit": risk_per_unit, "target_r": target_r,
            "amount_used": money["amount_used"],
            "target_profit_gross": money["target_profit_gross"],
            "sl_loss_gross": money["sl_loss_gross"],
            "brokerage_buy": money["brokerage_buy"],
            "brokerage_exit": money["brokerage_exit"],
            "brokerage_round_trip": money["brokerage_round_trip"],
            "brokerage_only": money["brokerage_only"],
            "stt": money["stt"],
            "exchange_transaction_charges": money["exchange_transaction_charges"],
            "stamp_duty": money["stamp_duty"],
            "sebi_charges": money["sebi_charges"],
            "gst": money["gst"],
            "total_charges": money["total_charges"],
            "target_total_charges": money["target_total_charges"],
            "sl_total_charges": money["sl_total_charges"],
            "charge_model": money["charge_model"],
            "target_profit_after_brokerage": money["target_profit_after_brokerage"],
            "sl_loss_after_brokerage": money["sl_loss_after_brokerage"],
            "money_model": money["money_model"],
            "paper_exit_price": "", "observed_exit_ltp": "",
            "gross_pnl_rupees": "", "total_brokerage_rupees": "", "net_pnl_after_brokerage": "",
            "premium_range_60s_entry": round(premium_range_60s, 2),
            "risk_model": "VOL_ADAPTIVE_7_12_MAX_0.8PCT_CAP10PCT_PREMIUM",
            "entry_timing_gate": "PASS", "reentry_gate": "PASS",
            "option_score": candidate["score"], "final_confidence": confidence, "final_reason": short_reason(reason),
            "fundamental_filter": fund.get("filter", "UNKNOWN"), "fundamental_support": candidate.get("fundamental_support",0),
            "news_risk": fund.get("news_risk", "UNKNOWN"), "technical_bias": tech.get("bias","UNKNOWN"),
            "technical_setup": tech.get("setup","NONE"), "technical_score": tech.get("tech_score",0),
            "setup_grade": tech.get("setup_grade","NONE"), "combined_score": candidate.get("combined_score",0),
            "strategy_event_time": tech.get("strategy_event_time") or tech.get("candle_time"),
            "strategy_id": tech.get("strategy_id", ""),
            "strategy_short_name": tech.get("strategy_short_name", ""),
            "strategy_status": tech.get("strategy_status", ""),
            "strategy_reason_entry": tech.get("strategy_reason", ""),
            "sweep_price_entry": tech.get("sweep_price", ""),
            "sweep_time_entry": tech.get("sweep_time", ""),
            "htf_fvg_lower_entry": tech.get("htf_fvg_lower", ""),
            "htf_fvg_upper_entry": tech.get("htf_fvg_upper", ""),
            "htf_fvg_time_entry": tech.get("htf_fvg_time", ""),
            "ltf_fvg_lower_entry": tech.get("ltf_fvg_lower", ""),
            "ltf_fvg_upper_entry": tech.get("ltf_fvg_upper", ""),
            "ltf_fvg_time_entry": tech.get("ltf_fvg_time", ""),
            "ifvg_confirmation_time_entry": tech.get("ifvg_confirmation_time", ""),
            "cisd_reference_open_entry": tech.get("cisd_reference_open", ""),
            "cisd_reference_time_entry": tech.get("cisd_reference_time", ""),
            "cisd_confirmation_time_entry": tech.get("cisd_confirmation_time", ""),
            "setup_invalidation_level": tech.get("setup_invalidation_level", ""),
            "target_liquidity": tech.get("target_liquidity", ""),
            "target_liquidity_time": tech.get("target_liquidity_time", ""),
            "target_liquidity_type": tech.get("target_liquidity_type", ""),
            "amd_accumulation_start": tech.get("amd_accumulation_start", ""),
            "amd_accumulation_end": tech.get("amd_accumulation_end", ""),
            "amd_range_high": tech.get("amd_range_high", ""),
            "amd_range_low": tech.get("amd_range_low", ""),
            "amd_poc_price": tech.get("amd_poc_price", ""),
            "amd_profile_total_volume": tech.get("amd_profile_total_volume", ""),
            "amd_profile_bin_size": tech.get("amd_profile_bin_size", ""),
            "amd_profile_source": tech.get("amd_profile_source", ""),
            "amd_profile_distribution": tech.get("amd_profile_distribution", ""),
            "amd_futures_poc_price": tech.get("amd_futures_poc_price", ""),
            "amd_futures_index_basis": tech.get("amd_futures_index_basis", ""),
            "amd_manipulation_price": tech.get("amd_manipulation_price", ""),
            "amd_manipulation_time": tech.get("amd_manipulation_time", ""),
            "amd_poc_cross_time": tech.get("amd_poc_cross_time", ""),
            "amd_poc_retest_time": tech.get("amd_poc_retest_time", ""),
            "all_valid_setups_entry": json.dumps(tech.get("setup_candidates") or [], separators=(",", ":"), default=str),
            "candlestick_primary_entry": tech.get("candlestick_primary", "NONE"),
            "candlestick_family_entry": tech.get("candlestick_family", "NONE"),
            "candlestick_direction_entry": tech.get("candlestick_direction", "NEUTRAL"),
            "candlestick_bias_entry": tech.get("candlestick_bias", "NEUTRAL"),
            "candlestick_bonus_entry": safe_float(tech.get("candlestick_bonus"), 0.0) or 0.0,
            "candlestick_patterns_entry": json.dumps(tech.get("candlestick_patterns") or [], separators=(",", ":"), default=str),
            "candlestick_conflict_entry": bool(tech.get("candlestick_conflict", False)),
            "weapon15_time": tech.get("weapon15_time"), "weapon15_ema9": tech.get("weapon15_ema9"),
            "weapon15_macd": tech.get("weapon15_macd"), "weapon15_macd_signal": tech.get("weapon15_macd_signal"),
            "weapon15_rsi14": tech.get("weapon15_rsi14"),
            "liquidity_event_entry": tech.get("liquidity_event"), "liquidity_level_entry": tech.get("liquidity_level"),
            "fvg_event_entry": tech.get("fvg_event"), "fvg_zone_low_entry": tech.get("fvg_zone_low"),
            "fvg_zone_high_entry": tech.get("fvg_zone_high"),
            "vwap_event_futures_ltp": tech.get("vwap_event_futures_ltp"),
            "vwap_event_futures_vwap": tech.get("vwap_event_futures_vwap"),
            "adx14": tech.get("adx14"), "plus_di14": tech.get("plus_di14"), "minus_di14": tech.get("minus_di14"),
            "atr14": tech.get("atr14"), "ema20_slope": tech.get("ema20_slope"), "ema50_slope": tech.get("ema50_slope"),
            "or_status_entry": tech.get("or_status"), "futures_ltp_entry": fltp, "futures_vwap_entry": fvwap,
            "premium_momentum_10s_entry": candidate.get("premium_momentum_10s"),
            "premium_momentum_30s_entry": candidate.get("premium_momentum_30s"),
            "status": "TRANSIT", "last_ltp": candidate.get("ltp",entry), "mfe": 0.0, "mae": 0.0,
            "mfe_time": "", "mae_time": "", "profit_protect_armed": False,
            "transit_alert_sent": False, "guardian_checks": 0, "guardian_last_check_ts": 0.0,
            "guardian_action": "NOT CHECKED", "guardian_confidence": 0, "guardian_risk": "UNKNOWN",
            "guardian_reason": "", "guardian_exit_price": "", "guardian_exit_time": "",
            "pending_warning_type": "", "pending_warning_reason": "", "pending_warning_time": "",
            "pending_warning_price": "", "pending_warning_confidence": 0, "pending_warning_risk": "",
            "warning_accept_type": "", "warning_accept_price": "", "warning_accept_time": "",
            "warning_accept_engine_ltp": "", "warning_accept_reason": "", "transit_exit_line": "",
            "warning_decline_type": "", "warning_decline_price": "", "warning_decline_time": "",
            "warning_decline_reason": "", "warning_decline_until_ts": 0.0,
            "manual_exit_price": "", "manual_exit_time": "", "manual_exit_reason": "",
            "silent_monitor_active": False, "silent_monitor_start_time": "",
            "silent_monitor_start_price": "", "silent_monitor_last_ltp": "",
            "silent_monitor_outcome": "", "silent_monitor_outcome_time": "",
            "silent_monitor_hit_price": "", "silent_monitor_mfe_after_accept": 0.0,
            "silent_monitor_mae_after_accept": 0.0,
            "outcome": "", "outcome_time": "",
            "shadow_strategy": shadow["strategy"],
            "shadow_factor_scores": json.dumps(shadow["factor_scores"], separators=(",", ":"), sort_keys=True),
            "shadow_base_weights": json.dumps(shadow["base_weights"], separators=(",", ":"), sort_keys=True),
            "shadow_suggested_weights_entry": json.dumps(shadow["suggested_weights"], separators=(",", ":"), sort_keys=True),
            "shadow_base_score": shadow["base_score"],
            "shadow_adaptive_score": shadow["adaptive_score"],
            "shadow_outcome_r": "",
            "shadow_learning_recorded": False,
            "shadow_suggested_weights_after": "",
        }
        with self.state_lock:
            self.active_transits[signal_no] = transit
            self.signal_history.append(transit)
            self.last_issued_setup_signature = setup_sig
            self.issued_setup_signatures.add(setup_sig)
        try:
            if self.technical is not None:
                self.technical.mark_sweep_ifvg_complete(tech, candidate, entry, signal_no)
                self.technical.mark_amd_poc_complete(tech, candidate, entry, signal_no, underlying_entry_price=spot)
        except Exception as exc:
            log.warning("Experimental strategy completion log skipped: %s", short_reason(exc, 100))
        self.save_signal_log()
        self.send_signal_event_once(
            signal_no, "SIGNAL",
            f"🟢 SIGNAL #{signal_no}\n{contract_label(transit)} | {money['lots']} lot(s) (Qty {money['quantity']})\n"
            f"Option Type: {str(transit.get('side') or candidate.get('side') or '--').upper()}\n"
            f"Entry: {entry:.2f} / Amt used: {rupee(money['amount_used'])}\n"
            f"Target: {target:.2f} / Profit: {rupee(money['target_profit_gross'])}\n"
            f"SL: {sl:.2f} / Loss: {rupee(money['sl_loss_gross'])}\n"
            f"Brokerage/Charges: {rupee(money['total_charges'])} (Brokerage {rupee(money['brokerage_only'])})\n"
            f"Reason: {short_reason(reason)}"
        )
    def _apply_terminal_money(self, transit, outcome, observed_ltp=None):
        """Finalize selected-lot paper P/L for a resolved signal.

        TARGET/SL use their trigger prices as the paper fill; Guardian/manual/session-close
        use the observed/locked exit LTP. This keeps the research accounting deterministic
        while preserving the observed market LTP separately.
        """
        outcome_u = str(outcome or "").upper()
        entry = safe_float(transit.get("entry"), 0.0) or 0.0
        target = safe_float(transit.get("target"), entry) or entry
        sl = safe_float(transit.get("sl"), entry) or entry
        lot = max(1, safe_int(transit.get("lot"), 1))
        obs = safe_float(observed_ltp, safe_float(transit.get("last_ltp"), entry))
        if outcome_u == "TARGET HIT":
            exit_px = target
        elif outcome_u == "SL HIT":
            exit_px = sl
        elif outcome_u == "IMMEDIATE EXIT":
            exit_px = safe_float(transit.get("guardian_exit_price"), obs)
        else:
            exit_px = obs
        if exit_px is None:
            exit_px = entry
        money = one_lot_money(entry, target, sl, lot, exit_price=exit_px, lots=safe_int(transit.get("lots"), 1))
        transit.update(money)
        transit["observed_exit_ltp"] = round(float(obs), 2) if obs is not None else ""
        return money

    def _money_result_line(self, transit):
        gross = safe_float(transit.get("gross_pnl_rupees"), 0.0) or 0.0
        net = safe_float(transit.get("net_pnl_after_brokerage"), 0.0) or 0.0
        brokerage = safe_float(transit.get("total_brokerage_rupees"), 0.0) or 0.0
        return f"Gross P/L: {rupee(gross)} | Brokerage/Charges: {rupee(brokerage)} | Net: {rupee(net)}"

    def guardian_objective_state(self, transit):
        token = transit["token"]
        d = self._current_option_snapshot(token)
        ltp = safe_float(d.get("ltp"), safe_float(transit.get("last_ltp"), 0.0))
        with self.state_lock:
            spot = float(self.nifty_live or 0.0)
            tech = dict(self.technical_state)
            fund = dict(self.fundamental_state)
            greek = dict(self.greeks_state.get("data", {}).get((transit["strike"], transit["side"]), {}))
            fvwap = safe_float(self.futures_vwap)
            fltp = safe_float(self.futures_ltp)

        entry, sl, target = float(transit["entry"]), float(transit["sl"]), float(transit["target"])
        risk_distance = max(0.05, entry - sl)
        move = ltp - entry
        mfe, mae = float(transit.get("mfe",0.0)), float(transit.get("mae",0.0))
        giveback = max(0.0, mfe - move)
        premium_mom_10s = self.premium_momentum(token, 10)
        premium_mom_30s = self.premium_momentum(token, 30)
        side = str(transit.get("side","")).upper()
        ema20 = safe_float(tech.get("ema20"))
        momentum = str(tech.get("momentum","UNKNOWN")).upper()
        structure = str(tech.get("structure","UNKNOWN")).upper()
        plus_di = safe_float(tech.get("plus_di14"),0) or 0
        minus_di = safe_float(tech.get("minus_di14"),0) or 0
        adx = safe_float(tech.get("adx14"),0) or 0

        technical_against = False
        di_against = False
        futures_against = False
        if side == "PE":
            technical_against = momentum == "UP" or (ema20 is not None and spot > ema20) or "HIGHER HIGH / HIGHER LOW" in structure
            di_against = plus_di >= minus_di
            futures_against = fltp is not None and fvwap is not None and fltp >= fvwap
        elif side == "CE":
            technical_against = momentum == "DOWN" or (ema20 is not None and spot < ema20) or "LOWER HIGH / LOWER LOW" in structure
            di_against = minus_di >= plus_di
            futures_against = fltp is not None and fvwap is not None and fltp <= fvwap

        try:
            entered = datetime.fromisoformat(str(transit["entry_time"]))
            if entered.tzinfo is None: entered = entered.replace(tzinfo=IST)
            age = (now_ist() - entered.astimezone(IST)).total_seconds()
        except Exception:
            age = 0

        near_sl = move <= -0.45 * risk_distance
        profit_armed = mfe >= 0.60 * risk_distance
        near_target_then_reversal = mfe >= 0.90 * risk_distance and giveback >= 0.30 * risk_distance
        profit_giveback = profit_armed and giveback >= max(0.30*risk_distance, 0.50*max(mfe,0.01))
        adverse_premium = premium_mom_10s <= -0.08*risk_distance or premium_mom_30s < -0.12*risk_distance
        time_stall = age >= TRANSIT_TIME_STOP_SECONDS and mfe < 0.25*risk_distance and move <= 0
        hard_news_block = str(fund.get("risk_gate","OPEN")).upper() == "HARD BLOCK"
        weak_trend = adx < max(17.0, MIN_ADX-2)

        flags=[]
        if technical_against: flags.append("technical reversal")
        if di_against: flags.append("DI reversed")
        if futures_against: flags.append("futures VWAP reversed")
        if near_sl: flags.append("moving toward SL")
        if profit_giveback: flags.append("profit giving back")
        if near_target_then_reversal: flags.append("near target reversal")
        if adverse_premium: flags.append("premium momentum weak")
        if time_stall: flags.append("trade stalled")
        if hard_news_block: flags.append("news hard block")
        if weak_trend: flags.append("trend strength faded")

        return {
            "spot":round(spot,2), "ltp":round(ltp,2), "entry":entry, "sl":sl, "target":target,
            "move":round(move,2), "mfe":round(mfe,2), "mae":round(mae,2), "giveback":round(giveback,2),
            "premium_momentum_10s":round(premium_mom_10s,2), "premium_momentum_30s":round(premium_mom_30s,2),
            "age_seconds":int(age), "profit_protect_armed":profit_armed,
            "technical":{"bias":tech.get("bias"),"setup":tech.get("setup"),"trend":tech.get("trend"),"momentum":tech.get("momentum"),"structure":tech.get("structure"),"adx14":tech.get("adx14"),"plus_di14":tech.get("plus_di14"),"minus_di14":tech.get("minus_di14"),"atr14":tech.get("atr14")},
            "futures":{"ltp":fltp,"vwap":fvwap},
            "fundamental":{"filter":fund.get("filter"),"risk_gate":fund.get("risk_gate"),"news_risk":fund.get("news_risk")},
            "option":{"bid":d.get("bid"),"ask":d.get("ask"),"delta":greek.get("delta"),"iv":greek.get("iv"),"theta":greek.get("theta")},
            "objective_flags":flags,
        }
    def transit_guardian_prompt(self, transit, state):
        return f"""
You are GPT-5.6 Luna guarding an active {self.index_root} option signal.
No broker order is placed.
HOLD = still healthy. WATCH = deterioration worth one amber warning.
EXIT_EARLY = evidence materially invalidates the setup or meaningful profit is being lost.
Do not predict certainty. Prefer capital/profit protection only when evidence is coherent.
SIGNAL: {json.dumps({k:transit.get(k) for k in ['signal_no','strike','side','entry','sl','target','technical_setup','final_confidence']})}
STATE: {json.dumps(state)}
Return JSON only:
{{"action":"HOLD"|"WATCH"|"EXIT_EARLY","confidence":0-100,"risk_level":"LOW"|"MEDIUM"|"HIGH","reason":"3-8 words only"}}
"""
    def transit_guardian_worker(self, signal_no):
        signal_no = safe_int(signal_no, -1)
        with self.state_lock:
            if signal_no in self.guardian_running_signals:
                return
            transit = self.active_transits.get(signal_no)
            if transit is None:
                return
            self.guardian_running_signals.add(signal_no)
            snapshot = dict(transit)
        try:
            state = self.guardian_objective_state(snapshot)
            response = self.openai.responses.create(
                model=BACKGROUND_MODEL,
                reasoning={"effort":"low"},
                input=self.transit_guardian_prompt(snapshot, state),
            )
            parsed = self.extract_json(response.output_text)
            if not parsed:
                raise RuntimeError("Luna Guardian returned invalid JSON")
            action = str(parsed.get("action","HOLD")).upper()
            if action not in ("HOLD","WATCH","EXIT_EARLY"):
                action = "HOLD"
            confidence = max(0, min(100, safe_int(parsed.get("confidence",0))))
            risk_level = str(parsed.get("risk_level","UNKNOWN")).upper()
            reason = short_reason(parsed.get("reason",""),64)
            flags = list(state.get("objective_flags") or [])
            if action == "EXIT_EARLY" and not flags:
                action = "WATCH"
                reason = "No objective deterioration"

            warning = None
            warning_event = None
            with self.state_lock:
                transit = self.active_transits.get(signal_no)
                if transit is None:
                    return
                transit["guardian_checks"] = safe_int(transit.get("guardian_checks"),0) + 1
                transit["guardian_last_check_ts"] = time.time()
                transit["guardian_action"] = action
                transit["guardian_confidence"] = confidence
                transit["guardian_risk"] = risk_level
                transit["guardian_reason"] = reason
                current = float(state["ltp"])
                pending_now = str(transit.get("pending_warning_type") or "").upper()

                decline_until = safe_float(transit.get("warning_decline_until_ts"), 0.0) or 0.0
                immediate_decline_cooldown = time.time() < float(decline_until)

                if (
                    action == "EXIT_EARLY"
                    and confidence >= TRANSIT_GUARDIAN_EXIT_CONFIDENCE
                    and not immediate_decline_cooldown
                ):
                    transit["pending_warning_type"] = "IMMEDIATE_EXIT"
                    transit["pending_warning_reason"] = reason
                    transit["pending_warning_time"] = now_ist().isoformat()
                    transit["pending_warning_price"] = current
                    transit["pending_warning_confidence"] = confidence
                    transit["pending_warning_risk"] = risk_level
                    warning = dict(transit)
                    warning_event = "IMMEDIATE_EXIT_WARNING"
                elif (
                    action in ("WATCH","EXIT_EARLY")
                    and confidence >= TRANSIT_GUARDIAN_WARNING_CONFIDENCE
                    and not transit.get("transit_alert_sent")
                    and pending_now != "IMMEDIATE_EXIT"
                ):
                    transit["transit_alert_sent"] = True
                    transit["pending_warning_type"] = "TRANSIT_ALERT"
                    transit["pending_warning_reason"] = reason
                    transit["pending_warning_time"] = now_ist().isoformat()
                    transit["pending_warning_price"] = current
                    transit["pending_warning_confidence"] = confidence
                    transit["pending_warning_risk"] = risk_level
                    warning = dict(transit)
                    warning_event = "TRANSIT_ALERT"

            if warning and warning_event == "IMMEDIATE_EXIT_WARNING":
                self.send_signal_event_once(
                    warning["signal_no"], warning_event,
                    f"🔴 IMMEDIATE EXIT WARNING #{warning['signal_no']}\n{contract_label(warning)}\nCurrent: {float(state['ltp']):.2f}\nEntry: {float(warning['entry']):.2f}\nT: {float(warning['target']):.2f}\nSL: {float(warning['sl']):.2f}\nAUTO EXIT enabled: this warning will be accepted automatically at the latest premium.\nReason: {reason}"
                )
            elif warning:
                self.send_signal_event_once(
                    warning["signal_no"], "TRANSIT_ALERT",
                    f"🟠 TRANSIT ALERT #{warning['signal_no']}\n{contract_label(warning)}\nCurrent: {float(state['ltp']):.2f}\nEntry: {float(warning['entry']):.2f}\nT: {float(warning['target']):.2f}\nSL: {float(warning['sl']):.2f}\nAUTO EXIT enabled: this warning will be accepted automatically at the latest premium.\nReason: {reason}"
                )
            # V8.0.1 TEMP AUTO-ACCEPT:
            # Show the normal warning first, then feed it into the existing accept
            # settlement path. This keeps all established accounting/silent-monitor logic.
            if warning and AUTO_ACCEPT_ALL_TRANSIT_WARNINGS:
                try:
                    atomic_json_write(WARNING_ACCEPT_FILE, {
                        "signal_no": safe_int(warning.get("signal_no"), -1),
                        "warning_type": str(warning.get("pending_warning_type") or "").upper(),
                        "premium": safe_float(state.get("ltp")),
                        "source": "V8.0.1_AUTO_ACCEPT",
                        "requested_at": now_ist().isoformat(),
                    })
                    self._consume_warning_accept_request()
                except Exception as auto_exc:
                    log.warning(
                        "AUTO TRANSIT WARNING ACCEPT failed #%s: %s",
                        safe_int(warning.get("signal_no"), -1),
                        short_reason(auto_exc, 100),
                    )
            self.save_signal_log()
        except Exception as exc:
            self.health_alert("guardian_error", f"⚠️ GUARDIAN ERROR\n{short_reason(exc,80)}", cooldown=120)
        finally:
            with self.state_lock:
                self.guardian_running_signals.discard(signal_no)

    def _consume_warning_accept_request(self):
        """Resolve only the requested pending warning; other TRANSITs keep running."""
        try:
            if not WARNING_ACCEPT_FILE.exists():
                return False
            try:
                raw = WARNING_ACCEPT_FILE.read_text(encoding="utf-8").strip()
            finally:
                try:
                    WARNING_ACCEPT_FILE.unlink(missing_ok=True)
                except Exception:
                    pass
            if not raw:
                return False
            try:
                req = json.loads(raw)
                if not isinstance(req, dict):
                    req = {}
            except Exception:
                req = {}

            requested_no = safe_int(req.get("signal_no"), -1)
            with self.state_lock:
                transit = self.active_transits.get(requested_no) if requested_no > 0 else None
                if transit is None:
                    # Backward compatibility with an older host that omitted signal_no.
                    pending = [
                        v for v in self.active_transits.values()
                        if str(v.get("pending_warning_type") or "").strip()
                    ]
                    if not pending:
                        return False
                    pending.sort(
                        key=lambda v: (
                            0 if str(v.get("pending_warning_type") or "").upper() == "IMMEDIATE_EXIT" else 1,
                            safe_int(v.get("signal_no"), 0),
                        )
                    )
                    transit = pending[0]
                signal_no = safe_int(transit.get("signal_no"), -1)
                pending_type = str(transit.get("pending_warning_type") or "").upper().strip()
                pending_reason = str(
                    transit.get("pending_warning_reason") or transit.get("guardian_reason") or ""
                ).strip()
                if not pending_type:
                    return False
                req_type = str(req.get("warning_type") or pending_type).upper().strip()
                if req_type != pending_type:
                    log.info(
                        "WARNING ACCEPT ignored | active #%s %s | request #%s %s",
                        signal_no, pending_type, requested_no, req_type,
                    )
                    return False
                token = str(transit.get("token") or "")

            snap = self._current_option_snapshot(token)
            engine_ltp = safe_float(snap.get("ltp"), safe_float(transit.get("last_ltp")))
            accepted_px = safe_float(req.get("premium"))
            if accepted_px is None or accepted_px <= 0:
                accepted_px = engine_ltp
            if accepted_px is None or accepted_px <= 0:
                log.warning("WARNING ACCEPT ignored: no valid premium for signal #%s", signal_no)
                return False
            accepted_px = tick_round(float(accepted_px))
            accepted_at = now_ist().isoformat()

            terminal = None
            with self.state_lock:
                transit = self.active_transits.get(signal_no)
                if transit is None:
                    return False
                current_pending = str(transit.get("pending_warning_type") or "").upper().strip()
                if current_pending != pending_type:
                    return False
                transit["warning_accept_type"] = pending_type
                transit["warning_accept_price"] = accepted_px
                transit["warning_accept_time"] = accepted_at
                transit["warning_accept_engine_ltp"] = (
                    round(float(engine_ltp), 2) if engine_ltp is not None else ""
                )
                transit["warning_accept_reason"] = pending_reason
                transit["transit_exit_line"] = f"Transit Exit: -{accepted_px:.2f}" if pending_type == "TRANSIT_ALERT" else ""
                transit["guardian_exit_price"] = accepted_px
                transit["guardian_exit_time"] = accepted_at
                transit["pending_warning_type"] = ""
                transit["outcome"] = "IMMEDIATE EXIT"
                transit["outcome_time"] = accepted_at
                self._apply_terminal_money(transit, "IMMEDIATE EXIT", accepted_px)

                # V4.4.1 SILENT POST-EXIT MONITOR:
                # The accepted premium settles the paper trade permanently.  Keep the
                # same signal in a separate research-only monitor until its ORIGINAL
                # target or SL is reached.  This never changes outcome/P&L and never
                # triggers Guardian/notifications.
                transit["silent_monitor_active"] = True
                transit["silent_monitor_start_time"] = accepted_at
                transit["silent_monitor_start_price"] = accepted_px
                transit["silent_monitor_last_ltp"] = accepted_px
                transit["silent_monitor_outcome"] = ""
                transit["silent_monitor_outcome_time"] = ""
                transit["silent_monitor_hit_price"] = ""
                transit["silent_monitor_mfe_after_accept"] = 0.0
                transit["silent_monitor_mae_after_accept"] = 0.0
                self.silent_monitors[signal_no] = transit

                terminal = dict(transit)
                self.active_transits.pop(signal_no, None)

            self.record_terminal_risk_state(terminal)
            if pending_type == "TRANSIT_ALERT":
                accepted_text = (
                    f"🔵 TRANSIT HIT #{signal_no}\n{contract_label(terminal)}\n"
                    f"Transit Hit: {accepted_px:.2f}\n"
                    f"Transit Exit: -{accepted_px:.2f}\n"
                    f"{self._money_result_line(terminal)}"
                )
            else:
                accepted_text = (
                    f"🔵 IMMEDIATE EXIT ACCEPTED #{signal_no}\n{contract_label(terminal)} | {safe_int(terminal.get('lots'),1)} lot(s) (Qty {safe_int(terminal.get('quantity'), safe_int(terminal.get('lot'),1))})\n"
                    f"Premium locked: {accepted_px:.2f}\n{self._money_result_line(terminal)}\nReason: {short_reason(pending_reason,64)}"
                )
            self.send_signal_event_once(signal_no, "WARNING_ACCEPTED", accepted_text)
            self.save_signal_log()
            try:
                self.write_app_ui(None, market_state="LIVE")
            except Exception:
                pass
            log.info(
                "WARNING ACCEPTED | #%s | %s | premium %.2f | engine LTP %s",
                signal_no, pending_type, accepted_px,
                f"{engine_ltp:.2f}" if engine_ltp is not None else "--",
            )
            return True
        except Exception as exc:
            log.warning("WARNING ACCEPT failed: %s", short_reason(exc, 100))
            return False

    def _consume_warning_decline_request(self):
        """Dismiss only the requested warning; the TRANSIT remains active.

        TRANSIT_ALERT is dismissed for that signal (the existing transit_alert_sent flag
        prevents the same informational warning from repeating). An IMMEDIATE_EXIT
        decline suppresses the same Guardian exit warning for 60 seconds; if risk is
        still present after that cooldown, Guardian may warn again.
        """
        try:
            if not WARNING_DECLINE_FILE.exists():
                return False
            try:
                raw = WARNING_DECLINE_FILE.read_text(encoding="utf-8").strip()
            finally:
                try:
                    WARNING_DECLINE_FILE.unlink(missing_ok=True)
                except Exception:
                    pass
            if not raw:
                return False
            try:
                req = json.loads(raw)
                if not isinstance(req, dict):
                    req = {}
            except Exception:
                req = {}

            requested_no = safe_int(req.get("signal_no"), -1)
            with self.state_lock:
                transit = self.active_transits.get(requested_no) if requested_no > 0 else None
                if transit is None:
                    pending = [
                        v for v in self.active_transits.values()
                        if str(v.get("pending_warning_type") or "").strip()
                    ]
                    if not pending:
                        return False
                    pending.sort(
                        key=lambda v: (
                            0 if str(v.get("pending_warning_type") or "").upper() == "IMMEDIATE_EXIT" else 1,
                            safe_int(v.get("signal_no"), 0),
                        )
                    )
                    transit = pending[0]

                signal_no = safe_int(transit.get("signal_no"), -1)
                pending_type = str(transit.get("pending_warning_type") or "").upper().strip()
                pending_reason = str(
                    transit.get("pending_warning_reason") or transit.get("guardian_reason") or ""
                ).strip()
                if not pending_type:
                    return False
                req_type = str(req.get("warning_type") or pending_type).upper().strip()
                if req_type != pending_type:
                    log.info(
                        "WARNING DECLINE ignored | active #%s %s | request #%s %s",
                        signal_no, pending_type, requested_no, req_type,
                    )
                    return False
                token = str(transit.get("token") or "")

            snap = self._current_option_snapshot(token)
            engine_ltp = safe_float(snap.get("ltp"), safe_float(transit.get("last_ltp")))
            declined_px = safe_float(req.get("premium"), engine_ltp)
            if declined_px is not None and declined_px > 0:
                declined_px = tick_round(float(declined_px))
            else:
                declined_px = ""
            declined_at = now_ist().isoformat()

            snapshot = None
            with self.state_lock:
                transit = self.active_transits.get(signal_no)
                if transit is None:
                    return False
                current_pending = str(transit.get("pending_warning_type") or "").upper().strip()
                if current_pending != pending_type:
                    return False

                transit["warning_decline_type"] = pending_type
                transit["warning_decline_price"] = declined_px
                transit["warning_decline_time"] = declined_at
                transit["warning_decline_reason"] = pending_reason
                if pending_type == "IMMEDIATE_EXIT":
                    transit["warning_decline_until_ts"] = time.time() + 60.0

                transit["pending_warning_type"] = ""
                transit["pending_warning_reason"] = ""
                transit["pending_warning_time"] = ""
                transit["pending_warning_price"] = ""
                transit["pending_warning_confidence"] = 0
                transit["pending_warning_risk"] = ""
                snapshot = dict(transit)

            label = "IMMEDIATE EXIT" if pending_type == "IMMEDIATE_EXIT" else "TRANSIT WARNING"
            px_text = f"{float(declined_px):.2f}" if declined_px not in (None, "") else "--"
            self.send_signal_event_once(
                signal_no,
                f"WARNING_DECLINED_{pending_type}_{int(time.time())}",
                f"↩️ {label} DECLINED #{signal_no}\n{contract_label(snapshot)}\n"
                f"Premium at decline: {px_text}\nTRANSIT continues normally.\n"
                f"Reason: {short_reason(pending_reason,64)}"
            )
            self.save_signal_log()
            try:
                self.write_app_ui(None, market_state="LIVE")
            except Exception:
                pass
            log.info(
                "WARNING DECLINED | #%s | %s | premium %s | TRANSIT continues",
                signal_no, pending_type, px_text,
            )
            return True
        except Exception as exc:
            log.warning("WARNING DECLINE failed: %s", short_reason(exc, 100))
            return False

    def _manual_exit_one(self, signal_no, reason="MANUAL EXIT"):
        """Close one active paper TRANSIT at the engine's current live premium.

        This is an unconditional user override.  It does not ask Guardian/strategy
        logic for permission and it never affects any other active TRANSIT.
        """
        signal_no = safe_int(signal_no, -1)
        if signal_no <= 0:
            return False
        with self.state_lock:
            transit = self.active_transits.get(signal_no)
            if transit is None:
                return False
            token = str(transit.get("token") or "")
        snap = self._current_option_snapshot(token) if token else {}
        ltp = safe_float(snap.get("ltp"), safe_float(transit.get("last_ltp")))
        if ltp is None or ltp <= 0:
            log.warning("MANUAL EXIT ignored: no valid live premium for signal #%s", signal_no)
            return False
        exit_px = tick_round(float(ltp))
        exit_at = now_ist().isoformat()
        terminal = None
        with self.state_lock:
            transit = self.active_transits.get(signal_no)
            if transit is None:
                return False
            transit["last_ltp"] = exit_px
            transit["manual_exit_price"] = exit_px
            transit["manual_exit_time"] = exit_at
            transit["manual_exit_reason"] = str(reason or "MANUAL EXIT")
            transit["paper_exit_price"] = exit_px
            transit["pending_warning_type"] = ""
            transit["pending_warning_reason"] = ""
            transit["pending_warning_time"] = ""
            transit["pending_warning_price"] = ""
            transit["pending_warning_confidence"] = 0
            transit["pending_warning_risk"] = ""
            transit["outcome"] = "MANUAL EXIT"
            transit["outcome_time"] = exit_at
            self._apply_terminal_money(transit, "MANUAL EXIT", exit_px)
            terminal = dict(transit)
            self.active_transits.pop(signal_no, None)

        self.record_terminal_risk_state(terminal)
        self.send_signal_event_once(
            signal_no,
            f"MANUAL_EXIT_{int(time.time())}",
            f"⏹️ MANUAL EXIT #{signal_no}\n{contract_label(terminal)} | {safe_int(terminal.get('lots'),1)} lot(s) (Qty {safe_int(terminal.get('quantity'), safe_int(terminal.get('lot'),1))})\n"
            f"Premium locked: {exit_px:.2f}\n{self._money_result_line(terminal)}"
        )
        self.save_signal_log()
        try:
            self.write_app_ui(None, market_state="LIVE")
        except Exception:
            pass
        log.info("MANUAL EXIT | #%s | premium %.2f", signal_no, exit_px)
        return True

    def _consume_manual_exit_request(self):
        try:
            if not MANUAL_EXIT_FILE.exists():
                return False
            try:
                raw = MANUAL_EXIT_FILE.read_text(encoding="utf-8").strip()
            finally:
                try:
                    MANUAL_EXIT_FILE.unlink(missing_ok=True)
                except Exception:
                    pass
            if not raw:
                return False
            try:
                req = json.loads(raw)
                if not isinstance(req, dict):
                    req = {}
            except Exception:
                req = {}
            signal_no = safe_int(req.get("signal_no"), -1)
            return self._manual_exit_one(signal_no, "USER EXIT BUTTON")
        except Exception as exc:
            log.warning("MANUAL EXIT request failed: %s", short_reason(exc, 100))
            return False

    def _consume_close_all_transits_request(self):
        try:
            if not CLOSE_ALL_TRANSITS_FILE.exists():
                return False
            try:
                CLOSE_ALL_TRANSITS_FILE.unlink(missing_ok=True)
            except Exception:
                pass
            with self.state_lock:
                signal_nos = sorted(
                    [safe_int(x, -1) for x in self.active_transits.keys() if safe_int(x, -1) > 0]
                )
            if not signal_nos:
                return False
            closed = 0
            for signal_no in signal_nos:
                if self._manual_exit_one(signal_no, "USER CLOSE ALL"):
                    closed += 1
            if closed:
                local_notify(f"⏹️ CLOSE ALL COMPLETE\nClosed {closed} active TRANSIT{'s' if closed != 1 else ''} at live premium.")
            return bool(closed)
        except Exception as exc:
            log.warning("CLOSE ALL request failed: %s", short_reason(exc, 100))
            return False

    def maybe_start_transit_guardian(self):
        transits = self._active_transit_snapshots()
        if not transits:
            return
        with self.state_lock:
            running = set(self.guardian_running_signals)
        for transit in transits:
            signal_no = safe_int(transit.get("signal_no"), -1)
            if signal_no <= 0 or signal_no in running:
                continue
            try:
                entered = datetime.fromisoformat(str(transit["entry_time"]))
                if entered.tzinfo is None:
                    entered = entered.replace(tzinfo=IST)
                age = (now_ist() - entered.astimezone(IST)).total_seconds()
            except Exception:
                age = 9999
            if age < TRANSIT_GUARDIAN_MIN_AGE_SECONDS:
                continue
            state = self.guardian_objective_state(transit)
            last = safe_float(transit.get("guardian_last_check_ts"),0.0) or 0.0
            since = time.time() - last if last else 999999
            urgent = bool(state.get("objective_flags"))
            due = since >= 180
            fast_due = urgent and since >= TRANSIT_GUARDIAN_FAST_RECHECK_SECONDS
            if due or fast_due:
                threading.Thread(
                    target=self.transit_guardian_worker,
                    args=(signal_no,),
                    daemon=True,
                ).start()

    def monitor_transit(self):
        """Update/resolve every active TRANSIT independently."""
        with self.state_lock:
            work = [
                (safe_int(v.get("signal_no"), -1), str(v.get("token") or ""))
                for v in self.active_transits.values()
            ]
        if not work:
            return

        terminals = []
        for signal_no, token in work:
            if signal_no <= 0 or not token:
                continue
            d = self._current_option_snapshot(token)
            ltp = safe_float(d.get("ltp"))
            if ltp is None:
                continue
            terminal = None
            with self.state_lock:
                transit = self.active_transits.get(signal_no)
                if transit is None:
                    continue
                transit["last_ltp"] = ltp
                move = ltp - float(transit["entry"])
                if move > float(transit.get("mfe",0.0)):
                    transit["mfe"] = move
                    transit["mfe_time"] = now_ist().isoformat()
                if move < float(transit.get("mae",0.0)):
                    transit["mae"] = move
                    transit["mae_time"] = now_ist().isoformat()
                risk = max(0.05, float(transit["entry"]) - float(transit["sl"]))
                if transit["mfe"] >= 0.60 * risk:
                    transit["profit_protect_armed"] = True
                if ltp >= float(transit["target"]):
                    transit["outcome"] = "TARGET HIT"
                    transit["outcome_time"] = now_ist().isoformat()
                    self._apply_terminal_money(transit, "TARGET HIT", ltp)
                    terminal = dict(transit)
                    self.active_transits.pop(signal_no, None)
                elif ltp <= float(transit["sl"]):
                    transit["outcome"] = "SL HIT"
                    transit["outcome_time"] = now_ist().isoformat()
                    self._apply_terminal_money(transit, "SL HIT", ltp)
                    terminal = dict(transit)
                    self.active_transits.pop(signal_no, None)
            if terminal:
                terminals.append(terminal)

        for terminal in terminals:
            self.record_terminal_risk_state(terminal)
            if terminal["outcome"] == "TARGET HIT":
                self.send_signal_event_once(
                    terminal["signal_no"], "TARGET_HIT",
                    f"🟢 TARGET HIT #{terminal['signal_no']}\n{contract_label(terminal)} | {safe_int(terminal.get('lots'),1)} lot(s) (Qty {safe_int(terminal.get('quantity'), safe_int(terminal.get('lot'),1))})\n"
                    f"Entry: {float(terminal['entry']):.2f} / Target: {float(terminal['target']):.2f}\n"
                    f"Profit: {rupee(terminal.get('target_profit_gross'))} / Net*: {rupee(terminal.get('net_pnl_after_brokerage'))}\n"
                    f"Brokerage/Charges: {rupee(terminal.get('total_brokerage_rupees'))}"
                )
            else:
                self.send_signal_event_once(
                    terminal["signal_no"], "SL_HIT",
                    f"🔴 SL HIT #{terminal['signal_no']}\n{contract_label(terminal)} | {safe_int(terminal.get('lots'),1)} lot(s) (Qty {safe_int(terminal.get('quantity'), safe_int(terminal.get('lot'),1))})\n"
                    f"Entry: {float(terminal['entry']):.2f} / SL: {float(terminal['sl']):.2f}\n"
                    f"Loss: {rupee(terminal.get('sl_loss_gross'))} / Net*: {rupee(terminal.get('net_pnl_after_brokerage'))}\n"
                    f"Brokerage/Charges: {rupee(terminal.get('total_brokerage_rupees'))}"
                )
        if terminals:
            self.save_signal_log()

    def monitor_silent_after_accept(self):
        """Research-only monitor for warning-accepted signals.

        Financial outcome/P&L was already locked at warning ACCEPT.  This tracker only
        observes whether the ORIGINAL target or SL would have been reached afterwards.
        It emits no notification and never modifies the locked paper exit/P&L.
        """
        with self.state_lock:
            work = [
                (safe_int(v.get("signal_no"), -1), str(v.get("token") or ""))
                for v in self.silent_monitors.values()
                if bool(v.get("silent_monitor_active", False))
            ]
        if not work:
            return

        completed = False
        for signal_no, token in work:
            if signal_no <= 0 or not token:
                continue
            snap = self._current_option_snapshot(token)
            ltp = safe_float(snap.get("ltp"))
            if ltp is None or ltp <= 0:
                continue
            with self.state_lock:
                row = self.silent_monitors.get(signal_no)
                if row is None or not bool(row.get("silent_monitor_active", False)):
                    continue
                start_px = safe_float(row.get("silent_monitor_start_price"), safe_float(row.get("warning_accept_price"), ltp))
                if start_px is None:
                    start_px = ltp
                move = float(ltp) - float(start_px)
                row["silent_monitor_last_ltp"] = round(float(ltp), 2)
                row["silent_monitor_mfe_after_accept"] = max(
                    safe_float(row.get("silent_monitor_mfe_after_accept"), 0.0) or 0.0, move
                )
                row["silent_monitor_mae_after_accept"] = min(
                    safe_float(row.get("silent_monitor_mae_after_accept"), 0.0) or 0.0, move
                )

                target = safe_float(row.get("target"))
                sl = safe_float(row.get("sl"))
                silent_outcome = ""
                hit_px = None
                if target is not None and ltp >= target:
                    silent_outcome = "TARGET HIT"
                    hit_px = target
                elif sl is not None and ltp <= sl:
                    silent_outcome = "SL HIT"
                    hit_px = sl

                if silent_outcome:
                    row["silent_monitor_active"] = False
                    row["silent_monitor_outcome"] = silent_outcome
                    row["silent_monitor_outcome_time"] = now_ist().isoformat()
                    row["silent_monitor_hit_price"] = round(float(hit_px), 2)
                    self.silent_monitors.pop(signal_no, None)
                    completed = True
                    log.info(
                        "SILENT MONITOR COMPLETE | #%s | %s | accepted %.2f | original %s %.2f | locked P/L unchanged",
                        signal_no, contract_label(row), float(start_px), silent_outcome, float(hit_px),
                    )

        if completed:
            self.save_signal_log()
            try:
                self.write_app_ui(None, market_state="LIVE")
            except Exception:
                pass

    @staticmethod
    def elapsed_text(iso_time):
        try:
            started = datetime.fromisoformat(str(iso_time))
            if started.tzinfo is None:
                started = started.replace(tzinfo=IST)
            seconds = max(0, int((now_ist() - started.astimezone(IST)).total_seconds()))
            minutes, sec = divmod(seconds, 60)
            hours, minutes = divmod(minutes, 60)
            return f"{hours}h {minutes}m {sec}s" if hours else f"{minutes}m {sec}s"
        except Exception:
            return "UNKNOWN"

    def transit_status_text(self):
        transits = self._active_transit_snapshots()
        with self.state_lock:
            last_signal = dict(self.signal_history[-1]) if self.signal_history else None

        if not transits:
            if last_signal:
                return (
                    "ℹ️ NO ACTIVE TRANSIT\n"
                    f"{contract_label(last_signal)}\n"
                    f"Last: {float(last_signal.get('last_ltp') or 0):.2f}\n"
                    f"Result: {last_signal.get('outcome') or last_signal.get('status', '')}"
                )
            return "ℹ️ NO ACTIVE TRANSIT"

        total_amount_used = round(sum(safe_float(t.get("amount_used"), 0.0) or 0.0 for t in transits), 2)
        blocks = [
            f"ACTIVE TRANSITS: {len(transits)}",
            f"TOTAL AMOUNT USED: {rupee(total_amount_used)}",
        ]
        for transit in transits:
            d = self._current_option_snapshot(transit["token"])
            ltp = safe_float(d.get("ltp"), safe_float(transit.get("last_ltp"), 0.0))
            pending_type = str(transit.get("pending_warning_type") or "").upper().strip()
            warning_line = ""
            if pending_type:
                warning_name = "IMMEDIATE EXIT WARNING" if pending_type == "IMMEDIATE_EXIT" else "TRANSIT WARNING"
                warning_line = f"\n⚠️ {warning_name}: ACCEPT TO EXIT / DECLINE TO CONTINUE"
            live_money = one_lot_money(
                float(transit["entry"]),
                float(transit["target"]),
                float(transit["sl"]),
                safe_int(transit.get("lot"), 1),
                exit_price=ltp,
                lots=safe_int(transit.get("lots"), 1),
            )
            target_net = transit.get("target_profit_after_brokerage")
            sl_net = -abs(safe_float(transit.get("sl_loss_after_brokerage"), 0.0))
            total_brokerage = safe_float(live_money.get("total_brokerage_rupees"), safe_float(transit.get("brokerage_round_trip"), 0.0)) or 0.0
            live_gross = safe_float(live_money.get("gross_pnl_rupees"), 0.0) or 0.0
            live_net = safe_float(live_money.get("net_pnl_after_brokerage"), live_gross - total_brokerage) or 0.0
            pnl_state, pnl_icon = pnl_traffic_state(live_gross, total_brokerage, live_net)
            blocks.append(
                f"{pnl_icon} #{transit['signal_no']} {contract_label(transit)} | {pnl_state} | {safe_int(transit.get('lots'),1)} lot(s) (Qty {safe_int(transit.get('quantity'), safe_int(transit.get('lot'),1))})\n"
                f"Option Type: {str(transit.get('side') or '--').upper()}\n"
                f"Current: {ltp:.2f} | Gross: {rupee_signed(live_gross)} | Net: {rupee_signed(live_net)}\n"
                f"Entry: {float(transit['entry']):.2f} | {rupee(transit.get('amount_used'))}\n"
                f"Reason: {short_reason(((str(transit.get('technical_setup') or '').strip() + ' | ') if str(transit.get('technical_setup') or '').strip() and str(transit.get('technical_setup') or '').strip().upper() not in ('NONE','NAN') else '') + str(transit.get('final_reason') or 'Approved setup'), 110)}\n"
                f"Target: {float(transit['target']):.2f} | {rupee_signed(target_net)} net\n"
                f"SL: {float(transit['sl']):.2f} | {rupee_signed(sl_net)} net\n"
                f"Brokerage/Charges: {rupee(total_brokerage)} total{warning_line}"
            )
        return "\n\n".join(blocks)

    def remote_command_worker_disabled(self):
        """Disabled in V3.1 unified-bot mode.

        Android build has no Telegram polling or remote deployment.
        Local notifications are handled by Termux:API.
        """
        return

    # ----------------------------------------------------------------------
    # V3.7.0 diagnostics / rejected setup research
    # ----------------------------------------------------------------------

    def _load_rejected_setup_log(self):
        self.rejected_setup_rows = []
        self.rejected_setup_keys = set()
        if not REJECTED_SETUP_LOG_FILE.exists():
            return
        try:
            with open(REJECTED_SETUP_LOG_FILE, "r", newline="", encoding="utf-8") as f:
                for row in csv.DictReader(f):
                    self.rejected_setup_rows.append(dict(row))
                    key = str(row.get("key") or "")
                    if key:
                        self.rejected_setup_keys.add(key)
        except Exception as exc:
            log.warning("DIAGNOSTIC LOG | rejected-setup CSV load failed: %s", short_reason(exc, 120))

    def _save_rejected_setup_log(self):
        fields = [
            "key", "time_ist", "index_root", "candle_time", "side", "setup",
            "technical_score", "spot", "reason", "adx14", "plus_di14", "minus_di14",
            "ema20", "ema50", "futures_ltp", "futures_vwap",
            "option_symbol", "option_score", "combined_score",
            "premium_momentum_10s", "premium_momentum_30s",
            "luna_decision", "luna_confidence", "luna_reason",
            "outcome_5m", "outcome_10m", "outcome_15m",
        ]
        try:
            REJECTED_SETUP_LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
            with open(REJECTED_SETUP_LOG_FILE, "w", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
                w.writeheader()
                for row in self.rejected_setup_rows[-1000:]:
                    w.writerow({k: row.get(k, "") for k in fields})
        except Exception as exc:
            log.warning("DIAGNOSTIC LOG | rejected-setup CSV save failed: %s", short_reason(exc, 120))

    def record_rejected_setup(self, candidate=None):
        """Record one HOLD/rejection state per completed-candle setup for research."""
        try:
            with self.state_lock:
                tech = dict(self.technical_state)
                review = dict(self.final_review_state)

            direction = str(tech.get("direction") or "").upper()
            if direction not in ("CE", "PE"):
                return False
            if not tech.get("setup") or str(tech.get("setup")).upper() == "NONE":
                return False
            if review.get("running"):
                return False
            if (
                str(review.get("decision") or "").upper() == "WAIT"
                and float(review.get("next_retry_ts") or 0.0) > 0
            ):
                # WAIT is still provisional while same-setup rechecks remain.
                return False

            tech_avail = self._technical_data_availability(live=True)
            greek_avail = self._greeks_data_availability(live=True)
            ready, _, reasons = self._entry_ui_state(candidate, tech_avail, greek_avail)
            if ready:
                return False
            reason = " | ".join(reasons[:6]) if reasons else "HOLD"
            if "WAITING FOR LUNA REVIEW" in reason or "LUNA REVIEW IN PROGRESS" in reason:
                return False

            setup_sig = self.setup_signature(tech, direction)
            key = "|".join(str(x) for x in setup_sig) + "|" + reason
            if key in self.rejected_setup_keys:
                return False

            with self.state_lock:
                spot = safe_float(self.nifty_live, 0.0) or 0.0
                fltp = safe_float(self.futures_ltp)
                fvwap = safe_float(self.futures_vwap)

            row = {
                "key": key,
                "time_ist": now_ist().isoformat(),
                "index_root": self.index_root,
                "candle_time": tech.get("candle_time"),
                "side": direction,
                "setup": tech.get("setup"),
                "technical_score": tech.get("tech_score"),
                "spot": round(float(spot), 2),
                "reason": reason,
                "adx14": tech.get("adx14"),
                "plus_di14": tech.get("plus_di14"),
                "minus_di14": tech.get("minus_di14"),
                "ema20": tech.get("ema20"),
                "ema50": tech.get("ema50"),
                "futures_ltp": fltp,
                "futures_vwap": fvwap,
                "option_symbol": (candidate or {}).get("symbol", ""),
                "option_score": (candidate or {}).get("score", ""),
                "combined_score": (candidate or {}).get("combined_score", ""),
                "premium_momentum_10s": (candidate or {}).get("premium_momentum_10s", ""),
                "premium_momentum_30s": (candidate or {}).get("premium_momentum_30s", ""),
                "luna_decision": review.get("decision", ""),
                "luna_confidence": review.get("confidence", ""),
                "luna_reason": review.get("reason", ""),
                "outcome_5m": "",
                "outcome_10m": "",
                "outcome_15m": "",
            }
            self.rejected_setup_rows.append(row)
            self.rejected_setup_keys.add(key)
            self._save_rejected_setup_log()
            log.info(
                "REJECTED SETUP | %s %s | score=%s | spot=%.2f | %s",
                direction, tech.get("setup"), tech.get("tech_score"), float(spot), reason,
            )
            return True
        except Exception as exc:
            log.warning("DIAGNOSTIC LOG | rejected-setup record failed: %s", short_reason(exc, 120))
            return False

    def update_rejected_setup_outcomes(self):
        """Attach underlying directional moves after 5/10/15 minutes."""
        now_ts = time.time()
        if now_ts - float(self.last_rejected_tracker_update_ts or 0.0) < 5:
            return
        self.last_rejected_tracker_update_ts = now_ts
        with self.state_lock:
            spot_now = safe_float(self.nifty_live)
        if spot_now is None or spot_now <= 0:
            return

        changed = False
        for row in self.rejected_setup_rows[-200:]:
            try:
                started = datetime.fromisoformat(str(row.get("time_ist")))
                if started.tzinfo is None:
                    started = started.replace(tzinfo=IST)
                age_min = (now_ist() - started.astimezone(IST)).total_seconds() / 60.0
                entry_spot = safe_float(row.get("spot"))
                side = str(row.get("side") or "").upper()
                if entry_spot is None or entry_spot <= 0 or side not in ("CE", "PE"):
                    continue
                move = float(spot_now) - float(entry_spot)
                directional = move if side == "CE" else -move
                for mins in REJECTED_SETUP_OUTCOME_HORIZONS:
                    field = f"outcome_{mins}m"
                    if age_min >= mins and not str(row.get(field) or "").strip():
                        row[field] = f"{directional:+.2f} index pts"
                        log.info(
                            "REJECTED OUTCOME | index=%s | side=%s | setup=%s | reason=%s | horizon=%sm | directional_move=%+.2f",
                            row.get("index_root"), side, row.get("setup"),
                            short_reason(row.get("reason"), 100), mins, directional,
                        )
                        changed = True
            except Exception:
                continue
        if changed:
            self._save_rejected_setup_log()

    def log_rejected_research_summary(self):
        """Write rejected-setup research into runtime log so Android Export always contains it."""
        rows = list(self.rejected_setup_rows[-300:])
        if not rows:
            log.info("REJECTED RESEARCH SUMMARY | no rejected setups recorded")
            return
        reason_counts = defaultdict(int)
        resolved = 0
        positive = 0
        for row in rows:
            reason = str(row.get("reason") or "UNKNOWN")
            category = reason.split(" | ", 1)[0][:80]
            reason_counts[category] += 1
            outcome = str(row.get("outcome_15m") or row.get("outcome_10m") or row.get("outcome_5m") or "")
            m = re.search(r"([+-]?\d+(?:\.\d+)?)", outcome)
            if m:
                resolved += 1
                if float(m.group(1)) > 0:
                    positive += 1
        log.info(
            "REJECTED RESEARCH SUMMARY | rows=%s | resolved=%s | favorable=%s | favorable_pct=%.1f",
            len(rows), resolved, positive, (100.0*positive/resolved if resolved else 0.0),
        )
        for reason, count in sorted(reason_counts.items(), key=lambda kv: kv[1], reverse=True)[:12]:
            log.info("REJECTED REASON COUNT | count=%s | reason=%s", count, reason)

    def _api_health_record(self, source, status, missing=None, detail="", now_ts=None):
        """Record one source/API health sample and log only meaningful changes/issues.

        This never writes to app_ui.json and never creates a user notification.
        Everything goes to index_v31_runtime.log for end-of-day Export Data analysis.
        """
        now_ts = float(now_ts or time.time())
        source = str(source or "UNKNOWN").upper()
        status = str(status or "UNKNOWN").upper()
        missing = [str(x) for x in (missing or []) if str(x).strip()]
        detail = short_reason(detail or "", 180)

        bad_statuses = {"MISSING", "STALE", "FAILED", "ERROR"}
        caution_statuses = {"PARTIAL"}
        bad = status in bad_statuses
        caution = status in caution_statuses

        stat = self.api_health_stats.setdefault(source, {
            "samples": 0,
            "bad_samples": 0,
            "partial_samples": 0,
            "first_bad_ts": 0.0,
            "last_bad_ts": 0.0,
            "last_status": "UNKNOWN",
            "last_missing": "",
            "last_detail": "",
        })
        stat["samples"] += 1
        if bad:
            stat["bad_samples"] += 1
            stat["last_bad_ts"] = now_ts
            if not stat["first_bad_ts"]:
                stat["first_bad_ts"] = now_ts
        elif caution:
            stat["partial_samples"] += 1

        stat["last_status"] = status
        stat["last_missing"] = ",".join(missing)
        stat["last_detail"] = detail

        missing_text = ",".join(missing) if missing else "NONE"
        state_sig = f"{status}|{missing_text}|{detail}"
        prev = self.api_health_last_state.get(source)
        changed = prev != state_sig
        prev_status = str(prev or "").split("|", 1)[0] if prev else ""
        prev_bad = prev_status in bad_statuses or prev_status in caution_statuses

        if (bad or caution):
            last_issue_log = float(self.api_health_last_issue_log.get(source, 0.0) or 0.0)
            if changed or now_ts - last_issue_log >= API_HEALTH_ISSUE_REPEAT_SECONDS:
                level = log.warning if bad else log.info
                level(
                    "API ISSUE | source=%s | status=%s | missing=%s | detail=%s",
                    source, status, missing_text, detail or "NONE",
                )
                self.api_health_last_issue_log[source] = now_ts
        elif changed and prev_bad:
            log.info(
                "API RECOVERY | source=%s | status=%s | missing=NONE | detail=%s",
                source, status, detail or "RECOVERED",
            )

        self.api_health_last_state[source] = state_sig

    def log_api_health_summary(self, force=False):
        """Write accumulated source reliability counters to the runtime export log."""
        now_ts = time.time()
        if not self.api_health_stats:
            return
        if (
            not force
            and now_ts - float(self.last_api_health_summary_ts or 0.0)
            < API_HEALTH_SUMMARY_INTERVAL_SECONDS
        ):
            return

        log.info("API HEALTH SUMMARY START | time=%s", now_ist().isoformat())
        for source in sorted(self.api_health_stats):
            stat = self.api_health_stats[source]
            samples = max(1, int(stat.get("samples") or 0))
            bad = int(stat.get("bad_samples") or 0)
            partial = int(stat.get("partial_samples") or 0)
            bad_pct = 100.0 * bad / samples
            partial_pct = 100.0 * partial / samples
            log.info(
                "API HEALTH SUMMARY | source=%s | samples=%s | bad=%s (%.1f%%) "
                "| partial=%s (%.1f%%) | last_status=%s | last_missing=%s | last_detail=%s",
                source,
                samples,
                bad,
                bad_pct,
                partial,
                partial_pct,
                stat.get("last_status") or "UNKNOWN",
                stat.get("last_missing") or "NONE",
                stat.get("last_detail") or "NONE",
            )
        log.info("API HEALTH SUMMARY END")
        self.last_api_health_summary_ts = now_ts

    def log_data_health(self, candidate=None, force=False):
        """Record complete LIVE data health for later exported-log analysis.

        No WebSocket/API missing-data detail from this method is shown on the live
        Android screen. Each source is separately identified so a full-day export
        can reveal whether Angel WebSocket, historical candles, Greeks, options,
        futures, REST quote recovery, or the OpenAI fundamental scan is unreliable.
        """
        if str(getattr(self, "runtime_phase", "")).upper() != "LIVE":
            return

        now_ts = time.time()
        try:
            ws = self._websocket_status_snapshot()
            tech_avail = self._technical_data_availability(live=True)
            greek_avail = self._greeks_data_availability(live=True)
            fund_ui = self._fundamental_ui_state()

            with self.state_lock:
                fund = dict(self.fundamental_state)
                tech = dict(self.technical_state)
                greeks_state = dict(self.greeks_state)
                fltp = safe_float(self.futures_ltp)
                fvwap = safe_float(self.futures_vwap)
                fts = float(self.futures_last_tick_ts or 0.0)
                expected_options = len(self.token_contract)
                option_rows = list(self.latest_options.values())
                rest_probe_ts = float(self.websocket_last_rest_probe_ts or 0.0)
                rest_probe_ok = bool(self.websocket_last_rest_probe_ok)
                rest_probe_price = safe_float(self.websocket_last_rest_probe_price)

            snapshot_parts = []

            # 1) Angel index WebSocket
            ws_age = ws.get("age")
            if (
                ws.get("state") == "HEALTHY"
                and ws_age is not None
                and ws_age <= WEBSOCKET_SIGNAL_BLOCK_SECONDS
            ):
                ws_status = "OK"
                ws_missing = []
                ws_detail = f"age={int(ws_age)}s"
            else:
                ws_status = "STALE" if ws_age is not None else "MISSING"
                ws_missing = ["INDEX_LTP_TICK"]
                age_text = "NO TICK" if ws_age is None else f"{int(ws_age)}s OLD"
                ws_detail = (
                    f"state={ws.get('state')} age={age_text} "
                    f"reason={short_reason(ws.get('reason') or 'NONE', 100)}"
                )
            self._api_health_record(
                "ANGEL_WS_INDEX", ws_status, ws_missing, ws_detail, now_ts
            )
            snapshot_parts.append(
                f"ANGEL_WS_INDEX={ws_status}"
                + (f"[{','.join(ws_missing)}]" if ws_missing else "")
            )

            # 2) Angel historical 5-minute candle path
            if tech_avail.get("candle_phase") == "BUILDING":
                hist_status = "BUILDING"
                hist_missing = []
                hist_detail = "opening 5m candle window still building"
            elif tech_avail.get("last3_available"):
                hist_status = "OK"
                hist_missing = []
                hist_detail = ",".join(tech_avail.get("candle_intervals") or [])
            else:
                hist_status = "MISSING"
                missing_times = [str(x) for x in (tech_avail.get("missing_last3_times") or [])]
                hist_missing = [f"5M_{x}" for x in missing_times] or ["LAST_3_COMPLETED_5M"]
                seed_error = ""
                try:
                    seed_error = str(getattr(self.technical, "seed_error", "") or "")
                except Exception:
                    pass
                hist_detail = " | ".join(
                    x for x in [
                        str(tech_avail.get("last3_reason") or ""),
                        seed_error,
                    ] if x
                ) or "completed 5m history unavailable"
            self._api_health_record(
                "ANGEL_HISTORICAL_5M", hist_status, hist_missing, hist_detail, now_ts
            )
            snapshot_parts.append(
                f"ANGEL_HISTORICAL_5M={hist_status}"
                + (f"[{','.join(hist_missing)}]" if hist_missing else "")
            )

            # 3) Derived technical core (not an external API, but tells us exactly
            # which calculations are unavailable because upstream source data failed).
            core_missing = [
                str(x) for x in (tech_avail.get("missing") or [])
                if x not in ("LAST 3 × 5M CANDLES", "CANDLE BUILDING ZONE")
            ]
            core_status = "OK" if not core_missing else "MISSING"
            core_detail = short_reason(tech.get("error") or "", 140)
            self._api_health_record(
                "DERIVED_TECH_CORE", core_status, core_missing, core_detail, now_ts
            )
            snapshot_parts.append(
                f"DERIVED_TECH_CORE={core_status}"
                + (f"[{','.join(core_missing)}]" if core_missing else "")
            )

            # 4) Angel futures WebSocket / futures VWAP data
            futures_missing = []
            if fltp is None or fltp <= 0:
                futures_missing.append("FUTURES_LTP")
            if fvwap is None or fvwap <= 0:
                futures_missing.append("FUTURES_VWAP")
            if not fts:
                futures_missing.append("FUTURES_WS_TICK")
                futures_detail = "NO FUTURES WEBSOCKET TICK"
            else:
                futures_age = now_ts - fts
                futures_detail = f"tick_age={int(futures_age)}s"
                if futures_age > FUTURES_STALE_SECONDS:
                    futures_missing.append(f"FUTURES_WS_TICK_{int(futures_age)}S_OLD")
            futures_status = "OK" if not futures_missing else "MISSING"
            self._api_health_record(
                "ANGEL_WS_FUTURES",
                futures_status,
                futures_missing,
                futures_detail,
                now_ts,
            )
            snapshot_parts.append(
                f"ANGEL_WS_FUTURES={futures_status}"
                + (f"[{','.join(futures_missing)}]" if futures_missing else "")
            )

            # 5) Angel options WebSocket coverage
            fresh_options = sum(
                1 for row in option_rows
                if now_ts - float((row or {}).get("timestamp") or 0.0) <= 10
            )
            if not expected_options:
                option_status = "MISSING"
                option_missing = ["OPTION_UNIVERSE"]
            elif fresh_options == 0:
                option_status = "MISSING"
                option_missing = [f"OPTION_TICKS_0_OF_{expected_options}"]
            elif fresh_options < max(1, expected_options // 3):
                option_status = "MISSING"
                option_missing = [f"OPTION_TICKS_{fresh_options}_OF_{expected_options}"]
            elif fresh_options < expected_options:
                option_status = "PARTIAL"
                option_missing = [f"OPTION_TICKS_{expected_options-fresh_options}_NOT_FRESH"]
            else:
                option_status = "OK"
                option_missing = []
            option_detail = f"fresh={fresh_options}/{expected_options}"
            self._api_health_record(
                "ANGEL_WS_OPTIONS",
                option_status,
                option_missing,
                option_detail,
                now_ts,
            )
            snapshot_parts.append(
                f"ANGEL_WS_OPTIONS={option_status}"
                + (f"[{','.join(option_missing)}]" if option_missing else "")
            )

            # 6) Greeks source: NFO uses Angel optionGreek; BFO uses local proxy Greeks.
            greek_source = (
                "LOCAL_BFO_GREEKS_PROXY"
                if str(self.derivative_exchange or "").upper() == "BFO"
                else "ANGEL_GREEKS_API"
            )
            greek_error = str(greeks_state.get("error") or "")
            if greek_avail.get("available"):
                greek_status = "OK"
                greek_missing = []
                greek_detail = f"age={int(now_ts-float(greeks_state.get('last_update') or now_ts))}s"
            elif greek_avail.get("checking"):
                greek_status = "CHECKING"
                greek_missing = []
                greek_detail = greek_error or "Greeks refresh in progress"
            else:
                greek_status = "MISSING"
                greek_missing = [str(x) for x in (greek_avail.get("missing") or [])]
                if not greek_missing:
                    greek_missing = ["GREEKS_RESPONSE"]
                why_g = greek_avail.get("why") or []
                greek_detail = greek_error or (str(why_g[0]) if why_g else "No usable Greeks")
            self._api_health_record(
                greek_source,
                greek_status,
                greek_missing,
                greek_detail,
                now_ts,
            )
            snapshot_parts.append(
                f"{greek_source}={greek_status}"
                + (f"[{','.join(greek_missing)}]" if greek_missing else "")
            )

            # 7) OpenAI + web-search fundamental/news scan
            fund_last = float(fund.get("last_update") or 0.0)
            fund_age = now_ts - fund_last if fund_last else None
            if fund_ui.get("ready") and fund_last and fund_age <= FUNDAMENTAL_STALE_SECONDS:
                fund_status = "OK"
                fund_missing = []
                fund_detail = f"age={int(fund_age/60)}m"
            elif fund_last:
                fund_status = "STALE"
                fund_missing = ["FUNDAMENTAL_NEWS_SCAN"]
                fund_detail = str(fund.get("error") or f"age={int(fund_age/60)}m")
            else:
                fund_status = "MISSING"
                fund_missing = ["FUNDAMENTAL_NEWS_SCAN"]
                fund_detail = str(fund.get("error") or "No valid fundamental/news scan")
            self._api_health_record(
                "OPENAI_FUNDAMENTAL_SCAN",
                fund_status,
                fund_missing,
                fund_detail,
                now_ts,
            )
            snapshot_parts.append(
                f"OPENAI_FUNDAMENTAL_SCAN={fund_status}"
                + (f"[{','.join(fund_missing)}]" if fund_missing else "")
            )

            # 8) Angel REST quote is only a recovery path. Do not mark it missing
            # when it has not been used; record it only after a probe actually ran.
            if rest_probe_ts:
                rest_age = now_ts - rest_probe_ts
                if rest_probe_ok:
                    rest_status = "OK"
                    rest_missing = []
                    rest_detail = f"age={int(rest_age)}s price={rest_probe_price}"
                else:
                    rest_status = "FAILED"
                    rest_missing = ["INDEX_LTP_REST_QUOTE"]
                    rest_detail = f"age={int(rest_age)}s last_probe_failed"
                self._api_health_record(
                    "ANGEL_REST_QUOTE_RECOVERY",
                    rest_status,
                    rest_missing,
                    rest_detail,
                    now_ts,
                )
                snapshot_parts.append(
                    f"ANGEL_REST_QUOTE_RECOVERY={rest_status}"
                    + (f"[{','.join(rest_missing)}]" if rest_missing else "")
                )

            # Current strategy state is useful in the same export log, but it is
            # separate from API reliability.
            if tech.get("entry_ready"):
                strategy_text = (
                    f"READY {tech.get('direction')} {tech.get('setup')} "
                    f"score={tech.get('tech_score')}"
                )
            else:
                strategy_text = short_reason(
                    tech.get("entry_block_reason") or "NO VALID TECHNICAL SETUP",
                    100,
                )

            snapshot_parts.append("TECH_SETUP=" + strategy_text)

            signature = " | ".join(snapshot_parts)
            changed = signature != self.last_data_health_signature
            due = (
                now_ts - float(self.last_data_health_log_ts or 0.0)
                >= DATA_HEALTH_LOG_INTERVAL_SECONDS
            )

            if force or changed or due:
                log.info("API HEALTH SNAPSHOT | %s", signature)
                self.last_data_health_signature = signature
                self.last_data_health_log_ts = now_ts

            self.log_api_health_summary(force=False)

        except Exception as exc:
            log.warning(
                "API HEALTH LOGGER ERROR | missing=DIAGNOSTIC_SNAPSHOT | detail=%s",
                short_reason(exc, 160),
            )

    # ----------------------------------------------------------------------
    # Persistence / stats
    # ----------------------------------------------------------------------

    def _load_previous_signal_log_for_stats(self):
        """Load only today's rows into live memory and restart display numbering at #1.

        The CSV remains multi-day. V3.8.0 also migrates legacy *current-day* numbering
        (for example #5..#11) to #1..#7 once, preserving the old number in
        legacy_signal_no. This keeps the Android Signals window intuitive without
        deleting any historical/export detail.
        """
        self.signal_counter = 0
        self.signal_history = []
        if not SIGNAL_LOG_FILE.exists():
            return
        try:
            df = pd.read_csv(SIGNAL_LOG_FILE)
            if df.empty:
                return
            if "signal_no" not in df.columns:
                df["signal_no"] = ""
            if "legacy_signal_no" not in df.columns:
                df["legacy_signal_no"] = ""
            if "signal_uid" not in df.columns:
                df["signal_uid"] = ""
            if "date" not in df.columns:
                return

            td = now_ist().date().isoformat()
            today_idx = list(df.index[df["date"].astype(str) == td])
            if not today_idx:
                return

            def sort_key(idx):
                et = str(df.at[idx, "entry_time"]) if "entry_time" in df.columns else ""
                sn = safe_int(df.at[idx, "signal_no"], 0)
                return (et, sn)

            today_idx.sort(key=sort_key)
            changed = False
            for display_no, idx in enumerate(today_idx, start=1):
                old_no = safe_int(df.at[idx, "signal_no"], 0)
                if old_no != display_no:
                    legacy = str(df.at[idx, "legacy_signal_no"] or "").strip()
                    if not legacy or legacy.lower() == "nan":
                        df.at[idx, "legacy_signal_no"] = old_no if old_no else ""
                    df.at[idx, "signal_no"] = display_no
                    changed = True
                uid = str(df.at[idx, "signal_uid"] or "").strip()
                if not uid or uid.lower() == "nan":
                    stamp = ""
                    try:
                        dt = self._parse_signal_time(df.at[idx, "entry_time"])
                        stamp = dt.strftime("%H%M%S") if dt else "000000"
                    except Exception:
                        stamp = "000000"
                    df.at[idx, "signal_uid"] = f"{td.replace('-', '')}-{display_no:03d}-{stamp}"
                    changed = True

            if changed:
                df.to_csv(SIGNAL_LOG_FILE, index=False)
                log.info("DAILY SIGNAL NUMBER MIGRATION | date=%s | rows=%s | display=#1..#%s", td, len(today_idx), len(today_idx))

            today = df.loc[today_idx].copy()
            today = today.sort_values(by=["signal_no"], key=lambda s: pd.to_numeric(s, errors="coerce"))
            self.signal_history = [dict(row) for row in today.to_dict("records")]
            self.signal_counter = len(self.signal_history)

            # Restore unfinished V4.4.1 silent post-exit monitors after an engine restart.
            # The trade remains financially closed; this only resumes research tracking.
            self.silent_monitors = {}
            for row in self.signal_history:
                active_raw = str(row.get("silent_monitor_active") or "").strip().lower()
                silent_done = str(row.get("silent_monitor_outcome") or "").strip()
                if silent_done.lower() in ("", "nan", "none"):
                    silent_done = ""
                if active_raw in ("true", "1", "yes") and not silent_done:
                    sn = safe_int(row.get("signal_no"), -1)
                    token = str(row.get("token") or "").strip()
                    if sn > 0 and token:
                        row["silent_monitor_active"] = True
                        self.silent_monitors[sn] = row

            # Rebuild exact-event de-duplication for V3.8 rows already recorded today.
            for row in self.signal_history:
                event_time = str(row.get("strategy_event_time") or "").strip()
                setup_name = str(row.get("technical_setup") or "NONE").upper()
                side = str(row.get("side") or "").upper()
                root = str(row.get("index_root") or self.index_root or "")
                if event_time and setup_name != "NONE" and side in ("CE", "PE"):
                    self.issued_setup_signatures.add((root, event_time, setup_name, side))
        except Exception as exc:
            log.warning("Daily signal history load skipped: %s", short_reason(exc, 120))
            self.signal_counter = 0
            self.signal_history = []

    def save_signal_log(self):
        fields=[
            "signal_no","signal_uid","legacy_signal_no","date","entry_time","index_root","expiry","symbol","token","side","strike","type","lot","lots","quantity",
            "spot_at_entry","entry","sl","target","amount_used","target_profit_gross","sl_loss_gross",
            "brokerage_buy","brokerage_exit","brokerage_round_trip","brokerage_only","stt","exchange_transaction_charges","stamp_duty","sebi_charges","gst","total_charges","target_total_charges","sl_total_charges","charge_model","target_profit_after_brokerage","sl_loss_after_brokerage","money_model",
            "risk_per_unit","target_r","premium_range_60s_entry","risk_model","entry_timing_gate","reentry_gate","option_score","final_confidence","final_reason",
            "fundamental_filter","fundamental_support","news_risk","technical_bias","technical_setup","technical_score","setup_grade","combined_score",
            "strategy_event_time","strategy_id","strategy_short_name","strategy_status","strategy_reason_entry",
            "sweep_price_entry","sweep_time_entry","htf_fvg_lower_entry","htf_fvg_upper_entry","htf_fvg_time_entry",
            "ltf_fvg_lower_entry","ltf_fvg_upper_entry","ltf_fvg_time_entry","ifvg_confirmation_time_entry",
            "cisd_reference_open_entry","cisd_reference_time_entry","cisd_confirmation_time_entry",
            "setup_invalidation_level","target_liquidity","target_liquidity_time","target_liquidity_type",
            "amd_accumulation_start","amd_accumulation_end","amd_range_high","amd_range_low","amd_poc_price",
            "amd_profile_total_volume","amd_profile_bin_size","amd_profile_source","amd_profile_distribution","amd_futures_poc_price","amd_futures_index_basis",
            "amd_manipulation_price","amd_manipulation_time","amd_poc_cross_time","amd_poc_retest_time",
            "all_valid_setups_entry",
            "candlestick_primary_entry","candlestick_family_entry","candlestick_direction_entry","candlestick_bias_entry",
            "candlestick_bonus_entry","candlestick_patterns_entry","candlestick_conflict_entry",
            "weapon15_time","weapon15_ema9","weapon15_macd","weapon15_macd_signal","weapon15_rsi14",
            "liquidity_event_entry","liquidity_level_entry","fvg_event_entry","fvg_zone_low_entry","fvg_zone_high_entry",
            "vwap_event_futures_ltp","vwap_event_futures_vwap",
            "adx14","plus_di14","minus_di14","atr14","ema20_slope","ema50_slope","or_status_entry",
            "futures_ltp_entry","futures_vwap_entry","premium_momentum_10s_entry","premium_momentum_30s_entry",
            "status","last_ltp","mfe","mae","mfe_time","mae_time","profit_protect_armed","transit_alert_sent",
            "guardian_checks","guardian_last_check_ts","guardian_action","guardian_confidence","guardian_risk","guardian_reason",
            "guardian_exit_price","guardian_exit_time",
            "pending_warning_type","pending_warning_reason","pending_warning_time","pending_warning_price",
            "pending_warning_confidence","pending_warning_risk",
            "warning_accept_type","warning_accept_price","warning_accept_time","warning_accept_engine_ltp","warning_accept_reason","transit_exit_line",
            "warning_decline_type","warning_decline_price","warning_decline_time","warning_decline_reason","warning_decline_until_ts",
            "manual_exit_price","manual_exit_time","manual_exit_reason",
            "silent_monitor_active","silent_monitor_start_time","silent_monitor_start_price","silent_monitor_last_ltp",
            "silent_monitor_outcome","silent_monitor_outcome_time","silent_monitor_hit_price",
            "silent_monitor_mfe_after_accept","silent_monitor_mae_after_accept",
            "outcome","outcome_time",
            "paper_exit_price","observed_exit_ltp","gross_pnl_rupees","total_brokerage_rupees","net_pnl_after_brokerage",
            "shadow_strategy","shadow_factor_scores","shadow_base_weights","shadow_suggested_weights_entry",
            "shadow_base_score","shadow_adaptive_score","shadow_outcome_r","shadow_learning_recorded",
            "shadow_suggested_weights_after"]
        existing=[]
        if SIGNAL_LOG_FILE.exists():
            try:
                with open(SIGNAL_LOG_FILE,"r",newline="",encoding="utf-8") as f: existing=list(csv.DictReader(f))
            except Exception: existing=[]
        # Preserve any legacy/future columns already present in the master CSV.
        # The Android Signals window is day-local, but the export remains a full
        # multi-day research record and must not lose older detail on rewrite.
        extra_fields = []
        for row in existing:
            for key in row.keys():
                if key and key not in fields and key not in extra_fields:
                    extra_fields.append(key)
        fields = fields + extra_fields
        with self.state_lock: todays=[dict(x) for x in self.signal_history]
        by_key={}
        # signal_no is day-local; signal_uid is globally unique when available.
        for row in existing:
            uid=str(row.get("signal_uid","") or "").strip()
            key=("UID",uid) if uid and uid.lower()!="nan" else (str(row.get("date","")), str(row.get("signal_no","")))
            by_key[key]=row
        for row in todays:
            uid=str(row.get("signal_uid","") or "").strip()
            key=("UID",uid) if uid and uid.lower()!="nan" else (str(row.get("date","")), str(row.get("signal_no","")))
            by_key[key]=row
        rows=list(by_key.values())
        rows.sort(key=lambda r:(str(r.get("date","")), safe_int(r.get("signal_no",0))))
        with open(SIGNAL_LOG_FILE,"w",newline="",encoding="utf-8") as f:
            w=csv.DictWriter(f,fieldnames=fields,extrasaction="ignore"); w.writeheader()
            for row in rows: w.writerow({k:row.get(k,"") for k in fields})
        self._write_signals_today_file()
        _daily_measurement_report(rows)
    def _row_paper_pnl(self, row):
        """Return (gross, brokerage, net) for one resolved row, including legacy rows."""
        stored_net = safe_float(row.get("net_pnl_after_brokerage"))
        stored_gross = safe_float(row.get("gross_pnl_rupees"))
        stored_brokerage = safe_float(row.get("total_brokerage_rupees"))
        if stored_gross is not None and stored_brokerage is not None and stored_net is not None:
            return stored_gross, stored_brokerage, stored_net

        entry = safe_float(row.get("entry"))
        target = safe_float(row.get("target"), entry)
        sl = safe_float(row.get("sl"), entry)
        lot = max(1, safe_int(row.get("lot"), 1))
        if entry is None or target is None or sl is None:
            return 0.0, 0.0, 0.0
        outcome = str(row.get("outcome") or "").upper()
        if outcome == "TARGET HIT":
            exit_px = target
        elif outcome == "SL HIT":
            exit_px = sl
        elif outcome == "IMMEDIATE EXIT":
            exit_px = safe_float(row.get("guardian_exit_price"), safe_float(row.get("last_ltp"), entry))
        elif outcome == "MANUAL EXIT":
            exit_px = safe_float(row.get("manual_exit_price"), safe_float(row.get("paper_exit_price"), safe_float(row.get("last_ltp"), entry)))
        elif outcome == "SESSION CLOSE":
            exit_px = safe_float(row.get("paper_exit_price"), safe_float(row.get("last_ltp"), entry))
        else:
            return 0.0, 0.0, 0.0
        m = one_lot_money(entry, target, sl, lot, exit_price=exit_px, lots=max(1, safe_int(row.get("lots"), DEFAULT_LOTS_PER_SIGNAL)))
        return m["gross_pnl_rupees"], m["total_brokerage_rupees"], m["net_pnl_after_brokerage"]

    def signals_today_text(self):
        """Human-readable current-day signal list with V4 real-money economics.

        Python owns all quantity, amount, brokerage and P/L arithmetic. Android only
        renders this text, preventing UI-side drift from the signal CSV/export.
        """
        td = now_ist().date().isoformat()
        rows = []
        try:
            if SIGNAL_LOG_FILE.exists():
                df = pd.read_csv(SIGNAL_LOG_FILE)
                if not df.empty and "date" in df.columns:
                    df = df[df["date"].astype(str) == td].copy()
                    if not df.empty:
                        if "signal_no" in df.columns:
                            df["_sn"] = pd.to_numeric(df["signal_no"], errors="coerce").fillna(0)
                            df = df.sort_values(by=["_sn"], ascending=False)
                        rows = [dict(x) for x in df.to_dict("records")]
        except Exception:
            rows = []

        # V7.7: CSV is the persistent history, but active in-memory TRANSIT rows
        # contain the freshest WebSocket LTP/P&L. Overlay today's live rows onto
        # the CSV rows so the Signals menu updates live exactly like the first page.
        with self.state_lock:
            live_rows = [dict(x) for x in self.signal_history]

        if rows and live_rows:
            live_by_key = {}
            for live in live_rows:
                uid = str(live.get("signal_uid") or "").strip()
                key = ("UID", uid) if uid and uid.lower() != "nan" else ("NO", safe_int(live.get("signal_no"), 0))
                live_by_key[key] = live

            merged = []
            seen = set()
            for persisted in rows:
                uid = str(persisted.get("signal_uid") or "").strip()
                key = ("UID", uid) if uid and uid.lower() != "nan" else ("NO", safe_int(persisted.get("signal_no"), 0))
                live = live_by_key.get(key)
                if live is not None:
                    combined = dict(persisted)
                    combined.update(live)
                    merged.append(combined)
                    seen.add(key)
                else:
                    merged.append(persisted)

            # Include any just-created signal not yet flushed to CSV.
            for live in reversed(live_rows):
                uid = str(live.get("signal_uid") or "").strip()
                key = ("UID", uid) if uid and uid.lower() != "nan" else ("NO", safe_int(live.get("signal_no"), 0))
                if key not in seen:
                    merged.insert(0, live)
                    seen.add(key)
            rows = merged

        elif not rows:
            rows = [dict(x) for x in reversed(live_rows)]

        if not rows:
            return f"Signals today: 0\n\nToday (IST)  •  {td}  •  Newest first\n\nNo signals today."

        targets = sum(1 for r in rows if str(r.get("outcome") or "").upper() == "TARGET HIT")
        sls = sum(1 for r in rows if str(r.get("outcome") or "").upper() == "SL HIT")
        guardians = sum(1 for r in rows if str(r.get("outcome") or "").upper() == "IMMEDIATE EXIT")
        manuals = sum(1 for r in rows if str(r.get("outcome") or "").upper() == "MANUAL EXIT")
        # Daily money headline: count only signals that have a final/locked result.
        # Active TRANSITs are deliberately excluded so the headline is realized paper P/L only.
        day_net = 0.0
        day_brokerage = 0.0
        resolved_count = 0
        for r in rows:
            outcome_r = str(r.get("outcome") or r.get("status") or "").strip().upper()
            if outcome_r in ("TARGET HIT", "SL HIT", "IMMEDIATE EXIT", "MANUAL EXIT", "SESSION CLOSE"):
                _gross_r, brokerage_r, net_r = self._row_paper_pnl(r)
                day_net += safe_float(net_r, 0.0) or 0.0
                day_brokerage += safe_float(brokerage_r, 0.0) or 0.0
                resolved_count += 1

        pnl_word = "PROFIT" if day_net > 0 else ("LOSS" if day_net < 0 else "P/L")
        parts = [
            f"TODAY NET {pnl_word}: {net_amount_marker(day_net)[0]} {rupee_signed(day_net)} | BROKERAGE: {rupee(day_brokerage)}",
            f"Signals today: {len(rows)} | Closed: {resolved_count}",
            f"Targets: {targets} | SL: {sls} | Guardian: {guardians} | Manual: {manuals}",
            f"Today (IST)  •  {td}  •  Newest first",
            "",
        ]

        for row in rows:
            signal_no = safe_int(row.get("signal_no"), 0)
            entry = safe_float(row.get("entry"), 0.0) or 0.0
            target = safe_float(row.get("target"), entry) or entry
            sl = safe_float(row.get("sl"), entry) or entry
            lot_size = max(1, safe_int(row.get("lot"), 1))
            lots = max(1, safe_int(row.get("lots"), DEFAULT_LOTS_PER_SIGNAL))
            quantity = max(1, safe_int(row.get("quantity"), lot_size * lots))

            # Prefer stored V4.0/V4.1 values. Reconstruct legacy/missing display
            # values from the same one_lot_money() function, never from Android.
            money = one_lot_money(entry, target, sl, lot_size, lots=lots)
            amount = safe_float(row.get("amount_used"), money["amount_used"])
            target_gross = safe_float(row.get("target_profit_gross"), money["target_profit_gross"])
            sl_gross = safe_float(row.get("sl_loss_gross"), money["sl_loss_gross"])
            buy_b = safe_float(row.get("brokerage_buy"), money["brokerage_buy"])
            exit_b = safe_float(row.get("brokerage_exit"), money["brokerage_exit"])
            # V8.9: always recompute projected Target/SL net with the current full
            # charge model. Legacy CSV rows may contain old Rs40-only values.
            target_net = safe_float(money.get("target_profit_after_brokerage"), 0.0) or 0.0
            sl_net = safe_float(money.get("sl_loss_after_brokerage"), 0.0) or 0.0

            entry_time = str(row.get("entry_time") or "")
            hhmm = "--:--"
            try:
                dt = datetime.fromisoformat(entry_time)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=IST)
                hhmm = dt.astimezone(IST).strftime("%H:%M")
            except Exception:
                if len(entry_time) >= 16:
                    hhmm = entry_time[11:16]

            symbol = str(row.get("symbol") or contract_label(row)).strip()
            outcome = str(row.get("outcome") or row.get("status") or "TRANSIT").strip().upper()
            if not outcome or outcome == "NAN":
                outcome = "TRANSIT"

            total_brokerage = safe_float(row.get("total_charges"), safe_float(row.get("brokerage_round_trip"), (buy_b or 0) + (exit_b or 0))) or 0.0
            resolved = outcome in ("TARGET HIT", "SL HIT", "IMMEDIATE EXIT", "MANUAL EXIT", "SESSION CLOSE")

            if resolved:
                display_gross, display_brokerage, display_net = self._row_paper_pnl(row)
            else:
                # V7.8: Signals menu must use the same freshest live option snapshot
                # as the first-page TRANSIT card, not only signal_history/CSV last_ltp.
                current_ltp = safe_float(row.get("last_ltp"), entry) or entry
                token = str(row.get("token") or "").strip()
                if token:
                    try:
                        live_quote = self._current_option_snapshot(token)
                        quote_ltp = safe_float(live_quote.get("ltp"), 0.0) or 0.0
                        if quote_ltp > 0:
                            current_ltp = quote_ltp
                    except Exception:
                        pass
                live_money = one_lot_money(entry, target, sl, lot_size, exit_price=current_ltp, lots=lots)
                display_gross = safe_float(live_money.get("gross_pnl_rupees"), 0.0) or 0.0
                display_brokerage = safe_float(live_money.get("total_brokerage_rupees"), total_brokerage) or total_brokerage
                display_net = safe_float(live_money.get("net_pnl_after_brokerage"), display_gross - display_brokerage) or 0.0

            pnl_state, pnl_icon = pnl_traffic_state(display_gross, display_brokerage, display_net)
            call_side = str(row.get("side") or "").strip().upper()
            if call_side not in ("CE","PE"):
                call_side = "CE" if symbol.upper().endswith("CE") else ("PE" if symbol.upper().endswith("PE") else "")
            # V9.0 status-dot rule. Dot represents trade state/exit type, never P/L.
            # Target=green, SL=red, Guardian/Transit exit=blue, running=orange,
            # manual/session close=black.
            if outcome == "TARGET HIT":
                result_icon = "🟢"
            elif outcome == "SL HIT":
                result_icon = "🔴"
            elif outcome == "IMMEDIATE EXIT":
                result_icon = "🔵"
            elif outcome in ("MANUAL EXIT", "SESSION CLOSE"):
                result_icon = "⚫"
            else:
                result_icon = "🟠"
            parts.extend([
                f"{result_icon} #{signal_no}  {hhmm}  {symbol}  |  {pnl_state}",
                f"Option Type: {call_side}" if call_side else "Option Type: --",
                f"Entry - {entry:.2f} | {rupee(amount)}",
                f"Target - {target:.2f} | {rupee_signed(target_net)} net",
                f"SL - {sl:.2f} | {rupee_signed(-abs(sl_net))} net",
                f"Brokerage - {rupee(display_brokerage)}",
            ])

            if resolved:
                result_label = outcome
                accepted_kind = str(row.get("warning_accept_type") or "").upper().strip()
                if outcome == "IMMEDIATE EXIT" and accepted_kind:
                    result_label = "IMMEDIATE EXIT ACCEPTED" if accepted_kind == "IMMEDIATE_EXIT" else "TRANSIT WARNING ACCEPTED"
                if outcome == "TARGET HIT":
                    parts.append(f"🟢 Target Hit | Gross {rupee_signed(display_gross)} | Net {net_amount_marker(display_net)[0]} {rupee_signed(display_net)}")
                elif outcome == "SL HIT":
                    parts.append(f"🔴 Stop Loss Hit | Gross {rupee_signed(display_gross)} | Net {net_amount_marker(display_net)[0]} {rupee_signed(display_net)}")
                else:
                    parts.append(
                        f"RESULT - {result_label} | Gross {rupee_signed(display_gross)} | Net {net_amount_marker(display_net)[0]} {rupee_signed(display_net)}"
                    )
                accepted_kind = str(row.get("warning_accept_type") or "").upper().strip()
                transit_exit_px = safe_float(row.get("warning_accept_price"), safe_float(row.get("guardian_exit_price")))
                if accepted_kind == "TRANSIT_ALERT" and transit_exit_px is not None:
                    parts.append(f"🔵 Transit Hit: {transit_exit_px:.2f}")
                    parts.append(f"Exit - {transit_exit_px:.2f}")
                elif accepted_kind == "IMMEDIATE_EXIT" and transit_exit_px is not None:
                    parts.append(f"🔵 Guardian Exit: {transit_exit_px:.2f}")
                    parts.append(f"Exit - {transit_exit_px:.2f}")
            else:
                parts.append(
                    f"STATUS - {outcome} | Gross {rupee_signed(display_gross)} | Net {net_amount_marker(display_net)[0]} {rupee_signed(display_net)}"
                )

            # Silent means no notification/second settlement.  It is shown only in
            # Signals history so the user can review whether the original T/SL later hit.
            silent_outcome = str(row.get("silent_monitor_outcome") or "").strip().upper()
            if silent_outcome in ("NAN", "NONE"):
                silent_outcome = ""
            silent_active_raw = str(row.get("silent_monitor_active") or "").strip().lower()
            if silent_outcome:
                hit_px = safe_float(row.get("silent_monitor_hit_price"))
                suffix = f" @ {hit_px:.2f}" if hit_px is not None else ""
                parts.append(f"Silent result - {silent_outcome}{suffix} (P/L unchanged)")
            elif silent_active_raw in ("true", "1", "yes"):
                last_silent = safe_float(row.get("silent_monitor_last_ltp"))
                suffix = f" | {last_silent:.2f}" if last_silent is not None else ""
                parts.append(f"Silent monitor - watching original T/SL{suffix}")

            reason_text = str(row.get("final_reason") or "").strip()
            setup = str(row.get("technical_setup") or "").strip()
            valid_setup = bool(setup and setup.lower() != "nan" and setup.upper() != "NONE")
            valid_reason = bool(reason_text and reason_text.lower() != "nan")
            if valid_setup or valid_reason:
                combined_reason = (
                    f"{setup} | {reason_text}" if valid_setup and valid_reason
                    else setup if valid_setup
                    else reason_text
                )
                parts.append(f"Reason: {short_reason(combined_reason, 110)}")
            if valid_setup:
                parts.append(f"Strategy: {setup}")
            parts.append("")

        return "\n".join(parts).rstrip()

    def _write_signals_today_file(self):
        try:
            text = self.signals_today_text()
            day = now_ist().date().isoformat()
            SIGNALS_TODAY_FILE.parent.mkdir(parents=True, exist_ok=True)
            SIGNALS_TODAY_FILE.write_text(f"DATE={day}\n{text}\n", encoding="utf-8")
        except Exception as exc:
            log.debug("Signals today display write skipped: %s", short_reason(exc, 100))

    def stats_text(self):
        if not SIGNAL_LOG_FILE.exists():
            return f"📊 V{VERSION} STATS\nNo signals yet."
        try:
            df = pd.read_csv(SIGNAL_LOG_FILE)
            if df.empty:
                return f"📊 V{VERSION} STATS\nNo signals yet."

            td = now_ist().date().isoformat()
            if "date" in df.columns:
                df = df[df["date"].astype(str) == td]

            outcomes = df["outcome"].fillna("").astype(str).str.upper()
            resolved_mask = outcomes.isin(["TARGET HIT", "SL HIT", "IMMEDIATE EXIT", "MANUAL EXIT", "SESSION CLOSE"])
            resolved = df[resolved_mask].copy()

            if resolved.empty:
                return (
                    f"📊 V{VERSION} STATS\nSignals: {len(df)}\nResolved: 0\n"
                    f"💰 Net paper P/L: {rupee(0)}"
                )

            ro = resolved["outcome"].fillna("").astype(str).str.upper()
            target_hits = int((ro == "TARGET HIT").sum())
            sl_hits = int((ro == "SL HIT").sum())
            early = int((ro == "IMMEDIATE EXIT").sum())
            manual_exit = int((ro == "MANUAL EXIT").sum())
            session_close = int((ro == "SESSION CLOSE").sum())

            # V8.9: Positive/Negative/Flat is determined ONLY by FINAL NET after
            # the complete round-trip charges. Outcome type (Target/SL/Guardian)
            # does not decide whether the trade was financially positive.
            positive = 0
            negative = 0
            flat = 0
            gross_day = 0.0
            brokerage_day = 0.0
            net_day = 0.0
            for _, row in resolved.iterrows():
                gross, brokerage, net = self._row_paper_pnl(row)
                gross_day += gross
                brokerage_day += brokerage
                net_day += net
                if net > 0.005:
                    positive += 1
                elif net < -0.005:
                    negative += 1
                else:
                    flat += 1

            resolved_n = positive + negative + flat
            rate = (100.0 * positive / resolved_n) if resolved_n else 0.0

            return (
                f"📊 V{VERSION} STATS\n"
                f"Signals: {len(df)} | Resolved: {resolved_n}\n"
                f"✅ Positive: {positive} | ❌ Negative: {negative} | ➖ Flat: {flat}\n"
                f"Observed positive rate: {rate:.1f}%\n"
                f"Targets: {target_hits} | SL: {sl_hits} | Early: {early} | Manual: {manual_exit} | Close: {session_close}\n"
                f"💰 Gross P/L: {rupee(gross_day)}\n"
                f"Brokerage/Charges: {rupee(brokerage_day)}\n"
                f"Net after charges: {rupee(net_day)}"
            )
        except Exception as exc:
            return f"📊 STATS ERROR\n{short_reason(exc,80)}"

    def health_alert(self, key, text, cooldown=HEALTH_ALERT_COOLDOWN_SECONDS):
        """Emit health warnings only during armed LIVE operation.

        LOGIN and CLOSED are deliberately silent. LIVE also has a startup grace
        window so data sources have time to initialise before any warning is shown.
        """
        now_ts = time.time()
        if str(getattr(self, "runtime_phase", "")).upper() != "LIVE":
            return
        if now_ts < float(getattr(self, "health_enabled_after", float("inf")) or float("inf")):
            return
        # Missing/stale upstream data is intentionally export-log only in V3.6.8.
        # The safety gates still block entries exactly as before; only the UI/user
        # notification is suppressed. index_v31_runtime.log retains the diagnosis.
        data_only_keys = {
            "ws_recovery_failed",
            "fundamental_error",
            "fund_stale",
            "greeks_not_ready",
            "greek_stale",
            "tech_not_ready",
            "final_review_error",
        }
        if key in data_only_keys:
            log.warning(
                "DATA ALERT (LOG ONLY) | key=%s | detail=%s",
                key, short_reason(text.replace("\n", " | "), 220),
            )
            self.last_health_alert[key] = now_ts
            return

        last = self.last_health_alert.get(key, 0)
        if now_ts - last < cooldown:
            return
        if local_notify(text):
            self.last_health_alert[key] = now_ts

    def heartbeat_worker(self):
        while not self.stop_event.is_set():
            with self.state_lock:
                active_count = len(self.active_transits)
                payload = {
                    "ts": time.time(),
                    "time_ist": now_ist().isoformat(),
                    "pid": os.getpid(),
                    "index": self.index_root,
                    "index_ltp": self.nifty_live,
                    "last_tick_ts": self.last_nifty_tick_ts,
                    "fundamental_last": self.fundamental_state["last_update"],
                    "greeks_last": self.greeks_state["last_update"],
                    "technical_last": self.technical_last_update,
                    "active_transit": bool(active_count),
                    "active_transit_count": active_count,
                }
            try:
                atomic_json_write(HEARTBEAT_FILE, payload)
            except Exception:
                pass
            _daily_measurement_report()
            time.sleep(HEARTBEAT_SECONDS)

    def internal_health_worker(self):
        while not self.stop_event.is_set():
            now_ts = time.time()

            if str(getattr(self, "runtime_phase", "")).upper() != "LIVE":
                time.sleep(5)
                continue

            if now_ts < float(getattr(self, "health_enabled_after", 0.0) or 0.0):
                self.log_data_health()
                time.sleep(5)
                continue

            # V3.6.2 WebSocket policy:
            #   stale/missing tick -> immediately block entry and start silent repair.
            #   warning -> only if reconnect + fresh-login recovery fails for 60s.
            with self.state_lock:
                last_tick = float(self.last_nifty_tick_ts or 0.0)
                recovering = bool(self.websocket_recovery_running)
                ws_state = str(self.websocket_state or "UNKNOWN").upper()
            age = (now_ts - last_tick) if last_tick else (now_ts - float(self.live_confirmed_ts or now_ts))
            if age > WEBSOCKET_STALE_SECONDS and not recovering:
                log.warning(
                    "DATA MISSING | WEBSOCKET | no %s index tick for %ss | state=%s",
                    self.index_root or "INDEX", int(age), ws_state,
                )
                if ws_state == "HEALTHY":
                    self._set_websocket_state("STALE", f"NO INDEX WEBSOCKET TICK FOR {int(age)} SECONDS")
                self._request_websocket_recovery(
                    f"NO {self.index_root or 'INDEX'} WEBSOCKET TICK FOR {int(age)} SECONDS"
                )

            with self.state_lock:
                fund_last = float(self.fundamental_state.get("last_update") or 0.0)
                greek_last = float(self.greeks_state.get("last_update") or 0.0)
                greek_data = dict(self.greeks_state.get("data") or {})
                greek_error = self.greeks_state.get("error")
                tech = dict(self.technical_state)

            if fund_last and now_ts - fund_last > FUNDAMENTAL_STALE_SECONDS and not after_signal_cutoff():
                self.health_alert(
                    "fund_stale",
                    f"⚠️ FUNDAMENTAL DATA STALE\nLast valid scan is {int((now_ts-fund_last)/60)} minutes old.",
                )

            greek_deadline = float(getattr(self, "greeks_grace_deadline", 0.0) or 0.0)
            if greek_deadline and now_ts >= greek_deadline:
                if not greek_data:
                    reason = short_reason(greek_error or "No usable Greeks response", 100)
                    self.health_alert(
                        "greeks_not_ready",
                        "⚠️ LIVE GREEKS NOT AVAILABLE\n"
                        f"Not ready after {LIVE_GREEKS_GRACE_SECONDS} seconds.\n"
                        f"Reason: {reason}",
                        cooldown=5 * 60,
                    )
                elif greek_last and now_ts - greek_last > GREEKS_STALE_SECONDS:
                    self.health_alert(
                        "greek_stale",
                        f"⚠️ GREEKS DATA STALE\nLast Greeks refresh is {int(now_ts-greek_last)} seconds old.",
                    )

            if not tech.get("ok") and now_ist() >= today_at(9, 30):
                err = tech.get("error")
                if err:
                    self.health_alert(
                        "tech_not_ready",
                        f"⚠️ TECHNICAL ENGINE NOT READY\n{err}",
                        cooldown=10 * 60,
                    )

            self.log_data_health()
            time.sleep(5)

    # ----------------------------------------------------------------------
    # Dashboard
    # ----------------------------------------------------------------------

    # ----------------------------------------------------------------------
    # V3.4 CLOSED-MARKET / PREVIOUS-CLOSE SNAPSHOT
    # ----------------------------------------------------------------------

    @staticmethod
    def _latest_completed_session_end():
        """Return a safe historical-data end time for the latest completed session.

        This is read-only market-data support for Android update verification. It
        never creates candidates, signals, TRANSITs, or broker orders.
        """
        n = now_ist()
        d = n.date()

        # Weekend -> previous Friday (or previous weekday after holidays, with
        # the historical endpoint simply returning the most recent data it has).
        while d.weekday() >= 5:
            d -= timedelta(days=1)

        # Before the cash session on a weekday, use the previous weekday.
        if n.weekday() < 5 and n.date() == d and (n.hour, n.minute) < (9, 15):
            d -= timedelta(days=1)
            while d.weekday() >= 5:
                d -= timedelta(days=1)

        # If the current weekday session has already progressed beyond 09:15,
        # query only up to the latest completed 5-minute boundary. After close,
        # 15:30 is the upper bound.
        if n.weekday() < 5 and n.date() == d and (n.hour, n.minute) < (15, 30):
            minute = (n.minute // 5) * 5
            end = n.replace(minute=minute, second=0, microsecond=0) - timedelta(minutes=5)
            floor = n.replace(hour=9, minute=15, second=0, microsecond=0)
            if end < floor:
                d -= timedelta(days=1)
                while d.weekday() >= 5:
                    d -= timedelta(days=1)
                return datetime(d.year, d.month, d.day, 15, 30, tzinfo=IST)
            return end

        return datetime(d.year, d.month, d.day, 15, 30, tzinfo=IST)

    def _choose_index_for_off_market_snapshot(self):
        """Use the normal daily selector, with a master-only fallback for closed markets."""
        try:
            self.choose_index_for_day()
            return
        except Exception as exc:
            log.warning(
                "V3.4 normal index selection unavailable off-market; using nearest-expiry fallback: %s",
                short_reason(exc, 120),
            )

        if not self.index_candidates:
            raise RuntimeError("No active index-option candidates in instrument master")

        earliest = min(x["expiry"] for x in self.index_candidates)
        tied = [x for x in self.index_candidates if x["expiry"] == earliest]

        chosen = None
        for item in sorted(tied, key=lambda x: (x["root"] != "NIFTY", x["root"], x["derivative_exchange"])):
            tok, disp = self._resolve_spot_token(item["root"], item["derivative_exchange"])
            if tok:
                chosen = (item, str(tok), disp or item["root"])
                break
        if chosen is None:
            raise RuntimeError("No spot token available for nearest-expiry index family")

        item, tok, disp = chosen
        self.index_root = item["root"]
        self.index_display_name = disp
        self.spot_token = tok
        self.spot_exchange = item["spot_exchange"]
        self.derivative_exchange = item["derivative_exchange"]
        self.spot_exchange_type = SPOT_WS_TYPE_BY_EXCHANGE[self.spot_exchange]
        self.derivative_exchange_type = DERIV_WS_TYPE_BY_EXCHANGE[self.derivative_exchange]
        self.nearest_expiry = earliest

        df = self.instrument_df.copy()
        opt = df[
            (df["name"].astype(str).str.upper().str.strip() == self.index_root)
            & (df["exch_seg"].astype(str).str.upper().str.strip() == self.derivative_exchange)
            & (df["instrumenttype"].astype(str).str.upper().str.strip() == "OPTIDX")
        ].copy()
        opt["expiry_dt"] = pd.to_datetime(opt["expiry"], format="%d%b%Y", errors="coerce")
        opt["strike_num"] = pd.to_numeric(opt["strike"], errors="coerce") / 100.0
        today = pd.Timestamp.now(tz="Asia/Kolkata").tz_localize(None).normalize()
        opt = opt[opt["expiry_dt"].notna() & (opt["expiry_dt"] >= today)]
        self.nifty_options_df = opt
        self.available_strikes = sorted({
            int(round(float(x)))
            for x in opt[opt["expiry_dt"] == earliest]["strike_num"].dropna().tolist()
        })

        log.info(
            "V3.4 off-market fallback selected %s/%s %s expiry %s",
            self.spot_exchange,
            self.derivative_exchange,
            self.index_root,
            self.nearest_expiry.date(),
        )

    def _ensure_futures_contract_for_selected_index(self):
        """Resolve nearest FUTIDX even when off-market selector used its fallback path."""
        if self.futures_token or self.instrument_df is None or not self.index_root:
            return
        df = self.instrument_df
        fut = df[
            (df["name"].astype(str).str.upper().str.strip() == self.index_root)
            & (df["exch_seg"].astype(str).str.upper().str.strip() == self.derivative_exchange)
            & (df["instrumenttype"].astype(str).str.upper().str.strip() == "FUTIDX")
        ].copy()
        if fut.empty:
            return
        fut["expiry_dt"] = pd.to_datetime(fut["expiry"], format="%d%b%Y", errors="coerce")
        today = pd.Timestamp.now(tz="Asia/Kolkata").tz_localize(None).normalize()
        fut = fut[fut["expiry_dt"].notna() & (fut["expiry_dt"] >= today)].sort_values("expiry_dt")
        if fut.empty:
            return
        row = fut.iloc[0]
        self.futures_token = str(row["token"])
        self.futures_symbol = str(row["symbol"])
        self.futures_expiry = row["expiry_dt"]

    @staticmethod
    def _parse_angel_market_timestamp(value):
        if value in (None, "", 0, "0"):
            return None
        try:
            if isinstance(value, (int, float)) or str(value).strip().replace(".", "", 1).isdigit():
                v = float(value)
                if v > 1e12:
                    v /= 1000.0
                if v > 1e9:
                    return datetime.fromtimestamp(v, tz=IST)
            ts = pd.to_datetime(value, errors="coerce")
            if pd.isna(ts):
                return None
            if getattr(ts, "tzinfo", None) is None:
                return ts.tz_localize(IST).to_pydatetime()
            return ts.tz_convert(IST).to_pydatetime()
        except Exception:
            return None

    def probe_angel_market_state(self):
        """Return OPEN/CLOSED/UNKNOWN from Angel exchange evidence.

        V3.6 never converts a network/API failure into CLOSED. A CLOSED result
        requires a successful Angel FULL market-data response with fetched rows
        but no fresh current-session trade/feed evidence. OPEN still requires
        fresh current-session evidence and the clock is only a sanity boundary.
        """
        self._ensure_futures_contract_for_selected_index()
        n = now_ist()
        details = []
        trade_times = []
        feed_times = []
        successful_full_rows = 0
        historical_probe_ok = False

        requests_to_try = []
        if self.futures_token:
            requests_to_try.append((self.derivative_exchange, self.futures_token, "FUTIDX"))
        if self.spot_token:
            requests_to_try.append((self.spot_exchange, self.spot_token, "SPOT"))

        for exchange, token, label in requests_to_try:
            try:
                r = self.angel_rest_call(self.smart.getMarketData, "FULL", {exchange: [str(token)]})
                fetched = ((r or {}).get("data") or {}).get("fetched", []) or []
                if (r or {}).get("status") and fetched:
                    successful_full_rows += len(fetched)
                for row in fetched:
                    t = self._parse_angel_market_timestamp(
                        row.get("exchTradeTime") or row.get("exchangeTradeTime") or row.get("lastTradeTime")
                    )
                    f = self._parse_angel_market_timestamp(
                        row.get("exchFeedTime") or row.get("exchangeFeedTime") or row.get("feedTime")
                    )
                    if t:
                        trade_times.append(t)
                    if f:
                        feed_times.append(f)
                    details.append(f"{label} FULL OK")
            except Exception as exc:
                details.append(f"{label} FULL ERROR: {short_reason(exc, 60)}")

        fresh_trade = any(
            t.date() == n.date() and -30 <= (n - t).total_seconds() <= MARKET_PROBE_TRADE_FRESH_SECONDS
            for t in trade_times
        )
        fresh_feed = any(
            f.date() == n.date() and -30 <= (n - f).total_seconds() <= MARKET_PROBE_FEED_FRESH_SECONDS
            for f in feed_times
        )

        # V3.7.4: do NOT spend a historical-candle request just to decide whether
        # the market is open. Angel FULL market data already supplies exchange trade/feed
        # timestamps, and getCandleData was our remaining rate-limit hotspot. Historical
        # candles are reserved for indicator seed and proven gap recovery only.
        recent_candle = False
        latest_candle_time = None
        historical_probe_ok = False
        details.append("5M PROBE SKIPPED: Angel FULL trade/feed time used")

        within_exchange_hours = (
            n.weekday() < 5
            and n.replace(hour=9, minute=15, second=0, microsecond=0)
            <= n
            < n.replace(hour=15, minute=30, second=0, microsecond=0)
        )

        # Dhan quote responses can lack a trade time. A successful HTTP response
        # without exchange-time evidence must not be labelled CLOSED.
        if BROKER_SELECTED == "DHAN" and not trade_times and not feed_times:
            successful_full_rows = 0
        broker_probe_ok = successful_full_rows > 0
        is_open = bool(
            broker_probe_ok
            and within_exchange_hours
            and (fresh_trade or fresh_feed)
        )

        if is_open:
            status = "OPEN"
        elif broker_probe_ok:
            status = "CLOSED"
        else:
            status = "UNKNOWN"

        reason_bits = []
        if fresh_trade:
            reason_bits.append("fresh Angel trade time")
        if fresh_feed:
            reason_bits.append("fresh Angel feed time")
        if status == "CLOSED":
            reason_bits.append("Angel FULL feed reachable but no fresh current-session trade evidence")
        elif status == "UNKNOWN":
            reason_bits.append("Angel market state not yet confirmed")

        return {
            "is_open": status == "OPEN",
            "probe_ok": broker_probe_ok,
            "status": status,
            "reason": ", ".join(reason_bits) if reason_bits else "waiting for Angel evidence",
            "trade_time": max(trade_times).isoformat() if trade_times else None,
            "feed_time": max(feed_times).isoformat() if feed_times else None,
            "latest_candle_time": latest_candle_time.isoformat() if latest_candle_time else None,
            "historical_probe_ok": historical_probe_ok,
            "details": details,
        }

    def _refresh_off_market_futures(self, session_date):
        self._ensure_futures_contract_for_selected_index()
        if not self.futures_token or session_date is None:
            return ["FUTURES LTP", "FUTURES VWAP"]
        start = datetime.combine(session_date, datetime.min.time(), tzinfo=IST).replace(hour=9, minute=15)
        end = start.replace(hour=15, minute=30)
        params = {
            "exchange": self.derivative_exchange,
            "symboltoken": self.futures_token,
            "interval": "FIVE_MINUTE",
            "fromdate": start.strftime("%Y-%m-%d %H:%M"),
            "todate": end.strftime("%Y-%m-%d %H:%M"),
        }
        try:
            r = self.angel_rest_call(self.smart.getCandleData, params)
            rows = (r or {}).get("data") or []
            pv = 0.0
            vol = 0.0
            last_close = None
            for row in rows:
                if len(row) < 6:
                    continue
                try:
                    h, l, c = float(row[2]), float(row[3]), float(row[4])
                    v = max(0.0, float(row[5]))
                    last_close = c
                    pv += ((h + l + c) / 3.0) * v
                    vol += v
                except Exception:
                    continue
            with self.state_lock:
                self.futures_ltp = float(last_close or 0.0)
                self.futures_vwap = (pv / vol) if vol > 0 else None
                self.futures_vwap_source = "LAST CLOSED SESSION"
            missing = []
            if not last_close:
                missing.append("FUTURES LTP")
            if vol <= 0:
                missing.append("FUTURES VWAP")
            return missing
        except Exception as exc:
            log.warning("Closed-session futures data unavailable: %s", short_reason(exc, 80))
            return ["FUTURES LTP", "FUTURES VWAP"]

    def _refresh_off_market_option_quotes(self):
        """Best-effort quotes for local BFO Greek proxy; NFO official Greeks do not need this."""
        if not self.contracts:
            return
        tokens = [str(c.get("token")) for c in self.contracts.values() if c.get("token")]
        if not tokens:
            return
        try:
            r = self.angel_rest_call(self.smart.getMarketData, "FULL", {self.derivative_exchange: tokens})
            rows = ((r or {}).get("data") or {}).get("fetched", []) or []
            now_ts = time.time()
            with self.state_lock:
                for row in rows:
                    tok = str(row.get("symbolToken") or row.get("token") or "")
                    if not tok:
                        continue
                    depth = row.get("depth") or {}
                    buys = depth.get("buy") or []
                    sells = depth.get("sell") or []
                    bid = safe_float((buys[0] or {}).get("price"), None) if buys else None
                    ask = safe_float((sells[0] or {}).get("price"), None) if sells else None
                    self.latest_options[tok] = {
                        "ltp": safe_float(row.get("ltp"), None),
                        "bid": bid,
                        "ask": ask,
                        "volume": safe_int(row.get("tradeVolume") or row.get("volumeTradeForTheDay"), 0),
                        "oi": safe_int(row.get("opnInterest") or row.get("openInterest"), 0),
                        "buy_qty": safe_int(row.get("totBuyQuan") or row.get("totalBuyQuantity"), 0),
                        "sell_qty": safe_int(row.get("totSellQuan") or row.get("totalSellQuantity"), 0),
                        "timestamp": now_ts,
                    }
        except Exception as exc:
            log.debug("Off-market option quote refresh skipped: %s", short_reason(exc, 80))

    def _technical_data_availability(self, live=False):
        """Check the exact inputs needed by the technical side.

        V3.6.1 candle policy:
          * CLOSED: last-three-candle validation is not required or displayed.
          * LIVE before 09:30: CANDLE BUILDING ZONE; no missing-candle error.
          * LIVE 09:30: verify the opening three completed candles
            09:15-09:20, 09:20-09:25, 09:25-09:30.
          * LIVE from 09:31 onward: monitor the rolling last three completed
            5-minute candles. A short publication grace avoids flagging a new
            boundary before Angel has published it.
        """
        missing = []
        reasons = []
        last3_available = False
        have_last3 = 0
        last3_times = []
        last3_gap_minutes = []
        last3_reason = None
        missing_last3_times = []
        expected_last3_times = []
        candle_phase = "CLOSED" if not live else "BUILDING"
        candle_intervals = []
        last_data_time = None
        session_date = None
        tech_obj = self.technical

        if tech_obj is None:
            return {
                "last3_available": False,
                "have_last3": 0,
                "last3_times": [],
                "expected_last3_times": [],
                "missing_last3_times": [],
                "last3_gap_minutes": [],
                "last3_reason": "5M ENGINE NOT INITIALIZED" if live else None,
                "candle_phase": candle_phase,
                "candle_intervals": [],
                "core_available": False,
                "missing": [
                    "5M HISTORY", "EMA20", "EMA50", "ATR14", "ADX14",
                    "+DI14", "-DI14", "OPENING RANGE", "DAY HIGH/LOW",
                    "FUTURES LTP", "FUTURES VWAP",
                ],
                "why": ["NO TECHNICAL 5M DATA OBJECT IS READY"],
                "last_data_time": None,
                "session_date": None,
            }

        try:
            with tech_obj.lock:
                df = tech_obj._normalize_df_locked(tech_obj.df.copy())
            if df.empty:
                raise RuntimeError("empty 5m history")

            if live:
                session_date = now_ist().date()
            else:
                session_date = max(df["time"].dt.date)

            sd = df[df["time"].dt.date == session_date].copy().sort_values("time")
            if not sd.empty:
                last_data_time = sd.iloc[-1]["time"].to_pydatetime()

            # --------------------------------------------------------------
            # LIVE candle phase only. CLOSED deliberately skips last-three
            # validation entirely.
            # --------------------------------------------------------------
            if live:
                n = now_ist()
                building_end = n.replace(hour=9, minute=30, second=0, microsecond=0)
                rolling_start = n.replace(hour=9, minute=31, second=0, microsecond=0)
                session_start = n.replace(hour=9, minute=15, second=0, microsecond=0)
                session_last = n.replace(hour=15, minute=25, second=0, microsecond=0)

                if n < building_end:
                    candle_phase = "BUILDING"
                    last3_reason = "CANDLE BUILDING ZONE UNTIL 09:30"
                    # Do not add candle data to `missing`; this is expected.
                else:
                    if n < rolling_start:
                        candle_phase = "OPENING"
                        expected = [
                            session_start,
                            session_start + timedelta(minutes=5),
                            session_start + timedelta(minutes=10),
                        ]
                        candle_intervals = [
                            "09:15-09:20", "09:20-09:25", "09:25-09:30"
                        ]
                    else:
                        candle_phase = "ROLLING"
                        # Give Angel a small publication grace at each exact 5m
                        # boundary so 09:35:02 does not falsely require 09:30 yet.
                        effective = n - timedelta(seconds=20)
                        boundary = effective.replace(
                            minute=(effective.minute // 5) * 5,
                            second=0,
                            microsecond=0,
                        )
                        expected_last = boundary - timedelta(minutes=5)
                        expected_last = min(max(expected_last, session_start), session_last)
                        expected = [
                            expected_last - timedelta(minutes=10),
                            expected_last - timedelta(minutes=5),
                            expected_last,
                        ]
                        expected = [x for x in expected if x >= session_start]
                        candle_intervals = [
                            f"{x.strftime('%H:%M')}-{(x + timedelta(minutes=5)).strftime('%H:%M')}"
                            for x in expected
                        ]

                    expected_last3_times = [x.strftime("%H:%M") for x in expected]
                    actual = {}
                    for ts in sd["time"] if not sd.empty else []:
                        py = ts.to_pydatetime().replace(second=0, microsecond=0)
                        actual[py] = ts

                    found = [x for x in expected if x in actual]
                    absent = [x for x in expected if x not in actual]
                    have_last3 = len(found)
                    last3_times = [x.strftime("%H:%M") for x in found]
                    missing_last3_times = [x.strftime("%H:%M") for x in absent]
                    last3_available = len(expected) == 3 and not absent

                    if absent:
                        last3_reason = "MISSING CANDLE(S): " + ", ".join(missing_last3_times)
                    elif len(expected) < 3:
                        last3_reason = f"ONLY {len(expected)}/3 COMPLETED CANDLES ARE DUE"
                    elif last3_available:
                        last3_gap_minutes = [5.0, 5.0]

                    if not last3_available:
                        missing.append("LAST 3 × 5M CANDLES")
                        reasons.append(last3_reason or "RECENT 5M CANDLES ARE INCOMPLETE")

            # --------------------------------------------------------------
            # Core indicator availability. Historical candles may still be used
            # while CLOSED; last-three validation is simply irrelevant there.
            # --------------------------------------------------------------
            if len(df) < 55:
                missing += ["EMA20", "EMA50", "ATR14", "ADX14", "+DI14", "-DI14"]
                reasons.append(f"INSUFFICIENT 5M HISTORY: {len(df)} CANDLES FOUND, NEED AT LEAST 55")
            else:
                calc = df.copy().sort_values("time").reset_index(drop=True)
                calc["ema20"] = calc["close"].ewm(span=20, adjust=False).mean()
                calc["ema50"] = calc["close"].ewm(span=50, adjust=False).mean()
                prev_close = calc["close"].shift(1)
                tr = pd.concat([
                    (calc["high"] - calc["low"]).abs(),
                    (calc["high"] - prev_close).abs(),
                    (calc["low"] - prev_close).abs(),
                ], axis=1).max(axis=1)
                calc["atr14"] = tr.ewm(alpha=1/14, adjust=False, min_periods=14).mean()
                up_move = calc["high"].diff()
                down_move = -calc["low"].diff()
                plus_dm = up_move.where((up_move > down_move) & (up_move > 0), 0.0)
                minus_dm = down_move.where((down_move > up_move) & (down_move > 0), 0.0)
                atr_w = tr.ewm(alpha=1/14, adjust=False, min_periods=14).mean().replace(0, pd.NA)
                calc["plus_di14"] = 100 * plus_dm.ewm(alpha=1/14, adjust=False, min_periods=14).mean() / atr_w
                calc["minus_di14"] = 100 * minus_dm.ewm(alpha=1/14, adjust=False, min_periods=14).mean() / atr_w
                dx = 100 * (calc["plus_di14"] - calc["minus_di14"]).abs() / (calc["plus_di14"] + calc["minus_di14"]).replace(0, pd.NA)
                calc["adx14"] = dx.ewm(alpha=1/14, adjust=False, min_periods=14).mean()
                latest = calc[calc["time"].dt.date <= session_date].iloc[-1]
                invalid_indicators = []
                for col, label in (
                    ("ema20", "EMA20"), ("ema50", "EMA50"),
                    ("atr14", "ATR14"), ("adx14", "ADX14"),
                    ("plus_di14", "+DI14"), ("minus_di14", "-DI14"),
                ):
                    if pd.isna(latest.get(col)):
                        missing.append(label)
                        invalid_indicators.append(label)
                if invalid_indicators:
                    reasons.append("INDICATOR COULD NOT BE CALCULATED: " + ", ".join(invalid_indicators))

            # Opening range becomes a required technical input only after 09:30
            # in LIVE. In CLOSED it can still be checked from the last session.
            opening = sd[(sd["time"].dt.hour == 9) & (sd["time"].dt.minute.isin([15, 20, 25]))]
            if live:
                n = now_ist()
                building_end = n.replace(hour=9, minute=30, second=0, microsecond=0)
                if n >= building_end and len(opening) < 3:
                    missing.append("OPENING RANGE")
                    reasons.append("09:15 / 09:20 / 09:25 OPENING-RANGE CANDLES ARE INCOMPLETE")
            else:
                if len(opening) < 3:
                    missing.append("OPENING RANGE")
                    reasons.append("LAST SESSION OPENING-RANGE CANDLES ARE INCOMPLETE")

            if sd.empty or pd.isna(sd["high"].max()) or pd.isna(sd["low"].min()):
                missing.append("DAY HIGH/LOW")
                reasons.append("SESSION HIGH/LOW CANNOT BE CALCULATED FROM AVAILABLE CANDLES")
        except Exception as exc:
            missing += [
                "5M HISTORY", "EMA20", "EMA50", "ATR14", "ADX14", "+DI14",
                "-DI14", "OPENING RANGE", "DAY HIGH/LOW",
            ]
            if live:
                last3_reason = last3_reason or "5M HISTORY COULD NOT BE READ"
            reasons.append("5M HISTORY ERROR: " + short_reason(exc, 80))

        with self.state_lock:
            fltp = safe_float(self.futures_ltp, None)
            fvwap = safe_float(self.futures_vwap, None)
            fts = safe_float(self.futures_last_tick_ts, 0.0) or 0.0
        if fltp is None or fltp <= 0:
            missing.append("FUTURES LTP")
            reasons.append("NO USABLE FUTURES LAST-TRADED PRICE WAS RECEIVED")
        if fvwap is None or fvwap <= 0:
            missing.append("FUTURES VWAP")
            reasons.append("FUTURES VWAP COULD NOT BE CALCULATED FROM AVAILABLE FUTURES DATA")
        if live and not fts:
            missing.append("FUTURES LIVE TICK")
            reasons.append("NO CURRENT FUTURES WEBSOCKET TICK")
        elif live and time.time() - fts > FUTURES_STALE_SECONDS:
            missing.append("FUTURES DATA STALE")
            reasons.append(f"LAST FUTURES TICK IS {int(time.time()-fts)} SECONDS OLD")

        # During the candle-building zone, technical entry is intentionally not
        # ready even if historical indicators exist. This is a state, not an error.
        if live and candle_phase == "BUILDING":
            missing.append("CANDLE BUILDING ZONE")
            reasons.append("WAITING FOR 09:15-09:30 OPENING CANDLES TO COMPLETE")

        unique = []
        for x in missing:
            if x not in unique:
                unique.append(x)
        unique_reasons = []
        for x in reasons:
            if x and x not in unique_reasons:
                unique_reasons.append(x)
        return {
            "last3_available": bool(last3_available),
            "have_last3": int(have_last3),
            "last3_times": last3_times,
            "expected_last3_times": expected_last3_times,
            "missing_last3_times": missing_last3_times,
            "last3_gap_minutes": last3_gap_minutes,
            "last3_reason": last3_reason,
            "candle_phase": candle_phase,
            "candle_intervals": candle_intervals,
            "core_available": not unique,
            "missing": unique,
            "why": unique_reasons,
            "last_data_time": last_data_time,
            "session_date": session_date,
        }

    def _greeks_data_availability(self, live=False):
        """Return exact Greek availability plus startup/grace-state information."""
        if not live:
            return {
                "available": False,
                "checking": False,
                "missing": [],
                "why": ["MARKET CLOSED"],
                "last_update": 0.0,
            }

        with self.state_lock:
            data = dict(self.greeks_state.get("data") or {})
            last = float(self.greeks_state.get("last_update") or 0.0)
            err = self.greeks_state.get("error")
            atm = self.current_atm

        now_ts = time.time()
        deadline = float(getattr(self, "greeks_grace_deadline", 0.0) or 0.0)
        checking = bool(not data and deadline and now_ts < deadline)

        if checking:
            remain = max(0, int(math.ceil(deadline - now_ts)))
            return {
                "available": False,
                "checking": True,
                "missing": [],
                "why": [f"WAITING FOR LIVE GREEKS ({remain}s grace remaining)"],
                "last_update": last,
            }

        missing = []
        reasons = []
        required = ("delta", "gamma", "theta", "vega", "iv")

        if atm is None:
            missing.append("ATM STRIKE")
            reasons.append("ATM STRIKE IS NOT RESOLVED")

        if not data:
            missing += ["DELTA", "GAMMA", "THETA", "VEGA", "IV"]
            if err:
                reasons.append("ANGEL GREEKS REQUEST FAILED: " + short_reason(err, 90))
            else:
                reasons.append("ANGEL HAS NOT RETURNED A USABLE LIVE GREEKS RESPONSE")

        if last and now_ts - last > GREEKS_STALE_SECONDS:
            missing.append("GREEKS STALE")
            reasons.append(f"LAST VALID GREEKS UPDATE IS {int(now_ts-last)} SECONDS OLD")

        if atm is not None and data:
            for side in ("CE", "PE"):
                g = data.get((int(atm), side))
                if not g:
                    missing.append(f"ATM {side} GREEKS")
                    reasons.append(f"NO ATM {side} GREEKS ROW WAS RETURNED")
                    continue
                present = set(g.get("_present_fields") or required)
                for field in required:
                    if field not in present or g.get(field) is None:
                        missing.append(f"{side} {field.upper()}")
                        reasons.append(f"{side} {field.upper()} IS MISSING FROM THE GREEKS RESPONSE")

        unique = []
        for x in missing:
            if x not in unique:
                unique.append(x)
        unique_reasons = []
        for x in reasons:
            if x and x not in unique_reasons:
                unique_reasons.append(x)
        return {
            "available": not unique,
            "checking": False,
            "missing": unique,
            "why": unique_reasons,
            "last_update": last,
        }

    def _fundamental_ui_state(self):
        with self.state_lock:
            fund = dict(self.fundamental_state)
        last = float(fund.get("last_update") or 0.0)
        fresh = bool(last and time.time() - last <= FUNDAMENTAL_STALE_SECONDS and not fund.get("error"))
        return {
            "ready": fresh,
            "ce": safe_int(fund.get("ce_probability"), 0),
            "pe": safe_int(fund.get("pe_probability"), 0),
            "sideways": safe_int(fund.get("sideways_probability"), 100),
        }

    def _entry_ui_state(self, candidate, tech_avail, greek_avail):
        with self.state_lock:
            tech = dict(self.technical_state)
            fund = dict(self.fundamental_state)
            review = dict(self.final_review_state)

        reasons = []
        if not tech_avail.get("core_available"):
            reasons += list(tech_avail.get("missing") or [])
        if not tech.get("ok"):
            if tech.get("error"):
                reasons.append(short_reason(tech.get("error"), 70))
        elif not tech.get("entry_ready") or tech.get("direction") not in ("CE", "PE"):
            block_reason = str(tech.get("entry_block_reason") or "").strip()
            reasons.append(block_reason or "NO VALID TECHNICAL SETUP")
        elif safe_float(tech.get("tech_score"), 0.0) < MIN_TECH_SCORE:
            reasons.append("TECH SCORE BELOW 68")
        else:
            direction = tech.get("direction")
            if not self.market_data_fresh():
                reasons.append("LIVE DATA RECOVERY" if str(getattr(self, "websocket_state", "")).upper() in ("RECOVERING", "STALE", "CONNECTING") else "LIVE MARKET DATA STALE")
            if not self.live_technical_confirmation(direction):
                reasons.append("LIVE TECH CONFIRMATION")
            if not self.futures_vwap_confirms(direction):
                reasons.append("FUTURES VWAP DIRECTION")
            fund_ui = self._fundamental_ui_state()
            if not fund_ui["ready"]:
                reasons.append("FUNDAMENTAL DATA")
            else:
                _, blocked, block_reason = self.fundamental_support(direction)
                if blocked:
                    reasons.append(short_reason(block_reason or "FUNDAMENTAL BLOCK", 70))
            if not greek_avail.get("available"):
                if greek_avail.get("checking"):
                    reasons.append("GREEKS CHECKING")
                else:
                    reasons += list(greek_avail.get("missing") or ["GREEKS DATA"])
            elif candidate is None:
                reasons.append("OPTION LIQUIDITY / MOMENTUM")
            else:
                timing_hold = str(candidate.get("entry_timing_hold_reason") or "").strip()
                reentry_hold = str(candidate.get("reentry_hold_reason") or "").strip()
                if timing_hold:
                    reasons.append(timing_hold)
                if reentry_hold:
                    reasons.append(reentry_hold)
                if safe_float(candidate.get("score"), 0.0) < MIN_OPTION_SCORE:
                    reasons.append("OPTION SCORE")
                if safe_float(candidate.get("combined_score"), 0.0) < MIN_COMBINED_SCORE:
                    reasons.append("COMBINED SCORE")
                current_sig = self.setup_signature(tech, direction)
                same_review = tuple(review.get("last_signature") or ()) == tuple(current_sig)
                if review.get("running") and same_review:
                    reasons.append("LUNA REVIEW IN PROGRESS")
                elif same_review and review.get("decision") != "APPROVE":
                    reasons.append(f"LUNA {review.get('decision') or 'WAIT'}")
                elif same_review and review.get("decision") == "APPROVE":
                    reasons.append("ENTRY PRICE / DRIFT CHECK")
                else:
                    reasons.append("WAITING FOR LUNA REVIEW")
        unique=[]
        for x in reasons:
            if x and x not in unique:
                unique.append(x)
        return False, 0, unique[:6]

    def _live_first_candle_status(self):
        """Return readiness for the V3.6.1 live candle phase.

        Before 09:30 the expected state is CANDLE BUILDING ZONE. At 09:30 the
        opening three 5m candles must exist. From 09:31 onward the rolling last
        three completed 5m candles are monitored.
        """
        n = now_ist()
        building_end = n.replace(hour=9, minute=30, second=0, microsecond=0)
        rolling_start = n.replace(hour=9, minute=31, second=0, microsecond=0)

        if n < building_end:
            return True, "CANDLE BUILDING ZONE UNTIL 09:30", None

        if self.technical is None:
            return False, "5M ENGINE NOT INITIALIZED", None

        avail = self._technical_data_availability(live=True)
        phase = avail.get("candle_phase")

        if phase == "OPENING":
            if avail.get("last3_available"):
                return True, "OPENING 3 × 5M CANDLES READY: 09:15-09:20, 09:20-09:25, 09:25-09:30", None
            return False, avail.get("last3_reason") or "OPENING 3 × 5M CANDLES NOT READY", None

        if phase == "ROLLING":
            if avail.get("last3_available"):
                intervals = ", ".join(avail.get("candle_intervals") or [])
                return True, "LAST 3 × 5M CANDLES READY" + (f": {intervals}" if intervals else ""), None
            return False, avail.get("last3_reason") or "LAST 3 × 5M CANDLES NOT READY", None

        return False, avail.get("last3_reason") or "5M CANDLE STATE NOT READY", None

    def _refresh_off_market_candles(self):
        """Fetch recent 5m history, then cross-check and repair the latest closed session.

        V3.6.1 deliberately performs a second, session-scoped Angel historical request.
        This avoids declaring the last three 5-minute candles unavailable merely because
        a wider multi-day historical response omitted an isolated row.  If an expected
        final-session candle is still absent, the engine retries that exact 5-minute slot
        once and reports the exact missing time in the UI.
        """
        end = self._latest_completed_session_end()
        start = end - timedelta(days=10)
        cache_file = PROJECT_DIR / (
            "nifty_5m_cache.csv" if self.index_root == "NIFTY" else f"{self.index_root.lower()}_5m_cache.csv"
        )
        technical = LocalTechnicalEngine(cache_file, self.spot_token, self.spot_exchange)
        with technical.lock:
            technical._load_cache_locked()

        errors = []

        def merge_result(result, source_label):
            if not result or not result.get("status") or not result.get("data"):
                raise RuntimeError(f"Historical data unavailable: {result}")
            seed = pd.DataFrame(
                result["data"],
                columns=["time", "open", "high", "low", "close", "volume"],
            )
            seed = technical._normalize_df_locked(seed)
            if seed.empty:
                raise RuntimeError("Historical response contained no completed 5m candles")
            with technical.lock:
                merged = pd.concat([technical.df, seed], ignore_index=True)
                technical.df = technical._normalize_df_locked(merged)
                technical.seed_source = source_label
                technical.seed_error = None
                technical._save_cache_locked()
            return len(seed)

        # Pass 1: recent history for indicator warm-up.
        broad_params = {
            "exchange": self.spot_exchange,
            "symboltoken": self.spot_token,
            "interval": "FIVE_MINUTE",
            "fromdate": start.strftime("%Y-%m-%d %H:%M"),
            "todate": end.strftime("%Y-%m-%d %H:%M"),
        }
        try:
            result = self.angel_rest_call(self.smart.getCandleData, broad_params)
            merge_result(result, "ANGEL RECENT HISTORY + LOCAL CACHE")
        except Exception as exc:
            errors.append("RECENT HISTORY: " + short_reason(exc, 100))
            log.warning("V3.6.1 recent candle refresh unavailable: %s", errors[-1])

        # Determine the latest actual trading-session date from what Angel/cache supplied.
        session_date = None
        with technical.lock:
            df_now = technical._normalize_df_locked(technical.df.copy())
        if not df_now.empty:
            session_date = max(df_now["time"].dt.date)

        # Pass 2: always re-request that one session in isolation. This is the important
        # cross-check which fixes the old 3/3-but-gap diagnostic.
        if session_date is not None:
            session_start = datetime(
                session_date.year, session_date.month, session_date.day, 9, 15, tzinfo=IST
            )
            n = now_ist()
            if session_date < n.date():
                request_end = datetime(
                    session_date.year, session_date.month, session_date.day, 15, 30, tzinfo=IST
                )
                expected_last = datetime(
                    session_date.year, session_date.month, session_date.day, 15, 25, tzinfo=IST
                )
            else:
                request_end = min(
                    self._latest_completed_session_end(),
                    datetime(session_date.year, session_date.month, session_date.day, 15, 30, tzinfo=IST),
                )
                expected_last = min(
                    request_end,
                    datetime(session_date.year, session_date.month, session_date.day, 15, 25, tzinfo=IST),
                )

            session_params = {
                "exchange": self.spot_exchange,
                "symboltoken": self.spot_token,
                "interval": "FIVE_MINUTE",
                "fromdate": session_start.strftime("%Y-%m-%d %H:%M"),
                "todate": request_end.strftime("%Y-%m-%d %H:%M"),
            }
            try:
                result = self.angel_rest_call(self.smart.getCandleData, session_params)
                merge_result(result, "ANGEL SESSION RECHECK + LOCAL CACHE")
            except Exception as exc:
                errors.append("SESSION RECHECK: " + short_reason(exc, 100))
                log.warning("V3.6.1 session candle recheck unavailable: %s", errors[-1])

            # Pass 3: if one of the expected final three slots is still absent, retry
            # each missing slot directly.  This is diagnostic/recovery only; no signals.
            expected = [expected_last - timedelta(minutes=10), expected_last - timedelta(minutes=5), expected_last]
            with technical.lock:
                df_check = technical._normalize_df_locked(technical.df.copy())
            sd = df_check[df_check["time"].dt.date == session_date].copy()
            present = set(sd["time"].dt.floor("min").tolist())
            missing_slots = [t for t in expected if pd.Timestamp(t).floor("min") not in present]

            for slot in missing_slots:
                slot_params = {
                    "exchange": self.spot_exchange,
                    "symboltoken": self.spot_token,
                    "interval": "FIVE_MINUTE",
                    "fromdate": slot.strftime("%Y-%m-%d %H:%M"),
                    "todate": (slot + timedelta(minutes=5)).strftime("%Y-%m-%d %H:%M"),
                }
                try:
                    result = self.angel_rest_call(self.smart.getCandleData, slot_params)
                    merge_result(result, "ANGEL TARGETED 5M REPAIR + LOCAL CACHE")
                except Exception as exc:
                    # Do not spam notifications: the exact missing candle is shown in UI.
                    errors.append(f"{slot.strftime('%H:%M')} RETRY: {short_reason(exc, 80)}")

        self.technical = technical
        with technical.lock:
            if technical.df.empty:
                return None, " | ".join(errors[:3]) if errors else "NO 5M HISTORY"
            df = technical._normalize_df_locked(technical.df)
            latest = df.iloc[-1]

        candle = {
            "time": str(latest["time"]),
            "open": round(float(latest["open"]), 2),
            "high": round(float(latest["high"]), 2),
            "low": round(float(latest["low"]), 2),
            "close": round(float(latest["close"]), 2),
            "volume": safe_float(latest.get("volume"), 0.0),
        }
        historical_error = " | ".join(errors[:3]) if errors else None
        return candle, historical_error

    def run_off_market_snapshot(self, market_state="CLOSED", force_candle_close=True, prepared=False, market_probe=None):
        """Read-only snapshot for confirmed CLOSED, or LIVE/read-only after cutoff.

        Confirmed CLOSED does not require a last-three-candle check. Historical
        candles may still be fetched once for indicator calculations. CLOSED Greeks
        are simply NOT AVAILABLE / REASON: MARKET CLOSED and never warn.
        """
        closed_mode = str(market_state or "").upper().startswith("CLOSED") or bool(force_candle_close)
        self.runtime_phase = "CLOSED" if closed_mode else "LIVE"
        self.phase_started_ts = time.time()
        self.health_enabled_after = float("inf") if closed_mode else time.time() + LIVE_GREEKS_GRACE_SECONDS

        log.info("V3.6 read-only snapshot starting: %s", "CLOSED" if closed_mode else "LIVE")
        if not prepared:
            self.load_instrument_master()
            self.login()
            self._choose_index_for_off_market_snapshot()
        self._ensure_futures_contract_for_selected_index()

        candle = None
        candle_error = None

        # CLOSED: do not validate, wait for, or display a last-three-candle check.
        # A single best-effort history refresh is used only so historical indicators
        # can still be calculated for the closed-market summary.
        candle, candle_error = self._refresh_off_market_candles()

        # After the CLOSED candle stage (ready or timed out), continue the rest.
        spot_error = None
        try:
            spot = self.initial_spot()
        except Exception as exc:
            spot = 0.0
            spot_error = f"{type(exc).__name__}: {short_reason(exc, 100)}"

        if candle and (force_candle_close or not spot or spot <= 0):
            spot = float(candle["close"])
            with self.state_lock:
                self.nifty_live = spot

        if spot and self.nifty_options_df is not None and self.nearest_expiry is not None:
            expiry_rows = self.nifty_options_df[self.nifty_options_df["expiry_dt"] == self.nearest_expiry]
            atm = self._nearest_available_strike_for(expiry_rows, spot)
            if atm is not None:
                self.build_option_universe(atm)

        session_date = None
        if self.technical is not None:
            try:
                with self.technical.lock:
                    df = self.technical._normalize_df_locked(self.technical.df.copy())
                if not df.empty:
                    session_date = max(df["time"].dt.date)
            except Exception:
                pass
        self._refresh_off_market_futures(session_date)

        if closed_mode:
            # Explicitly clear live Greeks; absence is expected when market is closed.
            with self.state_lock:
                self.greeks_state["data"] = {}
                self.greeks_state["last_update"] = 0.0
                self.greeks_state["error"] = None
        else:
            # LIVE/read-only after the signal cutoff can still show Greeks.
            self.greeks_check_started_ts = time.time()
            self.greeks_grace_deadline = self.greeks_check_started_ts + LIVE_GREEKS_GRACE_SECONDS
            self.greeks_worker()

        # Keep latest news probability available. In CLOSED phase any failure stays
        # on the screen/log only because health_alert is phase-gated to LIVE.
        with self.state_lock:
            fund_last = float(self.fundamental_state.get("last_update") or 0.0)
        if not fund_last or time.time() - fund_last > FUNDAMENTAL_REFRESH_SECONDS:
            self.fundamental_worker()

        availability = self._technical_data_availability(live=not closed_mode)
        greek_availability = self._greeks_data_availability(live=not closed_mode)

        with self.state_lock:
            self.technical_state = {
                "ok": False if closed_mode else bool(availability.get("core_available")),
                "candle_time": candle.get("time") if candle else None,
                "price": candle.get("close") if candle else None,
                "bias": "MARKET CLOSED" if closed_mode else "READ ONLY",
                "entry_ready": False,
                "direction": None,
                "setup": "OFF-MARKET SNAPSHOT" if closed_mode else "LIVE READ ONLY",
                "setup_grade": "NONE",
                "tech_score": 0.0,
                "error": None if availability.get("core_available") else ", ".join(availability.get("missing") or []),
            }
            self.technical_last_update = time.time()

        self.write_live_status(None)
        try:
            payload = json.loads(LIVE_STATUS_FILE.read_text(encoding="utf-8"))
        except Exception:
            payload = {}
        payload.update({
            "version": VERSION,
            "market_state": market_state,
            "market_probe": market_probe or {},
            "data_mode": "LAST_CLOSED_SESSION" if closed_mode else "LIVE_READ_ONLY",
            "last_candle": candle,
            "availability": {"technical": availability, "greeks": greek_availability},
            "off_market_errors": {"spot": spot_error, "candles": candle_error},
        })
        atomic_json_write(LIVE_STATUS_FILE, payload)
        self.write_app_ui(None, market_state=market_state, last_candle=candle)
        atomic_json_write(
            HEARTBEAT_FILE,
            {
                "ts": time.time(),
                "time_ist": now_ist().isoformat(),
                "phase": "CLOSED" if closed_mode else "LIVE_READ_ONLY",
                "version": VERSION,
                "index": self.index_root,
                "market_probe": market_probe or {},
            },
        )
        return True

    def write_live_status(self, candidate=None):
        """Write the current dashboard state to a small JSON file.

        This file is available for future local Android UI/status integration.
        a future local Android UI. Failure to write this file must never stop
        or influence the trading/signal engine.
        """
        try:
            with self.state_lock:
                spot = self.nifty_live
                atm = self.current_atm
                fund = dict(self.fundamental_state)
                tech = dict(self.technical_state)
                greek = dict(self.greeks_state)
                final_review = dict(self.final_review_state)
                active_transits = [dict(v) for v in self.active_transits.values()]
                active_transits.sort(key=lambda x: safe_int(x.get("signal_no"), 0), reverse=True)
                transit = active_transits[0] if active_transits else None
                fvwap = self.futures_vwap
                fltp = self.futures_ltp

            option_candidate = None
            if candidate:
                option_candidate = {
                    "label": contract_label(candidate),
                    "score": round(float(candidate.get("score") or 0.0), 2),
                    "combined_score": round(
                        float(candidate.get("combined_score") or 0.0), 2
                    ),
                    "entry_timing_hold_reason": candidate.get("entry_timing_hold_reason", ""),
                    "reentry_hold_reason": candidate.get("reentry_hold_reason", ""),
                    "premium_momentum_10s": candidate.get("premium_momentum_10s"),
                    "premium_momentum_30s": candidate.get("premium_momentum_30s"),
                }

            transit_data = None
            if transit:
                transit_data = {
                    "signal_no": transit.get("signal_no"),
                    "label": contract_label(transit),
                    "entry": safe_float(transit.get("entry"), 0.0),
                    "target": safe_float(transit.get("target"), 0.0),
                    "sl": safe_float(transit.get("sl"), 0.0),
                    "last_ltp": safe_float(transit.get("last_ltp"), 0.0),
                    "lots": safe_int(transit.get("lots"), 1),
                    "quantity": safe_int(transit.get("quantity"), safe_int(transit.get("lot"),1)),
                    "amount_used": safe_float(transit.get("amount_used"), 0.0),
                    "target_profit_gross": safe_float(transit.get("target_profit_gross"), 0.0),
                    "sl_loss_gross": safe_float(transit.get("sl_loss_gross"), 0.0),
                    "brokerage_buy": safe_float(transit.get("brokerage_buy"), ANGEL_FO_BROKERAGE_PER_EXECUTED_ORDER),
                    "brokerage_exit": safe_float(transit.get("brokerage_exit"), ANGEL_FO_BROKERAGE_PER_EXECUTED_ORDER),
                }

            payload = {
                "schema": 2,
                "version": VERSION,
                "signal_log_file": SIGNAL_LOG_FILE.name,
                "timestamp": time.time(),
                "time_ist": now_ist().strftime("%H:%M:%S IST"),
                "order_execution": "DISABLED / NOT PRESENT",
                "index": self.index_root or "--",
                "derivative_exchange": self.derivative_exchange,
                "index_live": round(float(spot or 0.0), 2),
                "atm": atm,
                "option_expiry": (
                    self.nearest_expiry.strftime("%d-%m-%Y")
                    if self.nearest_expiry is not None else "--"
                ),
                "futures_ltp": (
                    round(float(fltp or 0.0), 2) if fltp is not None else None
                ),
                "futures_vwap": (
                    round(float(fvwap or 0.0), 2) if fvwap is not None else None
                ),
                "fundamental": {
                    "filter": fund.get("filter"),
                    "news_risk": fund.get("news_risk"),
                    "confidence": fund.get("confidence"),
                    "risk_gate": fund.get("risk_gate"),
                    "ce_probability": fund.get("ce_probability"),
                    "pe_probability": fund.get("pe_probability"),
                    "sideways_probability": fund.get("sideways_probability"),
                },
                "technical": {
                    "ready": bool(tech.get("ok")),
                    "bias": tech.get("bias"),
                    "setup": tech.get("setup"),
                    "setup_grade": tech.get("setup_grade"),
                    "adx14": tech.get("adx14"),
                    "plus_di14": tech.get("plus_di14"),
                    "minus_di14": tech.get("minus_di14"),
                    "atr14": tech.get("atr14"),
                    "ema20": tech.get("ema20"),
                    "ema50": tech.get("ema50"),
                    "or_status": tech.get("or_status"),
                    "candlestick_primary": tech.get("candlestick_primary", "NONE"),
                    "candlestick_family": tech.get("candlestick_family", "NONE"),
                    "candlestick_direction": tech.get("candlestick_direction", "NEUTRAL"),
                    "candlestick_bias": tech.get("candlestick_bias", "NEUTRAL"),
                    "candlestick_bonus_ce": tech.get("candlestick_bonus_ce", 0.0),
                    "candlestick_bonus_pe": tech.get("candlestick_bonus_pe", 0.0),
                    "candlestick_patterns": tech.get("candlestick_patterns", []),
                    "entry_ready": bool(tech.get("entry_ready")),
                    "error": tech.get("error"),
                },
                "greeks_ready": bool(greek.get("data")),
                "option_candidate": option_candidate,
                "luna": {
                    "decision": final_review.get("decision"),
                    "confidence": final_review.get("confidence"),
                },
                "active_transit": transit_data,  # legacy/newest active signal
                "active_transits": [
                    {
                        "signal_no": t.get("signal_no"),
                        "label": contract_label(t),
                        "entry": safe_float(t.get("entry"), 0.0),
                        "target": safe_float(t.get("target"), 0.0),
                        "sl": safe_float(t.get("sl"), 0.0),
                        "last_ltp": safe_float(t.get("last_ltp"), 0.0),
                        "quantity": safe_int(t.get("quantity"), safe_int(t.get("lot"),1)),
                        "pending_warning_type": str(t.get("pending_warning_type") or ""),
                    } for t in active_transits
                ],
                "active_transit_count": len(active_transits),
                "signal_triggered_yet": bool(self.signal_history),
                "signal_limit": "NONE (research mode)",
            }
            atomic_json_write(LIVE_STATUS_FILE, payload)
            self.write_app_ui(candidate)
        except Exception as exc:
            log.debug("LIVE status write skipped: %s", short_reason(exc, 80))

    def app_dynamic_panel(self, candidate=None, closed=False, tech=None, fund=None, transit=None):
        """Return a Python-owned Android panel title/body.

        Shadow-learning data deliberately never appears here. The Android host only
        renders this generic frame; Python decides what the frame means at runtime.
        """
        tech = dict(tech or {})
        fund = dict(fund or {})
        transit = dict(transit or {}) if transit else None

        if closed:
            return (
                "ENGINE PANEL",
                "Market closed.\n"
                "Engine is idle and waiting for the next live session.\n"
                "This panel will switch automatically when market state changes."
            )

        if transit:
            setup = str(transit.get("technical_setup") or tech.get("setup") or "ACTIVE SETUP")
            candle = str(tech.get("candlestick_primary") or "NONE")
            return (
                "ENGINE WATCH",
                f"Monitoring active TRANSIT #{transit.get('signal_no')}.\n"
                f"Setup: {setup}\n"
                f"5M candle: {candle}"
            )

        if candidate:
            setup = str(tech.get("setup") or candidate.get("technical_setup") or "VALID SETUP")
            direction = str(tech.get("direction") or candidate.get("side") or "--").upper()
            tscore = safe_float(tech.get("tech_score"), 0.0) or 0.0
            oscore = safe_float(candidate.get("score"), 0.0) or 0.0
            cscore = safe_float(candidate.get("combined_score"), 0.0) or 0.0
            candle = str(tech.get("candlestick_primary") or "NONE")
            return (
                "SETUP WATCH",
                f"{setup} | {direction}\n"
                f"Tech {tscore:.1f} | Option {oscore:.1f} | Combined {cscore:.1f}\n"
                f"5M candle: {candle}"
            )

        setup = str(tech.get("setup") or "NONE")
        bias = str(tech.get("bias") or "WAIT")
        candle = str(tech.get("candlestick_primary") or "NONE")
        candle_bias = str(tech.get("candlestick_bias") or "NEUTRAL")
        or_status = str(tech.get("or_status") or "--")
        if setup not in ("", "NONE", "OFF-MARKET SNAPSHOT"):
            return (
                "TECHNICAL WATCH",
                f"Setup: {setup}\n"
                f"Bias: {bias}\n"
                f"5M candle: {candle} | {candle_bias}"
            )

        return (
            "MARKET WATCH",
            f"Bias: {bias}\n"
            f"Opening range: {or_status}\n"
            f"5M candle: {candle} | {candle_bias}"
        )

    def _active_transit_ui_row_v88(self, t):
        entry = float(safe_float(t.get("entry"), 0.0) or 0.0)
        target = float(safe_float(t.get("target"), entry) or entry)
        sl = float(safe_float(t.get("sl"), entry) or entry)
        ltp = float(safe_float(t.get("last_ltp"), entry) or entry)
        lot_size = max(1, safe_int(t.get("lot"), 1))
        lots = max(1, safe_int(t.get("lots"), DEFAULT_LOTS_PER_SIGNAL))
        live = one_lot_money(entry, target, sl, lot_size, exit_price=ltp, lots=lots)
        gross = safe_float(live.get("gross_pnl_rupees"), 0.0) or 0.0
        charges = safe_float(live.get("total_brokerage_rupees"), 0.0) or 0.0
        net = safe_float(live.get("net_pnl_after_brokerage"), gross - charges) or 0.0
        state = pnl_traffic_state(gross, charges, net)[0]
        return {
            "signal_no": safe_int(t.get("signal_no"), 0),
            "symbol": str(t.get("symbol") or contract_label(t)),
            "contract": contract_label(t),
            "option_type": str(t.get("side") or "").upper(),
            "ltp": round(ltp, 2),
            "entry": round(entry, 2),
            "lots": lots,
            "quantity": max(1, safe_int(t.get("quantity"), lot_size * lots)),
            "amount_used": round(float(safe_float(t.get("amount_used"), entry * lot_size * lots) or 0.0), 2),
            "brokerage_charges": round(charges, 2),
            "brokerage_charges_text": rupee(charges),
            "net_pnl": round(net, 2),
            "net_pnl_text": rupee_signed(net),
            "compact_text": f"#{safe_int(t.get('signal_no'), 0)} | {rupee_signed(net)}",
            "pnl_state": state,
            "pnl_color": "green" if net > 0 else "red" if net < 0 else "amber",
        }

    def write_app_ui(self, candidate=None, market_state=None, last_candle=None):
        """Write the compact Android dashboard with a Python-owned dynamic panel."""
        try:
            with self.state_lock:
                fund = dict(self.fundamental_state)
                tech = dict(self.technical_state)
                active_transits = [dict(v) for v in self.active_transits.values()]
                active_transits.sort(key=lambda x: safe_int(x.get("signal_no"), 0), reverse=True)
                transit = active_transits[0] if active_transits else None
                spot_live = safe_float(self.nifty_live, 0.0) or 0.0
                ws_state = str(getattr(self, "websocket_state", "UNKNOWN") or "UNKNOWN").upper()
                ws_recovering = bool(getattr(self, "websocket_recovery_running", False))
                ws_last_tick = float(self.last_nifty_tick_ts or 0.0)
                manual_refresh_running = bool(getattr(self, "manual_refresh_running", False))
                angel_logged_in = bool(getattr(self, "angel_logged_in", False))
            state_upper = str(market_state or "").upper()
            closed = state_upper.startswith("CLOSED") or (
                market_state is None and str(tech.get("setup") or "").upper() == "OFF-MARKET SNAPSHOT"
            )
            live = not closed
            tech_avail = self._technical_data_availability(live=live)
            greek_avail = self._greeks_data_availability(live=live)
            fund_ui = self._fundamental_ui_state()

            # Compact V3.6.4 dashboard formatting. Candle availability is kept
            # separate from the remaining core-technical availability so a single
            # missing rolling candle can be identified without hiding the status
            # of the other technical inputs.
            ui_missing = list(tech_avail.get("missing") or [])
            core_missing = [
                x for x in ui_missing
                if x not in ("LAST 3 × 5M CANDLES", "CANDLE BUILDING ZONE")
            ]

            if live and tech_avail.get("candle_phase") == "BUILDING":
                core_line = "CORE DATA: BUILDING"
            elif not core_missing:
                core_line = "CORE DATA: AVAILABLE"
            else:
                core_line = "CORE DATA: NOT AVAILABLE"

            if closed:
                greek_line = "GREEKS DATA: NOT AVAILABLE\nREASON: MARKET CLOSED"
            elif greek_avail.get("available"):
                greek_line = "GREEKS DATA: AVAILABLE"
            elif greek_avail.get("checking"):
                greek_line = "GREEKS DATA: CHECKING"
            else:
                greek_line = "GREEKS DATA: NOT AVAILABLE"

            lines = [
                "🔒 CLOSED" if closed else "📡 LIVE",
                f"ANGEL LOGIN: {'LOGGED IN' if angel_logged_in else 'LOGGED OUT'}",
            ]

            if live:
                phase = tech_avail.get("candle_phase") or "BUILDING"
                intervals = list(tech_avail.get("candle_intervals") or [])

                # Show only each candle's closing time: e.g.
                # 10:55-11:00 -> 11:00.
                window_ends = []
                for interval in intervals:
                    text = str(interval)
                    if "-" in text:
                        window_ends.append(text.rsplit("-", 1)[-1].strip())
                    elif text:
                        window_ends.append(text)

                # Missing timestamps are stored as candle START times. Convert
                # them to the same closing-time format used by WINDOW.
                missing_ends = []
                for item in (tech_avail.get("missing_last3_times") or []):
                    try:
                        dt = datetime.strptime(str(item), "%H:%M") + timedelta(minutes=5)
                        missing_ends.append(dt.strftime("%H:%M"))
                    except Exception:
                        missing_ends.append(str(item))

                if phase == "BUILDING":
                    lines.append("5M CANDLES: BUILDING")
                    lines.append("WINDOW: 09:20 | 09:25 | 09:30")
                else:
                    if tech_avail.get("last3_available"):
                        lines.append("5M CANDLES: AVAILABLE")
                    else:
                        lines.append("5M CANDLES: NOT AVAILABLE")

                    if window_ends:
                        lines.append("WINDOW: " + " | ".join(window_ends))

            # CLOSED deliberately has no 5-minute candle row.
            lines.append(core_line)
            lines.append(greek_line)

            if closed:
                lines.append(
                    f"FUNDAMENTAL: CE {fund_ui['ce']}% | PE {fund_ui['pe']}% | SIDEWAYS {fund_ui['sideways']}%"
                )
            else:
                lines.append("")
                lines.append("SIGNAL TRIGGER")
                fund_state = "READY" if fund_ui.get("ready") else "NOT READY"
                lines.append(
                    f"FUND: {fund_state} | CE-{fund_ui['ce']}% | PE-{fund_ui['pe']}% | SW-{fund_ui['sideways']}%"
                )

                if tech_avail.get("candle_phase") == "BUILDING":
                    lines.append("TECH: WAIT | REASON: CANDLE BUILDING")
                elif not core_missing and tech_avail.get("last3_available"):
                    lines.append("TECH: READY")
                else:
                    lines.append("TECH: WAIT | REASON: DATA NOT READY")

                candle_name = str(tech.get("candlestick_primary") or "NONE")
                candle_bias = str(tech.get("candlestick_bias") or "NEUTRAL")
                lines.append(f"CANDLE 5M: {candle_name} | {candle_bias}")

                entry_ready, entry_conf, hold = self._entry_ui_state(candidate, tech_avail, greek_avail)
                if entry_ready and tech_avail.get("candle_phase") != "BUILDING":
                    lines.append(f"ENTRY: READY | CONF-{entry_conf}%")
                else:
                    if tech_avail.get("candle_phase") == "BUILDING":
                        hold = ["CANDLE BUILDING"]

                    # Raw missing/stale API details belong only in exported runtime log.
                    data_words = (
                        "MISSING", "STALE", "RECOVERY", "GREEKS", "FUNDAMENTAL DATA",
                        "5M", "CANDLE BUILDING", "VWAP DIRECTION",
                    )
                    clean_hold = []
                    data_block_present = False
                    for item in (hold or []):
                        text = str(item)
                        upper = text.upper()
                        if any(word in upper for word in data_words):
                            data_block_present = True
                        else:
                            clean_hold.append(text)

                    if clean_hold:
                        reason = ", ".join(clean_hold)
                    elif data_block_present:
                        reason = "DATA NOT READY"
                    else:
                        reason = "WAITING FOR VALID SETUP"
                    lines.append("ENTRY: HOLD | REASON: " + reason)

            transit_text = self.transit_status_text()
            warning_transit = self._pending_warning_snapshot()

            last_data = tech_avail.get("last_data_time")
            if last_data:
                try:
                    last_data_text = last_data.astimezone(IST).strftime("%d-%m-%Y %H:%M")
                except Exception:
                    last_data_text = str(last_data)
            else:
                last_data_text = "--"

            index_line = "MARKET: CLOSED" if closed else "MARKET: LIVE"
            if closed:
                price_line = f"LAST DATA: {last_data_text}"
            else:
                # V3.6.8: WebSocket/API health stays out of the live Android screen.
                # Safety gates still use it internally and the exported runtime log
                # records every missing/stale source and exact missing field.
                root_label = self.index_root or "INDEX"
                price_text = f"{spot_live:.2f}" if spot_live > 0 else "--"
                price_line = f"{root_label} PRICE: {price_text}"
            state_text = market_state or ("CLOSED" if closed else "LIVE")
            dynamic_panel_title, dynamic_panel_text = self.app_dynamic_panel(
                candidate=candidate, closed=closed, tech=tech, fund=fund, transit=transit
            )
            ui = {
                "schema": 5,
                "engine_version": VERSION,
                "angel_logged_in": angel_logged_in,
                "login_status": "LOGGED IN" if angel_logged_in else "LOGGED OUT",
                "login_line": f"ANGEL LOGIN: {'LOGGED IN' if angel_logged_in else 'LOGGED OUT'}",
                "index_line": index_line,
                "price_line": price_line,
                "live_text": "\n".join(lines),
                "transit_text": transit_text,
                "active_transit_count": len(active_transits),
                "total_amount_used": round(sum(safe_float(t.get("amount_used"), 0.0) or 0.0 for t in active_transits), 2),
                "total_amount_used_text": rupee(sum(safe_float(t.get("amount_used"), 0.0) or 0.0 for t in active_transits)),
                "transit_exit_color": "blue",
                "active_transits_ui": [self._active_transit_ui_row_v88(t) for t in active_transits],
                "selected_lots_per_signal": current_lots_per_signal(),
                "selected_lots_text": f"{current_lots_per_signal()} lot(s)",
                "charge_model": CHARGE_MODEL,
                "stats_text": self.stats_text(),
                "signals_text": self.signals_today_text(),
                # V7.1: optional structured colour hint for hosts that support
                # per-field styling. Existing APKs still see the red/green emoji
                # embedded directly beside every NET amount in signals_text.
                "signals_net_color_rule": "negative=red,positive=green,zero=amber",
                "notifications_text": notifications_today_text(),
                "warning_pending": bool(warning_transit),
                "warning_signal_no": safe_int(warning_transit.get("signal_no"), 0) if warning_transit else 0,
                "warning_type": str(warning_transit.get("pending_warning_type") or "") if warning_transit else "",
                "warning_reason": str(warning_transit.get("pending_warning_reason") or "") if warning_transit else "",
                "warning_current_premium": round(float(safe_float(warning_transit.get("last_ltp"), 0.0) or 0.0), 2) if warning_transit else 0.0,
                "warning_accept_label": (
                    "ACCEPT IMMEDIATE EXIT" if warning_transit and str(warning_transit.get("pending_warning_type") or "").upper() == "IMMEDIATE_EXIT"
                    else "ACCEPT TRANSIT WARNING" if warning_transit and str(warning_transit.get("pending_warning_type") or "").upper() == "TRANSIT_ALERT"
                    else ""
                ),
                "warning_decline_label": (
                    "DECLINE IMMEDIATE EXIT" if warning_transit and str(warning_transit.get("pending_warning_type") or "").upper() == "IMMEDIATE_EXIT"
                    else "DECLINE TRANSIT WARNING" if warning_transit and str(warning_transit.get("pending_warning_type") or "").upper() == "TRANSIT_ALERT"
                    else ""
                ),
                "dynamic_panel_title": dynamic_panel_title,
                "dynamic_panel_text": dynamic_panel_text,
                # Legacy key for old APK hosts; contains NO shadow-learning data.
                "learning_text": dynamic_panel_text,
                "service_text": "",
                "market_state": state_text,
                "market_section_label": "🔒 CLOSED" if closed else "📡 LIVE",
            }
            atomic_json_write(APP_UI_FILE, ui)
        except Exception as exc:
            log.debug("APP UI write skipped: %s", short_reason(exc, 100))

    def dashboard(self, candidate=None):
        os.system("clear")
        with self.state_lock:
            atm = self.current_atm
            fund = dict(self.fundamental_state)
            tech = dict(self.technical_state)
            greek = dict(self.greeks_state)
            final_review = dict(self.final_review_state)
            active_transits = [dict(v) for v in self.active_transits.values()]
            active_transits.sort(key=lambda x: safe_int(x.get("signal_no"), 0), reverse=True)
            transit = active_transits[0] if active_transits else None
            signal_triggered = bool(self.signal_history)

        print("="*76)
        print(f"                    INDEX SIGNAL MONITOR V{VERSION}")
        print("="*76)
        print(f"TIME                 : {now_ist().strftime('%H:%M:%S IST')}")
        print(f"INDEX                : {self.index_root or '--'} | {self.derivative_exchange}")
        print(f"ATM                  : {atm}")
        print(f"OPTION EXPIRY        : {self.nearest_expiry.strftime('%d-%m-%Y') if self.nearest_expiry is not None else '--'}")
        print("-"*76)
        print(f"FUNDAMENTAL          : {fund.get('filter')} | Risk {fund.get('news_risk')} | Luna {fund.get('confidence')}%")
        print(f"TECH                 : {'READY' if tech.get('ok') else 'NOT READY'} | {tech.get('bias')} | {tech.get('setup')} {tech.get('setup_grade')}")
        print(f"CANDLE 5M            : {tech.get('candlestick_primary','NONE')} | {tech.get('candlestick_bias','NEUTRAL')} | Bonus CE {safe_float(tech.get('candlestick_bonus_ce'),0.0):.1f} / PE {safe_float(tech.get('candlestick_bonus_pe'),0.0):.1f}")
        print(f"ENTRY READY          : {tech.get('entry_ready')}")
        print(f"GREEKS               : {'READY' if greek.get('data') else 'WAITING'}")
        if candidate:
            print(f"OPTION CANDIDATE     : {contract_label(candidate)} | {candidate['score']:.1f}/100 | Combined {candidate.get('combined_score',0):.1f}")
        else:
            print("OPTION CANDIDATE     : NONE")
        print(f"LUNA                 : {final_review.get('decision')} | {final_review.get('confidence')}%")
        if transit:
            print(f"ACTIVE TRANSITS      : {len(active_transits)} | newest #{transit['signal_no']} {contract_label(transit)} | {safe_int(transit.get('lots'),1)} lot(s) / Qty {safe_int(transit.get('quantity'), safe_int(transit.get('lot'),1))}")
            print(f"MONEY                : Entry {float(transit.get('entry') or 0):.2f} / Used {rupee(transit.get('amount_used'))} | T Profit {rupee(transit.get('target_profit_gross'))} | SL Loss {rupee(transit.get('sl_loss_gross'))}")
            print(f"BROKERAGE/CHARGES    : {rupee(transit.get('brokerage_round_trip'))}")
        else:
            print("ACTIVE TRANSITS      : NONE")
        print(f"SIGNAL TRIGGERED YET : {'YES' if signal_triggered else 'NO'}")
        print("="*76)

    def run(self, prepared=False):
        if not os.environ.get("OPENAI_API_KEY"):
            raise RuntimeError("OPENAI_API_KEY is not available in this environment")

        # engine_main has already confirmed LIVE from Angel data. Clock checks below
        # are only trading-window safety boundaries, never the market-state decision.
        if now_ist().weekday() >= 5 or now_ist() < today_at(PROGRAM_START_HOUR, PROGRAM_START_MINUTE) or after_engine_stop():
            return

        self.runtime_phase = "LIVE"
        self.phase_started_ts = time.time()
        self.live_confirmed_ts = time.time()
        self.health_enabled_after = float("inf")

        threading.Thread(target=self.heartbeat_worker, daemon=True).start()
        if not prepared:
            self.load_instrument_master()
            self.login()
            self.choose_index_for_day()
        self._ensure_futures_contract_for_selected_index()

        # ------------------------------------------------------------------
        # LIVE STEP 1: 5-MINUTE CANDLE FIRST
        # ------------------------------------------------------------------
        cache_file = PROJECT_DIR / (
            "nifty_5m_cache.csv" if self.index_root == "NIFTY"
            else f"{self.index_root.lower()}_5m_cache.csv"
        )
        self.technical = LocalTechnicalEngine(cache_file, self.spot_token, self.spot_exchange)
        self.technical.futures_profile_provider = self._amd_futures_profile_candles

        write_phase_ui(
            "LIVE",
            "STEP 1: 5M CANDLE CHECK",
            [
                "MARKET CONFIRMED: LIVE",
                "Checking Angel completed 5-minute candles first...",
                "No warnings during startup data checks.",
            ],
            market_state="LIVE",
        )

        log.info("Initialising %s local technical engine as LIVE step 1", self.index_root)
        self.technical_state = self.technical.initialize(self.smart, self.angel_rest_call)
        self.technical_last_update = time.time()

        due_wait_started = None
        while not self.stop_event.is_set() and not _android_host_stop_requested():
            ready, reason, expected = self._live_first_candle_status()
            n = now_ist()
            building_end = n.replace(hour=9, minute=30, second=0, microsecond=0)

            if n < building_end:
                # Condition 1: 09:00-09:29 is deliberately a candle-building zone.
                # Do not wait, retry, or warn about missing 5m candles here. Continue
                # live startup so Greeks/fundamental/feed can initialise in parallel.
                self.live_candle_bootstrap_error = None
                write_phase_ui(
                    "LIVE",
                    "CANDLE BUILDING ZONE",
                    [
                        "09:15-09:20: building",
                        "09:20-09:25: building",
                        "09:25-09:30: building",
                        "Technical entry remains WAIT until 09:30.",
                    ],
                    market_state="LIVE",
                )
                break

            if ready:
                self.live_candle_bootstrap_error = None
                write_phase_ui(
                    "LIVE",
                    "STEP 1: 5M CANDLE READY",
                    [reason, "Continuing live startup..."],
                    market_state="LIVE",
                )
                break

            if due_wait_started is None:
                due_wait_started = time.time()

            # At/after 09:30, ask Angel again for already-completed broker candles.
            try:
                self.technical.maybe_recover_history_async()
            except Exception:
                pass
            with self.state_lock:
                try:
                    self.technical_state = self.technical.get_snapshot()
                    self.technical_last_update = time.time()
                except Exception:
                    pass

            elapsed = int(time.time() - due_wait_started)
            phase_name = "OPENING 3 × 5M CHECK" if n < n.replace(hour=9, minute=31, second=0, microsecond=0) else "LAST 3 × 5M CHECK"
            write_phase_ui(
                "LIVE",
                phase_name,
                [
                    f"WAIT: {min(elapsed, LIVE_CANDLE_DUE_GRACE_SECONDS)}/{LIVE_CANDLE_DUE_GRACE_SECONDS}s",
                    f"REASON: {reason}",
                    "Retrying Angel historical backfill...",
                ],
                market_state="LIVE",
            )

            if elapsed >= LIVE_CANDLE_DUE_GRACE_SECONDS:
                self.live_candle_bootstrap_error = reason
                break
            _sleep_until_or_stop(LIVE_CANDLE_RETRY_SECONDS)

        # ------------------------------------------------------------------
        # Remaining LIVE startup after 5m candle step
        # ------------------------------------------------------------------
        spot = self.initial_spot()
        atm = self._nearest_available_strike_for(
            self.nifty_options_df[self.nifty_options_df["expiry_dt"] == self.nearest_expiry],
            spot,
        )
        if atm is None:
            raise RuntimeError("Unable to determine ATM strike")
        option_tokens = self.build_option_universe(atm)

        self.seed_futures_vwap()
        self.start_websocket(option_tokens)

        # Start fundamental cache immediately.
        threading.Thread(target=self.fundamental_worker, daemon=True).start()
        next_fund_due = time.time() + FUNDAMENTAL_REFRESH_SECONDS

        # LIVE Greeks get exactly one full minute of silent startup grace.
        self.greeks_check_started_ts = time.time()
        self.greeks_grace_deadline = self.greeks_check_started_ts + LIVE_GREEKS_GRACE_SECONDS
        self.health_enabled_after = self.greeks_grace_deadline
        threading.Thread(target=self.greeks_worker, daemon=True).start()
        next_greeks_due = time.time() + 15

        # Health worker starts now, but health_alert remains silent until the grace
        # deadline. If Greeks are still absent after 60s, it then issues the warning.
        threading.Thread(target=self.internal_health_worker, daemon=True).start()
        try:
            self.log_data_health(force=True)
        except Exception:
            pass

        local_notify(
            f"📡 V{VERSION} LIVE MONITOR STARTED\n"
            f"Index: {self.index_root} ({self.derivative_exchange})\n"
            "5m startup check completed / continuing\nNo broker orders"
        )

        last_display = 0.0
        candidate = None

        try:
            while not self.stop_event.is_set():
                now_ts=time.time()
                if after_engine_stop(): break

                # Android Menu -> Refresh Data writes MANUAL_REFRESH_FILE. Consume
                # once and refresh in the background; an active TRANSIT is untouched.
                if self._consume_manual_refresh_request():
                    self._request_manual_data_refresh()
                self.maybe_expand_option_universe()
                # V3.4.1 late-start recovery: keep asking Angel for already-formed
                # 5-minute candles until today's completed history is current. This
                # makes a 09:41 restart immediately backfill 09:15..09:35 instead of
                # waiting for this process to build a new 5-minute candle itself.
                if self.technical is not None:
                    self.technical.maybe_recover_history_async()
                with self.state_lock:
                    if self.technical is not None:
                        self.technical_state=self.technical.get_snapshot()

                with self.state_lock:
                    fund_running=self.fundamental_state["running"]
                    fund_error=self.fundamental_state["error"]
                    fund_last=self.fundamental_state["last_update"]
                    fund_last_attempt=self.fundamental_state.get("last_attempt", 0.0)

                normal_due = now_ts >= next_fund_due
                retry_due = bool(fund_error) and (now_ts - float(fund_last_attempt or 0.0) >= FUNDAMENTAL_ERROR_RETRY_SECONDS)

                if not after_signal_cutoff() and not fund_running and (normal_due or retry_due):
                    threading.Thread(target=self.fundamental_worker,daemon=True).start()
                    next_fund_due=now_ts+FUNDAMENTAL_REFRESH_SECONDS

                if market_continuous_session() and now_ts>=next_greeks_due:
                    with self.state_lock: greek_running=self.greeks_state["running"]
                    if not greek_running:
                        threading.Thread(target=self.greeks_worker,daemon=True).start()
                    # During the initial 60-second grace, retry more frequently so the
                    # warning is only raised after several genuine attempts failed.
                    if now_ts < float(self.greeks_grace_deadline or 0.0):
                        next_greeks_due = now_ts + 15
                    else:
                        next_greeks_due = now_ts + GREEKS_REFRESH_SECONDS

                self._consume_warning_decline_request()
                self._consume_warning_accept_request()
                self._consume_manual_exit_request()
                self._consume_close_all_transits_request()
                self.monitor_transit()
                self.monitor_silent_after_accept()
                self.maybe_start_transit_guardian()

                if after_signal_cutoff() and not self.cutoff_message_sent:
                    self.cutoff_message_sent=True
                    local_notify("🕒 NEW SIGNALS STOPPED\n15:00 IST cutoff")

                candidate=None
                if not before_signal_start() and not after_signal_cutoff():
                    with self.state_lock:
                        tech_base=dict(self.technical_state)
                        fund=dict(self.fundamental_state)
                        greek_last=self.greeks_state["last_update"]
                        final_review_snapshot = dict(self.final_review_state)
                        final_review_running = bool(final_review_snapshot.get("running"))
                        old_signature = final_review_snapshot.get("last_signature")

                    # V3.8 MULTI-STRATEGY LEARNING:
                    # V4.4: Each strategy is evaluated independently. A missing EMA setup
                    # does not block ORB/Weapon/VWAP/Liquidity/FVG, and approved strategy
                    # signals remain active in parallel as separate one-lot TRANSITs.
                    strategy_variants = self.technical_strategy_variants(tech_base)
                    market_fresh = self.market_data_fresh()
                    greeks_fresh = bool(greek_last and now_ts-greek_last<=GREEKS_STALE_SECONDS)
                    fund_last = float(fund.get("last_update") or 0.0)
                    fund_stale = (not fund_last) or (now_ts - fund_last > FUNDAMENTAL_STALE_SECONDS)

                    any_ready_strategy = any(
                        v.get("ok") and v.get("entry_ready")
                        and safe_float(v.get("tech_score"), 0.0) >= MIN_TECH_SCORE
                        and str(v.get("direction") or "").upper() in ("CE", "PE")
                        for v in strategy_variants
                    )

                    if any_ready_strategy and fund_stale:
                        # Fundamentals are a shared background risk input, not a strategy
                        # agreement requirement. Refresh once when stale, then continue.
                        if not fund.get("running"):
                            last_attempt = float(fund.get("last_attempt") or 0.0)
                            if now_ts - last_attempt >= FUNDAMENTAL_ERROR_RETRY_SECONDS:
                                threading.Thread(target=self.fundamental_worker, daemon=True).start()
                                next_fund_due = now_ts + FUNDAMENTAL_REFRESH_SECONDS

                    option_cache = {}
                    review_candidate = None
                    review_tech = None
                    review_signature = None
                    review_retry_due = False
                    review_wait_count = int(final_review_snapshot.get("wait_retries") or 0)

                    if market_fresh and not fund_stale and greeks_fresh:
                        for tech_variant in strategy_variants:
                            direction = str(tech_variant.get("direction") or "").upper()
                            if direction not in ("CE", "PE"):
                                continue
                            if not tech_variant.get("ok") or not tech_variant.get("entry_ready"):
                                continue
                            if safe_float(tech_variant.get("tech_score"), 0.0) < MIN_TECH_SCORE:
                                continue

                            setup_sig = self.setup_signature(tech_variant, direction)
                            with self.state_lock:
                                if setup_sig in self.issued_setup_signatures:
                                    continue

                            if not self.live_technical_confirmation(direction, tech_variant):
                                continue
                            # Futures VWAP remains a shared directional safety check; the
                            # strategies themselves do not have to agree with one another.
                            if not self.futures_vwap_confirms(direction):
                                continue

                            support, blocked, block_reason = self.fundamental_support(direction)
                            if blocked:
                                if block_reason:
                                    self.health_alert(
                                        "fund_hard_block",
                                        f"🛑 TECH READY / FUNDAMENTAL BLOCK\nReason: {short_reason(block_reason,60)}",
                                        cooldown=6*60*60,
                                    )
                                continue

                            if direction not in option_cache:
                                selected = self.select_best_option(direction)
                                option_cache[direction] = dict(selected) if selected else None
                            raw0 = option_cache.get(direction)
                            if not raw0:
                                continue
                            raw = dict(raw0)
                            if safe_float(raw.get("score"), 0.0) < MIN_OPTION_SCORE:
                                continue

                            combined, _, block_reason = self.score_candidate_v31(raw, tech_variant, fund)
                            if combined is None:
                                continue
                            timing_ok, timing_reason = self.entry_timing_gate(raw, tech_variant)
                            cooldown_ok, cooldown_reason = self.reentry_cooldown_gate(direction)
                            if not timing_ok:
                                raw["entry_timing_hold_reason"] = timing_reason
                                continue
                            if not cooldown_ok:
                                raw["reentry_hold_reason"] = cooldown_reason
                                continue
                            if safe_float(raw.get("combined_score"), 0.0) < MIN_COMBINED_SCORE:
                                continue

                            # Keep the first fully-passing candidate for UI. Strategies are
                            # already sorted by local score, but another strategy can be used
                            # if the highest one is currently in Luna WAIT delay.
                            if candidate is None:
                                candidate = raw

                            same_signature = tuple(old_signature or ()) == tuple(setup_sig)
                            retry_due = (
                                same_signature
                                and str(final_review_snapshot.get("decision") or "").upper() == "WAIT"
                                and review_wait_count <= LUNA_WAIT_MAX_RECHECKS
                                and float(final_review_snapshot.get("next_retry_ts") or 0.0) > 0
                                and now_ts >= float(final_review_snapshot.get("next_retry_ts") or 0.0)
                            )
                            first_review = not same_signature

                            if not final_review_running and (first_review or retry_due):
                                review_candidate = raw
                                review_tech = tech_variant
                                review_signature = setup_sig
                                review_retry_due = retry_due
                                break

                    if review_candidate is not None and review_tech is not None and review_signature is not None:
                        candidate = review_candidate
                        fund_snapshot={
                            "filter":fund.get("filter"),"risk_gate":fund.get("risk_gate"),
                            "direction_score":fund.get("direction_score"),"market_bias":fund.get("market_bias"),
                            "news_risk":fund.get("news_risk"),"confidence":fund.get("confidence"),
                            "support_for_candidate":review_candidate.get("fundamental_support"),
                            "text":fund.get("text","")[:2500]
                        }
                        if review_retry_due:
                            log.info(
                                "LUNA WAIT RECHECK | setup=%s | side=%s | retry=%s/%s | candidate=%s",
                                review_tech.get("setup"), review_tech.get("direction"),
                                review_wait_count, LUNA_WAIT_MAX_RECHECKS, review_candidate.get("symbol"),
                            )
                        else:
                            log.info(
                                "MULTI-STRATEGY REVIEW | setup=%s | side=%s | tech=%s | option=%s | combined=%s",
                                review_tech.get("setup"), review_tech.get("direction"),
                                review_tech.get("tech_score"), review_candidate.get("score"),
                                review_candidate.get("combined_score"),
                            )
                        threading.Thread(
                            target=self.final_review_worker,
                            args=(dict(review_candidate), dict(review_tech), fund_snapshot, review_signature),
                            daemon=True,
                        ).start()

                    self.record_rejected_setup(candidate)

                self.update_rejected_setup_outcomes()
                if now_ts-last_display>=1:
                    last_display=now_ts
                    self.write_live_status(candidate)
                    self.dashboard(candidate)
                time.sleep(.20)
        except KeyboardInterrupt:
            log.info("Manual stop requested")
        finally:
            try:
                self.log_api_health_summary(force=True)
            except Exception:
                pass
            try:
                self.log_rejected_research_summary()
            except Exception:
                pass
            self.stop_event.set()
            terminals=[]
            with self.state_lock:
                for signal_no, live_transit in list(self.active_transits.items()):
                    live_transit["outcome"] = "SESSION CLOSE"
                    live_transit["outcome_time"] = now_ist().isoformat()
                    self._apply_terminal_money(live_transit, "SESSION CLOSE", live_transit.get("last_ltp"))
                    terminals.append(dict(live_transit))
                self.active_transits.clear()
            for terminal in terminals:
                self.record_terminal_risk_state(terminal)
                local_notify(
                    f"🟦 SESSION CLOSE #{terminal['signal_no']}\n{contract_label(terminal)} | {safe_int(terminal.get('lots'),1)} lot(s) (Qty {safe_int(terminal.get('quantity'), safe_int(terminal.get('lot'),1))})\n"
                    f"Final: {float(terminal.get('last_ltp') or 0):.2f}\n{self._money_result_line(terminal)}"
                )
            self.save_signal_log(); local_notify(self.stats_text()); local_notify(f"🛑 V{VERSION} ENGINE STOPPED")
            try:
                self._close_websocket_quiet()
            except Exception: pass
            try: atomic_json_write(HEARTBEAT_FILE,{"ts":time.time(),"time_ist":now_ist().isoformat(),"phase":"STOPPED"})
            except Exception: pass
# ============================================================================
# ANDROID ENGINE ENTRY
# ============================================================================

def _android_host_stop_requested():
    return os.environ.get("NIFTY_ANDROID_STOP", "").strip() == "1"


def _sleep_until_or_stop(seconds):
    deadline = time.time() + max(0.0, float(seconds))
    while time.time() < deadline:
        if _android_host_stop_requested():
            return False
        time.sleep(min(5.0, max(0.2, deadline - time.time())))
    return True


def _inside_live_signal_window(dt=None):
    n = dt or now_ist()
    if n.weekday() >= 5:
        return False
    start = n.replace(hour=PROGRAM_START_HOUR, minute=PROGRAM_START_MINUTE, second=0, microsecond=0)
    end = n.replace(hour=ENGINE_STOP_HOUR, minute=ENGINE_STOP_MINUTE, second=0, microsecond=0)
    return start <= n < end


def _inside_cash_market_window(dt=None):
    n = dt or now_ist()
    if n.weekday() >= 5:
        return False
    start = n.replace(hour=9, minute=15, second=0, microsecond=0)
    end = n.replace(hour=15, minute=30, second=0, microsecond=0)
    return start <= n < end


def _seconds_to_next_live_window(dt=None):
    n = dt or now_ist()
    candidate = n.replace(hour=PROGRAM_START_HOUR, minute=PROGRAM_START_MINUTE, second=0, microsecond=0)
    if n >= candidate or n.weekday() >= 5:
        candidate += timedelta(days=1)
    while candidate.weekday() >= 5:
        candidate += timedelta(days=1)
    return max(1, int((candidate - n).total_seconds()))


def _fresh_totp_from_android_secret():
    load_secrets_file()
    if not os.environ.get("OPENAI_API_KEY"):
        raise RuntimeError("OPENAI_API_KEY is missing from ~/NiftyMonitor/.secrets.env")
    _assert_broker_selection()
    if BROKER_SELECTED == "DHAN":
        # DhanDataClient verifies/reuses the saved session, and generates a fresh
        # TOTP only when authentication actually requires one.
        if not os.environ.get("DHAN_CLIENT_ID"):
            raise RuntimeError("DHAN_CLIENT_ID is missing")
        return "DHAN_SESSION"
    secret = os.environ.get("ANGEL_TOTP_SECRET", "").strip()
    if not secret:
        raise RuntimeError("ANGEL_TOTP_SECRET is missing from ~/NiftyMonitor/.secrets.env")
    try:
        clean_secret = secret.replace(" ", "").replace("-", "").upper()
        totp = pyotp.TOTP(clean_secret).now()
    except Exception as exc:
        raise RuntimeError(f"Could not generate Angel TOTP automatically: {exc}") from exc
    if not re.fullmatch(r"\d{6}", totp):
        raise RuntimeError("Automatic Angel TOTP generation did not return 6 digits")
    return totp


def _confirm_market_state(engine, timeout_seconds=MARKET_CONFIRM_TIMEOUT_SECONDS, progress_details=None):
    """Require consecutive Angel confirmations before choosing CLOSED or LIVE.

    UNKNOWN means Angel data could not prove either state; keep waiting silently.
    This is the crucial state gate before any CLOSED/LIVE data workflow starts.
    """
    deadline = time.time() + max(5, int(timeout_seconds))
    last_status = None
    same_count = 0
    last_probe = None
    attempt = 0

    while not _android_host_stop_requested() and time.time() < deadline:
        attempt += 1
        probe = engine.probe_angel_market_state()
        last_probe = probe
        status = str(probe.get("status") or "UNKNOWN").upper()
        reason = str(probe.get("reason") or "Waiting for Angel exchange evidence")

        if status in ("OPEN", "CLOSED") and probe.get("probe_ok"):
            if status == last_status:
                same_count += 1
            else:
                last_status = status
                same_count = 1
        else:
            last_status = None
            same_count = 0

        # Keep the UI simple while Angel confirmation is in progress.
        write_phase_ui(
            "MARKET_CHECK",
            details=progress_details or [],
            market_state="CHECKING",
        )

        if same_count >= MARKET_CONFIRM_CONSECUTIVE:
            return probe

        _sleep_until_or_stop(MARKET_CONFIRM_INTERVAL_SECONDS)

    # Do not guess CLOSED on timeout/API failure.
    return {
        "is_open": False,
        "probe_ok": False,
        "status": "UNKNOWN",
        "reason": (
            (last_probe or {}).get("reason")
            or "Market state could not be confirmed from Angel data"
        ),
        "details": (last_probe or {}).get("details", []),
    }


def _sleep_until_stop_or_refresh(seconds):
    """Sleep for CLOSED/read-only cycles, but wake immediately on app Refresh."""
    deadline = time.time() + max(0.0, float(seconds))
    while time.time() < deadline:
        if _android_host_stop_requested():
            return "STOP"
        try:
            if MANUAL_REFRESH_FILE.exists():
                try:
                    MANUAL_REFRESH_FILE.unlink()
                except Exception:
                    pass
                return "REFRESH"
        except Exception:
            pass
        time.sleep(min(1.0, max(0.2, deadline - time.time())))
    return "TIMEOUT"


def engine_main():
    """V3.6 Android lifecycle: LOGIN -> CONFIRM MARKET -> CLOSED or LIVE.

    LOGIN is shown as short one-line steps on the Android UI. Market confirmation
    remains notification-silent, and CLOSED/LIVE is never guessed from clock time alone.
    """
    os.environ.pop("NIFTY_ANDROID_STOP", None)
    _prepare_today_notification_file()
    if not acquire_single_engine_lock():
        # A healthy first instance owns the OS lock. Do not login, create WebSockets,
        # call historical APIs, or overwrite its live state from this duplicate.
        return False
    _record_engine_gap_on_start()
    persist_angel_login_state(False, reason="Engine starting", notify=False)
    log.info("V%s phase-pipeline lifecycle started", VERSION)

    # V6.9: keep one engine/session alive for the whole Python process.
    # CLOSED rechecks and app Refresh must not create a new Angel session.
    engine = None

    while not _android_host_stop_requested():
        phase = "LOGIN"
        steps = [
            "FEEDING TOTP: WAITING",
            "INSTRUMENT MASTER: WAITING",
            "ANGEL VERIFICATION: WAITING",
            "INDEX SELECTION: WAITING",
            "FUTURES CHECK: WAITING",
            "MARKET STATUS: WAITING",
        ]

        def show_login(step_text=""):
            # Show concise startup steps, one per line.
            write_phase_ui(
                "LOGIN",
                details=steps,
                market_state="LOGIN",
            )

        try:
            # --------------------------------------------------------------
            # 1/6 Credentials + fresh TOTP
            # --------------------------------------------------------------
            steps[0] = "FEEDING TOTP: CHECKING"
            show_login("STEP 1/6: CREDENTIALS / TOTP")
            totp = _fresh_totp_from_android_secret()
            steps[0] = "FEEDING TOTP: READY"
            show_login("STEP 1/6: READY")

            if engine is None:
                engine = IndexSignalEngineV31(totp)
            else:
                # Fresh TOTP is kept available for a genuine future re-login, but
                # merely refreshing/reopening the UI does not create a new session.
                engine.totp = str(totp).strip()
            engine.runtime_phase = "LOGIN"
            engine.phase_started_ts = time.time()
            engine.health_enabled_after = float("inf")

            # --------------------------------------------------------------
            # 2/6 Instrument master
            # --------------------------------------------------------------
            if engine.instrument_df is None or engine.instrument_df.empty:
                steps[1] = "INSTRUMENT MASTER: LOADING"
                show_login("STEP 2/6: INSTRUMENT MASTER")
                engine.load_instrument_master()
            else:
                steps[1] = "INSTRUMENT MASTER: CACHED"
                show_login("STEP 2/6: USING CACHE")
            steps[1] = "INSTRUMENT MASTER: READY"
            show_login("STEP 2/6: READY")

            # --------------------------------------------------------------
            # 3/6 Angel session
            # --------------------------------------------------------------
            with engine.state_lock:
                session_present = bool(
                    engine.angel_logged_in
                    and engine.smart is not None
                    and engine.auth_token
                    and engine.feed_token
                )

            if session_present:
                # V6.9: Refresh/CLOSED recheck reuses the already-authenticated
                # SmartAPI session. Do not generate another JWT/feed token.
                steps[2] = "DHAN VERIFICATION: SESSION REUSED"
                persist_angel_login_state(
                    True, reason="Existing Dhan session reused", notify=False
                )
                show_login("STEP 3/6: ALREADY LOGGED IN")
            else:
                steps[2] = "DHAN VERIFICATION: CONNECTING"
                show_login("STEP 3/6: DHAN LOGIN")
                engine.login()
                steps[2] = "DHAN VERIFICATION: READY"
                show_login("STEP 3/6: READY")

            # --------------------------------------------------------------
            # 4/6 Index selection
            # --------------------------------------------------------------
            steps[3] = "INDEX SELECTION: CHECKING"
            show_login("STEP 4/6: INDEX RESOLUTION")
            engine._choose_index_for_off_market_snapshot()
            selected_index = str(engine.index_root or "READY").strip()
            steps[3] = f"INDEX SELECTED: {selected_index}"
            show_login("STEP 4/6: READY")

            # --------------------------------------------------------------
            # 5/6 Futures contract
            # --------------------------------------------------------------
            steps[4] = "FUTURES CHECK: CHECKING"
            show_login("STEP 5/6: FUTURES RESOLUTION")
            engine._ensure_futures_contract_for_selected_index()
            if engine.futures_token:
                fut_label = str(engine.futures_symbol or "READY").strip()
                steps[4] = f"FUTURES CHECK: {fut_label}"
            else:
                steps[4] = "FUTURES CHECK: NOT AVAILABLE"
            show_login("STEP 5/6: COMPLETE")

            # --------------------------------------------------------------
            # 6/6 Crucial market-state confirmation
            # --------------------------------------------------------------
            phase = "MARKET_CHECK"
            engine.runtime_phase = "MARKET_CHECK"
            steps[5] = "MARKET STATUS: CHECKING"
            write_phase_ui(
                "MARKET_CHECK",
                details=steps,
                market_state="CHECKING",
            )

            probe = _confirm_market_state(engine, progress_details=steps)
            status = str(probe.get("status") or "UNKNOWN").upper()
            log.info("Dhan market confirmation: %s | %s", status, probe.get("reason"))

            if status == "UNKNOWN":
                # Silent retry; never guess CLOSED just because a probe failed.
                write_phase_ui(
                    "MARKET_CHECK",
                    details=steps,
                    market_state="CHECKING",
                )
                _sleep_until_or_stop(LOGIN_RETRY_SECONDS)
                continue

            if status == "OPEN":
                phase = "LIVE"
                engine.runtime_phase = "LIVE"
                engine.live_confirmed_ts = time.time()
                write_phase_ui(
                    "LIVE",
                    market_state="LIVE",
                )

                if not after_signal_cutoff():
                    engine.run(prepared=True)
                    if _android_host_stop_requested():
                        break
                    continue

                # Exchange is LIVE but new-signal cutoff has passed.
                engine.run_off_market_snapshot(
                    market_state="LIVE / NO NEW SIGNALS",
                    force_candle_close=False,
                    prepared=True,
                    market_probe=probe,
                )
                sleep_for = 60

            else:
                phase = "CLOSED"
                engine.runtime_phase = "CLOSED"
                engine.health_enabled_after = float("inf")
                write_phase_ui(
                    "CLOSED",
                    market_state="CLOSED",
                )
                engine.run_off_market_snapshot(
                    market_state="CLOSED",
                    force_candle_close=True,
                    prepared=True,
                    market_probe=probe,
                )

                n = now_ist()
                # Re-check more frequently during normal daytime so a genuine OPEN
                # transition is discovered promptly; holidays simply stay CLOSED.
                if n.weekday() < 5 and 8 <= n.hour <= 16:
                    sleep_for = 60
                else:
                    sleep_for = 15 * 60

            if _android_host_stop_requested():
                break
            sleep_result = _sleep_until_stop_or_refresh(sleep_for)
            if sleep_result == "REFRESH":
                # Re-run login/market confirmation immediately so CLOSED/LIVE and
                # all read-only data are refreshed from Angel.
                continue

        except Exception as exc:
            if _android_host_stop_requested():
                break

            log.exception("V%s %s phase error", VERSION, phase)

            # LOGIN / MARKET_CHECK / CLOSED: never throw warning notifications.
            # Show the exact step/error in the app and retry silently.
            if phase in ("LOGIN", "MARKET_CHECK", "CLOSED"):
                write_phase_ui(
                    "LOGIN" if phase == "LOGIN" else ("CLOSED" if phase == "CLOSED" else "MARKET_CHECK"),
                    details=[f"{BROKER_LABEL}: {short_reason(exc, 180)}"],
                    market_state=phase,
                )
            else:
                # Once LIVE is confirmed, genuine runtime failures may alert.
                try:
                    local_notify(
                        f"⚠️ V{VERSION} LIVE ENGINE ERROR\n"
                        f"{type(exc).__name__}: {short_reason(exc, 180)}\n"
                        "Retrying automatically / no orders"
                    )
                except Exception:
                    pass

            _sleep_until_or_stop(LOGIN_RETRY_SECONDS)

    # V6.8: STOP always leaves Angel visibly/logically logged out.
    try:
        if engine is not None:
            engine.logout(reason="Engine stopped", notify=True)
        else:
            persist_angel_login_state(False, reason="Engine stopped", notify=True)
    except Exception:
        persist_angel_login_state(False, reason="Engine stopped", notify=True)

    try:
        atomic_json_write(
            HEARTBEAT_FILE,
            {
                "ts": time.time(),
                "time_ist": now_ist().isoformat(),
                "phase": "STOPPED",
                "version": VERSION,
            },
        )
    except Exception:
        pass
    log.info("V%s phase-pipeline lifecycle stopped", VERSION)
    release_single_engine_lock()
    return True


# Stable class alias for the Android host STOP bridge and future compatible updates.
IndexSignalEngineV34 = IndexSignalEngineV31
IndexSignalEngineV35 = IndexSignalEngineV31
IndexSignalEngineV352 = IndexSignalEngineV31
IndexSignalEngineV360 = IndexSignalEngineV31
IndexSignalEngineV361 = IndexSignalEngineV31
IndexSignalEngineV362 = IndexSignalEngineV31
IndexSignalEngineV363 = IndexSignalEngineV31
IndexSignalEngineV364 = IndexSignalEngineV31
IndexSignalEngineV367 = IndexSignalEngineV31
IndexSignalEngineV368 = IndexSignalEngineV31
IndexSignalEngineV370 = IndexSignalEngineV31
IndexSignalEngineV371 = IndexSignalEngineV31
IndexSignalEngineV680 = IndexSignalEngineV31
IndexSignalEngineV690 = IndexSignalEngineV31


if __name__ == "__main__":
    engine_main()