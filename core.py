#!/usr/bin/env python3
"""PRISM -- Hyperliquid perpetuals signal engine.

Fuses trend, market structure/SMC, volume, momentum, volatility, and
multi-timeframe confluence into a 0-100 score; above a confidence
threshold it emits a LONG/SHORT signal with entry/stop/targets to
Telegram. Read-only decision support -- never places or amends orders.
Runs every 15 min (cron/GitHub Actions); state persisted in state.json.
"""

from __future__ import annotations

import os
import sys
import json
import copy
import math
import time
import fcntl
import random
import logging
import argparse
import statistics
import threading
import collections
from concurrent.futures import ThreadPoolExecutor
import urllib.request
import urllib.error
from dataclasses import dataclass
from datetime import datetime, timezone, timedelta
from typing import Any, Dict, List, Optional, Tuple, Sequence

LOG_LEVEL = os.environ.get("PRISM_LOG_LEVEL", "INFO").upper()
logging.basicConfig(
    level=getattr(logging, LOG_LEVEL, logging.INFO),
    format="%(asctime)s UTC | %(levelname)-7s | %(name)s | %(message)s",
)
logging.Formatter.converter = time.gmtime
log = logging.getLogger("PRISM")

ENGINE_NAME = "PRISM"
ENGINE_VERSION = "1.1.6"
# State-file schema. v5 = feature-validator window gating + shadow recovery,
# realized_r on closed records, compacted daily_stats. v6 = never-pruned
# compact trade_archive, breaker + starvation state, daily_stats_archive
# (see _migrate_state).
STATE_SCHEMA_VERSION = 6

TG_BOT_TOKEN = os.environ.get("TG_BOT_TOKEN", "")
TG_CHAT_ID = os.environ.get("TG_CHAT_ID", "")
TELEGRAM_ENABLED = bool(TG_BOT_TOKEN and TG_CHAT_ID)
if not TELEGRAM_ENABLED:
    log.warning(
        "TG_BOT_TOKEN and/or TG_CHAT_ID is missing/empty -- running in "
        "signal-generation-only mode; no Telegram dispatch will occur."
    )

STATE_PATH = os.environ.get("PRISM_STATE_PATH", "state.json")
CANDLE_CACHE_PATH = os.environ.get("PRISM_CANDLE_CACHE_PATH", "candle_cache.json")
LOCK_PATH = os.environ.get("PRISM_LOCK_PATH", "prism_engine.lock")

HL_API_URL = os.environ.get("HL_API_URL", "https://api.hyperliquid.xyz/info")
HL_MAX_WEIGHT_PER_MIN = 1150
HL_REQUEST_TIMEOUT_SEC = 15
HL_MAX_RETRIES = 4
HL_BACKOFF_BASE_SEC = 0.75

# Symbols are scanned concurrently (I/O-bound: each is mostly waiting on
# Hyperliquid HTTP calls). All threads share HyperliquidClient's single
# _WeightRateLimiter, so raising this doesn't bypass the weight budget --
# it just lets more symbols queue up waiting on the same pacer instead of
# waiting on each other one at a time. Override via env if needed.
SCAN_WORKER_THREADS = int(os.environ.get("PRISM_SCAN_WORKERS", "6"))

WATCHLIST: List[str] = [
    "BTC", "ETH", "HYPE", "ZEC", "NEAR", "ONDO", "SUI", "PENGU", "BNB", "SOL",
    "TRX", "BCH", "DOGE", "ADA", "DOT", "TAO", "AVAX", "LINK", "AAVE", "XRP",
    "XLM", "UNI", "LTC", "APT", "PENDLE",
]

TIMEFRAMES: Dict[str, str] = {
    "1D": "Long-term institutional bias",
    "4H": "Primary trend",
    "1H": "Trend confirmation, market regime",
    "30M": "Setup formation, confluence",
    "15M": "Entry execution, final decision",
}
EXECUTION_TF = "15M"
HL_INTERVAL_MAP = {"1D": "1d", "4H": "4h", "1H": "1h", "30M": "30m", "15M": "15m"}

CANDLE_LOOKBACK: Dict[str, int] = {
    "1D": 400, "4H": 600, "1H": 700, "30M": 800, "15M": 900,
}
CANDLE_STALE_AFTER_SEC: Dict[str, int] = {
    "1D": 3 * 86400, "4H": 6 * 3600, "1H": 3 * 3600, "30M": 2 * 3600, "15M": 45 * 60,
}
CANDLE_REFETCH_OVERLAP_BARS: Dict[str, int] = {
    # On every incremental fetch, re-request this many already-cached
    # trailing *closed* candles (in addition to anything newer) instead of
    # starting exactly at the last cached timestamp. The merge step below
    # overwrites the cached rows with whatever comes back, so this makes the
    # cache self-healing against an exchange-side candle that was still
    # finalizing (missing/short-lived stale close) at the moment a previous
    # run fetched it. 15M is EXECUTION_TF -- what entries/exits key off of --
    # so it gets the widest overlap; others get a minimal 1-bar safety net.
    "1D": 1, "4H": 1, "1H": 1, "30M": 2, "15M": 3,
}

RESEARCH_PARAMS: Dict[str, Any] = {
    "min_consecutive_windows_for_weight_change": 2,
    "ablation_min_sample_size": 20,
}
PRODUCTION_PARAMS: Dict[str, Any] = {
    "confluence_threshold": 80,
    "swing_lookback": 3,
    "atr_period": 14,
    "rsi_period": 14,
    "adx_period": 14,
    "bb_period": 20, "bb_std": 2.0,
    "donchian_period": 20,
    "keltner_period": 20, "keltner_atr_mult": 2.0,
    "vol_sma_period": 20,
    "atr_percentile_lookback": 100,
    "equal_level_tolerance_pct": 0.05,
    "fvg_min_gap_atr_mult": 0.10,
    "max_concurrent_positions": 5,
    "max_daily_loss_pct": 3.0,
    "max_drawdown_circuit_breaker_pct": 10.0,
    "portfolio_exposure_cap_pct": 25.0,
    "correlation_filter_threshold": 0.80,
    "risk_per_trade_pct": 1.0,
    "kelly_mode_enabled": False,
    "kelly_fraction_cap": 0.5,
    "daily_summary_hour_utc": 8,
    "liquidity_sweep_lookback_bars": 12,
    "liquidity_sweep_confirm_bars": 6,
    "watch_tier_threshold": 70,
    # Minimum spacing between two watch-tier Telegram alerts for the *same*
    # symbol *and* direction. Prevents a setup that lingers in the 70-79
    # composite-score band for hours (common at 15M-execution cadence) from
    # re-alerting every single 15-min scan. A direction flip (WATCH LONG ->
    # WATCH SHORT or vice versa) always bypasses this and alerts immediately,
    # since that's a materially different setup, not a repeat of the same one.
    "watch_tier_cooldown_hours": 4,
    "mtf_veto_strength_floor": 40.0,
    "daily_stats_retention_days": 90,
}

# closed_signals is a flat, ever-growing list appended to from two separate
# exit paths in monitor_active_signals (resolved via TP1/SL/Closed, and
# expired-unfilled). Bounded centrally in _prune_state rather than trimmed
# ad hoc at each append site, so neither path can be missed.
CLOSED_SIGNALS_MAX = 2000

# --- Feature-validator hardening (v1.1.5) -------------------------------
# A feature is never adjusted/disabled on fewer than this many resolved
# trades inside the rolling window (n~19 gave near-identical, non-
# discriminative per-feature stats because features fire together).
MIN_FEATURE_SAMPLE = 30
# Validator/shadow statistics use only the most recent N resolved trades.
FEATURE_ROLLING_WINDOW = 50
# Max share of total (default-baseline) feature weight that may be disabled
# at once; excess candidates are ranked by expectancy and only the worst
# are disabled, the rest are held at the active-weight floor below.
MAX_DISABLED_WEIGHT_SHARE = 0.5
# Weight (x DEFAULT_FEATURE_WEIGHT) given to a feature restored from
# disabled, and the floor for decayed-but-not-disabled features.
RESTORE_WEIGHT_FACTOR = 0.2
# Weight below which a decayed feature is considered disabled.
DISABLE_WEIGHT_EPSILON = 0.01
# Per-day cap on stored feature-adjustment log lines in daily_stats (the
# running total is kept in `feature_adjustments_count`). This list was the
# source of the ~9.75 MB daily_stats bloat (one line per feature per scan).
DAILY_FEATURE_ADJ_MAX_LINES = 10
# Rolling window (resolved trades per grade) and shrinkage for calibration.
CALIBRATION_ROLLING_WINDOW = 50
CALIBRATION_MIN_SAMPLE = 20
# Prior strength (pseudo-trades) and prior win rate for win_probability.
# 0.40 == breakeven WR at the fixed 1.5R target: claim no edge until
# realized per-grade results demonstrate one.
CALIBRATION_PRIOR_STRENGTH = 20
CALIBRATION_PRIOR_WIN_RATE = 0.40
# Warn when realized WR differs from the mean advertised probability by more
# than this, once the bucket has CALIBRATION_DRIFT_MIN_SAMPLE trades.
CALIBRATION_DRIFT_TOLERANCE = 0.20
CALIBRATION_DRIFT_MIN_SAMPLE = 15

# --- Audit hardening (v1.1.6) --------------------------------------------
# Starvation detection: if no tier="signal" candidate has been produced for
# this long (and for at least STARVATION_MIN_SCANS scans, so a stalled cron
# is not mistaken for starvation), adaptive state (disabled/decayed feature
# weights) is relieved back to defaults. Purely time/scan driven, so it works
# when live signal flow is zero.
STARVATION_MIN_HOURS = 72
STARVATION_MIN_SCANS = 200
# Minimum spacing between two relief actions.
STARVATION_RELIEF_COOLDOWN_HOURS = 72
# Drawdown circuit breaker auto-recovery: after this many hours tripped, the
# drawdown baseline is re-set (peak := current equity curve point). Without
# it, a tripped breaker suppresses all signals, so no new trades can ever
# close to repair the drawdown -> permanent lockout.
BREAKER_COOLDOWN_HOURS = 48
# What a tripped breaker (drawdown breaker or daily-loss kill-switch) does to
# NEW signals. "suppress" (default, previous behaviour): no alert, nothing
# tracked. "watch_only": sent as an untracked watch-tier alert carrying a
# BREAKER note. "dispatch": sent and tracked like a normal signal, with the
# BREAKER note leading its reasons. The engine never places orders either way.
BREAKER_DISPATCH_MODE = os.environ.get("PRISM_BREAKER_DISPATCH", "suppress")
BREAKER_DISPATCH_MODES = ("suppress", "watch_only", "dispatch")
if BREAKER_DISPATCH_MODE not in BREAKER_DISPATCH_MODES:
    log.warning("Unknown PRISM_BREAKER_DISPATCH %r -- falling back to suppress.", BREAKER_DISPATCH_MODE)
    BREAKER_DISPATCH_MODE = "suppress"
# Active signals older than this (wall clock since generated_at) are force-
# resolved: candle history since generation is replayed for a missed TP1/SL,
# otherwise the trade is closed mark-to-market. Longer than the longest
# holding-time bucket (48h) plus slack for outages.
STALE_SIGNAL_MAX_AGE_HOURS = 72
# Minimum resolved trades before the win-rate/expectancy health warning fires.
SELF_MONITOR_MIN_SAMPLE = 20

# --- Entry / exit model flags -------------------------------------------
# Entry model. "market" (default): entry = generation-candle close, treated
# as filled immediately (the old Pending->Activated gate was a no-op: ~90% of
# signals "activated" within 1 bar). "retest_limit" (default OFF): limit
# order RETEST_ATR_FRACTION x ATR back from the close; stays Pending until
# touched and expires after RETEST_EXPIRY_BARS 15M bars unfilled.
ENTRY_MODEL = os.environ.get("PRISM_ENTRY_MODEL", "market")
ENTRY_MODELS = ("market", "retest_limit")
RETEST_ATR_FRACTION = 0.5
RETEST_EXPIRY_BARS = 16
# Exit model parameters for "partial_at_1R_then_trail" (see EXIT_MODEL).
PARTIAL_AT_1R_FRACTION = 0.5   # share of position closed at +1R
PARTIAL_TRAIL_R = 1.0          # trailing-stop distance (in R) behind best price

BASE_CATEGORY_WEIGHTS: Dict[str, float] = {
    "trend": 25.0, "structure": 20.0, "momentum": 15.0, "liquidity": 15.0,
    "volume": 10.0, "volatility": 10.0, "risk": 5.0,
}
assert abs(sum(BASE_CATEGORY_WEIGHTS.values()) - 100.0) < 1e-9

REGIMES = [
    "Strong Bull Trend", "Strong Bear Trend", "Weak Trend", "Sideways", "Range",
    "Expansion", "Compression", "High Volatility", "Low Volatility",
    "Breakout", "Pullback", "Mean Reversion",
]

REGIME_WEIGHT_MULTIPLIERS: Dict[str, Dict[str, float]] = {
    "Strong Bull Trend":  {"trend": 1.35, "momentum": 1.20, "structure": 1.0, "liquidity": 0.85, "volume": 1.0, "volatility": 0.85, "risk": 1.0},
    "Strong Bear Trend":  {"trend": 1.35, "momentum": 1.20, "structure": 1.0, "liquidity": 0.85, "volume": 1.0, "volatility": 0.85, "risk": 1.0},
    "Weak Trend":         {"trend": 1.10, "momentum": 1.05, "structure": 1.0, "liquidity": 1.0,  "volume": 1.0, "volatility": 1.0,  "risk": 1.0},
    "Sideways":           {"trend": 0.65, "momentum": 0.90, "structure": 1.05, "liquidity": 1.30, "volume": 1.05, "volatility": 1.0, "risk": 1.0},
    "Range":              {"trend": 0.60, "momentum": 0.85, "structure": 1.10, "liquidity": 1.35, "volume": 1.05, "volatility": 1.0, "risk": 1.0},
    "Expansion":          {"trend": 1.15, "momentum": 1.10, "structure": 1.05, "liquidity": 0.90, "volume": 1.05, "volatility": 0.95, "risk": 1.0},
    "Compression":        {"trend": 0.80, "momentum": 0.85, "structure": 1.15, "liquidity": 1.05, "volume": 0.95, "volatility": 1.35, "risk": 1.0},
    "High Volatility":    {"trend": 0.90, "momentum": 1.05, "structure": 0.95, "liquidity": 1.0,  "volume": 1.0, "volatility": 1.45, "risk": 1.15},
    "Low Volatility":     {"trend": 1.0,  "momentum": 0.95, "structure": 1.05, "liquidity": 1.0,  "volume": 1.0, "volatility": 1.10, "risk": 0.95},
    "Breakout":           {"trend": 1.20, "momentum": 1.15, "structure": 1.05, "liquidity": 1.10, "volume": 1.20, "volatility": 1.10, "risk": 1.0},
    "Pullback":           {"trend": 1.10, "momentum": 0.90, "structure": 1.15, "liquidity": 1.10, "volume": 0.95, "volatility": 0.95, "risk": 1.0},
    "Mean Reversion":     {"trend": 0.60, "momentum": 1.10, "structure": 1.05, "liquidity": 1.20, "volume": 1.0, "volatility": 1.0,  "risk": 1.0},
}

CANDIDATE_FEATURES: List[str] = [
    "bos", "choch", "order_block", "breaker_block", "mitigation_block",
    "fair_value_gap", "liquidity_sweep", "equal_highs_lows",
    "ema_stack", "sma_trend", "vwap",
    "rsi", "macd", "atr_stop_quality", "adx", "obv", "cmf",
    "bollinger_bands", "donchian_channels",
]
DEFAULT_FEATURE_WEIGHT = 1.0 / len(CANDIDATE_FEATURES)

def score_to_grade(score: float) -> str:
    if score >= 95: return "A+"
    if score >= 90: return "A"
    if score >= 85: return "B+"
    if score >= 80: return "B"
    return "No Trade"

# Exit model (new signals only; open records keep the model they were created
# with). Default "full_exit_at_tp1" = all-out at fixed TP1 (1.5R), which needs
# a 40% win rate to break even (realized so far: ~37%).
# "partial_at_1R_then_trail" (default OFF, enable via PRISM_EXIT_MODEL):
# close PARTIAL_AT_1R_FRACTION at +1R, move stop to breakeven, trail the rest
# PARTIAL_TRAIL_R behind the best price (final cap = TP3). Trade-off: +1R is
# reached more often than +1.5R and the breakeven stop caps the downside once
# the partial is banked, which lifts hit-rate and smooths the curve, but it
# gives up some of the full 1.5R payoff on winners that run straight to TP1
# and adds path dependence; only validate it on forward data, not on the n~20
# sample that motivated it.
EXIT_MODEL_FULL = "full_exit_at_tp1"
EXIT_MODEL_PARTIAL = "partial_at_1R_then_trail"
EXIT_MODELS = (EXIT_MODEL_FULL, EXIT_MODEL_PARTIAL)
EXIT_MODEL = os.environ.get("PRISM_EXIT_MODEL", EXIT_MODEL_FULL)
if EXIT_MODEL not in EXIT_MODELS:
    log.warning("Unknown PRISM_EXIT_MODEL %r -- falling back to %s.", EXIT_MODEL, EXIT_MODEL_FULL)
    EXIT_MODEL = EXIT_MODEL_FULL
if ENTRY_MODEL not in ENTRY_MODELS:
    log.warning("Unknown PRISM_ENTRY_MODEL %r -- falling back to market.", ENTRY_MODEL)
    ENTRY_MODEL = "market"

SIGNAL_STATUSES = ("Pending", "Activated", "TP1", "SL", "Expired", "Closed", "Cancelled")

REACTION_EMOJI = "\U0001F4AF"  # 💯 -- must be one of Telegram's fixed standard reaction emoji

def _utcnow() -> datetime:
    return datetime.now(timezone.utc)

def _atomic_write_json(path: str, payload: Any) -> bool:
    """Write JSON atomically: temp file in the same directory, then os.replace.
    Guarantees a crash mid-write never leaves a corrupt file for the next
    (fresh GitHub Actions runner's) invocation to load (Section 2)."""
    tmp_path = f"{path}.tmp-{os.getpid()}-{int(time.time() * 1000)}"
    try:
        with open(tmp_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, sort_keys=True)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp_path, path)
        return True
    except Exception:
        log.exception("Failed to atomically write %s", path)
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except OSError:
            pass
        return False

def _safe_load_json(path: str, default: Any) -> Any:
    if not os.path.exists(path):
        return default
    try:
        with open(path, "r", encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        log.warning("Failed to parse %s -- falling back to default.", path)
        return default

HL_DEFAULT_INFO_WEIGHT = 20
_CANDLE_INTERVAL_MS: Dict[str, int] = {
    "1d": 86_400_000, "4h": 14_400_000, "1h": 3_600_000, "30m": 1_800_000, "15m": 900_000,
}

def _candle_request_weight(interval: str, start_ms: int, end_ms: int) -> int:
    """Dynamic per-request weight for a candleSnapshot call (Section B.3,
    ported from Vantage Point's `_request_weight`): larger candle-count
    requests cost more weight, rather than Axis v4.0.0's flat weight=20
    for every candle request regardless of how many bars were asked for."""
    step = _CANDLE_INTERVAL_MS.get(interval)
    if not step or end_ms <= start_ms:
        return HL_DEFAULT_INFO_WEIGHT
    n_bars = max(1, math.ceil((end_ms - start_ms) / step))
    return HL_DEFAULT_INFO_WEIGHT * math.ceil(n_bars / 60)

class _WeightRateLimiter:
    """Sliding-window Hyperliquid weight pacer (Section B.3, ported from
    Vantage Point's `_WeightRateLimiter`, replacing Axis v4.0.0's
    fixed-60-second-window `WeightPacer`). A deque of (timestamp, weight)
    events is pruned to the trailing `window_s` seconds on every call, so
    weight usage is evaluated continuously -- Axis's old fixed-window pacer
    could allow a 2x weight burst across a window boundary (e.g. spending
    the full budget in the last instant of one window and again in the
    first instant of the next); a sliding window cannot be burst that way."""

    def __init__(self, max_weight_per_min: float) -> None:
        self.budget = max_weight_per_min
        self.window_s = 60.0
        self._lock = threading.Lock()
        self._events: "collections.deque[Tuple[float, float]]" = collections.deque()

    def acquire(self, weight: float) -> None:
        while True:
            with self._lock:
                now = time.monotonic()
                cutoff = now - self.window_s
                while self._events and self._events[0][0] < cutoff:
                    self._events.popleft()
                used = sum(w for _, w in self._events)
                if used + weight <= self.budget:
                    self._events.append((now, weight))
                    return
                sleep_for = max(0.05, self._events[0][0] + self.window_s - now)
            time.sleep(min(sleep_for, 2.0))

class HyperliquidClient:
    """Thin, read-only client around Hyperliquid's public /info endpoint.
    No private/authenticated endpoints are used anywhere in this file --
    this engine never places, amends, or cancels an order."""

    def __init__(self, base_url: str = HL_API_URL) -> None:
        self.base_url = base_url
        self.pacer = _WeightRateLimiter(HL_MAX_WEIGHT_PER_MIN)

    def _post(self, payload: Dict[str, Any], weight: int = 2) -> Optional[Any]:
        self.pacer.acquire(weight)
        body = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            self.base_url, data=body,
            headers={"Content-Type": "application/json"}, method="POST",
        )
        # Label used only for logging so retry/backoff waits are traceable to
        # a specific request instead of showing up as an unexplained gap in
        # the run log (previously every branch below slept in total silence).
        req_kind = payload.get("type", "?")
        req_args = payload.get("req")
        coin = req_args.get("coin") if isinstance(req_args, dict) else None
        req_label = f"{req_kind}/{coin}" if coin else req_kind

        last_err: Optional[Exception] = None
        for attempt in range(HL_MAX_RETRIES):
            try:
                with urllib.request.urlopen(req, timeout=HL_REQUEST_TIMEOUT_SEC) as resp:
                    raw = resp.read()
                    return json.loads(raw.decode("utf-8"))
            except urllib.error.HTTPError as e:
                last_err = e
                if e.code == 429:
                    retry_after = e.headers.get("Retry-After") if e.headers else None
                    try:
                        sleep_s = float(retry_after) if retry_after is not None else (
                            HL_BACKOFF_BASE_SEC * (2 ** attempt) + random.uniform(0, 0.3))
                    except (TypeError, ValueError):
                        sleep_s = HL_BACKOFF_BASE_SEC * (2 ** attempt) + random.uniform(0, 0.3)
                    log.warning(
                        "Rate-limited (429) on %s -- attempt %d/%d, sleeping %.1fs (%s).",
                        req_label, attempt + 1, HL_MAX_RETRIES, sleep_s,
                        "server Retry-After" if retry_after else "local backoff")
                    time.sleep(sleep_s)
                    continue
                if 500 <= e.code < 600:
                    sleep_s = HL_BACKOFF_BASE_SEC * (2 ** attempt) + random.uniform(0, 0.3)
                    log.warning(
                        "Server error (%d) on %s -- attempt %d/%d, sleeping %.1fs.",
                        e.code, req_label, attempt + 1, HL_MAX_RETRIES, sleep_s)
                    time.sleep(sleep_s)
                    continue
                break
            except (urllib.error.URLError, TimeoutError, OSError) as e:
                last_err = e
                sleep_s = HL_BACKOFF_BASE_SEC * (2 ** attempt) + random.uniform(0, 0.3)
                log.warning(
                    "Network error on %s (%s) -- attempt %d/%d, sleeping %.1fs.",
                    req_label, e, attempt + 1, HL_MAX_RETRIES, sleep_s)
                time.sleep(sleep_s)
                continue
        log.error("Hyperliquid request failed after retries: %s (payload type=%s)",
                   last_err, payload.get("type"))
        return None

    def all_mids(self) -> Dict[str, float]:
        data = self._post({"type": "allMids"}, weight=2)
        if not isinstance(data, dict):
            return {}
        out: Dict[str, float] = {}
        for k, v in data.items():
            try:
                out[k] = float(v)
            except (TypeError, ValueError):
                continue
        return out

    def candles(self, coin: str, interval: str, start_ms: int, end_ms: int) -> Optional[List[Dict[str, Any]]]:
        payload = {
            "type": "candleSnapshot",
            "req": {"coin": coin, "interval": interval, "startTime": start_ms, "endTime": end_ms},
        }
        data = self._post(payload, weight=_candle_request_weight(interval, start_ms, end_ms))
        if data is None:
            return None
        if not isinstance(data, list):
            return None
        out = []
        for c in data:
            try:
                out.append({
                    "t": int(c["t"]), "o": float(c["o"]), "h": float(c["h"]),
                    "l": float(c["l"]), "c": float(c["c"]), "v": float(c["v"]),
                })
            except (KeyError, TypeError, ValueError):
                continue
        out.sort(key=lambda r: r["t"])
        return out

class CandleCacheStore:
    """Persistent, bounded, shared candle cache keyed by asset+timeframe
    (Section 22). Every sub-engine reads from / the collector writes to this
    single structure so identical candle data is fetched and computed only
    once per run, and a fresh runner only fetches newly-closed candles since
    the last cached timestamp rather than the full lookback every time."""

    def __init__(self, path: str = CANDLE_CACHE_PATH) -> None:
        self.path = path
        self.data: Dict[str, Dict[str, List[Dict[str, Any]]]] = _safe_load_json(path, {})
        if not isinstance(self.data, dict):
            log.warning("candle_cache.json content was not a dict -- resetting.")
            self.data = {}
        # Multiple symbols can now be scanned concurrently (run_scan uses a
        # thread pool); each symbol touches a different top-level key, but an
        # explicit lock removes any doubt about interleaved get/put safety
        # rather than relying on CPython dict-op atomicity implicitly.
        self._lock = threading.Lock()

    def get(self, symbol: str, tf: str) -> List[Dict[str, Any]]:
        with self._lock:
            return list(self.data.get(symbol, {}).get(tf, []))

    def put(self, symbol: str, tf: str, candles: List[Dict[str, Any]]) -> None:
        with self._lock:
            self.data.setdefault(symbol, {})[tf] = candles[-CANDLE_LOOKBACK[tf]:]

    def save(self) -> None:
        if not _atomic_write_json(self.path, self.data):
            log.error("Could not persist %s -- next run will re-fetch more than necessary.", self.path)

def _interval_ms(tf: str) -> int:
    return {"1D": 86_400_000, "4H": 14_400_000, "1H": 3_600_000,
            "30M": 1_800_000, "15M": 900_000}[tf]

def _drop_unclosed_candles(candles: List[Dict[str, Any]], step_ms: int, now_ms: int) -> List[Dict[str, Any]]:
    """H6 fix: a candle is only "closed" once its full interval has elapsed
    (t + step_ms <= now_ms). The exchange API happily returns the
    still-forming current-interval row alongside historical ones; using it
    as-is means entry price, BOS/CHoCH evaluation, and every indicator
    reading can be computed against a live, mutating close -- exactly the
    repainting risk the engine's own close-based-rules design is meant to
    avoid. Trim any trailing candle(s) that haven't fully closed yet."""
    while candles and candles[-1]["t"] + step_ms > now_ms:
        candles = candles[:-1]
    return candles

def fetch_symbol_mtf(client: HyperliquidClient, cache: CandleCacheStore, symbol: str,
                      now_ms: int) -> Optional[Dict[str, List[Dict[str, Any]]]]:
    """Fetch/refresh every timeframe in TIMEFRAMES for one symbol, merging with
    the persistent cache (only newly-closed candles are requested), pruning to
    the bounded lookback, and falling back to a full re-fetch for a single
    timeframe if its cache entry is missing/corrupt/stale (Section 22)."""
    out: Dict[str, List[Dict[str, Any]]] = {}
    for tf in TIMEFRAMES:
        interval = HL_INTERVAL_MAP[tf]
        step_ms = _interval_ms(tf)
        lookback = CANDLE_LOOKBACK[tf]
        cached = cache.get(symbol, tf)

        stale = False
        if cached:
            last_t = cached[-1]["t"]
            age_sec = (now_ms - last_t) / 1000.0
            if age_sec > CANDLE_STALE_AFTER_SEC[tf] * 3:
                stale = True
                log.warning("Cache for %s/%s stale beyond threshold -- full re-fetch.", symbol, tf)

        if not cached or stale:
            start_ms = now_ms - step_ms * lookback
            fresh = client.candles(symbol, interval, start_ms, now_ms)
            if fresh is None:
                log.error("Fetch failed for %s/%s -- skipping this timeframe.", symbol, tf)
                if cached:
                    out[tf] = cached
                continue
            fresh = _drop_unclosed_candles(fresh, step_ms, now_ms)
            cache.put(symbol, tf, fresh)
            out[tf] = cache.get(symbol, tf)
            continue

        last_cached_t = cached[-1]["t"]
        current_bar_open_ms = (now_ms // step_ms) * step_ms
        if current_bar_open_ms <= last_cached_t + step_ms:
            out[tf] = cached
            continue
        overlap_bars = CANDLE_REFETCH_OVERLAP_BARS.get(tf, 1)
        start_ms = max(cached[0]["t"], last_cached_t - overlap_bars * step_ms)
        fresh = client.candles(symbol, interval, start_ms, now_ms)
        if fresh is None:
            log.error("Incremental fetch failed for %s/%s -- using stale cache.", symbol, tf)
            out[tf] = cached
            continue
        fresh = _drop_unclosed_candles(fresh, step_ms, now_ms)
        fresh_ts = {c["t"] for c in fresh}
        merged = [c for c in cached if c["t"] not in fresh_ts] + fresh
        merged.sort(key=lambda r: r["t"])
        cache.put(symbol, tf, merged)
        out[tf] = cache.get(symbol, tf)

    if not out.get(EXECUTION_TF):
        log.error("No %s data available for %s -- cannot evaluate this run.", EXECUTION_TF, symbol)
        return None
    return out

def _closes(c): return [x["c"] for x in c]
def _highs(c):  return [x["h"] for x in c]
def _lows(c):   return [x["l"] for x in c]
def _opens(c):  return [x["o"] for x in c]
def _vols(c):   return [x["v"] for x in c]

def sma(series: Sequence[float], period: int) -> List[Optional[float]]:
    out: List[Optional[float]] = [None] * len(series)
    if period <= 0 or len(series) < period:
        return out
    running = sum(series[:period])
    out[period - 1] = running / period
    for i in range(period, len(series)):
        running += series[i] - series[i - period]
        out[i] = running / period
    return out

def ema(series: Sequence[float], period: int) -> List[Optional[float]]:
    out: List[Optional[float]] = [None] * len(series)
    if period <= 0 or len(series) < period:
        return out
    k = 2.0 / (period + 1)
    seed = sum(series[:period]) / period
    out[period - 1] = seed
    prev = seed
    for i in range(period, len(series)):
        prev = series[i] * k + prev * (1 - k)
        out[i] = prev
    return out

def rsi(closes: Sequence[float], period: int = 14) -> List[Optional[float]]:
    n = len(closes)
    out: List[Optional[float]] = [None] * n
    if n <= period:
        return out
    gains = [0.0] * n
    losses = [0.0] * n
    for i in range(1, n):
        delta = closes[i] - closes[i - 1]
        gains[i] = max(delta, 0.0)
        losses[i] = max(-delta, 0.0)
    avg_gain = sum(gains[1:period + 1]) / period
    avg_loss = sum(losses[1:period + 1]) / period
    def _rsi_val(ag, al):
        if al == 0 and ag == 0:
            return 50.0
        if al == 0:
            return 100.0
        rs = ag / al
        return 100.0 - (100.0 / (1.0 + rs))
    out[period] = _rsi_val(avg_gain, avg_loss)
    for i in range(period + 1, n):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
        out[i] = _rsi_val(avg_gain, avg_loss)
    return out

def macd(closes: Sequence[float], fast: int = 12, slow: int = 26, signal: int = 9):
    ema_fast = ema(closes, fast)
    ema_slow = ema(closes, slow)
    line: List[Optional[float]] = [
        (a - b) if (a is not None and b is not None) else None
        for a, b in zip(ema_fast, ema_slow)
    ]
    dense = [x for x in line if x is not None]
    sig_dense = ema(dense, signal) if len(dense) >= signal else []
    signal_line: List[Optional[float]] = [None] * len(line)
    if sig_dense:
        offset = len(line) - len(dense)
        for i, v in enumerate(sig_dense):
            signal_line[offset + i] = v
    hist: List[Optional[float]] = [
        (a - b) if (a is not None and b is not None) else None
        for a, b in zip(line, signal_line)
    ]
    return line, signal_line, hist

def true_range(highs, lows, closes) -> List[Optional[float]]:
    n = len(closes)
    out: List[Optional[float]] = [None] * n
    if n == 0:
        return out
    out[0] = highs[0] - lows[0]
    for i in range(1, n):
        out[i] = max(
            highs[i] - lows[i],
            abs(highs[i] - closes[i - 1]),
            abs(lows[i] - closes[i - 1]),
        )
    return out

def atr(highs, lows, closes, period: int = 14) -> List[Optional[float]]:
    tr = true_range(highs, lows, closes)
    n = len(tr)
    out: List[Optional[float]] = [None] * n
    valid = [x for x in tr if x is not None]
    if len(valid) < period:
        return out
    first_idx = period
    seed = sum(tr[:period]) / period
    out[first_idx - 1] = seed
    prev = seed
    for i in range(first_idx, n):
        prev = (prev * (period - 1) + tr[i]) / period
        out[i] = prev
    return out

def adx(highs, lows, closes, period: int = 14) -> List[Optional[float]]:
    n = len(closes)
    out: List[Optional[float]] = [None] * n
    if n < period * 2:
        return out
    plus_dm = [0.0] * n
    minus_dm = [0.0] * n
    tr = true_range(highs, lows, closes)
    for i in range(1, n):
        up_move = highs[i] - highs[i - 1]
        down_move = lows[i - 1] - lows[i]
        plus_dm[i] = up_move if (up_move > down_move and up_move > 0) else 0.0
        minus_dm[i] = down_move if (down_move > up_move and down_move > 0) else 0.0
    tr_s = sum(x or 0.0 for x in tr[1:period + 1])
    pdm_s = sum(plus_dm[1:period + 1])
    mdm_s = sum(minus_dm[1:period + 1])
    dx_series: List[Optional[float]] = [None] * n
    idx = period
    def _dx(tr_s, pdm_s, mdm_s):
        if tr_s == 0:
            return 0.0
        pdi = 100 * (pdm_s / tr_s)
        mdi = 100 * (mdm_s / tr_s)
        denom = pdi + mdi
        return 0.0 if denom == 0 else 100 * abs(pdi - mdi) / denom
    dx_series[idx] = _dx(tr_s, pdm_s, mdm_s)
    for i in range(period + 1, n):
        tr_s = tr_s - tr_s / period + (tr[i] or 0.0)
        pdm_s = pdm_s - pdm_s / period + plus_dm[i]
        mdm_s = mdm_s - mdm_s / period + minus_dm[i]
        dx_series[i] = _dx(tr_s, pdm_s, mdm_s)
    dx_valid_start = period
    dx_vals = [v for v in dx_series[dx_valid_start:] if v is not None]
    if len(dx_vals) < period:
        return out
    adx_seed = sum(dx_vals[:period]) / period
    out[dx_valid_start + period - 1] = adx_seed
    prev = adx_seed
    for i in range(dx_valid_start + period, n):
        v = dx_series[i]
        if v is None:
            continue
        prev = (prev * (period - 1) + v) / period
        out[i] = prev
    return out

def obv(closes, vols) -> List[float]:
    out = [0.0] * len(closes)
    for i in range(1, len(closes)):
        if closes[i] > closes[i - 1]:
            out[i] = out[i - 1] + vols[i]
        elif closes[i] < closes[i - 1]:
            out[i] = out[i - 1] - vols[i]
        else:
            out[i] = out[i - 1]
    return out

def cmf(highs, lows, closes, vols, period: int = 20) -> List[Optional[float]]:
    n = len(closes)
    mfv = [0.0] * n
    for i in range(n):
        hl = highs[i] - lows[i]
        if hl == 0:
            mfv[i] = 0.0
        else:
            mfm = ((closes[i] - lows[i]) - (highs[i] - closes[i])) / hl
            mfv[i] = mfm * vols[i]
    out: List[Optional[float]] = [None] * n
    for i in range(period - 1, n):
        vol_sum = sum(vols[i - period + 1:i + 1])
        out[i] = (sum(mfv[i - period + 1:i + 1]) / vol_sum) if vol_sum else 0.0
    return out

def bollinger_bands(closes, period: int = 20, num_std: float = 2.0):
    mid = sma(closes, period)
    upper: List[Optional[float]] = [None] * len(closes)
    lower: List[Optional[float]] = [None] * len(closes)
    for i in range(period - 1, len(closes)):
        window = closes[i - period + 1:i + 1]
        m = mid[i]
        if m is None:
            continue
        sd = statistics.pstdev(window)
        upper[i] = m + num_std * sd
        lower[i] = m - num_std * sd
    return upper, mid, lower

def keltner_channel(highs, lows, closes, period: int = 20, atr_mult: float = 2.0):
    mid = ema(closes, period)
    atr_vals = atr(highs, lows, closes, period)
    upper = [(m + atr_mult * a) if (m is not None and a is not None) else None
              for m, a in zip(mid, atr_vals)]
    lower = [(m - atr_mult * a) if (m is not None and a is not None) else None
              for m, a in zip(mid, atr_vals)]
    return upper, mid, lower

def donchian_channel(highs, lows, period: int = 20):
    n = len(highs)
    upper: List[Optional[float]] = [None] * n
    lower: List[Optional[float]] = [None] * n
    for i in range(period - 1, n):
        upper[i] = max(highs[i - period + 1:i + 1])
        lower[i] = min(lows[i - period + 1:i + 1])
    mid = [((u + l) / 2) if (u is not None and l is not None) else None
           for u, l in zip(upper, lower)]
    return upper, mid, lower

def vwap_session(highs, lows, closes, vols) -> List[Optional[float]]:
    """Simple cumulative VWAP over the supplied candle window (used as a
    rolling/anchored-from-window-start VWAP; the anchored VWAP variant below
    anchors explicitly from a chosen index, e.g. most recent swing)."""
    n = len(closes)
    out: List[Optional[float]] = [None] * n
    cum_pv = 0.0
    cum_v = 0.0
    for i in range(n):
        typical = (highs[i] + lows[i] + closes[i]) / 3.0
        cum_pv += typical * vols[i]
        cum_v += vols[i]
        out[i] = (cum_pv / cum_v) if cum_v else None
    return out

def anchored_vwap(highs, lows, closes, vols, anchor_idx: int) -> List[Optional[float]]:
    n = len(closes)
    out: List[Optional[float]] = [None] * n
    if anchor_idx < 0 or anchor_idx >= n:
        return out
    cum_pv = 0.0
    cum_v = 0.0
    for i in range(anchor_idx, n):
        typical = (highs[i] + lows[i] + closes[i]) / 3.0
        cum_pv += typical * vols[i]
        cum_v += vols[i]
        out[i] = (cum_pv / cum_v) if cum_v else None
    return out

def linreg_slope(series: Sequence[float], period: int) -> Optional[float]:
    if len(series) < period:
        return None
    window = series[-period:]
    xs = list(range(period))
    x_mean = sum(xs) / period
    y_mean = sum(window) / period
    num = sum((x - x_mean) * (y - y_mean) for x, y in zip(xs, window))
    den = sum((x - x_mean) ** 2 for x in xs)
    if den == 0:
        return 0.0
    slope = num / den
    return slope / y_mean if y_mean else slope

def stoch_rsi(closes, rsi_period: int = 14, stoch_period: int = 14) -> List[Optional[float]]:
    r = rsi(closes, rsi_period)
    n = len(r)
    out: List[Optional[float]] = [None] * n
    for i in range(n):
        if r[i] is None:
            continue
        window = [v for v in r[max(0, i - stoch_period + 1):i + 1] if v is not None]
        if len(window) < stoch_period:
            continue
        lo, hi = min(window), max(window)
        out[i] = 0.0 if hi == lo else (r[i] - lo) / (hi - lo) * 100.0
    return out

def roc(closes, period: int = 10) -> List[Optional[float]]:
    n = len(closes)
    out: List[Optional[float]] = [None] * n
    for i in range(period, n):
        prev = closes[i - period]
        out[i] = ((closes[i] - prev) / prev * 100.0) if prev else None
    return out

def cci(highs, lows, closes, period: int = 20) -> List[Optional[float]]:
    n = len(closes)
    tp = [(highs[i] + lows[i] + closes[i]) / 3.0 for i in range(n)]
    out: List[Optional[float]] = [None] * n
    for i in range(period - 1, n):
        window = tp[i - period + 1:i + 1]
        m = sum(window) / period
        mad = sum(abs(x - m) for x in window) / period
        out[i] = 0.0 if mad == 0 else (tp[i] - m) / (0.015 * mad)
    return out

def swing_points(highs, lows, lookback: int = 3) -> Tuple[List[bool], List[bool]]:
    """Objective swing-pivot rule (Section 9): bar i is a swing high iff its
    high is strictly greater than the high of every bar within `lookback` on
    both sides; symmetric definition for swing lows. Deterministic, no
    subjective interpretation."""
    n = len(highs)
    sh = [False] * n
    sl = [False] * n
    for i in range(lookback, n - lookback):
        window_h = highs[i - lookback:i + lookback + 1]
        window_l = lows[i - lookback:i + lookback + 1]
        if highs[i] == max(window_h) and window_h.count(highs[i]) == 1:
            sh[i] = True
        if lows[i] == min(window_l) and window_l.count(lows[i]) == 1:
            sl[i] = True
    return sh, sl

def atr_percentile(atr_series: List[Optional[float]], lookback: int = 100) -> Optional[float]:
    valid = [v for v in atr_series if v is not None]
    if len(valid) < 10:
        return None
    window = valid[-lookback:]
    current = valid[-1]
    rank = sum(1 for v in window if v <= current)
    return 100.0 * rank / len(window)

@dataclass
class FeatureSet:
    """Every precomputed series for one symbol+timeframe candle window.
    Built exactly once per symbol/timeframe/run (Section 22) and passed by
    reference into every sub-engine that needs it."""
    candles: List[Dict[str, Any]]
    closes: List[float]
    highs: List[float]
    lows: List[float]
    opens: List[float]
    vols: List[float]
    ema20: List[Optional[float]]
    ema50: List[Optional[float]]
    ema200: List[Optional[float]]
    sma50: List[Optional[float]]
    sma200: List[Optional[float]]
    rsi14: List[Optional[float]]
    macd_line: List[Optional[float]]
    macd_signal: List[Optional[float]]
    macd_hist: List[Optional[float]]
    atr14: List[Optional[float]]
    adx14: List[Optional[float]]
    obv: List[float]
    cmf20: List[Optional[float]]
    bb_upper: List[Optional[float]]
    bb_mid: List[Optional[float]]
    bb_lower: List[Optional[float]]
    kc_upper: List[Optional[float]]
    kc_mid: List[Optional[float]]
    kc_lower: List[Optional[float]]
    donchian_upper: List[Optional[float]]
    donchian_mid: List[Optional[float]]
    donchian_lower: List[Optional[float]]
    vwap: List[Optional[float]]
    stoch_rsi: List[Optional[float]]
    roc10: List[Optional[float]]
    cci20: List[Optional[float]]
    swing_high: List[bool]
    swing_low: List[bool]
    vol_sma20: List[Optional[float]]

    @property
    def last(self) -> int:
        return len(self.closes) - 1

def build_feature_set(candles: List[Dict[str, Any]], p: Dict[str, Any] = PRODUCTION_PARAMS) -> Optional[FeatureSet]:
    if len(candles) < 25:
        return None
    c, h, l, o, v = _closes(candles), _highs(candles), _lows(candles), _opens(candles), _vols(candles)
    macd_line, macd_signal, macd_hist = macd(c)
    bb_u, bb_m, bb_l = bollinger_bands(c, p["bb_period"], p["bb_std"])
    kc_u, kc_m, kc_l = keltner_channel(h, l, c, p["keltner_period"], p["keltner_atr_mult"])
    dc_u, dc_m, dc_l = donchian_channel(h, l, p["donchian_period"])
    sh, sl = swing_points(h, l, p["swing_lookback"])
    return FeatureSet(
        candles=candles, closes=c, highs=h, lows=l, opens=o, vols=v,
        ema20=ema(c, 20), ema50=ema(c, 50), ema200=ema(c, 200),
        sma50=sma(c, 50), sma200=sma(c, 200),
        rsi14=rsi(c, p["rsi_period"]),
        macd_line=macd_line, macd_signal=macd_signal, macd_hist=macd_hist,
        atr14=atr(h, l, c, p["atr_period"]),
        adx14=adx(h, l, c, p["adx_period"]),
        obv=obv(c, v), cmf20=cmf(h, l, c, v, 20),
        bb_upper=bb_u, bb_mid=bb_m, bb_lower=bb_l,
        kc_upper=kc_u, kc_mid=kc_m, kc_lower=kc_l,
        donchian_upper=dc_u, donchian_mid=dc_m, donchian_lower=dc_l,
        vwap=vwap_session(h, l, c, v),
        stoch_rsi=stoch_rsi(c), roc10=roc(c, 10), cci20=cci(h, l, c, 20),
        swing_high=sh, swing_low=sl,
        vol_sma20=sma(v, p["vol_sma_period"]),
    )

@dataclass
class RegimeResult:
    market_regime: str
    regime_confidence: float
    expected_behavior: str
    votes: Dict[str, float]

def classify_regime(fs: FeatureSet) -> Optional[RegimeResult]:
    """Classify the current regime from MULTIPLE independent quantitative
    features (Section 7) -- never a single indicator. Each candidate regime
    accumulates a vote score from independent evidence; the winner is the
    classification, and regime_confidence is its share of total votes."""
    i = fs.last
    adx_v = fs.adx14[i]
    atr_v = fs.atr14[i]
    close = fs.closes[i]
    if adx_v is None or atr_v is None or close == 0:
        return None

    atr_pct_hist = atr_percentile(fs.atr14, PRODUCTION_PARAMS["atr_percentile_lookback"])
    bb_u, bb_l, bb_m = fs.bb_upper[i], fs.bb_lower[i], fs.bb_mid[i]
    bb_width = ((bb_u - bb_l) / bb_m * 100.0) if (bb_u and bb_l and bb_m) else None
    bb_width_hist = [
        ((u - l) / m * 100.0) for u, l, m in zip(fs.bb_upper, fs.bb_lower, fs.bb_mid)
        if u is not None and l is not None and m
    ]
    bb_width_pctl = None
    if bb_width is not None and len(bb_width_hist) >= 20:
        window = bb_width_hist[-100:]
        bb_width_pctl = 100.0 * sum(1 for x in window if x <= bb_width) / len(window)

    slope20 = linreg_slope(fs.closes, 20)
    ema20_v, ema50_v, ema200_v = fs.ema20[i], fs.ema50[i], fs.ema200[i]
    dc_u, dc_l = fs.donchian_upper[i], fs.donchian_lower[i]

    votes: Dict[str, float] = {r: 0.0 for r in REGIMES}

    if adx_v >= 30:
        if slope20 and slope20 > 0 and ema20_v and ema50_v and ema20_v > ema50_v:
            votes["Strong Bull Trend"] += 3
        elif slope20 and slope20 < 0 and ema20_v and ema50_v and ema20_v < ema50_v:
            votes["Strong Bear Trend"] += 3
        else:
            votes["Weak Trend"] += 1
    elif 18 <= adx_v < 30:
        votes["Weak Trend"] += 2
    else:
        votes["Sideways"] += 2
        votes["Range"] += 1

    if dc_u is not None and dc_l is not None and atr_v:
        dc_width_in_atr = (dc_u - dc_l) / atr_v
        if dc_width_in_atr < 4.0:
            votes["Range"] += 2
            votes["Compression"] += 1
        elif dc_width_in_atr > 9.0:
            votes["Expansion"] += 2

    if atr_pct_hist is not None:
        if atr_pct_hist >= 80:
            votes["High Volatility"] += 3
        elif atr_pct_hist <= 20:
            votes["Low Volatility"] += 3

    if bb_width_pctl is not None:
        if bb_width_pctl <= 20:
            votes["Compression"] += 2
        elif bb_width_pctl >= 80:
            votes["Expansion"] += 2

    if i > 0 and dc_u is not None and dc_l is not None:
        prev_u, prev_l = fs.donchian_upper[i - 1], fs.donchian_lower[i - 1]
        if prev_u is not None and close > prev_u:
            votes["Breakout"] += 3
        elif prev_l is not None and close < prev_l:
            votes["Breakout"] += 3

    if ema20_v and ema50_v and ema200_v:
        if ema50_v > ema200_v and close < ema20_v and slope20 and slope20 > 0:
            votes["Pullback"] += 2
        elif ema50_v < ema200_v and close > ema20_v and slope20 and slope20 < 0:
            votes["Pullback"] += 2

    if bb_u is not None and bb_l is not None and adx_v < 20:
        if close > bb_u or close < bb_l:
            votes["Mean Reversion"] += 2

    total = sum(votes.values())
    if total <= 0:
        return RegimeResult("Sideways", 25.0, "No strong evidence either way; treat as low-edge chop.", votes)

    winner = max(votes, key=votes.get)
    confidence = round(100.0 * votes[winner] / total, 1)

    expected_map = {
        "Strong Bull Trend": "Favor trend-following longs; discount mean-reversion shorts.",
        "Strong Bear Trend": "Favor trend-following shorts; discount mean-reversion longs.",
        "Weak Trend": "Directional bias present but unreliable; require extra confluence.",
        "Sideways": "Favor liquidity/structure plays at range extremes over breakouts.",
        "Range": "Fade range extremes; discount breakout entries without a confirmed sweep.",
        "Expansion": "Range/volatility opening up; breakout continuation favored.",
        "Compression": "Volatility coiling; favor breakout-probability setups, tight risk.",
        "High Volatility": "Widen stops via ATR; discount low-conviction momentum entries.",
        "Low Volatility": "Compression-breakout setups favored; expect slow drift otherwise.",
        "Breakout": "Momentum continuation favored; watch for immediate liquidity sweep back.",
        "Pullback": "Favor continuation entries at the pullback's structural level.",
        "Mean Reversion": "Favor fade-the-extreme setups; discount fresh trend entries.",
    }
    return RegimeResult(winner, confidence, expected_map[winner], votes)

@dataclass
class TrendResult:
    trend_direction: str
    trend_strength: float
    trend_quality: float
    reasons: List[str]
    sma_trend_aligned: bool = False
    price_above_vwap: Optional[bool] = None
    adx_strong: bool = False

def evaluate_trend(fs: FeatureSet) -> Optional[TrendResult]:
    i = fs.last
    ema20_v, ema50_v, ema200_v = fs.ema20[i], fs.ema50[i], fs.ema200[i]
    sma50_v, sma200_v = fs.sma50[i], fs.sma200[i]
    adx_v = fs.adx14[i]
    vwap_v = fs.vwap[i]
    close = fs.closes[i]
    slope50 = linreg_slope(fs.closes, 50)
    if ema200_v is None or adx_v is None:
        return None

    reasons: List[str] = []
    bull_votes = 0
    bear_votes = 0

    if ema20_v and ema50_v and ema200_v:
        if ema20_v > ema50_v > ema200_v:
            bull_votes += 2; reasons.append("EMA stack bullish (20>50>200)")
        elif ema20_v < ema50_v < ema200_v:
            bear_votes += 2; reasons.append("EMA stack bearish (20<50<200)")
    if sma50_v and sma200_v:
        if sma50_v > sma200_v:
            bull_votes += 1; reasons.append("SMA50 above SMA200")
        elif sma50_v < sma200_v:
            bear_votes += 1; reasons.append("SMA50 below SMA200")
    if vwap_v:
        if close > vwap_v:
            bull_votes += 1; reasons.append("Price above session VWAP")
        else:
            bear_votes += 1; reasons.append("Price below session VWAP")
    if slope50 is not None:
        if slope50 > 0:
            bull_votes += 1; reasons.append("50-bar linear regression slope positive")
        elif slope50 < 0:
            bear_votes += 1; reasons.append("50-bar linear regression slope negative")

    sh_idx = [j for j in range(i + 1) if fs.swing_high[j]]
    sl_idx = [j for j in range(i + 1) if fs.swing_low[j]]
    if len(sh_idx) >= 2 and len(sl_idx) >= 2:
        if fs.highs[sh_idx[-1]] > fs.highs[sh_idx[-2]] and fs.lows[sl_idx[-1]] > fs.lows[sl_idx[-2]]:
            bull_votes += 2; reasons.append("Structure printing higher-highs/higher-lows")
        elif fs.highs[sh_idx[-1]] < fs.highs[sh_idx[-2]] and fs.lows[sl_idx[-1]] < fs.lows[sl_idx[-2]]:
            bear_votes += 2; reasons.append("Structure printing lower-highs/lower-lows")

    if bull_votes == bear_votes:
        direction = "neutral"
    elif bull_votes > bear_votes:
        direction = "bullish"
    else:
        direction = "bearish"

    total_votes = bull_votes + bear_votes
    strength = round(100.0 * max(bull_votes, bear_votes) / total_votes, 1) if total_votes else 0.0
    strength = round(strength * min(1.0, adx_v / 40.0), 1)

    atr_v = fs.atr14[i]
    quality = 50.0
    if atr_v and len(sh_idx) >= 1 and len(sl_idx) >= 1:
        recent_range = max(fs.highs[-20:]) - min(fs.lows[-20:])
        if recent_range > 0:
            choppiness = 1.0 - min(1.0, (atr_v * 20) / recent_range)
            quality = round(max(0.0, min(100.0, 100.0 * (1.0 - choppiness))), 1)
    adx_recent = [v for v in fs.adx14[-10:] if v is not None]
    if len(adx_recent) >= 5:
        consistency = 100.0 - min(100.0, statistics.pstdev(adx_recent) * 3)
        quality = round((quality + consistency) / 2.0, 1)

    return TrendResult(
        direction, strength, quality, reasons,
        sma_trend_aligned=bool(sma50_v and sma200_v and (
            (sma50_v > sma200_v and direction == "bullish") or (sma50_v < sma200_v and direction == "bearish"))),
        price_above_vwap=(close > vwap_v) if vwap_v else None,
        adx_strong=bool(adx_v is not None and adx_v >= 25),
    )

@dataclass
class StructureResult:
    bos: Optional[str]
    choch: Optional[str]
    internal_trend: str
    external_trend: str
    protected_high: Optional[float]
    protected_low: Optional[float]
    continuation_or_reversal: str
    reasons: List[str]

def evaluate_structure(fs: FeatureSet) -> Optional[StructureResult]:
    """BOS = price CLOSES beyond the most recent confirmed swing high/low in
    the direction of the prevailing structure (continuation). CHoCH = price
    CLOSES beyond the most recent confirmed swing point AGAINST the
    prevailing structure (the first break that flips it). Both are exact,
    reproducible close-based rules -- never wick-based, never subjective."""
    i = fs.last
    sh_idx = [j for j in range(i + 1) if fs.swing_high[j]]
    sl_idx = [j for j in range(i + 1) if fs.swing_low[j]]
    if len(sh_idx) < 2 or len(sl_idx) < 2:
        return None

    reasons: List[str] = []
    last_sh, prev_sh = fs.highs[sh_idx[-1]], fs.highs[sh_idx[-2]]
    last_sl, prev_sl = fs.lows[sl_idx[-1]], fs.lows[sl_idx[-2]]

    internal_trend = "bullish" if last_sh > prev_sh and last_sl > prev_sl else (
        "bearish" if last_sh < prev_sh and last_sl < prev_sl else "neutral")

    ext_sh = sh_idx[-4:] if len(sh_idx) >= 4 else sh_idx
    ext_sl = sl_idx[-4:] if len(sl_idx) >= 4 else sl_idx
    if len(ext_sh) >= 2 and len(ext_sl) >= 2:
        external_trend = "bullish" if fs.highs[ext_sh[-1]] > fs.highs[ext_sh[0]] and fs.lows[ext_sl[-1]] > fs.lows[ext_sl[0]] else (
            "bearish" if fs.highs[ext_sh[-1]] < fs.highs[ext_sh[0]] and fs.lows[ext_sl[-1]] < fs.lows[ext_sl[0]] else "neutral")
    else:
        external_trend = "neutral"

    close = fs.closes[i]
    bos = None
    choch = None

    prevailing = internal_trend
    if prevailing == "bullish" and close > last_sh:
        bos = "bullish"; reasons.append(f"Close {close:.6g} broke above prior swing high {last_sh:.6g} (BOS, continuation)")
    elif prevailing == "bearish" and close < last_sl:
        bos = "bearish"; reasons.append(f"Close {close:.6g} broke below prior swing low {last_sl:.6g} (BOS, continuation)")
    elif prevailing == "bullish" and close < last_sl:
        choch = "bearish"; reasons.append(f"Close {close:.6g} broke below swing low {last_sl:.6g} against bullish structure (CHoCH)")
    elif prevailing == "bearish" and close > last_sh:
        choch = "bullish"; reasons.append(f"Close {close:.6g} broke above swing high {last_sh:.6g} against bearish structure (CHoCH)")

    protected_high = last_sh if internal_trend != "bullish" else None
    protected_low = last_sl if internal_trend != "bearish" else None

    if choch:
        continuation_or_reversal = "reversal"
    elif bos:
        continuation_or_reversal = "continuation"
    else:
        continuation_or_reversal = "undetermined"

    return StructureResult(bos, choch, internal_trend, external_trend,
                            protected_high, protected_low, continuation_or_reversal, reasons)

@dataclass
class OrderBlock:
    kind: str
    idx: int
    top: float
    bottom: float
    breaker: bool = False
    mitigated: bool = False
    trigger: str = "bos_break"

@dataclass
class FairValueGap:
    kind: str
    idx: int
    top: float
    bottom: float
    inverse: bool = False

@dataclass
class LiquidityPool:
    kind: str
    level: float
    idx_list: List[int]
    swept: bool = False

@dataclass
class SMCResult:
    order_blocks: List[OrderBlock]
    fvgs: List[FairValueGap]
    liquidity_pools: List[LiquidityPool]
    sweeps: List[str]
    zone: str
    displacement: bool
    reasons: List[str]

def _median_body_displacement_indices(fs: FeatureSet, start: int, n: int) -> List[int]:
    """Vantage Point's displacement-trigger test (Section B.2, ported): a
    candle is a displacement leg if its body is >=1.5x the median body of
    the preceding 10 candles -- self-normalizing and volatility-adaptive,
    independent of Axis's own BOS-break trigger below."""
    out: List[int] = []
    for i in range(start, n):
        body = abs(fs.closes[i] - fs.opens[i])
        prev_bodies = [abs(fs.closes[j] - fs.opens[j]) for j in range(max(0, i - 10), i)]
        median_body = statistics.median(prev_bodies) if prev_bodies else 0.0
        if median_body > 0 and body >= 1.5 * median_body:
            out.append(i)
    return out

def _find_order_blocks(fs: FeatureSet, max_lookback: int = 120) -> List[OrderBlock]:
    """Order Block = the last opposite-colored candle before a displacement
    move. Axis's original (and still primary) trigger: for each bar i that
    closes beyond the most recent swing high/low (a Break of Structure),
    scan backward for the last opposite-colored candle immediately
    preceding the displacement leg -- that candle's high/low is the order
    block. Section B.2 (ported from Vantage Point): an EITHER/OR alternate
    trigger is also evaluated -- a candle whose body is >=1.5x the median
    body of the preceding 10 candles counts as a displacement leg even
    without a BOS break. Either trigger firing on a given displacement
    candle is sufficient to flag the preceding opposite candle as a valid
    order block; `OrderBlock.trigger` records which trigger(s) fired, for
    auditability. Axis's full historical lookback scan is preserved
    (unshrunk) for both triggers.
    Breaker Block = an order block whose range is later fully closed through
    (invalidated) in the opposite direction -- it flips role.
    Mitigation Block = an order block that price has returned into (any
    overlap) without a full close-through -- marks it "mitigated" for
    weighting purposes, but does not remove it (still valid until broken)."""
    n = len(fs.closes)
    start = max(1, n - max_lookback)
    sh_idx = [j for j in range(n) if fs.swing_high[j]]
    sl_idx = [j for j in range(n) if fs.swing_low[j]]

    def _last_opposite_before(i: int, bullish: bool) -> Optional[int]:
        for k in range(i - 1, max(0, i - 8), -1):
            if bullish and fs.closes[k] < fs.opens[k]:
                return k
            if not bullish and fs.closes[k] > fs.opens[k]:
                return k
        return None

    trigger_by_key: Dict[Tuple[int, str], set] = {}

    for i in range(start, n):
        prior_sh = [j for j in sh_idx if j < i]
        if prior_sh and fs.closes[i] > fs.highs[prior_sh[-1]]:
            k = _last_opposite_before(i, True)
            if k is not None:
                trigger_by_key.setdefault((k, "bullish"), set()).add("bos_break")
        prior_sl = [j for j in sl_idx if j < i]
        if prior_sl and fs.closes[i] < fs.lows[prior_sl[-1]]:
            k = _last_opposite_before(i, False)
            if k is not None:
                trigger_by_key.setdefault((k, "bearish"), set()).add("bos_break")

    for i in _median_body_displacement_indices(fs, start, n):
        bullish_disp = fs.closes[i] > fs.opens[i]
        k = _last_opposite_before(i, bullish_disp)
        if k is not None:
            trigger_by_key.setdefault((k, "bullish" if bullish_disp else "bearish"), set()).add("median_displacement")

    obs: List[OrderBlock] = [
        OrderBlock(kind, k, fs.highs[k], fs.lows[k], trigger="+".join(sorted(triggers)))
        for (k, kind), triggers in trigger_by_key.items()
    ]

    seen = set()
    unique: List[OrderBlock] = []
    for ob in sorted(obs, key=lambda o: o.idx, reverse=True):
        key = (ob.idx, ob.kind)
        if key in seen:
            continue
        seen.add(key)
        unique.append(ob)
    unique = unique[:15]

    for ob in unique:
        for j in range(ob.idx + 1, n):
            if ob.kind == "bullish":
                if fs.lows[j] <= ob.top and fs.lows[j] >= ob.bottom:
                    ob.mitigated = True
                if fs.closes[j] < ob.bottom:
                    ob.breaker = True
            else:
                if fs.highs[j] >= ob.bottom and fs.highs[j] <= ob.top:
                    ob.mitigated = True
                if fs.closes[j] > ob.top:
                    ob.breaker = True
    return unique

def _find_fvgs(fs: FeatureSet, atr_v: Optional[float], max_lookback: int = 100) -> List[FairValueGap]:
    """Fair Value Gap: a 3-candle imbalance where candle[i-2].high < candle[i].low
    (bullish FVG, the gap is the untraded range between them) or
    candle[i-2].low > candle[i].high (bearish FVG). Only counted if the gap
    size clears a minimum ATR-relative threshold (filters noise on illiquid
    assets). Inverse FVG: a FVG that price has fully closed through -- it
    flips to acting as support/resistance in the opposite direction."""
    n = len(fs.closes)
    start = max(2, n - max_lookback)
    min_gap = (atr_v * PRODUCTION_PARAMS["fvg_min_gap_atr_mult"]) if atr_v else 0.0
    out: List[FairValueGap] = []
    for i in range(start, n):
        if fs.lows[i] > fs.highs[i - 2] and (fs.lows[i] - fs.highs[i - 2]) >= min_gap:
            out.append(FairValueGap("bullish", i - 1, fs.lows[i], fs.highs[i - 2]))
        elif fs.highs[i] < fs.lows[i - 2] and (fs.lows[i - 2] - fs.highs[i]) >= min_gap:
            out.append(FairValueGap("bearish", i - 1, fs.lows[i - 2], fs.highs[i]))

    for gap in out:
        for j in range(gap.idx + 2, n):
            if gap.kind == "bullish" and fs.closes[j] < gap.bottom:
                gap.inverse = True
            elif gap.kind == "bearish" and fs.closes[j] > gap.top:
                gap.inverse = True
    return out[-20:]

def _find_liquidity_pools(fs: FeatureSet, tolerance_pct: float) -> List[LiquidityPool]:
    """Equal Highs/Lows: 2+ swing points within tolerance_pct of each other,
    forming a resting-liquidity level. Buy-side liquidity sits above equal
    highs / recent swing highs; sell-side liquidity sits below equal lows /
    recent swing lows -- both are exact price levels, not annotations."""
    n = len(fs.closes)
    sh_idx = [j for j in range(n) if fs.swing_high[j]][-12:]
    sl_idx = [j for j in range(n) if fs.swing_low[j]][-12:]
    pools: List[LiquidityPool] = []

    def _cluster(idxs, values_fn, kind):
        used = set()
        for a in range(len(idxs)):
            if idxs[a] in used:
                continue
            base = values_fn(idxs[a])
            cluster = [idxs[a]]
            for b in range(a + 1, len(idxs)):
                if idxs[b] in used:
                    continue
                v = values_fn(idxs[b])
                if base and abs(v - base) / base * 100.0 <= tolerance_pct:
                    cluster.append(idxs[b])
            if len(cluster) >= 2:
                used.update(cluster)
                level = statistics.mean(values_fn(x) for x in cluster)
                pools.append(LiquidityPool(kind, level, cluster))

    _cluster(sh_idx, lambda j: fs.highs[j], "equal_highs")
    _cluster(sl_idx, lambda j: fs.lows[j], "equal_lows")

    if sh_idx:
        pools.append(LiquidityPool("buy_side", fs.highs[sh_idx[-1]], [sh_idx[-1]]))
    if sl_idx:
        pools.append(LiquidityPool("sell_side", fs.lows[sl_idx[-1]], [sl_idx[-1]]))

    lookback_bars = PRODUCTION_PARAMS["liquidity_sweep_lookback_bars"]
    confirm_bars = PRODUCTION_PARAMS["liquidity_sweep_confirm_bars"]
    last_i = n - 1
    for pool in pools:
        for j in range(max(0, last_i - lookback_bars), last_i + 1):
            if pool.kind in ("equal_highs", "buy_side") and fs.highs[j] > pool.level:
                for k in range(j, min(n, j + confirm_bars)):
                    if fs.closes[k] < pool.level:
                        pool.swept = True
                        break
            elif pool.kind in ("equal_lows", "sell_side") and fs.lows[j] < pool.level:
                for k in range(j, min(n, j + confirm_bars)):
                    if fs.closes[k] > pool.level:
                        pool.swept = True
                        break
    return pools

def evaluate_smc(fs: FeatureSet) -> Optional[SMCResult]:
    i = fs.last
    atr_v = fs.atr14[i]
    close = fs.closes[i]
    reasons: List[str] = []

    obs = _find_order_blocks(fs)
    fvgs = _find_fvgs(fs, atr_v)
    pools = _find_liquidity_pools(fs, PRODUCTION_PARAMS["equal_level_tolerance_pct"])

    sweeps = [f"{p.kind} liquidity swept at {p.level:.6g}" for p in pools if p.swept]

    sh_idx = [j for j in range(i + 1) if fs.swing_high[j]]
    sl_idx = [j for j in range(i + 1) if fs.swing_low[j]]
    zone = "equilibrium"
    if sh_idx and sl_idx:
        range_high = fs.highs[sh_idx[-1]]
        range_low = fs.lows[sl_idx[-1]]
        if range_high > range_low:
            pct = (close - range_low) / (range_high - range_low)
            if pct >= 0.60:
                zone = "premium"
            elif pct <= 0.40:
                zone = "discount"
            else:
                zone = "equilibrium"
            reasons.append(f"Price sits at {pct*100:.0f}% of dealing range -> {zone}")

    displacement = False
    if atr_v and i >= 1:
        candle_range = fs.highs[i] - fs.lows[i]
        if candle_range >= 1.5 * atr_v:
            close_pos = (close - fs.lows[i]) / candle_range if candle_range else 0.5
            if close_pos >= 0.66 or close_pos <= 0.34:
                displacement = True
                reasons.append("Displacement candle detected (range >=1.5x ATR, strong close)")

    fresh_bull_ob = [ob for ob in obs if ob.kind == "bullish" and not ob.breaker]
    fresh_bear_ob = [ob for ob in obs if ob.kind == "bearish" and not ob.breaker]
    if fresh_bull_ob:
        reasons.append(f"{len(fresh_bull_ob)} unmitigated/valid bullish order block(s) below price")
    if fresh_bear_ob:
        reasons.append(f"{len(fresh_bear_ob)} unmitigated/valid bearish order block(s) above price")
    if fvgs:
        reasons.append(f"{len(fvgs)} fair value gap(s) in recent structure")

    return SMCResult(obs, fvgs, pools, sweeps, zone, displacement, reasons)

@dataclass
class VolumeResult:
    relative_volume: float
    obv_trend: str
    cmf_bias: str
    institutional_participation: bool
    volume_climax: bool
    exhaustion: bool
    absorption: bool
    continuation: bool
    reasons: List[str]

def evaluate_volume(fs: FeatureSet) -> Optional[VolumeResult]:
    i = fs.last
    vol = fs.vols[i]
    vol_sma = fs.vol_sma20[i]
    if vol_sma is None or vol_sma == 0:
        return None
    reasons: List[str] = []
    rel_vol = round(vol / vol_sma, 2)

    obv_slope = linreg_slope(fs.obv[-20:], min(20, len(fs.obv))) if len(fs.obv) >= 5 else None
    obv_trend = "rising" if (obv_slope and obv_slope > 0) else ("falling" if (obv_slope and obv_slope < 0) else "flat")

    cmf_v = fs.cmf20[i]
    cmf_bias = "accumulation" if (cmf_v is not None and cmf_v > 0.05) else (
        "distribution" if (cmf_v is not None and cmf_v < -0.05) else "neutral")

    institutional_participation = rel_vol >= 1.5 and cmf_bias != "neutral"
    if institutional_participation:
        reasons.append(f"Relative volume {rel_vol}x with {cmf_bias} CMF bias -> institutional participation")

    atr_v = fs.atr14[i]
    candle_range = fs.highs[i] - fs.lows[i]
    volume_climax = rel_vol >= 3.0 and atr_v is not None and candle_range >= 1.3 * atr_v
    if volume_climax:
        reasons.append(f"Volume climax: {rel_vol}x average volume on an expanded-range candle")

    exhaustion = False
    if volume_climax and candle_range > 0:
        close_pos = (fs.closes[i] - fs.lows[i]) / candle_range
        prior_close = fs.closes[i - 1] if i > 0 else fs.closes[i]
        moved_up = fs.closes[i] > prior_close
        exhaustion = (moved_up and close_pos < 0.4) or (not moved_up and close_pos > 0.6)
        if exhaustion:
            reasons.append("Exhaustion signature: high volume but close rejected back into range")

    absorption = False
    if atr_v and rel_vol >= 1.8 and candle_range <= 0.5 * atr_v:
        absorption = True
        reasons.append("Absorption: elevated volume with compressed range (size absorbed)")

    continuation = obv_trend == "rising" and rel_vol >= 1.1 and fs.closes[i] > fs.closes[i - 1] if i > 0 else False
    continuation = continuation or (obv_trend == "falling" and rel_vol >= 1.1 and i > 0 and fs.closes[i] < fs.closes[i - 1])
    if continuation:
        reasons.append("Volume confirms directional continuation (OBV aligned with price)")

    return VolumeResult(rel_vol, obv_trend, cmf_bias, institutional_participation,
                         volume_climax, exhaustion, absorption, continuation, reasons)

@dataclass
class MomentumResult:
    rsi: Optional[float]
    macd_hist: Optional[float]
    stoch_rsi: Optional[float]
    momentum_state: str
    regular_divergence: Optional[str]
    hidden_divergence: Optional[str]
    reasons: List[str]

def _pivot_compare_divergence(
    fs: FeatureSet, osc: List[Optional[float]], max_lookback: int = 120,
) -> Tuple[Optional[str], Optional[str]]:
    """Divergence defined against a precise pivot-comparison rule: compare
    the two most recent confirmed swing highs (for bearish/regular-high
    divergence) or swing lows (bullish/regular-low divergence) in PRICE
    against the oscillator value at those exact same bar indices.
    Regular divergence = price makes a new extreme the oscillator does not
    confirm (reversal signal). Hidden divergence = price fails to make a new
    extreme while the oscillator does (continuation signal).
    AUDIT-L11 fix: previously scanned the full, unbounded candle window
    (up to 900 bars on 15M) with no recency cap, unlike its sibling SMC
    functions (_find_order_blocks: 120-bar cap; _find_liquidity_pools:
    12-pivot cap). In practice recent swing pivots almost always confirm
    well within this window, but an explicit cap removes the theoretical
    risk of comparing a pivot pair from stale, no-longer-relevant history."""
    n = len(fs.closes)
    start = max(0, n - max_lookback)
    sh_idx = [j for j in range(start, n) if fs.swing_high[j] and osc[j] is not None][-2:]
    sl_idx = [j for j in range(start, n) if fs.swing_low[j] and osc[j] is not None][-2:]

    regular = None
    hidden = None
    if len(sh_idx) == 2:
        p0, p1 = fs.highs[sh_idx[0]], fs.highs[sh_idx[1]]
        o0, o1 = osc[sh_idx[0]], osc[sh_idx[1]]
        if p1 > p0 and o1 < o0:
            regular = "bearish"
        elif p1 < p0 and o1 > o0:
            hidden = "bearish"
    if len(sl_idx) == 2:
        p0, p1 = fs.lows[sl_idx[0]], fs.lows[sl_idx[1]]
        o0, o1 = osc[sl_idx[0]], osc[sl_idx[1]]
        if p1 < p0 and o1 > o0:
            regular = regular or "bullish"
        elif p1 > p0 and o1 < o0:
            hidden = hidden or "bullish"
    return regular, hidden

def evaluate_momentum(fs: FeatureSet) -> Optional[MomentumResult]:
    i = fs.last
    rsi_v = fs.rsi14[i]
    hist_v = fs.macd_hist[i]
    stoch_v = fs.stoch_rsi[i]
    if rsi_v is None:
        return None
    reasons: List[str] = []

    hist_recent = [x for x in fs.macd_hist[-5:] if x is not None]
    if len(hist_recent) >= 3:
        d1 = hist_recent[-1] - hist_recent[-2]
        d2 = hist_recent[-2] - hist_recent[-3]
        if d1 > 0 and d2 > 0:
            state = "accelerating"
        elif d1 < 0 and d2 < 0:
            state = "decelerating"
        else:
            state = "flat"
    else:
        state = "flat"
    reasons.append(f"MACD histogram momentum: {state}")

    regular_div, hidden_div = _pivot_compare_divergence(fs, fs.rsi14)
    if regular_div:
        reasons.append(f"Regular {regular_div} RSI divergence at last two swing pivots")
    if hidden_div:
        reasons.append(f"Hidden {hidden_div} RSI divergence at last two swing pivots")

    return MomentumResult(rsi_v, hist_v, stoch_v, state, regular_div, hidden_div, reasons)

@dataclass
class VolatilityResult:
    atr: float
    atr_pctl: Optional[float]
    bb_width_pct: Optional[float]
    state: str
    breakout_condition: bool
    stop_quality_ok: bool
    reasons: List[str]

def evaluate_volatility(fs: FeatureSet) -> Optional[VolatilityResult]:
    i = fs.last
    atr_v = fs.atr14[i]
    if atr_v is None:
        return None
    reasons: List[str] = []
    atr_pctl = atr_percentile(fs.atr14, PRODUCTION_PARAMS["atr_percentile_lookback"])
    bb_u, bb_l, bb_m = fs.bb_upper[i], fs.bb_lower[i], fs.bb_mid[i]
    bb_width_pct = ((bb_u - bb_l) / bb_m * 100.0) if (bb_u and bb_l and bb_m) else None

    if atr_pctl is not None and atr_pctl >= 75:
        state = "expansion"
        reasons.append(f"ATR at {atr_pctl:.0f}th percentile of its own history -> expansion")
    elif atr_pctl is not None and atr_pctl <= 25:
        state = "compression"
        reasons.append(f"ATR at {atr_pctl:.0f}th percentile of its own history -> compression")
    else:
        state = "normal"

    dc_u, dc_l = fs.donchian_upper[i], fs.donchian_lower[i]
    breakout_condition = False
    if dc_u is not None and dc_l is not None and i > 0:
        prev_u, prev_l = fs.donchian_upper[i - 1], fs.donchian_lower[i - 1]
        if prev_u is not None and fs.closes[i] > prev_u:
            breakout_condition = True
        elif prev_l is not None and fs.closes[i] < prev_l:
            breakout_condition = True
    if breakout_condition:
        reasons.append("Donchian channel breakout condition met")

    price = fs.closes[i]
    atr_pct_of_price = (atr_v / price * 100.0) if price else None
    stop_quality_ok = atr_pct_of_price is not None and 0.15 <= atr_pct_of_price <= 6.0
    if not stop_quality_ok:
        reasons.append(f"ATR is {atr_pct_of_price:.2f}% of price -- outside sane stop-quality band")

    return VolatilityResult(atr_v, atr_pctl, bb_width_pct, state, breakout_condition, stop_quality_ok, reasons)

@dataclass
class LiquidityLevels:
    pdh: Optional[float]
    pdl: Optional[float]
    pwh: Optional[float]
    pwl: Optional[float]
    asia_high: Optional[float]
    asia_low: Optional[float]
    london_high: Optional[float]
    london_low: Optional[float]
    ny_high: Optional[float]
    ny_low: Optional[float]

@dataclass
class LiquidityResult:
    levels: LiquidityLevels
    sweep_events: List[str]
    stop_hunt: bool
    return_to_range: bool
    liquidity_grab: bool
    reasons: List[str]

def _session_extrema(candles_15m: List[Dict[str, Any]], hour_start: int, hour_end: int) -> Tuple[Optional[float], Optional[float]]:
    """hour_start/hour_end are UTC hour boundaries for the session, applied
    to the most recently completed instance of that session window."""
    if not candles_15m:
        return None, None
    now = datetime.fromtimestamp(candles_15m[-1]["t"] / 1000.0, tz=timezone.utc)
    day = now.date()
    session_start = datetime(day.year, day.month, day.day, hour_start, tzinfo=timezone.utc)
    session_end = datetime(day.year, day.month, day.day, hour_end, tzinfo=timezone.utc) if hour_end > hour_start else \
        datetime(day.year, day.month, day.day, hour_end, tzinfo=timezone.utc) + timedelta(days=1)
    if now < session_end:
        session_start -= timedelta(days=1)
        session_end -= timedelta(days=1)
    bars = [c for c in candles_15m if session_start.timestamp() * 1000 <= c["t"] < session_end.timestamp() * 1000]
    if not bars:
        return None, None
    return max(b["h"] for b in bars), min(b["l"] for b in bars)

def evaluate_liquidity(mtf_features: Dict[str, FeatureSet]) -> Optional[LiquidityResult]:
    fs_15m = mtf_features.get("15M")
    fs_1d = mtf_features.get("1D")
    if fs_15m is None:
        return None
    reasons: List[str] = []

    pdh = pdl = pwh = pwl = None
    if fs_1d and len(fs_1d.candles) >= 1:
        pdh, pdl = fs_1d.highs[-1], fs_1d.lows[-1]
    fs_4h = mtf_features.get("4H")
    if fs_4h:
        interval_ms_4h = _CANDLE_INTERVAL_MS.get("4H", 14_400_000)
        bars_per_day = max(1, round(86_400_000 / interval_ms_4h))
        bars_per_week = bars_per_day * 7
        if len(fs_4h.candles) >= bars_per_week:
            last_week = fs_4h.candles[-bars_per_week:-bars_per_day] or fs_4h.candles[-bars_per_week:]
            if last_week:
                pwh = max(c["h"] for c in last_week)
                pwl = min(c["l"] for c in last_week)

    asia_h, asia_l = _session_extrema(fs_15m.candles, 0, 8)
    london_h, london_l = _session_extrema(fs_15m.candles, 7, 16)
    ny_h, ny_l = _session_extrema(fs_15m.candles, 13, 21)
    levels = LiquidityLevels(pdh, pdl, pwh, pwl, asia_h, asia_l, london_h, london_l, ny_h, ny_l)

    close = fs_15m.closes[-1]
    sweep_events: List[str] = []
    stop_hunt = False
    return_to_range = False
    liquidity_grab = False

    recent = fs_15m.candles[-PRODUCTION_PARAMS["liquidity_sweep_lookback_bars"]:]
    confirm_bars = PRODUCTION_PARAMS["liquidity_sweep_confirm_bars"]
    level_map = {
        "PDH": pdh, "PDL": pdl, "PWH": pwh, "PWL": pwl,
        "Asian High": asia_h, "Asian Low": asia_l,
        "London High": london_h, "London Low": london_l,
        "NY High": ny_h, "NY Low": ny_l,
    }
    for name, level in level_map.items():
        if level is None:
            continue
        is_high_level = "High" in name or name in ("PDH", "PWH")
        for idx, c in enumerate(recent):
            pierced = c["h"] > level if is_high_level else c["l"] < level
            if not pierced:
                continue
            confirmed = False
            for c2 in recent[idx:idx + confirm_bars]:
                closed_back = c2["c"] < level if is_high_level else c2["c"] > level
                if closed_back:
                    sweep_events.append(f"{name} ({level:.6g}) swept then closed back inside range")
                    if name in ("PWH", "PWL"):
                        sweep_events.append(
                            f"(Note: {name} is an approximate rolling-week high/low from 4H candles, "
                            "not an exact calendar week)"
                        )
                    stop_hunt = True
                    if abs(close - level) / level * 100.0 < 0.5:
                        return_to_range = True
                    liquidity_grab = True
                    confirmed = True
                    break
            if confirmed:
                break

    if sweep_events:
        reasons.extend(sweep_events)
    if stop_hunt:
        reasons.append(f"Stop-hunt sequence confirmed (wick beyond level, close back inside within {confirm_bars} bars)")

    return LiquidityResult(levels, sweep_events, stop_hunt, return_to_range, liquidity_grab, reasons)

@dataclass
class MTFResult:
    per_tf_trend: Dict[str, str]
    aligned: bool
    veto: bool
    veto_reason: Optional[str]
    alignment_score: float
    soft_conflict: bool = False
    soft_conflict_reason: Optional[str] = None

def aggregate_mtf(mtf_trends: Dict[str, Optional[TrendResult]]) -> MTFResult:
    """Strongly prefer alignment across Daily, 4H, 1H, 30M before a 15M
    signal fires. Default: veto outright on a direct, confidently-held
    Daily-vs-4H conflict (Section 15); otherwise, disagreement scales down
    confidence via alignment_score rather than an automatic veto.

    FREQ1 fix: a direct Daily-vs-4H directional conflict now only hard-vetoes
    (early-exit before the remaining, more expensive sub-engines run) when
    BOTH reads clear `mtf_veto_strength_floor` on trend_strength. Previously
    ANY opposite-sign read vetoed outright, including a Daily direction that
    flipped on a single marginal vote (evaluate_trend's direction only needs
    bull_votes != bear_votes) against a strong, well-evidenced 4H trend --
    discarding a plausibly-good setup before structure/SMC/volume/momentum
    were ever evaluated. A conflict below the strength floor is now a soft,
    visible penalty on the risk-category score instead (see
    score_confluence), so the fixed confluence_threshold remains the actual
    quality gate rather than this earlier, blunter one."""
    per_tf: Dict[str, str] = {}
    per_tf_strength: Dict[str, float] = {}
    for tf in TIMEFRAMES:
        tr = mtf_trends.get(tf)
        per_tf[tf] = tr.trend_direction if tr else "unknown"
        per_tf_strength[tf] = tr.trend_strength if tr else 0.0

    veto = False
    veto_reason = None
    soft_conflict = False
    soft_conflict_reason = None
    daily, h4 = per_tf.get("1D"), per_tf.get("4H")
    daily_strength = per_tf_strength.get("1D", 0.0)
    h4_strength = per_tf_strength.get("4H", 0.0)
    floor = PRODUCTION_PARAMS["mtf_veto_strength_floor"]
    if daily in ("bullish", "bearish") and h4 in ("bullish", "bearish") and daily != h4:
        if daily_strength >= floor and h4_strength >= floor:
            veto = True
            veto_reason = (f"Daily bias ({daily}, strength {daily_strength:.0f}) directly conflicts with "
                            f"4H bias ({h4}, strength {h4_strength:.0f}) -- both above the {floor:.0f} confidence floor")
        else:
            soft_conflict = True
            soft_conflict_reason = (f"Daily bias ({daily}, strength {daily_strength:.0f}) conflicts with "
                                     f"4H bias ({h4}, strength {h4_strength:.0f}), but at least one side is below "
                                     f"the {floor:.0f} confidence floor for a hard veto")

    exec_dir = per_tf.get(EXECUTION_TF, "unknown")
    higher_tfs = [tf for tf in TIMEFRAMES if tf != EXECUTION_TF]
    agree = sum(1 for tf in higher_tfs if per_tf.get(tf) == exec_dir and exec_dir in ("bullish", "bearish"))
    alignment_score = round(agree / len(higher_tfs), 2) if higher_tfs else 0.0
    aligned = alignment_score >= 0.75

    return MTFResult(per_tf, aligned, veto, veto_reason, alignment_score, soft_conflict, soft_conflict_reason)

@dataclass
class ConfluenceResult:
    total_score: float
    category_scores: Dict[str, float]
    category_weights: Dict[str, float]
    reasons_by_category: Dict[str, List[str]]
    direction: str
    fired_features: List[str]

def _regime_adjusted_weights(regime: str) -> Dict[str, float]:
    mult = REGIME_WEIGHT_MULTIPLIERS.get(regime, {k: 1.0 for k in BASE_CATEGORY_WEIGHTS})
    raw = {k: BASE_CATEGORY_WEIGHTS[k] * mult.get(k, 1.0) for k in BASE_CATEGORY_WEIGHTS}
    total = sum(raw.values())
    return {k: round(v / total * 100.0, 4) for k, v in raw.items()}

def _weighted_condition_score(
    conditions: List[Tuple[bool, float, Optional[str], Optional[str]]],
    feature_weights: Dict[str, float],
) -> Tuple[float, List[str], List[str]]:
    """Shared declarative scoring helper (Section B.1, ported from Vantage
    Point's `_weighted_bool_score` and adapted to Axis's point-based, rather
    than fraction-based, category scoring). `conditions` is a list of
    (fired, points, feature_key, reason_text) tuples -- exactly Axis's
    original per-category point values, just no longer expressed as
    repeated manual `+=` arithmetic. A fired condition contributes `points`
    to the category total, scaled by that feature's current adaptive weight
    times the candidate-feature count when `feature_key` is given (matching
    Axis's existing adaptive-weight convention exactly), or the raw
    `points` value when `feature_key` is None. Returns the (uncapped) raw
    total plus the reasons for every fired condition that supplied
    non-empty reason text; category-specific capping/post-adjustment is
    left to the caller since a couple of categories apply one further,
    genuinely different scaling step after this (see score_confluence)."""
    total = 0.0
    reasons: List[str] = []
    fired_features: List[str] = []
    for fired, points, feature_key, reason in conditions:
        if not fired:
            continue
        pts = points
        if feature_key is not None:
            pts *= feature_weights.get(feature_key, DEFAULT_FEATURE_WEIGHT) * len(CANDIDATE_FEATURES)
            fired_features.append(feature_key)
        total += pts
        if reason:
            reasons.append(reason)
    return total, reasons, fired_features

def score_confluence(
    trend: TrendResult, structure: StructureResult, smc: SMCResult,
    volume: VolumeResult, momentum: MomentumResult, volatility: VolatilityResult,
    liquidity: LiquidityResult, regime: RegimeResult, mtf: MTFResult,
    feature_weights: Dict[str, float],
) -> ConfluenceResult:
    """Single weighted 0-100 composite from category sub-scores (Section 16).
    Each category sub-score is itself a 0-100 evidence tally, then combined
    with the regime-adjusted category weights. Feature-level weights
    (Section 5, adaptive) scale how much each contributing condition counts
    within its category, so a degraded/disabled feature contributes less (or
    nothing) without deleting the underlying detection code."""
    weights = _regime_adjusted_weights(regime.market_regime)
    reasons: Dict[str, List[str]] = {k: [] for k in weights}
    cat: Dict[str, float] = {k: 0.0 for k in weights}

    bullish_bias = trend.trend_direction == "bullish"
    bearish_bias = trend.trend_direction == "bearish"

    TREND_STRENGTH_AGREEMENT_FLOOR = 60.0
    trend_reliability = (
        min(1.0, trend.trend_strength / TREND_STRENGTH_AGREEMENT_FLOOR)
        if (bullish_bias or bearish_bias) else 0.0
    )

    trend_conditions: List[Tuple[bool, float, Optional[str], Optional[str]]] = [
        (True, trend.trend_strength * 0.6 + trend.trend_quality * 0.4, "ema_stack", None),
        (trend.sma_trend_aligned, 15.0, "sma_trend", None),
        (trend.price_above_vwap is not None and ((trend.price_above_vwap and bullish_bias) or (not trend.price_above_vwap and bearish_bias)),
         15.0, "vwap", None),
        (trend.adx_strong and (bullish_bias or bearish_bias), 15.0, "adx", None),
    ]
    t_raw, _, t_fired = _weighted_condition_score(trend_conditions, feature_weights)
    cat["trend"] = min(100.0, t_raw)
    reasons["trend"].extend(trend.reasons)

    structure_conditions: List[Tuple[bool, float, Optional[str], Optional[str]]] = [
        (bool(structure.bos) and (bullish_bias or bearish_bias) and ((structure.bos == "bullish") == bullish_bias), 45.0 * trend_reliability, "bos", None),
        (bool(structure.choch) and (bullish_bias or bearish_bias) and ((structure.choch == "bullish") == bullish_bias), 25.0 * trend_reliability, "choch", None),
        (structure.internal_trend == structure.external_trend and structure.internal_trend != "neutral",
         20.0, None, "Internal structure aligned with external (major) structure"),
        (structure.continuation_or_reversal == "continuation", 10.0, None, None),
    ]
    s_raw, s_reasons, s_fired = _weighted_condition_score(structure_conditions, feature_weights)
    cat["structure"] = min(100.0, s_raw)
    reasons["structure"].extend(s_reasons)
    reasons["structure"].extend(structure.reasons)

    rsi_in_range = momentum.rsi is not None and (
        (bullish_bias and 45 <= momentum.rsi <= 70) or (bearish_bias and 30 <= momentum.rsi <= 55)
    )
    momentum_conditions: List[Tuple[bool, float, Optional[str], Optional[str]]] = [
        (rsi_in_range, 25.0 * trend_reliability, "rsi", None),
        (momentum.momentum_state == "accelerating" and (bullish_bias or bearish_bias), 25.0 * trend_reliability, "macd", None),
        (bool(momentum.regular_divergence) and (
            (momentum.regular_divergence == "bullish" and bullish_bias) or
            (momentum.regular_divergence == "bearish" and bearish_bias)
        ), 20.0, None, None),
        (bool(momentum.hidden_divergence) and (
            (momentum.hidden_divergence == "bullish" and bullish_bias) or
            (momentum.hidden_divergence == "bearish" and bearish_bias)
        ), 15.0, None, None),
    ]
    m_raw, _, m_fired = _weighted_condition_score(momentum_conditions, feature_weights)
    cat["momentum"] = min(100.0, m_raw)
    reasons["momentum"].extend(momentum.reasons)

    dir_kind = "bullish" if bullish_bias else ("bearish" if bearish_bias else None)
    fresh_ob_aligned = dir_kind is not None and any(
        ob.kind == dir_kind and not ob.breaker and not ob.mitigated for ob in smc.order_blocks)
    breaker_ob_aligned = dir_kind is not None and any(
        ob.kind == dir_kind and ob.breaker for ob in smc.order_blocks)
    mitigated_ob_aligned = dir_kind is not None and any(
        ob.kind == dir_kind and ob.mitigated for ob in smc.order_blocks)
    fvg_aligned = dir_kind is not None and any(f.kind == dir_kind for f in smc.fvgs)
    equal_hl_aligned = (bullish_bias and any(p.swept and p.kind in ("equal_lows", "sell_side") for p in smc.liquidity_pools)) or \
                        (bearish_bias and any(p.swept and p.kind in ("equal_highs", "buy_side") for p in smc.liquidity_pools))

    liquidity_conditions: List[Tuple[bool, float, Optional[str], Optional[str]]] = [
        (bool(liquidity.stop_hunt), 40.0, "liquidity_sweep", None),
        (bool(liquidity.return_to_range), 20.0, None, None),
        (smc.zone == "discount" and bullish_bias, 20.0, None, "Long setup located in discount zone of dealing range"),
        (smc.zone == "premium" and bearish_bias, 20.0, None, "Short setup located in premium zone of dealing range"),
        (bool(smc.sweeps), 15.0, "liquidity_sweep", None),
        (fresh_ob_aligned, 20.0, "order_block", f"Fresh {dir_kind} order block supporting the setup" if dir_kind else None),
        (breaker_ob_aligned, 15.0, "breaker_block", f"{dir_kind} breaker block supporting the setup" if dir_kind else None),
        (mitigated_ob_aligned, 10.0, "mitigation_block", f"{dir_kind} mitigation block reacted to price" if dir_kind else None),
        (fvg_aligned, 15.0, "fair_value_gap", f"Aligned {dir_kind} fair value gap present" if dir_kind else None),
        (equal_hl_aligned, 15.0, "equal_highs_lows", "Equal highs/lows liquidity swept in the direction of the setup"),
    ]
    l_raw, l_reasons, l_fired = _weighted_condition_score(liquidity_conditions, feature_weights)
    cat["liquidity"] = min(100.0, l_raw)
    reasons["liquidity"].extend(l_reasons)
    reasons["liquidity"].extend(liquidity.reasons)

    volume_conditions: List[Tuple[bool, float, Optional[str], Optional[str]]] = [
        (bool(volume.institutional_participation)
         and ((volume.cmf_bias == "accumulation" and bullish_bias) or (volume.cmf_bias == "distribution" and bearish_bias)),
         35.0, "cmf", None),
        (bool(volume.continuation)
         and ((volume.obv_trend == "rising" and bullish_bias) or (volume.obv_trend == "falling" and bearish_bias)),
         30.0, "obv", None),
        (bool(volume.absorption) and smc.zone in ("discount", "premium"), 20.0, None, "Absorption detected at a premium/discount extreme"),
        (bool(volume.exhaustion) and not (bullish_bias or bearish_bias), 10.0, None, None),
    ]
    v_raw, v_reasons, v_fired = _weighted_condition_score(volume_conditions, feature_weights)
    cat["volume"] = min(100.0, v_raw)
    reasons["volume"].extend(v_reasons)
    reasons["volume"].extend(volume.reasons)

    volatility_conditions: List[Tuple[bool, float, Optional[str], Optional[str]]] = [
        (bool(volatility.stop_quality_ok), 40.0, "atr_stop_quality", None),
        (volatility.state == "expansion" and regime.market_regime in ("Breakout", "Expansion", "Strong Bull Trend", "Strong Bear Trend"), 35.0, None, None),
        (volatility.state == "compression" and regime.market_regime in ("Compression", "Range", "Sideways"), 25.0, None, None),
        (bool(volatility.breakout_condition), 25.0, "donchian_channels", None),
        (volatility.bb_width_pct is not None and volatility.state in ("expansion", "compression"),
         15.0, "bollinger_bands", None),
    ]
    vol_raw, _, vol_fired = _weighted_condition_score(volatility_conditions, feature_weights)
    cat["volatility"] = min(100.0, vol_raw)
    if not volatility.stop_quality_ok:
        reasons["volatility"].append("Stop-placement quality unfavorable at current volatility")
    reasons["volatility"].extend(volatility.reasons)

    internal_vs_trend_agree = (
        (bullish_bias or bearish_bias)
        and structure.internal_trend != "neutral"
        and structure.internal_trend == trend.trend_direction
    )
    internal_vs_trend_conflict = (
        (bullish_bias or bearish_bias)
        and structure.internal_trend != "neutral"
        and structure.internal_trend != trend.trend_direction
    )
    risk_conditions: List[Tuple[bool, float, Optional[str], Optional[str]]] = [
        (internal_vs_trend_agree, 15.0, None,
         "Internal (swing) structure trend agrees with the EMA/ADX trend read"),
    ]
    r_raw, _, r_fired = _weighted_condition_score(risk_conditions, feature_weights)
    r_raw += mtf.alignment_score * 100
    if mtf.soft_conflict:
        r_raw *= 0.70
    cat["risk"] = min(100.0, r_raw)
    reasons["risk"].append(f"Higher-timeframe alignment score: {mtf.alignment_score}")
    if internal_vs_trend_conflict:
        reasons["risk"].append(
            f"Caution: internal swing structure reads {structure.internal_trend} while the "
            f"EMA/ADX trend read is {trend.trend_direction} -- these two trend evidences disagree"
        )
    if mtf.soft_conflict:
        reasons["risk"].append(f"Caution: {mtf.soft_conflict_reason}")

    total = sum(cat[k] * weights[k] / 100.0 for k in cat)

    if internal_vs_trend_conflict:
        total *= 0.85

    fired_features = sorted(set(t_fired + s_fired + m_fired + l_fired + v_fired + vol_fired + r_fired))

    if mtf.veto:
        direction = "WAIT"
        reasons["risk"].append(f"VETO: {mtf.veto_reason}")
        total = min(total, PRODUCTION_PARAMS["confluence_threshold"] - 1)
    elif bullish_bias and not bearish_bias:
        direction = "LONG"
    elif bearish_bias and not bullish_bias:
        direction = "SHORT"
    else:
        direction = "WAIT"

    return ConfluenceResult(round(total, 2), cat, weights, reasons, direction, fired_features)

@dataclass
class SignalDecision:
    direction: str
    entry: Optional[float]
    stop_loss: Optional[float]
    tp1: Optional[float]
    tp2: Optional[float]
    tp3: Optional[float]
    risk_reward: Optional[float]
    holding_time: str
    win_probability: float
    confidence: float
    grade: str
    reasons: List[str]
    fired_features: Optional[List[str]] = None
    tier: str = "none"

def _entry_engine(
    fs_15m: FeatureSet, structure: StructureResult, smc: SMCResult,
    volatility: VolatilityResult, direction: str,
) -> Tuple[Optional[float], Optional[float], Optional[float], Optional[float], Optional[float]]:
    """Entry = current close (execution timeframe, market-on-close of the
    just-finished 15M bar -- consistent with the "one look every 15 minutes"
    cadence discipline). Stop = beyond the nearest structurally relevant
    invalidation point (protected high/low, or nearest valid order block
    edge), padded by a small ATR buffer so normal noise doesn't stop out a
    structurally correct trade. Targets = R-multiples of the resulting risk,
    with TP1 additionally capped at the nearest opposing liquidity pool /
    order block if one sits closer than the pure R-multiple target (a
    realistic, reachable first target)."""
    entry = fs_15m.closes[fs_15m.last]
    atr_v = volatility.atr
    buffer = 0.25 * atr_v
    if ENTRY_MODEL == "retest_limit" and direction in ("LONG", "SHORT"):
        # Flag-gated (default off): limit entry a fraction of ATR back toward
        # structure instead of chasing the close; stop/targets key off it.
        entry = entry - RETEST_ATR_FRACTION * atr_v if direction == "LONG" else entry + RETEST_ATR_FRACTION * atr_v

    if direction == "LONG":
        struct_stop = structure.protected_low
        ob_stops = [ob.bottom for ob in smc.order_blocks if ob.kind == "bullish" and not ob.breaker and ob.bottom < entry]
        candidates = [x for x in [struct_stop] + ob_stops if x is not None and x < entry]
        stop = (max(candidates) if candidates else entry - 2 * atr_v) - buffer
        risk = entry - stop
        if risk <= 0:
            return entry, None, None, None, None
        tp1, tp2, tp3 = entry + 1.5 * risk, entry + 2.5 * risk, entry + 4.0 * risk
        opposing_pools = [p.level for p in smc.liquidity_pools if p.level > entry and p.kind in ("equal_highs", "buy_side")]
        if opposing_pools:
            nearest = min(opposing_pools)
            if entry < nearest < tp1:
                tp1 = nearest
    elif direction == "SHORT":
        struct_stop = structure.protected_high
        ob_stops = [ob.top for ob in smc.order_blocks if ob.kind == "bearish" and not ob.breaker and ob.top > entry]
        candidates = [x for x in [struct_stop] + ob_stops if x is not None and x > entry]
        stop = (min(candidates) if candidates else entry + 2 * atr_v) + buffer
        risk = stop - entry
        if risk <= 0:
            return entry, None, None, None, None
        tp1, tp2, tp3 = entry - 1.5 * risk, entry - 2.5 * risk, entry - 4.0 * risk
        opposing_pools = [p.level for p in smc.liquidity_pools if p.level < entry and p.kind in ("equal_lows", "sell_side")]
        if opposing_pools:
            nearest = max(opposing_pools)
            if tp1 < nearest < entry:
                tp1 = nearest
    else:
        return entry, None, None, None, None

    return entry, stop, tp1, tp2, tp3

def _holding_time_estimate(regime: str, volatility: VolatilityResult) -> str:
    """Deterministic mapping from regime + volatility state to an expected
    holding-time bucket for a 15M-execution / 1H-4H-context swing setup."""
    if regime in ("Strong Bull Trend", "Strong Bear Trend", "Breakout", "Expansion"):
        return "6-24 hours"
    if regime in ("Compression", "Low Volatility"):
        return "12-48 hours"
    if regime in ("Range", "Sideways", "Mean Reversion"):
        return "2-12 hours"
    return "4-18 hours"

def _win_probability_estimate(confluence: float, feature_calibration: Optional[Dict[str, Any]]) -> float:
    """Calibrated win probability for the signal's grade. Uses the rolling
    realized win rate of the grade (feature_calibration, from
    run_self_monitoring), shrunk toward CALIBRATION_PRIOR_WIN_RATE with
    CALIBRATION_PRIOR_STRENGTH pseudo-trades, so a grade with no/little
    history advertises the no-edge prior (not the old score-derived ~80%)
    and converges to realized results as trades accrue. `confluence` is kept
    for signature compatibility; the old score->probability map was the
    source of the grade-B 80% vs 37% realized miscalibration."""
    n = int((feature_calibration or {}).get("sample_size", 0) or 0)
    observed = (feature_calibration or {}).get("observed_win_rate")
    wins = (observed * n) if (observed is not None and n > 0) else 0.0
    if observed is None:
        n = 0
    p = (wins + CALIBRATION_PRIOR_STRENGTH * CALIBRATION_PRIOR_WIN_RATE) / (n + CALIBRATION_PRIOR_STRENGTH)
    return round(max(0.05, min(0.95, p)), 4)

def build_signal_decision(
    fs_15m: FeatureSet, trend: TrendResult, structure: StructureResult, smc: SMCResult,
    volume: VolumeResult, momentum: MomentumResult, volatility: VolatilityResult,
    liquidity: LiquidityResult, regime: RegimeResult, mtf: MTFResult,
    confluence: ConfluenceResult, calibration: Optional[Dict[str, Any]],
) -> SignalDecision:
    threshold = PRODUCTION_PARAMS["confluence_threshold"]
    watch_threshold = PRODUCTION_PARAMS["watch_tier_threshold"]
    direction = confluence.direction
    if confluence.total_score < watch_threshold or direction == "WAIT":
        return SignalDecision(
            "WAIT", None, None, None, None, None, None, "-", 0.0,
            confluence.total_score, score_to_grade(confluence.total_score),
            ["Composite score below watch threshold or no directional edge -- no trade."],
            fired_features=[],
        )

    entry, stop, tp1, tp2, tp3 = _entry_engine(fs_15m, structure, smc, volatility, direction)
    if stop is None or entry is None:
        return SignalDecision(
            "WAIT", None, None, None, None, None, None, "-", 0.0,
            confluence.total_score, score_to_grade(confluence.total_score),
            ["No valid structural stop could be derived -- no trade."],
            fired_features=[],
        )
    risk = abs(entry - stop)
    reward = abs(tp1 - entry)
    rr = round(reward / risk, 2) if risk else None
    if rr is None or rr < 1.5:
        return SignalDecision(
            "WAIT", None, None, None, None, None, None, "-", 0.0,
            confluence.total_score, score_to_grade(confluence.total_score),
            [f"Risk/reward to TP1 ({rr}) below minimum acceptable threshold -- no trade."],
            fired_features=[],
        )

    win_prob = _win_probability_estimate(confluence.total_score, calibration)
    grade = score_to_grade(confluence.total_score)
    holding_time = _holding_time_estimate(regime.market_regime, volatility)
    tier = "signal" if confluence.total_score >= threshold else "watch"

    reasons: List[str] = []
    for cat_reasons in confluence.reasons_by_category.values():
        reasons.extend(cat_reasons)
    if tier == "watch":
        reasons.insert(
            0,
            f"WATCH TIER: composite {confluence.total_score:.1f} clears the {watch_threshold}-point watch "
            f"floor but not the {threshold}-point signal threshold -- developing setup, not a trade signal.",
        )

    return SignalDecision(
        direction, round(entry, 6), round(stop, 6), round(tp1, 6),
        round(tp2, 6) if tp2 else None, round(tp3, 6) if tp3 else None,
        rr, holding_time, win_prob, confluence.total_score, grade, reasons,
        fired_features=list(confluence.fired_features), tier=tier,
    )

CORRELATION_MIN_OVERLAP_BARS = 60

CORRELATION_SECTOR_BUCKETS: Dict[str, str] = {
    "BTC": "majors", "ETH": "majors",
    "SOL": "l1_smart_contract", "NEAR": "l1_smart_contract", "SUI": "l1_smart_contract",
    "AVAX": "l1_smart_contract", "ADA": "l1_smart_contract", "DOT": "l1_smart_contract",
    "APT": "l1_smart_contract", "TAO": "l1_smart_contract",
    "BNB": "exchange_ecosystem",
    "TRX": "payments_legacy", "XRP": "payments_legacy", "XLM": "payments_legacy",
    "BCH": "payments_legacy", "LTC": "payments_legacy",
    "DOGE": "meme",
    "LINK": "defi_infra", "AAVE": "defi_infra", "UNI": "defi_infra",
    "ONDO": "defi_infra", "PENDLE": "defi_infra",
    "HYPE": "perp_dex", "ZEC": "privacy", "PENGU": "meme",
}

def _correlation_bucket(symbol: str) -> str:
    return CORRELATION_SECTOR_BUCKETS.get(symbol, f"unbucketed:{symbol}")

def _return_series(candles: List[Dict[str, Any]]) -> List[float]:
    """Simple period-over-period close return series from a closed-candle
    list (Section B.4), used as the input to the real Pearson correlation
    calculation."""
    closes_ = [c["c"] for c in candles]
    return [(closes_[i] / closes_[i - 1] - 1.0) for i in range(1, len(closes_)) if closes_[i - 1]]

def _pearson_correlation(a: List[float], b: List[float]) -> Optional[float]:
    """Pearson correlation coefficient between two return series (Section
    B.4), using only the most recent overlapping window. Returns None if
    there isn't enough overlapping history or either series is constant
    (zero variance)."""
    n = min(len(a), len(b))
    if n < CORRELATION_MIN_OVERLAP_BARS:
        return None
    a, b = a[-n:], b[-n:]
    mean_a, mean_b = sum(a) / n, sum(b) / n
    cov = sum((x - mean_a) * (y - mean_b) for x, y in zip(a, b))
    var_a = sum((x - mean_a) ** 2 for x in a)
    var_b = sum((y - mean_b) ** 2 for y in b)
    denom = math.sqrt(var_a * var_b)
    if denom == 0:
        return None
    return cov / denom

def evaluate_correlation_risk_gate(
    symbol: str, direction: str, open_positions: List[Dict[str, Any]],
    cache: Optional["CandleCacheStore"], p: Dict[str, Any] = PRODUCTION_PARAMS,
) -> Tuple[bool, List[str]]:
    """Correlation-aware portfolio risk gate (Section B.4, ported from
    Halcyon's evaluate_risk_gates() and then extended). Halcyon's only
    genuinely functional correlation-adjacent check was a majors (BTC/ETH)
    vs. alts bucket proxy that vetoes a second same-direction signal in the
    same bucket -- that proxy is kept here as a FALLBACK, and (AUDIT-M4)
    refined from one flat "alts" bucket into several sector buckets
    (CORRELATION_SECTOR_BUCKETS) so unrelated alts no longer veto each other
    by default. The primary check is a real rolling Pearson correlation
    between each currently-open signal's symbol and the candidate symbol,
    computed from their cached closed-candle return series on the execution
    timeframe (the candle cache already holds enough history for this); a
    same-direction pair at or above `correlation_filter_threshold` vetoes
    the candidate. The bucket proxy is only used for a given pair when
    there isn't enough overlapping cached candle history for a real
    calculation."""
    threshold = p["correlation_filter_threshold"]
    veto: List[str] = []

    cand_returns: Optional[List[float]] = None
    if cache is not None:
        cand_candles = cache.get(symbol, EXECUTION_TF)
        cand_returns = _return_series(cand_candles) if cand_candles else None

    for pos in open_positions:
        other_symbol = pos.get("symbol")
        other_direction = pos.get("signal") or pos.get("direction")
        if not other_symbol or other_symbol == symbol or other_direction != direction:
            continue

        corr: Optional[float] = None
        if cache is not None and cand_returns:
            other_candles = cache.get(other_symbol, EXECUTION_TF)
            other_returns = _return_series(other_candles) if other_candles else None
            if other_returns:
                corr = _pearson_correlation(cand_returns, other_returns)

        if corr is not None:
            if abs(corr) >= threshold:
                veto.append(
                    f"Correlation filter: open {other_direction} signal on {other_symbol} correlates "
                    f"{corr:.2f} with {symbol} (>= {threshold:.2f} threshold)"
                )
        else:
            bucket = _correlation_bucket(symbol)
            other_bucket = _correlation_bucket(other_symbol)
            if bucket == other_bucket and not bucket.startswith("unbucketed:"):
                veto.append(
                    f"Correlation-cluster fallback: an open {direction} signal already exists in the "
                    f"'{bucket}' bucket (insufficient candle history for {symbol}/{other_symbol} "
                    f"to compute a real correlation)"
                )

    return (not veto, veto)

@dataclass
class PositionSizeResult:
    method: str
    position_size_units: Optional[float]
    risk_amount: Optional[float]
    notes: List[str]
    risk_pct_of_equity: Optional[float] = None

def _update_breaker_state(state: Dict[str, Any], p: Dict[str, Any] = PRODUCTION_PARAMS) -> List[str]:
    """Main-thread (before the scan fan-out) evaluation of the drawdown
    circuit breaker over the never-pruned trade history, measured from the
    last re-baseline. Trips at max_drawdown_circuit_breaker_pct and
    auto-recovers after BREAKER_COOLDOWN_HOURS by re-baselining the equity
    peak, so a tripped breaker cannot lock the engine out forever (it blocks
    the very signals whose trades would repair the drawdown)."""
    lines: List[str] = []
    br = state.setdefault("breaker", {"status": "ok", "reason": None, "tripped_at": None,
                                      "rebaselined_at": None, "trip_count": 0})
    since = br.get("rebaselined_at") or ""
    running = peak = 0.0
    for c in _resolved_history(state):
        if (c.get("resolved_at") or "") < since:
            continue
        rp = (c.get("position_sizing") or {}).get("risk_pct_of_equity")
        running += _resolved_pnl_r(c) * (rp if rp is not None else p["risk_per_trade_pct"])
        peak = max(peak, running)
    drawdown_pct = peak - running
    limit = abs(p["max_drawdown_circuit_breaker_pct"])
    now = _utcnow()
    if br["status"] == "ok":
        if drawdown_pct >= limit:
            br.update(status="tripped", tripped_at=now.isoformat(), trip_count=br.get("trip_count", 0) + 1,
                      reason=f"Drawdown circuit breaker triggered: {drawdown_pct:.2f}% (limit {limit:.2f}%).")
            lines.append(f"[Breaker] TRIPPED -- {br['reason']} Dispatch mode: {BREAKER_DISPATCH_MODE}.")
    else:
        tripped_at = _parse_iso(br.get("tripped_at"))
        if drawdown_pct < limit:
            br.update(status="ok", reason=None, tripped_at=None)
            lines.append("[Breaker] cleared (drawdown back under limit).")
        elif tripped_at is None or (now - tripped_at) >= timedelta(hours=BREAKER_COOLDOWN_HOURS):
            br.update(status="ok", reason=None, tripped_at=None, rebaselined_at=now.isoformat())
            lines.append(f"[Breaker] auto-reset after {BREAKER_COOLDOWN_HOURS}h cooldown; drawdown baseline "
                         "re-set (recovery independent of signal flow).")
    return lines

def _breaker_reason(state: Dict[str, Any], p: Dict[str, Any] = PRODUCTION_PARAMS) -> Optional[str]:
    """Reason string if a breaker (drawdown breaker or daily-loss
    kill-switch) is currently tripped, else None. Read-only (worker-thread
    safe); the drawdown state itself is maintained by _update_breaker_state."""
    today = _utcnow().strftime("%Y-%m-%d")
    day_bucket = state.get("daily_stats", {}).get(today, {})
    rr_list = day_bucket.get("rr_list", [])
    risk_pct_list = day_bucket.get("risk_pct_list", [])
    if rr_list:
        realized_pct = sum(
            r * (risk_pct_list[idx] if idx < len(risk_pct_list) else p["risk_per_trade_pct"])
            for idx, r in enumerate(rr_list)
        )
        if realized_pct <= -abs(p["max_daily_loss_pct"]):
            return (f"Daily loss kill-switch triggered: realized {realized_pct:.2f}% "
                    f"(limit -{p['max_daily_loss_pct']:.2f}%).")
    br = state.get("breaker", {})
    if br.get("status") == "tripped":
        return br.get("reason")
    return None

def _check_portfolio_guardrails(state: Dict[str, Any], open_positions: List[Dict[str, Any]],
                                 p: Dict[str, Any] = PRODUCTION_PARAMS,
                                 include_breaker: bool = True) -> Optional[str]:
    """C1 fix: actually enforce the portfolio guardrails PRODUCTION_PARAMS
    documents as active (max concurrent positions, daily realized-loss
    kill-switch, rolling-drawdown circuit breaker). Returns a veto reason
    string if a signal should be blocked, else None. scan_symbol passes
    include_breaker=False and handles breaker trips itself so their dispatch
    behaviour follows BREAKER_DISPATCH_MODE."""
    if len(open_positions) >= p["max_concurrent_positions"]:
        return f"Max concurrent positions reached ({len(open_positions)}/{p['max_concurrent_positions']})."
    return _breaker_reason(state, p) if include_breaker else None

def compute_position_size(
    account_equity: float, entry: float, stop: float, atr_v: float,
    open_positions: List[Dict[str, Any]], win_rate: Optional[float], avg_rr: Optional[float],
    symbol: Optional[str] = None, direction: Optional[str] = None,
    cache: Optional["CandleCacheStore"] = None,
    p: Dict[str, Any] = PRODUCTION_PARAMS,
) -> PositionSizeResult:
    """ATR-based / fixed-risk-% position sizing with a portfolio of guardrails
    (Section 17.3): max concurrent positions, max daily loss, drawdown
    circuit breaker, exposure cap, a real correlation filter (Section B.4 /
    A.1 -- `correlation_filter_threshold` is now actually evaluated via
    `evaluate_correlation_risk_gate()` whenever `symbol`/`direction` are
    supplied, rather than being defined and never consulted), and an
    optional Kelly-criterion sizing mode. This function is advisory sizing
    math only -- this engine places no orders; it is surfaced for
    completeness / downstream consumers of the signal JSON. The correlation
    gate itself is also invoked directly from scan_symbol()'s pipeline
    before a signal is finalized (see Section 22), independent of whether
    this sizing function is called."""
    notes: List[str] = []
    if len(open_positions) >= p["max_concurrent_positions"]:
        return PositionSizeResult("blocked", 0.0, 0.0, ["Max concurrent positions reached -- size forced to 0."])

    if symbol is not None and direction is not None:
        corr_passed, corr_veto = evaluate_correlation_risk_gate(symbol, direction, open_positions, cache, p)
        if not corr_passed:
            return PositionSizeResult("blocked", 0.0, 0.0, corr_veto)

    risk_pct = p["risk_per_trade_pct"] / 100.0
    risk_amount = account_equity * risk_pct

    if p["kelly_mode_enabled"] and win_rate is not None and avg_rr:
        b = avg_rr
        kelly_f = win_rate - (1 - win_rate) / b if b else 0.0
        kelly_f = max(0.0, min(kelly_f, p["kelly_fraction_cap"]))
        risk_amount = account_equity * kelly_f
        notes.append(f"Kelly sizing applied: f={kelly_f:.4f} (capped at {p['kelly_fraction_cap']})")
        method = "kelly"
    else:
        method = "fixed_risk_pct"

    risk_per_unit = abs(entry - stop)
    if risk_per_unit <= 0:
        return PositionSizeResult(method, None, None, ["Invalid stop distance -- cannot size position."])

    size_units = risk_amount / risk_per_unit

    exposure_notional = size_units * entry
    exposure_pct = exposure_notional / account_equity * 100.0 if account_equity else 0.0
    if exposure_pct > p["portfolio_exposure_cap_pct"]:
        size_units *= p["portfolio_exposure_cap_pct"] / exposure_pct
        notes.append("Position trimmed to respect portfolio exposure cap.")

    risk_pct_of_equity = round(risk_amount / account_equity * 100.0, 4) if account_equity else None

    return PositionSizeResult(method, round(size_units, 6), round(risk_amount, 2), notes, risk_pct_of_equity)

def build_signal_json(
    symbol: str, decision: SignalDecision, regime: RegimeResult, trend: TrendResult,
    mtf: MTFResult, confluence: ConfluenceResult,
    position_size: Optional["PositionSizeResult"] = None,
) -> Dict[str, Any]:
    """Structured JSON exactly matching Section 18's mandatory field set,
    extended with a few extra fields useful for state-tracking / auditing."""
    result = {
        "symbol": symbol,
        "signal": decision.direction,
        "confidence": decision.confidence,
        "grade": decision.grade,
        "entry": decision.entry,
        "stop_loss": decision.stop_loss,
        "take_profit": [decision.tp1, decision.tp2, decision.tp3],
        "risk_reward": decision.risk_reward,
        "market_regime": regime.market_regime,
        "trend": trend.trend_direction.capitalize(),
        "holding_time": decision.holding_time,
        "timeframe": EXECUTION_TF,
        "higher_timeframe_alignment": mtf.aligned,
        "scores": {
            "trend": round(confluence.category_scores["trend"] * confluence.category_weights["trend"] / 100.0, 2),
            "structure": round(confluence.category_scores["structure"] * confluence.category_weights["structure"] / 100.0, 2),
            "momentum": round(confluence.category_scores["momentum"] * confluence.category_weights["momentum"] / 100.0, 2),
            "liquidity": round(confluence.category_scores["liquidity"] * confluence.category_weights["liquidity"] / 100.0, 2),
            "volume": round(confluence.category_scores["volume"] * confluence.category_weights["volume"] / 100.0, 2),
            "volatility": round(confluence.category_scores["volatility"] * confluence.category_weights["volatility"] / 100.0, 2),
            "risk": round(confluence.category_scores["risk"] * confluence.category_weights["risk"] / 100.0, 2),
        },
        "reasons": decision.reasons[:12] if decision.reasons else [],
        "fired_features": decision.fired_features or [],
        "win_probability": decision.win_probability,
        "engine_name": ENGINE_NAME,
        "engine_version": ENGINE_VERSION,
        "generated_at": _utcnow().isoformat(),
        "exit_model": EXIT_MODEL,
    }
    if position_size is not None:
        result["position_sizing"] = {
            "method": position_size.method,
            "size_units": position_size.position_size_units,
            "risk_amount": position_size.risk_amount,
            "risk_pct_of_equity": position_size.risk_pct_of_equity,
            "notes": position_size.notes,
        }
    return result

def default_state() -> Dict[str, Any]:
    return {
        "schema_version": STATE_SCHEMA_VERSION,
        "engine_name": ENGINE_NAME,
        "engine_version": ENGINE_VERSION,
        "created_at": _utcnow().isoformat(),
        "last_run_at": None,
        "watchlist": list(WATCHLIST),
        "feature_weights": {f: DEFAULT_FEATURE_WEIGHT for f in CANDIDATE_FEATURES},
        "feature_stats": {
            f: {
                "weight": DEFAULT_FEATURE_WEIGHT, "confidence": 0.5, "predictive_score": 0.0,
                "win_rate": None, "expectancy": None, "profit_factor": None,
                "sharpe_contribution": None, "max_drawdown_contribution": None,
                "sample_size": 0, "consecutive_bad_windows": 0, "consecutive_good_windows": 0,
                "disabled": False, "last_adjusted_at": None, "last_adjustment_reason": None,
                # Window gating (v5): a "window" is only counted when resolved
                # trades were added since these were last recorded.
                "last_evaluated_resolved_count": 0, "last_evaluated_resolved_id": None,
                # Consecutive good rolling windows measured by shadow replay
                # while disabled (recovery path independent of live signals).
                "shadow_consecutive_good_windows": 0,
            } for f in CANDIDATE_FEATURES
        },
        "active_signals": {},
        "closed_signals": [],
        "per_asset_stats": {s: {"signals": 0, "wins": 0, "losses": 0} for s in WATCHLIST},
        "per_regime_stats": {r: {"signals": 0, "wins": 0, "losses": 0} for r in REGIMES},
        "daily_stats": {},
        "self_monitoring": {
            "overall_win_rate": None, "rolling_30d_win_rate": None,
            "confidence_calibration": {}, "warnings": [],
        },
        "last_daily_summary_date": None,
        "account_equity_reference": 10000.0,
        "pending_notifications": [],
        # Per-symbol cooldown tracker for watch-tier alerts (Section: watch
        # tier cooldown). Keyed by symbol -> {"last_alert_at_ms": int,
        # "direction": "LONG"/"SHORT"}. Deliberately small/bounded (at most
        # len(WATCHLIST) entries) so it needs no pruning, unlike
        # closed_signals/daily_stats.
        "watch_tier_alerts": {},
        # Compact never-pruned record of every resolved trade (see
        # _archive_sync); the adaptive loops read this, not closed_signals.
        "trade_archive": {"features": list(CANDIDATE_FEATURES), "rows": []},
        # Roll-up of daily_stats days dropped by retention pruning.
        "daily_stats_archive": {"signals": 0, "wins": 0, "losses": 0, "timeouts": 0, "pruned_days": 0},
        "breaker": {"status": "ok", "reason": None, "tripped_at": None, "rebaselined_at": None, "trip_count": 0},
        "starvation": {"last_signal_at": _utcnow().isoformat(), "scans_since_signal": 0,
                       "last_relief_at": None, "relief_count": 0},
    }

class StateStore:
    """Read/write of `state.json` (Section 16). Loaded once at run start,
    mutated in-memory through the run, written back atomically at the end
    (Section 2). Missing/corrupt state falls back to a fresh default rather
    than crashing the run."""

    def __init__(self, path: str = STATE_PATH) -> None:
        self.path = path
        loaded = _safe_load_json(path, None)
        if isinstance(loaded, dict) and loaded.get("schema_version") == STATE_SCHEMA_VERSION:
            self.state = loaded
        elif isinstance(loaded, dict) and isinstance(loaded.get("schema_version"), int) \
                and 4 <= loaded["schema_version"] < STATE_SCHEMA_VERSION:
            # Older compatible schema: migrate in place (idempotent) instead of
            # discarding closed_signals history.
            self.state = loaded
            for line in _migrate_state(self.state):
                log.info(line)
        else:
            if loaded is not None:
                log.warning("state.json schema mismatch or unreadable -- initializing fresh state.")
            self.state = default_state()
        for s in WATCHLIST:
            self.state["per_asset_stats"].setdefault(s, {"signals": 0, "wins": 0, "losses": 0})
        for r in REGIMES:
            self.state["per_regime_stats"].setdefault(r, {"signals": 0, "wins": 0, "losses": 0})
        for f in CANDIDATE_FEATURES:
            self.state["feature_weights"].setdefault(f, DEFAULT_FEATURE_WEIGHT)
            self.state["feature_stats"].setdefault(f, default_state()["feature_stats"][f])
            # Back-fill any new per-feature keys on stats loaded from older files.
            for k, v in default_state()["feature_stats"][f].items():
                self.state["feature_stats"][f].setdefault(k, v)
        self.state.setdefault("watch_tier_alerts", {})
        for k in ("trade_archive", "daily_stats_archive", "breaker", "starvation"):
            self.state.setdefault(k, default_state()[k])

    def save(self) -> None:
        self.state["last_run_at"] = _utcnow().isoformat()
        if not _atomic_write_json(self.path, self.state):
            log.error("Failed to persist state.json -- next run will not see this run's updates.")

def _new_day_bucket() -> Dict[str, Any]:
    return {"signals": 0, "wins": 0, "losses": 0, "rr_list": [],
            "feature_adjustments": [], "feature_adjustments_count": 0}

def _day_bucket(state: Dict[str, Any], day: str) -> Dict[str, Any]:
    bucket = state["daily_stats"].setdefault(day, _new_day_bucket())
    bucket.setdefault("feature_adjustments", [])
    bucket.setdefault("feature_adjustments_count", len(bucket["feature_adjustments"]))
    return bucket

def _record_feature_adjustment(day_bucket: Dict[str, Any], line: str) -> None:
    """Count every adjustment but keep only the last DAILY_FEATURE_ADJ_MAX_LINES
    lines -- the unbounded per-scan list is what bloated daily_stats."""
    day_bucket["feature_adjustments_count"] = day_bucket.get("feature_adjustments_count", 0) + 1
    lines = day_bucket.setdefault("feature_adjustments", [])
    lines.append(line)
    if len(lines) > DAILY_FEATURE_ADJ_MAX_LINES:
        del lines[:len(lines) - DAILY_FEATURE_ADJ_MAX_LINES]

def _parse_iso(value: Optional[str]) -> Optional[datetime]:
    if not value:
        return None
    try:
        dt = datetime.fromisoformat(value)
    except ValueError:
        return None
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)

# Archive row layout: [signal_id, resolved_at, symbol, signal, grade,
# confidence, status, realized_r, win_probability, risk_pct, fired_mask].
def _archive_sync(state: Dict[str, Any]) -> int:
    """Append every resolved closed_signals record not yet archived. The
    archive is compact (~100 B/trade, fired features as a bitmask over the
    stored feature order) and is NEVER pruned, so the adaptive loops
    (feature validator, calibration, drawdown breaker) keep their full
    statistics even though closed_signals is capped at CLOSED_SIGNALS_MAX.
    Idempotent (keyed by signal_id); called centrally before any prune."""
    arch = state.setdefault("trade_archive", {"features": list(CANDIDATE_FEATURES), "rows": []})
    order = arch["features"]
    for f in CANDIDATE_FEATURES:
        if f not in order:
            order.append(f)  # append-only so existing masks keep their meaning
    bit = {f: i for i, f in enumerate(order)}
    seen = {row[0] for row in arch["rows"]}
    added = 0
    for c in state.get("closed_signals", []):
        r = _resolved_pnl_r(c)
        sid = c.get("signal_id")
        if r is None or sid is None or sid in seen:
            continue
        fired = c.get("fired_features") or [f for f in CANDIDATE_FEATURES if _feature_fired(c, f)]
        mask = 0
        for f in fired:
            if f in bit:
                mask |= 1 << bit[f]
        risk_pct = (c.get("position_sizing") or {}).get("risk_pct_of_equity")
        arch["rows"].append([sid, c.get("resolved_at"), c.get("symbol"), c.get("signal"), _record_grade(c),
                             c.get("confidence"), c.get("status"), round(r, 4), c.get("win_probability"),
                             risk_pct, mask])
        seen.add(sid)
        added += 1
    return added

def _resolved_history(state: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Resolved trades (oldest -> newest) rebuilt from the never-pruned
    archive as record-shaped dicts, so every stats helper works unchanged."""
    _archive_sync(state)
    arch = state["trade_archive"]
    order = arch["features"]
    out: List[Dict[str, Any]] = []
    for sid, rat, sym, sig, grade, conf, status, r, wp, rp, mask in arch["rows"]:
        out.append({
            "signal_id": sid, "resolved_at": rat or "", "symbol": sym, "signal": sig, "grade": grade,
            "confidence": conf, "status": status, "realized_r": r, "win_probability": wp,
            "position_sizing": {"risk_pct_of_equity": rp},
            "fired_features": [f for i, f in enumerate(order) if mask >> i & 1],
        })
    return out

def _resolved_pnl_r(record: Dict[str, Any]) -> Optional[float]:
    """R-multiple outcome of a resolved signal record. Prefers the stored
    `realized_r` (set for every TP1/SL/Closed resolution, including the
    partial-exit model and mark-to-market timeouts); falls back to the legacy
    derivation (TP1=+RR, SL=-1R, Closed=timeout_mtm_r) for older records."""
    if record.get("status") not in ("TP1", "SL", "Closed"):
        return None
    if record.get("realized_r") is not None:
        return float(record["realized_r"])
    status = record.get("status")
    rr = record.get("risk_reward")
    if status == "TP1" and rr:
        return float(rr)
    if status == "SL":
        return -1.0
    if status == "Closed" and record.get("timeout_mtm_r") is not None:
        return float(record["timeout_mtm_r"])
    return None

def _resolved_is_win(record: Dict[str, Any]) -> bool:
    """Win == positive realized R (so a profitable timeout/partial counts and
    a Closed trade is no longer silently scored as a loss in win-rate stats)."""
    r = _resolved_pnl_r(record)
    if r is None:
        return record.get("status") == "TP1"
    return r > 0

def _resolved_records(closed: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Resolved trades with a defined R, oldest -> newest."""
    return [c for c in closed if _resolved_pnl_r(c) is not None]

def _record_grade(c: Dict[str, Any]) -> str:
    return c.get("grade") or score_to_grade(float(c.get("confidence", 0) or 0))

def _feature_fired(c: Dict[str, Any], feature: str) -> bool:
    fired = c.get("fired_features")
    if fired:
        return feature in fired
    # Legacy records without fired_features: fall back to reason-text match.
    return any(feature.replace("_", " ") in r.lower() or feature in r.lower() for r in c.get("reasons", []))

def _window_metrics(outcomes: List[float]) -> Tuple[float, float, float]:
    """(win_rate, profit_factor, expectancy) for a list of R outcomes."""
    wins = [o for o in outcomes if o > 0]
    losses = [o for o in outcomes if o <= 0]
    gross_profit = sum(wins)
    gross_loss = abs(sum(losses))
    pf = (gross_profit / gross_loss) if gross_loss > 0 else (float("inf") if gross_profit > 0 else 0.0)
    return len(wins) / len(outcomes), pf, statistics.mean(outcomes)

def _is_underperforming(expectancy: float, profit_factor: float) -> bool:
    return expectancy < 0 or profit_factor < 1.0

def _shadow_good_streak(resolved: List[Dict[str, Any]], feature: str) -> int:
    """Shadow-score a (disabled) feature by replaying the closed-trade
    history: at each trade k, take the trailing FEATURE_ROLLING_WINDOW trades
    ending at k, keep those where the feature fired, and test the good-window
    criteria (n >= MIN_FEATURE_SAMPLE, expectancy >= 0, PF >= 1). Returns the
    number of consecutive good windows ending at the newest trade. Pure
    function of closed_signals, so it needs no live signal flow from the
    feature (disabled features are still recorded in fired_features)."""
    streak = 0
    for k in range(len(resolved) - 1, -1, -1):
        window = resolved[max(0, k + 1 - FEATURE_ROLLING_WINDOW):k + 1]
        outcomes = [_resolved_pnl_r(c) for c in window if _feature_fired(c, feature)]
        if len(outcomes) < MIN_FEATURE_SAMPLE:
            break
        _, pf, exp = _window_metrics(outcomes)
        if _is_underperforming(exp, pf):
            break
        streak += 1
    return streak

def _migrate_v4_to_v5(state: Dict[str, Any]) -> List[str]:
    """v4 -> v5: reset feature weights/disabled flags/window counters that were
    corrupted by per-scan window counting (closed_signals preserved), seed the
    window gate at the current resolved count, back-fill realized_r, and
    compact daily_stats."""
    lines: List[str] = []
    closed = state.get("closed_signals", [])
    resolved = _resolved_records(closed)
    last_id = resolved[-1].get("signal_id") if resolved else None
    now = _utcnow().isoformat()

    state["feature_weights"] = {f: DEFAULT_FEATURE_WEIGHT for f in CANDIDATE_FEATURES}
    stats_all = state.setdefault("feature_stats", {})
    for f in CANDIDATE_FEATURES:
        s = stats_all.setdefault(f, copy.deepcopy(default_state()["feature_stats"][f]))
        s["weight"] = DEFAULT_FEATURE_WEIGHT
        s["disabled"] = False
        s["consecutive_bad_windows"] = 0
        s["consecutive_good_windows"] = 0
        s["last_evaluated_resolved_count"] = len(resolved)
        s["last_evaluated_resolved_id"] = last_id
        s["shadow_consecutive_good_windows"] = 0
        s["last_adjusted_at"] = now
        s["last_adjustment_reason"] = "Reset by schema v5 migration (v4 counters were incremented per scan on a static sample)."
    lines.append(f"[Migrate] feature weights/stats reset; window gate seeded at {len(resolved)} resolved trade(s).")

    backfilled = 0
    for c in closed:
        if c.get("status") in ("TP1", "SL", "Closed") and c.get("realized_r") is None:
            r = _resolved_pnl_r(c)
            if r is not None:
                c["realized_r"] = round(r, 4)
                backfilled += 1
    lines.append(f"[Migrate] realized_r back-filled on {backfilled} closed record(s).")

    compacted = 0
    for day, bucket in state.get("daily_stats", {}).items():
        adj = bucket.get("feature_adjustments")
        if isinstance(adj, list):
            bucket.setdefault("feature_adjustments_count", len(adj))
            if len(adj) > DAILY_FEATURE_ADJ_MAX_LINES:
                bucket["feature_adjustments"] = adj[-DAILY_FEATURE_ADJ_MAX_LINES:]
                compacted += 1
    lines.append(f"[Migrate] daily_stats feature_adjustments compacted on {compacted} day(s).")

    state["schema_version"] = 5
    return lines

def _migrate_v5_to_v6(state: Dict[str, Any]) -> List[str]:
    """v5 -> v6: add the never-pruned trade_archive (back-filled from
    closed_signals), breaker/starvation state, daily_stats_archive."""
    lines: List[str] = []
    state.setdefault("trade_archive", {"features": list(CANDIDATE_FEATURES), "rows": []})
    state.setdefault("daily_stats_archive", {"signals": 0, "wins": 0, "losses": 0, "timeouts": 0, "pruned_days": 0})
    state.setdefault("breaker", {"status": "ok", "reason": None, "tripped_at": None,
                                 "rebaselined_at": None, "trip_count": 0})
    stamps = [c.get("generated_at") for c in state.get("closed_signals", []) if c.get("generated_at")]
    stamps += [r.get("generated_at") for r in state.get("active_signals", {}).values() if r.get("generated_at")]
    state.setdefault("starvation", {"last_signal_at": max(stamps) if stamps else _utcnow().isoformat(),
                                    "scans_since_signal": 0, "last_relief_at": None, "relief_count": 0})
    added = _archive_sync(state)
    lines.append(f"[Migrate] trade_archive back-filled with {added} resolved trade(s).")
    state["schema_version"] = 6
    return lines

def _migrate_state(state: Dict[str, Any]) -> List[str]:
    """Idempotent, version-chained schema migration to STATE_SCHEMA_VERSION
    (each step is guarded by the version stamp, so re-running on migrated
    state is a no-op)."""
    lines: List[str] = []
    version = state.get("schema_version", 0)
    if version < 5:
        lines += _migrate_v4_to_v5(state)
    if state.get("schema_version", 0) < 6:
        lines += _migrate_v5_to_v6(state)
    if version < STATE_SCHEMA_VERSION:
        state["schema_version"] = STATE_SCHEMA_VERSION
        state["engine_version"] = ENGINE_VERSION
    return lines

def update_feature_stats_from_closed_signals(state: Dict[str, Any]) -> List[str]:
    """Evidence-driven feature validation (Section 5 / 5.1) over the rolling
    window of the last FEATURE_ROLLING_WINDOW resolved trades.

    * A "window" is counted only when new resolved trades arrived since the
      feature's last evaluation (`last_evaluated_resolved_count`/`_id` in
      feature_stats) -- re-scanning an unchanged sample never moves counters.
    * No feature is adjusted/disabled with fewer than MIN_FEATURE_SAMPLE
      trades in the window.
    * At most MAX_DISABLED_WEIGHT_SHARE of total feature weight may be
      disabled; excess candidates are ranked by expectancy (worst first).
    * Disabled features are re-enabled only by shadow replay of
      closed_signals (see _shadow_good_streak), restoring to
      DEFAULT_FEATURE_WEIGHT * RESTORE_WEIGHT_FACTOR."""
    log_lines: List[str] = []
    # Read from the never-pruned archive (not closed_signals) so pruning can
    # never shrink the validator's own sample.
    resolved_all = _resolved_history(state)
    if len(resolved_all) < RESEARCH_PARAMS["ablation_min_sample_size"]:
        return log_lines
    resolved_count = len(resolved_all)
    newest_id = resolved_all[-1].get("signal_id") if resolved_all else None
    window = resolved_all[-FEATURE_ROLLING_WINDOW:]
    min_windows = RESEARCH_PARAMS["min_consecutive_windows_for_weight_change"]
    restore_weight = DEFAULT_FEATURE_WEIGHT * RESTORE_WEIGHT_FACTOR
    now = _utcnow().isoformat()

    disable_candidates: List[Tuple[float, str, float, str]] = []  # (expectancy, feature, pf, reason)

    for feature in CANDIDATE_FEATURES:
        stats = state["feature_stats"][feature]
        last_count = stats.get("last_evaluated_resolved_count", 0) or 0
        last_id = stats.get("last_evaluated_resolved_id")
        if resolved_count < last_count:
            # History shrank (e.g. manual edit): re-baseline, count no window.
            stats["last_evaluated_resolved_count"] = resolved_count
            stats["last_evaluated_resolved_id"] = newest_id
            continue
        # newest_id check also covers CLOSED_SIGNALS_MAX pruning, where the
        # count plateaus while new trades keep arriving.
        if resolved_count == last_count and newest_id == last_id:
            continue  # unchanged sample -> not a new window
        stats["last_evaluated_resolved_count"] = resolved_count
        stats["last_evaluated_resolved_id"] = newest_id

        outcomes = [_resolved_pnl_r(c) for c in window if _feature_fired(c, feature)]
        if len(outcomes) >= 10:
            win_rate, profit_factor, expectancy = _window_metrics(outcomes)
            stats["win_rate"] = round(win_rate, 4)
            stats["profit_factor"] = round(profit_factor, 4) if profit_factor != float("inf") else 999.0
            stats["expectancy"] = round(expectancy, 4)
            stats["sample_size"] = len(outcomes)
            sd = statistics.pstdev(outcomes)
            stats["sharpe_contribution"] = round(expectancy / sd, 4) if sd else 0.0
            running = peak = max_dd = 0.0
            for o in outcomes:
                running += o
                peak = max(peak, running)
                max_dd = min(max_dd, running - peak)
            stats["max_drawdown_contribution"] = round(max_dd, 4)
        else:
            stats["sample_size"] = len(outcomes)

        if stats.get("disabled"):
            # Recovery path: shadow-score on the closed-trade history; does not
            # depend on this feature contributing to live signals.
            streak = _shadow_good_streak(resolved_all, feature)
            stats["shadow_consecutive_good_windows"] = streak
            stats["consecutive_good_windows"] = streak
            if streak >= min_windows:
                state["feature_weights"][feature] = restore_weight
                stats["weight"] = restore_weight
                stats["disabled"] = False
                stats["consecutive_bad_windows"] = 0
                stats["consecutive_good_windows"] = 0
                stats["shadow_consecutive_good_windows"] = 0
                reason = (f"Shadow replay passed {streak} consecutive good windows "
                          f"-> restored to weight {restore_weight:.4f}")
                stats["last_adjusted_at"] = now
                stats["last_adjustment_reason"] = reason
                log_lines.append(f"[FeatureValidator] {feature}: {reason}")
            continue

        if len(outcomes) < MIN_FEATURE_SAMPLE:
            continue  # too little evidence to adjust or disable

        win_rate, profit_factor, expectancy = _window_metrics(outcomes)
        old_weight = state["feature_weights"][feature]

        if _is_underperforming(expectancy, profit_factor):
            stats["consecutive_bad_windows"] += 1
            stats["consecutive_good_windows"] = 0
            if stats["consecutive_bad_windows"] >= min_windows:
                severity = min(1.0, abs(expectancy) / 1.0 + (1.0 - min(profit_factor, 1.0)))
                new_weight = max(0.0, old_weight * (1.0 - 0.5 * severity))
                reason = (f"{stats['consecutive_bad_windows']} consecutive underperforming windows "
                          f"(expectancy={expectancy:.3f}R, PF={profit_factor:.2f}, n={len(outcomes)})")
                if new_weight < DISABLE_WEIGHT_EPSILON:
                    # Defer: the disable cap is applied across all candidates below.
                    disable_candidates.append((expectancy, feature, profit_factor, reason))
                    continue
                reason += f" -> weight {old_weight:.4f} -> {new_weight:.4f}"
                state["feature_weights"][feature] = new_weight
                stats["weight"] = new_weight
                stats["last_adjusted_at"] = now
                stats["last_adjustment_reason"] = reason
                log_lines.append(f"[FeatureValidator] {feature}: {reason}")
        else:
            stats["consecutive_good_windows"] += 1
            stats["consecutive_bad_windows"] = 0
            if old_weight < DEFAULT_FEATURE_WEIGHT and stats["consecutive_good_windows"] >= min_windows:
                new_weight = min(DEFAULT_FEATURE_WEIGHT, old_weight * 1.15)
                reason = (f"{stats['consecutive_good_windows']} consecutive good windows -> weight regrowth "
                          f"{old_weight:.4f} -> {new_weight:.4f}")
                state["feature_weights"][feature] = new_weight
                stats["weight"] = new_weight
                stats["last_adjusted_at"] = now
                stats["last_adjustment_reason"] = reason
                log_lines.append(f"[FeatureValidator] {feature}: {reason}")

    # Disable cap: share measured on default-baseline weight (every feature
    # has the same baseline), i.e. max_disabled = floor(share * N features).
    if disable_candidates:
        max_disabled = int(MAX_DISABLED_WEIGHT_SHARE * len(CANDIDATE_FEATURES))
        already = sum(1 for f in CANDIDATE_FEATURES if state["feature_stats"][f].get("disabled"))
        allowed = max(0, max_disabled - already)
        disable_candidates.sort(key=lambda t: t[0])  # worst expectancy first
        for rank, (expectancy, feature, profit_factor, reason) in enumerate(disable_candidates):
            stats = state["feature_stats"][feature]
            old_weight = state["feature_weights"][feature]
            if rank < allowed:
                new_weight = 0.0
                stats["disabled"] = True
                stats["shadow_consecutive_good_windows"] = 0
                reason += f" -> DISABLED (weight {old_weight:.4f} -> 0.0000)"
            else:
                # Cap reached: hold at the active floor rather than disabling.
                new_weight = restore_weight
                reason += (f" -> disable cap {MAX_DISABLED_WEIGHT_SHARE:.0%} reached, held at floor "
                           f"{new_weight:.4f}")
            state["feature_weights"][feature] = new_weight
            stats["weight"] = new_weight
            stats["last_adjusted_at"] = now
            stats["last_adjustment_reason"] = reason
            log_lines.append(f"[FeatureValidator] {feature}: {reason}")
    return log_lines

def run_self_monitoring(state: Dict[str, Any]) -> List[str]:
    """Section 20: continuously evaluate engine health; log warnings and
    record them in state.json, but never silently change trading behavior --
    only FeatureValidator (evidence-driven, logged) adjusts weights."""
    warnings: List[str] = []
    closed = state.get("closed_signals", [])
    # Win == positive realized R (Closed/mark-to-market and partial-exit
    # trades included) so every resolved trade is counted consistently.
    resolved = _resolved_history(state)  # never-pruned archive, not the capped closed_signals
    if resolved:
        wins = sum(1 for c in resolved if _resolved_is_win(c))
        overall_win_rate = wins / len(resolved)
        state["self_monitoring"]["overall_win_rate"] = round(overall_win_rate, 4)

        cutoff = (_utcnow() - timedelta(days=30)).isoformat()
        recent = [c for c in resolved if c.get("resolved_at", "") >= cutoff]
        if recent:
            r_wins = sum(1 for c in recent if _resolved_is_win(c))
            state["self_monitoring"]["rolling_30d_win_rate"] = round(r_wins / len(recent), 4)

        # Per-grade calibration over the last CALIBRATION_ROLLING_WINDOW
        # resolved trades of each grade; feeds _win_probability_estimate.
        calib: Dict[str, Any] = {}
        for grade in ("A+", "A", "B+", "B"):
            bucket = [c for c in resolved if _record_grade(c) == grade][-CALIBRATION_ROLLING_WINDOW:]
            if bucket:
                bw = sum(1 for c in bucket if _resolved_is_win(c)) / len(bucket)
                calib[grade] = {"sample_size": len(bucket), "realized_win_rate": round(bw, 4),
                                "realized_expectancy_r": round(statistics.mean(_resolved_pnl_r(c) for c in bucket), 4)}
                advertised = [c["win_probability"] for c in bucket if c.get("win_probability") is not None]
                if advertised:
                    implied = statistics.mean(advertised)
                    calib[grade]["mean_advertised_probability"] = round(implied, 4)
                    if abs(bw - implied) > CALIBRATION_DRIFT_TOLERANCE and len(bucket) >= CALIBRATION_DRIFT_MIN_SAMPLE:
                        warnings.append(
                            f"Confidence calibration drift for grade {grade}: advertised ~{implied:.0%}, "
                            f"realized {bw:.0%} over last {len(bucket)} signals.")
        state["self_monitoring"]["confidence_calibration"] = calib

        # Health warning is expectancy-based: a fixed win-rate floor ignores the
        # payoff ratio (40% WR is breakeven at 1.5R but a loser at 1R).
        mean_r = statistics.mean(_resolved_pnl_r(c) for c in resolved)
        if mean_r < 0 and len(resolved) >= SELF_MONITOR_MIN_SAMPLE:
            warnings.append(
                f"Expectancy {mean_r:+.2f}R (win rate {overall_win_rate:.0%}) over {len(resolved)} resolved "
                "signals is negative -- recommend feature revalidation and parameter review."
            )

    disabled = [f for f, s in state["feature_stats"].items() if s.get("disabled")]
    if disabled:
        warnings.append(f"Features currently disabled due to sustained underperformance: {', '.join(disabled)}")

    timing = state.get("self_monitoring", {}).get("activation_timing", {})
    immediate = timing.get("immediate_1_bar", 0)
    delayed = timing.get("delayed_gt_1_bar", 0)
    total_activations = immediate + delayed
    # Only meaningful for the retest_limit entry model; under "market" entries
    # are filled immediately by construction and this gate is not used.
    if ENTRY_MODEL != "market" and total_activations >= 20:
        immediate_frac = immediate / total_activations
        state["self_monitoring"]["activation_timing_immediate_pct"] = round(immediate_frac, 4)
        if immediate_frac >= 0.90:
            warnings.append(
                f"'Activated' status is providing little discriminative signal: {immediate_frac:.0%} of "
                f"{total_activations} activations happened within 1 bar of signal generation. Entry is set "
                "to the generation candle's own close, so this is expected, but it means the Activated gate "
                "rarely filters anything in practice."
            )

    state["self_monitoring"]["warnings"] = warnings
    for w in warnings:
        log.warning("[SelfMonitoring] %s", w)
    return warnings

def _clean_label(identifier: str) -> str:
    """No raw underscores in user-facing text (Section 26.2): convert
    internal identifiers to clean Title Case with spaces, e.g.
    'order_block_reject' -> 'Order Block Reject'."""
    return " ".join(word.capitalize() for word in identifier.replace("-", "_").split("_"))

def _fmt_num(x: Optional[float]) -> str:
    if x is None:
        return "-"
    if abs(x) >= 100:
        return f"{x:,.2f}"
    if abs(x) >= 1:
        return f"{x:,.4f}"
    return f"{x:.8f}".rstrip("0").rstrip(".")

_MDV2_RESERVED = set("_*[]()~`>#+-=|{}.!\\")

def _escape_markdown_v2(value: Any) -> str:
    """Escape every MarkdownV2-reserved character in a piece of dynamic,
    plain-text content. Applied to symbol names, reasons, labels, grades,
    and any other value interpolated OUTSIDE a backtick code span -- never
    applied to the literal markdown syntax (*, `, escaped "-" separators)
    the message templates add themselves."""
    return "".join(f"\\{ch}" if ch in _MDV2_RESERVED else ch for ch in str(value))

def _escape_markdown_v2_code(value: Any) -> str:
    """Escape a dynamic value that will sit inside a `backtick code span`.
    Per the MarkdownV2 spec, only backslash and backtick need escaping
    inside a code entity -- other reserved characters (., -, etc., which
    formatted prices/numbers routinely contain) are literal there."""
    s = str(value)
    return s.replace("\\", "\\\\").replace("`", "\\`")

TELEGRAM_MAX_MESSAGE_LEN = 4096

def _truncate_for_telegram(text: str) -> str:
    """M1 fix: Telegram hard-rejects any message body over 4096 chars.
    Truncate defensively with a visible marker rather than silently
    dropping the whole message."""
    if len(text) <= TELEGRAM_MAX_MESSAGE_LEN:
        return text
    marker = "\n\n_\\.\\.\\. truncated \\(message exceeded Telegram's length limit\\)_"
    return text[: TELEGRAM_MAX_MESSAGE_LEN - len(marker)] + marker

class TelegramNotifier:
    """All Telegram dispatch (Section 26). Reads TG_BOT_TOKEN / TG_CHAT_ID
    only from environment (Section 26.1); if either is missing, every method
    here becomes a logged no-op rather than raising, so the scheduled run
    continues in signal-generation-only mode."""

    def __init__(self, bot_token: str = TG_BOT_TOKEN, chat_id: str = TG_CHAT_ID) -> None:
        self.bot_token = bot_token
        self.chat_id = chat_id
        self.enabled = bool(bot_token and chat_id)

    def _api(self, method: str, payload: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        if not self.enabled:
            log.warning("Telegram dispatch skipped (%s) -- credentials not configured.", method)
            return None
        url = f"https://api.telegram.org/bot{self.bot_token}/{method}"
        body = json.dumps(payload).encode("utf-8")
        for attempt in range(3):
            req = urllib.request.Request(url, data=body, headers={"Content-Type": "application/json"}, method="POST")
            try:
                with urllib.request.urlopen(req, timeout=15) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                    if data.get("ok"):
                        log.info("Telegram %s dispatch: sent", method)
                        return data.get("result")
                    params = data.get("parameters") or {}
                    retry_after = params.get("retry_after")
                    if retry_after is not None and attempt < 2:
                        log.warning("Telegram %s soft-failed (rate limited) -- retrying in %ss.", method, retry_after)
                        time.sleep(float(retry_after))
                        continue
                    log.error("Telegram %s dispatch failed: %s", method, data.get("description"))
                    return None
            except urllib.error.HTTPError as e:
                if e.code == 429 or 500 <= e.code < 600:
                    retry_after_hdr = e.headers.get("Retry-After") if e.headers else None
                    try:
                        sleep_s = float(retry_after_hdr) if retry_after_hdr is not None else 0.5 * (2 ** attempt)
                    except (TypeError, ValueError):
                        sleep_s = 0.5 * (2 ** attempt)
                    if attempt == 2:
                        log.error("Telegram %s dispatch failed after retries: HTTP %s", method, e.code)
                        return None
                    time.sleep(sleep_s)
                    continue
                log.error("Telegram %s dispatch failed: HTTP %s", method, e.code)
                return None
            except Exception as e:
                if attempt == 2:
                    log.error("Telegram %s dispatch failed after retries: %s", method, e)
                    return None
                time.sleep(0.5 * (attempt + 1))
        return None

    def send_message(self, text: str, reply_to_message_id: Optional[int] = None) -> Optional[int]:
        text = _truncate_for_telegram(text)
        payload: Dict[str, Any] = {
            "chat_id": self.chat_id, "text": text, "parse_mode": "MarkdownV2",
            "disable_web_page_preview": True,
        }
        if reply_to_message_id is not None:
            payload["reply_to_message_id"] = reply_to_message_id
        result = self._api("sendMessage", payload)
        return result.get("message_id") if result else None

    def send_reaction(self, message_id: int) -> None:
        self._api("setMessageReaction", {
            "chat_id": self.chat_id, "message_id": message_id,
            "reaction": [{"type": "emoji", "emoji": REACTION_EMOJI}],
        })

    def format_signal_message(self, sig: Dict[str, Any]) -> str:
        e = _escape_markdown_v2
        ec = _escape_markdown_v2_code
        direction_emoji = {"LONG": "🟢", "SHORT": "🔴"}.get(sig["signal"], "")
        lines = [
            f"*{e(ENGINE_NAME)} {e(ENGINE_VERSION)}*",
            f"{e(_clean_label(sig['symbol']))}  \\-\\-  {e(sig['signal'])} {direction_emoji}",
            "",
            f"Grade: *{e(sig['grade'])}*   Confidence: *{e(sig['confidence'])}*",
            f"Regime: {e(_clean_label(sig['market_regime']))}   Trend: {e(sig['trend'])}",
            f"Timeframe: {e(sig['timeframe'])}   HTF Aligned: {e('Yes' if sig['higher_timeframe_alignment'] else 'No')}",
            "",
            "Entry:",
            f"`{ec(_fmt_num(sig['entry']))}`",
            "SL:",
            f"`{ec(_fmt_num(sig['stop_loss']))}`",
            "TP1:",
            f"`{ec(_fmt_num(sig['take_profit'][0]))}`",
            "TP2 \\(suggested\\):",
            f"`{ec(_fmt_num(sig['take_profit'][1]))}`",
            "TP3 \\(suggested\\):",
            f"`{ec(_fmt_num(sig['take_profit'][2]))}`",
            "",
            f"Risk/Reward: {e(sig['risk_reward'])}   Expected Hold: {e(sig['holding_time'])}",
        ]
        reasons = sig.get("reasons") or []
        if reasons:
            lines.append("")
            lines.append("Why:")
            for r in reasons[:5]:
                lines.append(f"\\- {e(r)}")
        return "\n".join(lines)

    def dispatch_signal(self, sig: Dict[str, Any]) -> Optional[int]:
        text = self.format_signal_message(sig)
        message_id = self.send_message(text)
        if message_id is not None:
            self.send_reaction(message_id)
        return message_id

    def format_watch_message(self, sig: Dict[str, Any]) -> str:
        """FREQ2: deliberately shorter and visually distinct from
        format_signal_message -- no TP/RR block, since a watch-tier alert
        is not a trade and must never be mistaken for one at a glance.
        Still surfaces price context (Section 19's _entry_engine already
        computes this for every watch-tier candidate): PRISM's entry model
        is market-on-close, so decision.entry *is* the price this would
        trigger at if the composite matures into a real signal -- shown
        here as "Possible entry" rather than as a separate number, since
        the engine doesn't compute a distinct pullback/breakout trigger.
        Also shows the structural invalidation level (protected high/low
        or nearest order block edge) that would become the stop if that
        happens -- labeled "Invalidation" rather than "SL" so it reads as
        a level to watch, not a live order. Reasons list intentionally
        omitted per user preference -- grade/composite/regime/trend plus
        the two price levels are the signal, not the feature checklist."""
        e = _escape_markdown_v2
        ec = _escape_markdown_v2_code
        direction = sig.get("signal")
        invalidation_note = "closes below" if direction == "LONG" else "closes above"
        lines = [
            f"_{e(ENGINE_NAME)} {e(ENGINE_VERSION)} \\-\\- Watch Tier \\(not a signal\\)_",
            f"{e(_clean_label(sig['symbol']))}  \\-\\-  {e(sig['signal'])} bias forming",
            "",
            f"Grade: *{e(sig['grade'])}*   Composite: *{e(sig['confidence'])}*",
            f"Regime: {e(_clean_label(sig['market_regime']))}   Trend: {e(sig['trend'])}",
        ]
        if sig.get("entry") is not None and sig.get("stop_loss") is not None:
            lines += [
                "",
                f"Possible entry: `{ec(_fmt_num(sig['entry']))}`",
                f"Invalidation \\(bias off if price {e(invalidation_note)}\\): "
                f"`{ec(_fmt_num(sig['stop_loss']))}`",
            ]
        return "\n".join(lines)

    def dispatch_watch_tier(self, sig: Dict[str, Any]) -> Optional[int]:
        """FREQ2: fire-and-forget -- no reaction, no reply-based status
        lifecycle (there is no position to track the lifecycle of)."""
        text = self.format_watch_message(sig)
        return self.send_message(text)

    def dispatch_status_update(self, sig_record: Dict[str, Any], status: str) -> bool:
        if status not in SIGNAL_STATUSES:
            log.error("Refusing to dispatch unknown status '%s' -- not in fixed status set.", status)
            return False
        if status not in ("TP1", "SL"):
            return True
        symbol = _escape_markdown_v2(_clean_label(sig_record["symbol"]))
        engine = _escape_markdown_v2(ENGINE_NAME)
        header_map = {
            "TP1": f"{engine} \\-\\- {symbol} TP1 Hit \\(Win\\)",
            "SL": f"{engine} \\-\\- {symbol} Stop Loss Hit \\(Loss\\)",
        }
        text = f"*{header_map[status]}*"
        reply_id = sig_record.get("telegram_message_id")
        message_id = self.send_message(text, reply_to_message_id=reply_id)
        return message_id is not None or not self.enabled


    def dispatch_daily_summary(self, state: Dict[str, Any]) -> None:
        today = _utcnow().strftime("%Y-%m-%d")
        day_stats = state.get("daily_stats", {}).get(today, {})
        total = day_stats.get("signals", 0)
        wins = day_stats.get("wins", 0)
        losses = day_stats.get("losses", 0)
        win_rate = (wins / (wins + losses)) if (wins + losses) else None

        rr_list = day_stats.get("rr_list", [])
        avg_rr = round(statistics.mean(rr_list), 2) if rr_list else None
        gross_profit = sum(r for r in rr_list if r > 0)
        gross_loss = abs(sum(r for r in rr_list if r <= 0))
        profit_factor = round(gross_profit / gross_loss, 2) if gross_loss else (round(gross_profit, 2) if gross_profit else None)

        e = _escape_markdown_v2
        win_rate_str = e(f"{win_rate:.0%}") if win_rate is not None else "\\-"
        profit_factor_str = e(profit_factor) if profit_factor is not None else "\\-"
        avg_rr_str = e(avg_rr) if avg_rr is not None else "\\-"
        lines = [
            f"*{e(ENGINE_NAME)} {e(ENGINE_VERSION)} \\-\\- Daily Summary*",
            f"Date: {e(today)}",
            "",
            f"Total signals: {e(total)}",
            f"Wins: {e(wins)}   Losses: {e(losses)}   Win rate: {win_rate_str}",
            f"Profit factor: {profit_factor_str}",
            f"Avg risk/reward: {avg_rr_str}",
            "",
            "By regime:",
        ]
        for regime, stats in state.get("per_regime_stats", {}).items():
            if stats.get("signals"):
                lines.append(f"\\- {e(_clean_label(regime))}: {e(stats['signals'])} signals, {e(stats['wins'])}W/{e(stats['losses'])}L")
        lines.append("")
        lines.append("By asset:")
        for asset, stats in state.get("per_asset_stats", {}).items():
            if stats.get("signals"):
                lines.append(f"\\- {e(_clean_label(asset))}: {e(stats['signals'])} signals, {e(stats['wins'])}W/{e(stats['losses'])}L")

        calib = state.get("self_monitoring", {}).get("confidence_calibration", {})
        if calib:
            lines.append("")
            lines.append("Confidence calibration:")
            for grade, c in calib.items():
                realized_pct = f"{c['realized_win_rate']:.0%}"
                lines.append(f"\\- {e(grade)}: realized {e(realized_pct)} over {e(c['sample_size'])} signals")

        adjustments = day_stats.get("feature_adjustments", [])
        if adjustments:
            lines.append("")
            lines.append("Feature weight adjustments today:")
            for a in adjustments[:10]:
                lines.append(f"\\- {e(a)}")

        message_id = self.send_message("\n".join(lines))
        if message_id is not None:
            self.send_reaction(message_id)
        state["last_daily_summary_date"] = today

def _max_holding_bars_15m(holding_time_label: str) -> int:
    """Convert an holding-time label into a bar-count on the 15M execution
    timeframe, for the max-holding-time exit rule (Section 17.2)."""
    hours_map = {
        "2-12 hours": 12, "4-18 hours": 18, "6-24 hours": 24, "12-48 hours": 48,
    }
    if holding_time_label not in hours_map:
        log.warning("Unrecognized holding_time label %r -- defaulting max-hold to 24h.", holding_time_label)
    return int(hours_map.get(holding_time_label, 24) * 4)

def monitor_active_signals(state: Dict[str, Any], mtf_features_by_symbol: Dict[str, Dict[str, FeatureSet]],
                            notifier: TelegramNotifier) -> None:
    """Resolve previously-emitted signals still open in state.json against
    freshly-fetched price action (Section 17.2 exit model = full exit at
    TP1; Section 26.3 reply-based status lifecycle). Never places or amends
    an order -- this only updates state.json and posts Telegram replies."""
    active = state.get("active_signals", {})
    today = _utcnow().strftime("%Y-%m-%d")
    day_bucket = _day_bucket(state, today)

    for sig_id, record in list(active.items()):
        symbol = record["symbol"]
        # Max-age resolution (stale-signal fix): a record whose TP1/SL was
        # missed (data gap, symbol unscannable, watermark older than the
        # candle window) used to sit active forever. Past
        # STALE_SIGNAL_MAX_AGE_HOURS it is force-resolved below.
        gen_dt = _parse_iso(record.get("generated_at"))
        stale = gen_dt is not None and (_utcnow() - gen_dt) >= timedelta(hours=STALE_SIGNAL_MAX_AGE_HOURS)
        fs_map = mtf_features_by_symbol.get(symbol)
        if not fs_map or EXECUTION_TF not in fs_map:
            if stale:
                record["status"] = "Cancelled"
                record["resolved_at"] = _utcnow().isoformat()
                record["cancel_reason"] = "stale_no_price_data"
                state["active_signals"].pop(sig_id, None)
                state["closed_signals"].append(record)
                log.warning("Signal %s (%s) stale >%dh with no price data -- cancelled (outcome unknown, "
                            "excluded from stats).", sig_id, symbol, STALE_SIGNAL_MAX_AGE_HOURS)
            continue
        fs = fs_map[EXECUTION_TF]

        watermark = record.get("last_checked_candle_t")
        candles = fs.candles
        if stale and not record.get("stale_replayed") and candles and gen_dt is not None:
            # One-time replay of every cached candle since generation so a
            # missed TP1/SL is still found; partial-exit state is reset so the
            # replay is self-consistent.
            gen_ms = int(gen_dt.timestamp() * 1000)
            new_indices = [i for i, c in enumerate(candles) if c["t"] >= gen_ms] or [len(candles) - 1]
            record["stale_replayed"] = True
            for k in ("partial_taken", "trail_stop", "best_price"):
                record.pop(k, None)
            record["bars_open"] = 0
        elif watermark is None:
            new_indices = [len(candles) - 1] if candles else []
        else:
            new_indices = [i for i, c in enumerate(candles) if c["t"] > watermark]
        if not new_indices:
            continue

        bars_elapsed = len(new_indices)
        bars_since = record.get("bars_open", 0) + bars_elapsed
        record["bars_open"] = bars_since
        record["last_checked_candle_t"] = candles[new_indices[-1]]["t"]

        direction = record["signal"]
        entry, stop, tp1 = record["entry"], record["stop_loss"], record["take_profit"][0]

        if not record.get("activated"):
            touched = False
            bars_to_touch = None
            gapped_side = None  # "SL" or "TP1" -- price reached this zone
                                 # without entry ever printing in-range first
            for i in new_indices:
                if fs.lows[i] <= entry <= fs.highs[i]:
                    touched = True
                    bars_to_touch = bars_since - len(new_indices) + (new_indices.index(i) + 1)
                    break
                # Entry didn't print on this bar -- check whether price
                # already ran through SL or TP without the pending order
                # ever having been in range (e.g. a gap on the bar right
                # after signal creation, since entry == the prior bar's
                # close). Checked only once we know this bar didn't bracket
                # entry: a bar that both brackets entry *and* reaches SL/TP
                # is a genuine fill-then-stop/target case, handled by the
                # normal activated-signal path below on a later run, not by
                # this missed-entry path.
                hit_sl_gap = (direction == "LONG" and fs.lows[i] <= stop) or (direction == "SHORT" and fs.highs[i] >= stop)
                hit_tp1_gap = (direction == "LONG" and fs.highs[i] >= tp1) or (direction == "SHORT" and fs.lows[i] <= tp1)
                if hit_sl_gap or hit_tp1_gap:
                    gapped_side = "SL" if hit_sl_gap else "TP1"
                    break
            if touched:
                record["activated"] = True
                record["bars_to_activate"] = bars_to_touch
                timing = state.setdefault("self_monitoring", {}).setdefault(
                    "activation_timing", {"immediate_1_bar": 0, "delayed_gt_1_bar": 0})
                if bars_to_touch <= 1:
                    timing["immediate_1_bar"] += 1
                else:
                    timing["delayed_gt_1_bar"] += 1
                ok = notifier.dispatch_status_update(record, "Activated")
                if not ok:
                    state.setdefault("pending_notifications", []).append({"signal_id": sig_id, "status": "Activated"})
                log.info("Signal %s (%s) activated (%d bar(s) to touch).", sig_id, symbol, bars_to_touch)
            elif gapped_side is not None:
                # Never filled -- price ran to SL or TP without entry ever
                # printing in-range. Resolved so it doesn't sit "Pending"
                # for the rest of the holding window, but deliberately not
                # a win or a loss: no position was ever actually taken.
                record["status"] = "Cancelled"
                record["resolved_at"] = _utcnow().isoformat()
                record["cancel_reason"] = f"gapped_to_{gapped_side.lower()}_unfilled"
                ok = notifier.dispatch_status_update(record, "Cancelled")
                if not ok:
                    state.setdefault("pending_notifications", []).append({"signal_id": sig_id, "status": "Cancelled"})
                state["active_signals"].pop(sig_id, None)
                state["closed_signals"].append(record)
                log.info("Signal %s (%s) cancelled -- reached %s zone before entry was ever filled.",
                          sig_id, symbol, gapped_side)
            elif stale or bars_since > (min(_max_holding_bars_15m(record.get("holding_time", "6-24 hours")), RETEST_EXPIRY_BARS)
                               if record.get("entry_model") == "retest_limit"
                               else _max_holding_bars_15m(record.get("holding_time", "6-24 hours"))):
                # retest_limit orders expire sooner than the max-hold window.
                record["status"] = "Expired"
                record["resolved_at"] = _utcnow().isoformat()
                ok = notifier.dispatch_status_update(record, "Expired")
                if not ok:
                    state.setdefault("pending_notifications", []).append({"signal_id": sig_id, "status": "Expired"})
                state["active_signals"].pop(sig_id, None)
                state["closed_signals"].append(record)
                log.info("Signal %s (%s) expired unfilled.", sig_id, symbol)
            continue

        model = record.get("exit_model", EXIT_MODEL_FULL)
        is_long = direction == "LONG"
        risk_per_unit = abs(entry - stop)
        resolved_status = None
        realized_r: Optional[float] = None
        exit_price: Optional[float] = None
        max_hold = _max_holding_bars_15m(record.get("holding_time", "6-24 hours"))

        def _signed_r(price: float) -> float:
            return ((price - entry) if is_long else (entry - price)) / risk_per_unit if risk_per_unit > 0 else 0.0

        if model == EXIT_MODEL_PARTIAL and risk_per_unit > 0:
            # Partial at +1R, stop -> breakeven, trail the remainder
            # PARTIAL_TRAIL_R behind the best price; remainder capped at TP3.
            # Intra-bar ordering is conservative: stop is checked before
            # targets, and the bar that triggers the partial does not also
            # test the (new) breakeven stop.
            frac = PARTIAL_AT_1R_FRACTION
            one_r = entry + risk_per_unit if is_long else entry - risk_per_unit
            tp_far = record["take_profit"][2] if len(record["take_profit"]) > 2 and record["take_profit"][2] else None
            for i in new_indices:
                hi, lo = fs.highs[i], fs.lows[i]
                if not record.get("partial_taken"):
                    hit_sl = (lo <= stop) if is_long else (hi >= stop)
                    hit_1r = (hi >= one_r) if is_long else (lo <= one_r)
                    if hit_sl:
                        resolved_status, realized_r, exit_price = "SL", -1.0, stop
                        break
                    if hit_1r:
                        record["partial_taken"] = True
                        record["trail_stop"] = entry
                        record["best_price"] = hi if is_long else lo
                    continue
                trail = record["trail_stop"]
                hit_trail = (lo <= trail) if is_long else (hi >= trail)
                hit_far = tp_far is not None and ((hi >= tp_far) if is_long else (lo <= tp_far))
                if hit_trail or hit_far:
                    exit_price = trail if hit_trail else tp_far  # stop wins ties
                    realized_r = frac * 1.0 + (1.0 - frac) * _signed_r(exit_price)
                    resolved_status = "TP1"
                    break
                best = max(record["best_price"], hi) if is_long else min(record["best_price"], lo)
                record["best_price"] = best
                cand = best - PARTIAL_TRAIL_R * risk_per_unit if is_long else best + PARTIAL_TRAIL_R * risk_per_unit
                record["trail_stop"] = max(trail, cand) if is_long else min(trail, cand)
        else:
            for i in new_indices:
                hit_tp1 = (direction == "LONG" and fs.highs[i] >= tp1) or (direction == "SHORT" and fs.lows[i] <= tp1)
                hit_sl = (direction == "LONG" and fs.lows[i] <= stop) or (direction == "SHORT" and fs.highs[i] >= stop)
                if hit_tp1 and hit_sl:
                    resolved_status = "SL"
                    break
                elif hit_sl:
                    resolved_status = "SL"
                    break
                elif hit_tp1:
                    resolved_status = "TP1"
                    break
            if resolved_status == "SL":
                realized_r, exit_price = -1.0, stop
            elif resolved_status == "TP1":
                exit_price = tp1
                realized_r = float(record.get("risk_reward") or _signed_r(tp1))

        if resolved_status is None and (bars_since > max_hold or stale):
            # Timeout: realized R is marked to market at the last close
            # (vs entry/SL distance), plus any already-banked partial, and is
            # stored on the record so the trade is counted in all stats.
            resolved_status = "Closed"
            exit_price = fs.closes[new_indices[-1]]
            mtm_r = _signed_r(exit_price)
            if record.get("partial_taken"):
                realized_r = PARTIAL_AT_1R_FRACTION * 1.0 + (1.0 - PARTIAL_AT_1R_FRACTION) * mtm_r
            else:
                realized_r = mtm_r
            record["timeout_mtm_r"] = round(mtm_r, 4)  # legacy field, kept for compatibility

        if resolved_status:
            record["status"] = resolved_status
            record["resolved_at"] = _utcnow().isoformat()
            record["realized_r"] = round(realized_r, 4) if realized_r is not None else None
            record["exit_price"] = exit_price
            ok = notifier.dispatch_status_update(record, resolved_status)
            if not ok:
                state.setdefault("pending_notifications", []).append({"signal_id": sig_id, "status": resolved_status})
            state["active_signals"].pop(sig_id, None)
            state["closed_signals"].append(record)

            asset_stats = state["per_asset_stats"].setdefault(symbol, {"signals": 0, "wins": 0, "losses": 0})
            regime_stats = state["per_regime_stats"].setdefault(record.get("market_regime", "Sideways"),
                                                                   {"signals": 0, "wins": 0, "losses": 0})
            trade_risk_pct = (record.get("position_sizing") or {}).get("risk_pct_of_equity")
            if trade_risk_pct is None:
                trade_risk_pct = PRODUCTION_PARAMS["risk_per_trade_pct"]
            day_bucket.setdefault("risk_pct_list", [])
            if resolved_status == "TP1":
                asset_stats["wins"] += 1
                regime_stats["wins"] += 1
                day_bucket["wins"] += 1
            elif resolved_status == "SL":
                asset_stats["losses"] += 1
                regime_stats["losses"] += 1
                day_bucket["losses"] += 1
            elif resolved_status == "Closed":
                asset_stats.setdefault("timeouts", 0)
                asset_stats["timeouts"] += 1
                regime_stats.setdefault("timeouts", 0)
                regime_stats["timeouts"] += 1
                day_bucket.setdefault("timeouts", 0)
                day_bucket["timeouts"] += 1
            day_bucket["rr_list"].append(record["realized_r"])
            day_bucket["risk_pct_list"].append(trade_risk_pct)
            log.info("Signal %s (%s) resolved: %s (realized %.2fR)", sig_id, symbol, resolved_status,
                      record["realized_r"] if record["realized_r"] is not None else 0.0)

def _watch_cooldown_elapsed(state: Dict[str, Any], symbol: str, direction: str, now_ms: int) -> Optional[float]:
    """Hours since the last same-direction watch alert if still inside the
    cooldown (alert should be suppressed), else None."""
    last_alert = state.get("watch_tier_alerts", {}).get(symbol)
    if last_alert is not None and last_alert.get("direction") == direction:
        elapsed_hours = (now_ms - last_alert["last_alert_at_ms"]) / 3_600_000.0
        if elapsed_hours < PRODUCTION_PARAMS["watch_tier_cooldown_hours"]:
            return elapsed_hours
    return None

def scan_symbol(client: HyperliquidClient, cache: CandleCacheStore, state: Dict[str, Any],
                 symbol: str, now_ms: int) -> Tuple[Optional[Dict[str, FeatureSet]], Optional[Dict[str, Any]]]:
    """Full per-symbol pipeline with early exits (Section 22): fetch MTF
    candles -> build shared feature sets -> regime/trend/MTF gate -> if the
    higher-timeframe gate fails, short-circuit before running the remaining,
    more expensive sub-engines."""
    raw = fetch_symbol_mtf(client, cache, symbol, now_ms)
    if raw is None:
        return None, None

    mtf_features: Dict[str, FeatureSet] = {}
    for tf, candles in raw.items():
        fs = build_feature_set(candles)
        if fs is not None:
            mtf_features[tf] = fs
    if EXECUTION_TF not in mtf_features:
        log.error("Insufficient %s data for %s after feature build -- skipping.", EXECUTION_TF, symbol)
        return mtf_features, None

    mtf_trends: Dict[str, Optional[TrendResult]] = {tf: evaluate_trend(fs) for tf, fs in mtf_features.items()}
    mtf = aggregate_mtf(mtf_trends)
    if mtf.veto:
        log.info("%s: MTF veto (%s) -- early exit before remaining sub-engines.", symbol, mtf.veto_reason)
        return mtf_features, None

    fs_15m = mtf_features[EXECUTION_TF]
    regime = classify_regime(fs_15m)
    trend = mtf_trends.get(EXECUTION_TF)
    if regime is None or trend is None:
        log.warning("%s: insufficient data for regime/trend classification -- skipping.", symbol)
        return mtf_features, None
    log.info("%s: regime=%s (%.0f%% confidence)", symbol, regime.market_regime, regime.regime_confidence)

    structure = evaluate_structure(fs_15m)
    smc = evaluate_smc(fs_15m)
    volume = evaluate_volume(fs_15m)
    momentum = evaluate_momentum(fs_15m)
    volatility = evaluate_volatility(fs_15m)
    liquidity = evaluate_liquidity(mtf_features)
    if not all([structure, smc, volume, momentum, volatility, liquidity]):
        log.warning("%s: one or more sub-engines returned no result (insufficient data) -- skipping.", symbol)
        return mtf_features, None

    feature_weights = state.get("feature_weights", {f: DEFAULT_FEATURE_WEIGHT for f in CANDIDATE_FEATURES})
    confluence = score_confluence(trend, structure, smc, volume, momentum, volatility,
                                   liquidity, regime, mtf, feature_weights)

    calibration = None
    calib_by_grade = state.get("self_monitoring", {}).get("confidence_calibration", {})
    projected_grade = score_to_grade(confluence.total_score)
    if projected_grade in calib_by_grade:
        # Passed through even for small samples: _win_probability_estimate
        # shrinks toward the prior by sample size. Sizing (Kelly, off by
        # default) additionally requires CALIBRATION_MIN_SAMPLE below.
        calibration = {
            "observed_win_rate": calib_by_grade[projected_grade]["realized_win_rate"],
            "sample_size": calib_by_grade[projected_grade]["sample_size"],
        }

    decision = build_signal_decision(fs_15m, trend, structure, smc, volume, momentum,
                                      volatility, liquidity, regime, mtf, confluence, calibration)
    if decision.direction not in ("LONG", "SHORT"):
        log.info("%s: score %.1f (%s) -- no trade this run.", symbol, confluence.total_score, decision.grade)
        return mtf_features, None

    if decision.tier == "watch":
        watch_json = build_signal_json(symbol, decision, regime, trend, mtf, confluence, position_size=None)
        watch_json["_tier"] = "watch"

        # Cooldown check (read-only -- safe here on the worker thread, same
        # as the active_signals dedup check below). The actual state *write*
        # (recording that this alert fired) happens back on the main thread
        # in run_scan, once all symbols' results are in, matching the
        # existing read-here/mutate-there split for this function.
        elapsed_hours = _watch_cooldown_elapsed(state, symbol, decision.direction, now_ms)
        if elapsed_hours is not None:
            log.info(
                "%s: WATCH %s suppressed -- %.1fh into a %dh cooldown since the last %s watch alert.",
                symbol, watch_json["signal"], elapsed_hours, PRODUCTION_PARAMS["watch_tier_cooldown_hours"],
                decision.direction,
            )
            return mtf_features, None

        log.info("%s: WATCH %s grade=%s confidence=%.1f (below signal threshold, above watch floor).",
                  symbol, watch_json["signal"], watch_json["grade"], watch_json["confidence"])
        return mtf_features, watch_json

    open_positions = list(state.get("active_signals", {}).values())

    if any(pos.get("symbol") == symbol for pos in open_positions):
        log.info("%s: signal suppressed -- symbol already has an open active signal.", symbol)
        return mtf_features, None

    guardrail_veto = _check_portfolio_guardrails(state, open_positions, include_breaker=False)
    if guardrail_veto:
        log.info("%s: signal vetoed by portfolio guardrail -- %s", symbol, guardrail_veto)
        return mtf_features, None

    # Circuit-breaker dispatch policy is explicit (BREAKER_DISPATCH_MODE), not
    # an implicit silent drop: suppress | watch_only | dispatch.
    breaker_note: Optional[str] = None
    breaker_reason = _breaker_reason(state)
    if breaker_reason:
        if BREAKER_DISPATCH_MODE == "suppress":
            log.info("%s: signal suppressed by tripped breaker -- %s", symbol, breaker_reason)
            return mtf_features, None
        breaker_note = f"BREAKER: {breaker_reason} (dispatch mode: {BREAKER_DISPATCH_MODE})"
        if BREAKER_DISPATCH_MODE == "watch_only":
            watch_json = build_signal_json(symbol, decision, regime, trend, mtf, confluence, position_size=None)
            watch_json["_tier"] = "watch"
            watch_json["reasons"] = [breaker_note] + list(watch_json.get("reasons") or [])
            if _watch_cooldown_elapsed(state, symbol, decision.direction, now_ms) is not None:
                return mtf_features, None
            log.info("%s: breaker tripped -- sending as untracked WATCH alert.", symbol)
            return mtf_features, watch_json
        log.info("%s: breaker tripped -- dispatching and tracking signal anyway (mode=dispatch).", symbol)

    corr_passed, corr_veto = evaluate_correlation_risk_gate(symbol, decision.direction, open_positions, cache)
    if not corr_passed:
        log.info("%s: signal vetoed by correlation risk gate -- %s", symbol, "; ".join(corr_veto))
        return mtf_features, None

    position_size = compute_position_size(
        account_equity=state.get("account_equity_reference", 10000.0),
        entry=decision.entry, stop=decision.stop_loss, atr_v=volatility.atr,
        open_positions=open_positions,
        win_rate=(calibration.get("observed_win_rate")
                  if calibration and calibration.get("sample_size", 0) >= CALIBRATION_MIN_SAMPLE else None),
        avg_rr=decision.risk_reward,
        symbol=symbol, direction=decision.direction, cache=cache,
    )

    sig = build_signal_json(symbol, decision, regime, trend, mtf, confluence, position_size)
    if breaker_note:
        sig["reasons"] = [breaker_note] + list(sig.get("reasons") or [])
    sig["_tier"] = "signal"
    log.info("%s: SIGNAL %s grade=%s confidence=%.1f rr=%s", symbol, sig["signal"], sig["grade"],
              sig["confidence"], sig["risk_reward"])
    return mtf_features, sig

def _retry_pending_notifications(state: Dict[str, Any], notifier: TelegramNotifier) -> None:
    """M2 fix: state.json now distinguishes 'sent' from 'silently never
    sent' via pending_notifications; attempt redelivery each run instead of
    losing failed sends forever."""
    pending = state.get("pending_notifications", [])
    if not pending:
        return
    still_pending: List[Dict[str, Any]] = []
    for item in pending:
        sig_id = item.get("signal_id")
        status = item.get("status")
        record = state.get("active_signals", {}).get(sig_id)
        if record is None:
            record = next((c for c in state.get("closed_signals", []) if c.get("signal_id") == sig_id), None)
        if record is None:
            continue  # record no longer exists; drop the stale retry entry
        if status == "New":
            message_id = notifier.dispatch_signal(record)
            if message_id is not None:
                record["telegram_message_id"] = message_id
            else:
                still_pending.append(item)
            continue
        ok = notifier.dispatch_status_update(record, status)
        if not ok:
            still_pending.append(item)
    state["pending_notifications"] = still_pending

def _prune_state(state: Dict[str, Any]) -> List[str]:
    """Bound state.json's two unbounded-growth collections. Run once per
    scan, after all of this run's bookkeeping has landed in state, so
    nothing this run just wrote gets pruned before it's used.

    closed_signals: a flat list appended to from two separate exit paths
    in monitor_active_signals (resolved via TP1/SL/Closed, and
    expired-unfilled). Trimming it here -- once, centrally -- means both
    paths stay bounded, instead of a per-append-site trim that's easy to
    add at one call site and forget at the other.

    daily_stats: keyed by calendar date, gains one new entry every day
    forever with no cap. Nothing else in the engine reads a day's entry
    after that day is over (daily summary only ever reads `today`), so
    entries older than PRODUCTION_PARAMS['daily_stats_retention_days']
    are pure dead weight and safe to drop.
    """
    log_lines: List[str] = []

    # Archive first: the compact never-pruned archive must hold every resolved
    # trade before the full records are trimmed (adaptive loops read it).
    _archive_sync(state)

    closed = state.get("closed_signals")
    if isinstance(closed, list) and len(closed) > CLOSED_SIGNALS_MAX:
        dropped = len(closed) - CLOSED_SIGNALS_MAX
        state["closed_signals"] = closed[-CLOSED_SIGNALS_MAX:]
        log_lines.append(f"[Prune] closed_signals: dropped {dropped} oldest record(s), kept most recent {CLOSED_SIGNALS_MAX}.")

    daily_stats = state.get("daily_stats")
    if isinstance(daily_stats, dict):
        # Safety net for the feature_adjustments bloat: keep counts, cap lines.
        for bucket in daily_stats.values():
            adj = bucket.get("feature_adjustments")
            if isinstance(adj, list) and len(adj) > DAILY_FEATURE_ADJ_MAX_LINES:
                bucket.setdefault("feature_adjustments_count", len(adj))
                bucket["feature_adjustments"] = adj[-DAILY_FEATURE_ADJ_MAX_LINES:]
        retention_days = PRODUCTION_PARAMS["daily_stats_retention_days"]
        cutoff_date = (_utcnow() - timedelta(days=retention_days)).strftime("%Y-%m-%d")
        stale_days = [d for d in daily_stats if d < cutoff_date]
        if stale_days:
            roll = state.setdefault("daily_stats_archive", {"signals": 0, "wins": 0, "losses": 0,
                                                            "timeouts": 0, "pruned_days": 0})
            for d in stale_days:
                b = daily_stats.pop(d, None) or {}
                # Keep lifetime counts of pruned days (per-day detail is dropped).
                for k in ("signals", "wins", "losses", "timeouts"):
                    roll[k] = roll.get(k, 0) + b.get(k, 0)
                roll["pruned_days"] = roll.get("pruned_days", 0) + 1
            log_lines.append(
                f"[Prune] daily_stats: dropped {len(stale_days)} day(s) older than "
                f"{retention_days}d (before {cutoff_date})."
            )
    return log_lines

def _log_closed_signals_range(state: Dict[str, Any]) -> None:
    """Visibility into how much history CLOSED_SIGNALS_MAX currently
    represents. This cap feeds run_self_monitoring's overall/rolling win
    rate and per-grade confidence_calibration -- which in turn feeds
    _win_probability_estimate's blended probability and, downstream,
    position sizing -- so whether to raise or lower it should be a
    data-backed call, not a guess. Cheap: just scans resolved_at
    timestamps already in memory. Logged every run."""
    closed = state.get("closed_signals", [])
    dates = [c["resolved_at"] for c in closed if c.get("resolved_at")]
    if not dates:
        log.info("closed_signals: %d/%d records on file (no resolved_at timestamps yet).",
                  len(closed), CLOSED_SIGNALS_MAX)
        return
    oldest_s, newest_s = min(dates), max(dates)
    span_note = ""
    try:
        span_days = (datetime.fromisoformat(newest_s) - datetime.fromisoformat(oldest_s)).total_seconds() / 86400.0
        span_note = f" (~{span_days:.0f} days of history)"
    except ValueError:
        pass
    log.info("closed_signals: %d/%d records on file, spanning %s -> %s%s.",
              len(closed), CLOSED_SIGNALS_MAX, oldest_s, newest_s, span_note)

def _starvation_check(state: Dict[str, Any], produced_signal: bool) -> List[str]:
    """Starvation detection + relief. Adaptive weights (disabled/decayed
    features) can leave too little score mass to ever clear the signal
    threshold; with no signals there are no new trades for the validator or
    its shadow replay to learn from. This watchdog is driven only by scan
    count and wall-clock, so it recovers the engine without live signal flow:
    after STARVATION_MIN_HOURS/STARVATION_MIN_SCANS with no signal it
    restores every feature to its default weight (rate-limited by
    STARVATION_RELIEF_COOLDOWN_HOURS). A tripped drawdown breaker has its own
    recovery, so it is reported rather than treated as weight starvation."""
    lines: List[str] = []
    ss = state.setdefault("starvation", {"last_signal_at": _utcnow().isoformat(), "scans_since_signal": 0,
                                         "last_relief_at": None, "relief_count": 0})
    now = _utcnow()
    if produced_signal:
        ss["last_signal_at"] = now.isoformat()
        ss["scans_since_signal"] = 0
        return lines
    ss["scans_since_signal"] = ss.get("scans_since_signal", 0) + 1
    last_signal = _parse_iso(ss.get("last_signal_at")) or now
    if (now - last_signal) < timedelta(hours=STARVATION_MIN_HOURS) or ss["scans_since_signal"] < STARVATION_MIN_SCANS:
        return lines
    last_relief = _parse_iso(ss.get("last_relief_at"))
    if last_relief is not None and (now - last_relief) < timedelta(hours=STARVATION_RELIEF_COOLDOWN_HOURS):
        return lines
    if state.get("breaker", {}).get("status") == "tripped":
        lines.append("[Starvation] no signals but the drawdown breaker is tripped -- breaker recovery applies, "
                     "no weight relief.")
        return lines
    relieved = []
    for f in CANDIDATE_FEATURES:
        stats = state["feature_stats"][f]
        if stats.get("disabled") or state["feature_weights"].get(f, DEFAULT_FEATURE_WEIGHT) < DEFAULT_FEATURE_WEIGHT:
            state["feature_weights"][f] = DEFAULT_FEATURE_WEIGHT
            stats.update(weight=DEFAULT_FEATURE_WEIGHT, disabled=False, consecutive_bad_windows=0,
                         consecutive_good_windows=0, shadow_consecutive_good_windows=0,
                         last_adjusted_at=now.isoformat(),
                         last_adjustment_reason="Starvation relief: weight restored to default.")
            relieved.append(f)
    ss["last_relief_at"] = now.isoformat()
    ss["relief_count"] = ss.get("relief_count", 0) + 1
    if relieved:
        lines.append(f"[Starvation] no signal for {(now - last_signal).total_seconds() / 3600:.0f}h / "
                     f"{ss['scans_since_signal']} scans -- relief: restored {len(relieved)} feature(s) to default weight.")
    else:
        lines.append(f"[Starvation] no signal for {(now - last_signal).total_seconds() / 3600:.0f}h / "
                     f"{ss['scans_since_signal']} scans with default weights -- not adaptation-induced "
                     "(market/threshold driven); nothing to relieve.")
    return lines

def run_scan(client: HyperliquidClient, cache: CandleCacheStore, store: StateStore,
             notifier: TelegramNotifier) -> None:
    state = store.state
    now_ms = int(time.time() * 1000)
    skipped: List[str] = []
    mtf_features_by_symbol: Dict[str, Dict[str, FeatureSet]] = {}
    new_signals: List[Dict[str, Any]] = []
    new_watch_alerts: List[Dict[str, Any]] = []  # FREQ2: informational, never persisted to state

    today = _utcnow().strftime("%Y-%m-%d")
    day_bucket = _day_bucket(state, today)

    _retry_pending_notifications(state, notifier)
    for line in _update_breaker_state(state):
        log.info(line)

    def _scan_one(symbol: str) -> Tuple[str, Optional[Dict[str, FeatureSet]], Optional[Dict[str, Any]]]:
        # Runs on a worker thread. scan_symbol only *reads* state/cache during
        # this phase (state mutation happens below, back on the main thread,
        # once every symbol's result is in) so no lock is needed here beyond
        # the ones already added to CandleCacheStore and the pacer.
        try:
            mtf_features, sig = scan_symbol(client, cache, state, symbol, now_ms)
            return symbol, mtf_features, sig
        except Exception:
            log.exception("Unhandled exception scanning %s -- skipping this asset for this run.", symbol)
            return symbol, None, None

    # Symbols are I/O-bound (waiting on Hyperliquid HTTP calls), so a small
    # thread pool lets that waiting overlap instead of serializing 25 symbols
    # one after another. pool.map still yields results in WATCHLIST order
    # even though the underlying work completes out of order, so downstream
    # bookkeeping (per_asset_stats, log ordering, etc.) is unchanged.
    with ThreadPoolExecutor(max_workers=SCAN_WORKER_THREADS) as pool:
        for symbol, mtf_features, sig in pool.map(_scan_one, WATCHLIST):
            if mtf_features:
                mtf_features_by_symbol[symbol] = mtf_features
            else:
                skipped.append(symbol)
                continue
            if sig:
                if sig.get("_tier") == "watch":
                    new_watch_alerts.append(sig)
                else:
                    new_signals.append(sig)

    log.info("Scan complete: %d/%d assets evaluated, %d skipped, %d signals generated, %d watch-tier alerts.",
              len(WATCHLIST) - len(skipped), len(WATCHLIST), len(skipped), len(new_signals), len(new_watch_alerts))

    monitor_active_signals(state, mtf_features_by_symbol, notifier)

    for sig in new_signals:
        sig.pop("_tier", None)
        message_id = notifier.dispatch_signal(sig)
        sig_id = f"{sig['symbol']}-{int(time.time())}-{random.randint(1000,9999)}"
        record = dict(sig)
        record["signal_id"] = sig_id
        record["telegram_message_id"] = message_id
        record["bars_open"] = 0
        record["entry_model"] = ENTRY_MODEL
        if ENTRY_MODEL == "market":
            # Entry == generation-candle close, i.e. already filled: the old
            # Pending->Activated gate never filtered anything (~90% within one
            # bar), so the record starts live. The watermark is the signal
            # candle so monitoring covers every candle after it (the previous
            # None watermark only examined the single newest candle).
            record["activated"] = True
            record["bars_to_activate"] = 0
            record["status"] = "Activated"
            sig_fs = mtf_features_by_symbol.get(sig["symbol"], {}).get(EXECUTION_TF)
            if sig_fs is not None and sig_fs.candles:
                record["last_checked_candle_t"] = sig_fs.candles[-1]["t"]
        else:
            record["activated"] = False
            record["status"] = "Pending"
        if message_id is None and notifier.enabled:
            state.setdefault("pending_notifications", []).append({"signal_id": sig_id, "status": "New"})
        state["active_signals"][sig_id] = record
        state["per_asset_stats"].setdefault(sig["symbol"], {"signals": 0, "wins": 0, "losses": 0})
        state["per_asset_stats"][sig["symbol"]]["signals"] += 1
        state["per_regime_stats"].setdefault(sig["market_regime"], {"signals": 0, "wins": 0, "losses": 0})
        state["per_regime_stats"][sig["market_regime"]]["signals"] += 1
        day_bucket["signals"] += 1

    for sig in new_watch_alerts:
        sig.pop("_tier", None)
        notifier.dispatch_watch_tier(sig)
        state.setdefault("watch_tier_alerts", {})[sig["symbol"]] = {
            "last_alert_at_ms": now_ms,
            "direction": sig["signal"],
        }

    _archive_sync(state)
    for line in _starvation_check(state, bool(new_signals)):
        log.info(line)
        _record_feature_adjustment(day_bucket, line)

    adjustment_lines = update_feature_stats_from_closed_signals(state)
    for line in adjustment_lines:
        log.info(line)
        _record_feature_adjustment(day_bucket, line)
    run_self_monitoring(state)

    for line in _prune_state(state):
        log.info(line)
    _log_closed_signals_range(state)

    hour = _utcnow().hour
    if hour >= PRODUCTION_PARAMS["daily_summary_hour_utc"] and state.get("last_daily_summary_date") != today:
        notifier.dispatch_daily_summary(state)

def main() -> int:
    parser = argparse.ArgumentParser(description=f"{ENGINE_NAME} {ENGINE_VERSION} signal engine")
    parser.add_argument("--mode", choices=["scan", "validate"], default="scan",
                         help="'scan' runs a live watchlist scan (default). "
                              "'validate' runs offline feature-validation bookkeeping only, "
                              "using RESEARCH_PARAMS (Section 21) -- never affects live weights "
                              "directly, only reports what a scan would currently do with them.")
    args = parser.parse_args()

    start = time.monotonic()
    log.info("=== %s %s run starting (mode=%s, pid=%d) ===", ENGINE_NAME, ENGINE_VERSION, args.mode, os.getpid())
    log.info("Watchlist: %d assets.", len(WATCHLIST))

    # Exclusive, non-blocking run lock (Section 2 fix): a scan can take
    # significantly longer than the 15-min cron/Actions cadence (e.g. one
    # observed run took ~31 min), so without mutual exclusion a fresh
    # invocation can start while the previous one is still running. Both
    # processes then load the same starting state.json, mutate independent
    # in-memory copies, and whichever finishes last silently overwrites the
    # other's saved progress -- state.json/candle_cache.json each look
    # "successfully written" every run yet never actually accumulate
    # anything. Bail out immediately (not an error -- just skip this cycle)
    # rather than let a second run proceed. Do NOT take this same lock again
    # anywhere else (e.g. inside StateStore.save()/CandleCacheStore.save()):
    # flock is per open-file-description, so a second fd on LOCK_PATH from
    # this same process would block on the fd held below for the entire
    # process lifetime and self-deadlock instead of erroring.
    lock_f = open(LOCK_PATH, "a+")
    try:
        fcntl.flock(lock_f.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        log.warning("Another run is already in progress (lock held on %s) -- exiting.", os.path.abspath(LOCK_PATH))
        lock_f.close()
        return 0

    try:
        log.info("Resolved state path: %s (cwd=%s)", os.path.abspath(STATE_PATH), os.getcwd())
        log.info("Resolved candle cache path: %s", os.path.abspath(CANDLE_CACHE_PATH))
        store = StateStore(STATE_PATH)
        cache = CandleCacheStore(CANDLE_CACHE_PATH)
        client = HyperliquidClient(HL_API_URL)
        notifier = TelegramNotifier(TG_BOT_TOKEN, TG_CHAT_ID)

        try:
            if args.mode == "validate":
                scratch_state = copy.deepcopy(store.state)
                lines = update_feature_stats_from_closed_signals(scratch_state)
                for line in lines:
                    log.info(line)
                run_self_monitoring(scratch_state)
            else:
                run_scan(client, cache, store, notifier)
        except Exception:
            log.exception("Unhandled exception at top level of main() -- run aborted, state will still be saved.")
            if args.mode != "validate":
                store.save()
                cache.save()
            return 1

        if args.mode != "validate":
            store.save()
            cache.save()
            for p in (STATE_PATH, CANDLE_CACHE_PATH):
                try:
                    log.info("Persisted %s (%d bytes)", os.path.abspath(p), os.path.getsize(p))
                except OSError:
                    log.error("Post-save check failed -- %s does not exist on disk.", os.path.abspath(p))
        duration = time.monotonic() - start
        log.info("=== %s %s run finished in %.1fs ===", ENGINE_NAME, ENGINE_VERSION, duration)
        return 0
    finally:
        fcntl.flock(lock_f.fileno(), fcntl.LOCK_UN)
        lock_f.close()

if __name__ == "__main__":
    sys.exit(main())
