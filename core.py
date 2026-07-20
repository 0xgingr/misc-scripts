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
ENGINE_VERSION = "1.1.4"

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
    "watch_tier_threshold": 65,
    "mtf_veto_strength_floor": 40.0,
}

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

EXIT_MODEL = "full_exit_at_tp1"
assert EXIT_MODEL == "full_exit_at_tp1"

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
        if last_cached_t + step_ms > now_ms:
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
    """Base estimate from a monotonic, deliberately-conservative mapping of
    composite score -> probability, then nudged by observed confidence
    calibration if state.json has enough history (Section 20: do X%-
    confidence signals actually win ~X% of the time?)."""
    base = 0.35 + (confluence - 50.0) / 100.0 if confluence >= 50 else 0.35
    base = max(0.30, min(0.85, base))
    if feature_calibration and feature_calibration.get("sample_size", 0) >= 20:
        observed = feature_calibration.get("observed_win_rate")
        if observed is not None:
            base = round((base * 0.6 + observed * 0.4), 4)
    return round(base, 4)

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

def _check_portfolio_guardrails(state: Dict[str, Any], open_positions: List[Dict[str, Any]],
                                 p: Dict[str, Any] = PRODUCTION_PARAMS) -> Optional[str]:
    """C1 fix: actually enforce the portfolio guardrails PRODUCTION_PARAMS
    documents as active (max concurrent positions, daily realized-loss
    kill-switch, rolling-drawdown circuit breaker). Returns a veto reason
    string if a signal should be blocked, else None."""
    if len(open_positions) >= p["max_concurrent_positions"]:
        return f"Max concurrent positions reached ({len(open_positions)}/{p['max_concurrent_positions']})."

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

    closed = state.get("closed_signals", [])
    if closed:
        running_pct = 0.0
        peak_pct = 0.0
        for c in closed:
            r = _resolved_pnl_r(c)
            if r is None:
                continue
            trade_risk_pct = (c.get("position_sizing") or {}).get("risk_pct_of_equity")
            if trade_risk_pct is None:
                trade_risk_pct = p["risk_per_trade_pct"]
            running_pct += r * trade_risk_pct
            peak_pct = max(peak_pct, running_pct)
        drawdown_pct = peak_pct - running_pct
        if drawdown_pct >= abs(p["max_drawdown_circuit_breaker_pct"]):
            return (f"Drawdown circuit breaker triggered: {drawdown_pct:.2f}% "
                    f"(limit {p['max_drawdown_circuit_breaker_pct']:.2f}%).")
    return None

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
        "schema_version": 4,
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
    }

class StateStore:
    """Read/write of `state.json` (Section 16). Loaded once at run start,
    mutated in-memory through the run, written back atomically at the end
    (Section 2). Missing/corrupt state falls back to a fresh default rather
    than crashing the run."""

    def __init__(self, path: str = STATE_PATH) -> None:
        self.path = path
        loaded = _safe_load_json(path, None)
        if isinstance(loaded, dict) and loaded.get("schema_version") == default_state()["schema_version"]:
            self.state = loaded
        else:
            if loaded is not None:
                log.warning("state.json schema mismatch or unreadable -- initializing fresh state.")
            self.state = default_state()
        for s in WATCHLIST:
            self.state["per_asset_stats"].setdefault(s, {"signals": 0, "wins": 0, "losses": 0})
        for f in CANDIDATE_FEATURES:
            self.state["feature_weights"].setdefault(f, DEFAULT_FEATURE_WEIGHT)
            self.state["feature_stats"].setdefault(f, default_state()["feature_stats"][f])

    def save(self) -> None:
        self.state["last_run_at"] = _utcnow().isoformat()
        if not _atomic_write_json(self.path, self.state):
            log.error("Failed to persist state.json -- next run will not see this run's updates.")

def _resolved_pnl_r(record: Dict[str, Any]) -> Optional[float]:
    """R-multiple outcome of a resolved signal record (win=+RR at TP1 under
    the declared full-exit-at-TP1 model; loss=-1R; anything else unresolved)."""
    status = record.get("status")
    rr = record.get("risk_reward")
    if status == "TP1" and rr:
        return float(rr)
    if status == "SL":
        return -1.0
    if status == "Closed" and record.get("timeout_mtm_r") is not None:
        return float(record["timeout_mtm_r"])
    return None

def update_feature_stats_from_closed_signals(state: Dict[str, Any]) -> List[str]:
    """Evidence-driven feature validation (Section 5 / 5.1): for every
    feature, look at recently-closed signals whose `reasons` cited that
    feature, compute rolling win rate / expectancy / profit factor, and
    adjust weight proportionally to severity of under/over-performance.
    Weight changes are logged with the evidence behind them (returned as a
    list of human-readable log lines the caller writes at INFO)."""
    log_lines: List[str] = []
    closed = state.get("closed_signals", [])
    if len(closed) < RESEARCH_PARAMS["ablation_min_sample_size"]:
        return log_lines

    for feature in CANDIDATE_FEATURES:
        relevant = [c for c in closed if feature in c.get("fired_features", [])]
        if not relevant:
            relevant = [c for c in closed if not c.get("fired_features") and any(
                feature.replace("_", " ") in r.lower() or feature in r.lower()
                for r in c.get("reasons", []))]
        relevant = relevant[-200:]
        if len(relevant) < 10:
            continue
        outcomes = [_resolved_pnl_r(c) for c in relevant]
        outcomes = [o for o in outcomes if o is not None]
        if len(outcomes) < 10:
            continue
        wins = [o for o in outcomes if o > 0]
        losses = [o for o in outcomes if o <= 0]
        win_rate = len(wins) / len(outcomes)
        gross_profit = sum(wins) if wins else 0.0
        gross_loss = abs(sum(losses)) if losses else 0.0
        profit_factor = (gross_profit / gross_loss) if gross_loss > 0 else (float("inf") if gross_profit > 0 else 0.0)
        expectancy = statistics.mean(outcomes)

        stats = state["feature_stats"][feature]
        stats["win_rate"] = round(win_rate, 4)
        stats["profit_factor"] = round(profit_factor, 4) if profit_factor != float("inf") else 999.0
        stats["expectancy"] = round(expectancy, 4)
        stats["sample_size"] = len(outcomes)
        if len(outcomes) >= 2:
            stats["sharpe_contribution"] = round(expectancy / statistics.pstdev(outcomes), 4) if statistics.pstdev(outcomes) else 0.0
        running = 0.0
        peak = 0.0
        max_dd = 0.0
        for o in outcomes:
            running += o
            peak = max(peak, running)
            max_dd = min(max_dd, running - peak)
        stats["max_drawdown_contribution"] = round(max_dd, 4)

        underperforming = expectancy < 0 or profit_factor < 1.0
        old_weight = state["feature_weights"][feature]

        if underperforming:
            stats["consecutive_bad_windows"] += 1
            stats["consecutive_good_windows"] = 0
            if stats["consecutive_bad_windows"] >= RESEARCH_PARAMS["min_consecutive_windows_for_weight_change"]:
                severity = min(1.0, abs(expectancy) / 1.0 + (1.0 - min(profit_factor, 1.0)))
                new_weight = max(0.0, old_weight * (1.0 - 0.5 * severity))
                if new_weight < 0.01:
                    new_weight = 0.0
                    stats["disabled"] = True
                reason = (f"{stats['consecutive_bad_windows']} consecutive underperforming windows "
                          f"(expectancy={expectancy:.3f}R, PF={profit_factor:.2f}) -> weight {old_weight:.4f} -> {new_weight:.4f}")
                state["feature_weights"][feature] = new_weight
                stats["weight"] = new_weight
                stats["last_adjusted_at"] = _utcnow().isoformat()
                stats["last_adjustment_reason"] = reason
                log_lines.append(f"[FeatureValidator] {feature}: {reason}")
        else:
            stats["consecutive_good_windows"] += 1
            stats["consecutive_bad_windows"] = 0
            if stats["disabled"] and stats["consecutive_good_windows"] >= RESEARCH_PARAMS["min_consecutive_windows_for_weight_change"]:
                new_weight = max(old_weight, DEFAULT_FEATURE_WEIGHT * 0.2)
                stats["disabled"] = False
                reason = (f"Renewed predictive value across {stats['consecutive_good_windows']} windows "
                          f"(expectancy={expectancy:.3f}R, PF={profit_factor:.2f}) -> gradually restored to weight {new_weight:.4f}")
                state["feature_weights"][feature] = new_weight
                stats["weight"] = new_weight
                stats["last_adjusted_at"] = _utcnow().isoformat()
                stats["last_adjustment_reason"] = reason
                log_lines.append(f"[FeatureValidator] {feature}: {reason}")
            elif not stats["disabled"] and old_weight < DEFAULT_FEATURE_WEIGHT and stats["consecutive_good_windows"] >= RESEARCH_PARAMS["min_consecutive_windows_for_weight_change"]:
                new_weight = min(DEFAULT_FEATURE_WEIGHT, old_weight * 1.15)
                reason = (f"{stats['consecutive_good_windows']} consecutive good windows -> weight regrowth "
                          f"{old_weight:.4f} -> {new_weight:.4f}")
                state["feature_weights"][feature] = new_weight
                stats["weight"] = new_weight
                stats["last_adjusted_at"] = _utcnow().isoformat()
                stats["last_adjustment_reason"] = reason
                log_lines.append(f"[FeatureValidator] {feature}: {reason}")
    return log_lines

def run_self_monitoring(state: Dict[str, Any]) -> List[str]:
    """Section 20: continuously evaluate engine health; log warnings and
    record them in state.json, but never silently change trading behavior --
    only FeatureValidator (evidence-driven, logged) adjusts weights."""
    warnings: List[str] = []
    closed = state.get("closed_signals", [])
    resolved = [c for c in closed if c.get("status") in ("TP1", "SL", "Closed")]
    if resolved:
        wins = sum(1 for c in resolved if c["status"] == "TP1")
        overall_win_rate = wins / len(resolved)
        state["self_monitoring"]["overall_win_rate"] = round(overall_win_rate, 4)

        cutoff = (_utcnow() - timedelta(days=30)).isoformat()
        recent = [c for c in resolved if c.get("resolved_at", "") >= cutoff]
        if recent:
            r_wins = sum(1 for c in recent if c["status"] == "TP1")
            state["self_monitoring"]["rolling_30d_win_rate"] = round(r_wins / len(recent), 4)

        calib: Dict[str, Any] = {}
        for grade, lo, hi in (("A+", 95, 100), ("A", 90, 94), ("B+", 85, 89), ("B", 80, 84)):
            bucket = [c for c in resolved if lo <= c.get("confidence", 0) <= hi]
            if bucket:
                bw = sum(1 for c in bucket if c["status"] == "TP1") / len(bucket)
                calib[grade] = {"sample_size": len(bucket), "realized_win_rate": round(bw, 4)}
                implied = lo / 100.0
                if abs(bw - implied) > 0.20 and len(bucket) >= 15:
                    w = (f"Confidence calibration drift for grade {grade}: implied ~{implied:.0%}, "
                         f"realized {bw:.0%} over {len(bucket)} signals.")
                    warnings.append(w)
        state["self_monitoring"]["confidence_calibration"] = calib

        if overall_win_rate < 0.35 and len(resolved) >= 20:
            warnings.append(
                f"Overall win rate {overall_win_rate:.0%} over {len(resolved)} resolved signals is "
                "below a healthy floor -- recommend feature revalidation and parameter review."
            )

    disabled = [f for f, s in state["feature_stats"].items() if s.get("disabled")]
    if disabled:
        warnings.append(f"Features currently disabled due to sustained underperformance: {', '.join(disabled)}")

    timing = state.get("self_monitoring", {}).get("activation_timing", {})
    immediate = timing.get("immediate_1_bar", 0)
    delayed = timing.get("delayed_gt_1_bar", 0)
    total_activations = immediate + delayed
    if total_activations >= 20:
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
        format_signal_message -- no SL/TP/RR block, since a watch-tier alert
        is not a trade and must never be mistaken for one at a glance."""
        e = _escape_markdown_v2
        lines = [
            f"_{e(ENGINE_NAME)} {e(ENGINE_VERSION)} \\-\\- Watch Tier \\(not a signal\\)_",
            f"{e(_clean_label(sig['symbol']))}  \\-\\-  {e(sig['signal'])} bias forming",
            "",
            f"Grade: *{e(sig['grade'])}*   Composite: *{e(sig['confidence'])}*",
            f"Regime: {e(_clean_label(sig['market_regime']))}   Trend: {e(sig['trend'])}",
        ]
        reasons = sig.get("reasons") or []
        if reasons:
            lines.append("")
            lines.append("Why it's on watch:")
            for r in reasons[:4]:
                lines.append(f"\\- {e(r)}")
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
    day_bucket = state["daily_stats"].setdefault(today, {"signals": 0, "wins": 0, "losses": 0, "rr_list": [], "feature_adjustments": []})

    for sig_id, record in list(active.items()):
        symbol = record["symbol"]
        fs_map = mtf_features_by_symbol.get(symbol)
        if not fs_map or EXECUTION_TF not in fs_map:
            continue
        fs = fs_map[EXECUTION_TF]

        watermark = record.get("last_checked_candle_t")
        candles = fs.candles
        if watermark is None:
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
            for i in new_indices:
                if fs.lows[i] <= entry <= fs.highs[i]:
                    touched = True
                    bars_to_touch = bars_since - len(new_indices) + (new_indices.index(i) + 1)
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
            elif bars_since > _max_holding_bars_15m(record.get("holding_time", "6-24 hours")):
                record["status"] = "Expired"
                record["resolved_at"] = _utcnow().isoformat()
                ok = notifier.dispatch_status_update(record, "Expired")
                if not ok:
                    state.setdefault("pending_notifications", []).append({"signal_id": sig_id, "status": "Expired"})
                state["active_signals"].pop(sig_id, None)
                state["closed_signals"].append(record)
                log.info("Signal %s (%s) expired unfilled.", sig_id, symbol)
            continue

        resolved_status = None
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
        if resolved_status is None and bars_since > _max_holding_bars_15m(record.get("holding_time", "6-24 hours")):
            resolved_status = "Closed"

        if resolved_status:
            record["status"] = resolved_status
            record["resolved_at"] = _utcnow().isoformat()
            ok = notifier.dispatch_status_update(record, resolved_status)
            if not ok:
                state.setdefault("pending_notifications", []).append({"signal_id": sig_id, "status": resolved_status})
            state["active_signals"].pop(sig_id, None)
            state["closed_signals"].append(record)
            state["closed_signals"] = state["closed_signals"][-2000:]

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
                day_bucket["rr_list"].append(record.get("risk_reward", 0.0))
                day_bucket["risk_pct_list"].append(trade_risk_pct)
            elif resolved_status == "SL":
                asset_stats["losses"] += 1
                regime_stats["losses"] += 1
                day_bucket["losses"] += 1
                day_bucket["rr_list"].append(-1.0)
                day_bucket["risk_pct_list"].append(trade_risk_pct)
            elif resolved_status == "Closed":
                asset_stats.setdefault("timeouts", 0)
                asset_stats["timeouts"] += 1
                regime_stats.setdefault("timeouts", 0)
                regime_stats["timeouts"] += 1
                day_bucket.setdefault("timeouts", 0)
                day_bucket["timeouts"] += 1
                last_close = fs.closes[new_indices[-1]] if new_indices else entry
                risk_per_unit = abs(entry - stop)
                if risk_per_unit > 0:
                    mtm_r = ((last_close - entry) if direction == "LONG" else (entry - last_close)) / risk_per_unit
                else:
                    mtm_r = 0.0
                record["timeout_mtm_r"] = round(mtm_r, 4)
                day_bucket["rr_list"].append(mtm_r)
                day_bucket["risk_pct_list"].append(trade_risk_pct)
            log.info("Signal %s (%s) resolved: %s", sig_id, symbol, resolved_status)

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
        log.info("%s: WATCH %s grade=%s confidence=%.1f (below signal threshold, above watch floor).",
                  symbol, watch_json["signal"], watch_json["grade"], watch_json["confidence"])
        return mtf_features, watch_json

    open_positions = list(state.get("active_signals", {}).values())

    if any(pos.get("symbol") == symbol for pos in open_positions):
        log.info("%s: signal suppressed -- symbol already has an open active signal.", symbol)
        return mtf_features, None

    guardrail_veto = _check_portfolio_guardrails(state, open_positions)
    if guardrail_veto:
        log.info("%s: signal vetoed by portfolio guardrail -- %s", symbol, guardrail_veto)
        return mtf_features, None

    corr_passed, corr_veto = evaluate_correlation_risk_gate(symbol, decision.direction, open_positions, cache)
    if not corr_passed:
        log.info("%s: signal vetoed by correlation risk gate -- %s", symbol, "; ".join(corr_veto))
        return mtf_features, None

    position_size = compute_position_size(
        account_equity=state.get("account_equity_reference", 10000.0),
        entry=decision.entry, stop=decision.stop_loss, atr_v=volatility.atr,
        open_positions=open_positions,
        win_rate=calibration.get("observed_win_rate") if calibration else None,
        avg_rr=decision.risk_reward,
        symbol=symbol, direction=decision.direction, cache=cache,
    )

    sig = build_signal_json(symbol, decision, regime, trend, mtf, confluence, position_size)
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

def run_scan(client: HyperliquidClient, cache: CandleCacheStore, store: StateStore,
             notifier: TelegramNotifier) -> None:
    state = store.state
    now_ms = int(time.time() * 1000)
    skipped: List[str] = []
    mtf_features_by_symbol: Dict[str, Dict[str, FeatureSet]] = {}
    new_signals: List[Dict[str, Any]] = []
    new_watch_alerts: List[Dict[str, Any]] = []  # FREQ2: informational, never persisted to state

    today = _utcnow().strftime("%Y-%m-%d")
    day_bucket = state["daily_stats"].setdefault(today, {"signals": 0, "wins": 0, "losses": 0, "rr_list": [], "feature_adjustments": []})

    _retry_pending_notifications(state, notifier)

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
        record["activated"] = False
        record["bars_open"] = 0
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

    adjustment_lines = update_feature_stats_from_closed_signals(state)
    for line in adjustment_lines:
        log.info(line)
        day_bucket["feature_adjustments"].append(line)
    run_self_monitoring(state)

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
