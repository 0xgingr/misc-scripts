
from __future__ import annotations

import os
import sys
import json
import math
import time
import fcntl
import logging
import statistics
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone, timedelta
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Optional, Any

import requests

ENGINE_NAME = "VANTAGE ANNEX"
ENGINE_SLUG = "vantage_annex"
__version__ = "2.0.1"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    stream=sys.stdout,
)
log = logging.getLogger(ENGINE_SLUG)


TG_BOT_TOKEN = os.getenv("TG_BOT_TOKEN")
TG_CHAT_ID = os.getenv("TG_CHAT_ID")
if not TG_BOT_TOKEN:
    raise RuntimeError("TG_BOT_TOKEN environment variable is required")
if not TG_CHAT_ID:
    raise RuntimeError("TG_CHAT_ID environment variable is required")

STATE_FILE = os.getenv("STATE_FILE", "state.json")
CANDLE_CACHE_FILE = os.getenv("CANDLE_CACHE_FILE", "candle_cache.json")
SCAN_WORKERS = int(os.getenv("SCAN_WORKERS", "4"))
HL_BASE_URL = "https://api.hyperliquid.xyz/info"

WATCHLIST = [
    "BTCUSDT", "ETHUSDT", "HYPEUSDT", "ZECUSDT", "NEARUSDT",
    "ONDOUSDT", "SUIUSDT", "PENGUUSDT", "BNBUSDT", "SOLUSDT",
    "TRXUSDT", "BCHUSDT", "DOGEUSDT", "ADAUSDT", "DOTUSDT",
    "TAOUSDT", "AVAXUSDT", "LINKUSDT", "AAVEUSDT", "XRPUSDT",
    "XLMUSDT", "UNIUSDT", "LTCUSDT", "APTUSDT", "PENDLEUSDT",
]
MACRO_ASSET = "BTCUSDT"
MAJORS = {"BTCUSDT", "ETHUSDT", "SOLUSDT", "BNBUSDT", "XRPUSDT", "ADAUSDT", "DOGEUSDT"}

TF_HTF_SWING, TF_MID_SWING, TF_LTF_SWING = "1d", "4h", "1h"
TF_HTF_INTRADAY, TF_MID_INTRADAY, TF_LTF_INTRADAY = "4h", "1h", "15m"
ALL_TFS = ["1d", "4h", "1h", "15m"]
TF_BARS = {"1d": 260, "4h": 320, "1h": 320, "15m": 400}
SCAN_INTERVAL_MIN = 15

EMA_FAST, EMA_SLOW, EMA_TREND = 21, 50, 200
RSI_LEN, ATR_LEN, ADX_LEN, BB_LEN = 14, 14, 14, 20

MAX_CONCURRENT_ACTIVE_SIGNALS = int(os.getenv("MAX_CONCURRENT_ACTIVE_SIGNALS", "8"))
MAX_CORRELATED_CONCURRENT = 1

MIN_SAMPLE_SIZE = int(os.getenv("MIN_SAMPLE_SIZE", "20"))
MIN_SAMPLE_SIZE_CATEGORY = int(os.getenv("MIN_SAMPLE_SIZE_CATEGORY", "12"))
TIER2_RETENTION_DAYS = 15

CIRCUIT_BREAKER_WINDOW = 30
CIRCUIT_BREAKER_WIN_RATE_DROP = 0.20
CIRCUIT_BREAKER_PF_DROP_FRAC = 0.25

RR_MIN_GATE = 1.5

RR_TP1_FLOOR = 2.0
RR_TP1_CEIL_SOFT = 3.5

MIN_MOVE_PCT_TP1 = 0.012
MIN_MOVE_PCT_TP2 = 0.020

MIN_MOVE_ATR_TP1 = 0.5
MIN_MOVE_ATR_TP2 = 0.8

ENTRY_MIN_DIST_ATR_INTRADAY = 0.15
ENTRY_MIN_DIST_ATR_SWING = 0.25
ENTRY_MAX_PENDING_ATR_INTRADAY = 2.5
ENTRY_MAX_PENDING_ATR_SWING = 4.0

MAX_MOVE_PCT_SL_INTRADAY = 0.020
MAX_MOVE_PCT_SL_SWING = 0.045
MAX_MOVE_PCT_TP1_INTRADAY = 0.035
MAX_MOVE_PCT_TP1_SWING = 0.080
MAX_MOVE_PCT_TP2_INTRADAY = 0.060
MAX_MOVE_PCT_TP2_SWING = 0.140

MAX_MOVE_ATR_SL_INTRADAY = 3.0
MAX_MOVE_ATR_SL_SWING = 4.5
MAX_MOVE_ATR_TP1_INTRADAY = 5.0
MAX_MOVE_ATR_TP1_SWING = 7.0
MAX_MOVE_ATR_TP2_INTRADAY = 8.0
MAX_MOVE_ATR_TP2_SWING = 12.0


def _atr_pct_bound(entry: float, atr_val: float, atr_mult: float, pct: float) -> float:
    """min(ATR-relative distance, flat-% distance). Used both as a ceiling
    (MAX_MOVE_*: reject if actual distance > this) and as a floor
    (MIN_MOVE_*: reject if actual distance < this) -- in both roles the
    flat % is the outer backstop and the ATR term is what actually scales
    the bound to this asset's current regime. Falls back to the flat %
    alone if ATR is unavailable (e.g. too little candle history)."""
    pct_cap = entry * pct
    if atr_val <= 1e-12:
        return pct_cap
    return min(atr_val * atr_mult, pct_cap)

ASSUMED_LEVERAGE = float(os.getenv("ASSUMED_LEVERAGE", "10"))
MAINTENANCE_MARGIN_RATE = 0.005

SCALP_PRONE_ENGINES = {"mean_reversion", "range_trading"}
SCALP_PRONE_REGIMES = {"low_volatility", "consolidation"}

PENDING_ENTRY_EXPIRY_BARS = {
    "15m": 8,
    "1h": 12,
}

NEWS_BLACKOUT_MIN_BEFORE = 30
NEWS_BLACKOUT_MIN_AFTER = 30

EMOJI_WIN = "🏆"
EMOJI_LOSS = "😭"
EMOJI_EXPIRED = "🤷"
EMOJI_CIRCUIT_BREAKER = "🤯"
EMOJI_RECOVERED = "👏"
EMOJI_CANCELLED = "🚫"
REACTION_IMAGE_PATH = os.getenv("REACTION_IMAGE_PATH", "reaction.jpg")

SPECIALIST_ENGINES = [
    "smc", "trend_continuation", "breakout", "pullback", "liquidity_sweep",
    "order_block", "breaker_block", "fair_value_gap", "momentum", "reversal",
    "mean_reversion", "range_trading", "volatility_expansion",
]

# BUGFIX (v2.0.1): RegimeVector.label() can return "choppy", but no engine
# listed it as a fit regime -- composite_score()'s fit_ok gate is a hard
# reject, so every candidate from every engine was killed at the eligibility
# stage for as long as the macro regime (computed off BTC's 1D candles, so
# it can hold for many consecutive days) read as choppy. That's a complete,
# silent, deterministic signal blackout, not just a low pass-rate filter.
# Fixed by adding "choppy" to the three engines already designed for
# range-bound/no-trend conditions (liquidity_sweep, mean_reversion,
# range_trading) -- every trend/breakout/momentum engine is still correctly
# vetoed in choppy conditions, unchanged from before.
#
# Also note: "reversal" is listed below by 5 engines (smc, liquidity_sweep,
# order_block, breaker_block, reversal) but label() has no branch that ever
# returns "reversal" -- it's currently dead/unreachable. Those engines still
# fit via their other listed regimes so this doesn't block them outright,
# but if a real reversal-regime detector was intended, it never got wired
# into RegimeVector.label(). Left as-is pending a decision on that.
ENGINE_REGIME_FIT = {
    "smc": {"trending", "expansion", "reversal"},
    "trend_continuation": {"trending", "expansion"},
    "breakout": {"expansion", "trending"},
    "pullback": {"trending"},
    "liquidity_sweep": {"reversal", "ranging", "consolidation", "choppy"},
    "order_block": {"trending", "reversal"},
    "breaker_block": {"reversal", "trending"},
    "fair_value_gap": {"trending", "expansion"},
    "momentum": {"trending", "expansion", "high_volatility"},
    "reversal": {"reversal", "ranging"},
    "mean_reversion": {"ranging", "consolidation", "low_volatility", "choppy"},
    "range_trading": {"ranging", "consolidation", "choppy"},
    "volatility_expansion": {"expansion", "high_volatility"},
}

FAILURE_CATEGORIES = [
    "regime_mismatch", "structural_invalidation_too_tight", "chased_swept_liquidity",
    "mtf_conflict_ignored", "sfp_mss_sequence_violated", "correct_read_poor_rr",
    "confidence_miscalibration", "filter_over_permissiveness", "genuine_variance",
]


def _default_engine_weight_state() -> dict:
    return {name: 1.0 for name in SPECIALIST_ENGINES}


def _default_regime_fit_state() -> dict:
    return {name: 1.0 for name in SPECIALIST_ENGINES}


def _default_segment_stats() -> dict:
    return {"n": 0, "wins": 0, "losses": 0, "sum_r": 0.0, "sum_hold_min": 0.0}


def default_state() -> dict:
    return {
        "schema_version": 1,
        "tier1": {
            "engine_weights": _default_engine_weight_state(),
            "regime_fit_weights": {name: {} for name in SPECIALIST_ENGINES},
            "confidence_calibration": {name: {} for name in SPECIALIST_ENGINES},
            "sl_buffer_percentile": {},
            "liquidity_sanity_threshold": {name: 0.5 for name in SPECIALIST_ENGINES},
            "sfp_mss_strictness": {name: 0.5 for name in SPECIALIST_ENGINES},
            "mtf_alignment_weight": 0.15,
            "session_open_weight": 0.05,
            "segments": {"asset": {}, "regime": {}, "timeframe": {}, "engine": {}},
            "session_anchor_bucket": {"anchored": _default_segment_stats(),
                                       "non_anchored": _default_segment_stats()},
            "forensic_categories": {c: {"count": 0, "recent_trend": []} for c in FAILURE_CATEGORIES},
            "baseline": {"win_rate": None, "profit_factor": None, "avg_rr": None, "n": 0},
            "circuit_breaker": {"active": False, "since": None, "reason": None},
            "totals": {"signals": 0, "wins": 0, "losses": 0, "expired": 0,
                       "sum_r": 0.0, "sum_hold_min": 0.0},
            "filter_funnel": {},
        },
        "tier2": {
            "trade_log": [],
            "active_signals": [],
        },
    }


class StateStore:
    """Loads/saves state.json with an advisory file lock and deep-merged defaults
    so new fields introduced by a future version never crash an older state file."""

    def __init__(self, path: str):
        self.path = Path(path)
        self._fh = None

    def load(self) -> dict:
        self._fh = open(self.path, "a+")
        fcntl.flock(self._fh.fileno(), fcntl.LOCK_EX)
        self._fh.seek(0)
        raw = self._fh.read()
        if raw.strip():
            try:
                loaded = json.loads(raw)
            except json.JSONDecodeError:
                log.error("state.json corrupt -- starting from defaults")
                loaded = {}
        else:
            loaded = {}
        state = default_state()
        _deep_merge_defaults(loaded, state)
        return state

    def save(self, state: dict) -> None:
        tmp = self.path.with_suffix(".tmp")
        with open(tmp, "w") as f:
            json.dump(state, f, indent=2, sort_keys=True, default=str)
        os.replace(tmp, self.path)
        if self._fh:
            fcntl.flock(self._fh.fileno(), fcntl.LOCK_UN)
            self._fh.close()
            self._fh = None

    def prune_tier2(self, state: dict) -> None:
        cutoff = datetime.now(timezone.utc) - timedelta(days=TIER2_RETENTION_DAYS)
        log_list = state["tier2"]["trade_log"]
        kept = []
        for rec in log_list:
            try:
                ts = datetime.fromisoformat(rec.get("resolved_at", ""))
            except (ValueError, TypeError):
                kept.append(rec)
                continue
            if ts >= cutoff:
                kept.append(rec)
        state["tier2"]["trade_log"] = kept


class CandleCacheStore:
    """Persisted candle cache keyed by symbol+timeframe -- shared by both
    combos and every specialist engine so identical data is fetched once."""

    def __init__(self, path: str):
        self.path = Path(path)

    def load(self) -> dict:
        if not self.path.exists():
            return {}
        try:
            with open(self.path) as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            log.warning("candle cache unreadable -- starting empty")
            return {}

    def save(self, cache: dict) -> None:
        tmp = self.path.with_suffix(".tmp")
        with open(tmp, "w") as f:
            json.dump(cache, f)
        os.replace(tmp, self.path)


def _deep_merge_defaults(loaded: dict, defaults: dict) -> None:
    """Fill any key missing from `loaded` with the value from `defaults`,
    recursively, mutating `defaults` in place to become the merged result
    is wrong -- instead mutate `loaded` in place and let caller use it.
    Simpler: merge defaults INTO loaded so loaded wins wherever present."""
    for k, v in defaults.items():
        if k not in loaded:
            loaded[k] = v
        elif isinstance(v, dict) and isinstance(loaded.get(k), dict):
            _deep_merge_defaults(loaded[k], v)
    defaults.clear()
    defaults.update(loaded)


def clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))


def bounded_update(current: float, target: float, lo: float, hi: float,
                    max_step_frac: float = 0.15) -> float:
    """Sec 5 mandatory bounded + dampened parameter update: exponential
    smoothing toward `target`, capped so no single run can move `current`
    by more than `max_step_frac` of the (hi-lo) range, then clamped into
    [lo, hi]. This is the single choke point every adaptive parameter update
    in this file passes through."""
    span = hi - lo
    if span <= 0:
        return clamp(target, lo, hi)
    max_step = span * max_step_frac
    delta = clamp(target - current, -max_step, max_step)
    return clamp(current + delta, lo, hi)


class _WeightedRateLimiter:
    """Hyperliquid's documented weight budget is 1200/min per IP. Track a
    rolling window of consumed weight and sleep only when actually needed."""

    def __init__(self, budget_per_min: int = 1150):
        self.budget = budget_per_min
        self._events: list[tuple[float, int]] = []

    def acquire(self, weight: int = 20) -> None:
        now = time.monotonic()
        self._events = [(t, w) for t, w in self._events if now - t < 60]
        used = sum(w for _, w in self._events)
        if used + weight > self.budget:
            sleep_for = 60 - (now - self._events[0][0]) + 0.05
            if sleep_for > 0:
                time.sleep(sleep_for)
            now = time.monotonic()
            self._events = [(t, w) for t, w in self._events if now - t < 60]
        self._events.append((now, weight))


class HyperliquidClient:
    def __init__(self, cache: Optional[dict] = None):
        self._limiter = _WeightedRateLimiter()
        self._session = requests.Session()
        self.cache = cache if cache is not None else {}

    def _post(self, payload: dict, weight: int = 20, retries: int = 4) -> Any:
        self._limiter.acquire(weight)
        backoff = 1.0
        last_exc = None
        for attempt in range(retries):
            try:
                resp = self._session.post(HL_BASE_URL, json=payload, timeout=15)
                if resp.status_code == 429:
                    time.sleep(backoff)
                    backoff *= 2
                    continue
                resp.raise_for_status()
                return resp.json()
            except (requests.RequestException, ValueError) as exc:
                last_exc = exc
                time.sleep(backoff)
                backoff *= 2
        log.error("HL request failed after retries: %s", last_exc)
        return None

    def candles(self, symbol: str, interval: str, n_bars: int) -> list[dict]:
        """Delta-fetch: only pull candles newer than what's cached, append,
        and prune to the rolling lookback -- never re-download full history
        on a warm cache. Falls back to a full fetch on any cache problem."""
        coin = symbol.replace("USDT", "").replace("USD", "")
        cache_key = f"{symbol}:{interval}"
        entry = self.cache.get(cache_key)
        interval_ms = _interval_to_ms(interval)
        now_ms = int(time.time() * 1000)

        start_ms = now_ms - interval_ms * (n_bars + 2)
        if entry and isinstance(entry.get("candles"), list) and entry["candles"]:
            try:
                last_ts = entry["candles"][-1]["t"]
                if now_ms - last_ts < interval_ms * (n_bars * 3):
                    start_ms = last_ts - interval_ms
            except (KeyError, IndexError, TypeError):
                entry = None

        payload = {
            "type": "candleSnapshot",
            "req": {"coin": coin, "interval": interval, "startTime": start_ms, "endTime": now_ms},
        }
        raw = self._post(payload, weight=20)
        fresh = []
        if raw:
            for c in raw:
                try:
                    fresh.append({
                        "t": int(c["t"]), "o": float(c["o"]), "h": float(c["h"]),
                        "l": float(c["l"]), "c": float(c["c"]), "v": float(c.get("v", 0.0)),
                    })
                except (KeyError, TypeError, ValueError):
                    continue

        merged: dict[int, dict] = {}
        if entry and isinstance(entry.get("candles"), list):
            for c in entry["candles"]:
                merged[c["t"]] = c
        for c in fresh:
            merged[c["t"]] = c

        if not merged:
            log.warning("no candle data for %s %s -- graceful skip", symbol, interval)
            return []

        ordered = sorted(merged.values(), key=lambda c: c["t"])
        keep = ordered[-(n_bars + 5):]
        self.cache[cache_key] = {"candles": keep, "updated_at": now_ms}

        if keep and keep[-1]["t"] + interval_ms > now_ms:
            closed = keep[:-1]
        else:
            closed = keep
        return closed[-n_bars:]

    def mark_prices(self) -> dict[str, float]:
        raw = self._post({"type": "allMids"}, weight=2)
        out: dict[str, float] = {}
        if not raw:
            return out
        for coin, px in raw.items():
            sym = coin + "USDT"
            if sym in WATCHLIST:
                try:
                    out[sym] = float(px)
                except (TypeError, ValueError):
                    continue
        return out


def _interval_to_ms(interval: str) -> int:
    unit = interval[-1]
    n = int(interval[:-1])
    mult = {"m": 60_000, "h": 3_600_000, "d": 86_400_000}[unit]
    return n * mult


def ema(values: list[float], length: int) -> list[float]:
    if not values:
        return []
    k = 2.0 / (length + 1)
    out = [values[0]]
    for v in values[1:]:
        out.append(v * k + out[-1] * (1 - k))
    return out


def rsi(closes: list[float], length: int = RSI_LEN) -> list[float]:
    if len(closes) < length + 1:
        return [50.0] * len(closes)
    gains, losses = [0.0], [0.0]
    for i in range(1, len(closes)):
        d = closes[i] - closes[i - 1]
        gains.append(max(d, 0.0))
        losses.append(max(-d, 0.0))
    avg_g = sum(gains[1:length + 1]) / length
    avg_l = sum(losses[1:length + 1]) / length
    out = [50.0] * length
    for i in range(length, len(closes)):
        avg_g = (avg_g * (length - 1) + gains[i]) / length
        avg_l = (avg_l * (length - 1) + losses[i]) / length
        rs = avg_g / avg_l if avg_l > 1e-12 else 999.0
        out.append(100 - 100 / (1 + rs))
    return out


def atr(candles: list[dict], length: int = ATR_LEN) -> list[float]:
    if len(candles) < 2:
        return [0.0] * len(candles)
    trs = [candles[0]["h"] - candles[0]["l"]]
    for i in range(1, len(candles)):
        h, l, pc = candles[i]["h"], candles[i]["l"], candles[i - 1]["c"]
        trs.append(max(h - l, abs(h - pc), abs(l - pc)))
    out = [trs[0]]
    for i in range(1, len(trs)):
        n = min(i + 1, length)
        out.append((out[-1] * (n - 1) + trs[i]) / n)
    return out


def adx(candles: list[dict], length: int = ADX_LEN) -> list[float]:
    n = len(candles)
    if n < length + 2:
        return [15.0] * n

    def _smooth(vals: list[float]) -> list[float]:
        out = [sum(vals[:length])]
        for v in vals[length:]:
            out.append(out[-1] - out[-1] / length + v)
        return out

    plus_dm, minus_dm, trs = [], [], []
    for i in range(1, n):
        up = candles[i]["h"] - candles[i - 1]["h"]
        dn = candles[i - 1]["l"] - candles[i]["l"]
        plus_dm.append(up if (up > dn and up > 0) else 0.0)
        minus_dm.append(dn if (dn > up and dn > 0) else 0.0)
        h, l, pc = candles[i]["h"], candles[i]["l"], candles[i - 1]["c"]
        trs.append(max(h - l, abs(h - pc), abs(l - pc)))

    s_tr = _smooth(trs)
    s_pdm = _smooth(plus_dm)
    s_mdm = _smooth(minus_dm)
    out = [15.0] * (n - len(s_tr) + length)
    dxs = []
    for tr_s, pdm_s, mdm_s in zip(s_tr, s_pdm, s_mdm):
        if tr_s <= 1e-12:
            dxs.append(0.0)
            continue
        pdi = 100 * pdm_s / tr_s
        mdi = 100 * mdm_s / tr_s
        denom = pdi + mdi
        dxs.append(100 * abs(pdi - mdi) / denom if denom > 1e-12 else 0.0)
    if dxs:
        adx_val = sum(dxs[:length]) / min(length, len(dxs))
        adx_series = [adx_val]
        for dx in dxs[length:]:
            adx_val = (adx_val * (length - 1) + dx) / length
            adx_series.append(adx_val)
        out.extend(adx_series)
    while len(out) < n:
        out.append(out[-1] if out else 15.0)
    return out[:n]


def bollinger_width_percentile(closes: list[float], length: int = BB_LEN,
                                lookback: int = 100) -> float:
    """Current BB width expressed as a percentile of its own recent history --
    a volatility percentile that stays meaningful across assets (Sec 6)."""
    if len(closes) < length + 5:
        return 50.0
    widths = []
    for i in range(length, len(closes) + 1):
        window = closes[i - length:i]
        mean = sum(window) / length
        sd = statistics.pstdev(window) if length > 1 else 0.0
        widths.append((4 * sd / mean) if mean > 1e-12 else 0.0)
    if not widths:
        return 50.0
    recent = widths[-lookback:]
    current = recent[-1]
    rank = sum(1 for w in recent if w <= current)
    return 100.0 * rank / len(recent)


def realized_vol_percentile(candles: list[dict], length: int = ATR_LEN,
                             lookback: int = 100) -> float:
    """ATR expressed as a percentile of its own recent distribution -- feeds
    the Regime Vector's volatility-percentile component (Sec 6)."""
    series = atr(candles, length)
    if len(series) < 10:
        return 50.0
    recent = series[-lookback:]
    current = recent[-1]
    rank = sum(1 for v in recent if v <= current)
    return 100.0 * rank / len(recent)


def noise_index(candles: list[dict], lookback: int = 30) -> float:
    """How choppy/whipsaw-prone recent action has been, independent of raw
    volatility: ratio of summed wick range to net directional displacement
    over the window. High = noisy/choppy, low = clean directional movement."""
    window = candles[-lookback:]
    if len(window) < 5:
        return 0.5
    total_range = sum(c["h"] - c["l"] for c in window)
    net_move = abs(window[-1]["c"] - window[0]["c"])
    if total_range <= 1e-12:
        return 0.5
    directionality = net_move / total_range
    return clamp(1.0 - directionality, 0.0, 1.0)


@dataclass
class Pivot:
    idx: int
    kind: str
    price: float
    t: int


def find_pivots(candles: list[dict], left: int = 2, right: int = 2) -> list[Pivot]:
    """Fractal swing points. All candles passed in are already closed (the
    caller never includes the still-forming bar), so this never repaints."""
    out = []
    n = len(candles)
    for i in range(left, n - right):
        h = candles[i]["h"]
        l = candles[i]["l"]
        if all(h >= candles[j]["h"] for j in range(i - left, i + right + 1) if j != i):
            out.append(Pivot(i, "high", h, candles[i]["t"]))
        if all(l <= candles[j]["l"] for j in range(i - left, i + right + 1) if j != i):
            out.append(Pivot(i, "low", l, candles[i]["t"]))
    return out


def detect_bos_choch(candles: list[dict], pivots: list[Pivot]) -> dict:
    """Break of Structure / Change of Character off the most recent confirmed
    swing sequence, using only closed candle closes."""
    highs = [p for p in pivots if p.kind == "high"]
    lows = [p for p in pivots if p.kind == "low"]
    if not highs or not lows:
        return {"event": None, "bias": "neutral"}
    last_high, last_low = highs[-1], lows[-1]
    last_close = candles[-1]["c"]
    if last_close > last_high.price:
        event = "choch_bull" if last_high.idx > last_low.idx else "bos_bull"
        return {"event": event, "bias": "bullish", "level": last_high.price, "at_idx": len(candles) - 1}
    if last_close < last_low.price:
        event = "choch_bear" if last_low.idx > last_high.idx else "bos_bear"
        return {"event": event, "bias": "bearish", "level": last_low.price, "at_idx": len(candles) - 1}
    return {"event": None, "bias": "neutral"}


def find_equal_levels(pivots: list[Pivot], kind: str, tol_pct: float = 0.0015) -> list[dict]:
    """EQH/EQL clustering: groups of same-kind pivots within tol_pct of each
    other mark concentrated resting liquidity (BSL above EQH, SSL below EQL)."""
    same = sorted([p for p in pivots if p.kind == kind], key=lambda p: p.price)
    clusters = []
    cluster = []
    for p in same:
        if not cluster or abs(p.price - cluster[-1].price) / max(cluster[-1].price, 1e-9) <= tol_pct:
            cluster.append(p)
        else:
            if len(cluster) >= 2:
                clusters.append(cluster)
            cluster = [p]
    if len(cluster) >= 2:
        clusters.append(cluster)
    out = []
    for c in clusters:
        level = sum(p.price for p in c) / len(c)
        out.append({"level": level, "count": len(c), "kind": "BSL" if kind == "high" else "SSL",
                     "pivots": c})
    return out


@dataclass
class Zone:
    kind: str
    direction: str
    top: float
    bottom: float
    idx: int
    mitigated: bool = False
    origin_sweep_level: Optional[float] = None

    @property
    def mid(self) -> float:
        return (self.top + self.bottom) / 2


def find_order_blocks(candles: list[dict], atr_series: list[float], lookback: int = 60) -> list[Zone]:
    """Last opposite-colored candle immediately before a strong displacement
    leg (move > 1.5x ATR), the classic institutional order-block footprint."""
    out = []
    n = len(candles)
    start = max(1, n - lookback)
    for i in range(start, n):
        atr_i = atr_series[i] if i < len(atr_series) else atr_series[-1]
        if atr_i <= 1e-12:
            continue
        body = candles[i]["c"] - candles[i]["o"]
        if abs(body) < 1.5 * atr_i:
            continue
        prev = candles[i - 1]
        if body > 0 and prev["c"] < prev["o"]:
            out.append(Zone("order_block", "bullish", prev["o"], prev["l"], i - 1))
        elif body < 0 and prev["c"] > prev["o"]:
            out.append(Zone("order_block", "bearish", prev["h"], prev["o"], i - 1))
    return out


def find_fvgs(candles: list[dict], atr_series: list[float], lookback: int = 60) -> list[Zone]:
    """Three-candle imbalance: candle[i-2].high/low doesn't overlap candle[i].low/high."""
    out = []
    n = len(candles)
    start = max(2, n - lookback)
    for i in range(start, n):
        c0, c2 = candles[i - 2], candles[i]
        if c2["l"] > c0["h"]:
            out.append(Zone("fvg", "bullish", c2["l"], c0["h"], i))
        elif c2["h"] < c0["l"]:
            out.append(Zone("fvg", "bearish", c0["l"], c2["h"], i))
    return out


def find_breaker_blocks(candles: list[dict], structure: dict, order_blocks: list[Zone]) -> list[Zone]:
    """A former order block that structure has broken through and flipped --
    the most recent confirmed institutional footprint (Sec 8 step 5)."""
    if not structure.get("event"):
        return []
    bias = structure["bias"]
    out = []
    for ob in order_blocks:
        if bias == "bullish" and ob.direction == "bearish" and candles[-1]["c"] > ob.top:
            out.append(Zone("breaker_block", "bullish", ob.top, ob.bottom, ob.idx))
        elif bias == "bearish" and ob.direction == "bullish" and candles[-1]["c"] < ob.bottom:
            out.append(Zone("breaker_block", "bearish", ob.top, ob.bottom, ob.idx))
    return out


def detect_sfp(candles: list[dict], pivots: list[Pivot], eq_tol_pct: float = 0.0018) -> Optional[dict]:
    """Swing failure pattern with a purity read: a genuine wick-based sweep of
    a prior swing (preferentially an EQH/EQL cluster) that closes back inside,
    vs. an ambiguous/partial sweep. Never assumes a sweep is coming -- only
    fires when the most recent closed candle actually produced one."""
    if len(candles) < 6 or not pivots:
        return None
    last = candles[-1]
    highs = [p for p in pivots if p.kind == "high" and p.idx < len(candles) - 1]
    lows = [p for p in pivots if p.kind == "low" and p.idx < len(candles) - 1]
    eq_highs = find_equal_levels(pivots, "high", eq_tol_pct)
    eq_lows = find_equal_levels(pivots, "low", eq_tol_pct)

    if highs:
        piv = max(highs, key=lambda p: p.idx)
        if last["h"] > piv.price and last["c"] < piv.price:
            wick = last["h"] - max(last["c"], last["o"])
            body = abs(last["c"] - last["o"])
            purity = clamp(wick / max(wick + body, 1e-9), 0.0, 1.0)
            eq_match = next((e for e in eq_highs if abs(e["level"] - piv.price) / piv.price < eq_tol_pct), None)
            return {"direction": "bearish", "swept_level": piv.price, "purity": purity,
                    "pure": purity >= 0.55, "liquidity_pool": eq_match, "idx": len(candles) - 1}
    if lows:
        piv = max(lows, key=lambda p: p.idx)
        if last["l"] < piv.price and last["c"] > piv.price:
            wick = min(last["c"], last["o"]) - last["l"]
            body = abs(last["c"] - last["o"])
            purity = clamp(wick / max(wick + body, 1e-9), 0.0, 1.0)
            eq_match = next((e for e in eq_lows if abs(e["level"] - piv.price) / piv.price < eq_tol_pct), None)
            return {"direction": "bullish", "swept_level": piv.price, "purity": purity,
                    "pure": purity >= 0.55, "liquidity_pool": eq_match, "idx": len(candles) - 1}
    return None


def premium_discount_zone(candles: list[dict], lookback: int = 80) -> dict:
    window = candles[-lookback:]
    if len(window) < 5:
        return {"zone": "equilibrium", "high": 0.0, "low": 0.0}
    hi = max(c["h"] for c in window)
    lo = min(c["l"] for c in window)
    last = candles[-1]["c"]
    if hi <= lo:
        return {"zone": "equilibrium", "high": hi, "low": lo}
    pos = (last - lo) / (hi - lo)
    zone = "premium" if pos > 0.6 else ("discount" if pos < 0.4 else "equilibrium")
    return {"zone": zone, "high": hi, "low": lo, "position": pos}


def fib_ote_refine(direction: str, impulse_start: float, impulse_end: float,
                    zone_top: float, zone_bottom: float) -> Optional[float]:
    """Fib OTE precision modifier (Sec 8 step 6): refines WHERE inside an
    already-validated zone to place entry, favoring the 61.8-79% retracement
    pocket where it overlaps the structural zone. Never nominates a zone on
    its own and contributes no separate score term (Sec 4)."""
    if impulse_end == impulse_start:
        return None
    span = impulse_end - impulse_start
    ote_low = impulse_end - span * 0.79
    ote_high = impulse_end - span * 0.618
    lo, hi = min(ote_low, ote_high), max(ote_low, ote_high)
    overlap_lo = max(lo, min(zone_bottom, zone_top))
    overlap_hi = min(hi, max(zone_bottom, zone_top))
    if overlap_lo > overlap_hi:
        return None
    return (overlap_lo + overlap_hi) / 2


@dataclass
class TFView:
    tf: str
    candles: list[dict]
    pivots: list[Pivot]
    structure: dict
    order_blocks: list[Zone]
    fvgs: list[Zone]
    breaker_blocks: list[Zone]
    sfp: Optional[dict]
    prem_disc: dict
    eq_highs: list[dict]
    eq_lows: list[dict]
    ema_fast: list[float]
    ema_slow: list[float]
    ema_trend: list[float]
    rsi: list[float]
    atr: list[float]
    adx: list[float]

    @property
    def last(self) -> dict:
        return self.candles[-1]


def build_tf_view(tf: str, candles: list[dict]) -> Optional[TFView]:
    if len(candles) < max(EMA_TREND, ATR_LEN, ADX_LEN) + 10:
        return None
    closes = [c["c"] for c in candles]
    pivots = find_pivots(candles)
    structure = detect_bos_choch(candles, pivots)
    atr_series = atr(candles, ATR_LEN)
    obs = find_order_blocks(candles, atr_series)
    fvgs = find_fvgs(candles, atr_series)
    breakers = find_breaker_blocks(candles, structure, obs)
    sfp = detect_sfp(candles, pivots)
    pd_zone = premium_discount_zone(candles)
    return TFView(
        tf=tf, candles=candles, pivots=pivots, structure=structure,
        order_blocks=obs, fvgs=fvgs, breaker_blocks=breakers, sfp=sfp,
        prem_disc=pd_zone, eq_highs=find_equal_levels(pivots, "high"),
        eq_lows=find_equal_levels(pivots, "low"),
        ema_fast=ema(closes, EMA_FAST), ema_slow=ema(closes, EMA_SLOW),
        ema_trend=ema(closes, EMA_TREND), rsi=rsi(closes), atr=atr_series,
        adx=adx(candles),
    )


@dataclass
class SymbolSnapshot:
    symbol: str
    mark: float
    views: dict[str, TFView] = field(default_factory=dict)


def collect_snapshot(hl: HyperliquidClient, symbol: str, mark: float) -> Optional[SymbolSnapshot]:
    views = {}
    for tf in ALL_TFS:
        candles = hl.candles(symbol, tf, TF_BARS[tf])
        if not candles:
            continue
        view = build_tf_view(tf, candles)
        if view:
            views[tf] = view
    if len(views) < 3:
        return None
    return SymbolSnapshot(symbol=symbol, mark=mark, views=views)


@dataclass
class RegimeVector:
    macro_bias: float
    volatility_pctile: float
    trend_strength: float
    session_weight: float
    session_open_proximity: float
    liquidity_draw: float
    noise_index: float
    breadth: float

    def label(self) -> str:
        if self.volatility_pctile > 75 and self.trend_strength > 30:
            return "expansion"
        if self.trend_strength >= 25 and abs(self.macro_bias) > 0.25:
            return "trending"
        if self.noise_index > 0.65 and self.trend_strength < 20:
            return "choppy"
        if self.volatility_pctile < 30 and self.trend_strength < 18:
            return "consolidation" if self.noise_index < 0.5 else "ranging"
        if self.volatility_pctile < 25:
            return "low_volatility"
        if self.volatility_pctile > 85:
            return "high_volatility"
        return "ranging"


def _session_weight_now() -> float:
    """Historical contribution to reliable moves, by active liquidity session.
    DECISION: London/NY overlap weighted highest (deepest liquidity), Asia
    lowest (thinnest, most prone to false structure)."""
    h = datetime.now(timezone.utc).hour
    if 12 <= h < 16:
        return 1.0
    if 7 <= h < 12 or 16 <= h < 21:
        return 0.75
    return 0.4


def _session_open_proximity_now() -> float:
    """Continuous, decaying score for closeness to London (07:00 UTC) or
    NY (12:00 UTC) session open -- soft input only (Sec 6), never a gate."""
    now = datetime.now(timezone.utc)
    minutes = now.hour * 60 + now.minute
    opens = [7 * 60, 12 * 60]
    best = min(abs(minutes - o) for o in opens)
    decay_window = 90
    return clamp(1.0 - best / decay_window, 0.0, 1.0)


def compute_regime_vector(macro_view: Optional[TFView], all_snaps: dict[str, SymbolSnapshot]) -> RegimeVector:
    if macro_view is None:
        macro_bias = 0.0
        vol_pctile = 50.0
        trend = 15.0
        noise = 0.5
    else:
        last_close = macro_view.last["c"]
        ema_t = macro_view.ema_trend[-1] if macro_view.ema_trend else last_close
        ema_f = macro_view.ema_fast[-1] if macro_view.ema_fast else last_close
        macro_bias = clamp((last_close - ema_t) / max(ema_t, 1e-9) * 8, -1.0, 1.0)
        if ema_f < ema_t:
            macro_bias = min(macro_bias, 0.0) if macro_bias > 0 else macro_bias
        vol_pctile = realized_vol_percentile(macro_view.candles)
        trend = macro_view.adx[-1] if macro_view.adx else 15.0
        noise = noise_index(macro_view.candles)

    liquidity_draw = 0.0
    if macro_view:
        px = macro_view.last["c"]
        erl_dist = min([abs(px - e["level"]) for e in (macro_view.eq_highs + macro_view.eq_lows)] or [1e9])
        irl_zones = [z for z in (macro_view.order_blocks + macro_view.fvgs) if not z.mitigated]
        irl_dist = min([abs(px - z.mid) for z in irl_zones] or [1e9])
        if erl_dist < 1e9 or irl_dist < 1e9:
            total = erl_dist + irl_dist
            if total > 1e-9:
                liquidity_draw = clamp((irl_dist - erl_dist) / total, -1.0, 1.0)

    coherent = 0
    total_assets = 0
    macro_dir = 1 if macro_bias >= 0 else -1
    for sym, snap in all_snaps.items():
        v = snap.views.get("1h")
        if not v or len(v.ema_fast) < 2 or len(v.ema_slow) < 2:
            continue
        total_assets += 1
        asset_dir = 1 if v.ema_fast[-1] >= v.ema_slow[-1] else -1
        if asset_dir == macro_dir:
            coherent += 1
    breadth = (coherent / total_assets) if total_assets else 0.5

    return RegimeVector(
        macro_bias=macro_bias, volatility_pctile=vol_pctile, trend_strength=trend,
        session_weight=_session_weight_now(), session_open_proximity=_session_open_proximity_now(),
        liquidity_draw=liquidity_draw, noise_index=noise, breadth=breadth,
    )


@dataclass
class ZoneSelection:
    direction: str
    poi: Zone
    sfp: Optional[dict]
    mss_confirmed: bool
    breaker: Optional[Zone]
    entry_hint: float
    session_anchored: bool


def select_zone(htf: TFView, mid: TFView, ltf: TFView, state: dict) -> Optional[ZoneSelection]:
    """Implements Sec 8's mandatory ordered sequence:
    1. HTF bias   2. POI   3. SFP purity   4. MSS   5. breaker   6. Fib OTE refine.
    Returns None if the sequence doesn't validate a tradeable zone -- this is
    a selection mechanism, not a scorer; scoring happens downstream (Sec 4)."""
    htf_bias = htf.structure.get("bias", "neutral")
    if htf_bias == "neutral":
        return None
    direction = "bullish" if htf_bias == "bullish" else "bearish"

    poi_candidates = [z for z in (mid.order_blocks + mid.fvgs)
                       if z.direction == direction and not z.mitigated]
    if not poi_candidates:
        return None

    sfp = ltf.sfp
    session_anchored = False
    chosen_poi = None
    if sfp and sfp["direction"] == direction:
        purity_ok = sfp["pure"]
        strictness = state["tier1"]["sfp_mss_strictness"].get("smc", 0.5)
        if not purity_ok and strictness > 0.65:
            sfp = None
        else:
            for poi in poi_candidates:
                if abs(poi.mid - sfp["swept_level"]) / max(sfp["swept_level"], 1e-9) < 0.01:
                    poi.origin_sweep_level = sfp["swept_level"]
                    chosen_poi = poi
                    break
            session_anchored = _session_open_proximity_now() > 0.5

    if chosen_poi is None:
        px = ltf.last["c"]
        chosen_poi = min(poi_candidates, key=lambda z: abs(z.mid - px))

    ltf_bias = ltf.structure.get("bias", "neutral")
    mss_confirmed = (ltf_bias == direction) or (mid.structure.get("bias") == direction)
    if not mss_confirmed:
        return None

    breaker = next((b for b in mid.breaker_blocks if b.direction == direction), None)
    poi_for_entry = breaker if breaker else chosen_poi

    impulse_start = ltf.candles[max(0, len(ltf.candles) - 20)]["c"]
    impulse_end = ltf.last["c"]
    refined = fib_ote_refine(direction, impulse_start, impulse_end, poi_for_entry.top, poi_for_entry.bottom)
    entry_hint = refined if refined is not None else poi_for_entry.mid

    return ZoneSelection(direction=direction, poi=poi_for_entry, sfp=sfp,
                          mss_confirmed=mss_confirmed, breaker=breaker,
                          entry_hint=entry_hint, session_anchored=session_anchored)


def _rr(entry: float, sl: float, target: float, direction: str) -> float:
    risk = abs(entry - sl)
    if risk <= 1e-12:
        return 0.0
    reward = (target - entry) if direction == "bullish" else (entry - target)
    return reward / risk


def adaptive_sl_buffer(view: TFView, state: dict, asset: str) -> float:
    """Sec 10 mandatory: SL buffer sized from a live percentile of recent
    adverse-wick excursions beyond structure, not a fixed constant. The
    percentile itself is a bounded, dampened adaptive parameter (Sec 5)."""
    key = f"{asset}:{view.tf}"
    pctile = state["tier1"]["sl_buffer_percentile"].get(key, 65.0)
    wicks = []
    for i in range(1, len(view.candles)):
        c = view.candles[i]
        body_top = max(c["o"], c["c"])
        body_bot = min(c["o"], c["c"])
        wicks.append(c["h"] - body_top)
        wicks.append(body_bot - c["l"])
    wicks = sorted(w for w in wicks if w > 0)
    if not wicks:
        return view.atr[-1] * 0.25 if view.atr else 0.0
    idx = clamp(int(len(wicks) * pctile / 100.0), 0, len(wicks) - 1)
    buffer = wicks[idx]
    atr_val = view.atr[-1] if view.atr else buffer
    return clamp(buffer, atr_val * 0.4, atr_val * 2.5)


def estimate_liquidation_price(direction: str, entry: float,
                                leverage: float = ASSUMED_LEVERAGE,
                                mmr: float = MAINTENANCE_MARGIN_RATE) -> float:
    """Reference liquidation price at ASSUMED_LEVERAGE, used only as a
    conservative sanity backstop (see config comment) -- never as an actual
    margin/PNL calculation, since real account leverage/size are unknown to
    the engine."""
    if direction == "bullish":
        return entry * (1.0 - 1.0 / leverage + mmr)
    return entry * (1.0 + 1.0 / leverage - mmr)


def _clear_sl_of_liquidity_pool(direction: str, sl: float, view: TFView) -> float:
    """eq_lows/eq_highs mark clustered resting liquidity (SSL below price for
    longs, BSL above price for shorts) -- exactly what a stop-hunt wick
    targets before reversing. If the stop doesn't clear the full cluster
    (not just its average level), push it past the cluster's far edge plus
    the cluster's own width as a margin."""
    pools = view.eq_lows if direction == "bullish" else view.eq_highs
    for pool in pools:
        prices = [p.price for p in pool["pivots"]]
        lo, hi = min(prices), max(prices)
        margin = max(hi - lo, 1e-9)
        if direction == "bullish" and sl >= lo:
            sl = lo - margin
        elif direction == "bearish" and sl <= hi:
            sl = hi + margin
    return sl


def _opposing_structural_levels(direction: str, entry: float, view: TFView) -> list[float]:
    """Every genuine chart level that could act as resistance (long) or
    support (short) ahead of price -- swing pivots, EQH/EQL liquidity
    clusters, and unmitigated opposing order/breaker blocks and FVGs. TP is
    chosen from what's actually on the chart, never synthesized to hit an
    RR number."""
    levels = []
    if direction == "bullish":
        levels += [p.price for p in view.pivots if p.kind == "high" and p.price > entry]
        levels += [e["level"] for e in view.eq_highs if e["level"] > entry]
        levels += [z.bottom for z in (view.order_blocks + view.breaker_blocks)
                   if z.direction == "bearish" and not z.mitigated and z.bottom > entry]
        levels += [z.bottom for z in view.fvgs
                   if z.direction == "bearish" and not z.mitigated and z.bottom > entry]
    else:
        levels += [p.price for p in view.pivots if p.kind == "low" and p.price < entry]
        levels += [e["level"] for e in view.eq_lows if e["level"] < entry]
        levels += [z.top for z in (view.order_blocks + view.breaker_blocks)
                   if z.direction == "bullish" and not z.mitigated and z.top < entry]
        levels += [z.top for z in view.fvgs
                   if z.direction == "bullish" and not z.mitigated and z.top < entry]
    levels = sorted(set(levels))
    return levels if direction == "bullish" else list(reversed(levels))


def build_risk_plan(direction: str, entry: float, structural_sl: float, view: TFView,
                     state: dict, asset: str, combo: str) -> Optional[dict]:
    """SL/TP1/TP2 are genuine chart levels, not RR-formula outputs. SL = the
    engine's real invalidation level (swing low/OB/BB/swept level, itself
    already sourced from the LTF/mid-TF zone by the calling engine -- e.g.
    the 15m swing low or the h4/h1 POI/OB edge -- never a distant HTF
    level), pushed out only for noise (wick-based buffer) and to clear a
    known liquidity pool -- never resized to hit an RR target. TP1/TP2 =
    the nearest and second-nearest real opposing structural levels (pivot,
    EQH/EQL, unmitigated OB/breaker/FVG) -- never stretched or clipped by
    an RR formula. If the chart doesn't offer a second real target, the
    signal is skipped rather than fabricating one. RR appears only as a
    final reject-only quality gate (RR_MIN_GATE): if rr1 comes in under it,
    the signal is simply not sent -- the levels are never reshaped to clear
    the gate.

    Two further reject-only gates, added so a technically-real level still
    can't produce an intraday/swing signal that's impractical to actually
    hit or unsafe to hold:
      - MAX_MOVE_* ceilings on SL/TP1/TP2 (combo-aware, ATR-relative with a
        flat-% backstop): a real level that sits too far away for the
        combo's holding horizon -- relative to this asset's own recent
        ATR, not a one-size-fits-all % -- is skipped, same as the
        MIN_MOVE_* floors reject levels that are too close.
      - Liquidation-safety check: the SL must trigger before a reference
        liquidation (at ASSUMED_LEVERAGE) would, i.e. SL must sit on the
        safe side of that reference liquidation price."""
    buffer = adaptive_sl_buffer(view, state, asset)
    sl = (structural_sl - buffer) if direction == "bullish" else (structural_sl + buffer)
    sl = _clear_sl_of_liquidity_pool(direction, sl, view)

    risk = abs(entry - sl)
    if risk <= 1e-12:
        return None

    atr_val_now = view.atr[-1] if view.atr else 0.0
    max_sl_pct = MAX_MOVE_PCT_SL_INTRADAY if combo == "intraday" else MAX_MOVE_PCT_SL_SWING
    max_sl_atr = MAX_MOVE_ATR_SL_INTRADAY if combo == "intraday" else MAX_MOVE_ATR_SL_SWING
    max_sl_dist = _atr_pct_bound(entry, atr_val_now, max_sl_atr, max_sl_pct)
    if risk > max_sl_dist:
        return None

    liq = estimate_liquidation_price(direction, entry)
    if direction == "bullish" and sl <= liq:
        return None
    if direction == "bearish" and sl >= liq:
        return None

    targets = _opposing_structural_levels(direction, entry, view)
    if len(targets) < 2:
        return None
    tp1, tp2 = targets[0], targets[1]
    rr1 = _rr(entry, sl, tp1, direction)
    rr2 = _rr(entry, sl, tp2, direction)

    if direction == "bullish":
        assert tp2 > tp1, "TP ordering integrity violated (bullish)"
    else:
        assert tp2 < tp1, "TP ordering integrity violated (bearish)"

    if abs(tp1 - entry) < _atr_pct_bound(entry, atr_val_now, MIN_MOVE_ATR_TP1, MIN_MOVE_PCT_TP1):
        return None
    if abs(tp2 - entry) < _atr_pct_bound(entry, atr_val_now, MIN_MOVE_ATR_TP2, MIN_MOVE_PCT_TP2):
        return None

    max_tp1_pct = MAX_MOVE_PCT_TP1_INTRADAY if combo == "intraday" else MAX_MOVE_PCT_TP1_SWING
    max_tp2_pct = MAX_MOVE_PCT_TP2_INTRADAY if combo == "intraday" else MAX_MOVE_PCT_TP2_SWING
    max_tp1_atr = MAX_MOVE_ATR_TP1_INTRADAY if combo == "intraday" else MAX_MOVE_ATR_TP1_SWING
    max_tp2_atr = MAX_MOVE_ATR_TP2_INTRADAY if combo == "intraday" else MAX_MOVE_ATR_TP2_SWING
    max_tp1_dist = _atr_pct_bound(entry, atr_val_now, max_tp1_atr, max_tp1_pct)
    max_tp2_dist = _atr_pct_bound(entry, atr_val_now, max_tp2_atr, max_tp2_pct)
    if abs(tp1 - entry) > max_tp1_dist:
        return None
    if abs(tp2 - entry) > max_tp2_dist:
        return None

    if rr1 < RR_MIN_GATE:
        return None

    return {"sl": sl, "tp1": tp1, "tp2": tp2, "rr1": rr1, "rr2": rr2, "risk": risk, "buffer": buffer}


def passes_entry_placement_rules(entry: float, sl: float, tp1: float, atr_val: float,
                                  mark: float, combo: str = "intraday") -> bool:
    """Sec 10 entry-placement rules: minimum entry-to-SL/TP1 distance, and a
    cap on how far a pending/zone entry may sit from current market price.
    Split by combo: intraday (4h/1h/15m) trades tighter, faster-forming
    zones, while swing (1d/4h/1h) setups legitimately form and get tagged
    from further away on higher timeframes. A single flat multiplier for
    both was rejecting genuine swing zone-entries that were never
    unreasonable for that combo's timeframe, just further from mark in ATR
    terms than an intraday setup would be."""
    if atr_val <= 1e-12:
        return False
    min_dist_mult = ENTRY_MIN_DIST_ATR_SWING if combo == "swing" else ENTRY_MIN_DIST_ATR_INTRADAY
    max_pending_mult = ENTRY_MAX_PENDING_ATR_SWING if combo == "swing" else ENTRY_MAX_PENDING_ATR_INTRADAY
    min_dist = atr_val * min_dist_mult
    if abs(entry - sl) < min_dist or abs(entry - tp1) < min_dist:
        return False
    max_pending_dist = atr_val * max_pending_mult
    if abs(entry - mark) > max_pending_dist:
        return False
    return True


@dataclass
class Candidate:
    id: str
    symbol: str
    engine: str
    combo: str
    direction: str
    entry: float
    sl: float
    tp1: float
    tp2: float
    rr1: float
    rr2: float
    confidence: float
    confluences: list[str]
    regime_best_fit: set
    entry_kind: str
    session_anchored: bool = False
    liquidity_pool_hit: bool = False
    mtf_aligned: bool = True
    created_at: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    entry_filled: bool = False
    pending_bars: int = 0
    watermark_ts: Optional[int] = None
    sfp_purity: Optional[float] = None
    filter_margin_thin: bool = False
    buffer_to_risk_ratio: float = 0.0

    def to_dict(self) -> dict:
        d = asdict(self)
        d["regime_best_fit"] = sorted(self.regime_best_fit)
        return d


def _new_id(symbol: str, engine: str) -> str:
    return f"{symbol}-{engine}-{int(time.time() * 1000)}"


def _tp_ordering_sane(cand: Candidate) -> bool:
    if cand.direction == "bullish":
        return cand.tp2 > cand.tp1 > cand.entry > cand.sl
    return cand.tp2 < cand.tp1 < cand.entry < cand.sl


def _combo_views(snap: SymbolSnapshot, combo: str) -> Optional[tuple[TFView, TFView, TFView]]:
    if combo == "intraday":
        tfs = (TF_HTF_INTRADAY, TF_MID_INTRADAY, TF_LTF_INTRADAY)
    else:
        tfs = (TF_HTF_SWING, TF_MID_SWING, TF_LTF_SWING)
    views = [snap.views.get(tf) for tf in tfs]
    if any(v is None for v in views):
        return None
    return tuple(views)


def _finalize(symbol: str, engine: str, combo: str, direction: str, entry: float,
              structural_sl: float, ltf: TFView, state: dict, confidence: float,
              confluences: list[str], regime_fit: set, entry_kind: str,
              mark: float, session_anchored: bool = False,
              liquidity_pool_hit: bool = False, mtf_aligned: bool = True,
              sfp_purity: Optional[float] = None) -> Optional[Candidate]:
    plan = build_risk_plan(direction, entry, structural_sl, ltf, state, symbol, combo)
    if plan is None:
        return None
    atr_val = ltf.atr[-1] if ltf.atr else 0.0
    if not passes_entry_placement_rules(entry, plan["sl"], plan["tp1"], atr_val, mark, combo):
        return None
    thin = confidence < 0.5
    buf_ratio = plan["buffer"] / plan["risk"] if plan["risk"] > 1e-12 else 0.0
    cand = Candidate(
        id=_new_id(symbol, engine), symbol=symbol, engine=engine, combo=combo,
        direction=direction, entry=entry, sl=plan["sl"], tp1=plan["tp1"], tp2=plan["tp2"],
        rr1=plan["rr1"], rr2=plan["rr2"], confidence=clamp(confidence, 0.0, 1.0),
        confluences=confluences, regime_best_fit=regime_fit, entry_kind=entry_kind,
        session_anchored=session_anchored, liquidity_pool_hit=liquidity_pool_hit,
        mtf_aligned=mtf_aligned, sfp_purity=sfp_purity, filter_margin_thin=thin,
        buffer_to_risk_ratio=buf_ratio,
    )
    if not _tp_ordering_sane(cand):
        return None
    return cand


def engine_smc(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    zone = select_zone(htf, mid, ltf, state)
    if zone is None:
        return []
    confluences = ["htf_bias", "poi_validated", "mss_confirmed"]
    confidence = 0.55
    if zone.sfp and zone.sfp["pure"]:
        confluences.append("pure_sfp")
        confidence += 0.1
    if zone.breaker:
        confluences.append("breaker_block")
        confidence += 0.08
    if zone.poi.origin_sweep_level is not None:
        confluences.append("sweep_to_poi_causality")
        confidence += 0.05
    liquidity_hit = zone.sfp is not None and zone.sfp.get("liquidity_pool") is not None
    cand = _finalize(snap.symbol, "smc", combo, zone.direction, zone.entry_hint,
                      zone.poi.bottom if zone.direction == "bullish" else zone.poi.top,
                      ltf, state, confidence, confluences, ENGINE_REGIME_FIT["smc"],
                      "pending", snap.mark, session_anchored=zone.session_anchored,
                      liquidity_pool_hit=liquidity_hit,
                      sfp_purity=zone.sfp["purity"] if zone.sfp else None)
    return [cand] if cand else []


def engine_trend_continuation(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    if len(htf.ema_fast) < 2 or len(htf.ema_slow) < 2 or len(htf.ema_trend) < 1:
        return []
    bullish = htf.ema_fast[-1] > htf.ema_slow[-1] > htf.ema_trend[-1]
    bearish = htf.ema_fast[-1] < htf.ema_slow[-1] < htf.ema_trend[-1]
    if not (bullish or bearish):
        return []
    direction = "bullish" if bullish else "bearish"
    entry = mid.ema_fast[-1] if mid.ema_fast else mid.last["c"]
    structural_sl = min(p.price for p in ltf.pivots[-6:] if p.kind == "low") if \
        any(p.kind == "low" for p in ltf.pivots[-6:]) else ltf.last["l"]
    if direction == "bearish":
        highs = [p.price for p in ltf.pivots[-6:] if p.kind == "high"]
        structural_sl = max(highs) if highs else ltf.last["h"]
    confluences = ["ema_stack_aligned", "htf_trend"]
    confidence = 0.5 + min(0.2, (mid.adx[-1] if mid.adx else 15) / 100)
    return _list(_finalize(snap.symbol, "trend_continuation", combo, direction, entry,
                            structural_sl, ltf, state, confidence, confluences,
                            ENGINE_REGIME_FIT["trend_continuation"], "pending", snap.mark))


def engine_breakout(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    recent = ltf.candles[-25:]
    if len(recent) < 10:
        return []
    range_high = max(c["h"] for c in recent[:-1])
    range_low = min(c["l"] for c in recent[:-1])
    last = ltf.last
    atr_val = ltf.atr[-1] if ltf.atr else 0.0
    if atr_val <= 0:
        return []
    if last["c"] > range_high and (last["c"] - range_high) < atr_val * 0.6:
        direction, entry, structural_sl = "bullish", last["c"], range_low
    elif last["c"] < range_low and (range_low - last["c"]) < atr_val * 0.6:
        direction, entry, structural_sl = "bearish", last["c"], range_high
    else:
        return []
    confluences = ["range_breakout", "close_beyond_range"]
    confidence = 0.5
    return _list(_finalize(snap.symbol, "breakout", combo, direction, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["breakout"],
                            "market", snap.mark))


def engine_pullback(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    if len(mid.ema_fast) < 2 or len(mid.ema_slow) < 2:
        return []
    bullish = mid.ema_fast[-1] > mid.ema_slow[-1] and htf.structure.get("bias") == "bullish"
    bearish = mid.ema_fast[-1] < mid.ema_slow[-1] and htf.structure.get("bias") == "bearish"
    if not (bullish or bearish):
        return []
    direction = "bullish" if bullish else "bearish"
    last_rsi = ltf.rsi[-1] if ltf.rsi else 50
    if direction == "bullish" and last_rsi > 55:
        return []
    if direction == "bearish" and last_rsi < 45:
        return []
    entry = ltf.ema_fast[-1] if ltf.ema_fast else ltf.last["c"]
    obs = [z for z in mid.order_blocks if z.direction == direction]
    structural_sl = min((z.bottom for z in obs), default=ltf.last["l"]) if direction == "bullish" \
        else max((z.top for z in obs), default=ltf.last["h"])
    confluences = ["htf_bias_pullback", "rsi_cooled"]
    confidence = 0.48
    return _list(_finalize(snap.symbol, "pullback", combo, direction, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["pullback"],
                            "pending", snap.mark))


def engine_liquidity_sweep(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    if not ltf.sfp:
        return []
    sfp = ltf.sfp
    direction = sfp["direction"]
    entry = ltf.last["c"]
    structural_sl = sfp["swept_level"]
    confluences = ["liquidity_sweep"]
    confidence = 0.45 + (0.15 if sfp["pure"] else 0.0)
    if sfp.get("liquidity_pool"):
        confluences.append("eqh_eql_cluster_swept")
        confidence += 0.08
    return _list(_finalize(snap.symbol, "liquidity_sweep", combo, direction, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["liquidity_sweep"],
                            "market", snap.mark, liquidity_pool_hit=bool(sfp.get("liquidity_pool")),
                            sfp_purity=sfp["purity"]))


def engine_order_block(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    bias = htf.structure.get("bias")
    if bias not in ("bullish", "bearish"):
        return []
    unmit = [z for z in mid.order_blocks if z.direction == bias and not z.mitigated]
    if not unmit:
        return []
    px = ltf.last["c"]
    ob = min(unmit, key=lambda z: abs(z.mid - px))
    if bias == "bullish" and not (ob.bottom <= px <= ob.top * 1.02):
        return []
    if bias == "bearish" and not (ob.bottom * 0.98 <= px <= ob.top):
        return []
    entry = ob.mid
    structural_sl = ob.bottom if bias == "bullish" else ob.top
    confluences = ["order_block_retest", "htf_bias_aligned"]
    confidence = 0.5
    return _list(_finalize(snap.symbol, "order_block", combo, bias, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["order_block"],
                            "pending", snap.mark))


def engine_breaker_block(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    if not mid.breaker_blocks:
        return []
    bias = htf.structure.get("bias")
    candidates = [z for z in mid.breaker_blocks if z.direction == bias]
    if not candidates:
        return []
    bb = candidates[0]
    entry = bb.mid
    structural_sl = bb.bottom if bias == "bullish" else bb.top
    confluences = ["breaker_block_flip", "structure_shift_confirmed"]
    confidence = 0.55
    return _list(_finalize(snap.symbol, "breaker_block", combo, bias, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["breaker_block"],
                            "pending", snap.mark))


def engine_fair_value_gap(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    bias = htf.structure.get("bias")
    fvgs = [z for z in mid.fvgs if z.direction == bias and not z.mitigated]
    if not fvgs:
        return []
    px = ltf.last["c"]
    gap = min(fvgs, key=lambda z: abs(z.mid - px))
    entry = gap.mid
    structural_sl = gap.bottom if bias == "bullish" else gap.top
    confluences = ["fvg_rebalance", "htf_bias_aligned"]
    confidence = 0.47
    return _list(_finalize(snap.symbol, "fair_value_gap", combo, bias, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["fair_value_gap"],
                            "pending", snap.mark))


def engine_momentum(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    if len(ltf.rsi) < 2:
        return []
    r = ltf.rsi[-1]
    adx_val = ltf.adx[-1] if ltf.adx else 15
    if adx_val < 22:
        return []
    if r > 60 and ltf.last["c"] > (ltf.ema_fast[-1] if ltf.ema_fast else ltf.last["c"]):
        direction = "bullish"
    elif r < 40 and ltf.last["c"] < (ltf.ema_fast[-1] if ltf.ema_fast else ltf.last["c"]):
        direction = "bearish"
    else:
        return []
    entry = ltf.last["c"]
    atr_val = ltf.atr[-1] if ltf.atr else 0.0
    structural_sl = entry - atr_val * 1.2 if direction == "bullish" else entry + atr_val * 1.2
    confluences = ["momentum_thrust", "adx_confirmed"]
    confidence = 0.45 + min(0.15, (adx_val - 22) / 100)
    return _list(_finalize(snap.symbol, "momentum", combo, direction, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["momentum"],
                            "market", snap.mark))


def engine_reversal(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    if not ltf.sfp or not mid.structure.get("event"):
        return []
    sfp = ltf.sfp
    mid_event_bias = mid.structure.get("bias")
    if sfp["direction"] != mid_event_bias:
        return []
    direction = sfp["direction"]
    entry = ltf.last["c"]
    structural_sl = sfp["swept_level"]
    confluences = ["sfp_reversal", "choch_confirmed"]
    confidence = 0.5 + (0.1 if sfp["pure"] else 0.0)
    return _list(_finalize(snap.symbol, "reversal", combo, direction, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["reversal"],
                            "market", snap.mark, sfp_purity=sfp["purity"]))


def engine_mean_reversion(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    adx_val = ltf.adx[-1] if ltf.adx else 15
    if adx_val > 20:
        return []
    pd = ltf.prem_disc
    r = ltf.rsi[-1] if ltf.rsi else 50
    if pd["zone"] == "premium" and r > 68:
        direction, structural_sl = "bearish", pd["high"]
    elif pd["zone"] == "discount" and r < 32:
        direction, structural_sl = "bullish", pd["low"]
    else:
        return []
    entry = ltf.last["c"]
    confluences = ["premium_discount_extreme", "rsi_extreme", "low_adx_range"]
    confidence = 0.45
    plan_entry = entry
    cand = _finalize(snap.symbol, "mean_reversion", combo, direction, plan_entry, structural_sl,
                      ltf, state, confidence, confluences, ENGINE_REGIME_FIT["mean_reversion"],
                      "market", snap.mark)
    return [cand] if cand else []


def engine_range_trading(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    adx_val = mid.adx[-1] if mid.adx else 15
    if adx_val > 18:
        return []
    recent = ltf.candles[-40:]
    if len(recent) < 15:
        return []
    range_high = max(c["h"] for c in recent)
    range_low = min(c["l"] for c in recent)
    span = range_high - range_low
    if span <= 0:
        return []
    px = ltf.last["c"]
    pos = (px - range_low) / span
    if pos > 0.85:
        direction, structural_sl = "bearish", range_high
    elif pos < 0.15:
        direction, structural_sl = "bullish", range_low
    else:
        return []
    entry = px
    confluences = ["range_boundary_reaction", "low_adx_confirmed"]
    confidence = 0.44
    return _list(_finalize(snap.symbol, "range_trading", combo, direction, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["range_trading"],
                            "market", snap.mark))


def engine_volatility_expansion(snap: SymbolSnapshot, combo: str, state: dict) -> list[Candidate]:
    views = _combo_views(snap, combo)
    if not views:
        return []
    htf, mid, ltf = views
    vol_pct = realized_vol_percentile(ltf.candles)
    if vol_pct < 80:
        return []
    bias = htf.structure.get("bias")
    if bias not in ("bullish", "bearish"):
        return []
    last = ltf.last
    body = abs(last["c"] - last["o"])
    atr_val = ltf.atr[-1] if ltf.atr else 0.0
    if atr_val <= 0 or body < atr_val * 1.1:
        return []
    direction = "bullish" if last["c"] > last["o"] else "bearish"
    if direction != bias:
        return []
    entry = last["c"]
    structural_sl = last["l"] if direction == "bullish" else last["h"]
    confluences = ["volatility_expansion_bar", "htf_bias_aligned"]
    confidence = 0.46
    return _list(_finalize(snap.symbol, "volatility_expansion", combo, direction, entry, structural_sl,
                            ltf, state, confidence, confluences, ENGINE_REGIME_FIT["volatility_expansion"],
                            "market", snap.mark))


def _list(cand: Optional[Candidate]) -> list[Candidate]:
    return [cand] if cand else []


ENGINE_FUNCS = {
    "smc": engine_smc, "trend_continuation": engine_trend_continuation,
    "breakout": engine_breakout, "pullback": engine_pullback,
    "liquidity_sweep": engine_liquidity_sweep, "order_block": engine_order_block,
    "breaker_block": engine_breaker_block, "fair_value_gap": engine_fair_value_gap,
    "momentum": engine_momentum, "reversal": engine_reversal,
    "mean_reversion": engine_mean_reversion, "range_trading": engine_range_trading,
    "volatility_expansion": engine_volatility_expansion,
}


def run_ensemble(snap: SymbolSnapshot, state: dict, regime_label: str) -> list[Candidate]:
    out = []
    veto_scalp = regime_label in SCALP_PRONE_REGIMES
    for combo in ("intraday", "swing"):
        for name, fn in ENGINE_FUNCS.items():
            if veto_scalp and name in SCALP_PRONE_ENGINES:
                continue
            try:
                out.extend(fn(snap, combo, state))
            except Exception:
                log.exception("engine %s (%s) failed on %s -- skipping", name, combo, snap.symbol)
    return out


def confluence_strength(cand: Candidate) -> float:
    return clamp(math.log1p(len(cand.confluences)) / math.log1p(6), 0.0, 1.0)


def regime_fit_score(cand: Candidate, regime: RegimeVector, state: dict) -> tuple[float, bool]:
    """Sec 13 mandatory regime-fit veto/discount."""
    label = regime.label()
    fit_weight = state["tier1"]["regime_fit_weights"].get(cand.engine, {}).get(label, 1.0)
    if label in cand.regime_best_fit:
        return clamp(0.7 + 0.3 * fit_weight, 0.0, 1.0), True
    return clamp(0.15 * fit_weight, 0.0, 1.0), False


def mtf_alignment_score(cand: Candidate) -> float:
    return 1.0 if cand.mtf_aligned else 0.2


def historical_segment_score(cand: Candidate, regime: RegimeVector, state: dict) -> float:
    seg = state["tier1"]["segments"]["engine"].get(cand.engine, _default_segment_stats())
    if seg["n"] < MIN_SAMPLE_SIZE:
        return 0.5
    wr = seg["wins"] / seg["n"] if seg["n"] else 0.5
    return clamp(wr, 0.0, 1.0)


def liquidity_sanity_score(cand: Candidate, view: TFView, state: dict) -> tuple[float, bool]:
    """Sec 13 liquidity sanity check: reject/discount entries sitting inside
    or adjacent to an about-to-be-swept pool, unless the engine is a
    liquidity-sweep specialist designed to trade exactly that."""
    threshold = state["tier1"]["liquidity_sanity_threshold"].get(cand.engine, 0.5)
    if cand.engine == "liquidity_sweep":
        return 1.0, True
    if not cand.liquidity_pool_hit:
        return 1.0, True
    penalty = clamp(1.0 - threshold, 0.0, 1.0)
    return penalty, penalty > 0.3


def ev_estimate(cand: Candidate, wr_prior: float) -> float:
    return wr_prior * cand.rr1 - (1 - wr_prior) * 1.0


def _news_blackout_active(symbol: str, state: dict) -> bool:
    """Sec 13 macro/news blackout. DECISION: without a live economic-calendar
    feed wired in, this engine checks a documented, operator-editable window
    list persisted in state.json (empty by default) rather than silently
    no-op'ing the requirement -- the gate is fully implemented and enforced,
    it simply has no scheduled events until the operator populates one."""
    windows = state["tier1"].get("news_blackout_windows", [])
    now = datetime.now(timezone.utc)
    for w in windows:
        try:
            start = datetime.fromisoformat(w["start"]) - timedelta(minutes=NEWS_BLACKOUT_MIN_BEFORE)
            end = datetime.fromisoformat(w["end"]) + timedelta(minutes=NEWS_BLACKOUT_MIN_AFTER)
        except (KeyError, ValueError):
            continue
        affected = set(w.get("assets", [])) | ({MACRO_ASSET} if w.get("macro", False) else set())
        if start <= now <= end and (symbol in affected or symbol in MAJORS and w.get("macro")):
            return True
    return False


def composite_score(cand: Candidate, regime: RegimeVector, view: TFView, state: dict) -> tuple[float, bool]:
    """Sec 4 mandatory continuous blend over a small, auditable set of terms
    -- never a discrete point stack. Each term is independently attributable."""
    t1 = state["tier1"]
    fit, fit_ok = regime_fit_score(cand, regime, state)
    mtf = mtf_alignment_score(cand)
    conflu = confluence_strength(cand)
    hist = historical_segment_score(cand, regime, state)
    liq, liq_ok = liquidity_sanity_score(cand, view, state)
    rr_term = clamp((cand.rr1 - RR_TP1_FLOOR) / 2.0, 0.0, 1.0)
    session_term = regime.session_open_proximity if cand.session_anchored else 0.0
    eng_weight = t1["engine_weights"].get(cand.engine, 1.0)
    mtf_w = t1["mtf_alignment_weight"]
    session_w = t1["session_open_weight"]

    weights = {"fit": 0.22, "mtf": mtf_w, "confluence": 0.18, "hist": 0.15,
               "liquidity": 0.12, "rr": 0.13, "session": session_w, "confidence": 0.05}
    total_w = sum(weights.values()) or 1.0
    raw = (weights["fit"] * fit + weights["mtf"] * mtf + weights["confluence"] * conflu +
           weights["hist"] * hist + weights["liquidity"] * liq + weights["rr"] * rr_term +
           weights["session"] * session_term + weights["confidence"] * cand.confidence)
    score = clamp((raw / total_w) * eng_weight, 0.0, 1.0)
    score = 1 / (1 + math.exp(-6 * (score - 0.5)))
    label = regime.label()
    scalp_veto = label in SCALP_PRONE_REGIMES and cand.engine in SCALP_PRONE_ENGINES
    eligible = fit_ok and liq_ok and _tp_ordering_sane(cand) and not scalp_veto
    return score, eligible


def calibrate_confidence(cand: Candidate, state: dict) -> float:
    cal = state["tier1"]["confidence_calibration"].get(cand.engine, {})
    bucket = str(int(cand.confidence * 10))
    offset = cal.get(bucket, 0.0)
    return clamp(cand.confidence + offset, 0.0, 1.0)


def assign_tier(score: float, rr1: float) -> str:
    if score >= 0.72 and rr1 >= RR_TP1_CEIL_SOFT:
        return "A+"
    if score >= 0.58:
        return "A"
    return "B"


def _correlated_group(symbol: str) -> str:
    return "majors" if symbol in MAJORS else symbol


def decision_engine_rank(candidates: list[Candidate], regime: RegimeVector,
                          snaps: dict[str, SymbolSnapshot], state: dict,
                          active_signals: list[dict]) -> list[Candidate]:
    scored = []
    funnel = state["tier1"]["filter_funnel"]
    regime_label = regime.label()
    regime_fit_kills = 0

    def _track(stage: str, killed: bool):
        f = funnel.setdefault(stage, {"seen": 0, "killed": 0})
        f["seen"] += 1
        if killed:
            f["killed"] += 1

    for cand in candidates:
        _track("news_blackout", False)
        if _news_blackout_active(cand.symbol, state):
            funnel["news_blackout"]["killed"] += 1
            continue
        view = snaps[cand.symbol].views.get(
            TF_LTF_INTRADAY if cand.combo == "intraday" else TF_LTF_SWING)
        if view is None:
            continue
        score, eligible = composite_score(cand, regime, view, state)
        _track("composite_eligibility", not eligible)
        if not eligible:
            if regime_label not in cand.regime_best_fit:
                regime_fit_kills += 1
            continue
        cand.confidence = calibrate_confidence(cand, state)
        tier = assign_tier(score, cand.rr1)
        scored.append((score, tier, cand))

    scored.sort(key=lambda x: x[0], reverse=True)

    active_groups: dict[str, int] = {}
    for sig in active_signals:
        g = _correlated_group(sig["symbol"])
        active_groups[g] = active_groups.get(g, 0) + 1

    seen_symbols: set[str] = set()
    final: list[Candidate] = []
    for score, tier, cand in scored:
        if len(final) + len(active_signals) >= MAX_CONCURRENT_ACTIVE_SIGNALS:
            break
        if cand.symbol in seen_symbols:
            continue
        group = _correlated_group(cand.symbol)
        if active_groups.get(group, 0) >= MAX_CORRELATED_CONCURRENT:
            continue
        cand.confluences.append(f"tier:{tier}")
        final.append(cand)
        seen_symbols.add(cand.symbol)
        active_groups[group] = active_groups.get(group, 0) + 1

    log.info(
        "decision_engine_rank: regime=%s raw_candidates=%d passed_eligibility=%d "
        "killed_on_regime_fit=%d sent=%d",
        regime_label, len(candidates), len(scored), regime_fit_kills, len(final),
    )
    return final


def check_fill_and_resolve(signal: dict, candles: list[dict]) -> dict:
    """Chronological, closed-candle, watermark-based scan (never point-in-
    time mark price). Advances signal['watermark_ts'] one closed candle at a
    time so re-runs never re-evaluate already-resolved history and never
    skip a candle. Enforces: no SL/TP evaluation before entry fill (Sec 12).

    The watermark is anchored to each candle's OPEN TIMESTAMP (`c["t"]`, ms),
    never to its position in `candles` -- the list is a fixed-size *rolling*
    window that gets re-fetched fresh every scan, so array positions shift
    underneath a saved index. Seeding the watermark from the signal's
    `created_at` on first use guarantees pre-creation history is never
    evaluated.

    Single-TP resolution: only SL and TP1 are ever checked here. TP2 is
    still computed and shown on the signal message as a suggested further
    target, but it's cosmetic -- never read here, never affects fill/
    resolution. 100% of size is treated as closing at TP1; there is no
    partial exit and no auto-breakeven question (nothing remains open past
    TP1 to reposition)."""
    direction = signal["direction"]
    entry, sl, tp1 = signal["entry"], signal["sl"], signal["tp1"]
    entry_kind = signal["entry_kind"]
    expiry_bars = PENDING_ENTRY_EXPIRY_BARS.get(
        TF_LTF_INTRADAY if signal["combo"] == "intraday" else TF_LTF_SWING, 10)

    watermark_ts = signal.get("watermark_ts")
    if watermark_ts is None:
        created_ms = int(datetime.fromisoformat(signal["created_at"]).timestamp() * 1000)
        watermark_ts = created_ms - 1

    for c in candles:
        if c["t"] <= watermark_ts:
            continue
        watermark_ts = c["t"]
        signal["watermark_ts"] = watermark_ts

        if entry_kind == "market" and not signal.get("entry_filled"):
            signal["entry_filled"] = True

        if not signal.get("entry_filled"):
            if c["l"] <= entry <= c["h"]:
                signal["entry_filled"] = True
            else:
                signal["pending_bars"] = signal.get("pending_bars", 0) + 1
                if signal["pending_bars"] >= expiry_bars:
                    return {"status": "expired", "result": "expired"}
                continue

        hit_sl = (c["l"] <= sl) if direction == "bullish" else (c["h"] >= sl)
        hit_tp1 = (c["h"] >= tp1) if direction == "bullish" else (c["l"] <= tp1)

        if hit_sl and hit_tp1:
            return {"status": "closed", "result": "loss"}
        if hit_sl:
            return {"status": "closed", "result": "loss"}
        if hit_tp1:
            return {"status": "closed", "result": "win"}
    return {"status": "open"}


def _confidence_bucket_realized_wr(engine: Optional[str], confidence: float, state: dict) -> Optional[float]:
    """Realized win rate for this engine's confidence-decile bucket, computed
    from Tier 2 history -- used to detect confidence miscalibration (Sec 13)."""
    if not engine:
        return None
    bucket = int(confidence * 10)
    trades = [r for r in state["tier2"]["trade_log"]
              if r.get("engine") == engine and int(r.get("confidence", 0.5) * 10) == bucket
              and r.get("result") in ("win", "loss")]
    if len(trades) < MIN_SAMPLE_SIZE_CATEGORY:
        return None
    return sum(1 for r in trades if r["result"] == "win") / len(trades)


def diagnose_trade(signal: dict, regime_at_entry: dict, state: dict, result: str) -> str:
    """Closed-set taxonomy classification -- exactly one primary category,
    assigned BEFORE any statistic updates (Sec 13.1)."""
    if result == "win":
        return "genuine_variance"

    engine = signal["engine"]
    regime_label = regime_at_entry.get("label", "ranging")
    if regime_label not in ENGINE_REGIME_FIT.get(engine, set()):
        return "regime_mismatch"

    if not signal.get("mtf_aligned", True):
        return "mtf_conflict_ignored"

    if signal.get("liquidity_pool_hit") and engine != "liquidity_sweep":
        return "chased_swept_liquidity"

    sfp_purity = signal.get("sfp_purity")
    if sfp_purity is not None and sfp_purity < 0.55:
        return "sfp_mss_sequence_violated"

    conf_bucket_wr = _confidence_bucket_realized_wr(signal.get("engine"), signal.get("confidence", 0.5), state)
    if conf_bucket_wr is not None and signal.get("confidence", 0) - conf_bucket_wr > 0.2:
        return "confidence_miscalibration"

    if signal.get("rr1", 0) < RR_TP1_CEIL_SOFT * 0.85:
        return "correct_read_poor_rr"

    if signal.get("filter_margin_thin"):
        return "filter_over_permissiveness"

    if signal.get("buffer_to_risk_ratio", 0) > 0 and signal.get("buffer_to_risk_ratio", 0) < 0.18:
        return "structural_invalidation_too_tight"

    return "genuine_variance"


def apply_forensic_adaptive_response(category: str, signal: dict, state: dict, frozen: bool = False) -> str:
    """One diagnosis, one deterministic route (Sec 13.3), through the same
    bounded/dampened/min-sample-gated update path as every adaptive param.
    Category counters always update for auditability (Sec 13.5); the actual
    parameter mutation is skipped while `frozen` (circuit breaker active,
    Sec 5) so adaptation truly freezes at last-known-good values."""
    t1 = state["tier1"]
    engine = signal["engine"]
    cat_state = t1["forensic_categories"][category]
    cat_state["count"] += 1
    cat_state["recent_trend"] = (cat_state["recent_trend"] + [1])[-50:]

    if frozen:
        return "no_change_circuit_breaker_active"

    if cat_state["count"] < MIN_SAMPLE_SIZE_CATEGORY:
        return "no_change_insufficient_sample"

    if category == "regime_mismatch":
        regime_label = signal.get("regime_at_entry", {}).get("label", "ranging")
        cur = t1["regime_fit_weights"].setdefault(engine, {}).get(regime_label, 1.0)
        new = bounded_update(cur, cur - 0.1, 0.2, 1.0, max_step_frac=0.1)
        t1["regime_fit_weights"][engine][regime_label] = new
        return f"regime_fit_weight[{engine}][{regime_label}] -> {new:.3f}"

    if category == "structural_invalidation_too_tight":
        key = f"{signal['symbol']}:{signal.get('ltf_tf', TF_LTF_INTRADAY)}"
        cur = t1["sl_buffer_percentile"].get(key, 65.0)
        new = bounded_update(cur, cur + 5, 50.0, 90.0, max_step_frac=0.2)
        t1["sl_buffer_percentile"][key] = new
        return f"sl_buffer_percentile[{key}] -> {new:.1f}"

    if category == "chased_swept_liquidity":
        cur = t1["liquidity_sanity_threshold"].get(engine, 0.5)
        new = bounded_update(cur, cur + 0.1, 0.1, 0.9, max_step_frac=0.15)
        t1["liquidity_sanity_threshold"][engine] = new
        return f"liquidity_sanity_threshold[{engine}] -> {new:.3f}"

    if category == "mtf_conflict_ignored":
        cur = t1["mtf_alignment_weight"]
        new = bounded_update(cur, cur + 0.02, 0.05, 0.35, max_step_frac=0.2)
        t1["mtf_alignment_weight"] = new
        return f"mtf_alignment_weight -> {new:.3f}"

    if category == "sfp_mss_sequence_violated":
        cur = t1["sfp_mss_strictness"].get(engine, 0.5)
        new = bounded_update(cur, cur + 0.1, 0.3, 0.95, max_step_frac=0.15)
        t1["sfp_mss_strictness"][engine] = new
        return f"sfp_mss_strictness[{engine}] -> {new:.3f}"

    if category == "correct_read_poor_rr":
        return "no_change_rr_floor_calibration_review"

    if category == "confidence_miscalibration":
        bucket = str(int(signal.get("confidence", 0.5) * 10))
        cal = t1["confidence_calibration"].setdefault(engine, {})
        cur = cal.get(bucket, 0.0)
        new = bounded_update(cur, cur - 0.05, -0.3, 0.3, max_step_frac=0.25)
        cal[bucket] = new
        return f"confidence_calibration[{engine}][{bucket}] -> {new:.3f}"

    if category == "filter_over_permissiveness":
        cur = t1["liquidity_sanity_threshold"].get(engine, 0.5)
        new = bounded_update(cur, cur + 0.08, 0.1, 0.9, max_step_frac=0.15)
        t1["liquidity_sanity_threshold"][engine] = new
        return f"liquidity_sanity_threshold[{engine}] -> {new:.3f} (over-permissive filter)"

    return "no_change_genuine_variance"


def reinforce_win(signal: dict, state: dict, frozen: bool = False) -> str:
    """Sec 13.2: reinforce only the factors genuinely present AND causally
    relevant -- never credit an engine's overall weight for a win driven
    mostly by regime tailwind (checked via regime-fit alignment first).
    Skips the actual mutation while `frozen` (circuit breaker active)."""
    if frozen:
        return "no_change_circuit_breaker_active"
    t1 = state["tier1"]
    engine = signal["engine"]
    regime_label = signal.get("regime_at_entry", {}).get("label", "ranging")
    seg = t1["segments"]["engine"].setdefault(engine, _default_segment_stats())
    if seg["n"] < MIN_SAMPLE_SIZE:
        return "no_change_insufficient_sample"
    if regime_label not in ENGINE_REGIME_FIT.get(engine, set()):
        return "no_change_win_not_causally_attributed_to_engine"
    cur = t1["engine_weights"].get(engine, 1.0)
    new = bounded_update(cur, cur + 0.03, 0.4, 1.8, max_step_frac=0.08)
    t1["engine_weights"][engine] = new
    return f"engine_weights[{engine}] -> {new:.3f}"


def _update_segment(seg: dict, result: str, r_multiple: float, hold_min: float) -> None:
    seg["n"] += 1
    if result == "win":
        seg["wins"] += 1
    elif result == "loss":
        seg["losses"] += 1
    seg["sum_r"] += r_multiple
    seg["sum_hold_min"] += hold_min


def resolve_and_learn(signal: dict, resolution: dict, state: dict) -> None:
    t1, t2 = state["tier1"], state["tier2"]
    result = resolution["result"]

    if resolution["status"] == "expired":
        signal["result"] = "expired"
        t1["totals"]["expired"] += 1
        t2["trade_log"].append({**signal, "resolved_at": datetime.now(timezone.utc).isoformat()})
        return

    if result == "win":
        r_multiple = signal["rr1"]
    else:
        r_multiple = -1.0

    filled_ts = signal.get("filled_ts") or signal.get("watermark_ts", 0)
    hold_min = (signal.get("watermark_ts", 0) - filled_ts) / 60000.0
    hold_min = max(hold_min, 0)

    category = diagnose_trade(signal, signal.get("regime_at_entry", {}), state, result)
    cb_active = t1["circuit_breaker"]["active"]
    if result == "win":
        adaptive_note = reinforce_win(signal, state, frozen=cb_active)
    else:
        adaptive_note = apply_forensic_adaptive_response(category, signal, state, frozen=cb_active)

    for dim, key in (("asset", signal["symbol"]), ("regime", signal.get("regime_at_entry", {}).get("label", "unknown")),
                      ("timeframe", signal["combo"]), ("engine", signal["engine"])):
        seg = t1["segments"][dim].setdefault(key, _default_segment_stats())
        _update_segment(seg, result, r_multiple, hold_min)

    if signal.get("session_anchored"):
        _update_segment(t1["session_anchor_bucket"]["anchored"], result, r_multiple, hold_min)
    else:
        _update_segment(t1["session_anchor_bucket"]["non_anchored"], result, r_multiple, hold_min)
    anchored, non_anchored = t1["session_anchor_bucket"]["anchored"], t1["session_anchor_bucket"]["non_anchored"]
    if anchored["n"] >= MIN_SAMPLE_SIZE and non_anchored["n"] >= MIN_SAMPLE_SIZE:
        wr_a = anchored["wins"] / anchored["n"]
        wr_n = non_anchored["wins"] / non_anchored["n"]
        cur = t1["session_open_weight"]
        target = cur + 0.03 if wr_a > wr_n + 0.05 else cur * 0.9
        t1["session_open_weight"] = bounded_update(cur, target, 0.0, 0.3, max_step_frac=0.2)

    t1["totals"]["signals"] += 1
    if result == "win":
        t1["totals"]["wins"] += 1
    else:
        t1["totals"]["losses"] += 1
    t1["totals"]["sum_r"] += r_multiple
    t1["totals"]["sum_hold_min"] += hold_min

    base = t1["baseline"]
    if base["n"] < MIN_SAMPLE_SIZE:
        base["n"] += 1
        tot = t1["totals"]
        base["win_rate"] = tot["wins"] / max(tot["signals"], 1)
        base["avg_rr"] = tot["sum_r"] / max(tot["signals"], 1)
        resolved = [r for r in t2["trade_log"] if r.get("result") in ("win", "loss")]
        gross_win = sum(r["r_multiple"] for r in resolved if r.get("result") == "win")
        gross_loss = abs(sum(r["r_multiple"] for r in resolved if r.get("result") == "loss"))
        base["profit_factor"] = (gross_win / gross_loss) if gross_loss > 1e-9 else None

    signal["result"] = result
    signal["r_multiple"] = r_multiple
    signal["forensic_category"] = category
    signal["adaptive_response"] = adaptive_note
    t2["trade_log"].append({**signal, "resolved_at": datetime.now(timezone.utc).isoformat()})
    evaluate_circuit_breaker(state)


def evaluate_circuit_breaker(state: dict) -> Optional[str]:
    """Sec 5 live-performance circuit breaker. Dual-metric: trips on EITHER a
    material win-rate drop OR a material profit-factor drop vs baseline, so a
    stretch where win rate holds but average losses grow relative to average
    wins still gets caught. Recovery requires BOTH metrics back at/above
    baseline -- deliberately stricter than the trip condition so one lucky
    trade after a bad stretch can't flip it back off."""
    t1 = state["tier1"]
    base = t1["baseline"]
    cb = t1["circuit_breaker"]
    resolved = [r for r in state["tier2"]["trade_log"] if r.get("result") in ("win", "loss")]
    recent = resolved[-CIRCUIT_BREAKER_WINDOW:]
    if base["win_rate"] is None or len(recent) < CIRCUIT_BREAKER_WINDOW:
        return None
    rolling_wr = sum(1 for r in recent if r["result"] == "win") / len(recent)
    gains = sum(r["r_multiple"] for r in recent if r["r_multiple"] > 0)
    losses = abs(sum(r["r_multiple"] for r in recent if r["r_multiple"] < 0)) or 1e-9
    rolling_pf = gains / losses

    wr_trip = base["win_rate"] - rolling_wr >= CIRCUIT_BREAKER_WIN_RATE_DROP
    pf_trip = (base["profit_factor"] is not None and
               rolling_pf <= base["profit_factor"] * (1 - CIRCUIT_BREAKER_PF_DROP_FRAC))
    materially_below = wr_trip or pf_trip

    if not cb["active"] and materially_below:
        cb["active"] = True
        cb["since"] = datetime.now(timezone.utc).isoformat()
        pf_baseline_txt = f"{base['profit_factor']:.2f}" if base["profit_factor"] is not None else "n/a (no baseline losses)"
        cb["reason"] = (f"win_rate={rolling_wr:.2%} (baseline {base['win_rate']:.2%}), "
                         f"pf={rolling_pf:.2f} (baseline {pf_baseline_txt})")
        return "tripped"
    pf_recovered = base["profit_factor"] is None or rolling_pf >= base["profit_factor"]
    if cb["active"] and rolling_wr >= base["win_rate"] and pf_recovered:
        cb["active"] = False
        cb["since"] = None
        cb["reason"] = None
        return "recovered"
    return None


def _display_name(identifier: str) -> str:
    """Sec 17 mandatory: no raw underscores in any user-facing text -- clean
    Title Case with spaces, applied at the formatting layer for every message."""
    return identifier.replace("_", " ").replace("-", " ").title()


def _ticker(symbol: str) -> str:
    """Bare uppercase ticker for message headers, e.g. 'BNBUSDT' -> 'BNB'."""
    return symbol.replace("USDT", "").replace("USD", "").upper()


def _expiry_hours(combo: str) -> float:
    tf = TF_LTF_INTRADAY if combo == "intraday" else TF_LTF_SWING
    bars = PENDING_ENTRY_EXPIRY_BARS.get(tf, 10)
    return bars * (_interval_to_ms(tf) / 3_600_000)


def format_price(price: float) -> str:
    if price >= 100:
        return f"{price:.2f}"
    if price >= 1:
        return f"{price:.4f}"
    return f"{price:.6f}"


def send_telegram(text: str, reply_to: Optional[int] = None, photo_path: Optional[str] = None) -> Optional[int]:
    base = f"https://api.telegram.org/bot{TG_BOT_TOKEN}"
    try:
        if photo_path and os.path.exists(photo_path):
            with open(photo_path, "rb") as f:
                resp = requests.post(f"{base}/sendPhoto", data={
                    "chat_id": TG_CHAT_ID, "caption": text, "parse_mode": "Markdown",
                    **({"reply_to_message_id": reply_to} if reply_to else {}),
                }, files={"photo": f}, timeout=15)
        else:
            payload = {"chat_id": TG_CHAT_ID, "text": text, "parse_mode": "Markdown"}
            if reply_to:
                payload["reply_to_message_id"] = reply_to
            resp = requests.post(f"{base}/sendMessage", json=payload, timeout=15)
        resp.raise_for_status()
        return resp.json().get("result", {}).get("message_id")
    except requests.RequestException:
        log.exception("Telegram send failed")
        return None


def format_signal_message(cand: Candidate, tier: str, regime_label: str) -> str:
    direction_tag = "LONG \U0001F7E2" if cand.direction == "bullish" else "SHORT \U0001F534"
    lines = [
        f"*{ENGINE_NAME}* v{__version__}",
        f"*{_ticker(cand.symbol)}* — {direction_tag}",
        "",
        f"Setup: {_display_name(cand.engine)}  |  Tier: {tier}",
        f"Regime: {_display_name(regime_label)}  |  Confidence: {cand.confidence:.0%}",
        "",
        f"Entry: `{format_price(cand.entry)}`",
        f"SL: `{format_price(cand.sl)}`",
        f"TP1: `{format_price(cand.tp1)}`",
        f"TP2: `{format_price(cand.tp2)}`",
        "",
        f"RR: {cand.rr1:.2f} / {cand.rr2:.2f}",
        "",
        "Confluences: " + ", ".join(_display_name(c) for c in cand.confluences),
        "_TP2 is a suggested further target only — position closes in full at TP1._",
    ]
    if cand.entry_kind == "pending":
        lines.append(f"Pending — expires in {_expiry_hours(cand.combo):.1f}h")
    return "\n".join(lines)


def format_outcome_message(signal: dict, resolution: dict) -> str:
    if resolution["status"] == "expired":
        return (f"{EMOJI_EXPIRED} *{ENGINE_NAME}* — {_display_name(signal['symbol'])} Expired (No Fill)\n\n"
                f"Entry never filled within its pending window.")
    if resolution["result"] == "win":
        return (f"{EMOJI_WIN} *{ENGINE_NAME}* — {_display_name(signal['symbol'])} TP1 Hit — Win\n\n"
                f"Realized: {signal.get('r_multiple', 0):.2f}R\n"
                f"SL: `{format_price(signal['sl'])}`\n"
                f"TP1: `{format_price(signal['tp1'])}`\n\n"
                f"Position closed in full at TP1. Nothing remains open on this signal.")
    return (f"{EMOJI_LOSS} *{ENGINE_NAME}* — {_display_name(signal['symbol'])} SL Hit — Loss\n\n"
            f"SL: `{format_price(signal['sl'])}`")


def send_daily_summary(state: dict) -> None:
    t1 = state["tier1"]
    tot = t1["totals"]
    n = max(tot["signals"], 1)
    win_rate = tot["wins"] / n
    log_entries = [r for r in state["tier2"]["trade_log"] if r.get("result") in ("win", "loss")]
    gross_win = sum(r["r_multiple"] for r in log_entries if r.get("result") == "win")
    gross_loss = abs(sum(r["r_multiple"] for r in log_entries if r.get("result") == "loss"))
    profit_factor = (gross_win / gross_loss) if gross_loss > 1e-9 else float("inf")
    avg_rr = tot["sum_r"] / n
    avg_hold = tot["sum_hold_min"] / n

    lines = [
        f"*{ENGINE_NAME}* `{__version__}` — Daily Summary",
        "",
        f"Total Signals: {tot['signals']}   Expired: {tot['expired']}",
        f"Wins: {tot['wins']}   Losses: {tot['losses']}",
        f"Win Rate: {win_rate:.1%}",
        f"Profit Factor: {profit_factor:.2f}" if profit_factor != float("inf") else "Profit Factor: inf",
        f"Average RR: {avg_rr:.2f}",
        f"Average Hold Time: {avg_hold:.0f} min",
        "",
        "By Regime:",
    ]
    for regime, seg in sorted(t1["segments"]["regime"].items()):
        if seg["n"] == 0:
            continue
        wr = seg["wins"] / seg["n"]
        lines.append(f"  {_display_name(regime)}: {seg['n']} trades, {wr:.0%} WR")
    lines.append("")
    lines.append("By Engine:")
    for eng, seg in sorted(t1["segments"]["engine"].items()):
        if seg["n"] == 0:
            continue
        wr = seg["wins"] / seg["n"]
        lines.append(f"  {_display_name(eng)}: {seg['n']} trades, {wr:.0%} WR, weight {t1['engine_weights'].get(eng, 1.0):.2f}")

    if log_entries:
        best = max(log_entries, key=lambda r: r.get("r_multiple", -999))
        worst = min(log_entries, key=lambda r: r.get("r_multiple", 999))
        lines.append("")
        lines.append(f"Best Setup: {_display_name(best['symbol'])} ({_display_name(best['engine'])}), {best.get('r_multiple', 0):.2f}R")
        lines.append(f"Worst Setup: {_display_name(worst['symbol'])} ({_display_name(worst['engine'])}), {worst.get('r_multiple', 0):.2f}R")

    lines.append("")
    lines.append("Forensic Category Breakdown:")
    for cat, cs in t1["forensic_categories"].items():
        if cs["count"] == 0:
            continue
        trend = sum(cs["recent_trend"][-10:])
        lines.append(f"  {_display_name(cat)}: {cs['count']} total, {trend}/10 recent")

    anchored, non_anchored = t1["session_anchor_bucket"]["anchored"], t1["session_anchor_bucket"]["non_anchored"]
    lines.append("")
    lines.append("Session-Anchored SFP Bucket:")
    if anchored["n"]:
        lines.append(f"  Anchored: {anchored['n']} trades, {anchored['wins']/anchored['n']:.0%} WR")
    if non_anchored["n"]:
        lines.append(f"  Non Anchored: {non_anchored['n']} trades, {non_anchored['wins']/non_anchored['n']:.0%} WR")

    cb = t1["circuit_breaker"]
    lines.append("")
    lines.append(f"Circuit Breaker: {'ACTIVE — adaptation frozen' if cb['active'] else 'Inactive'}")

    send_telegram("\n".join(lines), photo_path=REACTION_IMAGE_PATH)


def monitor_active_signals(state: dict, hl: HyperliquidClient) -> None:
    t2 = state["tier2"]
    still_active = []
    for signal in t2["active_signals"]:
        tf = TF_LTF_INTRADAY if signal["combo"] == "intraday" else TF_LTF_SWING
        candles = hl.candles(signal["symbol"], tf, TF_BARS[tf])
        if not candles:
            still_active.append(signal)
            continue
        was_filled = signal.get("entry_filled", False)
        resolution = check_fill_and_resolve(signal, candles)

        if not was_filled and signal.get("entry_filled"):
            signal["filled_ts"] = signal.get("watermark_ts", 0)

        if resolution["status"] == "open":
            still_active.append(signal)
            continue

        resolve_and_learn(signal, resolution, state)
        send_telegram(format_outcome_message(signal, resolution), reply_to=signal.get("tg_message_id"))

    t2["active_signals"] = still_active


def run_scan(hl: HyperliquidClient, store: StateStore, cache_store: CandleCacheStore) -> None:
    state = store.load()
    cache = cache_store.load()
    hl.cache = cache

    try:
        monitor_active_signals(state, hl)

        marks = hl.mark_prices()
        snaps: dict[str, SymbolSnapshot] = {}
        with ThreadPoolExecutor(max_workers=SCAN_WORKERS) as ex:
            futures = {ex.submit(collect_snapshot, hl, sym, marks.get(sym, 0.0)): sym for sym in WATCHLIST}
            for fut in as_completed(futures):
                sym = futures[fut]
                try:
                    snap = fut.result()
                    if snap:
                        snaps[sym] = snap
                except Exception:
                    log.exception("snapshot failed for %s", sym)

        macro_snap = snaps.get(MACRO_ASSET)
        macro_view = macro_snap.views.get("1d") if macro_snap else None
        regime = compute_regime_vector(macro_view, snaps)
        regime_dict = {**asdict(regime), "label": regime.label()}
        log.info(
            "regime=%s macro_bias=%.3f vol_pctile=%.1f trend_strength=%.1f noise=%.2f breadth=%.2f",
            regime_dict["label"], regime.macro_bias, regime.volatility_pctile,
            regime.trend_strength, regime.noise_index, regime.breadth,
        )

        prev_cb_active = state["tier1"]["circuit_breaker"]["active"]

        all_candidates: list[Candidate] = []
        for sym, snap in snaps.items():
            all_candidates.extend(run_ensemble(snap, state, regime_dict["label"]))

        if state["tier1"]["circuit_breaker"]["active"]:
            log.info("circuit breaker active -- signal generation continues, adaptation frozen")

        ranked = decision_engine_rank(all_candidates, regime, snaps, state, state["tier2"]["active_signals"])

        for cand in ranked:
            tier = next((c.split(":", 1)[1] for c in cand.confluences if c.startswith("tier:")), "B")
            msg_id = send_telegram(format_signal_message(cand, tier, regime_dict["label"]))
            sig = cand.to_dict()
            sig["regime_at_entry"] = regime_dict
            sig["ltf_tf"] = TF_LTF_INTRADAY if cand.combo == "intraday" else TF_LTF_SWING
            sig["tg_message_id"] = msg_id
            sig["filled_ts"] = None
            state["tier2"]["active_signals"].append(sig)

        cb_now_active = state["tier1"]["circuit_breaker"]["active"]
        if cb_now_active and not prev_cb_active:
            send_telegram(f"{EMOJI_CIRCUIT_BREAKER} *{ENGINE_NAME}* Circuit Breaker Tripped\n\n"
                           f"{state['tier1']['circuit_breaker']['reason']}\n"
                           f"Automatic parameter adaptation is frozen at last-known-good values. "
                           f"Signal generation continues unaffected.")
        elif not cb_now_active and prev_cb_active:
            send_telegram(f"{EMOJI_RECOVERED} *{ENGINE_NAME}* Circuit Breaker Cleared\n\n"
                           f"Live performance has recovered to baseline. Adaptation resumed.")

        now = datetime.now(timezone.utc)
        last_summary = state["tier1"].get("last_daily_summary_date")
        if now.hour == 8 and last_summary != now.date().isoformat():
            send_daily_summary(state)
            state["tier1"]["last_daily_summary_date"] = now.date().isoformat()

        store.prune_tier2(state)
    finally:
        cache_store.save(hl.cache)
        store.save(state)


def main() -> None:
    log.info("%s v%s starting scan", ENGINE_NAME, __version__)
    store = StateStore(STATE_FILE)
    cache_store = CandleCacheStore(CANDLE_CACHE_FILE)
    hl = HyperliquidClient()
    try:
        run_scan(hl, store, cache_store)
    except Exception:
        log.exception("scan failed")
        raise
    log.info("scan complete")


if __name__ == "__main__":
    main()
