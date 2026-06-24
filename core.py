import os, json, time, math, random, threading, requests
import signal as os_signal
import sys
import copy
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

__version__ = "16.0.0"    # [v15.5.5 SUMMARY] Ported the dynamic pairwise correlation
                            # clustering / union-find system from v15.8.1 (Fix-33) and wired
                            # it into deduplicate_correlated() as the live correlated-exposure
                            # control, replacing the static, hand-maintained CORR_GROUPS
                            # dict. See compute_pairwise_correlation_matrix(),
                            # cluster_by_correlation(), group_of_dynamic() and the
                            # [v15.5.5] block in main(). NOTE: in v15.8.1 itself this
                            # machinery was diagnostic-only (never consulted by
                            # deduplicate_correlated()) — see the audit notes delivered
                            # alongside this file for why, and what changed here.
                            # Everything below this point is unmodified v15.5.4.0 logic.
                            # [v15.5.4.0 SUMMARY] This pass: Fix-40 (gap-covering candle
                            # fetch for active-signal tracking), Fix-41 (short-side RS
                            # exemption in BTC regime filter), Fix-42 (relaxed daily-ADX
                            # gate for PULL signals), Fix-43 (vol_score_ok fail-closed on
                            # vm15==0), Fix-44 (explicit category tags for the penalty
                            # priority cap), Fix-45 (crowded+strong-RS combo penalty for
                            # shorts in breadth adjustment), Fix-46 (daily ADX routed
                            # through the indicator cache), Fix-47 (soft positive-score
                            # cap + widened win-rate score buckets).
                            # [Fix-15] Top-10 ROI fixes from full audit:
                            # BUG-C1 atr_pct=0 in scoring, BUG-C2 penalty cap priority inversion,
                            # BUG-H4 SR clearance now PULL-only, BUG-H1 short proximity RS gate inverted,
                            # BUG-H3 funding double-penalty consolidated, BUG-H2 PULL vol score corrected,
                            # TG-3 spread_history persisted to state, RISK-3 MIN_RR kept at 1.0 (reverted by request),
                            # PERF-1 bollinger called once, Code dead constants/function removed.
                            # [Fix-40] check_active_signals(): candle fetch window for an active
                            # signal is now widened dynamically to cover any gap since
                            # last_processed_candle_ts (downtime/scan-delay), instead of being
                            # silently truncated to the last N_15M bars. Unreconstructable gaps
                            # (> MAX_GAP_FETCH_15M_BARS) resolve as "expired_gap" rather than
                            # "expired" so they don't pollute win-rate stats with a fake outcome.
                            # [Fix-41] check_btc_regime_filter(): added the mirrored RS exemption
                            # to the short/bullish-regime branch (was long-only), using the
                            # existing RS_BEARISH_REGIME_EXEMPT_PCT constant for symmetry.
                            # [Fix-42] Added DAILY_ADX_REQUIRED_FOR_PULL (default False).
                            # _detect_raw_signals() now gates PULL signals on daily_adx_ok_pull
                            # instead of daily_adx_ok; BREAK signals are unchanged.
                            # [Fix-43] vol_score_ok / vol_score_ok_pull now fail closed
                            # (False, not True) when the 15m volume moving average is 0.
                            # [Fix-44] Penalty-stacking cap in _apply_scoring_and_filters() now
                            # tags each score_adjustments entry with an explicit category
                            # ("btc_regime"/"oi_confirmation"/"exhaustion"/"rs_negative"/"secondary")
                            # instead of matching free-text label substrings.
                            # [Fix-45] apply_breadth_adjustment(): added the mirrored "crowded +
                            # strong RS" -2 combo penalty to the short branch (was long-only).
                            # [Fix-46] _compute_signal_indicators(): daily ADX now routed through
                            # get_cached_indicators(symbol, "1d", candles_d) instead of calling
                            # adx_dmi() directly every scan. Self-test extended to cover "1d".
                            # [Fix-47] Added MAX_POSITIVE_ADJUSTMENTS=6 soft cap on stacked bonus
                            # adjustments in _apply_scoring_and_filters() (mirrors the existing
                            # negative cap). Widened compute_win_rates()'s by_score bucket range
                            # from range(4,8) to range(4, 6+MAX_POSITIVE_ADJUSTMENTS+1) so no
                            # achievable final score is left out of by-score win-rate aggregation.

_FF_TZ = ZoneInfo("America/New_York")
OI_EXPECTED_INTERVAL_S: float = 15 * 60

# ── CONFIG ───────────────────────────────────────────────────
# [P0-6] Safe env var handling — no more KeyError crash at import
TG_BOT_TOKEN = os.getenv("TG_BOT_TOKEN")
TG_CHAT_ID   = os.getenv("TG_CHAT_ID")
if not TG_BOT_TOKEN:
    raise RuntimeError("TG_BOT_TOKEN environment variable is required")
if not TG_CHAT_ID:
    raise RuntimeError("TG_CHAT_ID environment variable is required")

STATE_FILE            = "state.json"
SCAN_WORKERS          = int(os.getenv("SCAN_WORKERS", "2"))
HL_MIN_INTERVAL_S     = float(os.getenv("HL_MIN_INTERVAL_S", "0.18"))
HL_MIN_INTERVAL_MAX_S = float(os.getenv("HL_MIN_INTERVAL_MAX_S", "0.60"))
HL_TF_WORKERS         = int(os.getenv("HL_TF_WORKERS", "1"))

_hl_request_lock    = threading.Lock()
_hl_last_request_ts = 0.0
_hl_min_interval_s  = HL_MIN_INTERVAL_S
_hl_consecutive_successes = 0

_hl_session = requests.Session()

# ── HARDCODED WATCHLIST ───────────────────────────────────────
WATCHLIST = [
    "BTCUSDT", "ETHUSDT", "HYPEUSDT", "ZECUSDT", "NEARUSDT",
    "ONDOUSDT", "SUIUSDT", "PENGUUSDT", "BNBUSDT", "SOLUSDT",
    "TRXUSDT", "BCHUSDT", "DOGEUSDT", "ADAUSDT", "DOTUSDT",
    "TAOUSDT", "AVAXUSDT", "LINKUSDT", "AAVEUSDT", "XRPUSDT",
    "XLMUSDT", "UNIUSDT", "LTCUSDT", "APTUSDT", "PENDLEUSDT",
]

# [v15.5.5] The static, hand-maintained CORR_GROUPS dict that used to live here
# has been removed. Correlated-exposure grouping is now computed dynamically
# every scan from measured pairwise return correlation — see
# compute_pairwise_correlation_matrix() / cluster_by_correlation() /
# group_of_dynamic() below, and the clustering step in main()'s Phase 1.

# ── INDICATOR LENGTHS ────────────────────────────────────────
FAST_LEN  = 21
SLOW_LEN  = 50
TREND_LEN = 200
RSI_LEN   = 14
ATR_LEN   = 14
ADX_LEN   = 14
BB_LEN    = 20
BB_MULT   = 2.0
VOL_LEN   = 20
OBV_LEN   = 10

# ── RISK / SCORE ─────────────────────────────────────────────
MIN_SCORE            = 4
MAX_SIGNALS_PER_SCAN = 4  # IMP-S17-5 — increased by 1 (was 3)
MAX_SIGNAL_HISTORY   = 2000
# [Fix-7] MIN_OI_USD kept at 500K per "Implementation All except MIN_OI_USD"
MIN_OI_USD: float = 500_000.0

# [Fix-9] Penalty stacking cap — prevents over-filtering from double-counted risks
MAX_NEGATIVE_ADJUSTMENTS: int = 3

# [Fix-47] Soft cap on stacked positive (bonus) adjustments, mirroring
# MAX_NEGATIVE_ADJUSTMENTS. Without this, bonuses (divergence +2, RSI confluence
# +1, D200 +1, S/R proximity +1, funding tailwind +1, OI acceleration +1,
# false-breakout +1, etc.) could stack past 7, beyond what compute_win_rates()'s
# by_score bucketing covered — losing granularity exactly where high-conviction
# trades live. 6 was chosen to roughly match the positive-adjustment headroom
# seen in practice without suppressing genuinely strong setups (most real
# signals stack 2-4 bonuses; 6 still allows an unusually strong confluence of
# signals through largely uncapped while still giving compute_win_rates() a
# bounded score range to bucket against).
MAX_POSITIVE_ADJUSTMENTS: int = 6

# [Risk-31] Maximum concurrent active signals cap (audit #31, related to #32)
# [Fix-1] Raised from 8 → 12: Risk is managed by leverage scaling, not signal count
MAX_CONCURRENT_ACTIVE_SIGNALS: int = 12

# ── HIGHER-TIMEFRAME DIVERGENCE CHECK ─────────────────────
USE_1H_RSI_DIVERGENCE: bool = True
DIVERGENCE_LOOKBACK: int = 20  # [Logic-21] was 10 — increased to 20 to capture divergences forming over 20+ bars
# [Fix-10] Increased from 1 → 2: 1H RSI divergence is a rare, high-conviction signal
DIVERGENCE_BONUS: int = 2

# ── FUNDING RATE AS CARRY METRIC ──────────────────────────
USE_FUNDING_CARRY: bool = True
FUNDING_CARRY_POSITIVE_THRESHOLD: float = 0.0005
FUNDING_CARRY_NEGATIVE_THRESHOLD: float = -0.0005
FUNDING_CARRY_BONUS: int = 1

# ── DYNAMIC MAX_SIGNALS_PER_SCAN ───────────────────────────
USE_DYNAMIC_MAX_SIGNALS: bool = True
# [Fix-5] Increased caps by 1 each: in strong trends, 5 signals across 25 coins is restrictive
MAX_SIGNALS_BULL_TREND: int = 6  # IMP-S17-5 — increased by 1 (was 5)
MAX_SIGNALS_DEFAULT: int = 4     # IMP-S17-5 — increased by 1 (was 3)
BREADTH_BULL_THRESHOLD: float = 0.70

# ── FALSE BREAKOUT PATTERN DETECTION ───────────────────────
USE_FALSE_BREAKOUT_DETECTION: bool = True
FALSE_BREAKOUT_LOOKBACK_BARS: int = 12
FALSE_BREAKOUT_BONUS: int = 1

# ── FILTERS ──────────────────────────────────────────────────
ADX_BREAK_GATE  = 25.0
ADX_SCORE_MIN   = 20.0

RSI_BREAK_LONG_MIN  = 45.0;  RSI_BREAK_LONG_MAX  = 70.0  # IMP-S15-7 — tightened from 75 to remove top-buying-risk tail; Catches breakouts launching from neutral RSI territory
RSI_BREAK_SHORT_MIN = 30.0;  RSI_BREAK_SHORT_MAX = 55.0  # IMP-S15-7 — mirror tightening (100-70); Symmetric
RSI_PULL_LONG_MIN   = 40.0;  RSI_PULL_LONG_MAX   = 58.0  # IMP-S17-3 — widened from [42,55]; RSI < 40 = breakdown signature, not pullback; RSI > 58 = barely pulled back, poor R:R
RSI_PULL_SHORT_MIN  = 42.0;  RSI_PULL_SHORT_MAX  = 60.0  # IMP-S17-3 — mirror widening from [45,58]
RSI_1H_PULL_LONG_MAX  = 70.0
RSI_1H_PULL_SHORT_MIN = 30.0

VOL_SCORE_MULT  = 1.0  # IMP-S15-9 — raised from 0.75x; BREAK now requires at least average volume as a hard gate (also used as PULL low-vol-bonus reference below)
MAX_ATR_PCT     = 10.0
MIN_ATR_PCT     = 0.2
WICK_FILTER     = 0.45
RANGE_PCT_BREAK = 0.20
PULL_ZONE_MULT  = 0.25
PULL_TOUCH_LOOKBACK   = 5  # IMP-S16-5 — 3→5 bars (45 min→75 min): captures slow EMA-dip pullbacks (supersedes [PATCH-7b]'s 5→3 narrowing)
PULL_RECOVER_ATR_MULT_TREND: float = 0.30  # Catches entries closer to actual EMA touch
PULL_RECOVER_ATR_MULT_MIXED: float = 0.25  # [PATCH-7c] 0.10→0.25: same ratio scaling as trend
TREND_HOLD_BARS = 2
# BREAK-specific trend hold (separate from PULL)
TREND_HOLD_BARS_BREAK: int = 1   # Only 1 bar of 4H EMA alignment required for BREAK
TREND_HOLD_BARS_PULL:  int = 2   # Keep 2 bars for PULL (confirmed trend needed)

# 4H momentum quality gate for PULL
MIN_4H_SPREAD_ATR_MULT: float = 0.20  # IMP-S17-8 — lowered from 0.30; allows earlier entries into nascent trends. 4H EMA spread must be >= 0.2x 4H ATR

# 4H exhaustion suppressor for BREAK
EXHAUSTION_SPREAD_LOOKBACK: int = 3   # Bars back to compare spread for BREAK exhaustion check

# FIX-D20: EARLY_BREAK_VOL_SURGE and EARLY_BREAK_SCORE_ADJ removed — dead constants.
# Restore when _check_early_break() is re-implemented with live candle fetch.
# EARLY_BREAK_VOL_SURGE: float = 1.8
# EARLY_BREAK_SCORE_ADJ: int = 0
USE_EXHAUSTION_SHORT:       bool = True
EXHAUSTION_SHORT_SCORE_ADJ: int  = -1
USE_EXHAUSTION_LONG:        bool = True
EXHAUSTION_LONG_SCORE_ADJ:  int  = -1
# [New] Pullback alignment mode — 4H trend holding, 1H temporarily against it.
# PULL-only (never BREAK). Distinct from "exhaustion" (which requires the 4H
# trend to be breaking down). See build_pullback_alignment_mode.md for rationale.
USE_PULLBACK_ALIGNMENT:     bool = True
PULLBACK_SCORE_ADJ:         int  = 0    # Blanket penalty removed; quality controlled via RSI (E3)
PULLBACK_PREMIUM_SCORE_ADJ: int = 1    # Bonus for Tier A Premium Pullback setups
USE_ROLLING_VWAP  = True
# NOTE: USE_ROLLING_VWAP=True uses daily_vwap() (session-anchored, UTC midnight reset).
# The rolling_vwap() function is unused. ROLLING_VWAP_LEN was removed as dead config.

USE_D200_FILTER   = True
D200_SOFT_ADJ     = 1

USE_DAILY_ADX     = True
MIN_DAILY_ADX     = 18.0
# [Fix-42] PULL is a 4H/1H construct (a dip inside an already-held 4H trend);
# requiring daily-timeframe trend strength on top of that is overly strict and
# was the most likely cause of unexpected signal droughts during healthy but
# low-daily-volatility consolidation phases. Default False = PULL signals are
# not gated on daily ADX; BREAK signals keep the stricter daily_adx_ok gate.
DAILY_ADX_REQUIRED_FOR_PULL: bool = False
PULL_REQUIRES_4H  = True
# Per-symbol or per-BTC-regime-label override for PULL_REQUIRES_4H.
# Keys can be either an exact symbol (e.g. "BTCUSDT") or a substring that
# matches against the current BTC regime label. Exact symbol match takes
# precedence over a regime-label substring match. Empty by default — this
# is a no-op until a reviewer populates it; PULL_REQUIRES_4H above remains
# the global fallback.
PULL_REQUIRES_4H_OVERRIDE: dict[str, bool] = {}

# ── ACCURACY FILTERS ──────────────────────────────────────────
FUNDING_SUPPRESS_EXTREME: float = 0.0010
# [Fix-8] Tightened from 0.30 → 0.20: Regime-aware TP/SL (Feature-50) now handles S/R adaptation
SR_CLEARANCE_ATR_MULT: float    = 0.20  # Used for BREAK and general S/R logic
SR_CLEARANCE_ATR_MULT_PULL: float = 0.15  # Relaxed for PULL (was suppressing valid entries near structure)
SUPPORT_PROXIMITY_ATR: float    = 0.75

# ── BREAK / PULL QUALITY REFINEMENTS ─────────────────────────
BREAK_OI_FLAT_VOL_THRESHOLD: float = 1.5
FUNDING_PULL_WARN_MIN: float        = 0.0005

# ── OI TREND ─────────────────────────────────────────────────
OI_HISTORY_DEPTH: int        = 6
OI_CHANGE_THRESHOLD_PCT: float = 1.0
OI_STALE_CUTOFF_S: float = 45 * 60  # 45 minutes

# ── BREAKOUT VOLUME ───────────────────────────────────────────
BREAK_VOL_MULT: float = 1.2
BREAK_VOL_ACCEL_BARS: int = 2

# ── RELATIVE STRENGTH ─────────────────────────────────────────
RS_TOP_PERCENTILE: float    = 0.20
RS_BOTTOM_PERCENTILE: float = 0.20
# [Fix-6] Loosened from -4.0 → -6.0: -4% RS vs BTC is common for coins with sector-specific catalysts
RS_BREAK_HARD_GATE_PCT: float = -6.0
RS_BREAK_HARD_GATE_PENALTY: int = -3
RS_BREAK_SOFT_PERCENTILE: float = 0.25

# ── MARKET BREADTH ────────────────────────────────────────────
BREADTH_WEAK_LONG_THRESHOLD:  float = 0.20
BREADTH_WEAK_SHORT_THRESHOLD: float = 0.80
BREADTH_CROWDED_LONG_THRESHOLD: float = 0.75
BREADTH_CROWDED_LONG_THRESHOLD_MIXED: float = 0.80
BREADTH_EXTREME_LONG_THRESHOLD: float = 0.90
BREADTH_EXTREME_SHORT_THRESHOLD: float = 0.10
BREADTH_RS_NEGATIVE_THRESH: float  = 0.0

# ── PULL QUALITY FLOORS ───────────────────────────────────────
PULL_VOL_FLOOR: float          = 0.40
PULL_VOL_FLOOR_OVERBOUGHT: float  = 0.50
PULL_VOL_OVERBOUGHT_BREADTH: float = 0.80
# [Fix-4] Shortened from 1800 → 900: 15min is sufficient — cooldown already blocks same symbol/direction
PULL_REENTRY_COOLDOWN_S: int   = 900

# ── ACCURACY FILTERS ──────────────────────────────────────────
PROXIMITY_RS_MIN: float = -5.0
TP1_WALL_MIN_CLEARANCE: float = 0.40

# ── PULL LIMIT-ORDER ZONE ────────────────────────────────────
PULL_LIMIT_TRANCHE_PCT: float  = 0.50
PULL_LIMIT_MAX_ATR_DIST: float = 1.50

# ── SPREAD / LIQUIDITY AWARENESS ─────────────────────────
SPREAD_WARN_PCT: float     = 0.20
SPREAD_SUPPRESS_PCT: float = 0.40
# [Risk-36] Baseline exempt set — dynamic exemption also applied at runtime
SPREAD_EXEMPT: set[str] = {
    "BTCUSDT", "ETHUSDT", "SOLUSDT", "BNBUSDT",
    "XRPUSDT", "ADAUSDT", "DOGEUSDT",
}
# [Risk-36] Dynamic spread exemption: if avg spread over last N scans is low, exempt
SPREAD_DYNAMIC_HISTORY_LEN: int = 10
SPREAD_DYNAMIC_AVG_THRESHOLD: float = 0.15  # 0.10 -> 0.15

# ── HISTORICAL WIN RATE ───────────────────────────────────────
WIN_RATE_MIN_SAMPLE: int    = 20
WIN_RATE_HIGH_THRESH: float = 0.65
WIN_RATE_LOW_THRESH: float  = 0.45
WIN_RATE_MIN_SAMPLE_FOR_ADJ: int = 100  # IMP-S17-9 — raised from 80; require more samples before trusting WR adjustment
WIN_RATE_LOOKBACK_DAYS:  int   = 30
WIN_RATE_RECENT_DAYS:    int   = 7
WIN_RATE_RECENT_WEIGHT:  float = 2.0  # [P0-2] Now actually used
WIN_RATE_STALE_DAYS: int = 14

# ── OI SCALE CAP ──────────────────────────────────────────────
MAX_OI_SCALE: float = 3.0

# ── MINIMUM R:R RATIO ─────────────────────────────────────────
MIN_RR_RATIO: float = 1.0

# ── ATR FALLBACK ──────────────────────────────────────────────
ATR_FALLBACK_PCT: float = 0.30

# ── ECONOMIC CALENDAR ─────────────────────────────────────────
MACRO_WINDOW_BEFORE_MINS: int   = 60
MACRO_WINDOW_AFTER_MINS:  int   = 30
MACRO_HIGH_ATR_SUPPRESS_PCT: float = 3.0
MACRO_CACHE_TTL_S: int          = 3600

# [Logic-22] Symbol-relative macro ATR threshold multiplier
# If symbol's ATR percentile > 70%, require higher ATR to suppress (symbol is naturally volatile)
MACRO_ATR_PCTILE_HIGH: float = 0.70
MACRO_ATR_PCTILE_HIGH_MULT: float = 1.5

# ── CANDLE COUNTS ─────────────────────────────────────────────
N_15M = 300
N_1H  = 200
N_4H  = 200
N_1D  = 600

# ── REACTION SETTINGS ─────────────────────────────────────────
REACT_TP1           = "🔥"
REACT_TP2           = "🏆"
REACT_SL            = "😭"
SIGNAL_MAX_AGE_BARS = 48
# [Fix-40] Cap on how many 15m candles we'll request to cover a downtime/scan-delay gap
# when tracking an active signal. Below this, the fetch window is widened dynamically to
# guarantee no candles between last_processed_candle_ts and now are skipped. Above this,
# full historical reconstruction is not attempted and the signal is resolved as
# "expired_gap" instead of being silently force-resolved as "expired".
MAX_GAP_FETCH_15M_BARS = 2000

# ── HYPERLIQUID ENDPOINT ──────────────────────────────────────
HL_INFO_URL = "https://api.hyperliquid.xyz/info"

INTERVAL_MS = {
    "15m": 15 * 60 * 1000,
    "1h":  60 * 60 * 1000,
    "4h":  4  * 60 * 60 * 1000,
    "1d":  24 * 60 * 60 * 1000,
}

# v12 UPGRADE CONSTANTS
PULL_BODY_MIN_RATIO: float = 0.20
H4_STALE_AGE_FRACTION: float = 0.85
H4_STALE_SPREAD_MIN:   float = 0.15
OI_ACCEL_MIN_THRESHOLD: float = 1.0
OI_SCORE_CAP: int              = 2
SESSION_DEAD_ZONE_START_UTC: int = 3
SESSION_DEAD_ZONE_END_UTC:   int = 6
SESSION_LOW_ATR_PERCENTILE:  float = 0.10
TP1_MULT_BREAK: float = 1.0
TP2_MULT_BREAK: float = 2.5
SL_MULT_BREAK:  float = 0.85
TP1_MULT_PULL:  float = 1.0
TP2_MULT_PULL:  float = 2.0
SL_MULT_PULL:   float = 0.85
HIGH_ATR_THRESHOLD: float = 3.0
SL_HIGH_ATR_MULT:   float = 0.90
ATR_HIST_DEPTH:     int   = 48
ATR_LOW_PERCENTILE:  float = 0.10
ATR_HIGH_PERCENTILE: float = 0.90
EMA_VELOCITY_LOOKBACK:   int   = 4
EMA_VELOCITY_STRONG_MIN: float = 0.05
EMA_VELOCITY_WEAK_MAX:   float = 0.005
RSI_4H_PULL_LONG_MAX:  float = 70.0
RSI_4H_PULL_SHORT_MIN: float = 30.0
FUNDING_HISTORY_DEPTH: int = 4

FUNDING_WARN_EXTREME = 0.0010
FUNDING_WARN_HIGH    = 0.0005

# [Feature-50] Regime-aware TP/SL multiplier adjustments
USE_REGIME_AWARE_TP_SL: bool = True
REGIME_HIGH_VOL_TP1_MULT: float = 1.2   # widen TP1 in high-vol
REGIME_HIGH_VOL_TP2_MULT: float = 1.15
REGIME_HIGH_VOL_SL_MULT: float  = 0.95  # slightly tighten SL
REGIME_LOW_VOL_TP1_MULT: float  = 0.85  # tighten TP1 in low-vol
REGIME_LOW_VOL_TP2_MULT: float  = 0.90
REGIME_LOW_VOL_SL_MULT: float   = 1.10  # slightly widen SL
REGIME_BEAR_TP1_MULT: float = 0.9       # take profits earlier in bear regime
REGIME_BULL_TP2_MULT: float = 1.1       # extend TP2 in bull regime

# [Logic-24] Dynamic BTC correlation threshold
LOW_BTC_CORR_THRESHOLD: float = 0.65  # |correlation| below this = "decorrelated"
LOW_BTC_CORR_LOOKBACK_BARS: int = 42  # 7 days of 4H candles
RS_BEARISH_REGIME_EXEMPT_PCT: float = 3.0

# [v15.5.5] Dynamic pairwise correlation clustering — ported from v15.8.1's
# Fix-33 (compute_pairwise_correlation_matrix / cluster_by_correlation),
# generalizing the single-symbol-vs-BTC approach above to all-pairs-within-
# watchlist. Renamed from v15.8.1's LAYER1_CLUSTER_CORR_THRESHOLD since it's
# no longer specific to the "layer1" group — it now drives clustering across
# the whole watchlist. Same default value (0.75) carried over unchanged.
DYNAMIC_CORR_CLUSTER_THRESHOLD: float = 0.85  # IMP-S17-4 — raised from 0.75; tighter clusters, more decorrelated signals get through. |correlation| >= this unions two symbols into the same cluster
CORR_MATRIX_MIN_SAMPLE: int = 20              # minimum overlapping-return sample size before a pair is scored at all

# [Risk-34] Leverage sizing (concurrent-position deduction removed — see v15.8.1)
LEVERAGE_BASE_RISK_PCT: float = 10.0
LEVERAGE_RANGE_LOW_RISK_PCT: float = 5.0
LEVERAGE_RANGE_HIGH_RISK_PCT: float = 15.0
LEVERAGE_MAX: float = 15.0

# [Logic-16] S/R lookback window
SR_LOOKBACK_BARS: int = 200  # was 100 — extended for major S/R levels

# [Logic-13] Cooldown constants — comment fixed
# [Fix-2] Shortened from 3 → 2: 2 bars (30min) still prevents immediate duplicate
SIGNAL_COOLDOWN_BARS:           int = 2   # 2 × 15m = 30 min
SIGNAL_COOLDOWN_BARS_HIGHSCORE: int = 2   # 2 × 15m = 30 min for high-score signals
SIGNAL_HIGHSCORE_THRESHOLD:     int = 7
# [Fix-3] Shortened from 2 → 1: A winning trade proved the regime — re-enter sooner for continuations
SIGNAL_COOLDOWN_POST_WIN_BARS:  int = 1   # 1 bar = 15 min post-win

STATE_VERSION = 4  # Bumped for audit fixes

# ═══════════════════════════════════════════════════════════════
# HYPERLIQUID DATA FETCHING
# ═══════════════════════════════════════════════════════════════

def hl_coin(symbol: str) -> str:
    return symbol.replace("USDT", "")

def hl_post(payload: dict):
    """Post to Hyperliquid API with retry and rate-limit handling.

    [P0-1] Raises RuntimeError instead of silently returning None after
    exhausting all retries on 429.
    """
    global _hl_last_request_ts, _hl_min_interval_s, _hl_consecutive_successes
    max_attempts  = int(os.getenv("HL_MAX_ATTEMPTS", "6"))
    base_sleep_s  = float(os.getenv("HL_BASE_SLEEP_S", "0.75"))
    for attempt in range(max_attempts):
        try:
            with _hl_request_lock:
                now     = time.time()
                elapsed = now - _hl_last_request_ts
                wait_s  = _hl_min_interval_s - elapsed
                if wait_s > 0:
                    time.sleep(wait_s)
                _hl_last_request_ts = time.time()

            r = _hl_session.post(
                HL_INFO_URL,
                json=payload,
                headers={"Content-Type": "application/json"},
                timeout=15,
            )
            if r.status_code == 429:
                with _hl_request_lock:
                    _hl_min_interval_s = min(
                        HL_MIN_INTERVAL_MAX_S, _hl_min_interval_s * 1.25 + 0.02
                    )
                    _hl_consecutive_successes = 0
                retry_after = r.headers.get("Retry-After")
                try:
                    retry_after_s = float(retry_after) if retry_after is not None else None
                except ValueError:
                    retry_after_s = None
                sleep_s = retry_after_s if retry_after_s is not None else (base_sleep_s * (2 ** attempt))
                sleep_s = min(20.0, max(base_sleep_s, sleep_s)) + random.uniform(0.0, 0.35)
                time.sleep(sleep_s)
                continue
            r.raise_for_status()
            with _hl_request_lock:
                _hl_consecutive_successes += 1
                if _hl_consecutive_successes >= 10:
                    _hl_min_interval_s = HL_MIN_INTERVAL_S
                    _hl_consecutive_successes = 0
                else:
                    _hl_min_interval_s = max(HL_MIN_INTERVAL_S, _hl_min_interval_s - 0.0025)
            return r.json()
        except Exception as e:
            if attempt == max_attempts - 1:
                raise
            sleep_s = min(20.0, base_sleep_s * (2 ** attempt)) + random.uniform(0.0, 0.25)
            time.sleep(sleep_s)

    # [P0-1] Exhausted all retries on 429 — raise instead of returning None
    raise RuntimeError("hl_post exhausted all retries (likely persistent 429)")

def current_bar_open_ms(reference_ms: int, interval: str) -> int:
    iv_ms = INTERVAL_MS.get(interval, 60 * 60 * 1000)
    return (reference_ms // iv_ms) * iv_ms

def filter_closed_candles(candles: list[dict], interval: str, reference_ms: int) -> list[dict]:
    cutoff = current_bar_open_ms(reference_ms, interval)
    return [c for c in candles if c["t"] < cutoff]

def get_candles(symbol: str, interval: str, n: int,
                start_time_ms: int | None = None,
                reference_ms: int | None = None) -> list[dict]:
    coin   = hl_coin(symbol)
    iv_ms  = INTERVAL_MS.get(interval, 60 * 60 * 1000)
    ref_ms = int(time.time() * 1000) if reference_ms is None else reference_ms
    end_ms = current_bar_open_ms(ref_ms, interval)

    computed_start_ms = start_time_ms if start_time_ms is not None else end_ms - iv_ms * (n + 10)

    payload = {
        "type": "candleSnapshot",
        "req": {
            "coin":      coin,
            "interval":  interval,
            "startTime": computed_start_ms,
            "endTime":   end_ms,
        },
    }
    raw = hl_post(payload)
    # [P0-1] Defensive: if hl_post somehow returns None, treat as empty
    if raw is None:
        return []
    candles = []
    for c in raw:
        base_v  = float(c["v"])
        quote_v = float(c["q"]) if c.get("q") is not None else base_v
        candles.append({
            "t": int(c["t"]),   "o": float(c["o"]),
            "h": float(c["h"]), "l": float(c["l"]),
            "c": float(c["c"]), "v": base_v, "qv": quote_v,
        })
    candles = filter_closed_candles(candles, interval, ref_ms)
    return candles[-n:]

def _detect_candle_gaps(candles: list[dict], interval_ms: int,
                        max_gap_mult: float = 2.0, symbol: str = "") -> list[dict]:
    """Log and skip symbols with candle timestamp gaps. Returns candles unchanged,
    or [] if a gap > max_gap_mult * interval_ms is found (caller should skip the
    symbol for this scan since indicator values would reference the wrong bars)."""  # IMP-S18-5
    for i in range(1, len(candles)):
        gap_ms = candles[i]["t"] - candles[i - 1]["t"]
        if gap_ms > interval_ms * max_gap_mult:
            gap_min = gap_ms / 60_000
            print(f"  [CANDLE GAP] {symbol} 15m candle gap detected: {gap_min:.1f} min "
                  f"at index {i} (ts={candles[i]['t']}). Skipping symbol.")
            return []   # IMP-S18-5 — return empty to trigger symbol-skip in caller
    return candles

def fetch_all_candles(symbol: str, reference_ms: int | None = None) -> tuple[list, list, list, list] | None:
    candles_15m = get_candles(symbol, "15m", N_15M, reference_ms=reference_ms)
    if len(candles_15m) < 50:
        return None
    candles_15m = _detect_candle_gaps(candles_15m, interval_ms=INTERVAL_MS["15m"],
                                       symbol=symbol)   # IMP-S18-5
    if not candles_15m:
        return None   # IMP-S18-5 — skip symbol on detected gap
    results = {}
    with ThreadPoolExecutor(max_workers=max(1, HL_TF_WORKERS)) as ex:
        futures = {
            ex.submit(get_candles, symbol, "1h", N_1H, None, reference_ms): "1h",
            ex.submit(get_candles, symbol, "4h", N_4H, None, reference_ms): "4h",
            ex.submit(get_candles, symbol, "1d", N_1D, None, reference_ms): "1d",
        }
        for fut in as_completed(futures):
            tf = futures[fut]
            try:
                results[tf] = fut.result()
            except Exception as e:
                print(f"  [CANDLES] {symbol} {tf} fetch failed: {e} — skipping symbol")
                return None
    if not all(k in results for k in ("1h", "4h", "1d")):
        return None
    return candles_15m, results["1h"], results["4h"], results["1d"]

# ═══════════════════════════════════════════════════════════════
# FUNDING RATE + OPEN INTEREST
# ═══════════════════════════════════════════════════════════════

_meta_cache: dict | None = None
_meta_cache_lock = threading.Lock()
_meta_cache_fetched_at: float = 0.0
META_CACHE_TTL_S: float = 55.0

def get_meta_and_asset_ctxs() -> dict | None:
    """Fetch meta and asset contexts with proper double-checked locking.

    [P1-8] Fixed: fetch happens OUTSIDE the lock to avoid blocking all threads
    on a single slow HTTP request. Re-check-and-swap after fetch.
    """
    global _meta_cache, _meta_cache_fetched_at

    # Fast path: check cache under lock
    with _meta_cache_lock:
        age = time.time() - _meta_cache_fetched_at
        if _meta_cache is not None and age < META_CACHE_TTL_S:
            return _meta_cache

    # Slow path: fetch WITHOUT holding the lock
    try:
        data       = hl_post({"type": "metaAndAssetCtxs"})
        if data is None:
            return _meta_cache  # return stale cache if available
        meta       = data[0]
        asset_ctxs = data[1]
        universe   = meta.get("universe", [])
        cache = {}
        for i, asset in enumerate(universe):
            name = asset.get("name", "")
            if not name:
                continue
            ctx      = asset_ctxs[i]
            funding  = float(ctx["funding"])       if ctx.get("funding")      is not None else None
            oi_coins = float(ctx["openInterest"])  if ctx.get("openInterest") is not None else None
            mark     = float(ctx["markPx"])        if ctx.get("markPx")       is not None else None
            cache[name] = {"funding": funding, "open_interest_coins": oi_coins, "mark_px": mark}

        # Re-check-and-swap under lock
        with _meta_cache_lock:
            _meta_cache = cache
            _meta_cache_fetched_at = time.time()
        return _meta_cache
    except Exception as e:
        print(f"  [META CACHE] fetch failed: {e}")
        with _meta_cache_lock:
            return _meta_cache  # return stale cache if available

def get_market_context(symbol: str) -> dict | None:
    coin  = hl_coin(symbol)
    cache = get_meta_and_asset_ctxs()
    if cache is None or coin not in cache:
        return None
    entry    = cache[coin]
    funding  = entry.get("funding")
    oi_coins = entry.get("open_interest_coins")
    mark     = entry.get("mark_px")
    oi_usd   = oi_coins * mark if (oi_coins is not None and mark is not None) else None
    return {"funding": funding, "open_interest": oi_usd, "open_interest_coins": oi_coins}

# ═══════════════════════════════════════════════════════════════
# STATE MANAGEMENT  — [P1-7] All state access now under _state_lock
# ═══════════════════════════════════════════════════════════════

_state_lock = threading.RLock()  # [P1-7] RLock for re-entrant access

def update_funding_history(state: dict, symbol: str, rate: float | None) -> None:
    if rate is None:
        return
    with _state_lock:
        hist = state.setdefault("funding_history", {}).setdefault(symbol, [])
        hist.append({"ts": int(time.time()), "rate": rate})
        state["funding_history"][symbol] = hist[-FUNDING_HISTORY_DEPTH:]

def get_funding_trend(state: dict, symbol: str) -> str:
    with _state_lock:
        hist = list(state.get("funding_history", {}).get(symbol, []))
    if len(hist) < 2:
        return "stable"
    recent = hist[-1]["rate"]
    prior  = hist[-2]["rate"]
    delta  = recent - prior
    if delta > 0.0001:
        return "rising"
    if delta < -0.0001:
        return "falling"
    return "stable"

def update_oi_history(state: dict, symbol: str, oi_usd: float | None) -> None:
    if oi_usd is None:
        return
    with _state_lock:
        oi_hist     = state.setdefault("oi_history", {})
        symbol_hist = oi_hist.setdefault(symbol, [])
        symbol_hist.append({"ts": int(time.time()), "oi": oi_usd})
        oi_hist[symbol] = symbol_hist[-OI_HISTORY_DEPTH:]

def compute_oi_trend(state: dict, symbol: str, current_price: float,
                     price_direction: str, trade_direction: str) -> dict:
    OI_FRESHNESS_CUTOFF_S = 30 * 60   # IMP-S18-4 — 30 minutes
    with _state_lock:
        oi_hist = list(state.get("oi_history", {}).get(symbol, []))
    if not oi_hist:
        return {
            "oi_trend": "unknown", "oi_change_pct": None,
            "oi_acceleration": None, "score_adj": 0,
            "label": "OI Trend: Unknown", "breakdown_tag": "OI?",
            "condition": "Unknown",
        }
    _last_ts_s18_4 = oi_hist[-1].get("ts", 0)
    if (time.time() - _last_ts_s18_4) > OI_FRESHNESS_CUTOFF_S:             # IMP-S18-4
        print(f"  [OI FRESHNESS] {symbol} OI data is stale "
              f"({(time.time() - _last_ts_s18_4) / 60:.1f} min) — returning unknown")
        return {
            "oi_trend": "unknown", "oi_change_pct": None,
            "oi_acceleration": None, "score_adj": 0,
            "label": "OI Trend: Unknown (stale)", "breakdown_tag": "OI?",
            "condition": "Unknown",
        }
    if len(oi_hist) < 2:
        return {
            "oi_trend": "unknown", "oi_change_pct": None,
            "oi_acceleration": None, "score_adj": 0,
            "label": "OI Trend: Unknown", "breakdown_tag": "OI?",
            "condition": "Unknown",
        }
    recent = oi_hist[-1]["oi"]
    prior  = oi_hist[-2]["oi"]
    if prior == 0:
        return {
            "oi_trend": "unknown", "oi_change_pct": None,
            "oi_acceleration": None, "score_adj": 0,
            "label": "OI Trend: Unknown", "breakdown_tag": "OI?",
            "condition": "Unknown",
        }
    raw_change_pct = (recent - prior) / prior * 100.0
    elapsed_s      = max(1.0, oi_hist[-1]["ts"] - oi_hist[-2]["ts"])
    if elapsed_s > OI_STALE_CUTOFF_S:
        return {
            "oi_trend": "unknown", "oi_change_pct": None,
            "oi_acceleration": None, "score_adj": 0,
            "label": "OI Trend: Unknown (stale)", "breakdown_tag": "OI?",
            "condition": "Unknown",
        }
    if elapsed_s < OI_EXPECTED_INTERVAL_S:                        # FIX-D10
        # Rapid resample: scale UP to normalize to 15-min rate (capped)
        scale = min(MAX_OI_SCALE, OI_EXPECTED_INTERVAL_S / elapsed_s)
    else:
        # Longer-than-expected interval: do NOT deflate; treat as one 15-min period
        scale = 1.0
    oi_change_pct  = raw_change_pct * scale

    oi_acceleration = None
    if len(oi_hist) >= 3:
        prior2 = oi_hist[-3]["oi"]
        if prior2 != 0:
            prev_elapsed = max(1.0, oi_hist[-2]["ts"] - oi_hist[-3]["ts"])
            prev_raw     = (prior - prior2) / prior2 * 100.0
            prev_scale   = min(MAX_OI_SCALE, OI_EXPECTED_INTERVAL_S / prev_elapsed)
            prev_change  = prev_raw * prev_scale
            oi_acceleration = oi_change_pct - prev_change

    oi_rising  = oi_change_pct >  OI_CHANGE_THRESHOLD_PCT
    oi_falling = oi_change_pct < -OI_CHANGE_THRESHOLD_PCT

    if oi_rising:
        oi_trend = "rising"
    elif oi_falling:
        oi_trend = "falling"
    else:
        oi_trend = "flat"

    bullish_confirm = price_direction == "up"   and oi_rising
    bearish_confirm = price_direction == "down" and oi_rising
    bullish_div     = price_direction == "up"   and oi_falling
    bearish_div     = price_direction == "down" and oi_falling

    # [Logic-10] Fixed OI trend asymmetry for shorts
    # Previously: bullish_div (price up + OI down = shorts covering) for shorts
    # was lumped into neutral alongside bearish_div (long-covering).
    # Now: shorts covering is explicitly penalized for short signals.
    if trade_direction == "long":
        if bullish_confirm:
            score_adj, condition, breakdown_tag = 1,  "Bullish Confirmation",                     "OI↑"
        elif bearish_confirm:
            score_adj, condition, breakdown_tag = -1, "Counter vs Long (OI rising on down move)", "OI Divergence"
        elif bullish_div:
            # Price up + OI falling = longs taking profit = neutral for new longs
            score_adj, condition, breakdown_tag = 0,  "Neutral (longs unwinding)",                "OI→"
        elif bearish_div:
            # Price down + OI falling = long-covering = neutral
            score_adj, condition, breakdown_tag = 0,  "Neutral (long-covering)",                  "OI→"
        else:
            score_adj, condition, breakdown_tag = 0,  "Neutral",                                  "OI→"
    else:  # short
        if bearish_confirm:
            score_adj, condition, breakdown_tag = 1,  "Bearish Confirmation",                      "OI↑"
        elif bullish_confirm:
            score_adj, condition, breakdown_tag = -1, "Counter vs Short (OI rising on up move)",   "OI Divergence"
        elif bullish_div:
            # [Logic-10] Price up + OI falling = shorts covering = bullish pressure against short
            score_adj, condition, breakdown_tag = -1, "Shorts covering (OI falling on up move)",   "OI↓"
        elif bearish_div:
            # Price down + OI falling = long-covering = neutral for shorts
            score_adj, condition, breakdown_tag = 0,  "Neutral (long-covering)",                   "OI→"
        else:
            score_adj, condition, breakdown_tag = 0,  "Neutral",                                   "OI→"

    label = (
        f"OI Trend: {oi_trend.capitalize()}  "
        f"OI Change: {oi_change_pct:+.1f}% (norm)"
    )
    return {
        "oi_trend":        oi_trend,
        "oi_change_pct":   oi_change_pct,
        "oi_acceleration": oi_acceleration,
        "score_adj":       score_adj,
        "label":           label,
        "breakdown_tag":   breakdown_tag,
        "condition":       condition,
    }

def format_funding(rate: float | None, direction: str) -> str:
    if rate is None:
        return "Funding: n/a"
    pct    = rate * 100
    per_8h = f"{pct:+.4f}%/8h"
    headwind = (rate > 0 and direction == "long") or (rate < 0 and direction == "short")
    tailwind = (rate < 0 and direction == "long") or (rate > 0 and direction == "short")
    abs_rate = abs(rate)
    if headwind and abs_rate >= FUNDING_WARN_EXTREME:
        tag = "⚠️ EXTREME — longs paying heavily" if direction == "long" else "⚠️ EXTREME — shorts paying heavily"
    elif headwind and abs_rate >= FUNDING_WARN_HIGH:
        tag = "⚡ elevated against trade"
    elif tailwind and abs_rate >= FUNDING_WARN_HIGH:
        tag = "✅ in your favour"
    else:
        tag = "✅ neutral"
    return f"Funding: {per_8h}  {tag}"

def format_oi(oi_usd: float | None) -> str:
    if oi_usd is None:
        return "OI: n/a"
    if oi_usd >= 1_000_000_000:
        return f"OI: ${oi_usd / 1_000_000_000:.2f}B"
    if oi_usd >= 1_000_000:
        return f"OI: ${oi_usd / 1_000_000:.1f}M"
    return f"OI: ${oi_usd:,.0f}"

# ── S/R LEVELS ──────────────────────────────────────────────

SR_PIVOT_LEFT_BARS  = 3
SR_PIVOT_RIGHT_BARS = 3
SR_CLUSTER_ATR_MULT = 0.3

def _cluster_levels(pivots: list[float], atr_val: float, tolerance: float = 0.3) -> list[float]:
    """Cluster nearby pivot levels.

    [Logic-17] Uses median instead of running mean to avoid drift
    when 3+ pivots cluster together.
    """
    if not pivots or atr_val <= 0:
        return pivots
    zones: list[float] = []
    zone_members: list[list[float]] = []  # Track members for median calc
    for p in sorted(pivots):
        if zones and abs(p - zones[-1]) < atr_val * tolerance:
            # Add to existing cluster
            zone_members[-1].append(p)
            # [Logic-17] Use median instead of mean
            members = zone_members[-1]
            zones[-1] = sorted(members)[len(members) // 2]
        else:
            zones.append(p)
            zone_members.append([p])
    return zones

def find_sr_levels(candles_15m: list[dict], n_levels: int = 2,
                   atr_val: float | None = None) -> tuple[list[float], list[float]]:
    cur          = candles_15m[-1]["c"]
    pivots_high  = []
    pivots_low   = []
    lb = SR_PIVOT_LEFT_BARS
    rb = SR_PIVOT_RIGHT_BARS
    avail  = len(candles_15m) - 1
    # [Logic-16] Extended from 100 to SR_LOOKBACK_BARS (200) for major S/R levels
    window = candles_15m[max(0, avail - SR_LOOKBACK_BARS): avail]
    for i in range(lb, len(window) - rb):
        h = window[i]["h"]
        l = window[i]["l"]
        if all(h > window[i - k]["h"] for k in range(1, lb + 1)) and \
           all(h > window[i + k]["h"] for k in range(1, rb + 1)):
            pivots_high.append(h)
        if all(l < window[i - k]["l"] for k in range(1, lb + 1)) and \
           all(l < window[i + k]["l"] for k in range(1, rb + 1)):
            pivots_low.append(l)

    eff_atr = atr_val if atr_val and atr_val > 0 else (cur * 0.005)
    pivots_high = _cluster_levels(pivots_high, eff_atr, SR_CLUSTER_ATR_MULT)
    pivots_low  = _cluster_levels(pivots_low,  eff_atr, SR_CLUSTER_ATR_MULT)

    resistances = sorted([p for p in pivots_high if p > cur], key=lambda x: x - cur)[:n_levels]
    supports    = sorted([p for p in pivots_low  if p < cur], key=lambda x: cur - x)[:n_levels]
    return supports, resistances

# ═══════════════════════════════════════════════════════════════
# BTC MARKET REGIME FILTER
# ═══════════════════════════════════════════════════════════════

_btc_regime_cache: dict | None = None
_btc_regime_lock  = threading.Lock()

def compute_btc_regime(candles_1h: list[dict], candles_4h: list[dict],
                       candles_1d: list[dict] | None = None) -> dict:
    def _arr(candles):
        return [c["c"] for c in candles]

    c4h = _arr(candles_4h)
    c1h = _arr(candles_1h)

    ef4h = safe(ema(c4h, FAST_LEN)[-1])
    es4h = safe(ema(c4h, SLOW_LEN)[-1])
    ef1h = safe(ema(c1h, FAST_LEN)[-1])
    es1h = safe(ema(c1h, SLOW_LEN)[-1])

    btc_4h_momentum_bull = len(c4h) >= 6 and c4h[-2] > c4h[-5]   # FIX-D11
    btc_4h_momentum_bear = len(c4h) >= 6 and c4h[-2] < c4h[-5]   # FIX-D11

    btc_bullish = (ef4h > es4h) and (ef1h > es1h) and btc_4h_momentum_bull
    btc_bearish_intraday = (ef4h < es4h) and (ef1h < es1h) and btc_4h_momentum_bear  # FIX-D11

    # Daily confirmation: only treat as confirmed bearish if daily EMA21 < EMA50 as well
    btc_daily_bearish = False
    if candles_1d and len(candles_1d) >= SLOW_LEN:
        c1d = _arr(candles_1d)
        ef1d = safe(ema(c1d, FAST_LEN)[-1])
        es1d = safe(ema(c1d, SLOW_LEN)[-1])
        btc_daily_bearish = ef1d < es1d

    # Bearish requires both intraday structure AND daily trend confirmation
    btc_bearish = btc_bearish_intraday and btc_daily_bearish
    # Intraday-only bearish (4H/1H bear but daily still bullish) → treat as Mixed
    btc_intraday_only_bearish = btc_bearish_intraday and not btc_daily_bearish

    if btc_bullish:
        label = "BTC Regime: Bullish"
    elif btc_bearish:
        label = "BTC Regime: Bearish (confirmed)"
    elif btc_intraday_only_bearish:
        label = "BTC Regime: Mixed (4H dip, daily intact)"
    else:
        label = "BTC Regime: Mixed"

    return {
        "bullish": btc_bullish,
        "bearish": btc_bearish,
        "intraday_bearish": btc_bearish_intraday,
        "label": label,
    }

def set_btc_regime(regime: dict):
    global _btc_regime_cache
    with _btc_regime_lock:
        _btc_regime_cache = regime

def get_btc_regime() -> dict | None:
    with _btc_regime_lock:
        return _btc_regime_cache

# [Logic-24] Dynamic BTC correlation set — computed from rolling correlation
# Falls back to hardcoded baseline if computation fails
LOW_BTC_CORR_BASELINE: set[str] = {"TAOUSDT", "TRXUSDT", "PENDLEUSDT", "ONDOUSDT", "HYPEUSDT"}
_dynamic_low_btc_corr: set[str] = set()
_dynamic_corr_lock = threading.Lock()

def update_dynamic_btc_correlation(symbol: str, candles_4h: list[dict], btc_candles_4h: list[dict] | None) -> None:
    """Compute rolling correlation between symbol and BTC returns.

    [Logic-24] Replaces hardcoded LOW_BTC_CORR with dynamic computation.
    """
    if btc_candles_4h is None or len(btc_candles_4h) < LOW_BTC_CORR_LOOKBACK_BARS + 2:
        return
    if len(candles_4h) < LOW_BTC_CORR_LOOKBACK_BARS + 2:
        return

    n = LOW_BTC_CORR_LOOKBACK_BARS
    sym_closes = [c["c"] for c in candles_4h[-(n + 1):]]
    btc_closes = [c["c"] for c in btc_candles_4h[-(n + 1):]]

    sym_returns = [(sym_closes[i] - sym_closes[i - 1]) / sym_closes[i - 1]
                   for i in range(1, len(sym_closes)) if sym_closes[i - 1] != 0]
    btc_returns = [(btc_closes[i] - btc_closes[i - 1]) / btc_closes[i - 1]
                   for i in range(1, len(btc_closes)) if btc_closes[i - 1] != 0]

    if len(sym_returns) < 10 or len(btc_returns) < 10:
        return

    min_len = min(len(sym_returns), len(btc_returns))
    sym_returns = sym_returns[:min_len]
    btc_returns = btc_returns[:min_len]

    mean_s = sum(sym_returns) / min_len
    mean_b = sum(btc_returns) / min_len

    cov = sum((s - mean_s) * (b - mean_b) for s, b in zip(sym_returns, btc_returns)) / min_len
    var_s = sum((s - mean_s) ** 2 for s in sym_returns) / min_len
    var_b = sum((b - mean_b) ** 2 for b in btc_returns) / min_len

    if var_s <= 0 or var_b <= 0:
        return

    corr = cov / (math.sqrt(var_s) * math.sqrt(var_b))

    with _dynamic_corr_lock:
        if abs(corr) < LOW_BTC_CORR_THRESHOLD:
            _dynamic_low_btc_corr.add(symbol)
        else:
            _dynamic_low_btc_corr.discard(symbol)

def get_low_btc_corr_set() -> set[str]:
    """Return the current set of low-BTC-correlation symbols.

    [Logic-24] Uses dynamic set if populated, falls back to baseline.
    """
    with _dynamic_corr_lock:
        if _dynamic_low_btc_corr:
            return _dynamic_low_btc_corr.copy()
    return LOW_BTC_CORR_BASELINE.copy()

# ═══════════════════════════════════════════════════════════════
# [v15.5.5] DYNAMIC PAIRWISE CORRELATION CLUSTERING
# Ported from v15.8.1 (Fix-33). Generalizes update_dynamic_btc_correlation()
# above (vs-BTC only) to all-pairs-within-watchlist, then unions symbols into
# clusters via union-find wherever measured correlation clears
# DYNAMIC_CORR_CLUSTER_THRESHOLD. Unlike v15.8.1 — where this same machinery
# was diagnostic-only and never consulted by deduplicate_correlated() — here
# it IS the correlated-exposure control: deduplicate_correlated() below calls
# group_of_dynamic() instead of looking symbols up in a static CORR_GROUPS
# dict. Uses the same 4H candle history already fetched per symbol in Phase 1
# of main() — no new data fetching required.
# ═══════════════════════════════════════════════════════════════

_dynamic_corr_clusters: list[frozenset[str]] = []
_dynamic_corr_clusters_lock = threading.Lock()

def compute_pairwise_correlation_matrix(
    symbols: list[str],
    candle_bundles: dict[str, tuple],
    candle_idx: int = 2,
    lookback: int = LOW_BTC_CORR_LOOKBACK_BARS,
) -> dict[tuple[str, str], float]:
    """Pairwise Pearson correlation of 4H close-to-close returns across
    `symbols`, generalizing update_dynamic_btc_correlation() (vs-BTC only) to
    all pairs. `candle_bundles[sym][candle_idx]` is expected to be the 4H
    candle list — matches the convention already used at the
    update_dynamic_btc_correlation() call site in main() (bundle[2]). Pairs
    with insufficient overlapping history are simply omitted from the result
    rather than raising."""
    returns_by_symbol: dict[str, list[float]] = {}
    for sym in symbols:
        bundle = candle_bundles.get(sym)
        if not bundle or len(bundle) <= candle_idx:
            continue
        candles = bundle[candle_idx]
        if len(candles) < lookback + 2:
            continue
        closes = [c["c"] for c in candles[-(lookback + 1):]]
        rets = [(closes[i] - closes[i - 1]) / closes[i - 1]
                for i in range(1, len(closes)) if closes[i - 1] != 0]
        if len(rets) >= CORR_MATRIX_MIN_SAMPLE:
            returns_by_symbol[sym] = rets

    matrix: dict[tuple[str, str], float] = {}
    syms = sorted(returns_by_symbol.keys())
    for i, a in enumerate(syms):
        for b in syms[i + 1:]:
            ra, rb = returns_by_symbol[a], returns_by_symbol[b]
            n = min(len(ra), len(rb))
            if n < CORR_MATRIX_MIN_SAMPLE:
                continue
            ra_, rb_ = ra[:n], rb[:n]
            mean_a = sum(ra_) / n
            mean_b = sum(rb_) / n
            cov   = sum((x - mean_a) * (y - mean_b) for x, y in zip(ra_, rb_)) / n
            var_a = sum((x - mean_a) ** 2 for x in ra_) / n
            var_b = sum((y - mean_b) ** 2 for y in rb_) / n
            if var_a <= 0 or var_b <= 0:
                continue
            matrix[(a, b)] = cov / (math.sqrt(var_a) * math.sqrt(var_b))
    return matrix

def cluster_by_correlation(
    symbols: list[str],
    corr_matrix: dict[tuple[str, str], float],
    threshold: float = DYNAMIC_CORR_CLUSTER_THRESHOLD,
) -> list[set[str]]:
    """Greedy union-find clustering: symbols end up in the same cluster if a
    chain of pairwise correlations >= `threshold` connects them. This is a
    simple, reviewable clustering choice, not a claim that it's the "right"
    algorithm for this purpose (e.g. it can chain a long transitive sequence
    of pairs together even if not all pairs in the resulting cluster are
    mutually correlated above threshold). Symbols with no qualifying edge —
    including any symbol missing from `corr_matrix` entirely, e.g. due to
    insufficient candle history this scan — end up as their own singleton
    cluster, so every symbol in `symbols` is always covered."""
    parent = {s: s for s in symbols}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    for (a, b), corr in corr_matrix.items():
        if a in parent and b in parent and corr >= threshold:
            union(a, b)

    clusters: dict[str, set[str]] = {}
    for s in symbols:
        clusters.setdefault(find(s), set()).add(s)
    return list(clusters.values())

def set_dynamic_corr_clusters(clusters: list[set[str]]) -> None:
    global _dynamic_corr_clusters
    with _dynamic_corr_clusters_lock:
        _dynamic_corr_clusters = [frozenset(c) for c in clusters]

def get_dynamic_corr_clusters() -> list[frozenset[str]]:
    with _dynamic_corr_clusters_lock:
        return list(_dynamic_corr_clusters)

def group_of_dynamic(symbol: str) -> object:
    """Return a stable, hashable group key for `symbol` based on this scan's
    dynamic correlation clusters, for use as the grouping key in
    deduplicate_correlated() (replaces the old static CORR_GROUPS lookup).
    Falls back to the symbol itself (a singleton group) if cluster data
    hasn't been computed yet this scan (e.g. very first scan after startup,
    before main()'s Phase 1 clustering step has run) or the symbol isn't
    covered by any computed cluster."""
    for cluster in get_dynamic_corr_clusters():
        if symbol in cluster:
            return cluster
    return symbol

def log_dynamic_corr_clusters(clusters: list[set[str]]) -> None:
    """Print this scan's dynamic correlation clusters for visibility. Unlike
    v15.8.1's log_dynamic_layer1_clustering() (diagnostic-only, gated behind
    LOG_DYNAMIC_CORR_GROUPS, never consulted by deduplicate_correlated()),
    these clusters are the live exposure-control grouping — see
    deduplicate_correlated() / group_of_dynamic()."""
    multi = [sorted(c) for c in clusters if len(c) > 1]
    if multi:
        print(f"  [CORR MATRIX] Dynamic correlation clusters this scan "
              f"(threshold={DYNAMIC_CORR_CLUSTER_THRESHOLD}): {multi}")
    else:
        print(f"  [CORR MATRIX] No symbol pairs cleared the "
              f"{DYNAMIC_CORR_CLUSTER_THRESHOLD} correlation threshold this scan "
              f"— all symbols treated as decorrelated singletons.")

def check_btc_regime_filter(direction: str, symbol: str,
                            signal_type: str = "") -> tuple[int, str]:
    if hl_coin(symbol) == "BTC":
        return 0, "BTC Regime: N/A (BTC itself)"

    regime = get_btc_regime()
    if regime is None:
        return 0, "BTC Regime: Unknown"

    label = regime["label"]
    # [Logic-24] Use dynamic correlation set
    low_corr_set = get_low_btc_corr_set()

    if direction == "long" and regime["bearish"]:
        if symbol in low_corr_set:
            return 0, f"{label} — counter-trend (exempt, decorrelated)"
        # RS exemption: coin actively outperforming BTC → treat as decorrelated this scan
        with _rs_lock:
            rs_snap = dict(_rs_snapshot if _rs_snapshot is not None else _rs_scores)
        btc_ret  = rs_snap.get("BTCUSDT")
        coin_ret = rs_snap.get(symbol)
        if btc_ret is not None and coin_ret is not None:
            rs_vs_btc = coin_ret - btc_ret
            if rs_vs_btc >= RS_BEARISH_REGIME_EXEMPT_PCT:
                return 0, f"{label} — counter-trend (exempt, RS +{rs_vs_btc:.1f}% vs BTC)"
        return -1, f"{label} — counter-trend (-1)"

    if direction == "short" and regime["bullish"]:
        if symbol in low_corr_set:
            return 0, f"{label} — counter-trend (exempt, decorrelated)"
        # [Fix-41] Mirror of the long-branch RS exemption above: a short is
        # "outperforming the regime" when it's *weaker* than BTC, i.e. rs_vs_btc
        # negative and at least as negative as -RS_BEARISH_REGIME_EXEMPT_PCT.
        with _rs_lock:
            rs_snap = dict(_rs_snapshot if _rs_snapshot is not None else _rs_scores)
        btc_ret  = rs_snap.get("BTCUSDT")
        coin_ret = rs_snap.get(symbol)
        if btc_ret is not None and coin_ret is not None:
            rs_vs_btc = coin_ret - btc_ret
            if rs_vs_btc <= -RS_BEARISH_REGIME_EXEMPT_PCT:
                return 0, f"{label} — counter-trend (exempt, RS {rs_vs_btc:.1f}% vs BTC)"
        return -1, f"{label} — counter-trend (-1)"

    if direction == "long" and regime["bullish"]:
        return +1, f"{label} — tailwind (+1)"
    if direction == "short" and regime["bearish"]:
        return +1, f"{label} — tailwind (+1)"

    if not regime["bullish"] and not regime["bearish"]:
        if signal_type == "BREAK":
            return 0, f"{label} — Mixed (neutral for BREAK)"
        else:
            return 0, f"{label} — Mixed (0)"

    return 0, f"{label} — Mixed (0)"

# ═══════════════════════════════════════════════════════════════
# MARKET BREADTH FILTER
# ═══════════════════════════════════════════════════════════════

_breadth_ema50_above: dict[str, bool] = {}
_breadth_snapshot:   dict[str, bool] | None = None
_breadth_lock = threading.Lock()

def reset_breadth_cache() -> None:
    global _breadth_snapshot
    with _breadth_lock:
        _breadth_ema50_above.clear()
        _breadth_snapshot = None

def record_breadth_result(symbol: str, price_above_ema50: bool):
    with _breadth_lock:
        _breadth_ema50_above[symbol] = price_above_ema50

def finalize_breadth_cache() -> None:
    global _breadth_snapshot
    with _breadth_lock:
        _breadth_snapshot = dict(_breadth_ema50_above)

def compute_market_breadth() -> dict:
    with _breadth_lock:
        results = dict(_breadth_snapshot if _breadth_snapshot is not None else _breadth_ema50_above)
    if not results:
        return {"breadth_50_pct": 0.5, "label": "Market Breadth: Unknown"}
    above = sum(1 for v in results.values() if v)
    pct   = above / len(results)
    if pct < BREADTH_WEAK_LONG_THRESHOLD:
        label = f"Market Breadth: {pct*100:.0f}% > EMA50 (Weak)"
    elif pct > BREADTH_WEAK_SHORT_THRESHOLD:
        label = f"Market Breadth: {pct*100:.0f}% > EMA50 (Overbought)"
    else:
        label = f"Market Breadth: {pct*100:.0f}% > EMA50 (Healthy)"
    return {"breadth_50_pct": pct, "label": label}

def apply_breadth_adjustment(direction: str, rs_pct: float | None = None,
                              btc_regime: dict | None = None) -> tuple[int, str]:
    breadth = compute_market_breadth()
    pct     = breadth["breadth_50_pct"]
    label   = breadth["label"]
    adj     = 0

    _is_mixed = (btc_regime is not None
                 and not btc_regime.get("bullish")
                 and not btc_regime.get("bearish"))
    _crowded_thresh = (BREADTH_CROWDED_LONG_THRESHOLD_MIXED
                       if _is_mixed
                       else BREADTH_CROWDED_LONG_THRESHOLD)

    if direction == "long":
        if pct > BREADTH_EXTREME_LONG_THRESHOLD:
            adj    = -2
            label += " (-2)"
        elif pct > _crowded_thresh:
            rs_weak = rs_pct is not None and rs_pct <= BREADTH_RS_NEGATIVE_THRESH
            if rs_weak:
                adj    = -2
                label += " (-2, crowded+weak RS)"
            else:
                adj    = -1
                label += " (-1, crowded)"
        elif pct < BREADTH_WEAK_LONG_THRESHOLD:
            adj    = -1
            label += " (-1)"
    elif direction == "short":
        if pct < BREADTH_EXTREME_SHORT_THRESHOLD:
            adj    = -2
            label += " (-2)"
        elif pct > BREADTH_WEAK_SHORT_THRESHOLD:
            # [Fix-45] Mirror of the long-branch "crowded + weak RS" combo penalty:
            # a short is in a poor environment when breadth is broadly bullish AND
            # the coin's own RS is strongly positive (outperforming, i.e. a bad
            # short candidate). Uses -BREADTH_RS_NEGATIVE_THRESH as the sign-flipped
            # mirror threshold (symmetric while the constant is 0.0).
            rs_weak_for_short = rs_pct is not None and rs_pct >= -BREADTH_RS_NEGATIVE_THRESH
            if rs_weak_for_short:
                adj    = -2
                label += " (-2, crowded+strong RS)"
            else:
                adj    = -1
                label += " (-1, crowded)"
    return adj, label

# ═══════════════════════════════════════════════════════════════
# RELATIVE STRENGTH RANKING
# ═══════════════════════════════════════════════════════════════

_rs_scores:   dict[str, float] = {}
_rs_snapshot: dict[str, float] | None = None
_rs_lock = threading.Lock()

def reset_rs_cache() -> None:
    global _rs_snapshot
    with _rs_lock:
        _rs_scores.clear()
        _rs_snapshot = None

def record_rs_return(symbol: str, return_7d_pct: float):
    with _rs_lock:
        _rs_scores[symbol] = return_7d_pct

def finalize_rs_cache() -> None:
    global _rs_snapshot
    with _rs_lock:
        _rs_snapshot = dict(_rs_scores)

def compute_relative_strength(symbol: str) -> dict:
    with _rs_lock:
        scores = dict(_rs_snapshot if _rs_snapshot is not None else _rs_scores)

    btc_return  = scores.get("BTCUSDT")
    coin_return = scores.get(symbol)

    if btc_return is None or coin_return is None:
        return {"rs_pct": None, "percentile": None, "score_adj": 0, "label": "Relative Strength: N/A"}

    rs     = coin_return - btc_return
    # [Logic-20] Exclude BTC from the distribution — BTC's RS is always 0 by definition
    # and including it distorts the percentile calculation.
    other_scores = {k: v for k, v in scores.items() if k != "BTCUSDT"}
    all_rs = sorted([v - btc_return for v in other_scores.values()])
    n      = len(all_rs)
    if n == 0:
        return {"rs_pct": rs, "percentile": 0.5, "score_adj": 0,
                "label": f"Relative Strength: {rs:+.1f}%"}
    try:
        rank       = next(i for i, v in enumerate(all_rs) if v >= rs)
        percentile = rank / max(n - 1, 1)
    except StopIteration:
        percentile = 1.0

    if percentile >= (1.0 - RS_TOP_PERCENTILE):
        score_adj = 1
    elif percentile <= RS_BOTTOM_PERCENTILE:
        score_adj = -1
    else:
        score_adj = 0

    return {"rs_pct": rs, "percentile": percentile, "score_adj": score_adj,
            "label": f"Relative Strength: {rs:+.1f}%"}

# ═══════════════════════════════════════════════════════════════
# HISTORICAL PERFORMANCE ANALYTICS
# ═══════════════════════════════════════════════════════════════

def record_signal_history(state: dict, symbol: str, direction: str,
                           signal_type: str, score: int,
                           funding_rate: float | None, atr_pct: float,
                           oi_change_pct: float | None,
                           alignment_mode: str = "full",
                           sent: bool = True) -> str:
    # [P1-7] Thread-safe state mutation
    with _state_lock:
        hist     = state.setdefault("signal_history", [])
        entry_id = f"{symbol}_{int(time.time())}"
        hist.append({
            "id":              entry_id,
            "symbol":          symbol,
            "direction":       direction,
            "signal_type":     signal_type,
            "score":           score,
            "alignment_mode":  alignment_mode,
            "funding_rate":    funding_rate,
            "atr_pct":         atr_pct,
            "oi_change_pct":   oi_change_pct,
            "result":          None,
            "sent":            sent,
            "timestamp":       int(time.time()),
        })
        if len(hist) > MAX_SIGNAL_HISTORY:
            state["signal_history"] = hist[-MAX_SIGNAL_HISTORY:]
    return entry_id

def update_signal_result(state: dict, signal_id: str, result: str) -> None:
    # [P1-7] Thread-safe state mutation
    with _state_lock:
        for entry in state.get("signal_history", []):
            if entry.get("id") == signal_id:
                entry["result"] = result
                return

def compute_win_rates(state: dict) -> dict:
    now_ts       = int(time.time())
    lookback_cut = now_ts - WIN_RATE_LOOKBACK_DAYS * 86400
    recent_cut   = now_ts - WIN_RATE_RECENT_DAYS   * 86400
    stale_cutoff = now_ts - WIN_RATE_STALE_DAYS    * 86400

    # [P1-7] Thread-safe state read
    with _state_lock:
        raw_hist = [e for e in state.get("signal_history", [])
                    if e.get("result") in ("tp1", "tp2", "sl")
                    and e.get("timestamp", 0) >= lookback_cut
                    and e.get("sent", True)]

    # [Risk-staleness] Prefer only recent (non-stale) history where there's
    # enough of it; fall back to the full lookback window (existing
    # behavior) when staleness filtering would leave too few entries for a
    # given bucket. This fallback is applied per sub-aggregation below,
    # mirroring the existing WIN_RATE_MIN_SAMPLE "not enough data" handling.
    fresh_hist = [e for e in raw_hist if e.get("timestamp", 0) >= stale_cutoff]

    # [P0-2] Use WIN_RATE_RECENT_WEIGHT constant properly
    # Recent entries are duplicated `int(WIN_RATE_RECENT_WEIGHT)` times
    weight_int = max(1, int(WIN_RATE_RECENT_WEIGHT))

    def _weighted(entries):
        out = []
        for e in entries:
            if e.get("timestamp", 0) >= recent_cut:
                out.extend([e] * weight_int)
            else:
                out.append(e)
        return out

    hist       = _weighted(raw_hist)
    fresh      = _weighted(fresh_hist)

    wrs: dict = {"by_symbol": {}, "by_type": {}, "by_score": {}, "by_direction": {},
                 "by_alignment_mode": {}}

    def wr_for(entries):
        n    = len(entries)
        wins = sum(1 for e in entries if e["result"] in ("tp1", "tp2"))
        return (wins / n if n > 0 else 0.0), n

    def best_subset(pred):
        # Prefer staleness-filtered (fresh) entries; fall back to the full
        # lookback window if filtering leaves too few to meet the existing
        # minimum-sample bar.
        fresh_subset = [e for e in fresh if pred(e)]
        if len(fresh_subset) >= WIN_RATE_MIN_SAMPLE:
            return fresh_subset
        return [e for e in hist if pred(e)]

    for sym in set(e["symbol"] for e in hist):
        subset = best_subset(lambda e, sym=sym: e["symbol"] == sym)
        wr, n  = wr_for(subset)
        if n >= WIN_RATE_MIN_SAMPLE:
            wrs["by_symbol"][sym] = {"wr": wr, "n": n}

    for st in ("BREAK", "PULL"):
        subset = best_subset(lambda e, st=st: e.get("signal_type") == st)
        wr, n  = wr_for(subset)
        if n >= WIN_RATE_MIN_SAMPLE:
            wrs["by_type"][st] = {"wr": wr, "n": n}

    # [Fix-47] Widened from range(4, 8) to cover the new realistic max score
    # (base 6 + MAX_POSITIVE_ADJUSTMENTS) so no achievable final score is left
    # out of the win-rate-by-score aggregation.
    for sc in range(4, 6 + MAX_POSITIVE_ADJUSTMENTS + 1):
        subset = best_subset(lambda e, sc=sc: e.get("score") == sc)
        wr, n  = wr_for(subset)
        if n >= WIN_RATE_MIN_SAMPLE:
            wrs["by_score"][str(sc)] = {"wr": wr, "n": n}

    for d in ("long", "short"):
        subset = best_subset(lambda e, d=d: e.get("direction") == d)
        wr, n  = wr_for(subset)
        if n >= WIN_RATE_MIN_SAMPLE:
            wrs["by_direction"][d] = {"wr": wr, "n": n}

    for mode in ("full", "exhaustion", "pullback"):
        subset = best_subset(lambda e, mode=mode: e.get("alignment_mode", "full") == mode)
        wr, n  = wr_for(subset)
        if n >= WIN_RATE_MIN_SAMPLE:
            wrs["by_alignment_mode"][mode] = {"wr": wr, "n": n}

    return wrs

_win_rates_cache:      dict | None = None
_win_rates_cache_lock  = threading.Lock()

def reset_win_rates_cache() -> None:
    global _win_rates_cache
    with _win_rates_cache_lock:
        _win_rates_cache = None

def get_cached_win_rates(state: dict) -> dict:
    global _win_rates_cache
    with _win_rates_cache_lock:
        if _win_rates_cache is None:
            _win_rates_cache = compute_win_rates(state)
        return _win_rates_cache

def compute_win_rate_analytics(state: dict, symbol: str, direction: str,
                                signal_type: str, score: int,
                                alignment_mode: str = "full") -> dict:
    wrs       = get_cached_win_rates(state)
    mode_data = wrs.get("by_alignment_mode", {}).get(alignment_mode)
    if mode_data:
        wr, n = mode_data["wr"], mode_data["n"]
    else:
        sym_data = wrs["by_symbol"].get(symbol)
        if sym_data:
            wr, n = sym_data["wr"], sym_data["n"]
        else:
            dir_data = wrs["by_direction"].get(direction)
            if dir_data:
                wr, n = dir_data["wr"], dir_data["n"]
            else:
                return {"win_rate": None, "sample_size": 0, "score_adj": 0,
                        "label": "Win Rate: Insufficient data"}
    if wr >= WIN_RATE_HIGH_THRESH:
        score_adj = 1
    elif wr <= WIN_RATE_LOW_THRESH:
        score_adj = -1
    else:
        score_adj = 0
    if n < WIN_RATE_MIN_SAMPLE_FOR_ADJ:
        return {"win_rate": wr, "sample_size": n, "score_adj": 0,
                "label": f"Win Rate: {wr*100:.0f}% (n={n}, insufficient for adj)"}
    # FIX-D16: Guard against recency bias — if recent_n (last 30d sample) is less than
    # half the minimum threshold, the history is too recency-dominated to be reliable.
    _recency_n = mode_data.get("recent_n", n) if mode_data else n
    if _recency_n < WIN_RATE_MIN_SAMPLE_FOR_ADJ * 0.5:
        return {"win_rate": wr, "sample_size": n, "score_adj": 0,
                "label": f"Win Rate: {wr*100:.0f}% (n={n}, recent_n={_recency_n} too low — neutral)"}  # FIX-D16
    return {"win_rate": wr, "sample_size": n, "score_adj": score_adj,
            "label": f"Win Rate: {wr*100:.0f}%  Sample: {n}  (30d weighted)"}

# ═══════════════════════════════════════════════════════════════
# ECONOMIC CALENDAR FILTER
# ═══════════════════════════════════════════════════════════════

MACRO_EVENT_KEYWORDS = [
    "fomc", "federal funds", "interest rate decision",
    "cpi", "consumer price index",
    "ppi", "producer price index",
    "nfp", "nonfarm payroll", "non-farm payroll",
    "gdp", "gross domestic product",
    "ecb", "bank of england", "boe",
]

MACRO_CALENDAR_URL = "https://nfs.faireconomy.media/ff_calendar_thisweek.json"

def parse_forexfactory_event_utc(ev_date: str, ev_time: str) -> datetime | None:
    try:
        if "day" in ev_time.lower() or ev_time.strip() == "":
            dt_str   = f"{ev_date} 14:00"
            dt_local = datetime.strptime(dt_str, "%Y-%m-%d %H:%M").replace(tzinfo=_FF_TZ)
        else:
            dt_str   = f"{ev_date} {ev_time}"
            dt_local = datetime.strptime(dt_str, "%Y-%m-%d %I:%M%p").replace(tzinfo=_FF_TZ)
        return dt_local.astimezone(timezone.utc)
    except Exception:
        return None

def fetch_macro_calendar(state: dict) -> list[dict]:
    # [P1-7] Thread-safe state access
    with _state_lock:
        cache_entry = state.get("macro_calendar_cache", {})
        cached_at   = cache_entry.get("fetched_at", 0)
    now_ts      = int(time.time())
    if now_ts - cached_at < MACRO_CACHE_TTL_S:
        return cache_entry.get("events", [])
    _macro_max_attempts = 3
    _macro_base_sleep   = 1.0
    raw_events = []
    for _attempt in range(_macro_max_attempts):
        try:
            resp = requests.get(MACRO_CALENDAR_URL, timeout=10)
            resp.raise_for_status()
            raw_events = resp.json()
            break
        except Exception as e:
            if _attempt == _macro_max_attempts - 1:
                print(f"  [MACRO CAL] fetch failed after {_macro_max_attempts} attempts: {e} — using cached/empty")
                return cache_entry.get("events", [])
            _sleep = min(10.0, _macro_base_sleep * (2 ** _attempt)) + random.uniform(0.0, 0.25)
            print(f"  [MACRO CAL] attempt {_attempt + 1} failed: {e} — retrying in {_sleep:.1f}s")
            time.sleep(_sleep)
    events = []
    for ev in raw_events:
        impact  = str(ev.get("impact", "")).lower()
        title   = str(ev.get("title",  "")).lower()
        ev_date = ev.get("date", "")
        ev_time = ev.get("time", "")
        if impact not in ("high",):
            continue
        if not any(kw in title for kw in MACRO_EVENT_KEYWORDS):
            continue
        dt_utc = parse_forexfactory_event_utc(ev_date, ev_time)
        if dt_utc is None:
            continue
        events.append({"name": ev.get("title", "Unknown event"),
                       "datetime_utc": dt_utc.isoformat(), "impact": impact})
    # [P1-7] Thread-safe state mutation
    with _state_lock:
        state["macro_calendar_cache"] = {"fetched_at": now_ts, "events": events}
    print(f"  [MACRO CAL] Loaded {len(events)} high-impact events")
    return events

def apply_macro_filter(state: dict, atr_pct: float,
                       reference_ms: int | None = None,
                       atr_pctile: float | None = None) -> dict:
    """Apply macro event filter.

    [Logic-22] hard_suppress threshold is now symbol-volatility-aware:
    if the symbol's ATR percentile is high (naturally volatile), the
    suppression threshold is raised so we don't over-suppress.
    """
    events      = fetch_macro_calendar(state)
    _ref_ts     = (reference_ms / 1000) if reference_ms is not None else time.time()
    now_utc     = datetime.fromtimestamp(_ref_ts, tz=timezone.utc)
    nearest_event = None
    nearest_mins  = None
    for ev in events:
        try:
            ev_dt = datetime.fromisoformat(ev["datetime_utc"])
        except Exception:
            continue
        mins_delta = (ev_dt - now_utc).total_seconds() / 60.0
        if -MACRO_WINDOW_AFTER_MINS <= mins_delta <= MACRO_WINDOW_BEFORE_MINS:
            if nearest_mins is None or abs(mins_delta) < abs(nearest_mins):
                nearest_event = ev["name"]
                nearest_mins  = mins_delta
    if nearest_event is None:
        return {"in_window": False, "event_name": None, "mins_to_event": None,
                "score_adj": 0, "label": "Macro Risk: None", "hard_suppress": False}

    # [Logic-22] Symbol-relative ATR threshold
    effective_threshold = MACRO_HIGH_ATR_SUPPRESS_PCT
    if atr_pctile is not None and atr_pctile > MACRO_ATR_PCTILE_HIGH:
        effective_threshold *= MACRO_ATR_PCTILE_HIGH_MULT

    score_adj     = -1
    hard_suppress = atr_pct >= effective_threshold
    if nearest_mins >= 0:
        label = f"⚠️ Macro Event Nearby\n{nearest_event} in {int(nearest_mins)} minutes"
    else:
        label = f"⚠️ Macro Event Nearby\n{nearest_event} {int(abs(nearest_mins))} minutes ago"
    return {"in_window": True, "event_name": nearest_event, "mins_to_event": nearest_mins,
            "score_adj": score_adj, "label": label, "hard_suppress": hard_suppress}

# ═══════════════════════════════════════════════════════════════
# INDICATOR MATH
# ═══════════════════════════════════════════════════════════════

def ema(values: list[float], period: int) -> list[float]:
    if len(values) < period:
        return [float("nan")] * len(values)
    k      = 2.0 / (period + 1)
    result = [float("nan")] * len(values)
    result[period - 1] = sum(values[:period]) / period
    for i in range(period, len(values)):
        result[i] = values[i] * k + result[i - 1] * (1 - k)
    return result

def rsi(closes: list[float], period: int) -> list[float]:
    if len(closes) < period + 1:
        return [float("nan")] * len(closes)
    result = [float("nan")] * len(closes)
    gains, losses = [], []
    for i in range(1, len(closes)):
        d = closes[i] - closes[i - 1]
        gains.append(max(d, 0))
        losses.append(max(-d, 0))
    avg_g = sum(gains[:period]) / period
    avg_l = sum(losses[:period]) / period
    rs    = avg_g / avg_l if avg_l != 0 else float("inf")
    result[period] = 100 - 100 / (1 + rs)
    for i in range(period, len(gains)):
        avg_g = (avg_g * (period - 1) + gains[i])  / period
        avg_l = (avg_l * (period - 1) + losses[i]) / period
        rs    = avg_g / avg_l if avg_l != 0 else float("inf")
        result[i + 1] = 100 - 100 / (1 + rs)
    return result

def atr(highs, lows, closes, period: int) -> list[float]:
    trs = [float("nan")]
    for i in range(1, len(closes)):
        tr = max(
            highs[i] - lows[i],
            abs(highs[i] - closes[i - 1]),
            abs(lows[i]  - closes[i - 1]),
        )
        trs.append(tr)
    result = [float("nan")] * len(closes)
    if len(trs) < period + 1:
        return result
    result[period] = sum(trs[1:period + 1]) / period
    for i in range(period + 1, len(trs)):
        result[i] = (result[i - 1] * (period - 1) + trs[i]) / period
    return result

def bollinger(closes, period: int, mult: float):
    """Compute Bollinger Bands.

    [Perf-27] Optimized from O(n×period) to O(n) using rolling sums.
    """
    n = len(closes)
    basis_arr = [float("nan")] * n
    upper_arr = [float("nan")] * n
    lower_arr = [float("nan")] * n
    if n < period:
        return basis_arr, upper_arr, lower_arr

    # [Perf-27] Rolling sum and sum-of-squares for O(n) computation
    rolling_sum = sum(closes[:period])
    rolling_sq_sum = sum(x * x for x in closes[:period])

    for i in range(period - 1, n):
        if i > period - 1:
            rolling_sum += closes[i] - closes[i - period]
            rolling_sq_sum += closes[i] * closes[i] - closes[i - period] * closes[i - period]

        m = rolling_sum / period
        # Variance = E[x²] - E[x]²  (population variance)
        var = max(0.0, rolling_sq_sum / period - m * m)
        sd = math.sqrt(var)
        basis_arr[i] = m
        upper_arr[i] = m + mult * sd
        lower_arr[i] = m - mult * sd

    return basis_arr, upper_arr, lower_arr

def adx_dmi(highs, lows, closes, period: int):
    n        = len(closes)
    plus_dm  = [0.0] * n
    minus_dm = [0.0] * n
    tr_arr   = [0.0] * n
    for i in range(1, n):
        up   = highs[i]    - highs[i - 1]
        down = lows[i - 1] - lows[i]
        plus_dm[i]  = up   if (up > down   and up > 0)   else 0
        minus_dm[i] = down if (down > up   and down > 0) else 0
        tr_arr[i]   = max(
            highs[i] - lows[i],
            abs(highs[i] - closes[i - 1]),
            abs(lows[i]  - closes[i - 1]),
        )

    def wilder_smooth(arr):
        res = [0.0] * n
        if n <= period:
            return res
        res[period] = sum(arr[1:period + 1])
        for i in range(period + 1, n):
            res[i] = res[i - 1] - res[i - 1] / period + arr[i]
        return res

    sm_tr   = wilder_smooth(tr_arr)
    sm_plus = wilder_smooth(plus_dm)
    sm_min  = wilder_smooth(minus_dm)

    di_plus  = [float("nan")] * n
    di_minus = [float("nan")] * n
    dx_arr   = [float("nan")] * n
    adx_arr  = [float("nan")] * n

    for i in range(period, n):
        if sm_tr[i] == 0:
            continue
        dp = 100 * sm_plus[i] / sm_tr[i]
        dm = 100 * sm_min[i]  / sm_tr[i]
        di_plus[i]  = dp
        di_minus[i] = dm
        dsum = dp + dm
        dx_arr[i] = 100 * abs(dp - dm) / dsum if dsum != 0 else 0

    first = next((i for i in range(period, n) if not math.isnan(dx_arr[i])), None)
    if first is None:
        return di_plus, di_minus, adx_arr
    seed_end = first + period
    if seed_end > n:
        return di_plus, di_minus, adx_arr
    valid = [dx_arr[i] for i in range(first, seed_end) if not math.isnan(dx_arr[i])]
    if len(valid) < period:
        return di_plus, di_minus, adx_arr
    adx_arr[seed_end - 1] = sum(valid) / period
    for i in range(seed_end, n):
        if not math.isnan(adx_arr[i - 1]) and not math.isnan(dx_arr[i]):
            adx_arr[i] = (adx_arr[i - 1] * (period - 1) + dx_arr[i]) / period
    return di_plus, di_minus, adx_arr

def obv(closes, volumes) -> list[float]:
    result = [0.0] * len(closes)
    for i in range(1, len(closes)):
        if closes[i] > closes[i - 1]:
            result[i] = result[i - 1] + volumes[i]
        elif closes[i] < closes[i - 1]:
            result[i] = result[i - 1] - volumes[i]
        else:
            result[i] = result[i - 1]
    return result

def detect_rsi_divergence(closes: list[float], rsi_values: list[float],
                          highs: list[float], lows: list[float],
                          lookback: int = 20) -> dict:
    """Detect RSI divergence.

    [Logic-21] Default lookback increased from 10 to 20 to capture
    divergences forming over 20+ bars (typical on 1H timeframe).
    """
    min_len = lookback + 2
    if (len(closes) < min_len or len(rsi_values) < min_len
            or len(highs) < min_len or len(lows) < min_len):
        return {"type": None, "strength": 0}

    recent_highs = highs[-(lookback + 2):]
    recent_lows  = lows[-(lookback + 2):]
    recent_rsi   = rsi_values[-(lookback + 2):]

    price_highs = []
    price_lows = []
    rsi_highs = []
    rsi_lows = []

    for i in range(1, len(recent_highs) - 1):
        if recent_highs[i] > recent_highs[i - 1] and recent_highs[i] > recent_highs[i + 1]:
            price_highs.append((i, recent_highs[i]))
            rsi_highs.append((i, recent_rsi[i]))
        if recent_lows[i] < recent_lows[i - 1] and recent_lows[i] < recent_lows[i + 1]:
            price_lows.append((i, recent_lows[i]))
            rsi_lows.append((i, recent_rsi[i]))

    bearish_div = False
    if len(price_highs) >= 2 and len(rsi_highs) >= 2:
        if (price_highs[-1][1] > price_highs[-2][1] and
            rsi_highs[-1][1] < rsi_highs[-2][1]):
            bearish_div = True

    bullish_div = False
    if len(price_lows) >= 2 and len(rsi_lows) >= 2:
        if (price_lows[-1][1] < price_lows[-2][1] and
            rsi_lows[-1][1] > rsi_lows[-2][1]):
            bullish_div = True

    if bearish_div:
        return {"type": "bearish", "strength": 1}
    elif bullish_div:
        return {"type": "bullish", "strength": 1}
    else:
        return {"type": None, "strength": 0}

def sma(values, period: int) -> list[float]:
    result = [float("nan")] * len(values)
    for i in range(period - 1, len(values)):
        result[i] = sum(values[i - period + 1: i + 1]) / period
    return result

def daily_vwap(candles_15m: list[dict], reference_ms: int | None = None) -> float:
    """Compute session-anchored daily VWAP.

    [Logic-23] Documented: VWAP resets at UTC midnight (00:00 UTC).
    This is the standard convention for crypto markets. The reset
    creates a discontinuity at midnight UTC, which is acceptable
    because the VWAP is used as a trend filter, not an execution
    benchmark. For Asian-session traders, this resets mid-day but
    is consistent across all symbols.
    """
    if not candles_15m:
        return 0.0
    ref_ms = int(time.time() * 1000) if reference_ms is None else reference_ms
    ref_dt = datetime.fromtimestamp(ref_ms / 1000, tz=timezone.utc)
    today_start = ref_dt.replace(hour=0, minute=0, second=0, microsecond=0)
    start_ms = int(today_start.timestamp() * 1000)
    today_candles = [c for c in candles_15m if c["t"] >= start_ms]
    if not today_candles:
        return safe(candles_15m[-1]["c"])
    total_vol = sum(c["v"] for c in today_candles)
    if total_vol == 0:
        return safe(candles_15m[-1]["c"])
    total_pv = sum(((c["h"] + c["l"] + c["c"]) / 3) * c["v"] for c in today_candles)  # FIX-D5
    return total_pv / total_vol

def safe(v, fallback=0.0):
    """Return fallback if v is None or NaN.

    [P0-3] Now handles non-numeric inputs gracefully via try/except.
    """
    try:
        if v is None:
            return fallback
        if isinstance(v, (int, float)) and math.isnan(v):
            return fallback
        return v
    except (TypeError, ValueError):
        return fallback

# ═══════════════════════════════════════════════════════════════
# INDICATOR CACHE  — [Perf-26]
# ═══════════════════════════════════════════════════════════════

_indicator_cache: dict[str, dict] = {}
_indicator_cache_lock = threading.Lock()

def _compute_all_indicators(candles: list[dict]) -> dict:
    """Compute all indicators for a single candle array."""
    o = [c["o"] for c in candles]
    h = [c["h"] for c in candles]
    l = [c["l"] for c in candles]
    c = [c["c"] for c in candles]
    v = [c["v"] for c in candles]

    _bb_basis, _bb_upper, _bb_lower = bollinger(c, BB_LEN, BB_MULT)
    return {
        "o": o, "h": h, "l": l, "c": c, "v": v,
        "ema_fast": ema(c, FAST_LEN),
        "ema_slow": ema(c, SLOW_LEN),
        "rsi": rsi(c, RSI_LEN),
        "atr": atr(h, l, c, ATR_LEN),
        "adx": adx_dmi(h, l, c, ADX_LEN),
        "bb_basis": _bb_basis,
        "bb_upper": _bb_upper,
        "bb_lower": _bb_lower,
        "vol_ma": sma(v, VOL_LEN),
        "obv": obv(c, v),
    }

def get_cached_indicators(symbol: str, timeframe: str, candles: list[dict]) -> dict:
    """Get indicators with caching.

    [Perf-26] Caches indicator results keyed by (symbol, timeframe, candle signature).
    Avoids recomputing all indicators from scratch when the same candle data
    is used across multiple scans.
    """
    if not candles:
        return _compute_all_indicators(candles)

    cache_key = f"{symbol}_{timeframe}"
    
    # [Fix-12] Hardened cache signature to include first/last candle prices.
    # Prevents stale cache hits if the same symbol is fetched with overlapping windows.
    first = candles[0]
    last = candles[-1]
    cache_sig = (
        len(candles),
        last["t"], last["c"],
        first["t"], first["c"],
    )

    with _indicator_cache_lock:
        cached = _indicator_cache.get(cache_key)
        if cached and cached.get("sig") == cache_sig:
            return cached["data"]

    data = _compute_all_indicators(candles)

    with _indicator_cache_lock:
        _indicator_cache[cache_key] = {"sig": cache_sig, "data": data}
        # Limit cache size
        if len(_indicator_cache) > 200:
            oldest_key = next(iter(_indicator_cache))
            del _indicator_cache[oldest_key]

    return data

def clear_indicator_cache() -> None:
    with _indicator_cache_lock:
        _indicator_cache.clear()

def _selftest_indicator_cache_isolation():
    """Ensure two different symbols do not share cached indicators."""
    a = [{"t": i, "o": 100+i, "h": 101+i, "l": 99+i, "c": 100+i, "v": 1.0, "qv": 100.0} for i in range(60)]
    b = [{"t": i, "o": 1+i*0.01, "h": 1.01+i*0.01, "l": 0.99+i*0.01, "c": 1+i*0.01, "v": 1.0, "qv": 1.0} for i in range(60)]
    ia = get_cached_indicators("SELFA", "15m", a)
    ib = get_cached_indicators("SELFB", "15m", b)
    assert ia["c"][-1] != ib["c"][-1], "Indicator cache is leaking across symbols!"

    # [Fix-46] Mirror the above for the "1d" timeframe now that daily ADX is
    # routed through get_cached_indicators() too — confirm daily indicators
    # don't leak across symbols either.
    da = [{"t": i, "o": 200+i, "h": 201+i, "l": 199+i, "c": 200+i, "v": 1.0, "qv": 200.0} for i in range(220)]
    db = [{"t": i, "o": 2+i*0.02, "h": 2.02+i*0.02, "l": 1.98+i*0.02, "c": 2+i*0.02, "v": 1.0, "qv": 2.0} for i in range(220)]
    iad = get_cached_indicators("SELFA_D", "1d", da)
    ibd = get_cached_indicators("SELFB_D", "1d", db)
    assert iad["c"][-1] != ibd["c"][-1], "Daily indicator cache is leaking across symbols!"

# ═══════════════════════════════════════════════════════════════
# STATE HELPERS
# ═══════════════════════════════════════════════════════════════

def update_atr_history(state: dict, symbol: str, atr_pct: float) -> None:
    with _state_lock:
        hist = state.setdefault("atr_history", {}).setdefault(symbol, [])
        hist.append({"ts": int(time.time()), "atr_pct": atr_pct})
        if len(hist) > ATR_HIST_DEPTH:
            state["atr_history"][symbol] = hist[-ATR_HIST_DEPTH:]

def get_atr_percentile(state: dict, symbol: str, atr_pct: float) -> float | None:
    with _state_lock:
        hist = list(state.get("atr_history", {}).get(symbol, []))
    vals = sorted(e["atr_pct"] for e in hist)
    if len(vals) < 10:
        return None
    below = sum(1 for v in vals if v < atr_pct)
    return below / len(vals)

def prune_state(state: dict) -> None:
    """Prune stale entries from state.

    [P1-7] All mutations now under _state_lock.
    """
    now = int(time.time())
    with _state_lock:
        for sym in list(state.get("oi_history", {}).keys()):
            state["oi_history"][sym] = [e for e in state["oi_history"][sym]
                                        if now - e["ts"] < 86400]
            if not state["oi_history"][sym]:
                del state["oi_history"][sym]

        cutoff_cooldown = now - PULL_REENTRY_COOLDOWN_S * 3
        state["post_loss_cooldown"] = {
            k: v for k, v in state.get("post_loss_cooldown", {}).items()
            if v > cutoff_cooldown
        }

        for sym in list(state.get("atr_history", {}).keys()):
            state["atr_history"][sym] = [
                e for e in state["atr_history"][sym]
                if now - e["ts"] < 86400
            ]
            if not state["atr_history"][sym]:
                del state["atr_history"][sym]

        state["resolved_signals"] = [
            e for e in state.get("resolved_signals", [])
            if now - e.get("resolved_at", 0) < 259200
        ]
        MAX_RESOLVED_SIGNALS = 500   # IMP-S18-9 — cap resolved signal list to bound RAM use
        if len(state.get("resolved_signals", [])) > MAX_RESOLVED_SIGNALS:
            state["resolved_signals"] = state["resolved_signals"][-MAX_RESOLVED_SIGNALS:]   # IMP-S18-9
            print(f"  [STATE PRUNE] resolved_signals capped to {MAX_RESOLVED_SIGNALS} entries")

        for sym in list(state.get("funding_history", {}).keys()):
            state["funding_history"][sym] = [
                e for e in state["funding_history"][sym]
                if now - e["ts"] < 7200
            ]
            if not state["funding_history"][sym]:
                del state["funding_history"][sym]

        current_bar = int(time.time() * 1000) // (15 * 60 * 1000)
        state["signal_cooldowns"] = {
            k: v for k, v in state.get("signal_cooldowns", {}).items()
            if current_bar - v < 96
        }

        cutoff_bar = current_bar - 96
        for sym in list(state.get("failed_breakouts", {}).keys()):
            state["failed_breakouts"][sym] = [
                fb for fb in state["failed_breakouts"][sym]
                if fb.get("bar_index", 0) > cutoff_bar
            ]
            if not state["failed_breakouts"][sym]:
                del state["failed_breakouts"][sym]

        state["active_signals"] = [
            s for s in state.get("active_signals", [])
            if current_bar - s.get("bar_index", current_bar) < SIGNAL_MAX_AGE_BARS
            and not s.get("resolved", False)
        ]

# ═══════════════════════════════════════════════════════════════
# SIGNAL LOGIC
# ═══════════════════════════════════════════════════════════════

class SignalResult:
    def __init__(self):
        self.fire_long   = False
        self.fire_short  = False
        self.signal_type = ""
        self.score       = 0
        self.final_score = 0
        self.entry = self.tp1 = self.tp2 = self.sl = 0.0
        self.entry_low = self.entry_high = 0.0
        self.atr_pct = 0.0
        self.atr_val  = 0.0
        self.breakdown = ""
        self.v10_gates = ""
        self.funding_rate:  float | None = None
        self.open_interest: float | None = None
        self.supports:    list[float] = []
        self.resistances: list[float] = []
        self.oi_trend_data:    dict = {}
        self.btc_regime_label: str  = ""
        self.breadth_label:    str  = ""
        self.rs_data:          dict = {}
        self.win_rate_data:    dict = {}
        self.macro_data:       dict = {}
        self.d200_label:       str  = ""
        self.vol_ratio:        float | None = None
        self.alignment_mode:   str  = "full"
        # [Fix-44] 3rd element is a stable category key ("btc_regime",
        # "oi_confirmation", "exhaustion", "rs_negative", or "secondary"/None)
        # used by the penalty-stacking cap instead of fragile label substring matching.
        self.score_adjustments: list[tuple[str, int, str | None]] = []
        self.limit_entry:       float | None = None
        self.limit_entry_dist:  float | None = None
        self.spread_pct:        float | None = None
        self.symbol:            str  = ""

def record_market_inputs_from_candles(symbol: str,
                                      candles_15m: list[dict],
                                      candles_4h: list[dict]) -> None:
    c15 = [c["c"] for c in candles_15m]
    c4h = [c["c"] for c in candles_4h]
    ema_s4h = ema(c4h, SLOW_LEN)
    _h4h_mid = (candles_4h[-1]["h"] + candles_4h[-1]["l"]) / 2   # IMP-S16-10 — midpoint reduces wick noise in trend-direction flag
    price_above_ema50_4h = _h4h_mid > safe(ema_s4h[-1])   # IMP-S16-10
    record_breadth_result(symbol, price_above_ema50_4h)
    # [Logic-19] Return None for insufficient history instead of 0.0
    if len(c4h) >= 42:
        ret_7d = (c4h[-1] - c4h[-42]) / c4h[-42] * 100.0 if c4h[-42] != 0 else 0.0
    elif len(c15) >= 672:
        ret_7d = (c15[-1] - c15[-672]) / c15[-672] * 100.0 if c15[-672] != 0 else 0.0
    else:
        ret_7d = 0.0
    record_rs_return(symbol, ret_7d)

def get_pull_recover_mult(btc_regime: dict | None) -> float:
    if btc_regime is None:
        return PULL_RECOVER_ATR_MULT_TREND
    bullish = btc_regime.get("bullish", False)
    bearish = btc_regime.get("bearish", False)
    mixed   = not bullish and not bearish
    if mixed:
        return PULL_RECOVER_ATR_MULT_MIXED
    return PULL_RECOVER_ATR_MULT_TREND

def get_effective_min_score(btc_regime: dict | None, breadth_pct: float) -> int:
    if btc_regime is None:
        return MIN_SCORE
    bearish = btc_regime.get("bearish", False)
    # [PATCH-6] Original condition (bearish AND breadth > 75%) was inverted for the
    # real risk case: a confirmed bear regime with near-capitulation breadth (<10%)
    # is the common loss environment and should raise the bar most. The old condition
    # never fired in observed data (breadth was 4%). Both branches now preserved.
    if bearish and breadth_pct < 0.10:
        return MIN_SCORE + 1   # confirmed bear + near-capitulation breadth
    if bearish and breadth_pct > 0.75:
        return MIN_SCORE + 1   # original condition preserved
    return MIN_SCORE

def get_dynamic_max_signals(btc_regime: dict | None, breadth_pct: float) -> int:
    if not USE_DYNAMIC_MAX_SIGNALS:
        return MAX_SIGNALS_PER_SCAN
    if btc_regime is None:
        return MAX_SIGNALS_DEFAULT
    bullish = btc_regime.get("bullish", False)
    bearish = btc_regime.get("bearish", False)
    if bullish and breadth_pct > BREADTH_BULL_THRESHOLD:
        return MAX_SIGNALS_BULL_TREND
    if bearish and breadth_pct < (1.0 - BREADTH_BULL_THRESHOLD):
        return MAX_SIGNALS_BULL_TREND
    return MAX_SIGNALS_DEFAULT

def get_pull_requires_4h(symbol: str, btc_regime: dict | None) -> bool:
    if symbol in PULL_REQUIRES_4H_OVERRIDE:
        return PULL_REQUIRES_4H_OVERRIDE[symbol]
    if btc_regime is not None:
        label = btc_regime.get("label", "")
        for key, val in PULL_REQUIRES_4H_OVERRIDE.items():
            if key in label:
                return val
    return PULL_REQUIRES_4H

def check_false_breakout_pattern(state: dict, symbol: str, direction: str,
                                 bar_index: int) -> tuple[bool, str]:
    if not USE_FALSE_BREAKOUT_DETECTION:
        return False, ""
    # [P1-7] Thread-safe state read
    with _state_lock:
        failed_breakouts_dict = state.get("failed_breakouts", {})
        symbol_breakouts = list(failed_breakouts_dict.get(symbol, []))
    for fb in symbol_breakouts:
        fb_direction = fb.get("direction")
        if fb_direction != direction:
            bars_since = bar_index - fb.get("bar_index", 0)
            if 1 <= bars_since <= FALSE_BREAKOUT_LOOKBACK_BARS:
                desc = f"False breakout re-entry ({fb_direction.upper()} BREAK failed {bars_since} bars ago)"
                return True, desc
    return False, ""

def record_failed_breakout(state: dict, symbol: str, direction: str,
                          signal_type: str, bar_index: int) -> None:
    if not USE_FALSE_BREAKOUT_DETECTION:
        return
    if signal_type != "BREAK":
        return
    # [P1-7] Thread-safe state mutation
    with _state_lock:
        failed_breakouts = state.setdefault("failed_breakouts", {})
        symbol_breakouts = failed_breakouts.setdefault(symbol, [])
        symbol_breakouts.append({
            "direction": direction,
            "bar_index": bar_index,
            "timestamp": int(time.time()),
        })
        cutoff_bar = bar_index - 96
        failed_breakouts[symbol] = [
            fb for fb in symbol_breakouts if fb.get("bar_index", 0) > cutoff_bar
        ]

# ═══════════════════════════════════════════════════════════════
# [Feature-50] REGIME-AWARE TP/SL MULTIPLIERS
# ═══════════════════════════════════════════════════════════════

def get_regime_aware_multipliers(btc_regime: dict | None,
                                  atr_pctile: float | None,
                                  signal_type: str) -> tuple[float, float, float]:
    """Return (tp1_mult, tp2_mult, sl_mult) adjusted for regime and volatility.

    [Feature-50] Scales TP/SL multipliers based on:
    - ATR percentile (high vol → widen TP, slightly tighten SL)
    - BTC regime (bull → extend TP2; bear → take TP1 earlier)
    """
    if signal_type == "BREAK":
        tp1_mult = TP1_MULT_BREAK
        tp2_mult = TP2_MULT_BREAK
        sl_mult  = SL_MULT_BREAK
    else:
        tp1_mult = TP1_MULT_PULL
        tp2_mult = TP2_MULT_PULL
        sl_mult  = SL_MULT_PULL

    if not USE_REGIME_AWARE_TP_SL:
        return tp1_mult, tp2_mult, sl_mult

    # High volatility regime: widen TPs, slightly tighten SL
    if atr_pctile is not None and atr_pctile > ATR_HIGH_PERCENTILE:
        tp1_mult *= REGIME_HIGH_VOL_TP1_MULT
        tp2_mult *= REGIME_HIGH_VOL_TP2_MULT
        sl_mult  *= REGIME_HIGH_VOL_SL_MULT

    # Low volatility regime: tighten TPs, slightly widen SL
    if atr_pctile is not None and atr_pctile < ATR_LOW_PERCENTILE:
        tp1_mult *= REGIME_LOW_VOL_TP1_MULT
        tp2_mult *= REGIME_LOW_VOL_TP2_MULT
        sl_mult  *= REGIME_LOW_VOL_SL_MULT

    # BTC regime adjustments
    if btc_regime is not None:
        if btc_regime.get("bearish"):
            tp1_mult *= REGIME_BEAR_TP1_MULT  # take profits earlier in bear
        if btc_regime.get("bullish"):
            tp2_mult *= REGIME_BULL_TP2_MULT  # extend TP2 in bull

    return tp1_mult, tp2_mult, sl_mult

# ═══════════════════════════════════════════════════════════════
# [Quality-37] DECOMPOSED SIGNAL COMPUTATION
# ═══════════════════════════════════════════════════════════════

def _compute_signal_indicators(symbol: str, candles_15m, candles_1h, candles_4h, candles_d) -> dict:
    """Extract all indicator values needed for signal computation.

    [Quality-37] Decomposed from the monolithic compute_signals function.
    [Fix-12] CRITICAL: pass the actual `symbol` to get_cached_indicators.
             Previously hardcoded "15m_temp"/"1h_temp"/"4h_temp" caused all
             symbols to share a single cache entry, so every coin inherited
             the first-cached symbol's (usually BTC's) OHLCV + indicators.
             Symptom: identical entry/TP/SL values across all pairs.
    """
    ind = {}

    # 15m indicators (cached)
    i15 = get_cached_indicators(symbol, "15m", candles_15m)
    ind["o15"], ind["h15"], ind["l15"], ind["c15"], ind["v15"] = i15["o"], i15["h"], i15["l"], i15["c"], i15["v"]
    ind["ema_f15"] = i15["ema_fast"]
    ind["ema_s15"] = i15["ema_slow"]
    ind["rsi15"]   = i15["rsi"]
    ind["atr15"]   = i15["atr"]
    ind["adx15_arr"] = i15["adx"][2]
    ind["bb_b15"], ind["bb_u15"], ind["bb_l15"] = i15["bb_basis"], i15["bb_upper"], i15["bb_lower"]
    ind["vol_ma15"] = i15["vol_ma"]
    ind["obv15"]    = i15["obv"]

    # 1H indicators
    i1h = get_cached_indicators(symbol, "1h", candles_1h)
    ind["ema_f1h"] = i1h["ema_fast"]
    ind["ema_s1h"] = i1h["ema_slow"]
    ind["rsi1h"]   = i1h["rsi"]
    ind["h1h"], ind["l1h"], ind["c1h"], ind["v1h"] = i1h["h"], i1h["l"], i1h["c"], i1h["v"]

    # 4H indicators
    i4h = get_cached_indicators(symbol, "4h", candles_4h)
    ind["ema_f4h"] = i4h["ema_fast"]
    ind["ema_s4h"] = i4h["ema_slow"]
    ind["adx4h_arr"] = i4h["adx"][2]
    ind["h4h"], ind["l4h"], ind["c4h"] = i4h["h"], i4h["l"], i4h["c"]
    ind["rsi4h"]   = i4h["rsi"]

    # Daily indicators
    if candles_d and len(candles_d) >= TREND_LEN:
        c_d = [c["c"] for c in candles_d]
        # [Fix-46] Route daily ADX through the indicator cache like every other
        # timeframe (15m/1h/4h), instead of recomputing adx_dmi from scratch
        # (200+ candles) on every single scan for every symbol.
        i_d = get_cached_indicators(symbol, "1d", candles_d)
        ind["ema_d200"] = ema(c_d, TREND_LEN)
        ind["adx_daily"] = safe(i_d["adx"][2][-1], 25.0)
    else:
        ind["ema_d200"] = None
        ind["adx_daily"] = 25.0

    return ind

def is_likely_reversal_disguised_as_pullback(ind, direction: str) -> bool:
    """
    Returns True if 2+ reversal signs are present — signal should be suppressed.
    Protects against RSI-collapse entries entering as pullbacks.
    """
    c15  = ind["c15"]
    r15  = safe(ind["rsi15"][-1])
    r1h  = safe(ind["rsi1h"][-1])
    ef4h = safe(ind["ema_f4h"][-1])
    es4h = safe(ind["ema_s4h"][-1])

    signals = []

    if direction == "long":
        signals.append(r15 < 42)              # 15m RSI below healthy pullback floor
        signals.append(r1h < 40)              # 1H RSI in bearish territory
        signals.append(ef4h < es4h)           # 4H actually flipped bearish
        signals.append(all(c15[-(i+1)] < c15[-(i+2)] for i in range(3)))  # 3 declining closes
    else:
        signals.append(r15 > 58)
        signals.append(r1h > 60)
        signals.append(ef4h > es4h)
        signals.append(all(c15[-(i+1)] > c15[-(i+2)] for i in range(3)))

    return sum(signals) >= 2  # Two or more reversal signs = suppress

def _detect_raw_signals(ind: dict, state: dict, reference_ms: int | None,
                         funding_rate: float | None, symbol: str = "?") -> SignalResult:
    """Detect raw BREAK/PULL signals and compute base score.

    [Quality-37] Decomposed from compute_signals.
    [Fix-11] Added 4H ADX as 6th base score component; raised gate from MIN_SCORE-1 to MIN_SCORE.
    """
    res = SignalResult()

    btc_regime = get_btc_regime()
    breadth_snap = compute_market_breadth()
    breadth_pct = breadth_snap["breadth_50_pct"]

    # Extract values
    o15, h15, l15, c15, v15 = ind["o15"], ind["h15"], ind["l15"], ind["c15"], ind["v15"]
    ema_f15, ema_s15 = ind["ema_f15"], ind["ema_s15"]
    rsi15_arr = ind["rsi15"]
    atr15_arr = ind["atr15"]
    adx15_arr = ind["adx15_arr"]
    bb_b15, bb_u15, bb_l15 = ind["bb_b15"], ind["bb_u15"], ind["bb_l15"]
    vol_ma15 = ind["vol_ma15"]
    obv15 = ind["obv15"]

    ef15 = safe(ema_f15[-1])
    es15 = safe(ema_s15[-1])
    r15  = safe(rsi15_arr[-1])
    a15  = safe(atr15_arr[-1], 25.0)
    adx15 = safe(adx15_arr[-1], 25.0)
    bb_basis   = safe(bb_b15[-1])
    bb_upper_v = safe(bb_u15[-1])
    bb_lower_v = safe(bb_l15[-1])
    vm15 = safe(vol_ma15[-1])

    cur_c = c15[-1]; cur_o = o15[-1]
    cur_h = h15[-1]; cur_l = l15[-1]
    cur_v = v15[-1]
    prev_l = l15[-2]; prev_h = h15[-2]

    atr_val  = a15 if a15 > 0 else (cur_c * ATR_FALLBACK_PCT / 100)
    atr_pct  = atr_val / cur_c * 100
    market_ok = MIN_ATR_PCT <= atr_pct <= MAX_ATR_PCT

    update_atr_history(state, symbol, atr_pct)

    rv         = daily_vwap(candles_15m_from_ind(ind), reference_ms=reference_ms)

    rsi_break_long  = RSI_BREAK_LONG_MIN  <= r15 <= RSI_BREAK_LONG_MAX
    rsi_break_short = RSI_BREAK_SHORT_MIN <= r15 <= RSI_BREAK_SHORT_MAX
    rsi_pull_long   = RSI_PULL_LONG_MIN   <= r15 <= RSI_PULL_LONG_MAX
    rsi_pull_short  = RSI_PULL_SHORT_MIN  <= r15 <= RSI_PULL_SHORT_MAX

    bb_mid_upper = (bb_basis + bb_upper_v) / 2 if bb_upper_v > 0 else bb_basis
    bb_mid_lower = (bb_basis + bb_lower_v) / 2 if bb_lower_v > 0 else bb_basis
    bb_long  = cur_c >= bb_mid_upper
    bb_short = cur_c <= bb_mid_lower

    obv_slope_long  = obv15[-1] > obv15[-(1 + OBV_LEN)]
    obv_slope_short = obv15[-1] < obv15[-(1 + OBV_LEN)]

    adx_score_ok = adx15 >= ADX_SCORE_MIN
    # [Fix-43] Fail closed: a zero/garbage 15m volume baseline (stale data, cache
    # warm-up, illiquid pair) should never grant an automatic pass on this
    # noise-rejection filter.
    vol_score_ok = False if vm15 == 0 else (cur_v >= vm15 * VOL_SCORE_MULT)
    vol_ratio    = (cur_v / vm15) if vm15 > 0 else None
    vol_ok_break_hard = (cur_v >= vm15 * VOL_SCORE_MULT) if vm15 > 0 else False   # IMP-S15-9 — hard gate, BREAK requires >= 1.0x avg volume

    _ref_ts_vol = (reference_ms / 1000) if reference_ms is not None else time.time()
    _is_weekend = datetime.fromtimestamp(_ref_ts_vol, tz=timezone.utc).weekday() >= 5
    _vol_accel_bars = 1 if _is_weekend else BREAK_VOL_ACCEL_BARS
    vol_accel_ok = all(
        cur_v > v15[-(i + 2)]
        for i in range(_vol_accel_bars)
    ) if len(v15) > _vol_accel_bars + 1 else False

    # vol_score_ok_pull is recomputed correctly once signal_type is known (see below).
    # FIX-D14: Compute PULL-appropriate vol flag now using PULL thresholds (0.10–1.30x).
    # Used in base-score for PULL candidates (proxy: long_pull/short_pull flags applied below).
    _PULL_VOL_RATIO_MIN_EARLY: float = 0.10
    _PULL_VOL_RATIO_MAX_EARLY: float = 1.30
    vol_score_ok_pull_early = (False if vm15 == 0
                               else _PULL_VOL_RATIO_MIN_EARLY <= (cur_v / vm15) <= _PULL_VOL_RATIO_MAX_EARLY)  # FIX-D14
    vol_score_ok_pull = vol_score_ok

    # 1H
    ef1h = safe(ind["ema_f1h"][-1]); es1h = safe(ind["ema_s1h"][-1])
    h1_bull = ef1h > es1h
    h1_bear = ef1h < es1h
    r1h = safe(ind["rsi1h"][-1])

    rsi_divergence = {"type": None, "strength": 0}
    if USE_1H_RSI_DIVERGENCE:
        rsi_divergence = detect_rsi_divergence(
            ind["c1h"], ind["rsi1h"], ind["h1h"], ind["l1h"], DIVERGENCE_LOOKBACK
        )

    # 4H
    ef4h = safe(ind["ema_f4h"][-1]); es4h = safe(ind["ema_s4h"][-1])
    adx4h = safe(ind["adx4h_arr"][-1], 25.0)
    h4_bull = ef4h > es4h
    h4_bear = ef4h < es4h

    # [Fix-11] 4H ADX as base score component
    adx4h_score_ok = adx4h >= ADX_SCORE_MIN  # 20.0

    def trend_held(ef_arr, es_arr, bull: bool) -> bool:
        for offset in range(1, TREND_HOLD_BARS + 1):
            idx = -(offset + 1)
            if len(ef_arr) < offset + 2:
                return False
            ef_v = safe(ef_arr[idx])
            es_v = safe(es_arr[idx])
            if bull and ef_v <= es_v:
                return False
            if not bull and ef_v >= es_v:
                return False
        return True

    def trend_held_for_break(ef_arr, es_arr, bull: bool) -> bool:
        """1-bar 4H EMA hold check — used for BREAK signals only."""
        for offset in range(1, TREND_HOLD_BARS_BREAK + 1):
            idx = -(offset + 1)
            if len(ef_arr) < offset + 2:
                return False
            ef_v = safe(ef_arr[idx])
            es_v = safe(es_arr[idx])
            if bull and ef_v <= es_v:
                return False
            if not bull and ef_v >= es_v:
                return False
        return True

    h4_trend_held_bull = trend_held(ind["ema_f4h"], ind["ema_s4h"], True)
    h4_trend_held_bear = trend_held(ind["ema_f4h"], ind["ema_s4h"], False)
    h4_trend_held_bull_break = trend_held_for_break(ind["ema_f4h"], ind["ema_s4h"], True)
    h4_trend_held_bear_break = trend_held_for_break(ind["ema_f4h"], ind["ema_s4h"], False)

    # IMP-S15-8 — require a stricter 3-bar 4H trend hold for PULL specifically when the
    # BTC regime is "mixed" (ambiguous higher timeframe + minimal confirmation is risky).
    _btc_label_s15_8 = (btc_regime or {}).get("label", "")
    _mixed_regime_s15_8 = "mixed" in _btc_label_s15_8.lower()
    _h4_hold_required_pull = 3 if _mixed_regime_s15_8 else TREND_HOLD_BARS   # IMP-S15-8

    def trend_held_for_pull(ef_arr, es_arr, bull: bool) -> bool:
        """Regime-aware 4H EMA hold check for PULL — stricter hold in mixed regime."""  # IMP-S15-8
        for offset in range(1, _h4_hold_required_pull + 1):
            idx = -(offset + 1)
            if len(ef_arr) < offset + 2:
                return False
            ef_v = safe(ef_arr[idx])
            es_v = safe(es_arr[idx])
            if bull and ef_v <= es_v:
                return False
            if not bull and ef_v >= es_v:
                return False
        return True

    h4_trend_held_bull_pull = trend_held_for_pull(ind["ema_f4h"], ind["ema_s4h"], True)    # IMP-S15-8
    h4_trend_held_bear_pull = trend_held_for_pull(ind["ema_f4h"], ind["ema_s4h"], False)   # IMP-S15-8

    # Daily 200 EMA + ADX
    if ind["ema_d200"] is not None:
        d200 = safe(ind["ema_d200"][-1])
    else:
        d200 = cur_c
    adx_daily = ind["adx_daily"]

    d200_above = cur_c > d200
    d200_below = cur_c < d200
    daily_adx_ok = adx_daily >= MIN_DAILY_ADX if USE_DAILY_ADX else True
    # [Fix-42] PULL signals use a separate, relaxed daily-ADX gate (default: not
    # required at all) — BREAK signals keep the original, stricter daily_adx_ok.
    # `daily_adx_ok` itself is unchanged so v10_gates/breakdown display strings
    # still reflect the real daily ADX state regardless of this flag.
    daily_adx_ok_pull = daily_adx_ok if DAILY_ADX_REQUIRED_FOR_PULL else True

    # Alignment gates
    full_long_align  = h4_bull and h4_trend_held_bull and h1_bull
    full_short_align = h4_bear and h4_trend_held_bear and h1_bear
    # BREAK-specific alignment (uses 1-bar trend hold)
    full_long_align_break  = h4_bull and h4_trend_held_bull_break and h1_bull
    full_short_align_break = h4_bear and h4_trend_held_bear_break and h1_bear

    _f4h_back = safe(ind["ema_f4h"][-(EXHAUSTION_SPREAD_LOOKBACK + 1)])
    _s4h_back = safe(ind["ema_s4h"][-(EXHAUSTION_SPREAD_LOOKBACK + 1)])
    h4_spread_now  = ef4h - es4h
    h4_spread_prev = _f4h_back - _s4h_back

    # 4H momentum quality check for PULL — is the trend spread healthy?
    atr4h_arr         = atr(ind["h4h"], ind["l4h"], ind["c4h"], ATR_LEN)
    atr4h_val         = safe(atr4h_arr[-1], 0.0)
    h4_spread_atr_ratio = abs(h4_spread_now) / atr4h_val if atr4h_val > 0 else 0.0
    h4_trend_momentum_ok = h4_spread_atr_ratio >= MIN_4H_SPREAD_ATR_MULT

    # [Logic-25] Renamed for clarity: spread_abs_narrowing means absolute spread is shrinking
    if USE_EXHAUSTION_SHORT:
        spread_abs_narrowing_bull = (abs(h4_spread_now) < abs(h4_spread_prev)) and (h4_spread_now > 0)
        exhaustion_short_align = (
            h4_bull
            and not h4_trend_held_bull
            and spread_abs_narrowing_bull
            and h1_bear
        )
    else:
        exhaustion_short_align = False

    if USE_EXHAUSTION_LONG:
        spread_abs_narrowing_bear = (abs(h4_spread_now) < abs(h4_spread_prev)) and (h4_spread_now < 0)
        exhaustion_long_align = (
            h4_bear
            and not h4_trend_held_bear
            and spread_abs_narrowing_bear
            and h1_bull
        )
    else:
        exhaustion_long_align = False

    # [New] Pullback alignment: 4H trend is healthy and HOLDING (not breaking down,
    # unlike exhaustion), but 1H has temporarily moved against it. This is the
    # "dip inside a held swing trend" case — PULL-only, never feeds BREAK.
    if USE_PULLBACK_ALIGNMENT:
        pullback_long_align  = h4_bull and h4_trend_held_bull_pull and h1_bear    # IMP-S15-8
        pullback_short_align = h4_bear and h4_trend_held_bear_pull and h1_bull    # IMP-S15-8
    else:
        pullback_long_align  = False
        pullback_short_align = False

    pull_long_align  = (h4_bull and h4_trend_held_bull_pull and h1_bull) \
                        if get_pull_requires_4h(symbol, btc_regime) else (h4_trend_held_bull_pull and h1_bull)
    pull_short_align = (
        (h4_bear and h4_trend_held_bear_pull and h1_bear)
        if get_pull_requires_4h(symbol, btc_regime)
        else (h4_trend_held_bear_pull and h1_bear)
    )
    if USE_EXHAUSTION_SHORT and exhaustion_short_align:
        pull_short_align = True
    if USE_EXHAUSTION_LONG and exhaustion_long_align:
        pull_long_align = True
    if USE_PULLBACK_ALIGNMENT and pullback_long_align:
        pull_long_align = True
    if USE_PULLBACK_ALIGNMENT and pullback_short_align:
        pull_short_align = True

    _is_pullback_long  = USE_PULLBACK_ALIGNMENT and pullback_long_align
    _is_pullback_short = USE_PULLBACK_ALIGNMENT and pullback_short_align
    vwap_long  = True if _is_pullback_long  else (cur_c > rv if USE_ROLLING_VWAP else True)
    vwap_short = True if _is_pullback_short else (cur_c < rv if USE_ROLLING_VWAP else True)

    rng = cur_h - cur_l + 1e-10

    def clean_bull_bar():
        return (cur_h - max(cur_o, cur_c)) / rng <= WICK_FILTER
    def clean_bear_bar():
        return (min(cur_o, cur_c) - cur_l) / rng <= WICK_FILTER
    def close_in_top_range():
        return (cur_c - cur_l) / rng >= (1.0 - RANGE_PCT_BREAK)
    def close_in_bot_range():
        return (cur_c - cur_l) / rng <= RANGE_PCT_BREAK

    # Soft ADX gate: pass if ADX >= 25, OR if ADX >= 20 and rising (momentum building)
    _adx15_arr  = ind["adx15_arr"]
    _adx15_prev = safe(_adx15_arr[-(1 + 3)], 25.0)   # ADX 3 closed bars ago
    adx_rising  = adx15 > _adx15_prev
    adx_break_ok = adx15 >= ADX_BREAK_GATE or (adx15 >= 20.0 and adx_rising)
    break_bull_bar = cur_c > cur_o and clean_bull_bar() and close_in_top_range()
    break_bear_bar = cur_c < cur_o and clean_bear_bar() and close_in_bot_range()

    pull_zone          = atr_val * PULL_ZONE_MULT
    pull_touched_long  = any(
        l15[-(i + 1)] <= safe(ema_f15[-(i + 1)]) + pull_zone
        for i in range(0, PULL_TOUCH_LOOKBACK + 1)
    )
    pull_touched_short = any(
        h15[-(i + 1)] >= safe(ema_f15[-(i + 1)]) - pull_zone
        for i in range(0, PULL_TOUCH_LOOKBACK + 1)
    )
    _pull_recover_mult  = get_pull_recover_mult(btc_regime)
    pull_recover_long   = (cur_c > ef15 + atr_val * _pull_recover_mult) and cur_c > cur_o
    pull_recover_short  = (cur_c < ef15 - atr_val * _pull_recover_mult) and cur_c < cur_o
    pull_bull_bar      = cur_c > cur_o and clean_bull_bar()
    pull_bear_bar      = cur_c < cur_o and clean_bear_bar()

    # [Fix-11] Base score now has 6 components (was 5): added 4H ADX confirmation
    # Max base score goes from 5 → 6, gate goes from MIN_SCORE-1 → MIN_SCORE (3→4)
    long_score = sum([
        bb_long,
        h4_bull and h4_trend_held_bull,
        adx_score_ok,
        obv_slope_long,
        vol_score_ok,
        adx4h_score_ok,  # NEW: 4H ADX confirmation
    ])
    short_score = sum([
        bb_short,
        h4_bear and h4_trend_held_bear,
        adx_score_ok,
        obv_slope_short,
        vol_score_ok,
        adx4h_score_ok,  # NEW: 4H ADX confirmation
    ])

    # [Fix-11] Gate raised from MIN_SCORE-1 to MIN_SCORE (proportionally with new 6th component)
    long_break  = (daily_adx_ok and (full_long_align_break or exhaustion_long_align) and break_bull_bar
                   and adx_break_ok and rsi_break_long and vol_ok_break_hard  # IMP-S15-9
                   and long_score  >= MIN_SCORE and market_ok)
    short_break = (daily_adx_ok
                   and (full_short_align_break or exhaustion_short_align)
                   and break_bear_bar
                   and adx_break_ok and rsi_break_short and vol_ok_break_hard  # IMP-S15-9
                   and short_score >= MIN_SCORE and market_ok)

    # Tier A Premium Pullback detection (highest win probability, +1 bonus)
    r4h = safe(ind["rsi4h"][-1])
    pull_tier_a_long = (
        h4_bull and h4_trend_held_bull_break      # 4H uptrend held (1-bar sufficient for Tier A)
        and 50.0 <= r4h <= 70.0                   # 4H RSI in healthy momentum zone
        and ef1h < es1h                           # 1H temporarily bearish = genuine pullback
        and 44.0 <= safe(ind["rsi15"][-1]) <= 54.0  # 15m RSI in mid-range bounce zone
        and cur_c > ef15                          # Recovering above EMA21
        and len(v15) >= 4                         # Need enough volume history for both checks
        and v15[-2] < v15[-3]                     # Pullback bar volume declining (healthy retracement)
        and v15[-1] > v15[-2]                     # Recovery bar volume expands (momentum confirmation)
    )
    pull_tier_a_short = (
        h4_bear and h4_trend_held_bear_break      # 4H downtrend held (1-bar sufficient for Tier A)
        and 30.0 <= r4h <= 50.0                   # 4H RSI in healthy momentum zone (symmetric)
        and ef1h > es1h                           # 1H temporarily bullish = genuine pullback
        and 46.0 <= safe(ind["rsi15"][-1]) <= 56.0  # 15m RSI in mid-range bounce zone (symmetric)
        and cur_c < ef15                          # Recovering below EMA21
        and len(v15) >= 4                         # Need enough volume history for both checks
        and v15[-2] < v15[-3]                     # Pullback bar volume declining (healthy retracement)
        and v15[-1] > v15[-2]                     # Recovery bar volume expands (momentum confirmation)
    )

    long_pull  = (daily_adx_ok_pull and pull_long_align and pull_touched_long
                  and pull_recover_long  and pull_bull_bar and vwap_long  and rsi_pull_long
                  and h4_trend_momentum_ok   # NEW: 4H trend must have meaningful spread
                  and long_score  >= MIN_SCORE and market_ok)
    short_pull = (daily_adx_ok_pull
                  and pull_short_align
                  and pull_touched_short
                  and pull_recover_short and pull_bear_bar and vwap_short and rsi_pull_short
                  and h4_trend_momentum_ok   # NEW: 4H trend must have meaningful spread
                  and short_score >= MIN_SCORE and market_ok)

    # Anti-reversal filter for PULL — suppress if 2+ reversal signs present
    if long_pull and is_likely_reversal_disguised_as_pullback(ind, "long"):
        long_pull = False

    if short_pull and is_likely_reversal_disguised_as_pullback(ind, "short"):
        short_pull = False

    long_sig  = long_break  or long_pull
    short_sig = short_break or short_pull

    # FIX-D14: Recompute base scores using PULL-appropriate vol flag for PULL candidates.
    # long_pull/short_pull are now known, so substitute vol_score_ok_pull_early for PULL paths.
    if long_pull and not long_break:
        long_score = sum([
            bb_long,
            h4_bull and h4_trend_held_bull,
            adx_score_ok,
            obv_slope_long,
            vol_score_ok_pull_early,   # FIX-D14 — use PULL vol flag for PULL candidates
            adx4h_score_ok,
        ])
    if short_pull and not short_break:
        short_score = sum([
            bb_short,
            h4_bear and h4_trend_held_bear,
            adx_score_ok,
            obv_slope_short,
            vol_score_ok_pull_early,   # FIX-D14 — use PULL vol flag for PULL candidates
            adx4h_score_ok,
        ])

    # Store all computed values for later use
    res._ind = ind
    res._ctx = {
        "btc_regime": btc_regime, "breadth_pct": breadth_pct,
        "r15": r15, "r1h": r1h, "adx15": adx15, "atr_val": atr_val, "atr_pct": atr_pct,
        "market_ok": market_ok, "d200": d200, "d200_above": d200_above, "d200_below": d200_below,
        "daily_adx_ok": daily_adx_ok, "vol_ratio": vol_ratio, "vol_accel_ok": vol_accel_ok,
        "vol_score_ok": vol_score_ok, "vol_score_ok_pull": vol_score_ok_pull,
        "h1_bull": h1_bull, "h1_bear": h1_bear, "h4_bull": h4_bull, "h4_bear": h4_bear,
        "h4_trend_held_bull": h4_trend_held_bull, "h4_trend_held_bear": h4_trend_held_bear,
        "full_long_align": full_long_align, "full_short_align": full_short_align,
        "exhaustion_short_align": exhaustion_short_align, "exhaustion_long_align": exhaustion_long_align,
        "pullback_long_align": pullback_long_align, "pullback_short_align": pullback_short_align,
        "rsi_divergence": rsi_divergence,
        "bb_long": bb_long, "bb_short": bb_short,
        "obv_slope_long": obv_slope_long, "obv_slope_short": obv_slope_short,
        "adx_score_ok": adx_score_ok, "adx4h": adx4h, "adx4h_score_ok": adx4h_score_ok,
        "ef15": ef15, "es15": es15, "ef1h": ef1h, "es1h": es1h, "ef4h": ef4h, "es4h": es4h,
        "candles_15m_len": len(c15),
        "atr4h_val": atr4h_val, "h4_spread_atr_ratio": h4_spread_atr_ratio,
        "pull_tier_a_long": pull_tier_a_long, "pull_tier_a_short": pull_tier_a_short,
        "funding_rate": funding_rate,
    }

    if long_sig:
        res.fire_long   = True
        if long_break and long_pull and pull_touched_long:
            # FIX-D12: Prefer BREAK when base score is at ceiling (strongest momentum)
            res.signal_type = "BREAK" if long_score >= 6 else "PULL"
        elif long_break:
            res.signal_type = "BREAK"
        else:
            res.signal_type = "PULL"
        res.score       = long_score
        _setup_signal_entry(res, cur_c, atr_val)
    elif short_sig:
        res.fire_short  = True
        if short_break and short_pull and pull_touched_short:
            # FIX-D12: Prefer BREAK when base score is at ceiling (strongest momentum)
            res.signal_type = "BREAK" if short_score >= 6 else "PULL"
        elif short_break:
            res.signal_type = "BREAK"
        else:
            res.signal_type = "PULL"
        res.score       = short_score
        _setup_signal_entry(res, cur_c, atr_val)

    # Recompute vol_score_ok_pull now that signal_type is known
    # [Fix-43] Same fail-closed pattern as vol_score_ok: a zero baseline must fail, not pass.
    # [PATCH-2] Fix dead branch. For PULL signals, healthy volume is LOW
    # (declining into the EMA is the classic retracement signature). Accept
    # any vol_ratio in [0.10, 1.30] as "healthy" for PULL display purposes.
    # Values > 1.30 on a pullback candle suggest distribution or reversal.
    # The base score still uses vol_score_ok (BREAK threshold, >= 0.75x) —
    # the PULL low-vol correction in _apply_scoring_and_filters (PATCH-3)
    # restores the missed base-score point for the 0.10–0.75x band.
    PULL_VOL_RATIO_MIN: float = 0.10
    PULL_VOL_RATIO_MAX: float = 1.30
    if res.fire_long or res.fire_short:
        res._ctx["vol_score_ok_pull"] = False if vm15 == 0 else (
            cur_v >= vm15 * VOL_SCORE_MULT if res.signal_type == "BREAK"
            else PULL_VOL_RATIO_MIN <= (cur_v / vm15) <= PULL_VOL_RATIO_MAX
        )

    return res

def candles_15m_from_ind(ind: dict) -> list[dict]:
    """Reconstruct candle list from indicator dict for VWAP."""
    candles = []
    for i in range(len(ind["c15"])):
        candles.append({"t": 0, "o": ind["o15"][i], "h": ind["h15"][i],
                        "l": ind["l15"][i], "c": ind["c15"][i], "v": ind["v15"][i]})
    return candles

def _setup_signal_entry(res: SignalResult, cur_c: float, atr_val: float):
    res.entry        = cur_c
    zone_half_width  = atr_val * PULL_ZONE_MULT
    res.entry_low    = cur_c - zone_half_width
    res.entry_high   = cur_c + zone_half_width
    res.atr_val      = atr_val

def is_likely_exhausted_break(ind: dict, atr_val: float, direction: str) -> bool:
    """
    Suppress BREAK if 2+ exhaustion signs are present simultaneously.
    Catches blow-off tops (long) and capitulation spikes (short).
    """
    c15 = ind["c15"]
    h15 = ind["h15"]
    l15 = ind["l15"]

    # 1. ATR expansion: current ATR >> recent average
    recent_atrs = [v for v in ind["atr15"][-20:] if not math.isnan(v)]
    avg_atr     = (sum(recent_atrs[:-3]) / len(recent_atrs[:-3])
                   if len(recent_atrs) > 3 else atr_val)
    atr_expanded = atr_val > avg_atr * 1.8

    # 2. Multi-bar extension: last 3 bars all moved in the same direction
    if direction == "long":
        multi_bar_ext = all(c15[-(i+1)] > c15[-(i+2)] for i in range(3))
    else:
        multi_bar_ext = all(c15[-(i+1)] < c15[-(i+2)] for i in range(3))

    # 3. RSI extreme: blow-off territory
    r15 = safe(ind["rsi15"][-1])
    rsi_extreme = (r15 > 78 and direction == "long") or (r15 < 22 and direction == "short")

    exhaustion_count = sum([atr_expanded, multi_bar_ext, rsi_extreme])
    return exhaustion_count >= 2

def continuation_score(ind, ctx, direction: str) -> int:
    """
    Score 0–6 using features already computed in ctx.
    Returns int. Score >= 4 = allow BREAK. Score <= 2 = suppress or penalise.
    """
    score = 0
    obv15 = ind["obv15"]
    OBV_LEN = 10

    if direction == "long":
        score += 1 if obv15[-1] > obv15[-(1 + OBV_LEN)] else 0          # OBV slope rising
        score += 1 if ctx.get("vol_ratio", 0) > 1.5 else 0               # Volume ratio > 1.5x MA
        r4h = safe(ind["rsi4h"][-1])
        score += 1 if 45.0 <= r4h <= 65.0 else 0                         # 4H RSI not extreme
        score += 1 if ctx.get("d200_above", False) else 0                 # Price above D200
        score += 1 if ctx.get("funding_rate", 0) < 0 else 0              # Negative funding (longs paid)
        score += 1 if (ctx.get("btc_regime") or {}).get("bullish", False) else 0  # FIX-D2
    else:
        score += 1 if obv15[-1] < obv15[-(1 + OBV_LEN)] else 0
        score += 1 if ctx.get("vol_ratio", 0) > 1.5 else 0
        r4h = safe(ind["rsi4h"][-1])
        score += 1 if 35.0 <= r4h <= 55.0 else 0
        score += 1 if not ctx.get("d200_above", True) else 0
        score += 1 if ctx.get("funding_rate", 0) > 0 else 0
        score += 1 if (ctx.get("btc_regime") or {}).get("bearish", False) else 0  # FIX-D2

    return score

def _apply_scoring_and_filters(res: SignalResult, state: dict,
                                symbol: str, reference_ms: int | None,
                                funding_rate: float | None,
                                candles_15m: list[dict]) -> SignalResult:
    """Apply all scoring adjustments and final filters.

    [Quality-37] Decomposed from compute_signals.
    [Fix-9] Added penalty stacking cap before final MIN_SCORE check.
    """
    ind = res._ind
    ctx = res._ctx
    btc_regime = ctx["btc_regime"]
    breadth_pct = ctx["breadth_pct"]

    if not (res.fire_long or res.fire_short):
        return res

    direction = "long" if res.fire_long else "short"
    cur_c = res.entry
    cur_o = ind["o15"][-1]
    cur_h = ind["h15"][-1]
    cur_l = ind["l15"][-1]
    cur_v = ind["v15"][-1]
    price_dir = "up" if cur_c > cur_o else "down"
    atr_val = res.atr_val
    atr_pct = (atr_val / cur_c * 100) if cur_c > 0 else res.atr_pct

    # ── Step 1: OI Confirmation ───────────────────────────────
    oi_data = compute_oi_trend(state, symbol, cur_c, price_dir, direction)
    res.oi_trend_data = oi_data
    adjusted_score = res.score + oi_data["score_adj"]
    adjs = res.score_adjustments
    if oi_data["score_adj"] != 0:
        adjs.append((f"OI ({oi_data['breakdown_tag']})", oi_data["score_adj"], "oi_confirmation"))

    oi_acceleration = oi_data.get("oi_acceleration")
    oi_trend        = oi_data.get("oi_trend", "unknown")
    oi_contribution = oi_data["score_adj"]

    if oi_acceleration is not None:
        if (oi_acceleration > OI_ACCEL_MIN_THRESHOLD
                and oi_trend == "rising"
                and oi_data["score_adj"] > 0
                and oi_contribution < OI_SCORE_CAP):
            adjusted_score += 1
            oi_contribution += 1
            adjs.append(("OI Acceleration (confirming↑)", 1, "oi_confirmation"))
        elif (oi_acceleration < -OI_ACCEL_MIN_THRESHOLD
                and oi_trend == "falling"
                and oi_data["score_adj"] < 0
                and oi_contribution > -OI_SCORE_CAP):
            adjusted_score -= 1
            oi_contribution -= 1
            adjs.append(("OI Acceleration (diverging↓)", -1, "oi_confirmation"))

    # ── Step 2: BTC Regime + Market Breadth ──────────────────
    btc_adj, btc_label = check_btc_regime_filter(direction, symbol, res.signal_type)
    res.btc_regime_label = btc_label
    adjusted_score += btc_adj
    if btc_adj != 0:
        adjs.append((btc_label, btc_adj, "btc_regime"))

    rs_data      = compute_relative_strength(symbol)
    res.rs_data  = rs_data

    breadth_adj, breadth_label = apply_breadth_adjustment(
        direction, rs_pct=rs_data.get("rs_pct"), btc_regime=btc_regime
    )
    res.breadth_label = breadth_label
    adjusted_score += breadth_adj
    if breadth_adj != 0:
        adjs.append((breadth_label, breadth_adj, "secondary"))

    # Exhaustion adjustments
    if (direction == "short"
            and USE_EXHAUSTION_SHORT
            and ctx["exhaustion_short_align"]
            and not ctx["full_short_align"]):
        if oi_data.get("oi_trend") == "falling":
            adjs.append(("Exhaustion + OI confirms (no penalty)", 0, "exhaustion"))
        else:
            adjusted_score += EXHAUSTION_SHORT_SCORE_ADJ
            adjs.append(("Exhaustion short mode (4H spread narrowing, not yet confirmed)",
                         EXHAUSTION_SHORT_SCORE_ADJ, "exhaustion"))

    if (direction == "long"
            and USE_EXHAUSTION_LONG
            and ctx["exhaustion_long_align"]
            and not ctx["full_long_align"]):
        if oi_data.get("oi_trend") == "rising":
            adjs.append(("Exhaustion + OI confirms (no penalty)", 0, "exhaustion"))
        else:
            adjusted_score += EXHAUSTION_LONG_SCORE_ADJ
            adjs.append(("Exhaustion long mode (4H spread narrowing, not yet confirmed)",
                         EXHAUSTION_LONG_SCORE_ADJ, "exhaustion"))

    # Pullback adjustments — 4H trend held (not breaking down), 1H temporarily against it.
    # Only applies when the signal didn't already qualify under full alignment.
    if (direction == "long" and USE_PULLBACK_ALIGNMENT
            and ctx["pullback_long_align"] and not ctx["full_long_align"]):
        # Only penalize if RS is negative OR 4H spread is thin — not blanket
        rs_neg        = rs_data.get("rs_pct") is not None and rs_data["rs_pct"] < -2.0
        momentum_weak = ctx.get("h4_spread_atr_ratio", 1.0) < 0.20
        if rs_neg or momentum_weak:
            adjusted_score -= 1
            adjs.append(("Pullback mode — weak RS or thin 4H spread", -1, "secondary"))
        # else: no penalty for clean pullback setup with good RS and healthy 4H spread

    if (direction == "short" and USE_PULLBACK_ALIGNMENT
            and ctx["pullback_short_align"] and not ctx["full_short_align"]):
        # Only penalize if RS is negative OR 4H spread is thin — not blanket
        rs_neg        = rs_data.get("rs_pct") is not None and rs_data["rs_pct"] > 2.0
        momentum_weak = ctx.get("h4_spread_atr_ratio", 1.0) < 0.20
        if rs_neg or momentum_weak:
            adjusted_score -= 1
            adjs.append(("Pullback mode — weak RS or thin 4H spread", -1, "secondary"))
        # else: no penalty for clean pullback setup with good RS and healthy 4H spread

    # Tier A Premium Pullback bonus — highest win probability setups
    if direction == "long" and ctx.get("pull_tier_a_long", False):
        adjusted_score += PULLBACK_PREMIUM_SCORE_ADJ
        adjs.append(("Tier A Premium Pullback (4H RSI healthy, 1H dip, 15m mid-range recovery)",
                     PULLBACK_PREMIUM_SCORE_ADJ, "secondary"))

    if direction == "short" and ctx.get("pull_tier_a_short", False):
        adjusted_score += PULLBACK_PREMIUM_SCORE_ADJ
        adjs.append(("Tier A Premium Pullback (4H RSI healthy, 1H bounce, 15m mid-range recovery)",
                     PULLBACK_PREMIUM_SCORE_ADJ, "secondary"))

    if direction == "short":
        if ctx["full_short_align"]:
            res.alignment_mode = "full"
        elif USE_EXHAUSTION_SHORT and ctx["exhaustion_short_align"]:
            res.alignment_mode = "exhaustion"
        elif USE_PULLBACK_ALIGNMENT and ctx["pullback_short_align"]:
            res.alignment_mode = "pullback"
        else:
            res.alignment_mode = "full"
    else:  # long
        if ctx["full_long_align"]:
            res.alignment_mode = "full"
        elif USE_EXHAUSTION_LONG and ctx["exhaustion_long_align"]:
            res.alignment_mode = "exhaustion"
        elif USE_PULLBACK_ALIGNMENT and ctx["pullback_long_align"]:
            res.alignment_mode = "pullback"
        else:
            res.alignment_mode = "full"

    # 4H stale bias
    _ref_ms       = reference_ms if reference_ms is not None else int(time.time() * 1000)
    iv_4h_ms      = 4 * 60 * 60 * 1000
    bar_open_4h_ms = (_ref_ms // iv_4h_ms) * iv_4h_ms
    bar_age_frac  = (_ref_ms - bar_open_4h_ms) / iv_4h_ms
    atr1h_val = safe(atr(ctx.get("h1h", ind["h1h"]), ctx.get("l1h", ind["l1h"]),
                         ctx.get("c1h", ind["c1h"]), ATR_LEN)[-1]) if len(ind["h1h"]) > ATR_LEN else 0.0
    _h1_spread    = (ctx["ef1h"] - ctx["es1h"]) / atr1h_val if atr1h_val > 0 else 0.0
    h4_stale_bias = (
        bar_age_frac >= H4_STALE_AGE_FRACTION
        and ((direction == "long"  and _h1_spread < H4_STALE_SPREAD_MIN)
          or (direction == "short" and _h1_spread > -H4_STALE_SPREAD_MIN))
    )
    _is_mixed_local = (btc_regime is not None
                       and not btc_regime.get("bullish")
                       and not btc_regime.get("bearish"))
    if h4_stale_bias and not _is_mixed_local:
        adjusted_score -= 1
        adjs.append((f"4H bias stale ({bar_age_frac*100:.0f}% into bar, 1H spread {_h1_spread:+.2f}x ATR)", -1, "secondary"))

    # ── Step 3: Relative Strength ─────────────────────────────
    adjusted_score += rs_data["score_adj"]
    if rs_data["score_adj"] != 0:
        adjs.append((rs_data["label"], rs_data["score_adj"], "secondary"))

    # ── Step 4: Historical Win Rate ───────────────────────────
    wr_data = compute_win_rate_analytics(
        state, symbol, direction, res.signal_type, res.score, res.alignment_mode
    )
    res.win_rate_data = wr_data
    adjusted_score += wr_data["score_adj"]
    if wr_data["score_adj"] != 0:
        adjs.append((wr_data["label"], wr_data["score_adj"], "secondary"))

    # ── Step 5: Macro Filter ──────────────────────────────────
    _atr_pctile = get_atr_percentile(state, symbol, atr_pct)
    macro_data = apply_macro_filter(state, atr_pct, reference_ms=reference_ms,
                                     atr_pctile=_atr_pctile)
    res.macro_data = macro_data
    if macro_data["hard_suppress"]:
        print(f"  [MACRO FILTER] {symbol} hard suppressed — elevated ATR + macro risk window")
        res.fire_long  = False
        res.fire_short = False
        return res
    adjusted_score += macro_data["score_adj"]
    if macro_data["score_adj"] != 0:
        adjs.append(("Macro Risk Window", macro_data["score_adj"], "secondary"))

    # ── Step 6b: Signal-type quality floors ───────────────────
    _step3_rs_adj = rs_data.get("score_adj", 0)   # FIX-D3 — track Step 3 RS charge to avoid double-counting
    res.supports, res.resistances = find_sr_levels(candles_15m, atr_val=atr_val)
    vol_ratio = ctx["vol_ratio"]
    vol_accel_ok = ctx["vol_accel_ok"]

    if res.signal_type == "PULL":
        vm15_apply = safe(ind["vol_ma15"][-1]) if "vol_ma15" in ind else 0.0
        cur_v_apply = ind["v15"][-1]
        # [PATCH-8] Removed price_dir == "down" guard. On a PULL entry bar price
        # is always "up" (green recovery bar is required by pull_recover_long), so
        # the original condition was structurally always False — OI falling on PULL
        # was never penalized. OI falling on the recovery bar means no institutional
        # longs are being added as price recovers: genuinely low conviction.
        _oi_falling_bearish = (
            oi_data.get("oi_trend") == "falling"
            and oi_data.get("score_adj", 0) == 0
        )
        if _oi_falling_bearish:
            adjusted_score -= 1
            adjs.append(("OI falling on PULL entry (no new longs on recovery)", -1, "secondary"))

        if vol_ratio is not None:
            _vol_floor = (PULL_VOL_FLOOR_OVERBOUGHT
                            if breadth_pct > PULL_VOL_OVERBOUGHT_BREADTH
                            else PULL_VOL_FLOOR)
            # Relax floor during Asian session — 0.30 is adequate in thin liquidity
            _ref_ts_s_d1 = (reference_ms / 1000) if reference_ms is not None else time.time()
            _utc_hour    = datetime.fromtimestamp(_ref_ts_s_d1, tz=timezone.utc).hour  # FIX-D1
            _asian_session = 0 <= _utc_hour < 8   # 00:00–08:00 UTC = Asian session low liquidity
            _effective_vol_floor = _vol_floor * 0.75 if _asian_session else _vol_floor
            if vol_ratio <= _effective_vol_floor:
                # Very low volume — lack of buyer conviction.
                adjusted_score -= 1
                adjs.append((f"Vol floor (ratio {vol_ratio:.2f}x <= {_effective_vol_floor:.2f}x"
                             f"{' overbought' if breadth_pct > PULL_VOL_OVERBOUGHT_BREADTH else ''}"
                             f"{' (Asian session relaxed)' if _asian_session else ''})", -1, "secondary"))
            elif vol_ratio < VOL_SCORE_MULT:
                # [PATCH-3] Mutually exclusive with floor check. Vol is between the
                # floor and the BREAK threshold (0.40x–0.75x): classic declining-volume
                # pullback signature. The base score penalised it (vol_score_ok failed),
                # restore +1 here. Floor fires ≤ 0.40x; this fires 0.40x < vol < 0.75x.
                # (Replaces the standalone _pull_vol_low_bonus_ok block above which was
                # non-mutually-exclusive — could add +1 and then immediately lose -1 on
                # the floor check for the same vol_ratio.)
                adjusted_score += 1
                adjs.append(("PULL low-vol correction (healthy pullback volume)", +1, "secondary"))

        candle_range = cur_h - cur_l
        body_size    = abs(cur_c - cur_o)
        body_ratio   = body_size / candle_range if candle_range > 0 else 1.0
        pull_body_ok = body_ratio >= PULL_BODY_MIN_RATIO
        if not pull_body_ok:
            adjusted_score -= 1
            adjs.append((f"Weak candle body (ratio {body_ratio:.2f} < {PULL_BODY_MIN_RATIO})", -1, "secondary"))

    if res.signal_type == "BREAK":
        # Continuation pre-filter — soft penalty for low continuation probability
        cont_score = continuation_score(ind, ctx, direction)
        if cont_score <= 2:
            adjusted_score -= 1
            adjs.append((f"Low continuation probability (score {cont_score}/6)", -1, "secondary"))

        if vol_ratio is not None and vol_ratio < BREAK_VOL_MULT:
            adjusted_score -= 1
            adjs.append((f"Break vol slightly low ({vol_ratio:.2f}x < {BREAK_VOL_MULT:.2f}x)", -1, "secondary"))
        if not vol_accel_ok:
            adjusted_score -= 1
            adjs.append(("Vol acceleration low", -1, "secondary"))

        # BREAK exhaustion check: penalise if 4H spread is narrowing after an extended move
        _h4_spread_now  = ctx["ef4h"] - ctx["es4h"]
        _h4_spread_prev = (safe(ind["ema_f4h"][-(EXHAUSTION_SPREAD_LOOKBACK + 1)])
                           - safe(ind["ema_s4h"][-(EXHAUSTION_SPREAD_LOOKBACK + 1)]))
        _spread_narrowing = abs(_h4_spread_now) < abs(_h4_spread_prev) * 0.85   # >15% narrowing
        _spread_extended  = abs(_h4_spread_now) / ctx.get("atr4h_val", 0) > 1.5 if ctx.get("atr4h_val", 0) > 0 else False
        if _spread_narrowing and _spread_extended:
            adjusted_score -= 1
            adjs.append(("4H spread contracting after extension (possible blow-off)", -1, "exhaustion"))

        if oi_data.get("oi_trend") == "flat" and (vol_ratio is None or vol_ratio < BREAK_OI_FLAT_VOL_THRESHOLD):
            adjusted_score -= 1
            adjs.append(("OI flat + low vol on BREAK (low conviction)", -1, "secondary"))

        rs_pct = rs_data.get("rs_pct")
        if rs_pct is not None:
            if rs_pct < RS_BREAK_HARD_GATE_PCT:
                print(f"  [RS GATE] {symbol} BREAK RS {rs_pct:+.1f}% < "
                      f"{RS_BREAK_HARD_GATE_PCT:.1f}% — applying penalty instead of hard suppress")
                _net_hard = min(RS_BREAK_HARD_GATE_PENALTY - _step3_rs_adj, 0)   # FIX-D3
                adjusted_score += _net_hard
                adjs.append((f"RS break hard gate (RS {rs_pct:+.1f}% < {RS_BREAK_HARD_GATE_PCT:.1f}%)",
                             _net_hard, "secondary"))
            elif rs_pct < 0:
                rs_percentile = rs_data.get("percentile")
                if rs_percentile is not None and rs_percentile <= RS_BREAK_SOFT_PERCENTILE:
                    _net_soft = min(-1 - _step3_rs_adj, 0)   # FIX-D3
                    adjusted_score += _net_soft
                    adjs.append((f"RS negative on BREAK ({rs_pct:+.1f}%, "
                                 f"{rs_percentile*100:.0f}th pct)", _net_soft, "rs_negative"))

    elif res.signal_type == "PULL":
        # [PATCH-4] PULL RS gate. BREAK has hard + soft gates; PULL had none.
        # A coin underperforming BTC on a PULL entry suggests structural weakness,
        # not healthy retracement. Softer thresholds than BREAK to preserve frequency.
        RS_PULL_SOFT_GATE_PCT: float = -2.0   # IMP-S17-10 — loosened from -1.0%; mild negative RS is normal in healthy rotation. Softer than BREAK's 0% bottom-pct check
        RS_PULL_HARD_GATE_PCT: float = -4.0   # softer than BREAK's -6.0%
        rs_pct = rs_data.get("rs_pct")
        if rs_pct is not None:
            if rs_pct < RS_PULL_HARD_GATE_PCT:
                _net_pull_hard = min(-2 - _step3_rs_adj, 0)   # FIX-D3
                adjusted_score += _net_pull_hard
                adjs.append((f"RS strongly negative on PULL ({rs_pct:+.1f}% < "
                             f"{RS_PULL_HARD_GATE_PCT:.1f}%)", _net_pull_hard, "rs_negative"))
            elif rs_pct < RS_PULL_SOFT_GATE_PCT:
                _net_pull_soft = min(-1 - _step3_rs_adj, 0)   # FIX-D3
                adjusted_score += _net_pull_soft
                adjs.append((f"RS negative on PULL ({rs_pct:+.1f}% < "
                             f"{RS_PULL_SOFT_GATE_PCT:.1f}%)", _net_pull_soft, "rs_negative"))

    if res.signal_type == "BREAK":
        if direction == "long" and res.resistances:
            nearest_res = res.resistances[0]
            if res.entry < nearest_res < res.tp1:
                tp_range = res.tp1 - res.entry
                if tp_range > 0:
                    blocked_pct = (nearest_res - res.entry) / tp_range
                    if blocked_pct >= TP1_WALL_MIN_CLEARANCE:
                        adjusted_score -= 1
                        adjs.append((f"Resistance blocks TP1 ({blocked_pct*100:.0f}%)", -1, "secondary"))
        elif direction == "short" and res.supports:
            nearest_sup = res.supports[0]
            if res.tp1 < nearest_sup < res.entry:
                tp_range = res.entry - res.tp1
                if tp_range > 0:
                    blocked_pct = (res.entry - nearest_sup) / tp_range
                    if blocked_pct >= TP1_WALL_MIN_CLEARANCE:
                        adjusted_score -= 1
                        adjs.append((f"Support blocks TP1 ({blocked_pct*100:.0f}%)", -1, "secondary"))

    if res.signal_type == "PULL":
        # [PATCH-5] PULL TP1 resistance wall check. Mirrors the BREAK check above.
        # PULL entries sit closer to recent swing lows, making resistance overhead
        # more likely to be within TP1 range. Uses the same TP1_WALL_MIN_CLEARANCE
        # threshold (0.40): resistance blocking ≥ 40% of path to TP1 degrades R:R.
        if direction == "long" and res.resistances:
            nearest_res = res.resistances[0]
            if res.entry < nearest_res < res.tp1:
                tp_range = res.tp1 - res.entry
                if tp_range > 0:
                    blocked_pct = (nearest_res - res.entry) / tp_range
                    if blocked_pct >= TP1_WALL_MIN_CLEARANCE:
                        adjusted_score -= 1
                        adjs.append((f"Resistance blocks PULL TP1 ({blocked_pct*100:.0f}%)", -1, "secondary"))
        elif direction == "short" and res.supports:
            nearest_sup = res.supports[0]
            if res.tp1 < nearest_sup < res.entry:
                tp_range = res.entry - res.tp1
                if tp_range > 0:
                    blocked_pct = (res.entry - nearest_sup) / tp_range
                    if blocked_pct >= TP1_WALL_MIN_CLEARANCE:
                        adjusted_score -= 1
                        adjs.append((f"Support blocks PULL TP1 ({blocked_pct*100:.0f}%)", -1, "secondary"))

    # ── Step 7: D200 Soft Bonus/Penalty ──────────────────────
    if USE_D200_FILTER:
        if direction == "long" and ctx["d200_above"]:
            adjusted_score += D200_SOFT_ADJ
            adjs.append((f"D200: Price above (+{D200_SOFT_ADJ})", D200_SOFT_ADJ, "secondary"))
            res.d200_label = f"D200: Price above (+{D200_SOFT_ADJ})"
        elif direction == "long" and ctx["d200_below"]:
            adjusted_score -= D200_SOFT_ADJ
            adjs.append((f"D200: Price below (-{D200_SOFT_ADJ})", -D200_SOFT_ADJ, "secondary"))
            res.d200_label = f"D200: Price below (-{D200_SOFT_ADJ})"
        elif direction == "short" and ctx["d200_below"]:
            adjusted_score += D200_SOFT_ADJ
            adjs.append((f"D200: Price below (+{D200_SOFT_ADJ})", D200_SOFT_ADJ, "secondary"))
            res.d200_label = f"D200: Price below (+{D200_SOFT_ADJ})"
        elif direction == "short" and ctx["d200_above"]:
            adjusted_score -= D200_SOFT_ADJ
            adjs.append((f"D200: Price above (-{D200_SOFT_ADJ})", -D200_SOFT_ADJ, "secondary"))
            res.d200_label = f"D200: Price above (-{D200_SOFT_ADJ})"
        else:
            res.d200_label = "D200: Neutral"
    else:
        res.d200_label = "D200: Disabled"

    # ── Step 8: Session / EMA velocity / RSI confluence / ATR pctile ─
    _ref_ts_s   = (reference_ms / 1000) if reference_ms is not None else time.time()
    _now_utc    = datetime.fromtimestamp(_ref_ts_s, tz=timezone.utc)
    _in_dead = SESSION_DEAD_ZONE_START_UTC <= _now_utc.hour < SESSION_DEAD_ZONE_END_UTC
    _atr_vals = [v for v in ind["atr15"][-(48 + ATR_LEN):] if not math.isnan(v)]
    if _atr_vals:
        _atr_pct_thresh = sorted(_atr_vals)[int(len(_atr_vals) * SESSION_LOW_ATR_PERCENTILE)]
    else:
        _atr_pct_thresh = atr_val
    _low_atr        = atr_val <= _atr_pct_thresh
    session_penalty = _in_dead and _low_atr and res.signal_type != "BREAK"   # IMP-S17-7 — BREAK exempt from dead-zone penalty
    if session_penalty:
        adjusted_score -= 1
        adjs.append((f"Low-liquidity session ({_now_utc.hour:02d}:xx UTC, thin ATR)", -1, "secondary"))

    ema_f15 = ind["ema_f15"]
    if len(ema_f15) >= EMA_VELOCITY_LOOKBACK + 2:
        _ef_velocity = (safe(ema_f15[-1]) - safe(ema_f15[-(1 + EMA_VELOCITY_LOOKBACK)])) / atr_val
        if res.signal_type == "BREAK":
            if _ef_velocity > EMA_VELOCITY_STRONG_MIN and direction == "long":
                adjusted_score += 1
                adjs.append((f"EMA accelerating up ({_ef_velocity:+.3f}×ATR)", +1, "secondary"))
            elif _ef_velocity < -EMA_VELOCITY_STRONG_MIN and direction == "short":
                adjusted_score += 1
                adjs.append((f"EMA accelerating down ({_ef_velocity:+.3f}×ATR)", +1, "secondary"))
            elif abs(_ef_velocity) < EMA_VELOCITY_WEAK_MAX:
                adjusted_score -= 1
                adjs.append((f"EMA flattening ({_ef_velocity:+.3f}×ATR) on BREAK", -1, "secondary"))

    rsi4h_arr = ind["rsi4h"]
    _r4h_raw  = rsi4h_arr[-1] if len(rsi4h_arr) >= 1 else float("nan")
    r4h_valid = not math.isnan(_r4h_raw)
    r4h       = _r4h_raw if r4h_valid else 50.0
    r15 = ctx["r15"]
    r1h = ctx["r1h"]

    rsi_divergence = ctx["rsi_divergence"]
    if USE_1H_RSI_DIVERGENCE and rsi_divergence["type"] is not None:   # FIX-D8
        div_type = rsi_divergence["type"]
        if res.signal_type in ("PULL", "BREAK") or res.alignment_mode == "exhaustion":
            if direction == "short" and div_type == "bearish":
                adjusted_score += DIVERGENCE_BONUS
                adjs.append(("1H RSI bearish divergence", DIVERGENCE_BONUS, "secondary"))
            elif direction == "long" and div_type == "bullish":
                adjusted_score += DIVERGENCE_BONUS
                adjs.append(("1H RSI bullish divergence", DIVERGENCE_BONUS, "secondary"))

    if USE_FALSE_BREAKOUT_DETECTION and res.signal_type == "PULL":
        _ref_ms_for_pattern = reference_ms if reference_ms is not None else int(time.time() * 1000)
        _bar_index_pattern = _ref_ms_for_pattern // (15 * 60 * 1000)
        is_false_breakout, fb_desc = check_false_breakout_pattern(state, symbol, direction, _bar_index_pattern)
        if is_false_breakout:
            adjusted_score += FALSE_BREAKOUT_BONUS
            adjs.append((fb_desc, FALSE_BREAKOUT_BONUS, "secondary"))

    # FIX-D17: rsi_15m_ok_long / rsi_15m_ok_short removed — redundant.
    # The 15m RSI range is already a hard gate in _detect_raw_signals; any signal
    # reaching this point has already passed it. Downstream code uses rsi_confluence_long/short
    # (1H/4H only) so these variables were dead assignments.

    rsi_1h_ok_long   = r1h <= RSI_1H_PULL_LONG_MAX
    rsi_4h_ok_long   = r4h <= RSI_4H_PULL_LONG_MAX
    rsi_1h_ok_short  = r1h >= RSI_1H_PULL_SHORT_MIN
    rsi_4h_ok_short  = r4h >= RSI_4H_PULL_SHORT_MIN
    rsi_confluence_long  = rsi_1h_ok_long  and rsi_4h_ok_long
    rsi_confluence_short = rsi_1h_ok_short and rsi_4h_ok_short

    if direction == "long":
        if rsi_confluence_long:
            adjusted_score += 1
            adjs.append(("RSI confluence 1H/4H", +1, "secondary"))
        elif r4h_valid and r4h > RSI_4H_PULL_LONG_MAX:
            adjusted_score -= 1
            adjs.append((f"4H RSI overbought ({r4h:.0f})", -1, "secondary"))

    if direction == "short":
        if rsi_confluence_short:
            adjusted_score += 1
            adjs.append(("RSI confluence 1H/4H", +1, "secondary"))
        elif r4h_valid and r4h < RSI_4H_PULL_SHORT_MIN:
            adjusted_score -= 1
            adjs.append((f"4H RSI oversold ({r4h:.0f})", -1, "secondary"))

    if _atr_pctile is not None:
        if res.signal_type == "BREAK" and _atr_pctile < ATR_LOW_PERCENTILE:
            adjusted_score -= 1
            adjs.append((f"ATR low vs symbol history ({_atr_pctile*100:.0f}th pct)", -1, "secondary"))
        elif res.signal_type == "PULL" and _atr_pctile > ATR_HIGH_PERCENTILE:
            adjusted_score -= 1
            adjs.append((f"ATR high vs symbol history ({_atr_pctile*100:.0f}th pct)", -1, "secondary"))

    # ── Step 9: S/R Proximity ──
    if res.signal_type == "PULL" and res.supports and direction == "long":
        nearest_sup = res.supports[0]
        if (res.entry - nearest_sup) < atr_val * SUPPORT_PROXIMITY_ATR:
            _rs_pct = rs_data.get("rs_pct")
            if _rs_pct is None or _rs_pct >= PROXIMITY_RS_MIN:
                adjusted_score += 1
                adjs.append(("Support proximity", +1, "secondary"))
            else:
                adjs.append((f"Support proximity skipped (RS {_rs_pct:+.1f}% < {PROXIMITY_RS_MIN:.0f}%)", 0, "secondary"))

    if res.signal_type == "PULL" and res.resistances and direction == "short":
        nearest_res = res.resistances[0]
        if (nearest_res - res.entry) < atr_val * SUPPORT_PROXIMITY_ATR:
            _rs_pct = rs_data.get("rs_pct")
            # For shorts: weakest RS (most negative) = best short target.
            # Gate is inverted vs longs — reward coins with RS <= -PROXIMITY_RS_MIN.
            _short_rs_ok = _rs_pct is None or _rs_pct <= -PROXIMITY_RS_MIN
            if _short_rs_ok:
                adjusted_score += 1
                adjs.append(("Resistance proximity", +1, "secondary"))
            else:
                adjs.append((f"Resistance proximity skipped (RS {_rs_pct:+.1f}% not weak enough)", 0, "secondary"))

    # ── Step 10: Funding Rate Adjustments ────────────────────
    # Tailwind carry bonus and headwind penalty are consolidated into a single
    # graduated block to prevent double-counting the same funding risk.
    if funding_rate is not None:
        rate = funding_rate
        tailwind = (rate < 0 and direction == "long") or (rate > 0 and direction == "short")
        headwind = (rate > 0 and direction == "long") or (rate < 0 and direction == "short")

        # Tailwind carry bonus (unchanged)
        if USE_FUNDING_CARRY and tailwind:
            if direction == "short" and rate >= FUNDING_CARRY_POSITIVE_THRESHOLD:
                adjusted_score += FUNDING_CARRY_BONUS
                adjs.append((f"Funding tailwind carry on {res.signal_type} ({rate*100:+.4f}%/8h)", FUNDING_CARRY_BONUS, "secondary"))
            elif direction == "long" and rate <= FUNDING_CARRY_NEGATIVE_THRESHOLD:
                adjusted_score += FUNDING_CARRY_BONUS
                adjs.append((f"Funding tailwind carry on {res.signal_type} ({rate*100:+.4f}%/8h)", FUNDING_CARRY_BONUS, "secondary"))

        # Consolidated headwind penalty — single graduated penalty, not two stacking ones.
        # Extreme rates are already hard-suppressed upstream in scan_symbol.
        if headwind and FUNDING_PULL_WARN_MIN is not None:
            abs_rate = abs(rate)
            _funding_trend = get_funding_trend(state, symbol)
            if abs_rate >= FUNDING_PULL_WARN_MIN:
                if _funding_trend == "rising":
                    # Rising headwind: elevated risk — apply −2 as a single unit
                    adjusted_score -= 2
                    adjs.append((f"Funding headwind rising on {res.signal_type} ({rate*100:+.4f}%/8h ↑)", -2, "secondary"))
                else:
                    # Stable headwind in warn zone: −1
                    adjusted_score -= 1
                    adjs.append((f"Funding headwind on {res.signal_type} ({rate*100:+.4f}%/8h)", -1, "secondary"))

    # ── Compute TP/SL with regime-aware multipliers ──────────
    # [Feature-50] Use regime-aware multipliers
    _tp1_m, _tp2_m, _sl_m = get_regime_aware_multipliers(
        btc_regime, _atr_pctile, res.signal_type
    )
    # Override SL for high ATR
    if atr_pct > HIGH_ATR_THRESHOLD:
        _sl_m = SL_HIGH_ATR_MULT

    if res.fire_long:
        res.tp1 = cur_c + atr_val * _tp1_m
        res.tp2 = cur_c + atr_val * _tp2_m
        res.sl  = cur_c - atr_val * _sl_m
        if res.signal_type == "PULL":
            _limit_px  = safe(ind["ema_f15"][-1])
            _limit_dist = (cur_c - _limit_px) / atr_val if atr_val > 0 else 0.0
            if _limit_px > 0 and 0 < _limit_dist <= PULL_LIMIT_MAX_ATR_DIST:
                res.limit_entry      = _limit_px
                res.limit_entry_dist = _limit_dist
    elif res.fire_short:
        res.tp1 = cur_c - atr_val * _tp1_m
        res.tp2 = cur_c - atr_val * _tp2_m
        res.sl  = cur_c + atr_val * _sl_m
        if res.signal_type == "PULL":
            _limit_px  = safe(ind["ema_f15"][-1])
            _limit_dist = (_limit_px - cur_c) / atr_val if atr_val > 0 else 0.0
            if _limit_px > 0 and 0 < _limit_dist <= PULL_LIMIT_MAX_ATR_DIST:
                res.limit_entry      = _limit_px
                res.limit_entry_dist = _limit_dist

    # [Logic-18] S/R adaptive TP1 override — check clearance BEFORE overriding
    # to avoid creating impossible R:R that gets killed by R:R filter
    if res.signal_type == "BREAK":
        if res.fire_long and res.resistances:
            sr_tp1  = res.resistances[0]
            atr_tp1 = res.entry + atr_val * _tp1_m
            # Only override if S/R gives a reasonable (not too tight) TP
            if res.entry < sr_tp1 < atr_tp1:
                sr_dist = (sr_tp1 - res.entry) / atr_val
                if sr_dist >= SR_CLEARANCE_ATR_MULT:
                    res.tp1 = sr_tp1
        elif res.fire_short and res.supports:
            sr_tp1  = res.supports[0]
            atr_tp1 = res.entry - atr_val * _tp1_m
            if atr_tp1 < sr_tp1 < res.entry:
                sr_dist = (res.entry - sr_tp1) / atr_val
                if sr_dist >= SR_CLEARANCE_ATR_MULT:
                    res.tp1 = sr_tp1

    if res.signal_type == "PULL":
        if res.fire_long and res.resistances:
            sr_tp1  = res.resistances[0]
            atr_tp1 = res.entry + atr_val * _tp1_m
            sr_dist = (sr_tp1 - res.entry) / atr_val
            if sr_dist >= SR_CLEARANCE_ATR_MULT:
                res.tp1 = min(sr_tp1, atr_tp1)
        elif res.fire_short and res.supports:
            sr_tp1  = res.supports[0]
            atr_tp1 = res.entry - atr_val * _tp1_m
            sr_dist = (res.entry - sr_tp1) / atr_val
            if sr_dist >= SR_CLEARANCE_ATR_MULT:
                res.tp1 = min(sr_tp1, atr_tp1)   # FIX-D7 — for shorts, lower price = better TP

    _rsi_conf_awarded = (direction == "long" and rsi_confluence_long) or \
                        (direction == "short" and rsi_confluence_short)
    if res.signal_type == "PULL" and not _rsi_conf_awarded:
        if direction == "long" and r1h > RSI_1H_PULL_LONG_MAX:
            adjusted_score -= 1
            adjs.append((f"1H RSI extended ({r1h:.0f} > {RSI_1H_PULL_LONG_MAX:.0f})", -1, "secondary"))
        elif direction == "short" and r1h < RSI_1H_PULL_SHORT_MIN:
            adjusted_score -= 1
            adjs.append((f"1H RSI extended ({r1h:.0f} < {RSI_1H_PULL_SHORT_MIN:.0f})", -1, "secondary"))

    # ══════════════════════════════════════════════════════════════
    # [Fix-9] PENALTY STACKING CAP
    # ══════════════════════════════════════════════════════════════
    # Prevent over-filtering from multiple penalties that partially measure
    # the same risk (e.g., OI counter-trend + BTC regime counter-trend).
    # Priority penalties (BTC Regime, OI, Exhaustion, RS negative) are kept
    # first; secondary penalties are trimmed to stay within the cap.
    total_neg = sum(adj for _, adj, *_ in adjs if adj < 0)
    if total_neg < -MAX_NEGATIVE_ADJUSTMENTS:
        # [Fix-44] Explicit category tags instead of substring matching against
        # the free-text label — substrings like "OI" used to incidentally match
        # unrelated penalties (e.g. "OI flat + low vol on BREAK") that aren't the
        # intended Step-1 OI confirmation/acceleration penalties.
        PENALTY_PRIORITY_CATEGORIES = {
            "btc_regime",       # Keep — most important macro filter
            "oi_confirmation",  # Keep — capital flow confirmation
            "exhaustion",       # Keep — trend quality
            "rs_negative",      # Keep — relative weakness
        }

        cap = -MAX_NEGATIVE_ADJUSTMENTS  # e.g., -3
        current_sum = 0
        kept_indices: set[int] = set()

        # FIX-D13: Reserve cap budget so RS hard gate doesn't zero out regime/OI/exhaustion penalties
        _RS_PENALTY_LABELS = {"rs_negative"}
        _rs_total = sum(adj for _, lbl, adj in [
            (i, lbl, adj) for i, (lbl, adj, cat) in enumerate(adjs)
            if adj < 0 and cat in PENALTY_PRIORITY_CATEGORIES and lbl in _RS_PENALTY_LABELS
        ])
        _non_rs_cap = max(cap, cap - _rs_total)  # budget left for non-RS priorities  # FIX-D13

        # First pass: keep priority penalties — sorted smallest-first so large
        # single penalties don't starve other priorities within the same class.
        priority_entries = [
            (i, lbl, adj) for i, (lbl, adj, cat) in enumerate(adjs)
            if adj < 0 and cat in PENALTY_PRIORITY_CATEGORIES
        ]
        priority_entries.sort(key=lambda x: abs(x[2]))  # smallest magnitude first
        for i, lbl, adj in priority_entries:
            _effective_cap = cap if lbl in _RS_PENALTY_LABELS else _non_rs_cap  # FIX-D13
            if current_sum + adj >= _effective_cap:
                kept_indices.add(i)
                current_sum += adj

        # Second pass: fill remaining budget with secondary penalties
        for i, (lbl, adj, cat) in enumerate(adjs):
            if adj < 0 and i not in kept_indices:
                if current_sum + adj >= cap:
                    kept_indices.add(i)
                    current_sum += adj

        # Rebuild adjs preserving original order — trim non-kept negatives
        trimmed_count = sum(1 for i, (_, adj, _cat) in enumerate(adjs)
                           if adj < 0 and i not in kept_indices)
        if trimmed_count > 0:
            new_adjs = [(lbl, adj, cat) for i, (lbl, adj, cat) in enumerate(adjs)
                        if adj >= 0 or i in kept_indices]
            adjs[:] = new_adjs
            adjusted_score = res.score + sum(adj for _, adj, _cat in adjs)
            print(f"  [PENALTY CAP] {symbol} {direction.upper()} — "
                  f"trimmed {trimmed_count} secondary penalty(ies) to stay within "
                  f"-{MAX_NEGATIVE_ADJUSTMENTS} cap. Final neg total: {current_sum}")

    # ══════════════════════════════════════════════════════════════
    # [Fix-47] BONUS (POSITIVE ADJUSTMENT) STACKING CAP
    # ══════════════════════════════════════════════════════════════
    # Symmetric soft cap on the bonus portion only (relative to res.score, not
    # absolute), so signals with a high base score aren't unfairly capped.
    total_pos = sum(adj for _, adj, *_ in adjs if adj > 0)
    if total_pos > MAX_POSITIVE_ADJUSTMENTS:
        excess = total_pos - MAX_POSITIVE_ADJUSTMENTS
        adjusted_score -= excess
        print(f"  [BONUS CAP] {symbol} {direction.upper()} — trimmed {excess} excess "
              f"positive adjustment(s) to stay within +{MAX_POSITIVE_ADJUSTMENTS} cap.")

    # ── Final suppression check ───────────────────────────────
    res.final_score = adjusted_score
    res.atr_pct     = atr_pct
    res.vol_ratio   = vol_ratio

    # Build breakdown string
    vol_score_ok_pull = ctx.get("vol_score_ok_pull", True)
    # [Logic-11] Use unified vol_score_ok_pull for display consistency
    bb_s  = "BB✓"  if (ctx["bb_long"]  if res.fire_long else ctx["bb_short"])  else "BB✗"
    d_s   = "4H✓"  if (ctx["h4_bull"] and ctx["h4_trend_held_bull"] if res.fire_long
                       else ctx["h4_bear"] and ctx["h4_trend_held_bear"]) else "4H✗"
    adx_s = "ADX✓" if ctx["adx_score_ok"]  else "ADX✗"
    obv_s = "OBV✓" if (ctx["obv_slope_long"] if res.fire_long else ctx["obv_slope_short"]) else "OBV✗"
    vol_s = "VOL✓" if vol_score_ok_pull else "VOL✗"
    # [Logic-12] Only show VA for BREAK signals
    if res.signal_type == "BREAK":
        accel_s = "VA✓" if vol_accel_ok else "VA✗"
        res.breakdown = f"{bb_s} {d_s} {adx_s} {obv_s} {vol_s} {oi_data['breakdown_tag']} {accel_s}"
    else:
        res.breakdown = f"{bb_s} {d_s} {adx_s} {obv_s} {vol_s} {oi_data['breakdown_tag']}"

    # Build gates string
    h1 = ctx["h1_bull"] if res.fire_long else ctx["h1_bear"]
    if res.fire_long and ctx["exhaustion_long_align"] and not ctx["full_long_align"]:
        h4_tag = "4H:⚠"
    elif not res.fire_long and ctx["exhaustion_short_align"] and not ctx["full_short_align"]:
        h4_tag = "4H:⚠"
    elif res.fire_long and ctx["pullback_long_align"] and not ctx["full_long_align"]:
        h4_tag = "4H:✓"  # 4H held fine — it's 1H that pulled back, shown via h1_tag below
    elif not res.fire_long and ctx["pullback_short_align"] and not ctx["full_short_align"]:
        h4_tag = "4H:✓"
    else:
        h4_tag = f"4H:{'✓' if (ctx['full_long_align'] if res.fire_long else ctx['full_short_align']) else '✗'}"

    if res.alignment_mode == "pullback":
        h1_tag = "1H:↩ (pullback)"
    else:
        h1_tag = f"1H:{'✓' if h1 else '✗'}"
    res.v10_gates = (f"DailyADX:{'✓' if ctx['daily_adx_ok'] else '✗'} {h4_tag} {h1_tag}")

    _effective_min = get_effective_min_score(btc_regime, breadth_pct)
    if adjusted_score < _effective_min:
        print(f"  [SCORE FILTER] {symbol} {direction.upper()} suppressed: "
              f"base={res.score} → final={adjusted_score} < {_effective_min}"
              f"{' (regime-adjusted)' if _effective_min > MIN_SCORE else ''}")
        res.fire_long  = False
        res.fire_short = False
        return res

    # R:R filter
    _tp1_dist = abs(res.tp1 - res.entry)
    _sl_dist  = abs(res.sl  - res.entry)
    if _sl_dist > 0 and (_tp1_dist / _sl_dist) < MIN_RR_RATIO:
        print(f"  [RR FILTER] {symbol} {direction.upper()} suppressed — "
              f"R:R {_tp1_dist/_sl_dist:.2f} < {MIN_RR_RATIO} "
              f"(TP1={res.tp1:.4f} entry={res.entry:.4f} SL={res.sl:.4f})")
        res.fire_long  = False
        res.fire_short = False
        return res

    # Exhausted-break suppressor
    if res.signal_type == "BREAK" and res.fire_long:
        if is_likely_exhausted_break(ind, ctx["atr_val"], "long"):
            res.fire_long = False   # Suppress — likely blow-off top
            print(f"  [EXHAUSTION FILTER] {symbol} BREAK LONG suppressed — likely blow-off top")

    if res.signal_type == "BREAK" and res.fire_short:
        if is_likely_exhausted_break(ind, ctx["atr_val"], "short"):
            res.fire_short = False  # Suppress — likely capitulation spike
            print(f"  [EXHAUSTION FILTER] {symbol} BREAK SHORT suppressed — likely capitulation spike")

    # S/R clearance filter — PULL only.
    # For BREAK signals, the entry IS at/past S/R by design; applying this filter
    # would suppress legitimate breakouts. Only PULL entries approaching S/R from
    # inside the range benefit from this clearance gate.
    if SR_CLEARANCE_ATR_MULT_PULL > 0 and res.signal_type == "PULL" and (res.fire_long or res.fire_short):
        min_clearance = atr_val * SR_CLEARANCE_ATR_MULT_PULL
        if res.fire_long and res.resistances:
            nearest_res = res.resistances[0]
            if nearest_res - res.entry < min_clearance:
                print(f"  [SR FILTER] {symbol} PULL LONG suppressed — resistance {nearest_res:.4f} "
                      f"too close to entry {res.entry:.4f}")
                res.fire_long = False
        if res.fire_short and res.supports:
            nearest_sup = res.supports[0]
            if res.entry - nearest_sup < min_clearance:
                print(f"  [SR FILTER] {symbol} PULL SHORT suppressed — support {nearest_sup:.4f} "
                      f"too close to entry {res.entry:.4f}")
                res.fire_short = False

    # Clean up temporary attributes
    if hasattr(res, '_ind'):
        del res._ind
    if hasattr(res, '_ctx'):
        del res._ctx

    return res

# FIX-D20: _check_early_break() removed — dead code (was never called).
# Re-implement when live in-progress candle fetch is available.
# Wire output to advisory Telegram channel only, not live signal channel.
# Run in paper-trade/log-only mode for ≥2 weeks before activating live.
# Track in GitHub issue for future implementation.

def compute_signals(symbol, candles_15m, candles_1h, candles_4h, candles_d,
                    state: dict, record_market_inputs: bool = True,
                    reference_ms: int | None = None,
                    funding_rate: float | None = None) -> SignalResult:
    """Main signal computation entry point.

    [Quality-37] Decomposed into:
      1. _compute_signal_indicators — extract all indicator values
      2. _detect_raw_signals — detect BREAK/PULL and compute base score
      3. _apply_scoring_and_filters — apply all adjustments and final filters
    """
    res = SignalResult()
    res.symbol = symbol

    if not candles_15m or len(candles_15m) < 50:
        return res

    # Phase 1: Compute indicators
    # [Fix-12] Pass the actual symbol down to prevent cache cross-contamination
    ind = _compute_signal_indicators(symbol, candles_15m, candles_1h, candles_4h, candles_d)

    if record_market_inputs:
        record_market_inputs_from_candles(symbol, candles_15m, candles_4h)

    # Phase 2: Detect raw signals
    res = _detect_raw_signals(ind, state, reference_ms, funding_rate, symbol)
    res.symbol = symbol

    # Early BREAK advisory (FIX-D20): _check_early_break() removed — see comment above.
    # Re-enable when live in-progress candle fetch is implemented.

    if not (res.fire_long or res.fire_short):
        return res

    # Phase 3: Apply scoring adjustments and final filters
    res = _apply_scoring_and_filters(res, state, symbol, reference_ms,
                                      funding_rate, candles_15m)

    return res

# ═══════════════════════════════════════════════════════════════
# COOLDOWN STATE
# ═══════════════════════════════════════════════════════════════

def _migrate_state(old: dict, target_version) -> dict:    # IMP-S18-2
    """Preserve key history fields across state schema version bumps, instead of
    silently dropping all historical state when `_version` changes."""
    new = {
        "_version": target_version,
        "oi_history": {}, "signal_history": [], "macro_calendar_cache": {},
        "post_loss_cooldown": {}, "atr_history": {}, "funding_history": {},
        "signal_cooldowns": {}, "last_signal_outcome": {},
        "failed_breakouts": {}, "active_signals": [], "resolved_signals": [],
        "spread_history": {},
    }
    for field in ("signal_history", "resolved_signals", "post_loss_cooldown",
                  "oi_history", "spread_history"):
        if field in old:
            new[field] = old[field]
    return new   # IMP-S18-2

def load_state() -> dict:
    _fresh = {
        "_version": STATE_VERSION,
        "oi_history": {}, "signal_history": [], "macro_calendar_cache": {},
        "post_loss_cooldown": {}, "atr_history": {}, "funding_history": {},
        "signal_cooldowns": {}, "last_signal_outcome": {},
        "failed_breakouts": {}, "active_signals": [], "resolved_signals": [],
        "spread_history": {},
    }
    for path in (STATE_FILE, STATE_FILE + ".bak"):
        if Path(path).exists():
            try:
                s = json.loads(Path(path).read_text())
                if s.get("_version", 1) != STATE_VERSION:
                    print(f"[STATE] Schema version mismatch in {path} — migrating state "
                          f"(preserving signal/resolved/cooldown/oi/spread history)")  # IMP-S18-2
                    s = _migrate_state(s, STATE_VERSION)   # IMP-S18-2
                s.setdefault("oi_history", {})
                s.setdefault("signal_history", [])
                s.setdefault("macro_calendar_cache", {})
                s.setdefault("post_loss_cooldown", {})
                s.setdefault("atr_history", {})
                s.setdefault("funding_history", {})
                s.setdefault("signal_cooldowns", {})
                s.setdefault("last_signal_outcome", {})
                s.setdefault("failed_breakouts", {})
                s.setdefault("active_signals", [])
                s.setdefault("resolved_signals", [])
                s.setdefault("spread_history", {})
                if path != STATE_FILE:
                    print(f"[STATE] Loaded from backup {path}")
                return s
            except Exception as e:
                print(f"[STATE] Failed to load {path}: {e}")
    print("[STATE] Starting fresh — no valid state file found")
    return _fresh

def save_state(state: dict):
    # [P1-7] Thread-safe state save with RLock
    with _state_lock:
        state_copy = copy.deepcopy(state)
    tmp_path = STATE_FILE + ".tmp"
    Path(tmp_path).write_text(json.dumps(state_copy, indent=2))
    os.replace(tmp_path, STATE_FILE)
    try:
        import shutil
        shutil.copy2(STATE_FILE, STATE_FILE + ".bak")
    except Exception:
        pass

def check_cooldown(state, coin, direction, bar_index, signal_type: str = "",
                   candidate_score: int = 0) -> bool:
    symbol = coin if coin.endswith("USDT") else coin + "USDT"

    # [P1-7] Thread-safe state read
    with _state_lock:
        active = list(state.get("active_signals", []))
        _cd_key    = f"{symbol}_{direction}_{signal_type}" if signal_type in ("BREAK", "PULL") else f"{symbol}_{direction}"
        last_bar   = state.get("signal_cooldowns",  {}).get(_cd_key)
        # FIX-D4: look up type-specific post-loss cooldown; fall back to bare key for legacy entries
        _pl_cd = state.get("post_loss_cooldown", {})
        _type_specific_cd_key = f"{symbol}_{direction}_{signal_type}" if signal_type in ("BREAK", "PULL") else None
        last_sl_ts = (_pl_cd.get(_type_specific_cd_key) if _type_specific_cd_key else None) or _pl_cd.get(f"{symbol}_{direction}")
        prev_outcome = state.get("last_signal_outcome", {}).get(f"{symbol}_{direction}", "unknown")

    # [Risk-31] Check max concurrent active signals
    active_count = sum(1 for s in active if not s.get("resolved", False))
    if active_count >= MAX_CONCURRENT_ACTIVE_SIGNALS:
        print(f"  [MAX CONCURRENT] {hl_coin(symbol)} {direction.upper()} blocked — "
              f"{active_count} active signals (max {MAX_CONCURRENT_ACTIVE_SIGNALS})")
        return False

    for sig in active:
        if sig.get("symbol") == symbol and not sig.get("resolved", False):
            if sig.get("direction") == direction:
                return False

    if last_bar is not None:
        bars_elapsed = bar_index - last_bar
        if prev_outcome in ("tp1", "tp2"):
            required_bars = SIGNAL_COOLDOWN_POST_WIN_BARS
        elif candidate_score >= SIGNAL_HIGHSCORE_THRESHOLD:
            required_bars = SIGNAL_COOLDOWN_BARS_HIGHSCORE
        else:
            _regime_label_s16_9 = (get_btc_regime() or {}).get("label", "")
            _bear_regime_s16_9 = "bear" in _regime_label_s16_9.lower()
            required_bars = SIGNAL_COOLDOWN_BARS if _bear_regime_s16_9 else 1   # IMP-S16-9 — 1 bar (15min) in neutral/bull, 2 bars in bear

        if bars_elapsed < required_bars:
            remaining_bars = required_bars - bars_elapsed
            print(f"  [BAR COOLDOWN] {hl_coin(symbol)} {direction.upper()} "
                  f"{signal_type} (score={candidate_score}) blocked — "
                  f"{remaining_bars} bar(s) remaining (need {required_bars})")
            return False

    if last_sl_ts is not None:
        elapsed = int(time.time()) - last_sl_ts
        if elapsed < PULL_REENTRY_COOLDOWN_S:
            remaining = PULL_REENTRY_COOLDOWN_S - elapsed
            print(f"  [POST-LOSS COOLDOWN] {hl_coin(symbol)} {direction.upper()} "
                  f"{signal_type} blocked — {remaining}s remaining after SL")
            return False

    return True

def update_cooldown(state, coin, direction, bar_index, signal_type: str = ""):
    symbol = coin if coin.endswith("USDT") else coin + "USDT"
    cooldown_key = (f"{symbol}_{direction}_{signal_type}"
                    if signal_type in ("BREAK", "PULL")
                    else f"{symbol}_{direction}")
    # [P1-7] Thread-safe state mutation
    with _state_lock:
        state.setdefault("signal_cooldowns", {})[cooldown_key] = bar_index

# ═══════════════════════════════════════════════════════════════
# TELEGRAM
# ═══════════════════════════════════════════════════════════════

def stars(score: int) -> str:
    capped = max(0, min(score, 8))
    return "★" * capped + "☆" * (8 - capped)

def _sanitize_error(e: Exception) -> str:
    """Sanitize error messages to prevent token/URL leakage.

    [P0-5] Strips Telegram bot tokens and API URLs from exception messages.
    """
    msg = str(e)
    # Remove bot token patterns
    if "bot" in msg and "/" in msg:
        # Truncate any URL-like string
        import re
        msg = re.sub(r'https?://[^\s]+', '[URL]', msg)
    # Also handle the class name approach
    return f"{e.__class__.__name__}: {msg[:200]}"

def send_telegram(text: str) -> int | None:
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/sendMessage"
    for attempt in range(3):
        try:
            r = requests.post(url, json={
                "chat_id":    TG_CHAT_ID,
                "text":       text,
                "parse_mode": "HTML",
            }, timeout=10)
            r.raise_for_status()
            return r.json()["result"]["message_id"]
        except Exception as e:
            if attempt == 2:
                # [P0-5] Sanitized error — no token leak
                print(f"[TG ERROR] {_sanitize_error(e)}")
            time.sleep(2)
    return None

def react_to_message(message_id: int, emoji: str) -> bool:
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/setMessageReaction"
    try:
        r = requests.post(url, json={
            "chat_id":    TG_CHAT_ID,
            "message_id": message_id,
            "reaction":   [{"type": "emoji", "emoji": emoji}],
            "is_big":     False,
        }, timeout=10)
        r.raise_for_status()
        print(f"  [REACT] {emoji} → msg_id {message_id}")
        return True   # IMP-S18-3
    except Exception as e:
        # [P0-5] Sanitized error
        print(f"  [REACT ERROR] msg_id {message_id}: {_sanitize_error(e)}")
        return False   # IMP-S18-3

_tg_react_failures: dict[int, int] = {}   # IMP-S18-3 — module-level per-msg_id failure tracker
TG_REACT_MAX_FAILURES = 3   # IMP-S18-3

def react_to_message_safe(msg_id: int, *args, **kwargs):    # IMP-S18-3
    """Rate-limits react_to_message(): stops retrying a msg_id that has failed
    TG_REACT_MAX_FAILURES times in a row, to avoid flooding the Telegram API
    with calls for a single permanently-invalid msg_id."""
    if _tg_react_failures.get(msg_id, 0) >= TG_REACT_MAX_FAILURES:
        return   # silently skip permanently-failing msg_ids
    ok = react_to_message(msg_id, *args, **kwargs)
    if not ok:
        _tg_react_failures[msg_id] = _tg_react_failures.get(msg_id, 0) + 1
        print(f"  [REACT] msg_id={msg_id} failure count now "
              f"{_tg_react_failures[msg_id]}/{TG_REACT_MAX_FAILURES}")

RANK_MEDALS = {1: "🥇", 2: "🥈", 3: "🥉"}

def priority_score(sig: SignalResult) -> tuple:
    direction = "long" if sig.fire_long else "short"
    rate      = sig.funding_rate
    tailwind  = False if rate is None else (
        (rate < 0 and direction == "long") or (rate > 0 and direction == "short")
    )
    sig_type_wr = sig.win_rate_data.get("win_rate") or 0.5
    oi_confirm  = sig.oi_trend_data.get("score_adj", 0) > 0
    return (sig.final_score, round(sig_type_wr, 2), int(tailwind), int(oi_confirm), sig.symbol)

def format_signal(symbol: str, sig: SignalResult, engine_tag: str = "V5", rank: int = 0) -> str:
    direction = "▲ LONG" if sig.fire_long else "▼ SHORT"
    dir_str   = "long" if sig.fire_long else "short"
    emoji     = "🟢" if sig.fire_long else "🔴"
    ts        = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    def fmt(v):
        if v >= 1000: return f"{v:,.2f}"
        if v >= 1:    return f"{v:.4f}"
        return f"{v:.6f}"

    pull_entry_block = ""
    if sig.signal_type == "PULL" and sig.limit_entry is not None:
        pct_tgt = int(PULL_LIMIT_TRANCHE_PCT * 100)
        pct_now = 100 - pct_tgt
        pull_entry_block = (
            f"\n<b>📌 Split Entry Plan (PULL)</b>\n"
            f"  Tranche A ({pct_now}%):  Market @ <code>{fmt(sig.entry)}</code>\n"
            f"  Tranche B ({pct_tgt}%):  Limit  @ <code>{fmt(sig.limit_entry)}</code>  "
            f"(EMA21, {sig.limit_entry_dist:.2f}× ATR below)\n"
        )

    spread_line = ""
    if sig.spread_pct is not None:
        spread_tag = ("⚠️ elevated" if sig.spread_pct >= SPREAD_WARN_PCT else "✅ tight")
        spread_line = f"\nSpread/Liquidity: {sig.spread_pct:.3f}%  {spread_tag}"

    def _leverage_for_risk_pct(atr_pct: float, score: int, signal_type: str,
                               account_risk_pct: float) -> float:
        sl_atr_mult = SL_HIGH_ATR_MULT if atr_pct > HIGH_ATR_THRESHOLD else (
            SL_MULT_BREAK if signal_type == "BREAK" else SL_MULT_PULL
        )
        # [Fix-39] Dropped the stray /100.0 here. account_risk_pct (e.g. 2.0,
        # meaning "2%") and atr_pct (e.g. 1.5, meaning "1.5%") are both already
        # in the same "percent-number" convention used elsewhere in this file
        # (see HIGH_ATR_THRESHOLD comparisons above). Dividing sl_pct down into
        # a 0-1 fraction while leaving account_risk_pct un-scaled made the ratio
        # ~100x too large, so leverage saturated at LEVERAGE_MAX for virtually
        # any nonzero ATR% instead of producing a real 1x-10x gradient.
        sl_pct = atr_pct * sl_atr_mult
        if sl_pct <= 0:
            return 1.0
        max_lev = account_risk_pct / sl_pct
        lev = min(max(1.0, max_lev), LEVERAGE_MAX)
        if score <= 4:
            lev = max(1.0, lev * 0.8)
        return lev

    def recommended_leverage(atr_pct: float, score: int, signal_type: str) -> str:
        lev = _leverage_for_risk_pct(atr_pct, score, signal_type, LEVERAGE_BASE_RISK_PCT)
        return f"{lev:.1f}x"

    def recommended_leverage_range(atr_pct: float, score: int, signal_type: str) -> str:
        lo = _leverage_for_risk_pct(atr_pct, score, signal_type, LEVERAGE_RANGE_LOW_RISK_PCT)
        hi = _leverage_for_risk_pct(atr_pct, score, signal_type, LEVERAGE_RANGE_HIGH_RISK_PCT)
        lo_i = max(1, min(int(round(lo)), int(LEVERAGE_MAX)))
        hi_i = max(1, min(int(round(hi)), int(LEVERAGE_MAX)))
        if lo_i > hi_i:
            lo_i, hi_i = hi_i, lo_i
        if lo_i == hi_i:
            return f"{lo_i}x"
        return f"{lo_i}x\u2013{hi_i}x"

    lev_range    = recommended_leverage(sig.atr_pct, sig.final_score, sig.signal_type)
    lev_band     = recommended_leverage_range(sig.atr_pct, sig.final_score, sig.signal_type)
    funding_str  = format_funding(sig.funding_rate, dir_str)
    rate         = sig.funding_rate
    headwind     = rate is not None and (
        (rate > 0 and dir_str == "long") or (rate < 0 and dir_str == "short")
    )
    chk_funding  = "⚠️" if (headwind and rate is not None and abs(rate) >= FUNDING_SUPPRESS_EXTREME) else "✅"

    sr_lines = ""
    if sig.resistances:
        sr_lines += "🔴 Resistance: " + "  |  ".join(f"<code>{fmt(r)}</code>" for r in sig.resistances) + "\n"
    if sig.supports:
        sr_lines += "🟢 Support:    " + "  |  ".join(f"<code>{fmt(s)}</code>" for s in sig.supports) + "\n"

    oi_data      = sig.oi_trend_data
    oi_line      = oi_data.get("label", "OI Trend: Unknown")
    btc_line     = sig.btc_regime_label or "BTC Regime: Unknown"
    breadth_line = sig.breadth_label    or "Market Breadth: Unknown"
    rs_line      = sig.rs_data.get("label", "Relative Strength: N/A")
    wr_line      = sig.win_rate_data.get("label", "Win Rate: N/A")
    macro_line   = sig.macro_data.get("label", "Macro Risk: None") if sig.macro_data else "Macro Risk: None"
    d200_line    = sig.d200_label or "D200: Unknown"
    vol_ratio_line = (f"Volume Ratio: {sig.vol_ratio:.1f}x" if sig.vol_ratio is not None
                      else "Volume Ratio: N/A")

    score_trail = ""
    if sig.score_adjustments:
        parts = []
        for lbl, adj, *_ in sig.score_adjustments:
            sign = "+" if adj > 0 else ""
            safe_lbl = lbl.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            parts.append(f"{safe_lbl}: {sign}{adj}")
        score_trail = "\n<i>Adjustments: " + "  |  ".join(parts) + "</i>"

    sr_block     = f"\n{sr_lines}" if sr_lines else ""
    medal        = RANK_MEDALS.get(rank, "")
    rank_tag     = f"{medal} <b>Priority #{rank}</b>\n" if rank else ""
    counter_tag  = "⚠️ " if "counter-trend" in (sig.btc_regime_label or "") else ""

    return (
        f"{rank_tag}{counter_tag}{emoji} <b>{direction} [{sig.signal_type}]</b>  {stars(sig.final_score)}\n"
        f"<b>Pair:</b>  {symbol}\n\n"
        f"<b>Entry:</b> <code>{fmt(sig.entry)}</code>\n"
        f"<b>Entry Zone:</b> <code>{fmt(sig.entry_low)}</code> – <code>{fmt(sig.entry_high)}</code>\n"
        f"{pull_entry_block}"
        f"\n<b>TP1:</b>   <code>{fmt(sig.tp1)}</code>\n"
        f"<b>TP2:</b>   <code>{fmt(sig.tp2)}</code>\n"
        f"<b>SL:</b>    <code>{fmt(sig.sl)}</code>\n\n"
        f"<b>Leverage:</b> {lev_range}\n"
        f"<b>Leverage Range:</b> {lev_band}\n"
        f"<b>Score:</b> {sig.final_score}/{sig.score}+adj  |  {sig.breakdown}\n"
        f"<b>Gates:</b> {sig.v10_gates}\n"
        f"\n<b>Signal Context</b>\n"
        f"{oi_line}\n"
        f"{btc_line}\n"
        f"{breadth_line}\n"
        f"{rs_line}\n"
        f"{wr_line}\n"
        f"{macro_line}\n"
        f"{d200_line}\n"
        f"{vol_ratio_line}"
        f"{spread_line}"
        f"{score_trail}"
        f"{sr_block}\n"
        f"<b>Pre-Trade Checklist</b>\n"
        f"✅ Trend identified (4H/1H/15m aligned)\n"
        f"{'✅' if sig.supports or sig.resistances else '☐'} Key S/R marked\n"
        f"✅ Clear entry signal ({sig.signal_type}, score {sig.final_score}/{sig.score}+adj)\n"
        f"✅ Leverage appropriate ({lev_range})\n"
        f"{chk_funding} {funding_str}\n"
        f"📊 {format_oi(sig.open_interest)}\n\n"
        f"<i>Scalp Swing v{__version__} [4H/15m] • Hyperliquid Perps • {ts}</i>"
    )

# ═══════════════════════════════════════════════════════════════
# ACTIVE SIGNAL TRACKING
# ═══════════════════════════════════════════════════════════════

def track_signal(state: dict, symbol: str, direction: str,
                 msg_id: int, sig: SignalResult, bar_index: int,
                 hist_id: str | None = None):
    # [P1-7] Thread-safe state mutation
    with _state_lock:
        active = state.setdefault("active_signals", [])
        active.append({
            "symbol":          symbol,
            "direction":       direction,
            "msg_id":          msg_id,
            "bar_index":       bar_index,
            "signal_bar_time": bar_index * 900_000,
            "tp1":             sig.tp1,
            "tp2":             sig.tp2,
            "sl":              sig.sl,
            "tp1_hit":         False,
            "resolved":        False,
            "hist_id":         hist_id,
            "signal_type":     sig.signal_type,
        })

def check_active_signals(state: dict, bar_index_now: int,
                         scan_reference_ms: int | None = None):
    """Check active signals for TP/SL hits.

    [Logic-15] Improved same-candle TP1+SL disambiguation:
    Uses proximity of entry to TP1 vs SL to determine which was likely hit first,
    rather than relying solely on candle color.
    """
    # [P1-7] Thread-safe state read
    with _state_lock:
        signals = list(state.get("active_signals", []))
    if not signals:
        return

    ref_ms = scan_reference_ms if scan_reference_ms is not None else int(time.time() * 1000)
    still_active = []
    for sig in signals:
        age = bar_index_now - sig.get("bar_index", bar_index_now)
        if age > SIGNAL_MAX_AGE_BARS:
            print(f"  [TRACK] {sig['symbol']} expired after {age} bars — dropping")
            hist_id = sig.get("hist_id")
            if hist_id:
                update_signal_result(state, hist_id, "expired")
            with _state_lock:
                state.setdefault("resolved_signals", []).append({
                    "symbol":      sig["symbol"],
                    "direction":   sig.get("direction", ""),
                    "outcome":     "expired",
                    "resolved_at": int(time.time()),
                })
            continue
        if sig.get("resolved", False):
            continue

        symbol    = sig["symbol"]
        direction = sig["direction"]
        msg_id    = sig["msg_id"]
        tp1       = sig["tp1"]
        tp2       = sig["tp2"]
        sl        = sig["sl"]
        tp1_hit   = sig.get("tp1_hit", False)
        signal_bar_time_ms = sig.get("signal_bar_time")
        last_processed_ts  = sig.get("last_processed_candle_ts", signal_bar_time_ms or 0)

        # [Fix-40] Compute the fetch window dynamically from the elapsed time since
        # last_processed_ts so a gap (downtime/scan delay) longer than N_15M bars
        # doesn't silently drop candles. With no gap this reduces to the old N_15M
        # default (see Verification checklist).
        fetch_start_ms = last_processed_ts if last_processed_ts else signal_bar_time_ms
        iv_ms = INTERVAL_MS.get("15m", 15 * 60 * 1000)
        gap_bars = max(0, (ref_ms - (fetch_start_ms or ref_ms)) // iv_ms) + 5  # +5 buffer
        if gap_bars > N_15M:
            if gap_bars > MAX_GAP_FETCH_15M_BARS:
                # Gap too large to reconstruct fully — don't silently mark "expired"
                # (that would pollute win-rate stats with a fake outcome). Resolve as
                # "expired_gap" and exclude it from win-rate calculations instead.
                print(f"  [TRACK] {symbol} gap of {gap_bars} 15m bars exceeds "
                      f"MAX_GAP_FETCH_15M_BARS ({MAX_GAP_FETCH_15M_BARS}) — "
                      f"resolving as expired_gap (excluded from win-rate stats)")
                hist_id = sig.get("hist_id")
                if hist_id:
                    update_signal_result(state, hist_id, "expired_gap")
                with _state_lock:
                    state.setdefault("resolved_signals", []).append({
                        "symbol":      symbol,
                        "direction":   direction,
                        "outcome":     "expired_gap",
                        "resolved_at": int(time.time()),
                    })
                continue
            print(f"  [TRACK] {symbol} gap-covering candle fetch: requesting "
                  f"{gap_bars} 15m bars (default {N_15M}) to avoid missing TP/SL events")
            n_to_fetch = gap_bars
        else:
            n_to_fetch = N_15M

        try:
            candles = get_candles(symbol, "15m", n_to_fetch,
                                  start_time_ms=fetch_start_ms,
                                  reference_ms=ref_ms)
        except Exception as e:
            print(f"  [TRACK] candle fetch failed for {symbol}: {e}")
            still_active.append(sig)
            continue

        if not candles:
            still_active.append(sig)
            continue

        new_candles = [c for c in candles if c["t"] > last_processed_ts]
        if not new_candles:
            still_active.append(sig)
            continue

        hist_id = sig.get("hist_id")
        entry_px = sig.get("entry", tp1)  # fallback

        def resolve_signal(outcome: str):
            if hist_id:
                update_signal_result(state, hist_id, outcome)
            with _state_lock:
                state.setdefault("resolved_signals", []).append({
                    "symbol":      symbol,
                    "direction":   direction,
                    "outcome":     outcome,
                    "resolved_at": int(time.time()),
                })
            sig["resolved"] = True
            if outcome in ("tp1", "tp2", "sl"):
                _resolved_type = sig.get("signal_type", "")
                _cd_suffix = f"_{_resolved_type}" if _resolved_type in ("BREAK", "PULL") else ""
                cooldown_key = f"{symbol}_{direction}{_cd_suffix}"  # FIX-D4
                with _state_lock:
                    state.setdefault("last_signal_outcome", {})[cooldown_key] = outcome
                    if outcome == "sl":
                        state.setdefault("post_loss_cooldown", {})[cooldown_key] = int(time.time())  # FIX-D4
                if outcome == "sl":
                    signal_type = sig.get("signal_type", "UNKNOWN")
                    record_failed_breakout(state, symbol, direction, signal_type, bar_index_now)

        for candle in new_candles:
            c_high = candle["h"]
            c_low  = candle["l"]
            c_open = candle["o"]
            c_close = candle["c"]
            last_processed_ts = candle["t"]

            if direction == "long":
                if not tp1_hit:
                    if c_high >= tp1 and c_low <= sl:
                        # [Logic-15] Improved disambiguation:
                        # Use proximity to determine which was hit first.
                        # Price starts at open and moves through the candle.
                        # The level closer to open is more likely hit first.
                        tp1_dist_from_open = abs(tp1 - c_open)
                        sl_dist_from_open  = abs(sl - c_open)
                        if sl_dist_from_open < tp1_dist_from_open:
                            # SL is closer to open — more likely hit first
                            react_to_message_safe(msg_id, REACT_SL)
                            resolve_signal("sl")
                            break
                        else:
                            react_to_message_safe(msg_id, REACT_TP1)
                            tp1_hit = True
                            sig["tp1_hit"] = True
                    elif c_high >= tp1:
                        react_to_message_safe(msg_id, REACT_TP1)
                        tp1_hit = True
                        sig["tp1_hit"] = True
                    elif c_low <= sl:
                        react_to_message_safe(msg_id, REACT_SL)
                        resolve_signal("sl")
                        break

                if tp1_hit and c_high >= tp2:
                    react_to_message_safe(msg_id, REACT_TP2)
                    resolve_signal("tp2")
                    break

                if tp1_hit and not sig.get("resolved", False) and c_low <= sl:
                    print(f"  [TRACK] {symbol} SL hit after TP1 — resolving silently as TP1 win")
                    resolve_signal("tp1")
                    break
            else:  # short
                if not tp1_hit:
                    if c_low <= tp1 and c_high >= sl:
                        # [Logic-15] Same proximity-based disambiguation for shorts
                        tp1_dist_from_open = abs(tp1 - c_open)
                        sl_dist_from_open  = abs(sl - c_open)
                        if sl_dist_from_open < tp1_dist_from_open:
                            react_to_message_safe(msg_id, REACT_SL)
                            resolve_signal("sl")
                            break
                        else:
                            react_to_message_safe(msg_id, REACT_TP1)
                            tp1_hit = True
                            sig["tp1_hit"] = True
                    elif c_low <= tp1:
                        react_to_message_safe(msg_id, REACT_TP1)
                        tp1_hit = True
                        sig["tp1_hit"] = True
                    elif c_high >= sl:
                        react_to_message_safe(msg_id, REACT_SL)
                        resolve_signal("sl")
                        break

                if tp1_hit and c_low <= tp2:
                    react_to_message_safe(msg_id, REACT_TP2)
                    resolve_signal("tp2")
                    break

                if tp1_hit and not sig.get("resolved", False) and c_high >= sl:
                    print(f"  [TRACK] {symbol} SL hit after TP1 — resolving silently as TP1 win")
                    resolve_signal("tp1")
                    break

        if not sig.get("resolved", False):
            sig["last_processed_candle_ts"] = last_processed_ts
            still_active.append(sig)

    # [P1-7] Thread-safe state update
    with _state_lock:
        state["active_signals"] = still_active

# ═══════════════════════════════════════════════════════════════
# DYNAMIC SPREAD EXEMPTION — [Risk-36]
# ═══════════════════════════════════════════════════════════════

_spread_history: dict[str, list[float]] = {}
_spread_history_lock = threading.Lock()

def update_spread_history(symbol: str, spread_pct: float) -> None:
    with _spread_history_lock:
        hist = _spread_history.setdefault(symbol, [])
        hist.append(spread_pct)
        _spread_history[symbol] = hist[-SPREAD_DYNAMIC_HISTORY_LEN:]

def is_spread_exempt_dynamic(symbol: str) -> bool:
    """Check if a symbol is exempt from spread filtering.

    [Risk-36] Dynamic exemption: if the symbol's average spread over
    recent scans is below threshold, it's exempt even if not in the
    hardcoded SPREAD_EXEMPT set.
    """
    # Hardcoded baseline always exempt
    if symbol in SPREAD_EXEMPT:
        return True

    with _spread_history_lock:
        hist = _spread_history.get(symbol, [])
        if len(hist) >= 3:
            avg_spread = sum(hist) / len(hist)
            if avg_spread < SPREAD_DYNAMIC_AVG_THRESHOLD:
                return True

    return False

def sync_spread_history_to_state(state: dict) -> None:
    """Persist the in-memory spread history into state so it survives across cron runs."""
    with _spread_history_lock:
        snapshot = {sym: list(hist) for sym, hist in _spread_history.items()}
    with _state_lock:
        state["spread_history"] = snapshot

# ═══════════════════════════════════════════════════════════════
# DAILY SUMMARY
# ═══════════════════════════════════════════════════════════════

def should_send_summary(state: dict) -> bool:
    now = datetime.now(timezone.utc)
    # [P1-7] Thread-safe state read
    with _state_lock:
        last = state.get("last_summary_ts", 0)
    if now.hour == 8 and now.minute < 15 and (now.timestamp() - last) > 3600:
        with _state_lock:
            state["last_summary_ts"] = now.timestamp()
        return True
    return False

def send_summary(state: dict):
    cutoff_24h = int(time.time()) - 86400
    cutoff_48h = int(time.time()) - 172800
    # [P1-7] Thread-safe state read
    with _state_lock:
        recent = [e for e in state.get("resolved_signals", []) if e["resolved_at"] >= cutoff_24h]
        all_history = [e for e in state.get("signal_history", [])
                        if e.get("result") in ("tp1", "tp2", "sl")]
    tp1_count  = sum(1 for e in recent if e["outcome"] == "tp1")
    tp2_count  = sum(1 for e in recent if e["outcome"] == "tp2")
    sl_count   = sum(1 for e in recent if e["outcome"] == "sl")
    winners    = tp1_count + tp2_count
    losers     = sl_count
    if winners == 0 and losers == 0:
        return

    total       = len(all_history)
    overall_wr  = None
    if total >= WIN_RATE_MIN_SAMPLE:
        wins       = sum(1 for r in all_history if r.get("result") in ("tp1", "tp2"))
        overall_wr = wins / total

    lines = [
        f"📊 Signal Summary (last 24h)  •  v{__version__}",
        f"✅ Winners: {winners} (🔥×{tp1_count}  🏆×{tp2_count})",
        f"❌ Losers:  {losers} (😭×{sl_count})",
    ]
    if overall_wr is not None:
        lines.append(f"📈 Overall Win Rate: {overall_wr*100:.0f}% ({total} trades)")

    def r_pnl(entries):
        return sum(
            +2 if e["result"] == "tp2"
            else +1 if e["result"] == "tp1"
            else -1
            for e in entries if e.get("result") in ("tp1", "tp2", "sl")
        )

    breakdown_lines = []
    for sig_type in ("BREAK", "PULL"):
        for dirn in ("long", "short"):
            subset = [e for e in all_history
                      if e.get("signal_type") == sig_type and e.get("direction") == dirn]
            if len(subset) >= 5:
                wins = sum(1 for e in subset if e["result"] in ("tp1", "tp2"))
                wr   = wins / len(subset)
                pnl  = r_pnl(subset)
                breakdown_lines.append(
                    f"  {sig_type} {dirn}: {wr*100:.0f}% WR  {pnl:+d}R  (n={len(subset)})"
                )

    if breakdown_lines:
        lines.append("\n📋 By type / direction:\n" + "\n".join(breakdown_lines))

    send_telegram("\n".join(lines))
    # [P1-7] Thread-safe state mutation
    with _state_lock:
        state["resolved_signals"] = [
            e for e in state.get("resolved_signals", []) if e["resolved_at"] >= cutoff_48h
        ]

# ═══════════════════════════════════════════════════════════════
# SCAN
# ═══════════════════════════════════════════════════════════════

def collect_market_inputs(symbol: str, state: dict, reference_ms: int) -> tuple | None:
    data = fetch_all_candles(symbol, reference_ms=reference_ms)
    if data is None:
        return None
    candles_15m, candles_1h, candles_4h, candles_d = data
    record_market_inputs_from_candles(symbol, candles_15m, candles_4h)

    ctx = get_market_context(symbol)
    if ctx and ctx.get("funding") is not None:
        update_funding_history(state, symbol, ctx.get("funding"))

    return data

def scan_symbol(symbol: str, state: dict, bar_index_now: int,
                candle_bundle: tuple | None = None,
                reference_ms: int | None = None) -> list[tuple]:
    coin = hl_coin(symbol)
    if candle_bundle is None:
        data = fetch_all_candles(symbol, reference_ms=reference_ms)
        if data is None:
            print(f"    Skipping {coin}: insufficient candles")
            return []
    else:
        data = candle_bundle

    candles_15m, candles_1h, candles_4h, candles_d = data

    ctx = get_market_context(symbol)
    if ctx:
        if ctx.get("open_interest") is not None and ctx["open_interest"] < MIN_OI_USD:
            print(f"    Skipping {coin}: OI too low (${ctx['open_interest']:,.0f})")
            return []

        oi_usd_val = ctx.get("open_interest")
        update_oi_history(state, symbol, oi_usd_val)

    live_cache   = get_meta_and_asset_ctxs()
    live_funding = (live_cache.get(hl_coin(symbol), {}).get("funding")
                    if live_cache else None)
    _ctx_funding = ctx.get("funding") if ctx else None
    funding_for_suppress = live_funding if live_funding is not None else _ctx_funding
    if live_funding is not None and live_funding != _ctx_funding:
        pct = (live_funding * 100) if live_funding is not None else float("nan")
        print(f"    [FUNDING REFRESH] {coin}: updated → {pct:+.4f}%/8h")

    sig = compute_signals(symbol, candles_15m, candles_1h, candles_4h, candles_d,
                          state, record_market_inputs=False, reference_ms=reference_ms,
                          funding_rate=funding_for_suppress)
    if not (sig.fire_long or sig.fire_short):
        print(f"    {coin}: no signal")
        return []

    direction = "long" if sig.fire_long else "short"
    if not check_cooldown(state, symbol, direction, bar_index_now,
                          signal_type=sig.signal_type,
                          candidate_score=sig.final_score):
        print(f"    {coin} signal suppressed by cooldown")
        return []

    print(f"    🚀 SIGNAL: {coin} {direction.upper()} [{sig.signal_type}] "
          f"base={sig.score} final={sig.final_score}")

    # IMP-S16-7 — use the current live mark price (proxy for current-bar open) as the
    # Tranche A "Market" entry basis instead of the prior closed 15m candle's close,
    # tightening the gap between signal generation and actual fill on gap-prone opens.
    _live_entry_px_s16_7 = (live_cache.get(hl_coin(symbol), {}).get("mark_px")
                            if live_cache else None)
    if _live_entry_px_s16_7 is not None and _live_entry_px_s16_7 > 0:
        sig.entry = _live_entry_px_s16_7   # IMP-S16-7

    if ctx:
        sig.funding_rate  = live_funding if live_funding is not None else ctx.get("funding")
        sig.open_interest = ctx.get("open_interest")
        pct = (sig.funding_rate * 100) if sig.funding_rate is not None else float("nan")
        print(f"    [MARKET CTX] {coin}: funding={pct:+.4f}%/8h  {format_oi(sig.open_interest)}")

    if FUNDING_SUPPRESS_EXTREME is not None and funding_for_suppress is not None:
        rate     = funding_for_suppress
        headwind = (rate > 0 and direction == "long") or (rate < 0 and direction == "short")
        if headwind and abs(rate) >= FUNDING_SUPPRESS_EXTREME:
            pct = rate * 100
            print(f"    [FUNDING FILTER] {coin} {direction.upper()} suppressed — "
                  f"funding {pct:+.4f}%/8h is extreme headwind")
            return []

    _breadth_pct_scan = compute_market_breadth()["breadth_50_pct"]
    _eff_min_scan = get_effective_min_score(get_btc_regime(), _breadth_pct_scan)

    # [Risk-36] Dynamic spread exemption
    if not is_spread_exempt_dynamic(symbol):
        live_mark = (live_cache.get(hl_coin(symbol), {}).get("mark_px")
                     if live_cache else None)
        if live_mark is not None and live_mark > 0:
            _bid = ctx.get("best_bid") if ctx else None    # FIX-D18
            _ask = ctx.get("best_ask") if ctx else None
            if _bid and _ask and _bid > 0:
                _spread_pct = (_ask - _bid) / _bid * 100.0   # FIX-D18 — true bid/ask spread
            else:
                _close_px   = candles_15m[-1]["c"]
                _spread_pct = abs(live_mark - _close_px) / _close_px * 100.0
                # NOTE: proxy spread — may include inter-phase price drift, not true bid-ask
            with _spread_history_lock:                                 # IMP-S18-8
                sig.spread_pct = _spread_pct
            update_spread_history(symbol, _spread_pct)
            if _spread_pct >= SPREAD_SUPPRESS_PCT:
                print(f"    [SPREAD FILTER] {coin} {direction.upper()} hard suppressed — "
                      f"mark/close divergence {_spread_pct:.3f}% >= {SPREAD_SUPPRESS_PCT:.2f}%")
                return []
            elif _spread_pct >= SPREAD_WARN_PCT:
                sig.final_score -= 1
                sig.score_adjustments.append(
                    (f"Spread/liquidity warn ({_spread_pct:.3f}%)", -1, "secondary")
                )
                print(f"    [SPREAD WARN] {coin} {direction.upper()} −1 score — "
                      f"mark/close divergence {_spread_pct:.3f}%")
                if sig.final_score < _eff_min_scan:
                    print(f"    [SPREAD FILTER] {coin} suppressed after spread penalty "
                          f"(final={sig.final_score} < eff_min={_eff_min_scan})")
                    return []
    else:
        # Still track spread for dynamic exemption maintenance
        live_mark = (live_cache.get(hl_coin(symbol), {}).get("mark_px")
                     if live_cache else None)
        if live_mark is not None and live_mark > 0:
            _bid = ctx.get("best_bid") if ctx else None    # FIX-D18
            _ask = ctx.get("best_ask") if ctx else None
            if _bid and _ask and _bid > 0:
                _spread_pct = (_ask - _bid) / _bid * 100.0   # FIX-D18 — true bid/ask spread
            else:
                _close_px   = candles_15m[-1]["c"]
                _spread_pct = abs(live_mark - _close_px) / _close_px * 100.0
                # NOTE: proxy spread — may include inter-phase price drift, not true bid-ask
            with _spread_history_lock:                                 # IMP-S18-8
                sig.spread_pct = _spread_pct
            update_spread_history(symbol, _spread_pct)

    return [(symbol, direction, sig)]

# ═══════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════

def deduplicate_correlated(signals: list[tuple]) -> list[tuple]:
    def _group_of_dynamic_safe(symbol):    # IMP-S18-7
        try:                                                          # IMP-S18-7
            return group_of_dynamic(symbol)
        except Exception as e:
            print(f"  [CORR GROUP] group_of_dynamic({symbol}) failed: {e} — treating as singleton")
            return symbol   # IMP-S18-7 — each symbol is its own group as safe fallback

    def _sort_key(t):
        sig = t[2]
        rs = sig.rs_data.get("rs_pct")
        if rs is None: rs = -999.0
        if sig.fire_short:
            return -rs
        return rs

    signals.sort(key=_sort_key, reverse=True)

    seen_groups: set[tuple] = set()
    result: list[tuple]     = []
    # FIX-D19: Track per-(group, direction) counts to allow top-2 from large clusters
    _group_counts: dict = {}
    MAX_FROM_LARGE_CLUSTER = 2
    _all_symbols = [t[0] for t in signals]
    for sig_tuple in signals:
        symbol    = sig_tuple[0]
        direction = sig_tuple[1]
        # [v15.5.5] Group key now comes from this scan's dynamic correlation
        # clusters (see compute_pairwise_correlation_matrix() /
        # cluster_by_correlation() / group_of_dynamic()) instead of a static
        # hand-maintained CORR_GROUPS dict.
        group = _group_of_dynamic_safe(symbol)   # IMP-S18-7
        _group_size = sum(1 for s in _all_symbols if _group_of_dynamic_safe(s) == group)   # IMP-S18-7
        _watchlist_size = max(len(_all_symbols), 1)
        _large_cluster = _group_size >= int(_watchlist_size * 0.5)   # FIX-D19
        _limit = MAX_FROM_LARGE_CLUSTER if _large_cluster else 1      # FIX-D19
        _group_dir_key = (group, direction)
        _group_counts.setdefault(_group_dir_key, 0)
        if _group_counts[_group_dir_key] < _limit:                    # FIX-D19
            _group_counts[_group_dir_key] += 1
            seen_groups.add(_group_dir_key)
            result.append(sig_tuple)

    # [Bugfix] Opposite-direction conflicts within the same correlation
    # group are not caught by the same-direction dedup above (different
    # keys: (group, "long") vs (group, "short")). Resolve any surviving
    # long/short pair in the same group by priority_score, keeping the
    # higher-priority side.
    by_group: dict = {}
    for sig_tuple in result:
        g = _group_of_dynamic_safe(sig_tuple[0])   # IMP-S18-7
        by_group.setdefault(g, []).append(sig_tuple)

    dropped_ids = set()
    for g, tuples in by_group.items():
        longs  = [t for t in tuples if t[1] == "long"]
        shorts = [t for t in tuples if t[1] == "short"]
        if longs and shorts:
            best_long  = max(longs,  key=lambda t: priority_score(t[2]))
            best_short = max(shorts, key=lambda t: priority_score(t[2]))
            loser = best_short if priority_score(best_long[2]) >= priority_score(best_short[2]) else best_long
            dropped_ids.add(id(loser))
            g_label = sorted(g) if isinstance(g, frozenset) else g
            print(f"  [CORR CONFLICT] Group {g_label} has both long ({best_long[0]}) and "
                  f"short ({best_short[0]}) surviving dedup — dropping lower-priority "
                  f"{loser[1]} on {loser[0]}.")

    if dropped_ids:
        result = [t for t in result if id(t) not in dropped_ids]

    return result

_shutdown = False

def _handle_sigterm(signum, frame):
    global _shutdown
    _shutdown = True

os_signal.signal(os_signal.SIGTERM, _handle_sigterm)

def main():
    print(f"[{datetime.now(timezone.utc).isoformat()}] Scanner starting…")
    print(f"Watchlist ({len(WATCHLIST)} pairs): {[hl_coin(s) for s in WATCHLIST]}")

    scan_reference_ms = int(time.time() * 1000)
    bar_index_now     = scan_reference_ms // (15 * 60 * 1000)
    state             = load_state()

    # [Fix-TG-3] Restore spread history from persisted state
    _saved_spread = state.get("spread_history", {})
    if _saved_spread:
        with _spread_history_lock:
            for _sym, _hist in _saved_spread.items():
                _spread_history[_sym] = list(_hist)
        print(f"[INIT] Spread history restored: {len(_saved_spread)} symbol(s)")

    # IMP-S18-6 — restore dynamic correlation clusters from state on cold start,
    # so the first scan after a restart isn't stuck with singleton-only groups.
    if "_dynamic_corr_clusters" in state and not get_dynamic_corr_clusters():
        _restored_clusters = [set(c) for c in state["_dynamic_corr_clusters"]]
        set_dynamic_corr_clusters(_restored_clusters)
        print(f"[INIT] Restored {len(_restored_clusters)} corr clusters from state (cold-start)")  # IMP-S18-6

    prune_state(state)

    reset_breadth_cache()
    reset_rs_cache()
    reset_win_rates_cache()
    clear_indicator_cache()

    # [Fix-12] Run self-test to ensure cache isolation
    try:
        _selftest_indicator_cache_isolation()
        print("[INIT] Indicator cache isolation self-test passed.")
    except AssertionError as e:
        print(f"[INIT] FATAL: Indicator cache self-test failed: {e}")
        sys.exit(1)

    print("[INIT] Fetching market context (metaAndAssetCtxs)…")
    get_meta_and_asset_ctxs()

    if _shutdown:
        save_state(state)
        sys.exit(0)

    # IMP-S16-8 — check_active_signals() moved to scan END (see bottom of main())
    # so TP/SL resolution uses the freshest candles from this completed scan,
    # not the previous scan's. save_state() call moved alongside it.

    if should_send_summary(state):
        send_summary(state)
        save_state(state)

    print("[PHASE 1] Collecting market breadth / RS inputs…")
    candle_bundles: dict[str, tuple] = {}
    with ThreadPoolExecutor(max_workers=max(1, SCAN_WORKERS)) as ex:
        futures = {
            ex.submit(collect_market_inputs, sym, state, scan_reference_ms): sym
            for sym in WATCHLIST
        }
        for fut in as_completed(futures):
            sym = futures[fut]
            try:
                bundle = fut.result()
                if bundle is not None:
                    candle_bundles[sym] = bundle
            except Exception as e:
                print(f"    ERROR collecting inputs for {sym}: {e}")

    finalize_breadth_cache()
    finalize_rs_cache()
    with _breadth_lock:
        breadth_n = len(_breadth_snapshot or {})
    with _rs_lock:
        rs_n = len(_rs_snapshot or {})
    print(f"  Breadth symbols: {breadth_n}  RS symbols: {rs_n}")

    # IMP-S18-10 — graceful Phase 1 failure: if too few symbols resolved candles,
    # breadth/RS snapshots are unreliable and Phase 2 signals would be mis-scored.
    MIN_SYMBOLS_FOR_SCAN = 10   # IMP-S18-10
    resolved_symbols = [s for s in WATCHLIST if candle_bundles.get(s)]
    if len(resolved_symbols) < MIN_SYMBOLS_FOR_SCAN:
        print(
            f"  [PHASE 1 ABORT] Resolved only {len(resolved_symbols)}/{len(WATCHLIST)} symbols "
            f"(threshold: {MIN_SYMBOLS_FOR_SCAN}) — aborting scan cycle to prevent bad breadth signals"
        )
        save_state(state)
        return   # IMP-S18-10 — skip Phase 2 entirely for this cycle

    # [Logic-24] Update dynamic BTC correlation using collected 4H candles
    btc_4h_bundle = candle_bundles.get("BTCUSDT")
    if btc_4h_bundle:
        btc_4h_candles = btc_4h_bundle[2]  # 4H candles
        for sym, bundle in candle_bundles.items():
            if sym == "BTCUSDT":
                continue
            update_dynamic_btc_correlation(sym, bundle[2], btc_4h_candles)

    # [v15.5.5] Build this scan's dynamic pairwise correlation clusters across
    # the watchlist (ported from v15.8.1 Fix-33), reusing the same Phase-1 4H
    # candle bundles — no new data fetching. This replaces the static
    # CORR_GROUPS dict as the grouping deduplicate_correlated() uses for
    # correlated-exposure control. On failure (or on a cold-start scan before
    # any candles are available), fall back to treating every watchlist
    # symbol as its own singleton group rather than crashing the scan.
    try:
        _corr_matrix = compute_pairwise_correlation_matrix(WATCHLIST, candle_bundles)
        _corr_clusters = cluster_by_correlation(WATCHLIST, _corr_matrix)
        set_dynamic_corr_clusters(_corr_clusters)
        log_dynamic_corr_clusters(_corr_clusters)
        state["_dynamic_corr_clusters"] = [list(c) for c in get_dynamic_corr_clusters()]   # IMP-S18-6 — persist to state
    except Exception as e:
        print(f"  [CORR MATRIX] dynamic clustering failed, falling back to singleton groups: {e}")
        set_dynamic_corr_clusters([{s} for s in WATCHLIST])

    print("[INIT] Computing BTC regime…")
    try:
        if btc_4h_bundle is None:
            print("  [BTC REGIME] BTCUSDT candles unavailable from Phase 1 — regime not computed")
        else:
            _, btc_1h, btc_4h, btc_1d = btc_4h_bundle
            regime = compute_btc_regime(btc_1h, btc_4h, btc_1d)
            set_btc_regime(regime)
            print(f"  {regime['label']}")
    except Exception as e:
        print(f"  [BTC REGIME] failed to compute: {e}")

    if _shutdown:
        save_state(state)
        sys.exit(0)

    print("[PHASE 2] Scanning symbols for signals…")
    print("[INIT] Refreshing market context before Phase 2…")
    get_meta_and_asset_ctxs()

    pending_signals: list[tuple] = []
    with ThreadPoolExecutor(max_workers=max(1, SCAN_WORKERS)) as ex:
        futures = {
            ex.submit(scan_symbol, sym, state, bar_index_now, candle_bundles.get(sym),
                      scan_reference_ms): sym
            for sym in WATCHLIST
        }
        for fut in as_completed(futures):
            sym = futures[fut]
            try:
                result = fut.result()
                if result:
                    pending_signals.extend(result)
            except Exception as e:
                print(f"    ERROR processing {sym}: {e}")

    pending_signals.sort(key=lambda t: priority_score(t[2]), reverse=True)
    deduped_signals = deduplicate_correlated(pending_signals)

    _btc_regime_main = get_btc_regime()
    _breadth_pct_main = compute_market_breadth()["breadth_50_pct"]
    _max_signals = get_dynamic_max_signals(_btc_regime_main, _breadth_pct_main)
    print(f"  [DYNAMIC SIGNALS] Max signals this scan: {_max_signals} "
          f"(BTC regime: {_btc_regime_main['label'] if _btc_regime_main else 'Unknown'}, "
          f"breadth: {_breadth_pct_main*100:.0f}%)")

    top_signals     = deduped_signals[:_max_signals]
    top_set         = set(id(t) for t in top_signals)
    dropped_signals = [t for t in deduped_signals if id(t) not in top_set]

    if dropped_signals:
        dropped_names = [f"{hl_coin(s)} {d.upper()}" for s, d, _ in dropped_signals]
        print(f"  [RANK] Dropped {len(dropped_signals)} lower-priority signal(s): {', '.join(dropped_names)}")
        for symbol, direction, sig in dropped_signals:
            record_signal_history(
                state, symbol, direction, sig.signal_type, sig.final_score,
                sig.funding_rate, sig.atr_pct,
                sig.oi_trend_data.get("oi_change_pct"),
                sig.alignment_mode,
                sent=False,
            )

    signals_fired = 0
    for rank, (symbol, direction, sig) in enumerate(top_signals, start=1):
        msg    = format_signal(symbol, sig, "CORE", rank=rank)
        msg_id = send_telegram(msg)

        hist_id = record_signal_history(
            state, symbol, direction, sig.signal_type, sig.final_score,
            sig.funding_rate, sig.atr_pct,
            sig.oi_trend_data.get("oi_change_pct"),
            sig.alignment_mode,
            sent=True,
        )

        if msg_id:
            update_cooldown(state, symbol, direction, bar_index_now, signal_type=sig.signal_type)
            track_signal(state, symbol, direction, msg_id, sig, bar_index_now, hist_id=hist_id)
            print(f"  [TRACK] #{rank} {hl_coin(symbol)} {direction.upper()} "
                  f"TP1={sig.tp1:.4f} TP2={sig.tp2:.4f} SL={sig.sl:.4f}")
        else:
            print(f"  [TG FAIL] #{rank} {hl_coin(symbol)} {direction.upper()} "
                  f"— Telegram send failed, cooldown NOT set (eligible to re-fire next scan)")
        signals_fired += 1
        time.sleep(0.5)

    print("[TRACK] Checking active signals…")
    check_active_signals(state, bar_index_now, scan_reference_ms)   # IMP-S16-8 — moved to scan end for fresh candles

    sync_spread_history_to_state(state)
    save_state(state)
    print(f"Scan complete. {signals_fired} signal(s) fired.")

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        try:
            send_telegram(f"🚨 Engine crashed: {e}")
        except:
            pass
        raise
    finally:
        _hl_session.close()
