"""
Shared paths and constants for all evaluation scripts.
"""

import csv
import sys
from pathlib import Path

csv.field_size_limit(sys.maxsize)

# Root of the evaluation directory
EVAL_DIR = Path(__file__).resolve().parent.parent

# Input data (never modified)
DATA_DIR = EVAL_DIR / "data"

# All generated output under one folder
OUTPUT_DIR = EVAL_DIR / "output"
SUMMARIES_DIR = OUTPUT_DIR / "summaries"
FIGURES_DIR = OUTPUT_DIR / "figures"
SAMPLES_DIR = OUTPUT_DIR / "samples"
REVIEW_DIR = OUTPUT_DIR / "manual_review"
GENERATED_DATA_DIR = OUTPUT_DIR / "data"
ADDRESSES_DIR = REVIEW_DIR / "addresses"
INSPECTIONS_DIR = REVIEW_DIR / "inspections"
VERDICTS_DIR = REVIEW_DIR / "verdicts"

# Ensure output directories exist
for d in [SUMMARIES_DIR, FIGURES_DIR, SAMPLES_DIR,
          ADDRESSES_DIR, INSPECTIONS_DIR, VERDICTS_DIR,
          GENERATED_DATA_DIR]:
    d.mkdir(parents=True, exist_ok=True)

# Normalization tables (from src/common/types.ml, confirmed via OpenAPI spec)
VERDICT_MAP = {
    0: "arbitrage", 1: "warning",
    "arbitrage": "arbitrage", "warning": "warning",
}

REASON_MAP = {
    0: "leftoverTransaction", 1: "balancePositive", 2: "balanceMixed",
    3: "balanceNegative", 4: "finalBalancePositive", 5: "finalBalanceMixed",
    6: "finalBalanceNegative", 7: "negativeProfit", 8: "noArbitrageCycles",
}

SAMPLE_SIZE = 100
SEED = 42

# Column index for tag_data in system_arbis.csv
# Old format (DB export): 5
# New format (bench script with timing columns): 7
TAG_DATA_COL = 7

# Generated data (produced by 00_preprocess.py)
COMPACT_CSV = GENERATED_DATA_DIR / "system_compact.csv"
HASHES_TXT = GENERATED_DATA_DIR / "system_hashes.txt"
EIGENPHI_FILTERED = GENERATED_DATA_DIR / "eigenphi_arbis_txs_filtered.csv"


def load_compact():
    """Load system_compact.csv and return a list of row dicts.

    Each dict has keys: tx_hash, block, verdict, reasons (tuple),
    num_cycles (int), num_leftovers (int), decode_ms (float or None),
    algo_ms (float or None).

    Exits with a clear error if the compact file is missing — run
    script/00_preprocess.py first.
    """
    import sys

    if not COMPACT_CSV.exists():
        print(
            f"ERROR: {COMPACT_CSV} not found.\n"
            "Run step 0 first:  python3 script/00_preprocess.py"
        )
        sys.exit(1)

    rows = []
    with open(COMPACT_CSV, newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            reasons_str = row["reasons"]
            reasons = tuple(sorted(reasons_str.split("|"))) if reasons_str else ()

            try:
                decode_ms = float(row["decode_ms"]) if row["decode_ms"] else None
            except ValueError:
                decode_ms = None

            try:
                algo_ms = float(row["algo_ms"]) if row["algo_ms"] else None
            except ValueError:
                algo_ms = None

            fp_raw = row.get("fixpoint_detected", "")
            fixpoint_detected = fp_raw == "True" if fp_raw else None

            rows.append({
                "tx_hash": row["tx_hash"],
                "block": int(row["block"]),
                "verdict": row["verdict"],
                "reasons": reasons,
                "num_cycles": int(row["num_cycles"]),
                "num_leftovers": int(row["num_leftovers"]),
                "fixpoint_detected": fixpoint_detected,
                "decode_ms": decode_ms,
                "algo_ms": algo_ms,
            })
    return rows


def normalize_verdict(v):
    return VERDICT_MAP.get(v, str(v))


def normalize_reasons(reasons):
    return tuple(sorted(
        REASON_MAP.get(r, r) if isinstance(r, int) else r
        for r in reasons
    ))


def normalize_hash(h):
    h = h.strip()
    if h.startswith("\\x"):
        h = h[2:]
    if h.startswith("0x") or h.startswith("0X"):
        h = h[2:]
    return h.lower()


def classify_by_reasons(verdict, reasons):
    if verdict == "arbitrage":
        return "confirmed_arbitrage"
    has_left = "leftoverTransaction" in reasons
    has_neg = "negativeProfit" in reasons
    has_neg_final = "finalBalanceNegative" in reasons
    has_mixed = "finalBalanceMixed" in reasons or "balanceMixed" in reasons
    if has_left and not has_neg and not has_mixed and not has_neg_final:
        return "probable_arbitrage_incomplete"
    elif has_neg or has_neg_final:
        return "attempted_arbitrage_unprofitable"
    elif has_mixed:
        return "uncertain_mixed_balance"
    else:
        return "warning_other"


# Category folder names
CATEGORY_FOLDERS = {
    1: "cat1_both_confirmed",
    2: "cat2_system_only_confirmed",
    3: "cat3_system_only_warnings",
    4: "cat4_eigenphi_only",
}

# Sample sizes per category
SAMPLE_SIZES = {
    1: 100,
    2: 100,
    3: 100,
    4: 200,  # larger sample for Eigenphi-only investigation
}

# --- Well-known Ethereum addresses ---
# Single source of truth for all scripts. Addresses are lowercase.

KNOWN_ADDRESSES = {
    # Tokens
    "0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2": "WETH",
    "0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48": "USDC",
    "0xdac17f958d2ee523a2206206994597c13d831ec7": "USDT",
    "0x6b175474e89094c44da98b954eedeac495271d0f": "DAI",
    "0x2260fac5e5542a773aa44fbcfedf7c193bc2c599": "WBTC",
    "0x111111111117dc0aa78b770fa6a738034120c302": "1INCH",
    "0x514910771af9ca656af840dff83e8264ecf986ca": "LINK",
    "0x7f39c581f595b53c5cb19bd0b3f8da6c935e2ca0": "wstETH",
    "0x1f9840a85d5af5bf1d1762f925bdaddc4201f984": "UNI",
    "0x853d955acef822db058eb8505911ed77f175b99e": "FRAX",
    "0xd533a949740bb3306d119cc777fa900ba034cd52": "CRV",
    # Native / burn
    "0x0000000000000000000000000000000000000000": "ETH (null)",
    "0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee": "ETH (burn)",
    # Routers / aggregators
    "0x111111125421ca6dc452d289314280a0f8842a65": "1inch Router v6",
    "0x1111111254eeb25477b68fb85ed929f73a960582": "1inch Router v5",
    "0x1111111254fb6c44bac0bed2854e76f90643097d": "1inch Router v4",
    "0xbbbbbbb520d69a9775e85b458c58c648259fad5f": "1inch Aggregation Router",
    "0x7a250d5630b4cf539739df2c5dacb4c659f2488d": "Uniswap V2 Router",
    "0x68b3465833fb72a70ecdf485e0e4c7bd8665fc45": "Uniswap V3 Router",
    "0x3fc91a3afd70395cd496c647d5a6cc9d4b2b7fad": "Uniswap Universal Router",
    "0xd9e1ce17f2641f24ae83637ab66a2cca9c378b9f": "SushiSwap Router",
    "0xdef1c0ded9bec7f1a1670819833240f027b25eff": "0x Exchange Proxy",
    "0x9008d19f58aabd9ed0d60971565aa8510560ab41": "CoW Protocol",
    "0xba12222222228d8ba445958a75a0704d566bf2c8": "Balancer Vault",
    # Factories / singletons
    "0x000000000004444c5dc75cb358380d2e3de08a90": "Uniswap V4",
    "0x1f98431c8ad98523631ae4a59f267346ea31f984": "Uniswap V3 Factory",
    "0x5c69bee701ef814a2b6a3edd4b1652cb9cc5aa6f": "Uniswap V2 Factory",
}

# Subset views for specific scripts
KNOWN_ROUTERS = {
    addr: name for addr, name in KNOWN_ADDRESSES.items()
    if "Router" in name or "Aggregation" in name or "Exchange" in name
    or "Protocol" in name or "Vault" in name
}

def is_dex_pool(name):
    """Check if a contract name indicates a DEX pool or AMM."""
    n = name.lower()
    return any(kw in n for kw in [
        "pool", "pair", "vault", "converter", "dex", "bpool",
        "uniswap v4", "uniswap v3", "uniswap v2",
        "pancake", "algebra", "sushi", "curve", "balancer",
        "bancor",
    ])


def classify_pool(name):
    """Return a short pool type label, or None if not a pool."""
    n = name.lower()
    if "uniswapv3pool" in n or "uniswap v3" in n:
        return "UniV3"
    if "uniswapv2" in n or "uniswap v2" in n:
        return "UniV2"
    if "uniswap v4" in n:
        return "UniV4"
    if "pancakev3" in n or "pancake" in n:
        return "PancakeV3"
    if "algebrapool" in n or "algebra" in n:
        return "Algebra"
    if "curve" in n:
        return "Curve"
    if "sushiswap" in n or "sushi" in n:
        return "Sushi"
    if "balancer" in n or "bpool" in n:
        return "Balancer"
    if "bancor" in n or "standardpoolconverter" in n:
        return "Bancor"
    if "fluiddex" in n or "fluid" in n:
        return "Fluid"
    if "settler" in n or "settlement" in n:
        return "Settler"
    if "pool" in n or "pair" in n:
        return "Pool"
    return None


def is_router(name):
    """Check if a contract name indicates a router/aggregator."""
    n = name.lower()
    return any(kw in n for kw in [
        "router", "aggregat", "settler", "settlement",
        "exchange", "proxy", "adapter", "cow protocol",
    ])


KNOWN_BOTS = {
    "0x00000000009e50a7ddb7a7b0e2ee6604fd120e49",
    "0x0000000000007a8d56014359bf3e98f18b7773f9",
    "0x00000000fd3a7b3fa5bcfa843c648714b11e089b",
    "0x0000000000001efe53a797754f094caf01bf92c7",
    "0x0000000000efa780a8e6f50fc5de9c1497bfd175",
    "0x888888888887715fb9d9f84175af9e6cce46807e",
    "0xbadc0de76438f9524d42c219b390636196bfbdfc",
}
