"""
25_crosschain_comparison.py — Cross-chain comparison table.

Side-by-side: Ethereum vs Arbitrum vs BSC detection rates,
cycle lengths, tier breakdowns.

Reads:  data/system_compact.csv (Ethereum)
        data/arbitrum_1k/summary.csv (Arbitrum)
        data/bsc_1k/summary.csv (BSC)
Writes: summaries/06_crosschain/comparison.txt
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import sys
import numpy as np
from collections import Counter
from pathlib import Path
from config import SUMMARIES_DIR, load_compact

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
DATA_DIR = EVAL_DIR / "data"
ARBITRUM_SUMMARY = DATA_DIR / "arbitrum_1k" / "summary.csv"
BSC_SUMMARY = DATA_DIR / "bsc_1k" / "summary.csv"
OUT_TXT = SUMMARIES_DIR / "06_crosschain/comparison.txt"


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def load_chain_summary(path):
    """Load a cross-chain summary CSV and return rows + stats."""
    if not path.exists():
        return None, None, None, None
    rows = []
    with open(path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)
    verdicts = Counter(r["verdict"] for r in rows)
    total = len(rows)
    cycles = [int(r.get("num_cycles", 0)) for r in rows
              if int(r.get("num_cycles", 0)) > 0]
    return rows, verdicts, total, cycles


def main():
    # Ethereum data (from compact CSV)
    eth_rows = load_compact()
    eth_verdicts = Counter(r["verdict"] for r in eth_rows)
    eth_total = len(eth_rows)
    eth_cycles = [r["num_cycles"] for r in eth_rows if r["num_cycles"] > 0]

    # Arbitrum data
    arb_rows, arb_verdicts, arb_total, arb_cycles = load_chain_summary(
        ARBITRUM_SUMMARY)

    # BSC data
    bsc_rows, bsc_verdicts, bsc_total, bsc_cycles = load_chain_summary(
        BSC_SUMMARY)

    with open(OUT_TXT, "w") as out:
        p("=" * 85, out)
        p("CROSS-CHAIN COMPARISON: ETHEREUM vs ARBITRUM vs BSC", out)
        p("=" * 85, out)
        p("", out)

        # Header
        cols = ["Ethereum"]
        if arb_verdicts:
            cols.append("Arbitrum")
        if bsc_verdicts:
            cols.append("BSC")

        header = f"{'Metric':<35s}" + "".join(f"{c:>15s}" for c in cols)
        p(header, out)
        p("-" * (35 + 15 * len(cols)), out)

        # Transactions analyzed
        vals = [f"{eth_total:>15,}"]
        if arb_total is not None:
            vals.append(f"{arb_total:>15,}")
        if bsc_total is not None:
            vals.append(f"{bsc_total:>15,}")
        p(f"  {'Transactions analyzed':<33s}" + "".join(vals), out)

        # Flagged
        eth_flagged = eth_verdicts.get("arbitrage", 0) + eth_verdicts.get(
            "warning", 0)
        flagged = [f"{eth_flagged:>15,}"]
        if arb_verdicts:
            af = arb_verdicts.get("arbitrage", 0) + arb_verdicts.get(
                "warning", 0)
            flagged.append(f"{af:>15,}")
        else:
            af = 0
        if bsc_verdicts:
            bf = bsc_verdicts.get("arbitrage", 0) + bsc_verdicts.get(
                "warning", 0)
            flagged.append(f"{bf:>15,}")
        else:
            bf = 0
        p(f"  {'Flagged (arb + warn)':<33s}" + "".join(flagged), out)

        # Detection rate
        eth_rate = 100 * eth_flagged / eth_total if eth_total else 0
        rates = [f"{eth_rate:>14.1f}%"]
        if arb_total:
            arb_rate = 100 * af / arb_total
            rates.append(f"{arb_rate:>14.1f}%")
        if bsc_total:
            bsc_rate = 100 * bf / bsc_total
            rates.append(f"{bsc_rate:>14.1f}%")
        p(f"  {'Detection rate':<33s}" + "".join(rates), out)

        p("", out)

        # Confirmed
        eth_conf = eth_verdicts.get("arbitrage", 0)
        confs = [f"{eth_conf:>15,}"]
        if arb_verdicts:
            confs.append(f"{arb_verdicts.get('arbitrage', 0):>15,}")
        if bsc_verdicts:
            confs.append(f"{bsc_verdicts.get('arbitrage', 0):>15,}")
        p(f"  {'Confirmed arbitrages':<33s}" + "".join(confs), out)

        # Warnings
        eth_warn = eth_verdicts.get("warning", 0)
        warns = [f"{eth_warn:>15,}"]
        if arb_verdicts:
            warns.append(f"{arb_verdicts.get('warning', 0):>15,}")
        if bsc_verdicts:
            warns.append(f"{bsc_verdicts.get('warning', 0):>15,}")
        p(f"  {'Warnings':<33s}" + "".join(warns), out)

        # Confirmed / flagged
        eth_pct = 100 * eth_conf / eth_flagged if eth_flagged else 0
        pcts = [f"{eth_pct:>14.1f}%"]
        if arb_verdicts and af:
            pcts.append(
                f"{100 * arb_verdicts.get('arbitrage', 0) / af:>14.1f}%")
        if bsc_verdicts and bf:
            pcts.append(
                f"{100 * bsc_verdicts.get('arbitrage', 0) / bf:>14.1f}%")
        p(f"  {'Confirmed / flagged':<33s}" + "".join(pcts), out)

        p("", out)

        # Cycles
        if eth_cycles:
            meds = [f"{np.median(eth_cycles):>15.1f}"]
            maxs = [f"{max(eth_cycles):>15d}"]
            if arb_cycles:
                meds.append(f"{np.median(arb_cycles):>15.1f}")
                maxs.append(f"{max(arb_cycles):>15d}")
            if bsc_cycles:
                meds.append(f"{np.median(bsc_cycles):>15.1f}")
                maxs.append(f"{max(bsc_cycles):>15d}")
            p(f"  {'Median cycles per tx':<33s}" + "".join(meds), out)
            p(f"  {'Max cycles per tx':<33s}" + "".join(maxs), out)

        p("", out)

        # Code changes
        code = [f"{'---':>15s}"]
        if arb_verdicts:
            code.append(f"{'0':>15s}")
        if bsc_verdicts:
            code.append(f"{'0':>15s}")
        p(f"  {'Code changes':<33s}" + "".join(code), out)

        p("", out)
        p("Errors:", out)
        p(f"  {'Ethereum':<33s} {eth_verdicts.get('error', 0):>15,}", out)
        if arb_verdicts:
            p(f"  {'Arbitrum':<33s}"
              f" {arb_verdicts.get('error', 0):>15,}", out)
        if bsc_verdicts:
            p(f"  {'BSC':<33s}"
              f" {bsc_verdicts.get('error', 0):>15,}", out)

    print(f"Summary: {OUT_TXT}")


if __name__ == "__main__":
    main()
