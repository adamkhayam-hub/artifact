"""
26_bsc_summary.py — Summarize BSC cross-chain validation results.

Reads:  data/bsc_1k/summary.csv
Writes: summaries/06_crosschain/bsc.txt
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import sys
from collections import Counter
from pathlib import Path

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
DATA_DIR = EVAL_DIR / "data" / "bsc_1k"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)

SUMMARY_CSV = DATA_DIR / "summary.csv"
OUT = SUMMARIES_DIR / "06_crosschain/bsc.txt"


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def main():
    if not SUMMARY_CSV.exists():
        print(f"ERROR: {SUMMARY_CSV} not found.")
        print("Run run_bsc_1k.sh first.")
        sys.exit(1)

    rows = []
    with open(SUMMARY_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)

    verdicts = Counter(r["verdict"] for r in rows)
    blocks = set(r["block"] for r in rows)

    # Estimate total txs including legacy-skipped
    # Sample 10 blocks via RPC to get total vs EIP-1559 ratio
    import json
    import urllib.request
    RPC = "https://bnb-mainnet.g.alchemy.com/v2/_l8Cppqu66CAVCdnZ7lG0"
    sample_blocks = sorted(set(r["block"] for r in rows))[:10]
    total_all = 0
    total_eip1559 = 0
    for block_dec in sample_blocks:
        block_hex = hex(int(block_dec))
        req = urllib.request.Request(
            RPC, method="POST",
            headers={"Content-Type": "application/json"},
            data=json.dumps({
                "jsonrpc": "2.0", "method": "eth_getBlockByNumber",
                "params": [block_hex, True], "id": 1
            }).encode())
        try:
            with urllib.request.urlopen(req, timeout=10) as resp:
                data = json.loads(resp.read())
            txs = data.get("result", {}).get("transactions", [])
            total_all += len(txs)
            eip = sum(1 for tx in txs
                      if tx.get("type") in ("0x2", "0x1"))
            total_eip1559 += eip
        except Exception:
            pass
    if total_all > 0:
        eip_ratio = total_eip1559 / total_all
        estimated_total = int(len(rows) / eip_ratio) if eip_ratio > 0 else 0
        estimated_skipped = estimated_total - len(rows)
    else:
        estimated_total = 0
        estimated_skipped = 0
        eip_ratio = 0

    with open(OUT, "w") as out:
        p("=" * 60, out)
        p("BSC CROSS-CHAIN VALIDATION", out)
        p("=" * 60, out)
        p(f"Blocks: {len(blocks)}", out)
        p(f"EIP-1559 transactions analyzed: {len(rows)}", out)
        if estimated_total > 0:
            p(f"Estimated total (incl. legacy): ~{estimated_total:,}", out)
            p(f"Legacy skipped: ~{estimated_skipped:,}"
              f" ({100*(1-eip_ratio):.0f}% of block txs)", out)
        else:
            p("(Legacy count unavailable)", out)
        p("", out)

        total = len(rows)
        p("Verdicts:", out)
        for v in ["arbitrage", "warning", "none", "error"]:
            count = verdicts.get(v, 0)
            pct = count / total * 100 if total > 0 else 0
            p(f"  {v:12s}  {count:>6d}  ({pct:.1f}%)", out)

        flagged = verdicts.get("arbitrage", 0) + verdicts.get("warning", 0)
        p("", out)
        p(f"Flagged (arb + warn): {flagged} ({flagged/total*100:.1f}%)", out)

        # Cycle stats for flagged txs
        arb_rows = [r for r in rows if r["verdict"] == "arbitrage"]
        warn_rows = [r for r in rows if r["verdict"] == "warning"]

        if arb_rows:
            cycles = [int(r.get("num_cycles", 0)) for r in arb_rows]
            p("", out)
            p(f"Confirmed arbitrages: {len(arb_rows)}", out)
            p(f"  Avg cycles: {sum(cycles)/len(cycles):.1f}", out)
            p(f"  Max cycles: {max(cycles)}", out)

        if warn_rows:
            cycles = [int(r.get("num_cycles", 0)) for r in warn_rows]
            leftovers = [int(r.get("num_leftovers", 0)) for r in warn_rows]
            p("", out)
            p(f"Warnings: {len(warn_rows)}", out)
            p(f"  Avg cycles: {sum(cycles)/len(cycles):.1f}", out)
            p(f"  Avg leftovers: {sum(leftovers)/len(leftovers):.1f}", out)

        # Reason breakdown for warnings
        reason_counts = Counter()
        for r in warn_rows:
            reasons = r.get("reasons", "").split("|")
            for reason in reasons:
                if reason:
                    reason_counts[reason] += 1

        if reason_counts:
            p("", out)
            p("Warning reasons:", out)
            for reason, count in reason_counts.most_common():
                p(f"  {reason:30s}  {count:>5d}", out)

        # Detection rate comparison with other chains
        p("", out)
        p("-" * 60, out)
        p("COMPARISON WITH OTHER CHAINS", out)
        p("-" * 60, out)
        p(f"  BSC:      {len(arb_rows)} arb, {len(warn_rows)} warn"
          f" / {total} txs"
          f" ({flagged/total*100:.1f}% flagged)", out)

        # Try to load Arbitrum for comparison
        arb_csv = EVAL_DIR / "data" / "arbitrum_1k" / "summary.csv"
        if arb_csv.exists():
            arb_rows_all = []
            with open(arb_csv) as f:
                for row in csv.DictReader(f):
                    arb_rows_all.append(row)
            arb_verdicts = Counter(r["verdict"] for r in arb_rows_all)
            arb_total = len(arb_rows_all)
            arb_flagged = (arb_verdicts.get("arbitrage", 0)
                           + arb_verdicts.get("warning", 0))
            p(f"  Arbitrum: {arb_verdicts.get('arbitrage', 0)} arb,"
              f" {arb_verdicts.get('warning', 0)} warn"
              f" / {arb_total} txs"
              f" ({arb_flagged/arb_total*100:.1f}% flagged)", out)

    print(f"Summary written to {OUT}")


if __name__ == "__main__":
    main()
