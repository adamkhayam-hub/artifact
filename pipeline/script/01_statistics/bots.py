"""
21_bot_concentration.py — Bot concentration analysis.

How many unique sender addresses produce the detections?
Power-law distribution of arbitrage activity.

Reads:  data/system_arbis.csv (needs from address, column 0 = tx, but
        from address is not in compact CSV — extract from full CSV tag_data)
        OR data/system_compact.csv if we add from_address
Writes: summaries/01_statistics/bots.txt
        figures/fig_bot_concentration.pdf

NOTE: The bot is typically the `to` address (the smart contract
the EOA calls). The compact CSV does not contain addresses.
This script reads the full CSV to extract the bot (to) address
from the first cycle's origin.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import json
import sys
from collections import Counter
from pathlib import Path

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
DATA_DIR = EVAL_DIR / "data"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
FIGURES_DIR = EVAL_DIR / "output" / "figures"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)
FIGURES_DIR.mkdir(parents=True, exist_ok=True)

ARGOS_CSV = DATA_DIR / "system_arbis.csv"
OUT_TXT = SUMMARIES_DIR / "01_statistics/bots.txt"
OUT_FIG = FIGURES_DIR / "fig_bot_concentration.pdf"

TAG_DATA_COL = 7


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def normalize_hash(h):
    h = h.strip()
    if h.startswith("\\x"):
        h = h[2:]
    if h.startswith("0x") or h.startswith("0X"):
        h = h[2:]
    return h.lower()


def main():
    if not ARGOS_CSV.exists():
        print(f"ERROR: {ARGOS_CSV} not found.")
        sys.exit(1)

    print("Reading sender addresses from full CSV (this takes a few minutes)...")
    sender_counts = Counter()
    sender_verdicts = Counter()
    total = 0

    with open(ARGOS_CSV) as f:
        reader = csv.reader(f)
        for row in reader:
            total += 1
            try:
                data = json.loads(row[TAG_DATA_COL])
                resume = data.get("resume", data)
                verdict = resume.get("arbitrage", "none")

                # Extract from address from the first transfer or resume
                rr = resume.get("resume", {})
                cycles = rr.get("transfersInCycles", [])
                if cycles and cycles[0]:
                    first_transfer = cycles[0][0]
                    from_val = first_transfer.get("from", {}).get("value", {})
                    if isinstance(from_val, dict) and "value" in from_val:
                        addr = from_val["value"]
                        if isinstance(addr, dict):
                            addr = addr.get("address", "unknown")
                    elif isinstance(from_val, str):
                        addr = from_val
                    else:
                        addr = "unknown"
                    sender_counts[addr.lower()] += 1
                    sender_verdicts[(addr.lower(), verdict)] += 1
            except (IndexError, json.JSONDecodeError, KeyError):
                pass

            if total % 500_000 == 0:
                print(f"  {total:>10,} rows processed")

    # Top senders
    top_senders = sender_counts.most_common(50)

    with open(OUT_TXT, "w") as out:
        p("=" * 60, out)
        p("BOT CONCENTRATION ANALYSIS", out)
        p("=" * 60, out)
        p(f"Total transactions with cycles: {sum(sender_counts.values()):,}", out)
        p(f"Unique sender addresses: {len(sender_counts):,}", out)
        p("", out)

        # Power-law metrics
        values = sorted(sender_counts.values(), reverse=True)
        total_txs = sum(values)
        top10_pct = 100 * sum(values[:10]) / total_txs if total_txs else 0
        top50_pct = 100 * sum(values[:50]) / total_txs if total_txs else 0
        p(f"Top 10 senders: {sum(values[:10]):,} txs ({top10_pct:.1f}%)", out)
        p(f"Top 50 senders: {sum(values[:50]):,} txs ({top50_pct:.1f}%)", out)
        p("", out)

        p("Top 20 senders:", out)
        for addr, count in top_senders[:20]:
            pct = 100 * count / total_txs
            p(f"  {addr[:16]}...  {count:>8,}  ({pct:.1f}%)", out)

    print(f"Summary: {OUT_TXT}")

    # Figure: log-log rank plot
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np

        values = sorted(sender_counts.values(), reverse=True)
        ranks = range(1, len(values) + 1)

        fig, ax = plt.subplots(figsize=(6, 4))
        ax.loglog(ranks, values, ".", markersize=3, color="steelblue")
        ax.set_xlabel("Sender rank")
        ax.set_ylabel("Number of transactions")
        ax.set_title("Bot concentration (log-log)")
        plt.tight_layout()
        fig.savefig(OUT_FIG, dpi=150, bbox_inches="tight")
        plt.close()
        print(f"Figure: {OUT_FIG}")
    except ImportError:
        print("matplotlib not available; skipping figure.")


if __name__ == "__main__":
    main()
