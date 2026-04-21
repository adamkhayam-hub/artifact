"""
18_arbinet_comparison.py — Three-way comparison: Ours vs ArbiNet vs Eigenphi.

Setup:
    ArbiNet predictions for the comparison block range are shipped in
    `data/arbinet/` (pre-computed). No separate setup is needed to run
    this script in offline mode.

Reads:
    data/system_compact.csv       (Ours verdicts, from 00_preprocess.py)
    data/eigenphi_arbis_txs.csv  (Eigenphi labels)
    data/arbinet_results.csv     (ArbiNet predictions)

Writes:
    summaries/05_arbinet/comparison.txt
    figures/fig_three_way.pdf

Block range: COMPARISON_FIRST..COMPARISON_LAST (1000 consecutive blocks)
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import sys
from collections import Counter
from pathlib import Path

csv.field_size_limit(sys.maxsize)

# ── Configuration ──────────────────────────────────────────────
EVAL_DIR = Path(__file__).resolve().parent.parent.parent
DATA_DIR = EVAL_DIR / "data"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
FIGURES_DIR = EVAL_DIR / "output" / "figures"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)
FIGURES_DIR.mkdir(parents=True, exist_ok=True)

# 1000 consecutive blocks from the middle of the evaluation range
COMPARISON_FIRST = 24_100_000
COMPARISON_LAST = 24_100_999

# ArbiNet fork path (set to your clone location)
ARBINET_DIR = Path.home() / "git" / "arbinet"

# Input files
# For the 3-way comparison, use the dedicated 3-way CSV if it exists,
# otherwise fall back to the main compact CSV.
THREEWAY_CSV = DATA_DIR / "system_arbis_3wayeval.csv"
COMPACT_CSV = DATA_DIR / "system_compact.csv"
EIGENPHI_CSV = DATA_DIR / "eigenphi_arbis_txs.csv"  # full file, covers 24.1M range
ARBINET_CSV = DATA_DIR / "arbinet" / "arbinet1k.csv"

# Output files
OUT_TXT = SUMMARIES_DIR / "05_arbinet/comparison.txt"
OUT_FIG = FIGURES_DIR / "fig_three_way.pdf"


def normalize_hash(h):
    h = h.strip()
    if h.startswith("\\x"):
        h = h[2:]
    if h.startswith("0x") or h.startswith("0X"):
        h = h[2:]
    return h.lower()


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def load_system_in_range():
    """Load Ours verdicts for the comparison block range.

    Uses the dedicated 3-way CSV (bench format) if available,
    otherwise falls back to the main compact CSV.
    """
    import json
    system = {}  # hash -> verdict

    if THREEWAY_CSV.exists():
        # Bench format: tx_hash,block,tag,...,tag_data
        VERDICT_FROM_TAG = {4: "arbitrage", 5: "warning"}
        with open(THREEWAY_CSV) as f:
            reader = csv.reader(f)
            for row in reader:
                if row[0].startswith("transaction"):
                    continue  # skip header
                tx_hash = normalize_hash(row[0])
                block = int(row[1])
                if COMPARISON_FIRST <= block <= COMPARISON_LAST:
                    tag = int(row[2])
                    system[tx_hash] = VERDICT_FROM_TAG.get(tag, "unknown")
        return system

    # Fallback: compact CSV
    with open(COMPACT_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            block = int(row["block"])
            if COMPARISON_FIRST <= block <= COMPARISON_LAST:
                system[row["tx_hash"]] = row["verdict"]
    return system


def load_eigenphi_in_range():
    """Load Eigenphi labels for the comparison block range."""
    eigenphi = set()
    with open(EIGENPHI_CSV) as f:
        reader = csv.reader(f)
        for row in reader:
            try:
                block = int(row[0])
                if COMPARISON_FIRST <= block <= COMPARISON_LAST:
                    h = normalize_hash(row[1])
                    eigenphi.add(h)
            except (IndexError, ValueError):
                continue
    return eigenphi


def load_arbinet():
    """Load ArbiNet detections.

    CSV format: tx_hash,block
    Every row is a detected arbitrage (ArbiNet only outputs positives).
    """
    if not ARBINET_CSV.exists():
        print(f"ERROR: {ARBINET_CSV} not found.")
        print("Run parse_arbinet.py first.")
        sys.exit(1)

    arbinet = {}  # hash -> bool
    with open(ARBINET_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            h = normalize_hash(row.get("tx_hash", ""))
            arbinet[h] = True  # all rows are arbitrage detections
    return arbinet


def main():
    # Load data
    print("Loading Ours verdicts...")
    system = load_system_in_range()
    print(f"  {len(system)} transactions in range")

    print("Loading Eigenphi labels...")
    eigenphi = load_eigenphi_in_range()
    print(f"  {len(eigenphi)} labels in range")

    print("Loading ArbiNet predictions...")
    arbinet = load_arbinet()
    print(f"  {len(arbinet)} predictions")

    # All transaction hashes in the comparison
    all_hashes = set(system.keys()) | eigenphi | set(arbinet.keys())
    in_range_hashes = set()
    for h in all_hashes:
        # Only include txs that at least one system flagged
        if h in system or h in eigenphi or h in arbinet:
            in_range_hashes.add(h)

    # Build 8-cell table
    #   Ours+/- x Eigenphi+/- x ArbiNet+/-
    cells = Counter()
    for h in in_range_hashes:
        a = h in system  # Ours flagged (arbitrage or warning)
        e = h in eigenphi  # Eigenphi flagged
        n = arbinet.get(h, False)  # ArbiNet predicted arbitrage

        # Finer: Ours confirmed vs warning
        a_confirmed = system.get(h) == "arbitrage"
        a_warning = system.get(h) == "warning"

        key = (
            "A+" if a else "A-",
            "E+" if e else "E-",
            "N+" if n else "N-",
        )
        cells[key] += 1

    with open(OUT_TXT, "w") as out:
        p("=" * 70, out)
        p("THREE-WAY COMPARISON: Ours vs ArbiNet vs Eigenphi", out)
        p("=" * 70, out)
        p(f"Block range: {COMPARISON_FIRST} - {COMPARISON_LAST} "
          f"({COMPARISON_LAST - COMPARISON_FIRST + 1} blocks)", out)
        p(f"Transactions in range: {len(in_range_hashes)}", out)
        p("", out)

        # Summary counts
        system_pos = sum(1 for h in in_range_hashes if h in system)
        eigenphi_pos = len(eigenphi & in_range_hashes)
        arbinet_pos = sum(1 for h in in_range_hashes if arbinet.get(h, False))

        p(f"Ours detections:   {system_pos}", out)
        p(f"Eigenphi labels:    {eigenphi_pos}", out)
        p(f"ArbiNet positives:  {arbinet_pos}", out)
        p("", out)

        # 8-cell table
        p("-" * 70, out)
        p("8-CELL COMPARISON TABLE", out)
        p("-" * 70, out)
        p(f"{'Ours':>8} {'Eigenphi':>10} {'ArbiNet':>10} {'Count':>8} "
          f"{'%':>7}", out)
        p("-" * 50, out)

        total = len(in_range_hashes) if in_range_hashes else 1
        for a_label in ["A+", "A-"]:
            for e_label in ["E+", "E-"]:
                for n_label in ["N+", "N-"]:
                    key = (a_label, e_label, n_label)
                    count = cells.get(key, 0)
                    pct = count / total * 100
                    p(f"{a_label:>8} {e_label:>10} {n_label:>10} "
                      f"{count:>8} {pct:>6.1f}%", out)
        p("", out)

        # Key findings
        p("-" * 70, out)
        p("KEY FINDINGS", out)
        p("-" * 70, out)

        all_agree = cells.get(("A+", "E+", "N+"), 0)
        system_only = (cells.get(("A+", "E-", "N-"), 0) +
                      cells.get(("A+", "E-", "N+"), 0))
        eigenphi_only = (cells.get(("A-", "E+", "N-"), 0) +
                         cells.get(("A-", "E+", "N+"), 0))
        arbinet_only = (cells.get(("A-", "E-", "N+"), 0) +
                        cells.get(("A+", "E-", "N+"), 0))

        system_eigenphi_not_arbinet = cells.get(("A+", "E+", "N-"), 0)
        all_three = cells.get(("A+", "E+", "N+"), 0)
        eigenphi_arbinet_not_system = cells.get(("A-", "E+", "N+"), 0)

        p(f"  All three agree (A+ E+ N+):           {all_agree}", out)
        p(f"  Ours + Eigenphi, ArbiNet misses:      "
          f"{system_eigenphi_not_arbinet}", out)
        p(f"  Eigenphi + ArbiNet, Ours misses:      "
          f"{eigenphi_arbinet_not_system}", out)
        p(f"  Ours-only (not Eigenphi, not ArbiNet): "
          f"{cells.get(('A+', 'E-', 'N-'), 0)}", out)
        p(f"  Eigenphi-only (not Ours, not ArbiNet): "
          f"{cells.get(('A-', 'E+', 'N-'), 0)}", out)
        p("", out)

        # Ours-exclusive breakdown by verdict tier
        p("-" * 70, out)
        p("OURS-EXCLUSIVE BREAKDOWN", out)
        p("-" * 70, out)
        exclusive_confirmed = 0
        exclusive_attempted = 0
        exclusive_probable = 0
        exclusive_uncertain = 0
        for h in in_range_hashes:
            if h in system and h not in eigenphi and h not in arbinet:
                verdict = system[h]
                if verdict == "arbitrage":
                    exclusive_confirmed += 1
                elif verdict == "warning":
                    # Need full data to classify warnings
                    exclusive_attempted += 1  # counted as warning
        # Load full data for warning breakdown
        if THREEWAY_CSV.exists():
            import json
            warning_cats = Counter()
            with open(THREEWAY_CSV) as wf:
                wreader = csv.reader(wf)
                for row in wreader:
                    if row[0].startswith("transaction"):
                        continue
                    wh = normalize_hash(row[0])
                    if wh not in eigenphi and wh not in arbinet:
                        tag = int(row[2])
                        if tag == 5:
                            try:
                                data = json.loads(row[7])
                                resume = data.get("resume", data)
                                reasons = resume.get("reason", [])
                                has_neg = ("negativeProfit" in reasons
                                           or "finalBalanceNegative" in reasons)
                                has_left = "leftoverTransaction" in reasons
                                has_mix = ("balanceMixed" in reasons
                                           or "finalBalanceMixed" in reasons)
                                if has_neg:
                                    warning_cats["attempted"] += 1
                                elif has_left:
                                    warning_cats["probable"] += 1
                                elif has_mix:
                                    warning_cats["uncertain"] += 1
                                else:
                                    warning_cats["other"] += 1
                            except Exception:
                                warning_cats["parse_error"] += 1
            exclusive_total = exclusive_confirmed + sum(warning_cats.values())
            p(f"  Confirmed:   {exclusive_confirmed:>6}"
              f"  ({100*exclusive_confirmed/exclusive_total:.1f}%)", out)
            for cat in ["attempted", "probable", "uncertain", "other"]:
                n = warning_cats.get(cat, 0)
                p(f"  {cat.capitalize():11s}  {n:>6}"
                  f"  ({100*n/exclusive_total:.1f}%)", out)
            p(f"  Total:       {exclusive_total:>6}", out)
        p("", out)

        # Pairwise agreement
        p("-" * 70, out)
        p("PAIRWISE AGREEMENT", out)
        p("-" * 70, out)

        ae_agree = sum(cells.get(k, 0)
                       for k in cells if k[0][1] == k[1][1])
        an_agree = sum(cells.get(k, 0)
                       for k in cells if k[0][1] == k[2][1])
        en_agree = sum(cells.get(k, 0)
                       for k in cells if k[1][1] == k[2][1])

        p(f"  Ours-Eigenphi agree: {ae_agree}/{total} "
          f"({ae_agree/total*100:.1f}%)", out)
        p(f"  Ours-ArbiNet agree:  {an_agree}/{total} "
          f"({an_agree/total*100:.1f}%)", out)
        p(f"  Eigenphi-ArbiNet:     {en_agree}/{total} "
          f"({en_agree/total*100:.1f}%)", out)
        p("", out)

        # Temporal degradation note
        p("-" * 70, out)
        p("NOTES", out)
        p("-" * 70, out)
        p("  ArbiNet was trained on blocks 15,540,000-15,585,000 "
          "(Sep 2022).", out)
        p(f"  Comparison blocks: {COMPARISON_FIRST}-{COMPARISON_LAST} "
          "(Nov 2025-Mar 2026).", out)
        p("  Temporal gap: ~3 years. New protocols (V4, etc.) "
          "not in training data.", out)
        p("  Ours requires no retraining: structural rules are "
          "protocol-agnostic.", out)

    print(f"\nSummary written to {OUT_TXT}")

    # Figure: Venn-style bar chart
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        categories = [
            "All three",
            "Ours+Eigenphi\nonly",
            "Ours+ArbiNet\nonly",
            "Eigenphi+ArbiNet\nonly",
            "Ours only",
            "Eigenphi only",
            "ArbiNet only",
        ]
        values = [
            cells.get(("A+", "E+", "N+"), 0),
            cells.get(("A+", "E+", "N-"), 0),
            cells.get(("A+", "E-", "N+"), 0),
            cells.get(("A-", "E+", "N+"), 0),
            cells.get(("A+", "E-", "N-"), 0),
            cells.get(("A-", "E+", "N-"), 0),
            cells.get(("A-", "E-", "N+"), 0),
        ]
        colors = [
            "#2ecc71",  # all three: green
            "#3498db",  # system+eigenphi: blue
            "#9b59b6",  # system+arbinet: purple
            "#e67e22",  # eigenphi+arbinet: orange
            "#1abc9c",  # system only: teal
            "#e74c3c",  # eigenphi only: red
            "#f39c12",  # arbinet only: yellow
        ]

        fig, ax = plt.subplots(figsize=(8, 4))
        bars = ax.barh(categories, values, color=colors, edgecolor="white")
        ax.set_xlabel("Number of transactions")
        ax.set_title(f"Three-way comparison "
                     f"(blocks {COMPARISON_FIRST}-{COMPARISON_LAST})")

        for bar, val in zip(bars, values):
            if val > 0:
                ax.text(bar.get_width() + max(values) * 0.01,
                        bar.get_y() + bar.get_height() / 2,
                        str(val), va="center", fontsize=9)

        plt.tight_layout()
        fig.savefig(OUT_FIG, dpi=150, bbox_inches="tight")
        plt.close()
        print(f"Figure written to {OUT_FIG}")
    except ImportError:
        print("matplotlib not available; skipping figure.")


if __name__ == "__main__":
    main()
