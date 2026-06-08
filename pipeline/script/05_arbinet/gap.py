"""
28_3way_gap.py — Analyze 3-way gap transactions.

Step 1: Extract tx hashes not in Ours from 3-way comparison.
Step 2: Run debug_graph on each (via run_3way_gap.sh).
Step 3: Check DOTs for yellow nodes (same as 27_cat4_to_gap.py).

This script handles steps 1 and 3. Step 2 is out-of-band (RPC).

Reads:
    data/system_arbis_3wayeval.csv
    data/eigenphi_arbis_txs.csv
    data/arbinet/arbinet1k.csv
    data/3way_gap/<tx_hash>/*.dot (after step 2)

Writes:
    data/3way_gap_hashes.json (step 1: tx list for debug_graph)
    summaries/05_arbinet/gap.txt (step 3: analysis)
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import json
import os
import subprocess
import sys
from pathlib import Path

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
DATA_DIR = EVAL_DIR / "data"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)

THREEWAY_CSV = DATA_DIR / "system_arbis_3wayeval.csv"
EIGENPHI_CSV = DATA_DIR / "eigenphi_arbis_txs.csv"
ARBINET_CSV = DATA_DIR / "arbinet" / "arbinet1k.csv"
GAP_DIR = DATA_DIR / "3way_gap"
HASHES_JSON = DATA_DIR / "3way_gap_hashes.json"
OUT_TXT = SUMMARIES_DIR / "05_arbinet/gap.txt"

FIRST = 24_100_000
LAST = 24_100_999


def normalize_hash(h):
    h = h.strip()
    if h.startswith("\\x"):
        h = h[2:]
    if h.startswith("0x") or h.startswith("0X"):
        h = h[2:]
    return h.lower()


def extract_hashes():
    """Step 1: extract tx hashes not classified by Ours."""
    system = set()
    with open(THREEWAY_CSV) as f:
        reader = csv.reader(f)
        for row in reader:
            if row[0].startswith("transaction"):
                continue
            system.add(normalize_hash(row[0]))

    eigenphi = set()
    with open(EIGENPHI_CSV) as f:
        reader = csv.reader(f)
        for row in reader:
            try:
                block = int(row[0])
                if FIRST <= block <= LAST:
                    eigenphi.add(normalize_hash(row[1]))
            except (IndexError, ValueError):
                continue

    arbinet = set()
    with open(ARBINET_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            block = int(row["block"])
            if FIRST <= block <= LAST:
                arbinet.add(normalize_hash(row["tx_hash"]))

    arbi_only = sorted(arbinet - system - eigenphi)
    eig_only = sorted(eigenphi - system - arbinet)
    both_not_system = sorted((eigenphi & arbinet) - system)

    result = {
        "arbinet_only": arbi_only,
        "eigenphi_only": eig_only,
        "both_not_system": both_not_system,
    }

    with open(HASHES_JSON, "w") as f:
        json.dump(result, f, indent=2)

    all_hashes = arbi_only + eig_only + both_not_system
    print(f"ArbiNet-only:     {len(arbi_only)}")
    print(f"Eigenphi-only:    {len(eig_only)}")
    print(f"Both not Ours:   {len(both_not_system)}")
    print(f"Total to inspect: {len(all_hashes)}")
    print(f"Written to: {HASHES_JSON}")
    return result


def has_yellow_node(dot_path):
    with open(dot_path) as f:
        content = f.read()
    return content.count("#FFFF99") > 1


def get_last_dot(tx_dir):
    dots = sorted(
        [f for f in os.listdir(tx_dir) if f.endswith(".dot")],
        key=lambda x: int(x.replace(".dot", "")),
    )
    if not dots:
        return None
    return os.path.join(tx_dir, dots[-1])


def generate_pdfs(tx_dir):
    generated = 0
    for f in sorted(os.listdir(tx_dir)):
        if f.endswith(".dot"):
            dot_path = os.path.join(tx_dir, f)
            pdf_path = os.path.join(tx_dir, f.replace(".dot", ".pdf"))
            result = subprocess.run(
                ["dot", "-Tpdf", dot_path, "-o", pdf_path],
                capture_output=True,
            )
            if result.returncode == 0:
                generated += 1
    return generated


def analyze(categories):
    """Step 3: check DOTs for yellow nodes."""
    out = []

    def p(s=""):
        out.append(s)
        print(s)

    p("=" * 70)
    p("3-WAY GAP ANALYSIS")
    p("=" * 70)

    if not GAP_DIR.exists():
        p(f"  ERROR: {GAP_DIR} not found.")
        p("  Run debug_graph on the gap txs first (step 2).")
        with open(OUT_TXT, "w") as f:
            f.write("\n".join(out) + "\n")
        return

    total_pdfs = 0

    for cat_name, hashes in categories.items():
        yellow = []
        cycles_no_yellow = []
        no_cycles = []
        missing = []

        for tx in hashes:
            tx_dir = GAP_DIR / tx
            if not tx_dir.is_dir():
                missing.append(tx)
                continue

            n_pdfs = generate_pdfs(str(tx_dir))
            total_pdfs += n_pdfs

            last_dot = get_last_dot(str(tx_dir))
            if last_dot is None:
                no_cycles.append(tx)
                continue

            if has_yellow_node(last_dot):
                yellow.append(tx)
            else:
                # Check if any cycles exist (red doubleoctagons)
                with open(last_dot) as f:
                    content = f.read()
                has_cycle = content.count("FFE4E1") > 1
                if has_cycle:
                    cycles_no_yellow.append(tx)
                else:
                    no_cycles.append(tx)

        total = len(hashes)
        analyzed = total - len(missing)
        p("")
        p(f"--- {cat_name} ({total} txs, {analyzed} analyzed,"
          f" {len(missing)} missing) ---")
        if analyzed > 0:
            p(f"  Yellow (to_ gap):    {len(yellow):>4}"
              f"  ({100*len(yellow)/analyzed:.1f}%)")
            p(f"  Cycles, no yellow:   {len(cycles_no_yellow):>4}"
              f"  ({100*len(cycles_no_yellow)/analyzed:.1f}%)")
            p(f"  No cycles:           {len(no_cycles):>4}"
              f"  ({100*len(no_cycles)/analyzed:.1f}%)")

    p("")
    p(f"PDFs generated: {total_pdfs}")

    with open(OUT_TXT, "w") as f:
        f.write("\n".join(out) + "\n")
    print(f"\nSaved to {OUT_TXT}")


def main():
    if "--extract" in sys.argv or not HASHES_JSON.exists():
        categories = extract_hashes()
    else:
        with open(HASHES_JSON) as f:
            categories = json.load(f)

    if "--extract" in sys.argv:
        print("\nStep 1 done. Now run debug_graph on these txs.")
        print(f"Output to: {GAP_DIR}/")
        return

    analyze(categories)


if __name__ == "__main__":
    main()
