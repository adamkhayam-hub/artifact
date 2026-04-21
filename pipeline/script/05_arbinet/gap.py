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
import shutil
import subprocess
import sys
from pathlib import Path

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
ARTIFACT_DIR = EVAL_DIR.parent
BLOCKDB_DIR = ARTIFACT_DIR / "blockdb"
DATA_DIR = EVAL_DIR / "data"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)

THREEWAY_CSV = DATA_DIR / "system_arbis_3wayeval.csv"
EIGENPHI_CSV = DATA_DIR / "eigenphi_arbis_txs.csv"
ARBINET_CSV = DATA_DIR / "arbinet" / "arbinet1k.csv"
GAP_DIR = EVAL_DIR / "output" / "3way_gap"
HASHES_JSON = EVAL_DIR / "output" / "3way_gap_hashes.json"
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


def find_trace(tx_hash):
    """Find trace + cft_input in blockdb for a gap tx (1K range)."""
    for subdir in ["1k", "220k", ""]:
        base = BLOCKDB_DIR / subdir if subdir else BLOCKDB_DIR
        if not base.exists():
            continue
        for block_dir in base.iterdir():
            if not block_dir.is_dir():
                continue
            trace = block_dir / f"{tx_hash}.trace.json"
            cft = block_dir / f"{tx_hash}.cft_input.json"
            if trace.exists() and cft.exists():
                return str(trace), str(cft)
    return None, None


DETECT_MODE = os.environ.get("DETECT_MODE", "skip")
DETECT_CONFIG = os.environ.get("DETECT_CONFIG", "")


def run_inspect(tx_hash):
    """Run detection on a gap transaction. Returns True on success."""
    tx_dir = GAP_DIR / tx_hash
    if (tx_dir / "arbitrage.json").exists():
        return True

    tx_dir.mkdir(parents=True, exist_ok=True)

    if DETECT_MODE == "online":
        import tempfile, json
        tx_file = Path(tempfile.mktemp(suffix=".json"))
        tx_file.write_text(json.dumps([tx_hash]))
        try:
            cmd = [
                "docker", "run", "--rm",
                "-v", f"{tx_file}:/tmp/tx.json:ro",
                "-v", f"{DETECT_CONFIG}:/tmp/config.json:ro",
                "-v", f"{GAP_DIR}:/gap",
                "detect-api", "inspect_tx",
                "--config", "/tmp/config.json",
                "--transaction", "/tmp/tx.json",
                "--outdir", "/gap",
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
            return (tx_dir / "arbitrage.json").exists()
        except (subprocess.TimeoutExpired, Exception):
            return False
        finally:
            tx_file.unlink(missing_ok=True)
    else:
        trace_path, cft_path = find_trace(tx_hash)
        if not trace_path:
            return False
        use_docker = shutil.which("inspect_tx_offline") is None
        try:
            if use_docker:
                cmd = [
                    "docker", "run", "--rm",
                    "-v", f"{BLOCKDB_DIR}:/blockdb:ro",
                    "-v", f"{GAP_DIR}:/gap",
                    "detect-api", "inspect_tx_offline",
                    "--trace", trace_path.replace(str(BLOCKDB_DIR), "/blockdb"),
                    "--cft-input", cft_path.replace(str(BLOCKDB_DIR), "/blockdb"),
                    "--outdir", "/gap",
                ]
            else:
                cmd = [
                    "inspect_tx_offline",
                    "--trace", trace_path,
                    "--cft-input", cft_path,
                    "--outdir", str(GAP_DIR),
                ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            return (tx_dir / "arbitrage.json").exists()
        except (subprocess.TimeoutExpired, Exception):
            return False


def generate_dots(categories):
    """Step 2: run inspect_tx_offline on all gap transactions."""
    GAP_DIR.mkdir(parents=True, exist_ok=True)
    all_hashes = []
    for hashes in categories.values():
        all_hashes.extend(hashes)

    total = len(all_hashes)
    ok = 0
    for i, tx_hash in enumerate(all_hashes):
        skip = (GAP_DIR / tx_hash / "arbitrage.json").exists()
        if skip:
            ok += 1
            continue
        print(f"  [{i+1}/{total}] {tx_hash[:16]}... ", end="", flush=True)
        success = run_inspect(tx_hash)
        print("OK" if success else "SKIP (no trace)")
        if success:
            ok += 1

    print(f"  Generated: {ok}/{total}")


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
    if DETECT_MODE == "skip":
        print("SKIPPED: no blockdb/ and no --online config.")
        print("Run with --offline (needs blockdb/) or --online --config <path>")
        return

    if "--extract" in sys.argv or not HASHES_JSON.exists():
        categories = extract_hashes()
    else:
        with open(HASHES_JSON) as f:
            categories = json.load(f)

    # Step 2: generate DOTs
    mode_label = "RPC" if DETECT_MODE == "online" else "blockdb"
    print(f"\nStep 2: generating DOTs ({mode_label})...")
    generate_dots(categories)

    # Step 3: analyze DOTs
    analyze(categories)


if __name__ == "__main__":
    main()
