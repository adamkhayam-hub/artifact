"""
15_cat4_forensic.py — Run forensic analysis on cat4 (Eigenphi-only) transactions.

Step 1: Run debug_graph on each cat4 sample via RPC
Step 2: Parse results and classify each transaction
Step 3: Produce summary

Reads:  samples/05_manual_sample_cat4_eigenphi_only.csv
Writes: data/cat4_forensic/<tx_hash>/arbitrage.json (+ .dot, trace.json)
        data/cat4_forensic/summary.csv
        summaries/04_cat4/forensic.txt

Requires: ETHEREUM_CONFIG env var set (source system.env first)
          debug_graph.exe built (make build-ocaml)

Resume-safe: skips transactions whose arbitrage.json already exists.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
REPO_ROOT = EVAL_DIR.parent.parent
SAMPLES_DIR = EVAL_DIR / "output" / "samples"
DATA_DIR = EVAL_DIR / "data"
FORENSIC_DIR = DATA_DIR / "cat4_forensic"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)

SAMPLE_FILE = SAMPLES_DIR / "05_manual_sample_cat4_eigenphi_only.csv"
SUMMARY_CSV = FORENSIC_DIR / "summary.csv"
OUT_TXT = SUMMARIES_DIR / "04_cat4/forensic.txt"

EXE = REPO_ROOT / "_build" / "default" / "debug" / "graph" / "debug_graph.exe"
CONFIG = os.environ.get("ETHEREUM_CONFIG", "")


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def run_debug_graph(tx_hash):
    """Run debug_graph on a single transaction. Returns True on success."""
    tx_dir = FORENSIC_DIR / tx_hash
    if (tx_dir / "arbitrage.json").exists():
        return True  # already done

    tx_dir.mkdir(parents=True, exist_ok=True)
    tx_file = Path("/tmp") / f"cat4_tx_{tx_hash[:8]}.json"
    tx_file.write_text(f'["{tx_hash}"]')

    try:
        result = subprocess.run(
            [str(EXE), "--config", CONFIG,
             "--transaction", str(tx_file),
             "--outdir", str(FORENSIC_DIR)],
            capture_output=True, text=True, timeout=120)
        tx_file.unlink(missing_ok=True)
        return (tx_dir / "arbitrage.json").exists()
    except (subprocess.TimeoutExpired, Exception):
        tx_file.unlink(missing_ok=True)
        return False


def parse_result(tx_hash):
    """Parse arbitrage.json for a transaction."""
    arbi_file = FORENSIC_DIR / tx_hash / "arbitrage.json"
    if not arbi_file.exists():
        return {"verdict": "error", "reasons": "", "num_cycles": 0,
                "num_leftovers": 0, "has_arbitrage": False, "status": "no_output"}
    try:
        with open(arbi_file) as f:
            data = json.load(f)
        r = data["resume"]
        rr = r.get("resume", {})
        return {
            "verdict": r.get("arbitrage", "none"),
            "reasons": "|".join(r.get("reason", [])),
            "num_cycles": len(rr.get("transfersInCycles", [])),
            "num_leftovers": len(rr.get("leftovers", [])),
            "has_arbitrage": rr.get("hasArbitrage", False),
            "status": "ok",
        }
    except Exception:
        return {"verdict": "error", "reasons": "parse_error", "num_cycles": 0,
                "num_leftovers": 0, "has_arbitrage": False, "status": "parse_error"}


def classify(result):
    """Apply the cat4 decision tree."""
    if result["status"] != "ok":
        return "exec_error", f"debug_graph failed: {result['status']}"

    verdict = result["verdict"]
    has_arb = result["has_arbitrage"]
    reasons = result["reasons"].split("|") if result["reasons"] else []
    num_cycles = result["num_cycles"]

    if has_arb and verdict in ("arbitrage", "warning"):
        if verdict == "arbitrage":
            return "now_detected_confirmed", f"Confirmed arbitrage ({num_cycles} cycles)"
        else:
            return "now_detected_warning", f"Warning ({num_cycles} cycles, {','.join(reasons)})"

    if num_cycles > 0:
        return "has_cycles_not_arb", f"Cycles found but not arbitrage ({','.join(reasons)})"

    if "noArbitrageCycles" in reasons:
        if "balanceNegative" in reasons or "finalBalanceNegative" in reasons:
            return "eigenphi_fp_negative", "No cycles, negative balance — Eigenphi FP"
        elif "balancePositive" in reasons:
            return "possible_to_gap", "No cycles at to_ but positive balance — check DOTs for inner arbitrage"
        else:
            return "eigenphi_fp_other", f"No cycles ({','.join(reasons)})"

    return "unknown", f"Unclassified ({verdict}, {','.join(reasons)})"


def main():
    if not SAMPLE_FILE.exists():
        print(f"ERROR: {SAMPLE_FILE} not found. Run step 5 first.")
        sys.exit(1)

    if not EXE.exists():
        print(f"ERROR: {EXE} not found. Run 'make build-ocaml' first.")
        sys.exit(1)

    if not CONFIG:
        print("ERROR: ETHEREUM_CONFIG not set. Source system.env first.")
        sys.exit(1)

    # Read cat4 samples
    samples = []
    with open(SAMPLE_FILE) as f:
        reader = csv.DictReader(f)
        for row in reader:
            samples.append(row["tx_hash"])

    FORENSIC_DIR.mkdir(parents=True, exist_ok=True)
    total = len(samples)

    print("=" * 60)
    print("CAT4 FORENSIC ANALYSIS")
    print("=" * 60)
    print(f"Transactions: {total}")
    print(f"Output: {FORENSIC_DIR}")
    print()

    # Step 1: Run debug_graph on each transaction
    with open(SUMMARY_CSV, "w") as f:
        f.write("tx_hash,verdict,reasons,num_cycles,num_leftovers,has_arbitrage,status,classification,detail\n")

    for i, tx_hash in enumerate(samples):
        skip = (FORENSIC_DIR / tx_hash / "arbitrage.json").exists()
        if skip:
            print(f"[{i+1}/{total}] SKIP {tx_hash[:16]}... (done)")
        else:
            print(f"[{i+1}/{total}] {tx_hash[:16]}... ", end="", flush=True)
            ok = run_debug_graph(tx_hash)
            print("OK" if ok else "FAILED")

        # Step 2: Parse and classify
        result = parse_result(tx_hash)
        cat, detail = classify(result)

        with open(SUMMARY_CSV, "a") as f:
            f.write(f"{tx_hash},{result['verdict']},{result['reasons']},"
                    f"{result['num_cycles']},{result['num_leftovers']},"
                    f"{result['has_arbitrage']},{result['status']},"
                    f"{cat},{detail}\n")

    # Step 3: Summary
    classifications = Counter()
    rows = []
    with open(SUMMARY_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)
            classifications[row["classification"]] += 1

    with open(OUT_TXT, "w") as out:
        p("=" * 60, out)
        p("CAT4 FORENSIC SUMMARY", out)
        p("=" * 60, out)
        p(f"Total transactions: {len(rows)}", out)
        p("", out)

        p("Classification breakdown:", out)
        for cat, count in classifications.most_common():
            pct = count / len(rows) * 100
            p(f"  {cat:30s}: {count:4d} ({pct:5.1f}%)", out)

        p("", out)
        now_detected = (classifications.get("now_detected_confirmed", 0)
                       + classifications.get("now_detected_warning", 0))
        eigenphi_fp = (classifications.get("eigenphi_fp_negative", 0)
                      + classifications.get("eigenphi_fp_other", 0))
        to_gap = classifications.get("possible_to_gap", 0)
        has_cycles = classifications.get("has_cycles_not_arb", 0)
        errors = classifications.get("exec_error", 0)

        p("Interpretation:", out)
        p(f"  Now detected (current algo):  {now_detected:4d} ({now_detected/len(rows)*100:.1f}%)", out)
        p(f"  Eigenphi false positives:      {eigenphi_fp:4d} ({eigenphi_fp/len(rows)*100:.1f}%)", out)
        p(f"  Possible to_ gap:             {to_gap:4d} ({to_gap/len(rows)*100:.1f}%)"
          f" — check DOTs (script 04_cat4/to_gap.py)", out)
        p(f"  Has cycles but not arb:        {has_cycles:4d} ({has_cycles/len(rows)*100:.1f}%)", out)
        p(f"  Execution errors:              {errors:4d} ({errors/len(rows)*100:.1f}%)", out)

    print(f"\nSummary: {OUT_TXT}")


if __name__ == "__main__":
    main()
