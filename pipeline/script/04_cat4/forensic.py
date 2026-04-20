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
import shutil
import subprocess
import sys
from collections import Counter
from pathlib import Path

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
ARTIFACT_DIR = EVAL_DIR.parent
BLOCKDB_DIR = ARTIFACT_DIR / "blockdb"
SAMPLES_DIR = EVAL_DIR / "output" / "samples"
FORENSIC_DIR = EVAL_DIR / "output" / "cat4_forensic"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)

SAMPLE_FILE = SAMPLES_DIR / "05_manual_sample_cat4_eigenphi_only.csv"
SUMMARY_CSV = FORENSIC_DIR / "summary.csv"
OUT_TXT = SUMMARIES_DIR / "04_cat4/forensic.txt"

DETECT_MODE = os.environ.get("DETECT_MODE", "skip")
DETECT_CONFIG = os.environ.get("DETECT_CONFIG", "")
USE_DOCKER = shutil.which("inspect_tx_offline") is None


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def find_trace(tx_hash, block_number):
    """Find trace + cft_input in blockdb for a given tx."""
    for subdir in ["evaluation", "comparison", "220k", "1k", ""]:
        base = BLOCKDB_DIR / subdir / str(block_number) if subdir else BLOCKDB_DIR / str(block_number)
        trace = base / f"{tx_hash}.trace.json"
        cft = base / f"{tx_hash}.cft_input.json"
        if trace.exists() and cft.exists():
            return str(trace), str(cft)
    return None, None


def run_inspect(tx_hash, block_number):
    """Run detection on a single transaction. Returns True on success."""
    tx_dir = FORENSIC_DIR / tx_hash
    if (tx_dir / "arbitrage.json").exists():
        return True  # already done

    tx_dir.mkdir(parents=True, exist_ok=True)

    if DETECT_MODE == "online":
        # RPC mode: fetch trace from archive node
        import tempfile, json
        tx_file = Path(tempfile.mktemp(suffix=".json"))
        tx_file.write_text(json.dumps([tx_hash]))
        try:
            cmd = [
                "docker", "run", "--rm",
                "-v", f"{tx_file}:/tmp/tx.json:ro",
                "-v", f"{DETECT_CONFIG}:/tmp/config.json:ro",
                "-v", f"{FORENSIC_DIR}:/forensic",
                "detect-api", "inspect_tx",
                "--config", "/tmp/config.json",
                "--transaction", "/tmp/tx.json",
                "--outdir", "/forensic",
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
            return (tx_dir / "arbitrage.json").exists()
        except (subprocess.TimeoutExpired, Exception) as e:
            print(f"  Error: {e}")
            return False
        finally:
            tx_file.unlink(missing_ok=True)
    else:
        # Offline mode: use pre-exported traces
        trace_path, cft_path = find_trace(tx_hash, block_number)
        if not trace_path:
            print(f"  Trace not found for {tx_hash} (block {block_number})")
            return False
        try:
            if USE_DOCKER:
                cmd = [
                    "docker", "run", "--rm",
                    "-v", f"{BLOCKDB_DIR}:/blockdb:ro",
                    "-v", f"{FORENSIC_DIR}:/forensic",
                    "detect-api", "inspect_tx_offline",
                    "--trace", trace_path.replace(str(BLOCKDB_DIR), "/blockdb"),
                    "--cft-input", cft_path.replace(str(BLOCKDB_DIR), "/blockdb"),
                    "--outdir", "/forensic",
                ]
            else:
                cmd = [
                    "inspect_tx_offline",
                    "--trace", trace_path,
                    "--cft-input", cft_path,
                    "--outdir", str(FORENSIC_DIR),
                ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            return (tx_dir / "arbitrage.json").exists()
        except (subprocess.TimeoutExpired, Exception) as e:
            print(f"  Error running inspect_tx_offline: {e}")
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

    if DETECT_MODE == "skip":
        print("SKIPPED: no blockdb/ and no --online config.")
        print("Run with --offline (needs blockdb/) or --online --config <path>")
        return

    if DETECT_MODE == "offline" and not BLOCKDB_DIR.exists():
        print(f"ERROR: {BLOCKDB_DIR} not found.")
        print("Place exported traces in artifact/blockdb/")
        sys.exit(1)

    # Read cat4 samples (tx_hash + block)
    samples = []
    with open(SAMPLE_FILE) as f:
        reader = csv.DictReader(f)
        for row in reader:
            samples.append((row["tx_hash"], int(row["block"])))

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

    for i, (tx_hash, block) in enumerate(samples):
        skip = (FORENSIC_DIR / tx_hash / "arbitrage.json").exists()
        if skip:
            print(f"[{i+1}/{total}] SKIP {tx_hash[:16]}... (done)")
        else:
            print(f"[{i+1}/{total}] {tx_hash[:16]}... ", end="", flush=True)
            ok = run_inspect(tx_hash, block)
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
