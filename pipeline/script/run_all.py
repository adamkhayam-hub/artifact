"""
Run the full evaluation pipeline.

Usage:
    python3 script/run_all.py                           # run all steps (auto-detect mode)
    python3 script/run_all.py --offline                 # force offline mode (uses blockdb/)
    python3 script/run_all.py --online --config cfg.json # RPC mode (uses archive node)
    python3 script/run_all.py --from 5                  # resume from step 5
    python3 script/run_all.py --clean                   # clean outputs first, then run all

Steps:
    0.   Preprocess            (00) — single pass over 26GB CSV
    1-3. Statistical analysis  (01, 02, 03) — read compact CSV
    4.   Figures               (04) — reads compact CSV
    5.   Sampling              (05) — reads full 26GB CSV (needs tag_data)
    6.   Inspect samples       (07) — reads full 26GB CSV (needs tag_data)
    7.   Resolve addresses     (08) — Blockscout API
    8.   Auto-verdict          (09)
    9.   Write verdicts        (10)
   10.   Detailed review       (11)
   11.   Final verdicts        (12)
   12.   Reasoned verdicts     (13)
   13.   Cat4 forensic         (15) — RPC execution + analysis
   14.   Manual review         (14) — after all automated analysis
   15.   Performance analysis  (17) — reads from compact CSV
   16.   Parse ArbiNet output  (parse_arbinet) — raw txt → CSV
   17.   ArbiNet comparison    (18) — three-way table
   18.   Arbitrum summary      (19) — cross-chain stats
"""

import shutil
import subprocess
import sys
import time
from pathlib import Path

EVAL_DIR = Path(__file__).resolve().parent.parent
SCRIPT_DIR = EVAL_DIR / "script"

OUTPUT = EVAL_DIR / "output"
SUMMARIES = OUTPUT / "summaries"
FIGURES = OUTPUT / "figures"
SAMPLES = OUTPUT / "samples"
REVIEW = OUTPUT / "manual_review"

DATA = EVAL_DIR / "data"

STEPS = [
    # --- 00: Preprocessing ---
    (0,  "00_preprocess.py",                      "Preprocess: CSV extraction + Eigenphi filter",
     [OUTPUT / "data" / "system_compact.csv"]),

    # --- 01: Statistics (reads compact CSV) ---
    (1,  "01_statistics/explore.py",              "Statistics: exploration + fixpoint coverage",
     [SUMMARIES / "01_statistics" / "explore.txt"]),
    (2,  "01_statistics/accuracy.py",             "Statistics: accuracy (Argos vs Eigenphi)",
     [SUMMARIES / "01_statistics" / "accuracy.txt"]),
    (3,  "01_statistics/topology.py",             "Statistics: topology",
     [SUMMARIES / "01_statistics" / "topology.txt"]),
    (4,  "01_statistics/performance.py",          "Statistics: performance",
     [SUMMARIES / "01_statistics" / "performance.txt"]),
    (5,  "01_statistics/attempted.py",            "Statistics: attempted arbitrage competition",
     [SUMMARIES / "01_statistics" / "attempted.txt"]),
    (6,  "01_statistics/bots.py",                 "Statistics: bot concentration",
     [SUMMARIES / "01_statistics" / "bots.txt"]),
    (7,  "01_statistics/temporal.py",             "Statistics: temporal distribution",
     [SUMMARIES / "01_statistics" / "temporal.txt"]),
    (8,  "01_statistics/gas.py",                  "Statistics: gas efficiency",
     [SUMMARIES / "01_statistics" / "gas.txt"]),

    # --- 02: Figures ---
    (9,  "02_figures/figures.py",                 "Figures: PDF generation",
     [FIGURES / "fig_confidence_tiers.pdf"]),

    # --- 03: Manual review ---
    (10, "03_manual_review/sample.py",            "Manual review: sampling (reads full CSV)",
     [SAMPLES / "05_manual_sample_cat1_both_confirmed.csv"]),
    (11, "03_manual_review/inspect_all.py",       "Manual review: inspect samples (reads full CSV)",
     [REVIEW / "inspections" / "cat1_both_confirmed"]),
    (12, "03_manual_review/resolve.py",           "Manual review: resolve addresses (Blockscout)",
     [REVIEW / "addresses" / "resolved_addresses.csv"]),
    (13, "03_manual_review/auto_verdict.py",      "Manual review: auto-verdict",
     [REVIEW / "verdicts" / "09_auto_verdicts" / "auto_verdicts_cat1.csv"]),
    (14, "03_manual_review/write_verdicts.py",    "Manual review: write verdicts",
     []),
    (15, "03_manual_review/detailed.py",          "Manual review: detailed review",
     [REVIEW / "verdicts" / "11_detailed_review" / "detailed_review_summary.txt"]),
    (16, "03_manual_review/final.py",             "Manual review: final verdicts",
     [REVIEW / "verdicts" / "12_final_verdicts" / "final_verdicts_summary.txt"]),
    (17, "03_manual_review/reasoned.py",          "Manual review: reasoned verdicts",
     [REVIEW / "verdicts" / "13_reasoned_verdicts" / "reasoned_summary.txt"]),
    (18, "03_manual_review/review.py",            "Manual review: full review (cats 1-4)",
     [REVIEW / "verdicts" / "14_manual_review" / "manual_review_summary.txt"]),

    # --- 04: Cat4 forensic ---
    (19, "04_cat4/forensic.py",                   "Cat4: forensic (RPC + analysis)",
     [SUMMARIES / "04_cat4" / "forensic.txt"]),
    (20, "04_cat4/to_gap.py",                     "Cat4: to_ gap analysis + PDF generation",
     [SUMMARIES / "04_cat4" / "to_gap.txt"]),

    # --- 05: ArbiNet comparison ---
    (21, "05_arbinet/parse.py",                   "ArbiNet: parse raw output",
     [DATA / "arbinet" / "arbinet1k.csv"]),
    (22, "05_arbinet/comparison.py",              "ArbiNet: three-way comparison",
     [SUMMARIES / "05_arbinet" / "comparison.txt"]),
    (23, "05_arbinet/degradation.py",             "ArbiNet: temporal degradation",
     [SUMMARIES / "05_arbinet" / "degradation.txt"]),
    (24, "05_arbinet/gap.py",                     "ArbiNet: 3-way gap analysis",
     [SUMMARIES / "05_arbinet" / "gap.txt"]),

    # --- 06: Cross-chain ---
    (25, "06_crosschain/arbitrum.py",             "Cross-chain: Arbitrum summary",
     [SUMMARIES / "06_crosschain" / "arbitrum.txt"]),
    (26, "06_crosschain/bsc.py",                  "Cross-chain: BSC summary",
     [SUMMARIES / "06_crosschain" / "bsc.txt"]),
    (27, "06_crosschain/comparison.py",           "Cross-chain: Ethereum vs Arbitrum vs BSC",
     [SUMMARIES / "06_crosschain" / "comparison.txt"]),

    # --- 07: Master summary ---
    (28, "99_master_summary.py",                  "Master summary: all numbers",
     [SUMMARIES / "99_master_summary.txt"]),
]

# Only clean outputs that depend on sampling (steps 5-10).
# Summaries and figures (steps 1-4) are preserved since they
# are expensive to regenerate (26GB CSV reads).
CLEAN_DIRS = ["samples", "manual_review"]


CLEAN_ALL_DIRS = [
    "output",
    "data/cat4_forensic", "data/3way_gap",
]

CLEAN_ALL_FILES = []


def clean(full=False):
    dirs = CLEAN_ALL_DIRS if full else CLEAN_DIRS
    label = "CLEANING ALL" if full else "CLEANING (samples + manual review)"
    print("=" * 60)
    print(label)
    print("=" * 60)
    for d in dirs:
        path = EVAL_DIR / d
        if path.exists():
            shutil.rmtree(path)
            print(f"  Removed {d}/")
        else:
            print(f"  {d}/ (already clean)")
    if full:
        for f in CLEAN_ALL_FILES:
            path = EVAL_DIR / f
            if path.exists():
                path.unlink()
                print(f"  Removed {f}")
    print()


def ensure_output_dirs():
    """Create output subdirectories."""
    for d in [SUMMARIES, FIGURES, SAMPLES, REVIEW,
              OUTPUT / "data"]:
        d.mkdir(parents=True, exist_ok=True)
    for d in ["01_statistics", "02_figures", "03_manual_review",
              "04_cat4", "05_arbinet", "06_crosschain"]:
        (SUMMARIES / d).mkdir(parents=True, exist_ok=True)


def outputs_exist(expected_outputs):
    """Check if all expected output files/dirs exist."""
    if not expected_outputs:
        return False
    return all(p.exists() for p in expected_outputs)


def run_step(step_num, script_name, description, expected_outputs=None):
    if expected_outputs and outputs_exist(expected_outputs):
        print(f"  STEP {step_num}: {description} — SKIPPED (outputs exist)")
        return

    print("=" * 60)
    print(f"STEP {step_num}: {description}")
    print(f"  Script: {script_name}")
    print("=" * 60)

    start = time.time()
    import os
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = str(SCRIPT_DIR) + (":" + existing if existing else "")

    # Statistical steps (1-4): quiet (scripts save their own summaries)
    # Manual review steps (5+): show stdout live
    quiet = step_num <= 4

    if quiet:
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / script_name)],
            cwd=str(EVAL_DIR),
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            text=True,
        )
    else:
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / script_name)],
            cwd=str(EVAL_DIR),
            env=env,
        )

    elapsed = time.time() - start

    if result.returncode != 0:
        print(f"\n  FAILED (exit code {result.returncode}) after {elapsed:.1f}s")
        if quiet and result.stderr:
            print(result.stderr)
        sys.exit(1)

    print(f"  Done in {elapsed:.1f}s")
    print()


def main():
    args = sys.argv[1:]
    start_from = 0
    end_at = 999

    if "--clean-all" in args:
        clean(full=True)
        args.remove("--clean-all")
    elif "--clean" in args:
        clean()
        args.remove("--clean")

    if "--from" in args:
        idx = args.index("--from")
        start_from = int(args[idx + 1])

    if "--to" in args:
        idx = args.index("--to")
        end_at = int(args[idx + 1])

    # Detection mode for steps 19-20, 24 (forensic + gap)
    import os
    if "--online" in args:
        if "--config" in args:
            cfg_idx = args.index("--config")
            os.environ["DETECT_MODE"] = "online"
            os.environ["DETECT_CONFIG"] = str(Path(args[cfg_idx + 1]).resolve())
            print(f"Mode: ONLINE (RPC via {os.environ['DETECT_CONFIG']})")
        else:
            print("ERROR: --online requires --config <path_to_config.json>")
            sys.exit(1)
    elif "--offline" in args:
        os.environ["DETECT_MODE"] = "offline"
        print("Mode: OFFLINE (using blockdb/)")
    else:
        # Auto-detect
        artifact_dir = EVAL_DIR.parent
        blockdb = artifact_dir / "blockdb"
        if blockdb.exists() and any(blockdb.iterdir()):
            os.environ["DETECT_MODE"] = "offline"
            print("Mode: OFFLINE (auto-detected blockdb/)")
        else:
            os.environ["DETECT_MODE"] = "skip"
            print("Mode: SKIP forensic steps (no blockdb/, no --online)")
    print()

    ensure_output_dirs()
    total_start = time.time()

    for step_num, script_name, description, expected in STEPS:
        if step_num < start_from or step_num > end_at:
            print(f"  Skipping step {step_num}: {description}")
            continue
        run_step(step_num, script_name, description, expected)

    total_elapsed = time.time() - total_start
    print("=" * 60)
    print(f"ALL DONE in {total_elapsed:.0f}s ({total_elapsed/60:.1f} min)")
    print("=" * 60)


if __name__ == "__main__":
    main()
