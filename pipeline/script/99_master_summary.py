"""
99_master_summary.py — Consolidated evaluation report.

Reads all individual summaries and produces one master document
with all numbers needed for the paper.

Reads:  summaries/*.txt
Writes: summaries/99_master_summary.txt
"""

from pathlib import Path

EVAL_DIR = Path(__file__).resolve().parent.parent
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
OUT = SUMMARIES_DIR / "99_master_summary.txt"


def extract(path, *keywords):
    """Extract lines containing any keyword from a summary file."""
    if not path.exists():
        return [f"  (missing: {path.name})"]
    lines = path.read_text().splitlines()
    results = []
    for line in lines:
        for kw in keywords:
            if kw.lower() in line.lower():
                results.append("  " + line.strip())
                break
    return results


def section(title):
    return [
        "",
        "=" * 70,
        title,
        "=" * 70,
    ]


def main():
    out = []
    out.append("MASTER EVALUATION SUMMARY")
    out.append("Generated from individual summaries")
    out.append("")

    # --- Block range and scale ---
    out += section("1. SCALE")
    out += extract(
        SUMMARIES_DIR / "01_statistics/explore.txt",
        "Argos:", "Eigenphi:", "Total Argos",
    )

    # --- Fixpoint coverage ---
    out += section("2. FIXPOINT COVERAGE")
    out += extract(
        SUMMARIES_DIR / "01_statistics/explore.txt",
        "Fixpoint alone", "Promoted", "fixpoint=",
    )

    # --- Verdict distribution ---
    out += section("3. VERDICT DISTRIBUTION")
    out += extract(
        SUMMARIES_DIR / "01_statistics/explore.txt",
        "arbitrage", "warning", "confirmed", "attempted",
        "probable", "uncertain",
    )

    # --- Accuracy (Argos vs Eigenphi) ---
    out += section("4. ACCURACY (Argos vs Eigenphi)")
    out += extract(
        SUMMARIES_DIR / "01_statistics/accuracy.txt",
        "Precision", "Recall", "F1", "TP:", "FP:", "FN:",
        "Eigenphi-only", "Argos-only", "confirmed_arbitrage",
    )

    # --- Three-way comparison ---
    out += section("5. THREE-WAY (Argos vs Eigenphi vs ArbiNet)")
    out += extract(
        SUMMARIES_DIR / "05_arbinet/comparison.txt",
        "Argos detection", "Eigenphi label", "ArbiNet positive",
        "All three", "Argos-only", "ArbiNet miss",
        "Eigenphi-only", "Argos + Eigenphi", "Argos + ArbiNet",
    )

    # --- Topology ---
    out += section("6. TOPOLOGY")
    out += extract(
        SUMMARIES_DIR / "01_statistics/topology.txt",
        "Total cycles", "Cycles", "Lending",
    )

    # --- Performance ---
    out += section("7. PERFORMANCE")
    out += extract(
        SUMMARIES_DIR / "01_statistics/performance.txt",
        "median", "P95", "P99", "max", "decode", "algo",
    )

    # --- Cat4 forensic + to_ gap ---
    out += section("8. CAT4 FORENSIC (Eigenphi-only)")
    out += extract(
        SUMMARIES_DIR / "04_cat4/forensic.txt",
        "now_detected", "eigenphi_fp", "decoder",
        "has_cycles", "Total",
    )
    out += [""]
    out += ["  --- to_ gap analysis ---"]
    out += extract(
        SUMMARIES_DIR / "04_cat4/to_gap.txt",
        "Yellow node", "Cycles but", "No cycles",
        "false positive", "to_ limitation", "inner contract",
    )

    # --- Cross-chain ---
    out += section("9. CROSS-CHAIN")
    out += extract(
        SUMMARIES_DIR / "06_crosschain/comparison.txt",
        "Confirmed", "Warning", "Detection rate", "Code change",
        "Ethereum", "Arbitrum", "BSC",
    )

    # --- Attempted arbitrages ---
    out += section("10. ATTEMPTED ARBITRAGES")
    out += extract(
        SUMMARIES_DIR / "01_statistics/attempted.txt",
        "Confirmed", "Attempted", "Mean", "Median",
    )

    # --- Bot concentration ---
    out += section("11. BOT CONCENTRATION")
    out += extract(
        SUMMARIES_DIR / "01_statistics/bots.txt",
        "Top", "sender", "concentration",
    )

    # --- ArbiNet degradation ---
    out += section("12. ARBINET DEGRADATION")
    out += extract(
        SUMMARIES_DIR / "05_arbinet/degradation.txt",
        "Window", "Argos", "ArbiNet", "Eigenphi", "Total",
    )

    # --- Key numbers for paper ---
    out += section("PAPER NUMBERS (copy-paste)")
    out.append("")

    # Read specific values
    s01 = (SUMMARIES_DIR / "01_statistics/explore.txt").read_text()
    s02 = (SUMMARIES_DIR / "01_statistics/accuracy.txt").read_text()
    s27 = (SUMMARIES_DIR / "04_cat4/to_gap.txt").read_text()

    for line in s01.splitlines():
        if "Total Argos" in line:
            out.append(f"  Total detections: {line.split(':')[1].strip()}")
        if "Fixpoint alone" in line:
            out.append(f"  Fixpoint: {line.strip()}")
        if "Promoted" in line and "%" in line:
            out.append(f"  Promoted: {line.strip()}")

    for line in s02.splitlines():
        if "confirmed_arbitrage" in line and "Total" not in line:
            out.append(f"  {line.strip()}")

    for line in s27.splitlines():
        if "Yellow node" in line:
            out.append(f"  Cat4 to_ gap: {line.strip()}")
        if "No cycles" in line:
            out.append(f"  Cat4 Eigenphi FP: {line.strip()}")

    out.append("")

    text = "\n".join(out) + "\n"
    OUT.write_text(text)
    print(text)
    print(f"Saved to {OUT}")


if __name__ == "__main__":
    main()
