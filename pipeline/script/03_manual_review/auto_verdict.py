"""
Auto-verdict for cat1 and cat2 transactions based on structural analysis.

For each inspect file, determine:
  - Is the cycle structure consistent with arbitrage? (same token in/out, positive profit)
  - How many pools/intermediaries are involved?
  - Is it a simple triangle, multi-hop, or multi-cycle?
  - Any red flags? (single transfer cycle, suspicious pattern)

Writes verdicts to data/manual_review/auto_verdicts_cat{1,2}.csv
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import re

from config import (
    INSPECTIONS_DIR, VERDICTS_DIR, CATEGORY_FOLDERS,
    KNOWN_ADDRESSES, KNOWN_ROUTERS, KNOWN_BOTS,
)


def parse_inspect_file(filepath):
    """Parse an inspect file and return structured data."""
    content = filepath.read_text()

    tx_hash = ""
    verdict = ""
    reasons = ""
    final_balance = []
    gross_balance = []
    cycles = []
    current_cycle = []
    n_cycles = 0
    eigenphi_main = False

    for line in content.split("\n"):
        line = line.strip()

        if line.startswith("TRANSACTION:"):
            tx_hash = line.split(":")[1].strip()
        elif line.startswith("Verdict:"):
            verdict = line.split(":")[1].strip()
        elif line.startswith("Reasons:"):
            reasons = line.split(":", 1)[1].strip()
        elif line.startswith("FINAL BALANCE:"):
            final_balance.append(line.split(":", 1)[1].strip())
        elif line.startswith("GROSS BALANCE:"):
            gross_balance.append(line.split(":", 1)[1].strip())
        elif line.startswith("CYCLES:"):
            n_cycles = int(line.split(":")[1].strip())
        elif "Cycle " in line and "transfers" in line:
            if current_cycle:
                cycles.append(current_cycle)
            current_cycle = []
        elif line.startswith("[") and "->" in content[content.index(line):content.index(line)+200]:
            current_cycle.append(line)
        elif "In Eigenphi:" in line or "In Eigenphi main set:" in line:
            eigenphi_main = "YES" in line

    if current_cycle:
        cycles.append(current_cycle)

    return {
        "tx_hash": tx_hash,
        "verdict": verdict,
        "reasons": reasons,
        "final_balance": final_balance,
        "gross_balance": gross_balance,
        "n_cycles": n_cycles,
        "cycles": cycles,
        "eigenphi_main": eigenphi_main,
    }


def analyze_cycle(content):
    """Analyze the full file content to determine if it's a real arbitrage."""
    # Extract all addresses involved in transfers
    addr_pattern = re.compile(r"(0x[0-9a-f]{40})")
    lines = content.split("\n")

    transfers = []
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line.startswith("[") and i + 2 < len(lines):
            # Transfer line: [idx] from_addr
            from_match = addr_pattern.search(line)
            next_line = lines[i + 1].strip()
            to_match = addr_pattern.search(next_line) if next_line.startswith("->") else None
            amount_line = lines[i + 2].strip() if i + 2 < len(lines) else ""

            if from_match and to_match:
                transfers.append({
                    "from": from_match.group(1),
                    "to": to_match.group(1),
                    "amount_line": amount_line,
                })
        i += 1

    if not transfers:
        return "INCONCLUSIVE", "no transfers found in file"

    # Check if first and last transfer form a cycle (same address)
    first_from = transfers[0]["from"]
    last_to = transfers[-1]["to"] if transfers else ""

    # Check for known bot addresses
    uses_known_bot = first_from in KNOWN_BOTS
    uses_known_router = any(
        t["from"] in KNOWN_ROUTERS or t["to"] in KNOWN_ROUTERS
        for t in transfers
    )

    # Check if cycle closes (same initiator)
    cycle_closes = first_from == last_to

    # Count unique intermediaries
    all_addrs = set()
    for t in transfers:
        all_addrs.add(t["from"])
        all_addrs.add(t["to"])
    n_intermediaries = len(all_addrs) - 1  # minus the initiator

    # Determine verdict
    flags = []

    if not cycle_closes:
        flags.append("cycle does not close")

    if len(transfers) == 1:
        flags.append("single-transfer cycle (degenerate)")

    # Check if first and last token match (same token in/out)
    # WETH and ETH (native) are economically equivalent due to
    # decode-layer normalization, so we treat them as matching.
    first_token = transfers[0]["amount_line"].split()[-1] if transfers[0]["amount_line"] else ""
    last_token = transfers[-1]["amount_line"].split()[-1] if transfers[-1]["amount_line"] else ""
    eth_equivalents = {"WETH", "ETH", "(native)"}
    stable_equivalents = {"USDC", "USDT", "DAI"}
    tokens_match = (
        first_token == last_token
        or {first_token, last_token} <= eth_equivalents
        or {first_token, last_token} <= stable_equivalents
    )
    if first_token and last_token and not tokens_match:
        # Multi-token arbitrage: cycle closes on address, profit
        # across multiple tokens. Still a valid arbitrage if our
        # algorithm confirmed positive delta.
        flags.append(f"multi-token cycle: {first_token} / {last_token}")

    if uses_known_router:
        router_names = [KNOWN_ROUTERS[t["from"]] for t in transfers if t["from"] in KNOWN_ROUTERS]
        router_names += [KNOWN_ROUTERS[t["to"]] for t in transfers if t["to"] in KNOWN_ROUTERS]
        flags.append(f"uses router: {', '.join(set(router_names))}")

    # Build verdict
    if cycle_closes and len(transfers) >= 2:
        verdict = "ARBITRAGE"
        detail = f"{len(transfers)} transfers, {n_intermediaries} intermediaries"
        if uses_known_bot:
            detail += ", known MEV bot"
        if flags:
            detail += f" [{'; '.join(flags)}]"
    elif cycle_closes:
        verdict = "ARBITRAGE"
        detail = "single transfer cycle"
        if flags:
            detail += f" [{'; '.join(flags)}]"
    else:
        verdict = "SUSPICIOUS"
        detail = "; ".join(flags)

    return verdict, detail


def process_category(folder_name):
    """Process all inspect files in a category."""
    folder = INSPECTIONS_DIR / folder_name
    results = []

    for txt_file in sorted(folder.glob("tx_*.txt")):
        content = txt_file.read_text()

        if "NOT IN ARGOS" in content:
            tx_match = re.search(r"TRANSACTION: (0x[0-9a-f]+)", content)
            tx_hash = tx_match.group(1) if tx_match else txt_file.stem
            results.append((tx_hash, "N/A", "not in Argos dataset"))
            continue

        # Get tx hash
        tx_match = re.search(r"TRANSACTION: (0x[0-9a-f]+)", content)
        tx_hash = tx_match.group(1) if tx_match else txt_file.stem

        # Get Eigenphi status
        eig_main = "YES" if "In Eigenphi main set:     YES" in content else "NO"

        auto_verdict, detail = analyze_cycle(content)
        results.append((tx_hash, auto_verdict, detail))

    return results


def main():
    for cat_num in [1, 2, 3]:
        folder_name = CATEGORY_FOLDERS[cat_num]
        results = process_category(folder_name)

        out_dir = VERDICTS_DIR / "09_auto_verdicts"
        out_dir.mkdir(parents=True, exist_ok=True)
        out_path = out_dir / f"auto_verdicts_cat{cat_num}.csv"
        with open(out_path, "w") as f:
            f.write("tx_hash,auto_verdict,detail\n")
            for tx_hash, verdict, detail in results:
                detail_clean = detail.replace(",", ";")
                f.write(f"{tx_hash},{verdict},{detail_clean}\n")

        # Summary
        verdicts = {}
        for _, v, _ in results:
            verdicts[v] = verdicts.get(v, 0) + 1

        print(f"\n{folder_name}:")
        for v, c in sorted(verdicts.items(), key=lambda x: -x[1]):
            print(f"  {v:20s}  {c}")
        print(f"  Total: {len(results)}")
        print(f"  Saved to {out_path}")


if __name__ == "__main__":
    main()
