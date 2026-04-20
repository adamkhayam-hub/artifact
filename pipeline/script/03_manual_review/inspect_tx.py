"""
Inspect a single transaction from the Argos dataset.

Usage: python3 06_inspect_tx.py <tx_hash>

Outputs a human-readable summary of:
  - Verdict and reasons
  - Each cycle with full transfer details (from, to, token, amount)
  - Leftover transfers
  - Leftover cycles (lending)
  - Transaction costs
  - Final balance

Well-known addresses are labeled for readability.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import json
import sys

from config import (
    EIGENPHI_FILTERED,
    DATA_DIR, KNOWN_ADDRESSES, TAG_DATA_COL,
    normalize_verdict, normalize_reasons, normalize_hash,
)


def label_address(addr):
    """Return a human-readable label for an address."""
    addr = addr.lower()
    if addr in KNOWN_ADDRESSES:
        return f"{KNOWN_ADDRESSES[addr]} ({addr[:8]}...)"
    return addr[:12] + "..."


def label_token(asset_obj):
    """Extract and label a token address from the JSON asset object."""
    if asset_obj.get("type") == "address":
        addr = asset_obj["value"]["value"].lower()
        if addr in KNOWN_ADDRESSES:
            return KNOWN_ADDRESSES[addr]
        return addr[:12] + "..."
    elif asset_obj.get("type") == "native":
        addr = asset_obj["value"].lower()
        if addr in KNOWN_ADDRESSES:
            return KNOWN_ADDRESSES[addr]
        return "ETH"
    return "?"


def extract_address(obj):
    """Extract address string from a JSON address object."""
    if obj.get("type") == "address":
        return obj["value"]["value"].lower()
    elif obj.get("type") == "native":
        return obj["value"].lower()
    return "?"


def format_amount(amount_str, token_name):
    """Format a wei amount to a readable decimal."""
    try:
        val = int(amount_str)
        # Heuristic: 18 decimals for most tokens, 6 for USDC/USDT
        if token_name in ("USDC", "USDT"):
            return f"{val / 1e6:,.2f}"
        elif token_name in ("WBTC",):
            return f"{val / 1e8:,.6f}"
        else:
            return f"{val / 1e18:,.6f}"
    except (ValueError, TypeError):
        return amount_str


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 06_inspect_tx.py <tx_hash>")
        sys.exit(1)

    target = normalize_hash(sys.argv[1])

    # Search in Argos data
    found = False
    with open(DATA_DIR / "system_arbis.csv", "r") as f:
        reader = csv.reader(f)
        next(reader)  # skip header
        for row in reader:
            h = normalize_hash(row[0])
            if h == target:
                found = True
                block = row[1]
                data = json.loads(row[TAG_DATA_COL])
                break

    if not found:
        print(f"Transaction {target} not found in Argos dataset.")
        # Check Eigenphi
        with open(EIGENPHI_FILTERED, "r") as f:
            reader = csv.reader(f)
            for erow in reader:
                if normalize_hash(erow[1]) == target:
                    print(f"Found in Eigenphi dataset (block {erow[0]}), but NOT in Argos.")
                    return
        print("Not found in Eigenphi either.")
        return

    resume = data["resume"]
    verdict = normalize_verdict(resume["arbitrage"])
    reasons = normalize_reasons(resume["reason"])
    inner = resume["resume"]

    print("=" * 70)
    print(f"TRANSACTION: {target}")
    print(f"BLOCK: {block}")
    print("=" * 70)
    print(f"Verdict:  {verdict}")
    print(f"Reasons:  {', '.join(str(r) for r in reasons)}")
    print()

    # Final balance
    final_balance = resume.get("finalBalance", [])
    if final_balance:
        print("FINAL BALANCE (after costs):")
        for fb in final_balance:
            token = label_token(fb["asset"])
            amt = format_amount(fb["amount"]["value"], token)
            print(f"  {token}: {amt}")
        print()

    # Delta balance (before costs)
    delta = inner.get("deltaBalance", [])
    if delta:
        print("GROSS BALANCE (before costs):")
        for d in delta:
            token = label_token(d["asset"])
            amt = format_amount(d["amount"]["value"], token)
            print(f"  {token}: {amt}")
        print()

    # Cycles
    cycles = inner.get("transfersInCycles", [])
    print(f"CYCLES: {len(cycles)}")
    for i, cycle in enumerate(cycles):
        print(f"\n  Cycle {i + 1} ({len(cycle)} transfers):")
        # Collect unique addresses to identify the initiator
        addresses_involved = set()
        for t in cycle:
            fr = extract_address(t["from"])
            to = extract_address(t["to"])
            token = label_token(t["asset"])
            amt = format_amount(t["amount"]["value"], token)
            print(f"    [{t['index']}] {label_address(fr)} -> {label_address(to)}")
            print(f"        {amt} {token}")
            addresses_involved.add(fr)
            addresses_involved.add(to)

    # Leftover cycles (lending)
    leftover_cycles = inner.get("transfersInLeftoversCycles", [])
    if leftover_cycles:
        print(f"\nLEFTOVER CYCLES (lending): {len(leftover_cycles)}")
        for i, lc in enumerate(leftover_cycles):
            print(f"\n  Leftover cycle {i + 1} ({len(lc)} transfers):")
            for t in lc:
                fr = extract_address(t["from"])
                to = extract_address(t["to"])
                token = label_token(t["asset"])
                amt = format_amount(t["amount"]["value"], token)
                print(f"    {label_address(fr)} -> {label_address(to)}")
                print(f"        {amt} {token}")

    # Leftovers
    leftovers = inner.get("leftovers", [])
    if leftovers:
        print(f"\nLEFTOVERS (unexplained): {len(leftovers)}")
        for t in leftovers:
            fr = extract_address(t["from"])
            to = extract_address(t["to"])
            token = label_token(t["asset"])
            amt = format_amount(t["amount"]["value"], token)
            print(f"  {label_address(fr)} -> {label_address(to)}")
            print(f"      {amt} {token}")

    # Transaction costs
    costs = inner.get("txCosts", [])
    if costs:
        print(f"\nTRANSACTION COSTS:")
        for t in costs:
            fr = extract_address(t["from"])
            to = extract_address(t["to"])
            token = label_token(t["asset"])
            amt = format_amount(t["amount"]["value"], token)
            print(f"  {label_address(fr)} -> {label_address(to)}")
            print(f"      {amt} {token}")

    # Check if in Eigenphi
    in_eigenphi = False
    with open(EIGENPHI_FILTERED, "r") as f:
        reader = csv.reader(f)
        for erow in reader:
            if normalize_hash(erow[1]) == target:
                in_eigenphi = True
                break

    print(f"\nEIGENPHI STATUS:")
    print(f"  In Eigenphi: {'YES' if in_eigenphi else 'NO'}")


if __name__ == "__main__":
    main()
