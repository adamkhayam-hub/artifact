"""
Inspect all sampled transactions and save results to subfolders.

Loads the Ours CSV once into memory, then iterates over all samples.
Prints full addresses (not truncated) for lookup.

Reads from: data/05_manual_sample_cat*.csv, data/system_arbis.csv
Writes to:  data/manual_review/cat{1,2,3,4}_*/tx_<hash>.txt
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import json
from collections import Counter

from config import (
    EIGENPHI_FILTERED,
    DATA_DIR, SAMPLES_DIR, INSPECTIONS_DIR, CATEGORY_FOLDERS,
    KNOWN_ADDRESSES, TAG_DATA_COL,
    normalize_verdict, normalize_reasons, normalize_hash,
)


def label_address(addr):
    addr = addr.lower()
    if addr in KNOWN_ADDRESSES:
        return f"{KNOWN_ADDRESSES[addr]} ({addr})"
    return addr


def deep_extract_address(obj):
    """Extract address from either string or integer encoding.
    String: {"type": "address", "value": {"value": "0x..."}}
    Integer: {"value": {"address": {"value": {"address": "0x..."}}}}
    """
    if isinstance(obj, str):
        return obj.lower()
    if not isinstance(obj, dict):
        return "?"
    # String format
    if obj.get("type") == "address":
        return obj["value"]["value"].lower()
    if obj.get("type") == "native":
        return obj["value"].lower()
    # Integer format
    if "value" in obj:
        inner = obj["value"]
        if isinstance(inner, dict) and "address" in inner:
            nested = inner["address"]
            if isinstance(nested, dict) and "value" in nested:
                v = nested["value"]
                if isinstance(v, dict) and "address" in v:
                    return v["address"].lower()
                if isinstance(v, str):
                    return v.lower()
        if isinstance(inner, str):
            return inner.lower()
    return "?"


def extract_address(obj):
    return deep_extract_address(obj)


def label_token(asset_obj):
    addr = deep_extract_address(asset_obj)
    if addr != "?" and addr in KNOWN_ADDRESSES:
        return KNOWN_ADDRESSES[addr]
    if addr != "?":
        return addr
    return "?"


def get_transfers(cycle_obj):
    """Get transfer list from either format.
    String: cycle is a list
    Integer: cycle is {"items": [...]}
    """
    if isinstance(cycle_obj, list):
        return cycle_obj
    if isinstance(cycle_obj, dict) and "items" in cycle_obj:
        return cycle_obj["items"]
    return []


def get_amount(transfer):
    """Extract amount string from either format.
    String: {"amount": {"type": "value", "value": "123"}}
    Integer: {"amount": {"value": {"simpleValue": "0x..."}}}
    """
    amt = transfer.get("amount", {})
    if isinstance(amt, dict):
        if amt.get("type") == "value":
            return amt.get("value", "0")
        if "value" in amt:
            inner = amt["value"]
            if isinstance(inner, dict) and "simpleValue" in inner:
                try:
                    return str(int(inner["simpleValue"], 16))
                except (ValueError, TypeError):
                    return inner["simpleValue"]
            if isinstance(inner, str):
                return inner
    return "0"


def format_amount(amount_str, token_name):
    """Format a raw integer amount into human-readable form.
    Uses enough decimals to never lose precision (18 for ETH-scale)."""
    try:
        val = int(amount_str)
        if token_name in ("USDC", "USDT"):
            return f"{val / 1e6:.6f}"
        elif token_name in ("WBTC",):
            return f"{val / 1e8:.8f}"
        else:
            return f"{val / 1e18:.18f}".rstrip("0").rstrip(".")
    except (ValueError, TypeError):
        return amount_str


def inspect_tx(data, block, target, eig_hashes):
    """Return a string with the full inspection of one transaction."""
    lines = []
    p = lines.append

    resume = data["resume"]
    verdict = normalize_verdict(resume["arbitrage"])
    reasons = normalize_reasons(resume["reason"])
    inner = resume["resume"]

    p("=" * 70)
    p(f"TRANSACTION: {target}")
    p(f"BLOCK: {block}")
    p("=" * 70)
    p(f"Verdict:  {verdict}")
    p(f"Reasons:  {', '.join(str(r) for r in reasons)}")
    p("")

    # Final balance
    for fb in resume.get("finalBalance", []):
        token = label_token(fb.get("asset", {}))
        amt = format_amount(get_amount(fb), token)
        p(f"FINAL BALANCE: {amt} {token}")
    p("")

    # Gross balance
    for d in inner.get("deltaBalance", []):
        token = label_token(d.get("asset", {}))
        amt = format_amount(get_amount(d), token)
        p(f"GROSS BALANCE: {amt} {token}")
    p("")

    # Cycles
    raw_cycles = inner.get("transfersInCycles", [])
    p(f"CYCLES: {len(raw_cycles)}")
    for i, raw_cycle in enumerate(raw_cycles):
        transfers = get_transfers(raw_cycle)
        p(f"\n  Cycle {i + 1} ({len(transfers)} transfers):")
        for t in transfers:
            fr = extract_address(t.get("from", {}))
            to = extract_address(t.get("to", {}))
            token = label_token(t.get("asset", {}))
            amt = format_amount(get_amount(t), token)
            idx = t.get("index", "?")
            p(f"    [{idx}] {label_address(fr)}")
            p(f"     -> {label_address(to)}")
            p(f"        {amt} {token}")

    # Leftover cycles
    raw_leftover_cycles = inner.get("transfersInLeftoversCycles", [])
    if raw_leftover_cycles:
        p(f"\nLEFTOVER CYCLES (lending): {len(raw_leftover_cycles)}")
        for i, raw_lc in enumerate(raw_leftover_cycles):
            lc_transfers = get_transfers(raw_lc)
            p(f"\n  Leftover cycle {i + 1} ({len(lc_transfers)} transfers):")
            for t in lc_transfers:
                fr = extract_address(t.get("from", {}))
                to = extract_address(t.get("to", {}))
                token = label_token(t.get("asset", {}))
                amt = format_amount(get_amount(t), token)
                p(f"    {label_address(fr)}")
                p(f"     -> {label_address(to)}")
                p(f"        {amt} {token}")

    # Leftovers
    leftovers = inner.get("leftovers", [])
    if leftovers:
        p(f"\nLEFTOVERS (unexplained): {len(leftovers)}")
        for t in get_transfers(leftovers) if isinstance(leftovers, dict) else leftovers:
            fr = extract_address(t.get("from", {}))
            to = extract_address(t.get("to", {}))
            token = label_token(t.get("asset", {}))
            amt = format_amount(get_amount(t), token)
            p(f"  {label_address(fr)}")
            p(f"   -> {label_address(to)}")
            p(f"      {amt} {token}")

    # Costs
    costs = inner.get("txCosts", [])
    if costs:
        p(f"\nTRANSACTION COSTS:")
        for t in get_transfers(costs) if isinstance(costs, dict) else costs:
            fr = extract_address(t.get("from", {}))
            to = extract_address(t.get("to", {}))
            token = label_token(t.get("asset", {}))
            amt = format_amount(get_amount(t), token)
            p(f"  {label_address(fr)}")
            p(f"   -> {label_address(to)}")
            p(f"      {amt} {token}")

    # Eigenphi status
    p(f"\nEIGENPHI STATUS:")
    p(f"  In Eigenphi main set:     {'YES' if target in eig_hashes else 'NO'}")

    return "\n".join(lines)


def main():
    # Collect all target hashes first
    target_hashes = set()
    categories = [
        ("05_manual_sample_cat1_both_confirmed.csv", CATEGORY_FOLDERS[1]),
        ("05_manual_sample_cat2_system_only_confirmed.csv", CATEGORY_FOLDERS[2]),
        ("05_manual_sample_cat3_system_only_warnings.csv", CATEGORY_FOLDERS[3]),
        ("05_manual_sample_cat4_eigenphi_only.csv", CATEGORY_FOLDERS[4]),
    ]
    for csv_name, _ in categories:
        with open(SAMPLES_DIR / csv_name, "r") as f:
            reader = csv.reader(f)
            next(reader)
            for row in reader:
                h = normalize_hash(row[0])
                target_hashes.add(h)
    print(f"Target hashes to look up: {len(target_hashes)}")

    print("Scanning Ours dataset for matches...")
    system_data = {}
    with open(DATA_DIR / "system_arbis.csv", "r") as f:
        reader = csv.reader(f)
        next(reader)
        for row in reader:
            h = normalize_hash(row[0])
            if h in target_hashes:
                system_data[h] = (row[1], row[TAG_DATA_COL])
    print(f"  Found {len(system_data):,} matches in Ours")

    print("Loading Eigenphi hashes...")
    eig_hashes = set()
    with open(EIGENPHI_FILTERED, "r") as f:
        reader = csv.reader(f)
        for row in reader:
            eig_hashes.add(normalize_hash(row[1]))
    print(f"  Loaded {len(eig_hashes):,} Eigenphi hashes")

    for csv_name, folder in categories:
        csv_path = SAMPLES_DIR / csv_name
        out_dir = INSPECTIONS_DIR / folder
        out_dir.mkdir(parents=True, exist_ok=True)

        with open(csv_path, "r") as f:
            reader = csv.reader(f)
            header = next(reader)
            rows = list(reader)

        print(f"\n{'=' * 60}")
        print(f"{folder} ({len(rows)} transactions)")
        print(f"{'=' * 60}")

        for i, row in enumerate(rows):
            tx_hash = normalize_hash(row[0])

            out_file = out_dir / f"tx_{tx_hash[:8]}.txt"

            if tx_hash in system_data:
                block, json_str = system_data[tx_hash]
                try:
                    data = json.loads(json_str)
                    output = inspect_tx(data, block, tx_hash, eig_hashes)
                except Exception as e:
                    output = f"ERROR parsing {tx_hash}: {e}"
            else:
                # Eigenphi-only: no Ours data
                block = row[1] if len(row) > 1 else "?"
                output = (
                    f"{'=' * 70}\n"
                    f"TRANSACTION: {tx_hash}\n"
                    f"BLOCK: {block}\n"
                    f"{'=' * 70}\n"
                    f"NOT IN OURS DATASET\n\n"
                    f"EIGENPHI STATUS:\n"
                    f"  In Eigenphi main set:     {'YES' if tx_hash in eig_hashes else 'NO'}\n"
                )

            with open(out_file, "w") as f:
                f.write(output + "\n")

            # One-line summary
            verdict_line = "N/A"
            for line in output.split("\n"):
                if line.startswith("Verdict:"):
                    verdict_line = line.split(":", 1)[1].strip()
                    break
                elif "NOT IN OURS" in line:
                    verdict_line = "not in Ours"
                    break
            print(f"  [{i+1:2d}/{len(rows)}] {tx_hash[:14]}...  {verdict_line}")

    print(f"\nDone. Results in {INSPECTIONS_DIR}/")


if __name__ == "__main__":
    main()
