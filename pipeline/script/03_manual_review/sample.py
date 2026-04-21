"""
Sample transactions for manual validation.

Categories:
  1. Both + confirmed (100): TP sanity check
  2. Ours-only + confirmed (100): exclusive detections
  3. Eigenphi-only (200): investigate what Eigenphi flags
     that we don't — are these real arbitrages or FPs?
  5. Ours-only + warnings (100): real structures or noise?

Reads from: data/*.csv (ground truth, never modified)
Writes to:  samples/05_manual_sample_cat{1,2,3,5}.csv
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import json
import random

from config import (
    EIGENPHI_FILTERED,
    DATA_DIR, SAMPLES_DIR, SAMPLE_SIZES, SEED, TAG_DATA_COL,
    normalize_verdict, normalize_reasons, normalize_hash, classify_by_reasons,
)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
ARTIFACT_DIR = EVAL_DIR.parent
BLOCKDB_DIR = ARTIFACT_DIR / "blockdb"


def get_available_blocks():
    """Return set of block numbers available in blockdb/.
    If blockdb/ doesn't exist, return None (no filtering)."""
    if not BLOCKDB_DIR.exists():
        return None
    blocks = set()
    for subdir in BLOCKDB_DIR.iterdir():
        if subdir.is_dir():
            for block_dir in subdir.iterdir():
                if block_dir.is_dir():
                    try:
                        blocks.add(int(block_dir.name))
                    except ValueError:
                        pass
    if not blocks:
        return None
    return blocks


def extract_address(obj):
    """Extract an address string from either encoding format.
    String format: {"type": "address", "value": {"value": "0x..."}}
    Integer format: {"value": {"address": {"value": {"address": "0x..."}}}}
    """
    if isinstance(obj, str):
        return obj
    if isinstance(obj, dict):
        # String format
        if obj.get("type") == "address":
            return obj["value"]["value"]
        if obj.get("type") == "native":
            return obj["value"]
        # Integer format
        if "value" in obj:
            inner = obj["value"]
            if isinstance(inner, dict) and "address" in inner:
                return inner["address"]["value"].get("address", inner["address"].get("value", ""))
            if isinstance(inner, str):
                return inner
    return ""


def get_transfers_from_cycle(cycle):
    """Extract transfer list from either encoding format.
    String format: cycle is a list of transfer dicts
    Integer format: cycle is a dict with {"items": [...]}
    """
    if isinstance(cycle, list):
        return cycle
    if isinstance(cycle, dict) and "items" in cycle:
        return cycle["items"]
    return []


def extract_summary(json_str):
    """Extract a compact summary from the Ours JSON result.
    Handles both string-encoded and integer-encoded formats.
    """
    try:
        data = json.loads(json_str)
        resume = data["resume"]
        verdict = normalize_verdict(resume["arbitrage"])
        reasons = normalize_reasons(resume["reason"])
        inner = resume["resume"]

        raw_cycles = inner.get("transfersInCycles", [])
        n_cycles = len(raw_cycles)
        n_leftovers = len(inner.get("leftovers", []))
        n_leftover_cycles = len(inner.get("transfersInLeftoversCycles", []))

        # Tokens involved in cycles
        tokens = set()
        for raw_cycle in raw_cycles:
            for transfer in get_transfers_from_cycle(raw_cycle):
                asset = transfer.get("asset", {})
                addr = extract_address(asset)
                if addr:
                    tokens.add(addr)

        return {
            "verdict": verdict,
            "reasons": "|".join(reasons),
            "n_cycles": n_cycles,
            "n_leftovers": n_leftovers,
            "n_leftover_cycles": n_leftover_cycles,
            "n_tokens": len(tokens),
            "tokens": "|".join(sorted(tokens)[:5]),
        }
    except Exception as e:
        return {"verdict": "error", "reasons": str(e),
                "n_cycles": 0, "n_leftovers": 0,
                "n_leftover_cycles": 0, "n_tokens": 0, "tokens": ""}


def main():
    random.seed(SEED)

    # --- Compute overlap max ---
    system_max = 0
    with open(DATA_DIR / "system_arbis.csv", "r") as f:
        reader = csv.reader(f)
        next(reader)
        for row in reader:
            b = int(row[1])
            if b > system_max:
                system_max = b

    eig_max = 0
    with open(EIGENPHI_FILTERED, "r") as f:
        reader = csv.reader(f)
        for row in reader:
            b = int(row[0])
            if b > eig_max:
                eig_max = b

    overlap_max = min(system_max, eig_max)

    # --- Load Eigenphi hashes ---
    eig_hashes = set()
    eig_hash_block = {}
    with open(EIGENPHI_FILTERED, "r") as f:
        reader = csv.reader(f)
        for row in reader:
            block = int(row[0])
            if block <= overlap_max:
                h = normalize_hash(row[1])
                eig_hashes.add(h)
                eig_hash_block[h] = block

    # --- Load Ours and classify ---
    # Store: hash -> (block, category, json_str)
    system_all = {}
    with open(DATA_DIR / "system_arbis.csv", "r") as f:
        reader = csv.reader(f)
        next(reader)
        for row in reader:
            h = normalize_hash(row[0])
            block = int(row[1])
            if block > overlap_max:
                continue
            try:
                data = json.loads(row[TAG_DATA_COL])
                verdict = normalize_verdict(data["resume"]["arbitrage"])
                reasons = normalize_reasons(data["resume"]["reason"])
                category = classify_by_reasons(verdict, reasons)
                system_all[h] = (block, category, row[TAG_DATA_COL])
            except Exception:
                pass

    system_hashes = set(system_all.keys())

    # --- Build category pools ---
    # Cat 1: Both + confirmed
    cat1 = [h for h in (system_hashes & eig_hashes)
            if system_all[h][1] == "confirmed_arbitrage"]
    # Cat 2: Ours-only + confirmed
    cat2 = [h for h in (system_hashes - eig_hashes)
            if system_all[h][1] == "confirmed_arbitrage"]
    # Cat 3: Ours-only + NOT confirmed (warnings)
    cat3 = [h for h in (system_hashes - eig_hashes)
            if system_all[h][1] != "confirmed_arbitrage"]
    # Cat 4: Eigenphi-only (not in Ours at all)
    cat4 = list(eig_hashes - system_hashes)

    pools = {1: cat1, 2: cat2, 3: cat3, 4: cat4}

    # Filter to available blocks if running offline
    available_blocks = get_available_blocks()
    if available_blocks is not None:
        print(f"Offline mode: {len(available_blocks)} blocks in blockdb/")
        for cat_num in pools:
            if cat_num == 4:
                pools[cat_num] = [h for h in pools[cat_num]
                                  if eig_hash_block.get(h, -1) in available_blocks]
            else:
                pools[cat_num] = [h for h in pools[cat_num]
                                  if system_all.get(h, (None,))[0] in available_blocks]
    else:
        print("RPC mode: sampling from full range")

    for cat_num, pool in sorted(pools.items()):
        print(f"Cat {cat_num} pool: {len(pool):,}")

    # --- Sample ---
    def validated_sample(pool, size, needs_system=True):
        """Sample from pool, skipping hashes without fully parseable data."""
        random.shuffle(pool)
        result = []
        for h in pool:
            if len(result) >= size:
                break
            if needs_system:
                if h not in system_all:
                    continue
                _, _, json_str = system_all[h]
                summary = extract_summary(json_str)
                if summary["verdict"] == "error":
                    continue
            result.append(h)
        return result

    samples = {
        1: validated_sample(list(cat1), SAMPLE_SIZES[1], needs_system=True),
        2: validated_sample(list(cat2), SAMPLE_SIZES[2], needs_system=True),
        3: validated_sample(list(cat3), SAMPLE_SIZES[3], needs_system=True),
        4: random.sample(cat4, min(SAMPLE_SIZES[4], len(cat4))),
    }

    # --- Write Cat 1, 2, 3 (have Ours data) ---
    cat_names = {1: "both_confirmed", 2: "system_only_confirmed", 3: "system_only_warnings"}
    for cat_num in [1, 2, 3]:
        sample = samples[cat_num]
        path = SAMPLES_DIR / f"05_manual_sample_cat{cat_num}_{cat_names[cat_num]}.csv"
        with open(path, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow([
                "tx_hash", "block", "verdict", "reasons",
                "n_cycles", "n_leftovers", "n_leftover_cycles",
                "n_tokens", "tokens_sample", "manual_verdict"
            ])
            for h in sample:
                block, category, json_str = system_all[h]
                summary = extract_summary(json_str)
                writer.writerow([
                    h, block, summary["verdict"], summary["reasons"],
                    summary["n_cycles"], summary["n_leftovers"],
                    summary["n_leftover_cycles"], summary["n_tokens"],
                    summary["tokens"], ""
                ])
        print(f"Wrote {len(sample)} txs to {path}")

    # --- Write Cat 4 (Eigenphi-only, no Ours data) ---
    path = SAMPLES_DIR / "05_manual_sample_cat4_eigenphi_only.csv"
    with open(path, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["tx_hash", "block", "manual_verdict", "manual_notes"])
        for h in samples[4]:
            block = eig_hash_block.get(h, "")
            writer.writerow([h, block, "", ""])
    print(f"Wrote {len(samples[4])} txs to {path}")

    # Save summary
    summary_lines = [
        f"Manual validation samples generated",
        f"Seed: {SEED}",
        f"",
    ]
    for cat_num in sorted(samples):
        summary_lines.append(
            f"Cat {cat_num} pool: {len(pools[cat_num]):,}, "
            f"sampled: {len(samples[cat_num])}"
        )
    output_path = SAMPLES_DIR / "05_manual_sample_summary.txt"
    with open(output_path, "w") as f:
        f.write("\n".join(summary_lines) + "\n")
    print(f"Summary saved to {output_path}")


if __name__ == "__main__":
    main()
