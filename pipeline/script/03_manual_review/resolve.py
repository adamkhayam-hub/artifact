"""
Resolve unknown addresses from cat1, cat2, and cat5 inspect files.

Strategy:
  1. Collect all unique addresses from inspect files
  2. Check Sourcify V2 for verified contract names
  3. Use public RPC (eth_getCode) to distinguish contracts from EOAs
  4. For unverified contracts, check if they are known Uniswap V2/V3
     pools by querying factory contracts

Reads from: data/manual_review/cat{1,2,5}_*/tx_*.txt
Writes to:  data/manual_review/resolved_addresses.csv
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import json
import re
import time
import urllib.request
import urllib.error

from config import INSPECTIONS_DIR, ADDRESSES_DIR, CATEGORY_FOLDERS, KNOWN_ADDRESSES

BLOCKSCOUT_URL = "https://eth.blockscout.com/api/v2/addresses"
HEADERS = {
    "Accept": "application/json",
    "User-Agent": "Mozilla/5.0 (evaluation-script)",
}

ETH_ADDR_RE = re.compile(r"0x[0-9a-f]{40}")


def blockscout_lookup(addr):
    """Look up an address on Blockscout. Returns (name, is_contract, token_name, token_symbol)."""
    url = f"{BLOCKSCOUT_URL}/{addr}"
    try:
        req = urllib.request.Request(url, headers=HEADERS)
        with urllib.request.urlopen(req, timeout=15) as resp:
            d = json.loads(resp.read())
            name = d.get("name") or ""
            is_contract = d.get("is_contract", False)
            token = d.get("token") or {}
            token_name = token.get("name", "") if token else ""
            token_symbol = token.get("symbol", "") if token else ""
            return name, is_contract, token_name, token_symbol
    except urllib.error.HTTPError as e:
        return f"HTTP {e.code}", False, "", ""
    except Exception as e:
        return f"error: {e}", False, "", ""


def collect_addresses(folders):
    """Collect all unique addresses from inspect files."""
    all_addresses = set()
    for folder in folders:
        folder_path = INSPECTIONS_DIR / folder
        if not folder_path.exists():
            continue
        for txt_file in folder_path.glob("tx_*.txt"):
            content = txt_file.read_text().lower()
            addrs = ETH_ADDR_RE.findall(content)
            all_addresses.update(addrs)
    return all_addresses


def main():
    folders = [
        CATEGORY_FOLDERS[1],
        CATEGORY_FOLDERS[2],
        CATEGORY_FOLDERS[3],
    ]

    print("Collecting addresses from inspect files...")
    all_addresses = collect_addresses(folders)
    unknown = all_addresses - set(KNOWN_ADDRESSES.keys())
    print(f"Total unique addresses: {len(all_addresses)}")
    print(f"Already known: {len(all_addresses) - len(unknown)}")
    print(f"To resolve: {len(unknown)}")

    results = {}

    # Add known addresses first
    for addr in all_addresses & set(KNOWN_ADDRESSES.keys()):
        results[addr] = {
            "name": KNOWN_ADDRESSES[addr],
            "is_contract": True,
            "token_symbol": "",
            "source": "hardcoded",
        }

    # Resolve unknown addresses via Blockscout
    for i, addr in enumerate(sorted(unknown)):
        if (i + 1) % 20 == 0:
            print(f"  Resolving {i + 1}/{len(unknown)}...")

        name, is_contract, token_name, token_symbol = blockscout_lookup(addr)

        label = name or token_name or ""
        if token_symbol and not name:
            label = f"{token_name} ({token_symbol})" if token_name else token_symbol

        if is_contract:
            if label:
                source = "blockscout"
            else:
                label = "unverified contract"
                source = "blockscout"
        else:
            label = label or "EOA"
            source = "blockscout"

        results[addr] = {
            "name": label,
            "is_contract": is_contract,
            "token_symbol": token_symbol,
            "source": source,
        }
        time.sleep(0.15)  # rate limit

    # Save
    out_path = ADDRESSES_DIR / "resolved_addresses.csv"
    with open(out_path, "w") as f:
        f.write("address,name,is_contract,token_symbol,source\n")
        for addr in sorted(results):
            info = results[addr]
            name = info["name"].replace(",", ";")
            sym = info.get("token_symbol", "")
            f.write(f"{addr},{name},{info['is_contract']},{sym},{info['source']}\n")

    print(f"\nSaved {len(results)} addresses to {out_path}")

    # Summary
    contracts = sum(1 for v in results.values() if v["is_contract"])
    eoas = sum(1 for v in results.values() if not v["is_contract"])
    named_contracts = sum(1 for v in results.values()
                          if v["is_contract"] and v["name"] not in ("unverified contract", ""))
    unverified = sum(1 for v in results.values() if v["name"] == "unverified contract")
    tokens = sum(1 for v in results.values() if v.get("token_symbol"))

    print(f"  Contracts: {contracts} (named: {named_contracts}, unverified: {unverified})")
    print(f"  EOAs: {eoas}")
    print(f"  Tokens: {tokens}")

    # Print named contracts (skip tokens, print separately)
    print("\nNamed contracts (non-token):")
    for addr, info in sorted(results.items()):
        if info["is_contract"] and info["name"] not in ("unverified contract", "", "EOA") and not info.get("token_symbol"):
            print(f"  {addr}  {info['name']}")

    print("\nTokens:")
    for addr, info in sorted(results.items()):
        if info.get("token_symbol"):
            print(f"  {addr}  {info['name']}")


if __name__ == "__main__":
    main()
