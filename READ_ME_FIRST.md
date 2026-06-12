# READ ME FIRST — Known ZIP download issue

If you obtained this artifact by clicking **Download
Repository (ZIP)** on anonymous.4open.science, **verify the
part file sizes before running `install.sh`**.

The anonymous.4open.science ZIP builder has a reproducible
bug that corrupts a single file in our bundle: the file is
returned with extra trailing bytes and causes `tar` to exit
with an error during `./install.sh`.

## How to check

Every non-final split part must be exactly **99,614,720
bytes** (95 MB). Expected sizes:

```
blockdb_parts/
  blockdb.tar.gz.part-aa       99614720
  blockdb.tar.gz.part-ab       99614720
  blockdb.tar.gz.part-ac       99614720
  blockdb.tar.gz.part-ad       81557049

pipeline/data_parts/
  data.tar.gz.part-aa .. part-ae   99614720 each
  data.tar.gz.part-af              46059520

detect-api_parts_arm64/
  detect-api.tar.gz.part-aa .. part-ax   99614720 each
  detect-api.tar.gz.part-ay               17990566

detect-api_parts_amd64/
  detect-api.tar.gz.part-aa .. part-al   99614720 each
  detect-api.tar.gz.part-am                7571358
```

Quick check (portable, macOS and Linux):

```bash
find blockdb_parts pipeline/data_parts detect-api_parts_arm64 \
     detect-api_parts_amd64 -name '*.part-*' -exec wc -c {} \; | sort
```

Flag any corrupted parts in one go:

```bash
find blockdb_parts pipeline/data_parts detect-api_parts_arm64 \
     detect-api_parts_amd64 -name '*.part-*' -exec wc -c {} \; |
  awk '$1!=99614720 && $1!=81557049 && $1!=46059520 \
       && $1!=17990566 && $1!=7571358 {print "BAD:",$0}'
```

If the second command prints nothing, every part has an expected
size. If it prints anything, the listed file is corrupted.

## How to fix

Re-download the corrupted file **individually** from the
anonymous.4open.science web UI: navigate into the containing
folder and click the file name. Single-file downloads are
not affected by the ZIP bug. Overwrite the bad copy with
the freshly downloaded file and re-run `./install.sh`.

## Script execute permissions

ZIP extraction does not preserve Unix execute bits.  Before
running any script, restore permissions:

```bash
chmod +x install.sh cleanup.sh \
         pipeline/run.sh pipeline/generate_csv.sh
```

The rest of this artifact is documented in
[`README.md`](README.md).
