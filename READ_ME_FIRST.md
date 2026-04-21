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
  data.tar.gz.part-aa .. part-ai   99614720 each
  data.tar.gz.part-aj              43883946

detect-api_parts_arm64/
  detect-api.tar.gz.part-aa .. part-al   99614720 each
  detect-api.tar.gz.part-am                3701096

detect-api_parts_amd64/
  detect-api.tar.gz.part-aa .. part-al   99614720 each
  detect-api.tar.gz.part-am                 665429
```

Quick check:

```bash
find blockdb_parts pipeline/data_parts detect-api_parts_arm64 \
     detect-api_parts_amd64 -name '*.part-*' -printf '%s %p\n' | sort
```

If any non-final part differs from 99,614,720 bytes, it is
corrupted.

## How to fix

Re-download the corrupted file **individually** from the
anonymous.4open.science web UI: navigate into the containing
folder and click the file name. Single-file downloads are
not affected by the ZIP bug. Overwrite the bad copy with
the freshly downloaded file and re-run `./install.sh`.

The rest of this artifact is documented in
[`README.md`](README.md).
