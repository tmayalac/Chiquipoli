#!/usr/bin/env bash
# Archives logs/final_run.txt (the mutable "latest run" pointer) into an
# immutable, dated copy under logs/archive/, per logs/README.md: "Never overwrite a successful
# log; use dated names."
#
# Usage: tools/archive_log.sh [path-to-log]   (default: logs/final_run.txt)
#
# The archived filename is derived from the log's own "UTC timestamp" line
# (not from `date now`), so the filename always matches the content -- the
# archive can be created any time after the run, not only immediately after.
set -euo pipefail

LOG="${1:-logs/final_run.txt}"

if [ ! -f "$LOG" ]; then
    echo "error: $LOG not found" >&2
    exit 1
fi

# Extract the ISO-8601 value directly (portable across BSD and GNU grep/sed;
# avoids prefix-stripping, which broke under BSD sed's lack of \s support).
TS_ISO="$(grep -oE '[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z' "$LOG" | head -n1 || true)"
if [ -z "$TS_ISO" ]; then
    echo "error: no UTC timestamp found in $LOG (is this a certify_a16.jl log?)" >&2
    exit 1
fi

# "2026-07-23T19:15:09Z" -> "20260723T191509Z"
TS_COMPACT="$(echo "$TS_ISO" | tr -d ':-')"

# Archived copies live in logs/archive/, beside the latest run but apart from it.
DEST_DIR="$(dirname "$LOG")/archive"
mkdir -p "$DEST_DIR"
DEST="$DEST_DIR/${TS_COMPACT}_a16_certificate.txt"

if [ -e "$DEST" ]; then
    echo "error: $DEST already exists -- refusing to overwrite an archived log" >&2
    exit 1
fi

cp "$LOG" "$DEST"
chmod 444 "$DEST"
echo "archived $LOG -> $DEST (timestamp from log content: $TS_ISO, now read-only)"
