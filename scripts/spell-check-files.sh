#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)

# Verify scripts exist
if [[ ! -f "$SCRIPT_DIR/extract-comments.py" ]]; then
  echo "Error: scripts/extract-comments.py not found." >&2
  exit 4
fi
if [[ ! -f "$SCRIPT_DIR/spell-check-llm.sh" ]]; then
  echo "Error: scripts/spell-check-llm.sh not found." >&2
  exit 4
fi

FILES="$@"

status=0
for file in $FILES; do
  if [[ ! -e "$file" ]]; then
    echo "Skipping missing file: $file" >&2
    status=2
    continue
  elif [[ ! -f "$file" ]]; then
    echo "Not a file: $file" >&2
    status=3
    continue
  fi
  case "$file" in
    *.v)
      echo "Checking Rocq file: $file"
      if ! "$SCRIPT_DIR/extract-comments.py" --keep-inline --single-line --merge-dots "$file" | "$SCRIPT_DIR/spell-check-llm.sh"; then
        echo "Command failed for: $file" >&2
        status=1
      fi
      ;;
    *.md|*.txt)
      echo "Checking text file: $file"
      if ! "$SCRIPT_DIR/spell-check-llm.sh" < "$file"; then
        echo "Command failed for: $file" >&2
        status=1
      fi
      ;;
    *)
      echo "Skipping file of unknown type: $file" >&2
      status=7
      ;;
  esac
done

exit $status
