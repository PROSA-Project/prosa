#!/usr/bin/env bash
# check_rocq_changed.sh
# Find all *.v and *.md files added or modified relative to a base branch and run
#   scripts/extract-comments.py --keep-inline --merge-dots <file.v> | scripts/spell-check-llm.sh (for .v)
#   cat <file.md> | scripts/spell-check-llm.sh (for .md)
#
# Usage:
#   ./spell-check-changed.sh [--base <branch>]
#
# Notes:
# - If --base is omitted, defaults to "main" if it exists, otherwise "master" if it exists.
# - Only considers files marked Added (A) or Modified (M).

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)

# --- Parse arguments ---
BASE_BRANCH=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --base)
      if [[ $# -lt 2 ]]; then
        echo "Error: --base requires a branch name" >&2
        exit 2
      fi
      BASE_BRANCH="$2"
      shift 2
      ;;
    -h|--help)
      echo "Usage: $0 [--base <branch>]"
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      echo "Usage: $0 [--base <branch>]" >&2
      exit 2
      ;;
  esac
done

# Ensure we're in a git repo
if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "Error: not inside a git repository." >&2
  exit 2
fi

# --- Determine default branch if not provided ---
if [[ -z "$BASE_BRANCH" ]]; then
  if git show-ref --verify --quiet refs/heads/main; then
    BASE_BRANCH="main"
  elif git show-ref --verify --quiet refs/heads/master; then
    BASE_BRANCH="master"
  else
    echo "Error: could not determine default branch (no 'main' or 'master' found)." >&2
    exit 2
  fi
fi

# Collect added or modified .v and .md files relative to merge-base of BASE_BRANCH...HEAD
CHANGED_FILES=$(git diff --name-only --diff-filter=AM "${BASE_BRANCH}...HEAD" | grep -E '\.(v|md)$' || true)

if [[ -z "$CHANGED_FILES" ]]; then
  echo "No added or modified *.v or *.md files relative to ${BASE_BRANCH}."
  exit 0
fi

exec "$SCRIPT_DIR/spell-check-files.sh" $CHANGED_FILES
