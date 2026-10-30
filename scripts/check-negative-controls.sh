#!/usr/bin/env bash
# Altered-contract controls. See the exact scope in the Python checker.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
python3 "$root/scripts/check-negative-controls.py" "$out/results"
