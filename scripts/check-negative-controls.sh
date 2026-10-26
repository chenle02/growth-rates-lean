#!/usr/bin/env bash
# Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
#
# check-negative-controls.sh: every GrowthRatesTest/Neg*.lean.disabled must FAIL to compile.
#
# Each control is a library statement with one deliberate falsification, followed by a proof
# attempt from the library. The script copies each control to a temporary .lean file inside the
# package (so `lake env lean` sees the built GrowthRates modules), compiles it, and requires
#   * a non-zero exit, and
#   * at least one `error:` line, none of which is a setup failure (missing import or object
#     file, unknown identifier/constant/namespace, parse error): the failure must come from the
#     falsified mathematics, not from a broken control.
# It prints PASS/FAIL per control and exits 1 if any control compiles or fails for a setup reason.
#
# Usage (from the package root, after `lake build GrowthRates`):
#   bash scripts/check-negative-controls.sh
# Honours LEAN_NUM_THREADS; wrap it in your resource cap, e.g.
#   LEAN_NUM_THREADS=4 systemd-run --user --scope -q -p CPUQuota=600% -p MemoryMax=24G \
#     bash scripts/check-negative-controls.sh
set -euo pipefail
export LC_ALL=C LANG=C

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"
shopt -s nullglob
controls=(GrowthRatesTest/Neg*.lean.disabled)
if [ "${#controls[@]}" -eq 0 ]; then
  echo "no negative control in GrowthRatesTest/Neg*.lean.disabled" >&2
  exit 1
fi

tmp=$(mktemp -d "$root/.lake/negative-controls.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

# Error text that means the control itself is broken rather than refuted.
setup_re='unknown (module|package|identifier|constant|namespace)|object file .* does not exist|unexpected token|expected term|unknown import|file not found|could not resolve import'

pass=0
fail=0
for ctl in "${controls[@]}"; do
  base=$(basename "$ctl" .lean.disabled)
  src="$tmp/$base.lean"
  log="$tmp/$base.log"
  cp "$ctl" "$src"
  set +e
  lake env lean "$src" >"$log" 2>&1
  code=$?
  set -e
  errors=$(grep -E '(^|: )error' "$log" || true)
  if [ "$code" -eq 0 ]; then
    echo "FAIL $base: compiled (exit 0); the falsified statement was accepted"
    fail=$((fail + 1))
  elif [ -z "$errors" ]; then
    echo "FAIL $base: exit $code without an error line"
    sed 's/^/    /' "$log" | head -20
    fail=$((fail + 1))
  elif printf '%s\n' "$errors" | grep -Eiq "$setup_re"; then
    echo "FAIL $base: setup error, not a mathematical refutation:"
    printf '%s\n' "$errors" | sed 's/^/    /' | head -10
    fail=$((fail + 1))
  else
    first=$(printf '%s\n' "$errors" | head -1 | sed "s|$tmp/||")
    echo "PASS $base: rejected (exit $code): ${first:0:160}"
    pass=$((pass + 1))
  fi
done

echo "negative controls: $pass passed, $fail failed, ${#controls[@]} total"
[ "$fail" -eq 0 ]
