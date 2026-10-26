#!/bin/bash
# verify.sh LOG: the lower-tier check of this package (written by `lean-pkg new`). Run it through
# `lean-pkg receipt systemd --run` from a clean checkout at the commit to certify; see docs/quickstart.md:
#
#   lean-pkg receipt systemd --unit growth-rates-lean-verify --commit "$(git rev-parse HEAD)" --log ../growth-rates-lean-verify/verify.log \
#     --stdout ../growth-rates-lean-verify/unit.out --stderr ../growth-rates-lean-verify/unit.err --run -- bash verify.sh ../growth-rates-lean-verify/verify.log
#
# What the receipt reads; keep these lines as they are:
#   stdout: exactly one line each of pre-manifest-sha256, post-manifest-sha256, verify-log-sha256
#   stderr: empty (every tool writes into the log)
#   the log: checker:, commit:, lean-toolchain:, the build between lean-pkg-build: begin / end (a fresh
#            build: Lake must compile the package's modules, not restore them), sorry-count:, axioms:, and
#            the claim-axioms lines of every claim in claims.yaml, read from the built environment
set -euo pipefail
export LC_ALL=C LANG=C
unset LANGUAGE
LOG=${1:?usage: bash verify.sh LOG}
# The modules the receipt certifies: the proof and the axioms report (the Challenge's sorry is by design and
# is judged by comparator-receipt, not here).
MODULES="GrowthRates.Solution GrowthRates.Axioms"
# Per-claim axioms read from the built environment (lean-pkg's ClaimAxioms.lean, core Lean only):
# `claim-axioms: NAME AXIOMS` / `claim-missing: NAME` for every claim of claims.yaml, then
# `claim-axioms-done: N`. The receipt refuses a missing or unchecked claim and sorryAx.
claims_decls() {
  awk 'function val(s) {
  sub(/^[A-Za-z_]+:[ \t]*/, "", s); sub(/[ \t]+#.*$/, "", s); sub(/[ \t\r]+$/, "", s)
  if (s ~ /^".*"$/ || s ~ /^'\''.*'\''$/) s = substr(s, 2, length(s) - 2)
  return s
}
function flush() { if (decl != "") print decl "\t" file; decl = ""; file = "" }
BEGIN { item = -1; key = -1 }
/^[ \t]*#/ || /^[ \t\r]*$/ { next }
/^claims:/ { inl = 1; next }
inl && /^[^ \t-]/ { flush(); inl = 0 }
!inl { next }
{
  match($0, /^ */); ind = RLENGTH; rest = substr($0, ind + 1)
  if (rest ~ /^- /) {
    if (item < 0) item = ind
    if (ind == item) { flush(); match(rest, /^- +/); ind = ind + RLENGTH; rest = substr(rest, RLENGTH + 1); key = ind }
  }
  if (ind == key) {
    if (rest ~ /^decl:/) decl = val(rest)
    else if (rest ~ /^file:/) file = val(rest)
  }
}
END { flush() }' "$1"
}
claim_axioms_run() {
  [ -f claims.yaml ] || return 0
  local pairs names mods
  pairs=$(claims_decls claims.yaml)
  if [ -z "$pairs" ]; then echo "claim-axioms-done: 0" >>"$1"; return 0; fi
  names=$(printf '%s\n' "$pairs" | cut -f1)
  mods=$(printf '%s\n' "$pairs" | cut -f2 | grep '\.lean$' | sed -e 's/\.lean$//' -e 's|/|.|g' | sort -u || true)
  mkdir -p "$2"
  cat >"$2/ClaimAxioms.lean" <<'LEAN_PKG_CLAIM_AXIOMS'
/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0
-/
-- lean_pkg.claim_axioms: the Lean half. Read-only probe of a compiled environment.
--
-- Usage: LEAN_PATH=<the package's> lean --run ClaimAxioms.lean MOD [MOD ...] -- NAME [NAME ...]
--
-- Imports MOD... exactly as `import MOD` would (data only: no extension state is loaded and no
-- initializer runs, so Lean walks every constant body itself instead of reading axiom lists cached in
-- the .olean files), then runs core Lean's `collectAxioms` on every NAME and prints one line per name:
--   claim-axioms: NAME AX1,AX2,...   (sorted; `none` when it depends on no axiom)
--   claim-missing: NAME              (no constant of that name in the environment)
-- and a final `claim-axioms-done: N` line (N = the number of names). A run without that line is
-- incomplete; lean_pkg/claim_axioms.py refuses it. Nothing is judged here. Core Lean only.
import Lean

open Lean

/-- The monad `collectAxioms` needs: an environment that can be read. -/
abbrev ClaimAxiomsM := StateM Environment

instance : MonadEnv ClaimAxiomsM where
  getEnv := get
  modifyEnv f := modify f

def main (args : List String) : IO UInt32 := do
  let mods := args.takeWhile (· != "--")
  let names := (args.dropWhile (· != "--")).drop 1
  if mods.isEmpty || names.isEmpty then
    IO.eprintln "usage: lean --run ClaimAxioms.lean MOD [MOD ...] -- NAME [NAME ...]"
    return 2
  initSearchPath (← findSysroot)
  let imports := mods.toArray.map fun m => ({ module := m.toName } : Import)
  let env ← importModules imports {} (loadExts := false)
  let mut n := 0
  for s in names do
    n := n + 1
    let name := s.toName
    if (env.find? name).isNone then
      IO.println s!"claim-missing: {s}"
    else
      let (axs, _) := (collectAxioms name : ClaimAxiomsM (Array Name)).run env
      let sorted := (axs.map toString).qsort (· < ·)
      let shown := if sorted.isEmpty then "none" else ",".intercalate sorted.toList
      IO.println s!"claim-axioms: {s} {shown}"
  IO.println s!"claim-axioms-done: {n}"
  return 0
LEAN_PKG_CLAIM_AXIOMS
  # shellcheck disable=SC2086 # one word per module and per name
  ${RUN:-} env LEAN_PATH="$3" lean --run "$2/ClaimAxioms.lean" $mods -- $names >>"$1" 2>&1
}
echo "pre-manifest-sha256 $(sha256sum lake-manifest.json | cut -d' ' -f1)"
rm -rf .lake/build
{
  echo "commit: $(git rev-parse HEAD)"
  echo "lean-toolchain: $(cat lean-toolchain)"
  echo "checker: verify.sh (lake build $MODULES; #print axioms)"
  echo "lean-pkg-build: begin"
} >"$LOG"
lake build $MODULES >>"$LOG" 2>&1
echo "lean-pkg-build: end" >>"$LOG"
ca_dir=$(mktemp -d)
claim_axioms_run "$LOG" "$ca_dir" "$(lake env printenv LEAN_PATH)"
rm -rf "$ca_dir"
sorry=$(grep -c -E "declaration uses ['\`]sorry['\`]" "$LOG" || true)
axioms=$(tr '\n' ' ' <"$LOG" | grep -o 'depends on axioms: \[[^]]*\]' | sed -e 's/^[^[]*\[//' -e 's/\]$//' \
  | tr ',' '\n' | tr -d ' ' | grep -v '^$' | sort -u | paste -sd, - || true)
{
  echo "sorry-count: $sorry"
  if [ -n "$axioms" ]; then
    echo "axioms: $axioms"
  elif grep -q 'does not depend on any axioms' "$LOG"; then
    echo "axioms: none"
  fi
  echo "generated-at: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} >>"$LOG"
# The seal: nothing may write to the log after this line.
echo "post-manifest-sha256 $(sha256sum lake-manifest.json | cut -d' ' -f1)"
echo "verify-log-sha256 $(sha256sum "$LOG" | cut -d' ' -f1)"
