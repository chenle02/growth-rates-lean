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
#            the claim-axioms lines of every claim in claims.yaml, read from the built environment, and
#            the hyp-probe/1 section after them (the Challenge, when built for it, goes to a side log
#            beside LOG, hyp-challenge-build.log, never into LOG)
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
# Conditional-claim facts read from the built environment (lean-pkg's HypProbe.lean, core Lean only;
# proposal 0003): the `== lean-pkg hypotheses (hyp-probe/1) ==` section, one `hyp-*: {json}` line
# per fact, then `hyp-done`. The Challenge is built into a side log, never into this log.
hyp_json_str() {
  printf '"%s"' "$(printf '%s' "$1" | tr -d '\000-\037' | sed -e 's/\\/\\\\/g' -e 's/"/\\"/g')"
}
hyp_error() {   # OUT PHASE EXIT FILE...: one hyp-error line, the first error line without paths
  local out=$1 phase=$2 rc=$3 msg
  shift 3
  msg=$(cat "$@" 2>/dev/null | grep -m1 -i 'error' | sed -e 's#[^ ]*/##g' | cut -c1-200 || true)
  echo "hyp-error: {\"phase\":\"$phase\",\"message\":$(hyp_json_str "exit $rc${msg:+: $msg}")}" >>"$out"
}
hypotheses_run() {
  [ -f claims.yaml ] || return 0
  local dir=$2 side=${4:-$2/hyp-challenge-build.log} pairs names mods rc cfgs="" cfg m ok built=1 decls chal list=""
  mkdir -p "$dir"
  local out="$dir/hyp.out" part="$dir/hyp.part" err="$dir/hyp.err"
  : >"$out"
  cat >"$dir/HypProbe.lean" <<'LEAN_PKG_HYP_PROBE'
/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0
-/
-- lean_pkg.hypotheses: the Lean half (proposal 0003, the `hyp-probe/1` section of the verify log).
-- Read-only probe of a compiled environment. Lean prints facts; lean_pkg/hypotheses.py judges them.
--
-- Usage (LEAN_PATH=<the package's>):
--   lean --run HypProbe.lean decl MOD [MOD ...] -- NAME [NAME ...]
--       imports MOD... and prints, for every NAME, one line
--         hyp-decl: {"v":1,"theorem":N,"binders":[{"i","head","kind","module","explicit"}...],"data_binders":k}
--         hyp-missing: {"v":1,"theorem":N}            (no constant of that name)
--   lean --run HypProbe.lean modules CFG [CFG ...]
--       reads each comparator configuration (JSON) and prints `challenge-module: M` for its `challenge_module`,
--       each module once (for the job, which builds them outside the sealed log; never part of the log).
--   lean --run HypProbe.lean challenge CFG [CFG ...]
--       imports every configuration's Challenge module into one environment and prints
--         hyp-challenge: {... as hyp-decl ..., "config":C}  (once per name of each configuration's theorem_names)
--       then positive facts only, over the distinct Challenge theorems:
--         hyp-corollary: {"corollary":T',"of":T,"drops":[H...],"binders":[i...]}
--         hyp-proof: {"proof":P,"proves":H}
--         hyp-witness: {"witness":W,"of":T}
--         hyp-skip: {"theorem":T,"reason":R}           (more than MAX_HYPS distinct hypothesis constants)
--         hyp-error: {"phase":"challenge","message":M}  (a configured name that is not in the environment)
-- The header line and the final `hyp-done` line are written by the job (hypotheses.job_sh), which counts
-- these lines. A run that fails (exit code not 0) is replaced by one `hyp-error` line there.
--
-- Comparison (proposal 0003, open question 4): `Expr.eqv` (`==`: binder names and annotations ignored), plus
-- equal binder annotations on the outer binders, plus the other theorem's universe parameters renamed
-- positionally. No unfolding, no `whnf`, no `isDefEq`. Only non-dependent binders are dropped. Core Lean only.
import Lean

open Lean Meta

namespace HypProbe

/-- Above this many distinct hypothesis constants the 2^m subset search is not run (`hyp-skip`). -/
def MAX_HYPS : Nat := 12

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- A JSON string. -/
def js (s : String) : String := (Json.str s).compress

def str (n : Name) : String := js n.toString

/-- A JSON object of already rendered values, its keys in the given order, compact. -/
def obj (pairs : List (String × String)) : String :=
  "{" ++ ",".intercalate (pairs.map fun (k, v) => js k ++ ":" ++ v) ++ "}"

def arr (xs : Array String) : String := "[" ++ ",".intercalate xs.toList ++ "]"

def line (tag : String) (pairs : List (String × String)) : IO Unit :=
  IO.println s!"{tag}: {obj pairs}"

/-- One `Prop` binder headed by a constant: its position, head, the head's kind and module, explicitness. -/
structure Hyp where
  i : Nat
  head : Name
  explicit : Bool

/-- The binders of a type's telescope (not unfolded): the `Prop` binders headed by a constant, and the number
of binders that are not `Prop`s. -/
def binders (ty : Expr) : MetaM (Array Hyp × Nat) :=
  forallTelescope ty fun xs _ => do
    let mut out := #[]
    let mut data := 0
    for h : i in [0:xs.size] do
      let d ← xs[i].fvarId!.getDecl
      let t := d.type
      if ← isProp t then
        let f := t.getAppFn
        if f.isConst then
          out := out.push { i, head := f.constName!, explicit := d.binderInfo.isExplicit }
      else
        data := data + 1
    return (out, data)

def moduleOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some idx => (env.allImportedModuleNames[idx.toNat]?.map toString).getD ""
  | none => ""

def binderJson (env : Environment) (h : Hyp) : String :=
  let k := (env.find? h.head).map kindOf |>.getD "missing"
  obj [("i", toString h.i), ("head", str h.head), ("kind", js k), ("module", js (moduleOf env h.head)),
    ("explicit", toString h.explicit)]

/-- The `hyp-decl` / `hyp-challenge` keys of a constant. -/
def declPairs (env : Environment) (thm : Name) (ty : Expr) : MetaM (List (String × String)) := do
  let (hs, data) ← binders ty
  return [("v", "1"), ("theorem", str thm), ("binders", arr (hs.map (binderJson env))),
    ("data_binders", toString data)]

/-- `ty` without the outer binders at the positions `drop` selects, or none when a kept binder or the body
mentions a dropped one. -/
partial def dropAt (drop : Nat → Bool) : Nat → Expr → Option Expr
  | i, .forallE n t b bi =>
    if drop i then
      if b.hasLooseBVar 0 then none else dropAt drop (i + 1) (b.lowerLooseBVars 1 1)
    else (dropAt drop (i + 1) b).map fun b' => .forallE n t b' bi
  | _, e => some e

/-- The binder annotations of the outer binders. -/
def infos : Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: infos b
  | _ => []

/-- `Expr.eqv` plus equal outer binder annotations. -/
def same (a b : Expr) : Bool := a == b && infos a == infos b

/-- `ci`'s type with its universe parameters renamed positionally to `us` (same count), else unchanged. -/
def typeAt (ci : ConstantInfo) (us : List Name) : Expr :=
  if ci.levelParams.length == us.length then ci.instantiateTypeLevelParams (us.map mkLevelParam) else ci.type

/-- The expected witness type of `ty`: `∃` over its non-`Prop` binders in order, of the right-nested `∧` of all
its `Prop` binders in order; none when there is no `Prop` binder or the result would mention a proof. -/
def witnessType (ty : Expr) : MetaM (Option Expr) :=
  forallTelescope ty fun xs _ => do
    let mut data := #[]
    let mut props := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then props := props.push t else data := data.push x
    if props.isEmpty then return none
    let conj := props.pop.foldr (fun p acc => mkAnd p acc) props.back!
    let mut body := conj
    for x in data.reverse do
      body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]
    body ← instantiateMVars body
    if body.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then return none
    return some body

/-- The subsets of `xs` (as lists, in `xs` order), the empty one first. -/
def subsets : List Name → List (List Name)
  | [] => [[]]
  | x :: rest => let r := subsets rest; r ++ r.map (x :: ·)

def runDecl (names : List String) : MetaM Unit := do
  let env ← getEnv
  for s in names do
    let n := s.toName
    match env.find? n with
    | none => line "hyp-missing" [("v", "1"), ("theorem", js s)]
    | some ci => line "hyp-decl" (← declPairs env n ci.type)

structure Config where
  path : String
  challenge : Name
  names : Array Name

def readConfig (path : String) : IO Config := do
  let text ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse text |>.mapError fun e => s!"{path}: not JSON: {e}")
  let m ← IO.ofExcept (j.getObjValAs? String "challenge_module"
    |>.mapError fun _ => s!"{path}: no string challenge_module")
  let ns ← IO.ofExcept (j.getObjValAs? (Array String) "theorem_names"
    |>.mapError fun _ => s!"{path}: theorem_names is not a list of strings")
  return { path, challenge := m.toName, names := ns.map String.toName }

def runChallenge (cfgs : Array Config) : MetaM Unit := do
  let env ← getEnv
  let mut thms : Array Name := #[]
  for c in cfgs do
    for n in c.names do
      match env.find? n with
      | none =>
        line "hyp-error" [("phase", js "challenge"),
          ("message", js s!"{n} (theorem_names of {c.path}) is not in the Challenge environment")]
      | some ci =>
        line "hyp-challenge" ((← declPairs env n ci.type) ++ [("config", js c.path)])
        unless thms.contains n do thms := thms.push n
  -- the binders of every distinct Challenge theorem, and every hypothesis constant
  let mut info : Array (Name × ConstantInfo × Array Hyp) := #[]
  let mut heads : Array Name := #[]
  for n in thms do
    let ci := (env.find? n).get!
    let (hs, _) ← binders ci.type
    info := info.push (n, ci, hs)
    for h in hs do
      unless heads.contains h.head do heads := heads.push h.head
  -- hyp-corollary: T' is T with every binder headed by a constant of S removed (S non-empty)
  for (t, tci, hs) in info do
    let consts := hs.foldl (fun acc h => if acc.contains h.head then acc else acc.push h.head) #[]
    if consts.size > MAX_HYPS then
      line "hyp-skip" [("theorem", str t), ("reason", js
        s!"{consts.size} distinct hypothesis constants, more than {MAX_HYPS}: the corollary search is not run")]
      continue
    for s in subsets consts.toList do
      if s.isEmpty then continue
      let pos := hs.filter (s.contains ·.head) |>.map (·.i)
      let some dropped := dropAt (pos.contains ·) 0 tci.type | continue
      for (c, cci, _) in info do
        if c == t then continue
        if same dropped (typeAt cci tci.levelParams) then
          line "hyp-corollary" [("corollary", str c), ("of", str t),
            ("drops", arr (s.toArray.map str)), ("binders", arr (pos.map toString))]
  -- hyp-proof: a theorem whose type is exactly a hypothesis constant
  for (p, pci, _) in info do
    match pci.type with
    | .const h _ => if heads.contains h then line "hyp-proof" [("proof", str p), ("proves", str h)]
    | _ => pure ()
  -- hyp-witness: a theorem whose type is the expected witness type of a conditional theorem
  for (t, tci, hs) in info do
    if hs.isEmpty then continue
    let some w ← (try witnessType tci.type catch _ => pure none) | continue
    for (c, cci, _) in info do
      if c == t then continue
      if typeAt cci tci.levelParams == w then
        line "hyp-witness" [("witness", str c), ("of", str t)]

def runMeta (env : Environment) (x : MetaM Unit) : IO Unit := do
  let ctx : Core.Context := { fileName := "<hypprobe>", fileMap := default }
  let _ ← (x.run' {}).toIO ctx { env := env }

def importAll (mods : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  importModules (mods.map fun m => ({ module := m } : Import)) {} (loadExts := false)

end HypProbe

open HypProbe in
def main (args : List String) : IO UInt32 := do
  match args with
  | "decl" :: rest =>
    let mods := rest.takeWhile (· != "--")
    let names := (rest.dropWhile (· != "--")).drop 1
    if mods.isEmpty || names.isEmpty then
      IO.eprintln "usage: lean --run HypProbe.lean decl MOD [MOD ...] -- NAME [NAME ...]"
      return 2
    let env ← importAll (mods.toArray.map String.toName)
    runMeta env (runDecl names)
    return 0
  | "modules" :: cfgs@(_ :: _) =>
    let mut seen : Array Name := #[]
    for p in cfgs do
      let c ← readConfig p
      unless seen.contains c.challenge do
        seen := seen.push c.challenge
        IO.println s!"challenge-module: {c.challenge}"
    return 0
  | "challenge" :: cfgs@(_ :: _) =>
    let cs ← cfgs.toArray.mapM readConfig
    let mods := cs.foldl (fun acc c => if acc.contains c.challenge then acc else acc.push c.challenge) #[]
    let env ← importAll mods
    runMeta env (runChallenge cs)
    return 0
  | _ =>
    IO.eprintln "usage: lean --run HypProbe.lean (decl MOD... -- NAME... | modules CFG... | challenge CFG...)"
    return 2
LEAN_PKG_HYP_PROBE
  pairs=$(claims_decls claims.yaml)
  if [ -n "$pairs" ]; then
    names=$(printf '%s\n' "$pairs" | cut -f1)
    mods=$(printf '%s\n' "$pairs" | cut -f2 | grep '\.lean$' | sed -e 's/\.lean$//' -e 's|/|.|g' | sort -u || true)
    rc=0
    # shellcheck disable=SC2086 # one word per module and per name
    ${RUN:-} env LEAN_PATH="$3" lean --run "$dir/HypProbe.lean" decl $mods -- $names >"$part" 2>"$err" || rc=$?
    if [ "$rc" = 0 ]; then grep -E '^hyp-[a-z-]+: ' "$part" >>"$out" || true
    else hyp_error "$out" decl "$rc" "$part" "$err"; fi
  fi
  if grep -Eq '^[[:blank:]-]+(hypotheses|discharges|witness):' claims.yaml; then
    for cfg in comparator*.json comparator/config*.json; do
      if [ -f "$cfg" ]; then cfgs="$cfgs $cfg"; list="$list${list:+,}$(hyp_json_str "$cfg")"; fi
    done
    if [ -n "$cfgs" ]; then
      rc=0
      # shellcheck disable=SC2086 # one word per configuration
      ${RUN:-} env LEAN_PATH="$3" lean --run "$dir/HypProbe.lean" modules $cfgs >"$part" 2>"$err" || rc=$?
      if [ "$rc" != 0 ]; then hyp_error "$out" challenge "$rc" "$part" "$err"
      else
        sed -n 's/^challenge-module: //p' "$part" >"$dir/modules"
        : >"$side"
        while IFS= read -r m; do
          ok=true
          ${RUN:-} lake build "$m" </dev/null >>"$side" 2>&1 || { ok=false; built=0; }
          echo "hyp-challenge-build: {\"module\":$(hyp_json_str "$m"),\"ok\":$ok}" >>"$out"
        done <"$dir/modules"
        if [ "$built" = 1 ]; then
          rc=0
          # shellcheck disable=SC2086 # one word per configuration
          ${RUN:-} env LEAN_PATH="$3" lean --run "$dir/HypProbe.lean" challenge $cfgs >"$part" 2>"$err" || rc=$?
          if [ "$rc" = 0 ]; then grep -E '^hyp-[a-z-]+: ' "$part" >>"$out" || true
          else hyp_error "$out" challenge "$rc" "$part" "$err"; fi
        else
          echo "hyp-error: {\"phase\":\"challenge\",\"message\":\"a Challenge module did not build (its output: the side log hyp-challenge-build.log)\"}" >>"$out"
        fi
      fi
    fi
  fi
  decls=$(grep -c -E '^hyp-(decl|missing): ' "$out" || true)
  chal=$(grep -c '^hyp-challenge: ' "$out" || true)
  {
    echo "== lean-pkg hypotheses (hyp-probe/1) =="
    cat "$out"
    echo "hyp-done: {\"v\":1,\"decls\":$decls,\"challenge\":$chal,\"configs\":[$list]}"
  } >>"$1"
}
echo "pre-manifest-sha256 $(sha256sum lake-manifest.json | cut -d' ' -f1)"
rm -rf .lake/build
{
  echo "commit: $(git rev-parse HEAD)"
  echo "lean-toolchain: $(cat lean-toolchain)"
  python3 -c 'import json; print("mathlib-rev: " + next(p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"] == "mathlib"))'
  echo "checker: verify.sh (lake build $MODULES; #print axioms)"
  echo "lean-pkg-build: begin"
} >"$LOG"
git diff --exit-code HEAD -- . ":!.lean-receipts" >>"$LOG" 2>&1
lake build -v $MODULES >>"$LOG" 2>&1
echo "lean-pkg-build: end" >>"$LOG"
python3 scripts/check-negative-controls.py "${LOG}.controls" >>"$LOG" 2>&1
python3 scripts/audit-owned.py "${LOG}.owned" >>"$LOG" 2>&1
python3 scripts/test-owned-reader.py "${LOG}.owned/stdout.log" "${LOG}.reader.json" >>"$LOG" 2>&1
python3 scripts/check-axiom-fixture.py "${LOG}.axiom-fixture" >>"$LOG" 2>&1
ca_dir=$(mktemp -d)
claim_axioms_run "$LOG" "$ca_dir" "$(lake env printenv LEAN_PATH)"
hypotheses_run "$LOG" "$ca_dir/hyp-probe" "$(lake env printenv LEAN_PATH)" "$(dirname "$LOG")/hyp-challenge-build.log"
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
git diff --exit-code HEAD -- . ":!.lean-receipts" >>"$LOG" 2>&1
# The seal: nothing may write to the log after this line.
echo "post-manifest-sha256 $(sha256sum lake-manifest.json | cut -d' ' -f1)"
echo "verify-log-sha256 $(sha256sum "$LOG" | cut -d' ' -f1)"
