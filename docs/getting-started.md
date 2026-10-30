---
title: "Getting started"
description: "Build growth-rates-lean, depend on it from another Lake project, and use its main theorem."
---

# Getting started

## Build

Toolchain Lean `v4.35.0` ([`lean-toolchain`](https://github.com/chenle02/growth-rates-lean/blob/main/lean-toolchain)); Mathlib `v4.35.0`, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` ([`lake-manifest.json`](https://github.com/chenle02/growth-rates-lean/blob/main/lake-manifest.json)).

```sh
git clone https://github.com/chenle02/growth-rates-lean.git
cd growth-rates-lean
lake exe cache get
lake build
```

## Depend on it

From another Lake project with the same toolchain, add to `lakefile.toml`:

```toml
[[require]]
name = "growth-rates-lean"
git = "https://github.com/chenle02/growth-rates-lean"
rev = "v0.1.0"
```

then run `lake update growth-rates-lean` and `lake exe cache get`. `import GrowthRates` imports every module; `import GrowthRates.RealFekete` (or another
module from the [modules page]({{ '/modules.html' | relative_url }})) imports one.

## A first example

`GrowthRates.RealFekete.tendsto_div_rate` is Fekete's lemma in continuous time. Its hypothesis
`RealTimeBounds b` has three fields: $`b(t)\ge0`$ for $`t\ge0`$, $`b(t+u)\le b(t)+b(u)`$ for $`t,u\ge0`$, and an
upper bound on every interval $`[0,h]`$. The limit is `rate b`, Mathlib's `sInf` of the slopes $`b(h)/h`$
over $`h>0`$.

```lean
import GrowthRates.RealFekete

open Filter Topology GrowthRates.RealFekete

/-- Fekete's lemma in continuous time, used directly. -/
example {b : ℝ → ℝ} (H : RealTimeBounds b) :
    Tendsto (fun t : ℝ => b t / t) atTop (𝓝 (rate b)) :=
  tendsto_div_rate H

/-- The same rate for a function within a logarithmic error of `b`. -/
example {b m : ℝ → ℝ} (H : RealTimeBounds b) (A B : ℝ)
    (hlo : ∀ t, 0 < t → m t ≤ b t)
    (hhi : ∀ t, 0 < t → b t ≤ m t + A + B * Real.log (1 + t)) :
    Tendsto (fun t : ℝ => m t / t) atTop (𝓝 (rate b)) :=
  tendsto_div_rate_of_comparison H A B hlo hhi
```

`rate_le_slope H ht` gives $`\operatorname{rate}b\le b(t)/t`$ for each $`t>0`$, and `rate_nonneg H` gives
$`\operatorname{rate}b\ge0`$.

## Verify

- `bash verify.sh LOG` is the build check that lean-pkg runs for its receipt, from a clean checkout at the
  commit to certify. It rebuilds `GrowthRates.Solution` and `GrowthRates.Axioms` from scratch and writes the
  build output, the `sorry` count, the `#print axioms` results and the axioms of every declaration in
  `claims.yaml` to `LOG`.
- `bash scripts/check-negative-controls.sh`, after `lake build GrowthRates`, compiles each deliberately
  altered contract in `GrowthRatesTest/` and requires each attempted API application to fail with its exact recorded elaboration errors, never setup errors.
- The trusted comparator statements are in
  [`GrowthRates/Challenge.lean`](https://github.com/chenle02/growth-rates-lean/blob/main/GrowthRates/Challenge.lean)
  (configuration [`comparator.json`](https://github.com/chenle02/growth-rates-lean/blob/main/comparator.json));
  their `sorry` is intentional.

## Trust and axioms

The library modules contain no `sorry`. Every declaration in `claims.yaml` and every comparator Solution
theorem must depend only on `propext`, `Classical.choice` and `Quot.sound`
([`GrowthRates/Axioms.lean`](https://github.com/chenle02/growth-rates-lean/blob/main/GrowthRates/Axioms.lean)).
Eight API regression controls reject altered applications; this does not prove every altered theorem false. Receipts are recorded under
`.lean-receipts/` once the gate runs, and the [verification page]({{ '/verification.html' | relative_url }})
shows them. No tool checks that the prose on this site describes the Lean statements.

## Reproduce the full local maintenance check

Install Git, Python 3 and Lean's `elan` manager first. Git retrieves source; elan selects
the compiler named in `lean-toolchain`; Lake builds it; Mathlib supplies the imported
mathematics. `lake exe cache get` downloads dependency artifacts rather than proving
them again. Keep the committed manifest; do not update dependencies during this check.

From a clean checkout after the dependency cache download:

```sh
verification_dir=$(mktemp -d)
export LAKE_CACHE_DIR="$verification_dir/lake-cache"
export LAKE_ARTIFACT_CACHE=false
export LEAN_NUM_THREADS=3
bash verify.sh "$verification_dir/verify.log"
```

This rebuilds all owned library and comparison implementation modules, runs the eight
API controls, reads every module-owned declaration and its complete available identities,
checks reader mutations and a separately compiled forbidden-axiom fixture, then audits
all 41 registered claims. A zero process exit and the three final manifest/log digest
lines indicate completion. Keep the log and adjacent control/audit directories together.
The raw owned record stream is about 2 GB; allow disk and memory headroom.

This command is the build/audit tier. The independent 26-slot statement comparison
requires lean-pkg's `receipt comparator` command on a supported host, and the published
checkpoint additionally records a separate source-only owned rebuild and exact stream
comparison. Running the command twice does not establish an independent compiler or
rebuild imported Mathlib from source. The compiler, imported dependency artifacts,
initial statement transcription and prose remain explicit trust boundaries.

If `lake` is missing, check the elan installation and PATH. Cache-download failures are
network/setup failures, not theorem refutations. If a dependency is dirty or at the
wrong revision, restore a fresh checkout at the committed pin rather than running
`lake update`. On memory exhaustion, reduce concurrent processes and preserve the
failed log before a fresh attempt.
