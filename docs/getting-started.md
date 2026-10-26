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
```

then run `lake update growth-rates-lean` and `lake exe cache get`. A release tag for `rev` will be added at
the first release. `import GrowthRates` imports every module; `import GrowthRates.RealFekete` (or another
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
  falsified statement in `GrowthRatesTest/` and requires every one to fail for a mathematical reason.
- The trusted comparator statements are in
  [`GrowthRates/Challenge.lean`](https://github.com/chenle02/growth-rates-lean/blob/main/GrowthRates/Challenge.lean)
  (configuration [`comparator.json`](https://github.com/chenle02/growth-rates-lean/blob/main/comparator.json));
  their `sorry` is intentional.

## Trust and axioms

The library modules contain no `sorry`. Every declaration in `claims.yaml` and every comparator Solution
theorem must depend only on `propext`, `Classical.choice` and `Quot.sound`
([`GrowthRates/Axioms.lean`](https://github.com/chenle02/growth-rates-lean/blob/main/GrowthRates/Axioms.lean)).
Eight negative controls check that falsified variants are rejected. Receipts are recorded under
`.lean-receipts/` once the gate runs, and the [verification page]({{ '/verification.html' | relative_url }})
shows them. No tool checks that the prose on this site describes the Lean statements.
