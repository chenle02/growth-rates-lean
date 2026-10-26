---
title: "Modules"
description: "The Lean modules of growth-rates-lean and the declarations each contains."
---

# Modules

The library root `GrowthRates` imports the four library modules below. Each declaration is listed with a
one-line description; the Lean statement decides every hypothesis. Theorems stated in the comparator
Challenge are marked *compared*.

## `GrowthRates.RealFekete`

Fekete's lemma in continuous time, for $`b\colon\mathbb{R}\to\mathbb{R}`$ on $`[0,\infty)`$, and the transfer
of its rate to comparable functions.

| Declaration | Meaning |
|---|---|
| `RealTimeBounds b` | Structure: $`b\ge0`$, $`b(t+u)\le b(t)+b(u)`$ for $`t,u\ge0`$, and an upper bound on every $`[0,h]`$ |
| `rate b` | Definition: $`\inf_{h>0}b(h)/h`$, as Mathlib's `sInf` of the slopes |
| `slopes_nonempty` | The set of slopes $`b(h)/h`$, $`h>0`$, is nonempty |
| `slopes_bdd` | Under `RealTimeBounds b` the slopes are bounded below by $`0`$ |
| `rate_le_slope` | $`\operatorname{rate}b\le b(t)/t`$ for every $`t>0`$ (compared) |
| `rate_nonneg` | $`\operatorname{rate}b\ge0`$ (compared) |
| `multiple_remainder` | Iterated subadditivity: $`b(kh+r)\le k\,b(h)+b(r)`$ for $`h,r\ge0`$, $`k\in\mathbb{N}`$ |
| `block_bound` | For each $`h>0`$ there is $`M`$ with $`b(t)/t\le b(h)/h+M/t`$ for all $`t>0`$ |
| `tendsto_div_rate` | **Fekete's lemma in continuous time:** $`b(t)/t\to\operatorname{rate}b`$ (compared) |
| `logarithmic_error_vanishes` | $`(A+B\log(1+t))/t\to0`$ |
| `tendsto_div_rate_of_comparison` | If $`m\le b\le m+A+B\log(1+t)`$ for $`t>0`$, then $`m(t)/t\to\operatorname{rate}b`$ (compared) |
| `lower_bound_of_comparison` | Under the upper comparison, $`t\operatorname{rate}b-A-B\log(1+t)\le m(t)`$ for every $`t>0`$ (compared) |
| `SubmulInputs N C` | Structure: $`C\ge0`$, $`N\ge1`$, $`N(t+u)\le N(t)N(u)`$ and $`N(t)\le e^{Ct}`$ on $`[0,\infty)`$ |
| `log_realTimeBounds` | Under `SubmulInputs N C`, $`\log N`$ satisfies `RealTimeBounds` |
| `log_rate_of_submul` | For $`0<F\le N`$ with $`\log N\le\log F+A+B\log(1+t)`$: $`\log F(t)/t\to\operatorname{rate}(\log N)`$ and the finite-time lower bound (compared) |
| `lower_bound_at_zero` | The lower bound at $`t=0`$ when the comparison is supplied there |

## `GrowthRates.LogDefect`

Fekete's lemma for functions that are superadditive up to a logarithmic defect
$`a(x)+a(y)-M\log(x+y)-B\le a(x+y)`$ for $`x,y\ge h`$, with $`M,B\ge0`$ and $`h\ge1`$.

| Declaration | Meaning |
|---|---|
| `correction M B x` | Definition: $`M\log x+B+M\log\tfrac92`$ |
| `corrected a M B x` | Definition: $`a(x)-\operatorname{correction}(M,B,x)`$ |
| `balanced_ratio` | $`(x+y)^2\le\tfrac92xy`$ when $`x/2\le y\le2x`$, $`x\ge0`$ |
| `balanced_merge` | Balanced merges of the corrected function are superadditive (compared) |
| `corrected_nat_blocks` | $`k\cdot\operatorname{corrected}(x)\le\operatorname{corrected}(kx)`$ for $`k\ge1`$, $`x\ge h`$, by balanced strong induction (compared) |
| `correction_nonneg` | The correction is nonnegative for $`M,B\ge0`$, $`x\ge1`$ |
| `nat_blocks` | $`k\cdot\operatorname{corrected}(x)\le a(kx)`$ for $`k\ge1`$, $`x\ge h`$ (compared) |
| `correction_sublinear` | $`\operatorname{correction}(M,B,t)/t\to0`$ |
| `fixed_block_lower` | A fixed block $`x\ge h`$ bounds $`a(t)/t`$ from below for all large $`t`$, using monotonicity |
| `rate a M B h` | Definition: $`\sup_{x\ge h}\operatorname{corrected}(x)/x`$ (Mathlib's `sSup`) |
| `tendsto_div_rate` | **Fekete's lemma with a logarithmic defect:** if also $`a`$ is monotone and $`a(x)\le Cx`$ on $`[h,\infty)`$, then $`a(t)/t\to\operatorname{rate}(a,M,B,h)`$ (compared) |
| `delayedRate b M B T0` | Definition: $`\sup_{T\ge T_0}\bigl(b(T)-M\log(1+T)-B-M\log\tfrac92\bigr)/(T+1)`$ |
| `tendsto_div_delayedRate` | Delayed form $`b(S)+b(T)-M\log(2+S+T)-B\le b(S+T+1)`$: $`b(t)/t\to\operatorname{delayedRate}\ge0`$ (compared) |
| `tendsto_log_div_delayedRate` | Multiplicative form for $`f\ge1`$: $`\log f(t)/t\to\operatorname{delayedRate}(\log f)\ge0`$ (compared) |

## `GrowthRates.Envelope`

Uniform and joint limits over an order parameter $`p\ge2`$, derived from fixed-order limits at the even
orders and one lower error uniform in the order.

| Declaration | Meaning |
|---|---|
| `evenOrder k` | Definition: $`2(k+1)`$ |
| `evenOrder_ge_two` | Every even order is at least $`2`$ |
| `exists_evenOrder_ge` | Every real $`p`$ is at most some even order |
| `envelope_limit` | Squeeze: a lower bound $`C-e\le f`$ with $`e\to0`$ and upper envelopes $`v_k\to a_k`$ with $`C`$ the greatest lower bound of the $`a_k`$ give $`f\to C`$ (compared) |
| `real_order_lower` | If $`q`$ is antitone in the order, even-order lower bounds give $`C-e(T)\le q(p,T)`$ for every real $`p\ge2`$ (compared) |
| `control_sandwich` | At a fixed $`T>0`$, the infimum $`\varphi(T)`$ over even orders satisfies $`C-e(T)\le\varphi(T)\le q(2k+2,T)`$ (compared) |
| `control_limit` | $`\varphi(T)\to C`$ from the fixed-order limits and $`e\to0`$ (compared) |
| `joint_limit` | If $`q`$ is antitone in the order, $`q(p_j,T_j)\to C`$ whenever $`p_j\to\infty`$, $`T_j\to\infty`$ (compared) |
| `corrected_infimum` | If $`C-e\le\varphi`$ on $`T>0`$, $`\varphi\to C`$ and $`e\to0`$, then $`C`$ is the greatest lower bound of $`\varphi+e`$ over $`T>0`$ |
| `corrected_sInf` | The same as an equality for Mathlib's `sInf` (compared) |
| `glb_div_time` | Division by $`T>0`$ preserves a greatest lower bound (compared) |

## `GrowthRates.FiniteError`

Explicit finite-time errors for a logarithmic growth rate $`\lambda`$, which is an input.

| Declaration | Meaning |
|---|---|
| `progression_limit` | If $`b(t)/t\to\lambda`$, then $`b(r+jh)/j\to\lambda h`$ along an arithmetic progression |
| `step_upper` | If $`b(t+h)\le b(t)+A`$ for $`t\ge r`$ and $`b(t)/t\to\lambda`$, then $`\lambda h\le A`$ (compared) |
| `step_lower` | If $`b(t)+A\le b(t+h)`$ for $`t\ge r`$ and $`b(t)/t\to\lambda`$, then $`A\le\lambda h`$ (compared) |
| `finite_bounds` | From the cut, confinement and composition inequalities: $`\lambda\ge0`$ and two-sided bounds on $`\log f(T)`$ for all $`T,\delta>0`$ (compared) |
| `optimize` | Two-sided bounds for every $`\delta>0`$ give $`\lvert b(T)-T\lambda\rvert\le n(1+\log(2+T\lambda/n))`$ (compared) |
| `log_error` | With $`f(0)=1`$ and $`n>0`$: $`\lvert\log f(T)-T\lambda\rvert\le n(1+\log(2+T\lambda/n))`$ for every $`T\ge0`$ (compared) |
| `sandwich_error` | The two-order sandwich estimate in pure real arithmetic (compared) |
| `CutInputs f B n lam` | Structure: the inputs of `log_error` for one function |
| `joint_error` | Two orders with `CutInputs` give $`\lvert x/(pz)-C\rvert\le c_n-C+(1+\log(2+Mz))/z`$ (compared) |

## Verification modules

These are not imported by `GrowthRates`.

| Module | Contents |
|---|---|
| `GrowthRates.Challenge` | The trusted comparator statements, in Mathlib vocabulary only, with every library definition written out; `sorry` by design |
| `GrowthRates.Solution` | Restates each Challenge theorem with the same name and type and proves it from the library |
| `GrowthRates.Axioms` | `#print axioms` for every declaration in `claims.yaml` and every Solution theorem |
