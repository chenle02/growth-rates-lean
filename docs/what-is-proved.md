# What is proved

<!-- Hand-written. Lean statements copied verbatim from GrowthRates/RealFekete.lean, GrowthRates/LogDefect.lean, GrowthRates/Envelope.lean and GrowthRates/FiniteError.lean at commit 689257126d3859efba8a38076353c9570d1fe1f1 (the commit the build receipt binds). Re-copy them when the receipts move. -->

`growth-rates-lean` is a Lean 4 library of real analysis about the linear growth rate of a real
function of a continuous time parameter. It proves Fekete's lemma in continuous time, with the
limit identified as the infimum of the slopes; transfers that rate to any function within a
logarithmic error; proves a Fekete lemma for functions that are superadditive up to a logarithmic
defect, with the limit identified as the supremum of explicitly corrected slopes; derives limits
of order infima and joint large-order/time limits from fixed-order limits; and, given the rate as a
hypothesis, turns abstract cut, confinement and composition inequalities into an explicit error at
every finite time. The Fekete-type and envelope results derive their limits and infima; the
finite-time results take the rate $`\lambda`$ as a hypothesis and derive the error bounds.

How to read this page: each card below is one row of [`coverage.yaml`](../coverage.yaml) and
states one main result, sometimes with the lemmas that make it usable on its own. The typeset
statement is the author's transcription and is meant to be faithful to the Lean statement, with
every hypothesis and every conclusion; Lean checks only the Lean statement, which is folded under
each card and linked to its source line. The trusted statements judged by the comparator are in
`GrowthRates/Challenge.lean`, where every library definition below is written out in Mathlib
vocabulary.

## Notation

- All functions are maps $`\mathbb R\to\mathbb R`$ unless stated otherwise, and $`\log`$ is
  Mathlib's `Real.log`. "As $`t\to\infty`$" is Mathlib's `Tendsto … atTop`.
- **Fekete hypotheses** `RealFekete.RealTimeBounds b`: $`b(t)\ge0`$ for $`t\ge0`$;
  $`b(t+u)\le b(t)+b(u)`$ for $`t,u\ge0`$; and for every $`h>0`$ there is $`M`$ with
  $`b(r)\le M`$ for $`0\le r\le h`$.
- **Fekete rate** `RealFekete.rate b` $`=\operatorname{rate}(b)=\inf\{b(h)/h : h>0\}`$
  (Mathlib's `sInf` of the image of $`(0,\infty)`$).
- **Multiplicative inputs** `RealFekete.SubmulInputs N C`: $`C\ge0`$, and for $`t,u\ge0`$:
  $`N(t)\ge1`$, $`N(t+u)\le N(t)N(u)`$ and $`N(t)\le e^{Ct}`$.
- **Logarithmic correction** `LogDefect.correction M B x` $`=c(x)=M\log x+B+M\log(9/2)`$, and
  `LogDefect.corrected a M B x` $`=\tilde a(x)=a(x)-c(x)`$.
- **Defect rate** `LogDefect.rate a M B h` $`=\sup_{x\ge h}\tilde a(x)/x`$ (Mathlib's `sSup` of
  the range over $`x\in[h,\infty)`$).
- **Delayed rate** `LogDefect.delayedRate g M B T0`
  $`=D(g)=\sup_{T\ge T_0}\big(g(T)-M\log(1+T)-B-M\log(9/2)\big)/(T+1)`$ (Mathlib's `sSup` of the
  range over $`T\in[T_0,\infty)`$).
- **Even orders** `Envelope.evenOrder k` $`=p_k=2(k+1)`$, so $`p_0,p_1,p_2,\dots=2,4,6,\dots`$
- **Greatest lower bound** `IsGLB (Set.range a) C`: $`C`$ is the greatest lower bound of
  $`\{a_k : k\in\mathbb N\}`$ (no boundedness beyond this is assumed).
- **Cut inputs** `FiniteError.CutInputs f B n lam` (with $`B:\mathbb R^2\to\mathbb R`$,
  $`n\in\mathbb N`$, $`\lambda=`$ `lam`): $`n>0`$; $`f(t)\ge1`$ for $`t\ge0`$; $`f(0)=1`$;
  $`\log f(t)/t\to\lambda`$; and the cut, confinement and composition inequalities of
  [card 6](#6-quantitative-finite-time-error).

## Main results

| # | Result | Reference | Lean | Status |
|---|---|---|---|---|
| 1 | [Fekete's lemma in continuous time](#1-feketes-lemma-in-continuous-time) | Fekete (1923), historical context; Hille (1948), Theorem 6.6.1 | `RealFekete.tendsto_div_rate` | proved (gate verified at `689257126d38`) |
| 2 | [Rate transfer under a logarithmic comparison](#2-rate-transfer-under-a-logarithmic-comparison) | consequence of 1 | `RealFekete.tendsto_div_rate_of_comparison` | proved (gate verified at `689257126d38`) |
| 3 | [Fekete's lemma with a logarithmic defect](#3-feketes-lemma-with-a-logarithmic-defect) | de Bruijn–Erdős (1952), Theorem 23 (related, not formalized) | `LogDefect.tendsto_div_rate` | proved (gate verified at `689257126d38`) |
| 4 | [Delayed and multiplicative forms](#4-delayed-and-multiplicative-forms) | consequence of 3 | `LogDefect.tendsto_div_delayedRate` | proved (gate verified at `689257126d38`) |
| 5 | [Uniform envelopes and joint limits over the order](#5-uniform-envelopes-and-joint-limits-over-the-order) | none (elementary) | `Envelope.joint_limit` | proved (gate verified at `689257126d38`) |
| 6 | [Quantitative finite-time error](#6-quantitative-finite-time-error) | none (elementary) | `FiniteError.log_error` | proved (gate verified at `689257126d38`) |
| 7 | [Joint error from two orders](#7-joint-error-from-two-orders) | none (elementary) | `FiniteError.joint_error` | proved (gate verified at `689257126d38`) |

### 1. Fekete's lemma in continuous time

A nonnegative subadditive function of a continuous time that is bounded on bounded intervals grows
linearly, at the rate given by the infimum of its slopes.

**Statement.** Let $`b:\mathbb R\to\mathbb R`$ satisfy $`b(t)\ge0`$ for $`t\ge0`$,
$`b(t+u)\le b(t)+b(u)`$ for $`t,u\ge0`$, and, for every $`h>0`$, some $`M`$ with $`b(r)\le M`$
for all $`0\le r\le h`$. Then, with $`\operatorname{rate}(b)=\inf\{b(h)/h : h>0\}`$,

```math
\lim_{t\to\infty}\frac{b(t)}{t}=\operatorname{rate}(b),\qquad
\operatorname{rate}(b)\le\frac{b(t)}{t}\quad\text{for every } t>0,\qquad
\operatorname{rate}(b)\ge0.
```

**Reference.** Historical setting: M. Fekete, *Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit ganzzahligen Koeffizienten*, Math. Z. **17** (1923), 228–249, §2, Theorem II, p.233 ([DOI](https://doi.org/10.1007/BF01504345), [primary scan](https://gdz.sub.uni-goettingen.de/download/PPN266833020_0017/PPN266833020_0017___LOG_0019.pdf)). The cited result concerns Chebyshev-polynomial minimal radii; it is not a literal general sequence or real-time theorem.

A directly checked continuous-time reference is E. Hille, *Functional Analysis and Semi-Groups*, first edition, AMS Colloquium Publications **31**, 1948, Theorem 6.6.1, p.135, together with the standing measurability convention in §6.2, p.131 ([primary scan](https://archive.org/download/functionalanalys017173mbp/functionalanalys017173mbp.pdf)). For the later Hille–Phillips revised edition (1957), the publisher lists Chapter 7, pp.237–255 ([DOI](https://doi.org/10.1090/coll/031)); that edition is background only here, with no theorem correspondence asserted. The sequence theorem in pinned Mathlib is [`Subadditive.tendsto_lim`, lines155–156](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Subadditive.lean#L155).

**Compared with the reference.** Hille's positive-half-line variant gives convergence to the infimum of slopes, possibly negative infinity, for finite measurable subadditive functions. The Lean theorem instead supplies local upper bounds directly and adds nonnegativity; it does not assume measurability, and its limit is finite and nonnegative. Thus this is a related formulation with its own stated hypotheses, not a literal formalization of Hille's theorem. Mathlib's cited result has a natural-number index and a lower-bound assumption on the slopes. Fekete's cited polynomial result supplies historical context only. The primary locations above were checked in rendered scans on 2026-10-30; the pinned Mathlib statement was read from source.

**Lean.** [`GrowthRates.RealFekete.tendsto_div_rate`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/RealFekete.lean#L124); also [`GrowthRates.RealFekete.rate_le_slope`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/RealFekete.lean#L69),
[`GrowthRates.RealFekete.rate_nonneg`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/RealFekete.lean#L74).

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem tendsto_div_rate {b : ℝ → ℝ} (H : RealTimeBounds b) :
    Tendsto (fun t : ℝ => b t / t) atTop (𝓝 (rate b))

lemma rate_le_slope {b : ℝ → ℝ} (H : RealTimeBounds b) {t : ℝ}
    (ht : 0 < t) : rate b ≤ b t / t

lemma rate_nonneg {b : ℝ → ℝ} (H : RealTimeBounds b) : 0 ≤ rate b
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (gate: verified, `lean-pkg` 0.23.0, 2026-10-30) |
| Sorry count | 0 (build receipt `.lean-receipts/689257126d38-systemd-user-growth-rates-gold-native4-20261030.service-4943bb9ac67946bb91ae30cbbaaeeef4-h-2db2e0fa6029.json`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt `claim_axioms`, read from the built environment, at commit `689257126d38`) |
| Statement comparison | comparator slots `GrowthRatesAudit.GrowthRates.RealFekete.tendsto_div_rate`, `….rate_le_slope`, `….rate_nonneg` in comparator.json; comparator receipt `.lean-receipts/689257126d38-comparator.json`: result pass (26 of 26 slots) |
| Definitions judged by a person | none recorded |
| Evidence commit | `689257126d38` (receipts in `.lean-receipts/`) |
| Human review | unchecked: no independent human review asserted |
| Not covered | no rate of convergence; no measurable-only version; no version with a limit $`-\infty`$ (nonnegativity is a hypothesis) |
| Signed off | lean-pkg 0.23.0 `gate` + `comparator`, 2026-10-30 (mechanical checks only) |

</details>

### 2. Rate transfer under a logarithmic comparison

A function that stays within a logarithmic error of a Fekete function has the same growth rate,
with an explicit lower bound at every time.

**Statement.** Let $`b`$ satisfy the hypotheses of [card 1](#1-feketes-lemma-in-continuous-time),
let $`A,B\in\mathbb R`$ and $`m:\mathbb R\to\mathbb R`$. If $`b(t)\le m(t)+A+B\log(1+t)`$ for
every $`t>0`$, then

```math
t\operatorname{rate}(b)-A-B\log(1+t)\le m(t)\qquad\text{for every } t>0;
```

if in addition $`m(t)\le b(t)`$ for every $`t>0`$, then $`m(t)/t\to\operatorname{rate}(b)`$ as
$`t\to\infty`$.

Multiplicative form: let $`C\ge0`$ and $`N`$ satisfy, for $`t,u\ge0`$, $`N(t)\ge1`$,
$`N(t+u)\le N(t)N(u)`$ and $`N(t)\le e^{Ct}`$. Let $`F:\mathbb R\to\mathbb R`$ and
$`A,B\in\mathbb R`$ with, for every $`t>0`$, $`0<F(t)\le N(t)`$ and
$`\log N(t)\le\log F(t)+A+B\log(1+t)`$. Then, with $`\nu=\operatorname{rate}(\log\circ N)`$,

```math
\lim_{t\to\infty}\frac{\log F(t)}{t}=\nu
\qquad\text{and}\qquad
t\nu-A-B\log(1+t)\le\log F(t)\quad\text{for every } t>0.
```

**Reference.** No separate source: this is an elementary consequence of
[card 1](#1-feketes-lemma-in-continuous-time) (a squeeze, since $`\log(1+t)/t\to0`$).

**Compared with the reference.** Not applicable. The comparison inequalities are hypotheses; the
constants $`A,B`$ have no sign condition.

**Lean.** [`GrowthRates.RealFekete.tendsto_div_rate_of_comparison`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/RealFekete.lean#L156); also
[`GrowthRates.RealFekete.lower_bound_of_comparison`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/RealFekete.lean#L178), [`GrowthRates.RealFekete.log_rate_of_submul`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/RealFekete.lean#L219).

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem tendsto_div_rate_of_comparison {b m : ℝ → ℝ} (H : RealTimeBounds b)
    (A B : ℝ)
    (hlo : ∀ t, 0 < t → m t ≤ b t)
    (hhi : ∀ t, 0 < t → b t ≤ m t + A + B * Real.log (1 + t)) :
    Tendsto (fun t : ℝ => m t / t) atTop (𝓝 (rate b))

theorem lower_bound_of_comparison {b m : ℝ → ℝ} (H : RealTimeBounds b)
    (A B : ℝ)
    (hhi : ∀ t, 0 < t → b t ≤ m t + A + B * Real.log (1 + t))
    {t : ℝ} (ht : 0 < t) :
    t * rate b - A - B * Real.log (1 + t) ≤ m t

theorem log_rate_of_submul {N F : ℝ → ℝ} {C A B : ℝ}
    (H : SubmulInputs N C)
    (Fpos : ∀ t, 0 < t → 0 < F t)
    (lower : ∀ t, 0 < t → F t ≤ N t)
    (upper : ∀ t, 0 < t →
      Real.log (N t) ≤ Real.log (F t) + A + B * Real.log (1 + t)) :
    Tendsto (fun t : ℝ => Real.log (F t) / t) atTop
      (𝓝 (rate (fun t => Real.log (N t)))) ∧
    (∀ t, 0 < t → t * rate (fun r => Real.log (N r))
      - A - B * Real.log (1 + t) ≤ Real.log (F t))
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (gate: verified, `lean-pkg` 0.23.0, 2026-10-30) |
| Sorry count | 0 (build receipt `.lean-receipts/689257126d38-systemd-user-growth-rates-gold-native4-20261030.service-4943bb9ac67946bb91ae30cbbaaeeef4-h-2db2e0fa6029.json`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt `claim_axioms`, read from the built environment, at commit `689257126d38`) |
| Statement comparison | comparator slots `GrowthRatesAudit.GrowthRates.RealFekete.tendsto_div_rate_of_comparison`, `….lower_bound_of_comparison`, `….log_rate_of_submul` in comparator.json; comparator receipt `.lean-receipts/689257126d38-comparator.json`: result pass (26 of 26 slots) |
| Definitions judged by a person | none recorded |
| Evidence commit | `689257126d38` (receipts in `.lean-receipts/`) |
| Human review | unchecked: no independent human review asserted |
| Not covered | no rate of convergence for $`m(t)/t`$; the comparison inequalities are never derived for a concrete function |
| Signed off | lean-pkg 0.23.0 `gate` + `comparator`, 2026-10-30 (mechanical checks only) |

</details>

### 3. Fekete's lemma with a logarithmic defect

A function that is superadditive up to a logarithmic defect grows linearly, at the rate given by the
supremum of explicitly corrected slopes.

**Statement.** Let $`a:\mathbb R\to\mathbb R`$, $`M\ge0`$, $`B\in\mathbb R`$, $`h\ge1`$, and assume

```math
a(x)+a(y)-M\log(x+y)-B\le a(x+y)\qquad\text{for all } x,y\ge h.
```

With $`c(x)=M\log x+B+M\log(9/2)`$ and $`\tilde a=a-c`$:

- (balanced merge) $`\tilde a(x)+\tilde a(y)\le\tilde a(x+y)`$ for $`x,y\ge h`$ with
  $`x/2\le y\le2x`$;
- (equal blocks) $`k\,\tilde a(x)\le\tilde a(kx)`$ for $`x\ge h`$ and every integer $`k\ge1`$;
- if moreover $`B\ge0`$: $`k\,\tilde a(x)\le a(kx)`$ for $`x\ge h`$ and every integer $`k\ge1`$;
- if moreover $`B\ge0`$, $`a`$ is nondecreasing on $`[h,\infty)`$ and $`a(x)\le Cx`$ for
  $`x\ge h`$ (some $`C\in\mathbb R`$), then

```math
\lim_{t\to\infty}\frac{a(t)}{t}=\sup_{x\ge h}\frac{\tilde a(x)}{x}.
```

**Reference.** N. G. de Bruijn and P. Erdős, *Some linear and some quadratic recursion formulas. II*, Nederl. Akad. Wetensch. Proc. Ser. A **55** = Indag. Math. **14** (1952), 152–163, §7, Theorem 23, equation (7.7), p.162 ([DOI](https://doi.org/10.1016/S1385-7258(52)50021-0), [primary scan](https://users.renyi.hu/~p_erdos/1952-10.pdf)). The printed theorem and its hypotheses were checked in the rendered primary scan on 2026-10-30.

**Compared with the reference.** Their theorem concerns sequences with a positive increasing error function satisfying a finite integral of φ(t)/t² on [1,∞). The near-subadditive inequality is required for balanced integer pairs n/2 ≤ m ≤ 2n; the resulting limit may be negative infinity. This library does not formalize that theorem. It proves a continuous-time relative in the superadditive direction for the logarithmic defect M log(x+y)+B, assuming the defect inequality for all x,y ≥ h. Its limit theorem additionally assumes monotonicity and a linear upper bound and identifies the limit as the exact supremum of corrected slopes.

**Lean.** [`GrowthRates.LogDefect.tendsto_div_rate`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/LogDefect.lean#L197); also [`GrowthRates.LogDefect.balanced_merge`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/LogDefect.lean#L58),
[`GrowthRates.LogDefect.corrected_nat_blocks`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/LogDefect.lean#L79), [`GrowthRates.LogDefect.nat_blocks`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/LogDefect.lean#L127).

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem tendsto_div_rate (a : ℝ → ℝ) (M B h C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hh : 1 ≤ h)
    (hmono : MonotoneOn a (Ici h))
    (hupper : ∀ x : ℝ, h ≤ x → a x ≤ C*x)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y)) :
    Tendsto (fun t : ℝ => a t / t) atTop (𝓝 (rate a M B h))

theorem balanced_merge (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x y : ℝ) (hx : h ≤ x) (hy : h ≤ y)
    (hxy : x / 2 ≤ y) (hyx : y ≤ 2 * x) :
    corrected a M B x + corrected a M B y ≤ corrected a M B (x+y)

theorem corrected_nat_blocks (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x : ℝ) (hx : h ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * corrected a M B x ≤ corrected a M B ((k : ℝ)*x)

theorem nat_blocks (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x : ℝ) (hx : h ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * corrected a M B x ≤ a ((k : ℝ)*x)
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (gate: verified, `lean-pkg` 0.23.0, 2026-10-30) |
| Sorry count | 0 (build receipt `.lean-receipts/689257126d38-systemd-user-growth-rates-gold-native4-20261030.service-4943bb9ac67946bb91ae30cbbaaeeef4-h-2db2e0fa6029.json`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt `claim_axioms`, read from the built environment, at commit `689257126d38`) |
| Statement comparison | comparator slots `GrowthRatesAudit.GrowthRates.LogDefect.tendsto_div_rate`, `….balanced_merge`, `….corrected_nat_blocks`, `….nat_blocks` in comparator.json; comparator receipt `.lean-receipts/689257126d38-comparator.json`: result pass (26 of 26 slots) |
| Definitions judged by a person | none recorded |
| Evidence commit | `689257126d38` (receipts in `.lean-receipts/`) |
| Human review | unchecked: no independent human review asserted |
| Not covered | no general summable-defect (de Bruijn–Erdős) theorem; no rate of convergence; the defect inequality is a hypothesis |
| Signed off | lean-pkg 0.23.0 `gate` + `comparator`, 2026-10-30 (mechanical checks only) |

</details>

### 4. Delayed and multiplicative forms

The same rate theorem for the delayed merge rule $`(S,T)\mapsto S+T+1`$, and for its multiplicative
version.

**Statement.** Let $`M,B\ge0`$, $`T_0\ge0`$, $`C\in\mathbb R`$, and let $`D`$ be the delayed rate
of the [Notation](#notation). Let $`b\ge0`$ on $`[0,\infty)`$ be nondecreasing on $`[0,\infty)`$,
with $`b(t)\le C(t+1)`$ for $`t\ge T_0`$ and

```math
b(S)+b(T)-M\log(2+S+T)-B\le b(S+T+1)\qquad (S,T\ge T_0).
```

Then $`D(b)\ge0`$ and $`b(t)/t\to D(b)`$ as $`t\to\infty`$.

Multiplicative form: let $`f\ge1`$ on $`[0,\infty)`$ be nondecreasing on $`[0,\infty)`$, with
$`f(t)\le e^{C(t+1)}`$ for $`t\ge T_0`$ and

```math
\frac{f(S)\,f(T)}{\exp\big(M\log(2+S+T)+B\big)}\le f(S+T+1)\qquad (S,T\ge T_0).
```

Then $`D(\log\circ f)\ge0`$ and $`\log f(t)/t\to D(\log\circ f)`$ as $`t\to\infty`$.

**Reference.** No separate source: the delayed form is [card 3](#3-feketes-lemma-with-a-logarithmic-defect)
applied to $`x\mapsto b(x-1)`$ on $`[T_0+1,\infty)`$; for the related literature see card 3.

**Compared with the reference.** Not applicable. Nonnegativity of $`b`$ (or $`f\ge1`$) is an added
hypothesis; it gives $`D\ge0`$.

**Lean.** [`GrowthRates.LogDefect.tendsto_div_delayedRate`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/LogDefect.lean#L247); also
[`GrowthRates.LogDefect.tendsto_log_div_delayedRate`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/LogDefect.lean#L329).

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem tendsto_div_delayedRate (b : ℝ → ℝ) (M B T0 C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hT0 : 0 ≤ T0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ b t)
    (hmono : MonotoneOn b (Ici 0))
    (hupper : ∀ t : ℝ, T0 ≤ t → b t ≤ C*(t+1))
    (hnear : ∀ S T : ℝ, T0 ≤ S → T0 ≤ T →
      b S + b T - M * Real.log (2+S+T) - B ≤ b (S+T+1)) :
    0 ≤ delayedRate b M B T0 ∧
    Tendsto (fun t : ℝ => b t / t) atTop (𝓝 (delayedRate b M B T0))

theorem tendsto_log_div_delayedRate (f : ℝ → ℝ) (M B T0 C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hT0 : 0 ≤ T0)
    (hone : ∀ t : ℝ, 0 ≤ t → 1 ≤ f t)
    (hmono : MonotoneOn f (Ici 0))
    (hupper : ∀ t : ℝ, T0 ≤ t → f t ≤ Real.exp (C*(t+1)))
    (hcompose : ∀ S T : ℝ, T0 ≤ S → T0 ≤ T →
      f S*f T / Real.exp (M*Real.log (2+S+T)+B) ≤ f (S+T+1)) :
    0 ≤ delayedRate (fun t => Real.log (f t)) M B T0 ∧
    Tendsto (fun t : ℝ => Real.log (f t)/t) atTop
      (𝓝 (delayedRate (fun t => Real.log (f t)) M B T0))
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (gate: verified, `lean-pkg` 0.23.0, 2026-10-30) |
| Sorry count | 0 (build receipt `.lean-receipts/689257126d38-systemd-user-growth-rates-gold-native4-20261030.service-4943bb9ac67946bb91ae30cbbaaeeef4-h-2db2e0fa6029.json`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt `claim_axioms`, read from the built environment, at commit `689257126d38`) |
| Statement comparison | comparator slots `GrowthRatesAudit.GrowthRates.LogDefect.tendsto_div_delayedRate`, `….tendsto_log_div_delayedRate` in comparator.json; comparator receipt `.lean-receipts/689257126d38-comparator.json`: result pass (26 of 26 slots) |
| Definitions judged by a person | none recorded |
| Evidence commit | `689257126d38` (receipts in `.lean-receipts/`) |
| Human review | unchecked: no independent human review asserted |
| Not covered | no rate of convergence; the composition inequality is a hypothesis, never derived for a concrete model |
| Signed off | lean-pkg 0.23.0 `gate` + `comparator`, 2026-10-30 (mechanical checks only) |

</details>

### 5. Uniform envelopes and joint limits over the order

Fixed-order limits and one lower error uniform in the order give convergence of the order infimum.
With antitonicity in the order, they also give a joint limit as both order and time tend to infinity.
This is not uniform convergence to the same constant over all orders $`p\ge2`$.

**Statement.** Let $`a:\mathbb N\to\mathbb R`$ and let $`C`$ be the greatest lower bound of
$`\{a_k\}`$; $`p_k=2(k+1)`$.

1. (Envelope squeeze) Along any filter $`l`$ on any type: if $`e\to0`$, eventually
   $`C-e\le f`$, and for each $`k`$ eventually $`f\le v_k`$ with $`v_k\to a_k`$, then
   $`f\to C`$.

Now let $`q:\mathbb R\times\mathbb R\to\mathbb R`$ and $`e:\mathbb R\to\mathbb R`$ satisfy

```math
\text{(L)}\qquad a_k-e(T)\le q(p_k,T)\qquad\text{for all } k\in\mathbb N,\ T>0.
```

2. (Every real order) If (L) holds and $`q(r,T)\le q(p,T)`$ whenever $`T>0`$ and $`2\le p\le r`$,
   then $`C-e(T)\le q(p,T)`$ for all real $`p\ge2`$ and $`T>0`$.
3. (Sandwich) If (L) holds and, for each $`T>0`$, $`\varphi(T)`$ is the greatest lower bound of
   $`\{q(p_k,T)\}_k`$, then for $`T>0`$: $`C-e(T)\le\varphi(T)`$ and $`\varphi(T)\le q(p_k,T)`$
   for every $`k`$.
4. (Limit of the infimum) Under 3, if $`e(T)\to0`$ and $`q(p_k,T)\to a_k`$ for each $`k`$ as
   $`T\to\infty`$, then $`\varphi(T)\to C`$.
5. (Joint limit) Under the hypotheses of 2, if $`e(T)\to0`$ and $`q(p_k,T)\to a_k`$ for each
   $`k`$ as $`T\to\infty`$, then for all sequences $`P_j\to\infty`$ and $`T_j\to\infty`$,

```math
q(P_j,T_j)\to C\qquad (j\to\infty).
```

6. (Corrected infimum) For any $`C\in\mathbb R`$ and $`\varphi,e:\mathbb R\to\mathbb R`$: if
   $`C-e(T)\le\varphi(T)`$ for $`T>0`$, $`\varphi(T)\to C`$ and $`e(T)\to0`$, then
   $`\inf\{\varphi(T)+e(T) : T>0\}=C`$ (Mathlib's `sInf`).
7. (Division by time) If $`T>0`$ and $`\phi`$ is the greatest lower bound of $`\{v_k\}`$, then
   $`\phi/T`$ is the greatest lower bound of $`\{v_k/T\}`$.

**Reference.** No literature source is claimed: these are elementary order-theoretic squeeze
arguments, stated for reuse.

**Compared with the reference.** Not applicable. Antitonicity in the order and the uniform lower
error (L) are hypotheses; no convergence rate for the fixed-order upper bounds that is uniform in
the order is assumed.

**Lean.** [`GrowthRates.Envelope.joint_limit`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/Envelope.lean#L132); also [`GrowthRates.Envelope.envelope_limit`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/Envelope.lean#L61),
[`GrowthRates.Envelope.real_order_lower`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/Envelope.lean#L88), [`GrowthRates.Envelope.control_sandwich`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/Envelope.lean#L99),
[`GrowthRates.Envelope.control_limit`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/Envelope.lean#L114), [`GrowthRates.Envelope.corrected_sInf`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/Envelope.lean#L169),
[`GrowthRates.Envelope.glb_div_time`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/Envelope.lean#L176).

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem envelope_limit {β : Type*} {l : Filter β} {a : ℕ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    {f e : β → ℝ} {v : ℕ → β → ℝ}
    (he : Tendsto e l (𝓝 0))
    (hlower : ∀ᶠ x in l, C - e x ≤ f x)
    (hupper : ∀ k, ∀ᶠ x in l, f x ≤ v k x)
    (hv : ∀ k, Tendsto (v k) l (𝓝 (a k))) :
    Tendsto f l (𝓝 C)

theorem real_order_lower {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hanti : ∀ T, 0 < T → ∀ p, 2 ≤ p → ∀ r, p ≤ r → q r T ≤ q p T)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (evenOrder k) T)
    {p T : ℝ} (hp : 2 ≤ p) (hT : 0 < T) : C - e T ≤ q p T

theorem control_sandwich {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e φ : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (evenOrder k) T)
    (hφ : ∀ T, 0 < T → IsGLB (range (fun k => q (evenOrder k) T)) (φ T))
    {T : ℝ} (hT : 0 < T) :
    C - e T ≤ φ T ∧ ∀ k, φ T ≤ q (evenOrder k) T

theorem control_limit {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e φ : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (evenOrder k) T)
    (hφ : ∀ T, 0 < T → IsGLB (range (fun k => q (evenOrder k) T)) (φ T))
    (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ k, Tendsto (q (evenOrder k)) atTop (𝓝 (a k))) :
    Tendsto φ atTop (𝓝 C)

theorem joint_limit {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hanti : ∀ T, 0 < T → ∀ p, 2 ≤ p → ∀ r, p ≤ r → q r T ≤ q p T)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (evenOrder k) T)
    (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ k, Tendsto (q (evenOrder k)) atTop (𝓝 (a k)))
    (p T : ℕ → ℝ) (hp : Tendsto p atTop atTop) (hT : Tendsto T atTop atTop) :
    Tendsto (fun j => q (p j) (T j)) atTop (𝓝 C)

theorem corrected_sInf {φ e : ℝ → ℝ} {C : ℝ}
    (hlower : ∀ T, 0 < T → C - e T ≤ φ T)
    (hφ : Tendsto φ atTop (𝓝 C)) (he : Tendsto e atTop (𝓝 0)) :
    sInf ((fun T => φ T + e T) '' Ioi 0) = C

theorem glb_div_time {v : ℕ → ℝ} {φ T : ℝ} (hT : 0 < T)
    (hφ : IsGLB (range v) φ) :
    IsGLB (range (fun k => v k / T)) (φ / T)
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (gate: verified, `lean-pkg` 0.23.0, 2026-10-30) |
| Sorry count | 0 (build receipt `.lean-receipts/689257126d38-systemd-user-growth-rates-gold-native4-20261030.service-4943bb9ac67946bb91ae30cbbaaeeef4-h-2db2e0fa6029.json`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt `claim_axioms`, read from the built environment, at commit `689257126d38`) |
| Statement comparison | comparator slots `GrowthRatesAudit.GrowthRates.Envelope.envelope_limit`, `….real_order_lower`, `….control_sandwich`, `….control_limit`, `….joint_limit`, `….corrected_sInf`, `….glb_div_time` in comparator.json; comparator receipt `.lean-receipts/689257126d38-comparator.json`: result pass (26 of 26 slots) |
| Definitions judged by a person | none recorded |
| Evidence commit | `689257126d38` (receipts in `.lean-receipts/`) |
| Human review | unchecked: no independent human review asserted |
| Not covered | the joint limit is along sequences only; orders below 2 are not covered; antitonicity and (L) are never derived for a concrete family |
| Signed off | lean-pkg 0.23.0 `gate` + `comparator`, 2026-10-30 (mechanical checks only) |

</details>

### 6. Quantitative finite-time error

Cut, confinement and composition inequalities turn the growth rate of $`\log f`$ into an explicit
error at every finite time.

**Statement.** *Steps.* Let $`h>0`$ and $`b(t)/t\to\lambda`$. If $`b(t+h)\le b(t)+A`$ for all
$`t\ge r`$, then $`\lambda h\le A`$; if $`b(t)+A\le b(t+h)`$ for all $`t\ge r`$, then
$`A\le\lambda h`$.

*Finite-time bounds.* Let $`n\in\mathbb N`$, let $`f\ge1`$ on $`[0,\infty)`$ with
$`\log f(t)/t\to\lambda`$, and let $`B:\mathbb R^2\to\mathbb R`$ satisfy

```math
\begin{aligned}
&\text{(cut)} && f(T+S)\le(1+T/\delta)^n f(T)\,f(S+\delta) && (T,S\ge0,\ \delta>0),\\
&\text{(confinement)} && \min(1,\delta/T)^n f(T)\le B(T,\delta) && (T,\delta>0),\\
&\text{(composition)} && B(T,\delta)\,f(t)\le f(t+T+\delta) && (T,\delta>0,\ t\ge0).
\end{aligned}
```

Then $`\lambda\ge0`$ and, for all $`T,\delta>0`$,

```math
\lambda(T-\delta)-n\log(1+T/\delta)\le\log f(T)\le\lambda(T+\delta)+n\log\max(1,T/\delta).
```

*Optimization.* If $`n>0`$ is real, $`\lambda\ge0`$ and $`b(T)`$ satisfies these two bounds for
all $`T,\delta>0`$, then $`|b(T)-T\lambda|\le n\big(1+\log(2+T\lambda/n)\big)`$ for every
$`T>0`$.

*Conclusion.* Under the finite-time hypotheses with $`n\ge1`$ and $`f(0)=1`$,

```math
|\log f(T)-T\lambda|\le n\big(1+\log(2+T\lambda/n)\big)\qquad\text{for every } T\ge0.
```

**Reference.** No literature source is claimed. The step lemmas are the standard argument that a
one-step increment bound passes to the rate; the cut, confinement and composition inequalities are
abstract hypotheses of this library.

**Compared with the reference.** Not applicable. The rate $`\lambda`$ is an input (for example from
[card 4](#4-delayed-and-multiplicative-forms)); the error bound is a conclusion, obtained with
$`\delta=T/(1+T\lambda/n)`$.

**Lean.** [`GrowthRates.FiniteError.log_error`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/FiniteError.lean#L189); also [`GrowthRates.FiniteError.step_upper`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/FiniteError.lean#L54),
[`GrowthRates.FiniteError.step_lower`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/FiniteError.lean#L76), [`GrowthRates.FiniteError.finite_bounds`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/FiniteError.lean#L93),
[`GrowthRates.FiniteError.optimize`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/FiniteError.lean#L163).

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem log_error (f : ℝ → ℝ) (B : ℝ → ℝ → ℝ) (n : ℕ) (lam : ℝ)
    (hn : 0 < n) (hone : ∀ t, 0 ≤ t → 1 ≤ f t) (hzero : f 0 = 1)
    (hrate : Tendsto (fun t => Real.log (f t)/t) atTop (𝓝 lam))
    (hcut : ∀ T S δ : ℝ, 0 ≤ T → 0 ≤ S → 0 < δ →
      f (T+S) ≤ (1+T/δ)^n*f T*f (S+δ))
    (hconfine : ∀ T δ : ℝ, 0 < T → 0 < δ →
      (min 1 (δ/T))^n*f T ≤ B T δ)
    (hcompose : ∀ T δ t : ℝ, 0 < T → 0 < δ → 0 ≤ t →
      B T δ*f t ≤ f (t+T+δ)) :
    ∀ T : ℝ, 0 ≤ T → |Real.log (f T)-T*lam| ≤
      (n:ℝ)*(1+Real.log (2+T*lam/(n:ℝ)))

lemma step_upper (b : ℝ → ℝ) (lam r h A : ℝ) (hh : 0 < h)
    (hrate : Tendsto (fun t => b t/t) atTop (𝓝 lam))
    (hstep : ∀ t, r ≤ t → b (t+h) ≤ b t+A) : lam*h ≤ A

lemma step_lower (b : ℝ → ℝ) (lam r h A : ℝ) (hh : 0 < h)
    (hrate : Tendsto (fun t => b t/t) atTop (𝓝 lam))
    (hstep : ∀ t, r ≤ t → b t+A ≤ b (t+h)) : A ≤ lam*h

theorem finite_bounds (f : ℝ → ℝ) (B : ℝ → ℝ → ℝ) (n : ℕ) (lam : ℝ)
    (hone : ∀ t, 0 ≤ t → 1 ≤ f t)
    (hrate : Tendsto (fun t => Real.log (f t)/t) atTop (𝓝 lam))
    (hcut : ∀ T S δ : ℝ, 0 ≤ T → 0 ≤ S → 0 < δ →
      f (T+S) ≤ (1+T/δ)^n*f T*f (S+δ))
    (hconfine : ∀ T δ : ℝ, 0 < T → 0 < δ →
      (min 1 (δ/T))^n*f T ≤ B T δ)
    (hcompose : ∀ T δ t : ℝ, 0 < T → 0 < δ → 0 ≤ t →
      B T δ*f t ≤ f (t+T+δ)) :
    0 ≤ lam ∧ ∀ T δ : ℝ, 0 < T → 0 < δ →
      lam*(T-δ)-(n:ℝ)*Real.log (1+T/δ) ≤ Real.log (f T) ∧
      Real.log (f T) ≤ lam*(T+δ)+(n:ℝ)*Real.log (max 1 (T/δ))

theorem optimize (b : ℝ → ℝ) (n lam : ℝ) (hn : 0 < n) (hlam : 0 ≤ lam)
    (hbound : ∀ T δ : ℝ, 0 < T → 0 < δ →
      lam*(T-δ)-n*Real.log (1+T/δ) ≤ b T ∧
      b T ≤ lam*(T+δ)+n*Real.log (max 1 (T/δ)))
    (T : ℝ) (hT : 0 < T) :
    |b T-T*lam| ≤ n*(1+Real.log (2+T*lam/n))
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (gate: verified, `lean-pkg` 0.23.0, 2026-10-30) |
| Sorry count | 0 (build receipt `.lean-receipts/689257126d38-systemd-user-growth-rates-gold-native4-20261030.service-4943bb9ac67946bb91ae30cbbaaeeef4-h-2db2e0fa6029.json`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt `claim_axioms`, read from the built environment, at commit `689257126d38`) |
| Statement comparison | comparator slots `GrowthRatesAudit.GrowthRates.FiniteError.log_error`, `….step_upper`, `….step_lower`, `….finite_bounds`, `….optimize` in comparator.json; comparator receipt `.lean-receipts/689257126d38-comparator.json`: result pass (26 of 26 slots) |
| Definitions judged by a person | none recorded |
| Evidence commit | `689257126d38` (receipts in `.lean-receipts/`) |
| Human review | unchecked: no independent human review asserted |
| Not covered | the cut, confinement and composition inequalities and the rate are hypotheses, never derived for a concrete model; no optimality of the error is claimed |
| Signed off | lean-pkg 0.23.0 `gate` + `comparator`, 2026-10-30 (mechanical checks only) |

</details>

### 7. Joint error from two orders

Two finite-time errors, at two orders, bound a quantity squeezed between them.

**Statement.** *Sandwich.* Let $`p,n,m,z>0`$, $`0\le C\le c_m\le c_n\le M`$ and
$`x,x_n,x_m\in\mathbb R`$ with

```math
|x_n-nc_nz|\le n\big(1+\log(2+c_nz)\big),\qquad
|x_m-mc_mz|\le m\big(1+\log(2+c_mz)\big),\qquad
\frac pm\,x_m\le x\le\frac pn\,x_n.
```

Then

```math
\Big|\frac{x}{pz}-C\Big|\le c_n-C+\frac{1+\log(2+Mz)}{z}.
```

*Joint form.* Let $`f_n`$ and $`f_m`$ satisfy the cut inputs of the [Notation](#notation) at integer
orders $`n,m`$, with functions $`B_n,B_m`$ and rates $`\lambda_n,\lambda_m`$. Let $`T\ge0`$,
$`p,z>0`$, $`0\le C\le c_m\le c_n\le M`$, $`T\lambda_n=nc_nz`$, $`T\lambda_m=mc_mz`$ and
$`\frac pm\log f_m(T)\le x\le\frac pn\log f_n(T)`$. Then the same bound on
$`|x/(pz)-C|`$ holds.

**Reference.** No literature source is claimed: real arithmetic on top of
[card 6](#6-quantitative-finite-time-error).

**Compared with the reference.** Not applicable. The scaling identities and the sandwich are
hypotheses; neither finite-time error is.

**Lean.** [`GrowthRates.FiniteError.joint_error`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/FiniteError.lean#L269); also [`GrowthRates.FiniteError.sandwich_error`](https://github.com/chenle02/growth-rates-lean/blob/689257126d3859efba8a38076353c9570d1fe1f1/GrowthRates/FiniteError.lean#L212).

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem joint_error (fn fm : ℝ → ℝ) (Bn Bm : ℝ → ℝ → ℝ)
    (n m : ℕ) (ln lm T x p z C cn cm M : ℝ)
    (Hn : CutInputs fn Bn n ln) (Hm : CutInputs fm Bm m lm)
    (hT : 0 ≤ T) (hp : 0 < p) (hz : 0 < z)
    (hC : 0 ≤ C) (hCm : C ≤ cm) (hmn : cm ≤ cn) (hnM : cn ≤ M)
    (hsn : T*ln=(n:ℝ)*cn*z) (hsm : T*lm=(m:ℝ)*cm*z)
    (hlo : p/(m:ℝ)*Real.log (fm T) ≤ x)
    (hhi : x ≤ p/(n:ℝ)*Real.log (fn T)) :
    |x/(p*z)-C| ≤ cn-C+(1+Real.log (2+M*z))/z

theorem sandwich_error (x xn xm p n m z C cn cm M : ℝ)
    (hp : 0 < p) (hn : 0 < n) (hm : 0 < m) (hz : 0 < z)
    (hC : 0 ≤ C) (hCm : C ≤ cm) (hmn : cm ≤ cn) (hnM : cn ≤ M)
    (hen : |xn-n*cn*z| ≤ n*(1+Real.log (2+cn*z)))
    (hem : |xm-m*cm*z| ≤ m*(1+Real.log (2+cm*z)))
    (hlo : p/m*xm ≤ x) (hhi : x ≤ p/n*xn) :
    |x/(p*z)-C| ≤ cn-C+(1+Real.log (2+M*z))/z
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (gate: verified, `lean-pkg` 0.23.0, 2026-10-30) |
| Sorry count | 0 (build receipt `.lean-receipts/689257126d38-systemd-user-growth-rates-gold-native4-20261030.service-4943bb9ac67946bb91ae30cbbaaeeef4-h-2db2e0fa6029.json`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt `claim_axioms`, read from the built environment, at commit `689257126d38`) |
| Statement comparison | comparator slots `GrowthRatesAudit.GrowthRates.FiniteError.joint_error`, `….sandwich_error` in comparator.json; comparator receipt `.lean-receipts/689257126d38-comparator.json`: result pass (26 of 26 slots) |
| Definitions judged by a person | none recorded |
| Evidence commit | `689257126d38` (receipts in `.lean-receipts/`) |
| Human review | unchecked: no independent human review asserted |
| Not covered | the scaling identities $`T\lambda=nc\,z`$ and the sandwich of $`x`$ are hypotheses |
| Signed off | lean-pkg 0.23.0 `gate` + `comparator`, 2026-10-30 (mechanical checks only) |

</details>

## Not proved here

- No continuous-time Fekete lemma under measurability alone: local boundedness and nonnegativity
  are hypotheses.
- No de Bruijn–Erdős theorem in its general summable-error form; only the logarithmic defect
  $`M\log(x+y)+B`$ is treated.
- No rate of convergence in the Fekete lemmas (cards 1–4).
- The cut, confinement and composition inequalities, and the comparison inequalities of card 2, are
  hypotheses; they are never derived for any concrete model.
- No probabilistic or PDE content.
- Nothing about any specific stochastic equation.

<details markdown="1">
<summary>Lean implementation notes</summary>

- `sInf` and `sSup` on `ℝ` follow Mathlib's conventions (they return `0` on an empty set or a set
  unbounded in the relevant direction). The library proves the needed boundedness: the slopes of
  card 1 are bounded below by `0` (`RealFekete.slopes_bdd`), and the corrected slopes of card 3 are
  bounded above by `C` under the hypotheses of `LogDefect.tendsto_div_rate`. The value of
  `RealFekete.rate b`, `LogDefect.rate` or `LogDefect.delayedRate` for a function outside these
  hypotheses carries no meaning.
- `Envelope.evenOrder k = 2 * ((k + 1 : ℕ) : ℝ)`, so the even orders start at `2`.
- `Real.log 0 = 0` and `Real.log (-x) = Real.log x`. The finite-time uses have positive log arguments
  on their stated domains; the limit proofs use eventual positivity. No positivity at arbitrary
  negative times is asserted.
- Division by `0` is `0` in Lean; `b t / t` at `t = 0` plays no role in a limit as `t → ∞`.
- `GrowthRates/RealFekete.lean` contains two `example`s, which are boundary checks and not claims:
  the zero function has rate `0`, and `t ↦ t * t` does not satisfy `RealTimeBounds`.
- Helper declarations (for example `RealFekete.block_bound`, `LogDefect.fixed_block_lower`,
  `Envelope.corrected_infimum`, `FiniteError.progression_limit`) are listed in `claims.yaml` as
  `experimental`: proved and axiom-checked, but not stated in the Challenge.

</details>

## How this was checked

The [verification page](verification.md) and the [coverage page](coverage.md) are generated by
lean-pkg from the build and comparator receipts in `.lean-receipts/`. The comparator checks each
statement of `GrowthRates/Solution.lean` against the trusted, Mathlib-only statement of the same
name in `GrowthRates/Challenge.lean` (the slots listed in `comparator.json`), and
`GrowthRates/Axioms.lean` prints the axioms of every claim. Eight altered-contract regression
controls attempt to apply these original APIs after removing hypotheses or changing conclusions.
The strict checker requires elaborated type/application or constructor-arity mismatches and rejects setup failures.
An unsuccessful attempted proof is not a certificate that every altered statement is false.
The maintenance gate additionally audits every module-owned declaration, its complete raw type,
available value or recursor rules, universe parameters, safety and transitive axioms; a separately
compiled fixture exercises rejection of a forbidden transitive axiom. A separate same-host
source-only owned rebuild is compared byte for byte. Imported dependencies remain trusted.
The [complete maintenance checkpoint](../.lean-receipts/689257126d38-gold/README.md) preserves both original
AI review reports, their actual confidence and failures, and the exact source-bound execution
that discharges their required mechanical repairs. This is not a later model PASS or human sign-off.

## References

1. M. Fekete, *Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit
   ganzzahligen Koeffizienten*, Math. Z. **17** (1923), 228–249.
   [doi:10.1007/BF01504345](https://doi.org/10.1007/BF01504345).
2. E. Hille and R. S. Phillips, *Functional Analysis and Semi-Groups*, rev. ed., American
   Mathematical Society Colloquium Publications **31**, AMS, Providence, RI, 1957.
   [doi:10.1090/coll/031](https://doi.org/10.1090/coll/031).
3. E. Hille, *Functional Analysis and Semi-Groups*, first edition, AMS Colloquium Publications **31**, 1948, Theorem 6.6.1, p.135; standing measurability convention §6.2, p.131. [Primary scan](https://archive.org/download/functionalanalys017173mbp/functionalanalys017173mbp.pdf).
4. N. G. de Bruijn and P. Erdős, *Some linear and some quadratic recursion formulas. II*, Nederl.
   Akad. Wetensch. Proc. Ser. A **55** = Indag. Math. **14** (1952), 152–163.
   [doi:10.1016/S1385-7258(52)50021-0](https://doi.org/10.1016/S1385-7258(52)50021-0).
5. The Mathlib Community, `Mathlib/Analysis/Subadditive.lean` (`Subadditive.tendsto_lim`),
   [mathlib4 at 56a0058](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Subadditive.lean).
