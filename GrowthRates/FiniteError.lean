module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Quantitative finite-time errors for a logarithmic growth rate

Knowing only that `log f t / t → lam` says nothing at a fixed time. This file turns three scalar
inequalities into an explicit error at every time:

* a **cut**: `f (T + S) ≤ (1 + T/δ)^n f T f (S + δ)`;
* a **confinement**: `(min 1 (δ/T))^n f T ≤ B T δ`;
* a **composition**: `B T δ f t ≤ f (t + T + δ)`.

`finite_bounds` gives two-sided bounds on `log f T` for every `δ > 0`, `optimize` chooses
`δ = T / (1 + T lam / n)`, and `log_error` concludes

`|log f T - T lam| ≤ n (1 + log (2 + T lam / n))`   for every `T ≥ 0`.

`sandwich_error` and `joint_error` combine two such orders into an error for a quantity squeezed
between them. The error estimates are conclusions; only the rate `lam` is an input.
-/

@[expose] public section

set_option autoImplicit false
open Filter Topology
namespace GrowthRates.FiniteError
/-- Along an arithmetic progression `r + j h`, `b (r + j h) / j → lam h`. -/
lemma progression_limit (b : ℝ → ℝ) (lam r h : ℝ) (hh : 0 < h)
    (hrate : Tendsto (fun t => b t / t) atTop (𝓝 lam)) :
    Tendsto (fun j : ℕ => b (r + (j : ℝ)*h) / (j : ℝ)) atTop (𝓝 (lam*h)) := by
  have ht : Tendsto (fun j : ℕ => r + (j : ℝ)*h) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const hh)
  have hs : Tendsto (fun j : ℕ => (r + (j : ℝ)*h)/(j : ℝ)) atTop (𝓝 h) := by
    have he : ∀ᶠ j : ℕ in atTop, (r + (j : ℝ)*h)/(j : ℝ) = r/(j : ℝ)+h := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
      have hn : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      field_simp
    apply Tendsto.congr' (Filter.EventuallyEq.symm he)
    simpa using (tendsto_const_div_atTop_nhds_zero_nat r).add_const h
  have he : ∀ᶠ j : ℕ in atTop,
      b (r+(j:ℝ)*h)/(j:ℝ) = (b (r+(j:ℝ)*h)/(r+(j:ℝ)*h))*((r+(j:ℝ)*h)/(j:ℝ)) := by
    filter_upwards [ht.eventually (eventually_gt_atTop (0:ℝ))] with j hj
    field_simp
  exact ((hrate.comp ht).mul hs).congr' (Filter.EventuallyEq.symm he)

/-- If `b (t + h) ≤ b t + A` for `t ≥ r` and `b t / t → lam`, then `lam h ≤ A`. -/
lemma step_upper (b : ℝ → ℝ) (lam r h A : ℝ) (hh : 0 < h)
    (hrate : Tendsto (fun t => b t/t) atTop (𝓝 lam))
    (hstep : ∀ t, r ≤ t → b (t+h) ≤ b t+A) : lam*h ≤ A := by
  have hi : ∀ j : ℕ, b (r+(j:ℝ)*h) ≤ b r+(j:ℝ)*A := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hhj := hstep (r+(j:ℝ)*h) (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
      have he : r+((j+1:ℕ):ℝ)*h = (r+(j:ℝ)*h)+h := by push_cast; ring
      rw [he]
      push_cast
      linarith
  have hu : Tendsto (fun j : ℕ => b r/(j:ℝ)+A) atTop (𝓝 A) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (b r)).add_const A
  apply le_of_tendsto_of_tendsto (progression_limit b lam r h hh hrate) hu
  filter_upwards [eventually_ge_atTop (1:ℕ)] with j hj
  have hjp : 0 < (j:ℝ) := by exact_mod_cast (by omega : 0<j)
  have hd := div_le_div_of_nonneg_right (hi j) hjp.le
  simpa [add_div, hjp.ne'] using hd

/-- If `b t + A ≤ b (t + h)` for `t ≥ r` and `b t / t → lam`, then `A ≤ lam h`. -/
lemma step_lower (b : ℝ → ℝ) (lam r h A : ℝ) (hh : 0 < h)
    (hrate : Tendsto (fun t => b t/t) atTop (𝓝 lam))
    (hstep : ∀ t, r ≤ t → b t+A ≤ b (t+h)) : A ≤ lam*h := by
  have hr : Tendsto (fun t => (-b t)/t) atTop (𝓝 (-lam)) := by
    convert hrate.neg using 1
    simp only [neg_div]
  have hs := step_upper (fun t => -b t) (-lam) r h (-A) hh hr (by
    intro t ht
    linarith [hstep t ht])
  linarith


/-- **Finite-time bounds from a cut and a confinement.** Let `f ≥ 1` on `[0, ∞)` with
`log f t / t → lam`, a cut inequality `f (T + S) ≤ (1 + T/δ)^n f T f (S + δ)`, a confinement
`(min 1 (δ/T))^n f T ≤ B T δ` and a composition `B T δ f t ≤ f (t + T + δ)`. Then `0 ≤ lam`, and for
all `T, δ > 0`: `lam (T - δ) - n log (1 + T/δ) ≤ log f T ≤ lam (T + δ) + n log (max 1 (T/δ))`.
No finite-time error is a hypothesis. -/
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
      Real.log (f T) ≤ lam*(T+δ)+(n:ℝ)*Real.log (max 1 (T/δ)) := by
  have hp : ∀ t, 0 ≤ t → 0 < f t := by intro t ht; linarith [hone t ht]
  have hlam : 0 ≤ lam := by
    apply ge_of_tendsto hrate
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact div_nonneg (Real.log_nonneg (hone t ht)) ht
  refine ⟨hlam, ?_⟩
  intro T δ hT hδ
  have ha : 0 < 1+T/δ := by positivity
  constructor
  · by_cases h : δ < T
    · have hs := step_upper (fun t => Real.log (f t)) lam δ (T-δ)
        ((n:ℝ)*Real.log (1+T/δ)+Real.log (f T)) (by linarith) hrate (by
          intro r hr
          have hc := hcut T (r-δ) δ hT.le (by linarith) hδ
          have he : T+(r-δ)=r+(T-δ) := by ring
          have hf : r-δ+δ=r := by ring
          rw [he, hf] at hc
          have hl := Real.log_le_log (hp _ (by linarith)) hc
          rw [Real.log_mul (mul_pos (pow_pos ha _) (hp T hT.le)).ne'
            (hp r (by linarith)).ne',
            Real.log_mul (pow_pos ha _).ne' (hp T hT.le).ne', Real.log_pow] at hl
          linarith)
      linarith
    · have hl := Real.log_nonneg (hone T hT.le)
      have hnlog : 0 ≤ (n:ℝ)*Real.log (1+T/δ) :=
        mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have := div_nonneg hT.le hδ.le; linarith))
      have hx : lam*(T-δ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
      linarith
  · have hm : 0 < min (1:ℝ) (δ/T) := lt_min zero_lt_one (div_pos hδ hT)
    have hBp : 0 < B T δ := lt_of_lt_of_le (mul_pos (pow_pos hm _) (hp T hT.le))
      (hconfine T δ hT hδ)
    have hs := step_lower (fun t => Real.log (f t)) lam 0 (T+δ)
      (Real.log (B T δ)) (by positivity) hrate (by
        intro t ht
        have hl := Real.log_le_log (mul_pos hBp (hp t ht)) (hcompose T δ t hT hδ ht)
        rw [Real.log_mul hBp.ne' (hp t ht).ne'] at hl
        have he : t+T+δ=t+(T+δ) := by ring
        rw [he] at hl
        linarith)
    have hc := Real.log_le_log (mul_pos (pow_pos hm _) (hp T hT.le))
      (hconfine T δ hT hδ)
    rw [Real.log_mul (pow_pos hm _).ne' (hp T hT.le).ne', Real.log_pow] at hc
    have he : Real.log (min (1:ℝ) (δ/T)) = -Real.log (max (1:ℝ) (T/δ)) := by
      by_cases h : δ ≤ T
      · rw [min_eq_right ((div_le_one hT).mpr h),
          max_eq_right ((one_le_div hδ).mpr h)]
        rw [Real.log_div hδ.ne' hT.ne', Real.log_div hT.ne' hδ.ne']
        ring
      · have h' : T ≤ δ := le_of_not_ge h
        rw [min_eq_left ((one_le_div hT).mpr h'),
          max_eq_left ((div_le_one hδ).mpr h'), Real.log_one]
        simp
    rw [he] at hc
    nlinarith


/-- **Optimized error.** Two-sided bounds of the form of `finite_bounds` for every `δ > 0` give
`|b T - T lam| ≤ n (1 + log (2 + T lam / n))`, including the boundary case `lam = 0`. -/
theorem optimize (b : ℝ → ℝ) (n lam : ℝ) (hn : 0 < n) (hlam : 0 ≤ lam)
    (hbound : ∀ T δ : ℝ, 0 < T → 0 < δ →
      lam*(T-δ)-n*Real.log (1+T/δ) ≤ b T ∧
      b T ≤ lam*(T+δ)+n*Real.log (max 1 (T/δ)))
    (T : ℝ) (hT : 0 < T) :
    |b T-T*lam| ≤ n*(1+Real.log (2+T*lam/n)) := by
  let q := T*lam/n
  have hq : 0 ≤ q := div_nonneg (mul_nonneg hT.le hlam) hn.le
  have hqp : 0 < 1+q := by linarith
  let δ := T/(1+q)
  have hd : 0 < δ := div_pos hT hqp
  have hTd : T/δ = 1+q := by dsimp [δ]; field_simp
  have hld : lam*δ = n*(q/(1+q)) := by dsimp [δ, q]; field_simp
  have hfr : q/(1+q) ≤ 1 := (div_le_one hqp).mpr (by linarith)
  have hb := hbound T δ hT hd
  rw [hTd, max_eq_right (by linarith : 1 ≤ 1+q)] at hb
  have he : 1+(1+q)=2+q := by ring
  rw [he] at hb
  have hlog : Real.log (1+q) ≤ Real.log (2+q) :=
    Real.log_le_log hqp (by linarith)
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hfr hn.le,
    mul_le_mul_of_nonneg_left hlog hn.le]

/-- **Quantitative error for `log f`.** Under the cut, confinement and composition inputs, with
`f 0 = 1` and `n > 0`: `|log f T - T lam| ≤ n (1 + log (2 + T lam / n))` for every `T ≥ 0`. -/
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
      (n:ℝ)*(1+Real.log (2+T*lam/(n:ℝ))) := by
  obtain ⟨hlam, hb⟩ := finite_bounds f B n lam hone hrate hcut hconfine hcompose
  intro T hT
  rcases eq_or_lt_of_le hT with he | ht
  · subst T
    simp only [hzero, Real.log_one, zero_mul, sub_zero, abs_zero, zero_div, add_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  · exact optimize (fun t => Real.log (f t)) n lam (by exact_mod_cast hn) hlam hb T ht


/-- **Sandwich error.** If `x` lies between `p/m · xm` and `p/n · xn`, and `xn`, `xm` are within the
optimized errors of `n cn z` and `m cm z`, with `0 ≤ C ≤ cm ≤ cn ≤ M`, then
`|x / (p z) - C| ≤ cn - C + (1 + log (2 + M z)) / z`. Pure real arithmetic. -/
theorem sandwich_error (x xn xm p n m z C cn cm M : ℝ)
    (hp : 0 < p) (hn : 0 < n) (hm : 0 < m) (hz : 0 < z)
    (hC : 0 ≤ C) (hCm : C ≤ cm) (hmn : cm ≤ cn) (hnM : cn ≤ M)
    (hen : |xn-n*cn*z| ≤ n*(1+Real.log (2+cn*z)))
    (hem : |xm-m*cm*z| ≤ m*(1+Real.log (2+cm*z)))
    (hlo : p/m*xm ≤ x) (hhi : x ≤ p/n*xn) :
    |x/(p*z)-C| ≤ cn-C+(1+Real.log (2+M*z))/z := by
  obtain ⟨henl, henu⟩ := abs_le.mp hen
  obtain ⟨heml, hemu⟩ := abs_le.mp hem
  have hcm : 0 ≤ cm := hC.trans hCm
  have hcn : 0 ≤ cn := hcm.trans hmn
  have hln : Real.log (2+cn*z) ≤ Real.log (2+M*z) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hlm : Real.log (2+cm*z) ≤ Real.log (2+M*z) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hu : x ≤ p*cn*z+p*(1+Real.log (2+M*z)) := by
    have heq : p/n*(n*cn*z+n*(1+Real.log (2+cn*z))) =
        p*cn*z+p*(1+Real.log (2+cn*z)) := by field_simp
    have hx : xn ≤ n*cn*z+n*(1+Real.log (2+cn*z)) := by linarith
    have hh := hhi.trans (mul_le_mul_of_nonneg_left hx (div_pos hp hn).le)
    rw [heq] at hh
    nlinarith
  have hl : p*cm*z-p*(1+Real.log (2+M*z)) ≤ x := by
    have hx : m*cm*z-m*(1+Real.log (2+cm*z)) ≤ xm := by linarith
    have hh := (mul_le_mul_of_nonneg_left hx (div_pos hp hm).le).trans hlo
    have heq : p/m*(m*cm*z-m*(1+Real.log (2+cm*z))) =
        p*cm*z-p*(1+Real.log (2+cm*z)) := by field_simp
    rw [heq] at hh
    nlinarith
  have hpu : x/(p*z) ≤ cn+(1+Real.log (2+M*z))/z := by
    apply (div_le_iff₀ (mul_pos hp hz)).mpr
    convert hu using 1
    field_simp
  have hpl : cm-(1+Real.log (2+M*z))/z ≤ x/(p*z) := by
    apply (le_div_iff₀ (mul_pos hp hz)).mpr
    convert hl using 1
    field_simp
  apply abs_le.mpr
  constructor <;> linarith


/-- The inputs of `log_error` for one function `f`, packaged: order `n > 0`, `f ≥ 1`, `f 0 = 1`,
the rate `lam`, and the cut, confinement and composition inequalities. -/
structure CutInputs (f : ℝ → ℝ) (B : ℝ → ℝ → ℝ) (n : ℕ) (lam : ℝ) : Prop where
  order_pos : 0 < n
  one_le : ∀ t, 0 ≤ t → 1 ≤ f t
  at_zero : f 0 = 1
  rate : Tendsto (fun t => Real.log (f t)/t) atTop (𝓝 lam)
  cut : ∀ T S δ : ℝ, 0 ≤ T → 0 ≤ S → 0 < δ →
    f (T+S) ≤ (1+T/δ)^n*f T*f (S+δ)
  confine : ∀ T δ : ℝ, 0 < T → 0 < δ → (min 1 (δ/T))^n*f T ≤ B T δ
  compose : ∀ T δ t : ℝ, 0 < T → 0 < δ → 0 ≤ t → B T δ*f t ≤ f (t+T+δ)

/-- **Joint error from two orders.** For two functions with `CutInputs` at orders `n`, `m`, the
scaling identities `T ln = n cn z`, `T lm = m cm z` and the sandwich
`p/m · log fm T ≤ x ≤ p/n · log fn T` give `|x / (p z) - C| ≤ cn - C + (1 + log (2 + M z)) / z`.
Neither finite-time error is a hypothesis. -/
theorem joint_error (fn fm : ℝ → ℝ) (Bn Bm : ℝ → ℝ → ℝ)
    (n m : ℕ) (ln lm T x p z C cn cm M : ℝ)
    (Hn : CutInputs fn Bn n ln) (Hm : CutInputs fm Bm m lm)
    (hT : 0 ≤ T) (hp : 0 < p) (hz : 0 < z)
    (hC : 0 ≤ C) (hCm : C ≤ cm) (hmn : cm ≤ cn) (hnM : cn ≤ M)
    (hsn : T*ln=(n:ℝ)*cn*z) (hsm : T*lm=(m:ℝ)*cm*z)
    (hlo : p/(m:ℝ)*Real.log (fm T) ≤ x)
    (hhi : x ≤ p/(n:ℝ)*Real.log (fn T)) :
    |x/(p*z)-C| ≤ cn-C+(1+Real.log (2+M*z))/z := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast Hn.order_pos.ne'
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast Hm.order_pos.ne'
  have en := log_error fn Bn n ln Hn.order_pos Hn.one_le Hn.at_zero Hn.rate
    Hn.cut Hn.confine Hn.compose T hT
  have em := log_error fm Bm m lm Hm.order_pos Hm.one_le Hm.at_zero Hm.rate
    Hm.cut Hm.confine Hm.compose T hT
  rw [hsn] at en
  rw [hsm] at em
  have hnq : (n:ℝ)*cn*z/(n:ℝ)=cn*z := by field_simp
  have hmq : (m:ℝ)*cm*z/(m:ℝ)=cm*z := by field_simp
  rw [hnq] at en
  rw [hmq] at em
  exact sandwich_error x (Real.log (fn T)) (Real.log (fm T)) p n m z C cn cm M hp
    (by exact_mod_cast Hn.order_pos) (by exact_mod_cast Hm.order_pos) hz hC hCm hmn hnM
    en em hlo hhi

end GrowthRates.FiniteError
