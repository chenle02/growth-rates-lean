module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Fekete's lemma in continuous time

Mathlib's `Subadditive.tendsto_lim` is Fekete's lemma for sequences `u : ℕ → ℝ`. This file proves
the continuous-time version for a function `b : ℝ → ℝ` on the nonnegative reals: if `b` is
nonnegative, subadditive (`b (t + u) ≤ b t + b u` for `t, u ≥ 0`) and bounded above on every
interval `[0, h]`, then

`b t / t → rate b = inf_{h > 0} b h / h` as `t → ∞`.

Neither the limit nor its value is a hypothesis. Local boundedness replaces the measurability
assumption of the classical continuous-time statement.

Two consequences transfer the rate to a comparable function:

* `tendsto_div_rate_of_comparison`: if `m t ≤ b t ≤ m t + A + B log (1 + t)` for `t > 0`,
  then `m t / t → rate b`;
* `lower_bound_of_comparison`: under the upper comparison alone, `t * rate b - A - B log (1 + t) ≤ m t`
  for every `t > 0` (a finite-time bound, not a limit).

The structure `SubmulInputs` packages the usual multiplicative input: `1 ≤ N t`,
`N (t + u) ≤ N t * N u` and `N t ≤ exp (C t)`. Then `log ∘ N` satisfies `RealTimeBounds`
(`log_realTimeBounds`), and `log_rate_of_submul` gives the rate of `log F` for any `F` with
`F ≤ N` and `log N ≤ log F + A + B log (1 + t)`.
-/

@[expose] public section

set_option autoImplicit false
open Filter Set
open scoped Topology
namespace GrowthRates.RealFekete

/-- Fekete hypotheses on nonnegative real times: nonnegativity, subadditivity and an upper bound
on every bounded interval `[0, h]`. -/
structure RealTimeBounds (b : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ t → 0 ≤ b t
  subadd : ∀ t u, 0 ≤ t → 0 ≤ u → b (t + u) ≤ b t + b u
  localUpper : ∀ h, 0 < h → ∃ M, ∀ r, 0 ≤ r → r ≤ h → b r ≤ M

/-- The Fekete rate `inf_{h > 0} b h / h` (Mathlib's `sInf` convention). -/
noncomputable def rate (b : ℝ → ℝ) : ℝ :=
  sInf ((fun h : ℝ => b h / h) '' Ioi 0)

/-- The set of slopes `b h / h`, `h > 0`, is nonempty. -/
lemma slopes_nonempty (b : ℝ → ℝ) :
    ((fun h : ℝ => b h / h) '' Ioi 0).Nonempty :=
  ⟨b 1 / 1, (1 : ℝ), by change (0 : ℝ) < 1; exact zero_lt_one, rfl⟩

/-- Under `RealTimeBounds b` the slopes `b h / h`, `h > 0`, are bounded below by `0`. -/
lemma slopes_bdd {b : ℝ → ℝ} (H : RealTimeBounds b) :
    BddBelow ((fun h : ℝ => b h / h) '' Ioi 0) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  exact div_nonneg (H.nonneg h (le_of_lt hh)) (le_of_lt hh)

/-- The rate is at most every slope: `rate b ≤ b t / t` for `t > 0`. -/
lemma rate_le_slope {b : ℝ → ℝ} (H : RealTimeBounds b) {t : ℝ}
    (ht : 0 < t) : rate b ≤ b t / t :=
  csInf_le (slopes_bdd H) ⟨t, ht, rfl⟩

/-- Under `RealTimeBounds b` the rate is nonnegative. -/
lemma rate_nonneg {b : ℝ → ℝ} (H : RealTimeBounds b) : 0 ≤ rate b := by
  apply le_csInf (slopes_nonempty b)
  rintro _ ⟨t, ht, rfl⟩
  exact div_nonneg (H.nonneg t (le_of_lt ht)) (le_of_lt ht)

/-- Iterated subadditivity: `b (k h + r) ≤ k b h + b r` for `h, r ≥ 0` and `k : ℕ`. -/
lemma multiple_remainder {b : ℝ → ℝ} (H : RealTimeBounds b)
    (h r : ℝ) (hh : 0 ≤ h) (hr : 0 ≤ r) (k : ℕ) :
    b ((k : ℝ) * h + r) ≤ (k : ℝ) * b h + b r := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 0 ≤ (k : ℝ) * h + r := add_nonneg (mul_nonneg (Nat.cast_nonneg k) hh) hr
    calc
      b (((k + 1 : ℕ) : ℝ) * h + r) = b (h + ((k : ℝ) * h + r)) := by
        congr 1
        push_cast
        ring
      _ ≤ b h + b ((k : ℝ) * h + r) := H.subadd _ _ hh hk
      _ ≤ b h + ((k : ℝ) * b h + b r) := add_le_add le_rfl ih
      _ = ((k + 1 : ℕ) : ℝ) * b h + b r := by push_cast; ring

/-- A block estimate `b t / t ≤ b h / h + M / t`, derived from subadditivity and the local bound. -/
lemma block_bound {b : ℝ → ℝ} (H : RealTimeBounds b) {h : ℝ} (hh : 0 < h) :
    ∃ M : ℝ, ∀ t : ℝ, 0 < t → b t / t ≤ b h / h + M / t := by
  obtain ⟨M, hM⟩ := H.localUpper h hh
  refine ⟨M, fun t ht => ?_⟩
  let k : ℕ := ⌊t / h⌋₊
  have hk : (k : ℝ) ≤ t / h := Nat.floor_le (div_nonneg ht.le hh.le)
  have hkt : (k : ℝ) * h ≤ t := (le_div_iff₀ hh).mp hk
  have hrem : 0 ≤ t - (k : ℝ) * h := sub_nonneg.mpr hkt
  have hfloor : t / h < (k : ℝ) + 1 := Nat.lt_floor_add_one (t / h)
  have hremh : t - (k : ℝ) * h ≤ h := by
    have := (div_lt_iff₀ hh).mp hfloor
    nlinarith
  have hb := multiple_remainder H h (t - (k : ℝ) * h) hh.le hrem k
  have hb' : b t ≤ (k : ℝ) * b h + M := by
    have heq : (k : ℝ) * h + (t - (k : ℝ) * h) = t := by ring
    rw [heq] at hb
    exact hb.trans (add_le_add le_rfl (hM _ hrem hremh))
  have hmul : (k : ℝ) * b h ≤ (t / h) * b h :=
    mul_le_mul_of_nonneg_right hk (H.nonneg h hh.le)
  have hnum : b t ≤ (t / h) * b h + M := hb'.trans (add_le_add hmul le_rfl)
  apply (div_le_iff₀ ht).2
  calc
    b t ≤ t / h * b h + M := hnum
    _ = (b h / h + M / t) * t := by field_simp

/-- **Fekete's lemma in continuous time.** Under `RealTimeBounds b`, `b t / t` converges to
`rate b` as `t → ∞`. Neither the limit nor its value is a hypothesis. -/
theorem tendsto_div_rate {b : ℝ → ℝ} (H : RealTimeBounds b) :
    Tendsto (fun t : ℝ => b t / t) atTop (𝓝 (rate b)) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro l hl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact hl.trans_le (rate_le_slope H ht)
  · intro L hL
    obtain ⟨_, ⟨h, hh, rfl⟩, hslope⟩ :=
      exists_lt_of_csInf_lt (slopes_nonempty b) hL
    obtain ⟨M, hM⟩ := block_bound H hh
    have hlim : Tendsto (fun t : ℝ => b h / h + M / t) atTop (𝓝 (b h / h)) := by
      have hdiv : Tendsto (fun t : ℝ => M / t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using (tendsto_const_nhds (x := b h / h)).add hdiv
    filter_upwards [hlim.eventually (gt_mem_nhds hslope), eventually_gt_atTop (0 : ℝ)] with t ht ht0
    exact (hM t ht0).trans_lt ht

/-- `(A + B log (1 + t)) / t → 0` as `t → ∞`. -/
lemma logarithmic_error_vanishes (A B : ℝ) :
    Tendsto (fun t : ℝ => (A + B * Real.log (1 + t)) / t) atTop (𝓝 0) := by
  have hshift : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_id
  have hlog : Tendsto (fun t : ℝ => Real.log (1 + t) / t) atTop (𝓝 0) := by
    simpa [Function.comp_def, add_assoc, add_comm, add_left_comm] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hshift
  have hA : Tendsto (fun t : ℝ => A / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have := hA.add (hlog.const_mul B)
  simpa [add_div, mul_div_assoc] using this

/-- **Rate transfer.** If `m t ≤ b t ≤ m t + A + B log (1 + t)` for `t > 0`, then `m t / t`
converges to the Fekete rate of `b`. -/
theorem tendsto_div_rate_of_comparison {b m : ℝ → ℝ} (H : RealTimeBounds b)
    (A B : ℝ)
    (hlo : ∀ t, 0 < t → m t ≤ b t)
    (hhi : ∀ t, 0 < t → b t ≤ m t + A + B * Real.log (1 + t)) :
    Tendsto (fun t : ℝ => m t / t) atTop (𝓝 (rate b)) := by
  have hb := tendsto_div_rate H
  have he := logarithmic_error_vanishes A B
  have hlower : Tendsto (fun t : ℝ => b t / t - (A + B * Real.log (1 + t)) / t)
      atTop (𝓝 (rate b)) := by simpa using hb.sub he
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro l hl
    filter_upwards [hlower.eventually (lt_mem_nhds hl), eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have hcomp : b t / t - (A + B * Real.log (1 + t)) / t ≤ m t / t := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith [hhi t ht0]) ht0.le
    exact ht.trans_le hcomp
  · intro L hL
    filter_upwards [hb.eventually (gt_mem_nhds hL), eventually_gt_atTop (0 : ℝ)] with t ht ht0
    exact (div_le_div_of_nonneg_right (hlo t ht0) ht0.le).trans_lt ht

/-- **Finite-time lower bound.** Under the upper comparison, `t * rate b - A - B log (1 + t) ≤ m t`
for every `t > 0`. No large-time limit is assumed. -/
theorem lower_bound_of_comparison {b m : ℝ → ℝ} (H : RealTimeBounds b)
    (A B : ℝ)
    (hhi : ∀ t, 0 < t → b t ≤ m t + A + B * Real.log (1 + t))
    {t : ℝ} (ht : 0 < t) :
    t * rate b - A - B * Real.log (1 + t) ≤ m t := by
  have hslope := (le_div_iff₀ ht).mp (rate_le_slope H ht)
  nlinarith [hhi t ht]


/-- Multiplicative inputs: `0 ≤ C`, `1 ≤ N t`, submultiplicativity on `t, u ≥ 0` and the
exponential bound `N t ≤ exp (C t)`. -/
structure SubmulInputs (N : ℝ → ℝ) (C : ℝ) : Prop where
  Cnonneg : 0 ≤ C
  one_le : ∀ t, 0 ≤ t → 1 ≤ N t
  submul : ∀ t u, 0 ≤ t → 0 ≤ u → N (t + u) ≤ N t * N u
  expUpper : ∀ t, 0 ≤ t → N t ≤ Real.exp (C * t)

/-- The logarithm of a function with `SubmulInputs` satisfies the Fekete hypotheses. -/
lemma log_realTimeBounds {N : ℝ → ℝ} {C : ℝ} (H : SubmulInputs N C) :
    RealTimeBounds (fun t => Real.log (N t)) := by
  have hpos : ∀ t, 0 ≤ t → 0 < N t := fun t ht => lt_of_lt_of_le zero_lt_one (H.one_le t ht)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact Real.log_nonneg (H.one_le t ht)
  · intro t u ht hu
    calc
      Real.log (N (t + u)) ≤ Real.log (N t * N u) :=
        Real.log_le_log (hpos _ (add_nonneg ht hu)) (H.submul t u ht hu)
      _ = Real.log (N t) + Real.log (N u) :=
        Real.log_mul (ne_of_gt (hpos t ht)) (ne_of_gt (hpos u hu))
  · intro h hh
    refine ⟨C * h, fun r hr hrh => ?_⟩
    calc
      Real.log (N r) ≤ Real.log (Real.exp (C * r)) :=
        Real.log_le_log (hpos r hr) (H.expUpper r hr)
      _ = C * r := Real.log_exp _
      _ ≤ C * h := mul_le_mul_of_nonneg_left hrh H.Cnonneg

/-- **Logarithmic rate of a comparable function.** If `N` has `SubmulInputs`, `0 < F t ≤ N t` and
`log N t ≤ log F t + A + B log (1 + t)` for `t > 0`, then `log F t / t` converges to the Fekete rate
of `log ∘ N`, and `t * rate (log ∘ N) - A - B log (1 + t) ≤ log F t` for every `t > 0`. -/
theorem log_rate_of_submul {N F : ℝ → ℝ} {C A B : ℝ}
    (H : SubmulInputs N C)
    (Fpos : ∀ t, 0 < t → 0 < F t)
    (lower : ∀ t, 0 < t → F t ≤ N t)
    (upper : ∀ t, 0 < t →
      Real.log (N t) ≤ Real.log (F t) + A + B * Real.log (1 + t)) :
    Tendsto (fun t : ℝ => Real.log (F t) / t) atTop
      (𝓝 (rate (fun t => Real.log (N t)))) ∧
    (∀ t, 0 < t → t * rate (fun r => Real.log (N r))
      - A - B * Real.log (1 + t) ≤ Real.log (F t)) := by
  have Hb := log_realTimeBounds H
  constructor
  · exact tendsto_div_rate_of_comparison Hb A B
      (fun t ht => Real.log_le_log (Fpos t ht) (lower t ht)) upper
  · intro t ht
    exact lower_bound_of_comparison Hb A B upper ht

/-- At `t = 0` the lower bound holds when the comparison is supplied there. -/
theorem lower_bound_at_zero {b m : ℝ → ℝ} (H : RealTimeBounds b)
    (A B : ℝ) (hzero : b 0 ≤ m 0 + A + B * Real.log (1 + 0)) :
    (0 : ℝ) * rate b - A - B * Real.log (1 + 0) ≤ m 0 := by
  have hb := H.nonneg 0 le_rfl
  simp only [add_zero, Real.log_one, mul_zero, zero_mul, sub_zero, zero_sub] at *
  linarith

/-- Boundary check: the zero function has rate zero. -/
example : rate (fun _ : ℝ => 0) = 0 := by
  have H : RealTimeBounds (fun _ : ℝ => 0) := by
    refine ⟨fun _ _ => le_rfl, fun _ _ _ _ => by simp, ?_⟩
    exact fun _ _ => ⟨0, fun _ _ _ => le_rfl⟩
  apply le_antisymm
  · simpa using rate_le_slope H (t := 1) zero_lt_one
  · exact rate_nonneg H

/-- Boundary check: quadratic growth is not subadditive. -/
example : ¬ RealTimeBounds (fun t : ℝ => t * t) := by
  intro H
  have := H.subadd 1 1 zero_le_one zero_le_one
  norm_num at this

end GrowthRates.RealFekete
