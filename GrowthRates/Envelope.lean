module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.Linarith

/-!
# Uniform envelopes and joint limits over an order parameter

A two-parameter family `q p T` (an order `p ≥ 2` and a time `T > 0`) often has a limit as
`T → ∞` at each fixed even order, while the statement one wants is uniform in the order, or joint
in `(p, T)`. This file derives such statements from fixed-order information:

* `envelope_limit`: an abstract squeeze between one vanishing lower error and a family of upper
  envelopes converging separately to values whose greatest lower bound is `C`;
* `real_order_lower`: monotonicity in the order transfers even-order lower bounds to every real
  order `p ≥ 2` (`evenOrder k = 2 (k + 1)`);
* `control_sandwich`, `control_limit`: for the infimum `φ T` over even orders at a fixed time,
  `φ T → C`;
* `joint_limit`: `q (p j) (T j) → C` along every pair of sequences with `p j → ∞`, `T j → ∞`;
* `corrected_infimum`, `corrected_sInf`: the infimum of `φ T + e T` over `T > 0` is exactly `C`;
* `glb_div_time`: division by a positive time preserves a greatest lower bound.

In each statement the limit or infimum in the conclusion is derived, never assumed.
-/

@[expose] public section

set_option autoImplicit false
open Filter Set
open scoped Topology
namespace GrowthRates.Envelope

/-- The even orders `2, 4, 6, …`: `evenOrder k = 2 (k + 1)`. -/
def evenOrder (k : ℕ) : ℝ := 2 * (k + 1 : ℕ)

/-- Every even order is at least `2`. -/
lemma evenOrder_ge_two (k : ℕ) : 2 ≤ evenOrder k := by
  unfold evenOrder
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  linarith

/-- Every real `p` is at most some even order. -/
lemma exists_evenOrder_ge (p : ℝ) : ∃ k, p ≤ evenOrder k := by
  obtain ⟨k, hk⟩ := exists_nat_gt p
  refine ⟨k, ?_⟩
  unfold evenOrder
  push_cast
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

/-- **Envelope squeeze.** If `C - e x ≤ f x` with `e → 0`, and for each `k` eventually
`f x ≤ v k x` with `v k → a k`, where `C` is the greatest lower bound of the `a k`, then `f → C`.
Neither the limit of `f` nor an upper rate uniform in `k` is a hypothesis. -/
theorem envelope_limit {β : Type*} {l : Filter β} {a : ℕ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    {f e : β → ℝ} {v : ℕ → β → ℝ}
    (he : Tendsto e l (𝓝 0))
    (hlower : ∀ᶠ x in l, C - e x ≤ f x)
    (hupper : ∀ k, ∀ᶠ x in l, f x ≤ v k x)
    (hv : ∀ k, Tendsto (v k) l (𝓝 (a k))) :
    Tendsto f l (𝓝 C) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hh : Tendsto (fun x => C - e x) l (𝓝 C) := by
      simpa using (tendsto_const_nhds.sub he)
    filter_upwards [(tendsto_order.mp hh).1 b hb, hlower] with x hx hx'
    exact lt_of_lt_of_le hx hx'
  · intro b hb
    obtain ⟨k, hk⟩ : ∃ k, a k < b := by
      by_contra h
      push Not at h
      have : b ≤ C := hC.2 (by rintro y ⟨k, rfl⟩; exact h k)
      exact (not_le_of_gt hb) this
    filter_upwards [(tendsto_order.mp (hv k)).2 b hk, hupper k] with x hx hx'
    exact lt_of_le_of_lt hx' hx

/-- **Every real order.** If `q r T` is antitone in `r ≥ 2` and each even order satisfies
`a k - e T ≤ q (evenOrder k) T`, then `C - e T ≤ q p T` for every real `p ≥ 2`, where `C` is the
greatest lower bound of the `a k`. -/
theorem real_order_lower {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hanti : ∀ T, 0 < T → ∀ p, 2 ≤ p → ∀ r, p ≤ r → q r T ≤ q p T)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (evenOrder k) T)
    {p T : ℝ} (hp : 2 ≤ p) (hT : 0 < T) : C - e T ≤ q p T := by
  obtain ⟨k, hk⟩ := exists_evenOrder_ge p
  have hc : C ≤ a k := hC.1 (mem_range_self k)
  exact (sub_le_sub_right hc _).trans ((hlower k T hT).trans (hanti T hT p hp _ hk))

/-- **Sandwich at a fixed time.** If `φ T` is the greatest lower bound of the even-order values
`q (evenOrder k) T`, the uniform lower bounds pass to `φ T`. No long-time limit is assumed. -/
theorem control_sandwich {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e φ : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (evenOrder k) T)
    (hφ : ∀ T, 0 < T → IsGLB (range (fun k => q (evenOrder k) T)) (φ T))
    {T : ℝ} (hT : 0 < T) :
    C - e T ≤ φ T ∧ ∀ k, φ T ≤ q (evenOrder k) T := by
  constructor
  · apply (hφ T hT).2
    rintro y ⟨k, rfl⟩
    exact (sub_le_sub_right (hC.1 (mem_range_self k)) _).trans (hlower k T hT)
  · intro k
    exact (hφ T hT).1 (mem_range_self k)

/-- **Limit of the infimum.** `φ T → C` follows from the fixed-order limits and one lower error
`e T → 0` uniform in the order; no upper estimate uniform in the order is needed. -/
theorem control_limit {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e φ : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (evenOrder k) T)
    (hφ : ∀ T, 0 < T → IsGLB (range (fun k => q (evenOrder k) T)) (φ T))
    (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ k, Tendsto (q (evenOrder k)) atTop (𝓝 (a k))) :
    Tendsto φ atTop (𝓝 C) := by
  apply envelope_limit hC he
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (control_sandwich hC hlower hφ hT).1
  · intro k
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (control_sandwich hC hlower hφ hT).2 k
  · exact hq

/-- **Joint limit along sequences.** If `q r T` is antitone in the order `r ≥ 2`, then
`q (p j) (T j) → C` whenever `p j → ∞` and `T j → ∞`. Each fixed-order limit is used only at that
fixed order before the infimum is taken. -/
theorem joint_limit {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hanti : ∀ T, 0 < T → ∀ p, 2 ≤ p → ∀ r, p ≤ r → q r T ≤ q p T)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (evenOrder k) T)
    (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ k, Tendsto (q (evenOrder k)) atTop (𝓝 (a k)))
    (p T : ℕ → ℝ) (hp : Tendsto p atTop atTop) (hT : Tendsto T atTop atTop) :
    Tendsto (fun j => q (p j) (T j)) atTop (𝓝 C) := by
  apply envelope_limit hC (he.comp hT)
  · filter_upwards [hp.eventually (eventually_ge_atTop (2 : ℝ)),
      hT.eventually (eventually_gt_atTop (0 : ℝ))] with j hpj hTj
    exact real_order_lower hC hanti hlower hpj hTj
  · intro k
    filter_upwards [hp.eventually (eventually_ge_atTop (evenOrder k)),
      hT.eventually (eventually_gt_atTop (0 : ℝ))] with j hpj hTj
    exact hanti _ hTj _ (evenOrder_ge_two k) _ hpj
  · intro k
    exact (hq k).comp hT

/-- **Corrected infimum.** If `C - e T ≤ φ T`, `φ T → C` and `e T → 0`, then the greatest lower
bound of `φ T + e T` over `T > 0` is exactly `C`. -/
theorem corrected_infimum {φ e : ℝ → ℝ} {C : ℝ}
    (hlower : ∀ T, 0 < T → C - e T ≤ φ T)
    (hφ : Tendsto φ atTop (𝓝 C)) (he : Tendsto e atTop (𝓝 0)) :
    IsGLB ((fun T => φ T + e T) '' Ioi 0) C := by
  constructor
  · rintro y ⟨T, hT, rfl⟩
    have := hlower T hT
    linarith
  · intro b hb
    have ht : Tendsto (fun T => φ T + e T) atTop (𝓝 C) := by
      simpa using hφ.add he
    apply ge_of_tendsto ht
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hb ⟨T, hT, rfl⟩

/-- Concrete sInf version, including the nonempty positive-time domain. -/
theorem corrected_sInf {φ e : ℝ → ℝ} {C : ℝ}
    (hlower : ∀ T, 0 < T → C - e T ≤ φ T)
    (hφ : Tendsto φ atTop (𝓝 C)) (he : Tendsto e atTop (𝓝 0)) :
    sInf ((fun T => φ T + e T) '' Ioi 0) = C := by
  exact (corrected_infimum hlower hφ he).csInf_eq ⟨φ 1 + e 1, 1, by norm_num, rfl⟩

/-- Division by a positive `T` preserves a greatest lower bound. -/
theorem glb_div_time {v : ℕ → ℝ} {φ T : ℝ} (hT : 0 < T)
    (hφ : IsGLB (range v) φ) :
    IsGLB (range (fun k => v k / T)) (φ / T) := by
  constructor
  · rintro y ⟨k, rfl⟩
    exact div_le_div_of_nonneg_right (hφ.1 (mem_range_self k)) hT.le
  · intro b hb
    apply (le_div_iff₀ hT).mpr
    apply hφ.2
    rintro y ⟨k, rfl⟩
    exact (le_div_iff₀ hT).mp (hb (mem_range_self k))

end GrowthRates.Envelope
