module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Fekete's lemma with a logarithmic defect

A function `a : ℝ → ℝ` is *near-superadditive with a logarithmic defect* on `[h, ∞)` when

`a x + a y - M log (x + y) - B ≤ a (x + y)`   for `x, y ≥ h`,

with `M, B ≥ 0` and `h ≥ 1`. Subtracting the explicit correction
`correction M B x = M log x + B + M log (9/2)` makes balanced merges superadditive
(`balanced_merge`, for `x / 2 ≤ y ≤ 2 x`), and a balanced strong induction then gives
`k * corrected a M B x ≤ corrected a M B (k x)` for every `k ≥ 1` (`corrected_nat_blocks`).
If moreover `a` is monotone and `a x ≤ C x` on `[h, ∞)`, then (`tendsto_div_rate`)

`a t / t → rate a M B h = sup_{x ≥ h} (a x - correction M B x) / x`.

The limit is identified exactly: it is the supremum of the corrected slopes, not a liminf or
limsup bound. `tendsto_div_delayedRate` is the same statement for the delayed form
`b S + b T - M log (2 + S + T) - B ≤ b (S + T + 1)`, and `tendsto_log_div_delayedRate` is its
multiplicative version for `f ≥ 1` with `log f` in place of `b`.

This is a continuous-parameter, explicit-rate relative of the de Bruijn–Erdős theorem on
near-subadditive sequences.
-/

@[expose] public section

set_option autoImplicit false
open Set Filter Topology
namespace GrowthRates.LogDefect

/-- The logarithmic correction `M log x + B + M log (9/2)`. -/
noncomputable def correction (M B x : ℝ) : ℝ :=
  M * Real.log x + B + M * Real.log (9 / 2 : ℝ)
/-- The corrected function `a x - correction M B x`. -/
noncomputable def corrected (a : ℝ → ℝ) (M B x : ℝ) : ℝ :=
  a x - correction M B x

/-- The elementary balanced-merge ratio, with no logarithms yet. -/
theorem balanced_ratio (x y : ℝ) (_hx : 0 ≤ x) (hxy : x / 2 ≤ y)
    (hyx : y ≤ 2 * x) : (x + y) ^ 2 ≤ (9 / 2 : ℝ) * (x * y) := by
  have : 0 ≤ (y - x / 2) * (2 * x - y) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Logarithmic correction makes balanced merges genuinely superadditive. -/
theorem balanced_merge (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x y : ℝ) (hx : h ≤ x) (hy : h ≤ y)
    (hxy : x / 2 ≤ y) (hyx : y ≤ 2 * x) :
    corrected a M B x + corrected a M B y ≤ corrected a M B (x+y) := by
  have xp : 0 < x := by linarith
  have yp : 0 < y := by linarith
  have sp : 0 < x+y := by linarith
  have hr := balanced_ratio x y xp.le hxy hyx
  have hl := Real.log_le_log (sq_pos_of_pos sp) hr
  rw [Real.log_pow, Real.log_mul (by norm_num : (9/2:ℝ) ≠ 0)
    (mul_ne_zero xp.ne' yp.ne'), Real.log_mul xp.ne' yp.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl hM
  have hn := hnear x y hx hy
  dsimp [corrected, correction]
  nlinarith

/-- Balanced strong induction derives equal-block growth from the near-superadditivity
hypothesis itself; no block recurrence is assumed. -/
theorem corrected_nat_blocks (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x : ℝ) (hx : h ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * corrected a M B x ≤ corrected a M B ((k : ℝ)*x) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · simp [hk1]
    have hk2 : 2 ≤ k := by omega
    let m := k / 2
    let n := k - m
    have hm1 : 1 ≤ m := by dsimp [m]; omega
    have hn1 : 1 ≤ n := by dsimp [n, m]; omega
    have hmk : m < k := by dsimp [m]; omega
    have hnk : n < k := by dsimp [n, m]; omega
    have hmn : m + n = k := by dsimp [n, m]; omega
    have hmn' : m ≤ n := by dsimp [n, m]; omega
    have hnm : n ≤ 2*m := by dsimp [n, m]; omega
    have xp : 0 ≤ x := by linarith
    have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hxM : h ≤ (m:ℝ)*x := by nlinarith
    have hxN : h ≤ (n:ℝ)*x := by nlinarith
    have hmnR : (m:ℝ) ≤ n := by exact_mod_cast hmn'
    have hnmR : (n:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hnm
    have hbal := balanced_merge a M B h hM hh hnear ((m:ℝ)*x) ((n:ℝ)*x)
      hxM hxN (by nlinarith) (by nlinarith)
    have hm := ih m hmk hm1
    have hn := ih n hnk hn1
    have hsum : (m:ℝ)+(n:ℝ) = k := by exact_mod_cast hmn
    have heq : (m:ℝ)*x+(n:ℝ)*x=(k:ℝ)*x := by nlinarith
    rw [heq] at hbal
    calc
      (k:ℝ)*corrected a M B x = (m:ℝ)*corrected a M B x + (n:ℝ)*corrected a M B x := by rw [← hsum]; ring
      _ ≤ corrected a M B ((m:ℝ)*x) + corrected a M B ((n:ℝ)*x) := add_le_add hm hn
      _ ≤ _ := hbal

/-- The correction is nonnegative for `M, B ≥ 0` and `x ≥ 1`. -/
theorem correction_nonneg (M B x : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B) (hx : 1 ≤ x) :
    0 ≤ correction M B x := by
  have hl := Real.log_nonneg hx
  have hc := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 9/2)
  dsimp [correction]
  positivity

/-- Equal blocks with an uncorrected right side: `k * corrected a M B x ≤ a (k x)` for `k ≥ 1`, `x ≥ h`. -/
theorem nat_blocks (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x : ℝ) (hx : h ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * corrected a M B x ≤ a ((k : ℝ)*x) := by
  have hi := corrected_nat_blocks a M B h hM hh hnear x hx k hk
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have ht : 1 ≤ (k:ℝ)*x := by nlinarith
  have he := correction_nonneg M B ((k:ℝ)*x) hM hB ht
  dsimp [corrected] at hi ⊢
  linarith


/-- The precise correction divided by time tends to zero. -/
theorem correction_sublinear (M B : ℝ) :
    Tendsto (fun t : ℝ => correction M B t / t) atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hh := (hl.const_mul M).add (hi.const_mul (B + M * Real.log (9/2:ℝ)))
  have he : (fun t : ℝ => correction M B t / t) =
      (fun t : ℝ => M * (Real.log t / t) + (B + M * Real.log (9/2:ℝ))*t⁻¹) := by
    funext t
    dsimp [correction]
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  simpa using hh

/-- A fixed block bounds all sufficiently large real times by monotonicity. -/
theorem fixed_block_lower (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hh : 1 ≤ h)
    (hmono : MonotoneOn a (Ici h))
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x : ℝ) (hx : h ≤ x) :
    Tendsto (fun t : ℝ => (⌊x⁻¹*t⌋₊ : ℝ)/t * corrected a M B x)
      atTop (𝓝 (corrected a M B x / x)) ∧
    ∀ᶠ t : ℝ in atTop,
      (⌊x⁻¹*t⌋₊ : ℝ)/t * corrected a M B x ≤ a t / t := by
  have xp : 0 < x := by linarith
  constructor
  · convert (tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr xp.le)).mul_const
      (corrected a M B x) using 1; simp [div_eq_mul_inv, mul_comm]
  · filter_upwards [eventually_ge_atTop x] with t ht
    have tp : 0 < t := xp.trans_le ht
    have hratio : (1:ℝ) ≤ x⁻¹*t := by
      have hd : 1 ≤ t/x := (le_div_iff₀ xp).mpr (by simpa using ht)
      simpa [div_eq_mul_inv, mul_comm] using hd
    have hk : 1 ≤ ⌊x⁻¹*t⌋₊ := (Nat.one_le_floor_iff _).mpr hratio
    have hkR : (1:ℝ) ≤ (⌊x⁻¹*t⌋₊ : ℝ) := by exact_mod_cast hk
    have hxk : h ≤ (⌊x⁻¹*t⌋₊ : ℝ)*x := by nlinarith
    have hf := Nat.floor_le (mul_nonneg (inv_nonneg.mpr xp.le) tp.le)
    have hft : (⌊x⁻¹*t⌋₊ : ℝ)*x ≤ t := by
      calc
        _ ≤ (x⁻¹*t)*x := mul_le_mul_of_nonneg_right hf xp.le
        _ = t := by field_simp
    have hm := hmono hxk (hx.trans ht) hft
    have hb := nat_blocks a M B h hM hB hh hnear x hx ⌊x⁻¹*t⌋₊ hk
    have hd := div_le_div_of_nonneg_right (hb.trans hm) tp.le
    simpa only [div_mul_eq_mul_div] using hd

/-- The rate: the supremum over `x ≥ h` of the corrected slopes `corrected a M B x / x`. -/
noncomputable def rate (a : ℝ → ℝ) (M B h : ℝ) : ℝ :=
  sSup (range (fun x : Ici h => corrected a M B x / x))

/-- **Fekete's lemma with a logarithmic defect.** If `a` is monotone on `[h, ∞)`, `a x ≤ C x`
there, and `a x + a y - M log (x + y) - B ≤ a (x + y)` for `x, y ≥ h`, then `a t / t` converges to
`rate a M B h`. No limit and no block recurrence is assumed. -/
theorem tendsto_div_rate (a : ℝ → ℝ) (M B h C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hh : 1 ≤ h)
    (hmono : MonotoneOn a (Ici h))
    (hupper : ∀ x : ℝ, h ≤ x → a x ≤ C*x)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y)) :
    Tendsto (fun t : ℝ => a t / t) atTop (𝓝 (rate a M B h)) := by
  let r : Ici h → ℝ := fun x => corrected a M B x / x
  have hb : BddAbove (range r) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx : h ≤ (x:ℝ) := x.property
    have hp : 0 < (x:ℝ) := by linarith
    have he := correction_nonneg M B x hM hB (hh.trans hx)
    apply (div_le_iff₀ hp).mpr
    dsimp [corrected]
    linarith [hupper x hx]
  have hn : (range r).Nonempty := ⟨r ⟨h, by simp⟩, mem_range_self _⟩
  let L := rate a M B h
  change Tendsto (fun t : ℝ => a t / t) atTop (𝓝 L)
  apply tendsto_order.mpr
  constructor
  · intro z hz
    obtain ⟨_, ⟨x, rfl⟩, hzx⟩ := (lt_csSup_iff hb hn).mp hz
    obtain ⟨hl, hle⟩ := fixed_block_lower a M B h hM hB hh hmono hnear x x.property
    have hgt := hl.eventually (eventually_gt_nhds hzx)
    filter_upwards [hgt, hle] with t hgt hle
    exact hgt.trans_le hle
  · intro z hz
    have hu : Tendsto (fun t : ℝ => L + correction M B t / t) atTop (𝓝 L) := by
      simpa using tendsto_const_nhds.add (correction_sublinear M B)
    have hlt := hu.eventually (eventually_lt_nhds hz)
    filter_upwards [hlt, eventually_ge_atTop h] with t hlt ht
    have tp : 0 < t := by linarith
    have hr : corrected a M B t / t ≤ L := le_csSup hb (mem_range_self (f:=r) ⟨t,ht⟩)
    have heq : a t / t = corrected a M B t / t + correction M B t / t := by
      dsimp [corrected]; ring
    rw [heq]
    linarith


/-- The rate of the delayed form: the supremum over `T ≥ T0` of
`(b T - M log (1 + T) - B - M log (9/2)) / (T + 1)`. -/
noncomputable def delayedRate (b : ℝ → ℝ) (M B T0 : ℝ) : ℝ :=
  sSup (range (fun T : Ici T0 =>
    (b T - M * Real.log (1 + T) - B - M * Real.log (9/2:ℝ)) / (T+1)))

/-- **Delayed form.** If `b ≥ 0` is monotone on `[0, ∞)`, `b t ≤ C (t + 1)` for `t ≥ T0`, and
`b S + b T - M log (2 + S + T) - B ≤ b (S + T + 1)` for `S, T ≥ T0`, then `delayedRate b M B T0 ≥ 0`
and `b t / t` converges to it. Neither a limit nor a block recurrence is assumed. -/
theorem tendsto_div_delayedRate (b : ℝ → ℝ) (M B T0 C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hT0 : 0 ≤ T0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ b t)
    (hmono : MonotoneOn b (Ici 0))
    (hupper : ∀ t : ℝ, T0 ≤ t → b t ≤ C*(t+1))
    (hnear : ∀ S T : ℝ, T0 ≤ S → T0 ≤ T →
      b S + b T - M * Real.log (2+S+T) - B ≤ b (S+T+1)) :
    0 ≤ delayedRate b M B T0 ∧
    Tendsto (fun t : ℝ => b t / t) atTop (𝓝 (delayedRate b M B T0)) := by
  let a : ℝ → ℝ := fun x => b (x-1)
  have hh : 1 ≤ T0+1 := by linarith
  have hamono : MonotoneOn a (Ici (T0+1)) := by
    intro x hx y hy hxy
    have hx' : T0+1 ≤ x := hx
    have hy' : T0+1 ≤ y := hy
    exact hmono (by change 0 ≤ x-1; linarith) (by change 0 ≤ y-1; linarith) (by linarith)
  have haupper : ∀ x : ℝ, T0+1 ≤ x → a x ≤ C*x := by
    intro x hx
    have hu := hupper (x-1) (by linarith)
    simpa [a] using hu
  have hanear : ∀ x y : ℝ, T0+1 ≤ x → T0+1 ≤ y →
      a x+a y-M*Real.log (x+y)-B ≤ a (x+y) := by
    intro x y hx hy
    have hn := hnear (x-1) (y-1) (by linarith) (by linarith)
    have he1 : 2+(x-1)+(y-1)=x+y := by ring
    have he2 : (x-1)+(y-1)+1=x+y-1 := by ring
    simpa only [a, he1, he2] using hn
  have hlim := tendsto_div_rate a M B (T0+1) C hM hB hh hamono haupper hanear
  have hrange :
      range (fun x : Ici (T0+1) => corrected a M B x / x) =
      range (fun T : Ici T0 =>
        (b T-M*Real.log (1+T)-B-M*Real.log (9/2:ℝ))/(T+1)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      have hx : T0+1 ≤ (x:ℝ) := x.property
      refine ⟨⟨(x:ℝ)-1, by change T0 ≤ (x:ℝ)-1; linarith⟩, ?_⟩
      dsimp [corrected, correction, a]
      have he : 1+((x:ℝ)-1)=(x:ℝ) := by ring
      rw [he]
      ring
    · rintro ⟨T, rfl⟩
      have hT : T0 ≤ (T:ℝ) := T.property
      refine ⟨⟨(T:ℝ)+1, by change T0+1 ≤ (T:ℝ)+1; linarith⟩, ?_⟩
      dsimp [corrected, correction, a]
      have he : (T:ℝ)+1-1=(T:ℝ) := by ring
      rw [he, add_comm (T:ℝ) 1]
      ring
  have hrate : rate a M B (T0+1)=delayedRate b M B T0 := by
    unfold rate delayedRate
    rw [hrange]
  rw [hrate] at hlim
  have hshift : Tendsto (fun t : ℝ => t+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro z
    filter_upwards [eventually_ge_atTop z] with t ht
    linarith
  have hlimshift : Tendsto (fun t : ℝ => b t / (t+1)) atTop
      (𝓝 (delayedRate b M B T0)) := by
    simpa [Function.comp_def, a] using hlim.comp hshift
  have hfactor : Tendsto (fun t : ℝ => 1+t⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hfinal : Tendsto (fun t : ℝ => b t/t) atTop
      (𝓝 (delayedRate b M B T0)) := by
    have hm := hlimshift.mul hfactor
    have he : (fun t : ℝ => b t/(t+1)*(1+t⁻¹)) =ᶠ[atTop]
        (fun t : ℝ => b t/t) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      have ht1 : t+1 ≠ 0 := by linarith
      field_simp
    simpa using hm.congr' he
  refine ⟨?_, hfinal⟩
  apply ge_of_tendsto hfinal
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact div_nonneg (hnonneg t ht.le) ht.le


/-- **Multiplicative form.** If `f ≥ 1` is monotone on `[0, ∞)`, `f t ≤ exp (C (t + 1))` for `t ≥ T0`,
and `f S f T / exp (M log (2 + S + T) + B) ≤ f (S + T + 1)` for `S, T ≥ T0`, then `log f t / t`
converges to `delayedRate (log ∘ f) M B T0 ≥ 0`. -/
theorem tendsto_log_div_delayedRate (f : ℝ → ℝ) (M B T0 C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hT0 : 0 ≤ T0)
    (hone : ∀ t : ℝ, 0 ≤ t → 1 ≤ f t)
    (hmono : MonotoneOn f (Ici 0))
    (hupper : ∀ t : ℝ, T0 ≤ t → f t ≤ Real.exp (C*(t+1)))
    (hcompose : ∀ S T : ℝ, T0 ≤ S → T0 ≤ T →
      f S*f T / Real.exp (M*Real.log (2+S+T)+B) ≤ f (S+T+1)) :
    0 ≤ delayedRate (fun t => Real.log (f t)) M B T0 ∧
    Tendsto (fun t : ℝ => Real.log (f t)/t) atTop
      (𝓝 (delayedRate (fun t => Real.log (f t)) M B T0)) := by
  have hp : ∀ t : ℝ, 0 ≤ t → 0 < f t := by
    intro t ht
    linarith [hone t ht]
  apply tendsto_div_delayedRate (fun t => Real.log (f t)) M B T0 C hM hB hT0
  · intro t ht
    exact Real.log_nonneg (hone t ht)
  · intro x hx y hy hxy
    exact Real.log_le_log (hp x hx) (hmono hx hy hxy)
  · intro t ht
    have hh := Real.log_le_log (hp t (hT0.trans ht)) (hupper t ht)
    simpa using hh
  · intro S T hS hT
    have hSp := hp S (hT0.trans hS)
    have hTp := hp T (hT0.trans hT)
    have hh := Real.log_le_log
      (div_pos (mul_pos hSp hTp) (Real.exp_pos _)) (hcompose S T hS hT)
    rw [Real.log_div (mul_ne_zero hSp.ne' hTp.ne') (Real.exp_ne_zero _),
      Real.log_mul hSp.ne' hTp.ne', Real.log_exp] at hh
    linarith

end GrowthRates.LogDefect
