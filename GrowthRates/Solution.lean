module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib
public import GrowthRates

@[expose] public section

/-!
# Comparator Solution (untrusted)

Restates every theorem of `GrowthRates.Challenge` with the same name and the same statement text,
and proves it from the library declaration named in its docstring: by `exact`, assembling the
library's hypothesis structures (`RealTimeBounds`, `SubmulInputs`, `CutInputs`) from the unfolded
fields. Docstrings are copied from the Challenge.

Every library definition used by a statement is written out (the docstring of each theorem names
the library declaration and the definitions unfolded):

* `RealFekete.RealTimeBounds b`: its three fields `0 ≤ b t` (`t ≥ 0`),
  `b (t + u) ≤ b t + b u` (`t, u ≥ 0`) and `∀ h > 0, ∃ M, ∀ r ∈ [0, h], b r ≤ M`;
* `RealFekete.rate b = sInf ((fun h => b h / h) '' Set.Ioi 0)`;
* `RealFekete.SubmulInputs N C`: its four fields;
* `LogDefect.correction M B x = M * log x + B + M * log (9 / 2)`,
  `LogDefect.corrected a M B x = a x - correction M B x`;
* `LogDefect.rate a M B h = sSup (Set.range fun x : Set.Ici h => corrected a M B x / x)`;
* `LogDefect.delayedRate b M B T0 =
  sSup (Set.range fun T : Set.Ici T0 => (b T - M * log (1 + T) - B - M * log (9 / 2)) / (T + 1))`;
* `Envelope.evenOrder k = 2 * ((k + 1 : ℕ) : ℝ)`;
* `FiniteError.CutInputs f B n lam`: its seven fields.

Name convention: a slot `GrowthRatesAudit.<D>` is the library declaration `<D>`.
-/

open Filter Set
open scoped Topology

/-! ## Fekete's lemma in continuous time (`GrowthRates.RealFekete`) -/

namespace GrowthRatesAudit.GrowthRates.RealFekete

/-- **Fekete's lemma in continuous time.** If `b` is nonnegative and subadditive on `[0, ∞)` and
bounded above on every `[0, h]`, then `b t / t → inf_{h > 0} b h / h`.
Library: `GrowthRates.RealFekete.tendsto_div_rate` (unfolds `RealTimeBounds`, `rate`). -/
theorem tendsto_div_rate {b : ℝ → ℝ}
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ b t)
    (hsubadd : ∀ t u, 0 ≤ t → 0 ≤ u → b (t + u) ≤ b t + b u)
    (hlocal : ∀ h, 0 < h → ∃ M, ∀ r, 0 ≤ r → r ≤ h → b r ≤ M) :
    Tendsto (fun t : ℝ => b t / t) atTop (𝓝 (sInf ((fun h : ℝ => b h / h) '' Ioi 0))) := by
  exact _root_.GrowthRates.RealFekete.tendsto_div_rate ⟨hnonneg, hsubadd, hlocal⟩

/-- The infimum `inf_{h > 0} b h / h` is at most every slope `b t / t`, `t > 0`.
Library: `GrowthRates.RealFekete.rate_le_slope` (unfolds `RealTimeBounds`, `rate`). -/
theorem rate_le_slope {b : ℝ → ℝ}
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ b t)
    (hsubadd : ∀ t u, 0 ≤ t → 0 ≤ u → b (t + u) ≤ b t + b u)
    (hlocal : ∀ h, 0 < h → ∃ M, ∀ r, 0 ≤ r → r ≤ h → b r ≤ M)
    {t : ℝ} (ht : 0 < t) :
    sInf ((fun h : ℝ => b h / h) '' Ioi 0) ≤ b t / t := by
  exact _root_.GrowthRates.RealFekete.rate_le_slope ⟨hnonneg, hsubadd, hlocal⟩ ht

/-- The infimum `inf_{h > 0} b h / h` is nonnegative.
Library: `GrowthRates.RealFekete.rate_nonneg` (unfolds `RealTimeBounds`, `rate`). -/
theorem rate_nonneg {b : ℝ → ℝ}
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ b t)
    (hsubadd : ∀ t u, 0 ≤ t → 0 ≤ u → b (t + u) ≤ b t + b u)
    (hlocal : ∀ h, 0 < h → ∃ M, ∀ r, 0 ≤ r → r ≤ h → b r ≤ M) :
    0 ≤ sInf ((fun h : ℝ => b h / h) '' Ioi 0) := by
  exact _root_.GrowthRates.RealFekete.rate_nonneg ⟨hnonneg, hsubadd, hlocal⟩

/-- **Rate transfer.** If `m t ≤ b t ≤ m t + A + B log (1 + t)` for `t > 0`, then `m t / t`
converges to the Fekete rate of `b`.
Library: `GrowthRates.RealFekete.tendsto_div_rate_of_comparison` (unfolds `RealTimeBounds`,
`rate`). -/
theorem tendsto_div_rate_of_comparison {b m : ℝ → ℝ}
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ b t)
    (hsubadd : ∀ t u, 0 ≤ t → 0 ≤ u → b (t + u) ≤ b t + b u)
    (hlocal : ∀ h, 0 < h → ∃ M, ∀ r, 0 ≤ r → r ≤ h → b r ≤ M)
    (A B : ℝ)
    (hlo : ∀ t, 0 < t → m t ≤ b t)
    (hhi : ∀ t, 0 < t → b t ≤ m t + A + B * Real.log (1 + t)) :
    Tendsto (fun t : ℝ => m t / t) atTop (𝓝 (sInf ((fun h : ℝ => b h / h) '' Ioi 0))) := by
  exact _root_.GrowthRates.RealFekete.tendsto_div_rate_of_comparison ⟨hnonneg, hsubadd, hlocal⟩ A B hlo hhi

/-- **Finite-time lower bound.** Under the upper comparison,
`t * rate b - A - B log (1 + t) ≤ m t` for every `t > 0`.
Library: `GrowthRates.RealFekete.lower_bound_of_comparison` (unfolds `RealTimeBounds`, `rate`). -/
theorem lower_bound_of_comparison {b m : ℝ → ℝ}
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ b t)
    (hsubadd : ∀ t u, 0 ≤ t → 0 ≤ u → b (t + u) ≤ b t + b u)
    (hlocal : ∀ h, 0 < h → ∃ M, ∀ r, 0 ≤ r → r ≤ h → b r ≤ M)
    (A B : ℝ)
    (hhi : ∀ t, 0 < t → b t ≤ m t + A + B * Real.log (1 + t))
    {t : ℝ} (ht : 0 < t) :
    t * sInf ((fun h : ℝ => b h / h) '' Ioi 0) - A - B * Real.log (1 + t) ≤ m t := by
  exact _root_.GrowthRates.RealFekete.lower_bound_of_comparison ⟨hnonneg, hsubadd, hlocal⟩ A B hhi ht

/-- **Logarithmic rate of a comparable function.** If `1 ≤ N t`, `N` is submultiplicative on
`[0, ∞)`, `N t ≤ exp (C t)` with `0 ≤ C`, `0 < F t ≤ N t` and
`log N t ≤ log F t + A + B log (1 + t)` for `t > 0`, then `log F t / t` converges to
`inf_{h > 0} log N h / h`, and `t * (that infimum) - A - B log (1 + t) ≤ log F t` for `t > 0`.
Library: `GrowthRates.RealFekete.log_rate_of_submul` (unfolds `SubmulInputs`, `rate`). -/
theorem log_rate_of_submul {N F : ℝ → ℝ} {C A B : ℝ}
    (hC : 0 ≤ C)
    (hone : ∀ t, 0 ≤ t → 1 ≤ N t)
    (hsubmul : ∀ t u, 0 ≤ t → 0 ≤ u → N (t + u) ≤ N t * N u)
    (hexp : ∀ t, 0 ≤ t → N t ≤ Real.exp (C * t))
    (Fpos : ∀ t, 0 < t → 0 < F t)
    (lower : ∀ t, 0 < t → F t ≤ N t)
    (upper : ∀ t, 0 < t →
      Real.log (N t) ≤ Real.log (F t) + A + B * Real.log (1 + t)) :
    Tendsto (fun t : ℝ => Real.log (F t) / t) atTop
      (𝓝 (sInf ((fun h : ℝ => Real.log (N h) / h) '' Ioi 0))) ∧
    (∀ t, 0 < t → t * sInf ((fun h : ℝ => Real.log (N h) / h) '' Ioi 0)
      - A - B * Real.log (1 + t) ≤ Real.log (F t)) := by
  exact _root_.GrowthRates.RealFekete.log_rate_of_submul ⟨hC, hone, hsubmul, hexp⟩ Fpos lower upper

end GrowthRatesAudit.GrowthRates.RealFekete

/-! ## Fekete's lemma with a logarithmic defect (`GrowthRates.LogDefect`) -/

namespace GrowthRatesAudit.GrowthRates.LogDefect

/-- **Balanced merge.** For a near-superadditive `a` with logarithmic defect, the corrected function
is superadditive on balanced pairs `x / 2 ≤ y ≤ 2 x`, `x, y ≥ h`.
Library: `GrowthRates.LogDefect.balanced_merge` (unfolds `corrected`, `correction`). -/
theorem balanced_merge (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x y : ℝ) (hx : h ≤ x) (hy : h ≤ y)
    (hxy : x / 2 ≤ y) (hyx : y ≤ 2 * x) :
    (a x - (M * Real.log x + B + M * Real.log (9 / 2 : ℝ))) +
      (a y - (M * Real.log y + B + M * Real.log (9 / 2 : ℝ))) ≤
      a (x+y) - (M * Real.log (x+y) + B + M * Real.log (9 / 2 : ℝ)) := by
  exact _root_.GrowthRates.LogDefect.balanced_merge a M B h hM hh hnear x y hx hy hxy hyx

/-- **Equal blocks.** `k * corrected a M B x ≤ corrected a M B (k x)` for every `k ≥ 1`, `x ≥ h`.
Library: `GrowthRates.LogDefect.corrected_nat_blocks` (unfolds `corrected`, `correction`). -/
theorem corrected_nat_blocks (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x : ℝ) (hx : h ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * (a x - (M * Real.log x + B + M * Real.log (9 / 2 : ℝ))) ≤
      a ((k : ℝ)*x) - (M * Real.log ((k : ℝ)*x) + B + M * Real.log (9 / 2 : ℝ)) := by
  exact _root_.GrowthRates.LogDefect.corrected_nat_blocks a M B h hM hh hnear x hx k hk

/-- **Equal blocks, uncorrected right side.** With `B ≥ 0` as well,
`k * corrected a M B x ≤ a (k x)`.
Library: `GrowthRates.LogDefect.nat_blocks` (unfolds `corrected`, `correction`). -/
theorem nat_blocks (a : ℝ → ℝ) (M B h : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hh : 1 ≤ h)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y))
    (x : ℝ) (hx : h ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * (a x - (M * Real.log x + B + M * Real.log (9 / 2 : ℝ))) ≤ a ((k : ℝ)*x) := by
  exact _root_.GrowthRates.LogDefect.nat_blocks a M B h hM hB hh hnear x hx k hk

/-- **Fekete's lemma with a logarithmic defect.** If `a` is monotone on `[h, ∞)`, `a x ≤ C x` there,
and `a x + a y - M log (x + y) - B ≤ a (x + y)` for `x, y ≥ h` (with `M, B ≥ 0`, `h ≥ 1`), then
`a t / t` converges to `sup_{x ≥ h} (a x - M log x - B - M log (9/2)) / x`.
Library: `GrowthRates.LogDefect.tendsto_div_rate` (unfolds `rate`, `corrected`, `correction`). -/
theorem tendsto_div_rate (a : ℝ → ℝ) (M B h C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hh : 1 ≤ h)
    (hmono : MonotoneOn a (Ici h))
    (hupper : ∀ x : ℝ, h ≤ x → a x ≤ C*x)
    (hnear : ∀ x y : ℝ, h ≤ x → h ≤ y →
      a x + a y - M * Real.log (x+y) - B ≤ a (x+y)) :
    Tendsto (fun t : ℝ => a t / t) atTop
      (𝓝 (sSup (range (fun x : Ici h =>
        (a x - (M * Real.log x + B + M * Real.log (9 / 2 : ℝ))) / x)))) := by
  exact _root_.GrowthRates.LogDefect.tendsto_div_rate a M B h C hM hB hh hmono hupper hnear

/-- **Delayed form.** If `b ≥ 0` is monotone on `[0, ∞)`, `b t ≤ C (t + 1)` for `t ≥ T0`, and
`b S + b T - M log (2 + S + T) - B ≤ b (S + T + 1)` for `S, T ≥ T0`, then the rate
`sup_{T ≥ T0} (b T - M log (1 + T) - B - M log (9/2)) / (T + 1)` is nonnegative and is the limit
of `b t / t`.
Library: `GrowthRates.LogDefect.tendsto_div_delayedRate` (unfolds `delayedRate`). -/
theorem tendsto_div_delayedRate (b : ℝ → ℝ) (M B T0 C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hT0 : 0 ≤ T0)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ b t)
    (hmono : MonotoneOn b (Ici 0))
    (hupper : ∀ t : ℝ, T0 ≤ t → b t ≤ C*(t+1))
    (hnear : ∀ S T : ℝ, T0 ≤ S → T0 ≤ T →
      b S + b T - M * Real.log (2+S+T) - B ≤ b (S+T+1)) :
    0 ≤ sSup (range (fun T : Ici T0 =>
      (b T - M * Real.log (1 + T) - B - M * Real.log (9/2:ℝ)) / (T+1))) ∧
    Tendsto (fun t : ℝ => b t / t) atTop
      (𝓝 (sSup (range (fun T : Ici T0 =>
        (b T - M * Real.log (1 + T) - B - M * Real.log (9/2:ℝ)) / (T+1))))) := by
  exact _root_.GrowthRates.LogDefect.tendsto_div_delayedRate b M B T0 C hM hB hT0 hnonneg hmono hupper hnear

/-- **Multiplicative form.** If `f ≥ 1` is monotone on `[0, ∞)`, `f t ≤ exp (C (t + 1))` for
`t ≥ T0`, and `f S f T / exp (M log (2 + S + T) + B) ≤ f (S + T + 1)` for `S, T ≥ T0`, then
`log f t / t` converges to the nonnegative rate
`sup_{T ≥ T0} (log f T - M log (1 + T) - B - M log (9/2)) / (T + 1)`.
Library: `GrowthRates.LogDefect.tendsto_log_div_delayedRate` (unfolds `delayedRate`). -/
theorem tendsto_log_div_delayedRate (f : ℝ → ℝ) (M B T0 C : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hT0 : 0 ≤ T0)
    (hone : ∀ t : ℝ, 0 ≤ t → 1 ≤ f t)
    (hmono : MonotoneOn f (Ici 0))
    (hupper : ∀ t : ℝ, T0 ≤ t → f t ≤ Real.exp (C*(t+1)))
    (hcompose : ∀ S T : ℝ, T0 ≤ S → T0 ≤ T →
      f S*f T / Real.exp (M*Real.log (2+S+T)+B) ≤ f (S+T+1)) :
    0 ≤ sSup (range (fun T : Ici T0 =>
      (Real.log (f T) - M * Real.log (1 + T) - B - M * Real.log (9/2:ℝ)) / (T+1))) ∧
    Tendsto (fun t : ℝ => Real.log (f t)/t) atTop
      (𝓝 (sSup (range (fun T : Ici T0 =>
        (Real.log (f T) - M * Real.log (1 + T) - B - M * Real.log (9/2:ℝ)) / (T+1))))) := by
  exact _root_.GrowthRates.LogDefect.tendsto_log_div_delayedRate f M B T0 C hM hB hT0 hone hmono hupper hcompose

end GrowthRatesAudit.GrowthRates.LogDefect

/-! ## Uniform envelopes and joint limits (`GrowthRates.Envelope`) -/

namespace GrowthRatesAudit.GrowthRates.Envelope

/-- **Envelope squeeze.** Verbatim.
Library: `GrowthRates.Envelope.envelope_limit`. -/
theorem envelope_limit {β : Type*} {l : Filter β} {a : ℕ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    {f e : β → ℝ} {v : ℕ → β → ℝ}
    (he : Tendsto e l (𝓝 0))
    (hlower : ∀ᶠ x in l, C - e x ≤ f x)
    (hupper : ∀ k, ∀ᶠ x in l, f x ≤ v k x)
    (hv : ∀ k, Tendsto (v k) l (𝓝 (a k))) :
    Tendsto f l (𝓝 C) := by
  exact _root_.GrowthRates.Envelope.envelope_limit hC he hlower hupper hv

/-- **Every real order.** Even-order lower bounds and monotonicity in the order give
`C - e T ≤ q p T` for every real `p ≥ 2`.
Library: `GrowthRates.Envelope.real_order_lower` (unfolds `evenOrder`). -/
theorem real_order_lower {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hanti : ∀ T, 0 < T → ∀ p, 2 ≤ p → ∀ r, p ≤ r → q r T ≤ q p T)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (2 * ((k + 1 : ℕ) : ℝ)) T)
    {p T : ℝ} (hp : 2 ≤ p) (hT : 0 < T) : C - e T ≤ q p T := by
  exact _root_.GrowthRates.Envelope.real_order_lower hC hanti hlower hp hT

/-- **Sandwich at a fixed time.**
Library: `GrowthRates.Envelope.control_sandwich` (unfolds `evenOrder`). -/
theorem control_sandwich {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e φ : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (2 * ((k + 1 : ℕ) : ℝ)) T)
    (hφ : ∀ T, 0 < T → IsGLB (range (fun k => q (2 * ((k + 1 : ℕ) : ℝ)) T)) (φ T))
    {T : ℝ} (hT : 0 < T) :
    C - e T ≤ φ T ∧ ∀ k, φ T ≤ q (2 * ((k + 1 : ℕ) : ℝ)) T := by
  exact _root_.GrowthRates.Envelope.control_sandwich hC hlower hφ hT

/-- **Limit of the infimum.**
Library: `GrowthRates.Envelope.control_limit` (unfolds `evenOrder`). -/
theorem control_limit {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e φ : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (2 * ((k + 1 : ℕ) : ℝ)) T)
    (hφ : ∀ T, 0 < T → IsGLB (range (fun k => q (2 * ((k + 1 : ℕ) : ℝ)) T)) (φ T))
    (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ k, Tendsto (q (2 * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 (a k))) :
    Tendsto φ atTop (𝓝 C) := by
  exact _root_.GrowthRates.Envelope.control_limit hC hlower hφ he hq

/-- **Joint limit along sequences.**
Library: `GrowthRates.Envelope.joint_limit` (unfolds `evenOrder`). -/
theorem joint_limit {q : ℝ → ℝ → ℝ} {a : ℕ → ℝ} {e : ℝ → ℝ}
    {C : ℝ} (hC : IsGLB (range a) C)
    (hanti : ∀ T, 0 < T → ∀ p, 2 ≤ p → ∀ r, p ≤ r → q r T ≤ q p T)
    (hlower : ∀ k T, 0 < T → a k - e T ≤ q (2 * ((k + 1 : ℕ) : ℝ)) T)
    (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ k, Tendsto (q (2 * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 (a k)))
    (p T : ℕ → ℝ) (hp : Tendsto p atTop atTop) (hT : Tendsto T atTop atTop) :
    Tendsto (fun j => q (p j) (T j)) atTop (𝓝 C) := by
  exact _root_.GrowthRates.Envelope.joint_limit hC hanti hlower he hq p T hp hT

/-- **Corrected infimum.** Verbatim.
Library: `GrowthRates.Envelope.corrected_sInf`. -/
theorem corrected_sInf {φ e : ℝ → ℝ} {C : ℝ}
    (hlower : ∀ T, 0 < T → C - e T ≤ φ T)
    (hφ : Tendsto φ atTop (𝓝 C)) (he : Tendsto e atTop (𝓝 0)) :
    sInf ((fun T => φ T + e T) '' Ioi 0) = C := by
  exact _root_.GrowthRates.Envelope.corrected_sInf hlower hφ he

/-- **Division by a positive time preserves a greatest lower bound.** Verbatim.
Library: `GrowthRates.Envelope.glb_div_time`. -/
theorem glb_div_time {v : ℕ → ℝ} {φ T : ℝ} (hT : 0 < T)
    (hφ : IsGLB (range v) φ) :
    IsGLB (range (fun k => v k / T)) (φ / T) := by
  exact _root_.GrowthRates.Envelope.glb_div_time hT hφ

end GrowthRatesAudit.GrowthRates.Envelope

/-! ## Quantitative finite-time errors (`GrowthRates.FiniteError`) -/

namespace GrowthRatesAudit.GrowthRates.FiniteError

/-- If `b (t + h) ≤ b t + A` for `t ≥ r` and `b t / t → lam`, then `lam h ≤ A`. Verbatim.
Library: `GrowthRates.FiniteError.step_upper`. -/
theorem step_upper (b : ℝ → ℝ) (lam r h A : ℝ) (hh : 0 < h)
    (hrate : Tendsto (fun t => b t/t) atTop (𝓝 lam))
    (hstep : ∀ t, r ≤ t → b (t+h) ≤ b t+A) : lam*h ≤ A := by
  exact _root_.GrowthRates.FiniteError.step_upper b lam r h A hh hrate hstep

/-- If `b t + A ≤ b (t + h)` for `t ≥ r` and `b t / t → lam`, then `A ≤ lam h`. Verbatim.
Library: `GrowthRates.FiniteError.step_lower`. -/
theorem step_lower (b : ℝ → ℝ) (lam r h A : ℝ) (hh : 0 < h)
    (hrate : Tendsto (fun t => b t/t) atTop (𝓝 lam))
    (hstep : ∀ t, r ≤ t → b t+A ≤ b (t+h)) : A ≤ lam*h := by
  exact _root_.GrowthRates.FiniteError.step_lower b lam r h A hh hrate hstep

/-- **Finite-time bounds from a cut and a confinement.** Verbatim.
Library: `GrowthRates.FiniteError.finite_bounds`. -/
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
  exact _root_.GrowthRates.FiniteError.finite_bounds f B n lam hone hrate hcut hconfine hcompose

/-- **Optimized error.** Verbatim.
Library: `GrowthRates.FiniteError.optimize`. -/
theorem optimize (b : ℝ → ℝ) (n lam : ℝ) (hn : 0 < n) (hlam : 0 ≤ lam)
    (hbound : ∀ T δ : ℝ, 0 < T → 0 < δ →
      lam*(T-δ)-n*Real.log (1+T/δ) ≤ b T ∧
      b T ≤ lam*(T+δ)+n*Real.log (max 1 (T/δ)))
    (T : ℝ) (hT : 0 < T) :
    |b T-T*lam| ≤ n*(1+Real.log (2+T*lam/n)) := by
  exact _root_.GrowthRates.FiniteError.optimize b n lam hn hlam hbound T hT

/-- **Quantitative error for `log f`.** Verbatim.
Library: `GrowthRates.FiniteError.log_error`. -/
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
  exact _root_.GrowthRates.FiniteError.log_error f B n lam hn hone hzero hrate hcut hconfine hcompose

/-- **Sandwich error.** Verbatim.
Library: `GrowthRates.FiniteError.sandwich_error`. -/
theorem sandwich_error (x xn xm p n m z C cn cm M : ℝ)
    (hp : 0 < p) (hn : 0 < n) (hm : 0 < m) (hz : 0 < z)
    (hC : 0 ≤ C) (hCm : C ≤ cm) (hmn : cm ≤ cn) (hnM : cn ≤ M)
    (hen : |xn-n*cn*z| ≤ n*(1+Real.log (2+cn*z)))
    (hem : |xm-m*cm*z| ≤ m*(1+Real.log (2+cm*z)))
    (hlo : p/m*xm ≤ x) (hhi : x ≤ p/n*xn) :
    |x/(p*z)-C| ≤ cn-C+(1+Real.log (2+M*z))/z := by
  exact _root_.GrowthRates.FiniteError.sandwich_error x xn xm p n m z C cn cm M hp hn hm hz hC hCm hmn hnM hen hem hlo hhi

/-- **Joint error from two orders.**
Library: `GrowthRates.FiniteError.joint_error` (unfolds `CutInputs` for both functions). -/
theorem joint_error (fn fm : ℝ → ℝ) (Bn Bm : ℝ → ℝ → ℝ)
    (n m : ℕ) (ln lm T x p z C cn cm M : ℝ)
    (hn : 0 < n) (hone_n : ∀ t, 0 ≤ t → 1 ≤ fn t) (hzero_n : fn 0 = 1)
    (hrate_n : Tendsto (fun t => Real.log (fn t)/t) atTop (𝓝 ln))
    (hcut_n : ∀ T S δ : ℝ, 0 ≤ T → 0 ≤ S → 0 < δ →
      fn (T+S) ≤ (1+T/δ)^n*fn T*fn (S+δ))
    (hconfine_n : ∀ T δ : ℝ, 0 < T → 0 < δ → (min 1 (δ/T))^n*fn T ≤ Bn T δ)
    (hcompose_n : ∀ T δ t : ℝ, 0 < T → 0 < δ → 0 ≤ t → Bn T δ*fn t ≤ fn (t+T+δ))
    (hm : 0 < m) (hone_m : ∀ t, 0 ≤ t → 1 ≤ fm t) (hzero_m : fm 0 = 1)
    (hrate_m : Tendsto (fun t => Real.log (fm t)/t) atTop (𝓝 lm))
    (hcut_m : ∀ T S δ : ℝ, 0 ≤ T → 0 ≤ S → 0 < δ →
      fm (T+S) ≤ (1+T/δ)^m*fm T*fm (S+δ))
    (hconfine_m : ∀ T δ : ℝ, 0 < T → 0 < δ → (min 1 (δ/T))^m*fm T ≤ Bm T δ)
    (hcompose_m : ∀ T δ t : ℝ, 0 < T → 0 < δ → 0 ≤ t → Bm T δ*fm t ≤ fm (t+T+δ))
    (hT : 0 ≤ T) (hp : 0 < p) (hz : 0 < z)
    (hC : 0 ≤ C) (hCm : C ≤ cm) (hmn : cm ≤ cn) (hnM : cn ≤ M)
    (hsn : T*ln=(n:ℝ)*cn*z) (hsm : T*lm=(m:ℝ)*cm*z)
    (hlo : p/(m:ℝ)*Real.log (fm T) ≤ x)
    (hhi : x ≤ p/(n:ℝ)*Real.log (fn T)) :
    |x/(p*z)-C| ≤ cn-C+(1+Real.log (2+M*z))/z := by
  exact _root_.GrowthRates.FiniteError.joint_error fn fm Bn Bm n m ln lm T x p z C cn cm M
    ⟨hn, hone_n, hzero_n, hrate_n, hcut_n, hconfine_n, hcompose_n⟩
    ⟨hm, hone_m, hzero_m, hrate_m, hcut_m, hconfine_m, hcompose_m⟩
    hT hp hz hC hCm hmn hnM hsn hsm hlo hhi

end GrowthRatesAudit.GrowthRates.FiniteError
