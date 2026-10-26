module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

import GrowthRates
import GrowthRates.Solution

/-!
# Axiom report

`verify.sh` builds this module; the lower-tier receipt reads the `#print axioms` output.
Part 1: every declaration of `claims.yaml` (in file order). Part 2: every comparator Solution theorem
(`comparator.json`). Each must depend only on `propext`, `Quot.sound` and `Classical.choice`.
-/

/-! ## Part 1: claims.yaml -/

#print axioms GrowthRates.RealFekete.slopes_nonempty
#print axioms GrowthRates.RealFekete.slopes_bdd
#print axioms GrowthRates.RealFekete.rate_le_slope
#print axioms GrowthRates.RealFekete.rate_nonneg
#print axioms GrowthRates.RealFekete.multiple_remainder
#print axioms GrowthRates.RealFekete.block_bound
#print axioms GrowthRates.RealFekete.tendsto_div_rate
#print axioms GrowthRates.RealFekete.logarithmic_error_vanishes
#print axioms GrowthRates.RealFekete.tendsto_div_rate_of_comparison
#print axioms GrowthRates.RealFekete.lower_bound_of_comparison
#print axioms GrowthRates.RealFekete.log_realTimeBounds
#print axioms GrowthRates.RealFekete.log_rate_of_submul
#print axioms GrowthRates.RealFekete.lower_bound_at_zero
#print axioms GrowthRates.LogDefect.balanced_ratio
#print axioms GrowthRates.LogDefect.balanced_merge
#print axioms GrowthRates.LogDefect.corrected_nat_blocks
#print axioms GrowthRates.LogDefect.correction_nonneg
#print axioms GrowthRates.LogDefect.nat_blocks
#print axioms GrowthRates.LogDefect.correction_sublinear
#print axioms GrowthRates.LogDefect.fixed_block_lower
#print axioms GrowthRates.LogDefect.tendsto_div_rate
#print axioms GrowthRates.LogDefect.tendsto_div_delayedRate
#print axioms GrowthRates.LogDefect.tendsto_log_div_delayedRate
#print axioms GrowthRates.Envelope.evenOrder_ge_two
#print axioms GrowthRates.Envelope.exists_evenOrder_ge
#print axioms GrowthRates.Envelope.envelope_limit
#print axioms GrowthRates.Envelope.real_order_lower
#print axioms GrowthRates.Envelope.control_sandwich
#print axioms GrowthRates.Envelope.control_limit
#print axioms GrowthRates.Envelope.joint_limit
#print axioms GrowthRates.Envelope.corrected_infimum
#print axioms GrowthRates.Envelope.corrected_sInf
#print axioms GrowthRates.Envelope.glb_div_time
#print axioms GrowthRates.FiniteError.progression_limit
#print axioms GrowthRates.FiniteError.step_upper
#print axioms GrowthRates.FiniteError.step_lower
#print axioms GrowthRates.FiniteError.finite_bounds
#print axioms GrowthRates.FiniteError.optimize
#print axioms GrowthRates.FiniteError.log_error
#print axioms GrowthRates.FiniteError.sandwich_error
#print axioms GrowthRates.FiniteError.joint_error

/-! ## Part 2: comparator Solution theorems -/

#print axioms GrowthRatesAudit.GrowthRates.RealFekete.tendsto_div_rate
#print axioms GrowthRatesAudit.GrowthRates.RealFekete.rate_le_slope
#print axioms GrowthRatesAudit.GrowthRates.RealFekete.rate_nonneg
#print axioms GrowthRatesAudit.GrowthRates.RealFekete.tendsto_div_rate_of_comparison
#print axioms GrowthRatesAudit.GrowthRates.RealFekete.lower_bound_of_comparison
#print axioms GrowthRatesAudit.GrowthRates.RealFekete.log_rate_of_submul
#print axioms GrowthRatesAudit.GrowthRates.LogDefect.balanced_merge
#print axioms GrowthRatesAudit.GrowthRates.LogDefect.corrected_nat_blocks
#print axioms GrowthRatesAudit.GrowthRates.LogDefect.nat_blocks
#print axioms GrowthRatesAudit.GrowthRates.LogDefect.tendsto_div_rate
#print axioms GrowthRatesAudit.GrowthRates.LogDefect.tendsto_div_delayedRate
#print axioms GrowthRatesAudit.GrowthRates.LogDefect.tendsto_log_div_delayedRate
#print axioms GrowthRatesAudit.GrowthRates.Envelope.envelope_limit
#print axioms GrowthRatesAudit.GrowthRates.Envelope.real_order_lower
#print axioms GrowthRatesAudit.GrowthRates.Envelope.control_sandwich
#print axioms GrowthRatesAudit.GrowthRates.Envelope.control_limit
#print axioms GrowthRatesAudit.GrowthRates.Envelope.joint_limit
#print axioms GrowthRatesAudit.GrowthRates.Envelope.corrected_sInf
#print axioms GrowthRatesAudit.GrowthRates.Envelope.glb_div_time
#print axioms GrowthRatesAudit.GrowthRates.FiniteError.step_upper
#print axioms GrowthRatesAudit.GrowthRates.FiniteError.step_lower
#print axioms GrowthRatesAudit.GrowthRates.FiniteError.finite_bounds
#print axioms GrowthRatesAudit.GrowthRates.FiniteError.optimize
#print axioms GrowthRatesAudit.GrowthRates.FiniteError.log_error
#print axioms GrowthRatesAudit.GrowthRates.FiniteError.sandwich_error
#print axioms GrowthRatesAudit.GrowthRates.FiniteError.joint_error
