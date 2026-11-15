/-
Scoped composed module: exactly which source obligations have verified Lean
content in this member's build.

This file imports every module that participates in the audit and then

* fixes in Lean data the list of registry records that carry at least one
  proved ingredient (`component_verified`) and counts them;
* records the two finite-moment separation facts that matter for source
  fidelity (the exact `q = 2, m = 1` value is neither `14` nor the free-limit
  value `57/4`);
* prints the axiom dependency of every headline export, so the accompanying
  build log is a check rather than a claim.

It deliberately contains no new mathematics.  Nothing here asserts that a
registered source contract is complete.
-/
import MomentGeometry.Frozen.Statements
import MomentGeometry.Coherent.UnitDensity

namespace MomentGeometry.Composed

open MomentGeometry

/-- Registry records that currently carry at least one *proved* Lean ingredient.
This is **not** a list of completed source contracts. -/
def recordsWithVerifiedComponents : List String :=
  ["op:hyperbolic-clock", "q:thm-powers", "q:kms-compatibility",
   "eq:coherent-finite-moments", "prop:repair"]

theorem recordsWithVerifiedComponents_count :
    recordsWithVerifiedComponents.length = 5 := by decide

/-- Cross-check: the four component-bearing priority records appear in the frozen
priority table, and `eq:coherent-finite-moments` is a non-priority record. -/
theorem component_records_split :
    (Frozen.priorityObligations.filter
        (fun o => recordsWithVerifiedComponents.contains o.id)).length = 4 := by
  decide

/-- The exact finite-k value at `q = 2`, `m = 1` (`D = 3`, `D' = 6`, `n = 3`) is
not the limiting constant `14` of the `D' = D(D+1)` specialisation. -/
theorem q2_m1_value_ne_fourteen : Coherent.expectedT4 3 3 6 ≠ 14 := by
  rw [Coherent.expectedT4_unit_density_q2_m1]
  norm_num

/-- Nor is it the free-limit moment `57/4 = 14 + 2^{-2}`; `57/4` is the
`m -> infinity` value at `q = 2`, `rho = 1`, not a finite expectation. -/
theorem q2_m1_value_ne_free_limit : Coherent.expectedT4 3 3 6 ≠ 57 / 4 := by
  rw [Coherent.expectedT4_unit_density_q2_m1]
  norm_num

/-- Sanity check on the `q = 1` family: at `D = 2` (`m = 1`, `D' = 3`) both the
general unit-density form and the specialised `q = 1` form agree. -/
theorem q1_m1_consistency :
    Coherent.expectedT4 2 2 3 = 29 / 2 - 1 / (2 * (2 * (2 : ℚ) - 1)) - 30 / 2
      + 23 / 2 ^ 2 - 6 / 2 ^ 3 := by
  norm_num [Coherent.expectedT4]

end MomentGeometry.Composed

#print axioms MomentGeometry.Composed.recordsWithVerifiedComponents_count
#print axioms MomentGeometry.Composed.component_records_split
#print axioms MomentGeometry.Composed.q2_m1_value_ne_fourteen
#print axioms MomentGeometry.Composed.q2_m1_value_ne_free_limit
#print axioms MomentGeometry.Composed.q1_m1_consistency
#print axioms MomentGeometry.Operator.Clock.completelyPositive_sinhc_zero
#print axioms MomentGeometry.Operator.Clock.completelyPositive_sinhc_rpow
#print axioms MomentGeometry.Operator.Clock.completelyPositive_iff_kernel
#print axioms MomentGeometry.Operator.KMS.antiPart_compatibility
#print axioms MomentGeometry.Operator.KMS.antiPart_eq_ratio_sq
#print axioms MomentGeometry.Operator.KMS.hermitian_composition
#print axioms MomentGeometry.Coherent.expectedT3_cubic_form
#print axioms MomentGeometry.Coherent.expectedT3_at_unit_density
#print axioms MomentGeometry.Coherent.expectedT4_unit_density_general
#print axioms MomentGeometry.Coherent.expectedT4_unit_density_q1_family
#print axioms MomentGeometry.Repair.repair_summary
#print axioms MomentGeometry.Repair.repair_moment_eq
#print axioms MomentGeometry.Repair.repair_density_range
#print axioms MomentGeometry.Repair.repair_total_mass
#print axioms MomentGeometry.Frozen.priorityObligations_length
#print axioms MomentGeometry.Frozen.priorityObligations_no_source_contract_verified
