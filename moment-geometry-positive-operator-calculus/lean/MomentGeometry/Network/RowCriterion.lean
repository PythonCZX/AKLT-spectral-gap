/-
MomentGeometry/Network/RowCriterion.lean

The row-sum certificate of `q:row-criterion`, in the numerical form required by
`GapAssembly.norm_sq_block_ge_of_conflict`.

A nonnegative symmetric conflict matrix whose row sums are bounded by `ρ` has
quadratic form bounded by `ρ`; consequently the blocked gap estimate holds with
`1 - ρ`.  This is the rational positive-vector certificate the source describes,
and it never computes an eigenvalue.
-/
import Mathlib
import MomentGeometry.Network.GapAssembly

open scoped BigOperators

namespace MomentGeometry.Network

/-- The quadratic form of an entrywise nonnegative symmetric conflict matrix with
row sums at most `ρ` is bounded by `ρ` times `∑_e z_e^2`. -/
theorem rayleigh_of_row_sum {ι : Type*} [Fintype ι]
    (C : ι → ι → ℝ) (hsym : ∀ e f, C e f = C f e) (hnn : ∀ e f, 0 ≤ C e f) (ρ : ℝ)
    (hrow : ∀ e, ∑ f, C e f ≤ ρ) :
    ∀ z : ι → ℝ, ∑ e, ∑ f, C e f * z e * z f ≤ ρ * ∑ e, (z e) ^ 2 := by
  intro z
  -- geometric-mean step, valid because the entries of `C` are nonnegative
  have hstep : ∑ e, ∑ f, C e f * z e * z f
      ≤ ∑ e, ∑ f, C e f * ((z e) ^ 2 + (z f) ^ 2) / 2 := by
    refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ => ?_
    have hg : 2 * (z e * z f) ≤ (z e) ^ 2 + (z f) ^ 2 := by
      nlinarith [sq_nonneg (z e - z f)]
    have h := mul_le_mul_of_nonneg_left hg (hnn e f)
    nlinarith
  -- the two halves of the symmetrized form coincide
  have hsplit : ∀ e, ∑ f, C e f * ((z e) ^ 2 + (z f) ^ 2) / 2
      = ((∑ f, C e f) * (z e) ^ 2 + ∑ f, C e f * (z f) ^ 2) / 2 := by
    intro e
    rw [← Finset.sum_div,
      Finset.sum_congr rfl (fun f _ =>
        (by ring : C e f * ((z e) ^ 2 + (z f) ^ 2)
          = C e f * (z e) ^ 2 + C e f * (z f) ^ 2)),
      Finset.sum_add_distrib, ← Finset.sum_mul]
  have hcol : ∑ e, ∑ f, C e f * (z f) ^ 2 = ∑ e, (∑ f, C e f) * (z e) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hsym i j
  have hcollapse : ∑ e, ∑ f, C e f * ((z e) ^ 2 + (z f) ^ 2) / 2
      = ∑ e, (∑ f, C e f) * (z e) ^ 2 := by
    rw [Finset.sum_congr rfl fun e _ => hsplit e, ← Finset.sum_div, Finset.sum_add_distrib, hcol]
    ring
  calc ∑ e, ∑ f, C e f * z e * z f
      ≤ ∑ e, (∑ f, C e f) * (z e) ^ 2 := by rw [← hcollapse]; exact hstep
    _ ≤ ∑ e, ρ * (z e) ^ 2 :=
        Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hrow e) (sq_nonneg _)
    _ = ρ * ∑ e, (z e) ^ 2 := by rw [Finset.mul_sum]

end MomentGeometry.Network

#print axioms MomentGeometry.Network.rayleigh_of_row_sum
