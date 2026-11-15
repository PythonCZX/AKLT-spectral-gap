/-
MomentGeometry/Network/WireGap.lean

Assembly of the blocked gap criterion `q:thm-wire-gap` from its two ingredients:

* the subspace-angle bound `hcross` on pairs of blocked projectors (the content of
  `q:lem-schur` transported through `q:projection-cross`, obtained in the source
  by whitening the completely positive local data), and
* the conflict-matrix certificate for `ρ(C) < 1`, taken here in the row-sum form
  of `q:row-criterion` (`C w ≤ ρ w` with `w = 1`).

Nothing in the statement refers to a dimension, a core, a bond dimension or a
condition number: the estimate is uniform over all finite graphs and all
arbitrary nonzero cores, exactly as the source asserts.

The conclusion is the Loewner inequality `H_block ≥ (1 - ρ)(I - G_all)` in
quadratic-form language, with `G_all` the orthogonal projection onto the full
ground space `ker H_block`.
-/
import Mathlib
import MomentGeometry.Network.ProjBasics
import MomentGeometry.Network.GapAssembly
import MomentGeometry.Network.GapSpectral
import MomentGeometry.Network.RowCriterion

open scoped BigOperators

namespace MomentGeometry.Network

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The blocked parent `H_block = ∑_e (1 - G_e)` is symmetric. -/
theorem isSymOp_block {ι : Type*} [Fintype ι]
    (P : ι → E →L[ℝ] E) (hP : ∀ e, IsOrthProj (P e)) :
    IsSymOp (∑ e, ((1 : E →L[ℝ] E) - P e)) := by
  refine IsSymOp.sum _ fun e _ => ?_
  exact IsSymOp.one.sub (hP e).sym

/-- The blocked parent `H_block = ∑_e (1 - G_e)` is positive semidefinite. -/
theorem nonneg_block {ι : Type*} [Fintype ι]
    (P : ι → E →L[ℝ] E) (hP : ∀ e, IsOrthProj (P e)) (x : E) :
    0 ≤ inner ℝ ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) x := by
  rw [← IsOrthProj.sum_norm_sq_compl P hP x]
  exact Finset.sum_nonneg fun e _ => sq_nonneg _

/-- **Blocked gap criterion (= the matrix step of `q:thm-wire-gap`).**

Let `G_e`, `e : ι`, be the orthogonal projectors onto the local ground spaces of
a blocked parent `H = ∑_e (I - G_e)`, let `G` be the orthogonal projector onto
the full ground space `ker H`, and let `C` be a symmetric conflict matrix with
zero diagonal whose row sums are bounded by `ρ ≤ 1`.  If the off-diagonal
off-block overlaps obey the subspace-angle bound `hcross`, then
`H ≥ (1-ρ)(I - G)`, that is, `(1-ρ)‖x - G x‖² ≤ ⟪H x, x⟫` for every `x`. -/
theorem block_gap_row_criterion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → E →L[ℝ] E) (hP : ∀ e, IsOrthProj (P e))
    (G : E →L[ℝ] E) (hG : IsOrthProj G)
    (C : ι → ι → ℝ) (hdiag : ∀ e, C e e = 0) (hsym : ∀ e f, C e f = C f e)
    (hnn : ∀ e f, 0 ≤ C e f) (ρ : ℝ)
    (hrow : ∀ e, ∑ f, C e f ≤ ρ)
    (hcross : ∀ (x : E) (e f : ι), e ≠ f →
      -(C e f * ‖x - P e x‖ * ‖x - P f x‖) ≤ inner ℝ (x - P e x) (x - P f x))
    (hHG : ∀ x : E, (∑ e, ((1 : E →L[ℝ] E) - P e)) (G x) = 0)
    (hGker : ∀ y : E, (∑ e, ((1 : E →L[ℝ] E) - P e)) y = 0 → G y = y) :
    ∀ x : E,
      (1 - ρ) * ‖x - G x‖ ^ 2
        ≤ inner ℝ ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) x := by
  have hsym' : IsSymOp (∑ e, ((1 : E →L[ℝ] E) - P e)) := isSymOp_block P hP
  have hpsd : ∀ x : E, 0 ≤ inner ℝ ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) x :=
    nonneg_block P hP
  have hquad := norm_sq_block_ge_of_conflict P hP C hdiag ρ
    (rayleigh_of_row_sum C hsym hnn ρ hrow) hcross
  -- `H² ≥ γ H` in quadratic form, with `γ = 1 - ρ`
  have h2 : ∀ x : E,
      (1 - ρ) * inner ℝ ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) x
        ≤ inner ℝ ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) := by
    intro x
    have h1 := hquad x
    rw [real_inner_self_eq_norm_sq]
    exact h1
  exact gap_loewner (∑ e, ((1 : E →L[ℝ] E) - P e)) G hsym' hG hpsd (1 - ρ) h2 hHG hGker

end MomentGeometry.Network

#print axioms MomentGeometry.Network.isSymOp_block
#print axioms MomentGeometry.Network.nonneg_block
#print axioms MomentGeometry.Network.block_gap_row_criterion
