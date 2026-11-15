/-
MomentGeometry/Network/ProjBasics.lean

Finite-dimensional Hilbert-space bookkeeping for the blocked gap assembly of
`q:thm-wire-gap`.

Nothing here is asymptotic: `E` is an arbitrary real inner product space and
`ι` an arbitrary finite type.  The file provides

* the order-theoretic calculus of orthogonal projections used as local
  ground-space projectors,
* the identity `∑_e ‖(1 - P_e) x‖^2 = ⟪H x, x⟫` for `H = ∑_e (1 - P_e)`,
* the expansion of `‖H x‖^2` into the diagonal and cross terms.

The gap estimate itself is in `GapAssembly.lean`.
-/
import Mathlib

open scoped BigOperators

namespace MomentGeometry.Network

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A continuous linear endomorphism of `E` that is symmetric for the real
inner product.  This is the same predicate as `LinearMap.IsSymmetric` unwound to
avoid coercion friction. -/
def IsSymOp (T : E →L[ℝ] E) : Prop := ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y)

/-- An orthogonal projection: a symmetric idempotent continuous linear map. -/
structure IsOrthProj (P : E →L[ℝ] E) : Prop where
  sym : IsSymOp P
  idem : ∀ x : E, P (P x) = P x

theorem isSymOp_iff_isSymmetric (T : E →L[ℝ] E) :
    IsSymOp T ↔ (T : E →ₗ[ℝ] E).IsSymmetric := Iff.rfl

namespace IsSymOp

variable {S T : E →L[ℝ] E}

theorem zero : IsSymOp (0 : E →L[ℝ] E) := by
  intro x y
  simp

theorem add (hS : IsSymOp S) (hT : IsSymOp T) : IsSymOp (S + T) := by
  intro x y
  simp only [add_apply, inner_add_left, inner_add_right, hS x y, hT x y]

theorem neg (hT : IsSymOp T) : IsSymOp (-T) := by
  intro x y
  simp only [neg_apply, inner_neg_left, inner_neg_right, hT x y]

theorem sub (hS : IsSymOp S) (hT : IsSymOp T) : IsSymOp (S - T) := by
  intro x y
  simp only [sub_apply, inner_sub_left, inner_sub_right, hS x y, hT x y]

theorem smul (c : ℝ) (hT : IsSymOp T) : IsSymOp (c • T) := by
  intro x y
  simp only [smul_apply, real_inner_smul_left, real_inner_smul_right, hT x y]

theorem sum {ι : Type*} (s : Finset ι) {T : ι → E →L[ℝ] E}
    (h : ∀ i ∈ s, IsSymOp (T i)) : IsSymOp (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsSymOp (0 : E →L[ℝ] E))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end IsSymOp

namespace IsOrthProj

variable {P : E →L[ℝ] E}

theorem inner_self (hP : IsOrthProj P) (x : E) : inner ℝ (P x) x = ‖P x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (P x), real_inner_comm, hP.sym x (P x), hP.idem x]

theorem inner_self' (hP : IsOrthProj P) (x : E) : inner ℝ x (P x) = ‖P x‖ ^ 2 := by
  rw [real_inner_comm, hP.inner_self x]

theorem orthogonal (hP : IsOrthProj P) (x : E) : inner ℝ (P x) (x - P x) = 0 := by
  rw [inner_sub_right, hP.inner_self x, real_inner_self_eq_norm_sq, sub_self]

theorem norm_sq_split (hP : IsOrthProj P) (x : E) : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (x - P x) (hP.orthogonal x)
  rw [add_sub_cancel] at h
  have h' : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
    rw [pow_two, pow_two, pow_two]; exact h
  exact h'

theorem compl (hP : IsOrthProj P) : IsOrthProj (1 - P) where
  sym := by
    intro x y
    simp only [sub_apply, one_apply_eq_self, inner_sub_left, inner_sub_right, hP.sym x y,
      real_inner_comm (P x) y]
  idem := by
    intro x
    simp only [sub_apply, one_apply_eq_self]
    have h := hP.idem x
    rw [map_sub, h, sub_self, sub_zero]

theorem nonneg_inner (hP : IsOrthProj P) (x : E) : 0 ≤ inner ℝ (P x) x := by
  rw [hP.inner_self x]; positivity

/-- `∑_e ‖(1 - P_e) x‖^2 = ⟪H x, x⟫` for `H = ∑_e (1 - P_e)`. -/
theorem sum_norm_sq_compl {ι : Type*} [Fintype ι]
    (P : ι → E →L[ℝ] E) (hP : ∀ e, IsOrthProj (P e)) (x : E) :
    ∑ e, ‖x - P e x‖ ^ 2 = inner ℝ ((∑ e, (1 - P e)) x) x := by
  have h1 : ∀ e, ‖x - P e x‖ ^ 2 = inner ℝ (((1 : E →L[ℝ] E) - P e) x) x := by
    intro e
    have := (hP e).compl.inner_self x
    simpa using this.symm
  simp_rw [h1]
  conv_rhs => rw [sum_apply]
  rw [← sum_inner]

end IsOrthProj

namespace IsSymOp

theorem one : IsSymOp (1 : E →L[ℝ] E) := by
  intro x y
  simp

end IsSymOp

end MomentGeometry.Network
