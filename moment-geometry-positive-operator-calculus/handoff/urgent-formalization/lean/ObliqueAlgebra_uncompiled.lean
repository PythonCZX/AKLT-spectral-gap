/-
UNCOMPILED SOURCE — 2026-11-15.
No Lean compiler or proof checker was run.
This file supplies only algebraic identities and the scalar spectral step.
The analytic Hilbert-space theorem is proved in oblique_proofs.tex and
still requires translation. There are no axioms or placeholder proofs here.
-/

import Mathlib

namespace ObliqueUnchecked

variable {R : Type*} [Ring R]

def comm (x y : R) : R := x * y - y * x

theorem comm_product (x y t : R) :
    comm (x * y) t = x * comm y t + comm x t * y := by
  unfold comm
  noncomm_ring

theorem comm_difference (x y t : R) :
    comm (x - y) t = comm x t - comm y t := by
  unfold comm
  noncomm_ring

theorem comm_square (x t : R) :
    comm (x * x) t = x * comm x t + comm x t * x := by
  exact comm_product x x t

theorem comm_inverse (d di t : R)
    (hleft : di * d = 1) (hright : d * di = 1) :
    comm di t = -di * comm d t * di := by
  unfold comm
  calc
    di * t - t * di =
        -(di * d) * t * di + di * t * (d * di) := by
      rw [hleft, hright]
      noncomm_ring
    _ = -di * (d * t - t * d) * di := by
      noncomm_ring

theorem conjugation_product (u v x y : R) (hvu : v * u = 1) :
    (u * x * v) * (u * y * v) = u * (x * y) * v := by
  calc
    (u * x * v) * (u * y * v) = u * (x * (v * u) * y) * v := by
      noncomm_ring
    _ = u * (x * y) * v := by
      rw [hvu]
      simp

theorem conjugation_idempotent (u v e : R)
    (hvu : v * u = 1) (he : e * e = e) :
    (u * e * v) * (u * e * v) = u * e * v := by
  rw [conjugation_product u v e e hvu, he]

theorem conjugation_compatible (u v e f : R)
    (hvu : v * u = 1) (hef : e * f = f * e) :
    (u * e * v) * (u * f * v) =
      (u * f * v) * (u * e * v) := by
  rw [conjugation_product u v e f hvu,
      conjugation_product u v f e hvu, hef]

theorem nonnegative_eigenvalue_gap (alpha lam : ℝ)
    (hlam : 0 ≤ lam) (hquad : alpha * lam ≤ lam * lam) :
    lam = 0 ∨ alpha ≤ lam := by
  by_cases hz : lam = 0
  · exact Or.inl hz
  · right
    have hp : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hz)
    by_contra hnot
    have hlt : lam < alpha := lt_of_not_ge hnot
    nlinarith

end ObliqueUnchecked
