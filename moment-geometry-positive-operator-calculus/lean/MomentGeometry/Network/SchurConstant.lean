/-
MomentGeometry/Network/SchurConstant.lean

The scalar constant `B(x,y)` of `q:lem-schur` / `q:Bxy`, and the algebraic
identity used at the end of its proof.  The proof there bounds the normalized
off-diagonal block by

  `xy/m + xy(1+x)(1+y)/m²`,  with `m = (1-x)(1-y)`,

and rewrites it as `B(x,y) = 2xy(1+xy)/((1-x)²(1-y)²)`.  The identity is
recorded here in both directions; the analytic (subspace-angle) content of the
lemma is *not* proved in this file.
-/
import Mathlib

namespace MomentGeometry.Network

/-- The two-port cosine constant `B(x,y) = 2xy(1+xy)/((1-x)^2(1-y)^2)`. -/
noncomputable def Bcos (x y : ℝ) : ℝ := 2 * x * y * (1 + x * y) / ((1 - x) ^ 2 * (1 - y) ^ 2)

/-- The chain `xy/m + xy(1+x)(1+y)/m^2 = B(x,y)` at the end of the proof of
`q:lem-schur`, for `m = (1-x)(1-y)`. -/
theorem schur_cosine_identity {x y : ℝ} (hx : x ≠ 1) (hy : y ≠ 1) :
    x * y / ((1 - x) * (1 - y))
        + x * y * (1 + x) * (1 + y) / (((1 - x) * (1 - y)) ^ 2) = Bcos x y := by
  have h1 : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h2 : (1 - y) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  unfold Bcos
  field_simp
  ring

/-- `B` is nonnegative for nonnegative arguments in `[0,1)`. -/
theorem Bcos_nonneg {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    0 ≤ Bcos x y := by
  unfold Bcos
  have h : 0 ≤ 1 + x * y := by nlinarith [mul_nonneg hx0 hy0]
  have hx : (0:ℝ) ≤ (1 - x) ^ 2 := sq_nonneg _
  have hy : (0:ℝ) ≤ (1 - y) ^ 2 := sq_nonneg _
  positivity

/-- `B` is strictly positive for positive arguments different from one. -/
theorem Bcos_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    0 < Bcos x y := by
  unfold Bcos
  have hxy : 0 < x * y := mul_pos hx hy
  have h : 0 < 1 + x * y := by linarith
  have hx' : 0 < (1 - x) ^ 2 := by
    have h' : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    positivity
  have hy' : 0 < (1 - y) ^ 2 := by
    have h' : (1 - y) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
    positivity
  positivity

end MomentGeometry.Network

#print axioms MomentGeometry.Network.schur_cosine_identity
#print axioms MomentGeometry.Network.Bcos_nonneg
#print axioms MomentGeometry.Network.Bcos_pos
