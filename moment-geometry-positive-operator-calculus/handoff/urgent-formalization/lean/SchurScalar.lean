import Mathlib

/-!
Unchecked Lean source. No compilation or proof checking was performed.
This file proves the scalar closures used after the operator construction
in cp_transport_proofs.tex. It is NOT a formalization of that construction.
No `sorry` and no new axioms are used here.
-/
namespace UrgentFormalization

noncomputable def schurConstant (x y : ℝ) : ℝ :=
  2 * x * y * (1 + x * y) / ((1 - x)^2 * (1 - y)^2)

theorem schurConstant_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ schurConstant x y := by
  unfold schurConstant
  positivity

theorem schur_denominator_pos {x y : ℝ}
    (hx : x < 1) (hy : y < 1) :
    0 < (1 - x)^2 * (1 - y)^2 := by
  have hx' : 0 < 1 - x := sub_pos.mpr hx
  have hy' : 0 < 1 - y := sub_pos.mpr hy
  positivity

theorem schur_constant_identity {x y : ℝ}
    (hx : x < 1) (hy : y < 1) :
    x * y / ((1 - x) * (1 - y)) +
      ((y + x * y) * (x + x * y)) / ((1 - x) * (1 - y))^2
      = schurConstant x y := by
  have hx0 : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hy0 : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  unfold schurConstant
  field_simp [hx0, hy0]
  <;> ring

/-- The exact two-port value used by degree-three, four-site decoration. -/
theorem degree_three_pair_constant :
    schurConstant (1/5) (1/5) = (13/64 : ℝ) := by
  norm_num [schurConstant]

theorem degree_three_block_gap :
    1 - 4 * schurConstant (1/5) (1/5) = (3/16 : ℝ) := by
  rw [degree_three_pair_constant]
  norm_num

theorem degree_three_physical_factor (g : ℝ) :
    (g / 3) * (1 - 4 * schurConstant (1/5) (1/5)) = g / 16 := by
  rw [degree_three_block_gap]
  ring

/-- Bilinear mixed-defect sign cancellation at the scalar coefficient level. -/
theorem mixed_defect_upper_identity (x y a b : ℝ) :
    ((x + a) * (y - b) + (x - a) * (y + b)) / 2 = x*y - a*b := by
  ring

theorem mixed_defect_lower_identity (x y a b : ℝ) :
    ((x + a) * (y + b) + (x - a) * (y - b)) / 2 = x*y + a*b := by
  ring

/-- Positive finite-patch data cannot yield a vanishing comparison factor. -/
theorem finite_patch_factor_positive {g m r : ℝ}
    (hg : 0 < g) (hm : 0 < m) (hr : r < 1) :
    0 < (g/m)*(1-r) := by
  exact mul_pos (div_pos hg hm) (sub_pos.mpr hr)

/-- Integration endpoint for an already supplied quadratic-form comparison. -/
theorem transfer_quadratic_lower_bound
    {micro blocked ground g m c : ℝ}
    (hm : 0 < m) (hg : 0 ≤ g)
    (hpatch : g * blocked ≤ m * micro)
    (hblock : c * ground ≤ blocked) :
    (g/m) * c * ground ≤ micro := by
  have h := mul_le_mul_of_nonneg_left hblock hg
  have hh : g * (c * ground) ≤ m * micro := le_trans h hpatch
  have hdiv : (g * (c * ground)) / m ≤ micro := by
    apply (div_le_iff₀ hm).mpr
    simpa only [mul_comm micro m] using hh
  have heq : (g * (c * ground)) / m = (g/m) * c * ground := by ring
  simpa only [heq] using hdiv

end UrgentFormalization
