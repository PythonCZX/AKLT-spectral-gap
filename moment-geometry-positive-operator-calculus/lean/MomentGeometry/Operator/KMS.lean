/-
Compatibility of Hermitian and anti-Hermitian divided differences, at the
scalar kernel level required by `q:kms-compatibility`.

The scalar identities do not by themselves prove the general matrix-integral
representation. They expose the precise hyperbolic transport laws that the
matrix-level spectral proof must implement without treating H and A as independent.
-/
import Mathlib

namespace MomentGeometry.Operator.KMS

/-- The Hermitian response kernel with its continuous value `r` at zero. -/
noncomputable def hermitianPart (r : ℝ) : ℝ → ℝ := fun x =>
  if x = 0 then r else (Real.sinh (r * x)) / Real.sinh x

/-- The anti-Hermitian response kernel, normalized against the denominator
`cosh(x)-1`, so its continuous value at zero is `r²`. -/
noncomputable def antiPart (r : ℝ) : ℝ → ℝ := fun x =>
  if x = 0 then r ^ 2 else (Real.cosh (r * x) - 1) / (Real.cosh x - 1)

@[simp] theorem hermitianPart_at_zero (r : ℝ) : hermitianPart r 0 = r := by
  simp [hermitianPart]

@[simp] theorem antiPart_at_zero (r : ℝ) : antiPart r 0 = r ^ 2 := by
  simp [antiPart]

/-- `(cosh z - 1)/sinh z = tanh(z/2)`, away from the removable singularity. -/
theorem cosh_sub_one_div_sinh_eq_tanh_half {x : ℝ} (hx : x ≠ 0) :
    (Real.cosh x - 1) / Real.sinh x = Real.tanh (x / 2) := by
  have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have hy : x / 2 ≠ 0 := by intro h; apply hx; linarith
  have hhalf : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr hy
  have hS : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    calc Real.sinh x = Real.sinh (2 * (x / 2)) := by ring_nf
      _ = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := Real.sinh_two_mul _
  have hC : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
    calc Real.cosh x - 1 = Real.cosh (2 * (x / 2)) - 1 := by ring_nf
      _ = (Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2) - 1 := by
        rw [Real.cosh_two_mul]
      _ = 2 * Real.sinh (x / 2) ^ 2 := by
        have h := Real.cosh_sq_sub_sinh_sq (x / 2)
        nlinarith
  rw [hS, hC, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- The anti-Hermitian response kernel is the advertised square of half ratios. -/
theorem antiPart_eq_ratio_sq (r : ℝ) {x : ℝ} (hx : x ≠ 0) :
    antiPart r x = (Real.sinh (r * x / 2) / Real.sinh (x / 2)) ^ 2 := by
  have hy : x / 2 ≠ 0 := by intro h; apply hx; linarith
  have hrx : r * x / 2 = (r * x) / 2 := by ring
  have factor : ∀ y : ℝ, Real.cosh y - 1 = 2 * Real.sinh (y / 2) ^ 2 := by
    intro y
    calc Real.cosh y - 1 = Real.cosh (2 * (y / 2)) - 1 := by ring_nf
      _ = (Real.cosh (y / 2) ^ 2 + Real.sinh (y / 2) ^ 2) - 1 := by
        rw [Real.cosh_two_mul]
      _ = 2 * Real.sinh (y / 2) ^ 2 := by
        have h := Real.cosh_sq_sub_sinh_sq (y / 2)
        nlinarith
  simp only [antiPart, hx, if_false]
  rw [factor, factor]
  field_simp


/-- KMS compatibility at the scalar divided-difference level:
the anti-Hermitian response `χ_r` times the base `tanh(x/2)` is
`tanh(rx/2)` times the Hermitian response `ψ_r`. -/
theorem antiPart_compatibility (r : ℝ) {x : ℝ} (hx : x ≠ 0) :
    antiPart r x * Real.tanh (x / 2) =
      Real.tanh (r * x / 2) * hermitianPart r x := by
  have hy : x / 2 ≠ 0 := by intro h; apply hx; linarith
  have hhalf : Real.cosh (x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hrcosh : Real.cosh (r * x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hsx : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr hy
  have hrep : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    calc Real.sinh x = Real.sinh (2 * (x / 2)) := by ring_nf
      _ = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := Real.sinh_two_mul _
  calc antiPart r x * Real.tanh (x / 2)
      = (Real.sinh (r * x / 2) / Real.sinh (x / 2)) ^ 2 * Real.tanh (x / 2) := by
        rw [antiPart_eq_ratio_sq r hx]
    _ = (Real.sinh (r * x / 2) / Real.cosh (r * x / 2)) *
        (Real.sinh (r * x) / Real.sinh x) := by
        have hrephalf : Real.sinh (r * x) =
            2 * Real.sinh (r * x / 2) * Real.cosh (r * x / 2) := by
          calc Real.sinh (r * x) = Real.sinh (2 * (r * x / 2)) := by ring_nf
            _ = 2 * Real.sinh (r * x / 2) * Real.cosh (r * x / 2) :=
              Real.sinh_two_mul _
        rw [Real.tanh_eq_sinh_div_cosh, hrep, hrephalf]
        field_simp
    _ = Real.tanh (r * x / 2) * hermitianPart r x := by
        rw [Real.tanh_eq_sinh_div_cosh]
        simp [hermitianPart, hx]

/-- Compositions use exactly the exponent laws appearing in the paper. -/
theorem hermitian_composition (r s : ℝ) (x : ℝ) :
    hermitianPart s (r * x) * hermitianPart r x = hermitianPart (r * s) x := by
  simp only [hermitianPart]
  by_cases hx : x = 0
  · subst x
    simp [mul_comm]
  by_cases hr : r = 0
  · subst r
    simp
  have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have hr0 : r * x ≠ 0 := mul_ne_zero hr hx
  have hsinhr : Real.sinh (r * x) ≠ 0 := Real.sinh_ne_zero.mpr hr0
  simp only [hx, hr0, if_false]
  rw [show s * (r * x) = (r * s) * x by ring]
  field_simp

end MomentGeometry.Operator.KMS

#print axioms MomentGeometry.Operator.KMS.cosh_sub_one_div_sinh_eq_tanh_half
#print axioms MomentGeometry.Operator.KMS.antiPart_compatibility
#print axioms MomentGeometry.Operator.KMS.antiPart_eq_ratio_sq
#print axioms MomentGeometry.Operator.KMS.hermitian_composition
