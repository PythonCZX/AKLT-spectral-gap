/-
Source-faithful finite unit-density moment forms.
This adds the D_{2m}-free fourth-moment form and exact small-family examples;
it is deliberately separate from the optional D'=D(D+1) specialization.
-/
import MomentGeometry.Coherent.Moments

namespace MomentGeometry.Coherent

/-- Exact unit-density fourth formula with the source parameter `D' = D_{2m}`
left free.  The constant term is 14 and the `D'` term is not expanded: the
limit `D/D' -> 2^{-q}` carries the source's `14 + 2^{-q}` remainder. -/
theorem expectedT4_unit_density_general (D D' : ℚ) (hD : D ≠ 0) (hD' : D' ≠ 0) :
    expectedT4 D D D' = 14 + (D - 1) / D' - 30 / D + 23 / D ^ 2 - 6 / D ^ 3 := by
  unfold expectedT4
  field_simp
  ring

/-- Exact source instance `q = 2`, `m = 1`: `D = D_1 = 3`, `D' = D_2 = 6`,
`n = D` (unit density, `rho = 1`).  The exact value is `20/3`, not `14`; the
limiting `57/4` is the `m -> infinity` free moment, not this finite
expectation. -/
theorem expectedT4_unit_density_q2_m1 :
    expectedT4 3 3 6 = 20 / 3 := by
  norm_num [expectedT4]

/-- The exact `q = 1` family: `D = m + 1`, `D' = D_{2m} = 2m + 1 = 2D - 1`,
`n = D`.  The deviation from the limiting `29/2 = 14 + 2^{-1}` is displayed
explicitly, so no unspecified limit is being asserted. -/
theorem expectedT4_unit_density_q1_family (D : ℚ) (hD : D ≠ 0) (h2 : 2 * D - 1 ≠ 0) :
    expectedT4 D D (2 * D - 1) =
      29 / 2 - 1 / (2 * (2 * D - 1)) - 30 / D + 23 / D ^ 2 - 6 / D ^ 3 := by
  rw [expectedT4_unit_density_general D (2 * D - 1) hD h2]
  have key : (D - 1) / (2 * D - 1) = 1 / 2 - 1 / (2 * (2 * D - 1)) := by
    have h : (D - 1) / (2 * D - 1) + (1 / 2) / (2 * D - 1) = 1 / 2 := by
      rw [← add_div, div_eq_iff h2]
      ring
    have h2' : (1 / 2) / (2 * D - 1) = 1 / (2 * (2 * D - 1)) := by rw [div_div]
    rw [h2'] at h
    linarith
  rw [key]
  ring

/-- Same `q = 1` family rewritten with the correction isolated. -/
theorem expectedT4_unit_density_q1_family_deviation (D : ℚ) (hD : D ≠ 0)
    (h2 : 2 * D - 1 ≠ 0) :
    expectedT4 D D (2 * D - 1) - 29 / 2 =
      -1 / (2 * (2 * D - 1)) - 30 / D + 23 / D ^ 2 - 6 / D ^ 3 := by
  rw [expectedT4_unit_density_q1_family D hD h2]
  ring


end MomentGeometry.Coherent
