/-
The wire contraction scalar and the exact rational transfer radius agree.

`AKLT.Wire` proves `Phi^[l] X = (-1/3)^l X` on trace-zero matrices, while
`AKLT.Radius` studies the rational scalar `beta_l = (-1)^l / 3^l` and the transfer
radius `delta_l = 2/(3^l + (-1)^l)`.  This file records that these are the same
number, so the operator statement of the wire and the exact rational certificate
of `q:cor-aklt` speak about one scalar.
-/
import Mathlib
import MomentGeometry.AKLT.Wire
import MomentGeometry.AKLT.Radius

namespace MomentGeometry.AKLT

/-- The complex wire scalar `(-1/3)^l` is the rational `beta_l`. -/
theorem neg_third_pow_eq_beta (l : ℕ) : (-(1 / 3) : ℂ) ^ l = ((beta l : ℚ) : ℂ) := by
  rw [beta]
  push_cast
  have h : (-(1 / 3) : ℂ) = (-1) / 3 := by ring
  rw [h, div_pow]

/-- The traceless wire contraction is multiplication by the exact rational
transfer scalar of `q:aklt-radius`. -/
theorem wire_contraction_matches_radius (l : ℕ) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : Matrix.trace X = 0) :
    phi^[l] X = ((beta l : ℚ) : ℂ) • X := by
  rw [phi_iterate_of_trace_zero l hX, neg_third_pow_eq_beta]

end MomentGeometry.AKLT
