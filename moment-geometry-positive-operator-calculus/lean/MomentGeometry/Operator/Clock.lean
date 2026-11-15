/-
Source contract `op:hyperbolic-clock`.
Finite-dimensional hyperbolic clock filters with the positive difference kernel.
This file exposes verified components, not the separate fractional-power response
identity required by `q:thm-powers`.
-/
import MomentGeometry.Operator.CP.Closure

namespace MomentGeometry.Operator.Clock

open Matrix
open scoped ComplexOrder

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Complete positivity of the multipliers at exponent zero, the identity filter. -/
theorem completelyPositive_sinhc_zero (k : ι → ℝ) :
    MomentGeometry.Operator.CP.IsCP
      (MomentGeometry.Operator.CP.multMap k (MomentGeometry.Operator.CP.sinhcSymRpow 0)) :=
  MomentGeometry.Operator.CP.isCP_sinhc_rpow_zero k

/-- Complete positivity at every positive real exponent. -/
theorem completelyPositive_sinhc_rpow (k : ι → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    MomentGeometry.Operator.CP.IsCP
      (MomentGeometry.Operator.CP.multMap k (MomentGeometry.Operator.CP.sinhcSymRpow τ)) :=
  MomentGeometry.Operator.CP.isCP_sinhc_rpow_uncond k hτ

/-- The Choi-style positivity criterion at the multiplier interface. -/
theorem completelyPositive_iff_kernel (k : ι → ℝ) (f : ℝ → ℂ) :
    MomentGeometry.Operator.CP.IsCP (MomentGeometry.Operator.CP.multMap k f) ↔
      (MomentGeometry.Operator.CP.Kmat k f).PosSemidef :=
  MomentGeometry.Operator.CP.isCP_multMap_iff k f

end MomentGeometry.Operator.Clock

#print axioms MomentGeometry.Operator.Clock.completelyPositive_sinhc_zero
#print axioms MomentGeometry.Operator.Clock.completelyPositive_sinhc_rpow
#print axioms MomentGeometry.Operator.Clock.completelyPositive_iff_kernel
#print axioms MomentGeometry.Operator.CP.bundle_sinhc
#print axioms MomentGeometry.Operator.CP.bundle_sinhc_rpow
#print axioms MomentGeometry.Operator.CP.isCP_spectralFilter
