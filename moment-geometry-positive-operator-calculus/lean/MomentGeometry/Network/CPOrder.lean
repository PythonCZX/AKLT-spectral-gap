/-
MomentGeometry/Network/CPOrder.lean

Order and composition laws for the finite completely positive maps of
`MomentGeometry.Operator.CP.Base`, as needed by the CP transport layer of
`q:thm-wire-gap`.

The sandwich `q:cp-sandwich` of the source is the relation
`Φ ≤_CP Ψ  :⟺  Ψ - Φ` completely positive.  This file proves that it is a
preorder, that amplification is functorial, and that CP maps are closed under
composition and addition.  Tensor products of CP maps, and the signed-average
("quadratic cancellation") identity for mixed defects, are *not* proved here.
-/
import MomentGeometry.Operator.CP.Base

open Matrix
open scoped BigOperators ComplexOrder

namespace MomentGeometry.Operator.CP

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Amplification is functorial: `amp (Φ ∘ Ψ) = amp Φ ∘ amp Ψ` on matrices. -/
theorem amp_comp {ν : Type u} [Fintype ν]
    (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) (A : Matrix (ι × ν) (ι × ν) ℂ) :
    amp (Φ.comp Ψ) A = amp Φ (amp Ψ A) := by
  ext p q
  simp only [amp]
  rfl

theorem amp_add {ν : Type u} [Fintype ν]
    (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) (A : Matrix (ι × ν) (ι × ν) ℂ) :
    amp (Φ + Ψ) A = amp Φ A + amp Ψ A := by
  ext p q
  simp only [amp, Matrix.add_apply]
  rfl

theorem amp_zero {ν : Type u} [Fintype ν] (A : Matrix (ι × ν) (ι × ν) ℂ) :
    amp (0 : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) A = 0 := by
  ext p q
  simp only [amp, Matrix.zero_apply]
  rfl

/-- Composition closure is already available as
`MomentGeometry.Operator.CP.IsCP.comp` in `Operator/CP/Base`; `amp_comp` above
identifies the amplification used there with the functorial one. -/
theorem IsCP.comp' {Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ}
    (hΦ : IsCP Φ) (hΨ : IsCP Ψ) : IsCP (Φ.comp Ψ) :=
  IsCP.comp hΦ hΨ

/-- Completely positive maps are closed under addition. -/
theorem IsCP.add {Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ}
    (hΦ : IsCP Φ) (hΨ : IsCP Ψ) : IsCP (Φ + Ψ) := by
  intro ν _ A hA
  rw [amp_add]
  exact (hΦ ν A hA).add (hΨ ν A hA)

/-- The zero map is completely positive. -/
theorem IsCP.zero : IsCP (0 : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) := by
  intro ν _ A _
  rw [amp_zero]
  exact Matrix.PosSemidef.zero

/-- The CP sandwich order `Φ ≤_CP Ψ` of `q:cp-sandwich`: `Ψ - Φ` is CP. -/
def CPLe (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) : Prop := IsCP (Ψ - Φ)

theorem CPLe.refl (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) : CPLe Φ Φ := by
  have h : Φ - Φ = 0 := sub_self Φ
  rw [CPLe, h]
  exact IsCP.zero

theorem CPLe.trans {Φ Ψ Θ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ}
    (h₁ : CPLe Φ Ψ) (h₂ : CPLe Ψ Θ) : CPLe Φ Θ := by
  have h : Θ - Φ = (Θ - Ψ) + (Ψ - Φ) := by abel
  rw [CPLe, h]
  exact h₂.add h₁

end MomentGeometry.Operator.CP

#print axioms MomentGeometry.Operator.CP.amp_comp
#print axioms MomentGeometry.Operator.CP.IsCP.comp'
#print axioms MomentGeometry.Operator.CP.IsCP.add
#print axioms MomentGeometry.Operator.CP.CPLe.trans
