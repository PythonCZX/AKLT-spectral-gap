/-
Finite Kraus families for the completely-positive interfaces.

This is a finite-dimensional realization, not a symbolic `channel_gap_compiler`
output. The amplification definition matches `MomentGeometry.Operator.CP.IsCP`.
-/
import MomentGeometry.Operator.CP.Closure

namespace MomentGeometry.Operator.CP

open Matrix
open scoped Classical ComplexOrder BigOperators
noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A finite family of Kraus matrices defines a completely-positive map. -/
noncomputable def krausMap {κ : Type u} [Fintype κ]
    (K : κ → Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun A := ∑ k, K k * A * (K k).conjTranspose
  map_add' A B := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    exact Finset.sum_add_distrib
  map_smul' r A := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [RingHom.id_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul]

lemma krausMap_apply {κ : Type u} [Fintype κ]
    (K : κ → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) :
    krausMap K A = ∑ k, K k * A * (K k).conjTranspose := rfl

lemma krausMap_eq_sum_conjMap {κ : Type u} [Fintype κ]
    (K : κ → Matrix ι ι ℂ) :
    krausMap K = ∑ k, conjMap (K k) := by
  ext A i j
  simp only [LinearMap.sum_apply, krausMap, LinearMap.coe_mk, AddHom.coe_mk,
    conjMap, Matrix.sum_apply]

/-- Complete positivity of the zero map in this matrix realization. -/
theorem isCP_zero : IsCP (0 : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) := by
  intro ν _ A _
  have hzero : (0 : Matrix (ι × ν) (ι × ν) ℂ).PosSemidef := PosSemidef.zero
  convert hzero using 1
  ext p q
  rfl

/-- Complete positivity is closed under finite sums. -/
theorem isCP_sum {κ : Type u} [Fintype κ]
    (f : κ → Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) (hf : ∀ k, IsCP (f k)) :
    IsCP (∑ k, f k) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty =>
      simpa using (isCP_zero (ι := ι))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      intro ν _ A hA
      change (amp (f a) A + amp (∑ x ∈ s, f x) A).PosSemidef
      exact (hf a ν A hA).add (ih ν A hA)

/-- Finite Kraus representations imply complete positivity. No trace
preservation or unitality is assumed; those are separate operator data. -/
theorem isCP_krausMap {κ : Type u} [Fintype κ]
    (K : κ → Matrix ι ι ℂ) : IsCP (krausMap K) := by
  rw [krausMap_eq_sum_conjMap]
  exact isCP_sum (fun k => conjMap (K k)) (fun k => isCP_conjMap (K k))

end

end MomentGeometry.Operator.CP

#print axioms MomentGeometry.Operator.CP.krausMap_eq_sum_conjMap
#print axioms MomentGeometry.Operator.CP.isCP_zero
#print axioms MomentGeometry.Operator.CP.isCP_sum
#print axioms MomentGeometry.Operator.CP.isCP_krausMap
