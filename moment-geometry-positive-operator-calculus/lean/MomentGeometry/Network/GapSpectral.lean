/-
MomentGeometry/Network/GapSpectral.lean

The spectral step of the blocked gap criterion.

`q:thm-wire-gap` produces the quadratic inequality `‖H x‖² ≥ (1-ρ)⟪H x, x⟫` for
the norm-one projector parent `H = ∑_e (I - G_e)`.  The Loewner form
`H ≥ (1-ρ)(I - G_all)` is a finite-dimensional spectral statement about the
symmetric operator `H`: because `H` is positive semidefinite, the eigenvalues on
the orthogonal complement of its kernel are either `0` or at least `1-ρ`.

Both facts are proved here from the eigenvalue decomposition of a symmetric
operator, with no additional hypothesis.
-/
import Mathlib
import MomentGeometry.Network.ProjBasics

open scoped BigOperators

namespace MomentGeometry.Network

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Spectral step.**  Let `H` be symmetric and positive semidefinite with
`γ⟪H x, x⟫ ≤ ⟪H x, H x⟫` for all `x` and `0 ≤ γ`.  Then `γ‖x‖² ≤ ⟪H x, x⟫`
whenever `x` is orthogonal to the kernel of `H`. -/
theorem gap_on_kernel_orthogonal (H : E →L[ℝ] E) (hH : IsSymOp H)
    (hpsd : ∀ x : E, 0 ≤ inner ℝ (H x) x) (γ : ℝ)
    (h2 : ∀ x : E, γ * inner ℝ (H x) x ≤ inner ℝ (H x) (H x)) :
    ∀ x : E, (∀ y : E, H y = 0 → inner ℝ x y = 0) → γ * ‖x‖ ^ 2 ≤ inner ℝ (H x) x := by
  intro x hx
  classical
  set T : E →ₗ[ℝ] E := (H : E →ₗ[ℝ] E) with hT
  have hTsym : T.IsSymmetric := hH
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := hTsym.eigenvectorBasis rfl
  let lam : Fin (Module.finrank ℝ E) → ℝ := hTsym.eigenvalues rfl
  have hBeigen : ∀ i, T (b i) = (lam i : ℝ) • b i := fun i =>
    hTsym.apply_eigenvectorBasis rfl i
  have hBnorm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hparseval : ∀ y z : E, ∑ i, inner ℝ y (b i) * inner ℝ (b i) z = inner ℝ y z :=
    fun y z => b.sum_inner_mul_inner y z
  -- the diagonal value of the quadratic form on an eigenvector
  have hdiag : ∀ i, inner ℝ (H (b i)) (b i) = lam i := by
    intro i
    have h := hBeigen i
    rw [show H (b i) = T (b i) from rfl, h, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hBnorm i]
    ring
  have hdiag2 : ∀ i, inner ℝ (H (b i)) (H (b i)) = lam i * lam i := by
    intro i
    have h := hBeigen i
    rw [show H (b i) = T (b i) from rfl, h, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hBnorm i]
    ring
  have hlam0 : ∀ i, 0 ≤ lam i := by
    intro i
    have h := hpsd (b i)
    rw [hdiag i] at h
    exact h
  have hlamge : ∀ i, lam i ≠ 0 → γ ≤ lam i := by
    intro i hi
    have h := h2 (b i)
    rw [hdiag i, hdiag2 i] at h
    have hpos : 0 < lam i := lt_of_le_of_ne (hlam0 i) (Ne.symm hi)
    nlinarith
  have hker : ∀ i, lam i = 0 → inner ℝ (b i) x = 0 := by
    intro i hi
    have hTb : T (b i) = 0 := by rw [hBeigen i, hi]; simp
    have h1 : inner ℝ x (b i) = 0 := hx (b i) hTb
    rw [real_inner_comm]
    exact h1
  have hexp : inner ℝ (H x) x = ∑ i, lam i * (inner ℝ (b i) x) ^ 2 := by
    have key : inner ℝ (H x) x = ∑ i, inner ℝ x (b i) * inner ℝ (b i) (H x) := by
      rw [← real_inner_comm (H x) x, ← hparseval x (H x)]
    have step : ∀ i, inner ℝ (b i) (H x) = lam i * inner ℝ (b i) x := by
      intro i
      have h1 : inner ℝ (b i) (H x) = inner ℝ (T (b i)) x := (hTsym (b i) x).symm
      rw [h1, hBeigen i, real_inner_smul_left]
    rw [key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← real_inner_comm x (b i), step i]
    ring
  have hnorm : ‖x‖ ^ 2 = ∑ i, (inner ℝ (b i) x) ^ 2 := by
    have key : ‖x‖ ^ 2 = ∑ i, inner ℝ x (b i) * inner ℝ (b i) x := by
      rw [← real_inner_self_eq_norm_sq, ← hparseval x x]
    rw [key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← real_inner_comm x (b i)]
    ring
  calc γ * ‖x‖ ^ 2 = ∑ i, γ * (inner ℝ (b i) x) ^ 2 := by
        rw [hnorm, Finset.mul_sum]
    _ ≤ ∑ i, lam i * (inner ℝ (b i) x) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : lam i = 0
        · rw [hi, hker i hi]; simp
        · exact mul_le_mul_of_nonneg_right (hlamge i hi) (sq_nonneg _)
    _ = inner ℝ (H x) x := hexp.symm

/-- **Blocked gap in Loewner form.**  Let `H` be the norm-one projector parent
(symmetric, positive semidefinite) and `G` the orthogonal projection onto its
full ground space `ker H`.  If `γ⟪H x, x⟫ ≤ ⟪H x, H x⟫` for all `x`, then
`γ‖x - G x‖² ≤ ⟪H x, x⟫`, i.e. `H ≥ γ (I - G)` as quadratic forms. -/
theorem gap_loewner (H G : E →L[ℝ] E) (hH : IsSymOp H) (hG : IsOrthProj G)
    (hpsd : ∀ x : E, 0 ≤ inner ℝ (H x) x) (γ : ℝ)
    (h2 : ∀ x : E, γ * inner ℝ (H x) x ≤ inner ℝ (H x) (H x))
    (hHG : ∀ x : E, H (G x) = 0) (hGker : ∀ y : E, H y = 0 → G y = y) :
    ∀ x : E, γ * ‖x - G x‖ ^ 2 ≤ inner ℝ (H x) x := by
  intro x
  have horth : ∀ y : E, H y = 0 → inner ℝ (x - G x) y = 0 := by
    intro y hy
    have hGy : G y = y := hGker y hy
    have h1 : inner ℝ (G x) y = inner ℝ x y := by rw [hG.sym x y, hGy]
    rw [inner_sub_left, h1, sub_self]
  have hkey := gap_on_kernel_orthogonal H hH hpsd γ h2 (x - G x) horth
  have hHsub : H (x - G x) = H x := by
    rw [map_sub, hHG x, sub_zero]
  have hcross : inner ℝ (H x) (G x) = 0 := by
    rw [hH x (G x), hHG x]
    simp
  calc γ * ‖x - G x‖ ^ 2
      ≤ inner ℝ (H (x - G x)) (x - G x) := hkey
    _ = inner ℝ (H x) x := by
        rw [hHsub, inner_sub_right, hcross]
        ring

end MomentGeometry.Network

#print axioms MomentGeometry.Network.gap_on_kernel_orthogonal
#print axioms MomentGeometry.Network.gap_loewner
