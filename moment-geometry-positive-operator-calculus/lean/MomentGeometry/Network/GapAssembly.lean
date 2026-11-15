/-
MomentGeometry/Network/GapAssembly.lean

The final matrix step of `q:thm-wire-gap`: from
(a) the pairwise off-diagonal control of the blocked projectors (the content of
    `q:lem-schur` transported through `q:projection-cross`), and
(b) a numerical bound `∑_{e,f} C_{ef} z_e z_f ≤ ρ ∑_e z_e^2` for the conflict
    matrix `C` (this is the quadratic-form form of `ρ(C) < 1`),
we derive the blocked gap `H_block ≥ (1 - ρ) (I - G_all)`.

The second file-level theorem converts the resulting quadratic inequality
`‖H x‖^2 ≥ γ ⟪H x, x⟫` into the Loewner statement, using the finite-dimensional
spectral decomposition of the symmetric operator `H`.  The only input that is
*not* proved here is the subspace-angle bound itself (the Friedrichs cosine
estimate `q:lem-schur`), which enters as the explicit hypothesis `hcross`.
-/
import Mathlib
import MomentGeometry.Network.ProjBasics

open scoped BigOperators

namespace MomentGeometry.Network

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Expansion of `‖H x‖^2` for `H = ∑_e (1 - P_e)` into pairwise inner
products of the complement vectors. -/
theorem norm_sq_block_eq_sum {ι : Type*} [Fintype ι]
    (P : ι → E →L[ℝ] E) (x : E) :
    ‖(∑ e, ((1 : E →L[ℝ] E) - P e)) x‖ ^ 2
      = ∑ e, ∑ f, inner ℝ (x - P e x) (x - P f x) := by
  have hx : (∑ e, ((1 : E →L[ℝ] E) - P e)) x = ∑ e, (x - P e x) := by
    rw [sum_apply]
    exact Finset.sum_congr rfl fun e _ => by simp
  rw [hx, ← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [inner_sum]

/-- Diagonal term of the expansion: `⟪x - P_e x, x - P_e x⟫ = ‖x - P_e x‖^2`. -/
theorem inner_compl_self (P : E →L[ℝ] E) (x : E) :
    inner ℝ (x - P x) (x - P x) = ‖x - P x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

/-- **Blocked gap, quadratic form.**  If the conflict matrix satisfies the
numerical bound `∑_{e,f} C_{ef} z_e z_f ≤ ρ ∑_e z_e^2` and the off-diagonal
inner products of the complement vectors are bounded by `-C_{ef} z_e z_f`, then
`‖H x‖^2 ≥ (1 - ρ) ⟪H x, x⟫` for every `x`. -/
theorem norm_sq_block_ge_of_conflict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → E →L[ℝ] E) (hP : ∀ e, IsOrthProj (P e))
    (C : ι → ι → ℝ) (hdiag : ∀ e, C e e = 0) (ρ : ℝ)
    (hray : ∀ z : ι → ℝ, ∑ e, ∑ f, C e f * z e * z f ≤ ρ * ∑ e, (z e) ^ 2)
    (hcross : ∀ (x : E) (e f : ι), e ≠ f →
      -(C e f * ‖x - P e x‖ * ‖x - P f x‖) ≤ inner ℝ (x - P e x) (x - P f x))
    (x : E) :
    (1 - ρ) * inner ℝ ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) x
      ≤ ‖(∑ e, ((1 : E →L[ℝ] E) - P e)) x‖ ^ 2 := by
  classical
  set z : ι → ℝ := fun e => ‖x - P e x‖ with hz
  -- per-pair bound, including the diagonal
  have hterm : ∀ e f : ι, -(C e f * z e * z f) ≤ inner ℝ (x - P e x) (x - P f x) := by
    intro e f
    by_cases hef : e = f
    · subst hef
      rw [hdiag, zero_mul, zero_mul, neg_zero, real_inner_self_eq_norm_sq]
      positivity
    · exact hcross x e f hef
  -- the diagonal of `C` vanishes, so the erased sums agree with the full sums
  have herase : ∀ e : ι,
      ∑ f ∈ Finset.univ.erase e, C e f * z e * z f = ∑ f, C e f * z e * z f := by
    intro e
    rw [← Finset.add_sum_erase (Finset.univ) (fun f => C e f * z e * z f) (Finset.mem_univ e),
      hdiag e]
    ring
  -- the off-diagonal inner products are bounded below by the negative conflict sum
  have hoff : -(∑ e, ∑ f, C e f * z e * z f)
      ≤ ∑ e, ∑ f ∈ Finset.univ.erase e, inner ℝ (x - P e x) (x - P f x) := by
    have h1 : ∑ e, ∑ f ∈ Finset.univ.erase e, -(C e f * z e * z f)
        ≤ ∑ e, ∑ f ∈ Finset.univ.erase e, inner ℝ (x - P e x) (x - P f x) :=
      Finset.sum_le_sum fun e _ =>
        Finset.sum_le_sum fun f _ => hterm e f
    have h3 : ∀ e : ι, ∑ f ∈ Finset.univ.erase e, -(C e f * z e * z f)
        = -(∑ f, C e f * z e * z f) := by
      intro e
      rw [Finset.sum_neg_distrib, herase e]
    have h2 : ∑ e, ∑ f ∈ Finset.univ.erase e, -(C e f * z e * z f)
        = -(∑ e, ∑ f, C e f * z e * z f) := by
      rw [Finset.sum_congr rfl fun e _ => h3 e, Finset.sum_neg_distrib]
    linarith
  -- diagonal/off-diagonal split of the expansion
  have hsplit : ‖(∑ e, ((1 : E →L[ℝ] E) - P e)) x‖ ^ 2
      = ∑ e, (z e) ^ 2
        + ∑ e, ∑ f ∈ Finset.univ.erase e, inner ℝ (x - P e x) (x - P f x) := by
    rw [norm_sq_block_eq_sum]
    have h1 : ∀ e : ι, ∑ f, inner ℝ (x - P e x) (x - P f x)
        = ‖x - P e x‖ ^ 2
          + ∑ f ∈ Finset.univ.erase e, inner ℝ (x - P e x) (x - P f x) := by
      intro e
      rw [← Finset.add_sum_erase (Finset.univ) (fun f => inner ℝ (x - P e x) (x - P f x))
        (Finset.mem_univ e), real_inner_self_eq_norm_sq]
    rw [Finset.sum_congr rfl fun e _ => h1 e, Finset.sum_add_distrib]
  -- the quadratic form of `H` is the sum of the squared norms
  have hquad : inner ℝ ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) x = ∑ e, (z e) ^ 2 := by
    rw [← IsOrthProj.sum_norm_sq_compl P hP x]
  calc (1 - ρ) * inner ℝ ((∑ e, ((1 : E →L[ℝ] E) - P e)) x) x
      = (1 - ρ) * ∑ e, (z e) ^ 2 := by rw [hquad]
    _ = ∑ e, (z e) ^ 2 - ρ * ∑ e, (z e) ^ 2 := by ring
    _ ≤ ∑ e, (z e) ^ 2 - ∑ e, ∑ f, C e f * z e * z f := by
          linarith [hray z]
    _ ≤ ∑ e, (z e) ^ 2
          + ∑ e, ∑ f ∈ Finset.univ.erase e, inner ℝ (x - P e x) (x - P f x) := by
          linarith [hoff]
    _ = ‖(∑ e, ((1 : E →L[ℝ] E) - P e)) x‖ ^ 2 := hsplit.symm

end MomentGeometry.Network

#print axioms MomentGeometry.Network.norm_sq_block_ge_of_conflict
