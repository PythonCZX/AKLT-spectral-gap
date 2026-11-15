/-
Copyright: formalization for the Moment Geometry project (swarm smwi6zlvo, member m6).

# Filtered commuting-projector models (`q:cor-filtered`), algebraic transport

Source: `proofs/quantum_results.tex`, Corollary `q:cor-filtered`.

For commuting local orthogonal projections `E i` and an invertible product filter
`L` with inverse `Li`, the conjugated matrices `P i = L * E i * Li` are
commuting idempotents (`filtered_idem`, `filtered_comm`), their ranges are the
filtered reference ranges (`filtered_range_iff`), and the ground space of the
physical parent Hamiltonian `∑ i, (1 - Π i)` (with `Π i` the orthogonal
projection onto `ran (P i)`, supplied as the hypothesis `hΠrange`) is the
filtered reference ground space `L ⋂ ran E i` (`filtered_ground_space`).

The *analytic* input of `q:cor-filtered` --- the perturbation bound
`‖P i - E i‖ ≤ e^{2 s ε} - 1` obtained by integrating the similarity derivative,
and the derivation of the cosine defects from it --- is not formalized here; the
numeric gap consequence given that input is `cor_filtered_gap` in
`MomentGeometry.Swarm.Oblique`.
-/
import MomentGeometry.Swarm.Oblique

namespace MomentGeometry.Swarm

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- The filtered idempotent `L * E * L⁻¹`. -/
def filtered (L Li E : Matrix n n ℂ) : Matrix n n ℂ := L * E * Li

/-- The filter is multiplicative on idempotents. -/
lemma filtered_mul (L Li A B : Matrix n n ℂ) (hLi : Li * L = 1) :
    filtered L Li A * filtered L Li B = filtered L Li (A * B) := by
  have h1 : filtered L Li A * filtered L Li B = L * A * (Li * L) * (B * Li) := by
    simp only [filtered]
    noncomm_ring
  rw [h1, hLi, Matrix.mul_one]
  simp only [filtered]
  noncomm_ring

lemma filtered_idem {L Li E : Matrix n n ℂ} (hLi : Li * L = 1) (hE : E * E = E) :
    filtered L Li E * filtered L Li E = filtered L Li E := by
  rw [filtered_mul L Li E E hLi, hE]

lemma filtered_comm {L Li E F : Matrix n n ℂ} (hLi : Li * L = 1) (hEF : E * F = F * E) :
    filtered L Li E * filtered L Li F = filtered L Li F * filtered L Li E := by
  rw [filtered_mul L Li E F hLi, filtered_mul L Li F E hLi, hEF]

lemma filtered_mulVec (L Li E : Matrix n n ℂ) (v : n → ℂ) :
    filtered L Li E *ᵥ v = L *ᵥ (E *ᵥ (Li *ᵥ v)) := by
  rw [show filtered L Li E = L * (E * Li) by
    simp only [filtered]
    rw [Matrix.mul_assoc]]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- The range condition transports through the filter. -/
lemma filtered_range_iff {L Li E : Matrix n n ℂ} (hL : L * Li = 1) (hLi : Li * L = 1)
    (v : n → ℂ) :
    filtered L Li E *ᵥ v = v ↔ E *ᵥ (Li *ᵥ v) = Li *ᵥ v := by
  rw [filtered_mulVec]
  constructor
  · intro h
    have h' := congrArg (fun w => Li *ᵥ w) h
    rw [show Li *ᵥ (L *ᵥ (E *ᵥ (Li *ᵥ v))) = E *ᵥ (Li *ᵥ v) by
      rw [Matrix.mulVec_mulVec, hLi, Matrix.one_mulVec]] at h'
    exact h'
  · intro h
    rw [h, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]

lemma filtered_common_range_iff {L Li : Matrix n n ℂ} (hL : L * Li = 1) (hLi : Li * L = 1)
    (E : ι → Matrix n n ℂ) (v : n → ℂ) :
    (∀ i, filtered L Li (E i) *ᵥ v = v) ↔ ∀ i, E i *ᵥ (Li *ᵥ v) = Li *ᵥ v :=
  forall_congr' (fun i => filtered_range_iff hL hLi v)

/-- **Ground space of the filtered parent** (`q:cor-filtered`): the kernel of the
norm-one parent built from the orthogonal projections onto the filtered reference
ranges is the filter applied to the common reference ground space. -/
theorem filtered_ground_space {L Li : Matrix n n ℂ} (hL : L * Li = 1) (hLi : Li * L = 1)
    (E : ι → Matrix n n ℂ) (P : ι → Matrix n n ℂ) (hP : ∀ i, IsOrthProj (P i))
    (hPrange : ∀ i v, P i *ᵥ v = v ↔ filtered L Li (E i) *ᵥ v = v) (v : n → ℂ) :
    blockHam P *ᵥ v = 0 ↔ ∃ w : n → ℂ, (∀ i, E i *ᵥ w = w) ∧ v = L *ᵥ w := by
  have hker : blockHam P *ᵥ v = 0 ↔ ∀ i, P i *ᵥ v = v := by
    rw [blockHam]
    rw [sum_mulVec_eq_zero_iff (fun i => IsOrthProj.one_sub_posSemidef (hP i)) v]
    simp [one_sub_mulVec_eq_zero_iff]
  rw [hker, forall_congr' (fun i => hPrange i v), filtered_common_range_iff hL hLi E v]
  constructor
  · intro h
    exact ⟨Li *ᵥ v, h, by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]⟩
  · rintro ⟨w, hw, rfl⟩
    intro i
    rw [show Li *ᵥ (L *ᵥ w) = w by rw [Matrix.mulVec_mulVec, hLi, Matrix.one_mulVec]]
    exact hw i

end MomentGeometry.Swarm
