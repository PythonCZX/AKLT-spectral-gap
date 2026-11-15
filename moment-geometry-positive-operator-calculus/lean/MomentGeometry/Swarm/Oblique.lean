/-
Copyright: formalization for the Moment Geometry project (swarm smwi6zlvo, member m6).

# The commuting-idempotent defect certificate: analytic heart

Source: `proofs/quantum_results.tex`, Theorem `q:thm-oblique` and Corollary `q:cor-filtered`.

This module formalizes the *finite-dimensional assembly step* that converts a
certified matrix of pairwise principal-angle cosines into a spectral gap for the
norm-one sum `H = ∑ i, (1 - G_i)` of complement projections.  It is the part of
`q:thm-oblique` that the source carries out through the inequalities
`q:projection-cross` and `H^2 ≥ [1 - ρ(B)] H`.

Main result (`defect_gap_qf`, `defect_gap`):

Let `Q i` be orthogonal projections, `b i j` a symmetric nonnegative defect
matrix with zero diagonal, and suppose

* (cosine certificate) `Re ⟨Q i ξ, Q j ξ⟩ ≥ - b i j ‖Q i ξ‖ ‖Q j ξ‖` for `i ≠ j`;
* (defect/Perron data) `∑ i ∑ j [i≠j] b i j z i z j ≤ ρ ∑ i (z i)^2` for all `z ≥ 0`;
* `ρ ≤ 1`.

Then `(1 - ρ) • H ≤ H * H` where `H = ∑ i, Q i`.  Equivalently, the spectrum of
`H` has no point in the open interval `(0, 1 - ρ)`: this is the source's spectral
conclusion `H ≥ [1 - ρ(B)] (I - Π_K)` for `H` in place of the blocked Hamiltonian.

The remaining analytic inputs of `q:thm-oblique` (the orthogonalizer formula,
the commutator bound, and the quotient construction producing the cosine
certificate from the numbers `a_i`, `ε_ij`) are NOT formalized here; see the
ledger.  The module supplies the last, purely finite-dimensional, step.
-/
import MomentGeometry.Swarm.Seed

namespace MomentGeometry.Swarm

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## The Hilbert-space norm and squared norm on `n → ℂ` -/

/-- Squared Hilbert norm, as a real quadratic form on `n → ℂ`. -/
noncomputable def qn (x : n → ℂ) : ℝ := RCLike.re (star x ⬝ᵥ x)

/-- Hilbert norm inherited from the dot product. -/
noncomputable def hn (x : n → ℂ) : ℝ := Real.sqrt (qn x)

lemma qn_eq_qf_one (x : n → ℂ) : qn x = qf 1 x := by
  simp [qn, qf, qfAdd, Matrix.one_mulVec]

lemma qn_nonneg (x : n → ℂ) : 0 ≤ qn x := by
  rw [qn_eq_qf_one]
  exact qf_nonneg PosSemidef.one x

lemma qn_eq_zero_iff (x : n → ℂ) : qn x = 0 ↔ x = 0 := by
  rw [qn_eq_qf_one, qf_eq_zero_iff PosSemidef.one, Matrix.one_mulVec]

lemma hn_nonneg (x : n → ℂ) : 0 ≤ hn x := Real.sqrt_nonneg _

lemma hn_sq (x : n → ℂ) : hn x ^ 2 = qn x := Real.sq_sqrt (qn_nonneg x)

/-! ## Bilinearity of the quadratic form -/

lemma qf_eq_re_dotProduct (A : Matrix n n ℂ) (ξ : n → ℂ) :
    qf A ξ = RCLike.re (star ξ ⬝ᵥ (A *ᵥ ξ)) := rfl

lemma qf_sub (A B : Matrix n n ℂ) (ξ : n → ℂ) : qf (A - B) ξ = qf A ξ - qf B ξ :=
  map_sub (qfAdd ξ) A B

lemma qf_real_smul (r : ℝ) (A : Matrix n n ℂ) (ξ : n → ℂ) :
    qf (r • A) ξ = r * qf A ξ := by
  have h1 : (r • A) *ᵥ ξ = r • (A *ᵥ ξ) := Matrix.smul_mulVec r A ξ
  have h2 : star ξ ⬝ᵥ (r • (A *ᵥ ξ)) = r • (star ξ ⬝ᵥ (A *ᵥ ξ)) :=
    dotProduct_smul r (star ξ) (A *ᵥ ξ)
  rw [qf_eq_re_dotProduct, qf_eq_re_dotProduct, h1, h2]
  simp

/-- `qf (A * B) ξ` is the pairing of `A ξ` with `B ξ` when `A` is self-adjoint. -/
lemma qf_mul_apply (A B : Matrix n n ℂ) (hA : Aᴴ = A) (ξ : n → ℂ) :
    qf (A * B) ξ = RCLike.re (star (A *ᵥ ξ) ⬝ᵥ (B *ᵥ ξ)) := by
  have h1 : (A * B) *ᵥ ξ = A *ᵥ (B *ᵥ ξ) := (Matrix.mulVec_mulVec ξ A B).symm
  have h2 : star (A *ᵥ ξ) = star ξ ᵥ* A := by rw [Matrix.star_mulVec, hA]
  have h3 : (star ξ ᵥ* A) ⬝ᵥ (B *ᵥ ξ) = star ξ ⬝ᵥ (A *ᵥ (B *ᵥ ξ)) :=
    (Matrix.dotProduct_mulVec (star ξ) A (B *ᵥ ξ)).symm
  rw [qf_eq_re_dotProduct, h1, ← h3, h2]

/-- Diagonal defect terms are the squared norms of the projected vectors. -/
lemma qf_sq_self {Q : Matrix n n ℂ} (hQ : IsOrthProj Q) (ξ : n → ℂ) :
    qf (Q * Q) ξ = qn (Q *ᵥ ξ) := by
  rw [qf_mul_apply Q Q hQ.2]
  simp [qn]

/-! ## From quadratic-form positivity to matrix positivity -/

lemma star_dotProduct' (u v : n → ℂ) : star (u ⬝ᵥ v) = star v ⬝ᵥ star u := by
  have h := Matrix.star_dotProduct (star u) v
  rw [star_star] at h
  rw [h, star_star]

lemma dotProduct_self_conj_eq (D : Matrix n n ℂ) (hD : Dᴴ = D) (ξ : n → ℂ) :
    star (star ξ ⬝ᵥ (D *ᵥ ξ)) = star ξ ⬝ᵥ (D *ᵥ ξ) := by
  rw [star_dotProduct', star_mulVec, hD, Matrix.dotProduct_mulVec, star_star]

/-- A Hermitian matrix whose real quadratic form is nonnegative is positive
semidefinite. -/
lemma posSemidef_of_qf_nonneg {D : Matrix n n ℂ} (hD : Dᴴ = D) (h : ∀ ξ, 0 ≤ qf D ξ) :
    D.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD fun ξ => ?_
  rw [Complex.nonneg_iff]
  refine ⟨h ξ, ?_⟩
  have hreal := dotProduct_self_conj_eq D hD ξ
  have him := congrArg Complex.im hreal
  simp only [Complex.star_def, Complex.conj_im, Complex.ofReal_im, neg_inj] at him
  linarith

/-! ## The defect-matrix gap theorem -/

/-- The Rayleigh form of the defect matrix. -/
noncomputable def rayleighForm (b : κ → κ → ℝ) (z : κ → ℝ) : ℝ :=
  ∑ i, ∑ j, (if i = j then 0 else b i j * (z i * z j))

/-- Row sum of the defect matrix (the diagonal is excluded). -/
noncomputable def rowSum (b : κ → κ → ℝ) (i : κ) : ℝ :=
  ∑ j, (if i = j then 0 else b i j)

/-- Column sum of the defect matrix (the diagonal is excluded). -/
noncomputable def colSum (b : κ → κ → ℝ) (j : κ) : ℝ :=
  ∑ i, (if i = j then 0 else b i j)

/-- **Row/column-sum defect bound** (arithmetic core of `q:cor-filtered`).

A symmetric defect matrix whose row and column sums are at most `2 δ M` satisfies
the Rayleigh hypothesis of `defect_gap` with `ρ = 2 δ M`.  In the source data
`δ = e^{2 s ε} - 1` and `M` is the number of neighbouring supports, and the row
sum bound follows from `b i j ≤ 2 δ` together with at most `M` nonzero entries
per row. -/
theorem rayleigh_of_rowSums (b : κ → κ → ℝ) (δ M : ℝ)
    (hrow : ∀ i, rowSum b i ≤ 2 * δ * M)
    (hcol : ∀ j, colSum b j ≤ 2 * δ * M)
    (hb : ∀ i j, 0 ≤ b i j) :
    ∀ z : κ → ℝ, (∀ i, 0 ≤ z i) →
      rayleighForm b z ≤ (2 * δ * M) * ∑ i, (z i) ^ 2 := by
  intro z hz
  -- Step 1: pairwise AM-GM bound
  have hstep1 : rayleighForm b z
      ≤ ∑ i, ∑ j, (if i = j then 0
          else (b i j * (z i) ^ 2) / 2 + (b i j * (z j) ^ 2) / 2) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    split_ifs with hij
    · exact le_rfl
    · have hpq : 2 * z i * z j ≤ (z i) ^ 2 + (z j) ^ 2 := two_mul_le_add_sq (z i) (z j)
      have hb' : 0 ≤ b i j := hb i j
      nlinarith [hpq, hb']
  -- Step 2: split into row and column sums
  have hstep2 : ∑ i, ∑ j, (if i = j then 0
        else (b i j * (z i) ^ 2) / 2 + (b i j * (z j) ^ 2) / 2)
      = (∑ i, (z i) ^ 2 * rowSum b i) / 2 + (∑ j, (z j) ^ 2 * colSum b j) / 2 := by
    have hpt : ∀ i j, (if i = j then 0
          else (b i j * (z i) ^ 2) / 2 + (b i j * (z j) ^ 2) / 2)
        = (if i = j then 0 else b i j * (z i) ^ 2) / 2
          + (if i = j then 0 else b i j * (z j) ^ 2) / 2 := by
      intro i j
      split_ifs <;> ring
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [rowSum]
      rw [Finset.mul_sum, ← Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring)
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [colSum]
      rw [Finset.mul_sum, ← Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)
  -- Step 3: apply the row and column bounds
  have hrow' : ∑ i, (z i) ^ 2 * rowSum b i ≤ (2 * δ * M) * ∑ i, (z i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    calc (z i) ^ 2 * rowSum b i ≤ (z i) ^ 2 * (2 * δ * M) := by
          exact mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
      _ = (2 * δ * M) * (z i) ^ 2 := by ring
  have hcol' : ∑ j, (z j) ^ 2 * colSum b j ≤ (2 * δ * M) * ∑ j, (z j) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    calc (z j) ^ 2 * colSum b j ≤ (z j) ^ 2 * (2 * δ * M) := by
          exact mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _)
      _ = (2 * δ * M) * (z j) ^ 2 := by ring
  have := hstep2
  nlinarith [hstep1, hstep2, hrow', hcol']

/-- Symmetry makes the row and column bounds equivalent. -/
lemma colSum_eq_rowSum (b : κ → κ → ℝ) (hsym : ∀ i j, b i j = b j i) (j : κ) :
    colSum b j = rowSum b j := by
  rw [colSum, rowSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h, hsym i j]

/-- **Defect-matrix gap theorem** (finite-dimensional assembly of `q:thm-oblique`,
quadratic-form form).  A certified cosine matrix together with a Rayleigh bound
`ρ` forces `(1 - ρ) • H ≤ H * H`. -/
theorem defect_gap_qf (Q : κ → Matrix n n ℂ) (b : κ → κ → ℝ) (ρ : ℝ)
    (hQ : ∀ i, IsOrthProj (Q i))
    (hcos : ∀ i j, i ≠ j → ∀ ξ : n → ℂ,
      -(b i j) * hn (Q i *ᵥ ξ) * hn (Q j *ᵥ ξ) ≤ RCLike.re (star (Q i *ᵥ ξ) ⬝ᵥ (Q j *ᵥ ξ)))
    (hray : ∀ z : κ → ℝ, (∀ i, 0 ≤ z i) → rayleighForm b z ≤ ρ * ∑ i, (z i) ^ 2) :
    ∀ ξ : n → ℂ,
      (1 - ρ) * qf (∑ i, Q i) ξ ≤ qf ((∑ i, Q i) * (∑ i, Q i)) ξ := by
  intro ξ
  have hsq : ∀ i, qf (Q i * Q i) ξ = (hn (Q i *ᵥ ξ)) ^ 2 := by
    intro i
    rw [qf_sq_self (hQ i), ← hn_sq]
  have hH : (∑ i, Q i) * (∑ i, Q i) = ∑ i, ∑ j, Q i * Q j := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  have hExp : qf ((∑ i, Q i) * (∑ i, Q i)) ξ = ∑ i, ∑ j, qf (Q i * Q j) ξ := by
    rw [hH, qf_sum]
    exact Finset.sum_congr rfl (fun i _ => qf_sum (fun j => Q i * Q j) ξ)
  have hDiag : qf (∑ i, Q i) ξ = ∑ i, (hn (Q i *ᵥ ξ)) ^ 2 := by
    rw [qf_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [← hsq i, hQ i |>.1])
  have hterm : ∑ i, ∑ j, qf (Q i * Q j) ξ
      ≥ ∑ i, ∑ j, (if i = j then (hn (Q i *ᵥ ξ)) ^ 2
          else -(b i j) * hn (Q i *ᵥ ξ) * hn (Q j *ᵥ ξ)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    split_ifs with hij
    · subst hij
      rw [hsq i]
    · rw [qf_mul_apply (Q i) (Q j) (hQ i).2]
      exact hcos i j hij ξ
  have hshape : ∑ i, ∑ j, (if i = j then (hn (Q i *ᵥ ξ)) ^ 2
        else -(b i j) * hn (Q i *ᵥ ξ) * hn (Q j *ᵥ ξ))
      = (∑ i, (hn (Q i *ᵥ ξ)) ^ 2) - rayleighForm b (fun i => hn (Q i *ᵥ ξ)) := by
    rw [rayleighForm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hpt : ∀ j, (if i = j then (hn (Q i *ᵥ ξ)) ^ 2
          else -(b i j) * hn (Q i *ᵥ ξ) * hn (Q j *ᵥ ξ))
        = (if i = j then (hn (Q i *ᵥ ξ)) ^ 2 else 0)
          - (if i = j then 0 else b i j * (hn (Q i *ᵥ ξ) * hn (Q j *ᵥ ξ))) := by
      intro j
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  have hray' : rayleighForm b (fun i => hn (Q i *ᵥ ξ)) ≤ ρ * ∑ i, (hn (Q i *ᵥ ξ)) ^ 2 :=
    hray (fun i => hn (Q i *ᵥ ξ)) (fun i => hn_nonneg _)
  rw [hExp, hDiag]
  rw [hshape] at hterm
  nlinarith [hterm, hray']

/-- **Defect-matrix gap theorem**, Loewner form: `(1 - ρ) • H ≤ H * H`. -/
theorem defect_gap (Q : κ → Matrix n n ℂ) (b : κ → κ → ℝ) (ρ : ℝ)
    (hQ : ∀ i, IsOrthProj (Q i))
    (hcos : ∀ i j, i ≠ j → ∀ ξ : n → ℂ,
      -(b i j) * hn (Q i *ᵥ ξ) * hn (Q j *ᵥ ξ) ≤ RCLike.re (star (Q i *ᵥ ξ) ⬝ᵥ (Q j *ᵥ ξ)))
    (hray : ∀ z : κ → ℝ, (∀ i, 0 ≤ z i) → rayleighForm b z ≤ ρ * ∑ i, (z i) ^ 2) :
    (1 - ρ) • (∑ i, Q i) ≤ (∑ i, Q i) * (∑ i, Q i) := by
  have hHermQ : (∑ i, Q i)ᴴ = ∑ i, Q i := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun i _ => (hQ i).2)
  have hHH : ((∑ i, Q i) * (∑ i, Q i))ᴴ = (∑ i, Q i) * (∑ i, Q i) := by
    rw [conjTranspose_mul, hHermQ]
  have hSH : ((1 - ρ) • (∑ i, Q i))ᴴ = (1 - ρ) • (∑ i, Q i) := by
    rw [Matrix.conjTranspose_smul, hHermQ]
    simp
  have hHerm : ((∑ i, Q i) * (∑ i, Q i) - (1 - ρ) • (∑ i, Q i))ᴴ
      = (∑ i, Q i) * (∑ i, Q i) - (1 - ρ) • (∑ i, Q i) := by
    rw [conjTranspose_sub, hHH, hSH]
  rw [Matrix.le_iff]
  refine posSemidef_of_qf_nonneg hHerm (fun ξ => ?_)
  rw [qf_sub, qf_real_smul]
  have := defect_gap_qf Q b ρ hQ hcos hray ξ
  linarith

/-- **Source form of the defect-matrix gap theorem**: the Hamiltonian is the sum of
the *complement* projections `1 - G i` of the source's orthogonal projections,
`H = ∑ i, (1 - G i)`. -/
theorem defect_gap_complement (G : κ → Matrix n n ℂ) (b : κ → κ → ℝ) (ρ : ℝ)
    (hG : ∀ i, IsOrthProj (G i))
    (hcos : ∀ i j, i ≠ j → ∀ ξ : n → ℂ,
      -(b i j) * hn ((1 - G i) *ᵥ ξ) * hn ((1 - G j) *ᵥ ξ)
        ≤ RCLike.re (star ((1 - G i) *ᵥ ξ) ⬝ᵥ ((1 - G j) *ᵥ ξ)))
    (hray : ∀ z : κ → ℝ, (∀ i, 0 ≤ z i) → rayleighForm b z ≤ ρ * ∑ i, (z i) ^ 2) :
    (1 - ρ) • (∑ i, (1 - G i)) ≤ (∑ i, (1 - G i)) * (∑ i, (1 - G i)) :=
  defect_gap (fun i => 1 - G i) b ρ (fun i => IsOrthProj.one_sub (hG i)) hcos hray

/-! ## The filtered commuting-projector gap (`q:cor-filtered`), numeric form -/

/-- **`q:cor-filtered` numeric gap certificate.**

If the pairwise cosine defects of the projections `1 - Q i` are at most `2 δ` in
the matrix `b` and the defect matrix has row and column sums at most `2 δ M`,
then the norm-one blocked Hamiltonian `H = ∑ i, Q i` satisfies `H^2 ≥ (1 - 2δM) H`;
with `2 δ M < 1` the blocked gap is at least `1 - 2 δ M`.

In the source data `δ = e^{2 s ε} - 1` and `M` is the number of neighbouring
supports, so this is exactly `gap H_L ≥ 1 - 2 M (e^{2 s ε} - 1)`. -/
theorem cor_filtered_gap (Q : κ → Matrix n n ℂ) (b : κ → κ → ℝ) (δ M : ℝ)
    (hQ : ∀ i, IsOrthProj (Q i))
    (hcos : ∀ i j, i ≠ j → ∀ ξ : n → ℂ,
      -(b i j) * hn (Q i *ᵥ ξ) * hn (Q j *ᵥ ξ) ≤ RCLike.re (star (Q i *ᵥ ξ) ⬝ᵥ (Q j *ᵥ ξ)))
    (hrow : ∀ i, rowSum b i ≤ 2 * δ * M)
    (hcol : ∀ j, colSum b j ≤ 2 * δ * M)
    (hb : ∀ i j, 0 ≤ b i j) (hρ : 2 * δ * M < 1) :
    (1 - 2 * δ * M) • (∑ i, Q i) ≤ (∑ i, Q i) * (∑ i, Q i)
      ∧ 0 < 1 - 2 * δ * M :=
  ⟨defect_gap Q b (2 * δ * M) hQ hcos (rayleigh_of_rowSums b δ M hrow hcol hb),
    by linarith⟩

end MomentGeometry.Swarm
