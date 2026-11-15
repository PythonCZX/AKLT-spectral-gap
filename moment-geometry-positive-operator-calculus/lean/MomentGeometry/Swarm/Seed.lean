/-
Copyright: formalization for the Moment Geometry project (swarm smwi6zlvo, member m6).

# `q:lem-seed`: the finite-patch comparison

Source: `proofs/quantum_results.tex`, Lemma `q:lem-seed` (registry record `q:lem-seed`).

Let `h a` (`a : ι`) be the microscopic local terms, all positive semidefinite
(`h_a ≥ 0`), and let `patch e` (`e : κ`) be the finite set of microscopic terms
*contained* in the two-block coarse patch `e`.  The microscopic and blocked
Hamiltonians are

  `Hmicro = ∑ a, h a`,      `Hblock = ∑ e, (1 - G e)`,

where `G e` is the orthogonal projection onto the ground space of the patch
Hamiltonian `Hpatch e = ∑ a ∈ patch e, h a`.

Hypotheses (exactly the source ones):

* `ker (Hpatch e) = ran (G e)`, i.e. `Hpatch e *ᵥ v = 0 ↔ G e *ᵥ v = v`;
* `Hpatch e ≥ g • (1 - G e)` for a single `g = g_* > 0`;
* coverage: every microscopic term lies in at least one and at most `m` patches.

Conclusion: `ker Hmicro = ker Hblock` and `Hmicro ≥ (g_* / m) • Hblock`;
consequently every gap certificate `γ` for the blocked Hamiltonian
(`γ • (1 - G_K) ≤ Hblock`) transfers to the certificate `g_* γ / m` for the
microscopic Hamiltonian.

This is the honest formal content of `gap H_micro ≥ (g_*/m) gap H_block`: the
numeric gap function is represented by its lower-bound certificates.  We do not
package a spectral-radius / `sSup` gap functional here.
-/
import Mathlib

namespace MomentGeometry.Swarm

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-! ## Quadratic-form toolkit for complex matrices -/

/-- The real quadratic form `v ↦ Re vᴴ A v` of a complex matrix, as an additive
functional of the matrix. -/
noncomputable def qfAdd (v : n → ℂ) : Matrix n n ℂ →+ ℝ where
  toFun A := RCLike.re (star v ⬝ᵥ (A *ᵥ v))
  map_zero' := by simp
  map_add' A B := by simp [add_mulVec, dotProduct_add]

/-- The real quadratic form `v ↦ Re vᴴ A v`. -/
noncomputable abbrev qf (A : Matrix n n ℂ) (v : n → ℂ) : ℝ := qfAdd v A

lemma qf_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (v : n → ℂ) : 0 ≤ qf A v :=
  hA.re_dotProduct_nonneg v

lemma qf_finset_sum (s : Finset κ) (A : κ → Matrix n n ℂ) (v : n → ℂ) :
    qf (∑ e ∈ s, A e) v = ∑ e ∈ s, qf (A e) v :=
  map_sum (qfAdd v) A s

lemma qf_sum (A : κ → Matrix n n ℂ) (v : n → ℂ) :
    qf (∑ e, A e) v = ∑ e, qf (A e) v := by
  simpa using qf_finset_sum (Finset.univ) A v

lemma PosSemidef_finset_sum {s : Finset κ} {A : κ → Matrix n n ℂ}
    (hA : ∀ e ∈ s, (A e).PosSemidef) : (∑ e ∈ s, A e).PosSemidef :=
  Finset.sum_induction A (fun M => M.PosSemidef) (fun _ _ ha hb => ha.add hb)
    PosSemidef.zero hA

lemma PosSemidef_sum {A : κ → Matrix n n ℂ} (hA : ∀ e, (A e).PosSemidef) :
    (∑ e, A e).PosSemidef :=
  PosSemidef_finset_sum (fun e _ => hA e)

/-- Vanishing criterion: a positive semidefinite matrix and its quadratic form
vanish simultaneously. -/
lemma qf_eq_zero_iff {A : Matrix n n ℂ} (hA : A.PosSemidef) (v : n → ℂ) :
    qf A v = 0 ↔ A *ᵥ v = 0 := by
  constructor
  · intro h
    have hnn : 0 ≤ star v ⬝ᵥ (A *ᵥ v) := hA.dotProduct_mulVec_nonneg v
    have him : (star v ⬝ᵥ (A *ᵥ v)).im = 0 := (Complex.nonneg_iff.mp hnn).2.symm
    have hre : (star v ⬝ᵥ (A *ᵥ v)).re = 0 := h
    have hz : star v ⬝ᵥ (A *ᵥ v) = 0 := Complex.ext hre him
    exact (hA.dotProduct_mulVec_zero_iff v).mp hz
  · intro h
    simp [qf, qfAdd, h]

/-- A finite sum of positive semidefinite matrices vanishes on `v` iff each
summand does. -/
lemma finset_sum_mulVec_eq_zero_iff (s : Finset κ) {A : κ → Matrix n n ℂ}
    (hA : ∀ e ∈ s, (A e).PosSemidef) (v : n → ℂ) :
    (∑ e ∈ s, A e) *ᵥ v = 0 ↔ ∀ e ∈ s, A e *ᵥ v = 0 := by
  rw [← qf_eq_zero_iff (PosSemidef_finset_sum hA) v, qf_finset_sum]
  have hnn : ∀ e ∈ s, 0 ≤ qf (A e) v := fun e he => qf_nonneg (hA e he) v
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  exact forall_congr' (fun e => forall_congr' (fun he => qf_eq_zero_iff (hA e he) v))

lemma sum_mulVec_eq_zero_iff {A : κ → Matrix n n ℂ}
    (hA : ∀ e, (A e).PosSemidef) (v : n → ℂ) :
    (∑ e, A e) *ᵥ v = 0 ↔ ∀ e, A e *ᵥ v = 0 := by
  simpa using finset_sum_mulVec_eq_zero_iff (Finset.univ) (fun e _ => hA e) v

/-! ## Orthogonal projections -/

/-- A matrix is an orthogonal projection when it is idempotent and self-adjoint. -/
def IsOrthProj (G : Matrix n n ℂ) : Prop := G * G = G ∧ Gᴴ = G

lemma IsOrthProj.one_sub_posSemidef {G : Matrix n n ℂ} (hG : IsOrthProj G) :
    (1 - G).PosSemidef := by
  have hsq : (1 - G) * (1 - G) = 1 - G := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hG.1, sub_self, sub_zero]
  have h : (1 - G) = (1 - G)ᴴ * (1 - G) := by
    rw [conjTranspose_sub, conjTranspose_one, hG.2, hsq]
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

lemma IsOrthProj.one_sub {G : Matrix n n ℂ} (hG : IsOrthProj G) : IsOrthProj (1 - G) := by
  have hsq : (1 - G) * (1 - G) = 1 - G := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hG.1, sub_self, sub_zero]
  refine ⟨hsq, ?_⟩
  rw [conjTranspose_sub, conjTranspose_one, hG.2]

lemma one_sub_mulVec_eq_zero_iff {G : Matrix n n ℂ} (v : n → ℂ) :
    (1 - G) *ᵥ v = 0 ↔ G *ᵥ v = v := by
  rw [sub_mulVec, one_mulVec, sub_eq_zero, eq_comm]

/-! ## The Hamiltonians -/

/-- Microscopic Hamiltonian: the sum of all local terms. -/
def microHam (h : ι → Matrix n n ℂ) : Matrix n n ℂ := ∑ a, h a

/-- Patch Hamiltonian: the microscopic terms contained in the two-block patch `e`. -/
def patchHam (h : ι → Matrix n n ℂ) (patch : κ → Finset ι) (e : κ) : Matrix n n ℂ :=
  ∑ a ∈ patch e, h a

/-- Blocked Hamiltonian: sum of the norm-one complement projections of the patch
ground spaces. -/
def blockHam (G : κ → Matrix n n ℂ) : Matrix n n ℂ := ∑ e, (1 - G e)

/-- Coverage multiplicity of a microscopic term: the number of coarse patches
that contain it. -/
def covCount (patch : κ → Finset ι) (a : ι) : ℕ :=
  (Finset.univ.filter (fun e => a ∈ patch e)).card

lemma microHam_posSemidef {h : ι → Matrix n n ℂ} (hh : ∀ a, (h a).PosSemidef) :
    (microHam h).PosSemidef :=
  PosSemidef_sum hh

lemma patchHam_posSemidef {h : ι → Matrix n n ℂ} (hh : ∀ a, (h a).PosSemidef)
    (patch : κ → Finset ι) (e : κ) : (patchHam h patch e).PosSemidef :=
  PosSemidef_finset_sum (fun a _ => hh a)

lemma blockHam_posSemidef {G : κ → Matrix n n ℂ} (hG : ∀ e, IsOrthProj (G e)) :
    (blockHam G).PosSemidef :=
  PosSemidef_sum (fun e => IsOrthProj.one_sub_posSemidef (hG e))

/-! ## Coverage arithmetic -/

/-- **Coverage reindexing.**  Summing the patch Hamiltonians reindexes the
microscopic terms with their coverage multiplicity. -/
lemma sum_patchHam (h : ι → Matrix n n ℂ) (patch : κ → Finset ι) :
    (∑ e, patchHam h patch e) = ∑ a, (covCount patch a : ℝ) • h a := by
  have h1 : ∀ e, patchHam h patch e = ∑ a, if a ∈ patch e then h a else 0 := by
    intro e
    rw [patchHam]
    have hstep : (∑ a, if a ∈ patch e then h a else 0) = ∑ a ∈ patch e, h a := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact hstep.symm
  calc (∑ e, patchHam h patch e)
      = ∑ e, ∑ a, (if a ∈ patch e then h a else 0) := Finset.sum_congr rfl (fun e _ => h1 e)
    _ = ∑ a, ∑ e, (if a ∈ patch e then h a else 0) := Finset.sum_comm
    _ = ∑ a, ∑ e ∈ Finset.univ.filter (fun e => a ∈ patch e), h a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ a, (covCount patch a : ℝ) • h a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_const, covCount, Nat.cast_smul_eq_nsmul]

/-- Coverage (`multiplicity ≤ m`) bounds the sum of patch Hamiltonians by `m`
times the microscopic Hamiltonian. -/
lemma sum_patchHam_le (h : ι → Matrix n n ℂ) (patch : κ → Finset ι) (m : ℕ)
    (hh : ∀ a, (h a).PosSemidef) (hm : ∀ a, covCount patch a ≤ m) :
    (∑ e, patchHam h patch e) ≤ (m : ℝ) • microHam h := by
  rw [sum_patchHam]
  have hsplit : (m : ℝ) • microHam h - ∑ a, (covCount patch a : ℝ) • h a
      = ∑ a, ((m : ℝ) - (covCount patch a : ℝ)) • h a := by
    rw [microHam, Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => by rw [sub_smul])
  rw [Matrix.le_iff, hsplit]
  refine PosSemidef_finset_sum (fun a _ => ?_)
  refine PosSemidef.smul (hh a) ?_
  have hle : (covCount patch a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm a
  linarith

/-! ## Kernel and gap statements -/

/-- **Same full kernel** (`q:lem-seed`, first conclusion). -/
theorem seed_kernel_eq (h : ι → Matrix n n ℂ) (patch : κ → Finset ι)
    (G : κ → Matrix n n ℂ) (hh : ∀ a, (h a).PosSemidef) (hG : ∀ e, IsOrthProj (G e))
    (hcover : ∀ a, ∃ e, a ∈ patch e)
    (hkern : ∀ (e : κ) (v : n → ℂ), patchHam h patch e *ᵥ v = 0 ↔ G e *ᵥ v = v)
    (v : n → ℂ) :
    microHam h *ᵥ v = 0 ↔ blockHam G *ᵥ v = 0 := by
  have hmicro : microHam h *ᵥ v = 0 ↔ ∀ a, h a *ᵥ v = 0 :=
    sum_mulVec_eq_zero_iff hh v
  have hpatch : ∀ e, patchHam h patch e *ᵥ v = 0 ↔ ∀ a ∈ patch e, h a *ᵥ v = 0 :=
    fun e => finset_sum_mulVec_eq_zero_iff (patch e) (fun a _ => hh a) v
  have hblock : blockHam G *ᵥ v = 0 ↔ ∀ e, G e *ᵥ v = v := by
    rw [blockHam]
    rw [sum_mulVec_eq_zero_iff (fun e => IsOrthProj.one_sub_posSemidef (hG e)) v]
    simp [one_sub_mulVec_eq_zero_iff]
  rw [hmicro, hblock]
  constructor
  · intro hall e
    exact (hkern e v).mp ((hpatch e).mpr fun a _ => hall a)
  · intro hGv a
    obtain ⟨e, he⟩ := hcover a
    exact (hpatch e).mp ((hkern e v).mpr (hGv e)) a he

/-- **Gap comparison** (`q:lem-seed`, second conclusion), operator form:
`Hmicro ≥ (g_* / m) • Hblock`. -/
theorem seed_gap_le (h : ι → Matrix n n ℂ) (patch : κ → Finset ι)
    (G : κ → Matrix n n ℂ) (g : ℝ) (m : ℕ) (hh : ∀ a, (h a).PosSemidef)
    (hG : ∀ e, IsOrthProj (G e)) (hm : ∀ a, covCount patch a ≤ m) (hm0 : 0 < m)
    (hpat : ∀ e, g • (1 - G e) ≤ patchHam h patch e) :
    (g / m) • blockHam G ≤ microHam h := by
  have hm0' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have h1 : g • blockHam G ≤ ∑ e, patchHam h patch e := by
    rw [blockHam, Finset.smul_sum]
    exact Finset.sum_le_sum (fun e _ => hpat e)
  have h2 : (∑ e, patchHam h patch e) ≤ (m : ℝ) • microHam h :=
    sum_patchHam_le h patch m hh hm
  have h3 : g • blockHam G ≤ (m : ℝ) • microHam h := le_trans h1 h2
  have hP : ((m : ℝ) • microHam h - g • blockHam G).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact sub_nonneg.mpr h3
  have hEq : microHam h - (g / m) • blockHam G
      = ((m : ℝ)⁻¹) • ((m : ℝ) • microHam h - g • blockHam G) := by
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt hm0'), one_smul,
      ← div_eq_inv_mul]
  rw [Matrix.le_iff, hEq]
  exact PosSemidef.smul hP (inv_nonneg.mpr (Nat.cast_nonneg m))

/-- **Gap transfer.**  Every gap certificate `γ` for the blocked Hamiltonian
(`γ • (1 - G_K) ≤ Hblock`) yields the certificate `g_* γ / m` for the
microscopic Hamiltonian.  This is the source inequality
`gap H_micro ≥ (g_*/m) gap H_block`, stated for lower-bound certificates. -/
theorem seed_gap_transfer (h : ι → Matrix n n ℂ) (patch : κ → Finset ι)
    (G : κ → Matrix n n ℂ) (G_K : Matrix n n ℂ) (g γ : ℝ) (m : ℕ)
    (hh : ∀ a, (h a).PosSemidef) (hG : ∀ e, IsOrthProj (G e))
    (hm : ∀ a, covCount patch a ≤ m) (hm0 : 0 < m) (hg : 0 ≤ g)
    (hpat : ∀ e, g • (1 - G e) ≤ patchHam h patch e)
    (hblk : γ • (1 - G_K) ≤ blockHam G) :
    (g * γ / m) • (1 - G_K) ≤ microHam h := by
  refine le_trans ?_ (seed_gap_le h patch G g m hh hG hm hm0 hpat)
  have hscalar : g * γ / m = (g / m) * γ := by ring
  rw [hscalar, ← smul_smul, Matrix.le_iff, ← smul_sub]
  refine PosSemidef.smul ?_ (div_nonneg hg (Nat.cast_nonneg m))
  rw [← Matrix.nonneg_iff_posSemidef]
  exact sub_nonneg.mpr hblk

end MomentGeometry.Swarm
