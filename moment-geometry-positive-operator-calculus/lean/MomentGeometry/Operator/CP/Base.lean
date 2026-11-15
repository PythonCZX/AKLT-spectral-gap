/-
Finite-dimensional completely positive structure of modular kernel multipliers.
Stage 1: definitions and the CP ⟺ positive-semidefinite-kernel criterion,
with the structural (unital / trace / composition / self-adjointness) laws.
-/
import Mathlib

open Matrix Complex MeasureTheory Filter
open scoped BigOperators ComplexOrder Topology

set_option linter.unusedSectionVars false

namespace MomentGeometry.Operator.CP

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Kernel matrix of a multiplier function `f` at the spectrum `k`. -/
def Kmat (k : ι → ℝ) (f : ℝ → ℂ) : Matrix ι ι ℂ := fun i j => f (k i - k j)

/-- The kernel multiplier map `A ↦ (f (k i - k j) * A i j)`. -/
noncomputable def multMap (k : ι → ℝ) (f : ℝ → ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun A := Kmat k f ⊙ A
  map_add' A B := by rw [hadamard_add]
  map_smul' c A := by
    ext i j
    simp only [Matrix.smul_apply, hadamard, smul_eq_mul, Matrix.of_apply,
      RingHom.id_apply]
    ring

theorem multMap_apply (k : ι → ℝ) (f : ℝ → ℂ) (A : Matrix ι ι ℂ) (i j : ι) :
    multMap k f A i j = f (k i - k j) * A i j := rfl

theorem multMap_hadamard (k : ι → ℝ) (f : ℝ → ℂ) (A : Matrix ι ι ℂ) :
    multMap k f A = Kmat k f ⊙ A := rfl

theorem Kmat_hadamard (k : ι → ℝ) (f g : ℝ → ℂ) :
    Kmat k (fun x => f x * g x) = Kmat k f ⊙ Kmat k g := rfl

/-- Amplification of an endomorphism of `M_ι(ℂ)` to `M_ι(M_ν)`. -/
def amp {ν : Type*} (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (A : Matrix (ι × ν) (ι × ν) ℂ) : Matrix (ι × ν) (ι × ν) ℂ :=
  fun p q => Φ (fun r s => A (r, p.2) (s, q.2)) p.1 q.1

/-- Complete positivity of an endomorphism of `M_ι(ℂ)`: every amplification is
positive on positive semidefinite matrices. -/
def IsCP (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) : Prop :=
  ∀ (ν : Type u) [Fintype ν], ∀ A : Matrix (ι × ν) (ι × ν) ℂ,
    A.PosSemidef → (amp Φ A).PosSemidef

theorem amp_multMap {ν : Type*} (k : ι → ℝ) (f : ℝ → ℂ)
    (A : Matrix (ι × ν) (ι × ν) ℂ) :
    amp (multMap k f) A = (Kmat k f).submatrix Prod.fst Prod.fst ⊙ A := by
  ext p q
  rfl

/-- **Schur direction**: a positive semidefinite kernel matrix gives a completely
positive multiplier map. -/
theorem isCP_multMap_of_posSemidef (k : ι → ℝ) (f : ℝ → ℂ)
    (h : (Kmat k f).PosSemidef) : IsCP (multMap k f) := by
  intro ν _ A hA
  rw [amp_multMap]
  exact (h.submatrix Prod.fst).hadamard hA

/-- **Choi direction**: complete positivity of the multiplier forces the kernel
matrix to be positive semidefinite. -/
theorem posSemidef_of_isCP (k : ι → ℝ) (f : ℝ → ℂ) (h : IsCP (multMap k f)) :
    (Kmat k f).PosSemidef := by
  classical
  set v : ι × ι → ℂ := fun p => if p.1 = p.2 then 1 else 0 with hv
  have hA : (vecMulVec v (star v)).PosSemidef := posSemidef_vecMulVec_self_star v
  have hres : (amp (multMap k f) (vecMulVec v (star v))).PosSemidef := h ι _ hA
  have hsub : ((amp (multMap k f) (vecMulVec v (star v))).submatrix
      (fun i => (i, i)) (fun i => (i, i))).PosSemidef :=
    hres.submatrix (fun i => (i, i))
  convert hsub using 1
  ext i j
  rw [Matrix.submatrix_apply, amp_multMap, Matrix.hadamard, Kmat, vecMulVec, hv]
  simp [Kmat]

/-- **Criterion**: a kernel multiplier is completely positive iff its kernel matrix
is positive semidefinite. -/
theorem isCP_multMap_iff (k : ι → ℝ) (f : ℝ → ℂ) :
    IsCP (multMap k f) ↔ (Kmat k f).PosSemidef :=
  ⟨posSemidef_of_isCP k f, isCP_multMap_of_posSemidef k f⟩

theorem multMap_one (k : ι → ℝ) : multMap k (fun _ => 1) = LinearMap.id := by
  ext A i j
  simp [multMap_apply]

theorem multMap_comp (k : ι → ℝ) (f g : ℝ → ℂ) :
    (multMap k f).comp (multMap k g) = multMap k (fun x => f x * g x) := by
  ext A i j
  simp [multMap_apply, mul_assoc]

theorem multMap_apply_one (k : ι → ℝ) (f : ℝ → ℂ) (hf : f 0 = 1) :
    multMap k f 1 = 1 := by
  ext i j
  rw [multMap_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [hf]
  · simp [h]

theorem multMap_trace (k : ι → ℝ) (f : ℝ → ℂ) (hf : f 0 = 1) (A : Matrix ι ι ℂ) :
    (multMap k f A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [multMap_apply, sub_self, hf, one_mul]

/-- Auxiliary: `star (f (k j - k i)) = f (k i - k j)` for a real, even symbol. -/
theorem star_apply_sub (k : ι → ℝ) (f : ℝ → ℂ) (hreal : ∀ x, star (f x) = f x)
    (heven : ∀ x, f (-x) = f x) (i j : ι) : star (f (k j - k i)) = f (k i - k j) := by
  rw [hreal]
  have h : k j - k i = -(k i - k j) := by ring
  rw [h, heven]

/-- Multiplier maps with a real, even symbol are self-adjoint for the
Hilbert–Schmidt inner product. -/
theorem multMap_hs_selfAdjoint (k : ι → ℝ) (f : ℝ → ℂ)
    (hreal : ∀ x, star (f x) = f x) (A B : Matrix ι ι ℂ) :
    ((multMap k f A)ᴴ * B).trace = (Aᴴ * multMap k f B).trace := by
  have key : ∀ i j : ι, star (f (k j - k i) * A j i) * B j i
      = star (A j i) * (f (k j - k i) * B j i) := by
    intro i j
    rw [star_mul', hreal]
    ring
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    multMap_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j

/-- Multiplier maps with a real, even symbol preserve hermiticity. -/
theorem multMap_isHermitian (k : ι → ℝ) (f : ℝ → ℂ)
    (hreal : ∀ x, star (f x) = f x) (heven : ∀ x, f (-x) = f x)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (multMap k f A).IsHermitian := by
  have h : ∀ i j : ι, star (A i j) = A j i := fun i j =>
    congrFun (congrFun hA j) i
  ext i j
  simp only [Matrix.conjTranspose_apply, multMap_apply]
  rw [star_mul', star_apply_sub k f hreal heven]
  have h' : star (A j i) = A i j := by rw [← h, star_star]
  rw [h']


/-! ## Kernels of characteristic functions are positive semidefinite -/

section CharFunKernel

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma norm_cexp_ofReal_mul_I (b t : ℝ) : ‖cexp ((b : ℂ) * (t : ℂ) * I)‖ = 1 := by
  have h : (b : ℂ) * (t : ℂ) * I = ((b * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma integrable_cexp_const {ν : Measure ℝ} [IsFiniteMeasure ν] (a : ℂ) (b : ℝ) :
    Integrable (fun t : ℝ => a * cexp ((b : ℂ) * (t : ℂ) * I)) ν := by
  refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) ‖a‖
    (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_cexp_ofReal_mul_I, mul_one]

lemma star_cexp_neg_mul_I (a t : ℝ) :
    star (cexp (-((a : ℂ) * (t : ℂ) * I))) = cexp ((a : ℂ) * (t : ℂ) * I) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_neg]

lemma sum_exp_factor (c : ι → ℂ) (k : ι → ℝ) (t : ℝ) :
    (∑ i, ∑ j, star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j)
      = star (∑ i, c i * cexp (-((k i : ℂ) * (t : ℂ) * I))) *
        (∑ i, c i * cexp (-((k i : ℂ) * (t : ℂ) * I))) := by
  have hfac : ∀ i j : ι, star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j
      = (star (c i) * cexp ((k i : ℂ) * (t : ℂ) * I)) *
        (c j * cexp (-((k j : ℂ) * (t : ℂ) * I))) := by
    intro i j
    have hexp : cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I)
        = cexp ((k i : ℂ) * (t : ℂ) * I) * cexp (-((k j : ℂ) * (t : ℂ) * I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]; ring
  calc (∑ i, ∑ j, star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j)
      = ∑ i, ∑ j, (star (c i) * cexp ((k i : ℂ) * (t : ℂ) * I)) *
          (c j * cexp (-((k j : ℂ) * (t : ℂ) * I))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfac i j
    _ = (∑ i, star (c i) * cexp ((k i : ℂ) * (t : ℂ) * I)) *
          (∑ j, c j * cexp (-((k j : ℂ) * (t : ℂ) * I))) := by
        rw [Finset.sum_mul_sum]
    _ = star (∑ i, c i * cexp (-((k i : ℂ) * (t : ℂ) * I))) *
          (∑ i, c i * cexp (-((k i : ℂ) * (t : ℂ) * I))) := by
        congr 1
        rw [star_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [star_mul', star_cexp_neg_mul_I]

end CharFunKernel

section CharFunKernel2

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma sum_exp_factor' (c : ι → ℂ) (k : ι → ℝ) (t : ℝ) :
    (∑ i, ∑ j, star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j)
      = ((Complex.normSq (∑ i, c i * cexp (-((k i : ℂ) * (t : ℂ) * I))) : ℝ) : ℂ) := by
  rw [sum_exp_factor, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

/-- **Kernels of characteristic functions are positive semidefinite.** -/
theorem posSemidef_charFun (k : ι → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (Kmat k (fun x => charFun ν x)).PosSemidef := by
  classical
  have hInt : ∀ (c : ι → ℂ) (i j : ι), Integrable
      (fun t : ℝ => star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j) ν := by
    intro c i j
    have h := integrable_cexp_const (ν := ν) (star (c i) * c j) (k i - k j)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    ring
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Kmat, Matrix.conjTranspose_apply]
    rw [show k j - k i = -(k i - k j) by ring, charFun_neg, Complex.star_def,
      Complex.conj_conj]
  · intro c
    have hexp : ∀ i j : ι, star (c i) * charFun ν (k i - k j) * c j
        = ∫ t, star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j ∂ν := by
      intro i j
      rw [charFun_apply_real, integral_mul_const, integral_const_mul]
    have hswap : ∀ i : ι, Integrable
        (fun t : ℝ => ∑ j, star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j) ν :=
      fun i => integrable_finsetSum _ fun j _ => hInt c i j
    have hstep1 : star c ⬝ᵥ (Kmat k (fun x => charFun ν x) *ᵥ c)
        = ∑ i, ∑ j, star (c i) * charFun ν (k i - k j) * c j := by
      simp only [dotProduct, Matrix.mulVec, Kmat, Finset.mul_sum, Pi.star_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hstep2 : (∑ i, ∑ j, star (c i) * charFun ν (k i - k j) * c j)
        = ∑ i, ∫ t, ∑ j,
            star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j ∂ν := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum Finset.univ (fun j _ => hInt c i j)]
      exact Finset.sum_congr rfl fun j _ => hexp i j
    have hstep3 : (∑ i, ∫ t, ∑ j,
          star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j ∂ν)
        = ∫ t, ∑ i, ∑ j,
            star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j ∂ν := by
      rw [integral_finsetSum Finset.univ (fun i _ => hswap i)]
    rw [hstep1, hstep2, hstep3]
    rw [show (∫ t, ∑ i, ∑ j,
          star (c i) * cexp (((k i - k j : ℝ) : ℂ) * (t : ℂ) * I) * c j ∂ν)
        = ∫ t, ((Complex.normSq (∑ i, c i * cexp (-((k i : ℂ) * (t : ℂ) * I))) : ℝ) : ℂ) ∂ν
        from integral_congr_ae (Filter.Eventually.of_forall fun t => sum_exp_factor' c k t)]
    have h5 : (∫ t, ((Complex.normSq (∑ i, c i * cexp (-((k i : ℂ) * (t : ℂ) * I))) : ℝ) : ℂ) ∂ν)
        = ((∫ t, Complex.normSq (∑ i, c i * cexp (-((k i : ℂ) * (t : ℂ) * I))) ∂ν : ℝ) : ℂ) :=
      integral_ofReal
    rw [h5, Complex.zero_le_real]
    exact integral_nonneg fun t => Complex.normSq_nonneg _

/-- Expansion of the quadratic form of a kernel matrix. -/
lemma dotProduct_kernel_expand (k : ι → ℝ) (M : ℝ → ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ (Kmat k M *ᵥ c) = ∑ i, ∑ j, star (c i) * (M (k i - k j) * c j) := by
  simp only [dotProduct, Matrix.mulVec, Kmat, Finset.mul_sum, Pi.star_apply]

/-- **Mixtures of positive semidefinite kernels are positive semidefinite.** -/
theorem posSemidef_of_integral (k : ι → ℝ) {w : Measure ℝ} {g : ℝ → ℝ → ℂ}
    (hg : ∀ u, (Kmat k (g u)).PosSemidef)
    (hint : ∀ i j, Integrable (fun u => g u (k i - k j)) w) :
    (Kmat k (fun x => ∫ u, g u x ∂w)).PosSemidef := by
  classical
  have hpt : ∀ (u : ℝ) (i j : ι), star (g u (k j - k i)) = g u (k i - k j) := by
    intro u i j
    have h := congrFun (congrFun (hg u).isHermitian i) j
    simpa only [Kmat, Matrix.conjTranspose_apply] using h
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Kmat, Matrix.conjTranspose_apply]
    rw [Complex.star_def, ← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => hpt u i j)
  · intro c
    have hIn : ∀ i j : ι, Integrable
        (fun u : ℝ => star (c i) * (g u (k i - k j) * c j)) w := by
      intro i j
      refine Integrable.congr (((hint i j).const_mul (star (c i))).mul_const (c j)) ?_
      exact Filter.Eventually.of_forall fun u => by ring

    have hstep0 : ∀ i j : ι, star (c i) * ((∫ u, g u (k i - k j) ∂w) * c j)
        = ∫ u, star (c i) * (g u (k i - k j) * c j) ∂w := by
      intro i j
      rw [show star (c i) * ((∫ u, g u (k i - k j) ∂w) * c j)
          = star (c i) * (∫ u, g u (k i - k j) ∂w) * c j from by ring]
      rw [show (∫ u, star (c i) * (g u (k i - k j) * c j) ∂w)
          = ∫ u, star (c i) * g u (k i - k j) * c j ∂w from
        integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)]
      rw [integral_mul_const, integral_const_mul]
    have hQ : star c ⬝ᵥ (Kmat k (fun x => ∫ u, g u x ∂w) *ᵥ c)
        = ∫ u, star c ⬝ᵥ (Kmat k (g u) *ᵥ c) ∂w := by
     calc star c ⬝ᵥ (Kmat k (fun x => ∫ u, g u x ∂w) *ᵥ c)
        = ∑ i, ∑ j, star (c i) * ((∫ u, g u (k i - k j) ∂w) * c j) :=
          dotProduct_kernel_expand k (fun x => ∫ u, g u x ∂w) c
      _ = ∑ i, ∑ j, ∫ u, star (c i) * (g u (k i - k j) * c j) ∂w :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hstep0 i j
      _ = ∑ i, ∫ u, ∑ j, star (c i) * (g u (k i - k j) * c j) ∂w := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum Finset.univ (fun j _ => hIn i j)]
      _ = ∫ u, ∑ i, ∑ j, star (c i) * (g u (k i - k j) * c j) ∂w := by
          rw [integral_finsetSum Finset.univ
            (fun i _ => integrable_finsetSum _ fun j _ => hIn i j)]
      _ = ∫ u, star c ⬝ᵥ (Kmat k (g u) *ᵥ c) ∂w := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          exact (dotProduct_kernel_expand k (g u) c).symm
    rw [hQ]
    exact integral_nonneg fun u => (hg u).dotProduct_mulVec_nonneg c

/-- **Gaussian (Ornstein–Uhlenbeck) symbol**: `x ↦ exp (-u x²)` has a positive
semidefinite kernel for `u ≥ 0`.  This is the Fourier representation of the Gaussian
law (Bochner's theorem in the one explicit instance needed below). -/
theorem posSemidef_gaussian (k : ι → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (Kmat k (fun x => cexp (-((u : ℂ) * (x : ℂ)^2)))).PosSemidef := by
  have h2u : (0 : ℝ) ≤ 2 * u := by linarith
  obtain ⟨h, -⟩ : (Kmat k (fun x => charFun
      (ProbabilityTheory.gaussianReal 0 (NNReal.mk (2 * u) h2u)) x)).PosSemidef ∧ True := by
    exact ⟨posSemidef_charFun k
      (ProbabilityTheory.gaussianReal 0 (NNReal.mk (2 * u) h2u)), trivial⟩
  have hfun : (fun x : ℝ => charFun
      (ProbabilityTheory.gaussianReal 0 (NNReal.mk (2 * u) h2u)) x)
      = fun x : ℝ => cexp (-((u : ℂ) * (x : ℂ)^2)) := by
    funext x
    rw [ProbabilityTheory.charFun_gaussianReal]
    have hv : ((↑(NNReal.mk (2 * u) h2u) : ℝ) : ℂ) = 2 * (u : ℂ) := by
      push_cast
      ring
    rw [hv]
    congr 1
    push_cast
    ring
  rwa [hfun] at h

/-- **Hadamard powers**: if a kernel is positive semidefinite then so is every
nonnegative integer power of its symbol (Schur product theorem). -/
theorem posSemidef_hadamard_pow (k : ι → ℝ) {f : ℝ → ℂ}
    (hf : (Kmat k f).PosSemidef) (n : ℕ) :
    (Kmat k (fun x => f x ^ n)).PosSemidef := by
  induction n with
  | zero =>
      have : (fun x : ℝ => f x ^ 0) = fun _ => 1 := by funext x; simp
      rw [this]
      have hJ : Kmat k (fun _ : ℝ => (1 : ℂ)) = vecMulVec (fun _ : ι => (1:ℂ))
          (star (fun _ : ι => (1:ℂ))) := by
        ext i j; simp [Kmat, vecMulVec]
      rw [hJ]
      exact posSemidef_vecMulVec_self_star _
  | succ n ih =>
      have : (fun x : ℝ => f x ^ (n + 1)) = fun x => f x * f x ^ n := by
        funext x; rw [pow_succ]; ring
      rw [this, Kmat_hadamard]
      exact hf.hadamard ih

/-- Kernel of a constant multiple of a symbol. -/
lemma Kmat_const_mul (k : ι → ℝ) (a : ℂ) (h : ℝ → ℂ) :
    Kmat k (fun x => a * h x) = a • Kmat k h := rfl

/-- **Resolvent (Cauchy) symbol**: `x ↦ (λ + x²)⁻¹` has a positive semidefinite kernel
for `λ > 0`.  This is the Gamma(1) (exponential) mixture of Gaussian symbols,
`∫_0^∞ e^{-λu} e^{-u x²} du = (λ + x²)⁻¹`. -/
theorem posSemidef_resolvent_base (k : ι → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (Kmat k (fun x => ((lam : ℂ) + ((x : ℝ) : ℂ)^2)⁻¹)).PosSemidef := by
  classical
  set g : ℝ → ℝ → ℂ :=
    fun u x => if 0 < u then cexp (-(((lam : ℂ) + ((x : ℝ) : ℂ)^2) * ((u : ℝ) : ℂ))) else 0
    with hgdef
  have hg : ∀ u, (Kmat k (g u)).PosSemidef := by
    intro u
    by_cases hu : 0 < u
    · have hfac : (g u) = fun x : ℝ => cexp (-(((lam : ℂ) * ((u : ℝ) : ℂ)))) *
          cexp (-((((u : ℝ) : ℂ)) * ((x : ℝ) : ℂ)^2)) := by
        funext x
        rw [hgdef]
        simp only [hu, if_true]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hpos : (0 : ℂ) ≤ cexp (-(((lam : ℂ) * ((u : ℝ) : ℂ)))) := by
        have harg : (-(((lam : ℂ) * ((u : ℝ) : ℂ)))) = ((-(lam * u) : ℝ) : ℂ) := by
          push_cast; ring
        have hval : cexp (-(((lam : ℂ) * ((u : ℝ) : ℂ)))) = ((Real.exp (-(lam * u)) : ℝ) : ℂ) := by
          rw [harg, ← Complex.ofReal_exp]
        rw [hval, Complex.zero_le_real]
        exact (Real.exp_pos _).le
      rw [hfac, Kmat_const_mul]
      exact (posSemidef_gaussian k hu.le).smul hpos
    · have hzero : (g u) = fun _ => 0 := by
        funext x
        rw [hgdef]
        simp only [hu, if_false]
      rw [hzero]
      exact PosSemidef.zero
  have hIntBase : Integrable (fun u : ℝ => Real.exp (-(lam * u))) (volume.restrict (Set.Ioi 0)) := by
    have h0 := exp_neg_integrableOn_Ioi (a := 0) hlam
    exact Integrable.congr h0 (Filter.Eventually.of_forall fun u => by ring)
  have hint : ∀ i j, Integrable (fun u => g u (k i - k j)) (volume.restrict (Set.Ioi 0)) := by
    intro i j
    refine Integrable.mono' hIntBase ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      rw [hgdef]
      exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
    · refine Filter.Eventually.of_forall fun u => ?_
      rw [hgdef]
      by_cases hu : 0 < u
      · simp only [hu, if_true]
        have harg : -(((lam : ℂ) + ((k i - k j : ℝ) : ℂ)^2) * ((u : ℝ) : ℂ))
            = ((-(((lam + (k i - k j)^2) * u)) : ℝ) : ℂ) := by push_cast; ring
        rw [harg, Complex.norm_exp, Complex.ofReal_re]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [sq_nonneg (k i - k j), hu, hlam]
      · simp only [hu, if_false, norm_zero]
        exact (Real.exp_pos _).le
  have hval : ∀ x : ℝ, (∫ u, g u x ∂(volume.restrict (Set.Ioi 0))) =
      ((lam : ℂ) + ((x : ℝ) : ℂ)^2)⁻¹ := by
    intro x
    have hpos : (0 : ℝ) < lam + x ^ 2 := by nlinarith [sq_nonneg x]
    have h1 : (∫ u, g u x ∂(volume.restrict (Set.Ioi 0))) = ∫ u in Set.Ioi 0,
        cexp (-(((lam : ℂ) + ((x : ℝ) : ℂ)^2) * ((u : ℝ) : ℂ))) := by
      rw [hgdef]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      have hu' : 0 < u := hu
      simp only [hu', if_true]
    rw [h1]
    have h2 : (∫ u in Set.Ioi 0, cexp (-(((lam : ℂ) + ((x : ℝ) : ℂ)^2) * ((u : ℝ) : ℂ))))
        = ∫ u in Set.Ioi 0, Complex.ofReal (Real.exp (-((lam + x ^ 2) * u))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
      have harg : -(((lam : ℂ) + ((x : ℝ) : ℂ)^2) * ((u : ℝ) : ℂ))
          = ((-((lam + x ^ 2) * u)) : ℝ) := by push_cast; ring
      rw [harg, ← Complex.ofReal_exp]
    rw [h2]
    have h3 : (∫ u in Set.Ioi 0, Complex.ofReal (Real.exp (-((lam + x ^ 2) * u))))
        = Complex.ofReal (∫ u in Set.Ioi 0, Real.exp (-((lam + x ^ 2) * u))) :=
      integral_ofReal
    rw [h3]
    have h4 : (∫ u in Set.Ioi 0, Real.exp (-((lam + x ^ 2) * u)))
        = ∫ u in Set.Ioi 0, u ^ ((1 : ℝ) - 1) * Real.exp (-((lam + x ^ 2) * u)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
      rw [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, one_mul]
    rw [h4, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ) < 1) hpos,
      Real.Gamma_one, mul_one, Real.rpow_one]
    rw [one_div, Complex.ofReal_inv]
    congr 1
    push_cast
    ring
  have hmain := posSemidef_of_integral k hg hint
  convert hmain using 2
  funext x
  exact (hval x).symm

/-- **Resolvent symbol in the report's normalisation**:
`x ↦ (1 + x²/λ)⁻¹` has a positive semidefinite kernel for `λ > 0`. -/
theorem posSemidef_resolvent (k : ι → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (Kmat k (fun x => ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹)).PosSemidef := by
  have hbase := posSemidef_resolvent_base k hlam
  have hne : ∀ x : ℝ, ((lam : ℂ) + ((x : ℝ) : ℂ)^2) ≠ 0 := by
    intro x
    have hpos : (0 : ℝ) < lam + x ^ 2 := by nlinarith [sq_nonneg x]
    have hz : ((lam + x ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
    convert hz using 2
    push_cast
    ring
  have hfun : (fun x : ℝ => ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹)
      = fun x : ℝ => (lam : ℂ) * (((lam : ℂ) + ((x : ℝ) : ℂ)^2)⁻¹) := by
    funext x
    field_simp
  rw [hfun, Kmat_const_mul]
  refine hbase.smul ?_
  rw [Complex.zero_le_real]
  exact hlam.le

/-- **Every finite product of resolvent symbols** has a positive semidefinite kernel
(the report's truncated filters). -/
theorem posSemidef_prod_resolvent (k : ι → ℝ) (s : Finset ℝ)
    (hs : ∀ lam ∈ s, 0 < lam) :
    (Kmat k (fun x => ∏ lam ∈ s, ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹)).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hJ : Kmat k (fun _ : ℝ => (1 : ℂ))
          = vecMulVec (fun _ : ι => (1 : ℂ)) (star (fun _ : ι => (1 : ℂ))) := by
        ext i j
        simp [Kmat, vecMulVec]
      simp only [Finset.prod_empty]
      rw [hJ]
      exact posSemidef_vecMulVec_self_star _
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha, Kmat_hadamard]
      exact (posSemidef_resolvent k (hs a (Finset.mem_insert_self a s))).hadamard
        (ih fun lam hlam => hs lam (Finset.mem_insert_of_mem hlam))

/-- **Pointwise limits of positive semidefinite kernels are positive semidefinite.** -/
theorem posSemidef_of_tendsto (k : ι → ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ n, (Kmat k (f n)).PosSemidef) {g : ℝ → ℂ}
    (h : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    (Kmat k g).PosSemidef := by
  classical
  have hHerm : (Kmat k g).IsHermitian := by
    ext i j
    have h1 : Tendsto (fun n => star (f n (k j - k i))) atTop (𝓝 (star (g (k j - k i)))) :=
      (continuous_star.tendsto _).comp (h (k j - k i))
    have h2 : Tendsto (fun n => star (f n (k j - k i))) atTop (𝓝 (g (k i - k j))) := by
      have he : ∀ n, star (f n (k j - k i)) = f n (k i - k j) := by
        intro n
        have hh := congrFun (congrFun (hf n).isHermitian i) j
        simpa only [Kmat, Matrix.conjTranspose_apply] using hh
      simp only [he]
      exact h (k i - k j)
    have hlim := tendsto_nhds_unique h1 h2
    simpa only [Kmat, Matrix.conjTranspose_apply] using hlim
  refine PosSemidef.of_dotProduct_mulVec_nonneg hHerm (fun c => ?_)
  have hQ : Tendsto (fun n => star c ⬝ᵥ (Kmat k (f n) *ᵥ c)) atTop
      (𝓝 (star c ⬝ᵥ (Kmat k g *ᵥ c))) := by
    have hentry : ∀ i j : ι, Tendsto (fun n => Kmat k (f n) i j) atTop (𝓝 (Kmat k g i j)) :=
      fun i j => h (k i - k j)
    have hmv : ∀ i : ι, Tendsto (fun n => (Kmat k (f n) *ᵥ c) i) atTop
        (𝓝 ((Kmat k g *ᵥ c) i)) := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      exact tendsto_finsetSum _ (fun j _ => (hentry i j).mul_const (c j))
    simp only [dotProduct, Pi.star_apply]
    exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul (hmv i))
  exact ge_of_tendsto hQ (Filter.Eventually.of_forall fun n =>
    (hf n).dotProduct_mulVec_nonneg c)

/-- The set of squared frequencies `{(π j)² : 1 ≤ j ≤ n}` of the Euler product. -/
noncomputable def lamSet (n : ℕ) : Finset ℝ := (Finset.Icc 1 n).image (fun j : ℕ => (Real.pi * (j : ℝ))^2)

lemma lamSet_pos {n : ℕ} {lam : ℝ} (h : lam ∈ lamSet n) : 0 < lam := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hp : 0 < Real.pi := Real.pi_pos
  positivity

/-- **The hyperbolic modular filter symbol `x ↦ x/sinh x` has a positive semidefinite
kernel**, *conditional on the classical Euler product*
`sinh x / x = ∏_{j≥1} (1 + x²/(π j)²)`, which is the single classical input of the
report's §2.1(ii) positivity argument (there used through Lévy's continuity theorem). -/
theorem posSemidef_sinhc (k : ι → ℝ)
    (hEuler : ∀ x : ℝ, Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
        ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹) atTop
      (𝓝 (if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ)))) :
    (Kmat k (fun x => if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ))).PosSemidef :=
  posSemidef_of_tendsto k
    (fun n x => ∏ lam ∈ lamSet n, ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹)
    (fun n => posSemidef_prod_resolvent k (lamSet n) (fun _ h => lamSet_pos h)) hEuler

/-! ## Identification with the commutator (modular) functional calculus -/

/-- The matrix unit `E_{ij}`. -/
def mun (i j : ι) : Matrix ι ι ℂ := fun r s => if r = i ∧ s = j then 1 else 0

/-- For a diagonal `K`, the commutator `ad_K` acts on the matrix units by the
modular eigenvalue `k i - k j` (the report's Lemma 0.1 in the diagonal case). -/
theorem ad_diag_mun (k : ι → ℝ) (i j : ι) :
    (Matrix.diagonal (fun r => ((k r : ℝ) : ℂ)) * mun i j -
        mun i j * Matrix.diagonal (fun r => ((k r : ℝ) : ℂ)))
      = (((k i - k j : ℝ)) : ℂ) • mun i j := by
  ext r s
  rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, mun,
    smul_eq_mul]
  by_cases h : r = i ∧ s = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

/-- The modular multiplier map acts on the commutator eigenbasis by the symbol. -/
theorem multMap_mun (k : ι → ℝ) (f : ℝ → ℂ) (i j : ι) :
    multMap k f (mun i j) = f (k i - k j) • mun i j := by
  ext r s
  rw [multMap_apply, Matrix.smul_apply, smul_eq_mul, mun]
  by_cases h : r = i ∧ s = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

/-! ## Completely positive modular filters (assembly) -/

/-- The Gaussian modular filter `e^{-u ad_K²}` is completely positive for `u ≥ 0`. -/
theorem isCP_gaussian (k : ι → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    IsCP (multMap k (fun x => cexp (-((u : ℂ) * ((x : ℝ) : ℂ)^2)))) :=
  isCP_multMap_of_posSemidef k _ (posSemidef_gaussian k hu)

/-- The resolvent factor `(1 + ad_K²/λ)⁻¹` is completely positive for `λ > 0`. -/
theorem isCP_resolvent (k : ι → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    IsCP (multMap k (fun x => ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹)) :=
  isCP_multMap_of_posSemidef k _ (posSemidef_resolvent k hlam)

/-- Every truncated modular filter `∏_{λ ∈ s} (1 + ad_K²/λ)⁻¹` is completely positive. -/
theorem isCP_prod_resolvent (k : ι → ℝ) (s : Finset ℝ) (hs : ∀ lam ∈ s, 0 < lam) :
    IsCP (multMap k (fun x => ∏ lam ∈ s, ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹)) :=
  isCP_multMap_of_posSemidef k _ (posSemidef_prod_resolvent k s hs)

/-- The hyperbolic modular filter `x ↦ x/sinh x`, conditional on the Euler product. -/
theorem isCP_sinhc (k : ι → ℝ)
    (hEuler : ∀ x : ℝ, Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
        ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹) atTop
      (𝓝 (if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ)))) :
    IsCP (multMap k (fun x => if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ))) :=
  isCP_multMap_of_posSemidef k _ (posSemidef_sinhc k hEuler)

/-- **The bundle**: a real, even symbol with `f 0 = 1` and positive semidefinite kernel
gives a unital, trace-preserving, Hilbert–Schmidt self-adjoint completely positive
filter, and the filters compose by multiplication of symbols. -/
theorem unital_CP_trace_bundle (k : ι → ℝ) (f : ℝ → ℂ) (hf0 : f 0 = 1)
    (hreal : ∀ x, star (f x) = f x) (heven : ∀ x, f (-x) = f x)
    (hPD : (Kmat k f).PosSemidef) :
    multMap k f 1 = 1 ∧ (∀ A : Matrix ι ι ℂ, (multMap k f A).trace = A.trace) ∧
      IsCP (multMap k f) ∧
      (∀ A B : Matrix ι ι ℂ,
        ((multMap k f A)ᴴ * B).trace = (Aᴴ * multMap k f B).trace) ∧
      (∀ A : Matrix ι ι ℂ, A.PosSemidef → (multMap k f A).PosSemidef) :=
  ⟨multMap_apply_one k f hf0, multMap_trace k f hf0, isCP_multMap_of_posSemidef k f hPD,
    multMap_hs_selfAdjoint k f hreal, fun A hA => hPD.hadamard hA⟩

/-- **Real powers of resolvents via Gamma subordination**: for `τ > 0` the truncated
modular filter symbol `x ↦ (1 + x²/λ)^{-τ}` has a positive semidefinite kernel.
This is the `Γ(τ)`-mixture `∫_0^∞ u^{τ-1}e^{-u} e^{-u x²/λ} du = Γ(τ) (1 + x²/λ)^{-τ}`
of Gaussian kernels. -/
theorem posSemidef_resolvent_rpow (k : ι → ℝ) {lam tau : ℝ} (hlam : 0 < lam) (htau : 0 < tau) :
    (Kmat k (fun x => Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau))).PosSemidef := by
  classical
  set G : ℝ → ℝ → ℂ := fun u x => if 0 < u then
      ((u ^ (tau - 1) * Real.exp (-u) : ℝ) : ℂ) *
        cexp (-((((u / lam) : ℝ) : ℂ) * ((x : ℝ) : ℂ)^2)) else 0 with hG
  have hbase : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (tau - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent htau
  have hg : ∀ u, (Kmat k (G u)).PosSemidef := by
    intro u
    by_cases hu : 0 < u
    · have hc : (0 : ℂ) ≤ ((u ^ (tau - 1) * Real.exp (-u) : ℝ) : ℂ) := by
        rw [Complex.zero_le_real]
        positivity
      have hfac : (G u) = fun x : ℝ => ((u ^ (tau - 1) * Real.exp (-u) : ℝ) : ℂ) *
          cexp (-((((u / lam) : ℝ) : ℂ) * ((x : ℝ) : ℂ)^2)) := by
        funext x
        rw [hG]
        simp only [hu, if_true]
      rw [hfac, Kmat_const_mul]
      refine (posSemidef_gaussian k ?_).smul hc
      exact div_nonneg hu.le hlam.le
    · have hzero : (G u) = fun _ => 0 := by
        funext x
        rw [hG]
        simp only [hu, if_false]
      rw [hzero]
      exact PosSemidef.zero
  have hint : ∀ i j, Integrable (fun u => G u (k i - k j)) (volume.restrict (Set.Ioi 0)) := by
    intro i j
    refine Integrable.mono' hbase ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      rw [hG]
      refine Measurable.ite measurableSet_Ioi ?_ measurable_const
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [hG]
      have hu' : 0 < u := hu
      simp only [hu', if_true]
      · have harg : -((((u / lam) : ℝ) : ℂ) * ((k i - k j : ℝ) : ℂ)^2)
            = ((-(((k i - k j)^2 / lam) * u)) : ℝ) := by push_cast; ring
        rw [harg, norm_mul, Complex.norm_exp, Complex.ofReal_re, Complex.norm_real,
          Real.norm_eq_abs]
        have hnn : (0:ℝ) ≤ u ^ (tau - 1) * Real.exp (-u) := by positivity
        rw [abs_of_nonneg hnn]
        have hc_eq : Real.exp (-u) * u ^ (tau - 1) = u ^ (tau - 1) * Real.exp (-u) := by ring
        rw [hc_eq]
        have hexp1 : Real.exp (-(((k i - k j)^2 / lam) * u)) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr ?_
          have h2 : (0:ℝ) ≤ (k i - k j)^2 / lam := by positivity
          nlinarith
        calc u ^ (tau - 1) * Real.exp (-u) * Real.exp (-((k i - k j) ^ 2 / lam * u))
            ≤ u ^ (tau - 1) * Real.exp (-u) * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ hnn
              rw [show (-((k i - k j) ^ 2 / lam * u)) = -(((k i - k j)^2 / lam) * u) from by ring]
              exact hexp1
          _ = u ^ (tau - 1) * Real.exp (-u) := by ring
  have hval : ∀ x : ℝ, (∫ u, G u x ∂(volume.restrict (Set.Ioi 0)))
      = ((Real.Gamma tau : ℝ) : ℂ) * Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau) := by
    intro x
    have hr : (0 : ℝ) < 1 + x ^ 2 / lam := by positivity
    have h1 : (∫ u, G u x ∂(volume.restrict (Set.Ioi 0))) = ∫ u in Set.Ioi 0,
        ((u ^ (tau - 1) * Real.exp (-u) : ℝ) : ℂ) *
          cexp (-((((u / lam) : ℝ) : ℂ) * ((x : ℝ) : ℂ)^2)) := by
      rw [hG]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      have hu' : 0 < u := hu
      simp only [hu', if_true]
    rw [h1]
    have h2 : (∫ u in Set.Ioi 0, ((u ^ (tau - 1) * Real.exp (-u) : ℝ) : ℂ) *
          cexp (-((((u / lam) : ℝ) : ℂ) * ((x : ℝ) : ℂ)^2)))
        = ∫ u in Set.Ioi 0, Complex.ofReal
            (u ^ (tau - 1) * Real.exp (-((1 + x ^ 2 / lam) * u))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
      have harg : -((((u / lam) : ℝ) : ℂ) * ((x : ℝ) : ℂ)^2)
          = ((-((x ^ 2 / lam) * u)) : ℝ) := by push_cast; ring
      have hreal : (u ^ (tau - 1) * Real.exp (-u)) * Real.exp (-((x ^ 2 / lam) * u))
          = u ^ (tau - 1) * Real.exp (-((1 + x ^ 2 / lam) * u)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      calc ((u ^ (tau - 1) * Real.exp (-u) : ℝ) : ℂ) *
            cexp (-((((u / lam) : ℝ) : ℂ) * ((x : ℝ) : ℂ)^2))
          = ((u ^ (tau - 1) * Real.exp (-u) : ℝ) : ℂ) *
              ((Real.exp (-((x ^ 2 / lam) * u)) : ℝ) : ℂ) := by
            rw [harg, ← Complex.ofReal_exp]
        _ = ((u ^ (tau - 1) * Real.exp (-((1 + x ^ 2 / lam) * u)) : ℝ) : ℂ) := by
            rw [← Complex.ofReal_mul, hreal]
    rw [h2]
    have h3 : (∫ u in Set.Ioi 0, Complex.ofReal
          (u ^ (tau - 1) * Real.exp (-((1 + x ^ 2 / lam) * u))))
        = Complex.ofReal (∫ u in Set.Ioi 0,
            u ^ (tau - 1) * Real.exp (-((1 + x ^ 2 / lam) * u))) :=
      integral_ofReal
    rw [h3]
    have h4 : (∫ u in Set.Ioi 0, u ^ (tau - 1) * Real.exp (-((1 + x ^ 2 / lam) * u)))
        = (1 / (1 + x ^ 2 / lam)) ^ tau * Real.Gamma tau :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi htau hr
    rw [h4, one_div]
    push_cast
    ring
  have hmain := posSemidef_of_integral k hg hint
  have hF : (fun x : ℝ => ∫ u, G u x ∂(volume.restrict (Set.Ioi 0)))
      = fun x : ℝ => ((Real.Gamma tau : ℝ) : ℂ) *
          Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau) := by
    funext x
    exact hval x
  rw [hF] at hmain
  have hcast : (fun x : ℝ => Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau))
      = fun x : ℝ => (((Real.Gamma tau)⁻¹ : ℝ) : ℂ) *
          (((Real.Gamma tau : ℝ) : ℂ) * Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau)) := by
    funext x
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have hG_pos : (Real.Gamma tau) ≠ 0 := (Real.Gamma_pos_of_pos htau).ne'
    field_simp
  rw [hcast, Kmat_const_mul]
  refine hmain.smul ?_
  rw [Complex.zero_le_real]
  exact inv_nonneg.mpr (Real.Gamma_pos_of_pos htau).le

end CharFunKernel2

/-- The real-`τ` truncated modular filter `(1 + ad_K²/λ)^{-τ}` is completely positive. -/
theorem isCP_resolvent_rpow (k : ι → ℝ) {lam tau : ℝ} (hlam : 0 < lam) (htau : 0 < tau) :
    IsCP (multMap k (fun x => Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau))) :=
  isCP_multMap_of_posSemidef k _ (posSemidef_resolvent_rpow k hlam htau)

/-- Integer powers of the hyperbolic modular filter (the `τ = n` members of the
report's family), conditional on the Euler product. -/
theorem posSemidef_sinhc_pow (k : ι → ℝ)
    (hEuler : ∀ x : ℝ, Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
        ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹) atTop
      (𝓝 (if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ)))) (n : ℕ) :
    (Kmat k (fun x => (if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ)) ^ n)).PosSemidef :=
  posSemidef_hadamard_pow k (posSemidef_sinhc k hEuler) n


/-- Finite products of real powers of resolvents have positive semidefinite kernels. -/
theorem posSemidef_prod_resolvent_rpow (k : ι → ℝ) (s : Finset ℝ)
    (hs : ∀ lam ∈ s, 0 < lam) {tau : ℝ} (htau : 0 < tau) :
    (Kmat k (fun x => ∏ lam ∈ s,
      Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau))).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hJ : Kmat k (fun _ : ℝ => (1 : ℂ))
          = vecMulVec (fun _ : ι => (1 : ℂ)) (star (fun _ : ι => (1 : ℂ))) := by
        ext i j
        simp [Kmat, vecMulVec]
      simp only [Finset.prod_empty]
      rw [hJ]
      exact posSemidef_vecMulVec_self_star _
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha, Kmat_hadamard]
      exact (posSemidef_resolvent_rpow k (hs a (Finset.mem_insert_self a s)) htau).hadamard
        (ih fun lam hlam => hs lam (Finset.mem_insert_of_mem hlam))

/-- **Real-`τ` hyperbolic modular filter**, conditional on the `τ`-powered Euler product:
`(x/sinh x)^τ = ∏_{j≥1} (1 + x²/(π j)²)^{-τ}`.  This is the report's `Φ^τ_K` for
every real `τ > 0`. -/
theorem posSemidef_sinhc_rpow (k : ι → ℝ) {tau : ℝ} (htau : 0 < tau)
    (hEuler : ∀ x : ℝ, Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
        Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau)) atTop
      (𝓝 (Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ tau))))) :
    (Kmat k (fun x => Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ tau)))).PosSemidef :=
  posSemidef_of_tendsto k
    (fun n x => ∏ lam ∈ lamSet n, Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau))
    (fun n => posSemidef_prod_resolvent_rpow k (lamSet n) (fun _ h => lamSet_pos h) htau) hEuler

/-- The corresponding complete-positivity statement. -/
theorem isCP_sinhc_rpow (k : ι → ℝ) {tau : ℝ} (htau : 0 < tau)
    (hEuler : ∀ x : ℝ, Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
        Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau)) atTop
      (𝓝 (Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ tau))))) :
    IsCP (multMap k (fun x => Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ tau)))) :=
  isCP_multMap_of_posSemidef k _ (posSemidef_sinhc_rpow k htau hEuler)

/-! ## Closure of complete positivity under composition, and the change-of-basis gap -/

/-- Conjugation by a fixed matrix, as a linear endomorphism of `M_ι(ℂ)`. -/
noncomputable def conjMap (U : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun A := U * A * Uᴴ
  map_add' A B := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

/-- `IsCP` is closed under composition. -/
theorem IsCP.comp {Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ} (hΦ : IsCP Φ) (hΨ : IsCP Ψ) :
    IsCP (Φ.comp Ψ) := by
  intro ν _ A hA
  have h1 : amp (Φ.comp Ψ) A = amp Φ (amp Ψ A) := rfl
  rw [h1]
  exact hΦ ν (amp Ψ A) (hΨ ν A hA)

/-- **Change of basis**: for a Hermitian `K = U diag(k) Uᴴ` the modular filter is
`A ↦ U · T_{k,f}(Uᴴ A U) · Uᴴ`.  Complete positivity of the modular filter for arbitrary
Hermitian `K` therefore reduces to complete positivity of the unitary conjugation
`conjMap U` — the one remaining formalization step, stated here as an explicit
hypothesis rather than hidden. -/
theorem isCP_changeOfBasis (k : ι → ℝ) (f : ℝ → ℂ) (hPD : (Kmat k f).PosSemidef)
    (U : Matrix ι ι ℂ) (hU : IsCP (conjMap U)) (hU' : IsCP (conjMap (Uᴴ))) :
    IsCP ((conjMap U).comp ((multMap k f).comp (conjMap (Uᴴ)))) :=
  hU.comp ((isCP_multMap_of_posSemidef k f hPD).comp hU')

/-- Unitality and trace preservation of the change-of-basis filter, unconditionally. -/
theorem changeOfBasis_unital_trace (k : ι → ℝ) (f : ℝ → ℂ) (hf0 : f 0 = 1)
    (U : Matrix ι ι ℂ) (hUU : U * Uᴴ = 1) (hUU' : Uᴴ * U = 1) :
    ((conjMap U).comp ((multMap k f).comp (conjMap (Uᴴ)))) 1 = 1 ∧
      ∀ A : Matrix ι ι ℂ,
        (((conjMap U).comp ((multMap k f).comp (conjMap (Uᴴ)))) A).trace = A.trace := by
  have hmap : ∀ A : Matrix ι ι ℂ,
      ((conjMap U).comp ((multMap k f).comp (conjMap (Uᴴ)))) A = U * (multMap k f (Uᴴ * A * U)) * Uᴴ := by
    intro A
    simp only [LinearMap.comp_apply, conjMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Matrix.conjTranspose_conjTranspose]
  refine ⟨?_, fun A => ?_⟩
  · rw [hmap]
    simp only [Matrix.mul_one]
    rw [hUU', multMap_apply_one k f hf0, Matrix.mul_one, hUU]
  · rw [hmap, Matrix.trace_mul_cycle, hUU', Matrix.one_mul, multMap_trace k f hf0,
      Matrix.trace_mul_cycle, hUU, Matrix.one_mul]

end MomentGeometry.Operator.CP

/-! ## Axiom audit -/

#print axioms MomentGeometry.Operator.CP.isCP_multMap_iff
#print axioms MomentGeometry.Operator.CP.posSemidef_charFun
#print axioms MomentGeometry.Operator.CP.posSemidef_of_integral
#print axioms MomentGeometry.Operator.CP.posSemidef_gaussian
#print axioms MomentGeometry.Operator.CP.posSemidef_resolvent_base
#print axioms MomentGeometry.Operator.CP.posSemidef_resolvent
#print axioms MomentGeometry.Operator.CP.posSemidef_prod_resolvent
#print axioms MomentGeometry.Operator.CP.posSemidef_of_tendsto
#print axioms MomentGeometry.Operator.CP.posSemidef_sinhc
#print axioms MomentGeometry.Operator.CP.isCP_gaussian
#print axioms MomentGeometry.Operator.CP.isCP_resolvent
#print axioms MomentGeometry.Operator.CP.isCP_prod_resolvent
#print axioms MomentGeometry.Operator.CP.isCP_sinhc
#print axioms MomentGeometry.Operator.CP.unital_CP_trace_bundle
#print axioms MomentGeometry.Operator.CP.multMap_comp
#print axioms MomentGeometry.Operator.CP.multMap_trace
#print axioms MomentGeometry.Operator.CP.multMap_hs_selfAdjoint
#print axioms MomentGeometry.Operator.CP.ad_diag_mun
#print axioms MomentGeometry.Operator.CP.posSemidef_resolvent_rpow
#print axioms MomentGeometry.Operator.CP.isCP_resolvent_rpow
#print axioms MomentGeometry.Operator.CP.posSemidef_sinhc_pow
#print axioms MomentGeometry.Operator.CP.posSemidef_hadamard_pow
#print axioms MomentGeometry.Operator.CP.posSemidef_prod_resolvent_rpow
#print axioms MomentGeometry.Operator.CP.posSemidef_sinhc_rpow
#print axioms MomentGeometry.Operator.CP.isCP_sinhc_rpow
#print axioms MomentGeometry.Operator.CP.IsCP.comp
#print axioms MomentGeometry.Operator.CP.conjMap
#print axioms MomentGeometry.Operator.CP.isCP_changeOfBasis
#print axioms MomentGeometry.Operator.CP.changeOfBasis_unital_trace
#print axioms MomentGeometry.Operator.CP.multMap_mun
