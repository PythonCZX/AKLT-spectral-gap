/-
Closure of the two analytic bridges of `MomentGeometry.Operator.CP.Base.lean`
(accepted package `results/coherent_continuation/review_smwh9rp69_m1`, swarm `smwh9rp69`).

1. **Euler's product for `x / sinh x`.**  From Mathlib's Euler sine product
   `Complex.tendsto_euler_sin_prod` at the imaginary argument `I x / π` we derive
   `∏_{j=1}^{n} (1 + x²/(πj)²) → sinh x / x`, hence
   `∏_{j=1}^{n} (1 + x²/(πj)²)^{-1} → x / sinh x`
   and, for *every* real exponent `τ`, the `τ`-th power version.  This discharges the
   hypothesis `hEuler` that `posSemidef_sinhc`, `isCP_sinhc`, `posSemidef_sinhc_pow`,
   `posSemidef_sinhc_rpow` and `isCP_sinhc_rpow` had left open.

2. **`IsCP (conjMap U)`.**  Conjugation by an arbitrary matrix is completely positive
   (no unitarity needed): the amplification is `W * A * Wᴴ` for the block matrix
   `W = U ⊗ 1`, and `Matrix.PosSemidef.mul_mul_conjTranspose_same` gives positivity.
   This discharges the hypotheses `hU`, `hU'` of `isCP_changeOfBasis`, and yields the
   unconditional complete positivity of the modular filter of an arbitrary Hermitian
   matrix `K` built from its spectral decomposition.

3. **The commutator functional calculus** `Φ_K = f(ad_K)` with `ad_K A = K A - A K`:
   monomial and polynomial symbols for diagonal `K` (`multMap_pow_eq_adMap_pow`,
   `multMap_polynomial`), the conjugation intertwining (`conjMap_adMap`, `conjMap_adMap_pow`),
   the general unitary presentation (`modularFilter_polynomial_eq_adMap`) and its
   independence of that presentation (`modularFilter_polynomial_wellDefined`), and — using
   Mathlib's spectral theorem — the filter `spectralFilter` of an arbitrary Hermitian matrix,
   which is CP for every PSD-kernel symbol, unital and trace preserving for `f 0 = 1`, and
   equal to `∑ c n (ad_K)^n` on polynomial symbols.

4. **The report's bundle** for the actual symbol: `bundle_sinhc`, `bundle_sinhc_rpow`
   (every real power `τ > 0`) and `bundle_prod_resolvent_rpow` / `bundle_sinhc_truncated`
   (every finite product `Φ^τ_{K,R}`) — unital, trace preserving, completely positive,
   Hilbert–Schmidt self-adjoint and positivity preserving.

No statement of the base file is altered or weakened; every new theorem is additive.
-/
import MomentGeometry.Operator.CP.Base

open Filter Topology Matrix
open scoped BigOperators ComplexOrder

set_option linter.unusedSectionVars false

namespace MomentGeometry.Operator.CP

/-! ## 1. Euler's product for `x / sinh x`, and its real powers -/

/-- Per-factor identity: the complex Euler sine factor at the imaginary argument
`I x / π` is the real factor `1 + x²/(π(j+1))²`. -/
lemma sinhc_factor (x : ℝ) (j : ℕ) :
    ((1:ℂ) - (Complex.I * (x:ℂ) / (Real.pi:ℂ))^2 / ((j:ℂ)+1)^2)
      = ((1 + x^2/((Real.pi * ((j:ℝ)+1))^2) : ℝ) : ℂ) := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by
    have : (Real.pi:ℝ) ≠ 0 := Real.pi_ne_zero
    exact_mod_cast this
  have hj : ((j:ℂ)+1) ≠ 0 := by
    have hjr : ((j:ℝ)+1) ≠ 0 := by positivity
    have hjeq : ((j:ℂ)+1) = (((j:ℝ)+1 : ℝ) : ℂ) := by push_cast; ring
    rw [hjeq]
    exact_mod_cast hjr
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

/-- The `n`-th partial product of the real factors is the real part of the
`n`-th partial product of the complex Euler sine factors. -/
lemma prod_factor (x : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n, ((1:ℂ) - (Complex.I * (x:ℂ) / (Real.pi:ℂ))^2 / ((j:ℂ)+1)^2))
      = ((∏ j ∈ Finset.range n, (1 + x^2/((Real.pi * ((j:ℝ)+1))^2)) : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, sinhc_factor x n,
        ← Complex.ofReal_mul]

/-- **Euler's product, complex form.**  For `x ≠ 0` the partial products of the
Euler sine factors at `I x / π` tend to `sinh x / x`. -/
lemma tendsto_prod_complex (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n,
      ((1:ℂ) - (Complex.I * (x:ℂ) / (Real.pi:ℂ))^2 / ((j:ℂ)+1)^2))
      atTop (𝓝 ((Real.sinh x : ℂ) / (x:ℂ))) := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by
    have : (Real.pi:ℝ) ≠ 0 := Real.pi_ne_zero
    exact_mod_cast this
  have hz : (Real.pi:ℂ) * (Complex.I * (x:ℂ) / (Real.pi:ℂ)) = Complex.I * (x:ℂ) := by
    field_simp
  have hsin : Complex.sin (Complex.I * (x:ℂ)) = (Real.sinh x : ℂ) * Complex.I := by
    rw [mul_comm Complex.I, Complex.sin_mul_I, Complex.ofReal_sinh]
  have h := Complex.tendsto_euler_sin_prod (Complex.I * (x:ℂ) / (Real.pi:ℂ))
  rw [hz, hsin] at h
  have hIx : (Complex.I * (x:ℂ)) ≠ 0 := by
    simp [hx]
  have h2 := h.mul_const ((Complex.I * (x:ℂ))⁻¹)
  convert h2 using 1
  · ext n
    rw [mul_assoc, mul_comm (∏ j ∈ Finset.range n,
      ((1:ℂ) - (Complex.I * (x:ℂ) / (Real.pi:ℂ))^2 / ((j:ℂ)+1)^2)) ((Complex.I * (x:ℂ))⁻¹),
      ← mul_assoc, mul_inv_cancel₀ hIx, one_mul]
  · exact congrArg 𝓝 (by field_simp)

/-- **Euler's product, real form.**  `∏_{j<n}(1 + x²/(π(j+1))²) → sinh x / x`. -/
lemma tendsto_prod_real (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1 + x^2/((Real.pi * ((j:ℝ)+1))^2)))
      atTop (𝓝 (Real.sinh x / x)) := by
  have h := tendsto_prod_complex x hx
  have hre : Tendsto (fun n : ℕ => ((∏ j ∈ Finset.range n,
      ((1:ℂ) - (Complex.I * (x:ℂ) / (Real.pi:ℂ))^2 / ((j:ℂ)+1)^2)) : ℂ).re) atTop
      (𝓝 (((Real.sinh x : ℂ) / (x:ℂ)).re)) := by
    simpa [Function.comp_def] using
      (Complex.continuous_re.tendsto ((Real.sinh x : ℂ) / (x:ℂ))).comp h
  have hlim : (((Real.sinh x : ℂ) / (x:ℂ))).re = Real.sinh x / x := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  simp only [prod_factor, Complex.ofReal_re, hlim] at hre
  exact hre

/-- **Euler's product, reciprocal form.**  `∏_{j<n}(1 + x²/(π(j+1))²)⁻¹ → x / sinh x`. -/
lemma tendsto_prod_inv_real (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1 + x^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹)
      atTop (𝓝 (x / Real.sinh x)) := by
  have h := tendsto_prod_real x hx
  have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have hne : Real.sinh x / x ≠ 0 := div_ne_zero hsinh hx
  have h2 : Tendsto (fun n : ℕ => (∏ j ∈ Finset.range n,
      (1 + x^2/((Real.pi * ((j:ℝ)+1))^2)))⁻¹) atTop (𝓝 ((Real.sinh x / x)⁻¹)) :=
    h.inv₀ hne
  have h3 : Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n,
      (1 + x^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹) atTop (𝓝 ((Real.sinh x / x)⁻¹)) :=
    Tendsto.congr (fun n => (Finset.prod_inv_distrib _).symm) h2
  rw [inv_div] at h3
  exact h3

/-- **Euler's product at every real exponent**, range form. -/
lemma tendsto_prod_rpow_real (x : ℝ) (hx : x ≠ 0) (tau : ℝ) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n,
        ((1 + x^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹) ^ tau)
      atTop (𝓝 ((x / Real.sinh x) ^ tau)) := by
  have h := tendsto_prod_inv_real x hx
  have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have hne : x / Real.sinh x ≠ 0 := div_ne_zero hx hsinh
  have h2 : Tendsto (fun n : ℕ => (∏ j ∈ Finset.range n,
      (1 + x^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹) ^ tau) atTop (𝓝 ((x / Real.sinh x) ^ tau)) :=
    h.rpow_const (p := tau) (Or.inl hne)
  exact Tendsto.congr (fun n => (Real.finsetProd_rpow _ _ (fun j _ => by positivity) tau).symm) h2

/-- **Euler's product, inverse, with the `x = 0` convention** matching the
`sinhc` symbol `if x = 0 then 1 else x / sinh x`. -/
theorem tendsto_sinhc_prod (x : ℝ) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1 + x^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹)
      atTop (𝓝 (if x = 0 then 1 else x / Real.sinh x)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h1 : (fun n : ℕ => ∏ j ∈ Finset.range n,
        (1 + (0:ℝ)^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹) = fun _ => 1 := by
      ext n; simp
    rw [h1]
    simp
  · rw [if_neg hx]
    exact tendsto_prod_inv_real x hx

/-- **Euler's product at every real exponent**, with the `x = 0` convention. -/
theorem tendsto_sinhc_prod_rpow (x : ℝ) (tau : ℝ) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n,
        ((1 + x^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹) ^ tau)
      atTop (𝓝 ((if x = 0 then 1 else x / Real.sinh x) ^ tau)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h1 : (fun n : ℕ => ∏ j ∈ Finset.range n,
        ((1 + (0:ℝ)^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹) ^ tau) = fun _ => 1 := by
      ext n; simp
    rw [h1]
    simp
  · rw [if_neg hx]
    exact tendsto_prod_rpow_real x hx tau

/-! ## 1b. Reindexing to the spectrum `lamSet n` and the complex form used by the base file -/

/-- `Complex.ofReal` of a finite product. -/
lemma prod_ofReal {α : Type*} (s : Finset α) (A : α → ℝ) :
    (↑(∏ i ∈ s, A i) : ℂ) = ∏ i ∈ s, (↑(A i) : ℂ) := by
  simpa only [Complex.ofRealHom_eq_coe] using map_prod Complex.ofRealHom A s

/-- A product over `Icc 1 n` is the corresponding product over `range n`. -/
lemma prod_Icc_one_eq_range (g : ℕ → ℝ) (n : ℕ) :
    (∏ j ∈ Finset.Icc 1 n, g j) = ∏ i ∈ Finset.range n, g (i+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

/-- The product over `lamSet n = {(π j)² : 1 ≤ j ≤ n}` is the range product with
`j ↦ (π (j+1))²`. -/
lemma prod_lamSet_eq (g : ℝ → ℝ) (n : ℕ) :
    (∏ lam ∈ lamSet n, g lam) = ∏ j ∈ Finset.range n, g ((Real.pi * ((j:ℝ)+1))^2) := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => (Real.pi * (j:ℝ))^2) ↑(Finset.Icc 1 n) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
    have ha0 : 0 < (a:ℝ) := by
      have h : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha.1
      exact_mod_cast h
    have hb0 : 0 < (b:ℝ) := by
      have h : 0 < b := lt_of_lt_of_le Nat.zero_lt_one hb.1
      exact_mod_cast h
    have h1 : 0 ≤ Real.pi * (a:ℝ) := by positivity
    have h2 : 0 ≤ Real.pi * (b:ℝ) := by positivity
    have hp : Real.pi * (a:ℝ) = Real.pi * (b:ℝ) := by
      rw [← pow_left_inj₀ h1 h2 (by norm_num : (2:ℕ) ≠ 0)]
      exact hab
    have hcast : (a:ℝ) = (b:ℝ) := mul_left_cancel₀ Real.pi_ne_zero hp
    exact_mod_cast hcast
  have hIcc : (∏ j ∈ Finset.Icc 1 n, g ((Real.pi * (j:ℝ))^2))
      = ∏ i ∈ Finset.range n, g ((Real.pi * ((i:ℝ)+1))^2) := by
    rw [prod_Icc_one_eq_range (fun j => g ((Real.pi * (j:ℝ))^2)) n]
    simp only [Nat.cast_add, Nat.cast_one]
  calc (∏ lam ∈ lamSet n, g lam)
      = ∏ j ∈ Finset.Icc 1 n, g ((Real.pi * (j:ℝ))^2) := by
        rw [lamSet, Finset.prod_image hinj]
    _ = ∏ i ∈ Finset.range n, g ((Real.pi * ((i:ℝ)+1))^2) := hIcc

/-- The `hEuler` hypothesis of `posSemidef_sinhc`, proved: the complex partial products
of the resolvent factors converge to the `sinhc` symbol. -/
theorem euler_sinhc (x : ℝ) :
    Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
        ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹) atTop
      (𝓝 (if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ))) := by
  have h := tendsto_sinhc_prod x
  have h1 : Tendsto (fun n : ℕ => ((∏ j ∈ Finset.range n,
      (1 + x^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹ : ℝ) : ℂ)) atTop
      (𝓝 (((if x = 0 then 1 else x / Real.sinh x) : ℝ) : ℂ)) := by
    have hc := (Complex.continuous_ofReal.tendsto
      ((if x = 0 then 1 else x / Real.sinh x) : ℝ)).comp h
    simpa [Function.comp_def] using hc
  have h2 : Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
      ((1 : ℂ) + ((x : ℝ) : ℂ)^2 / (lam : ℂ))⁻¹) atTop
      (𝓝 (((if x = 0 then 1 else x / Real.sinh x) : ℝ) : ℂ)) := by
    refine Tendsto.congr (fun n => ?_) h1
    rw [prod_ofReal, ← prod_ofReal, ← prod_lamSet_eq (fun lam => (1 + x^2/lam)⁻¹) n,
      prod_ofReal]
    refine Finset.prod_congr rfl fun lam _ => ?_
    rw [Complex.ofReal_inv]
    congr 1
    push_cast
    ring
  have hlim : (((if x = 0 then 1 else x / Real.sinh x) : ℝ) : ℂ)
      = (if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ)) := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [if_neg hx, if_neg hx]
      push_cast
      ring
  rw [hlim] at h2
  exact h2

/-- The `hEuler` hypothesis of `posSemidef_sinhc_rpow`, proved for **every** real
exponent `τ` (the base file only needed `τ > 0`). -/
theorem euler_sinhc_rpow (x : ℝ) (tau : ℝ) :
    Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
        Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau)) atTop
      (𝓝 (Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ tau)))) := by
  have h := tendsto_sinhc_prod_rpow x tau
  have h1 : Tendsto (fun n : ℕ => ((∏ j ∈ Finset.range n,
      ((1 + x^2/((Real.pi * ((j:ℝ)+1))^2))⁻¹) ^ tau : ℝ) : ℂ)) atTop
      (𝓝 (((if x = 0 then 1 else x / Real.sinh x) ^ tau : ℝ) : ℂ)) := by
    have hc := (Complex.continuous_ofReal.tendsto
      (((if x = 0 then 1 else x / Real.sinh x) ^ tau) : ℝ)).comp h
    simpa [Function.comp_def] using hc
  have h2 : Tendsto (fun n : ℕ => ∏ lam ∈ lamSet n,
      Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau)) atTop
      (𝓝 (((if x = 0 then 1 else x / Real.sinh x) ^ tau : ℝ) : ℂ)) := by
    refine Tendsto.congr (fun n => ?_) h1
    rw [prod_ofReal, ← prod_ofReal,
      ← prod_lamSet_eq (fun lam => (((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau) n, prod_ofReal]
  exact h2

/-! ## 1c. The `hEuler` hypotheses are now theorems: unconditional versions -/

section Unconditional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `posSemidef_sinhc` without the Euler-product hypothesis. -/
theorem posSemidef_sinhc_uncond (k : ι → ℝ) :
    (Kmat k (fun x => if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ))).PosSemidef :=
  posSemidef_sinhc k euler_sinhc

/-- `isCP_sinhc` without the Euler-product hypothesis. -/
theorem isCP_sinhc_uncond (k : ι → ℝ) :
    IsCP (multMap k (fun x => if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ))) :=
  isCP_sinhc k euler_sinhc

/-- `posSemidef_sinhc_pow` without the Euler-product hypothesis. -/
theorem posSemidef_sinhc_pow_uncond (k : ι → ℝ) (n : ℕ) :
    (Kmat k (fun x => (if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ)) ^ n)).PosSemidef :=
  posSemidef_sinhc_pow k euler_sinhc n

/-- `posSemidef_sinhc_rpow` without the Euler-product hypothesis (every real `τ > 0`). -/
theorem posSemidef_sinhc_rpow_uncond (k : ι → ℝ) {tau : ℝ} (htau : 0 < tau) :
    (Kmat k (fun x => Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ tau)))).PosSemidef :=
  posSemidef_sinhc_rpow k htau (fun x => euler_sinhc_rpow x tau)

/-- `isCP_sinhc_rpow` without the Euler-product hypothesis (every real `τ > 0`). -/
theorem isCP_sinhc_rpow_uncond (k : ι → ℝ) {tau : ℝ} (htau : 0 < tau) :
    IsCP (multMap k (fun x => Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ tau)))) :=
  isCP_sinhc_rpow k htau (fun x => euler_sinhc_rpow x tau)

/-- The exponent `τ = 0` endpoint of the report's range `τ ≥ 0`: the filter is the identity. -/
theorem isCP_sinhc_rpow_zero (k : ι → ℝ) :
    IsCP (multMap k (fun x => Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ (0:ℝ))))) := by
  have hsym : (fun x : ℝ => Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ (0:ℝ))))
      = fun _ => 1 := by
    funext x; simp
  rw [hsym]
  have hJ : (Kmat k (fun _ : ℝ => (1:ℂ)))
      = vecMulVec (fun _ : ι => (1:ℂ)) (star (fun _ : ι => (1:ℂ))) := by
    ext i j; simp [Kmat, vecMulVec]
  rw [isCP_multMap_iff, hJ]
  exact posSemidef_vecMulVec_self_star _

end Unconditional

/-! ## 2. Complete positivity of `A ↦ U A Uᴴ` for an arbitrary matrix `U` -/

section Conj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix product of complex matrices with the `Matrix` multiplication instance
fixed explicitly (unambiguous for instance search). -/
def mmul {m n p : Type*} [Fintype n] (M : Matrix m n ℂ) (N : Matrix n p ℂ) : Matrix m p ℂ :=
  M * N

lemma mmul_apply {m n p : Type*} [Fintype n] (M : Matrix m n ℂ) (N : Matrix n p ℂ)
    (i : m) (j : p) : mmul M N i j = ∑ k, M i k * N k j := Matrix.mul_apply

/-- The block matrix `U ⊗ 1` on the index set `ι × ν`. -/
def Tmat (U : Matrix ι ι ℂ) (ν : Type*) [DecidableEq ν] : Matrix (ι × ν) (ι × ν) ℂ :=
  fun p q => if p.2 = q.2 then U p.1 q.1 else 0

lemma Tmat_mul_apply {ν : Type*} [Fintype ν] [DecidableEq ν] (U : Matrix ι ι ℂ)
    (A : Matrix (ι × ν) (ι × ν) ℂ) (p : ι × ν) (r : ι × ν) :
    mmul (Tmat U ν) A p r = ∑ x : ι, U p.1 x * A (x, p.2) r := by
  rw [mmul_apply]
  simp only [Fintype.sum_prod_type, Tmat, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma Tmat_conjTranspose_apply {ν : Type*} [DecidableEq ν] (U : Matrix ι ι ℂ)
    (p q : ι × ν) :
    (Tmat U ν)ᴴ p q = if q.2 = p.2 then star (U q.1 p.1) else 0 := by
  simp only [Matrix.conjTranspose_apply, Tmat, apply_ite star, star_zero]

/-- Entry formula for the sandwich of `A` between `U ⊗ 1` and its adjoint. -/
lemma Tmat_sandwich_apply {ν : Type*} [Fintype ν] [DecidableEq ν] (U : Matrix ι ι ℂ)
    (A : Matrix (ι × ν) (ι × ν) ℂ) (p q : ι × ν) :
    mmul (mmul (Tmat U ν) A) (Tmat U ν)ᴴ p q
      = ∑ j : ι, ∑ x : ι, U p.1 x * A (x, p.2) (j, q.2) * star (U q.1 j) := by
  rw [mmul_apply]
  simp only [Tmat_mul_apply, Fintype.sum_prod_type, Tmat_conjTranspose_apply, mul_ite,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]

/-- Entry formula for an ordinary sandwich `U * B * Uᴴ` (matrices over `ι`). -/
lemma sandwich_apply (U B : Matrix ι ι ℂ) (i j : ι) :
    (U * B * Uᴴ : Matrix ι ι ℂ) i j
      = ∑ j' : ι, ∑ x : ι, U i x * B x j' * star (U j j') := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.conjTranspose_apply]

/-- Entry formula for the amplification of `conjMap U`. -/
lemma amp_conjMap_apply {ν : Type*} [Fintype ν] (U : Matrix ι ι ℂ)
    (A : Matrix (ι × ν) (ι × ν) ℂ) (p q : ι × ν) :
    amp (conjMap U) A p q
      = ∑ j : ι, ∑ x : ι, U p.1 x * A (x, p.2) (j, q.2) * star (U q.1 j) := by
  have hmain : amp (conjMap U) A p q
      = (U * Matrix.of (fun r s : ι => A (r, p.2) (s, q.2)) * Uᴴ
          : Matrix ι ι ℂ) p.1 q.1 := rfl
  rw [hmain, sandwich_apply]
  simp only [Matrix.of_apply]

/-- The amplification of `conjMap U` is the sandwich by `U ⊗ 1`. -/
theorem amp_conjMap {ν : Type*} [Fintype ν] [DecidableEq ν] (U : Matrix ι ι ℂ)
    (A : Matrix (ι × ν) (ι × ν) ℂ) :
    amp (conjMap U) A = mmul (mmul (Tmat U ν) A) (Tmat U ν)ᴴ := by
  ext p q
  rw [amp_conjMap_apply, Tmat_sandwich_apply]

/-- **Conjugation by an arbitrary matrix is completely positive.**  No unitarity
hypothesis is needed; the unitary case is the instance `U Uᴴ = Uᴴ U = 1`. -/
theorem isCP_conjMap (U : Matrix ι ι ℂ) : IsCP (conjMap U) := by
  classical
  intro ν _ A hA
  rw [amp_conjMap]
  exact hA.mul_mul_conjTranspose_same (Tmat U ν)

/-- The change-of-basis modular filter is completely positive with no extra
hypothesis (this is `isCP_changeOfBasis` without `hU`, `hU'`). -/
theorem isCP_changeOfBasis' (k : ι → ℝ) (f : ℝ → ℂ) (hPD : (Kmat k f).PosSemidef)
    (U : Matrix ι ι ℂ) :
    IsCP ((conjMap U).comp ((multMap k f).comp (conjMap (Uᴴ)))) :=
  (isCP_conjMap U).comp ((isCP_multMap_of_posSemidef k f hPD).comp (isCP_conjMap (Uᴴ)))


end Conj

/-! ## 3. The commutator functional calculus of the modular filter

The report writes the modular filter as `Φ_K = f(ad_K)` with `ad_K A = K A - A K`
(so that on the eigenbasis `ad_K E_ij = (k_i - k_j) E_ij`).  Here we prove:

* for a diagonal `K = diag k` the multiplier with the monomial symbol `x ↦ x^n` **is** the
  `n`-th power of `ad_K` (`multMap_pow_eq_adMap_pow`), and the same for every polynomial
  symbol (`multMap_polynomial`);
* conjugation intertwines `ad` (`conjMap_adMap`) and preserves its powers;
* consequently the modular filter of any `K = U · diag k · Uᴴ` with `U` unitary acts on a
  polynomial symbol exactly as `∑ c n (ad_K)^n` (`modularFilter_polynomial_eq_adMap`), and
  this is independent of the chosen spectral presentation
  (`modularFilter_polynomial_wellDefined`);
* instantiated at Mathlib's spectral theorem, every Hermitian `K` has such a presentation and
  the resulting filter (`spectralFilter`) is unital, trace preserving and completely positive
  for symbols with positive semidefinite kernel, and restricted to polynomial symbols it is
  the polynomial `∑ c n (ad_K)^n` in the commutator — the faithful Lean form of the report's
  `Φ_K = f(ad_K)` on the polynomial subclass of symbols.
-/

section Commutator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The commutator map `A ↦ K A - A K`. -/
noncomputable def adMap (K : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun A := mmul K A - mmul A K
  map_add' A B := by simp only [mmul, Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c A := by
    simp only [mmul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub]

omit [DecidableEq ι] in
lemma adMap_apply (K A : Matrix ι ι ℂ) : adMap K A = mmul K A - mmul A K := rfl

lemma diagonal_mul_apply {d : ι → ℂ} (A : Matrix ι ι ℂ) (i j : ι) :
    (Matrix.diagonal d * A) i j = d i * A i j := by
  simp [Matrix.mul_apply, Matrix.diagonal, Finset.mem_univ]

lemma mul_diagonal_apply {d : ι → ℂ} (A : Matrix ι ι ℂ) (i j : ι) :
    (A * Matrix.diagonal d) i j = A i j * d j := by
  simp [Matrix.mul_apply, Matrix.diagonal, Finset.mem_univ]

lemma adMap_diagonal_apply {d : ι → ℂ} (A : Matrix ι ι ℂ) (i j : ι) :
    adMap (Matrix.diagonal d) A i j = (d i - d j) * A i j := by
  rw [adMap_apply, mmul, mmul, Matrix.sub_apply, diagonal_mul_apply, mul_diagonal_apply,
    sub_mul, mul_comm (A i j) (d j)]

/-- The multiplier with the identity symbol is the commutator with the diagonal matrix. -/
lemma multMap_eq_adMap_diagonal (k : ι → ℝ) :
    multMap k (fun x => (x:ℂ)) = adMap (Matrix.diagonal (fun i => (k i : ℂ))) := by
  ext A i j
  rw [multMap_apply, adMap_diagonal_apply]
  push_cast
  ring

/-- **Monomial functional calculus**: the multiplier with symbol `x ↦ x^n` is the `n`-th
power of the commutator with the diagonal spectrum matrix. -/
lemma multMap_pow_eq_adMap_pow (k : ι → ℝ) (n : ℕ) :
    multMap k (fun x => (x:ℂ)^n) = (adMap (Matrix.diagonal (fun i => (k i : ℂ))))^n := by
  induction n with
  | zero =>
      rw [pow_zero]
      have h : (fun x : ℝ => (x:ℂ)^0) = fun _ => 1 := by funext x; simp
      rw [h, multMap_one]
      rfl
  | succ n ih =>
      have h : (fun x : ℝ => (x:ℂ)^(n+1)) = (fun x : ℝ => (x:ℂ)^n * (x:ℂ)) := by
        funext x; rw [pow_succ]
      rw [h, ← multMap_comp, ih, multMap_eq_adMap_diagonal]
      rfl

lemma multMap_add (k : ι → ℝ) (f g : ℝ → ℂ) :
    multMap k (f + g) = multMap k f + multMap k g := by
  ext A i j
  simp [multMap_apply, add_mul]

lemma multMap_smul (k : ι → ℝ) (c : ℂ) (f : ℝ → ℂ) :
    multMap k (c • f) = c • multMap k f := by
  ext A i j
  simp [multMap_apply, mul_assoc]

/-- **Polynomial functional calculus** (diagonal case). -/
lemma multMap_polynomial (k : ι → ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    multMap k (fun x => ∑ n ∈ s, c n * (x:ℂ)^n)
      = ∑ n ∈ s, c n • (adMap (Matrix.diagonal (fun i => (k i : ℂ))))^n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h : (fun x : ℝ => ∑ n ∈ (∅ : Finset ℕ), c n * (x:ℂ)^n) = 0 := by
        funext x; simp
      rw [h, Finset.sum_empty]
      ext A i j
      simp [multMap_apply]
  | insert a s ha ih =>
      have h : (fun x : ℝ => ∑ n ∈ insert a s, c n * (x:ℂ)^n)
          = (c a • fun x : ℝ => (x:ℂ)^a) + (fun x : ℝ => ∑ n ∈ s, c n * (x:ℂ)^n) := by
        funext x
        rw [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h, multMap_add, multMap_smul, multMap_pow_eq_adMap_pow, ih, Finset.sum_insert ha]

/-- Sandwiching preserves products when `U` is unitary. -/
lemma sandwich_mul (U X Y : Matrix ι ι ℂ) (hU'U : mmul Uᴴ U = 1) :
    mmul (mmul (mmul U X) Uᴴ) (mmul (mmul U Y) Uᴴ) = mmul (mmul U (mmul X Y)) Uᴴ := by
  simp only [mmul] at hU'U ⊢
  have h : (U * X * Uᴴ) * (U * Y * Uᴴ) = (U * X) * (Uᴴ * U) * (Y * Uᴴ) := by
    noncomm_ring
  rw [h, hU'U, Matrix.mul_one]
  noncomm_ring

/-- Conjugation intertwines the commutator with the conjugated matrix. -/
theorem conjMap_adMap (U K : Matrix ι ι ℂ) (hU'U : mmul Uᴴ U = 1) (A : Matrix ι ι ℂ) :
    conjMap U (adMap K A) = adMap (mmul (mmul U K) Uᴴ) (conjMap U A) := by
  have h1 : (U * K * Uᴴ) * (U * A * Uᴴ) = U * (K * A) * Uᴴ := by
    simpa only [mmul] using sandwich_mul U K A hU'U
  have h2 : (U * A * Uᴴ) * (U * K * Uᴴ) = U * (A * K) * Uᴴ := by
    simpa only [mmul] using sandwich_mul U A K hU'U
  simp only [adMap, conjMap, LinearMap.coe_mk, AddHom.coe_mk, mmul]
  rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]

lemma conjMap_conjMap (U : Matrix ι ι ℂ) (hUU : U * Uᴴ = 1) (A : Matrix ι ι ℂ) :
    conjMap U (conjMap Uᴴ A) = A := by
  simp only [conjMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_conjTranspose]
  have h : U * (Uᴴ * A * U) * Uᴴ = (U * Uᴴ) * A * (U * Uᴴ) := by noncomm_ring
  rw [h, hUU, Matrix.one_mul, Matrix.mul_one]

/-- Conjugation intertwines the powers of the commutator. -/
theorem conjMap_adMap_pow {d : ι → ℂ} (U : Matrix ι ι ℂ) (hU'U : mmul Uᴴ U = 1)
    (n : ℕ) (X : Matrix ι ι ℂ) :
    conjMap U (((adMap (Matrix.diagonal d))^n) X)
      = ((adMap (mmul (mmul U (Matrix.diagonal d)) Uᴴ))^n) (conjMap U X) := by
  revert X
  induction n with
  | zero => intro X; rfl
  | succ n ih =>
      intro X
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        conjMap_adMap U _ hU'U, ih]

/-- **Polynomial functional calculus for the modular filter.**  If `K = U · diag k · Uᴴ`
with `U` unitary, then the modular filter with polynomial symbol `f x = ∑ c n * x^n`
acts as the polynomial `∑ c n (ad_K)^n` in the commutator `ad_K A = K A - A K`. -/
theorem modularFilter_polynomial_eq_adMap (k : ι → ℝ) (U : Matrix ι ι ℂ)
    (hUU : U * Uᴴ = 1) (hU'U : Uᴴ * U = 1)
    (s : Finset ℕ) (c : ℕ → ℂ) (A : Matrix ι ι ℂ) :
    conjMap U (multMap k (fun x => ∑ n ∈ s, c n * (x:ℂ)^n) (conjMap Uᴴ A))
      = ∑ n ∈ s, c n •
        (((adMap (mmul (mmul U (Matrix.diagonal (fun i => (k i : ℂ)))) Uᴴ))^n) A) := by
  classical
  rw [multMap_polynomial]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [conjMap_adMap_pow U hU'U n (conjMap Uᴴ A), conjMap_conjMap U hUU]

/-- **The polynomial modular filter depends only on `K`, not on the spectral
factorization.** -/
theorem modularFilter_polynomial_wellDefined (k k' : ι → ℝ) (U U' : Matrix ι ι ℂ)
    (hUU : U * Uᴴ = 1) (hU'U : Uᴴ * U = 1)
    (hVV : U' * U'ᴴ = 1) (hV'V : U'ᴴ * U' = 1)
    (hK : mmul (mmul U (Matrix.diagonal (fun i => (k i : ℂ)))) Uᴴ
        = mmul (mmul U' (Matrix.diagonal (fun i => (k' i : ℂ)))) U'ᴴ)
    (s : Finset ℕ) (c : ℕ → ℂ) (A : Matrix ι ι ℂ) :
    conjMap U (multMap k (fun x => ∑ n ∈ s, c n * (x:ℂ)^n) (conjMap Uᴴ A))
      = conjMap U' (multMap k' (fun x => ∑ n ∈ s, c n * (x:ℂ)^n) (conjMap U'ᴴ A)) := by
  rw [modularFilter_polynomial_eq_adMap k U hUU hU'U,
    modularFilter_polynomial_eq_adMap k' U' hVV hV'V, hK]

/-! ### The Hermitian modular filter, via Mathlib's spectral theorem -/

/-- The modular filter of a Hermitian matrix `K`, defined through the orthonormal eigenbasis
of Mathlib's spectral theorem. -/
noncomputable def spectralFilter (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (f : ℝ → ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  (conjMap (hK.eigenvectorUnitary : Matrix ι ι ℂ)).comp
    ((multMap hK.eigenvalues f).comp (conjMap ((hK.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ)))

/-- The spectral theorem supplies the unitary factorization of a Hermitian matrix. -/
theorem spectral_factorization (K : Matrix ι ι ℂ) (hK : K.IsHermitian) :
    mmul (mmul (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        (Matrix.diagonal (fun i => (hK.eigenvalues i : ℂ))))
        ((hK.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) = K := by
  have h1 : Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hK.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hK.eigenvalues))
      = mmul (mmul (hK.eigenvectorUnitary : Matrix ι ι ℂ)
          (Matrix.diagonal (RCLike.ofReal ∘ hK.eigenvalues)))
          ((hK.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) := by
    simp only [mmul, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rw [show Matrix.diagonal (fun i => (hK.eigenvalues i : ℂ))
      = Matrix.diagonal (RCLike.ofReal ∘ hK.eigenvalues) from rfl]
  exact (hK.spectral_theorem.trans h1).symm

/-- The eigenvector unitary is unitary, left form. -/
theorem eigenvectorUnitary_mul (K : Matrix ι ι ℂ) (hK : K.IsHermitian) :
    (hK.eigenvectorUnitary : Matrix ι ι ℂ) * ((hK.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) = 1 := by
  have h := hK.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using h

/-- The eigenvector unitary is unitary, right form. -/
theorem eigenvectorUnitary_mul' (K : Matrix ι ι ℂ) (hK : K.IsHermitian) :
    ((hK.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) * (hK.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
  have h := hK.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h

/-- **Complete positivity of the Hermitian modular filter**, for every symbol with
positive semidefinite difference kernel. -/
theorem isCP_spectralFilter (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (f : ℝ → ℂ)
    (hPD : (Kmat hK.eigenvalues f).PosSemidef) : IsCP (spectralFilter K hK f) :=
  isCP_changeOfBasis' hK.eigenvalues f hPD _

/-- **Unitality and trace preservation of the Hermitian modular filter**. -/
theorem spectralFilter_unital_trace (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (f : ℝ → ℂ)
    (hf0 : f 0 = 1) :
    spectralFilter K hK f 1 = 1 ∧ ∀ A : Matrix ι ι ℂ,
      (spectralFilter K hK f A).trace = A.trace :=
  changeOfBasis_unital_trace hK.eigenvalues f hf0 _
    (eigenvectorUnitary_mul K hK) (eigenvectorUnitary_mul' K hK)

/-- **`Φ_K = f(ad_K)` on polynomial symbols, for every Hermitian `K`.** -/
theorem spectralFilter_polynomial_eq_adMap (K : Matrix ι ι ℂ) (hK : K.IsHermitian)
    (s : Finset ℕ) (c : ℕ → ℂ) (A : Matrix ι ι ℂ) :
    spectralFilter K hK (fun x => ∑ n ∈ s, c n * (x:ℂ)^n) A
      = ∑ n ∈ s, c n • (((adMap K)^n) A) := by
  have hfac := spectral_factorization K hK
  have h := modularFilter_polynomial_eq_adMap hK.eigenvalues
    (hK.eigenvectorUnitary : Matrix ι ι ℂ) (eigenvectorUnitary_mul K hK)
    (eigenvectorUnitary_mul' K hK) s c A
  have hL : spectralFilter K hK (fun x => ∑ n ∈ s, c n * (x:ℂ)^n) A
      = conjMap (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        (multMap hK.eigenvalues (fun x => ∑ n ∈ s, c n * (x:ℂ)^n)
          (conjMap ((hK.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) A)) := rfl
  rw [hL, h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hfac]

end Commutator

/-! ## 4. The report's claims for the actual filter: unital, trace preserving, CP, HS self-adjoint -/

section Bundles

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The report's hyperbolic modular symbol `x ↦ x / sinh x`, with value `1` at `0`. -/
noncomputable def sinhcSym : ℝ → ℂ :=
  fun x => if x = 0 then 1 else ((x : ℝ) : ℂ) / (Real.sinh x : ℂ)

/-- Real `τ`-th power of the hyperbolic modular symbol. -/
noncomputable def sinhcSymRpow (tau : ℝ) : ℝ → ℂ :=
  fun x => Complex.ofReal (((if x = 0 then 1 else x / Real.sinh x) ^ tau))

lemma sinhc_real (x : ℝ) :
    star (sinhcSym x) = sinhcSym x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sinhcSym]
  · simp only [sinhcSym, if_neg hx]
    rw [star_div₀,
      show star ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) from Complex.conj_ofReal x,
      show star (((Real.sinh x : ℝ)) : ℂ) = ((Real.sinh x : ℝ) : ℂ) from Complex.conj_ofReal _]

lemma sinhc_even (x : ℝ) :
    sinhcSym (-x) = sinhcSym x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sinhcSym]
  · simp only [sinhcSym, if_neg hx, if_neg (neg_ne_zero.mpr hx), Real.sinh_neg]
    push_cast
    ring

lemma sinhcSym_zero : sinhcSym 0 = 1 := by simp [sinhcSym]

/-- The full bundle for the report's filter `Φ_K = ad_K / sinh ad_K`: unital,
trace preserving, completely positive, Hilbert–Schmidt self-adjoint, positivity preserving. -/
theorem bundle_sinhc (k : ι → ℝ) :
    multMap k sinhcSym 1 = 1 ∧
      (∀ A : Matrix ι ι ℂ, (multMap k sinhcSym A).trace = A.trace) ∧
      IsCP (multMap k sinhcSym) ∧
      (∀ A B : Matrix ι ι ℂ,
        ((multMap k sinhcSym A)ᴴ * B).trace = (Aᴴ * multMap k sinhcSym B).trace) ∧
      (∀ A : Matrix ι ι ℂ, A.PosSemidef → (multMap k sinhcSym A).PosSemidef) :=
  unital_CP_trace_bundle k sinhcSym sinhcSym_zero sinhc_real sinhc_even
    (posSemidef_sinhc_uncond k)

lemma sinhcSymRpow_zero (tau : ℝ) : sinhcSymRpow tau 0 = 1 := by
  simp [sinhcSymRpow]

lemma sinhcSymRpow_real (tau : ℝ) (x : ℝ) :
    star (sinhcSymRpow tau x) = sinhcSymRpow tau x := by
  simp [sinhcSymRpow]

lemma sinhcSymRpow_even (tau : ℝ) (x : ℝ) :
    sinhcSymRpow tau (-x) = sinhcSymRpow tau x := by
  have h : (if -x = 0 then 1 else -x / Real.sinh (-x))
      = (if x = 0 then 1 else x / Real.sinh x) := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [if_neg hx, if_neg (neg_ne_zero.mpr hx), Real.sinh_neg]
      field_simp
  simp only [sinhcSymRpow, h]

/-- The full bundle for every real power `Φ_K^τ`, `τ > 0`. -/
theorem bundle_sinhc_rpow (k : ι → ℝ) {tau : ℝ} (htau : 0 < tau) :
    multMap k (sinhcSymRpow tau) 1 = 1 ∧
      (∀ A : Matrix ι ι ℂ, (multMap k (sinhcSymRpow tau) A).trace = A.trace) ∧
      IsCP (multMap k (sinhcSymRpow tau)) ∧
      (∀ A B : Matrix ι ι ℂ,
        ((multMap k (sinhcSymRpow tau) A)ᴴ * B).trace =
          (Aᴴ * multMap k (sinhcSymRpow tau) B).trace) ∧
      (∀ A : Matrix ι ι ℂ, A.PosSemidef → (multMap k (sinhcSymRpow tau) A).PosSemidef) :=
  unital_CP_trace_bundle k (sinhcSymRpow tau) (sinhcSymRpow_zero tau)
    (sinhcSymRpow_real tau) (sinhcSymRpow_even tau)
    (posSemidef_sinhc_rpow_uncond k htau)

/-- The `τ`-th power symbol of a finite product of resolvent factors. -/
noncomputable def prodResolventSym (s : Finset ℝ) (tau : ℝ) : ℝ → ℂ :=
  fun x => ∏ lam ∈ s, Complex.ofReal ((((1 : ℝ) + x ^ 2 / lam)⁻¹) ^ tau)

lemma prodResolventSym_zero (s : Finset ℝ) (tau : ℝ) :
    prodResolventSym s tau 0 = 1 := by
  simp [prodResolventSym]

lemma prodResolventSym_real (s : Finset ℝ) (tau : ℝ) (x : ℝ) :
    star (prodResolventSym s tau x) = prodResolventSym s tau x := by
  simp [prodResolventSym]

lemma prodResolventSym_even (s : Finset ℝ) (tau : ℝ) (x : ℝ) :
    prodResolventSym s tau (-x) = prodResolventSym s tau x := by
  simp only [prodResolventSym, neg_sq]

/-- **Every finite product is unital CP**: the report's truncated filter
`Φ^τ_{K,R} = ∏_{λ∈s}(I + ad_K²/λ)^{-τ}` is unital, trace preserving, CP, HS self-adjoint. -/
theorem bundle_prod_resolvent_rpow (k : ι → ℝ) (s : Finset ℝ) (hs : ∀ lam ∈ s, 0 < lam)
    {tau : ℝ} (htau : 0 < tau) :
    multMap k (prodResolventSym s tau) 1 = 1 ∧
      (∀ A : Matrix ι ι ℂ, (multMap k (prodResolventSym s tau) A).trace = A.trace) ∧
      IsCP (multMap k (prodResolventSym s tau)) ∧
      (∀ A B : Matrix ι ι ℂ,
        ((multMap k (prodResolventSym s tau) A)ᴴ * B).trace =
          (Aᴴ * multMap k (prodResolventSym s tau) B).trace) ∧
      (∀ A : Matrix ι ι ℂ, A.PosSemidef → (multMap k (prodResolventSym s tau) A).PosSemidef) :=
  unital_CP_trace_bundle k (prodResolventSym s tau) (prodResolventSym_zero s tau)
    (prodResolventSym_real s tau) (prodResolventSym_even s tau)
    (posSemidef_prod_resolvent_rpow k s hs htau)

/-- **The report's truncated filter** `Φ^τ_{K,R} = ∏_{j=1}^{R}(I + ad_K²/(π²j²))^{-τ}`
(`lamSet R = {(πj)² : 1 ≤ j ≤ R}`) is unital, trace preserving, CP and HS self-adjoint. -/
theorem bundle_sinhc_truncated (k : ι → ℝ) (R : ℕ) {tau : ℝ} (htau : 0 < tau) :
    multMap k (prodResolventSym (lamSet R) tau) 1 = 1 ∧
      (∀ A : Matrix ι ι ℂ, (multMap k (prodResolventSym (lamSet R) tau) A).trace = A.trace) ∧
      IsCP (multMap k (prodResolventSym (lamSet R) tau)) ∧
      (∀ A B : Matrix ι ι ℂ,
        ((multMap k (prodResolventSym (lamSet R) tau) A)ᴴ * B).trace =
          (Aᴴ * multMap k (prodResolventSym (lamSet R) tau) B).trace) ∧
      (∀ A : Matrix ι ι ℂ,
        A.PosSemidef → (multMap k (prodResolventSym (lamSet R) tau) A).PosSemidef) :=
  bundle_prod_resolvent_rpow k (lamSet R) (fun _ h => lamSet_pos h) htau

end Bundles

end MomentGeometry.Operator.CP

/-! ## Axiom audit -/

#print axioms MomentGeometry.Operator.CP.sinhc_factor
#print axioms MomentGeometry.Operator.CP.prod_factor
#print axioms MomentGeometry.Operator.CP.tendsto_prod_complex
#print axioms MomentGeometry.Operator.CP.tendsto_prod_real
#print axioms MomentGeometry.Operator.CP.tendsto_prod_inv_real
#print axioms MomentGeometry.Operator.CP.tendsto_prod_rpow_real
#print axioms MomentGeometry.Operator.CP.tendsto_sinhc_prod
#print axioms MomentGeometry.Operator.CP.tendsto_sinhc_prod_rpow
#print axioms MomentGeometry.Operator.CP.prod_ofReal
#print axioms MomentGeometry.Operator.CP.prod_Icc_one_eq_range
#print axioms MomentGeometry.Operator.CP.prod_lamSet_eq
#print axioms MomentGeometry.Operator.CP.euler_sinhc
#print axioms MomentGeometry.Operator.CP.euler_sinhc_rpow
#print axioms MomentGeometry.Operator.CP.posSemidef_sinhc_uncond
#print axioms MomentGeometry.Operator.CP.isCP_sinhc_uncond
#print axioms MomentGeometry.Operator.CP.posSemidef_sinhc_pow_uncond
#print axioms MomentGeometry.Operator.CP.posSemidef_sinhc_rpow_uncond
#print axioms MomentGeometry.Operator.CP.isCP_sinhc_rpow_uncond
#print axioms MomentGeometry.Operator.CP.isCP_sinhc_rpow_zero
#print axioms MomentGeometry.Operator.CP.mmul_apply
#print axioms MomentGeometry.Operator.CP.Tmat_mul_apply
#print axioms MomentGeometry.Operator.CP.Tmat_conjTranspose_apply
#print axioms MomentGeometry.Operator.CP.Tmat_sandwich_apply
#print axioms MomentGeometry.Operator.CP.sandwich_apply
#print axioms MomentGeometry.Operator.CP.amp_conjMap_apply
#print axioms MomentGeometry.Operator.CP.amp_conjMap
#print axioms MomentGeometry.Operator.CP.isCP_conjMap
#print axioms MomentGeometry.Operator.CP.isCP_changeOfBasis'

/-! ## Axiom audit: commutator functional calculus -/

#print axioms MomentGeometry.Operator.CP.adMap
#print axioms MomentGeometry.Operator.CP.adMap_apply
#print axioms MomentGeometry.Operator.CP.diagonal_mul_apply
#print axioms MomentGeometry.Operator.CP.mul_diagonal_apply
#print axioms MomentGeometry.Operator.CP.adMap_diagonal_apply
#print axioms MomentGeometry.Operator.CP.multMap_eq_adMap_diagonal
#print axioms MomentGeometry.Operator.CP.multMap_pow_eq_adMap_pow
#print axioms MomentGeometry.Operator.CP.multMap_add
#print axioms MomentGeometry.Operator.CP.multMap_smul
#print axioms MomentGeometry.Operator.CP.multMap_polynomial
#print axioms MomentGeometry.Operator.CP.sandwich_mul
#print axioms MomentGeometry.Operator.CP.conjMap_adMap
#print axioms MomentGeometry.Operator.CP.conjMap_conjMap
#print axioms MomentGeometry.Operator.CP.conjMap_adMap_pow
#print axioms MomentGeometry.Operator.CP.modularFilter_polynomial_eq_adMap
#print axioms MomentGeometry.Operator.CP.modularFilter_polynomial_wellDefined
#print axioms MomentGeometry.Operator.CP.spectralFilter
#print axioms MomentGeometry.Operator.CP.spectral_factorization
#print axioms MomentGeometry.Operator.CP.eigenvectorUnitary_mul
#print axioms MomentGeometry.Operator.CP.eigenvectorUnitary_mul'
#print axioms MomentGeometry.Operator.CP.isCP_spectralFilter
#print axioms MomentGeometry.Operator.CP.spectralFilter_unital_trace
#print axioms MomentGeometry.Operator.CP.spectralFilter_polynomial_eq_adMap
#print axioms MomentGeometry.Operator.CP.sinhc_real
#print axioms MomentGeometry.Operator.CP.sinhc_even
#print axioms MomentGeometry.Operator.CP.bundle_sinhc
#print axioms MomentGeometry.Operator.CP.bundle_sinhc_rpow
#print axioms MomentGeometry.Operator.CP.bundle_prod_resolvent_rpow
#print axioms MomentGeometry.Operator.CP.bundle_sinhc_truncated
