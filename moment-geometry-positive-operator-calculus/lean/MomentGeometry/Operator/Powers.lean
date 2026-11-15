/-
Fractional-power response `q:thm-powers` at the matrix level (component module).

Source: `results/moment_geometry/Moment_Geometry/proofs/quantum_results.tex`,
Theorem `q:thm-powers` (Positive modular response calculus).

What is *proved* here:

* the hyperbolic response symbols `psiR`, `chiR` (the paper's `ψ_r`, `χ_r`), the
  divided-difference symbol `PhiR` of the exponential integral, its Hermitian
  and anti-Hermitian pieces `PsiR`, `AR`, the modular symbol `fR x = x / sinh x`
  and `tanhHalf x = tanh (x/2)`, with their exact scalar identities;
* the matrix-level splitting of the divided-difference response into
  Hermitian and anti-Hermitian parts (`response_split`, `response_isHermitian`,
  `response_isAnti`), using the spectral (eigenbasis) presentation `k : ι → ℝ`
  of a Hermitian `K` — the same presentation as the verified
  `MomentGeometry.Operator.CP.{Base,Closure}` modules;
* the reduction of the Hermitian part to `ψ_r(ad_K) H` and of the
  anti-Hermitian part to `χ_r(ad_K) A` where `H`, `A` are the Hermitian and
  anti-Hermitian parts of the *base* response `r = 1`, including the KMS
  compatibility `A = tanh(ad_K/2) H` that makes this reduction possible
  (`response_hermitian`, `response_anti`, `baseA_eq_kms`);
* endpoint values `r = 0`, `r = 1`, and the `r ↓ 0` logarithmic-response limit
  at the level of symbols and of matrix entries (`tendsto_*`, `limit_*`);
* complete positivity of both response maps together with the mass/ancilla
  bounds: `Φ_r(1) = r • 1`, `Φ^χ_r(1) = r² • 1`, and, in *every* amplification
  and for every `0 ≤ A ≤ 1`, `0 ≤ (Φ ⊗ id)(A) ≤ r • 1` (resp. `r² • 1`).

What is *not* proved here (explicitly separated, never hidden):

* `ResponseModel`: the identification of the divided-difference response
  `(exp (r ad_K) - 1)/ad_K K̇` with the actual derivative `(∂_λ ρ^r) ρ^{-r}`
  along a positive matrix path. The source proof obtains it by differentiating
  the exponential (`Q_r = ∫_0^r e^{sK} K̇ e^{-sK} ds`, Duhamel). This is stated
  below as a named `Prop` interface, never as a proved theorem;
* `FourierDensity r`: the source's explicit positive density
  `p_r(t) = sin(πr) / (2 (cosh(πt) + cos(πr)))` with
  `ψ_r(x) = ∫ p_r(t) e^{itx} dt` and `∫ p_r = r` (a contour-integral
  evaluation). Its *consequences* — positive semidefiniteness of the kernel
  `(i,j) ↦ ψ_r(k_i - k_j)`, complete positivity, the masses and the ancilla
  bounds — are proved here as theorems with the kernel positivity as an
  explicit hypothesis, exactly as the verified `isCP_spectralFilter` interface
  in `CP/Closure` does.
-/
import MomentGeometry.Operator.CP.Closure

open Matrix Complex Filter
open scoped ComplexOrder BigOperators Topology

set_option maxHeartbeats 1000000

namespace MomentGeometry.Operator.Powers

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ## 1. The hyperbolic response symbols (scalar level) -/

/-- Hermitian response symbol `ψ_r(x) = sinh (r x) / sinh x`, continuous value `r` at `x = 0`. -/
noncomputable def psiR (r x : ℝ) : ℝ :=
  if x = 0 then r else Real.sinh (r * x) / Real.sinh x

/-- Anti-Hermitian response symbol `χ_r(x) = (sinh (r x / 2) / sinh (x / 2)) ^ 2`,
continuous value `r ^ 2` at `x = 0`. -/
noncomputable def chiR (r x : ℝ) : ℝ :=
  if x = 0 then r ^ 2 else (Real.sinh (r * x / 2) / Real.sinh (x / 2)) ^ 2

/-- Divided-difference (exponential integral) response symbol `Φ_r(x) = (e^{r x} - 1) / x`,
continuous value `r` at `x = 0`. -/
noncomputable def PhiR (r x : ℝ) : ℝ :=
  if x = 0 then r else (Real.exp (r * x) - 1) / x

/-- Hermitian part of `Φ_r`: `Ψ_r(x) = sinh (r x) / x`, value `r` at `0`. -/
noncomputable def PsiR (r x : ℝ) : ℝ :=
  if x = 0 then r else Real.sinh (r * x) / x

/-- Anti-Hermitian part of `Φ_r`: `A_r(x) = (cosh (r x) - 1) / x`, value `0` at `0`. -/
noncomputable def AR (r x : ℝ) : ℝ :=
  if x = 0 then 0 else (Real.cosh (r * x) - 1) / x

/-- The modular symbol `f(x) = x / sinh x`, value `1` at `0`. -/
noncomputable def fR (x : ℝ) : ℝ :=
  if x = 0 then 1 else x / Real.sinh x

/-- `tanh (x / 2)`, the `r = 1` anti-Hermitian symbol. -/
noncomputable def tanhHalf (x : ℝ) : ℝ :=
  Real.tanh (x / 2)

@[simp] theorem psiR_zero_pt (r : ℝ) : psiR r 0 = r := by simp [psiR]

@[simp] theorem chiR_zero_pt (r : ℝ) : chiR r 0 = r ^ 2 := by simp [chiR]

@[simp] theorem PhiR_zero_pt (r : ℝ) : PhiR r 0 = r := by simp [PhiR]

@[simp] theorem PsiR_zero_pt (r : ℝ) : PsiR r 0 = r := by simp [PsiR]

@[simp] theorem AR_zero_pt (r : ℝ) : AR r 0 = 0 := by simp [AR]

@[simp] theorem fR_zero : fR 0 = 1 := by simp [fR]

/-- The divided-difference symbol splits into its Hermitian and anti-Hermitian
pieces: `Φ_r = Ψ_r + A_r`. This is the scalar content of "taking Hermitian and
anti-Hermitian parts" in the source proof. -/
theorem PhiR_split (r x : ℝ) : PhiR r x = PsiR r x + AR r x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hexp : Real.exp (r * x) = Real.cosh (r * x) + Real.sinh (r * x) :=
      (Real.cosh_add_sinh (r * x)).symm
    simp only [PhiR, PsiR, AR, hx, if_false]
    rw [hexp]
    field_simp
    ring

/-- Recovering `Φ_r`'s Hermitian symbol from the modular symbol:
`Ψ_r(x) f(x) = ψ_r(x)`. -/
theorem PsiR_mul_fR (r x : ℝ) : PsiR r x * fR x = psiR r x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
    simp only [PsiR, fR, psiR, hx, if_false]
    field_simp

/-- The KMS substitution identity for the anti-Hermitian part:
`χ_r(x) tanh (x/2) = A_r(x) f(x)`, i.e. the anti-Hermitian response of the
modular generator is fully determined by the Hermitian one. -/
theorem chiR_mul_tanhHalf (r x : ℝ) : chiR r x * tanhHalf x = AR r x * fR x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [tanhHalf, chiR, AR, fR]
  · have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
    have hy : x / 2 ≠ 0 := by intro h; exact hx (by linarith)
    have hsh : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr hy
    have hch : Real.cosh (x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    -- `sinh x = 2 sinh (x/2) cosh (x/2)` and `cosh y - 1 = 2 sinh (y/2)^2`
    have hS : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
      calc Real.sinh x = Real.sinh (2 * (x / 2)) := by ring_nf
        _ = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := Real.sinh_two_mul _
    have hC : ∀ y : ℝ, Real.cosh y - 1 = 2 * Real.sinh (y / 2) ^ 2 := by
      intro y
      calc Real.cosh y - 1 = Real.cosh (2 * (y / 2)) - 1 := by ring_nf
        _ = (Real.cosh (y / 2) ^ 2 + Real.sinh (y / 2) ^ 2) - 1 := by
          rw [Real.cosh_two_mul]
        _ = 2 * Real.sinh (y / 2) ^ 2 := by
          have h := Real.cosh_sq_sub_sinh_sq (y / 2)
          nlinarith
    simp only [chiR, AR, fR, tanhHalf, hx, if_false, Real.tanh_eq_sinh_div_cosh]
    rw [hS, hC (r * x)]
    have harg : r * x / 2 = r * (x / 2) := by ring
    rw [harg]
    field_simp

/-- The anti-Hermitian base symbol is reproduced at `r = 1` from the exponent
`r`: `χ_r(x) A_1(x) = A_r(x)`. This is the identity that converts the
`r = 1` anti-Hermitian part into the `r`-anti-Hermitian part. -/
theorem chiR_mul_AR_one (r x : ℝ) : chiR r x * AR 1 x = AR r x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx2 : x / 2 ≠ 0 := by intro h; exact hx (by linarith)
    have hsh : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr hx2
    have hC : ∀ y : ℝ, Real.cosh y - 1 = 2 * Real.sinh (y / 2) ^ 2 := by
      intro y
      calc Real.cosh y - 1 = Real.cosh (2 * (y / 2)) - 1 := by ring_nf
        _ = (Real.cosh (y / 2) ^ 2 + Real.sinh (y / 2) ^ 2) - 1 := by
          rw [Real.cosh_two_mul]
        _ = 2 * Real.sinh (y / 2) ^ 2 := by
          have h := Real.cosh_sq_sub_sinh_sq (y / 2)
          nlinarith
    have harg : r * x / 2 = r * (x / 2) := by ring
    simp only [chiR, AR, hx, if_false, one_mul, harg]
    rw [hC, hC]
    field_simp

/-- `f` inverts `Ψ_1`: `f(x) Ψ_1(x) = 1`. -/
theorem fR_mul_PsiR_one (x : ℝ) : fR x * PsiR 1 x = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
    simp only [fR, PsiR, hx, if_false, one_mul]
    field_simp

/-- The base Hermitian symbol squared against `Ψ_1`:
`ψ_r(x) Ψ_1(x) = Ψ_r(x)`. -/
theorem psiR_mul_PsiR_one (r x : ℝ) : psiR r x * PsiR 1 x = PsiR r x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
    simp only [psiR, PsiR, hx, if_false, one_mul]
    field_simp

/-- `χ_r = ψ_r(·/2) ^ 2`: the anti-Hermitian symbol is the square of the
half-argument Hermitian symbol. This is the source's
`χ_r(x) = ψ_r(x/2)^2`, and it is what makes `χ_r` a complete square of a
completely positive map (hence CP with mass `r^2`). -/
theorem chiR_eq_psiR_half_sq (r x : ℝ) : chiR r x = psiR r (x / 2) * psiR r (x / 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sq]
  · have hy : x / 2 ≠ 0 := by intro h; exact hx (by linarith)
    simp only [chiR, psiR, hx, hy, if_false]
    ring_nf

/-- `ψ_r` is even. -/
theorem psiR_even (r x : ℝ) : psiR r (-x) = psiR r x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : -x ≠ 0 := neg_ne_zero.mpr hx
    have h2 : r * -x = -(r * x) := by ring
    simp only [psiR, h, hx, if_false, h2, Real.sinh_neg, neg_div_neg_eq]

/-- `A_r` is odd. -/
theorem AR_odd (r x : ℝ) : AR r (-x) = -AR r x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : -x ≠ 0 := neg_ne_zero.mpr hx
    have h2 : r * -x = -(r * x) := by ring
    simp only [AR, h, hx, if_false, h2, Real.cosh_neg]
    ring

/-- `Ψ_r` is even. -/
theorem PsiR_even (r x : ℝ) : PsiR r (-x) = PsiR r x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : -x ≠ 0 := neg_ne_zero.mpr hx
    have h2 : r * -x = -(r * x) := by ring
    simp only [PsiR, h, hx, if_false, h2, Real.sinh_neg, neg_div_neg_eq]

/-! ### Endpoint values of the symbols -/

/-- `ψ_0 = 0`: the zero response. -/
theorem psiR_zero_r (x : ℝ) : psiR 0 x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp only [psiR, hx, if_false, zero_mul, Real.sinh_zero, zero_div]

/-- `ψ_1 = 1`: the base Hermitian response is the identity filter. -/
theorem psiR_one (x : ℝ) : psiR 1 x = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
    simp only [psiR, hx, if_false, one_mul]
    exact div_self hs

/-- `χ_0 = 0`. -/
theorem chiR_zero_r (x : ℝ) : chiR 0 x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp only [chiR, hx, if_false, zero_mul, Real.sinh_zero, zero_div]
    ring

/-- `χ_1 = 1`: the base anti-Hermitian response is the identity filter, as it must
be since `A_1 = A` (the anti-Hermitian part is reproduced at `r = 1`). -/
theorem chiR_one (x : ℝ) : chiR 1 x = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hy : x / 2 ≠ 0 := by intro h; exact hx (by linarith)
    have hsh : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr hy
    simp only [chiR, hx, if_false, one_mul]
    field_simp

/-- The KMS compatibility of the *base* response: `A_1 = tanh (·/2) Ψ_1`, i.e.
`(cosh x - 1)/x = tanh (x/2) (sinh x / x)`. -/
theorem AR_one_eq_tanhHalf_mul (x : ℝ) : AR 1 x = tanhHalf x * PsiR 1 x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [tanhHalf]
  · have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
    have hx2 : x / 2 ≠ 0 := by intro h; exact hx (by linarith)
    have hsh : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr hx2
    have hch : Real.cosh (x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    have hS : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
      calc Real.sinh x = Real.sinh (2 * (x / 2)) := by ring_nf
        _ = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := Real.sinh_two_mul _
    have hC : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
      calc Real.cosh x - 1 = Real.cosh (2 * (x / 2)) - 1 := by ring_nf
        _ = (Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2) - 1 := by
          rw [Real.cosh_two_mul]
        _ = 2 * Real.sinh (x / 2) ^ 2 := by
          have h := Real.cosh_sq_sub_sinh_sq (x / 2)
          nlinarith
    -- reduce to `cosh x - 1 = tanh (x/2) * sinh x`
    have key : Real.cosh x - 1 = Real.tanh (x / 2) * Real.sinh x := by
      rw [Real.tanh_eq_sinh_div_cosh, hS, hC]
      field_simp
    simp only [AR, PsiR, tanhHalf, hx, if_false, one_mul]
    rw [key]
    ring

/-! ### Coherent composition of the fractional-power symbols -/

/-- `ψ_s(r x) ψ_r(x) = ψ_{rs}(x)`: the fractional-power Hermitian responses
compose coherently, as the source states after the proof of `q:thm-powers`. -/
theorem psiR_composition (r s x : ℝ) : psiR s (r * x) * psiR r x = psiR (r * s) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [mul_comm]
  rcases eq_or_ne r 0 with rfl | hr
  · simp [psiR_zero_r]
  rcases eq_or_ne s 0 with rfl | hs
  · simp [psiR_zero_r]
  have hrx : r * x ≠ 0 := mul_ne_zero hr hx
  have hsrx : s * (r * x) ≠ 0 := mul_ne_zero hs hrx
  have hrs : r * s ≠ 0 := mul_ne_zero hr hs
  have hsx : (r * s) * x ≠ 0 := mul_ne_zero hrs hx
  simp only [psiR, hx, hrx, hsrx, hsx, if_false]
  rw [show s * (r * x) = (r * s) * x by ring]
  field_simp

/-- `χ_s(r x) χ_r(x) = χ_{rs}(x)`: the anti-Hermitian responses compose
coherently as well (it follows from `χ_r = ψ_r(·/2)²` and `ψ` composition). -/
theorem chiR_composition (r s x : ℝ) : chiR s (r * x) * chiR r x = chiR (r * s) x := by
  simp only [chiR_eq_psiR_half_sq]
  rw [show r * x / 2 = r * (x / 2) by ring]
  rw [← psiR_composition r s (x / 2)]
  ring

/-! ## 2. Complex symbols and the multiplier maps -/

/-- Complexified Hermitian response symbol. -/
noncomputable def psiSym (r : ℝ) : ℝ → ℂ := fun x => (psiR r x : ℂ)

/-- Complexified anti-Hermitian response symbol. -/
noncomputable def chiSym (r : ℝ) : ℝ → ℂ := fun x => (chiR r x : ℂ)

/-- Complexified divided-difference response symbol. -/
noncomputable def PhiSym (r : ℝ) : ℝ → ℂ := fun x => (PhiR r x : ℂ)

/-- Complexified Hermitian piece of the divided difference. -/
noncomputable def PsiSym (r : ℝ) : ℝ → ℂ := fun x => (PsiR r x : ℂ)

/-- Complexified anti-Hermitian piece of the divided difference. -/
noncomputable def ASym (r : ℝ) : ℝ → ℂ := fun x => (AR r x : ℂ)

/-- Complexified modular symbol `x / sinh x`. -/
noncomputable def fSym : ℝ → ℂ := fun x => (fR x : ℂ)

/-- Complexified `tanh (x/2)`. -/
noncomputable def tanhHalfSym : ℝ → ℂ := fun x => (tanhHalf x : ℂ)

@[simp] theorem psiSym_apply (r x : ℝ) : psiSym r x = (psiR r x : ℂ) := rfl
@[simp] theorem chiSym_apply (r x : ℝ) : chiSym r x = (chiR r x : ℂ) := rfl
@[simp] theorem PhiSym_apply (r x : ℝ) : PhiSym r x = (PhiR r x : ℂ) := rfl
@[simp] theorem PsiSym_apply (r x : ℝ) : PsiSym r x = (PsiR r x : ℂ) := rfl
@[simp] theorem ASym_apply (r x : ℝ) : ASym r x = (AR r x : ℂ) := rfl
@[simp] theorem fSym_apply (x : ℝ) : fSym x = (fR x : ℂ) := rfl
@[simp] theorem tanhHalfSym_apply (x : ℝ) : tanhHalfSym x = (tanhHalf x : ℂ) := rfl

/-- Real-valuedness of the Hermitian response symbol. -/
theorem star_psiSym (r x : ℝ) : star (psiSym r x) = psiSym r x := Complex.conj_ofReal _

theorem star_chiSym (r x : ℝ) : star (chiSym r x) = chiSym r x := Complex.conj_ofReal _

theorem star_PsiSym (r x : ℝ) : star (PsiSym r x) = PsiSym r x := Complex.conj_ofReal _

/-! ## 3. Matrix level: the Hermitian/anti-Hermitian splitting -/

open MomentGeometry.Operator.CP

/-- Conjugate transpose of a difference multiplier. -/
theorem conjTranspose_multMap (k : ι → ℝ) (g : ℝ → ℂ) (X : Matrix ι ι ℂ) :
    (multMap k g X)ᴴ = multMap k (fun x => star (g (-x))) Xᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, multMap_apply, multMap_apply, Matrix.conjTranspose_apply]
  have h : k i - k j = -(k j - k i) := by ring
  rw [h, star_mul, neg_neg, mul_comm]

/-- Real, even symbols produce Hermitian multipliers of Hermitian matrices. -/
theorem isHermitian_multMap_of_even (k : ι → ℝ) (g : ℝ → ℂ)
    (heven : ∀ x, g (-x) = g x) (hreal : ∀ x, star (g x) = g x)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) : (multMap k g X).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_multMap, hX]
  have h : (fun x => star (g (-x))) = g := by
    funext x; rw [heven, hreal]
  rw [h]

/-- Real, odd symbols produce anti-Hermitian multipliers of Hermitian matrices. -/
theorem isAntiHermitian_multMap_of_odd (k : ι → ℝ) (g : ℝ → ℂ)
    (hodd : ∀ x, g (-x) = -g x) (hreal : ∀ x, star (g x) = g x)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    (multMap k g X)ᴴ = - multMap k g X := by
  rw [conjTranspose_multMap, hX]
  have h : (fun x => star (g (-x))) = fun x => - g x := by
    funext x; rw [hodd, star_neg, hreal]
  rw [h]
  ext i j
  simp [multMap_apply]

/-- The divided-difference response splits into Hermitian and anti-Hermitian parts. -/
theorem response_split (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) (r : ℝ) :
    multMap k (PhiSym r) Kdot
      = multMap k (PsiSym r) Kdot + multMap k (ASym r) Kdot := by
  have h : PhiSym r = PsiSym r + ASym r := by
    funext x
    simp only [PhiSym_apply, PsiSym_apply, ASym_apply, Pi.add_apply]
    rw [← Complex.ofReal_add, PhiR_split]
  rw [h, multMap_add]
  rfl

/-- The Hermitian part of the response is Hermitian. -/
theorem response_isHermitian (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) (hK : Kdot.IsHermitian)
    (r : ℝ) : (multMap k (PsiSym r) Kdot).IsHermitian :=
  isHermitian_multMap_of_even k _
    (fun x => by simp only [PsiSym_apply, PsiR_even r x]) (fun x => Complex.conj_ofReal _)
    Kdot hK

/-- The anti-Hermitian part of the response is anti-Hermitian. -/
theorem response_isAnti (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) (hK : Kdot.IsHermitian)
    (r : ℝ) : (multMap k (ASym r) Kdot)ᴴ = - multMap k (ASym r) Kdot :=
  isAntiHermitian_multMap_of_odd k _
    (fun x => by simp [ASym_apply, AR_odd r x]) (fun x => Complex.conj_ofReal _)
    Kdot hK

/-! ## 4. Reduction to `ψ_r (ad_K) H` and `χ_r (ad_K) A` -/

/-- The base Hermitian response `H = Ψ_1(ad_K) K̇`. -/
noncomputable def baseH (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  multMap k (PsiSym 1) Kdot

/-- The base anti-Hermitian response `A = A_1(ad_K) K̇`. -/
noncomputable def baseA (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  multMap k (ASym 1) Kdot

/-- Recovering the generator from the base Hermitian response: `K̇ = f(ad_K) H`,
i.e. `H = (sinh ad_K / ad_K) K̇` inverts to `K̇ = f(ad_K) H`. -/
theorem base_recovery (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) :
    multMap k fSym (baseH k Kdot) = Kdot := by
  unfold baseH
  rw [← LinearMap.comp_apply, multMap_comp]
  have h : (fun x => fSym x * PsiSym 1 x) = fun _ => (1 : ℂ) := by
    funext x
    simp only [fSym_apply, PsiSym_apply, ← Complex.ofReal_mul, fR_mul_PsiR_one,
      Complex.ofReal_one]
  rw [h, multMap_one]
  rfl

/-- **KMS compatibility** at the matrix level: the anti-Hermitian part of the
base response is `tanh (ad_K / 2)` of its Hermitian part,
`A = tanh (ad_K / 2) H`. -/
theorem baseA_eq_kms (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) :
    baseA k Kdot = multMap k tanhHalfSym (baseH k Kdot) := by
  unfold baseA baseH
  rw [← LinearMap.comp_apply, multMap_comp]
  rw [show (fun x => tanhHalfSym x * PsiSym 1 x) = ASym 1 from by
    funext x
    simp only [ASym_apply, tanhHalfSym_apply, PsiSym_apply, ← Complex.ofReal_mul,
      ← AR_one_eq_tanhHalf_mul x]]

/-- **Hermitian part of the `r`-response**: `Ψ_r(ad_K) K̇ = ψ_r(ad_K) H`. -/
theorem response_hermitian (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) (r : ℝ) :
    multMap k (PsiSym r) Kdot = multMap k (psiSym r) (baseH k Kdot) := by
  unfold baseH
  rw [← LinearMap.comp_apply, multMap_comp]
  rw [show (fun x => psiSym r x * PsiSym 1 x) = PsiSym r from by
    funext x
    simp only [psiSym_apply, PsiSym_apply, ← Complex.ofReal_mul, psiR_mul_PsiR_one]]

/-- **Anti-Hermitian part of the `r`-response**: `A_r(ad_K) K̇ = χ_r(ad_K) A`. -/
theorem response_anti (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) (r : ℝ) :
    multMap k (ASym r) Kdot = multMap k (chiSym r) (baseA k Kdot) := by
  unfold baseA
  rw [← LinearMap.comp_apply, multMap_comp]
  rw [show (fun x => chiSym r x * ASym 1 x) = ASym r from by
    funext x
    simp only [chiSym_apply, ASym_apply, ← Complex.ofReal_mul, chiR_mul_AR_one]]

/-- **Matrix-level coherent composition of the Hermitian responses**:
the `rs`-response is the `s`-response (at rescaled modular argument) composed
with the `r`-response.  This is the Lean form of
`ψ_s(r x) ψ_r(x) = ψ_{rs}(x)`. -/
theorem psiSym_comp (k : ι → ℝ) (r s : ℝ) (X : Matrix ι ι ℂ) :
    multMap k (fun x => psiSym s (r * x)) (multMap k (psiSym r) X)
      = multMap k (psiSym (r * s)) X := by
  rw [← LinearMap.comp_apply, multMap_comp]
  rw [show (fun x => psiSym s (r * x) * psiSym r x) = psiSym (r * s) from by
    funext x
    simp only [psiSym_apply, ← Complex.ofReal_mul, psiR_composition]]

/-- The full response decomposition in the source's form: the `r`-response of the
generator is `ψ_r(ad_K) H + χ_r(ad_K) A`. -/
theorem response_powers (k : ι → ℝ) (Kdot : Matrix ι ι ℂ) (r : ℝ) :
    multMap k (PhiSym r) Kdot
      = multMap k (psiSym r) (baseH k Kdot) + multMap k (chiSym r) (baseA k Kdot) := by
  rw [response_split, response_hermitian, response_anti]


/-! ## 5. Complete positivity, masses and ancilla bounds

The only external input is positivity of the kernel `(i,j) ↦ ψ_r(k_i - k_j)`,
which the source obtains from the explicit Fourier density
`p_r(t) = sin (π r) / (2 (cosh (π t) + cos (π r)))` with `ψ_r = p̂_r`, `p_r ≥ 0`,
`∫ p_r = r`. Everything below is a theorem.
-/

section CPBounds

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The mass (`r = 0` value) of a difference multiplier: `Φ(1) = g 0 • 1`. -/
theorem multMap_one_eq_smul (k : ι → ℝ) (g : ℝ → ℂ) (c : ℂ) (h : g 0 = c) :
    multMap k g (1 : Matrix ι ι ℂ) = c • 1 := by
  ext i j
  rw [multMap_apply]
  by_cases hij : i = j
  · subst hij
    simp [h]
  · simp [Matrix.one_apply, hij]

/-- The amplified mass: `(Φ ⊗ id)(1) = g 0 • 1` in every amplification. -/
theorem amp_multMap_one (k : ι → ℝ) (g : ℝ → ℂ) (c : ℂ) (h : g 0 = c) :
    amp (multMap k g) (1 : Matrix (ι × ν) (ι × ν) ℂ) = c • 1 := by
  rw [amp_multMap]
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp [Matrix.hadamard, Matrix.submatrix_apply, Kmat, h]
  · simp [Matrix.hadamard, Matrix.submatrix_apply, hpq]

/-- **The ancilla Loewner bound for a difference multiplier with mass `c`.**
In every amplification `ν` and for every `0 ≤ A ≤ 1`, a multiplier whose kernel
matrix is positive semidefinite has `0 ≤ (Φ ⊗ id)(A) ≤ c • 1`, where `c = g 0`
is its mass. -/
theorem amp_multMap_loewner (k : ι → ℝ) (g : ℝ → ℂ) (c : ℂ) (h0 : g 0 = c)
    (hPD : (Kmat k g).PosSemidef) (A : Matrix (ι × ν) (ι × ν) ℂ) (hA : A.PosSemidef)
    (hAc : ((1 : Matrix (ι × ν) (ι × ν) ℂ) - A).PosSemidef) :
    (amp (multMap k g) A).PosSemidef ∧ (c • 1 - amp (multMap k g) A).PosSemidef := by
  refine ⟨(hPD.submatrix Prod.fst).hadamard hA, ?_⟩
  have heq : (Kmat k g).submatrix Prod.fst Prod.fst ⊙ ((1 : Matrix (ι × ν) (ι × ν) ℂ) - A)
      = c • 1 - amp (multMap k g) A := by
    ext p q
    by_cases hpq : p = q
    · subst hpq
      simp [Matrix.hadamard, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Kmat, amp_multMap, h0, sub_mul, mul_sub]
    · simp [Matrix.hadamard, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Kmat, amp_multMap, hpq]
  rw [← heq]
  exact (hPD.submatrix Prod.fst).hadamard hAc

/-- **Complete positivity of the Hermitian response** `ψ_r(ad_K)`. -/
theorem isCP_psi (k : ι → ℝ) (r : ℝ)
    (hPD : (Kmat k (psiSym r)).PosSemidef) : IsCP (multMap k (psiSym r)) :=
  isCP_multMap_of_posSemidef k _ hPD

/-- Mass of the Hermitian response: `ψ_r(0) = r`, so `Φ_r(1) = r • 1`. -/
theorem psi_mass (k : ι → ℝ) (r : ℝ) :
    multMap k (psiSym r) (1 : Matrix ι ι ℂ) = ((r : ℝ) : ℂ) • 1 :=
  multMap_one_eq_smul k _ _ (by simp)

/-- **Ancilla-robust bound for the Hermitian response** with mass `r`: for every
ancillary system `ν` and every `0 ≤ A ≤ 1` on the amplified space,
`0 ≤ (ψ_r(ad_K) ⊗ id)(A) ≤ r • 1`. This is the matrix-level form of
`‖H_r‖ ≤ r ‖H‖` with an arbitrary ancilla. -/
theorem psi_amp_bound (k : ι → ℝ) (r : ℝ) (hPD : (Kmat k (psiSym r)).PosSemidef)
    (A : Matrix (ι × ν) (ι × ν) ℂ) (hA : A.PosSemidef)
    (hAc : ((1 : Matrix (ι × ν) (ι × ν) ℂ) - A).PosSemidef) :
    (amp (multMap k (psiSym r)) A).PosSemidef ∧
      (((r : ℝ) : ℂ) • 1 - amp (multMap k (psiSym r)) A).PosSemidef :=
  amp_multMap_loewner k (psiSym r) ((r : ℝ) : ℂ) (by simp) hPD A hA hAc

/-- `χ_r` is the square of the half-argument Hermitian multiplier:
`χ_r(ad_K) = ψ_r(ad_K / 2) ∘ ψ_r(ad_K / 2)`. -/
theorem chiSym_eq_comp (k : ι → ℝ) (r : ℝ) :
    multMap k (chiSym r)
      = (multMap k (fun x => psiSym r (x / 2))).comp
          (multMap k (fun x => psiSym r (x / 2))) := by
  rw [multMap_comp]
  rw [show (fun x => psiSym r (x / 2) * psiSym r (x / 2)) = chiSym r from by
    funext x
    simp only [chiSym_apply, psiSym_apply, ← Complex.ofReal_mul, chiR_eq_psiR_half_sq]]

/-- **Complete positivity of the anti-Hermitian response** `χ_r(ad_K)`, as the
composition of two completely positive Hermitian responses at half argument. -/
theorem isCP_chi (k : ι → ℝ) (r : ℝ)
    (hPD : (Kmat k (fun x => psiSym r (x / 2))).PosSemidef) :
    IsCP (multMap k (chiSym r)) := by
  rw [chiSym_eq_comp]
  exact (isCP_multMap_of_posSemidef k _ hPD).comp (isCP_multMap_of_posSemidef k _ hPD)

/-- Positivity of the `χ_r` kernel, from positivity of the half-argument `ψ_r`
kernel: the kernel of a product of symbols is the Hadamard product of the kernels. -/
theorem posSemidef_Kmat_chi (k : ι → ℝ) (r : ℝ)
    (hPD : (Kmat k (fun x => psiSym r (x / 2))).PosSemidef) :
    (Kmat k (chiSym r)).PosSemidef := by
  have hsym : chiSym r = fun x => psiSym r (x / 2) * psiSym r (x / 2) := by
    funext x
    simp only [chiSym_apply, psiSym_apply, ← Complex.ofReal_mul, chiR_eq_psiR_half_sq]
  rw [hsym, Kmat_hadamard]
  exact hPD.hadamard hPD

/-- Mass of the anti-Hermitian response: `χ_r(0) = r²`, so `Φ^χ_r(1) = r² • 1`. -/
theorem chi_mass (k : ι → ℝ) (r : ℝ) :
    multMap k (chiSym r) (1 : Matrix ι ι ℂ) = (((r ^ 2 : ℝ)) : ℂ) • 1 :=
  multMap_one_eq_smul k _ _ (by simp)

/-- **Ancilla-robust bound for the anti-Hermitian response** with mass `r²`. -/
theorem chi_amp_bound (k : ι → ℝ) (r : ℝ)
    (hPD : (Kmat k (fun x => psiSym r (x / 2))).PosSemidef)
    (A : Matrix (ι × ν) (ι × ν) ℂ) (hA : A.PosSemidef)
    (hAc : ((1 : Matrix (ι × ν) (ι × ν) ℂ) - A).PosSemidef) :
    (amp (multMap k (chiSym r)) A).PosSemidef ∧
      ((((r ^ 2 : ℝ)) : ℂ) • 1 - amp (multMap k (chiSym r)) A).PosSemidef :=
  amp_multMap_loewner k (chiSym r) (((r ^ 2 : ℝ)) : ℂ) (by simp)
    (posSemidef_Kmat_chi k r hPD) A hA hAc

end CPBounds

/-! ## 6. Endpoint regularity: `r = 0`, `r = 1` and the `r ↓ 0` limit -/

/-- `sinh y / y → 1` as `y → 0` (removable singularity). -/
theorem tendsto_sinh_div_self : Tendsto (fun y : ℝ => Real.sinh y / y) (𝓝[≠] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_sinh 0).tendsto_slope_zero
  simpa [div_eq_inv_mul, Real.sinh_zero, Real.cosh_zero] using h

/-- The fixed-`x` logarithmic-response limit of the Hermitian symbol:
`ψ_r(x)/r → f(x) = x / sinh x` as `r ↓ 0`. -/
theorem tendsto_psiR_div (x : ℝ) :
    Tendsto (fun r : ℝ => psiR r x / r) (𝓝[>] 0) (𝓝 (fR x)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [fR_zero]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp [psiR, div_self hr0]
  · have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
    -- the argument `r * x → 0` inside `𝓝[≠] 0`
    have harg : Tendsto (fun r : ℝ => r * x) (𝓝[>] (0 : ℝ)) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hcont : Tendsto (fun r : ℝ => r * x) (𝓝 (0 : ℝ)) (𝓝 (0 * x)) :=
          (continuous_id.mul continuous_const).tendsto 0
        simpa using hcont.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_ne_zero (ne_of_gt hr) hx
    have hinner : Tendsto (fun r : ℝ => Real.sinh (r * x) / (r * x)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
      tendsto_sinh_div_self.comp harg
    have hconst : Tendsto (fun r : ℝ => x / Real.sinh x) (𝓝[>] (0 : ℝ))
        (𝓝 (x / Real.sinh x)) := tendsto_const_nhds
    have hprod : Tendsto (fun r : ℝ => x / Real.sinh x * (Real.sinh (r * x) / (r * x)))
        (𝓝[>] (0 : ℝ)) (𝓝 (x / Real.sinh x)) := by
      simpa using hconst.mul hinner
    have hf : fR x = x / Real.sinh x := by simp [fR, hx]
    rw [hf]
    refine Tendsto.congr' ?_ hprod
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hrx : r * x ≠ 0 := mul_ne_zero hr0 hx
    simp only [psiR, hx, if_false]
    field_simp

/-- The anti-Hermitian response vanishes to first order: `χ_r(x)/r → 0` as `r ↓ 0`. -/
theorem tendsto_chiR_div (x : ℝ) :
    Tendsto (fun r : ℝ => chiR r x / r) (𝓝[>] 0) (𝓝 0) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_nhdsWithin_iff.mp tendsto_id).1
    refine Tendsto.congr' ?_ h
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp only [chiR_zero_pt, id]
    field_simp
  · have hx2 : x / 2 ≠ 0 := by intro h; exact hx (by linarith)
    have hs : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr hx2
    have harg : Tendsto (fun r : ℝ => r * x / 2) (𝓝[>] (0 : ℝ)) (𝓝[≠] 0) := by
      have h : (fun r : ℝ => r * x / 2) = (fun r : ℝ => r * (x / 2)) := by
        funext r; ring
      rw [h]
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hcont : Tendsto (fun r : ℝ => r * (x / 2)) (𝓝 (0 : ℝ)) (𝓝 (0 * (x / 2))) :=
          (continuous_id.mul continuous_const).tendsto 0
        simpa using hcont.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_ne_zero (ne_of_gt hr) hx2
    have hinner : Tendsto (fun r : ℝ => Real.sinh (r * x / 2) / (r * x / 2))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_sinh_div_self.comp harg
    -- `χ_r(x)/r = (x² / (4 sinh (x/2)²)) * r * (sinh (rx/2)/(rx/2))²`
    have hlim : Tendsto (fun r : ℝ => (x ^ 2 / (4 * Real.sinh (x / 2) ^ 2)) * r *
        (Real.sinh (r * x / 2) / (r * x / 2)) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => (x ^ 2 / (4 * Real.sinh (x / 2) ^ 2)) * r)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc : Tendsto (fun r : ℝ => (x ^ 2 / (4 * Real.sinh (x / 2) ^ 2)) * r)
            (𝓝 (0 : ℝ)) (𝓝 ((x ^ 2 / (4 * Real.sinh (x / 2) ^ 2)) * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simp only [mul_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun r : ℝ => (Real.sinh (r * x / 2) / (r * x / 2)) ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        simpa using hinner.pow 2
      have h12 := h1.mul h2
      simpa using h12
    refine Tendsto.congr' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hrx : r * x / 2 ≠ 0 := by
      rw [show r * x / 2 = r * (x / 2) by ring]
      exact mul_ne_zero hr0 hx2
    simp only [chiR, hx, if_false]
    field_simp
    norm_num

/-- **Matrix-level logarithmic-response limit** (Hermitian part): every matrix
entry of `ψ_r(ad_K) H` divided by `r` converges to the corresponding entry of
`f(ad_K) H` as `r ↓ 0`. -/
theorem tendsto_entry_psi_div (k : ι → ℝ) (H : Matrix ι ι ℂ) (i j : ι) :
    Tendsto (fun r : ℝ => (multMap k (psiSym r) H) i j / r) (𝓝[>] 0)
      (𝓝 ((multMap k fSym H) i j)) := by
  have hc : Tendsto (fun _ : ℝ => H i j) (𝓝[>] (0 : ℝ)) (𝓝 (H i j)) :=
    tendsto_const_nhds
  have hcomp : Tendsto (fun r : ℝ => ((psiR r (k i - k j) / r : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((fR (k i - k j) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_psiR_div (k i - k j))
  have h := hcomp.mul hc
  have hlim : (multMap k fSym H) i j = ((fR (k i - k j) : ℝ) : ℂ) * H i j := by
    simp [multMap_apply]
  rw [hlim]
  refine Tendsto.congr' ?_ h
  filter_upwards with r
  rw [multMap_apply]
  simp only [psiSym_apply, chiSym_apply]
  push_cast
  ring

/-- **Matrix-level logarithmic-response limit** (anti-Hermitian part): every
matrix entry of `χ_r(ad_K) A` divided by `r` converges to `0` as `r ↓ 0`. -/
theorem tendsto_entry_chi_div (k : ι → ℝ) (A : Matrix ι ι ℂ) (i j : ι) :
    Tendsto (fun r : ℝ => (multMap k (chiSym r) A) i j / r) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun _ : ℝ => A i j) (𝓝[>] (0 : ℝ)) (𝓝 (A i j)) :=
    tendsto_const_nhds
  have hcomp : Tendsto (fun r : ℝ => ((chiR r (k i - k j) / r : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_chiR_div (k i - k j))
  have h := hcomp.mul hc
  have hz : ((0 : ℝ) : ℂ) * A i j = 0 := by simp
  rw [hz] at h
  refine Tendsto.congr' ?_ h
  filter_upwards with r
  rw [multMap_apply]
  simp only [psiSym_apply, chiSym_apply]
  push_cast
  ring

/-! ## 6b. Arbitrary Hermitian `K`: Hermitian-ness and complete positivity

The response identities above are proved in the spectral presentation. For an
arbitrary Hermitian `K` the response filters are `spectralFilter K hK ·`
(`CP/Closure`); the two facts below are what is needed to speak about them
without a chosen eigenbasis. -/

section AbstractK

/-- Conjugation `X ↦ U X Uᴴ` preserves Hermitian matrices. -/
theorem conjMap_isHermitian {U X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (conjMap U X).IsHermitian := by
  simp only [Matrix.IsHermitian, conjMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hX.eq]
  simp [Matrix.mul_assoc]

/-- **Complete positivity of `ψ_r(ad_K)` for an arbitrary Hermitian `K`.** -/
theorem isCP_spectralFilter_psi (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (r : ℝ)
    (hPD : (Kmat hK.eigenvalues (psiSym r)).PosSemidef) :
    IsCP (spectralFilter K hK (psiSym r)) :=
  isCP_spectralFilter K hK _ hPD

/-- **Complete positivity of `χ_r(ad_K)` for an arbitrary Hermitian `K`**, from
positivity of the half-argument `ψ_r` kernel. -/
theorem isCP_spectralFilter_chi (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (r : ℝ)
    (hPD : (Kmat hK.eigenvalues (fun x => psiSym r (x / 2))).PosSemidef) :
    IsCP (spectralFilter K hK (chiSym r)) :=
  isCP_spectralFilter K hK _ (posSemidef_Kmat_chi hK.eigenvalues r hPD)

end AbstractK

/-! ## 7. Interfaces (explicitly NOT proved here)

Two inputs of the source theorem are stated only as named `Prop`s.  Nothing in
this file depends on them, and they are never used as if they were proved. -/

/-- **Source interface, not proved.**  The explicit positive Fourier density of
`q:thm-powers`: for `0 < r < 1` there is `p : ℝ → ℝ` with `p ≥ 0`, `∫ p = r`,
and `ψ_r(x) = ∫ p(t) cos (t x) dt` for every `x`.  The source evaluates the
integral by residues over a rectangle of height `2πi`
(`p_r(t) = sin (π r) / (2 (cosh (π t) + cos (π r)))`).

Mathematically this positivity implies `(Kmat k (psiSym r)).PosSemidef` for every
spectrum `k`, hence (by the theorems of this file) complete positivity and the
ancilla bounds for both responses.  That implication is *not* formalized here,
so the statements below keep kernel positivity as a hypothesis, exactly as the
verified `CP/Closure.isCP_spectralFilter` does. -/
def FourierDensityInterface (r : ℝ) : Prop :=
  ∃ p : ℝ → ℝ, (∀ t, 0 ≤ p t) ∧ ∫ t : ℝ, p t = r ∧
    ∀ x : ℝ, psiR r x = ∫ t : ℝ, p t * Real.cos (t * x)

/- **Source identification (interface, not a Lean statement here).**  The
divided-difference response formalized in this file is
`(exp (r ad_K) - 1)/ad_K K̇` (symbol `Φ_r` in a spectral presentation).  The
source identifies it with the derivative `Q_r = (∂_λ ρ^r) ρ^{-r}` of the
positive matrix path `λ ↦ ρ_λ = exp (K_λ)` via
`Q_r = ∫_0^r e^{sK} K̇ e^{-sK} ds` (Duhamel's formula, differentiating the
exponential).  Formalizing that identification needs the Fréchet derivative of
the matrix exponential along a non-commuting line together with the
matrix-valued interval integral; it is deliberately *not* claimed here, and no
theorem of this file depends on it.  The algebraic content of the source
theorem (`ψ_r`, `χ_r`, the Hermitian/anti-Hermitian splitting, the KMS
relation, complete positivity with masses `r`, `r²`) is proved for the
divided-difference response. -/


end MomentGeometry.Operator.Powers


#print axioms MomentGeometry.Operator.Powers.PhiR_split
#print axioms MomentGeometry.Operator.Powers.chiR_mul_tanhHalf
#print axioms MomentGeometry.Operator.Powers.chiR_eq_psiR_half_sq
#print axioms MomentGeometry.Operator.Powers.chiR_one
#print axioms MomentGeometry.Operator.Powers.response_split
#print axioms MomentGeometry.Operator.Powers.baseA_eq_kms
#print axioms MomentGeometry.Operator.Powers.response_hermitian
#print axioms MomentGeometry.Operator.Powers.response_anti
#print axioms MomentGeometry.Operator.Powers.response_powers

#print axioms MomentGeometry.Operator.Powers.psi_amp_bound
#print axioms MomentGeometry.Operator.Powers.chi_amp_bound
#print axioms MomentGeometry.Operator.Powers.chiSym_eq_comp
#print axioms MomentGeometry.Operator.Powers.tendsto_psiR_div
#print axioms MomentGeometry.Operator.Powers.tendsto_chiR_div
#print axioms MomentGeometry.Operator.Powers.tendsto_entry_psi_div
#print axioms MomentGeometry.Operator.Powers.tendsto_entry_chi_div
#print axioms MomentGeometry.Operator.Powers.psiR_composition
#print axioms MomentGeometry.Operator.Powers.chiR_composition
#print axioms MomentGeometry.Operator.Powers.psiR_one
#print axioms MomentGeometry.Operator.Powers.psiR_zero_r
#print axioms MomentGeometry.Operator.Powers.chiR_zero_r
#print axioms MomentGeometry.Operator.Powers.PhiR_split
#print axioms MomentGeometry.Operator.Powers.AR_one_eq_tanhHalf_mul
#print axioms MomentGeometry.Operator.Powers.psiR_mul_PsiR_one
#print axioms MomentGeometry.Operator.Powers.chiR_mul_AR_one
#print axioms MomentGeometry.Operator.Powers.fR_mul_PsiR_one
#print axioms MomentGeometry.Operator.Powers.conjTranspose_multMap
#print axioms MomentGeometry.Operator.Powers.response_isHermitian
#print axioms MomentGeometry.Operator.Powers.response_isAnti
#print axioms MomentGeometry.Operator.Powers.base_recovery
#print axioms MomentGeometry.Operator.Powers.multMap_one_eq_smul
#print axioms MomentGeometry.Operator.Powers.amp_multMap_one
#print axioms MomentGeometry.Operator.Powers.amp_multMap_loewner
#print axioms MomentGeometry.Operator.Powers.posSemidef_Kmat_chi
#print axioms MomentGeometry.Operator.Powers.isCP_psi
#print axioms MomentGeometry.Operator.Powers.isCP_chi
#print axioms MomentGeometry.Operator.Powers.psi_mass
#print axioms MomentGeometry.Operator.Powers.chi_mass
#print axioms MomentGeometry.Operator.Powers.tendsto_sinh_div_self
#print axioms MomentGeometry.Operator.Powers.psiSym_comp
#print axioms MomentGeometry.Operator.Powers.conjMap_isHermitian
#print axioms MomentGeometry.Operator.Powers.isCP_spectralFilter_psi
#print axioms MomentGeometry.Operator.Powers.isCP_spectralFilter_chi
