/-
`prop:repair` (positive moment repair): the finite-dimensional algebraic core.

Source: `sections/coherent_foundations.tex`, `prop:repair` and `eq:repairframe`.
The formalization guide asks for three *separate* interfaces: the moment map,
the positivity of the repair density, and the extended-valued energy
inequality.  This file provides the first two, plus the exact moment
cancellation.

What is proved here (from the frame data only, no analysis):

* `moment`, the coherent second-moment map `w ↦ ∑ᵢ wᵢ • Qᵢ`, with linearity;
* `repair_density_range`: the repair density `wᵢ = 1 - dᵢ/(2 C δ)` takes values
  in `[1/2, 3/2]` whenever `|dᵢ| ≤ C δ`, `C > 0`, `δ > 0`;
* `repair_total_mass`: it is a probability density, `∑ σᵢ wᵢ = 1`, from the
  frame identity `∑ σᵢ dᵢ = 0`;
* `repair_moment_eq`: the mixture `μ* = p μ + (1-p) σ w` with
  `p = (1+102δ)⁻¹` has moment exactly `τ`, from the frame identity
  `moment Q (σ d) = moment Q μ - τ`;
* `repair_summary`: the three statements combined with `C = 51`, i.e. the
  source constants `p = (1+102δ)⁻¹` and density bounds `[1/2, 3/2]`.

The external input that is *not* proved here is `eq:repairframe` itself: the
specific Haar fourth-moment computation for `B_z = 90 Q_z - 30 L(P_z) + 5 I` on
`Sym² ℂ³` together with the eigenvalue bound `‖B_z‖_HS = sqrt 2550 < 51`.  That
remains an explicit interface (see `MomentGeometry/Frozen/Statements.lean`).
The extended-valued energy inequality is not formalized in this file.
-/
import Mathlib

namespace MomentGeometry.Repair

open Finset

variable {ι V : Type*}

/-- The coherent moment map attached to a frame family `Q : ι → V`: the weight
function `w` is sent to `∑ᵢ wᵢ • Qᵢ`.  In the source, `Q z = P_z^{⊗2}` lives in
`Sym² ℂ^D` and `w = dμ/dσ`. -/
def moment [Fintype ι] [AddCommMonoid V] [Module ℝ V] (Q : ι → V) (w : ι → ℝ) : V :=
  ∑ i, w i • Q i

section Linear

variable [Fintype ι] [AddCommGroup V] [Module ℝ V]

theorem moment_add (Q : ι → V) (w w' : ι → ℝ) :
    moment Q (w + w') = moment Q w + moment Q w' := by
  simp only [moment, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem moment_smul (Q : ι → V) (a : ℝ) (w : ι → ℝ) :
    moment Q (a • w) = a • moment Q w := by
  simp only [moment, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

/-- Affineness of the moment map. -/
theorem moment_affine (Q : ι → V) (a b : ℝ) (w w' : ι → ℝ) :
    moment Q (fun i => a * w i + b * w' i) = a • moment Q w + b • moment Q w' := by
  have h : (fun i => a * w i + b * w' i) = a • w + b • w' := by
    funext i
    rfl
  rw [h, moment_add, moment_smul, moment_smul]

/-- The repair weight `wᵢ = 1 - dᵢ k` corrects the moment of the reference
density `σ` by `k • moment (σ d)`. -/
theorem moment_repairWeight (Q : ι → V) (σ d : ι → ℝ) (k : ℝ) :
    moment Q (fun i => σ i * (1 - d i * k)) =
      moment Q σ - k • moment Q (fun i => σ i * d i) := by
  have h1 : (fun i => σ i * (1 - d i * k)) = fun i => σ i - k * (σ i * d i) := by
    funext i
    ring
  rw [h1]
  simp only [moment]
  have h2 : ∀ i ∈ (Finset.univ : Finset ι),
      (σ i - k * (σ i * d i)) • Q i = σ i • Q i - k • ((σ i * d i) • Q i) := by
    intro i _
    rw [sub_smul, ← smul_smul]
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.smul_sum]

/-- Positivity range of the repair density: `|d| ≤ C δ` with `C, δ > 0` forces the
density `1 - d/(2 C δ)` into `[1/2, 3/2]`. -/
theorem repair_density_range {d δ C : ℝ} (hC : 0 < C) (hδ : 0 < δ) (h : |d| ≤ C * δ) :
    1 / 2 ≤ 1 - d / (2 * C * δ) ∧ 1 - d / (2 * C * δ) ≤ 3 / 2 := by
  have hpos : 0 < 2 * C * δ := by positivity
  have hne : 2 * C * δ ≠ 0 := ne_of_gt hpos
  rw [abs_le] at h
  have hup : d / (2 * C * δ) ≤ 1 / 2 := by
    have hle : d / (2 * C * δ) ≤ (C * δ) / (2 * C * δ) :=
      div_le_div_of_nonneg_right h.2 (le_of_lt hpos)
    have heq : (C * δ) / (2 * C * δ) = 1 / 2 := by
      rw [div_eq_iff hne]
      ring
    linarith
  have hlow : -(1 / 2) ≤ d / (2 * C * δ) := by
    have hle : (-(C * δ)) / (2 * C * δ) ≤ d / (2 * C * δ) :=
      div_le_div_of_nonneg_right h.1 (le_of_lt hpos)
    have heq : (-(C * δ)) / (2 * C * δ) = -(1 / 2) := by
      rw [div_eq_iff hne]
      ring
    linarith
  constructor <;> linarith

/-- The repair density is normalized: the frame identity `∑ σᵢ dᵢ = 0` gives
`∑ σᵢ (1 - dᵢ/(2 C δ)) = ∑ σᵢ`. -/
theorem repair_total_mass [DecidableEq ι] (σ d : ι → ℝ) (C δ : ℝ)
    (hframe0 : ∑ i, σ i * d i = 0) :
    ∑ i, σ i * (1 - d i / (2 * C * δ)) = ∑ i, σ i := by
  have h1 : ∀ i, σ i * (1 - d i / (2 * C * δ)) = σ i - (2 * C * δ)⁻¹ * (σ i * d i) := by
    intro i
    rw [div_eq_mul_inv]
    ring
  calc ∑ i, σ i * (1 - d i / (2 * C * δ))
      = ∑ i, (σ i - (2 * C * δ)⁻¹ * (σ i * d i)) := Finset.sum_congr rfl (fun i _ => h1 i)
    _ = ∑ i, σ i - ∑ i, (2 * C * δ)⁻¹ * (σ i * d i) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ i, σ i - (2 * C * δ)⁻¹ * ∑ i, (σ i * d i) := by rw [Finset.mul_sum]
    _ = ∑ i, σ i := by rw [hframe0, mul_zero, sub_zero]

/-- **Moment cancellation** in the general form where the two scalars `p` and `k`
obey `(1-p) k = p`.  This isolates the vector-space algebra from the arithmetic
of the source constants. -/
theorem repair_moment_eq_general [DecidableEq ι] (Q : ι → V) (σ μ : ι → ℝ) (τ : V)
    (d : ι → ℝ) (p k : ℝ) (hpk : (1 - p) * k = p)
    (hMσ : moment Q σ = τ) (hframe1 : moment Q (fun i => σ i * d i) = moment Q μ - τ) :
    moment Q (fun i => p * μ i + (1 - p) * (σ i * (1 - d i * k))) = τ := by
  rw [moment_affine, moment_repairWeight, hframe1, hMσ]
  have hexp : (1 - p) • (τ - k • (moment Q μ - τ)) =
      (1 - p) • τ - (p • moment Q μ - p • τ) := by
    rw [smul_sub, smul_smul, hpk, smul_sub]
  rw [hexp]
  have hsum : (1 - p) • τ + p • τ = τ := by
    rw [← add_smul, show 1 - p + p = 1 by ring, one_smul]
  calc p • moment Q μ + ((1 - p) • τ - (p • moment Q μ - p • τ))
      = (1 - p) • τ + p • τ := by abel
    _ = τ := hsum

/-- Auxiliary arithmetic: for `C, δ > 0` the scalars `p = (1+2Cδ)⁻¹` and
`k = (2Cδ)⁻¹` satisfy `(1-p) k = p`. -/
theorem repair_scalars (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    (1 - (1 + 2 * C * δ)⁻¹) * (2 * C * δ)⁻¹ = (1 + 2 * C * δ)⁻¹ := by
  have hs : 0 < 1 + 2 * C * δ := by positivity
  have hsne : 1 + 2 * C * δ ≠ 0 := ne_of_gt hs
  have hkpos : 0 < 2 * C * δ := by positivity
  have hkne : 2 * C * δ ≠ 0 := ne_of_gt hkpos
  have hp : (1 + 2 * C * δ)⁻¹ * (1 + 2 * C * δ) = 1 := inv_mul_cancel₀ hsne
  have hone : 1 - (1 + 2 * C * δ)⁻¹ = 2 * C * δ * (1 + 2 * C * δ)⁻¹ := by
    nlinarith [hp]
  calc (1 - (1 + 2 * C * δ)⁻¹) * (2 * C * δ)⁻¹
      = (2 * C * δ * (1 + 2 * C * δ)⁻¹) * (2 * C * δ)⁻¹ := by rw [hone]
    _ = (1 + 2 * C * δ)⁻¹ * ((2 * C * δ) * (2 * C * δ)⁻¹) := by ring
    _ = (1 + 2 * C * δ)⁻¹ := by rw [mul_inv_cancel₀ hkne, mul_one]

/-- **The moment cancellation of `prop:repair` with the source constants.**
`δ = ‖M_2(μ) - τ‖_HS`, `C = 51`, `p = (1+102δ)⁻¹`, repair density
`wᵢ = 1 - dᵢ (102δ)⁻¹`. -/
theorem repair_moment_eq [DecidableEq ι] (Q : ι → V) (σ μ : ι → ℝ) (τ : V) (d : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hMσ : moment Q σ = τ)
    (hframe1 : moment Q (fun i => σ i * d i) = moment Q μ - τ) :
    moment Q (fun i => (1 + 102 * δ)⁻¹ * μ i +
        (1 - (1 + 102 * δ)⁻¹) * (σ i * (1 - d i * (102 * δ)⁻¹))) = τ := by
  have h' : (1 - (1 + 102 * δ)⁻¹) * (102 * δ)⁻¹ = (1 + 102 * δ)⁻¹ := by
    have h := repair_scalars 51 δ (by norm_num) hδ
    have he : (2 : ℝ) * 51 * δ = 102 * δ := by norm_num
    rw [he] at h
    exact h
  exact repair_moment_eq_general Q σ μ τ d _ _ h' hMσ hframe1

/-- **`prop:repair`, positivity plus exact cancellation, source constants.**
If the frame data obey `∑ σᵢ dᵢ = 0`, `moment Q (σ d) = moment Q μ - τ`, and
`|dᵢ| ≤ 51 δ` with `δ > 0`, then the density `wᵢ = 1 - dᵢ/(102δ)` lies in
`[1/2, 3/2]`, is normalized against `σ`, and the mixture with weight
`p = (1+102δ)⁻¹` has moment `τ`. -/
theorem repair_summary [DecidableEq ι] (Q : ι → V) (σ μ : ι → ℝ) (τ : V) (d : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hσsum : ∑ i, σ i = 1)
    (hMσ : moment Q σ = τ) (hframe0 : ∑ i, σ i * d i = 0)
    (hframe1 : moment Q (fun i => σ i * d i) = moment Q μ - τ)
    (hbound : ∀ i, |d i| ≤ 51 * δ) :
    (∀ i, 1 / 2 ≤ 1 - d i / (102 * δ) ∧ 1 - d i / (102 * δ) ≤ 3 / 2) ∧
      (∑ i, σ i * (1 - d i / (102 * δ)) = 1) ∧
      moment Q (fun i => (1 + 102 * δ)⁻¹ * μ i +
        (1 - (1 + 102 * δ)⁻¹) * (σ i * (1 - d i * (102 * δ)⁻¹))) = τ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h := repair_density_range (C := 51) (by norm_num) hδ (hbound i)
    have he : (2 : ℝ) * 51 * δ = 102 * δ := by norm_num
    rw [he] at h
    exact h
  · have h := repair_total_mass σ d 51 δ hframe0
    have he : (2 : ℝ) * 51 * δ = 102 * δ := by norm_num
    rw [he, hσsum] at h
    exact h
  · exact repair_moment_eq Q σ μ τ d δ hδ hMσ hframe1

#print axioms MomentGeometry.Repair.moment_add
#print axioms MomentGeometry.Repair.moment_smul
#print axioms MomentGeometry.Repair.moment_affine
#print axioms MomentGeometry.Repair.moment_repairWeight
#print axioms MomentGeometry.Repair.repair_density_range
#print axioms MomentGeometry.Repair.repair_total_mass
#print axioms MomentGeometry.Repair.repair_moment_eq_general
#print axioms MomentGeometry.Repair.repair_scalars
#print axioms MomentGeometry.Repair.repair_moment_eq
#print axioms MomentGeometry.Repair.repair_summary

end Linear

end MomentGeometry.Repair
