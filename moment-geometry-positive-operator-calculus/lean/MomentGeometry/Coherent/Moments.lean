/-
Finite-degree coherent Gram trace identities (`eq:coherent-finite-moments`,
`proofs/coherent_gram.tex`) in `MomentGeometry`.

Content:
* `expectedT2/T3/T4`: the exact rational finite-`n` identities with
  `D = D_m = C(m+q,q)` and `D' = D_{2m}`;
* their exact algebraic normal forms, isolating the sampling-density
  content `ρ = n/D` from explicit finite-size corrections;
* the unit-density (`n = D`) specialisations, proved for `D ≠ 0`
  (resp. `D > 0`) so that the `field_simp` denominators are discharged;
* the *limiting* forms, properly formulated: a limit needs an asymptotic
  hypothesis on `(D, D')` and on `n/D`, and the fourth-moment constant is
  `2^{-q}` precisely because `D_{2m}/D_m → 2^q`.  These are `Tendsto`
  theorems; nothing below says the finite-`k` formulas *are* a limit.

The analytic inputs that turn the Gram expansion into `expectedT2/T3/T4`
(Fubini--Study reproducing-kernel contractions `∫ P_z^{⊗m} dσ = I/D` and
`∫ |⟨z,w⟩|^{4m} dσ(w) = 1/D'`) are not re-proved here; `D` and `D'` are
just parameters.  Nothing below claims the spectral law
`thm:coherent-spectral-law`.
-/
import Mathlib

namespace MomentGeometry.Coherent

open Filter Topology

/-! ### Exact finite-`n` identities (source: eq:coherent-finite-moments) -/

/-- Exact expected normalized second trace moment, `n` iid coherent rows. -/
def expectedT2 (n D : ℚ) : ℚ :=
  1 + (n - 1) / D

/-- Exact expected normalized third trace moment. -/
def expectedT3 (n D : ℚ) : ℚ :=
  1 + 3 * (n - 1) / D + (n - 1) * (n - 2) / D ^ 2

/-- Exact expected normalized fourth trace moment.  `D' = D_{2m}` enters
only through the crossing partition `{1,3}{2,4}`, whose cycle quotient has
two directed spanning trees. -/
def expectedT4 (n D Dprime : ℚ) : ℚ :=
  1 + 6 * (n - 1) / D + (n - 1) / Dprime
    + 6 * (n - 1) * (n - 2) / D ^ 2
    + (n - 1) * (n - 2) * (n - 3) / D ^ 3

/-- Real versions of the same rational functions, for the limit theorems. -/
noncomputable def expectedT2R (n D : ℝ) : ℝ :=
  1 + (n - 1) / D

noncomputable def expectedT3R (n D : ℝ) : ℝ :=
  1 + 3 * (n - 1) / D + (n - 1) * (n - 2) / D ^ 2

noncomputable def expectedT4R (n D Dprime : ℝ) : ℝ :=
  1 + 6 * (n - 1) / D + (n - 1) / Dprime
    + 6 * (n - 1) * (n - 2) / D ^ 2
    + (n - 1) * (n - 2) * (n - 3) / D ^ 3

/-! ### Exact algebraic normal forms -/

/-- The leading same-sample term of the fourth moment is `6ρ`. -/
theorem fourth_same_sample_coefficient (n D : ℚ) :
    6 * (n - 1) / D = 6 * (n / D - 1 / D) := by
  ring

theorem expectedT2_expanded (n D : ℚ) : expectedT2 n D = 1 + n / D - 1 / D := by
  unfold expectedT2
  ring

/-- Cubic normal form of the third moment.  The finite-size corrections are
`-3/D - 3(n/D²) + 2/D²`; the density-only content is `1 + 3ρ + ρ²`. -/
theorem expectedT3_cubic_form (n D : ℚ) (hD : D ≠ 0) :
    expectedT3 n D = 1 + 3 * (n / D) + (n / D) ^ 2
      - 3 / D - 3 * (n / D ^ 2) + 2 / D ^ 2 := by
  unfold expectedT3
  field_simp
  ring

/-- Exact unit-density third formula, before any spectral limit. -/
theorem expectedT3_at_unit_density (D : ℚ) (hD : D ≠ 0) :
    expectedT3 D D = 5 - 6 / D + 2 / D ^ 2 := by
  unfold expectedT3
  field_simp
  ring

/-- Quartic density form of the fourth moment at `n = r·D`: the density
content `1 + 6r + 6r² + r³` with explicit corrections.  The `(rD - 1)/D'`
term is kept separate — it is *not* a `1/D` correction, and its size is
governed by `D'/D`. -/
theorem expectedT4_density_form (r D D' : ℚ) (hD : D ≠ 0) :
    expectedT4 (r * D) D D' =
      1 + 6 * r + 6 * r ^ 2 + r ^ 3 + (r * D - 1) / D'
        - 6 * r ^ 2 / D - 18 * r / D - 6 / D
        + 11 * r / D ^ 2 + 12 / D ^ 2 - 6 / D ^ 3 := by
  unfold expectedT4
  field_simp
  ring

/-- Exact unit-density fourth formula at the symmetric-dimension
specialisation `D' = D (D+1)`.  Lower-order terms are finite-size
corrections; this is **not** the limiting `14 + 2^{-q}` statement. -/
theorem expectedT4_plane_unit_density (D : ℚ) (hD : 0 < D) :
    expectedT4 D D (D * (D + 1)) =
      14 - 31 / D + 23 / D ^ 2 - 6 / D ^ 3 + 2 / (D + 1) := by
  have h1 : D + 1 ≠ 0 := by positivity
  have h0 : D ≠ 0 := ne_of_gt hD
  unfold expectedT4
  field_simp
  ring

/-- Equivalent exact unit-density decomposition of the fourth moment. -/
theorem fourth_moment_at_equal_counts (D : ℚ) (hD : 0 < D) :
    expectedT4 D D (D * (D + 1)) =
      14 + (-31 / D + 23 / D ^ 2 - 6 / D ^ 3 + 2 / (D + 1)) := by
  rw [expectedT4_plane_unit_density D hD]
  ring

/-! ### Limits

The source's `m → ∞` statements are not the identities: they need
`D_m → ∞`, `n_m/D_m → ρ` and `D_{2m}/D_m → 2^q`.  The last hypothesis is
exactly what converts `(n-1)/D'` into `ρ 2^{-q}`. -/

theorem tendsto_inv_R : Tendsto (fun D : ℝ => D⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero

theorem tendsto_inv_sq_R : Tendsto (fun D : ℝ => (D ^ 2)⁻¹) atTop (𝓝 0) :=
  (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).inv_tendsto_atTop

/-- Second moment: `E T_2 = 1 + ρ - 1/D → 1 + ρ`. -/
theorem tendsto_expectedT2R (ρ : ℝ) :
    Tendsto (fun D : ℝ => expectedT2R (ρ * D) D) atTop (𝓝 (1 + ρ)) := by
  have hlim : Tendsto (fun D : ℝ => 1 + ρ - D⁻¹) atTop (𝓝 (1 + ρ - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_R
  have hlim' : Tendsto (fun D : ℝ => 1 + ρ - D⁻¹) atTop (𝓝 (1 + ρ)) := by
    simpa using hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
  have hD0 : D ≠ 0 := by positivity
  unfold expectedT2R
  field_simp
  ring

/-- Third moment: `E T_3 = 1 + 3ρ + ρ² + O(1/D)`. -/
theorem tendsto_expectedT3R (ρ : ℝ) :
    Tendsto (fun D : ℝ => expectedT3R (ρ * D) D) atTop (𝓝 (1 + 3 * ρ + ρ ^ 2)) := by
  have hlim : Tendsto
      (fun D : ℝ => 1 + 3 * ρ + ρ ^ 2 - 3 * ρ * D⁻¹ - 3 * D⁻¹ + 2 * (D ^ 2)⁻¹)
      atTop (𝓝 (1 + 3 * ρ + ρ ^ 2 - 3 * ρ * 0 - 3 * 0 + 2 * 0)) := by
    exact ((tendsto_const_nhds.sub ((tendsto_const_nhds.mul tendsto_inv_R))).sub
      (tendsto_inv_R.const_mul 3)).add (tendsto_inv_sq_R.const_mul 2)
  have hlim' : Tendsto
      (fun D : ℝ => 1 + 3 * ρ + ρ ^ 2 - 3 * ρ * D⁻¹ - 3 * D⁻¹ + 2 * (D ^ 2)⁻¹)
      atTop (𝓝 (1 + 3 * ρ + ρ ^ 2)) := by
    simpa using hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
  have hD0 : D ≠ 0 := by positivity
  unfold expectedT3R
  field_simp
  ring

/-- Eventual algebraic form of the fourth moment along `n = ρ D`. -/
theorem expectedT4R_density_form (ρ D D' : ℝ) (hD : D ≠ 0) (hD' : D' ≠ 0) :
    expectedT4R (ρ * D) D D' =
      1 + 6 * (ρ - D⁻¹) + (ρ - D⁻¹) * (D / D')
        + 6 * ((ρ - D⁻¹) * (ρ - 2 * D⁻¹))
        + (ρ - D⁻¹) * (ρ - 2 * D⁻¹) * (ρ - 3 * D⁻¹) := by
  unfold expectedT4R
  field_simp

/-- Fourth moment: with `n = ρ D` and `D'/D → 2^q`,
`E T_4 → 1 + (6 + 2^{-q}) ρ + 6 ρ² + ρ³`.  The crossing correction
`ρ 2^{-q}` is exactly the `(n-1)/D'` term under `D' ≈ 2^q D`. -/
theorem tendsto_expectedT4R (ρ : ℝ) (q : ℕ) (D' : ℝ → ℝ)
    (hD' : Tendsto (fun D : ℝ => D' D / D) atTop (𝓝 ((2 : ℝ) ^ q))) :
    Tendsto (fun D : ℝ => expectedT4R (ρ * D) D (D' D)) atTop
      (𝓝 (1 + (6 + ((2 : ℝ) ^ q)⁻¹) * ρ + 6 * ρ ^ 2 + ρ ^ 3)) := by
  have hpow : ((2 : ℝ) ^ q) ≠ 0 := by positivity
  have hpos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hne : ∀ᶠ D : ℝ in atTop, D' D ≠ 0 := by
    have h := hD'.eventually (eventually_ne_nhds (ne_of_gt hpos))
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with D hD hD1
    intro h0
    apply hD
    rw [h0]
    exact zero_div D
  have ha : Tendsto (fun D : ℝ => ρ - D⁻¹) atTop (𝓝 (ρ - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_R
  have hc : Tendsto (fun D : ℝ => ρ - 2 * D⁻¹) atTop (𝓝 (ρ - 2 * 0)) :=
    tendsto_const_nhds.sub (tendsto_inv_R.const_mul 2)
  have he : Tendsto (fun D : ℝ => ρ - 3 * D⁻¹) atTop (𝓝 (ρ - 3 * 0)) :=
    tendsto_const_nhds.sub (tendsto_inv_R.const_mul 3)
  have hb : Tendsto (fun D : ℝ => (D' D / D)⁻¹) atTop (𝓝 (((2 : ℝ) ^ q)⁻¹)) :=
    hD'.inv₀ hpow
  have hφ : Tendsto (fun D : ℝ =>
      1 + 6 * (ρ - D⁻¹) + (ρ - D⁻¹) * (D' D / D)⁻¹
        + 6 * ((ρ - D⁻¹) * (ρ - 2 * D⁻¹))
        + (ρ - D⁻¹) * (ρ - 2 * D⁻¹) * (ρ - 3 * D⁻¹)) atTop
      (𝓝 (1 + 6 * (ρ - 0) + (ρ - 0) * ((2 : ℝ) ^ q)⁻¹
        + 6 * ((ρ - 0) * (ρ - 2 * 0)) + (ρ - 0) * (ρ - 2 * 0) * (ρ - 3 * 0))) :=
    (((tendsto_const_nhds.add (ha.const_mul (6:ℝ))).add (ha.mul hb)).add
      ((ha.mul hc).const_mul (6:ℝ))).add ((ha.mul hc).mul he)
  have hfinal : Tendsto (fun D : ℝ =>
      1 + 6 * (ρ - D⁻¹) + (ρ - D⁻¹) * (D' D / D)⁻¹
        + 6 * ((ρ - D⁻¹) * (ρ - 2 * D⁻¹))
        + (ρ - D⁻¹) * (ρ - 2 * D⁻¹) * (ρ - 3 * D⁻¹)) atTop
      (𝓝 (1 + (6 + ((2 : ℝ) ^ q)⁻¹) * ρ + 6 * ρ ^ 2 + ρ ^ 3)) := by
    convert hφ using 2
    ring
  refine hfinal.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hne] with D hD1 hDn
  have hD0 : D ≠ 0 := by positivity
  rw [expectedT4R_density_form ρ D (D' D) hD0 hDn]
  field_simp

end MomentGeometry.Coherent
