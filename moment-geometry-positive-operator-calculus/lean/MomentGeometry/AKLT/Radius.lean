/-
Exact rational transfer-radius data of the spin-one wire (`q:cor-aklt`,
equation `q:aklt-radius`).

Source: `proofs/quantum_results.tex`.  With `beta_l = (-1/3)^l`, the Choi
eigenvalues of the transferred wire channel relative to the faithful Choi metric
of `Psi(X) = tr(X) 1 / 2` are

  `1 + 3 beta_l`  once,   `1 - beta_l`  three times,

and "centering them gives"

  `delta_l = 2 / (3^l + (-1)^l)`,   `l >= 2`.

This file formalizes that arithmetic exactly over `Q`: the two eigenvalue
families, their positivity for `l >= 2` (a genuine two-sided sandwich), the
centering identity `(upper - lower)/(upper + lower) = delta_l`, the values
`delta_2 = 1/5`, `delta_3 = 1/13` used by the supplied exact certificate
(`supplements/networks/channel_gap_compiler.py`, `aklt_channel`), and the bounds
`0 < delta_l <= 3^(1-l)`, `delta_l <= 1/9` for `l >= 3`.

The operator-side content (the wire channel's eigenvalues `1` on multiples of
the identity and `-1/3` on trace-zero matrices, and the power formula
`Phi^[l] = Psi + beta_l (id - Psi)`) is in `AKLT.Wire`; the two-port cosine
bound and the decoration exponent are in `AKLT.Decoration`.
-/
import Mathlib

namespace MomentGeometry.AKLT

/-- `beta_l = (-1/3)^l`, the scalar of the antisymmetric wire mode. -/
def beta (l : ℕ) : ℚ := (-1 : ℚ) ^ l / (3 : ℚ) ^ l

/-- First Choi eigenvalue family: `1 + 3 beta_l` (multiplicity one). -/
def choiA (l : ℕ) : ℚ := 1 + 3 * beta l

/-- Second Choi eigenvalue family: `1 - beta_l` (multiplicity three). -/
def choiB (l : ℕ) : ℚ := 1 - beta l

/-- The exact transfer radius `delta_l = 2/(3^l + (-1)^l)`. -/
def delta (l : ℕ) : ℚ := 2 / ((3 : ℚ) ^ l + (-1) ^ l)

/-- `(-1)^l` is `1` or `-1`. -/
theorem neg_one_pow_eq_one_or (l : ℕ) : (-1 : ℚ) ^ l = 1 ∨ (-1 : ℚ) ^ l = -1 := by
  have h2 : ((-1 : ℚ) ^ l) ^ 2 = 1 := by
    rw [sq, ← pow_add, show l + l = 2 * l by ring, pow_mul]
    norm_num
  exact sq_eq_one_iff.mp h2

theorem three_pow_pos (l : ℕ) : (0 : ℚ) < (3 : ℚ) ^ l := by positivity

theorem three_pow_ge (k l : ℕ) (h : k ≤ l) : (3 : ℚ) ^ k ≤ (3 : ℚ) ^ l :=
  pow_le_pow_right₀ (by norm_num) h

theorem neg_one_pow_abs (l : ℕ) : |(-1 : ℚ) ^ l| = 1 := by
  rcases neg_one_pow_eq_one_or l with h | h <;> simp [h]

theorem three_pow_sub_one_pos (l : ℕ) (h : (-1 : ℚ) ^ l = -1) : (0 : ℚ) < (3 : ℚ) ^ l - 1 := by
  have hl : l ≠ 0 := by rintro rfl; norm_num at h
  have h3l : (3 : ℚ) ≤ 3 ^ l := by
    calc (3 : ℚ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ l := three_pow_ge 1 l (Nat.one_le_iff_ne_zero.mpr hl)
  linarith

theorem three_pow_ge_three (l : ℕ) (hl : l ≠ 0) : (3 : ℚ) ≤ (3 : ℚ) ^ l := by
  calc (3 : ℚ) = 3 ^ 1 := by norm_num
    _ ≤ (3 : ℚ) ^ l := three_pow_ge 1 l (Nat.one_le_iff_ne_zero.mpr hl)

/-- `3^l + (-1)^l > 0`: the transfer radius is well defined and positive. -/
theorem three_pow_add_sign_pos (l : ℕ) : (0 : ℚ) < (3 : ℚ) ^ l + (-1) ^ l := by
  rcases neg_one_pow_eq_one_or l with h | h
  · rw [h]; have := three_pow_pos l; linarith
  · rw [h]; have := three_pow_sub_one_pos l h; linarith

/-- Closed form of the first eigenvalue family. -/
theorem choiA_closed (l : ℕ) : choiA l = ((3 : ℚ) ^ l + 3 * (-1) ^ l) / (3 : ℚ) ^ l := by
  rw [choiA, beta]
  field_simp

/-- Closed form of the second eigenvalue family. -/
theorem choiB_closed (l : ℕ) : choiB l = ((3 : ℚ) ^ l - (-1) ^ l) / (3 : ℚ) ^ l := by
  rw [choiB, beta]
  field_simp

/-- The two Choi eigenvalue families add up to `2 + 2 beta_l`. -/
theorem choiA_add_choiB (l : ℕ) : choiA l + choiB l = 2 + 2 * beta l := by
  simp only [choiA, choiB]; ring

/-- Their difference is `4 beta_l`. -/
theorem choiA_sub_choiB (l : ℕ) : choiA l - choiB l = 4 * beta l := by
  simp only [choiA, choiB]; ring

theorem beta_abs_le_third (l : ℕ) (hl : 1 ≤ l) : |beta l| ≤ 1 / 3 := by
  have h3 : (0 : ℚ) < 3 ^ l := three_pow_pos l
  have h3l : (3 : ℚ) ≤ 3 ^ l := by
    calc (3 : ℚ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ l := three_pow_ge 1 l hl
  rw [beta, abs_div, neg_one_pow_abs, abs_of_pos h3]
  rw [show (1 / 3 ^ l : ℚ) = (3 ^ l)⁻¹ by rw [one_div],
    show (1 / 3 : ℚ) = (3 : ℚ)⁻¹ by norm_num]
  rw [inv_le_inv₀ h3 (by norm_num : (0 : ℚ) < 3)]
  linarith

/-- The sandwich is nondegenerate: the sum of the two eigenvalue families is positive. -/
theorem choi_sum_pos (l : ℕ) (hl : 1 ≤ l) : 0 < choiA l + choiB l := by
  rw [choiA_add_choiB]
  have habs := beta_abs_le_third l hl
  have h : -(1 / 3 : ℚ) ≤ beta l := (abs_le.mp habs).1
  linarith

/-- Both families are strictly positive for `l >= 2`, so the sorted pair
`(lower, upper)` of the exact certificate is a genuine two-sided bound. -/
theorem choi_pos (l : ℕ) (hl : 2 ≤ l) : 0 < choiA l ∧ 0 < choiB l := by
  have h3 : (0 : ℚ) < 3 ^ l := three_pow_pos l
  have h9 : (9 : ℚ) ≤ 3 ^ l := by
    calc (9 : ℚ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ l := three_pow_ge 2 l hl
  rw [choiA_closed, choiB_closed]
  rcases neg_one_pow_eq_one_or l with h | h
  · rw [h]
    constructor <;> apply div_pos <;> linarith
  · rw [h]
    constructor <;> apply div_pos <;> linarith

/-- The centering identity of the source: with the two eigenvalue families
sorted, their normalized gap is exactly the transfer radius `delta_l`. -/
theorem centered_ratio_eq_delta (l : ℕ) :
    (max (choiA l) (choiB l) - min (choiA l) (choiB l))
      / (max (choiA l) (choiB l) + min (choiA l) (choiB l)) = delta l := by
  have h3 : (0 : ℚ) < (3 : ℚ) ^ l := three_pow_pos l
  have hx0 : (3 : ℚ) ^ l ≠ 0 := ne_of_gt h3
  rcases neg_one_pow_eq_one_or l with h | h
  · -- even length: `beta_l = 3^{-l} > 0`, so `choiA` is the upper family
    have hA : choiA l = ((3 : ℚ) ^ l + 3) / (3 : ℚ) ^ l := by
      rw [choiA_closed, h]; try ring
    have hB : choiB l = ((3 : ℚ) ^ l - 1) / (3 : ℚ) ^ l := by
      rw [choiB_closed, h]; try ring
    have hle : choiB l ≤ choiA l := by
      rw [hA, hB, div_le_div_iff₀ h3 h3]; linarith
    rw [max_eq_left hle, min_eq_right hle, hA, hB, delta, h]
    have e1 : ((3 : ℚ) ^ l + 3) / (3 : ℚ) ^ l - ((3 : ℚ) ^ l - 1) / (3 : ℚ) ^ l
        = 4 / (3 : ℚ) ^ l := by
      field_simp
      try ring
    have e2 : ((3 : ℚ) ^ l + 3) / (3 : ℚ) ^ l + ((3 : ℚ) ^ l - 1) / (3 : ℚ) ^ l
        = (2 * (3 : ℚ) ^ l + 2) / (3 : ℚ) ^ l := by
      field_simp
      try ring
    rw [e1, e2]
    have hd : 2 * (3 : ℚ) ^ l + 2 ≠ 0 := by positivity
    field_simp
    ring
  · -- odd length: `beta_l = -3^{-l} < 0`, so `choiB` is the upper family
    have hA : choiA l = ((3 : ℚ) ^ l - 3) / (3 : ℚ) ^ l := by
      rw [choiA_closed, h]; try ring
    have hB : choiB l = ((3 : ℚ) ^ l + 1) / (3 : ℚ) ^ l := by
      rw [choiB_closed, h]; try ring
    have hle : choiA l ≤ choiB l := by
      rw [hA, hB, div_le_div_iff₀ h3 h3]; linarith
    have hl : l ≠ 0 := by rintro rfl; norm_num at h
    rw [max_eq_right hle, min_eq_left hle, hA, hB, delta, h]
    have e1 : ((3 : ℚ) ^ l + 1) / (3 : ℚ) ^ l - ((3 : ℚ) ^ l - 3) / (3 : ℚ) ^ l
        = 4 / (3 : ℚ) ^ l := by
      field_simp
      try ring
    have e2 : ((3 : ℚ) ^ l + 1) / (3 : ℚ) ^ l + ((3 : ℚ) ^ l - 3) / (3 : ℚ) ^ l
        = (2 * (3 : ℚ) ^ l - 2) / (3 : ℚ) ^ l := by
      field_simp
      try ring
    rw [e1, e2]
    have h3l := three_pow_ge_three l hl
    have hd : 2 * (3 : ℚ) ^ l - 2 ≠ 0 := by
      have : (0 : ℚ) < 2 * (3 : ℚ) ^ l - 2 := by linarith
      exact ne_of_gt this
    field_simp
    ring

/-- The transfer radius is positive. -/
theorem delta_pos (l : ℕ) : 0 < delta l :=
  div_pos (by norm_num) (three_pow_add_sign_pos l)

/-- `delta_l <= 3/3^l = 3^(1-l)`, the geometric form used for the decoration
estimate. -/
theorem delta_le_pow (l : ℕ) : delta l ≤ 3 / (3 : ℚ) ^ l := by
  have hx : (0 : ℚ) < 3 ^ l := three_pow_pos l
  rw [delta, div_le_div_iff₀ (three_pow_add_sign_pos l) hx]
  rcases neg_one_pow_eq_one_or l with h | h
  · rw [h]; nlinarith [hx]
  · rw [h]
    have hl : l ≠ 0 := by rintro rfl; norm_num at h
    nlinarith [three_pow_ge_three l hl]

/-- `delta_l <= 1/9` for every `l >= 3`. -/
theorem delta_le_ninth (l : ℕ) (hl : 3 ≤ l) : delta l ≤ 1 / 9 := by
  have h3 : (0 : ℚ) < 3 ^ l := three_pow_pos l
  have h27 : (27 : ℚ) ≤ 3 ^ l := by
    calc (27 : ℚ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ l := three_pow_ge 3 l hl
  have hmid : (3 : ℚ) / 3 ^ l ≤ 1 / 9 := by
    rw [div_le_iff₀ h3]
    nlinarith
  linarith [delta_le_pow l]

/-- The exact value used by the supplied certificate: `delta_2 = 1/5`. -/
theorem delta_two : delta 2 = 1 / 5 := by
  rw [delta]; norm_num

/-- The exact value used by the supplied certificate: `delta_3 = 1/13`. -/
theorem delta_three : delta 3 = 1 / 13 := by
  rw [delta]; norm_num

end MomentGeometry.AKLT
