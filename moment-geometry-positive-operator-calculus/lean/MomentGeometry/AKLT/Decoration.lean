/-
Logarithmic sufficient decoration for the decorated AKLT wire (`q:cor-aklt`,
equation `q:log-decoration`).

Source: `proofs/quantum_results.tex`.  The two-port (cosine) bound of the exact
certificate `supplements/networks/channel_gap_compiler.py` is

  `B(x,y) = 2 x y (1 + x y) / ((1-x)^2 (1-y)^2)`,

and the decoration estimate needs, for the transfer radius
`delta_l = 2/(3^l + (-1)^l)` of `AKLT.Radius` and `Delta >= 2`,

  `2 (Delta - 1) B(delta_l, delta_l) < 1/2`  whenever  `144 Delta <= 9^l`.

This file proves exactly that row-sum arithmetic, over `Q`, with no floating
point step:

* `B(d,d) <= 4 d^2` for `0 <= d <= 1/9` (via the source's explicit constant
  `2(1+(1/9)^2)/(1-1/9)^4 = 3321/1024 < 4`);
* `delta_l <= 3/3^l`;
* hence `2 (Delta-1) B(delta_l,delta_l) <= (Delta-1)/(2 Delta) < 1/2`;
* the physical gap factor `(g/Delta)(1 - 2(Delta-1) B) > g/(2 Delta)` for `g > 0`;
* the exact certificate values (`B(1/5,1/5) = 13/64`, `B(1/13,1/13) = 85/5184`,
  rows `13/16`, `425/432` and gaps `3/16`, `7/432`) that the supplied test file
  asserts, and the existence of a natural `l` with `144 Delta <= 9^l`.

Everything here is *arithmetic of the certificate*: the finite-patch gap
`g_*(Delta,l) > 0` is kept as an explicit side condition of the physical bound
and is not claimed to be computed by this file.  No undecorated spin-3/2 gap is
asserted.
-/
import Mathlib
import MomentGeometry.AKLT.Radius

namespace MomentGeometry.AKLT

/-- The two-port (cosine) bound of the exact certificate. -/
def pairBound (x y : ℚ) : ℚ := 2 * x * y * (1 + x * y) / ((1 - x) ^ 2 * (1 - y) ^ 2)

/-- `B(d,d) = 2 d^2 (1+d^2)/(1-d)^4`. -/
theorem pairBound_self (d : ℚ) :
    pairBound d d = 2 * d ^ 2 * (1 + d ^ 2) / (1 - d) ^ 4 := by
  rw [pairBound]
  ring

/-- Exact value asserted by `supplements/networks/test_channel_gap_compiler.py`. -/
theorem pairBound_fifth : pairBound (1 / 5) (1 / 5) = 13 / 64 := by
  rw [pairBound]; norm_num

/-- Exact value asserted by `supplements/networks/test_channel_gap_compiler.py`. -/
theorem pairBound_thirteenth : pairBound (1 / 13) (1 / 13) = 85 / 5184 := by
  rw [pairBound]; norm_num

/-- The source's explicit constant at `d = 1/9`: `2(1+d^2)/(1-d)^4 = 3321/1024`. -/
theorem pairBound_ninth_constant :
    2 * (1 + (1 / 9) ^ 2) / (1 - 1 / 9) ^ 4 = (3321 : ℚ) / 1024 := by
  norm_num

/-- `3321/1024 < 4`, as the source checks. -/
theorem pairBound_ninth_constant_lt_four : (3321 : ℚ) / 1024 < 4 := by norm_num

/-- The two-port bound `B(d,d) <= 4 d^2` for `0 <= d <= 1/9`. -/
theorem pairBound_self_le_four_sq (d : ℚ) (h0 : 0 ≤ d) (h9 : d ≤ 1 / 9) :
    pairBound d d ≤ 4 * d ^ 2 := by
  have hd : (0 : ℚ) < 1 - d := by linarith
  rw [pairBound_self, div_le_iff₀ (pow_pos hd 4)]
  have hsq : (0 : ℚ) ≤ d ^ 2 := sq_nonneg d
  -- `(1-d)^4 = 1 - 4d + d^2 (6 - 4d + d^2) >= 1 - 4d`
  have h1 : (1 - 4 * d) ≤ (1 - d) ^ 4 := by
    have hexp : (1 - d) ^ 4 = 1 - 4 * d + d ^ 2 * (6 - 4 * d + d ^ 2) := by ring
    have hfac : (0 : ℚ) ≤ 6 - 4 * d + d ^ 2 := by nlinarith [sq_nonneg d]
    have hnonneg : (0 : ℚ) ≤ d ^ 2 * (6 - 4 * d + d ^ 2) := mul_nonneg hsq hfac
    linarith [hexp, hnonneg]
  have h2 : 4 * d ^ 2 * (1 - 4 * d) ≤ 4 * d ^ 2 * (1 - d) ^ 4 := by
    have hc : (0 : ℚ) ≤ 4 * d ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left h1 hc
  have h3 : 2 * d ^ 2 * (1 + d ^ 2) ≤ 4 * d ^ 2 * (1 - 4 * d) := by
    nlinarith [hsq, h0, h9]
  linarith

/-- Row-sum bound: at the logarithmic decoration level `144 Delta <= 9^l`
the total two-port contribution is strictly below one half. -/
theorem decoration_row_lt_half (Δ : ℚ) (l : ℕ) (hΔ : 2 ≤ Δ) (h9 : 144 * Δ ≤ (9 : ℚ) ^ l) :
    2 * (Δ - 1) * pairBound (delta l) (delta l) < 1 / 2 := by
  have hΔ1 : (1 : ℚ) ≤ Δ := by linarith
  have hΔpos : (0 : ℚ) < Δ := by linarith
  -- `l >= 3` from `9^l >= 144*Delta >= 288 > 81`
  have hl3 : 3 ≤ l := by
    by_contra hcon
    push Not at hcon
    have hle : (9 : ℚ) ^ l ≤ 9 ^ 2 := by
      calc (9 : ℚ) ^ l ≤ 9 ^ 2 := by
            apply pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 81 := by norm_num
    nlinarith
  have hd0 : (0 : ℚ) ≤ delta l := le_of_lt (delta_pos l)
  have hd9 : delta l ≤ 1 / 9 := delta_le_ninth l hl3
  have hB : pairBound (delta l) (delta l) ≤ 4 * (delta l) ^ 2 :=
    pairBound_self_le_four_sq _ hd0 hd9
  have h9pos : (0 : ℚ) < (9 : ℚ) ^ l := by positivity
  have h3pos : (0 : ℚ) < (3 : ℚ) ^ l := three_pow_pos l
  -- `9^l = (3^l)^2`
  have h9eq : ((3 : ℚ) ^ l) ^ 2 = (9 : ℚ) ^ l := by
    rw [show (9 : ℚ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have step3 : 8 * (Δ - 1) * (delta l) ^ 2 ≤ 8 * (Δ - 1) * (3 / (3 : ℚ) ^ l) ^ 2 := by
    have hcoef : (0 : ℚ) ≤ 8 * (Δ - 1) := by linarith
    have hsq : (delta l) ^ 2 ≤ (3 / (3 : ℚ) ^ l) ^ 2 :=
      pow_le_pow_left₀ hd0 (delta_le_pow l) 2
    exact mul_le_mul_of_nonneg_left hsq hcoef
  have step4 : 8 * (Δ - 1) * (3 / (3 : ℚ) ^ l) ^ 2 = 72 * (Δ - 1) / (9 : ℚ) ^ l := by
    have hsq : (3 / (3 : ℚ) ^ l) ^ 2 = 9 / ((3 : ℚ) ^ l) ^ 2 := by
      have h3 : (3 : ℚ) ^ l ≠ 0 := ne_of_gt h3pos
      field_simp
      norm_num
    rw [hsq, h9eq]
    field_simp
    ring
  have step5 : 72 * (Δ - 1) / (9 : ℚ) ^ l ≤ (Δ - 1) / (2 * Δ) := by
    rw [div_le_div_iff₀ h9pos (by positivity : (0 : ℚ) < 2 * Δ)]
    nlinarith [h9, hΔ1]
  have step6 : (Δ - 1) / (2 * Δ) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℚ) < 2 * Δ)]
    linarith
  have step1 : 2 * (Δ - 1) * pairBound (delta l) (delta l) ≤ 2 * (Δ - 1) * (4 * (delta l) ^ 2) := by
    have hcoef : (0 : ℚ) ≤ 2 * (Δ - 1) := by linarith
    exact mul_le_mul_of_nonneg_left hB hcoef
  have step2 : 2 * (Δ - 1) * (4 * (delta l) ^ 2) = 8 * (Δ - 1) * (delta l) ^ 2 := by ring
  nlinarith [step1, step2, step3, step4, step5, step6]

/-- The physical gap factor of `q:aklt-gap` is strictly bigger than `g/(2 Delta)`
once the logarithmic decoration level is reached. -/
theorem decoration_gap_positive (g Δ : ℚ) (l : ℕ) (hg : 0 < g) (hΔ : 2 ≤ Δ)
    (h9 : 144 * Δ ≤ (9 : ℚ) ^ l) :
    g / (2 * Δ) < (g / Δ) * (1 - 2 * (Δ - 1) * pairBound (delta l) (delta l)) := by
  have hΔpos : (0 : ℚ) < Δ := by linarith
  have hrow := decoration_row_lt_half Δ l hΔ h9
  have hhalf : (1 / 2 : ℚ) < 1 - 2 * (Δ - 1) * pairBound (delta l) (delta l) := by linarith
  have hgΔ : (0 : ℚ) < g / Δ := div_pos hg hΔpos
  have hstep : (g / Δ) * (1 / 2) < (g / Δ) * (1 - 2 * (Δ - 1) * pairBound (delta l) (delta l)) :=
    mul_lt_mul_of_pos_left hhalf hgΔ
  have heq : (g / Δ) * (1 / 2) = g / (2 * Δ) := by
    field_simp
  linarith [hstep, heq.le, heq.ge]

/-! ### The exact finite certificates of the supplied compiler -/

/-- `uniform_aklt(3, 4)`: the row sum is exactly `13/16`. -/
theorem uniform_aklt_three_four_row : 2 * (3 - 1) * pairBound (1 / 5) (1 / 5) = 13 / 16 := by
  rw [pairBound_fifth]; norm_num

/-- `uniform_aklt(3, 4)`: the certified coarse gap is exactly `3/16`. -/
theorem uniform_aklt_three_four_gap :
    1 - 2 * (3 - 1) * pairBound (1 / 5) (1 / 5) = 3 / 16 := by
  rw [pairBound_fifth]; norm_num

/-- `uniform_aklt(31, 6)`: the row sum is exactly `425/432`. -/
theorem uniform_aklt_thirtyone_six_row :
    2 * (31 - 1) * pairBound (1 / 13) (1 / 13) = 425 / 432 := by
  rw [pairBound_thirteenth]; norm_num

/-- `uniform_aklt(31, 6)`: the certified coarse gap is exactly `7/432`. -/
theorem uniform_aklt_thirtyone_six_gap :
    1 - 2 * (31 - 1) * pairBound (1 / 13) (1 / 13) = 7 / 432 := by
  rw [pairBound_thirteenth]; norm_num

/-- A natural decoration level with `144 Delta <= 9^l` always exists. -/
theorem exists_pow_nine_ge (Δ : ℚ) : ∃ l : ℕ, 144 * Δ ≤ (9 : ℚ) ^ l := by
  by_cases hΔ : Δ ≤ 0
  · exact ⟨0, by nlinarith⟩
  push Not at hΔ
  obtain ⟨n, hn⟩ := exists_nat_gt (144 * Δ)
  refine ⟨n, ?_⟩
  have hn2 : (144 * Δ) < (n : ℚ) := hn
  have h1 : ((n : ℚ)) < 2 ^ n := by
    have hn' := Nat.lt_two_pow_self (n := n)
    exact_mod_cast hn'
  have h2 : (2 : ℚ) ^ n ≤ (9 : ℚ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  linarith


/-- The least decoration level `l` with `144 Delta <= 9^l`; this is the source's
`l = ceil(log_9(144 Delta))`. -/
noncomputable def minDecoration (Δ : ℚ) : ℕ := Nat.find (exists_pow_nine_ge Δ)

theorem minDecoration_spec (Δ : ℚ) : 144 * Δ ≤ (9 : ℚ) ^ (minDecoration Δ) :=
  Nat.find_spec (exists_pow_nine_ge Δ)

/-- Minimality: the chosen level is strictly below `9 * 144 Delta`. -/
theorem minDecoration_lt (Δ : ℚ) (hΔ : 2 ≤ Δ) :
    (9 : ℚ) ^ (minDecoration Δ) < 9 * (144 * Δ) := by
  have hspec : 144 * Δ ≤ (9 : ℚ) ^ (minDecoration Δ) := minDecoration_spec Δ
  have hne : minDecoration Δ ≠ 0 := by
    rintro h0
    rw [h0] at hspec
    norm_num at hspec
    linarith
  have hle : 1 ≤ minDecoration Δ := Nat.one_le_iff_ne_zero.mpr hne
  have hnot : ¬ (144 * Δ ≤ (9 : ℚ) ^ (minDecoration Δ - 1)) := by
    intro hc
    have hmin : minDecoration Δ ≤ minDecoration Δ - 1 :=
      Nat.find_min' (exists_pow_nine_ge Δ) hc
    omega
  push Not at hnot
  obtain ⟨k, hk⟩ : ∃ k, minDecoration Δ = k + 1 := ⟨minDecoration Δ - 1, by omega⟩
  have hpow : (9 : ℚ) ^ (k + 1) = 9 * (9 : ℚ) ^ k := by
    rw [pow_succ']
  rw [hk] at hspec hnot ⊢
  rw [hpow]
  have hk1 : k + 1 - 1 = k := by omega
  rw [hk1] at hnot
  have hmul := mul_lt_mul_of_pos_left hnot (by norm_num : (0 : ℚ) < 9)
  linarith

/-- The logarithmic decoration level is at least three, as the source uses
(`delta_l <= 1/9` requires `l >= 3`). -/
theorem minDecoration_ge_three (Δ : ℚ) (hΔ : 2 ≤ Δ) : 3 ≤ minDecoration Δ := by
  by_contra hcon
  push Not at hcon
  have hle : (9 : ℚ) ^ (minDecoration Δ) ≤ 9 ^ 2 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hspec := minDecoration_spec Δ
  norm_num at hle
  nlinarith

/-- The source's "`n = 2l < log_3(144 Delta) + 2`", in exact rational form:
`3^(2l) < 1296 Delta`. -/
theorem minDecoration_pow_lt (Δ : ℚ) (hΔ : 2 ≤ Δ) :
    (3 : ℚ) ^ (2 * minDecoration Δ) < 1296 * Δ := by
  have h := minDecoration_lt Δ hΔ
  have h3 : (3 : ℚ) ^ (2 * minDecoration Δ) = (9 : ℚ) ^ (minDecoration Δ) := by
    rw [show (9 : ℚ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm]
  rw [h3]
  nlinarith

/-- `q:aklt-gap` at the source's minimal decoration level `n = 2l`,
`l = ceil(log_9(144 Delta))`: the gap factor exceeds `g/(2 Delta)`. -/
theorem decoration_gap_positive_at_min (g Δ : ℚ) (hg : 0 < g) (hΔ : 2 ≤ Δ) :
    g / (2 * Δ) < (g / Δ) *
      (1 - 2 * (Δ - 1) * pairBound (delta (minDecoration Δ)) (delta (minDecoration Δ))) :=
  decoration_gap_positive g Δ (minDecoration Δ) hg hΔ (minDecoration_spec Δ)

/-- `q:aklt-gap` in its exact-criterion form: whenever the two-port row sum is
below one, the gap factor is positive. -/
theorem decoration_gap_pos_of_row_lt_one (g Δ : ℚ) (l : ℕ) (hg : 0 < g) (hΔ : 0 < Δ)
    (hrow : 2 * (Δ - 1) * pairBound (delta l) (delta l) < 1) :
    0 < (g / Δ) * (1 - 2 * (Δ - 1) * pairBound (delta l) (delta l)) := by
  have hgΔ : (0 : ℚ) < g / Δ := div_pos hg hΔ
  have : (0 : ℚ) < 1 - 2 * (Δ - 1) * pairBound (delta l) (delta l) := by linarith
  exact mul_pos hgΔ this

end MomentGeometry.AKLT
