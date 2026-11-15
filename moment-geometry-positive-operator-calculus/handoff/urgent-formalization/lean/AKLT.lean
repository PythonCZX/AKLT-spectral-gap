import Mathlib

/-!
Unchecked urgent source. No compilation or tests have been run.
Only the elementary matrix and scalar steps are included here.
The full polynomial/SU(2)/spectral bridges are proved in aklt_proofs.tex
and explicitly catalogued as not yet formalized in aklt_obligations.md.
-/

namespace UrgentAKLT

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

def pauliX : QubitMatrix := !![0, 1; 1, 0]
def pauliY : QubitMatrix := !![0, -Complex.I; Complex.I, 0]
def pauliZ : QubitMatrix := !![1, 0; 0, -1]

/-- A coordinate form that avoids a trace-normalization ambiguity. -/
def pauliSumExpected (B : QubitMatrix) : QubitMatrix :=
  !![B 0 0 + 2 * B 1 1, -B 0 1;
     -B 1 0, 2 * B 0 0 + B 1 1]

/-- Proposed direct finite-entry proof. API normalization may need repair. -/
theorem pauli_sum_entries (B : QubitMatrix) :
    pauliX * B * pauliX + pauliY * B * pauliY + pauliZ * B * pauliZ =
      pauliSumExpected B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, pauliSumExpected,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring_nf <;> simp [Complex.I_sq]

/-- The explicit seed formula, expressed with natural powers only. -/
def explicitSeed (C M : ℝ) (R : ℕ) : ℝ :=
  (C ^ R * M ^ (R - 1))⁻¹

theorem explicitSeed_pos (C M : ℝ) (R : ℕ)
    (hC : 0 < C) (hM : 0 < M) :
    0 < explicitSeed C M R := by
  unfold explicitSeed
  exact inv_pos.mpr (mul_pos (pow_pos hC R) (pow_pos hM (R - 1)))

/-- Once a coarse bound has been established, the explicit scalar is positive. -/
theorem physicalConstant_pos (C M Δ : ℝ) (R : ℕ)
    (hC : 0 < C) (hM : 0 < M) (hΔ : 0 < Δ) :
    0 < explicitSeed C M R / (2 * Δ) := by
  exact div_pos (explicitSeed_pos C M R hC hM) (mul_pos (by norm_num) hΔ)

end UrgentAKLT
