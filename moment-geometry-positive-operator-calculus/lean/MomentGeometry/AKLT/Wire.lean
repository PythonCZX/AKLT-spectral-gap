/-
Spin-one wire channel for the decorated AKLT model (`q:cor-aklt`).

Source: `proofs/quantum_results.tex`, subsection "Microscopic normalization and
decorated AKLT models".  The spin-one wire channel is written there in Kraus
form and in depolarizing form,

  `Phi(X) = (1/3) sum_a sigma_a X sigma_a = (2/3) tr(X) 1 - (1/3) X`,

and with `Psi(X) = tr(X) 1 / 2` the source asserts

  `Phi^l = Psi + beta_l (id - Psi)`,  `beta_l = (-1/3)^l`.

This file proves the *operator* content at matrix level over `Complex`:

* `Psi` is the trace-halving conditional expectation, and it is idempotent;
* `Phi = (4/3) Psi - (1/3) id`, and its depolarizing form is proved;
* `Phi 1 = 1` and `Phi X = -(1/3) X` on trace-zero `X`: the exact transfer
  eigenvalues `1` and `-1/3` of the spin-one wire;
* `Phi^[l] X = Psi X + (-1/3)^l (X - Psi X)` for every `l`, and hence
  `Phi^[l] X = (-1/3)^l X` on the trace-zero subspace.

The equality of the Kraus sum `(1/3) sum_a sigma_a X sigma_a` with the
depolarizing form is *not* proved here; `Phi` is defined by the depolarizing
formula, which is the source's second expression.  That remaining check is
recorded in `REPORT.md`.  No Choi-matrix, positivity or many-body statement is
claimed in this file; the exact rational transfer-radius consequences are in
`AKLT.Radius` and `AKLT.Decoration`.
-/
import Mathlib

namespace MomentGeometry.AKLT

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace-halving map `Psi(X) = tr(X) 1 / n` on `n x n` matrices.

For `n = 2` this is the source's `Psi(X) = tr(X) 1 / 2`; the general form makes
the projection identity `Psi * Psi = Psi` uniform in the dimension. -/
noncomputable def psi (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := (Fintype.card n : ℂ)⁻¹ • (Matrix.trace X) • (1 : Matrix n n ℂ)
  map_add' X Y := by
    rw [Matrix.trace_add, add_smul]
    simp only [smul_add]
  map_smul' a X := by
    rw [Matrix.trace_smul]
    simp only [smul_smul, RingHom.id_apply]
    ring

@[simp] theorem psi_apply (X : Matrix n n ℂ) :
    psi n X = (Fintype.card n : ℂ)⁻¹ • (Matrix.trace X) • (1 : Matrix n n ℂ) := rfl

/-- `Psi` is idempotent: the normalized conditional expectation onto multiples
of the identity. -/
theorem psi_psi [Nonempty n] (X : Matrix n n ℂ) : psi n (psi n X) = psi n X := by
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_smul, Matrix.trace_one,
    smul_eq_mul, smul_smul]
  congr 1
  have hc : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The spin-one wire channel in depolarizing form,
`Phi(X) = (2/3) tr(X) 1 - (1/3) X`. -/
noncomputable def phi : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (4 / 3 : ℂ) • psi (Fin 2) - (1 / 3 : ℂ) • LinearMap.id

@[simp] theorem psi_fin_two_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    psi (Fin 2) X = (1 / 2 : ℂ) • (Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
  norm_num

theorem phi_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    phi X = (2 / 3 : ℂ) • (Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (1 / 3 : ℂ) • X := by
  simp only [phi, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    psi_fin_two_apply, smul_smul]
  congr 2
  ring

/-- `Phi = (4/3) Psi - (1/3) id`, the form used for the power recursion. -/
theorem phi_eq (X : Matrix (Fin 2) (Fin 2) ℂ) :
    phi X = (4 / 3 : ℂ) • psi (Fin 2) X - (1 / 3 : ℂ) • X := rfl

/-- `Phi` fixes the identity: the transfer eigenvalue `1` of the wire. -/
@[simp] theorem phi_one : phi (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [phi_apply]
  simp only [Matrix.trace_one, smul_smul]
  rw [← sub_smul]
  norm_num

/-- `Phi` acts as `-(1/3) id` on the trace-zero subspace: the exact rational
transfer eigenvalue of the spin-one wire on traceless matrices. -/
theorem phi_of_trace_zero {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Matrix.trace X = 0) :
    phi X = -(1 / 3 : ℂ) • X := by
  rw [phi_apply, hX]
  simp

/-- `Phi` fixes the range of `Psi`. -/
theorem phi_psi (X : Matrix (Fin 2) (Fin 2) ℂ) : phi (psi (Fin 2) X) = psi (Fin 2) X := by
  rw [psi_fin_two_apply, smul_smul, map_smul, phi_one]

/-- The source's power formula at matrix level:
`Phi^l X = Psi X + (-1/3)^l (X - Psi X)`. -/
theorem phi_iterate_apply (l : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    phi^[l] X = psi (Fin 2) X + (-(1 / 3) : ℂ) ^ l • (X - psi (Fin 2) X) := by
  induction l with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      have hlin : phi (psi (Fin 2) X + (-(1 / 3) : ℂ) ^ k • (X - psi (Fin 2) X))
          = psi (Fin 2) X + (-(1 / 3) : ℂ) ^ k • (phi X - psi (Fin 2) X) := by
        rw [map_add, map_smul, phi_psi, map_sub, phi_psi]
      rw [hlin, phi_eq]
      have : psi (Fin 2) X + (-(1 / 3) : ℂ) ^ k •
          ((4 / 3 : ℂ) • psi (Fin 2) X - (1 / 3 : ℂ) • X - psi (Fin 2) X)
          = psi (Fin 2) X + (-(1 / 3) : ℂ) ^ (k + 1) • (X - psi (Fin 2) X) := by
        rw [pow_succ]
        module
      exact this

/-- Operator form of the wire power formula: `Phi^l = Psi + beta_l (id - Psi)`. -/
theorem phi_iterate_eq (l : ℕ) :
    (phi^[l] : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
      = fun X => psi (Fin 2) X + (-(1 / 3) : ℂ) ^ l • (X - psi (Fin 2) X) := by
  funext X
  exact phi_iterate_apply l X

/-- Exact contraction on traceless matrices: `Phi^l X = beta_l X` there. -/
theorem phi_iterate_of_trace_zero (l : ℕ) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : Matrix.trace X = 0) :
    phi^[l] X = (-(1 / 3) : ℂ) ^ l • X := by
  have hpsi : psi (Fin 2) X = 0 := by
    rw [psi_fin_two_apply, hX]
    simp
  rw [phi_iterate_apply, hpsi]
  simp

end MomentGeometry.AKLT
