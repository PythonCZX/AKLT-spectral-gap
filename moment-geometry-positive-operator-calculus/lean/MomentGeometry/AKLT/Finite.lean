/-
Finite-patch data of the decorated AKLT argument (`q:cor-aklt`).

Two finite facts are needed by the source beyond the wire arithmetic of
`AKLT.Wire`, `AKLT.Radius`, `AKLT.Decoration`:

* "The local degree and wire-length bounds give only finitely many two-block
  patch types; each finite positive matrix has a positive least nonzero
  eigenvalue.  Their minimum `g_*(Delta,l)` is positive."  Only the finiteness
  and positivity of the minimum is a general fact; the numerical patch gaps are
  input data of the model, not something this file pretends to compute.

* "The image has dimension `D_v D_w` and contains no maximal-spin summand; this
  equals the dimension of the complement of that summand in
  `(D_v+1)(D_w+1)` dimensions."  The arithmetic of that split is proved.

It also isolates the precise form of the polynomial-divisibility step that is
still an explicit obligation: once the distinct edge brackets are known to be
pairwise coprime, `Finset.prod_dvd_of_coprime` gives divisibility by the product.
The bracket irreducibility itself (source: "distinct edge brackets are
nonassociate irreducibles in a polynomial unique factorization domain") is
*not* proved here and is recorded as an interface.

No `sorry`, no axioms: everything below is proved.
-/
import Mathlib

namespace MomentGeometry.AKLT

/-- A finite nonempty family of patch gaps with positive entries has a positive
minimum: this is the finiteness step producing `g_*(Delta,l) > 0`. -/
theorem finite_patch_gap_pos {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (g : ι → ℚ) (hg : ∀ i ∈ s, 0 < g i) :
    0 < s.inf' hs g ∧ ∀ i ∈ s, s.inf' hs g ≤ g i := by
  refine ⟨?_, fun i hi => Finset.inf'_le g hi⟩
  rw [Finset.lt_inf'_iff]
  intro i hi
  exact hg i hi

/-- A finite image of a positive rational function has a positive minimum. -/
theorem finite_image_min_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → ℚ) (hg : ∀ i, 0 < g i) :
    0 < Finset.univ.inf' Finset.univ_nonempty g :=
  (finite_patch_gap_pos Finset.univ Finset.univ_nonempty g (fun i _ => hg i)).1

/-- The dimension split of the regional kernel argument: the bracket image has
dimension `D_v D_w`, the maximal-spin summand has dimension `D_v + D_w + 1`, and
together they fill `(D_v+1)(D_w+1)`. -/
theorem region_dimension_split (Dv Dw : ℕ) :
    Dv * Dw + (Dv + Dw + 1) = (Dv + 1) * (Dw + 1) := by
  ring

/-- The complement of the maximal-spin summand has dimension `D_v D_w`. -/
theorem region_complement_dimension (Dv Dw : ℕ) :
    (Dv + 1) * (Dw + 1) - (Dv + Dw + 1) = Dv * Dw := by
  rw [← region_dimension_split]
  omega

/-- The polynomial-divisibility step in the exact form the source uses it: if
the distinct edge brackets are pairwise coprime and each divides the regional
polynomial, then their product divides it. -/
theorem bracket_product_dvd {R : Type*} [CommSemiring R] {ι : Type*}
    (s : Finset ι) (bracket : ι → R) (f : R)
    (hcop : (s : Set ι).Pairwise (Function.onFun IsCoprime bracket))
    (hdvd : ∀ e ∈ s, bracket e ∣ f) :
    (∏ e ∈ s, bracket e) ∣ f :=
  Finset.prod_dvd_of_coprime hcop hdvd

end MomentGeometry.AKLT
