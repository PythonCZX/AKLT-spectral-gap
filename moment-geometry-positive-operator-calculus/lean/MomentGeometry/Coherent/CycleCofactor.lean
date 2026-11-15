/-
Directed cycle-quotient multigraphs, rooted cofactors, and the exact
partition sums for the coherent first moments.

Source: `proofs/coherent_gram.tex` (definitions preceding
`thm:coherent-spectral-law`; `lem:tree-one-noncrossing`;
`eq:coherent-first-moments`) and the supplied exact verifier
`supplements/probability/verify_coherent_gram_moments.py`.

Conventions, matching the source and that verifier:

* a partition of the cyclic position set is encoded by a block labeling
  `w : Fin p → Fin p`; `mult w a b` counts cycle edges `i → i+1` with
  `w i = a`, `w (i+1) = b`, so **parallel edges are retained**;
* loops contribute nothing: the Laplacian is
  `L a a = Σ_{b ≠ a} mult w a b`, `L a b = - mult w a b` for `a ≠ b`;
* `treeNumber w root = det L^(root)` is the rooted cofactor of the
  quotient, i.e. the determinant of `L` with the root row and column
  deleted; the **one-vertex graph has cofactor 1** (the empty determinant);
  only labels actually used by `w` are vertices;
* `IsRGS` are the restricted-growth labelings — one per set partition — so
  sums over `rgsWords p` are sums over the partitions of `p` positions.

Everything here is finite combinatorics.  The analytic content of
`lem:coherent-graph-integral` (the `D_m^{-(r-1)}` Gaussian asymptotic and
its uniform bound) is **not** formalized, and no spectral limit is claimed.
-/
import Mathlib

set_option maxRecDepth 10000

namespace MomentGeometry.Coherent

open Finset

/-- Cyclic successor on `Fin p`. -/
def cyc {p : ℕ} (i : Fin p) : Fin p :=
  ⟨(i.val + 1) % p, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- Parallel-edge multiplicity of the cycle quotient. -/
def mult {p : ℕ} (w : Fin p → Fin p) (a b : Fin p) : ℕ :=
  (univ.filter (fun i : Fin p => w i = a ∧ w (cyc i) = b)).card

/-- Number of blocks of the partition encoded by `w`. -/
def blockCount {p : ℕ} (w : Fin p → Fin p) : ℕ := (univ.image w).card

/-- Outdegree Laplacian of the cycle quotient, loops excluded. -/
def lap {p : ℕ} (w : Fin p → Fin p) : Matrix (Fin p) (Fin p) ℤ :=
  Matrix.of fun a b =>
    if a = b then ((univ.erase a).sum (fun c => (mult w a c : ℤ))) else -(mult w a b : ℤ)

/-- Rooted cofactor `τ = det L^(root)`.  Vertices are the labels used by `w`,
which for a restricted-growth word are exactly `0, …, blockCount w - 1`. -/
def treeNumber {p : ℕ} (w : Fin p → Fin p) (root : Fin p) : ℤ :=
  (Matrix.of fun (a b : {a : Fin p // a ≠ root ∧ a.val < blockCount w}) =>
    lap w a.1 b.1).det

/-- Restricted-growth labelings: `w 0 = 0`, and every value is `0` or one
more than a value occurring strictly earlier.  One labeling per set
partition of the positions. -/
def IsRGS {p : ℕ} [NeZero p] (w : Fin p → Fin p) : Prop :=
  w 0 = 0 ∧ ∀ i : Fin p, w i = 0 ∨ ∃ j : Fin p, j.val < i.val ∧ (w j).val + 1 = (w i).val

instance {p : ℕ} [NeZero p] (w : Fin p → Fin p) : Decidable (IsRGS w) := by
  unfold IsRGS; infer_instance

/-- The canonical labelings of the partitions of `p` cyclically ordered
positions. -/
def rgsWords (p : ℕ) [NeZero p] : Finset (Fin p → Fin p) := univ.filter IsRGS

/-- Noncrossing in the cyclic order: no `a < b < c < d` with `a`,`c` in one
block and `b`,`d` in another. -/
def IsNoncrossing {p : ℕ} (w : Fin p → Fin p) : Prop :=
  ∀ a b c d : Fin p, a.val < b.val → b.val < c.val → c.val < d.val →
    ¬ (w a = w c ∧ w b = w d ∧ w a ≠ w b)

instance {p : ℕ} (w : Fin p → Fin p) : Decidable (IsNoncrossing w) := by
  unfold IsNoncrossing; infer_instance

/-- Exact partition sum for the `p`-th coherent limiting moment at complex
dimension `q` and sampling density `ρ`, using the cofactor weights `τ^{-q}`
and the block counts `ρ^{|π|-1}` of `eq:coherent-tree-moments`. -/
def momentSum (p q : ℕ) [NeZero p] (ρ : ℚ) : ℚ :=
  ∑ w ∈ rgsWords p, ρ ^ (blockCount w - 1) * (((treeNumber w 0 : ℚ)) ^ q)⁻¹

/-! ### Order-by-order checks -/

example : (rgsWords 1).card = 1 := by decide
example : (rgsWords 2).card = 2 := by decide
example : (rgsWords 3).card = 5 := by decide
example : (rgsWords 4).card = 15 := by decide

/-- Every partition of three positions has a single directed spanning tree. -/
theorem tree_one_three (w : Fin 3 → Fin 3) (hw : w ∈ rgsWords 3) :
    treeNumber w 0 = 1 := by
  revert w; decide

/-- Histogram of rooted cofactors at order four: fourteen partitions have
one directed spanning tree, and the single crossing partition has two. -/
theorem tree_histogram_four :
    ((rgsWords 4).filter (fun w => treeNumber w 0 = 1)).card = 14 ∧
    ((rgsWords 4).filter (fun w => treeNumber w 0 = 2)).card = 1 := by
  constructor <;> decide

/-- `τ = 1` exactly for noncrossing partitions at order four: the order-four
instance of `lem:tree-one-noncrossing`. -/
theorem tree_one_iff_noncrossing_four (w : Fin 4 → Fin 4) (hw : w ∈ rgsWords 4) :
    treeNumber w 0 = 1 ↔ IsNoncrossing w := by
  revert w; decide

/-- The cofactor is independent of the root, at order four. -/
theorem treeNumber_root_indep_four (w : Fin 4 → Fin 4) (r : Fin 4)
    (hw : w ∈ rgsWords 4) (hr : r.val < blockCount w) :
    treeNumber w 0 = treeNumber w r := by
  revert w r; decide

/-- Cofactors are positive integers, at order four. -/
theorem treeNumber_pos_four (w : Fin 4 → Fin 4) (r : Fin 4)
    (hw : w ∈ rgsWords 4) (hr : r.val < blockCount w) : 0 < treeNumber w r := by
  revert w r; decide

/-- The crossing partition of four positions: `{1,3}{2,4}`. -/
def crossingWord : Fin 4 → Fin 4 := ![0, 1, 0, 1]

theorem crossingWord_rgs : IsRGS crossingWord := by decide

theorem crossingWord_crossing : ¬ IsNoncrossing crossingWord := by decide

/-- The crossing quotient has two directed spanning trees, the excess that
supplies the `2^{-q}ρ` term of the fourth moment. -/
theorem crossingWord_tree : treeNumber crossingWord 0 = 2 := by decide

/-- The crossing quotient of four positions: two parallel edges each way
between the two blocks. -/
theorem crossingWord_mult (a b : Fin 4) (ha : a.val < 2) (hb : b.val < 2) :
    mult crossingWord a b = if a = b then 0 else 2 := by
  revert a b; decide

/-! ### Exact first moments

`momentSum` is the exact partition sum of `eq:coherent-tree-moments`.  The
qutrit values stated in the source (`1, 2, 5, 57/4` at `ρ = 1`, `q = 2`)
are computed exactly, e.g. by `#eval momentSum 4 2 1` and by the supplied
verifier `verify_coherent_gram_moments.py`.  A *kernel* proof of those
numerical equalities is blocked at this commit by reduction of the
`Fintype (Fin p → Fin p)` instance used by `rgsWords` (`decide` stalls
inside `Multiset.Pi`), so the values are recorded as a numerically
evaluated obligation rather than as theorems.  The cofactor histogram,
which is what enters the fourth moment, *is* proved above
(`tree_histogram_four`).
-/
end MomentGeometry.Coherent
