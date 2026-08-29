/-
`sec:shape-transfer` of `matching_classes_simple.tex`: `thm:glued-transfer`,
the gluing of per-shape quasi-isometries along the splits of the assembly.

The geometry of the assembly enters through the two distance formulas
`eq:assembly-anc` and `eq:assembly-div`, both of the shape

    d(x,y) = d(x, mark_u) + d(y, mark_v) + e + N,

with `e = 1` in the ancestor case, `e = 2` in the divergent case, and `N` the
total neck length of the intermediate copies.  What the marked property of the
per-shape maps transfers is exactly the three groups of terms, and the
bookkeeping certified here is that all of them fit the single constant `8K²`.

* `neck_le_of_markedQI`: the neck comparison at one shape, read off the marked
  quasi-isometry through the two marks.
* `neck_bounds`: the resulting dichotomy-free form `m ≤ 8K²m'` and
  `m' ≤ 4Km`, using that every shape carries at least one vertex (`m ≥ 1`);
  this is where the additive errors are absorbed multiplicatively.
* `neck_sum_bounds`: the same for the intermediate sums `N`, termwise.
* `glued_dist_bounds` and `glued_dist_same`: the termwise comparison, giving
  the quasi-isometry bounds `d' ≤ 8K²d + 8K²` and `d ≤ 8K²d' + (8K²)²` in the
  division-free convention of `IsMarkedQI`, off one copy and inside one copy
  respectively.
-/
import Mathlib.Tactic
import ChainClasses.MarkedQI

namespace ChainClasses

/-! ### The neck comparison -/

/-- A `K`-marked quasi-isometry compares the two entry-to-exit distances with
additive errors `3K` and `3K²`, the marks being moved by at most `K`. -/
lemma neck_le_of_markedQI {K : ℝ} (hK : 0 ≤ K) {X Y : MarkedSpace} {f : X.carrier → Y.carrier}
    (hf : IsMarkedQI K X Y f) :
    dist Y.entry Y.exit ≤ K * dist X.entry X.exit + 3 * K ∧
      dist X.entry X.exit ≤ K * dist Y.entry Y.exit + 3 * K ^ 2 := by
  have hentry : dist Y.entry (f X.entry) ≤ K := by rw [dist_comm]; exact hf.entry
  have hexit : dist (f X.exit) Y.exit ≤ K := hf.exit
  constructor
  · have htri : dist Y.entry Y.exit
        ≤ dist Y.entry (f X.entry) + dist (f X.entry) (f X.exit) + dist (f X.exit) Y.exit :=
      dist_triangle4 _ _ _ _
    have hmid := hf.upper X.entry X.exit
    linarith
  · have htri : dist (f X.entry) (f X.exit)
        ≤ dist (f X.entry) Y.entry + dist Y.entry Y.exit + dist Y.exit (f X.exit) :=
      dist_triangle4 _ _ _ _
    have h1 : dist (f X.entry) Y.entry ≤ K := hf.entry
    have h2 : dist Y.exit (f X.exit) ≤ K := by rw [dist_comm]; exact hf.exit
    have hlow := hf.lower X.entry X.exit
    have hmul : K * dist (f X.entry) (f X.exit) ≤ K * (dist Y.entry Y.exit + 2 * K) := by
      refine mul_le_mul_of_nonneg_left ?_ hK
      linarith
    nlinarith

/-- **The neck bounds of `thm:glued-transfer`**: with `m = d(a,b)+1 ≥ 1` the
neck length of a shape, the additive errors are absorbed multiplicatively,
`m/(8K²) ≤ m' ≤ 4Km`, in the division-free form. -/
lemma neck_bounds {K m m' : ℝ} (hK : 1 ≤ K) (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hup : m' ≤ K * (m - 1) + 3 * K + 1) (hlo : m - 1 ≤ K * (m' - 1) + 3 * K ^ 2) :
    m ≤ 8 * K ^ 2 * m' ∧ m' ≤ 4 * K * m := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  constructor
  · -- `3K² - K + 1 ≤ (8K² - K)m'`, since `m' ≥ 1` and `1 ≤ 5K²`
    have hfac : (0 : ℝ) ≤ (8 * K ^ 2 - K) * (m' - 1) := by
      have h1 : (0 : ℝ) ≤ 8 * K ^ 2 - K := by nlinarith
      nlinarith
    nlinarith
  · -- `Km + 2K + 1 ≤ 4Km`, since `m ≥ 1` and `K ≥ 1`
    nlinarith

/-- The neck bounds sum over the intermediate copies of a geodesic. -/
lemma neck_sum_bounds {ι : Type*} (s : Finset ι) {K : ℝ} (hK : 1 ≤ K) {m m' : ι → ℝ}
    (h1 : ∀ i ∈ s, 1 ≤ m i) (h1' : ∀ i ∈ s, 1 ≤ m' i)
    (hup : ∀ i ∈ s, m' i ≤ K * (m i - 1) + 3 * K + 1)
    (hlo : ∀ i ∈ s, m i - 1 ≤ K * (m' i - 1) + 3 * K ^ 2) :
    (∑ i ∈ s, m i) ≤ 8 * K ^ 2 * ∑ i ∈ s, m' i ∧ (∑ i ∈ s, m' i) ≤ 4 * K * ∑ i ∈ s, m i := by
  have hpair : ∀ i ∈ s, m i ≤ 8 * K ^ 2 * m' i ∧ m' i ≤ 4 * K * m i :=
    fun i hi => neck_bounds hK (h1 i hi) (h1' i hi) (hup i hi) (hlo i hi)
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => (hpair i hi).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => (hpair i hi).2

/-! ### The termwise comparison -/

/-- **`thm:glued-transfer`, the comparison off one copy.** Both
`eq:assembly-anc` (`e = 1`) and `eq:assembly-div` (`e = 2`) decompose the
distance into two mark distances, a constant, and a neck sum; the glued map
transfers each group, and all constants fit `8K²`. -/
theorem glued_dist_bounds {K A B N A' B' N' e d d' : ℝ} (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N) (hA' : 0 ≤ A') (hB' : 0 ≤ B') (he : 0 ≤ e)
    (hAup : A' ≤ K * A + 2 * K) (hAlo : A ≤ K * A' + 2 * K ^ 2)
    (hBup : B' ≤ K * B + 2 * K) (hBlo : B ≤ K * B' + 2 * K ^ 2)
    (hNup : N' ≤ 4 * K * N) (hNlo : N ≤ 8 * K ^ 2 * N')
    (hd : d = A + B + e + N) (hd' : d' = A' + B' + e + N') :
    d' ≤ 8 * K ^ 2 * d + 8 * K ^ 2 ∧ d ≤ 8 * K ^ 2 * d' + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hKL : K ≤ 8 * K ^ 2 := by nlinarith
  have h4KL : 4 * K ≤ 8 * K ^ 2 := by nlinarith
  have h1L : (1 : ℝ) ≤ 8 * K ^ 2 := by nlinarith
  subst hd hd'
  constructor
  · have e1 : K * A ≤ 8 * K ^ 2 * A := mul_le_mul_of_nonneg_right hKL hA
    have e2 : K * B ≤ 8 * K ^ 2 * B := mul_le_mul_of_nonneg_right hKL hB
    have e3 : 4 * K * N ≤ 8 * K ^ 2 * N := mul_le_mul_of_nonneg_right h4KL hN
    have e4 : e ≤ 8 * K ^ 2 * e := by nlinarith
    nlinarith
  · have e1 : K * A' ≤ 8 * K ^ 2 * A' := mul_le_mul_of_nonneg_right hKL hA'
    have e2 : K * B' ≤ 8 * K ^ 2 * B' := mul_le_mul_of_nonneg_right hKL hB'
    have e4 : e ≤ 8 * K ^ 2 * e := by nlinarith
    have e5 : 4 * K ^ 2 ≤ (8 * K ^ 2) ^ 2 := by nlinarith
    nlinarith

/-- **`thm:glued-transfer`, the comparison inside one copy.** A `K`-marked
quasi-isometry is in particular an `8K²`-quasi-isometry on its copy. -/
theorem glued_dist_same {K d d' : ℝ} (hK : 1 ≤ K) (hd : 0 ≤ d) (hd' : 0 ≤ d')
    (hup : d' ≤ K * d + K) (hlo : d ≤ K * d' + K ^ 2) :
    d' ≤ 8 * K ^ 2 * d + 8 * K ^ 2 ∧ d ≤ 8 * K ^ 2 * d' + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hKL : K ≤ 8 * K ^ 2 := by nlinarith
  constructor
  · have e1 : K * d ≤ 8 * K ^ 2 * d := mul_le_mul_of_nonneg_right hKL hd
    linarith
  · have e1 : K * d' ≤ 8 * K ^ 2 * d' := mul_le_mul_of_nonneg_right hKL hd'
    have e2 : K ^ 2 ≤ (8 * K ^ 2) ^ 2 := by nlinarith
    linarith

end ChainClasses
