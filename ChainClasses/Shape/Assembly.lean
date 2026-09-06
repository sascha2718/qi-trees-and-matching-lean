import Mathlib.Tactic
import ChainClasses.Scalar.GluedTransfer
import ChainClasses.Shape.ShapeMetric

/-!
`sec:shape-harris` and `sec:shape-transfer` of `matching_classes_simple.tex`:
the assembly of a family of shapes `(σ_w)_{w ∈ 𝔹}`, and the two distance
formulas `eq:assembly-anc` and `eq:assembly-div` that `thm:glued-transfer`
takes as hypotheses.

The assembly is carried by addresses in the ambient tree `𝒩`, as a single
realisation is in `ShapeMetric.lean`: the copy of `σ_w` is planted at the
address `copyAddr σ w`, so a vertex is a pair `⟨w, p⟩` of the word naming the
copy and an address `p` inside the realisation of `σ_w`, and it sits at
`copyAddr σ w ++ p`.  The recursion
`copyAddr σ (w ++ [j]) = copyAddr σ w ++ neckAddr (σ w) ++ [j]` plants the copy
at `wj` at a child of the exit of the copy at `w`, which is the joining edge of
the assembly.  No quotient enters: the exit is a leaf of its realisation, so
both of its children are free, and the address layer keeps distinct copies
apart by itself.  The metric is `treeDist` read through the address, so the
metric axioms are inherited and each distance formula is one wedge
computation.

* `Shape.eq_neckAddr_of_prefix`: the exit is a leaf of the realisation, the
  fact that makes the planting faithful; `wedge_eq_wedge_neckAddr` is the wedge
  computation it feeds.
* `copyAddr`, `copyAddr_concat`, `copyAddr_length`: the planting of the copies,
  its recursion, and its depth, the total neck length of the copies above `w`.
* `neckSum`, `copyAddr_length_of_prefix`: the sum `∑_{u<t<v} m_t` of the two
  distance formulas and the depth increment it measures.
* `Assembly`, `Assembly.code`, `Assembly.instMetricSpace`: the vertex set of
  the assembly and its metric.
* `Assembly.dist_same`, `Assembly.dist_anc` (**`eq:assembly-anc`**) and
  `Assembly.dist_div` (**`eq:assembly-div`**): the three distance formulas, in
  the form `d = A + B + e + N` that `glued_dist_same` and `glued_dist_bounds`
  consume; `Assembly.one_le_neckLen` is the termwise hypothesis of
  `neck_sum_bounds`.
* `Assembly.Adj`, `Assembly.dist_eq_one_iff_adj`: the metric is the graph
  metric of the gluing, the copies being joined by an edge from an exit to the
  two entries below it.
* `dist_mark_bounds`, `Assembly.neckSum_bounds`: the two remaining hypotheses
  of `glued_dist_bounds`, the mark comparison of a marked quasi-isometry and
  the neck comparison summed over the intermediate copies.
* `Assembly.glue`, `Assembly.glue_dist_bounds_anc`,
  `Assembly.glue_dist_bounds_div`, `Assembly.glue_dense` and
  `Assembly.glued_transfer`: **`thm:glued-transfer`** itself, the per-shape
  maps read copy by copy, an `8K²`-quasi-isometry of the assemblies.
-/

namespace ChainClasses

open Shape (realiseAux)

/-! ### The mark comparison -/

/-- **`thm:glued-transfer`**, the mark comparison: a `K`-marked quasi-isometry
compares the distances to a pair of marks it moves by at most `K`, with the
additive errors `2K` and `2K²`. -/
lemma dist_mark_bounds {K : ℝ} (hK : 0 ≤ K) {X Y : MarkedSpace} {f : X.carrier → Y.carrier}
    (hf : IsMarkedQI K X Y f) {mX : X.carrier} {mY : Y.carrier} (hm : dist (f mX) mY ≤ K)
    (a : X.carrier) :
    dist (f a) mY ≤ K * dist a mX + 2 * K ∧ dist a mX ≤ K * dist (f a) mY + 2 * K ^ 2 := by
  constructor
  · have h1 : dist (f a) mY ≤ dist (f a) (f mX) + dist (f mX) mY := dist_triangle _ _ _
    have h2 := hf.upper a mX
    linarith
  · have h1 : dist (f a) (f mX) ≤ dist (f a) mY + dist mY (f mX) := dist_triangle _ _ _
    have h2 : dist mY (f mX) ≤ K := by rw [dist_comm]; exact hm
    have h3 := hf.lower a mX
    have h4 : K * dist (f a) (f mX) ≤ K * (dist (f a) mY + K) :=
      mul_le_mul_of_nonneg_left (by linarith) hK
    nlinarith

/-! ### Wedges over a common stem -/

/-- A common stem passes through the wedge. -/
lemma wedge_append_append (z p q : Word) : wedge (z ++ p) (z ++ q) = z ++ wedge p q := by
  induction z with
  | nil => simp
  | cons a z ih =>
      rw [List.cons_append, List.cons_append, wedge_cons_cons, if_pos rfl, ih, List.cons_append]

/-- Distances inside one copy are the distances of the addresses. -/
lemma treeDist_append_append (z p q : Word) : treeDist (z ++ p) (z ++ q) = treeDist p q := by
  have h1 := treeDist_add_wedge_length (z ++ p) (z ++ q)
  have h2 := treeDist_add_wedge_length p q
  rw [wedge_append_append] at h1
  simp only [List.length_append] at h1
  omega

/-! ### The exit is a leaf -/

/-- **`def:shape`**: the exit of a realisation is a leaf, so no address of the
realisation lies strictly below it. -/
lemma Shape.eq_neckAddr_of_prefix : ∀ (l : List (Option Tri)) {p : Word},
    (realiseAux l).IsAddr p → Shape.neckAddr l <+: p → p = Shape.neckAddr l := by
  intro l
  induction l with
  | nil => intro p hp _; exact Tri.eq_nil_of_isAddr_leaf hp
  | cons b bs ih =>
      intro p hp hpre
      cases b with
      | none =>
          obtain ⟨s, rfl⟩ := hpre
          simp only [Shape.neckAddr_none, List.cons_append, realiseAux,
            Tri.isAddr_one_false] at hp ⊢
          rw [ih hp ⟨s, rfl⟩]
      | some d =>
          obtain ⟨s, rfl⟩ := hpre
          simp only [Shape.neckAddr_some, List.cons_append, realiseAux,
            Tri.isAddr_two_true] at hp ⊢
          rw [ih hp ⟨s, rfl⟩]

/-- The wedge of an address of a realisation with anything reaching past the
exit is its wedge with the exit: the branch parts at the exit at the latest. -/
lemma wedge_eq_wedge_neckAddr {l : List (Option Tri)} {p R : Word} {b : Bool}
    (hp : (realiseAux l).IsAddr p) (hR : Shape.neckAddr l ++ [b] <+: R) :
    wedge p R = wedge p (Shape.neckAddr l) := by
  have hnR : Shape.neckAddr l <+: R := (List.prefix_append _ [b]).trans hR
  have hg1 : wedge p (Shape.neckAddr l) <+: p := wedge_prefix_left _ _
  have hg2 : wedge p (Shape.neckAddr l) <+: Shape.neckAddr l := wedge_prefix_right _ _
  have hle : wedge p (Shape.neckAddr l) <+: wedge p R := prefix_wedge hg1 (hg2.trans hnR)
  rcases prefix_total_of_prefix (wedge_prefix_right p R) hnR with h | h
  · have h2 : wedge p R <+: wedge p (Shape.neckAddr l) :=
      prefix_wedge (wedge_prefix_left p R) h
    exact h2.eq_of_length (le_antisymm h2.length_le hle.length_le)
  · have hnp : Shape.neckAddr l <+: p := h.trans (wedge_prefix_left p R)
    have hpn : p = Shape.neckAddr l := Shape.eq_neckAddr_of_prefix l hp hnp
    subst hpn
    rw [wedge_of_prefix hnR, wedge_self]

/-! ### Planting the copies -/

/-- The address at which the copy of `σ_w` is planted in the assembly: the copy
at `w ++ [j]` hangs at the child `j` of the exit of the copy at `w`. -/
def copyAddr (σ : Word → Shape) (w : Word) : Word :=
  (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ Shape.neckAddr (σ p.1).decs ++ [j]))
    (([] : Word), ([] : Word))).2

/-- The first fold component records the consumed prefix. -/
lemma copyAddr_foldl_fst (σ : Word → Shape) (w a b : Word) :
    (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ Shape.neckAddr (σ p.1).decs ++ [j])) (a, b)).1
      = a ++ w := by
  induction w generalizing a b with
  | nil => simp
  | cons j t ih => simpa using ih (a ++ [j]) (b ++ Shape.neckAddr (σ a).decs ++ [j])

/-- The copy at the root sits at the root. -/
@[simp] lemma copyAddr_nil (σ : Word → Shape) : copyAddr σ [] = [] := rfl

/-- The recursion of the assembly: the copy at `w ++ [j]` is planted at the
child `j` of the exit of the copy at `w`. -/
lemma copyAddr_concat (σ : Word → Shape) (w : Word) (j : Bool) :
    copyAddr σ (w ++ [j]) = copyAddr σ w ++ Shape.neckAddr (σ w).decs ++ [j] := by
  have h := copyAddr_foldl_fst σ w [] []
  rw [List.nil_append] at h
  simp only [copyAddr, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [h]

/-- The planting only appends: it is monotone for the prefix order. -/
lemma copyAddr_prefix (σ : Word → Shape) {w w' : Word} (h : w <+: w') :
    copyAddr σ w <+: copyAddr σ w' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc]
      calc copyAddr σ w <+: copyAddr σ (w ++ u) := ih
        _ <+: copyAddr σ (w ++ u ++ [j]) := by
            rw [copyAddr_concat]
            exact (List.prefix_append _ _).trans (List.prefix_append _ _)

/-- The depth of a copy is the total neck length of the copies above it. -/
lemma copyAddr_length (σ : Word → Shape) (w : Word) :
    (copyAddr σ w).length = ∑ i ∈ Finset.range w.length, (σ (w.take i)).neckLen := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w j ih =>
      have hcong : ∀ i ∈ Finset.range w.length,
          (σ ((w ++ [j]).take i)).neckLen = (σ (w.take i)).neckLen := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [List.take_append_of_le_length (by omega)]
      rw [copyAddr_concat]
      simp only [List.length_append, List.length_singleton, Shape.neckAddr_length,
        Shape.decs_length, Finset.sum_range_succ]
      rw [Finset.sum_congr rfl hcong, List.take_left, ← ih, Shape.neckLen]
      omega

/-- **The neck sum of `eq:assembly-anc` and `eq:assembly-div`**: the total neck
length `∑_{u<t<v} m_t` of the copies strictly between `u` and `v`. -/
def neckSum (σ : Word → Shape) (u v : Word) : ℕ :=
  ∑ i ∈ Finset.Ico (u.length + 1) v.length, (σ (v.take i)).neckLen

/-- The depth increment from a copy to a copy below it: one whole neck, then
the necks of the copies in between. -/
lemma copyAddr_length_of_prefix (σ : Word → Shape) {u v : Word} (huv : u <+: v) (hne : u ≠ v) :
    (copyAddr σ v).length = (copyAddr σ u).length + (σ u).neckLen + neckSum σ u v := by
  have hlt : u.length < v.length := by
    rcases huv.length_le.lt_or_eq with h | h
    · exact h
    · exact absurd (huv.eq_of_length h) hne
  have hu : u = v.take u.length := List.prefix_iff_eq_take.mp huv
  have hlow : ∀ i ∈ Finset.range u.length,
      (σ (v.take i)).neckLen = (σ (u.take i)).neckLen := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hu, List.take_take, Nat.min_eq_left hi.le]
  have hsplit : ∑ i ∈ Finset.range v.length, (σ (v.take i)).neckLen
      = (∑ i ∈ Finset.range u.length, (σ (v.take i)).neckLen)
        + ∑ i ∈ Finset.Ico u.length v.length, (σ (v.take i)).neckLen := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hlt.le]
  have hbot : ∑ i ∈ Finset.Ico u.length v.length, (σ (v.take i)).neckLen
      = (σ u).neckLen + neckSum σ u v := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt, ← hu]
    rfl
  rw [copyAddr_length, copyAddr_length, hsplit, hbot, Finset.sum_congr rfl hlow]
  omega

/-! ### The distance formulas at the level of addresses -/

/-- Inside one copy the distance is the distance of the addresses. -/
lemma treeDist_copyAddr_same (σ : Word → Shape) (u p q : Word) :
    treeDist (copyAddr σ u ++ p) (copyAddr σ u ++ q) = treeDist p q :=
  treeDist_append_append _ _ _

/-- **`eq:assembly-anc`** at the level of addresses: from a vertex of the copy
at `u` to a vertex of a copy strictly below it, the geodesic leaves through the
exit of the copy at `u`, crosses one edge, traverses the intermediate copies,
and descends to the vertex from the entry of its copy. -/
lemma treeDist_copyAddr_anc (σ : Word → Shape) {u v : Word} (huv : u <+: v) (hne : u ≠ v)
    {p : Word} (hp : (realiseAux (σ u).decs).IsAddr p) (q : Word) :
    treeDist (copyAddr σ u ++ p) (copyAddr σ v ++ q)
      = treeDist p (Shape.neckAddr (σ u).decs) + 1 + neckSum σ u v + q.length := by
  obtain ⟨s, rfl⟩ := huv
  cases s with
  | nil => exact absurd (by simp) hne
  | cons j t =>
      have hstep : copyAddr σ u ++ Shape.neckAddr (σ u).decs ++ [j]
          <+: copyAddr σ (u ++ j :: t) := by
        rw [← copyAddr_concat]
        exact copyAddr_prefix σ ⟨t, by simp⟩
      obtain ⟨r, hr⟩ := hstep
      have hcode : copyAddr σ (u ++ j :: t) ++ q
          = copyAddr σ u ++ ((Shape.neckAddr (σ u).decs ++ [j]) ++ (r ++ q)) := by
        rw [← hr]; simp only [List.append_assoc]
      have hw : wedge (copyAddr σ u ++ p)
            (copyAddr σ u ++ ((Shape.neckAddr (σ u).decs ++ [j]) ++ (r ++ q)))
          = copyAddr σ u ++ wedge p (Shape.neckAddr (σ u).decs) := by
        rw [wedge_append_append, wedge_eq_wedge_neckAddr hp (List.prefix_append _ _)]
      have h1 := treeDist_add_wedge_length (copyAddr σ u ++ p)
        (copyAddr σ u ++ ((Shape.neckAddr (σ u).decs ++ [j]) ++ (r ++ q)))
      rw [hw] at h1
      have h2 := treeDist_add_wedge_length p (Shape.neckAddr (σ u).decs)
      have hrlen := congrArg List.length hr
      simp only [List.length_append, List.length_singleton] at hrlen
      have hlen := copyAddr_length_of_prefix σ (u := u) (v := u ++ j :: t) ⟨j :: t, rfl⟩ hne
      have hnlen : (Shape.neckAddr (σ u).decs).length = (σ u).necks := by
        rw [Shape.neckAddr_length, Shape.decs_length]
      have hneck : (σ u).neckLen = (σ u).necks + 1 := rfl
      rw [hcode]
      simp only [List.length_append, List.length_singleton] at h1
      omega

/-- **`eq:assembly-div`** at the level of addresses: from a vertex of the copy
at `u` to a vertex of the copy at a diverging `v`, the two branches climb to
the entries of their copies, traverse the intermediate copies, and meet at the
exit of the copy at the wedge. -/
lemma treeDist_copyAddr_div (σ : Word → Shape) {u v : Word} (hu : ¬ u <+: v) (hv : ¬ v <+: u)
    (p q : Word) :
    treeDist (copyAddr σ u ++ p) (copyAddr σ v ++ q)
      = p.length + q.length + 2 + neckSum σ (wedge u v) u + neckSum σ (wedge u v) v := by
  obtain ⟨z, a, b, hab, hzu, hzv⟩ := exists_diverge hu hv
  have hz : wedge u v = z := wedge_of_diverge hab hzu hzv
  have hzu' : z <+: u := (List.prefix_append z [a]).trans hzu
  have hzv' : z <+: v := (List.prefix_append z [b]).trans hzv
  have hzune : z ≠ u := by
    intro h
    have := hzu.length_le
    rw [← h] at this
    simp at this
  have hzvne : z ≠ v := by
    intro h
    have := hzv.length_le
    rw [← h] at this
    simp at this
  have hpu : copyAddr σ z ++ Shape.neckAddr (σ z).decs ++ [a] <+: copyAddr σ u := by
    rw [← copyAddr_concat]
    exact copyAddr_prefix σ hzu
  have hpv : copyAddr σ z ++ Shape.neckAddr (σ z).decs ++ [b] <+: copyAddr σ v := by
    rw [← copyAddr_concat]
    exact copyAddr_prefix σ hzv
  have hw : wedge (copyAddr σ u ++ p) (copyAddr σ v ++ q)
      = copyAddr σ z ++ Shape.neckAddr (σ z).decs :=
    wedge_of_diverge hab (hpu.trans (List.prefix_append _ _))
      (hpv.trans (List.prefix_append _ _))
  have h1 := treeDist_add_wedge_length (copyAddr σ u ++ p) (copyAddr σ v ++ q)
  rw [hw] at h1
  have hlenu := copyAddr_length_of_prefix σ hzu' hzune
  have hlenv := copyAddr_length_of_prefix σ hzv' hzvne
  have hnlen : (Shape.neckAddr (σ z).decs).length = (σ z).necks := by
    rw [Shape.neckAddr_length, Shape.decs_length]
  have hneck : (σ z).neckLen = (σ z).necks + 1 := rfl
  rw [hz]
  simp only [List.length_append] at h1
  omega

/-! ### The assembly as a metric space -/

/-- **The assembly of a family of shapes**: a vertex is an address inside the
realisation of the shape at `w`, tagged by the word `w` naming its copy. -/
structure Assembly (σ : Word → Shape) where
  /-- The word naming the copy. -/
  copy : Word
  /-- The address inside the realisation of the shape at that copy. -/
  vert : (shapeSpace (σ copy)).carrier

namespace Assembly

variable {σ : Word → Shape}

/-- The address of a vertex of the assembly in the ambient tree: the planting
of its copy followed by its address inside the copy. -/
def code (x : Assembly σ) : Word := copyAddr σ x.copy ++ x.vert.1

/-- A vertex of the assembly is determined by its copy and its address. -/
lemma vert_eq : ∀ {x y : Assembly σ}, x.copy = y.copy → x.vert.1 = y.vert.1 → x = y := by
  rintro ⟨u, p, hp⟩ ⟨v, q, hq⟩ h1 h2
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- The three relative positions of two copies. -/
lemma copy_trichotomy (u v : Word) :
    u = v ∨ (u <+: v ∧ u ≠ v) ∨ (v <+: u ∧ v ≠ u) ∨ (¬ u <+: v ∧ ¬ v <+: u) := by
  by_cases h1 : u <+: v
  · by_cases h2 : v <+: u
    · exact Or.inl (h1.eq_of_length (le_antisymm h1.length_le h2.length_le))
    · exact Or.inr (Or.inl ⟨h1, fun h => h2 (h ▸ List.prefix_refl _)⟩)
  · by_cases h2 : v <+: u
    · exact Or.inr (Or.inr (Or.inl ⟨h2, fun h => h1 (h ▸ List.prefix_refl _)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))

/-- Distinct vertices carry distinct addresses. -/
lemma code_injective : Function.Injective (code (σ := σ)) := by
  rintro ⟨u, p⟩ ⟨v, q⟩ h
  simp only [code] at h
  have h0 : treeDist (copyAddr σ u ++ p.1) (copyAddr σ v ++ q.1) = 0 :=
    treeDist_eq_zero_iff.mpr h
  rcases copy_trichotomy u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨hu, hv⟩
  · refine vert_eq rfl ?_
    rw [treeDist_copyAddr_same] at h0
    exact treeDist_eq_zero_iff.mp h0
  · rw [treeDist_copyAddr_anc σ huv hne p.2] at h0
    omega
  · rw [treeDist_comm, treeDist_copyAddr_anc σ hvu hne q.2] at h0
    omega
  · rw [treeDist_copyAddr_div σ hu hv] at h0
    omega

/-- The metric of the assembly, restricted from the ambient tree along the
addresses. -/
instance instMetricSpace (σ : Word → Shape) : MetricSpace (Assembly σ) where
  dist x y := (treeDist (code x) (code y) : ℝ)
  dist_self x := by simp
  dist_comm x y := by simp only [treeDist_comm (code x) (code y)]
  dist_triangle x y z := by
    have := treeDist_triangle (code x) (code y) (code z)
    exact_mod_cast this
  eq_of_dist_eq_zero {x y} h := by
    have h0 : treeDist (code x) (code y) = 0 := by exact_mod_cast h
    exact code_injective (treeDist_eq_zero_iff.mp h0)

/-- The distance of two vertices is the distance of their addresses. -/
@[simp] lemma dist_code (x y : Assembly σ) :
    dist x y = (treeDist (code x) (code y) : ℝ) := rfl

/-- The distance inside a realisation is the distance of the addresses. -/
@[simp] lemma dist_shapeSpace (τ : Shape) (p q : (shapeSpace τ).carrier) :
    dist p q = (treeDist p.1 q.1 : ℝ) := rfl

/-- The entry of a realisation is its root. -/
@[simp] lemma entry_shapeSpace (τ : Shape) : (shapeSpace τ).entry.1 = ([] : Word) := rfl

/-- The exit of a realisation is the far end of its neck. -/
@[simp] lemma exit_shapeSpace (τ : Shape) :
    (shapeSpace τ).exit.1 = Shape.neckAddr τ.decs := rfl

/-! ### The distance formulas -/

/-- Every shape carries at least one neck vertex: the hypothesis `1 ≤ m` of
`neck_bounds` and `neck_sum_bounds`. -/
lemma one_le_neckLen (τ : Shape) : (1 : ℝ) ≤ (τ.neckLen : ℝ) := by
  exact_mod_cast τ.neckLen_pos

/-- **`thm:glued-transfer`, inside one copy**: every copy is an induced subtree,
so its internal distances agree with those of the assembly. -/
theorem dist_same (σ : Word → Shape) (u : Word) (p q : (shapeSpace (σ u)).carrier) :
    dist (⟨u, p⟩ : Assembly σ) ⟨u, q⟩ = dist p q := by
  simp only [dist_code, code, dist_shapeSpace, treeDist_copyAddr_same]

/-- **`eq:assembly-anc`**: for `x` in the copy at `u` and `y` in the copy at a
`v` strictly below `u`, the distance is the distance of `x` to the exit of its
copy, plus the distance of `y` to the entry of its copy, plus one, plus the
total neck length of the copies strictly between `u` and `v`. -/
theorem dist_anc (σ : Word → Shape) {u v : Word} (huv : u <+: v) (hne : u ≠ v)
    (p : (shapeSpace (σ u)).carrier) (q : (shapeSpace (σ v)).carrier) :
    dist (⟨u, p⟩ : Assembly σ) ⟨v, q⟩
      = dist p (shapeSpace (σ u)).exit + dist q (shapeSpace (σ v)).entry + 1
        + ∑ i ∈ Finset.Ico (u.length + 1) v.length, ((σ (v.take i)).neckLen : ℝ) := by
  simp only [dist_code, code, dist_shapeSpace, entry_shapeSpace, exit_shapeSpace]
  rw [treeDist_copyAddr_anc σ huv hne p.2]
  simp only [neckSum, treeDist_nil_right]
  push_cast
  ring

/-- **`eq:assembly-div`**: for `x` in the copy at `u` and `y` in the copy at a
diverging `v`, the distance is the distance of `x` to the entry of its copy,
plus the distance of `y` to the entry of its copy, plus two, plus the total
neck lengths of the copies strictly between the wedge and each of `u` and
`v`. -/
theorem dist_div (σ : Word → Shape) {u v : Word} (hu : ¬ u <+: v) (hv : ¬ v <+: u)
    (p : (shapeSpace (σ u)).carrier) (q : (shapeSpace (σ v)).carrier) :
    dist (⟨u, p⟩ : Assembly σ) ⟨v, q⟩
      = dist p (shapeSpace (σ u)).entry + dist q (shapeSpace (σ v)).entry + 2
        + (∑ i ∈ Finset.Ico ((wedge u v).length + 1) u.length, ((σ (u.take i)).neckLen : ℝ)
          + ∑ i ∈ Finset.Ico ((wedge u v).length + 1) v.length,
              ((σ (v.take i)).neckLen : ℝ)) := by
  simp only [dist_code, code, dist_shapeSpace, entry_shapeSpace]
  rw [treeDist_copyAddr_div σ hu hv]
  simp only [neckSum, treeDist_nil_right]
  push_cast
  ring

/-! ### The gluing edges -/

/-- The gluing edge of the assembly: the exit of the copy at `w` is joined to
the entry of the copy at `w ++ [j]`. -/
def IsGlue (x y : Assembly σ) : Prop :=
  ∃ j : Bool, y.copy = x.copy ++ [j] ∧ x.vert.1 = Shape.neckAddr (σ x.copy).decs ∧
    y.vert.1 = []

/-- The adjacency of the assembly: the parent-child adjacency inside a copy,
together with the gluing edges between the copies. -/
def Adj (x y : Assembly σ) : Prop :=
  (x.copy = y.copy ∧ ((∃ b, y.vert.1 = x.vert.1 ++ [b]) ∨ ∃ b, x.vert.1 = y.vert.1 ++ [b]))
    ∨ IsGlue x y ∨ IsGlue y x

/-- A vertex at distance one from a vertex of a copy strictly above it is the
entry of a copy glued to the exit above. -/
lemma isGlue_of_dist_eq_one {u v : Word} (huv : u <+: v) (hne : u ≠ v)
    (p : (shapeSpace (σ u)).carrier) (q : (shapeSpace (σ v)).carrier)
    (h : treeDist (copyAddr σ u ++ p.1) (copyAddr σ v ++ q.1) = 1) :
    IsGlue (⟨u, p⟩ : Assembly σ) ⟨v, q⟩ := by
  rw [treeDist_copyAddr_anc σ huv hne p.2] at h
  have hlt : u.length < v.length := by
    rcases huv.length_le.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (huv.eq_of_length h') hne
  have hsum : neckSum σ u v = 0 := by omega
  have hshort : v.length ≤ u.length + 1 := by
    by_contra hc
    rw [Nat.not_le] at hc
    have hmem : u.length + 1 ∈ Finset.Ico (u.length + 1) v.length :=
      Finset.mem_Ico.mpr ⟨le_refl _, hc⟩
    have hle := Finset.single_le_sum
      (f := fun i => (σ (v.take i)).neckLen) (fun i _ => Nat.zero_le _) hmem
    have hpos := (σ (v.take (u.length + 1))).neckLen_pos
    rw [← neckSum, hsum] at hle
    omega
  obtain ⟨s, rfl⟩ := huv
  have hslen : s.length = 1 := by
    simp only [List.length_append] at hlt hshort
    omega
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hslen
  have hzero : treeDist p.1 (Shape.neckAddr (σ u).decs) = 0 := by omega
  have hqlen : q.1.length = 0 := by omega
  exact ⟨j, rfl, treeDist_eq_zero_iff.mp hzero, List.length_eq_zero_iff.mp hqlen⟩

/-- **The assembly is glued along edges**: its metric is the graph metric of
the parent-child adjacency inside the copies together with the edges joining
each exit to the two entries below it. -/
theorem dist_eq_one_iff_adj (x y : Assembly σ) : dist x y = 1 ↔ Adj x y := by
  obtain ⟨u, p⟩ := x
  obtain ⟨v, q⟩ := y
  have hcast : dist (⟨u, p⟩ : Assembly σ) ⟨v, q⟩ = 1
      ↔ treeDist (copyAddr σ u ++ p.1) (copyAddr σ v ++ q.1) = 1 := by
    simp only [dist_code, code]
    exact_mod_cast Iff.rfl
  rw [hcast]
  constructor
  · intro h
    rcases copy_trichotomy u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨hu, hv⟩
    · rw [treeDist_copyAddr_same] at h
      exact Or.inl ⟨rfl, treeDist_eq_one_iff.mp h⟩
    · exact Or.inr (Or.inl (isGlue_of_dist_eq_one huv hne p q h))
    · rw [treeDist_comm] at h
      exact Or.inr (Or.inr (isGlue_of_dist_eq_one hvu hne q p h))
    · rw [treeDist_copyAddr_div σ hu hv] at h
      omega
  · rintro (⟨rfl, hadj⟩ | ⟨j, hv, hp, hq⟩ | ⟨j, hu, hq, hp⟩)
    · rw [treeDist_copyAddr_same]
      exact treeDist_eq_one_iff.mpr hadj
    · simp only at hv hp hq
      subst hv
      rw [treeDist_copyAddr_anc σ ⟨[j], rfl⟩ (by simp) p.2, hp, hq]
      simp only [neckSum, treeDist_self, List.length_append, List.length_nil,
        List.length_singleton, Finset.Ico_self, Finset.sum_empty]
      omega
    · simp only at hu hq hp
      subst hu
      rw [treeDist_comm, treeDist_copyAddr_anc σ ⟨[j], rfl⟩ (by simp) q.2, hq, hp]
      simp only [neckSum, treeDist_self, List.length_append, List.length_nil,
        List.length_singleton, Finset.Ico_self, Finset.sum_empty]
      omega

/-! ### The glued transfer -/

variable {σ' : Word → Shape}

/-- **`thm:glued-transfer`**, the glued map: the per-shape maps, copy by
copy. -/
def glue (φ : ∀ w : Word, (shapeSpace (σ w)).carrier → (shapeSpace (σ' w)).carrier)
    (x : Assembly σ) : Assembly σ' := ⟨x.copy, φ x.copy x.vert⟩

/-- **`thm:glued-transfer`**, the neck sums: the comparison of `neck_bounds`,
summed over the intermediate copies. -/
lemma neckSum_bounds {K : ℝ} (hK : 1 ≤ K)
    (hφ : ∀ w, MarkedQI K (shapeSpace (σ w)) (shapeSpace (σ' w))) (a b : ℕ) (v : Word) :
    (∑ i ∈ Finset.Ico a b, ((σ (v.take i)).neckLen : ℝ))
        ≤ 8 * K ^ 2 * ∑ i ∈ Finset.Ico a b, ((σ' (v.take i)).neckLen : ℝ)
      ∧ (∑ i ∈ Finset.Ico a b, ((σ' (v.take i)).neckLen : ℝ))
        ≤ 4 * K * ∑ i ∈ Finset.Ico a b, ((σ (v.take i)).neckLen : ℝ) := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hlen : ∀ τ : Shape, ((τ.neckLen : ℝ)) = (τ.necks : ℝ) + 1 := by
    intro τ; rw [Shape.neckLen]; push_cast; ring
  refine neck_sum_bounds _ hK (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_)
  · exact one_le_neckLen _
  · exact one_le_neckLen _
  · obtain ⟨f, hf⟩ := hφ (v.take i)
    have h := (neck_le_of_markedQI hK0 hf).1
    rw [dist_entry_exit, dist_entry_exit] at h
    rw [hlen, hlen]
    linarith
  · obtain ⟨f, hf⟩ := hφ (v.take i)
    have h := (neck_le_of_markedQI hK0 hf).2
    rw [dist_entry_exit, dist_entry_exit] at h
    rw [hlen, hlen]
    linarith

/-- **`thm:glued-transfer`** for two vertices in the ancestor position: the
glued map transfers the two mark distances and the neck sum of
`eq:assembly-anc`, and every constant fits `8K²`. -/
theorem glue_dist_bounds_anc {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : Word, (shapeSpace (σ w)).carrier → (shapeSpace (σ' w)).carrier}
    (hφ : ∀ w, IsMarkedQI K (shapeSpace (σ w)) (shapeSpace (σ' w)) (φ w))
    {u v : Word} (huv : u <+: v) (hne : u ≠ v)
    (p : (shapeSpace (σ u)).carrier) (q : (shapeSpace (σ v)).carrier) :
    dist (glue φ (⟨u, p⟩ : Assembly σ)) (glue φ ⟨v, q⟩)
          ≤ 8 * K ^ 2 * dist (⟨u, p⟩ : Assembly σ) ⟨v, q⟩ + 8 * K ^ 2
      ∧ dist (⟨u, p⟩ : Assembly σ) ⟨v, q⟩
          ≤ 8 * K ^ 2 * dist (glue φ (⟨u, p⟩ : Assembly σ)) (glue φ ⟨v, q⟩)
            + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hA := dist_mark_bounds hK0 (hφ u) (hφ u).exit p
  have hB := dist_mark_bounds hK0 (hφ v) (hφ v).entry q
  have hN := neckSum_bounds hK (fun w => ⟨φ w, hφ w⟩) (u.length + 1) v.length v
  exact glued_dist_bounds hK dist_nonneg dist_nonneg
    (Finset.sum_nonneg fun i _ => by positivity) dist_nonneg dist_nonneg zero_le_one
    hA.1 hA.2 hB.1 hB.2 hN.2 hN.1 (dist_anc σ huv hne p q) (dist_anc σ' huv hne (φ u p) (φ v q))

/-- **`thm:glued-transfer`** for two vertices in diverging copies: the same
comparison over `eq:assembly-div`, the neck sum now running over both
branches. -/
theorem glue_dist_bounds_div {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : Word, (shapeSpace (σ w)).carrier → (shapeSpace (σ' w)).carrier}
    (hφ : ∀ w, IsMarkedQI K (shapeSpace (σ w)) (shapeSpace (σ' w)) (φ w))
    {u v : Word} (hu : ¬ u <+: v) (hv : ¬ v <+: u)
    (p : (shapeSpace (σ u)).carrier) (q : (shapeSpace (σ v)).carrier) :
    dist (glue φ (⟨u, p⟩ : Assembly σ)) (glue φ ⟨v, q⟩)
          ≤ 8 * K ^ 2 * dist (⟨u, p⟩ : Assembly σ) ⟨v, q⟩ + 8 * K ^ 2
      ∧ dist (⟨u, p⟩ : Assembly σ) ⟨v, q⟩
          ≤ 8 * K ^ 2 * dist (glue φ (⟨u, p⟩ : Assembly σ)) (glue φ ⟨v, q⟩)
            + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hA := dist_mark_bounds hK0 (hφ u) (hφ u).entry p
  have hB := dist_mark_bounds hK0 (hφ v) (hφ v).entry q
  have hNu := neckSum_bounds hK (fun w => ⟨φ w, hφ w⟩) ((wedge u v).length + 1) u.length u
  have hNv := neckSum_bounds hK (fun w => ⟨φ w, hφ w⟩) ((wedge u v).length + 1) v.length v
  refine glued_dist_bounds hK dist_nonneg dist_nonneg (by positivity) dist_nonneg dist_nonneg
    (by norm_num) hA.1 hA.2 hB.1 hB.2 ?_ ?_ (dist_div σ hu hv p q)
    (dist_div σ' hu hv (φ u p) (φ v q))
  · have h1 := hNu.2
    have h2 := hNv.2
    linarith
  · have h1 := hNu.1
    have h2 := hNv.1
    linarith

/-- **`thm:glued-transfer`**, coarse density: every vertex of the target
assembly is within `K` of the image, copy by copy. -/
lemma glue_dense {K : ℝ}
    {φ : ∀ w : Word, (shapeSpace (σ w)).carrier → (shapeSpace (σ' w)).carrier}
    (hφ : ∀ w, IsMarkedQI K (shapeSpace (σ w)) (shapeSpace (σ' w)) (φ w)) (y : Assembly σ') :
    ∃ x : Assembly σ, dist (glue φ x) y ≤ K := by
  obtain ⟨w, r⟩ := y
  obtain ⟨a, ha⟩ := (hφ w).dense r
  refine ⟨⟨w, a⟩, ?_⟩
  have h : dist (glue φ (⟨w, a⟩ : Assembly σ)) (⟨w, r⟩ : Assembly σ')
      = dist (φ w a) r := dist_same σ' w _ _
  rw [h]
  exact ha

/-- **`thm:glued-transfer`**: two families of shapes that are `K`-comparable
copy by copy have `8K²`-quasi-isometric assemblies, the glued map being the
per-shape maps read copy by copy. -/
theorem glued_transfer {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : Word, (shapeSpace (σ w)).carrier → (shapeSpace (σ' w)).carrier}
    (hφ : ∀ w, IsMarkedQI K (shapeSpace (σ w)) (shapeSpace (σ' w)) (φ w)) :
    (∀ x y : Assembly σ, dist (glue φ x) (glue φ y) ≤ 8 * K ^ 2 * dist x y + 8 * K ^ 2)
      ∧ (∀ x y : Assembly σ, dist x y
          ≤ 8 * K ^ 2 * dist (glue φ x) (glue φ y) + (8 * K ^ 2) ^ 2)
      ∧ ∀ y : Assembly σ', ∃ x : Assembly σ, dist (glue φ x) y ≤ 8 * K ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have key : ∀ x y : Assembly σ,
      dist (glue φ x) (glue φ y) ≤ 8 * K ^ 2 * dist x y + 8 * K ^ 2
        ∧ dist x y ≤ 8 * K ^ 2 * dist (glue φ x) (glue φ y) + (8 * K ^ 2) ^ 2 := by
    rintro ⟨u, p⟩ ⟨v, q⟩
    rcases copy_trichotomy u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨hu, hv⟩
    · have e1 : dist (glue φ (⟨u, p⟩ : Assembly σ)) (glue φ ⟨u, q⟩)
          = dist (φ u p) (φ u q) := dist_same σ' u _ _
      have e2 : dist (⟨u, p⟩ : Assembly σ) ⟨u, q⟩ = dist p q := dist_same σ u p q
      rw [e1, e2]
      refine glued_dist_same hK dist_nonneg dist_nonneg ((hφ u).upper p q) ?_
      rw [pow_two]
      exact (hφ u).lower p q
    · exact glue_dist_bounds_anc hK hφ huv hne p q
    · obtain ⟨h1, h2⟩ := glue_dist_bounds_anc hK hφ hvu hne q p
      rw [dist_comm (glue φ (⟨u, p⟩ : Assembly σ)), dist_comm (⟨u, p⟩ : Assembly σ)]
      exact ⟨h1, h2⟩
    · exact glue_dist_bounds_div hK hφ hu hv p q
  refine ⟨fun x y => (key x y).1, fun x y => (key x y).2, fun y => ?_⟩
  obtain ⟨x, hx⟩ := glue_dense hφ y
  exact ⟨x, hx.trans (by nlinarith)⟩

end Assembly

end ChainClasses
