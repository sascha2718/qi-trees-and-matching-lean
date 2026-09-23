import Mathlib.Tactic
import ChainClasses.Chain.Encoding
import ChainClasses.Chain.Labelling
import ChainClasses.Chain.Transfer
import BranchingProcess.Geometry

/-!
The bridge between the two settings in which this project speaks of
quasi-isometries: subsets of the ambient tree of words, carrying `treeDist`,
and Mathlib's `SimpleGraph` with its graph metric.

* `PrefixClosed`: a set of words closed under taking prefixes, the vertex set
  of a subtree of the ambient tree; `InTree` and `InAssoc` are two.
* `wordGraph T`: the parent-child graph on such a set, with adjacency
  `treeDist = 1`.
* `wordGraph_dist`: its graph metric is `treeDist`.
* `wordGraph_connected`, `wordGraph_isBridge`, `wordGraph_isTree`: it is a
  tree, the acyclicity coming from the descendants of a vertex being separated
  from the rest by the edge above it.
* `isQIWith_wordGraph`: a `ChainClasses.IsQIWith` between two such sets is a
  `BranchingProcess.IsQIWith` between their graphs, so the obstructions of
  `BranchingProcess.Geometry` apply to the sample trees of `sec:encoding`.
-/

namespace ChainClasses

open SimpleGraph

/-! ### Prefix-closed sets of words -/

/-- A set of words closed under taking prefixes: the vertex set of a subtree
of the ambient tree. -/
def PrefixClosed (T : Word → Prop) : Prop := ∀ ⦃u v : Word⦄, u <+: v → T v → T u

variable {T T' : Word → Prop}

/-- A nonempty prefix-closed set contains the root. -/
lemma PrefixClosed.nil (hT : PrefixClosed T) {v : Word} (hv : T v) : T [] :=
  hT List.nil_prefix hv

/-- The parent of a vertex of a prefix-closed set is one of its vertices. -/
lemma PrefixClosed.dropLast (hT : PrefixClosed T) {v : Word} (hv : T v) : T v.dropLast :=
  hT v.dropLast_prefix hv

/-- The sample tree of an offspring field is prefix-closed. -/
lemma prefixClosed_inTree (χ : Word → Bool) : PrefixClosed (InTree χ) := by
  intro u v huv hv
  induction hv generalizing u with
  | root =>
      rw [List.prefix_nil.mp huv]
      exact InTree.root
  | @one w _ ih =>
      rcases eq_or_ne u (w ++ [false]) with rfl | hne
      · exact InTree.one (by assumption)
      · exact ih (by
          have := (List.prefix_concat_iff).mp huv
          tauto)
  | @two w _ hχ ih =>
      rcases eq_or_ne u (w ++ [true]) with rfl | hne
      · exact InTree.two (by assumption) hχ
      · exact ih (by
          have := (List.prefix_concat_iff).mp huv
          tauto)

/-! ### The graph of a set of words -/

/-- The parent-child graph on a set of words: two vertices are adjacent when
one is the other extended by a letter, which `treeDist_eq_one_iff` reads off
the metric. -/
def wordGraph (T : Word → Prop) : SimpleGraph {w : Word // T w} where
  Adj u v := treeDist u.1 v.1 = 1
  symm := ⟨fun {_ _} h => by rwa [treeDist_comm]⟩
  loopless := ⟨fun {u} h => by
    rw [treeDist_self] at h
    exact absurd h (by omega)⟩

@[simp] lemma wordGraph_adj {u v : {w : Word // T w}} :
    (wordGraph T).Adj u v ↔ treeDist u.1 v.1 = 1 := Iff.rfl

/-- A vertex and its child are adjacent. -/
lemma wordGraph_adj_concat {u v : {w : Word // T w}} {b : Bool} (h : v.1 = u.1 ++ [b]) :
    (wordGraph T).Adj u v :=
  treeDist_eq_one_iff.mpr (Or.inl ⟨b, h⟩)

/-! ### The graph metric is `treeDist` -/

/-- Walking up to an ancestor: a vertex and a prefix of it are joined by a walk
of length the difference of the depths. -/
lemma exists_walk_of_prefix (hT : PrefixClosed T) :
    ∀ (n : ℕ) (u v : {w : Word // T w}), u.1 <+: v.1 → v.1.length - u.1.length = n →
      ∃ p : (wordGraph T).Walk u v, p.length = n := by
  intro n
  induction n with
  | zero =>
      intro u v huv hlen
      have : u = v := Subtype.ext (huv.eq_of_length (by have := huv.length_le; omega))
      subst this
      exact ⟨Walk.nil, rfl⟩
  | succ n ih =>
      intro u v huv hlen
      have hvne : v.1 ≠ [] := by
        intro h
        rw [h] at hlen
        simp at hlen
      obtain ⟨b, s, hs⟩ : ∃ (b : Bool) (s : Word), v.1 = s ++ [b] := by
        rcases List.eq_nil_or_concat v.1 with h | ⟨s, b, hs⟩
        · exact absurd h hvne
        · exact ⟨b, s, by rw [hs]; simp⟩
      have hsT : T s := hT (hs ▸ List.prefix_append s [b]) v.2
      have hslen : s.length + 1 = v.1.length := by
        rw [hs]; simp
      have hus : u.1 <+: s := by
        refine prefix_of_prefix_of_length_le huv (hs ▸ List.prefix_append s [b]) ?_
        omega
      obtain ⟨p, hp⟩ := ih u ⟨s, hsT⟩ hus (by simp only; omega)
      exact ⟨p.concat (wordGraph_adj_concat (T := T) (u := ⟨s, hsT⟩) (v := v) hs),
        by rw [Walk.length_concat, hp]⟩

/-- The wedge of two vertices is a vertex. -/
lemma wedge_mem (hT : PrefixClosed T) {u v : Word} (hu : T u) : T (wedge u v) :=
  hT (wedge_prefix_left u v) hu

/-- `treeDist` is subadditive along a walk: every edge changes it by at most
one. -/
lemma treeDist_le_walk_length {u v : {w : Word // T w}} (p : (wordGraph T).Walk u v) :
    treeDist u.1 v.1 ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab _ ih =>
      have h1 : treeDist a.1 b.1 = 1 := hab
      have := treeDist_triangle a.1 b.1 c.1
      simp only [Walk.length_cons]
      omega

/-- **The graph metric of `wordGraph` is `treeDist`.** -/
theorem wordGraph_dist (hT : PrefixClosed T) (u v : {w : Word // T w}) :
    (wordGraph T).dist u v = treeDist u.1 v.1 := by
  have hw : T (wedge u.1 v.1) := wedge_mem hT u.2
  obtain ⟨p, hp⟩ := exists_walk_of_prefix hT (u.1.length - (wedge u.1 v.1).length)
    ⟨wedge u.1 v.1, hw⟩ u (wedge_prefix_left u.1 v.1) rfl
  obtain ⟨q, hq⟩ := exists_walk_of_prefix hT (v.1.length - (wedge u.1 v.1).length)
    ⟨wedge u.1 v.1, hw⟩ v (wedge_prefix_right u.1 v.1) rfl
  have hle : (wordGraph T).dist u v ≤ treeDist u.1 v.1 := by
    have h := dist_le (p.reverse.append q)
    rw [Walk.length_append, Walk.length_reverse, hp, hq] at h
    have h1 := wedge_length_le_left u.1 v.1
    have h2 := wedge_length_le_right u.1 v.1
    have h3 := treeDist_add_wedge_length u.1 v.1
    omega
  refine le_antisymm hle ?_
  have hr : (wordGraph T).Reachable u v := ⟨p.reverse.append q⟩
  obtain ⟨r, hr'⟩ := hr.exists_walk_length_eq_dist
  have := treeDist_le_walk_length r
  omega

/-- **The graph of a nonempty prefix-closed set is connected.** -/
theorem wordGraph_connected (hT : PrefixClosed T) (hne : Nonempty {w : Word // T w}) :
    (wordGraph T).Connected := by
  obtain ⟨v0⟩ := hne
  have : Nonempty {w : Word // T w} := ⟨v0⟩
  refine ⟨fun u v => ?_⟩
  have hw : T (wedge u.1 v.1) := wedge_mem hT u.2
  obtain ⟨p, -⟩ := exists_walk_of_prefix hT (u.1.length - (wedge u.1 v.1).length)
    ⟨wedge u.1 v.1, hw⟩ u (wedge_prefix_left u.1 v.1) rfl
  obtain ⟨q, -⟩ := exists_walk_of_prefix hT (v.1.length - (wedge u.1 v.1).length)
    ⟨wedge u.1 v.1, hw⟩ v (wedge_prefix_right u.1 v.1) rfl
  exact ⟨p.reverse.append q⟩

/-! ### Acyclicity -/

/-- The descendants of a vertex are separated from the rest by the edge above
it: an edge of the graph joining a descendant of `y` to a nondescendant is the
edge from `y` to its parent. -/
lemma eq_of_adj_of_prefix {x y z z' : {w : Word // T w}} {b : Bool} (hxy : y.1 = x.1 ++ [b])
    (hz : y.1 <+: z.1) (hz' : ¬ y.1 <+: z'.1) (hadj : (wordGraph T).Adj z z') :
    z = y ∧ z' = x := by
  rcases treeDist_eq_one_iff.mp hadj with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact absurd (hc ▸ hz.trans (List.prefix_append z.1 [c])) hz'
  · have hz'p : z'.1 <+: z.1 := hc ▸ List.prefix_append z'.1 [c]
    have hlen : z.1.length = z'.1.length + 1 := by rw [hc]; simp
    have hylen : z'.1.length < y.1.length := by
      by_contra hcon
      exact hz' (prefix_of_prefix_of_length_le hz hz'p (by omega))
    have hyz : y.1.length = z.1.length := by have := hz.length_le; omega
    have hzy : z.1 = y.1 := (hz.eq_of_length hyz).symm
    have hzx : z'.1 = x.1 := by
      have : z'.1 ++ [c] = x.1 ++ [b] := by rw [← hc, hzy, hxy]
      exact (List.append_inj this (by
        have hxlen : x.1.length + 1 = y.1.length := by rw [hxy]; simp
        omega)).1
    exact ⟨Subtype.ext hzy, Subtype.ext hzx⟩

/-- Walks in the graph with the edge above `y` removed stay among the
descendants of `y` once they start there. -/
lemma prefix_of_walk_deleteEdges {x y : {w : Word // T w}} {b : Bool} (hxy : y.1 = x.1 ++ [b])
    {z z' : {w : Word // T w}} (p : ((wordGraph T).deleteEdges {s(x, y)}).Walk z z')
    (hz : y.1 <+: z.1) : y.1 <+: z'.1 := by
  induction p with
  | nil => exact hz
  | @cons a c d hac _ ih =>
      refine ih ?_
      by_contra hcon
      rw [deleteEdges_adj] at hac
      obtain ⟨rfl, rfl⟩ := eq_of_adj_of_prefix hxy hz hcon hac.1
      exact hac.2 (by simp [Sym2.eq_swap])

/-- **Every edge is a bridge**: deleting the edge above `y` separates the
descendants of `y` from its parent. -/
theorem wordGraph_isBridge {u v : {w : Word // T w}} (h : (wordGraph T).Adj u v) :
    (wordGraph T).IsBridge s(u, v) := by
  -- reduce to the case where `v` is the child
  suffices hkey : ∀ x y : {w : Word // T w}, (∃ b, y.1 = x.1 ++ [b]) →
      (wordGraph T).IsBridge s(x, y) by
    rcases treeDist_eq_one_iff.mp h with hb | hb
    · exact hkey u v hb
    · rw [Sym2.eq_swap]
      exact hkey v u hb
  rintro x y ⟨b, hxy⟩
  rw [isBridge_iff]
  rintro ⟨p⟩
  have hx : ¬ y.1 <+: x.1 := by
    intro hcon
    have := hcon.length_le
    rw [hxy] at this
    simp at this
  exact hx (prefix_of_walk_deleteEdges hxy p.reverse (List.prefix_refl _))

/-- **The graph of a nonempty prefix-closed set is a tree.** -/
theorem wordGraph_isTree (hT : PrefixClosed T) (hne : Nonempty {w : Word // T w}) :
    (wordGraph T).IsTree where
  connected := wordGraph_connected hT hne
  isAcyclic := isAcyclic_iff_forall_adj_isBridge.mpr fun _ _ h => wordGraph_isBridge h

/-! ### Transporting quasi-isometries -/

/-- The restriction of a map of words to the vertex set it preserves. -/
def restrictQI {K : ℕ} {f : Word → Word} (h : IsQIWith K T T' f) :
    {w : Word // T w} → {w : Word // T' w} := fun u => ⟨f u.1, h.maps u.1 u.2⟩

@[simp] lemma restrictQI_val {K : ℕ} {f : Word → Word} (h : IsQIWith K T T' f)
    (u : {w : Word // T w}) : (restrictQI h u).1 = f u.1 := rfl

/-- **The bridge.** A `K`-quasi-isometry of word sets in the sense of
`thm:transfer` is a `K`-quasi-isometry of their graphs in the sense of
`def:qi`, so `thm:tree-stability`, `thm:bush-separation` and
`thm:three-rays` apply to the trees of `sec:encoding`. -/
theorem isQIWith_wordGraph (hT : PrefixClosed T) (hT' : PrefixClosed T') {K : ℕ}
    {f : Word → Word} (h : IsQIWith K T T' f) :
    BranchingProcess.IsQIWith K (wordGraph T) (wordGraph T') (restrictQI h) where
  upper x y := by
    rw [wordGraph_dist hT' _ _, wordGraph_dist hT _ _]
    exact h.upper x.1 y.1 x.2 y.2
  lower x y := by
    rw [wordGraph_dist hT' _ _, wordGraph_dist hT _ _]
    exact h.lower x.1 y.1 x.2 y.2
  dense y' := by
    obtain ⟨x, hx, hdist⟩ := h.dense y'.1 y'.2
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [wordGraph_dist hT' _ _]
    exact hdist

/-- **The bridge, as quasi-isometry of graphs.** -/
theorem quasiIsometric_wordGraph (hT : PrefixClosed T) (hT' : PrefixClosed T') {K : ℕ}
    {f : Word → Word} (h : IsQIWith K T T' f) :
    BranchingProcess.QuasiIsometric (wordGraph T) (wordGraph T') :=
  ⟨K, restrictQI h, isQIWith_wordGraph hT hT' h⟩

open Classical in
/-- **The bridge, read backwards.** A quasi-isometry of the graphs is one of
the word sets, totalised off the source by the identity, so an obstruction
proved for word sets obstructs the graphs. -/
theorem isQIWith_of_wordGraph (hT : PrefixClosed T) (hT' : PrefixClosed T') {K : ℕ}
    {g : {w : Word // T w} → {w : Word // T' w}}
    (h : BranchingProcess.IsQIWith K (wordGraph T) (wordGraph T') g) :
    IsQIWith K T T' (fun x => if hx : T x then (g ⟨x, hx⟩).1 else x) where
  maps x hx := by
    rw [dite_eq_left hx]
    exact (g ⟨x, hx⟩).2
  upper x y hx hy := by
    rw [dite_eq_left hx, dite_eq_left hy]
    have := h.upper ⟨x, hx⟩ ⟨y, hy⟩
    rwa [wordGraph_dist hT' _ _, wordGraph_dist hT _ _] at this
  lower x y hx hy := by
    rw [dite_eq_left hx, dite_eq_left hy]
    have := h.lower ⟨x, hx⟩ ⟨y, hy⟩
    rwa [wordGraph_dist hT' _ _, wordGraph_dist hT _ _] at this
  dense y' hy' := by
    obtain ⟨x, hx⟩ := h.dense ⟨y', hy'⟩
    rw [wordGraph_dist hT' _ _] at hx
    exact ⟨x.1, x.2, by rw [dite_eq_left x.2]; exact hx⟩

/-- **The obstruction transfers.** If no map of word sets is a quasi-isometry,
then the graphs are not quasi-isometric. -/
theorem not_quasiIsometric_of_not_isQIWith (hT : PrefixClosed T) (hT' : PrefixClosed T')
    (h : ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K T T' f) :
    ¬ BranchingProcess.QuasiIsometric (wordGraph T) (wordGraph T') := by
  rintro ⟨K, g, hg⟩
  exact h ⟨K, _, isQIWith_of_wordGraph hT hT' hg⟩

/-- The whole ambient tree is prefix-closed: the binary tree `𝔹`. -/
lemma prefixClosed_true : PrefixClosed (fun _ : Word => True) := fun _ _ _ _ => trivial

end ChainClasses
