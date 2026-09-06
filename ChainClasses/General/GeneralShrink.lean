import ChainClasses.General.GeneralShapeShrink
import ChainClasses.General.GeneralShapeMass
import ChainClasses.Shape.AddrMetric

/-!
`thm:shape-shrink` of `gw_classes_simple.tex` at general arity, the moves after the
contraction: the shrinking pipeline `sec:general-transfer` of
`matching_classes_general.tex` needs in the proof of `thm:relabel`, as a function of an
arbitrary marked rose tree.

A marked rose tree is binarised by the left-child right-sibling encoding, the
root-to-mark path of the binary tree becomes the neck of a shape, and the shape is
padded with one-vertex bushes into the support of the law.  Each move is an address map
with a retraction, and one lemma turns such a pair into a marked quasi-isometry once
the two maps send parent-child pairs to pairs at bounded distance: the graph metric of
a rose tree is the address metric `addrDist` of `AddrMetric.lean`, so every distance
bound is a computation on words.

* `RTree.dist_gSpace_eq_addrDist`: the metric of a marked rose tree, on addresses.
* `RTree.dist_lt_size`, `gOne`, `markedQI_gCollapse`, `markedQI_gSmallPair`: the
  diameter of a rose tree is below its size, and **the collapse** of small shapes,
  two shapes of size at most `N` being `N`-comparable.
* `dist_le_mul_dist_of_adj`, `markedQI_gSpace_of_addrMaps`: **the quasi-isometry from
  an address map and a retraction** that both move parent-child pairs by at most `K`.
* `RTree.lcrs`, `RTree.lcrsAddr`, `markedQI_lcrs`: **`thm:shape-shrink`
  (`it:shape-shrink`), the binarisation** at general arity: the first child at
  index `0`, the next sibling at the index after the children, a bijection on
  vertices, a `(d+1)`-marked quasi-isometry under the offspring bound `d`.
* `gNeckShape`, `markedQI_gNeck`, `size_gNeckShape_le`, `bouquet_gNeckShape`,
  `gNeckShape_neckList_degLe_two`: **the neck construction**, the root-to-mark path as
  the neck, the children of the mark under one joint vertex, a fresh exit below the mark
  with empty bouquet, a `2`-marked quasi-isometry adding at most two vertices.
* `gPad`, `markedQI_gPad`, `size_gPad_le`, `chargedG_gPad`: **the support fix**, every
  neck vertex padded to `k-1` bushes and every bush vertex to `0` or `k` children, a
  `1`-marked quasi-isometry into the support of the law at arity `k`.
* `gShrinkOf`, `markedQI_gShrinkOf`, `size_gShrinkOf_le`, `chargedG_gShrinkOf`: **the
  composition**, an `18(d+1)`-marked quasi-isometry onto a charged shape of size at
  most `k(|t| + 2)`.
-/

namespace ChainClasses

open RTree

namespace RTree

/-! ### The metric of a marked rose tree on addresses -/

/-- The metric of a marked rose tree, on addresses. -/
lemma dist_gSpace_eq_addrDist {t : RTree} {e : List ℕ} (x y : (gSpace t e).carrier) :
    dist x y = (addrDist x.1 y.1 : ℝ) := by
  rw [dist_gSpace, rtreeGraph_dist]

/-! ### The diameter of a rose tree -/

instance instFintypeVert (t : RTree) : Fintype (Vert t) := List.Subtype.fintype (addrList t)

/-- The vertices are counted by the size. -/
lemma card_vert (t : RTree) : Fintype.card (Vert t) = t.size := by
  show Fintype.card {w // w ∈ addrList t} = t.size
  rw [Fintype.card_of_subtype (addrList t).toFinset (fun w => List.mem_toFinset),
    List.toFinset_card_of_nodup (nodup_addrList t), length_addrList]

/-- **The diameter of a rose tree is below its size**: a shortest walk is a path, and a
path visits each vertex at most once. -/
theorem dist_lt_size {t : RTree} (x y : Vert t) : (rtreeGraph t).dist x y < t.size := by
  obtain ⟨p, hp, hlen⟩ := (rtreeGraph_connected t).exists_path_of_dist x y
  have := hp.length_lt
  rw [card_vert] at this
  omega

end RTree

/-! ### The collapse of small shapes -/

/-- The one-vertex shape: a bare split with no bushes. -/
def gOne : GShape := ⟨0, fun _ => []⟩

/-- The one-vertex shape has a single vertex. -/
instance : Subsingleton (gShapeSpace gOne).carrier := by
  refine ⟨fun u v => Subtype.ext ?_⟩
  have hu : u.1 ∈ addrList (RTree.node []) := u.2
  have hv : v.1 ∈ addrList (RTree.node []) := v.2
  simp only [addrList_node, addrListF_nil, List.mem_singleton] at hu hv
  rw [hu, hv]

/-- The distance of two vertices of a shape is below its size. -/
lemma dist_lt_gSize (σ : GShape) (x y : (gShapeSpace σ).carrier) :
    dist x y < (σ.size : ℝ) := by
  have h : dist x y = ((rtreeGraph σ.realise).dist x y : ℝ) := rfl
  rw [h]
  exact_mod_cast RTree.dist_lt_size x y

/-- **The collapse**: a shape of size at most `N` is `N`-comparable to the one-vertex
shape. -/
theorem markedQI_gCollapse {N : ℝ} (hN : 1 ≤ N) (σ : GShape) (hσ : (σ.size : ℝ) ≤ N) :
    MarkedQI N (gShapeSpace σ) (gShapeSpace gOne) := by
  refine markedQI_of_subsingleton hN fun a b => ?_
  have h := (dist_lt_gSize σ a b).le.trans hσ
  nlinarith

/-- **The small-pair collapse**: two shapes of size at most `N` are `N`-comparable,
every vertex of the first being sent to the root of the second. -/
theorem markedQI_gSmallPair {N : ℝ} (hN : 1 ≤ N) (σ τ : GShape)
    (hσ : (σ.size : ℝ) ≤ N) (hτ : (τ.size : ℝ) ≤ N) :
    MarkedQI N (gShapeSpace σ) (gShapeSpace τ) := by
  have hN0 : (0 : ℝ) ≤ N := zero_le_one.trans hN
  refine ⟨fun _ => (gShapeSpace τ).entry, fun a b => ?_, fun a b => ?_, fun y => ?_, ?_, ?_⟩
  · rw [dist_self]
    nlinarith [dist_nonneg (x := a) (y := b)]
  · rw [dist_self, mul_zero, zero_add]
    have h := (dist_lt_gSize σ a b).le.trans hσ
    nlinarith
  · refine ⟨(gShapeSpace σ).entry, ?_⟩
    exact (dist_lt_gSize τ _ y).le.trans hτ
  · rw [dist_self]
    exact hN0
  · exact (dist_lt_gSize τ _ _).le.trans hτ

/-! ### Quasi-isometries from address maps -/

/-- A map sending edges to pairs at distance at most `K` stretches distances by at
most `K`. -/
lemma dist_le_mul_dist_of_adj {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}
    {f : V → V'} {K : ℕ} (hf : ∀ u v, G.Adj u v → G'.dist (f u) (f v) ≤ K)
    (hG : G.Connected) (hG' : G'.Connected) (x y : V) :
    G'.dist (f x) (f y) ≤ K * G.dist x y := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
  rw [← hp]
  clear hp
  induction p with
  | nil => simp
  | cons h p ih =>
      rename_i u v w
      rw [SimpleGraph.Walk.length_cons, Nat.mul_succ]
      have h1 := hG'.dist_triangle (u := f u) (v := f v) (w := f w)
      have h2 := hf _ _ h
      omega

/-- An address map with a retraction, both moving parent-child pairs by at most `K`,
is a `K`-marked quasi-isometry of the marked rose trees once it respects the marks up
to `K`. -/
theorem markedQI_gSpace_of_addrMaps {t t' : RTree} {e e' : List ℕ} {K : ℕ} (hK : 1 ≤ K)
    (f g : List ℕ → List ℕ)
    (hf : ∀ w, IsAddr t w → IsAddr t' (f w))
    (hg : ∀ y, IsAddr t' y → IsAddr t (g y))
    (hfadj : ∀ u a, IsAddr t (u ++ [a]) → addrDist (f (u ++ [a])) (f u) ≤ K)
    (hgadj : ∀ y b, IsAddr t' (y ++ [b]) → addrDist (g (y ++ [b])) (g y) ≤ K)
    (hgf : ∀ w, IsAddr t w → g (f w) = w)
    (hfg : ∀ y, IsAddr t' y → addrDist (f (g y)) y ≤ K)
    (hroot : addrDist (f []) [] ≤ K)
    (he : IsAddr t e) (he' : IsAddr t' e') (hexit : addrDist (f e) e' ≤ K) :
    MarkedQI (K : ℝ) (gSpace t e) (gSpace t' e') := by
  have hK0 : (0 : ℝ) ≤ K := by exact_mod_cast (zero_le_one.trans hK)
  set F : Vert t → Vert t' := fun x => ⟨f x.1, mem_addrList_iff.mpr (hf _ (mem_addrList_iff.mp x.2))⟩
    with hF
  set G : Vert t' → Vert t := fun y => ⟨g y.1, mem_addrList_iff.mpr (hg _ (mem_addrList_iff.mp y.2))⟩
    with hG
  -- parent-child pairs go to pairs at distance at most `K`
  have hadj : ∀ (s : RTree) (h : List ℕ → List ℕ) (u v : Vert s),
      (∀ w a, IsAddr s (w ++ [a]) → addrDist (h (w ++ [a])) (h w) ≤ K) →
      (rtreeGraph s).Adj u v → addrDist (h u.1) (h v.1) ≤ K := by
    intro s h u v hh huv
    rw [rtreeGraph_adj] at huv
    obtain ⟨hne, hrel⟩ := huv
    have key : ∀ x y : Vert s, x ≠ y → y.1 = x.1.dropLast → addrDist (h x.1) (h y.1) ≤ K := by
      intro x y hxy hyx
      have hx : x.1 ≠ [] := by
        intro hc
        exact hxy (Subtype.ext (by rw [hyx, hc]; simp))
      have hx' : x.1 = x.1.dropLast ++ [x.1.getLast hx] := (List.dropLast_append_getLast hx).symm
      have := hh x.1.dropLast (x.1.getLast hx) (by rw [← hx']; exact mem_addrList_iff.mp x.2)
      rw [hyx]
      convert this using 3
    rcases hrel with h1 | h1
    · rw [addrDist_comm]
      exact key v u hne.symm h1
    · exact key u v hne h1
  have hFadj : ∀ u v, (rtreeGraph t).Adj u v → (rtreeGraph t').dist (F u) (F v) ≤ K := by
    intro u v huv
    rw [rtreeGraph_dist]
    exact hadj t f u v hfadj huv
  have hGadj : ∀ u v, (rtreeGraph t').Adj u v → (rtreeGraph t).dist (G u) (G v) ≤ K := by
    intro u v huv
    rw [rtreeGraph_dist]
    exact hadj t' g u v hgadj huv
  have hFdist : ∀ x y : Vert t, (rtreeGraph t').dist (F x) (F y) ≤ K * (rtreeGraph t).dist x y :=
    dist_le_mul_dist_of_adj hFadj (rtreeGraph_connected t) (rtreeGraph_connected t')
  have hGdist : ∀ x y : Vert t', (rtreeGraph t).dist (G x) (G y) ≤ K * (rtreeGraph t').dist x y :=
    dist_le_mul_dist_of_adj hGadj (rtreeGraph_connected t') (rtreeGraph_connected t)
  have hGF : ∀ x : Vert t, G (F x) = x := fun x =>
    Subtype.ext (hgf x.1 (mem_addrList_iff.mp x.2))
  refine ⟨F, fun a b => ?_, fun a b => ?_, fun y => ⟨G y, ?_⟩, ?_, ?_⟩
  · rw [dist_gSpace, dist_gSpace]
    have h := hFdist a b
    have h' : ((rtreeGraph t').dist (F a) (F b) : ℝ) ≤ K * (rtreeGraph t).dist a b := by
      exact_mod_cast h
    linarith
  · rw [dist_gSpace, dist_gSpace]
    have h := hGdist (F a) (F b)
    rw [hGF, hGF] at h
    have h' : ((rtreeGraph t).dist a b : ℝ) ≤ K * (rtreeGraph t').dist (F a) (F b) := by
      exact_mod_cast h
    nlinarith
  · rw [dist_gSpace_eq_addrDist]
    exact_mod_cast hfg y.1 (mem_addrList_iff.mp y.2)
  · rw [dist_gSpace_eq_addrDist]
    exact_mod_cast hroot
  · rw [exit_gSpace_of_mem (mem_addrList_iff.mpr he), exit_gSpace_of_mem (mem_addrList_iff.mpr he'),
      dist_gSpace_eq_addrDist]
    exact_mod_cast hexit

/-! ### Addresses of a widened node -/

/-- An address below the root of a node with a last child reads a bush or the last
child. -/
lemma isAddr_node_append_single {β : List RTree} {R : RTree} {k : ℕ} {z : List ℕ} :
    IsAddr (.node (β ++ [R])) (k :: z) ↔
      (∃ h : k < β.length, IsAddr β[k] z) ∨ (k = β.length ∧ IsAddr R z) := by
  rcases lt_trichotomy k β.length with hk | rfl | hk
  · rw [isAddr_append_last_lt hk, isAddr_cons]
    constructor
    · rintro ⟨h, hz⟩
      exact Or.inl ⟨h, hz⟩
    · rintro (⟨h, hz⟩ | ⟨h, -⟩)
      · exact ⟨h, hz⟩
      · omega
  · rw [isAddr_append_last_eq]
    constructor
    · intro h
      exact Or.inr ⟨rfl, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · omega
      · exact h
  · constructor
    · intro h
      exact absurd h (not_isAddr_of_length_le
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega

/-- The single vertex carries only the empty address. -/
lemma isAddr_node_nil_iff {z : List ℕ} : IsAddr (.node []) z ↔ z = [] := by
  cases z with
  | nil => simp
  | cons k z =>
      rw [isAddr_cons]
      simp

/-- The realisation of a bush list with a nonempty tail. -/
lemma realiseAux_cons_of_ne_nil (β : List RTree) {L : List (List RTree)} (hL : L ≠ []) :
    GShape.realiseAux (β :: L) = .node (β ++ [GShape.realiseAux L]) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons r rest => rfl

/-- The default read of a list inside its length. -/
lemma getD_eq_getElem_of_lt {cs : List RTree} {j : ℕ} (hj : j < cs.length) :
    cs.getD j (.node []) = cs[j] := List.getD_eq_getElem cs _ hj

/-- Erasing one tree of a forest removes exactly its vertices. -/
lemma sizeF_eraseIdx_add {cs : List RTree} {j : ℕ} (hj : j < cs.length) :
    RTree.sizeF (cs.eraseIdx j) + cs[j].size = RTree.sizeF cs := by
  conv_rhs => rw [← List.take_append_drop j cs, List.drop_eq_getElem_cons hj]
  rw [List.eraseIdx_eq_take_drop_succ, RTree.sizeF_append, RTree.sizeF_append, RTree.sizeF_cons]
  omega

/-! ### The neck construction -/

/-- **The neck construction, the bush lists**: each vertex of the root-to-mark path
passes on its other children as its bushes, the mark passes on its children under one
joint vertex, and the neck runs one vertex further, to a fresh exit with empty
bouquet. -/
def gNeckList : RTree → List ℕ → List (List RTree)
  | .node cs, [] => [[.node cs], []]
  | .node cs, j :: v => cs.eraseIdx j :: gNeckList (cs.getD j (.node [])) v

@[simp] lemma gNeckList_nil (cs : List RTree) :
    gNeckList (.node cs) [] = [[.node cs], []] := rfl

@[simp] lemma gNeckList_cons (cs : List RTree) (j : ℕ) (v : List ℕ) :
    gNeckList (.node cs) (j :: v) = cs.eraseIdx j :: gNeckList (cs.getD j (.node [])) v := rfl

lemma gNeckList_ne_nil (t : RTree) (e : List ℕ) : gNeckList t e ≠ [] := by
  cases t; cases e <;> simp

/-- The neck construction ends with the empty bouquet. -/
lemma gNeckList_eq_append : ∀ (t : RTree) (e : List ℕ),
    ∃ L, gNeckList t e = L ++ [([] : List RTree)]
  | .node cs, [] => ⟨[[.node cs]], rfl⟩
  | .node cs, j :: v => by
      obtain ⟨L, hL⟩ := gNeckList_eq_append (cs.getD j (.node [])) v
      exact ⟨cs.eraseIdx j :: L, by rw [gNeckList_cons, hL, List.cons_append]⟩

/-- **The neck construction**: the shape of a marked rose tree. -/
def gNeckShape (t : RTree) (e : List ℕ) : GShape := gOfList (gNeckList t e)

lemma decs_gNeckShape (t : RTree) (e : List ℕ) : (gNeckShape t e).decs = gNeckList t e :=
  decs_gOfList (gNeckList_ne_nil t e)

/-- The fresh exit carries no bouquet. -/
theorem bouquet_gNeckShape (t : RTree) (e : List ℕ) : (gNeckShape t e).bouquet = [] := by
  obtain ⟨L, hL⟩ := gNeckList_eq_append t e
  have h := (gNeckShape t e).decs_eq_append
  rw [decs_gNeckShape, hL] at h
  have h2 := List.append_inj_right' h.symm (by simp)
  simpa using h2

/-- The marked space of the neck construction, on the bush lists. -/
lemma gShapeSpace_gNeckShape (t : RTree) (e : List ℕ) :
    gShapeSpace (gNeckShape t e)
      = gSpace (GShape.realiseAux (gNeckList t e)) (gExitAddr (gNeckList t e)) := by
  rw [gShapeSpace, GShape.realise, GShape.exitAddr, decs_gNeckShape]

/-- **The size of the neck construction**: the joint vertex and the fresh exit. -/
theorem size_realiseAux_gNeckList : ∀ (t : RTree) (e : List ℕ), IsAddr t e →
    (GShape.realiseAux (gNeckList t e)).size ≤ t.size + 2
  | .node cs, [], _ => by
      rw [gNeckList_nil, realiseAux_cons_of_ne_nil _ (by simp)]
      simp [GShape.realiseAux]
      omega
  | .node cs, j :: v, he => by
      rw [isAddr_cons] at he
      obtain ⟨hj, hv⟩ := he
      have ih := size_realiseAux_gNeckList cs[j] v hv
      rw [gNeckList_cons, getD_eq_getElem_of_lt hj,
        realiseAux_cons_of_ne_nil _ (gNeckList_ne_nil _ _), RTree.size_node,
        RTree.sizeF_append, RTree.sizeF_cons, RTree.sizeF_nil, RTree.size_node]
      have := sizeF_eraseIdx_add hj
      omega

theorem size_gNeckShape_le {t : RTree} {e : List ℕ} (he : IsAddr t e) :
    (gNeckShape t e).size ≤ t.size + 2 := by
  show (gNeckShape t e).realise.size ≤ t.size + 2
  rw [GShape.realise, decs_gNeckShape]
  exact size_realiseAux_gNeckList t e he

/-- Under the binary bound every neck vertex has at most one bush and every bush is
binary. -/
theorem gNeckList_degLe_two : ∀ (t : RTree) (e : List ℕ), IsAddr t e → DegLe 2 t →
    ∀ β ∈ gNeckList t e, β.length ≤ 1 ∧ ∀ b ∈ β, DegLe 2 b
  | .node cs, [], _, ht, β, hβ => by
      rw [gNeckList_nil] at hβ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
      rcases hβ with rfl | rfl
      · exact ⟨by simp, fun b hb => by rw [List.mem_singleton.mp hb]; exact ht⟩
      · simp
  | .node cs, j :: v, he, ht, β, hβ => by
      rw [isAddr_cons] at he
      obtain ⟨hj, hv⟩ := he
      obtain ⟨hlen, hall⟩ := ht
      rw [gNeckList_cons, getD_eq_getElem_of_lt hj, List.mem_cons] at hβ
      rcases hβ with rfl | hβ
      · refine ⟨?_, fun b hb => hall b (List.mem_of_mem_eraseIdx hb)⟩
        rw [List.length_eraseIdx_of_lt hj]
        omega
      · exact gNeckList_degLe_two cs[j] v hv (hall _ (List.getElem_mem hj)) β hβ

theorem gNeckShape_neckList_degLe_two {t : RTree} {e : List ℕ} (he : IsAddr t e)
    (ht : DegLe 2 t) :
    ∀ β ∈ (gNeckShape t e).neckList, β.length ≤ 1 ∧ ∀ b ∈ β, DegLe 2 b := by
  intro β hβ
  refine gNeckList_degLe_two t e he ht β ?_
  rw [← decs_gNeckShape, (gNeckShape t e).decs_eq_append]
  exact List.mem_append_left _ hβ

/-! ### The address map of the neck construction -/

/-- **The address map of the neck construction**: a vertex of the root-to-mark path
keeps its place on the neck, its other children move to the bush slots, and the
subtrees at the mark descend one step under the joint vertex. -/
def gNeckMap : RTree → List ℕ → List ℕ → List ℕ
  | .node _, [], [] => []
  | .node _, [], k :: z => 0 :: k :: z
  | .node _, _ :: _, [] => []
  | .node cs, j :: v, k :: z =>
      if k = j then (cs.length - 1) :: gNeckMap (cs.getD j (.node [])) v z
      else if k < j then k :: z else (k - 1) :: z

/-- The retraction of the neck construction: the joint vertex and the fresh exit go to
the mark, every other vertex to the vertex it came from. -/
def gNeckInv : RTree → List ℕ → List ℕ → List ℕ
  | .node _, [], [] => []
  | .node _, [], k :: z => if k = 0 then z else []
  | .node _, _ :: _, [] => []
  | .node cs, j :: v, k :: z =>
      if k = cs.length - 1 then j :: gNeckInv (cs.getD j (.node [])) v z
      else if k < j then k :: z else (k + 1) :: z

@[simp] lemma gNeckMap_nil_nil (cs : List RTree) : gNeckMap (.node cs) [] [] = [] := rfl
@[simp] lemma gNeckMap_nil_cons (cs : List RTree) (k : ℕ) (z : List ℕ) :
    gNeckMap (.node cs) [] (k :: z) = 0 :: k :: z := rfl
@[simp] lemma gNeckMap_cons_nil (cs : List RTree) (j : ℕ) (v : List ℕ) :
    gNeckMap (.node cs) (j :: v) [] = [] := rfl
lemma gNeckMap_cons_cons (cs : List RTree) (j : ℕ) (v : List ℕ) (k : ℕ) (z : List ℕ) :
    gNeckMap (.node cs) (j :: v) (k :: z) =
      if k = j then (cs.length - 1) :: gNeckMap (cs.getD j (.node [])) v z
      else if k < j then k :: z else (k - 1) :: z := rfl

@[simp] lemma gNeckInv_nil_nil (cs : List RTree) : gNeckInv (.node cs) [] [] = [] := rfl
lemma gNeckInv_nil_cons (cs : List RTree) (k : ℕ) (z : List ℕ) :
    gNeckInv (.node cs) [] (k :: z) = if k = 0 then z else [] := rfl
@[simp] lemma gNeckInv_cons_nil (cs : List RTree) (j : ℕ) (v : List ℕ) :
    gNeckInv (.node cs) (j :: v) [] = [] := rfl
lemma gNeckInv_cons_cons (cs : List RTree) (j : ℕ) (v : List ℕ) (k : ℕ) (z : List ℕ) :
    gNeckInv (.node cs) (j :: v) (k :: z) =
      if k = cs.length - 1 then j :: gNeckInv (cs.getD j (.node [])) v z
      else if k < j then k :: z else (k + 1) :: z := rfl

/-- The root stays at the root. -/
@[simp] lemma gNeckMap_nil (t : RTree) (e : List ℕ) : gNeckMap t e [] = [] := by
  cases t; cases e <;> rfl

/-- The root comes from the root. -/
@[simp] lemma gNeckInv_nil (t : RTree) (e : List ℕ) : gNeckInv t e [] = [] := by
  cases t; cases e <;> rfl

/-- The exit of the neck construction sits one step below the image of the mark. -/
lemma gExitAddr_gNeckList : ∀ (t : RTree) (e : List ℕ), IsAddr t e →
    gExitAddr (gNeckList t e) = gNeckMap t e e ++ [1]
  | .node cs, [], _ => rfl
  | .node cs, j :: v, he => by
      rw [isAddr_cons] at he
      obtain ⟨hj, hv⟩ := he
      rw [gNeckList_cons]
      obtain ⟨r, rest, hr⟩ : ∃ r rest, gNeckList (cs.getD j (.node [])) v = r :: rest := by
        cases h : gNeckList (cs.getD j (.node [])) v with
        | nil => exact absurd h (gNeckList_ne_nil _ _)
        | cons r rest => exact ⟨r, rest, rfl⟩
      rw [hr, gExitAddr_cons₂, ← hr, gNeckMap_cons_cons, if_pos rfl, List.cons_append,
        List.length_eraseIdx_of_lt hj, getD_eq_getElem_of_lt hj,
        gExitAddr_gNeckList cs[j] v hv]

/-- The addresses of the realisation at the mark: the joint vertex with the old
subtrees below it, and the exit. -/
lemma isAddr_mark_iff {cs : List RTree} {k : ℕ} {z : List ℕ} :
    IsAddr (GShape.realiseAux [[RTree.node cs], []]) (k :: z) ↔
      (k = 0 ∧ IsAddr (.node cs) z) ∨ (k = 1 ∧ z = []) := by
  rw [show GShape.realiseAux [[RTree.node cs], []]
      = .node ([RTree.node cs] ++ [GShape.realiseAux [[]]]) from rfl,
    isAddr_node_append_single]
  simp only [List.length_cons, List.length_nil, zero_add]
  constructor
  · rintro (⟨h, hz⟩ | ⟨rfl, hz⟩)
    · have hk : k = 0 := by omega
      subst hk
      exact Or.inl ⟨rfl, by simpa using hz⟩
    · exact Or.inr ⟨rfl, isAddr_node_nil_iff.mp hz⟩
  · rintro (⟨rfl, hz⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨by omega, by simpa using hz⟩
    · exact Or.inr ⟨rfl, isAddr_nil _⟩

/-- The addresses of the realisation along the neck: a bush, read through the erased
index, or the rest of the neck. -/
lemma isAddr_neck_iff {cs : List RTree} {j : ℕ} {v : List ℕ} (hj : j < cs.length) {k : ℕ}
    {z : List ℕ} :
    IsAddr (GShape.realiseAux (gNeckList (.node cs) (j :: v))) (k :: z) ↔
      (∃ hk : k < j, IsAddr (cs[k]'(by omega)) z) ∨
        (∃ hk : j ≤ k ∧ k + 1 < cs.length, IsAddr (cs[k + 1]'hk.2) z) ∨
        (k = cs.length - 1 ∧ IsAddr (GShape.realiseAux (gNeckList cs[j] v)) z) := by
  rw [gNeckList_cons, getD_eq_getElem_of_lt hj, realiseAux_cons_of_ne_nil _ (gNeckList_ne_nil _ _),
    isAddr_node_append_single]
  have hlen := List.length_eraseIdx_of_lt hj
  constructor
  · rintro (⟨h, hz⟩ | ⟨h, hz⟩)
    · rcases lt_or_ge k j with hk | hk
      · rw [List.getElem_eraseIdx_of_lt h hk] at hz
        exact Or.inl ⟨hk, hz⟩
      · rw [List.getElem_eraseIdx_of_ge h hk] at hz
        exact Or.inr (Or.inl ⟨⟨hk, by omega⟩, hz⟩)
    · exact Or.inr (Or.inr ⟨by omega, hz⟩)
  · rintro (⟨hk, hz⟩ | ⟨⟨hk, hk'⟩, hz⟩ | ⟨hk, hz⟩)
    · refine Or.inl ⟨by omega, ?_⟩
      rwa [List.getElem_eraseIdx_of_lt (by omega) hk]
    · refine Or.inl ⟨by omega, ?_⟩
      rwa [List.getElem_eraseIdx_of_ge (by omega) hk]
    · exact Or.inr ⟨by omega, hz⟩

/-- The address map lands in the realisation. -/
lemma isAddr_gNeckMap : ∀ (t : RTree) (e : List ℕ), IsAddr t e → ∀ w, IsAddr t w →
    IsAddr (GShape.realiseAux (gNeckList t e)) (gNeckMap t e w)
  | .node cs, [], _, [], _ => isAddr_nil _
  | .node cs, [], _, k :: z, hw => by
      rw [gNeckMap_nil_cons, gNeckList_nil, isAddr_mark_iff]
      exact Or.inl ⟨rfl, hw⟩
  | .node cs, j :: v, _, [], _ => by rw [gNeckMap_cons_nil]; exact isAddr_nil _
  | .node cs, j :: v, he, k :: z, hw => by
      rw [isAddr_cons] at he hw
      obtain ⟨hj, hv⟩ := he
      obtain ⟨hk, hz⟩ := hw
      simp only [gNeckMap_cons_cons, getD_eq_getElem_of_lt hj]
      by_cases hkj : k = j
      · subst hkj
        rw [if_pos rfl, isAddr_neck_iff hj]
        exact Or.inr (Or.inr ⟨rfl, isAddr_gNeckMap cs[k] v hv z hz⟩)
      · rw [if_neg hkj]
        by_cases hlt : k < j
        · rw [if_pos hlt, isAddr_neck_iff hj]
          exact Or.inl ⟨hlt, hz⟩
        · rw [if_neg hlt, isAddr_neck_iff hj]
          refine Or.inr (Or.inl ⟨⟨by omega, by omega⟩, ?_⟩)
          have : k - 1 + 1 = k := by omega
          simp only [this]
          exact hz

/-- The retraction lands in the tree. -/
lemma isAddr_gNeckInv : ∀ (t : RTree) (e : List ℕ), IsAddr t e → ∀ y,
    IsAddr (GShape.realiseAux (gNeckList t e)) y → IsAddr t (gNeckInv t e y)
  | .node cs, [], _, [], _ => isAddr_nil _
  | .node cs, [], _, k :: z, hy => by
      rw [gNeckList_nil, isAddr_mark_iff] at hy
      rw [gNeckInv_nil_cons]
      rcases hy with ⟨rfl, hz⟩ | ⟨rfl, rfl⟩
      · rw [if_pos rfl]; exact hz
      · rw [if_neg (by norm_num)]; exact isAddr_nil _
  | .node cs, j :: v, _, [], _ => by rw [gNeckInv_cons_nil]; exact isAddr_nil _
  | .node cs, j :: v, he, k :: z, hy => by
      rw [isAddr_cons] at he
      obtain ⟨hj, hv⟩ := he
      rw [isAddr_neck_iff hj] at hy
      simp only [gNeckInv_cons_cons, getD_eq_getElem_of_lt hj]
      rcases hy with ⟨hk, hz⟩ | ⟨⟨hk, hk'⟩, hz⟩ | ⟨hk, hz⟩
      · rw [if_neg (by omega), if_pos hk, isAddr_cons]
        exact ⟨by omega, hz⟩
      · rw [if_neg (by omega), if_neg (by omega), isAddr_cons]
        exact ⟨hk', hz⟩
      · rw [if_pos hk, isAddr_cons]
        exact ⟨hj, isAddr_gNeckInv cs[j] v hv z hz⟩

/-- The retraction inverts the address map. -/
lemma gNeckInv_gNeckMap : ∀ (t : RTree) (e : List ℕ), IsAddr t e → ∀ w, IsAddr t w →
    gNeckInv t e (gNeckMap t e w) = w
  | .node cs, [], _, [], _ => rfl
  | .node cs, [], _, k :: z, _ => by rw [gNeckMap_nil_cons, gNeckInv_nil_cons, if_pos rfl]
  | .node cs, j :: v, _, [], _ => by rw [gNeckMap_cons_nil, gNeckInv_cons_nil]
  | .node cs, j :: v, he, k :: z, hw => by
      rw [isAddr_cons] at he hw
      obtain ⟨hj, hv⟩ := he
      obtain ⟨hk, hz⟩ := hw
      simp only [gNeckMap_cons_cons, getD_eq_getElem_of_lt hj]
      by_cases hkj : k = j
      · subst hkj
        rw [if_pos rfl, gNeckInv_cons_cons, if_pos rfl, getD_eq_getElem_of_lt hj,
          gNeckInv_gNeckMap cs[k] v hv z hz]
      · rw [if_neg hkj]
        by_cases hlt : k < j
        · rw [if_pos hlt, gNeckInv_cons_cons, if_neg (by omega), if_pos hlt]
        · rw [if_neg hlt, gNeckInv_cons_cons, if_neg (by omega), if_neg (by omega)]
          congr 1
          omega

/-- The address map moves parent-child pairs by at most two: a step into the joint
vertex becomes two steps. -/
lemma addrDist_gNeckMap_append : ∀ (t : RTree) (e : List ℕ), IsAddr t e → ∀ u a,
    IsAddr t (u ++ [a]) → addrDist (gNeckMap t e (u ++ [a])) (gNeckMap t e u) ≤ 2
  | .node cs, [], _, [], a, _ => by simp
  | .node cs, [], _, k :: u, a, _ => by simp
  | .node cs, j :: v, he, [], a, _ => by
      rw [List.nil_append, gNeckMap_cons_cons, gNeckMap_cons_nil, gNeckMap_nil]
      split_ifs <;> simp
  | .node cs, j :: v, he, k :: u, a, hw => by
      rw [isAddr_cons] at he
      rw [List.cons_append, isAddr_cons] at hw
      obtain ⟨hj, hv⟩ := he
      obtain ⟨hk, hz⟩ := hw
      simp only [List.cons_append, gNeckMap_cons_cons, getD_eq_getElem_of_lt hj]
      by_cases hkj : k = j
      · subst hkj
        rw [if_pos rfl, if_pos rfl, addrDist_cons_cons_self]
        exact addrDist_gNeckMap_append cs[k] v hv u a hz
      · simp only [if_neg hkj]
        split_ifs <;> simp

/-- The retraction moves parent-child pairs by at most one. -/
lemma addrDist_gNeckInv_append : ∀ (t : RTree) (e : List ℕ), IsAddr t e → ∀ y b,
    IsAddr (GShape.realiseAux (gNeckList t e)) (y ++ [b]) →
    addrDist (gNeckInv t e (y ++ [b])) (gNeckInv t e y) ≤ 1
  | .node cs, [], _, [], b, hy => by
      rw [List.nil_append, gNeckList_nil, isAddr_mark_iff] at hy
      rw [List.nil_append, gNeckInv_nil_cons, gNeckInv_nil_nil]
      rcases hy with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  | .node cs, [], _, k :: y, b, hy => by
      rw [List.cons_append, gNeckList_nil, isAddr_mark_iff] at hy
      rw [List.cons_append, gNeckInv_nil_cons, gNeckInv_nil_cons]
      rcases hy with ⟨rfl, -⟩ | ⟨rfl, h⟩
      · simp
      · simp at h
  | .node cs, j :: v, he, [], b, hy => by
      rw [List.nil_append, gNeckInv_cons_cons, gNeckInv_cons_nil, gNeckInv_nil]
      split_ifs <;> simp
  | .node cs, j :: v, he, k :: y, b, hy => by
      rw [isAddr_cons] at he
      obtain ⟨hj, hv⟩ := he
      rw [List.cons_append, isAddr_neck_iff hj] at hy
      simp only [List.cons_append, gNeckInv_cons_cons, getD_eq_getElem_of_lt hj]
      rcases hy with ⟨hk, -⟩ | ⟨⟨hk, hk'⟩, -⟩ | ⟨hk, hz⟩
      · simp only [if_neg (show ¬ k = cs.length - 1 by omega), if_pos hk]; simp
      · simp only [if_neg (show ¬ k = cs.length - 1 by omega), if_neg (show ¬ k < j by omega)]
        simp
      · simp only [if_pos hk, addrDist_cons_cons_self]
        exact addrDist_gNeckInv_append cs[j] v hv y b hz

/-- The image is `1`-dense: the joint vertex and the exit are one step below the
image of the mark. -/
lemma addrDist_gNeckMap_gNeckInv : ∀ (t : RTree) (e : List ℕ), IsAddr t e → ∀ y,
    IsAddr (GShape.realiseAux (gNeckList t e)) y →
    addrDist (gNeckMap t e (gNeckInv t e y)) y ≤ 1
  | .node cs, [], _, [], _ => by simp
  | .node cs, [], _, k :: z, hy => by
      rw [gNeckList_nil, isAddr_mark_iff] at hy
      rw [gNeckInv_nil_cons]
      rcases hy with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · rw [if_pos rfl]
        cases z <;> simp
      · rw [if_neg (by norm_num)]
        simp
  | .node cs, j :: v, _, [], _ => by simp
  | .node cs, j :: v, he, k :: z, hy => by
      rw [isAddr_cons] at he
      obtain ⟨hj, hv⟩ := he
      rw [isAddr_neck_iff hj] at hy
      simp only [gNeckInv_cons_cons, getD_eq_getElem_of_lt hj]
      rcases hy with ⟨hk, -⟩ | ⟨⟨hk, hk'⟩, -⟩ | ⟨hk, hz⟩
      · rw [if_neg (by omega), if_pos hk, gNeckMap_cons_cons, if_neg (by omega), if_pos hk]
        simp
      · rw [if_neg (by omega), if_neg (by omega), gNeckMap_cons_cons, if_neg (by omega),
          if_neg (by omega)]
        simp
      · rw [if_pos hk, gNeckMap_cons_cons, if_pos rfl, getD_eq_getElem_of_lt hj, hk,
          addrDist_cons_cons_self]
        exact addrDist_gNeckMap_gNeckInv cs[j] v hv z hz

/-- **The neck construction is a `2`-marked quasi-isometry**: the address map changes
every parent-child distance by at most one step, is `1`-dense, fixes the entry and
sends the mark one step above the exit. -/
theorem markedQI_gNeck {t : RTree} {e : List ℕ} (he : e ∈ addrList t) :
    MarkedQI 2 (gSpace t e) (gShapeSpace (gNeckShape t e)) := by
  have he' : IsAddr t e := mem_addrList_iff.mp he
  rw [gShapeSpace_gNeckShape]
  have h := markedQI_gSpace_of_addrMaps (K := 2) (by norm_num) (gNeckMap t e) (gNeckInv t e)
    (isAddr_gNeckMap t e he') (isAddr_gNeckInv t e he')
    (addrDist_gNeckMap_append t e he')
    (fun y b hy => (addrDist_gNeckInv_append t e he' y b hy).trans (by norm_num))
    (gNeckInv_gNeckMap t e he')
    (fun y hy => (addrDist_gNeckMap_gNeckInv t e he' y hy).trans (by norm_num))
    (by rw [gNeckMap_nil]; simp)
    he' (isAddr_realiseAux_gExitAddr _)
    (by rw [gExitAddr_gNeckList t e he', addrDist_append_right]; simp)
  exact_mod_cast h

/-! ### The support fix: padding a shape -/

mutual

/-- **The support fix on a bush**: a vertex with `0 < c` children receives `k - c`
leaf children, a leaf stays a leaf. -/
def padT (k : ℕ) : RTree → RTree
  | .node [] => .node []
  | .node (c :: cs) =>
      .node (padF k (c :: cs) ++ List.replicate (k - (c :: cs).length) (.node []))

/-- The support fix on a forest. -/
def padF (k : ℕ) : List RTree → List RTree
  | [] => []
  | c :: cs => padT k c :: padF k cs

end

@[simp] lemma padT_nil (k : ℕ) : padT k (.node []) = .node [] := by rw [padT]

lemma padT_cons (k : ℕ) (c : RTree) (cs : List RTree) :
    padT k (.node (c :: cs))
      = .node (padF k (c :: cs) ++ List.replicate (k - (c :: cs).length) (.node [])) := by
  rw [padT]

/-- The padded forest is the padding of each tree. -/
lemma padF_eq_map (k : ℕ) : ∀ cs : List RTree, padF k cs = cs.map (padT k)
  | [] => by rw [padF, List.map_nil]
  | c :: cs => by rw [padF, padF_eq_map k cs, List.map_cons]

/-- **The support fix on a neck vertex**: the bushes padded, and one-vertex bushes
added up to `k - 1` of them. -/
def padList (k : ℕ) (β : List RTree) : List RTree :=
  padF k β ++ List.replicate (k - 1 - β.length) (.node [])

lemma length_padList (k : ℕ) (β : List RTree) :
    (padList k β).length = β.length + (k - 1 - β.length) := by
  rw [padList, List.length_append, padF_eq_map, List.length_map, List.length_replicate]

lemma length_le_length_padList (k : ℕ) (β : List RTree) : β.length ≤ (padList k β).length := by
  rw [length_padList]
  omega

/-- **The support fix on the bush lists**: every neck list padded, the bouquet left. -/
def padDecs (k : ℕ) : List (List RTree) → List (List RTree)
  | [] => []
  | [β] => [β]
  | β :: r :: rest => padList k β :: padDecs k (r :: rest)

@[simp] lemma padDecs_nil (k : ℕ) : padDecs k [] = [] := rfl
@[simp] lemma padDecs_singleton (k : ℕ) (β : List RTree) : padDecs k [β] = [β] := rfl
lemma padDecs_cons_cons (k : ℕ) (β r : List RTree) (rest : List (List RTree)) :
    padDecs k (β :: r :: rest) = padList k β :: padDecs k (r :: rest) := rfl

lemma padDecs_ne_nil (k : ℕ) {L : List (List RTree)} (hL : L ≠ []) : padDecs k L ≠ [] := by
  cases L with
  | nil => exact absurd rfl hL
  | cons β rest => cases rest <;> simp [padDecs_cons_cons]

/-- The padding acts on the neck lists and leaves the bouquet. -/
lemma padDecs_append_singleton (k : ℕ) : ∀ (N : List (List RTree)) (b : List RTree),
    padDecs k (N ++ [b]) = N.map (padList k) ++ [b]
  | [], b => rfl
  | [β], b => rfl
  | β :: r :: rest, b => by
      rw [List.cons_append, List.cons_append, padDecs_cons_cons, ← List.cons_append,
        padDecs_append_singleton k (r :: rest) b]
      simp

/-- **The support fix**: the padded shape. -/
def gPad (k : ℕ) (σ : GShape) : GShape := gOfList (padDecs k σ.decs)

lemma decs_gPad (k : ℕ) (σ : GShape) : (gPad k σ).decs = padDecs k σ.decs :=
  decs_gOfList (padDecs_ne_nil k σ.decs_ne_nil)

/-- The neck lists of the padded shape are the padded neck lists, and the bouquet is
unchanged. -/
lemma neckList_bouquet_gPad (k : ℕ) (σ : GShape) :
    (gPad k σ).neckList = σ.neckList.map (padList k) ∧ (gPad k σ).bouquet = σ.bouquet := by
  have h := (gPad k σ).decs_eq_append
  rw [decs_gPad, σ.decs_eq_append, padDecs_append_singleton] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h (by simp)
  exact ⟨h1.symm, by simpa using h2.symm⟩

lemma gShapeSpace_gPad (k : ℕ) (σ : GShape) :
    gShapeSpace (gPad k σ)
      = gSpace (GShape.realiseAux (padDecs k σ.decs)) (gExitAddr (padDecs k σ.decs)) := by
  rw [gShapeSpace, GShape.realise, GShape.exitAddr, decs_gPad]

/-! ### The size of the padded shape -/

lemma sizeF_replicate_leaf (m : ℕ) : RTree.sizeF (List.replicate m (.node [])) = m := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, RTree.sizeF_cons, ih]; simp; omega

/-- The padding multiplies the size by at most `k`: a padded vertex with `c ≥ 1`
children carries `1 + (k - c) ≤ k` vertices of its own. -/
lemma size_padT_le {k : ℕ} (hk : 1 ≤ k) (t : RTree) : (padT k t).size ≤ k * t.size := by
  induction t using RTree.ind with
  | _ cs ih =>
      have key : ∀ l : List RTree, (∀ c ∈ l, (padT k c).size ≤ k * c.size) →
          RTree.sizeF (padF k l) ≤ k * RTree.sizeF l := by
        intro l
        induction l with
        | nil => simp [padF]
        | cons c l ihl =>
            intro hall
            rw [padF, RTree.sizeF_cons, RTree.sizeF_cons, Nat.mul_add]
            exact Nat.add_le_add (hall c (by simp)) (ihl fun x hx => hall x (by simp [hx]))
      cases cs with
      | nil => simp; omega
      | cons c cs =>
          rw [padT_cons, RTree.size_node, RTree.sizeF_append, sizeF_replicate_leaf, RTree.size_node,
            Nat.mul_add, Nat.mul_one]
          have := key (c :: cs) ih
          simp only [List.length_cons]
          omega

lemma sizeF_padList_le {k : ℕ} (hk : 1 ≤ k) (β : List RTree) :
    RTree.sizeF (padList k β) + 1 ≤ k * (RTree.sizeF β + 1) := by
  rw [padList, RTree.sizeF_append, sizeF_replicate_leaf]
  have key : RTree.sizeF (padF k β) ≤ k * RTree.sizeF β := by
    induction β with
    | nil => simp [padF]
    | cons c l ihl =>
        rw [padF, RTree.sizeF_cons, RTree.sizeF_cons, Nat.mul_add]
        exact Nat.add_le_add (size_padT_le hk c) ihl
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- **The size of the padded shape**: at most `k` times the size. -/
lemma size_realiseAux_padDecs_le {k : ℕ} (hk : 1 ≤ k) :
    ∀ L : List (List RTree), L ≠ [] →
      (GShape.realiseAux (padDecs k L)).size ≤ k * (GShape.realiseAux L).size
  | [], hL => absurd rfl hL
  | [β], _ => by
      rw [padDecs_singleton, show GShape.realiseAux [β] = .node β from rfl, RTree.size_node]
      nlinarith
  | β :: r :: rest, _ => by
      have ih := size_realiseAux_padDecs_le hk (r :: rest) (by simp)
      rw [padDecs_cons_cons, realiseAux_cons_of_ne_nil _ (padDecs_ne_nil k (by simp)),
        realiseAux_cons_of_ne_nil _ (by simp), RTree.size_node, RTree.size_node,
        RTree.sizeF_append, RTree.sizeF_append, RTree.sizeF_cons, RTree.sizeF_cons,
        RTree.sizeF_nil]
      have := sizeF_padList_le hk β
      nlinarith

theorem size_gPad_le {k : ℕ} (hk : 1 ≤ k) (σ : GShape) : (gPad k σ).size ≤ k * σ.size := by
  show (gPad k σ).realise.size ≤ k * σ.realise.size
  rw [GShape.realise, decs_gPad]
  exact size_realiseAux_padDecs_le hk σ.decs σ.decs_ne_nil

/-! ### The padded shape lies in the support -/

/-- A padded bush is charged once leaves and the arity `k` carry mass: every vertex
has `0` or `k` children. -/
lemma chargedT_padT {J : ℕ} {θ : BranchingProcess.Offspring J} {k : ℕ} (h0 : 0 < θ 0)
    (hk : 0 < θ k) : ∀ {t : RTree}, DegLe k t → RTree.ChargedT θ (padT k t) := by
  intro t
  induction t using RTree.ind with
  | _ cs ih =>
      rintro ⟨hlen, hall⟩
      cases cs with
      | nil => exact ⟨by simpa using h0, by simp⟩
      | cons c cs =>
          rw [padT_cons]
          refine ⟨?_, ?_⟩
          · rw [List.length_append, padF_eq_map, List.length_map, List.length_replicate]
            have : (c :: cs).length + (k - (c :: cs).length) = k := by omega
            rw [this]
            exact hk
          · intro x hx
            rw [List.mem_append, padF_eq_map, List.mem_map, List.mem_replicate] at hx
            rcases hx with ⟨d, hd, rfl⟩ | ⟨-, rfl⟩
            · exact ih d hd (hall d hd)
            · exact ⟨by simpa using h0, by simp⟩

/-- **The support clause of the padding**: a shape whose neck lists have at most `k-1`
bushes of offspring at most `k` and whose bouquet is empty is padded into the support
of the law at arity `k`. -/
theorem chargedG_gPad {J : ℕ} {θ : BranchingProcess.Offspring J} {k : ℕ} (h0 : 0 < θ 0)
    (hk : 0 < θ k) (hk1 : 1 ≤ k) {σ : GShape}
    (hneck : ∀ β ∈ σ.neckList, β.length ≤ k - 1 ∧ ∀ b ∈ β, DegLe k b)
    (hbq : σ.bouquet = []) : GShape.ChargedG θ k (gPad k σ) := by
  obtain ⟨hN, hB⟩ := neckList_bouquet_gPad k σ
  refine ⟨?_, ?_⟩
  · intro β' hβ'
    rw [hN, List.mem_map] at hβ'
    obtain ⟨β, hβ, rfl⟩ := hβ'
    obtain ⟨hlen, hall⟩ := hneck β hβ
    refine ⟨?_, ?_⟩
    · rw [length_padList]
      have : 1 + (β.length + (k - 1 - β.length)) = k := by omega
      rw [this]
      exact hk
    · intro x hx
      rw [padList, List.mem_append, padF_eq_map, List.mem_map, List.mem_replicate] at hx
      rcases hx with ⟨d, hd, rfl⟩ | ⟨-, rfl⟩
      · exact chargedT_padT h0 hk (hall d hd)
      · exact ⟨by simpa using h0, by simp⟩
  · rw [hB, hbq]
    exact ⟨by simpa using hk, by simp⟩

/-! ### The addresses of a padded bush -/

/-- An address below the root of a widened node reads a bush or the last child. -/
lemma isAddr_node_append_single' {β : List RTree} {R : RTree} {k : ℕ} {z : List ℕ} :
    IsAddr (.node (β ++ [R])) (k :: z) ↔
      IsAddr (.node β) (k :: z) ∨ (k = β.length ∧ IsAddr R z) := by
  rw [isAddr_node_append_single, isAddr_cons]

/-- The addresses below a padded node: the padded children, and the new leaves. -/
lemma isAddr_map_padT_append_replicate {k m : ℕ} {cs : List RTree} {i : ℕ} {z : List ℕ} :
    IsAddr (.node (cs.map (padT k) ++ List.replicate m (.node []))) (i :: z) ↔
      (∃ h : i < cs.length, IsAddr (padT k cs[i]) z) ∨ (cs.length ≤ i ∧ i < cs.length + m ∧ z = []) := by
  rw [isAddr_cons]
  constructor
  · rintro ⟨h, hz⟩
    rcases lt_or_ge i cs.length with hi | hi
    · refine Or.inl ⟨hi, ?_⟩
      rwa [List.getElem_append_left (by simpa using hi), List.getElem_map] at hz
    · refine Or.inr ⟨hi, by simpa using h, ?_⟩
      rw [List.getElem_append_right (by simpa using hi), List.getElem_replicate] at hz
      exact isAddr_node_nil_iff.mp hz
  · rintro (⟨hi, hz⟩ | ⟨hi, hm, rfl⟩)
    · refine ⟨by simp; omega, ?_⟩
      rwa [List.getElem_append_left (by simpa using hi), List.getElem_map]
    · exact ⟨by simp; omega, isAddr_nil _⟩

/-- The addresses of a padded bush. -/
lemma isAddr_padT_cons_iff {k : ℕ} {cs : List RTree} {i : ℕ} {z : List ℕ} :
    IsAddr (padT k (.node cs)) (i :: z) ↔
      (∃ h : i < cs.length, IsAddr (padT k cs[i]) z) ∨
        (cs ≠ [] ∧ cs.length ≤ i ∧ i < cs.length + (k - cs.length) ∧ z = []) := by
  cases cs with
  | nil =>
      rw [padT_nil]
      simp [isAddr_cons]
  | cons c cs =>
      rw [padT_cons, padF_eq_map, isAddr_map_padT_append_replicate]
      simp

/-- The addresses of a padded neck vertex's bushes. -/
lemma isAddr_node_padList_iff {k : ℕ} {β : List RTree} {i : ℕ} {z : List ℕ} :
    IsAddr (.node (padList k β)) (i :: z) ↔
      (∃ h : i < β.length, IsAddr (padT k β[i]) z) ∨
        (β.length ≤ i ∧ i < (padList k β).length ∧ z = []) := by
  rw [length_padList, padList, padF_eq_map, isAddr_map_padT_append_replicate]

/-- Every address of a bush is an address of its padding. -/
lemma isAddr_padT (k : ℕ) (t : RTree) : ∀ w, IsAddr t w → IsAddr (padT k t) w := by
  induction t using RTree.ind with
  | _ cs ih =>
      intro w hw
      cases w with
      | nil => exact isAddr_nil _
      | cons i z =>
          rw [isAddr_cons] at hw
          obtain ⟨hi, hz⟩ := hw
          rw [isAddr_padT_cons_iff]
          exact Or.inl ⟨hi, ih _ (List.getElem_mem hi) z hz⟩

/-- The retraction of a padded bush: a new leaf goes to its parent. -/
def padInv : RTree → List ℕ → List ℕ
  | .node _, [] => []
  | .node cs, i :: z => if i < cs.length then i :: padInv (cs.getD i (.node [])) z else []

@[simp] lemma padInv_nil (cs : List RTree) : padInv (.node cs) [] = [] := rfl
lemma padInv_cons (cs : List RTree) (i : ℕ) (z : List ℕ) :
    padInv (.node cs) (i :: z) = if i < cs.length then i :: padInv (cs.getD i (.node [])) z else [] :=
  rfl

lemma padInv_nil' (t : RTree) : padInv t [] = [] := by cases t; rfl

/-- The retraction lands in the bush. -/
lemma isAddr_padInv (k : ℕ) (t : RTree) : ∀ y, IsAddr (padT k t) y → IsAddr t (padInv t y) := by
  induction t using RTree.ind with
  | _ cs ih =>
      intro y hy
      cases y with
      | nil => exact isAddr_nil _
      | cons i z =>
          rw [isAddr_padT_cons_iff] at hy
          rw [padInv_cons]
          rcases hy with ⟨hi, hz⟩ | ⟨-, hi, -, -⟩
          · rw [if_pos hi, getD_eq_getElem_of_lt hi, isAddr_cons]
            exact ⟨hi, ih _ (List.getElem_mem hi) z hz⟩
          · rw [if_neg (by omega)]
            exact isAddr_nil _

/-- The retraction fixes the old addresses. -/
lemma padInv_of_isAddr (t : RTree) : ∀ w, IsAddr t w → padInv t w = w := by
  induction t using RTree.ind with
  | _ cs ih =>
      intro w hw
      cases w with
      | nil => exact padInv_nil' _
      | cons i z =>
          rw [isAddr_cons] at hw
          obtain ⟨hi, hz⟩ := hw
          rw [padInv_cons, if_pos hi, getD_eq_getElem_of_lt hi, ih _ (List.getElem_mem hi) z hz]

/-- The retraction moves parent-child pairs by at most one. -/
lemma addrDist_padInv_append (k : ℕ) (t : RTree) : ∀ y b, IsAddr (padT k t) (y ++ [b]) →
    addrDist (padInv t (y ++ [b])) (padInv t y) ≤ 1 := by
  induction t using RTree.ind with
  | _ cs ih =>
      intro y b hy
      cases y with
      | nil =>
          rw [List.nil_append, padInv_cons, padInv_nil']
          split_ifs <;> simp
      | cons i z =>
          rw [List.cons_append, isAddr_padT_cons_iff] at hy
          rw [List.cons_append, padInv_cons, padInv_cons]
          rcases hy with ⟨hi, hz⟩ | ⟨-, hi, -, h⟩
          · rw [if_pos hi, if_pos hi, getD_eq_getElem_of_lt hi, addrDist_cons_cons_self]
            exact ih _ (List.getElem_mem hi) z b hz
          · simp at h

/-- The retraction moves every vertex by at most one. -/
lemma addrDist_padInv_self (k : ℕ) (t : RTree) : ∀ y, IsAddr (padT k t) y →
    addrDist (padInv t y) y ≤ 1 := by
  induction t using RTree.ind with
  | _ cs ih =>
      intro y hy
      cases y with
      | nil => simp [padInv_nil']
      | cons i z =>
          rw [isAddr_padT_cons_iff] at hy
          rw [padInv_cons]
          rcases hy with ⟨hi, hz⟩ | ⟨-, hi, -, rfl⟩
          · rw [if_pos hi, getD_eq_getElem_of_lt hi, addrDist_cons_cons_self]
            exact ih _ (List.getElem_mem hi) z hz
          · rw [if_neg (by omega)]
            simp

/-! ### The address map of the padding -/

/-- **The address map of the padding**: the neck child moves past the added bushes,
everything else keeps its address. -/
def gPadMap (k : ℕ) : List (List RTree) → List ℕ → List ℕ
  | [], w => w
  | [_], w => w
  | _ :: _ :: _, [] => []
  | β :: r :: rest, i :: z =>
      if i = β.length then (padList k β).length :: gPadMap k (r :: rest) z else i :: z

/-- The retraction of the padding: an added leaf goes to its parent. -/
def gPadInv (k : ℕ) : List (List RTree) → List ℕ → List ℕ
  | [], y => y
  | [_], y => y
  | _ :: _ :: _, [] => []
  | β :: r :: rest, i :: z =>
      if i = (padList k β).length then β.length :: gPadInv k (r :: rest) z
      else if i < β.length then i :: padInv (β.getD i (.node [])) z else []

@[simp] lemma gPadMap_nil_list (k : ℕ) (w : List ℕ) : gPadMap k [] w = w := rfl
@[simp] lemma gPadMap_singleton (k : ℕ) (β : List RTree) (w : List ℕ) :
    gPadMap k [β] w = w := rfl
@[simp] lemma gPadMap_cons_cons_nil (k : ℕ) (β r : List RTree) (rest : List (List RTree)) :
    gPadMap k (β :: r :: rest) [] = [] := rfl
lemma gPadMap_cons_cons_cons (k : ℕ) (β r : List RTree) (rest : List (List RTree)) (i : ℕ)
    (z : List ℕ) :
    gPadMap k (β :: r :: rest) (i :: z)
      = if i = β.length then (padList k β).length :: gPadMap k (r :: rest) z else i :: z := rfl

@[simp] lemma gPadInv_nil_list (k : ℕ) (y : List ℕ) : gPadInv k [] y = y := rfl
@[simp] lemma gPadInv_singleton (k : ℕ) (β : List RTree) (y : List ℕ) :
    gPadInv k [β] y = y := rfl
@[simp] lemma gPadInv_cons_cons_nil (k : ℕ) (β r : List RTree) (rest : List (List RTree)) :
    gPadInv k (β :: r :: rest) [] = [] := rfl
lemma gPadInv_cons_cons_cons (k : ℕ) (β r : List RTree) (rest : List (List RTree)) (i : ℕ)
    (z : List ℕ) :
    gPadInv k (β :: r :: rest) (i :: z)
      = if i = (padList k β).length then β.length :: gPadInv k (r :: rest) z
        else if i < β.length then i :: padInv (β.getD i (.node [])) z else [] := rfl

lemma gPadMap_nil (k : ℕ) : ∀ L : List (List RTree), gPadMap k L [] = []
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

lemma gPadInv_nil (k : ℕ) : ∀ L : List (List RTree), gPadInv k L [] = []
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- The exit of the padded shape is the image of the exit. -/
lemma gExitAddr_padDecs (k : ℕ) : ∀ L : List (List RTree),
    gExitAddr (padDecs k L) = gPadMap k L (gExitAddr L)
  | [] => rfl
  | [β] => rfl
  | β :: r :: rest => by
      rw [padDecs_cons_cons, gExitAddr_cons₂, gPadMap_cons_cons_cons, if_pos rfl]
      obtain ⟨r', rest', hr⟩ : ∃ r' rest', padDecs k (r :: rest) = r' :: rest' := by
        cases h : padDecs k (r :: rest) with
        | nil => exact absurd h (padDecs_ne_nil k (by simp))
        | cons r' rest' => exact ⟨r', rest', rfl⟩
      rw [hr, gExitAddr_cons₂, ← hr, gExitAddr_padDecs k (r :: rest)]

/-- The address map lands in the padded realisation. -/
lemma isAddr_gPadMap (k : ℕ) : ∀ L : List (List RTree), ∀ w, IsAddr (GShape.realiseAux L) w →
    IsAddr (GShape.realiseAux (padDecs k L)) (gPadMap k L w)
  | [], w, hw => hw
  | [β], w, hw => hw
  | β :: r :: rest, [], _ => by rw [gPadMap_cons_cons_nil]; exact isAddr_nil _
  | β :: r :: rest, i :: z, hw => by
      rw [realiseAux_cons_of_ne_nil _ (by simp), isAddr_node_append_single'] at hw
      rw [padDecs_cons_cons, realiseAux_cons_of_ne_nil _ (padDecs_ne_nil k (by simp)),
        gPadMap_cons_cons_cons]
      rcases hw with hw | ⟨rfl, hz⟩
      · rw [isAddr_cons] at hw
        obtain ⟨hi, hz⟩ := hw
        rw [if_neg (by omega), isAddr_node_append_single', isAddr_node_padList_iff]
        exact Or.inl (Or.inl ⟨hi, isAddr_padT k _ z hz⟩)
      · rw [if_pos rfl, isAddr_node_append_single']
        exact Or.inr ⟨rfl, isAddr_gPadMap k (r :: rest) z hz⟩

/-- The retraction lands in the realisation. -/
lemma isAddr_gPadInv (k : ℕ) : ∀ L : List (List RTree), ∀ y,
    IsAddr (GShape.realiseAux (padDecs k L)) y → IsAddr (GShape.realiseAux L) (gPadInv k L y)
  | [], y, hy => hy
  | [β], y, hy => hy
  | β :: r :: rest, [], _ => by rw [gPadInv_cons_cons_nil]; exact isAddr_nil _
  | β :: r :: rest, i :: z, hy => by
      rw [padDecs_cons_cons, realiseAux_cons_of_ne_nil _ (padDecs_ne_nil k (by simp)),
        isAddr_node_append_single', isAddr_node_padList_iff] at hy
      rw [realiseAux_cons_of_ne_nil _ (by simp), gPadInv_cons_cons_cons]
      have hle := length_le_length_padList k β
      rcases hy with (⟨hi, hz⟩ | ⟨hi, hi', -⟩) | ⟨rfl, hz⟩
      · rw [if_neg (by omega), if_pos hi, getD_eq_getElem_of_lt hi, isAddr_node_append_single',
          isAddr_cons]
        exact Or.inl ⟨hi, isAddr_padInv k _ z hz⟩
      · rw [if_neg (by omega), if_neg (by omega)]
        exact isAddr_nil _
      · rw [if_pos rfl, isAddr_node_append_single']
        exact Or.inr ⟨rfl, isAddr_gPadInv k (r :: rest) z hz⟩

/-- The retraction inverts the address map. -/
lemma gPadInv_gPadMap (k : ℕ) : ∀ L : List (List RTree), ∀ w, IsAddr (GShape.realiseAux L) w →
    gPadInv k L (gPadMap k L w) = w
  | [], _, _ => rfl
  | [β], _, _ => rfl
  | β :: r :: rest, [], _ => rfl
  | β :: r :: rest, i :: z, hw => by
      rw [realiseAux_cons_of_ne_nil _ (by simp), isAddr_node_append_single'] at hw
      rw [gPadMap_cons_cons_cons]
      have hle := length_le_length_padList k β
      rcases hw with hw | ⟨rfl, hz⟩
      · rw [isAddr_cons] at hw
        obtain ⟨hi, hz⟩ := hw
        rw [if_neg (by omega), gPadInv_cons_cons_cons, if_neg (by omega), if_pos hi,
          getD_eq_getElem_of_lt hi, padInv_of_isAddr _ z hz]
      · rw [if_pos rfl, gPadInv_cons_cons_cons, if_pos rfl, gPadInv_gPadMap k (r :: rest) z hz]

/-- The address map sends parent-child pairs to parent-child pairs. -/
lemma addrDist_gPadMap_append (k : ℕ) : ∀ L : List (List RTree), ∀ u a,
    IsAddr (GShape.realiseAux L) (u ++ [a]) → addrDist (gPadMap k L (u ++ [a])) (gPadMap k L u) ≤ 1
  | [], u, a, _ => by simp
  | [β], u, a, _ => by simp
  | β :: r :: rest, [], a, _ => by
      rw [List.nil_append, gPadMap_cons_cons_cons, gPadMap_cons_cons_nil]
      by_cases h : a = β.length
      · rw [if_pos h, gPadMap_nil]; simp
      · rw [if_neg h]; simp
  | β :: r :: rest, i :: u, a, hw => by
      rw [List.cons_append, realiseAux_cons_of_ne_nil _ (by simp),
        isAddr_node_append_single'] at hw
      rw [List.cons_append, gPadMap_cons_cons_cons, gPadMap_cons_cons_cons]
      rcases hw with hw | ⟨rfl, hz⟩
      · rw [isAddr_cons] at hw
        obtain ⟨hi, -⟩ := hw
        rw [if_neg (by omega), if_neg (by omega)]
        simp
      · rw [if_pos rfl, if_pos rfl, addrDist_cons_cons_self]
        exact addrDist_gPadMap_append k (r :: rest) u a hz

/-- The retraction moves parent-child pairs by at most one. -/
lemma addrDist_gPadInv_append (k : ℕ) : ∀ L : List (List RTree), ∀ y b,
    IsAddr (GShape.realiseAux (padDecs k L)) (y ++ [b]) →
    addrDist (gPadInv k L (y ++ [b])) (gPadInv k L y) ≤ 1
  | [], y, b, _ => by simp
  | [β], y, b, _ => by simp
  | β :: r :: rest, [], b, _ => by
      rw [List.nil_append, gPadInv_cons_cons_cons, gPadInv_cons_cons_nil]
      by_cases h : b = (padList k β).length
      · rw [if_pos h, gPadInv_nil]; simp
      · rw [if_neg h]
        by_cases h' : b < β.length
        · rw [if_pos h', padInv_nil']; simp
        · rw [if_neg h']; simp
  | β :: r :: rest, i :: y, b, hy => by
      rw [List.cons_append, padDecs_cons_cons,
        realiseAux_cons_of_ne_nil _ (padDecs_ne_nil k (by simp)),
        isAddr_node_append_single', isAddr_node_padList_iff] at hy
      rw [List.cons_append, gPadInv_cons_cons_cons, gPadInv_cons_cons_cons]
      have hle := length_le_length_padList k β
      rcases hy with (⟨hi, hz⟩ | ⟨-, -, h⟩) | ⟨rfl, hz⟩
      · simp only [if_neg (show ¬ i = (padList k β).length by omega), if_pos hi,
          getD_eq_getElem_of_lt hi, addrDist_cons_cons_self]
        exact addrDist_padInv_append k _ y b hz
      · exact absurd h (by simp)
      · rw [if_pos rfl, if_pos rfl, addrDist_cons_cons_self]
        exact addrDist_gPadInv_append k (r :: rest) y b hz

/-- The image is `1`-dense: every added leaf is one step from its parent. -/
lemma addrDist_gPadMap_gPadInv (k : ℕ) : ∀ L : List (List RTree), ∀ y,
    IsAddr (GShape.realiseAux (padDecs k L)) y → addrDist (gPadMap k L (gPadInv k L y)) y ≤ 1
  | [], y, _ => by simp
  | [β], y, _ => by simp
  | β :: r :: rest, [], _ => by simp
  | β :: r :: rest, i :: z, hy => by
      rw [padDecs_cons_cons, realiseAux_cons_of_ne_nil _ (padDecs_ne_nil k (by simp)),
        isAddr_node_append_single', isAddr_node_padList_iff] at hy
      rw [gPadInv_cons_cons_cons]
      have hle := length_le_length_padList k β
      rcases hy with (⟨hi, hz⟩ | ⟨hi, hi', rfl⟩) | ⟨rfl, hz⟩
      · rw [if_neg (show ¬ i = (padList k β).length by omega), if_pos hi, getD_eq_getElem_of_lt hi,
          gPadMap_cons_cons_cons, if_neg (show ¬ i = β.length by omega), addrDist_cons_cons_self]
        exact addrDist_padInv_self k _ z hz
      · rw [if_neg (show ¬ i = (padList k β).length by omega), if_neg (show ¬ i < β.length by omega),
          gPadMap_cons_cons_nil]
        simp
      · rw [if_pos rfl, gPadMap_cons_cons_cons, if_pos rfl, addrDist_cons_cons_self]
        exact addrDist_gPadMap_gPadInv k (r :: rest) z hz

/-- **The padding is a `1`-marked quasi-isometry**: the address map is an embedding
with `1`-dense image carrying the entry to the entry and the exit to the exit. -/
theorem markedQI_gPad (k : ℕ) (σ : GShape) :
    MarkedQI 1 (gShapeSpace σ) (gShapeSpace (gPad k σ)) := by
  rw [gShapeSpace_gPad]
  have h := markedQI_gSpace_of_addrMaps (K := 1) le_rfl (gPadMap k σ.decs) (gPadInv k σ.decs)
    (isAddr_gPadMap k σ.decs) (isAddr_gPadInv k σ.decs)
    (addrDist_gPadMap_append k σ.decs) (addrDist_gPadInv_append k σ.decs)
    (gPadInv_gPadMap k σ.decs) (addrDist_gPadMap_gPadInv k σ.decs)
    (by rw [gPadMap_nil]; simp)
    (isAddr_realiseAux_gExitAddr σ.decs) (isAddr_realiseAux_gExitAddr _)
    (by rw [gExitAddr_padDecs]; simp)
  exact_mod_cast h

/-! ### The binarisation: left child, right sibling -/

namespace RTree

/-- A node widened by a forest: its children followed by the forest. -/
def graft : RTree → List RTree → RTree
  | .node xs, ys => .node (xs ++ ys)

@[simp] lemma graft_node (xs ys : List RTree) : graft (.node xs) ys = .node (xs ++ ys) := rfl

mutual

/-- **The binarisation**: the root keeps its first child, at index `0`, and each vertex
carries its first child at index `0` and its next sibling at the index after that, so
that every vertex has at most two children and no vertex is added. -/
def lcrs : RTree → RTree
  | .node cs => .node (lcrsF cs)

/-- The spine of a forest: its first tree binarised and widened by the spine of the
rest, as a list of at most one tree. -/
def lcrsF : List RTree → List RTree
  | [] => []
  | c :: cs => [graft (lcrs c) (lcrsF cs)]

end

@[simp] lemma lcrs_node (cs : List RTree) : lcrs (.node cs) = .node (lcrsF cs) := by rw [lcrs]
@[simp] lemma lcrsF_nil : lcrsF [] = [] := by rw [lcrsF]
@[simp] lemma lcrsF_cons (c : RTree) (cs : List RTree) :
    lcrsF (c :: cs) = [graft (lcrs c) (lcrsF cs)] := by rw [lcrsF]

/-- The index of the sibling slot of a vertex: `1` when it has children, `0` otherwise. -/
def sib : RTree → ℕ
  | .node ds => (lcrsF ds).length

@[simp] lemma sib_node (ds : List RTree) : sib (.node ds) = (lcrsF ds).length := rfl

lemma length_lcrsF_le_one (cs : List RTree) : (lcrsF cs).length ≤ 1 := by
  cases cs <;> simp

/-- **The binarisation adds no vertex.** -/
theorem size_lcrs (t : RTree) : (lcrs t).size = t.size := by
  have key : ∀ cs : List RTree, (∀ c ∈ cs, (lcrs c).size = c.size) →
      sizeF (lcrsF cs) = sizeF cs := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
        intro hall
        obtain ⟨ds⟩ := c
        have h1 := hall (.node ds) (by simp)
        have h2 := ih fun x hx => hall x (by simp [hx])
        rw [lcrs_node, size_node, size_node] at h1
        rw [lcrsF_cons, lcrs_node, graft_node, sizeF_cons, sizeF_nil, size_node, sizeF_append,
          h2, sizeF_cons, size_node]
        omega
  induction t using RTree.ind with
  | _ cs ih => rw [lcrs_node, size_node, size_node, key cs ih]

/-- **The binarisation is binary.** -/
theorem degLe_two_lcrs (t : RTree) : DegLe 2 (lcrs t) := by
  have key : ∀ cs : List RTree, (∀ c ∈ cs, DegLe 2 (lcrs c)) → ∀ x ∈ lcrsF cs, DegLe 2 x := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
        intro hall x hx
        obtain ⟨ds⟩ := c
        rw [lcrsF_cons, lcrs_node, graft_node, List.mem_singleton] at hx
        subst hx
        obtain ⟨hlen, hmem⟩ := hall (.node ds) (by simp)
        refine ⟨?_, ?_⟩
        · rw [List.length_append]
          have := length_lcrsF_le_one ds
          have := length_lcrsF_le_one cs
          omega
        · intro y hy
          rw [List.mem_append] at hy
          rcases hy with hy | hy
          · exact hmem y hy
          · exact ih (fun x hx => hall x (by simp [hx])) y hy
  induction t using RTree.ind with
  | _ cs ih =>
      rw [lcrs_node]
      exact ⟨(length_lcrsF_le_one cs).trans (by norm_num), key cs ih⟩

/-! ### The address map of the binarisation -/

mutual

/-- **The address map of the binarisation**: a step to the `j`-th child becomes a step
into the child slot followed by `j` steps along the sibling slots. -/
def lcrsAddr : RTree → List ℕ → List ℕ
  | _, [] => []
  | .node cs, j :: w => 0 :: lcrsAddrF cs j w

/-- The address of a vertex of the `j`-th tree of a forest inside the spine of the
forest. -/
def lcrsAddrF : List RTree → ℕ → List ℕ → List ℕ
  | [], _, _ => []
  | c :: _, 0, w => lcrsAddr c w
  | c :: cs, i + 1, w => sib c :: lcrsAddrF cs i w

end

@[simp] lemma lcrsAddr_nil (t : RTree) : lcrsAddr t [] = [] := by cases t; rw [lcrsAddr]
@[simp] lemma lcrsAddr_cons (cs : List RTree) (j : ℕ) (w : List ℕ) :
    lcrsAddr (.node cs) (j :: w) = 0 :: lcrsAddrF cs j w := by rw [lcrsAddr]
@[simp] lemma lcrsAddrF_nil (j : ℕ) (w : List ℕ) : lcrsAddrF [] j w = [] := by rw [lcrsAddrF]
@[simp] lemma lcrsAddrF_cons_zero (c : RTree) (cs : List RTree) (w : List ℕ) :
    lcrsAddrF (c :: cs) 0 w = lcrsAddr c w := by rw [lcrsAddrF]
@[simp] lemma lcrsAddrF_cons_succ (c : RTree) (cs : List RTree) (i : ℕ) (w : List ℕ) :
    lcrsAddrF (c :: cs) (i + 1) w = sib c :: lcrsAddrF cs i w := by rw [lcrsAddrF]

lemma lcrsAddrF_zero_nil (cs : List RTree) : lcrsAddrF cs 0 [] = [] := by
  cases cs <;> simp

/-- The address inside the spine is the root of the tree followed by the address inside
it. -/
lemma lcrsAddrF_eq_append : ∀ (cs : List RTree) (j : ℕ) (w : List ℕ) (hj : j < cs.length),
    lcrsAddrF cs j w = lcrsAddrF cs j [] ++ lcrsAddr cs[j] w
  | [], j, _, hj => by simp at hj
  | c :: cs, 0, w, _ => by simp
  | c :: cs, i + 1, w, hj => by
      rw [lcrsAddrF_cons_succ, lcrsAddrF_cons_succ, List.cons_append,
        lcrsAddrF_eq_append cs i w (by simpa using hj)]
      rfl

/-- The root of the `j`-th tree sits `j` steps along the spine. -/
lemma length_lcrsAddrF_nil : ∀ (cs : List RTree) (j : ℕ), j < cs.length →
    (lcrsAddrF cs j []).length = j
  | [], j, hj => by simp at hj
  | c :: cs, 0, _ => by simp
  | c :: cs, i + 1, hj => by
      rw [lcrsAddrF_cons_succ, List.length_cons, length_lcrsAddrF_nil cs i (by simpa using hj)]

/-- The next root along the spine is one sibling step further. -/
lemma lcrsAddrF_nil_succ : ∀ (cs : List RTree) (i : ℕ) (hi : i + 1 < cs.length),
    lcrsAddrF cs (i + 1) [] = lcrsAddrF cs i [] ++ [sib cs[i]]
  | [], i, hi => by simp at hi
  | c :: cs, 0, _ => by simp [lcrsAddrF_zero_nil]
  | c :: cs, i + 1, hi => by
      rw [lcrsAddrF_cons_succ, lcrsAddrF_cons_succ, lcrsAddrF_nil_succ cs i (by simpa using hi),
        List.cons_append]
      rfl

/-- An address of a node is an address of the node widened by a forest. -/
lemma isAddr_node_append_left {xs : List RTree} (ys : List RTree) : ∀ {v : List ℕ},
    IsAddr (.node xs) v → IsAddr (.node (xs ++ ys)) v
  | [], _ => isAddr_nil _
  | k :: z, hv => by
      rw [isAddr_cons] at hv ⊢
      obtain ⟨hk, hz⟩ := hv
      refine ⟨by simp; omega, ?_⟩
      rwa [List.getElem_append_left hk]

/-- **The address map lands in the binarisation.** -/
theorem isAddr_lcrsAddr (t : RTree) : ∀ w, IsAddr t w → IsAddr (lcrs t) (lcrsAddr t w) := by
  induction t using RTree.ind with
  | _ cs ih =>
      have key : ∀ l : List RTree, (∀ c ∈ l, ∀ w, IsAddr c w → IsAddr (lcrs c) (lcrsAddr c w)) →
          ∀ j w, ∀ hj : j < l.length, IsAddr l[j] w →
            IsAddr (.node (lcrsF l)) (0 :: lcrsAddrF l j w) := by
        intro l
        induction l with
        | nil => intro _ j _ hj; simp at hj
        | cons c l ihl =>
            intro hall j w hj hw
            obtain ⟨ds⟩ := c
            rw [lcrsF_cons, lcrs_node, graft_node, isAddr_cons]
            refine ⟨by simp, ?_⟩
            simp only [List.getElem_cons_zero]
            cases j with
            | zero =>
                rw [lcrsAddrF_cons_zero]
                have := hall (.node ds) (by simp) w hw
                rw [lcrs_node] at this
                exact isAddr_node_append_left _ this
            | succ i =>
                rw [lcrsAddrF_cons_succ]
                have hi : i < l.length := by simpa using hj
                have hne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
                obtain ⟨Y, hY⟩ : ∃ Y, lcrsF l = [Y] := by
                  cases l with
                  | nil => exact absurd rfl hne
                  | cons d l => exact ⟨_, lcrsF_cons d l⟩
                have h2 := ihl (fun x hx => hall x (by simp [hx])) i w hi (by simpa using hw)
                rw [hY, isAddr_cons] at h2
                obtain ⟨hlt, h3⟩ := h2
                rw [hY, isAddr_node_append_single]
                exact Or.inr ⟨sib_node ds, by simpa using h3⟩
      intro w hw
      cases w with
      | nil => exact isAddr_nil _
      | cons j w =>
          rw [isAddr_cons] at hw
          obtain ⟨hj, hw⟩ := hw
          rw [lcrsAddr_cons, lcrs_node]
          exact key cs ih j w hj hw

/-- A vertex below the root has a sibling slot at index one. -/
lemma sib_eq_one_of_isAddr_cons {ds : List RTree} {k : ℕ} {z : List ℕ}
    (h : IsAddr (.node ds) (k :: z)) : sib (.node ds) = 1 := by
  rw [isAddr_cons] at h
  obtain ⟨hk, -⟩ := h
  cases ds with
  | nil => simp at hk
  | cons d ds => simp

/-- **The address map is injective on addresses.** -/
theorem lcrsAddr_inj (t : RTree) : ∀ u v, IsAddr t u → IsAddr t v →
    lcrsAddr t u = lcrsAddr t v → u = v := by
  induction t using RTree.ind with
  | _ cs ih =>
      have key : ∀ l : List RTree,
          (∀ c ∈ l, ∀ u v, IsAddr c u → IsAddr c v → lcrsAddr c u = lcrsAddr c v → u = v) →
          ∀ j j' w w', ∀ hj : j < l.length, ∀ hj' : j' < l.length, IsAddr l[j] w → IsAddr l[j'] w' →
            lcrsAddrF l j w = lcrsAddrF l j' w' → j = j' ∧ w = w' := by
        intro l
        induction l with
        | nil => intro _ j _ _ _ hj; simp at hj
        | cons c l ihl =>
            intro hall j j' w w' hj hj' hw hw' heq
            obtain ⟨ds⟩ := c
            cases j with
            | zero =>
                cases j' with
                | zero =>
                    simp only [lcrsAddrF_cons_zero] at heq
                    simp only [List.getElem_cons_zero] at hw hw'
                    exact ⟨rfl, hall _ (by simp) w w' hw hw' heq⟩
                | succ i' =>
                    exfalso
                    simp only [lcrsAddrF_cons_zero, lcrsAddrF_cons_succ] at heq
                    cases w with
                    | nil => simp at heq
                    | cons k z =>
                        simp only [List.getElem_cons_zero] at hw
                        rw [lcrsAddr_cons, sib_eq_one_of_isAddr_cons hw] at heq
                        simp at heq
            | succ i =>
                cases j' with
                | zero =>
                    exfalso
                    simp only [lcrsAddrF_cons_zero, lcrsAddrF_cons_succ] at heq
                    cases w' with
                    | nil => simp at heq
                    | cons k z =>
                        simp only [List.getElem_cons_zero] at hw'
                        rw [lcrsAddr_cons, sib_eq_one_of_isAddr_cons hw'] at heq
                        simp at heq
                | succ i' =>
                    simp only [lcrsAddrF_cons_succ, List.cons.injEq] at heq
                    obtain ⟨h1, h2⟩ := ihl (fun x hx => hall x (by simp [hx])) i i' w w'
                      (by simpa using hj) (by simpa using hj') (by simpa using hw)
                      (by simpa using hw') heq.2
                    exact ⟨by omega, h2⟩
      intro u v hu hv heq
      cases u with
      | nil =>
          cases v with
          | nil => rfl
          | cons j w => simp at heq
      | cons j w =>
          cases v with
          | nil => simp at heq
          | cons j' w' =>
              rw [isAddr_cons] at hu hv
              obtain ⟨hj, hw⟩ := hu
              obtain ⟨hj', hw'⟩ := hv
              simp only [lcrsAddr_cons, List.cons.injEq, true_and] at heq
              obtain ⟨rfl, rfl⟩ := key cs ih j j' w w' hj hj' hw hw' heq
              rfl

/-! ### The subtree at an address and the address map below it -/

/-- The subtree at an address, the single vertex off the tree. -/
def sub : RTree → List ℕ → RTree
  | t, [] => t
  | .node cs, j :: w => sub (cs.getD j (.node [])) w

@[simp] lemma sub_nil (t : RTree) : sub t [] = t := by cases t; rw [sub]
@[simp] lemma sub_cons (cs : List RTree) (j : ℕ) (w : List ℕ) :
    sub (.node cs) (j :: w) = sub (cs.getD j (.node [])) w := by rw [sub]

/-- An address splits at any prefix into the prefix and an address of the subtree. -/
lemma isAddr_append_iff : ∀ (t : RTree) (u v : List ℕ),
    IsAddr t (u ++ v) ↔ IsAddr t u ∧ IsAddr (sub t u) v
  | t, [], v => by simp
  | .node cs, j :: u, v => by
      rw [List.cons_append, isAddr_cons, isAddr_cons, sub_cons]
      by_cases hj : j < cs.length
      · constructor
        · rintro ⟨h, h1⟩
          rw [isAddr_append_iff] at h1
          exact ⟨⟨h, h1.1⟩, by rw [getD_eq_getElem_of_lt hj]; exact h1.2⟩
        · rintro ⟨⟨h, h1⟩, h2⟩
          refine ⟨h, (isAddr_append_iff _ u v).mpr ⟨h1, ?_⟩⟩
          rwa [getD_eq_getElem_of_lt hj] at h2
      · constructor
        · rintro ⟨h, -⟩; exact absurd h hj
        · rintro ⟨⟨h, -⟩, -⟩; exact absurd h hj

/-- The offspring bound passes to subtrees. -/
lemma degLe_sub {d : ℕ} : ∀ (t : RTree) (u : List ℕ), DegLe d t → IsAddr t u → DegLe d (sub t u)
  | t, [], ht, _ => by simpa using ht
  | .node cs, j :: u, ht, hu => by
      rw [isAddr_cons] at hu
      obtain ⟨hj, hu⟩ := hu
      obtain ⟨-, hall⟩ := ht
      rw [sub_cons, getD_eq_getElem_of_lt hj]
      exact degLe_sub cs[j] u (hall _ (List.getElem_mem hj)) hu

/-- **The address map below an address**: the image of an address of the subtree is
appended to the image of the address. -/
lemma lcrsAddr_append : ∀ (t : RTree) (u v : List ℕ), IsAddr t u →
    lcrsAddr t (u ++ v) = lcrsAddr t u ++ lcrsAddr (sub t u) v
  | t, [], v, _ => by simp
  | .node cs, j :: u, v, hu => by
      rw [isAddr_cons] at hu
      obtain ⟨hj, hu⟩ := hu
      rw [List.cons_append, lcrsAddr_cons, lcrsAddr_cons, sub_cons, getD_eq_getElem_of_lt hj,
        lcrsAddrF_eq_append cs j (u ++ v) hj, lcrsAddrF_eq_append cs j u hj,
        lcrsAddr_append cs[j] u v hu, List.cons_append, List.append_assoc]

/-- The image of a child: one step into the child slot and `a` sibling steps. -/
lemma lcrsAddr_concat {t : RTree} {u : List ℕ} {a : ℕ} (hu : IsAddr t (u ++ [a])) :
    ∃ cs : List RTree, sub t u = .node cs ∧ a < cs.length ∧
      lcrsAddr t (u ++ [a]) = lcrsAddr t u ++ 0 :: lcrsAddrF cs a [] := by
  rw [isAddr_append_iff] at hu
  obtain ⟨hu, ha⟩ := hu
  obtain ⟨cs, hcs⟩ : ∃ cs, sub t u = .node cs := by
    rcases h : sub t u with ⟨cs⟩
    exact ⟨cs, rfl⟩
  rw [hcs, isAddr_cons] at ha
  obtain ⟨ha, -⟩ := ha
  refine ⟨cs, hcs, ha, ?_⟩
  rw [lcrsAddr_append t u [a] hu, hcs, lcrsAddr_cons]

/-! ### The binarisation as a marked quasi-isometry -/

/-- The address map as a map of vertices. -/
def lcrsVert (t : RTree) (x : Vert t) : Vert (lcrs t) :=
  ⟨lcrsAddr t x.1, mem_addrList_iff.mpr (isAddr_lcrsAddr t x.1 (mem_addrList_iff.mp x.2))⟩

/-- **The binarisation is a bijection on vertices**: the address map is injective and
no vertex is added. -/
theorem lcrsVert_bijective (t : RTree) : Function.Bijective (lcrsVert t) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (lcrsAddr_inj t x.1 y.1 (mem_addrList_iff.mp x.2) (mem_addrList_iff.mp y.2) h')
  · rw [card_vert, card_vert, size_lcrs]

/-- The inverse of the address map on the addresses of the binarisation. -/
noncomputable def lcrsDec (t : RTree) (y : List ℕ) : List ℕ :=
  if h : y ∈ addrList (lcrs t) then
    ((Equiv.ofBijective _ (lcrsVert_bijective t)).symm ⟨y, h⟩).1
  else []

lemma isAddr_lcrsDec (t : RTree) {y : List ℕ} (hy : IsAddr (lcrs t) y) :
    IsAddr t (lcrsDec t y) := by
  rw [lcrsDec, dif_pos (mem_addrList_iff.mpr hy)]
  exact mem_addrList_iff.mp (Subtype.prop _)

lemma lcrsAddr_lcrsDec (t : RTree) {y : List ℕ} (hy : IsAddr (lcrs t) y) :
    lcrsAddr t (lcrsDec t y) = y := by
  rw [lcrsDec, dif_pos (mem_addrList_iff.mpr hy)]
  have := (Equiv.ofBijective _ (lcrsVert_bijective t)).apply_symm_apply ⟨y, mem_addrList_iff.mpr hy⟩
  exact congrArg Subtype.val this

lemma lcrsDec_lcrsAddr (t : RTree) {w : List ℕ} (hw : IsAddr t w) :
    lcrsDec t (lcrsAddr t w) = w := by
  have hmem : lcrsAddr t w ∈ addrList (lcrs t) := mem_addrList_iff.mpr (isAddr_lcrsAddr t w hw)
  rw [lcrsDec, dif_pos hmem]
  have := (Equiv.ofBijective _ (lcrsVert_bijective t)).symm_apply_apply ⟨w, mem_addrList_iff.mpr hw⟩
  exact congrArg Subtype.val this

/-- The address map stretches a parent-child pair to at most `d` steps under the
offspring bound `d`. -/
lemma addrDist_lcrsAddr_concat {d : ℕ} {t : RTree} (ht : DegLe d t) {u : List ℕ} {a : ℕ}
    (hu : IsAddr t (u ++ [a])) : addrDist (lcrsAddr t (u ++ [a])) (lcrsAddr t u) ≤ d := by
  obtain ⟨cs, hcs, ha, heq⟩ := lcrsAddr_concat hu
  have hd : DegLe d (sub t u) := degLe_sub t u ht ((isAddr_append_iff t u [a]).mp hu).1
  rw [hcs] at hd
  obtain ⟨hlen, -⟩ := hd
  rw [heq, addrDist_append_left, List.length_cons, length_lcrsAddrF_nil cs a ha]
  omega

/-- The inverse contracts a parent-child pair of the binarisation to at most two steps:
the parent of the image of a child is the image of the parent or of the previous
sibling. -/
lemma addrDist_lcrsDec_concat {t : RTree} {y : List ℕ} {b : ℕ} (hy : IsAddr (lcrs t) (y ++ [b])) :
    addrDist (lcrsDec t (y ++ [b])) (lcrsDec t y) ≤ 2 := by
  have hwa : IsAddr t (lcrsDec t (y ++ [b])) := isAddr_lcrsDec t hy
  have hweq : lcrsAddr t (lcrsDec t (y ++ [b])) = y ++ [b] := lcrsAddr_lcrsDec t hy
  have hwne : lcrsDec t (y ++ [b]) ≠ [] := by
    rintro hc
    rw [hc, lcrsAddr_nil] at hweq
    simp at hweq
  obtain ⟨u, a, hua⟩ : ∃ u a, lcrsDec t (y ++ [b]) = u ++ [a] :=
    ⟨_, _, (List.dropLast_append_getLast hwne).symm⟩
  rw [hua] at hwa hweq ⊢
  obtain ⟨cs, hcs, ha, heq⟩ := lcrsAddr_concat hwa
  have hu : IsAddr t u := ((isAddr_append_iff t u [a]).mp hwa).1
  cases a with
  | zero =>
      rw [heq, lcrsAddrF_zero_nil] at hweq
      have hy' : y = lcrsAddr t u := (List.append_inj' hweq (by simp)).1.symm
      rw [hy', lcrsDec_lcrsAddr t hu, addrDist_append_left]
      simp
  | succ i =>
      rw [heq, lcrsAddrF_nil_succ cs i ha] at hweq
      have hui : IsAddr t (u ++ [i]) := by
        rw [isAddr_append_iff, hcs, isAddr_cons]
        exact ⟨hu, by omega, isAddr_nil _⟩
      have himg : lcrsAddr t (u ++ [i]) = lcrsAddr t u ++ 0 :: lcrsAddrF cs i [] := by
        rw [lcrsAddr_append t u [i] hu, hcs, lcrsAddr_cons]
      have hweq' : (lcrsAddr t u ++ 0 :: lcrsAddrF cs i []) ++ [sib cs[i]] = y ++ [b] := by
        rw [← hweq]
        simp
      have hy' : y = lcrsAddr t (u ++ [i]) := by
        rw [himg]
        exact (List.append_inj' hweq' (by simp)).1.symm
      rw [hy', lcrsDec_lcrsAddr t hui, addrDist_append_append, addrDist_cons_cons_ne (by omega)]
      simp

end RTree

/-- **`thm:shape-shrink` (`it:shape-shrink`), the binarisation at general
arity**: under the offspring bound `d`, the left-child right-sibling encoding is a
`(d+1)`-marked quasi-isometry of marked rose trees, the mark going to its image. -/
theorem markedQI_lcrs {d : ℕ} (hd : 1 ≤ d) {t : RTree} (ht : DegLe d t) {e : List ℕ}
    (he : e ∈ addrList t) :
    MarkedQI ((d : ℝ) + 1) (gSpace t e) (gSpace (lcrs t) (lcrsAddr t e)) := by
  have he' : IsAddr t e := mem_addrList_iff.mp he
  have h := markedQI_gSpace_of_addrMaps (K := d + 1) (by omega) (lcrsAddr t) (lcrsDec t)
    (isAddr_lcrsAddr t) (fun y hy => isAddr_lcrsDec t hy)
    (fun u a hu => (addrDist_lcrsAddr_concat ht hu).trans (by omega))
    (fun y b hy => (addrDist_lcrsDec_concat hy).trans (by omega))
    (fun w hw => lcrsDec_lcrsAddr t hw)
    (fun y hy => by rw [lcrsAddr_lcrsDec t hy, addrDist_self]; omega)
    (by simp)
    he' (isAddr_lcrsAddr t e he') (by simp)
  exact_mod_cast h

/-! ### The composition -/

/-- **The shrinking map after the contraction**: binarise, build the neck, pad into
the support of the law at arity `k`. -/
def gShrinkOf (k : ℕ) (t : RTree) (e : List ℕ) : GShape :=
  gPad k (gNeckShape (lcrs t) (lcrsAddr t e))

/-- **`thm:shape-shrink` (`it:shape-shrink`), the moves after the contraction at
general arity**: a marked rose tree with offspring at most `d` reaches the shrunk shape
by an `18(d+1)`-marked quasi-isometry, the composition `3·(3·(d+1)·2)·1`. -/
theorem markedQI_gShrinkOf {d : ℕ} (hd : 1 ≤ d) {t : RTree} (ht : DegLe d t) {e : List ℕ}
    (he : e ∈ addrList t) (k : ℕ) :
    MarkedQI (18 * ((d : ℝ) + 1)) (gSpace t e) (gShapeSpace (gShrinkOf k t e)) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have he' : lcrsAddr t e ∈ addrList (lcrs t) :=
    mem_addrList_iff.mpr (isAddr_lcrsAddr t e (mem_addrList_iff.mp he))
  have h1 := markedQI_lcrs hd ht he
  have h2 := markedQI_gNeck he'
  have h3 := markedQI_gPad k (gNeckShape (lcrs t) (lcrsAddr t e))
  have h12 := markedQI_comp hd1 (by norm_num) h1 h2
  have h123 := markedQI_comp (K := 3 * ((d : ℝ) + 1) * 2) (by nlinarith) le_rfl h12 h3
  have e : 3 * (3 * ((d : ℝ) + 1) * 2) * 1 = 18 * ((d : ℝ) + 1) := by ring
  rw [e] at h123
  exact h123

/-- **The size clause**: the shrunk shape has at most `k(|t| + 2)` vertices. -/
theorem size_gShrinkOf_le {k : ℕ} (hk : 1 ≤ k) {t : RTree} {e : List ℕ}
    (he : e ∈ addrList t) : (gShrinkOf k t e).size ≤ k * (t.size + 2) := by
  have he' : IsAddr (lcrs t) (lcrsAddr t e) := isAddr_lcrsAddr t e (mem_addrList_iff.mp he)
  have h1 := size_gPad_le hk (gNeckShape (lcrs t) (lcrsAddr t e))
  have h2 := size_gNeckShape_le he'
  rw [size_lcrs] at h2
  exact h1.trans (Nat.mul_le_mul_left k h2)

/-- **The support clause**: the shrunk shape is charged at arity `k` once leaves and
the arity carry mass. -/
theorem chargedG_gShrinkOf {J : ℕ} {θ : BranchingProcess.Offspring J} {k : ℕ} (h0 : 0 < θ 0)
    (hk : 0 < θ k) (hk2 : 2 ≤ k) {t : RTree} {e : List ℕ} (he : e ∈ addrList t) :
    GShape.ChargedG θ k (gShrinkOf k t e) := by
  have he' : IsAddr (lcrs t) (lcrsAddr t e) := isAddr_lcrsAddr t e (mem_addrList_iff.mp he)
  refine chargedG_gPad h0 hk (by omega) (fun β hβ => ?_) (bouquet_gNeckShape _ _)
  obtain ⟨hlen, hall⟩ := gNeckShape_neckList_degLe_two he' (degLe_two_lcrs t) β hβ
  exact ⟨by omega, fun b hb => (hall b hb).mono (by omega)⟩

end ChainClasses
