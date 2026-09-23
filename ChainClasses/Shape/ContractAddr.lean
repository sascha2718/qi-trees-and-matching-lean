import Mathlib.Tactic
import ChainClasses.Shape.ContractTree

/-!
`sec:shape-net` of `matching_classes_simple.tex`: `thm:dilution`, the step that
makes the count bite and the lemma itself.

The marked contraction `Tri.contractPair` of `ContractTree.lean` is a rose tree
with one vertex marked, and the count `dilution_count` is a count of such data.
What is missing is that the datum determines the contracted tree of
`Contraction.lean` as a marked metric space.  A rose tree is therefore given an
address layer over `List ℕ`, and the two depth-first recursions of
`ContractTree.lean`, the one listing the part roots and the one building the
rose tree, are shown to read the tree in the same order.  The resulting pairing
of part roots with addresses carries the part-parent to the parent, hence is an
isomorphism of trees, hence an isometry; the marks match by construction, and
two shapes with the same marked contraction are `72s³`-comparable.

* `RTree.addrList` with `RTree.addrListF`: the addresses of a rose tree and of
  a forest, listed in the order the recursion of `Tri.contractTree` reads them.
  `RTree.IsAddr` is the address predicate, `mem_addrList_iff` the
  identification, `dropLast_mem_addrList` the closure under taking parents,
  `rtreeGraph` the parent-child graph they carry with `rtreeGraph_connected`
  its connectivity, and `rtreeSpace` the marked metric space of a marked rose
  tree.
* `pairList`, with `cutPairs` and `rootPairs` for the two auxiliary recursions:
  the part roots of `Tri.partList` paired with those addresses.
  `part_dropLast_mem_pairList` is the key, and `partAddr` with `addrPart` reads
  the pairing as a pair of mutually inverse maps.
* `toVert`, `dist_toVert`, `isMarkedIsom_toVert`: the contracted tree
  `partGraph s T` of `Contraction.lean` is the rose tree `Tri.contractTree s T`
  as a marked metric space.
* `markedQI_of_shapeContractPair_eq`: two shapes with the same marked
  contraction are `72s³`-comparable, the composition
  `3·2s·3(2s)²` of `thm:shape-net`.
* `dilution`, `dilution_netMem`: **`thm:dilution`**, over the scale
  `dilScale`, `s = ⌊(D/72)^{1/3}⌋`, and, in the crude regime `D ≤ 729`, the
  scale one at which `contractTree_one_injective` makes the contraction the
  realisation itself.
-/

namespace ChainClasses

open SimpleGraph

namespace RTree

/-! ### Addresses of a rose tree -/

/-- Shift the first letter of an address, the empty address unchanged: the
relabelling that appends one forest to another. -/
def bump (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | i :: w => (n + i) :: w

@[simp] lemma bump_nil (n : ℕ) : bump n [] = [] := rfl

@[simp] lemma bump_cons (n i : ℕ) (w : List ℕ) : bump n (i :: w) = (n + i) :: w := rfl

@[simp] lemma bump_zero (w : List ℕ) : bump 0 w = w := by
  cases w <;> simp

lemma bump_bump (m n : ℕ) (w : List ℕ) : bump m (bump n w) = bump (m + n) w := by
  cases w <;> simp [Nat.add_assoc]

@[simp] lemma bump_eq_nil_iff {n : ℕ} {w : List ℕ} : bump n w = [] ↔ w = [] := by
  cases w <;> simp

/-- The shift commutes with dropping the last letter. -/
lemma dropLast_bump (n : ℕ) (w : List ℕ) : (bump n w).dropLast = bump n w.dropLast := by
  cases w with
  | nil => simp
  | cons i w => cases w <;> simp

lemma bump_injective (n : ℕ) {w w' : List ℕ} (hw : w ≠ []) (hw' : w' ≠ [])
    (h : bump n w = bump n w') : w = w' := by
  cases w with
  | nil => exact absurd rfl hw
  | cons i v =>
      cases w' with
      | nil => exact absurd rfl hw'
      | cons j v' =>
          simp only [bump_cons, List.cons.injEq] at h
          exact by rw [h.2]; congr 1; omega

mutual

/-- The addresses of a rose tree, in the order the depth-first recursion reads
them: the root, then the addresses of the children in order. -/
def addrList : RTree → List (List ℕ)
  | .node cs => [] :: addrListF cs

/-- The addresses of the vertices of a forest, the index of the tree prefixed
to each. -/
def addrListF : List RTree → List (List ℕ)
  | [] => []
  | c :: cs => (addrList c).map (fun w => 0 :: w) ++ (addrListF cs).map (bump 1)

end

@[simp] lemma addrList_node (cs : List RTree) : addrList (.node cs) = [] :: addrListF cs := by
  rw [addrList]

@[simp] lemma addrListF_nil : addrListF [] = [] := by rw [addrListF]

@[simp] lemma addrListF_cons (c : RTree) (cs : List RTree) :
    addrListF (c :: cs) =
      (addrList c).map (fun w => 0 :: w) ++ (addrListF cs).map (bump 1) := by
  rw [addrListF]

/-- The addresses of a forest are counted by its vertices. -/
lemma length_addrListF : ∀ F : List RTree, (addrListF F).length = sizeF F
  | [] => by simp
  | c :: cs => by
      have hc : (addrList c).length = c.size := by
        cases c with
        | node ds =>
            rw [addrList_node, List.length_cons, length_addrListF ds, size_node]
            omega
      simp only [addrListF_cons, List.length_append, List.length_map, hc,
        length_addrListF cs, RTree.sizeF_cons]

/-- The addresses of a tree are counted by its vertices. -/
@[simp] lemma length_addrList (t : RTree) : (addrList t).length = t.size := by
  cases t with
  | node cs =>
      rw [addrList_node, List.length_cons, length_addrListF cs, size_node]
      omega

/-- Appending forests shifts the addresses of the second block. -/
lemma addrListF_append : ∀ F G : List RTree,
    addrListF (F ++ G) = addrListF F ++ (addrListF G).map (bump F.length)
  | [], G => by
      simp only [List.nil_append, addrListF_nil, List.length_nil]
      rw [show bump 0 = id from funext bump_zero, List.map_id]
  | c :: cs, G => by
      have hfun : (bump 1) ∘ (bump cs.length) = bump (cs.length + 1) := by
        funext w
        simp only [Function.comp_apply, bump_bump]
        congr 1
        omega
      simp only [List.cons_append, addrListF_cons, addrListF_append cs G, List.map_append,
        List.map_map, List.append_assoc, List.length_cons, hfun]

/-- Every address of a forest is nonempty. -/
lemma ne_nil_of_mem_addrListF : ∀ {F : List RTree} {w : List ℕ}, w ∈ addrListF F → w ≠ []
  | c :: cs, w, h => by
      rw [addrListF_cons, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨v, -, rfl⟩ := List.mem_map.mp h
        simp
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
        have := ne_nil_of_mem_addrListF hv
        cases v with
        | nil => exact absurd rfl this
        | cons i v => simp

/-- The blocks of a forest are listed once each once its trees are. -/
lemma nodup_addrListF_of : ∀ F : List RTree, (∀ c ∈ F, (addrList c).Nodup) →
    (addrListF F).Nodup
  | [], _ => by simp
  | c :: cs, hall => by
      have h1 : ((addrList c).map (fun w => 0 :: w)).Nodup :=
        (hall c (by simp)).map (fun _ _ h => by simpa using h)
      have h2 : ((addrListF cs).map (bump 1)).Nodup := by
        refine (nodup_addrListF_of cs fun x hx => hall x (by simp [hx])).map_on ?_
        intro a ha b hb h
        exact bump_injective 1 (ne_nil_of_mem_addrListF ha) (ne_nil_of_mem_addrListF hb) h
      refine List.Nodup.append h1 h2 ?_
      intro x hx hx'
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨u, hu, hueq⟩ := List.mem_map.mp hx'
      have hne := ne_nil_of_mem_addrListF hu
      cases u with
      | nil => exact absurd rfl hne
      | cons j u => simp only [bump_cons, List.cons.injEq] at hueq; omega

/-- The addresses of a tree are listed once each. -/
lemma nodup_addrList (t : RTree) : (addrList t).Nodup := by
  induction t using ind with
  | _ cs ih =>
      rw [addrList_node]
      exact List.nodup_cons.mpr ⟨fun h => ne_nil_of_mem_addrListF h rfl,
        nodup_addrListF_of cs ih⟩

/-! ### The address predicate -/

/-- The addresses of a rose tree: the root, and a letter naming a child of the
root followed by an address of that child. -/
def IsAddr : RTree → List ℕ → Prop
  | _, [] => True
  | .node cs, i :: w => ∃ h : i < cs.length, IsAddr cs[i] w
termination_by _ w => w.length

@[simp] lemma isAddr_nil (t : RTree) : IsAddr t [] := by
  cases t with | node cs => rw [IsAddr]; trivial

lemma isAddr_cons {cs : List RTree} {i : ℕ} {w : List ℕ} :
    IsAddr (.node cs) (i :: w) ↔ ∃ h : i < cs.length, IsAddr cs[i] w := by
  rw [IsAddr]

/-- The addresses of a forest, named by the tree they belong to. -/
lemma mem_addrListF_iff : ∀ {F : List RTree} {w : List ℕ},
    w ∈ addrListF F ↔ ∃ i, ∃ h : i < F.length, ∃ v, v ∈ addrList F[i] ∧ w = i :: v
  | [], w => by simp
  | c :: cs, w => by
      rw [addrListF_cons, List.mem_append]
      constructor
      · rintro (h | h)
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
          exact ⟨0, by simp, v, hv, rfl⟩
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
          obtain ⟨j, hj, v, hv, rfl⟩ := mem_addrListF_iff.mp hu
          refine ⟨j + 1, by simpa using hj, v, ?_, ?_⟩
          · simpa using hv
          · simp only [bump_cons]
            congr 1
            omega
      · rintro ⟨i, hi, v, hv, rfl⟩
        cases i with
        | zero => exact Or.inl (List.mem_map.mpr ⟨v, by simpa using hv, rfl⟩)
        | succ j =>
            refine Or.inr (List.mem_map.mpr
              ⟨j :: v, mem_addrListF_iff.mpr ⟨j, ?_, v, ?_, rfl⟩, ?_⟩)
            · simpa using hi
            · simpa using hv
            · simp only [bump_cons]
              congr 1
              omega

/-- **The listed addresses are exactly the addresses.** -/
theorem mem_addrList_iff : ∀ {t : RTree} {w : List ℕ}, w ∈ addrList t ↔ IsAddr t w
  | .node cs, [] => by simp
  | .node cs, i :: w => by
      rw [addrList_node, List.mem_cons, isAddr_cons]
      constructor
      · rintro (h | h)
        · exact absurd h.symm (by simp)
        · obtain ⟨j, hj, v, hv, heq⟩ := mem_addrListF_iff.mp h
          simp only [List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact ⟨hj, mem_addrList_iff.mp hv⟩
      · rintro ⟨hi, hw⟩
        exact Or.inr (mem_addrListF_iff.mpr ⟨i, hi, w, mem_addrList_iff.mpr hw, rfl⟩)

/-! ### The address set is closed under taking parents -/

/-- The root is an address. -/
@[simp] lemma nil_mem_addrList (t : RTree) : ([] : List ℕ) ∈ addrList t := by
  cases t with | node cs => rw [addrList_node]; exact List.mem_cons_self

/-- The parent of an address of a forest is either an address of that forest or
the root of the enclosing tree. -/
lemma dropLast_mem_addrListF_of : ∀ F : List RTree,
    (∀ c ∈ F, ∀ w ∈ addrList c, w.dropLast ∈ addrList c) →
    ∀ w ∈ addrListF F, w.dropLast = [] ∨ w.dropLast ∈ addrListF F
  | [], _, w, hw => by simp at hw
  | c :: cs, hall, w, hw => by
      rw [addrListF_cons, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        cases v with
        | nil => exact Or.inl rfl
        | cons i v =>
            refine Or.inr ?_
            rw [addrListF_cons, List.mem_append]
            refine Or.inl (List.mem_map.mpr ⟨(i :: v).dropLast, hall c (by simp) _ hv, ?_⟩)
            simp
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        rw [dropLast_bump]
        rcases dropLast_mem_addrListF_of cs (fun x hx => hall x (by simp [hx])) v hv with h | h
        · rw [h]; exact Or.inl rfl
        · refine Or.inr ?_
          rw [addrListF_cons, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨v.dropLast, h, rfl⟩)

/-- **The address set is closed under taking parents.** -/
lemma dropLast_mem_addrList (t : RTree) : ∀ w ∈ addrList t, w.dropLast ∈ addrList t := by
  induction t using ind with
  | _ cs ih =>
      intro w hw
      rw [addrList_node, List.mem_cons] at hw
      rcases hw with rfl | hw
      · simp
      · rcases dropLast_mem_addrListF_of cs ih w hw with h | h
        · rw [h]; simp
        · rw [addrList_node]; exact List.mem_cons_of_mem _ h

/-- A vertex of a rose tree: an address. -/
@[implicit_reducible]
def Vert (t : RTree) : Type := {w : List ℕ // w ∈ addrList t}

/-- **The parent-child graph of a rose tree**, read on addresses: a vertex is
joined to the vertex one letter above it. -/
def rtreeGraph (t : RTree) : SimpleGraph (Vert t) where
  Adj x y := x ≠ y ∧ (x.1 = y.1.dropLast ∨ y.1 = x.1.dropLast)
  symm := ⟨fun {_ _} h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun {_} h => h.1 rfl⟩

@[simp] lemma rtreeGraph_adj {t : RTree} {x y : Vert t} :
    (rtreeGraph t).Adj x y ↔ x ≠ y ∧ (x.1 = y.1.dropLast ∨ y.1 = x.1.dropLast) := Iff.rfl

/-- The root of a rose tree, as a vertex. -/
def rootVert (t : RTree) : Vert t := ⟨[], nil_mem_addrList t⟩

/-- **The parent-child graph is connected**: every address climbs to the
root. -/
theorem rtreeGraph_connected (t : RTree) : (rtreeGraph t).Connected := by
  have key : ∀ (n : ℕ) (x : Vert t), x.1.length ≤ n →
      (rtreeGraph t).Reachable (rootVert t) x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have : x.1 = [] := List.length_eq_zero_iff.mp (by omega)
        exact (Subtype.ext this : x = rootVert t).symm ▸ Reachable.refl _
    | succ n ih =>
        intro x hx
        rcases eq_or_ne x.1 ([] : List ℕ) with h | h
        · exact (Subtype.ext h : x = rootVert t).symm ▸ Reachable.refl _
        · have hlen : x.1.dropLast.length + 1 = x.1.length := by
            rw [List.length_dropLast]
            have : 0 < x.1.length := List.length_pos_iff.mpr h
            omega
          set y : Vert t := ⟨x.1.dropLast, dropLast_mem_addrList t x.1 x.2⟩ with hy
          have hne : y ≠ x := by
            intro hc
            rw [hc] at hy
            have := congrArg (fun z : Vert t => z.1.length) hy
            simp only at this
            omega
          exact (ih y (by simp only [hy]; omega)).trans
            (Adj.reachable ⟨hne, Or.inl rfl⟩)
  have : Nonempty (Vert t) := ⟨rootVert t⟩
  exact ⟨fun x y => (key x.1.length x le_rfl).symm.trans (key y.1.length y le_rfl)⟩

/-- **The metric of a rose tree** read on addresses. -/
noncomputable instance instMetricSpaceVert (t : RTree) : MetricSpace (Vert t) where
  dist x y := ((rtreeGraph t).dist x y : ℝ)
  dist_self x := by simp
  dist_comm x y := by simp only [SimpleGraph.dist_comm]
  dist_triangle x y z := by
    have := (rtreeGraph_connected t).dist_triangle (u := x) (v := y) (w := z)
    exact_mod_cast this
  eq_of_dist_eq_zero {x y} h := by
    refine (rtreeGraph_connected t).dist_eq_zero_iff.mp ?_
    exact_mod_cast h

@[simp] lemma dist_vert {t : RTree} (x y : Vert t) :
    dist x y = ((rtreeGraph t).dist x y : ℝ) := rfl

/-- The address at a given index, defaulting to the root. -/
lemma getD_mem_addrList (t : RTree) (k : ℕ) : (addrList t).getD k [] ∈ addrList t := by
  rcases lt_or_ge k (addrList t).length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · rw [List.getD_eq_default _ _ h]
    simp

/-- **`thm:dilution`**, the space the count sees: a rose tree with a marked
vertex, as a metric space with the root and the marked vertex as its two
marks. -/
noncomputable def rtreeSpace (p : RTree × ℕ) : MarkedSpace where
  carrier := Vert p.1
  entry := rootVert p.1
  exit := ⟨(addrList p.1).getD p.2 [], getD_mem_addrList p.1 p.2⟩

end RTree

/-! ### The part roots paired with the addresses of the contraction -/

open Tri RTree

/-- Dropping the last letter of a word with at least two letters. -/
lemma dropLast_cons_of_ne_nil {α : Type*} (a : α) {w : List α} (h : w ≠ []) :
    (a :: w).dropLast = a :: w.dropLast := by
  cases w with
  | nil => exact absurd rfl h
  | cons b w => rfl

/-- **`thm:dilution`**, the pairing: the part roots of `T`, as `Tri.partList`
lists them, against the addresses of `Tri.contractTree s T`, as
`RTree.addrList` lists them.  Both recursions read the tree in the same order,
so the pairing is the graph of a bijection. -/
def pairList (s : ℕ) (T : Tri) : List (Word × List ℕ) :=
  (partList s T).zip (addrList (contractTree s T))

/-- The same pairing for the parts topped by the maximal cut vertices of a
subtree. -/
def cutPairs (s : ℕ) (t : Tri) : List (Word × List ℕ) :=
  (cutAddrs s t).zip (addrListF (cutForest s t))

/-- The same pairing for the parts strictly below the root of a subtree. -/
def rootPairs (s : ℕ) (t : Tri) : List (Word × List ℕ) :=
  (rootAddrs s t).zip (addrListF (rootForest s t))

variable {s : ℕ}

/-- The root part heads the pairing. -/
lemma pairList_eq (t : Tri) : pairList s t = ([], []) :: rootPairs s t := by
  rw [pairList, partList_eq, contractTree_eq, addrList_node, List.zip_cons_cons, rootPairs]

/-- A cut root is paired with the first child of the enclosing part. -/
lemma cutPairs_of_isCut {t : Tri} (h : IsCut s t) :
    cutPairs s t = (pairList s t).map (Prod.map id (fun y => 0 :: y)) := by
  simp only [cutPairs, pairList]
  rw [cutForest_eq, ite_eq_left h, cutAddrs_eq, ite_eq_left h, addrListF_cons,
    addrListF_nil, List.map_nil, List.append_nil, partList_eq, List.zip_map_right]

/-- An uncut root passes up the parts below it unchanged. -/
lemma cutPairs_of_not_isCut {t : Tri} (h : ¬ IsCut s t) : cutPairs s t = rootPairs s t := by
  simp only [cutPairs, rootPairs]
  rw [cutForest_eq, ite_eq_right h, cutAddrs_eq, ite_eq_right h]

@[simp] lemma rootPairs_leaf : rootPairs s Tri.leaf = [] := by
  rw [rootPairs, rootAddrs_leaf, List.zip_nil_left]

lemma rootPairs_one (u : Tri) :
    rootPairs s (Tri.one u) = (cutPairs s u).map (Prod.map (fun w => false :: w) id) := by
  simp only [rootPairs, cutPairs]
  rw [rootAddrs_one, rootForest_one, List.zip_map_left]

lemma rootPairs_two (l r : Tri) :
    rootPairs s (Tri.two l r) =
      (cutPairs s l).map (Prod.map (fun w => false :: w) id) ++
        (cutPairs s r).map (Prod.map (fun w => true :: w) (bump (cutForest s l).length)) := by
  have hlen : ((cutAddrs s l).map (fun w => false :: w)).length
      = (addrListF (cutForest s l)).length := by
    rw [List.length_map, length_addrListF, length_cutAddrs]
  simp only [rootPairs, cutPairs]
  rw [rootAddrs_two, rootForest_two, addrListF_append, List.zip_append hlen,
    List.zip_map_left, List.zip_map]

/-! ### The pairing is compatible with the part structure -/

/-- The second entry of a pair below the root is a nonempty address. -/
lemma snd_ne_nil_of_mem_rootPairs {t : Tri} {x : Word} {y : List ℕ}
    (h : (x, y) ∈ rootPairs s t) : y ≠ [] :=
  ne_nil_of_mem_addrListF (List.of_mem_zip h).2

/-- The first entry of a pair below the root is a nonempty address. -/
lemma fst_ne_nil_of_mem_rootPairs {t : Tri} {x : Word} {y : List ℕ}
    (h : (x, y) ∈ rootPairs s t) : x ≠ [] :=
  ne_nil_of_mem_rootAddrs (List.of_mem_zip h).1

/-- Only a cut subtree pairs its own root. -/
lemma isCut_of_nil_mem_cutPairs {t : Tri} {y : List ℕ} (h : (([] : Word), y) ∈ cutPairs s t) :
    IsCut s t :=
  isCut_of_nil_mem_cutAddrs (List.of_mem_zip h).1

/-- The root of a cut subtree is the first child of the enclosing part. -/
lemma eq_of_nil_mem_cutPairs {t : Tri} {y : List ℕ} (h : (([] : Word), y) ∈ cutPairs s t) :
    y = [0] := by
  rw [cutPairs_of_isCut (isCut_of_nil_mem_cutPairs h)] at h
  obtain ⟨⟨x', y'⟩, hmem, heq⟩ := List.mem_map.mp h
  simp only [Prod.map, Prod.mk.injEq, id_eq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  rw [pairList_eq, List.mem_cons] at hmem
  rcases hmem with heq | hmem
  · rw [(Prod.mk.injEq _ _ _ _).mp heq |>.2]
  · exact absurd rfl (fst_ne_nil_of_mem_rootPairs hmem)

/-- The pairing of a subtree is compatible with the part structure once the
pairing of its parts is: the part-parent of a pair is a pair, or else the part
above is the enclosing one. -/
lemma part_dropLast_mem_cutPairs (s : ℕ) (t : Tri)
    (h : ∀ x y, (x, y) ∈ pairList s t → (part s t x.dropLast, y.dropLast) ∈ pairList s t) :
    ∀ x y, (x, y) ∈ cutPairs s t → x ≠ [] →
      (part s t x.dropLast, y.dropLast) ∈ cutPairs s t ∨
        (¬ IsCut s t ∧ part s t x.dropLast = [] ∧ y.dropLast = []) := by
  intro x y hxy hx
  by_cases hc : IsCut s t
  · rw [cutPairs_of_isCut hc] at hxy ⊢
    obtain ⟨⟨x', y'⟩, hmem, heq⟩ := List.mem_map.mp hxy
    simp only [Prod.map, Prod.mk.injEq, id_eq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hy' : y' ≠ [] := by
      rw [pairList_eq, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · exact absurd ((Prod.mk.injEq _ _ _ _).mp heq).1 hx
      · exact snd_ne_nil_of_mem_rootPairs hmem
    refine Or.inl ?_
    rw [dropLast_cons_of_ne_nil 0 hy']
    exact List.mem_map.mpr ⟨(part s t x'.dropLast, y'.dropLast), h _ _ hmem, rfl⟩
  · rw [cutPairs_of_not_isCut hc] at hxy ⊢
    have := h x y (by rw [pairList_eq]; exact List.mem_cons_of_mem _ hxy)
    rw [pairList_eq, List.mem_cons] at this
    rcases this with heq | hmem
    · exact Or.inr ⟨hc, ((Prod.mk.injEq _ _ _ _).mp heq).1, ((Prod.mk.injEq _ _ _ _).mp heq).2⟩
    · exact Or.inl hmem

/-- **The step of the recursion.**  A part of a subtree, read one letter down,
has its part-parent paired with the parent of its address. -/
lemma part_dropLast_step (s : ℕ) (t u : Tri) (a : Bool) (g : List ℕ → List ℕ)
    (hg : ∀ w, (g w).dropLast = g w.dropLast) (hgnil : g [] = [])
    (hpart : ∀ w : Word, part s t (a :: w) =
      if part s u w = [] then (if IsCut s u then [a] else []) else a :: part s u w)
    (hcut : ∀ x y, (x, y) ∈ cutPairs s u → x ≠ [] →
      (part s u x.dropLast, y.dropLast) ∈ cutPairs s u ∨
        (¬ IsCut s u ∧ part s u x.dropLast = [] ∧ y.dropLast = []))
    {z : Word} {y₀ : List ℕ} (hz : (z, y₀) ∈ cutPairs s u) :
    (part s t (a :: z).dropLast, (g y₀).dropLast) ∈
      (([], []) :: (cutPairs s u).map (Prod.map (fun w => a :: w) g)) := by
  rcases eq_or_ne z ([] : Word) with rfl | hzne
  · rw [eq_of_nil_mem_cutPairs hz]
    have h1 : (a :: ([] : Word)).dropLast = [] := rfl
    have h2 : (g [0]).dropLast = [] := by
      rw [hg, show ([0] : List ℕ).dropLast = [] from rfl, hgnil]
    rw [h1, h2, part_nil]
    exact List.mem_cons_self
  · rw [dropLast_cons_of_ne_nil a hzne, hpart, hg]
    rcases hcut z y₀ hz hzne with hmem | ⟨hnc, hq, hy⟩
    · have hqa : (if part s u z.dropLast = [] then (if IsCut s u then [a] else [])
          else a :: part s u z.dropLast) = a :: part s u z.dropLast := by
        by_cases hq : part s u z.dropLast = []
        · rw [ite_eq_left hq, hq]
          rw [hq] at hmem
          rw [ite_eq_left (isCut_of_nil_mem_cutPairs hmem)]
        · rw [ite_eq_right hq]
      rw [hqa]
      exact List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨(part s u z.dropLast, y₀.dropLast), hmem, rfl⟩)
    · rw [hq, ite_eq_left rfl, ite_eq_right hnc, hy, hgnil]
      exact List.mem_cons_self

/-- **`thm:dilution`, the pairing is a map of part trees.**  The part-parent of
a part root is paired with the parent of its address in the contraction. -/
theorem part_dropLast_mem_pairList (s : ℕ) : ∀ (t : Tri) (x : Word) (y : List ℕ),
    (x, y) ∈ pairList s t → (part s t x.dropLast, y.dropLast) ∈ pairList s t := by
  intro t
  induction t with
  | leaf =>
      intro x y hxy
      rw [pairList_eq, rootPairs_leaf, List.mem_singleton] at hxy
      obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp hxy
      rw [pairList_eq]
      simp [part_nil]
  | one u ih =>
      intro x y hxy
      rw [pairList_eq, rootPairs_one, List.mem_cons] at hxy
      rcases hxy with heq | hmem
      · obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp heq
        rw [pairList_eq]
        simp [part_nil]
      · obtain ⟨⟨z, y₀⟩, hz, heq⟩ := List.mem_map.mp hmem
        simp only [Prod.map, Prod.mk.injEq, id_eq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have := part_dropLast_step s (Tri.one u) u false id (fun _ => rfl) rfl
          (fun w => part_one_false u w) (part_dropLast_mem_cutPairs s u ih) hz
        rwa [pairList_eq, rootPairs_one]
  | two l r ihl ihr =>
      intro x y hxy
      rw [pairList_eq, rootPairs_two, List.mem_cons, List.mem_append] at hxy
      rcases hxy with heq | hmem | hmem
      · obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp heq
        rw [pairList_eq]
        simp [part_nil]
      · obtain ⟨⟨z, y₀⟩, hz, heq⟩ := List.mem_map.mp hmem
        simp only [Prod.map, Prod.mk.injEq, id_eq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hstep := part_dropLast_step s (Tri.two l r) l false id (fun _ => rfl) rfl
          (fun w => part_two_false l r w) (part_dropLast_mem_cutPairs s l ihl) hz
        simp only [id_eq] at hstep
        rw [pairList_eq, rootPairs_two]
        rcases List.mem_cons.mp hstep with heq' | hmem'
        · rw [heq']; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hmem')
      · obtain ⟨⟨z, y₀⟩, hz, heq⟩ := List.mem_map.mp hmem
        simp only [Prod.map, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hstep := part_dropLast_step s (Tri.two l r) r true
          (bump (cutForest s l).length) (fun w => dropLast_bump _ w) rfl
          (fun w => part_two_true l r w) (part_dropLast_mem_cutPairs s r ihr) hz
        rw [pairList_eq, rootPairs_two]
        rcases List.mem_cons.mp hstep with heq' | hmem'
        · rw [heq']; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ hmem')

/-! ### The pairing is a bijection -/

/-- A zip of two lists of equal length, the first without repetitions, is the
graph of the map reading the second list at the index of the first. -/
lemma mem_zip_iff_getD {α β : Type*} [BEq α] [LawfulBEq α] (d : β) :
    ∀ {l : List α} {m : List β}, l.Nodup → l.length = m.length → ∀ {x : α} {y : β},
      ((x, y) ∈ l.zip m ↔ x ∈ l ∧ y = m.getD (l.idxOf x) d) := by
  intro l
  induction l with
  | nil => intro m _ _ x y; simp
  | cons a l ih =>
      intro m hnd hlen x y
      cases m with
      | nil => simp at hlen
      | cons b m =>
          rw [List.zip_cons_cons, List.mem_cons]
          obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
          have hlen' : l.length = m.length := by simpa using hlen
          by_cases hxa : x = a
          · subst hxa
            rw [List.idxOf_cons_self, List.getD_cons_zero]
            constructor
            · rintro (heq | hmem)
              · exact ⟨List.mem_cons_self, ((Prod.mk.injEq _ _ _ _).mp heq).2⟩
              · exact absurd (List.of_mem_zip hmem).1 hna
            · rintro ⟨-, rfl⟩
              exact Or.inl rfl
          · have hidx : (a :: l).idxOf x = l.idxOf x + 1 := by
              have hax : (a == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxa)
              rw [List.idxOf_cons, hax, ite_eq_right Bool.false_ne_true]
            rw [hidx, List.getD_cons_succ, ih hnd' hlen']
            constructor
            · rintro (heq | hmem)
              · exact absurd ((Prod.mk.injEq _ _ _ _).mp heq).1 hxa
              · exact ⟨List.mem_cons_of_mem _ hmem.1, hmem.2⟩
            · rintro ⟨hx, hy⟩
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact absurd rfl hxa
              · exact Or.inr ⟨hx', hy⟩

/-- A zip read from the other side. -/
lemma mem_zip_swap {α β : Type*} {l : List α} {m : List β} {x : α} {y : β} :
    (x, y) ∈ l.zip m ↔ (y, x) ∈ m.zip l := by
  constructor
  · intro h
    have h2 : Prod.swap (x, y) ∈ (l.zip m).map Prod.swap := List.mem_map_of_mem h
    rwa [List.zip_swap] at h2
  · intro h
    have h2 : Prod.swap (y, x) ∈ (m.zip l).map Prod.swap := List.mem_map_of_mem h
    rwa [List.zip_swap] at h2

variable (s : ℕ) (T : Tri)

/-- **`thm:dilution`**: the address, in the contraction, of the part topped by a
given address. -/
def partAddr (x : Word) : List ℕ :=
  (addrList (contractTree s T)).getD ((partList s T).idxOf x) []

/-- The part root an address of the contraction names. -/
def addrPart (y : List ℕ) : Word :=
  (partList s T).getD ((addrList (contractTree s T)).idxOf y) []

/-- The part roots and the addresses of the contraction are equally many. -/
lemma length_partList_eq : (partList s T).length = (addrList (contractTree s T)).length := by
  rw [length_partList, length_addrList]

/-- The pairing read from the part roots. -/
lemma mem_pairList_iff {x : Word} {y : List ℕ} :
    (x, y) ∈ pairList s T ↔ x ∈ partList s T ∧ y = partAddr s T x := by
  rw [pairList]
  exact mem_zip_iff_getD [] (nodup_partList T) (length_partList_eq s T)

/-- The pairing read from the addresses. -/
lemma mem_pairList_iff' {x : Word} {y : List ℕ} :
    (x, y) ∈ pairList s T ↔ y ∈ addrList (contractTree s T) ∧ x = addrPart s T y := by
  rw [pairList, mem_zip_swap]
  exact mem_zip_iff_getD [] (nodup_addrList _) (length_partList_eq s T).symm

variable {s T} {x x' : Word}

/-- A part root is paired with its address. -/
lemma mem_pairList (hx : x ∈ partList s T) : (x, partAddr s T x) ∈ pairList s T :=
  (mem_pairList_iff s T).mpr ⟨hx, rfl⟩

/-- The address of a part root is an address of the contraction. -/
lemma partAddr_mem (hx : x ∈ partList s T) : partAddr s T x ∈ addrList (contractTree s T) :=
  ((mem_pairList_iff' s T).mp (mem_pairList hx)).1

/-- An address of the contraction names a part root. -/
lemma addrPart_mem {y : List ℕ} (hy : y ∈ addrList (contractTree s T)) :
    addrPart s T y ∈ partList s T :=
  ((mem_pairList_iff s T).mp ((mem_pairList_iff' s T).mpr ⟨hy, rfl⟩)).1

/-- The two readings are inverse to each other. -/
lemma addrPart_partAddr (hx : x ∈ partList s T) : addrPart s T (partAddr s T x) = x :=
  (((mem_pairList_iff' s T).mp (mem_pairList hx)).2).symm

lemma partAddr_addrPart {y : List ℕ} (hy : y ∈ addrList (contractTree s T)) :
    partAddr s T (addrPart s T y) = y :=
  (((mem_pairList_iff s T).mp ((mem_pairList_iff' s T).mpr ⟨hy, rfl⟩)).2).symm

/-- The part roots are named once each. -/
lemma partAddr_injOn (hx : x ∈ partList s T) (hx' : x' ∈ partList s T)
    (h : partAddr s T x = partAddr s T x') : x = x' := by
  rw [← addrPart_partAddr hx, ← addrPart_partAddr hx', h]

/-- The root part is named by the root. -/
@[simp] lemma partAddr_nil : partAddr s T [] = [] := by
  have : (([] : Word), ([] : List ℕ)) ∈ pairList s T := by
    rw [pairList_eq]; exact List.mem_cons_self
  exact (((mem_pairList_iff s T).mp this).2).symm

/-- **`thm:dilution`, the naming is a map of part trees.**  The part-parent of a
part root is named by the parent of its name. -/
lemma partAddr_part_dropLast (hx : x ∈ partList s T) :
    partAddr s T (part s T x.dropLast) = (partAddr s T x).dropLast :=
  (((mem_pairList_iff s T).mp
    (part_dropLast_mem_pairList s T x (partAddr s T x) (mem_pairList hx))).2).symm

/-- The part-parent of a part root is a part root. -/
lemma part_dropLast_mem_partList (hx : x ∈ partList s T) :
    part s T x.dropLast ∈ partList s T :=
  ((mem_pairList_iff s T).mp
    (part_dropLast_mem_pairList s T x (partAddr s T x) (mem_pairList hx))).1

/-! ### The contracted tree and the rose tree are isometric -/

/-- One vertex of the contracted tree lies below another exactly when the
second is distinct from the first and has it as its part-parent. -/
lemma partStep_iff {p q : PartVert s T} :
    PartStep p q ↔ p ≠ q ∧ p.1 = part s T q.1.dropLast := by
  constructor
  · rintro ⟨u, a, h1, h2⟩
    have hdl : q.1.dropLast = u := by rw [h1]; simp
    refine ⟨?_, by rw [hdl, h2]⟩
    intro hpq
    have hlen : (part s T u).length ≤ u.length := length_part_le (s := s) T u
    rw [← h2, hpq, h1] at hlen
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  · rintro ⟨hne, hp⟩
    have hq : q.1 ≠ [] := by
      intro h
      refine hne (Subtype.ext ?_)
      rw [hp, h, List.dropLast_nil, part_nil]
    obtain ⟨u, a, hua⟩ : ∃ (u : Word) (a : Bool), q.1 = u ++ [a] := by
      rcases List.eq_nil_or_concat q.1 with h | ⟨u, a, h⟩
      · exact absurd h hq
      · exact ⟨u, a, by rw [h]; simp⟩
    refine ⟨u, a, hua, ?_⟩
    rw [hp, hua]
    simp

/-- The contracted tree is the graph of the part-parent map. -/
lemma partGraph_adj_iff {p q : PartVert s T} :
    (partGraph s T).Adj p q ↔
      p ≠ q ∧ (p.1 = part s T q.1.dropLast ∨ q.1 = part s T p.1.dropLast) := by
  rw [partGraph_adj, partStep_iff, partStep_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1.symm, Or.inr h2⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1.symm, h2⟩

/-- **`thm:dilution`**: a part root read as an address of the contraction. -/
def toVert (p : PartVert s T) : Vert (contractTree s T) :=
  ⟨partAddr s T p.1, partAddr_mem ((mem_partList_iff T).mpr p.2)⟩

/-- An address of the contraction read as a part root. -/
def ofVert (y : Vert (contractTree s T)) : PartVert s T :=
  ⟨addrPart s T y.1, (mem_partList_iff T).mp (addrPart_mem y.2)⟩

@[simp] lemma toVert_val (p : PartVert s T) : (toVert p).1 = partAddr s T p.1 := rfl

@[simp] lemma ofVert_val (y : Vert (contractTree s T)) : (ofVert y).1 = addrPart s T y.1 := rfl

lemma ofVert_toVert (p : PartVert s T) : ofVert (toVert p) = p :=
  Subtype.ext (addrPart_partAddr ((mem_partList_iff T).mpr p.2))

lemma toVert_ofVert (y : Vert (contractTree s T)) : toVert (ofVert y) = y :=
  Subtype.ext (partAddr_addrPart y.2)

lemma toVert_injective : Function.Injective (toVert (s := s) (T := T)) := by
  intro p q h
  rw [← ofVert_toVert p, ← ofVert_toVert q, h]

/-- **The reading is an isomorphism of trees**: the part-parent relation is the
parent relation on addresses. -/
lemma toVert_adj_iff {p q : PartVert s T} :
    (rtreeGraph (contractTree s T)).Adj (toVert p) (toVert q) ↔ (partGraph s T).Adj p q := by
  have hp : p.1 ∈ partList s T := (mem_partList_iff T).mpr p.2
  have hq : q.1 ∈ partList s T := (mem_partList_iff T).mpr q.2
  have key : ∀ {x y : PartVert s T}, x.1 ∈ partList s T → y.1 ∈ partList s T →
      ((toVert x).1 = (toVert y).1.dropLast ↔ x.1 = part s T y.1.dropLast) := by
    intro x y hx hy
    rw [toVert_val, toVert_val, ← partAddr_part_dropLast hy]
    exact ⟨fun h => partAddr_injOn hx (part_dropLast_mem_partList hy) h, fun h => by rw [h]⟩
  rw [rtreeGraph_adj, partGraph_adj_iff, key hp hq, key hq hp]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h1 (by rw [hc]), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h1 (toVert_injective hc), h2⟩

/-- The reading as a graph homomorphism. -/
def toVertHom (s : ℕ) (T : Tri) : partGraph s T →g rtreeGraph (contractTree s T) :=
  ⟨toVert, fun {_ _} h => toVert_adj_iff.mpr h⟩

/-- The inverse reading as a graph homomorphism. -/
def ofVertHom (s : ℕ) (T : Tri) : rtreeGraph (contractTree s T) →g partGraph s T :=
  ⟨ofVert, fun {x y} h => by
    have hxy := toVert_adj_iff (p := ofVert x) (q := ofVert y)
    rw [toVert_ofVert, toVert_ofVert] at hxy
    exact hxy.mp h⟩

/-- A graph homomorphism does not increase distances. -/
lemma dist_le_of_hom {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') (hconn : G.Connected) (u v : V) : G'.dist (f u) (f v) ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := (hconn u v).exists_walk_length_eq_dist
  have h := SimpleGraph.dist_le (p.map f)
  rwa [SimpleGraph.Walk.length_map, hp] at h

/-- **`thm:dilution`, the contraction is the rose tree**: the contracted tree
of `Contraction.lean` and the rose tree of `ContractTree.lean` carry the same
metric. -/
theorem dist_toVert (p q : PartVert s T) :
    (rtreeGraph (contractTree s T)).dist (toVert p) (toVert q) = (partGraph s T).dist p q := by
  refine le_antisymm (dist_le_of_hom (toVertHom s T) partGraph_connected p q) ?_
  have h := dist_le_of_hom (ofVertHom s T) (rtreeGraph_connected _) (toVert p) (toVert q)
  have e1 : (ofVertHom s T) (toVert p) = p := ofVert_toVert p
  have e2 : (ofVertHom s T) (toVert q) = q := ofVert_toVert q
  rwa [e1, e2] at h

/-! ### Marked isometries -/

/-- A marked isometry: a surjective distance-preserving map carrying entry to
entry and exit to exit. -/
structure IsMarkedIsom (X Y : MarkedSpace) (f : X.carrier → Y.carrier) : Prop where
  dist_eq : ∀ a b, dist (f a) (f b) = dist a b
  surj : Function.Surjective f
  entry : f X.entry = Y.entry
  exit : f X.exit = Y.exit

/-- **A marked quasi-isometry followed by a marked isometry keeps its
constant**: the identification of `thm:dilution` leaves the constant unchanged. -/
lemma MarkedQI.trans_isom {K : ℝ} {X Y Z : MarkedSpace} {g : Y.carrier → Z.carrier}
    (h : MarkedQI K X Y) (hg : IsMarkedIsom Y Z g) : MarkedQI K X Z := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun x => g (f x), fun a b => ?_, fun a b => ?_, fun z => ?_, ?_, ?_⟩
  · rw [hg.dist_eq]; exact hf.upper a b
  · rw [hg.dist_eq]; exact hf.lower a b
  · obtain ⟨y, rfl⟩ := hg.surj z
    obtain ⟨a, ha⟩ := hf.dense y
    exact ⟨a, by rw [hg.dist_eq]; exact ha⟩
  · rw [← hg.entry, hg.dist_eq]; exact hf.entry
  · rw [← hg.exit, hg.dist_eq]; exact hf.exit

/-- **`thm:dilution`, the contraction as the counted datum**: the contracted
tree of a realisation, with the part of a marked vertex, is the rose tree the
count of `dilution_count` sees, marks and metric included. -/
theorem isMarkedIsom_toVert (s : ℕ) {T : Tri} {e : Word} (he : T.IsAddr e) :
    IsMarkedIsom (partSpace s he) (rtreeSpace (contractPair s T e)) toVert where
  dist_eq a b := by
    show ((rtreeGraph (contractTree s T)).dist (toVert a) (toVert b) : ℝ)
      = ((partGraph s T).dist a b : ℝ)
    rw [dist_toVert]
  surj y := ⟨ofVert y, toVert_ofVert y⟩
  entry := Subtype.ext (by simp only [toVert_val]; exact partAddr_nil)
  exit := Subtype.ext rfl

/-! ### Shapes with the same contraction are comparable -/

/-- **`thm:dilution`, the step that makes the count bite.**  Two shapes whose
contractions at scale `s` agree, the mark included, are `72s³`-comparable: the
projection of the first, the identification of the two contractions, and a
quasi-inverse of the projection of the second compose to
`3·2s·3(2s)²`. -/
theorem markedQI_of_shapeContractPair_eq {s : ℕ} (hs : 1 ≤ s) {σ τ : Shape}
    (h : shapeContractPair s σ = shapeContractPair s τ) :
    MarkedQI (72 * (s : ℝ) ^ 3) (shapeSpace σ) (shapeSpace τ) := by
  have hsr : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
  have h1 : MarkedQI (2 * (s : ℝ)) (shapeSpace σ) (rtreeSpace (shapeContractPair s σ)) :=
    (markedQI_contract_shape hs σ).trans_isom
      (isMarkedIsom_toVert s (Shape.isAddr_neckAddr σ.decs))
  have h2 : MarkedQI (2 * (s : ℝ)) (shapeSpace τ) (rtreeSpace (shapeContractPair s τ)) :=
    (markedQI_contract_shape hs τ).trans_isom
      (isMarkedIsom_toVert s (Shape.isAddr_neckAddr τ.decs))
  rw [← h] at h2
  have h3 : MarkedQI (3 * (2 * (s : ℝ)) ^ 2)
      (rtreeSpace (shapeContractPair s σ)) (shapeSpace τ) := markedQI_symm hs1 h2
  have h4 : (1 : ℝ) ≤ 3 * (2 * (s : ℝ)) ^ 2 := by nlinarith
  have h5 := markedQI_comp hs1 h4 h1 h3
  have e : 3 * (2 * (s : ℝ)) * (3 * (2 * (s : ℝ)) ^ 2) = 72 * (s : ℝ) ^ 3 := by ring
  rwa [e] at h5

/-! ### The contraction at scale one -/

/-- At scale one every vertex is cut, so every part is a single vertex. -/
lemma isCut_one (t : Tri) : IsCut 1 t := one_le_rawSize t

@[simp] lemma contractTree_one_leaf : contractTree 1 Tri.leaf = RTree.node [] := rfl

lemma contractTree_one_one (t : Tri) :
    contractTree 1 (Tri.one t) = RTree.node [contractTree 1 t] := by
  rw [contractTree_eq, rootForest_one, cutForest_eq, ite_eq_left (isCut_one t)]

lemma contractTree_one_two (l r : Tri) :
    contractTree 1 (Tri.two l r) = RTree.node [contractTree 1 l, contractTree 1 r] := by
  rw [contractTree_eq, rootForest_two, cutForest_eq, cutForest_eq,
    ite_eq_left (isCut_one l), ite_eq_left (isCut_one r)]
  rfl

/-- At scale one the contraction is the realisation itself, read as a rose
tree, so it determines it. -/
lemma contractTree_one_injective : Function.Injective (contractTree 1) := by
  intro t
  induction t with
  | leaf =>
      intro t' h
      cases t' with
      | leaf => rfl
      | one u => rw [contractTree_one_leaf, contractTree_one_one] at h; simp at h
      | two l r => rw [contractTree_one_leaf, contractTree_one_two] at h; simp at h
  | one u ih =>
      intro t' h
      cases t' with
      | leaf => rw [contractTree_one_one, contractTree_one_leaf] at h; simp at h
      | one u' =>
          rw [contractTree_one_one, contractTree_one_one] at h
          simp only [RTree.node.injEq, List.cons.injEq, and_true] at h
          rw [ih h]
      | two l r => rw [contractTree_one_one, contractTree_one_two] at h; simp at h
  | two l r ihl ihr =>
      intro t' h
      cases t' with
      | leaf => rw [contractTree_one_two, contractTree_one_leaf] at h; simp at h
      | one u => rw [contractTree_one_two, contractTree_one_one] at h; simp at h
      | two l' r' =>
          rw [contractTree_one_two, contractTree_one_two] at h
          simp only [RTree.node.injEq, List.cons.injEq, and_true] at h
          rw [ihl h.1, ihr h.2]

/-- At scale one the marked contraction determines the shape. -/
lemma shapeContractPair_one_injective : Function.Injective (shapeContractPair 1) := fun _ _ h =>
  Shape.realise_injective (contractTree_one_injective (congrArg Prod.fst h))

/-! ### Entropy dilution -/

/-- The count of `dilution_count_shape` over a family of shapes whose
contractions at scale `s` are pairwise distinct. -/
lemma card_le_of_contractPair_injOn {s n : ℕ} (hs : 1 ≤ s) (F : Finset Shape)
    (hsize : ∀ σ ∈ F, σ.size ≤ n)
    (hinj : ∀ σ ∈ F, ∀ τ ∈ F,
      shapeContractPair s σ = shapeContractPair s τ → σ = τ) :
    (F.card : ℝ) ≤ Real.exp (3 * ((n / s + 1 : ℕ) : ℝ)) := by
  classical
  have himg : (F.image (shapeContractPair s)).card = F.card :=
    Finset.card_image_of_injOn fun σ hσ τ hτ h => hinj σ hσ τ hτ h
  rw [← himg]
  refine dilution_count_shape hs n _ ?_
  intro p hp
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨σ, hsize σ hσ, rfl⟩

/-- **`thm:dilution`**, the scale: the largest `s` with `72s³ ≤ D`, which is
`⌊(D/72)^{1/3}⌋`. -/
def dilScale (D : ℕ) : ℕ := Nat.findGreatest (fun k => 72 * k ^ 3 ≤ D) D

lemma dilScale_def (D : ℕ) : dilScale D = Nat.findGreatest (fun k => 72 * k ^ 3 ≤ D) D := rfl

/-- Two is a candidate scale once `D` is large. -/
lemma cube_two_le {D : ℕ} (hD : 730 ≤ D) : 72 * 2 ^ 3 ≤ D := by
  have h : (72 : ℕ) * 2 ^ 3 = 576 := by norm_num
  omega

lemma dilScale_cube_le {D : ℕ} (hD : 730 ≤ D) : 72 * dilScale D ^ 3 ≤ D := by
  rw [dilScale_def]
  exact Nat.findGreatest_spec (P := fun k => 72 * k ^ 3 ≤ D) (m := 2) (by omega) (cube_two_le hD)

lemma two_le_dilScale {D : ℕ} (hD : 730 ≤ D) : 2 ≤ dilScale D := by
  rw [dilScale_def]
  exact Nat.le_findGreatest (by omega) (cube_two_le hD)

lemma dilScale_lt {D : ℕ} (hD : 730 ≤ D) : D < 72 * (dilScale D + 1) ^ 3 := by
  have hle := dilScale_cube_le hD
  have h2 := two_le_dilScale hD
  have hs : dilScale D ≤ dilScale D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hlt : dilScale D < D := by omega
  have hgr : ¬ (72 * (dilScale D + 1) ^ 3 ≤ D) := by
    refine Nat.findGreatest_is_greatest (P := fun k => 72 * k ^ 3 ≤ D) (n := D)
      (k := dilScale D + 1) ?_ (by omega)
    rw [← dilScale_def]
    omega
  omega

/-- **`thm:dilution`, entropy dilution**, in the form the net uses: a family of
shapes of size at most `n`, no two of which admit `D`-marked quasi-isometries
in both directions, has at most `exp (27 (n D^{-1/3} + 1))` members. -/
theorem dilution_of_not_both {D : ℕ} (hD : 2 ≤ D) (n : ℕ) (F : Finset Shape)
    (hsize : ∀ σ ∈ F, σ.size ≤ n)
    (hsep : ∀ σ ∈ F, ∀ τ ∈ F, σ ≠ τ →
      ¬ (MarkedQI (D : ℝ) (shapeSpace σ) (shapeSpace τ) ∧
        MarkedQI (D : ℝ) (shapeSpace τ) (shapeSpace σ))) :
    (F.card : ℝ) ≤ Real.exp (27 * ((n : ℝ) * (D : ℝ) ^ (-(1 : ℝ) / 3) + 1)) := by
  have hD0 : 0 < D := by omega
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hbig : 730 ≤ D
  · -- the scale `s = ⌊(D/72)^{1/3}⌋ ≥ 2`
    set s := dilScale D with hsdef
    have hs2 : 2 ≤ s := two_le_dilScale hbig
    have hs1 : 1 ≤ s := by omega
    have hcube : 72 * s ^ 3 ≤ D := dilScale_cube_le hbig
    have hD729 : D ≤ 729 * s ^ 3 := cube_bound hs2 (dilScale_lt hbig)
    have hinj : ∀ σ ∈ F, ∀ τ ∈ F,
        shapeContractPair s σ = shapeContractPair s τ → σ = τ := by
      intro σ hσ τ hτ h
      by_contra hne
      refine hsep σ hσ τ hτ hne ⟨?_, ?_⟩ <;>
        refine MarkedQI.mono (by positivity) ?_
          (markedQI_of_shapeContractPair_eq hs1 (by first | exact h | exact h.symm)) <;>
        · have hcast : ((72 * s ^ 3 : ℕ) : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast hcube
          push_cast at hcast
          linarith
    have hcount := card_le_of_contractPair_injOn hs1 F hsize hinj
    refine hcount.trans (Real.exp_le_exp.mpr ?_)
    -- `3 (n/s + 1) ≤ 27 (n D^{-1/3} + 1)`
    have hinv : (1 : ℝ) / s ≤ 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) :=
      inv_le_nine_rpow hs1 hD0 hD729
    have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
    have hdiv : ((n / s : ℕ) : ℝ) ≤ (n : ℝ) / (s : ℝ) := Nat.cast_div_le
    have hstep : (n : ℝ) / (s : ℝ) ≤ (n : ℝ) * (9 * (D : ℝ) ^ (-(1 : ℝ) / 3)) := by
      rw [div_eq_mul_inv, ← one_div]
      exact mul_le_mul_of_nonneg_left hinv hn0
    have hcast : ((n / s + 1 : ℕ) : ℝ) = ((n / s : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    nlinarith [Real.rpow_nonneg (le_of_lt (by exact_mod_cast hD0 : (0:ℝ) < (D:ℝ)))
      (-(1 : ℝ) / 3)]
  · -- the crude regime: the contraction at scale one determines the shape
    have hsmall : D ≤ 729 := by omega
    have hinj : ∀ σ ∈ F, ∀ τ ∈ F,
        shapeContractPair 1 σ = shapeContractPair 1 τ → σ = τ :=
      fun _ _ _ _ h => shapeContractPair_one_injective h
    have hcount := card_le_of_contractPair_injOn le_rfl F hsize hinj
    refine hcount.trans (Real.exp_le_exp.mpr ?_)
    have hone : (1 : ℝ) ≤ 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) := one_le_nine_rpow hD0 hsmall
    have hcast : ((n / 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      rw [Nat.div_one]; push_cast; ring
    rw [hcast]
    nlinarith

/-- **`thm:dilution`, entropy dilution.**  A family of shapes of size at most
`n`, no two of which admit a `D`-marked quasi-isometry, has at most
`exp (27 (n D^{-1/3} + 1))` members: the greedy cut at scale
`s = ⌊(D/72)^{1/3}⌋` sends the family injectively into the marked contractions
of at most `n/s + 1` vertices, which `dilution_count` counts. -/
theorem dilution {D : ℕ} (hD : 2 ≤ D) (n : ℕ) (F : Finset Shape)
    (hsize : ∀ σ ∈ F, σ.size ≤ n)
    (hsep : ∀ σ ∈ F, ∀ τ ∈ F, σ ≠ τ →
      ¬ MarkedQI (D : ℝ) (shapeSpace σ) (shapeSpace τ)) :
    (F.card : ℝ) ≤ Real.exp (27 * ((n : ℝ) * (D : ℝ) ^ (-(1 : ℝ) / 3) + 1)) :=
  dilution_of_not_both hD n F hsize fun σ hσ τ hτ hne h => hsep σ hσ τ hτ hne h.1

/-- **`thm:dilution`, the representatives.**  At most `exp (27 (n D^{-1/3}+1))`
members of the net `ℛ_D` carry a shape of size at most `n`. -/
theorem dilution_netMem {D : ℕ} (hD : 2 ≤ D) (n : ℕ) (F : Finset ℕ)
    (hnet : ∀ a ∈ F, netMem shapeFamily (D : ℝ) a)
    (hsize : ∀ a ∈ F, (shapeEnum a).size ≤ n) :
    (F.card : ℝ) ≤ Real.exp (27 * ((n : ℝ) * (D : ℝ) ^ (-(1 : ℝ) / 3) + 1)) := by
  classical
  have hcard : (F.image shapeEnum).card = F.card :=
    Finset.card_image_of_injective F shapeEnum_injective
  rw [← hcard]
  refine dilution_of_not_both hD n _ ?_ ?_
  · intro σ hσ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hσ
    exact hsize a ha
  · intro σ hσ τ hτ hne hboth
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hτ
    have hab : a ≠ b := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact (netMem_iff shapeFamily (D : ℝ) b).mp (hnet b hb) a hlt (hnet a ha) hboth.2
    · exact (netMem_iff shapeFamily (D : ℝ) a).mp (hnet a ha) b hlt (hnet b hb) hboth.1

end ChainClasses
