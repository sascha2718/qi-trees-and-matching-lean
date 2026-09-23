import Mathlib.Tactic
import ChainClasses.Shape.Contraction

/-!
`thm:dilution`, the contraction as a concrete tree: the parts of the greedy cut
of `Contraction.lean` assembled into a finite rooted tree of arbitrary arity,
with the part of the exit marked.

The part roots of `T` at scale `s` are the root of `T` together with the cut
vertices, and one part root is the parent of another when the second tops a
part immediately below the first.  Read off `T` by structural recursion this is
`cutForest`, the list of parts topped by the maximal cut vertices of a subtree,
and `rootForest`, the same list for the children of the root; the contraction
is the rose tree `contractTree` whose children are `rootForest`.  The same
recursion carried on addresses is `cutAddrs` and `rootAddrs`, so the vertices
of the contraction are listed by the addresses of the part roots, in the order
the tree is read.

* `Tri.cutForest`, `Tri.rootForest`, `Tri.contractTree`: the contraction as an
  `RTree`.  `sizeF_cutForest` counts the forest by `Tri.cutCount`, and
  `size_contractTree_le_div` is the count of **`thm:dilution`**: at most
  `|T|/s + 1` parts.
* `Tri.cutAddrs`, `Tri.rootAddrs`, `Tri.partList`: the part roots by address.
  `mem_partList_iff` identifies the list as the vertex set `PartVert s T` of
  `Contraction.lean`, `nodup_partList` lists each once, `length_partList`
  matches the count, and `card_partVert` reads the two together: the
  contraction has one vertex for each vertex of `partGraph s T`.
* `Tri.markOf`, `Tri.contractPair`, `shapeContractPair`: the part of a vertex
  read as an index into that list, and the marked tree it makes.
  `contractPair_spec` and `shapeContractPair_spec` are the hypothesis of
  `RTree.dilution_count`, and `dilution_count_shape` is the count it gives.
-/

namespace ChainClasses

namespace RTree

/-! ### Counting the vertices of a forest -/

/-- The empty forest has no vertices. -/
@[simp] lemma sizeF_nil : sizeF [] = 0 := by rw [sizeF]

/-- A forest is counted one tree at a time. -/
@[simp] lemma sizeF_cons (c : RTree) (cs : List RTree) :
    sizeF (c :: cs) = c.size + sizeF cs := by rw [sizeF]

/-- A tree is its root together with its children. -/
@[simp] lemma size_node (cs : List RTree) : (node cs).size = 1 + sizeF cs := by rw [size]

/-- Forests are counted blockwise. -/
@[simp] lemma sizeF_append (l₁ l₂ : List RTree) :
    sizeF (l₁ ++ l₂) = sizeF l₁ + sizeF l₂ := by
  induction l₁ with
  | nil => simp
  | cons c cs ih => simp only [List.cons_append, sizeF_cons, ih]; omega

end RTree

namespace Tri

variable {s : ℕ}

/-! ### The cut rule at each constructor -/

/-- A single vertex is cut exactly at scale one. -/
lemma isCut_leaf_iff : IsCut s leaf ↔ s ≤ 1 := Iff.rfl

/-- The cut rule at a vertex with one child. -/
lemma isCut_one_iff (t : Tri) : IsCut s (one t) ↔ s ≤ 1 + remSize s t := Iff.rfl

/-- The cut rule at a vertex with two children. -/
lemma isCut_two_iff (l r : Tri) :
    IsCut s (two l r) ↔ s ≤ 1 + remSize s l + remSize s r := Iff.rfl

/-! ### The contraction as a rose tree -/

/-- The parts of `t` topped by the maximal cut vertices of `t`, in the order
the tree is read: a cut root takes the whole of `t` as one part, and an uncut
root passes up the parts of its children. -/
def cutForest (s : ℕ) : Tri → List RTree
  | leaf => if IsCut s leaf then [RTree.node []] else []
  | one t => if IsCut s (one t) then [RTree.node (cutForest s t)] else cutForest s t
  | two l r =>
      if IsCut s (two l r) then [RTree.node (cutForest s l ++ cutForest s r)]
      else cutForest s l ++ cutForest s r

@[simp] lemma cutForest_leaf :
    cutForest s leaf = if IsCut s leaf then [RTree.node []] else [] := rfl

@[simp] lemma cutForest_one (t : Tri) :
    cutForest s (one t) =
      if IsCut s (one t) then [RTree.node (cutForest s t)] else cutForest s t := rfl

@[simp] lemma cutForest_two (l r : Tri) :
    cutForest s (two l r) =
      if IsCut s (two l r) then [RTree.node (cutForest s l ++ cutForest s r)]
      else cutForest s l ++ cutForest s r := rfl

/-- The children of the root part: the parts topped by the maximal cut vertices
below the root. -/
def rootForest (s : ℕ) : Tri → List RTree
  | leaf => []
  | one t => cutForest s t
  | two l r => cutForest s l ++ cutForest s r

@[simp] lemma rootForest_leaf : rootForest s leaf = [] := rfl

@[simp] lemma rootForest_one (t : Tri) : rootForest s (one t) = cutForest s t := rfl

@[simp] lemma rootForest_two (l r : Tri) :
    rootForest s (two l r) = cutForest s l ++ cutForest s r := rfl

/-- **`thm:dilution`**, the contracted tree: the part roots of `T` at scale `s`,
each part root carrying as children the part roots immediately below it. -/
def contractTree (s : ℕ) (T : Tri) : RTree := RTree.node (rootForest s T)

@[simp] lemma contractTree_eq (T : Tri) :
    contractTree s T = RTree.node (rootForest s T) := rfl

/-- A cut root contributes the one part it tops; an uncut root contributes the
parts below it. -/
lemma cutForest_eq (t : Tri) :
    cutForest s t = if IsCut s t then [contractTree s t] else rootForest s t := by
  cases t <;> simp

/-! ### The number of parts -/

/-- The forest of parts has exactly as many vertices as the greedy cut has
parts. -/
lemma sizeF_cutForest (t : Tri) : RTree.sizeF (cutForest s t) = cutCount s t := by
  induction t with
  | leaf =>
      rw [cutForest_leaf, cutCount]
      by_cases h : s ≤ 1
      · rw [ite_eq_left (isCut_leaf_iff.mpr h), ite_eq_left h]
        simp
      · rw [ite_eq_right (fun hc => h (isCut_leaf_iff.mp hc)), ite_eq_right h]
        simp
  | one t ih =>
      rw [cutForest_one, cutCount]
      by_cases h : s ≤ 1 + remSize s t
      · rw [ite_eq_left ((isCut_one_iff t).mpr h), ite_eq_left h]
        simp only [RTree.sizeF_cons, RTree.sizeF_nil, RTree.size_node, ih]
        omega
      · rw [ite_eq_right (fun hc => h ((isCut_one_iff t).mp hc)), ite_eq_right h, ih]
        omega
  | two l r ihl ihr =>
      rw [cutForest_two, cutCount]
      by_cases h : s ≤ 1 + remSize s l + remSize s r
      · rw [ite_eq_left ((isCut_two_iff l r).mpr h), ite_eq_left h]
        simp only [RTree.sizeF_cons, RTree.sizeF_nil, RTree.size_node, RTree.sizeF_append,
          ihl, ihr]
        omega
      · rw [ite_eq_right (fun hc => h ((isCut_two_iff l r).mp hc)), ite_eq_right h]
        simp only [RTree.sizeF_append, ihl, ihr]
        omega

/-- Below the root part sit at most as many vertices as the greedy cut has
parts, one fewer when the root itself is cut. -/
lemma sizeF_rootForest_le (t : Tri) : RTree.sizeF (rootForest s t) ≤ cutCount s t := by
  cases t with
  | leaf => simp only [rootForest_leaf, RTree.sizeF_nil]; exact Nat.zero_le _
  | one t =>
      rw [rootForest_one, sizeF_cutForest, cutCount]
      split <;> omega
  | two l r =>
      rw [rootForest_two, RTree.sizeF_append, sizeF_cutForest, sizeF_cutForest, cutCount]
      split <;> omega

/-- **`thm:dilution`, the parts**: the contraction carries one vertex more than
the greedy cut has parts, the extra one being the root part. -/
theorem size_contractTree_le (T : Tri) : (contractTree s T).size ≤ cutCount s T + 1 := by
  rw [contractTree_eq, RTree.size_node]
  have := sizeF_rootForest_le (s := s) T
  omega

/-- **`thm:dilution`, the parts**: at scale `s` the contraction of a tree of `n`
vertices has at most `n/s + 1` vertices. -/
theorem size_contractTree_le_div (hs : 1 ≤ s) (T : Tri) :
    (contractTree s T).size ≤ T.size / s + 1 := by
  have h1 := size_contractTree_le (s := s) T
  have h2 := cutCount_le_div s hs T
  omega

/-! ### The part of an address, read from the top -/

/-- **The step rule at the top.**  The part of an address one letter down is
the part of the rest of the address inside the subtree, read one letter down,
and the root of the subtree when that part is the whole of it. -/
lemma part_cons (T : Tri) (a : Bool) (w : Word) :
    part s T (a :: w) =
      if part s (subAt T [a]) w = [] then (if IsCut s (subAt T [a]) then [a] else [])
      else a :: part s (subAt T [a]) w := by
  induction w using List.reverseRecOn with
  | nil =>
      have h1 : part s T [a] = if IsCut s (subAt T [a]) then [a] else part s T [] := by
        simpa using part_concat (s := s) T [] a
      simp [h1]
  | append_singleton u b ih =>
      have hcons : a :: (u ++ [b]) = (a :: u) ++ [b] := by simp
      have hsub : subAt T ((a :: u) ++ [b]) = subAt (subAt T [a]) (u ++ [b]) := by
        rw [show (a :: u) ++ [b] = [a] ++ (u ++ [b]) by simp, subAt_append]
      rw [hcons, part_concat, hsub, part_concat]
      by_cases hcut : IsCut s (subAt (subAt T [a]) (u ++ [b]))
      · rw [ite_eq_left hcut, ite_eq_left hcut]
        simp
      · rw [ite_eq_right hcut, ite_eq_right hcut, ih]

/-- The step rule below a vertex with one child. -/
lemma part_one_false (t : Tri) (w : Word) :
    part s (one t) (false :: w) =
      if part s t w = [] then (if IsCut s t then [false] else []) else false :: part s t w := by
  simpa using part_cons (s := s) (one t) false w

/-- The step rule below the first child of a vertex with two. -/
lemma part_two_false (l r : Tri) (w : Word) :
    part s (two l r) (false :: w) =
      if part s l w = [] then (if IsCut s l then [false] else []) else false :: part s l w := by
  simpa using part_cons (s := s) (two l r) false w

/-- The step rule below the second child of a vertex with two. -/
lemma part_two_true (l r : Tri) (w : Word) :
    part s (two l r) (true :: w) =
      if part s r w = [] then (if IsCut s r then [true] else []) else true :: part s r w := by
  simpa using part_cons (s := s) (two l r) true w

/-! ### The part roots, listed by address -/

/-- The addresses of the maximal cut vertices of `t` and of the part roots
below them, in the order `cutForest` reads them. -/
def cutAddrs (s : ℕ) : Tri → List Word
  | leaf => if IsCut s leaf then [[]] else []
  | one t =>
      if IsCut s (one t) then [] :: (cutAddrs s t).map (fun w => false :: w)
      else (cutAddrs s t).map (fun w => false :: w)
  | two l r =>
      if IsCut s (two l r) then
        [] :: ((cutAddrs s l).map (fun w => false :: w) ++
          (cutAddrs s r).map (fun w => true :: w))
      else (cutAddrs s l).map (fun w => false :: w) ++ (cutAddrs s r).map (fun w => true :: w)

@[simp] lemma cutAddrs_leaf : cutAddrs s leaf = if IsCut s leaf then [[]] else [] := rfl

@[simp] lemma cutAddrs_one (t : Tri) :
    cutAddrs s (one t) =
      if IsCut s (one t) then [] :: (cutAddrs s t).map (fun w => false :: w)
      else (cutAddrs s t).map (fun w => false :: w) := rfl

@[simp] lemma cutAddrs_two (l r : Tri) :
    cutAddrs s (two l r) =
      if IsCut s (two l r) then
        [] :: ((cutAddrs s l).map (fun w => false :: w) ++
          (cutAddrs s r).map (fun w => true :: w))
      else (cutAddrs s l).map (fun w => false :: w) ++
        (cutAddrs s r).map (fun w => true :: w) := rfl

/-- The addresses of the part roots strictly below the root of `t`. -/
def rootAddrs (s : ℕ) : Tri → List Word
  | leaf => []
  | one t => (cutAddrs s t).map (fun w => false :: w)
  | two l r => (cutAddrs s l).map (fun w => false :: w) ++ (cutAddrs s r).map (fun w => true :: w)

@[simp] lemma rootAddrs_leaf : rootAddrs s leaf = [] := rfl

@[simp] lemma rootAddrs_one (t : Tri) :
    rootAddrs s (one t) = (cutAddrs s t).map (fun w => false :: w) := rfl

@[simp] lemma rootAddrs_two (l r : Tri) :
    rootAddrs s (two l r) =
      (cutAddrs s l).map (fun w => false :: w) ++
        (cutAddrs s r).map (fun w => true :: w) := rfl

/-- A cut root is listed ahead of the part roots below it. -/
lemma cutAddrs_eq (t : Tri) :
    cutAddrs s t = if IsCut s t then [] :: rootAddrs s t else rootAddrs s t := by
  cases t <;> simp

/-- The vertices of the contraction and their addresses are counted alike. -/
lemma length_cutAddrs (t : Tri) : (cutAddrs s t).length = RTree.sizeF (cutForest s t) := by
  induction t with
  | leaf =>
      by_cases h : IsCut s leaf
      · rw [cutAddrs_leaf, cutForest_leaf, ite_eq_left h, ite_eq_left h]
        simp
      · rw [cutAddrs_leaf, cutForest_leaf, ite_eq_right h, ite_eq_right h]
        simp
  | one t ih =>
      by_cases h : IsCut s (one t)
      · rw [cutAddrs_one, cutForest_one, ite_eq_left h, ite_eq_left h]
        simp only [List.length_cons, List.length_map, RTree.sizeF_cons, RTree.sizeF_nil,
          RTree.size_node, ih]
        omega
      · rw [cutAddrs_one, cutForest_one, ite_eq_right h, ite_eq_right h]
        simp only [List.length_map, ih]
  | two l r ihl ihr =>
      by_cases h : IsCut s (two l r)
      · rw [cutAddrs_two, cutForest_two, ite_eq_left h, ite_eq_left h]
        simp only [List.length_cons, List.length_append, List.length_map, RTree.sizeF_cons,
          RTree.sizeF_nil, RTree.size_node, RTree.sizeF_append, ihl, ihr]
        omega
      · rw [cutAddrs_two, cutForest_two, ite_eq_right h, ite_eq_right h]
        simp only [List.length_append, List.length_map, RTree.sizeF_append, ihl, ihr]

/-- **`thm:dilution`**, the vertices of the contraction listed by address: the
root part first, then the part roots below it in the order the tree is read. -/
def partList (s : ℕ) (T : Tri) : List Word := [] :: rootAddrs s T

@[simp] lemma partList_eq (T : Tri) : partList s T = [] :: rootAddrs s T := rfl

/-- The list of part roots is as long as the contraction has vertices. -/
lemma length_partList (T : Tri) : (partList s T).length = (contractTree s T).size := by
  cases T with
  | leaf => simp
  | one t =>
      simp only [partList_eq, rootAddrs_one, contractTree_eq, rootForest_one, List.length_cons,
        List.length_map, RTree.size_node, length_cutAddrs]
      omega
  | two l r =>
      simp only [partList_eq, rootAddrs_two, contractTree_eq, rootForest_two, List.length_cons,
        List.length_append, List.length_map, RTree.size_node, RTree.sizeF_append,
        length_cutAddrs]
      omega

/-! ### The listed addresses are the part roots -/

/-- The part roots below the root are named by nonempty addresses. -/
lemma ne_nil_of_mem_rootAddrs {t : Tri} {x : Word} (h : x ∈ rootAddrs s t) : x ≠ [] := by
  cases t with
  | leaf => simp at h
  | one t =>
      rw [rootAddrs_one, List.mem_map] at h
      obtain ⟨y, -, rfl⟩ := h
      simp
  | two l r =>
      rw [rootAddrs_two, List.mem_append] at h
      rcases h with h | h <;> rw [List.mem_map] at h <;> obtain ⟨y, -, rfl⟩ := h <;> simp

/-- The root of a subtree is listed exactly when the subtree is cut. -/
lemma isCut_of_nil_mem_cutAddrs {t : Tri} (h : ([] : Word) ∈ cutAddrs s t) : IsCut s t := by
  by_contra hc
  rw [cutAddrs_eq, ite_eq_right hc] at h
  exact ne_nil_of_mem_rootAddrs h rfl

/-- A cut subtree lists its own root. -/
lemma nil_mem_cutAddrs {t : Tri} (h : IsCut s t) : ([] : Word) ∈ cutAddrs s t := by
  rw [cutAddrs_eq, ite_eq_left h]
  exact List.mem_cons_self

/-- A part root of the subtree below a vertex with one child is one of the
tree's. -/
lemma mem_cutAddrs_one {t : Tri} {x : Word}
    (h : x ∈ (cutAddrs s t).map (fun w => false :: w)) : x ∈ cutAddrs s (one t) := by
  rw [cutAddrs_one]
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

/-- A part root of the first subtree below a vertex with two children is one of
the tree's. -/
lemma mem_cutAddrs_two_left {l r : Tri} {x : Word}
    (h : x ∈ (cutAddrs s l).map (fun w => false :: w)) : x ∈ cutAddrs s (two l r) := by
  rw [cutAddrs_two]
  split
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
  · exact List.mem_append_left _ h

/-- A part root of the second subtree below a vertex with two children is one
of the tree's. -/
lemma mem_cutAddrs_two_right {l r : Tri} {x : Word}
    (h : x ∈ (cutAddrs s r).map (fun w => true :: w)) : x ∈ cutAddrs s (two l r) := by
  rw [cutAddrs_two]
  split
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
  · exact List.mem_append_right _ h

/-- The part of an address is either the root or one of the listed part
roots. -/
lemma part_eq_nil_or_mem_cutAddrs : ∀ (t : Tri) (w : Word), t.IsAddr w →
    part s t w = [] ∨ part s t w ∈ cutAddrs s t := by
  intro t
  induction t with
  | leaf =>
      intro w hw
      rw [eq_nil_of_isAddr_leaf hw]
      exact Or.inl (part_nil _)
  | one t ih =>
      intro w hw
      cases w with
      | nil => exact Or.inl (part_nil _)
      | cons a w =>
          cases a with
          | true => exact absurd hw (isAddr_one_true t w)
          | false =>
              rw [part_one_false]
              by_cases hp : part s t w = []
              · rw [ite_eq_left hp]
                by_cases hc : IsCut s t
                · rw [ite_eq_left hc]
                  exact Or.inr (mem_cutAddrs_one (List.mem_map_of_mem (nil_mem_cutAddrs hc)))
                · rw [ite_eq_right hc]
                  exact Or.inl rfl
              · rw [ite_eq_right hp]
                rcases ih w hw with h | h
                · exact absurd h hp
                · exact Or.inr (mem_cutAddrs_one (List.mem_map_of_mem h))
  | two l r ihl ihr =>
      intro w hw
      cases w with
      | nil => exact Or.inl (part_nil _)
      | cons a w =>
          cases a with
          | false =>
              rw [part_two_false]
              by_cases hp : part s l w = []
              · rw [ite_eq_left hp]
                by_cases hc : IsCut s l
                · rw [ite_eq_left hc]
                  exact Or.inr (mem_cutAddrs_two_left
                    (List.mem_map_of_mem (nil_mem_cutAddrs hc)))
                · rw [ite_eq_right hc]
                  exact Or.inl rfl
              · rw [ite_eq_right hp]
                rcases ihl w hw with h | h
                · exact absurd h hp
                · exact Or.inr (mem_cutAddrs_two_left (List.mem_map_of_mem h))
          | true =>
              rw [part_two_true]
              by_cases hp : part s r w = []
              · rw [ite_eq_left hp]
                by_cases hc : IsCut s r
                · rw [ite_eq_left hc]
                  exact Or.inr (mem_cutAddrs_two_right
                    (List.mem_map_of_mem (nil_mem_cutAddrs hc)))
                · rw [ite_eq_right hc]
                  exact Or.inl rfl
              · rw [ite_eq_right hp]
                rcases ihr w hw with h | h
                · exact absurd h hp
                · exact Or.inr (mem_cutAddrs_two_right (List.mem_map_of_mem h))

/-- **The part of every vertex is listed.** -/
theorem part_mem_partList (T : Tri) {w : Word} (hw : T.IsAddr w) :
    part s T w ∈ partList s T := by
  rcases part_eq_nil_or_mem_cutAddrs T w hw with h | h
  · rw [partList_eq, h]
    exact List.mem_cons_self
  · rw [cutAddrs_eq] at h
    rw [partList_eq]
    split at h
    · exact h
    · exact List.mem_cons_of_mem _ h

/-- A listed address is an address of the tree topping its own part. -/
lemma isAddr_and_part_eq_of_mem_cutAddrs : ∀ (t : Tri) (x : Word), x ∈ cutAddrs s t →
    t.IsAddr x ∧ part s t x = x := by
  intro t
  induction t with
  | leaf =>
      intro x hx
      rw [cutAddrs_leaf] at hx
      split at hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨isAddr_nil _, part_nil _⟩
      · simp at hx
  | one t ih =>
      intro x hx
      rw [cutAddrs_eq] at hx
      have hbase : ∀ y ∈ (cutAddrs s t).map (fun w => false :: w),
          (one t).IsAddr y ∧ part s (one t) y = y := by
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        obtain ⟨hz1, hz2⟩ := ih z hz
        refine ⟨by simpa using hz1, ?_⟩
        rw [part_one_false]
        by_cases hzn : z = []
        · subst hzn
          rw [ite_eq_left hz2, ite_eq_left (isCut_of_nil_mem_cutAddrs hz)]
        · rw [ite_eq_right (by rw [hz2]; exact hzn), hz2]
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨isAddr_nil _, part_nil _⟩
        · exact hbase _ (by simpa using hx')
      · exact hbase _ (by simpa using hx)
  | two l r ihl ihr =>
      intro x hx
      rw [cutAddrs_eq] at hx
      have hleft : ∀ y ∈ (cutAddrs s l).map (fun w => false :: w),
          (two l r).IsAddr y ∧ part s (two l r) y = y := by
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        obtain ⟨hz1, hz2⟩ := ihl z hz
        refine ⟨by simpa using hz1, ?_⟩
        rw [part_two_false]
        by_cases hzn : z = []
        · subst hzn
          rw [ite_eq_left hz2, ite_eq_left (isCut_of_nil_mem_cutAddrs hz)]
        · rw [ite_eq_right (by rw [hz2]; exact hzn), hz2]
      have hright : ∀ y ∈ (cutAddrs s r).map (fun w => true :: w),
          (two l r).IsAddr y ∧ part s (two l r) y = y := by
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        obtain ⟨hz1, hz2⟩ := ihr z hz
        refine ⟨by simpa using hz1, ?_⟩
        rw [part_two_true]
        by_cases hzn : z = []
        · subst hzn
          rw [ite_eq_left hz2, ite_eq_left (isCut_of_nil_mem_cutAddrs hz)]
        · rw [ite_eq_right (by rw [hz2]; exact hzn), hz2]
      have hforest : ∀ y ∈ rootAddrs s (two l r),
          (two l r).IsAddr y ∧ part s (two l r) y = y := by
        intro y hy
        rw [rootAddrs_two, List.mem_append] at hy
        rcases hy with hy | hy
        · exact hleft y hy
        · exact hright y hy
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨isAddr_nil _, part_nil _⟩
        · exact hforest _ hx'
      · exact hforest _ hx

/-- **The listed addresses are exactly the part roots**: `partList` enumerates
the vertex set `PartVert s T` of the contracted tree. -/
theorem mem_partList_iff (T : Tri) {x : Word} :
    x ∈ partList s T ↔ T.IsAddr x ∧ part s T x = x := by
  constructor
  · intro hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨isAddr_nil _, part_nil _⟩
    · refine isAddr_and_part_eq_of_mem_cutAddrs T x ?_
      rw [cutAddrs_eq]
      split
      · exact List.mem_cons_of_mem _ hx'
      · exact hx'
  · rintro ⟨hx, hpx⟩
    have := part_mem_partList (s := s) T hx
    rwa [hpx] at this

/-- The part roots are listed once each. -/
lemma nodup_cutAddrs (t : Tri) : (cutAddrs s t).Nodup := by
  induction t with
  | leaf =>
      rw [cutAddrs_leaf]
      split <;> simp
  | one t ih =>
      rw [cutAddrs_one]
      have hmap : ((cutAddrs s t).map (fun w => false :: w)).Nodup :=
        ih.map (fun _ _ h => by simpa using h)
      split
      · refine List.nodup_cons.mpr ⟨?_, hmap⟩
        intro hc
        rw [List.mem_map] at hc
        obtain ⟨z, -, hz⟩ := hc
        exact absurd hz.symm (by simp)
      · exact hmap
  | two l r ihl ihr =>
      rw [cutAddrs_two]
      have hl : ((cutAddrs s l).map (fun w => false :: w)).Nodup :=
        ihl.map (fun _ _ h => by simpa using h)
      have hr : ((cutAddrs s r).map (fun w => true :: w)).Nodup :=
        ihr.map (fun _ _ h => by simpa using h)
      have happ : ((cutAddrs s l).map (fun w => false :: w) ++
          (cutAddrs s r).map (fun w => true :: w)).Nodup := by
        refine List.Nodup.append hl hr ?_
        intro x hx hx'
        rw [List.mem_map] at hx hx'
        obtain ⟨y, -, rfl⟩ := hx
        obtain ⟨z, -, hz⟩ := hx'
        exact absurd hz (by simp)
      split
      · refine List.nodup_cons.mpr ⟨?_, happ⟩
        intro hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc <;> rw [List.mem_map] at hc <;> obtain ⟨z, -, hz⟩ := hc <;>
          exact absurd hz.symm (by simp)
      · exact happ

/-- **The enumeration lists each part root once.** -/
theorem nodup_partList (T : Tri) : (partList s T).Nodup := by
  rw [partList_eq]
  refine List.nodup_cons.mpr ⟨fun hc => ne_nil_of_mem_rootAddrs hc rfl, ?_⟩
  have h := nodup_cutAddrs (s := s) T
  rw [cutAddrs_eq] at h
  split at h
  · exact (List.nodup_cons.mp h).2
  · exact h

/-! ### The mark -/

/-- **`thm:dilution`**, the mark: the part of a vertex, read as an index into
the vertices of the contraction. -/
def markOf (s : ℕ) (T : Tri) (w : Word) : ℕ := (partList s T).idxOf (part s T w)

/-- The mark of a vertex names a vertex of the contraction. -/
theorem markOf_lt (T : Tri) {w : Word} (hw : T.IsAddr w) :
    markOf s T w < (contractTree s T).size := by
  have h := List.idxOf_lt_length_of_mem (part_mem_partList (s := s) T hw)
  rwa [length_partList] at h

/-- Two vertices carry the same mark exactly when they lie in the same part. -/
theorem markOf_eq_iff (T : Tri) {v w : Word} (hv : T.IsAddr v) :
    markOf s T v = markOf s T w ↔ part s T v = part s T w :=
  List.idxOf_inj (part_mem_partList (s := s) T hv)

/-- The root part carries the mark `0`. -/
@[simp] lemma markOf_nil (T : Tri) : markOf s T [] = 0 := by
  rw [markOf, part_nil, partList_eq]
  simp [List.idxOf_cons_self]

/-! ### The marked contraction -/

/-- **`thm:dilution`**, the datum counted: the contraction of `T` at scale `s`
together with the part of the vertex `e`. -/
def contractPair (s : ℕ) (T : Tri) (e : Word) : RTree × ℕ := (contractTree s T, markOf s T e)

/-- **`thm:dilution`**, the hypothesis of the count: the marked contraction of a
tree of at most `n` vertices is a rooted tree of at most `n/s + 1` vertices with
one of them marked. -/
theorem contractPair_spec (hs : 1 ≤ s) {T : Tri} {n : ℕ} (hn : T.size ≤ n) {e : Word}
    (he : T.IsAddr e) :
    (contractPair s T e).1.size ≤ n / s + 1 ∧
      (contractPair s T e).2 < (contractPair s T e).1.size := by
  refine ⟨?_, markOf_lt (s := s) T he⟩
  have h1 := size_contractTree_le_div (s := s) hs T
  have h2 : T.size / s ≤ n / s := Nat.div_le_div_right hn
  exact le_trans h1 (by omega)

end Tri

/-! ### The vertices of the contraction are the part roots -/

open Tri

variable {s : ℕ} {T : Tri}

/-- **The bridge to `Contraction.lean`**: the addresses `partList` lists are
exactly the vertices of the contracted tree `partGraph s T`. -/
def partVertEquiv (s : ℕ) (T : Tri) :
    PartVert s T ≃ {x : Word // x ∈ (partList s T).toFinset} where
  toFun p := ⟨p.1, List.mem_toFinset.mpr ((mem_partList_iff T).mpr p.2)⟩
  invFun x := ⟨x.1, (mem_partList_iff T).mp (List.mem_toFinset.mp x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The part roots are finite in number. -/
instance instFintypePartVert (s : ℕ) (T : Tri) : Fintype (PartVert s T) :=
  Fintype.ofEquiv _ (partVertEquiv s T).symm

/-- **`thm:dilution`**: the contraction carries one vertex for each part, so the
count of `size_contractTree_le_div` is a count of the vertices of
`partGraph s T`. -/
theorem card_partVert (s : ℕ) (T : Tri) :
    Fintype.card (PartVert s T) = (contractTree s T).size := by
  rw [Fintype.card_congr (partVertEquiv s T), Fintype.card_coe,
    List.toFinset_card_of_nodup (nodup_partList T), length_partList]

/-! ### The marked contraction of a shape -/

/-- **`thm:dilution`**: the contraction of the realisation of a shape, marked at
the part of the exit. -/
def shapeContractPair (s : ℕ) (σ : Shape) : RTree × ℕ :=
  contractPair s σ.realise (Shape.neckAddr σ.decs)

/-- **`thm:dilution`**, the hypothesis of the count at a shape. -/
theorem shapeContractPair_spec {s : ℕ} (hs : 1 ≤ s) {σ : Shape} {n : ℕ}
    (hn : σ.size ≤ n) :
    (shapeContractPair s σ).1.size ≤ n / s + 1 ∧
      (shapeContractPair s σ).2 < (shapeContractPair s σ).1.size :=
  contractPair_spec hs hn (Shape.isAddr_neckAddr σ.decs)

/-- **`thm:dilution`**: a family of marked contractions of shapes of at most `n`
vertices, taken at scale `s`, has at most `e^{3(n/s+1)}` members. -/
theorem dilution_count_shape {s : ℕ} (hs : 1 ≤ s) (n : ℕ) (F : Finset (RTree × ℕ))
    (hF : ∀ p ∈ F, ∃ σ : Shape, σ.size ≤ n ∧ p = shapeContractPair s σ) :
    (F.card : ℝ) ≤ Real.exp (3 * ((n / s + 1 : ℕ) : ℝ)) := by
  refine RTree.dilution_count F (n / s + 1) ?_
  intro p hp
  obtain ⟨σ, hσ, rfl⟩ := hF p hp
  exact shapeContractPair_spec hs hσ

end ChainClasses
