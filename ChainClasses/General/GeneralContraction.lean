import Mathlib.Tactic
import ChainClasses.General.GeneralShapeMetric
import ChainClasses.General.GeneralDilution
import ChainClasses.Shape.AddrMetric

/-!
`it:general-dilution` of `matching_classes_general.tex`: `thm:dilution` at general
arity, the greedy contraction of a rose tree and the count it gives.

The cut of `GeneralDilution.lean` is read at the level of addresses, as
`Contraction.lean` reads the binary cut.  A vertex is *cut* when the remainder
accumulated below it reaches `s`, and the part of a vertex is topped by the nearest
cut ancestor-or-self, the root if there is none.  Three facts drive everything: the
part root is an ancestor (`part_prefix`), a vertex sits at most `s-1` below its part
root (`length_sub_length_part_le`), and a step down the tree either stays in the part
or opens a part at that very vertex (`part_append_singleton`).  None of them sees the
arity, so the contraction is a `2s`-marked quasi-isometry exactly as in the binary
case: a walk in the realisation projects to a walk of no greater length, and an edge
of the contraction spans at most `s` ambient edges.

The contraction is then assembled into a rose tree by the recursion of
`ContractTree.lean`, its vertices are listed by address in the order the recursion
reads them, and the pairing with the addresses of the rose tree is an isometry of
marked spaces, so the marked contraction determines the contracted tree up to
isometry and two shapes with the same marked contraction are `72s³`-comparable.
What the arity changes is only the degree of the contraction: a part has at most
`1 + J(s-1)` vertices, each with at most `J` children, so the contraction of a tree
with offspring numbers in `{0,…,J}` has offspring numbers in `{0,…,J(1+J(s-1))}`.

* `RTree.rawSize`, `RTree.IsCut`, `RTree.remSize_eq`: the accumulated remainder and
  the cut rule, matching `RTree.remSize` of `GeneralDilution.lean`.
* `RTree.subAt`, `RTree.part`, `RTree.IsPartRoot`: the subtree at an address and the
  top of a part, with `part_prefix`, `length_sub_length_part_le` and
  `part_append_singleton`.
* `GPartVert`, `gPartGraph`, `gPartSpace`: the contracted tree and its marked metric
  space.
* `markedQI_gContract`: **`it:general-dilution`, the contraction** is a `2s`-marked
  quasi-isometry, the constant free of the arity.
* `RTree.cutForest`, `RTree.gContractTree`, `size_gContractTree_le_div`: the
  contraction as a rose tree with at most `|t|/s + 1` vertices.
* `RTree.cutAddrs`, `RTree.partList`, `mem_partList_iff`, `nodup_partList`: the part
  roots listed by address, once each.
* `RTree.markOf`, `RTree.gContractPair`, `gContractMark`, `gShapeContractPair`: the
  marked contraction, the datum `RTree.dilution_count` counts.
* `gToVert`, `dist_gToVert`, `isMarkedIsom_gToVert`, `markedQI_gContractTree`: the
  contracted tree is the rose tree as a marked metric space.
* `degLe_gContractTree`: **`it:general-dilution`, the degree**: the contraction of a
  tree with offspring numbers in `{0,…,J}` has offspring numbers in
  `{0,…,J(1+J(s-1))}`.
* `markedQI_of_gContractPair_eq`, `markedQI_of_gShapeContractPair_eq`: marked rose
  trees, or shapes, with the same marked contraction are `72s³`-comparable.
* `gDilution`, `gDilution_netMem`: **`thm:dilution` at general arity**, over the scale
  `dilScale` and, in the crude regime `D ≤ 729`, the scale one at which the
  contraction is the realisation itself.
-/

namespace ChainClasses

open SimpleGraph

namespace RTree

variable {s : ℕ}

/-! ### The cut rule at the level of addresses -/

@[simp] lemma remSizeF_nil : remSizeF s [] = 0 := by rw [remSizeF]

@[simp] lemma remSizeF_cons (c : RTree) (cs : List RTree) :
    remSizeF s (c :: cs) = remSize s c + remSizeF s cs := by rw [remSizeF]

/-- The remainder accumulated at a vertex before the cut rule is applied: the vertex
together with the remainders passed up by its children. -/
def rawSize (s : ℕ) : RTree → ℕ
  | .node cs => 1 + remSizeF s cs

@[simp] lemma rawSize_node (cs : List RTree) : rawSize s (.node cs) = 1 + remSizeF s cs := rfl

/-- A vertex is cut when the remainder it accumulates reaches `s`. -/
def IsCut (s : ℕ) (t : RTree) : Prop := s ≤ rawSize s t

instance (s : ℕ) (t : RTree) : Decidable (IsCut s t) := Nat.decLe _ _

/-- The cut rule at a vertex, read on its children. -/
lemma isCut_node_iff (cs : List RTree) : IsCut s (.node cs) ↔ s ≤ 1 + remSizeF s cs := Iff.rfl

/-- The accumulated remainder counts the vertex itself. -/
lemma one_le_rawSize (t : RTree) : 1 ≤ rawSize s t := by
  cases t with | node cs => rw [rawSize_node]; omega

/-- The cut rule, as `GeneralDilution.lean` states it. -/
lemma remSize_eq (t : RTree) : remSize s t = if IsCut s t then 0 else rawSize s t := by
  cases t with | node cs => rw [remSize]; rfl

/-- An uncut vertex passes up everything it has accumulated. -/
lemma remSize_of_not_isCut {t : RTree} (h : ¬ IsCut s t) : remSize s t = rawSize s t := by
  rw [remSize_eq, if_neg h]

/-- The remainder of an uncut vertex is below `s`. -/
lemma rawSize_lt_of_not_isCut {t : RTree} (h : ¬ IsCut s t) : rawSize s t < s :=
  Nat.not_le.mp h

/-- A child passes up at most what the forest accumulates. -/
lemma remSize_le_remSizeF : ∀ (cs : List RTree) (i : ℕ) (h : i < cs.length),
    remSize s cs[i] ≤ remSizeF s cs
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => by rw [remSizeF_cons]; simp
  | _ :: cs, i + 1, h => by
      rw [remSizeF_cons]
      have := remSize_le_remSizeF cs i (by simpa using h)
      simp only [List.getElem_cons_succ]
      omega

/-! ### Subtrees -/

/-- The subtree at an address, a single vertex off the address set. -/
def subAt : RTree → List ℕ → RTree
  | t, [] => t
  | .node cs, i :: w => subAt (cs.getD i (.node [])) w

@[simp] lemma subAt_nil (t : RTree) : subAt t [] = t := by cases t; rfl

@[simp] lemma subAt_cons (cs : List RTree) (i : ℕ) (w : List ℕ) :
    subAt (.node cs) (i :: w) = subAt (cs.getD i (.node [])) w := rfl

/-- Reading a letter naming a child lands in that child. -/
lemma subAt_getElem (cs : List RTree) {i : ℕ} (h : i < cs.length) (w : List ℕ) :
    subAt (.node cs) (i :: w) = subAt cs[i] w := by
  rw [subAt_cons, List.getD_eq_getElem _ _ h]

/-- Reading an address in two steps lands in the subtree. -/
lemma isAddr_subAt : ∀ (t : RTree) (u v : List ℕ), IsAddr t (u ++ v) → IsAddr (subAt t u) v := by
  intro t u
  induction u generalizing t with
  | nil => intro v h; simpa using h
  | cons i u ih =>
      intro v h
      cases t with
      | node cs =>
          rw [List.cons_append, isAddr_cons] at h
          obtain ⟨hi, h⟩ := h
          rw [subAt_getElem cs hi]
          exact ih _ v h

/-- Reading an address in two steps. -/
lemma subAt_append : ∀ (t : RTree) (u v : List ℕ), subAt t (u ++ v) = subAt (subAt t u) v := by
  intro t u
  induction u generalizing t with
  | nil => simp
  | cons i u ih =>
      intro v
      cases t with
      | node cs => rw [List.cons_append, subAt_cons, subAt_cons, ih]

/-! ### The part of a vertex -/

/-- The top of the part containing an address, computed from the reversed address: the
nearest cut ancestor-or-self, the root if there is none. -/
def partRev (s : ℕ) (T : RTree) : List ℕ → List ℕ
  | [] => []
  | a :: r => if IsCut s (subAt T (r.reverse ++ [a])) then r.reverse ++ [a] else partRev s T r

/-- The top of the part containing an address. -/
def part (s : ℕ) (T : RTree) (w : List ℕ) : List ℕ := partRev s T w.reverse

@[simp] lemma part_nil (T : RTree) : part s T [] = [] := rfl

/-- The defining recursion: a vertex tops its own part when it is cut, and otherwise
belongs to the part of its parent. -/
lemma part_concat (T : RTree) (u : List ℕ) (a : ℕ) :
    part s T (u ++ [a]) = if IsCut s (subAt T (u ++ [a])) then u ++ [a] else part s T u := by
  simp only [part, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, partRev, List.reverse_reverse]

lemma part_of_isCut {T : RTree} {u : List ℕ} {a : ℕ} (h : IsCut s (subAt T (u ++ [a]))) :
    part s T (u ++ [a]) = u ++ [a] := by rw [part_concat, if_pos h]

lemma part_of_not_isCut {T : RTree} {u : List ℕ} {a : ℕ} (h : ¬ IsCut s (subAt T (u ++ [a]))) :
    part s T (u ++ [a]) = part s T u := by rw [part_concat, if_neg h]

/-- The part root is an ancestor. -/
lemma part_prefix (T : RTree) : ∀ w : List ℕ, part s T w <+: w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u a ih =>
      rw [part_concat]
      split
      · exact List.prefix_refl _
      · exact ih.trans (List.prefix_append u [a])

lemma length_part_le (T : RTree) (w : List ℕ) : (part s T w).length ≤ w.length :=
  (part_prefix T w).length_le

/-- **The step rule.**  Moving one edge down either stays inside the part or opens a
part at that vertex. -/
lemma part_append_singleton (T : RTree) (u : List ℕ) (a : ℕ) :
    part s T (u ++ [a]) = u ++ [a] ∨ part s T (u ++ [a]) = part s T u := by
  rw [part_concat]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Below the part root nothing is cut. -/
lemma not_isCut_of_lt {T : RTree} : ∀ {w p : List ℕ}, p <+: w → (part s T w).length < p.length →
    ¬ IsCut s (subAt T p) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro p hp hlt
      rw [List.prefix_nil.mp hp] at hlt
      simp at hlt
  | append_singleton u a ih =>
      intro p hp hlt
      rcases eq_or_ne p (u ++ [a]) with rfl | hne
      · intro hcut
        rw [part_of_isCut hcut] at hlt
        omega
      · have hpu : p <+: u := by
          have hlen : p.length ≤ u.length := by
            have h1 := hp.length_le
            simp only [List.length_append, List.length_cons, List.length_nil] at h1
            rcases lt_or_eq_of_le h1 with h2 | h2
            · omega
            · refine absurd (hp.eq_of_length ?_) hne
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
          exact List.prefix_of_prefix_length_le hp (List.prefix_append u [a]) hlen
        refine ih hpu ?_
        rcases part_append_singleton (s := s) T u a with h | h
        · rw [h] at hlt
          have := hpu.length_le
          simp only [List.length_append, List.length_cons, List.length_nil] at hlt
          omega
        · rwa [h] at hlt

/-! ### The depth of a part -/

/-- **The chain bound.**  If no vertex from the root down to `w` is cut, the depth of
`w` plus the remainder it passes up is at most what the root accumulates: each step
down consumes at least one vertex of the remainder. -/
lemma chain_bound : ∀ (t : RTree) (w : List ℕ), IsAddr t w →
    (∀ p, p <+: w → ¬ IsCut s (subAt t p)) →
    w.length + remSize s (subAt t w) ≤ rawSize s t := by
  intro t w
  induction w generalizing t with
  | nil =>
      intro _ h
      have h0 := h [] List.nil_prefix
      rw [subAt_nil] at h0 ⊢
      rw [remSize_of_not_isCut h0]
      simp
  | cons i u ih =>
      intro haddr h
      cases t with
      | node cs =>
          obtain ⟨hi, haddr⟩ := isAddr_cons.mp haddr
          have hchild : ¬ IsCut s cs[i] := by
            have := h [i] ⟨u, rfl⟩
            rwa [subAt_getElem cs hi, subAt_nil] at this
          have hih := ih cs[i] haddr fun p hp => by
            have := h (i :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
            rwa [subAt_getElem cs hi] at this
          have hl : remSize s cs[i] = rawSize s cs[i] := remSize_of_not_isCut hchild
          have hle := remSize_le_remSizeF (s := s) cs i hi
          rw [subAt_getElem cs hi, rawSize_node, List.length_cons]
          omega

/-- **A vertex sits at most `s-1` below its part root.**  The vertices strictly
between are uncut, and each step down consumes one vertex of the remainder
accumulated just below the part root, which is less than `s`. -/
theorem length_sub_length_part_le (T : RTree) {w : List ℕ} (hw : IsAddr T w) :
    w.length - (part s T w).length ≤ s - 1 := by
  obtain ⟨p, hpw⟩ : ∃ p, part s T w = p := ⟨_, rfl⟩
  have hpref : p <+: w := hpw ▸ part_prefix T w
  rw [hpw]
  rcases eq_or_ne p w with rfl | hne
  · omega
  obtain ⟨v, hv⟩ := hpref
  obtain ⟨b, v', rfl⟩ : ∃ (b : ℕ) (v' : List ℕ), v = b :: v' := by
    cases v with
    | nil => exact absurd (by simpa using hv) hne
    | cons b v' => exact ⟨b, v', rfl⟩
  subst hv
  have hsplit : p ++ b :: v' = (p ++ [b]) ++ v' := by simp
  -- everything strictly below the part root on the way down is uncut
  have hbelow : ∀ q, q <+: v' → ¬ IsCut s (subAt (subAt T (p ++ [b])) q) := by
    intro q hq
    rw [← subAt_append]
    refine not_isCut_of_lt (w := p ++ b :: v') ?_ ?_
    · rw [hsplit]
      exact List.prefix_append_right_inj (p ++ [b]) |>.mpr hq
    · rw [hpw]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have haddr : IsAddr (subAt T (p ++ [b])) v' :=
    isAddr_subAt _ _ _ (by rw [← hsplit]; exact hw)
  have hchild : ¬ IsCut s (subAt T (p ++ [b])) := by
    have := hbelow [] List.nil_prefix
    rwa [subAt_nil] at this
  have hlast : ¬ IsCut s (subAt (subAt T (p ++ [b])) v') := hbelow v' (List.prefix_refl _)
  have hone : 1 ≤ remSize s (subAt (subAt T (p ++ [b])) v') := by
    rw [remSize_of_not_isCut hlast]
    exact one_le_rawSize _
  have hkey := chain_bound (subAt T (p ++ [b])) v' haddr hbelow
  have hlt := rawSize_lt_of_not_isCut hchild
  simp only [List.length_append, List.length_cons]
  omega

/-- The part root tops its own part. -/
lemma part_idem (T : RTree) : ∀ w : List ℕ, part s T (part s T w) = part s T w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u a ih =>
      rw [part_concat]
      split
      · next h => rw [part_of_isCut h]
      · exact ih

/-- An address tops its own part. -/
def IsPartRoot (s : ℕ) (T : RTree) (w : List ℕ) : Prop := part s T w = w

@[simp] lemma isPartRoot_nil (T : RTree) : IsPartRoot s T [] := part_nil T

end RTree

/-! ### The contracted tree -/

open RTree

variable (s : ℕ) (t : RTree)

/-- A vertex of the contracted tree: an address topping its own part. -/
def GPartVert : Type := {w : List ℕ // w ∈ addrList t ∧ IsPartRoot s t w}

variable {s t}

/-- The part of an address, as a vertex of the contracted tree. -/
def gContract {w : List ℕ} (hw : w ∈ addrList t) : GPartVert s t :=
  ⟨part s t w, prefix_mem_addrList t hw (part_prefix t w), part_idem t w⟩

@[simp] lemma gContract_val {w : List ℕ} (hw : w ∈ addrList t) :
    (gContract (s := s) hw).1 = part s t w := rfl

/-- Every part root is its own contraction. -/
lemma gContract_self (p : GPartVert s t) : gContract (s := s) p.2.1 = p :=
  Subtype.ext p.2.2

/-- One vertex of the contracted tree lies below another: the second is a child in the
ambient tree whose part is topped by the first. -/
def GPartStep (p q : GPartVert s t) : Prop :=
  ∃ (u : List ℕ) (a : ℕ), q.1 = u ++ [a] ∧ p.1 = part s t u

variable (s t)

/-- **The contracted tree**: the part roots, joined when one is the part of the parent
of the other. -/
def gPartGraph : SimpleGraph (GPartVert s t) where
  Adj p q := GPartStep p q ∨ GPartStep q p
  symm := ⟨fun {_ _} h => h.symm⟩
  loopless := ⟨fun {p} h => by
    have hkey : ¬ GPartStep p p := by
      rintro ⟨u, a, h1, h2⟩
      have hlen := length_part_le (s := s) t u
      rw [← h2] at hlen
      rw [h1] at hlen
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    rcases h with h | h
    · exact hkey h
    · exact hkey h⟩

variable {s t}

@[simp] lemma gPartGraph_adj {p q : GPartVert s t} :
    (gPartGraph s t).Adj p q ↔ GPartStep p q ∨ GPartStep q p := Iff.rfl

/-- The root part. -/
def gRootPart : GPartVert s t := ⟨[], nil_mem_addrList t, part_nil t⟩

/-- Climbing one step: the part of the parent is adjacent to the part below. -/
lemma adj_gContract_dropLast {p : GPartVert s t} {u : List ℕ} {a : ℕ} (hp : p.1 = u ++ [a])
    (hu : u ∈ addrList t) : (gPartGraph s t).Adj (gContract (s := s) hu) p :=
  Or.inl ⟨u, a, hp, rfl⟩

/-- **The contracted tree is connected**: every part root climbs to the root part. -/
theorem gPartGraph_connected : (gPartGraph s t).Connected := by
  have key : ∀ (n : ℕ) (p : GPartVert s t), p.1.length ≤ n →
      (gPartGraph s t).Reachable (gRootPart (s := s) (t := t)) p := by
    intro n
    induction n with
    | zero =>
        intro p hp
        have : p.1 = [] := List.length_eq_zero_iff.mp (by omega)
        exact (Subtype.ext this : p = gRootPart).symm ▸ Reachable.refl _
    | succ n ih =>
        intro p hp
        rcases List.eq_nil_or_concat p.1 with h | ⟨u, a, hua⟩
        · exact (Subtype.ext h : p = gRootPart).symm ▸ Reachable.refl _
        · have hua' : p.1 = u ++ [a] := by rw [hua]; simp
          have hu : u ∈ addrList t := by
            refine prefix_mem_addrList t p.2.1 ?_
            rw [hua']
            exact List.prefix_append u [a]
          have hlen : (gContract (s := s) hu).1.length ≤ n := by
            have h1 := length_part_le (s := s) t u
            have h2 : p.1.length = u.length + 1 := by
              rw [hua']
              simp
            simp only [gContract_val]
            omega
          exact (ih _ hlen).trans (Adj.reachable (adj_gContract_dropLast hua' hu))
  haveI : Nonempty (GPartVert s t) := ⟨gRootPart⟩
  exact ⟨fun p q => (key p.1.length p le_rfl).symm.trans (key q.1.length q le_rfl)⟩

/-- The metric of the contracted tree. -/
noncomputable instance instMetricSpaceGPartVert : MetricSpace (GPartVert s t) where
  dist p q := ((gPartGraph s t).dist p q : ℝ)
  dist_self p := by simp
  dist_comm p q := by simp only [SimpleGraph.dist_comm]
  dist_triangle p q r := by
    have := (gPartGraph_connected (s := s) (t := t)).dist_triangle (u := p) (v := q) (w := r)
    exact_mod_cast this
  eq_of_dist_eq_zero {p q} h := by
    refine (gPartGraph_connected (s := s) (t := t)).dist_eq_zero_iff.mp ?_
    exact_mod_cast h

@[simp] lemma dist_gPartVert (p q : GPartVert s t) :
    dist p q = ((gPartGraph s t).dist p q : ℝ) := rfl

/-! ### The two bounds -/

/-- An edge of a rose tree joins a vertex to a child. -/
lemma exists_concat_of_adj {x y : Vert t} (h : (rtreeGraph t).Adj x y) :
    (∃ b, y.1 = x.1 ++ [b]) ∨ (∃ b, x.1 = y.1 ++ [b]) := by
  have key : ∀ {x y : Vert t}, x ≠ y → x.1 = y.1.dropLast → ∃ b, y.1 = x.1 ++ [b] := by
    intro x y hne hxy
    rcases List.eq_nil_or_concat y.1 with hy | ⟨u, b, hu⟩
    · refine absurd (Subtype.ext ?_) hne
      rw [hxy, hy]
      rfl
    · refine ⟨b, ?_⟩
      rw [hxy, hu, List.concat_eq_append, List.dropLast_concat]
  obtain ⟨hne, h | h⟩ := h
  · exact Or.inl (key hne h)
  · exact Or.inr (key hne.symm h)

/-- One ambient edge moves the part by at most one edge of the contraction. -/
lemma dist_gContract_adj {x y : Vert t} (h : (rtreeGraph t).Adj x y) :
    (gPartGraph s t).dist (gContract (s := s) x.2) (gContract (s := s) y.2) ≤ 1 := by
  have key : ∀ (x y : Vert t) (b : ℕ), y.1 = x.1 ++ [b] →
      (gPartGraph s t).dist (gContract (s := s) x.2) (gContract (s := s) y.2) ≤ 1 := by
    intro x y b hxy
    rcases part_append_singleton (s := s) t x.1 b with hcut | hsame
    · rcases eq_or_ne (gContract (s := s) x.2) (gContract (s := s) y.2) with heq | hne
      · rw [heq]
        simp
      · have hadj : (gPartGraph s t).Adj (gContract (s := s) x.2) (gContract (s := s) y.2) :=
          Or.inl ⟨x.1, b, by rw [gContract_val, hxy]; exact hcut, rfl⟩
        exact SimpleGraph.dist_le (Walk.cons hadj Walk.nil)
    · have : gContract (s := s) x.2 = gContract (s := s) y.2 := by
        refine Subtype.ext ?_
        simp only [gContract_val, hxy, hsame]
      rw [this]
      simp
  rcases exists_concat_of_adj h with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact key x y b hb
  · rw [SimpleGraph.dist_comm]
    exact key y x b hb

/-- The contraction of a walk is a walk of no greater length. -/
lemma dist_gContract_le_walk {x y : Vert t} (p : (rtreeGraph t).Walk x y) :
    (gPartGraph s t).dist (gContract (s := s) x.2) (gContract (s := s) y.2) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab _ ih =>
      have h1 := dist_gContract_adj (s := s) hab
      have h2 := (gPartGraph_connected (s := s) (t := t)).dist_triangle
        (u := gContract (s := s) a.2) (v := gContract (s := s) b.2) (w := gContract (s := s) c.2)
      simp only [Walk.length_cons]
      omega

/-- **The upper bound**: the contraction does not increase distances. -/
theorem dist_gContract_le (x y : Vert t) :
    (gPartGraph s t).dist (gContract (s := s) x.2) (gContract (s := s) y.2)
      ≤ (rtreeGraph t).dist x y := by
  obtain ⟨p, hp⟩ := ((rtreeGraph_connected t) x y).exists_walk_length_eq_dist
  have hle := dist_gContract_le_walk (s := s) p
  rwa [hp] at hle

/-- Climbing from an address to a prefix takes one edge per letter dropped. -/
lemma rtree_dist_le_of_prefix_aux (t : RTree) : ∀ (n : ℕ) (x y : Vert t), x.1 <+: y.1 →
    y.1.length ≤ x.1.length + n → (rtreeGraph t).dist x y ≤ n := by
  intro n
  induction n with
  | zero =>
      intro x y hp hl
      have hxy : x = y := Subtype.ext (hp.eq_of_length (by have := hp.length_le; omega))
      rw [hxy]
      simp
  | succ n ih =>
      intro x y hp hl
      rcases eq_or_ne x y with rfl | hne
      · simp
      · have hlen : x.1.length < y.1.length := by
          have h1 := hp.length_le
          rcases lt_or_eq_of_le h1 with h2 | h2
          · exact h2
          · exact absurd (Subtype.ext (hp.eq_of_length h2)) hne
        have hy : y.1 ≠ [] := by
          intro h
          rw [h] at hlen
          simp at hlen
        set z : Vert t := ⟨y.1.dropLast, dropLast_mem_addrList t y.1 y.2⟩ with hz
        have hzlen : z.1.length + 1 = y.1.length := by
          rw [hz, List.length_dropLast]
          omega
        have hxz : x.1 <+: z.1 := by
          refine List.prefix_of_prefix_length_le hp (List.dropLast_prefix y.1) ?_
          rw [hz, List.length_dropLast]
          omega
        have hzy : (rtreeGraph t).Adj z y := by
          refine ⟨fun h => ?_, Or.inl rfl⟩
          have : z.1.length = y.1.length := congrArg (fun v : Vert t => v.1.length) h
          omega
        have h1 := ih x z hxz (by omega)
        have h2 : (rtreeGraph t).dist z y ≤ 1 := SimpleGraph.dist_le (Walk.cons hzy Walk.nil)
        have h3 := (rtreeGraph_connected t).dist_triangle (u := x) (v := z) (w := y)
        omega

/-- The distance from an address to a prefix is at most the number of letters
dropped. -/
lemma rtree_dist_le_of_prefix {x y : Vert t} (h : x.1 <+: y.1) :
    (rtreeGraph t).dist x y ≤ y.1.length - x.1.length :=
  rtree_dist_le_of_prefix_aux t _ x y h (by have := h.length_le; omega)

/-- A part root, as a vertex of the ambient tree. -/
def gAmb (p : GPartVert s t) : Vert t := ⟨p.1, p.2.1⟩

@[simp] lemma gAmb_val (p : GPartVert s t) : (gAmb p).1 = p.1 := rfl

/-- One edge of the contraction spans at most `s` ambient edges: the parent of the
lower part root lies in the upper part, at most `s-1` below its top. -/
lemma dist_gAmb_le_of_adj (hs : 1 ≤ s) {p q : GPartVert s t} (h : (gPartGraph s t).Adj p q) :
    (rtreeGraph t).dist (gAmb p) (gAmb q) ≤ s := by
  have key : ∀ {p q : GPartVert s t}, GPartStep p q →
      (rtreeGraph t).dist (gAmb p) (gAmb q) ≤ s := by
    rintro p q ⟨u, a, h1, h2⟩
    have hu : IsAddr t u := by
      refine isAddr_of_prefix (mem_addrList_iff.mp q.2.1) ?_
      rw [h1]
      exact List.prefix_append u [a]
    have hpref : p.1 <+: q.1 := by
      rw [h1, h2]
      exact (part_prefix t u).trans (List.prefix_append u [a])
    have hd := length_sub_length_part_le (s := s) t hu
    have h3 : q.1.length = u.length + 1 := by rw [h1]; simp
    have h4 : p.1.length = (part s t u).length := by rw [h2]
    have h5 := length_part_le (s := s) t u
    have h6 := rtree_dist_le_of_prefix (x := gAmb p) (y := gAmb q) hpref
    simp only [gAmb_val] at h6
    omega
  rcases h with h | h
  · exact key h
  · rw [SimpleGraph.dist_comm]
    exact key h

/-- Lifting a walk of the contraction to the realisation. -/
lemma dist_gAmb_le_of_walk (hs : 1 ≤ s) {p q : GPartVert s t} (w : (gPartGraph s t).Walk p q) :
    (rtreeGraph t).dist (gAmb p) (gAmb q) ≤ s * w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab _ ih =>
      have h1 := dist_gAmb_le_of_adj (s := s) hs hab
      have h2 := (rtreeGraph_connected t).dist_triangle (u := gAmb a) (v := gAmb b) (w := gAmb c)
      simp only [Walk.length_cons, Nat.mul_add, Nat.mul_one]
      omega

lemma dist_gAmb_le (hs : 1 ≤ s) (p q : GPartVert s t) :
    (rtreeGraph t).dist (gAmb p) (gAmb q) ≤ s * (gPartGraph s t).dist p q := by
  obtain ⟨w, hw⟩ := ((gPartGraph_connected (s := s) (t := t)) p q).exists_walk_length_eq_dist
  have hle := dist_gAmb_le_of_walk (s := s) hs w
  rwa [hw] at hle

/-- A vertex is at most `s-1` ambient edges from its part root. -/
lemma dist_gAmb_gContract_le (hs : 1 ≤ s) (x : Vert t) :
    (rtreeGraph t).dist (gAmb (gContract (s := s) x.2)) x ≤ s - 1 := by
  have h := rtree_dist_le_of_prefix (x := gAmb (gContract (s := s) x.2)) (y := x)
    (part_prefix t x.1)
  have hd := length_sub_length_part_le (s := s) t (mem_addrList_iff.mp x.2)
  simp only [gAmb_val, gContract_val] at h
  have _ := hs
  omega

/-- **The lower bound**: a path of parts lifts, at most `s` ambient edges per part edge
and at most `s-1` at each end. -/
theorem rtree_dist_le_gContract (hs : 1 ≤ s) (x y : Vert t) :
    (rtreeGraph t).dist x y
      ≤ s * (gPartGraph s t).dist (gContract (s := s) x.2) (gContract (s := s) y.2)
        + 2 * (s - 1) := by
  have hx := dist_gAmb_gContract_le hs x
  have hy := dist_gAmb_gContract_le hs y
  have hmid := dist_gAmb_le hs (gContract (s := s) x.2) (gContract (s := s) y.2)
  have t1 := (rtreeGraph_connected t).dist_triangle (u := x) (v := gAmb (gContract (s := s) x.2))
    (w := y)
  have t2 := (rtreeGraph_connected t).dist_triangle (u := gAmb (gContract (s := s) x.2))
    (v := gAmb (gContract (s := s) y.2)) (w := y)
  have hcx : (rtreeGraph t).dist x (gAmb (gContract (s := s) x.2))
      = (rtreeGraph t).dist (gAmb (gContract (s := s) x.2)) x := SimpleGraph.dist_comm
  omega

/-! ### The contraction as a marked quasi-isometry -/

/-- The contracted tree as a marked metric space: the root part is the entry and the
part of the exit, when the exit is an address, is the mark. -/
noncomputable def gPartSpace (s : ℕ) (t : RTree) (e : List ℕ) : MarkedSpace where
  carrier := GPartVert s t
  entry := gRootPart
  exit := if he : e ∈ addrList t then gContract (s := s) he else gRootPart

lemma exit_gPartSpace_of_mem {e : List ℕ} (he : e ∈ addrList t) :
    (gPartSpace s t e).exit = gContract (s := s) he := dif_pos he

/-- **`it:general-dilution`, the contraction.**  Contracting every part of the greedy
cut to a point is a `2s`-marked quasi-isometry of a rose tree with a marked address
onto a rooted tree with a marked vertex; the constant does not see the arity. -/
theorem markedQI_gContract (hs : 1 ≤ s) {e : List ℕ} (he : e ∈ addrList t) :
    MarkedQI (2 * s : ℝ) (gSpace t e) (gPartSpace s t e) := by
  have hs0 : (0 : ℝ) ≤ 2 * (s : ℝ) := by positivity
  refine ⟨fun x => gContract (s := s) x.2, fun a b => ?_, fun a b => ?_, fun y => ?_, ?_, ?_⟩
  · -- the contraction does not increase distances
    have h := dist_gContract_le (s := s) a b
    have hgrow : (rtreeGraph t).dist a b ≤ 2 * s * (rtreeGraph t).dist a b + 2 * s := by
      nlinarith
    have hnat : (gPartGraph s t).dist (gContract (s := s) a.2) (gContract (s := s) b.2)
        ≤ 2 * s * (rtreeGraph t).dist a b + 2 * s := h.trans hgrow
    show (((gPartGraph s t).dist (gContract (s := s) a.2) (gContract (s := s) b.2) : ℕ) : ℝ)
      ≤ 2 * (s : ℝ) * (((rtreeGraph t).dist a b : ℕ) : ℝ) + 2 * (s : ℝ)
    exact_mod_cast hnat
  · -- a path of parts lifts
    have h := rtree_dist_le_gContract (s := s) hs a b
    have hgrow : s * (gPartGraph s t).dist (gContract (s := s) a.2) (gContract (s := s) b.2)
          + 2 * (s - 1)
        ≤ 2 * s * (gPartGraph s t).dist (gContract (s := s) a.2) (gContract (s := s) b.2)
            + 2 * s * (2 * s) := by
      have h1 : s * (gPartGraph s t).dist (gContract (s := s) a.2) (gContract (s := s) b.2)
          ≤ 2 * s * (gPartGraph s t).dist (gContract (s := s) a.2) (gContract (s := s) b.2) := by
        nlinarith
      have h2 : 2 * (s - 1) ≤ 2 * s * (2 * s) := by nlinarith [Nat.sub_le s 1]
      omega
    have hnat : (rtreeGraph t).dist a b
        ≤ 2 * s * (gPartGraph s t).dist (gContract (s := s) a.2) (gContract (s := s) b.2)
            + 2 * s * (2 * s) := h.trans hgrow
    show (((rtreeGraph t).dist a b : ℕ) : ℝ)
      ≤ 2 * (s : ℝ) * (((gPartGraph s t).dist (gContract (s := s) a.2)
          (gContract (s := s) b.2) : ℕ) : ℝ) + 2 * (s : ℝ) * (2 * (s : ℝ))
    exact_mod_cast hnat
  · -- every part root is its own contraction
    refine ⟨gAmb y, ?_⟩
    rw [show gContract (s := s) (gAmb y).2 = y from gContract_self y, _root_.dist_self]
    exact hs0
  · exact le_of_eq_of_le (_root_.dist_self _) hs0
  · rw [exit_gPartSpace_of_mem he]
    show dist (gContract (s := s) (gSpace t e).exit.2) (gContract (s := s) he) ≤ 2 * (s : ℝ)
    rw [exit_gSpace_of_mem he, _root_.dist_self]
    exact hs0


namespace RTree

variable {s : ℕ}

/-! ### The contraction as a rose tree -/

mutual

/-- The parts of `t` topped by the maximal cut vertices of `t`, in the order the tree
is read: a cut root takes the whole of `t` as one part, and an uncut root passes up the
parts of its children. -/
def cutForest (s : ℕ) : RTree → List RTree
  | .node cs => if IsCut s (.node cs) then [.node (cutForestF s cs)] else cutForestF s cs

/-- The parts topped by the maximal cut vertices of a forest, in order. -/
def cutForestF (s : ℕ) : List RTree → List RTree
  | [] => []
  | c :: cs => cutForest s c ++ cutForestF s cs

end

@[simp] lemma cutForest_node (cs : List RTree) :
    cutForest s (.node cs) =
      if IsCut s (.node cs) then [.node (cutForestF s cs)] else cutForestF s cs := by
  rw [cutForest]

@[simp] lemma cutForestF_nil : cutForestF s [] = [] := by rw [cutForestF]

@[simp] lemma cutForestF_cons (c : RTree) (cs : List RTree) :
    cutForestF s (c :: cs) = cutForest s c ++ cutForestF s cs := by rw [cutForestF]

/-- The children of the root part: the parts topped by the maximal cut vertices below
the root. -/
def rootForest (s : ℕ) : RTree → List RTree
  | .node cs => cutForestF s cs

@[simp] lemma rootForest_node (cs : List RTree) : rootForest s (.node cs) = cutForestF s cs := rfl

/-- **`it:general-dilution`**, the contracted tree: the part roots of `t` at scale `s`,
each part root carrying as children the part roots immediately below it. -/
def gContractTree (s : ℕ) (t : RTree) : RTree := .node (rootForest s t)

@[simp] lemma gContractTree_eq (t : RTree) : gContractTree s t = .node (rootForest s t) := rfl

/-- A cut root contributes the one part it tops; an uncut root contributes the parts
below it. -/
lemma cutForest_eq (t : RTree) :
    cutForest s t = if IsCut s t then [gContractTree s t] else rootForest s t := by
  cases t with | node cs => rw [cutForest_node, gContractTree_eq, rootForest_node]

/-- A vertex of the forest of parts lies in the forest of one of the trees. -/
lemma mem_cutForestF_iff : ∀ {cs : List RTree} {x : RTree},
    x ∈ cutForestF s cs ↔ ∃ c ∈ cs, x ∈ cutForest s c
  | [], x => by simp
  | c :: cs, x => by
      rw [cutForestF_cons, List.mem_append, mem_cutForestF_iff]
      simp

/-! ### The number of parts -/

@[simp] lemma cutCountF_nil : cutCountF s [] = 0 := by rw [cutCountF]

@[simp] lemma cutCountF_cons (c : RTree) (cs : List RTree) :
    cutCountF s (c :: cs) = cutCount s c + cutCountF s cs := by rw [cutCountF]

lemma sizeF_cutForestF_of : ∀ cs : List RTree,
    (∀ c ∈ cs, sizeF (cutForest s c) = cutCount s c) →
    sizeF (cutForestF s cs) = cutCountF s cs
  | [], _ => by simp
  | c :: cs, h => by
      rw [cutForestF_cons, sizeF_append, cutCountF_cons, h c (by simp),
        sizeF_cutForestF_of cs fun d hd => h d (by simp [hd])]

/-- The forest of parts has exactly as many vertices as the greedy cut has parts. -/
lemma sizeF_cutForest (t : RTree) : sizeF (cutForest s t) = cutCount s t := by
  induction t using ind with
  | _ cs ih =>
      have hF := sizeF_cutForestF_of cs ih
      rw [cutForest_node, cutCount]
      by_cases h : IsCut s (.node cs)
      · rw [if_pos h, if_pos ((isCut_node_iff cs).mp h)]
        simp only [sizeF_cons, sizeF_nil, size_node, hF]
        omega
      · rw [if_neg h, if_neg (fun hc => h ((isCut_node_iff cs).mpr hc)), hF, Nat.add_zero]

/-- The forest of parts of a forest is counted by the cut. -/
lemma sizeF_cutForestF (cs : List RTree) : sizeF (cutForestF s cs) = cutCountF s cs :=
  sizeF_cutForestF_of cs fun c _ => sizeF_cutForest c

/-- **`it:general-dilution`, the parts**: the contraction carries one vertex more than
the greedy cut has parts, the extra one being the root part. -/
theorem size_gContractTree_le (t : RTree) : (gContractTree s t).size ≤ cutCount s t + 1 := by
  cases t with
  | node cs =>
      rw [gContractTree_eq, rootForest_node, size_node, sizeF_cutForestF, cutCount]
      split <;> omega

/-- **`it:general-dilution`, the parts**: at scale `s` the contraction of a tree of `n`
vertices has at most `n/s + 1` vertices. -/
theorem size_gContractTree_le_div (hs : 1 ≤ s) (t : RTree) :
    (gContractTree s t).size ≤ t.size / s + 1 := by
  have h1 := size_gContractTree_le (s := s) t
  have h2 := cutCount_le_div hs t
  omega

/-! ### The part of an address, read from the top -/

/-- **The step rule at the top.**  The part of an address one letter down is the part
of the rest of the address inside the subtree, read one letter down, and the root of
the subtree when that part is the whole of it. -/
lemma part_cons (T : RTree) (a : ℕ) (w : List ℕ) :
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
      · rw [if_pos hcut, if_pos hcut]
        simp
      · rw [if_neg hcut, if_neg hcut, ih]

/-- The step rule below the first child. -/
lemma part_node_cons_zero (c : RTree) (cs : List RTree) (w : List ℕ) :
    part s (.node (c :: cs)) (0 :: w) =
      if part s c w = [] then (if IsCut s c then [0] else []) else 0 :: part s c w := by
  have h : subAt (.node (c :: cs)) [0] = c := rfl
  rw [part_cons, h]

/-- The step rule below a later child: the same as in the forest without the first
child, the letter shifted. -/
lemma part_node_cons_succ (c : RTree) (cs : List RTree) (j : ℕ) (w : List ℕ) :
    part s (.node (c :: cs)) ((j + 1) :: w) = bump 1 (part s (.node cs) (j :: w)) := by
  have h : subAt (.node (c :: cs)) [j + 1] = subAt (.node cs) [j] := by
    rw [subAt_cons, subAt_cons, List.getD_cons_succ]
  rw [part_cons, part_cons, h]
  split_ifs <;> simp [bump, Nat.add_comm]

/-! ### The part roots, listed by address -/

mutual

/-- The addresses of the maximal cut vertices of `t` and of the part roots below them,
in the order `cutForest` reads them. -/
def cutAddrs (s : ℕ) : RTree → List (List ℕ)
  | .node cs => if IsCut s (.node cs) then [] :: cutAddrsF s cs else cutAddrsF s cs

/-- The addresses of the part roots of a forest, the index of the tree prefixed to
each. -/
def cutAddrsF (s : ℕ) : List RTree → List (List ℕ)
  | [] => []
  | c :: cs => (cutAddrs s c).map (fun w => 0 :: w) ++ (cutAddrsF s cs).map (bump 1)

end

@[simp] lemma cutAddrs_node (cs : List RTree) :
    cutAddrs s (.node cs) = if IsCut s (.node cs) then [] :: cutAddrsF s cs else cutAddrsF s cs := by
  rw [cutAddrs]

@[simp] lemma cutAddrsF_nil : cutAddrsF s [] = [] := by rw [cutAddrsF]

@[simp] lemma cutAddrsF_cons (c : RTree) (cs : List RTree) :
    cutAddrsF s (c :: cs) = (cutAddrs s c).map (fun w => 0 :: w) ++ (cutAddrsF s cs).map (bump 1) := by
  rw [cutAddrsF]

/-- The addresses of the part roots strictly below the root of `t`. -/
def rootAddrs (s : ℕ) : RTree → List (List ℕ)
  | .node cs => cutAddrsF s cs

@[simp] lemma rootAddrs_node (cs : List RTree) : rootAddrs s (.node cs) = cutAddrsF s cs := rfl

/-- A cut root is listed ahead of the part roots below it. -/
lemma cutAddrs_eq (t : RTree) :
    cutAddrs s t = if IsCut s t then [] :: rootAddrs s t else rootAddrs s t := by
  cases t with | node cs => rw [cutAddrs_node, rootAddrs_node]

/-- The part roots of a forest, named by the tree they belong to. -/
lemma mem_cutAddrsF_iff : ∀ {F : List RTree} {w : List ℕ},
    w ∈ cutAddrsF s F ↔ ∃ i, ∃ h : i < F.length, ∃ v, v ∈ cutAddrs s F[i] ∧ w = i :: v
  | [], w => by simp
  | c :: cs, w => by
      rw [cutAddrsF_cons, List.mem_append]
      constructor
      · rintro (h | h)
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
          exact ⟨0, by simp, v, hv, rfl⟩
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
          obtain ⟨j, hj, v, hv, rfl⟩ := mem_cutAddrsF_iff.mp hu
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
              ⟨j :: v, mem_cutAddrsF_iff.mpr ⟨j, ?_, v, ?_, rfl⟩, ?_⟩)
            · simpa using hi
            · simpa using hv
            · simp only [bump_cons]
              congr 1
              omega

/-- The part roots below the root are named by nonempty addresses. -/
lemma ne_nil_of_mem_cutAddrsF {F : List RTree} {x : List ℕ} (h : x ∈ cutAddrsF s F) : x ≠ [] := by
  obtain ⟨i, -, v, -, rfl⟩ := mem_cutAddrsF_iff.mp h
  simp

lemma ne_nil_of_mem_rootAddrs {t : RTree} {x : List ℕ} (h : x ∈ rootAddrs s t) : x ≠ [] := by
  cases t with | node cs => exact ne_nil_of_mem_cutAddrsF h

/-- The root of a subtree is listed exactly when the subtree is cut. -/
lemma isCut_of_nil_mem_cutAddrs {t : RTree} (h : ([] : List ℕ) ∈ cutAddrs s t) : IsCut s t := by
  by_contra hc
  rw [cutAddrs_eq, if_neg hc] at h
  exact ne_nil_of_mem_rootAddrs h rfl

/-- A cut subtree lists its own root. -/
lemma nil_mem_cutAddrs {t : RTree} (h : IsCut s t) : ([] : List ℕ) ∈ cutAddrs s t := by
  rw [cutAddrs_eq, if_pos h]
  exact List.mem_cons_self

/-- A part root below the root is one of the tree's. -/
lemma mem_cutAddrs_of_mem_cutAddrsF {cs : List RTree} {x : List ℕ} (h : x ∈ cutAddrsF s cs) :
    x ∈ cutAddrs s (.node cs) := by
  rw [cutAddrs_node]
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

/-- The part of an address is either the root or one of the listed part roots. -/
lemma part_eq_nil_or_mem_cutAddrs : ∀ (t : RTree) (w : List ℕ), IsAddr t w →
    part s t w = [] ∨ part s t w ∈ cutAddrs s t := by
  intro t
  induction t using ind with
  | _ cs ih =>
      intro w hw
      cases w with
      | nil => exact Or.inl (part_nil _)
      | cons i w =>
          obtain ⟨hi, hw⟩ := isAddr_cons.mp hw
          have hsub : subAt (.node cs) [i] = cs[i] := by rw [subAt_getElem cs hi, subAt_nil]
          rw [part_cons, hsub]
          have hmem : ∀ v ∈ cutAddrs s cs[i], i :: v ∈ cutAddrs s (.node cs) := fun v hv =>
            mem_cutAddrs_of_mem_cutAddrsF (mem_cutAddrsF_iff.mpr ⟨i, hi, v, hv, rfl⟩)
          by_cases hp : part s cs[i] w = []
          · rw [if_pos hp]
            by_cases hc : IsCut s cs[i]
            · rw [if_pos hc]
              exact Or.inr (hmem [] (nil_mem_cutAddrs hc))
            · rw [if_neg hc]
              exact Or.inl rfl
          · rw [if_neg hp]
            rcases ih cs[i] (List.getElem_mem hi) w hw with h | h
            · exact absurd h hp
            · exact Or.inr (hmem _ h)

/-- **`it:general-dilution`**, the vertices of the contraction listed by address: the
root part first, then the part roots below it in the order the tree is read. -/
def partList (s : ℕ) (T : RTree) : List (List ℕ) := [] :: rootAddrs s T

@[simp] lemma partList_eq (T : RTree) : partList s T = [] :: rootAddrs s T := rfl

/-- **The part of every vertex is listed.** -/
theorem part_mem_partList (T : RTree) {w : List ℕ} (hw : w ∈ addrList T) :
    part s T w ∈ partList s T := by
  rcases part_eq_nil_or_mem_cutAddrs T w (mem_addrList_iff.mp hw) with h | h
  · rw [partList_eq, h]
    exact List.mem_cons_self
  · rw [cutAddrs_eq] at h
    rw [partList_eq]
    split at h
    · exact h
    · exact List.mem_cons_of_mem _ h

/-- A listed address is an address of the tree topping its own part. -/
lemma isAddr_and_part_eq_of_mem_cutAddrs : ∀ (t : RTree) (x : List ℕ), x ∈ cutAddrs s t →
    IsAddr t x ∧ part s t x = x := by
  intro t
  induction t using ind with
  | _ cs ih =>
      intro x hx
      have hforest : ∀ y ∈ cutAddrsF s cs, IsAddr (.node cs) y ∧ part s (.node cs) y = y := by
        intro y hy
        obtain ⟨i, hi, v, hv, rfl⟩ := mem_cutAddrsF_iff.mp hy
        obtain ⟨hv1, hv2⟩ := ih cs[i] (List.getElem_mem hi) v hv
        refine ⟨isAddr_cons.mpr ⟨hi, hv1⟩, ?_⟩
        have hsub : subAt (.node cs) [i] = cs[i] := by rw [subAt_getElem cs hi, subAt_nil]
        rw [part_cons, hsub]
        by_cases hvn : v = []
        · subst hvn
          rw [if_pos hv2, if_pos (isCut_of_nil_mem_cutAddrs hv)]
        · rw [if_neg (by rw [hv2]; exact hvn), hv2]
      rw [cutAddrs_node] at hx
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨isAddr_nil _, part_nil _⟩
        · exact hforest _ hx'
      · exact hforest _ hx

/-- **The listed addresses are exactly the part roots**: `partList` enumerates the
vertex set `GPartVert s T` of the contracted tree. -/
theorem mem_partList_iff (T : RTree) {x : List ℕ} :
    x ∈ partList s T ↔ x ∈ addrList T ∧ part s T x = x := by
  constructor
  · intro hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨nil_mem_addrList _, part_nil _⟩
    · have h := isAddr_and_part_eq_of_mem_cutAddrs T x (by
        rw [cutAddrs_eq]
        split
        · exact List.mem_cons_of_mem _ hx'
        · exact hx')
      exact ⟨mem_addrList_iff.mpr h.1, h.2⟩
  · rintro ⟨hx, hpx⟩
    have := part_mem_partList (s := s) T hx
    rwa [hpx] at this

/-- The blocks of a forest are listed once each once its trees are. -/
lemma nodup_cutAddrsF_of : ∀ F : List RTree, (∀ c ∈ F, (cutAddrs s c).Nodup) →
    (cutAddrsF s F).Nodup
  | [], _ => by simp
  | c :: cs, hall => by
      rw [cutAddrsF_cons]
      have h1 : ((cutAddrs s c).map (fun w => 0 :: w)).Nodup :=
        (hall c (by simp)).map (fun _ _ h => by simpa using h)
      have h2 : ((cutAddrsF s cs).map (bump 1)).Nodup := by
        refine (nodup_cutAddrsF_of cs fun x hx => hall x (by simp [hx])).map_on ?_
        intro a ha b hb h
        exact bump_injective 1 (ne_nil_of_mem_cutAddrsF ha) (ne_nil_of_mem_cutAddrsF hb) h
      refine List.Nodup.append h1 h2 ?_
      intro x hx hx'
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨u, hu, hueq⟩ := List.mem_map.mp hx'
      have hne := ne_nil_of_mem_cutAddrsF hu
      cases u with
      | nil => exact absurd rfl hne
      | cons j u => simp only [bump_cons, List.cons.injEq] at hueq; omega

/-- The part roots are listed once each. -/
lemma nodup_cutAddrs (t : RTree) : (cutAddrs s t).Nodup := by
  induction t using ind with
  | _ cs ih =>
      rw [cutAddrs_node]
      have hF := nodup_cutAddrsF_of cs ih
      split
      · exact List.nodup_cons.mpr ⟨fun h => ne_nil_of_mem_cutAddrsF h rfl, hF⟩
      · exact hF

/-- **The enumeration lists each part root once.** -/
theorem nodup_partList (T : RTree) : (partList s T).Nodup := by
  rw [partList_eq]
  refine List.nodup_cons.mpr ⟨fun hc => ne_nil_of_mem_rootAddrs hc rfl, ?_⟩
  have h := nodup_cutAddrs (s := s) T
  rw [cutAddrs_eq] at h
  split at h
  · exact (List.nodup_cons.mp h).2
  · exact h

/-- The vertices of the contraction and their addresses are counted alike. -/
lemma length_cutAddrsF_of : ∀ F : List RTree,
    (∀ c ∈ F, (cutAddrs s c).length = sizeF (cutForest s c)) →
    (cutAddrsF s F).length = sizeF (cutForestF s F)
  | [], _ => by simp
  | c :: cs, h => by
      rw [cutAddrsF_cons, cutForestF_cons, List.length_append, List.length_map, List.length_map,
        sizeF_append, h c (by simp), length_cutAddrsF_of cs fun d hd => h d (by simp [hd])]

lemma length_cutAddrs (t : RTree) : (cutAddrs s t).length = sizeF (cutForest s t) := by
  induction t using ind with
  | _ cs ih =>
      have hF := length_cutAddrsF_of cs ih
      rw [cutAddrs_node, cutForest_node]
      split
      · simp only [List.length_cons, sizeF_cons, sizeF_nil, size_node, hF]
        omega
      · exact hF

lemma length_cutAddrsF (F : List RTree) : (cutAddrsF s F).length = sizeF (cutForestF s F) :=
  length_cutAddrsF_of F fun c _ => length_cutAddrs c

/-- The list of part roots is as long as the contraction has vertices. -/
lemma length_partList (T : RTree) : (partList s T).length = (gContractTree s T).size := by
  cases T with
  | node cs =>
      rw [partList_eq, rootAddrs_node, gContractTree_eq, rootForest_node, List.length_cons,
        size_node, length_cutAddrsF]
      omega

/-! ### The mark -/

/-- **`it:general-dilution`**, the mark: the part of a vertex, read as an index into
the vertices of the contraction. -/
def markOf (s : ℕ) (T : RTree) (w : List ℕ) : ℕ := (partList s T).idxOf (part s T w)

/-- The mark of a vertex names a vertex of the contraction. -/
theorem markOf_lt (T : RTree) {w : List ℕ} (hw : w ∈ addrList T) :
    markOf s T w < (gContractTree s T).size := by
  have h := List.idxOf_lt_length_of_mem (part_mem_partList (s := s) T hw)
  rwa [length_partList] at h

/-- Two vertices carry the same mark exactly when they lie in the same part. -/
theorem markOf_eq_iff (T : RTree) {v w : List ℕ} (hv : v ∈ addrList T) :
    markOf s T v = markOf s T w ↔ part s T v = part s T w :=
  List.idxOf_inj (part_mem_partList (s := s) T hv)

/-- The root part carries the mark `0`. -/
@[simp] lemma markOf_nil (T : RTree) : markOf s T [] = 0 := by
  rw [markOf, part_nil, partList_eq]
  simp [List.idxOf_cons_self]

/-- **`it:general-dilution`**, the datum counted: the contraction of `T` at scale `s`
together with the part of the vertex `e`. -/
def gContractPair (s : ℕ) (T : RTree) (e : List ℕ) : RTree × ℕ := (gContractTree s T, markOf s T e)

/-- **`it:general-dilution`**, the hypothesis of the count: the marked contraction of
a tree of at most `n` vertices is a rooted tree of at most `n/s + 1` vertices with one
of them marked. -/
theorem gContractPair_spec (hs : 1 ≤ s) {T : RTree} {n : ℕ} (hn : T.size ≤ n) {e : List ℕ}
    (he : e ∈ addrList T) :
    (gContractPair s T e).1.size ≤ n / s + 1 ∧
      (gContractPair s T e).2 < (gContractPair s T e).1.size := by
  refine ⟨?_, markOf_lt (s := s) T he⟩
  have h1 := size_gContractTree_le_div (s := s) hs T
  have h2 : T.size / s ≤ n / s := Nat.div_le_div_right hn
  exact le_trans h1 (by omega)

end RTree


/-! ### The part roots paired with the addresses of the contraction -/

variable {s : ℕ}

/-- **`it:general-dilution`**, the pairing: the part roots of `T`, as `RTree.partList`
lists them, against the addresses of `RTree.gContractTree s T`, as `RTree.addrList`
lists them.  Both recursions read the tree in the same order, so the pairing is the
graph of a bijection. -/
def gPairList (s : ℕ) (T : RTree) : List (List ℕ × List ℕ) :=
  (partList s T).zip (addrList (gContractTree s T))

/-- The same pairing for the parts topped by the maximal cut vertices of a subtree. -/
def gCutPairs (s : ℕ) (t : RTree) : List (List ℕ × List ℕ) :=
  (cutAddrs s t).zip (addrListF (cutForest s t))

/-- The same pairing for the parts topped by the maximal cut vertices of a forest. -/
def gCutPairsF (s : ℕ) (cs : List RTree) : List (List ℕ × List ℕ) :=
  (cutAddrsF s cs).zip (addrListF (cutForestF s cs))

/-- The same pairing for the parts strictly below the root of a subtree. -/
def gRootPairs (s : ℕ) (t : RTree) : List (List ℕ × List ℕ) :=
  (rootAddrs s t).zip (addrListF (rootForest s t))

/-- The root part heads the pairing. -/
lemma gPairList_eq (t : RTree) : gPairList s t = ([], []) :: gRootPairs s t := by
  rw [gPairList, partList_eq, gContractTree_eq, addrList_node, List.zip_cons_cons, gRootPairs]

@[simp] lemma gRootPairs_node (cs : List RTree) : gRootPairs s (.node cs) = gCutPairsF s cs := rfl

/-- A cut root is paired with the first child of the enclosing part. -/
lemma gCutPairs_of_isCut {t : RTree} (h : IsCut s t) :
    gCutPairs s t = (gPairList s t).map (Prod.map id (fun y => 0 :: y)) := by
  simp only [gCutPairs, gPairList]
  rw [cutForest_eq, if_pos h, cutAddrs_eq, if_pos h, addrListF_cons,
    addrListF_nil, List.map_nil, List.append_nil, partList_eq, List.zip_map_right]

/-- An uncut root passes up the parts below it unchanged. -/
lemma gCutPairs_of_not_isCut {t : RTree} (h : ¬ IsCut s t) : gCutPairs s t = gRootPairs s t := by
  simp only [gCutPairs, gRootPairs]
  rw [cutForest_eq, if_neg h, cutAddrs_eq, if_neg h]

@[simp] lemma gCutPairsF_nil : gCutPairsF s [] = [] := by
  rw [gCutPairsF, cutAddrsF_nil, List.zip_nil_left]

/-- The pairing of a forest: the first tree's pairs with the letter `0` prefixed, then
the pairs of the rest, the letters and the addresses shifted. -/
lemma gCutPairsF_cons (c : RTree) (cs : List RTree) :
    gCutPairsF s (c :: cs) =
      (gCutPairs s c).map (Prod.map (fun w => 0 :: w) id) ++
        (gCutPairsF s cs).map (Prod.map (bump 1) (bump (cutForest s c).length)) := by
  have hlen : ((cutAddrs s c).map (fun w => 0 :: w)).length
      = (addrListF (cutForest s c)).length := by
    rw [List.length_map, length_addrListF, length_cutAddrs]
  simp only [gCutPairsF, gCutPairs]
  rw [cutAddrsF_cons, cutForestF_cons, addrListF_append, List.zip_append hlen,
    List.zip_map_left, List.zip_map]

/-! ### The pairing is compatible with the part structure -/

/-- The second entry of a pair below the root is a nonempty address. -/
lemma snd_ne_nil_of_mem_gRootPairs {t : RTree} {x y : List ℕ}
    (h : (x, y) ∈ gRootPairs s t) : y ≠ [] :=
  ne_nil_of_mem_addrListF (List.of_mem_zip h).2

/-- The first entry of a pair below the root is a nonempty address. -/
lemma fst_ne_nil_of_mem_gRootPairs {t : RTree} {x y : List ℕ}
    (h : (x, y) ∈ gRootPairs s t) : x ≠ [] :=
  ne_nil_of_mem_rootAddrs (List.of_mem_zip h).1

/-- The first entry of a pair of a forest is a nonempty address. -/
lemma fst_ne_nil_of_mem_gCutPairsF {cs : List RTree} {x y : List ℕ}
    (h : (x, y) ∈ gCutPairsF s cs) : x ≠ [] :=
  ne_nil_of_mem_cutAddrsF (List.of_mem_zip h).1

/-- Only a cut subtree pairs its own root. -/
lemma isCut_of_nil_mem_gCutPairs {t : RTree} {y : List ℕ} (h : (([] : List ℕ), y) ∈ gCutPairs s t) :
    IsCut s t :=
  isCut_of_nil_mem_cutAddrs (List.of_mem_zip h).1

/-- The root of a cut subtree is the first child of the enclosing part. -/
lemma eq_of_nil_mem_gCutPairs {t : RTree} {y : List ℕ} (h : (([] : List ℕ), y) ∈ gCutPairs s t) :
    y = [0] := by
  rw [gCutPairs_of_isCut (isCut_of_nil_mem_gCutPairs h)] at h
  obtain ⟨⟨x', y'⟩, hmem, heq⟩ := List.mem_map.mp h
  simp only [Prod.map, Prod.mk.injEq, id_eq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  rw [gPairList_eq, List.mem_cons] at hmem
  rcases hmem with heq | hmem
  · rw [(Prod.mk.injEq _ _ _ _).mp heq |>.2]
  · exact absurd rfl (fst_ne_nil_of_mem_gRootPairs hmem)

/-- The pairing of a subtree is compatible with the part structure once the pairing
of its parts is: the part-parent of a pair is a pair, or else the part above is the
enclosing one. -/
lemma part_dropLast_mem_gCutPairs (s : ℕ) (t : RTree)
    (h : ∀ x y, (x, y) ∈ gPairList s t → (part s t x.dropLast, y.dropLast) ∈ gPairList s t) :
    ∀ x y, (x, y) ∈ gCutPairs s t → x ≠ [] →
      (part s t x.dropLast, y.dropLast) ∈ gCutPairs s t ∨
        (¬ IsCut s t ∧ part s t x.dropLast = [] ∧ y.dropLast = []) := by
  intro x y hxy hx
  by_cases hc : IsCut s t
  · rw [gCutPairs_of_isCut hc] at hxy ⊢
    obtain ⟨⟨x', y'⟩, hmem, heq⟩ := List.mem_map.mp hxy
    simp only [Prod.map, Prod.mk.injEq, id_eq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hy' : y' ≠ [] := by
      rw [gPairList_eq, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · exact absurd ((Prod.mk.injEq _ _ _ _).mp heq).1 hx
      · exact snd_ne_nil_of_mem_gRootPairs hmem
    refine Or.inl ?_
    rw [dropLast_cons_of_ne_nil 0 hy']
    exact List.mem_map.mpr ⟨(part s t x'.dropLast, y'.dropLast), h _ _ hmem, rfl⟩
  · rw [gCutPairs_of_not_isCut hc] at hxy ⊢
    have := h x y (by rw [gPairList_eq]; exact List.mem_cons_of_mem _ hxy)
    rw [gPairList_eq, List.mem_cons] at this
    rcases this with heq | hmem
    · exact Or.inr ⟨hc, ((Prod.mk.injEq _ _ _ _).mp heq).1, ((Prod.mk.injEq _ _ _ _).mp heq).2⟩
    · exact Or.inl hmem

/-- **The step of the recursion.**  A part of a subtree, read one letter down, has its
part-parent paired with the parent of its address. -/
lemma part_dropLast_gStep (s : ℕ) (t u : RTree) (a : ℕ) (g : List ℕ → List ℕ)
    (hg : ∀ w, (g w).dropLast = g w.dropLast) (hgnil : g [] = [])
    (hpart : ∀ w : List ℕ, part s t (a :: w) =
      if part s u w = [] then (if IsCut s u then [a] else []) else a :: part s u w)
    (hcut : ∀ x y, (x, y) ∈ gCutPairs s u → x ≠ [] →
      (part s u x.dropLast, y.dropLast) ∈ gCutPairs s u ∨
        (¬ IsCut s u ∧ part s u x.dropLast = [] ∧ y.dropLast = []))
    {z : List ℕ} {y₀ : List ℕ} (hz : (z, y₀) ∈ gCutPairs s u) :
    (part s t (a :: z).dropLast, (g y₀).dropLast) ∈
      (([], []) :: (gCutPairs s u).map (Prod.map (fun w => a :: w) g)) := by
  rcases eq_or_ne z ([] : List ℕ) with rfl | hzne
  · rw [eq_of_nil_mem_gCutPairs hz]
    have h1 : (a :: ([] : List ℕ)).dropLast = [] := rfl
    have h2 : (g [0]).dropLast = [] := by
      rw [hg, show ([0] : List ℕ).dropLast = [] from rfl, hgnil]
    rw [h1, h2, part_nil]
    exact List.mem_cons_self
  · rw [dropLast_cons_of_ne_nil a hzne, hpart, hg]
    rcases hcut z y₀ hz hzne with hmem | ⟨hnc, hq, hy⟩
    · have hqa : (if part s u z.dropLast = [] then (if IsCut s u then [a] else [])
          else a :: part s u z.dropLast) = a :: part s u z.dropLast := by
        by_cases hq : part s u z.dropLast = []
        · rw [if_pos hq, hq]
          rw [hq] at hmem
          rw [if_pos (isCut_of_nil_mem_gCutPairs hmem)]
        · rw [if_neg hq]
      rw [hqa]
      exact List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨(part s u z.dropLast, y₀.dropLast), hmem, rfl⟩)
    · rw [hq, if_pos rfl, if_neg hnc, hy, hgnil]
      exact List.mem_cons_self

/-- **The step of the recursion over a forest.**  The pairing of a forest is a map of
part trees once the pairings of its trees are: a part root below the root has its
part-parent paired with the parent of its address, or else the part above is the
root. -/
lemma part_dropLast_mem_gCutPairsF (s : ℕ) : ∀ cs : List RTree,
    (∀ c ∈ cs, ∀ x y, (x, y) ∈ gCutPairs s c → x ≠ [] →
      (part s c x.dropLast, y.dropLast) ∈ gCutPairs s c ∨
        (¬ IsCut s c ∧ part s c x.dropLast = [] ∧ y.dropLast = [])) →
    ∀ x y, (x, y) ∈ gCutPairsF s cs →
      (part s (.node cs) x.dropLast, y.dropLast) ∈ ([], []) :: gCutPairsF s cs
  | [], _, x, y, hxy => by simp at hxy
  | c :: cs, hall, x, y, hxy => by
      rw [gCutPairsF_cons, List.mem_append] at hxy
      rcases hxy with hmem | hmem
      · -- the first child: the step lemma at the letter `0`
        obtain ⟨⟨z, y₀⟩, hz, heq⟩ := List.mem_map.mp hmem
        simp only [Prod.map, Prod.mk.injEq, id_eq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hstep := part_dropLast_gStep s (.node (c :: cs)) c 0 id (fun _ => rfl) rfl
          (fun w => part_node_cons_zero c cs w) (hall c (by simp)) hz
        simp only [id_eq] at hstep
        rw [gCutPairsF_cons]
        rcases List.mem_cons.mp hstep with heq' | hmem'
        · rw [heq']; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hmem')
      · -- a later child: the pairing of the rest of the forest, shifted
        obtain ⟨⟨x', y'⟩, hx', heq⟩ := List.mem_map.mp hmem
        simp only [Prod.map, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have ih := part_dropLast_mem_gCutPairsF s cs
          (fun d hd => hall d (List.mem_cons_of_mem c hd)) x' y' hx'
        have hne := fst_ne_nil_of_mem_gCutPairsF hx'
        obtain ⟨j, z, rfl⟩ : ∃ j z, x' = j :: z := by
          cases x' with
          | nil => exact absurd rfl hne
          | cons j z => exact ⟨j, z, rfl⟩
        rw [bump_cons, dropLast_bump]
        rcases eq_or_ne z ([] : List ℕ) with rfl | hzne
        · -- the part root is a child of the root: its part-parent is the root
          have hy' : y'.dropLast = [] := by
            rcases List.mem_cons.mp ih with heq' | hmem'
            · exact ((Prod.mk.injEq _ _ _ _).mp heq').2
            · have h0 : part s (.node cs) ([j] : List ℕ).dropLast = [] := by
                rw [show ([j] : List ℕ).dropLast = [] from rfl, part_nil]
              rw [h0] at hmem'
              exact absurd rfl (fst_ne_nil_of_mem_gCutPairsF hmem')
          rw [hy', bump_nil, show ((1 + j) :: ([] : List ℕ)).dropLast = [] from rfl, part_nil]
          exact List.mem_cons_self
        · rw [dropLast_cons_of_ne_nil _ hzne, show 1 + j = j + 1 from Nat.add_comm 1 j,
            part_node_cons_succ, gCutPairsF_cons]
          rw [dropLast_cons_of_ne_nil _ hzne] at ih
          rcases List.mem_cons.mp ih with heq' | hmem'
          · obtain ⟨h1, h2⟩ := (Prod.mk.injEq _ _ _ _).mp heq'
            rw [h1, h2, bump_nil, bump_nil]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_append_right _
              (List.mem_map.mpr ⟨_, hmem', rfl⟩))

/-- **`it:general-dilution`, the pairing is a map of part trees.**  The part-parent of
a part root is paired with the parent of its address in the contraction. -/
theorem part_dropLast_mem_gPairList (s : ℕ) : ∀ (t : RTree) (x y : List ℕ),
    (x, y) ∈ gPairList s t → (part s t x.dropLast, y.dropLast) ∈ gPairList s t := by
  intro t
  induction t using ind with
  | _ cs ih =>
      intro x y hxy
      rw [gPairList_eq, gRootPairs_node] at hxy ⊢
      rcases List.mem_cons.mp hxy with heq | hmem
      · obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp heq
        simp [part_nil]
      · exact part_dropLast_mem_gCutPairsF s cs
          (fun c hc => part_dropLast_mem_gCutPairs s c (ih c hc)) x y hmem


/-! ### The pairing is a bijection -/

variable (s : ℕ) (T : RTree)

/-- **`it:general-dilution`**: the address, in the contraction, of the part topped by a
given address. -/
def gPartAddr (x : List ℕ) : List ℕ :=
  (addrList (gContractTree s T)).getD ((partList s T).idxOf x) []

/-- The part root an address of the contraction names. -/
def gAddrPart (y : List ℕ) : List ℕ :=
  (partList s T).getD ((addrList (gContractTree s T)).idxOf y) []

/-- The part roots and the addresses of the contraction are equally many. -/
lemma length_partList_eq_length_addrList : (partList s T).length = (addrList (gContractTree s T)).length := by
  rw [length_partList, length_addrList]

/-- The pairing read from the part roots. -/
lemma mem_gPairList_iff {x y : List ℕ} :
    (x, y) ∈ gPairList s T ↔ x ∈ partList s T ∧ y = gPartAddr s T x := by
  rw [gPairList]
  exact mem_zip_iff_getD [] (nodup_partList T) (length_partList_eq_length_addrList s T)

/-- The pairing read from the addresses. -/
lemma mem_gPairList_iff' {x y : List ℕ} :
    (x, y) ∈ gPairList s T ↔ y ∈ addrList (gContractTree s T) ∧ x = gAddrPart s T y := by
  rw [gPairList, mem_zip_swap]
  exact mem_zip_iff_getD [] (nodup_addrList _) (length_partList_eq_length_addrList s T).symm

variable {s T} {x x' : List ℕ}

/-- A part root is paired with its address. -/
lemma mem_gPairList (hx : x ∈ partList s T) : (x, gPartAddr s T x) ∈ gPairList s T :=
  (mem_gPairList_iff s T).mpr ⟨hx, rfl⟩

/-- The address of a part root is an address of the contraction. -/
lemma gPartAddr_mem (hx : x ∈ partList s T) : gPartAddr s T x ∈ addrList (gContractTree s T) :=
  ((mem_gPairList_iff' s T).mp (mem_gPairList hx)).1

/-- An address of the contraction names a part root. -/
lemma gAddrPart_mem {y : List ℕ} (hy : y ∈ addrList (gContractTree s T)) :
    gAddrPart s T y ∈ partList s T :=
  ((mem_gPairList_iff s T).mp ((mem_gPairList_iff' s T).mpr ⟨hy, rfl⟩)).1

/-- The two readings are inverse to each other. -/
lemma gAddrPart_gPartAddr (hx : x ∈ partList s T) : gAddrPart s T (gPartAddr s T x) = x :=
  (((mem_gPairList_iff' s T).mp (mem_gPairList hx)).2).symm

lemma gPartAddr_gAddrPart {y : List ℕ} (hy : y ∈ addrList (gContractTree s T)) :
    gPartAddr s T (gAddrPart s T y) = y :=
  (((mem_gPairList_iff s T).mp ((mem_gPairList_iff' s T).mpr ⟨hy, rfl⟩)).2).symm

/-- The part roots are named once each. -/
lemma gPartAddr_injOn (hx : x ∈ partList s T) (hx' : x' ∈ partList s T)
    (h : gPartAddr s T x = gPartAddr s T x') : x = x' := by
  rw [← gAddrPart_gPartAddr hx, ← gAddrPart_gPartAddr hx', h]

/-- The root part is named by the root. -/
@[simp] lemma gPartAddr_nil : gPartAddr s T [] = [] := by
  have : (([] : List ℕ), ([] : List ℕ)) ∈ gPairList s T := by
    rw [gPairList_eq]; exact List.mem_cons_self
  exact (((mem_gPairList_iff s T).mp this).2).symm

/-- **`it:general-dilution`, the naming is a map of part trees.**  The part-parent of
a part root is named by the parent of its name. -/
lemma gPartAddr_part_dropLast (hx : x ∈ partList s T) :
    gPartAddr s T (part s T x.dropLast) = (gPartAddr s T x).dropLast :=
  (((mem_gPairList_iff s T).mp
    (part_dropLast_mem_gPairList s T x (gPartAddr s T x) (mem_gPairList hx))).2).symm

/-- The part-parent of a part root is a part root. -/
lemma gPart_dropLast_mem_partList (hx : x ∈ partList s T) :
    part s T x.dropLast ∈ partList s T :=
  ((mem_gPairList_iff s T).mp
    (part_dropLast_mem_gPairList s T x (gPartAddr s T x) (mem_gPairList hx))).1

/-! ### The contracted tree and the rose tree are isometric -/

/-- One vertex of the contracted tree lies below another exactly when the second is
distinct from the first and has it as its part-parent. -/
lemma gPartStep_iff {p q : GPartVert s T} :
    GPartStep p q ↔ p ≠ q ∧ p.1 = part s T q.1.dropLast := by
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
    obtain ⟨u, a, hua⟩ : ∃ (u : List ℕ) (a : ℕ), q.1 = u ++ [a] := by
      rcases List.eq_nil_or_concat q.1 with h | ⟨u, a, h⟩
      · exact absurd h hq
      · exact ⟨u, a, by rw [h]; simp⟩
    refine ⟨u, a, hua, ?_⟩
    rw [hp, hua]
    simp

/-- The contracted tree is the graph of the part-parent map. -/
lemma gPartGraph_adj_iff {p q : GPartVert s T} :
    (gPartGraph s T).Adj p q ↔
      p ≠ q ∧ (p.1 = part s T q.1.dropLast ∨ q.1 = part s T p.1.dropLast) := by
  rw [gPartGraph_adj, gPartStep_iff, gPartStep_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1.symm, Or.inr h2⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1.symm, h2⟩

/-- **`it:general-dilution`**: a part root read as an address of the contraction. -/
def gToVert (p : GPartVert s T) : Vert (gContractTree s T) :=
  ⟨gPartAddr s T p.1, gPartAddr_mem ((mem_partList_iff T).mpr p.2)⟩

/-- An address of the contraction read as a part root. -/
def gOfVert (y : Vert (gContractTree s T)) : GPartVert s T :=
  ⟨gAddrPart s T y.1, (mem_partList_iff T).mp (gAddrPart_mem y.2)⟩

@[simp] lemma gToVert_val (p : GPartVert s T) : (gToVert p).1 = gPartAddr s T p.1 := rfl

@[simp] lemma gOfVert_val (y : Vert (gContractTree s T)) : (gOfVert y).1 = gAddrPart s T y.1 := rfl

lemma gOfVert_gToVert (p : GPartVert s T) : gOfVert (gToVert p) = p :=
  Subtype.ext (gAddrPart_gPartAddr ((mem_partList_iff T).mpr p.2))

lemma gToVert_gOfVert (y : Vert (gContractTree s T)) : gToVert (gOfVert y) = y :=
  Subtype.ext (gPartAddr_gAddrPart y.2)

lemma gToVert_injective : Function.Injective (gToVert (s := s) (T := T)) := by
  intro p q h
  rw [← gOfVert_gToVert p, ← gOfVert_gToVert q, h]

/-- **The reading is an isomorphism of trees**: the part-parent relation is the parent
relation on addresses. -/
lemma gToVert_adj_iff {p q : GPartVert s T} :
    (rtreeGraph (gContractTree s T)).Adj (gToVert p) (gToVert q) ↔ (gPartGraph s T).Adj p q := by
  have hp : p.1 ∈ partList s T := (mem_partList_iff T).mpr p.2
  have hq : q.1 ∈ partList s T := (mem_partList_iff T).mpr q.2
  have key : ∀ {x y : GPartVert s T}, x.1 ∈ partList s T → y.1 ∈ partList s T →
      ((gToVert x).1 = (gToVert y).1.dropLast ↔ x.1 = part s T y.1.dropLast) := by
    intro x y hx hy
    rw [gToVert_val, gToVert_val, ← gPartAddr_part_dropLast hy]
    exact ⟨fun h => gPartAddr_injOn hx (gPart_dropLast_mem_partList hy) h, fun h => by rw [h]⟩
  rw [rtreeGraph_adj, gPartGraph_adj_iff, key hp hq, key hq hp]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h1 (by rw [hc]), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h1 (gToVert_injective hc), h2⟩

/-- The reading as a graph homomorphism. -/
def gToVertHom (s : ℕ) (T : RTree) : gPartGraph s T →g rtreeGraph (gContractTree s T) :=
  ⟨gToVert, fun {_ _} h => gToVert_adj_iff.mpr h⟩

/-- The inverse reading as a graph homomorphism. -/
def gOfVertHom (s : ℕ) (T : RTree) : rtreeGraph (gContractTree s T) →g gPartGraph s T :=
  ⟨gOfVert, fun {x y} h => by
    have hxy := gToVert_adj_iff (p := gOfVert x) (q := gOfVert y)
    rw [gToVert_gOfVert, gToVert_gOfVert] at hxy
    exact hxy.mp h⟩

/-- **`it:general-dilution`, the contraction is the rose tree**: the contracted tree
`gPartGraph s T` and the rose tree `gContractTree s T` carry the same metric. -/
theorem dist_gToVert (p q : GPartVert s T) :
    (rtreeGraph (gContractTree s T)).dist (gToVert p) (gToVert q) = (gPartGraph s T).dist p q := by
  refine le_antisymm (dist_le_of_hom (gToVertHom s T) gPartGraph_connected p q) ?_
  have h := dist_le_of_hom (gOfVertHom s T) (rtreeGraph_connected _) (gToVert p) (gToVert q)
  have e1 : (gOfVertHom s T) (gToVert p) = p := gOfVert_gToVert p
  have e2 : (gOfVertHom s T) (gToVert q) = q := gOfVert_gToVert q
  rwa [e1, e2] at h

/-! ### The marked contraction -/

/-- **`it:general-dilution`**, the mark as an address: the address in the contraction
of the part root of `e`. -/
def gContractMark (s : ℕ) (T : RTree) (e : List ℕ) : List ℕ := gPartAddr s T (part s T e)

/-- The mark as an address is the marked index read in the address list. -/
lemma gContractMark_eq (e : List ℕ) :
    gContractMark s T e = (addrList (gContractPair s T e).1).getD (gContractPair s T e).2 [] := rfl

/-- The mark is an address of the contraction. -/
lemma gContractMark_mem {e : List ℕ} (he : e ∈ addrList T) :
    gContractMark s T e ∈ addrList (gContractTree s T) :=
  gPartAddr_mem (part_mem_partList T he)

/-- **`it:general-dilution`, the contraction as the counted datum**: the contracted
tree of a marked rose tree, with the part of the marked vertex, is the rose tree the
count of `dilution_count` sees, marks and metric included. -/
theorem isMarkedIsom_gToVert (s : ℕ) {T : RTree} {e : List ℕ} (he : e ∈ addrList T) :
    IsMarkedIsom (gPartSpace s T e) (gSpace (gContractTree s T) (gContractMark s T e)) gToVert where
  dist_eq a b := by
    show ((rtreeGraph (gContractTree s T)).dist (gToVert a) (gToVert b) : ℝ)
      = ((gPartGraph s T).dist a b : ℝ)
    rw [dist_gToVert]
  surj y := ⟨gOfVert y, gToVert_gOfVert y⟩
  entry := Subtype.ext (by simp only [gToVert_val]; exact gPartAddr_nil)
  exit := by
    rw [exit_gPartSpace_of_mem he, exit_gSpace_of_mem (gContractMark_mem he)]
    exact Subtype.ext rfl

/-- **`it:general-dilution`, the contraction as a rose tree**: a rose tree with a
marked address is `2s`-comparable to its contraction, a rose tree with the part of the
mark marked. -/
theorem markedQI_gContractTree (hs : 1 ≤ s) {e : List ℕ} (he : e ∈ addrList T) :
    MarkedQI (2 * s : ℝ) (gSpace T e) (gSpace (gContractTree s T) (gContractMark s T e)) :=
  (markedQI_gContract hs he).trans_isom (isMarkedIsom_gToVert s he)

/-! ### The degree of the contraction -/

/-- The parts topped by the maximal cut vertices of a forest are at most one per cut
tree and `J` per vertex of the remainder of an uncut tree. -/
lemma length_cutForestF_le {J : ℕ} : ∀ cs : List RTree,
    (∀ c ∈ cs, (cutForest s c).length ≤ if IsCut s c then 1 else J * remSize s c) →
    (cutForestF s cs).length ≤ cs.length + J * remSizeF s cs
  | [], _ => by simp
  | c :: cs, h => by
      have h1 := h c (by simp)
      have h2 := length_cutForestF_le cs fun d hd => h d (by simp [hd])
      have h3 : (if IsCut s c then 1 else J * remSize s c) ≤ 1 + J * remSize s c := by
        split <;> omega
      rw [cutForestF_cons, List.length_append, List.length_cons, remSizeF_cons, Nat.mul_add]
      omega

/-- The parts topped by the maximal cut vertices of a tree with offspring numbers in
`{0,…,J}`: one if the root is cut, and otherwise at most `J` per vertex of the
remainder, each vertex of the remainder having at most `J` children. -/
lemma length_cutForest_le {J : ℕ} : ∀ t : RTree, DegLe J t →
    (cutForest s t).length ≤ if IsCut s t then 1 else J * remSize s t := by
  intro t
  induction t using ind with
  | _ cs ih =>
      rintro ⟨hlen, hall⟩
      have hF := length_cutForestF_le cs fun c hc => ih c hc (hall c hc)
      rw [cutForest_node]
      by_cases h : IsCut s (.node cs)
      · rw [if_pos h, if_pos h]
        simp
      · rw [if_neg h, if_neg h, remSize_of_not_isCut h, rawSize_node, Nat.mul_add, Nat.mul_one]
        have := Nat.mul_le_mul_right (remSizeF s cs) hlen
        omega

/-- The children of a tree with offspring numbers in `{0,…,J}` have offspring numbers
in `{0,…,J}`. -/
lemma RTree.DegLe.children {J : ℕ} {cs : List RTree} (hdeg : DegLe J (.node cs)) :
    ∀ c ∈ cs, DegLe J c := by
  obtain ⟨-, hall⟩ := hdeg
  exact hall

/-- The root of a part with offspring numbers in `{0,…,J}` has at most `J(1 + J(s-1))`
parts immediately below it. -/
lemma degLe_node_cutForestF (hs : 1 ≤ s) {J : ℕ} {cs : List RTree} (hdeg : DegLe J (.node cs))
    (hmem : ∀ y ∈ cutForestF s cs, DegLe (J * (1 + J * (s - 1))) y) :
    DegLe (J * (1 + J * (s - 1))) (.node (cutForestF s cs)) := by
  obtain ⟨hlen, hall⟩ := hdeg
  refine ⟨?_, hmem⟩
  have h1 := length_cutForestF_le (s := s) cs fun c hc => length_cutForest_le c (hall c hc)
  have h2 : remSizeF s cs ≤ cs.length * (s - 1) := remSizeF_le hs cs
  have h3 : J * remSizeF s cs ≤ J * (J * (s - 1)) :=
    Nat.mul_le_mul_left J (h2.trans (Nat.mul_le_mul_right _ hlen))
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Every part of a tree with offspring numbers in `{0,…,J}` has, in the contraction,
offspring numbers in `{0,…,J(1+J(s-1))}`. -/
lemma degLe_of_mem_cutForest (hs : 1 ≤ s) {J : ℕ} : ∀ t : RTree, DegLe J t →
    ∀ x ∈ cutForest s t, DegLe (J * (1 + J * (s - 1))) x := by
  intro t
  induction t using ind with
  | _ cs ih =>
      intro hdeg x hx
      have hmem : ∀ y ∈ cutForestF s cs, DegLe (J * (1 + J * (s - 1))) y := by
        intro y hy
        obtain ⟨c, hc, hyc⟩ := mem_cutForestF_iff.mp hy
        exact ih c hc (hdeg.children c hc) y hyc
      rw [cutForest_node] at hx
      split at hx
      · rw [List.mem_singleton.mp hx]
        exact degLe_node_cutForestF hs hdeg hmem
      · exact hmem x hx

/-- **`it:general-dilution`, the degree of the contraction.**  A part has at most
`1 + J(s-1)` vertices, each with at most `J` children, and the parts immediately below
a part root are the children of that root in the contraction, so the contraction of a
tree with offspring numbers in `{0,…,J}` has offspring numbers in
`{0,…,J(1+J(s-1))}`. -/
theorem degLe_gContractTree (hs : 1 ≤ s) {J : ℕ} {t : RTree} (hdeg : DegLe J t) :
    DegLe (J * (1 + J * (s - 1))) (gContractTree s t) := by
  cases t with
  | node cs =>
      rw [gContractTree_eq, rootForest_node]
      refine degLe_node_cutForestF hs hdeg ?_
      intro y hy
      obtain ⟨c, hc, hyc⟩ := mem_cutForestF_iff.mp hy
      exact degLe_of_mem_cutForest hs c (hdeg.children c hc) y hyc

/-- The degree bound of the contraction, absorbed into `J²s`. -/
theorem degLe_gContractTree_mul (hs : 1 ≤ s) {J : ℕ} {t : RTree} (hdeg : DegLe J t) :
    DegLe (J * (J * s)) (gContractTree s t) := by
  refine (degLe_gContractTree hs hdeg).mono ?_
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp
  · exact Nat.mul_le_mul_left J (part_le_mul hJ hs)

/-! ### Marked rose trees with the same contraction are comparable -/

/-- **`it:general-dilution`, the step that makes the count bite.**  Two marked rose
trees whose contractions at scale `s` agree, the mark included, are
`72s³`-comparable: the projection of the first, the identification of the two
contractions, and a quasi-inverse of the projection of the second compose to
`3·2s·3(2s)²`. -/
theorem markedQI_of_gContractPair_eq (hs : 1 ≤ s) {T T' : RTree} {e e' : List ℕ}
    (he : e ∈ addrList T) (he' : e' ∈ addrList T')
    (h : gContractPair s T e = gContractPair s T' e') :
    MarkedQI (72 * (s : ℝ) ^ 3) (gSpace T e) (gSpace T' e') := by
  have hsr : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
  have hT : gContractTree s T = gContractTree s T' := congrArg Prod.fst h
  have hm : gContractMark s T e = gContractMark s T' e' := by
    rw [gContractMark_eq, gContractMark_eq, h]
  have h1 := markedQI_gContractTree hs he
  have h2 := markedQI_gContractTree hs he'
  rw [hT, hm] at h1
  have h3 : MarkedQI (3 * (2 * (s : ℝ)) ^ 2)
      (gSpace (gContractTree s T') (gContractMark s T' e')) (gSpace T' e') := markedQI_symm hs1 h2
  have h4 : (1 : ℝ) ≤ 3 * (2 * (s : ℝ)) ^ 2 := by nlinarith
  have h5 := markedQI_comp hs1 h4 h1 h3
  have e : 3 * (2 * (s : ℝ)) * (3 * (2 * (s : ℝ)) ^ 2) = 72 * (s : ℝ) ^ 3 := by ring
  rwa [e] at h5

/-- **`it:general-dilution`**: the contraction of the realisation of a shape, marked
at the part of the exit. -/
def gShapeContractPair (s : ℕ) (σ : GShape) : RTree × ℕ :=
  gContractPair s σ.realise σ.exitAddr

/-- **`it:general-dilution`**, the hypothesis of the count at a shape. -/
theorem gShapeContractPair_spec (hs : 1 ≤ s) {σ : GShape} {n : ℕ} (hn : σ.size ≤ n) :
    (gShapeContractPair s σ).1.size ≤ n / s + 1 ∧
      (gShapeContractPair s σ).2 < (gShapeContractPair s σ).1.size :=
  gContractPair_spec hs hn σ.exitAddr_mem_addrList

/-- **`it:general-dilution`**: two shapes with the same marked contraction at scale
`s` are `72s³`-comparable. -/
theorem markedQI_of_gShapeContractPair_eq (hs : 1 ≤ s) {σ τ : GShape}
    (h : gShapeContractPair s σ = gShapeContractPair s τ) :
    MarkedQI (72 * (s : ℝ) ^ 3) (gShapeSpace σ) (gShapeSpace τ) :=
  markedQI_of_gContractPair_eq hs σ.exitAddr_mem_addrList τ.exitAddr_mem_addrList h

/-- **`it:general-dilution`**: a family of marked contractions of shapes of at most
`n` vertices, taken at scale `s`, has at most `e^{3(n/s+1)}` members. -/
theorem gDilution_count_shape (hs : 1 ≤ s) (n : ℕ) (F : Finset (RTree × ℕ))
    (hF : ∀ p ∈ F, ∃ σ : GShape, σ.size ≤ n ∧ p = gShapeContractPair s σ) :
    (F.card : ℝ) ≤ Real.exp (3 * ((n / s + 1 : ℕ) : ℝ)) := by
  refine RTree.dilution_count F (n / s + 1) ?_
  intro p hp
  obtain ⟨σ, hσ, rfl⟩ := hF p hp
  exact gShapeContractPair_spec hs hσ

/-! ### The contraction at scale one -/

namespace RTree

/-- At scale one every vertex is cut, so every part is a single vertex. -/
lemma isCut_one (t : RTree) : IsCut 1 t := one_le_rawSize t

/-- At scale one every address tops its own part. -/
lemma part_one (T : RTree) : ∀ w : List ℕ, part 1 T w = w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u a _ => exact part_of_isCut (RTree.isCut_one _)

/-- At scale one the forest of parts of a forest is the forest itself. -/
lemma cutForestF_one_of : ∀ cs : List RTree, (∀ c ∈ cs, gContractTree 1 c = c) →
    cutForestF 1 cs = cs
  | [], _ => by simp
  | c :: cs, h => by
      rw [cutForestF_cons, cutForest_eq, if_pos (RTree.isCut_one c), h c (by simp),
        cutForestF_one_of cs fun d hd => h d (by simp [hd])]
      rfl

/-- At scale one the contraction is the tree itself. -/
lemma gContractTree_one (t : RTree) : gContractTree 1 t = t := by
  induction t using ind with
  | _ cs ih => rw [gContractTree_eq, rootForest_node, cutForestF_one_of cs ih]

end RTree

/-- A shape is determined by its realisation together with its exit. -/
lemma realiseAux_gExitAddr_inj : ∀ (L L' : List (List RTree)), L ≠ [] → L' ≠ [] →
    GShape.realiseAux L = GShape.realiseAux L' → gExitAddr L = gExitAddr L' → L = L'
  | [], _, h, _, _, _ => absurd rfl h
  | _ :: _, [], _, h, _, _ => absurd rfl h
  | [β], [β'], _, _, hr, _ => by
      have : β = β' := by simpa [GShape.realiseAux] using hr
      rw [this]
  | [_], _ :: _ :: _, _, _, _, he => by simp [gExitAddr_cons₂] at he
  | _ :: _ :: _, [_], _, _, _, he => by simp [gExitAddr_cons₂] at he
  | β :: r :: rest, β' :: r' :: rest', _, _, hr, he => by
      rw [show GShape.realiseAux (β :: r :: rest)
          = .node (β ++ [GShape.realiseAux (r :: rest)]) from rfl,
        show GShape.realiseAux (β' :: r' :: rest')
          = .node (β' ++ [GShape.realiseAux (r' :: rest')]) from rfl, RTree.node.injEq] at hr
      rw [gExitAddr_cons₂, gExitAddr_cons₂, List.cons.injEq] at he
      obtain ⟨hlen, he'⟩ := he
      obtain ⟨hβ, hX⟩ := List.append_inj hr hlen
      have hX' : GShape.realiseAux (r :: rest) = GShape.realiseAux (r' :: rest') := by
        simpa using hX
      rw [hβ, realiseAux_gExitAddr_inj (r :: rest) (r' :: rest') (by simp) (by simp) hX' he']

/-- A shape is its realisation with its exit. -/
lemma GShape.eq_of_realise_exitAddr {σ τ : GShape} (hr : σ.realise = τ.realise)
    (he : σ.exitAddr = τ.exitAddr) : σ = τ :=
  GShape.eq_of_decs (realiseAux_gExitAddr_inj σ.decs τ.decs σ.decs_ne_nil τ.decs_ne_nil hr he)

/-- At scale one the marked contraction determines the shape: the contraction is the
realisation and the mark is the exit. -/
lemma gShapeContractPair_one_injective : Function.Injective (gShapeContractPair 1) := by
  intro σ τ h
  have hT : σ.realise = τ.realise := by
    have := congrArg Prod.fst h
    rwa [gShapeContractPair, gShapeContractPair, gContractPair, gContractPair,
      gContractTree_one, gContractTree_one] at this
  have hm : markOf 1 σ.realise σ.exitAddr = markOf 1 σ.realise τ.exitAddr := by
    have := congrArg Prod.snd h
    rwa [gShapeContractPair, gShapeContractPair, gContractPair, gContractPair, ← hT] at this
  rw [markOf_eq_iff σ.realise σ.exitAddr_mem_addrList, part_one, part_one] at hm
  exact GShape.eq_of_realise_exitAddr hT hm

/-! ### Entropy dilution -/

/-- The count of `gDilution_count_shape` over a family of shapes whose contractions at
scale `s` are pairwise distinct. -/
lemma card_le_of_gContractPair_injOn {s n : ℕ} (hs : 1 ≤ s) (F : Finset GShape)
    (hsize : ∀ σ ∈ F, σ.size ≤ n)
    (hinj : ∀ σ ∈ F, ∀ τ ∈ F,
      gShapeContractPair s σ = gShapeContractPair s τ → σ = τ) :
    (F.card : ℝ) ≤ Real.exp (3 * ((n / s + 1 : ℕ) : ℝ)) := by
  classical
  have himg : (F.image (gShapeContractPair s)).card = F.card :=
    Finset.card_image_of_injOn fun σ hσ τ hτ h => hinj σ hσ τ hτ h
  rw [← himg]
  refine gDilution_count_shape hs n _ ?_
  intro p hp
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨σ, hsize σ hσ, rfl⟩

/-- **`thm:dilution` at general arity, entropy dilution**, in the form the net uses: a
family of shapes of size at most `n`, no two of which admit `D`-marked
quasi-isometries in both directions, has at most `exp (27 (n D^{-1/3} + 1))`
members. -/
theorem gDilution_of_not_both {D : ℕ} (hD : 2 ≤ D) (n : ℕ) (F : Finset GShape)
    (hsize : ∀ σ ∈ F, σ.size ≤ n)
    (hsep : ∀ σ ∈ F, ∀ τ ∈ F, σ ≠ τ →
      ¬ (MarkedQI (D : ℝ) (gShapeSpace σ) (gShapeSpace τ) ∧
        MarkedQI (D : ℝ) (gShapeSpace τ) (gShapeSpace σ))) :
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
        gShapeContractPair s σ = gShapeContractPair s τ → σ = τ := by
      intro σ hσ τ hτ h
      by_contra hne
      refine hsep σ hσ τ hτ hne ⟨?_, ?_⟩ <;>
        refine MarkedQI.mono (by positivity) ?_
          (markedQI_of_gShapeContractPair_eq hs1 (by first | exact h | exact h.symm)) <;>
        · have hcast : ((72 * s ^ 3 : ℕ) : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast hcube
          push_cast at hcast
          linarith
    have hcount := card_le_of_gContractPair_injOn hs1 F hsize hinj
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
        gShapeContractPair 1 σ = gShapeContractPair 1 τ → σ = τ :=
      fun _ _ _ _ h => gShapeContractPair_one_injective h
    have hcount := card_le_of_gContractPair_injOn le_rfl F hsize hinj
    refine hcount.trans (Real.exp_le_exp.mpr ?_)
    have hone : (1 : ℝ) ≤ 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) := one_le_nine_rpow hD0 hsmall
    have hcast : ((n / 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      rw [Nat.div_one]; push_cast; ring
    rw [hcast]
    nlinarith

/-- **`thm:dilution` at general arity, entropy dilution.**  A family of shapes of size
at most `n`, no two of which admit a `D`-marked quasi-isometry, has at most
`exp (27 (n D^{-1/3} + 1))` members: the greedy cut at scale
`s = ⌊(D/72)^{1/3}⌋` sends the family injectively into the marked contractions of
at most `n/s + 1` vertices, which `dilution_count` counts.  The arity enters
nowhere: the contraction is a `2s`-marked quasi-isometry at every arity. -/
theorem gDilution {D : ℕ} (hD : 2 ≤ D) (n : ℕ) (F : Finset GShape)
    (hsize : ∀ σ ∈ F, σ.size ≤ n)
    (hsep : ∀ σ ∈ F, ∀ τ ∈ F, σ ≠ τ →
      ¬ MarkedQI (D : ℝ) (gShapeSpace σ) (gShapeSpace τ)) :
    (F.card : ℝ) ≤ Real.exp (27 * ((n : ℝ) * (D : ℝ) ^ (-(1 : ℝ) / 3) + 1)) :=
  gDilution_of_not_both hD n F hsize fun σ hσ τ hτ hne h => hsep σ hσ τ hτ hne h.1

/-- **`thm:dilution` at general arity, the representatives.**  At most
`exp (27 (n D^{-1/3}+1))` members of the net `ℛ_D` over `𝒮` carry a shape of size at
most `n`. -/
theorem gDilution_netMem {D : ℕ} (hD : 2 ≤ D) (n : ℕ) (F : Finset ℕ)
    (hnet : ∀ a ∈ F, netMem gShapeFamily (D : ℝ) a)
    (hsize : ∀ a ∈ F, (gShapeEnum a).size ≤ n) :
    (F.card : ℝ) ≤ Real.exp (27 * ((n : ℝ) * (D : ℝ) ^ (-(1 : ℝ) / 3) + 1)) := by
  classical
  have hcard : (F.image gShapeEnum).card = F.card :=
    Finset.card_image_of_injective F gShapeEnum_injective
  rw [← hcard]
  refine gDilution_of_not_both hD n _ ?_ ?_
  · intro σ hσ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hσ
    exact hsize a ha
  · intro σ hσ τ hτ hne hboth
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hτ
    have hab : a ≠ b := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact (netMem_iff gShapeFamily (D : ℝ) b).mp (hnet b hb) a hlt (hnet a ha) hboth.2
    · exact (netMem_iff gShapeFamily (D : ℝ) a).mp (hnet a ha) b hlt (hnet b hb) hboth.1

end ChainClasses
