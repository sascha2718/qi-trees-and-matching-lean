import Mathlib.Tactic
import ChainClasses.Shape.Dilution
import ChainClasses.Shape.ShapeMetric
import ChainClasses.Chain.WordGraph

/-!
`thm:dilution`, the geometric step: contracting the realisation of a shape
along the greedy cut is a `2s`-marked quasi-isometry onto a rooted tree with a
marked vertex.

The cut of `Dilution.lean` is read at the level of addresses.  A vertex is
*cut* when the remainder accumulated below it reaches `s`, and the part of a
vertex is topped by the nearest cut ancestor-or-self, the root if there is
none.  Three facts drive everything: the part root is an ancestor
(`part_prefix`), a vertex sits at most `s-1` below its part root
(`length_sub_length_part_le`), and a step down the tree either stays in the
part or opens a part at that very vertex (`part_concat`).

The contracted tree is the set of part roots with the part-parent adjacency,
carried by `partGraph` as a `SimpleGraph` and by `partSpace` as a marked metric
space.  The two bounds then read off the ambient metric: a walk in the
realisation projects to a walk of no greater length, and an edge of the
contraction spans at most `s` ambient edges.

* `Tri.rawSize`, `Tri.IsCut`: the accumulated remainder and the cut rule,
  matching `Tri.remSize` of `Dilution.lean`.
* `Tri.part`, `Tri.IsPartRoot`: the top of a part.
* `partGraph`, `partSpace`: the contracted tree and its marked metric space.
* `markedQI_contract`: the contraction is a `2s`-marked quasi-isometry.
-/

namespace ChainClasses

open SimpleGraph
open Shape (realiseAux)

namespace Tri

variable {s : ℕ}

/-! ### The cut rule at the level of addresses -/

/-- The remainder accumulated at a vertex before the cut rule is applied: the
vertex together with the remainders passed up by its children. -/
def rawSize (s : ℕ) : Tri → ℕ
  | leaf => 1
  | one t => 1 + remSize s t
  | two l r => 1 + remSize s l + remSize s r

/-- A vertex is cut when the remainder it accumulates reaches `s`. -/
def IsCut (s : ℕ) (t : Tri) : Prop := s ≤ rawSize s t

instance (s : ℕ) (t : Tri) : Decidable (IsCut s t) := Nat.decLe _ _

/-- The accumulated remainder counts the vertex itself. -/
lemma one_le_rawSize (t : Tri) : 1 ≤ rawSize s t := by
  cases t <;> (simp only [rawSize]; omega)

/-- The cut rule, as `Dilution.lean` states it. -/
lemma remSize_eq (t : Tri) : remSize s t = if IsCut s t then 0 else rawSize s t := by
  cases t <;> rfl

/-- An uncut vertex passes up everything it has accumulated. -/
lemma remSize_of_not_isCut {t : Tri} (h : ¬ IsCut s t) : remSize s t = rawSize s t := by
  rw [remSize_eq, ite_eq_right h]

/-- The remainder of an uncut vertex is below `s`. -/
lemma rawSize_lt_of_not_isCut {t : Tri} (h : ¬ IsCut s t) : rawSize s t < s :=
  Nat.not_le.mp h

/-! ### Subtrees -/

/-- The subtree at an address, a single vertex off the address set. -/
def subAt : Tri → Word → Tri
  | t, [] => t
  | one t, false :: w => subAt t w
  | one _, true :: _ => leaf
  | two l _, false :: w => subAt l w
  | two _ r, true :: w => subAt r w
  | leaf, _ :: _ => leaf

@[simp] lemma subAt_nil (t : Tri) : subAt t [] = t := by cases t <;> rfl

@[simp] lemma subAt_leaf (w : Word) : subAt leaf w = leaf := by
  cases w with
  | nil => rfl
  | cons a w => cases a <;> rfl

@[simp] lemma subAt_one_false (t : Tri) (w : Word) : subAt (one t) (false :: w) = subAt t w := rfl

@[simp] lemma subAt_one_true (t : Tri) (w : Word) : subAt (one t) (true :: w) = leaf := rfl

@[simp] lemma subAt_two_false (l r : Tri) (w : Word) :
    subAt (two l r) (false :: w) = subAt l w := rfl

@[simp] lemma subAt_two_true (l r : Tri) (w : Word) :
    subAt (two l r) (true :: w) = subAt r w := rfl

/-- Reading an address in two steps lands in the subtree. -/
lemma isAddr_subAt : ∀ (t : Tri) (u v : Word), t.IsAddr (u ++ v) → (subAt t u).IsAddr v := by
  intro t u
  induction u generalizing t with
  | nil => intro v h; simpa using h
  | cons a u ih =>
      intro v h
      cases t with
      | leaf => exact absurd h (Tri.isAddr_leaf_cons a (u ++ v))
      | one t =>
          cases a with
          | true => exact absurd h (Tri.isAddr_one_true t (u ++ v))
          | false => exact ih t v h
      | two l r =>
          cases a with
          | false => exact ih l v h
          | true => exact ih r v h

/-- Reading an address in two steps. -/
lemma subAt_append : ∀ (t : Tri) (u v : Word), subAt t (u ++ v) = subAt (subAt t u) v := by
  intro t u
  induction u generalizing t with
  | nil => simp
  | cons a u ih =>
      intro v
      cases t with
      | leaf => cases a <;> simp
      | one t => cases a <;> simp [ih]
      | two l r => cases a <;> simp [ih]

/-! ### The part of a vertex -/

/-- The top of the part containing an address, computed from the reversed
address: the nearest cut ancestor-or-self, the root if there is none. -/
def partRev (s : ℕ) (T : Tri) : Word → Word
  | [] => []
  | a :: r => if IsCut s (subAt T (r.reverse ++ [a])) then r.reverse ++ [a] else partRev s T r

/-- The top of the part containing an address. -/
def part (s : ℕ) (T : Tri) (w : Word) : Word := partRev s T w.reverse

@[simp] lemma part_nil (T : Tri) : part s T [] = [] := rfl

/-- The defining recursion: a vertex tops its own part when it is cut, and
otherwise belongs to the part of its parent. -/
lemma part_concat (T : Tri) (u : Word) (a : Bool) :
    part s T (u ++ [a]) = if IsCut s (subAt T (u ++ [a])) then u ++ [a] else part s T u := by
  simp only [part, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, partRev, List.reverse_reverse]

lemma part_of_isCut {T : Tri} {u : Word} {a : Bool} (h : IsCut s (subAt T (u ++ [a]))) :
    part s T (u ++ [a]) = u ++ [a] := by rw [part_concat, ite_eq_left h]

lemma part_of_not_isCut {T : Tri} {u : Word} {a : Bool} (h : ¬ IsCut s (subAt T (u ++ [a]))) :
    part s T (u ++ [a]) = part s T u := by rw [part_concat, ite_eq_right h]

/-- The part root is an ancestor. -/
lemma part_prefix (T : Tri) : ∀ w : Word, part s T w <+: w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u a ih =>
      rw [part_concat]
      split
      · exact List.prefix_refl _
      · exact ih.trans (List.prefix_append u [a])

lemma length_part_le (T : Tri) (w : Word) : (part s T w).length ≤ w.length :=
  (part_prefix T w).length_le

/-- **The step rule.**  Moving one edge down either stays inside the part or
opens a part at that vertex. -/
lemma part_append_singleton (T : Tri) (u : Word) (a : Bool) :
    part s T (u ++ [a]) = u ++ [a] ∨ part s T (u ++ [a]) = part s T u := by
  rw [part_concat]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Below the part root nothing is cut. -/
lemma not_isCut_of_lt {T : Tri} : ∀ {w p : Word}, p <+: w → (part s T w).length < p.length →
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
          exact prefix_of_prefix_of_length_le hp (List.prefix_append u [a]) hlen
        refine ih hpu ?_
        rcases part_append_singleton (s := s) T u a with h | h
        · rw [h] at hlt
          have := hpu.length_le
          simp only [List.length_append, List.length_cons, List.length_nil] at hlt
          omega
        · rwa [h] at hlt

/-! ### The depth of a part -/

/-- **The chain bound.**  If no vertex from the root down to `w` is cut, the
depth of `w` plus the remainder it passes up is at most what the root
accumulates: each step down consumes at least one vertex of the remainder. -/
lemma chain_bound : ∀ (t : Tri) (w : Word), t.IsAddr w →
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
  | cons a u ih =>
      intro haddr h
      cases t with
      | leaf => exact absurd haddr (Tri.isAddr_leaf_cons a u)
      | one t =>
          cases a with
          | true => exact absurd haddr (Tri.isAddr_one_true t u)
          | false =>
              have hchild : ¬ IsCut s t := by
                have := h [false] ⟨u, rfl⟩
                simpa using this
              have hih := ih t haddr fun p hp => by
                have := h (false :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
                simpa using this
              have hl : remSize s t = rawSize s t := remSize_of_not_isCut hchild
              simp only [subAt_one_false, rawSize, List.length_cons]
              omega
      | two l r =>
          cases a with
          | false =>
              have hchild : ¬ IsCut s l := by
                have := h [false] ⟨u, rfl⟩
                simpa using this
              have hih := ih l haddr fun p hp => by
                have := h (false :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
                simpa using this
              have hl : remSize s l = rawSize s l := remSize_of_not_isCut hchild
              simp only [subAt_two_false, rawSize, List.length_cons]
              omega
          | true =>
              have hchild : ¬ IsCut s r := by
                have := h [true] ⟨u, rfl⟩
                simpa using this
              have hih := ih r haddr fun p hp => by
                have := h (true :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
                simpa using this
              have hr : remSize s r = rawSize s r := remSize_of_not_isCut hchild
              simp only [subAt_two_true, rawSize, List.length_cons]
              omega

/-- **A vertex sits at most `s-1` below its part root.**  The vertices strictly
between are uncut, and each step down consumes one vertex of the remainder
accumulated just below the part root, which is less than `s`. -/
theorem length_sub_length_part_le (T : Tri) {w : Word} (hw : T.IsAddr w) :
    w.length - (part s T w).length ≤ s - 1 := by
  obtain ⟨p, hpw⟩ : ∃ p, part s T w = p := ⟨_, rfl⟩
  have hpref : p <+: w := hpw ▸ part_prefix T w
  rw [hpw]
  rcases eq_or_ne p w with rfl | hne
  · omega
  obtain ⟨v, hv⟩ := hpref
  obtain ⟨b, v', rfl⟩ : ∃ (b : Bool) (v' : Word), v = b :: v' := by
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
      exact List.prefix_self_append_iff.mpr hq
    · rw [hpw]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have haddr : (subAt T (p ++ [b])).IsAddr v' :=
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
lemma part_idem (T : Tri) : ∀ w : Word, part s T (part s T w) = part s T w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u a ih =>
      rw [part_concat]
      split
      · next h => rw [part_of_isCut h]
      · exact ih

end Tri

/-! ### The contracted tree -/

open Tri

variable (s : ℕ) (T : Tri)

/-- A vertex of the contracted tree: an address topping its own part. -/
@[implicit_reducible]
def PartVert : Type := {w : Word // T.IsAddr w ∧ part s T w = w}

variable {s T}

/-- The part of an address, as a vertex of the contracted tree. -/
def contract {w : Word} (hw : T.IsAddr w) : PartVert s T :=
  ⟨part s T w, T.isAddr_of_prefix (part_prefix T w) hw, part_idem T w⟩

@[simp] lemma contract_val {w : Word} (hw : T.IsAddr w) :
    (contract (s := s) hw).1 = part s T w := rfl

/-- Every part root is its own contraction. -/
lemma contract_self (p : PartVert s T) : contract (s := s) p.2.1 = p :=
  Subtype.ext p.2.2

/-- One vertex of the contracted tree lies below another: the second is a
child in the ambient tree whose part is topped by the first. -/
def PartStep (p q : PartVert s T) : Prop :=
  ∃ (u : Word) (a : Bool), q.1 = u ++ [a] ∧ p.1 = part s T u

variable (s T)

/-- **The contracted tree**: the part roots, joined when one is the part of the
parent of the other. -/
def partGraph : SimpleGraph (PartVert s T) where
  Adj p q := PartStep p q ∨ PartStep q p
  symm := ⟨fun {_ _} h => h.symm⟩
  loopless := ⟨fun {p} h => by
    have hkey : ¬ PartStep p p := by
      rintro ⟨u, a, h1, h2⟩
      have hlen := length_part_le (s := s) T u
      rw [← h2] at hlen
      rw [h1] at hlen
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    rcases h with h | h
    · exact hkey h
    · exact hkey h⟩

variable {s T}

@[simp] lemma partGraph_adj {p q : PartVert s T} :
    (partGraph s T).Adj p q ↔ PartStep p q ∨ PartStep q p := Iff.rfl

/-- The root part. -/
def rootPart : PartVert s T := ⟨[], T.isAddr_nil, part_nil T⟩

/-- Climbing one step: the part of the parent is adjacent to the part below. -/
lemma adj_contract_dropLast {p : PartVert s T} {u : Word} {a : Bool} (hp : p.1 = u ++ [a])
    (hu : T.IsAddr u) : (partGraph s T).Adj (contract (s := s) hu) p :=
  Or.inl ⟨u, a, hp, rfl⟩

/-- **The contracted tree is connected**: every part root climbs to the root
part. -/
theorem partGraph_connected : (partGraph s T).Connected := by
  have key : ∀ (n : ℕ) (p : PartVert s T), p.1.length ≤ n →
      (partGraph s T).Reachable (rootPart (s := s) (T := T)) p := by
    intro n
    induction n with
    | zero =>
        intro p hp
        have : p.1 = [] := List.length_eq_zero_iff.mp (by omega)
        exact (Subtype.ext this : p = rootPart).symm ▸ Reachable.refl _
    | succ n ih =>
        intro p hp
        rcases List.eq_nil_or_concat p.1 with h | ⟨u, a, hua⟩
        · exact (Subtype.ext h : p = rootPart).symm ▸ Reachable.refl _
        · have hua' : p.1 = u ++ [a] := by rw [hua]; simp
          have hu : T.IsAddr u := by
            refine T.isAddr_of_prefix ?_ p.2.1
            rw [hua']
            exact List.prefix_append u [a]
          have hlen : (contract (s := s) hu).1.length ≤ n := by
            have h1 := length_part_le (s := s) T u
            have h2 : p.1.length = u.length + 1 := by
              rw [hua']
              simp
            simp only [contract_val]
            omega
          exact (ih _ hlen).trans (Adj.reachable (adj_contract_dropLast hua' hu))
  have : Nonempty (PartVert s T) := ⟨rootPart⟩
  exact ⟨fun p q => (key p.1.length p le_rfl).symm.trans (key q.1.length q le_rfl)⟩

/-- The metric of the contracted tree. -/
noncomputable instance instMetricSpacePartVert : MetricSpace (PartVert s T) where
  dist p q := ((partGraph s T).dist p q : ℝ)
  dist_self p := by simp
  dist_comm p q := by simp only [SimpleGraph.dist_comm]
  dist_triangle p q r := by
    have := (partGraph_connected (s := s) (T := T)).dist_triangle (u := p) (v := q) (w := r)
    exact_mod_cast this
  eq_of_dist_eq_zero {p q} h := by
    refine (partGraph_connected (s := s) (T := T)).dist_eq_zero_iff.mp ?_
    exact_mod_cast h

@[simp] lemma dist_partVert (p q : PartVert s T) :
    dist p q = ((partGraph s T).dist p q : ℝ) := rfl

/-! ### The two bounds -/

/-- The address set of a tree is prefix-closed. -/
lemma prefixClosed_isAddr (T : Tri) : PrefixClosed T.IsAddr :=
  fun _ _ hp hw => T.isAddr_of_prefix hp hw

/-- One ambient edge moves the part by at most one edge of the contraction. -/
lemma dist_contract_adj {x y : {w : Word // T.IsAddr w}} (h : (wordGraph T.IsAddr).Adj x y) :
    (partGraph s T).dist (contract (s := s) x.2) (contract (s := s) y.2) ≤ 1 := by
  have key : ∀ (x y : {w : Word // T.IsAddr w}) (b : Bool), y.1 = x.1 ++ [b] →
      (partGraph s T).dist (contract (s := s) x.2) (contract (s := s) y.2) ≤ 1 := by
    intro x y b hxy
    rcases part_append_singleton (s := s) T x.1 b with hcut | hsame
    · rcases eq_or_ne (contract (s := s) x.2) (contract (s := s) y.2) with heq | hne
      · rw [heq]
        simp
      · have hadj : (partGraph s T).Adj (contract (s := s) x.2) (contract (s := s) y.2) :=
          Or.inl ⟨x.1, b, by rw [contract_val, hxy]; exact hcut, rfl⟩
        exact SimpleGraph.dist_le (Walk.cons hadj Walk.nil)
    · have : contract (s := s) x.2 = contract (s := s) y.2 := by
        refine Subtype.ext ?_
        simp only [contract_val, hxy, hsame]
      rw [this]
      simp
  rcases treeDist_eq_one_iff.mp h with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact key x y b hb
  · rw [SimpleGraph.dist_comm]
    exact key y x b hb

/-- The contraction of a walk is a walk of no greater length. -/
lemma dist_contract_le_walk {x y : {w : Word // T.IsAddr w}}
    (p : (wordGraph T.IsAddr).Walk x y) :
    (partGraph s T).dist (contract (s := s) x.2) (contract (s := s) y.2) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab _ ih =>
      have h1 := dist_contract_adj (s := s) hab
      have h2 := (partGraph_connected (s := s) (T := T)).dist_triangle
        (u := contract (s := s) a.2) (v := contract (s := s) b.2) (w := contract (s := s) c.2)
      simp only [Walk.length_cons]
      omega

/-- **The upper bound**: the contraction does not increase distances. -/
theorem dist_contract_le (x y : {w : Word // T.IsAddr w}) :
    (partGraph s T).dist (contract (s := s) x.2) (contract (s := s) y.2)
      ≤ treeDist x.1 y.1 := by
  have hconn := wordGraph_connected (prefixClosed_isAddr T) ⟨x⟩
  obtain ⟨p, hp⟩ := (hconn x y).exists_walk_length_eq_dist
  have hle := dist_contract_le_walk (s := s) p
  rw [hp, wordGraph_dist (prefixClosed_isAddr T)] at hle
  exact hle

/-- One edge of the contraction spans at most `s` ambient edges: the parent of
the lower part root lies in the upper part, at most `s-1` below its top. -/
lemma treeDist_le_of_adj (hs : 1 ≤ s) {p q : PartVert s T} (h : (partGraph s T).Adj p q) :
    treeDist p.1 q.1 ≤ s := by
  have key : ∀ {p q : PartVert s T}, PartStep p q → treeDist p.1 q.1 ≤ s := by
    rintro p q ⟨u, a, h1, h2⟩
    have hu : T.IsAddr u := by
      refine T.isAddr_of_prefix ?_ q.2.1
      rw [h1]
      exact List.prefix_append u [a]
    have hpref : p.1 <+: q.1 := by
      rw [h1, h2]
      exact (part_prefix T u).trans (List.prefix_append u [a])
    rw [treeDist_of_prefix hpref]
    have hd := length_sub_length_part_le (s := s) T hu
    have h3 : q.1.length = u.length + 1 := by rw [h1]; simp
    have h4 : p.1.length = (part s T u).length := by rw [h2]
    have h5 := length_part_le (s := s) T u
    omega
  rcases h with h | h
  · exact key h
  · rw [treeDist_comm]
    exact key h

/-- Lifting a walk of the contraction to the realisation. -/
lemma treeDist_le_of_partWalk (hs : 1 ≤ s) {p q : PartVert s T} (w : (partGraph s T).Walk p q) :
    treeDist p.1 q.1 ≤ s * w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab _ ih =>
      have h1 := treeDist_le_of_adj (s := s) hs hab
      have h2 := treeDist_triangle a.1 b.1 c.1
      simp only [Walk.length_cons, Nat.mul_add, Nat.mul_one]
      omega

lemma treeDist_le_dist_partVert (hs : 1 ≤ s) (p q : PartVert s T) :
    treeDist p.1 q.1 ≤ s * (partGraph s T).dist p q := by
  obtain ⟨w, hw⟩ := ((partGraph_connected (s := s) (T := T)) p q).exists_walk_length_eq_dist
  have hle := treeDist_le_of_partWalk (s := s) hs w
  rwa [hw] at hle

/-- **The lower bound**: a path of parts lifts, at most `s` ambient edges per
part edge and at most `s-1` at each end. -/
theorem treeDist_le_contract (hs : 1 ≤ s) (x y : {w : Word // T.IsAddr w}) :
    treeDist x.1 y.1
      ≤ s * (partGraph s T).dist (contract (s := s) x.2) (contract (s := s) y.2)
        + 2 * (s - 1) := by
  have hx : treeDist (part s T x.1) x.1 ≤ s - 1 := by
    rw [treeDist_of_prefix (part_prefix T x.1)]
    exact length_sub_length_part_le T x.2
  have hy : treeDist (part s T y.1) y.1 ≤ s - 1 := by
    rw [treeDist_of_prefix (part_prefix T y.1)]
    exact length_sub_length_part_le T y.2
  have hmid := treeDist_le_dist_partVert hs (contract (s := s) x.2) (contract (s := s) y.2)
  rw [contract_val, contract_val] at hmid
  have t1 := treeDist_triangle x.1 (part s T x.1) y.1
  have t2 := treeDist_triangle (part s T x.1) (part s T y.1) y.1
  have hcx : treeDist x.1 (part s T x.1) = treeDist (part s T x.1) x.1 := treeDist_comm _ _
  omega

/-! ### The contraction as a marked quasi-isometry -/

/-- The contracted tree as a marked metric space: the root part is the entry
and the part of the exit is the mark. -/
@[implicit_reducible]
noncomputable def partSpace (s : ℕ) {T : Tri} {e : Word} (he : T.IsAddr e) : MarkedSpace where
  carrier := PartVert s T
  entry := rootPart
  exit := contract (s := s) he

/-- **`thm:dilution`, the contraction.**  Contracting every part of the greedy
cut to a point is a `2s`-marked quasi-isometry of the realisation of a shape
onto a rooted tree with a marked vertex. -/
theorem markedQI_contract (hs : 1 ≤ s) (l : List (Option Tri)) :
    MarkedQI (2 * s : ℝ) (listSpace l)
      (partSpace s (T := realiseAux l) (Shape.isAddr_neckAddr l)) := by
  have hs0 : (0 : ℝ) ≤ 2 * (s : ℝ) := by positivity
  refine ⟨fun x => contract (s := s) x.2, fun a b => ?_, fun a b => ?_, fun y => ?_, ?_, ?_⟩
  · -- the contraction does not increase distances
    have h := dist_contract_le (s := s) a b
    have hgrow : treeDist a.1 b.1 ≤ 2 * s * treeDist a.1 b.1 + 2 * s := by nlinarith
    have hnat : (partGraph s (realiseAux l)).dist (contract (s := s) a.2)
        (contract (s := s) b.2) ≤ 2 * s * treeDist a.1 b.1 + 2 * s := h.trans hgrow
    show (((partGraph s (realiseAux l)).dist (contract (s := s) a.2)
        (contract (s := s) b.2) : ℕ) : ℝ)
      ≤ 2 * (s : ℝ) * (treeDist a.1 b.1 : ℝ) + 2 * (s : ℝ)
    exact_mod_cast hnat
  · -- a path of parts lifts
    have h := treeDist_le_contract (s := s) hs a b
    have hgrow : s * (partGraph s (realiseAux l)).dist (contract (s := s) a.2)
          (contract (s := s) b.2) + 2 * (s - 1)
        ≤ 2 * s * (partGraph s (realiseAux l)).dist (contract (s := s) a.2)
            (contract (s := s) b.2) + 2 * s * (2 * s) := by
      have h1 : s * (partGraph s (realiseAux l)).dist (contract (s := s) a.2)
            (contract (s := s) b.2)
          ≤ 2 * s * (partGraph s (realiseAux l)).dist (contract (s := s) a.2)
            (contract (s := s) b.2) := by nlinarith
      have h2 : 2 * (s - 1) ≤ 2 * s * (2 * s) := by nlinarith [Nat.sub_le s 1]
      omega
    have hnat : treeDist a.1 b.1
        ≤ 2 * s * (partGraph s (realiseAux l)).dist (contract (s := s) a.2)
            (contract (s := s) b.2) + 2 * s * (2 * s) := h.trans hgrow
    show (treeDist a.1 b.1 : ℝ)
      ≤ 2 * (s : ℝ) * (((partGraph s (realiseAux l)).dist (contract (s := s) a.2)
          (contract (s := s) b.2) : ℕ) : ℝ) + 2 * (s : ℝ) * (2 * (s : ℝ))
    exact_mod_cast hnat
  · -- every part root is its own contraction
    refine ⟨⟨y.1, y.2.1⟩, ?_⟩
    rw [show contract (s := s) y.2.1 = y from contract_self y, _root_.dist_self]
    exact hs0
  · exact le_of_eq_of_le (_root_.dist_self _) hs0
  · exact le_of_eq_of_le (_root_.dist_self _) hs0

/-- **`thm:dilution`, the contraction of a shape**: the realisation of a shape
is `2s`-comparable to its contraction, a rooted tree with a marked vertex. -/
theorem markedQI_contract_shape (hs : 1 ≤ s) (σ : Shape) :
    MarkedQI (2 * s : ℝ) (shapeSpace σ)
      (partSpace s (T := realiseAux σ.decs) (Shape.isAddr_neckAddr σ.decs)) :=
  markedQI_contract hs σ.decs

end ChainClasses
