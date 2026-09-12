import Mathlib.Tactic
import ChainClasses.Shape.ContractAddr

/-!
The address layer of `sec:general-relabel` of `matching_classes_general.tex`: the
metric of the ambient `ℕ`-ary tree on addresses `List ℕ`, and the identification of
the graph metric of a rose tree with it.

Every metric realisation of the general transfer runs on this layer: a realisation is
a rose tree, its vertices are addresses (`RTree.Vert` of `ContractAddr.lean`), and its
graph is the parent-child graph `RTree.rtreeGraph`.  Two addresses meet at their
longest common prefix, the wedge, and the path between them climbs from one to the
wedge and descends to the other, so the graph distance is `|u| + |v| - 2|u ∧ v|`.
Once this identity is in place, every distance bound on a realisation, a shape or an
assembly is a computation on words: the wedge of two addresses with a common stem is
the stem followed by the wedge of the tails, two addresses leaving a common prefix by
different letters meet at that prefix, and an address and its parent are at distance
one.

* `wedgeN`, `wedgeN_prefix_left`, `wedgeN_prefix_right`, `prefix_wedgeN`: the wedge of
  two addresses, the greatest lower bound for the prefix order, with `wedgeN_comm`,
  `wedgeN_of_prefix`, `wedgeN_append_append`, `wedgeN_of_diverge` and the first
  divergence `exists_divergeN` of two incomparable addresses.
* `addrDist`, `addrDist_add_wedgeN_length`, `addrDist_triangle`, `addrDist_eq_zero_iff`:
  the tree metric on addresses, its truncation-free form, and the metric axioms.
* `addrDist_of_prefix`, `addrDist_append_append`, `addrDist_cons_cons_self`,
  `addrDist_cons_cons_ne`: the distance to an ancestor, inside a subtree, and across a
  divergence.
* `addrDist_eq_one_iff`, `RTree.rtreeGraph_adj_iff`, `RTree.rtreeGraph_adj_iff_addrDist`:
  the addresses at distance one are a parent and a child, which is the adjacency of
  the rose tree.
* `RTree.isAddr_of_prefix`, `RTree.prefix_mem_addrList`, `RTree.wedgeN_mem_addrList`:
  the address set is closed under prefixes, so the wedge of two vertices is a vertex.
* `RTree.exists_walk_of_prefix`, `RTree.addrDist_le_walk_length`: the walk up to an
  ancestor, and the lower bound on every walk.
* `RTree.rtreeGraph_dist`, `RTree.dist_vert_eq_addrDist`: **the graph metric of a rose
  tree is the address metric**.
-/

namespace ChainClasses

/-! ### The wedge of two addresses -/

/-- The longest common prefix of two addresses: the wedge point in the ambient
`ℕ`-ary tree. -/
def wedgeN : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _, [] => []
  | a :: x, b :: y => if a = b then a :: wedgeN x y else []

@[simp] lemma wedgeN_nil_left (y : List ℕ) : wedgeN [] y = [] := rfl

@[simp] lemma wedgeN_nil_right (x : List ℕ) : wedgeN x [] = [] := by
  cases x <;> rfl

lemma wedgeN_cons_cons (a b : ℕ) (x y : List ℕ) :
    wedgeN (a :: x) (b :: y) = if a = b then a :: wedgeN x y else [] := rfl

@[simp] lemma wedgeN_cons_cons_self (a : ℕ) (x y : List ℕ) :
    wedgeN (a :: x) (a :: y) = a :: wedgeN x y := by rw [wedgeN_cons_cons, if_pos rfl]

lemma wedgeN_cons_cons_ne {a b : ℕ} (h : a ≠ b) (x y : List ℕ) :
    wedgeN (a :: x) (b :: y) = [] := by rw [wedgeN_cons_cons, if_neg h]

lemma wedgeN_prefix_left : ∀ x y : List ℕ, wedgeN x y <+: x
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: x, b :: y => by
      rw [wedgeN_cons_cons]
      split
      · exact (List.cons_prefix_cons).mpr ⟨rfl, wedgeN_prefix_left x y⟩
      · exact List.nil_prefix

lemma wedgeN_prefix_right : ∀ x y : List ℕ, wedgeN x y <+: y
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: x, b :: y => by
      rw [wedgeN_cons_cons]
      split
      · next h => exact (List.cons_prefix_cons).mpr ⟨h, wedgeN_prefix_right x y⟩
      · exact List.nil_prefix

/-- The wedge is the greatest lower bound for the prefix order. -/
lemma prefix_wedgeN : ∀ {p x y : List ℕ}, p <+: x → p <+: y → p <+: wedgeN x y
  | [], _, _, _, _ => List.nil_prefix
  | c :: p, a :: x, b :: y, hx, hy => by
      rw [List.cons_prefix_cons] at hx hy
      obtain ⟨rfl, hx⟩ := hx
      obtain ⟨rfl, hy⟩ := hy
      rw [wedgeN_cons_cons_self]
      exact (List.cons_prefix_cons).mpr ⟨rfl, prefix_wedgeN hx hy⟩
  | _ :: _, [], _, hx, _ => by simp at hx
  | _ :: _, _ :: _, [], _, hy => by simp at hy

lemma wedgeN_of_prefix {x y : List ℕ} (h : x <+: y) : wedgeN x y = x :=
  (wedgeN_prefix_left x y).eq_of_length
    (le_antisymm (wedgeN_prefix_left x y).length_le
      (prefix_wedgeN (List.prefix_refl x) h).length_le)

@[simp] lemma wedgeN_self (x : List ℕ) : wedgeN x x = x :=
  wedgeN_of_prefix (List.prefix_refl x)

lemma wedgeN_comm : ∀ x y : List ℕ, wedgeN x y = wedgeN y x
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: x, b :: y => by
      rw [wedgeN_cons_cons, wedgeN_cons_cons]
      by_cases h : a = b
      · subst h; rw [if_pos rfl, if_pos rfl, wedgeN_comm x y]
      · rw [if_neg h, if_neg (Ne.symm h)]

lemma wedgeN_length_le_left (x y : List ℕ) : (wedgeN x y).length ≤ x.length :=
  (wedgeN_prefix_left x y).length_le

lemma wedgeN_length_le_right (x y : List ℕ) : (wedgeN x y).length ≤ y.length :=
  (wedgeN_prefix_right x y).length_le

/-- A common stem passes through the wedge. -/
lemma wedgeN_append_append (z p q : List ℕ) : wedgeN (z ++ p) (z ++ q) = z ++ wedgeN p q := by
  induction z with
  | nil => simp
  | cons a z ih =>
      rw [List.cons_append, List.cons_append, wedgeN_cons_cons_self, ih, List.cons_append]

/-- Two addresses leaving a common prefix by different letters meet at that
prefix. -/
lemma wedgeN_of_diverge {p x y : List ℕ} {a b : ℕ} (hab : a ≠ b)
    (hx : p ++ [a] <+: x) (hy : p ++ [b] <+: y) : wedgeN x y = p := by
  have hpx : p <+: x := (List.prefix_append p [a]).trans hx
  have hpy : p <+: y := (List.prefix_append p [b]).trans hy
  have hp : p <+: wedgeN x y := prefix_wedgeN hpx hpy
  refine (hp.eq_of_length (le_antisymm ?_ hp.length_le).symm).symm
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hax : p ++ [a] <+: wedgeN x y :=
    List.prefix_of_prefix_length_le hx (wedgeN_prefix_left x y) (by simp; omega)
  have hay : p ++ [a] <+: y := hax.trans (wedgeN_prefix_right x y)
  have : p ++ [a] = p ++ [b] :=
    List.prefix_of_prefix_length_le hay hy (by simp) |>.eq_of_length (by simp)
  exact hab (by simpa using this)

/-- First divergence of two prefix-incomparable addresses. -/
lemma exists_divergeN {w w' : List ℕ} (h1 : ¬ w <+: w') (h2 : ¬ w' <+: w) :
    ∃ (p : List ℕ) (a b : ℕ), a ≠ b ∧ (p ++ [a]) <+: w ∧ (p ++ [b]) <+: w' := by
  induction w generalizing w' with
  | nil => exact absurd (List.nil_prefix) h1
  | cons x t ih =>
      cases w' with
      | nil => exact absurd (List.nil_prefix) h2
      | cons x' t' =>
          by_cases hx : x = x'
          · subst hx
            have h1' : ¬ t <+: t' := fun hp => h1 ((List.cons_prefix_cons).mpr ⟨rfl, hp⟩)
            have h2' : ¬ t' <+: t := fun hp => h2 ((List.cons_prefix_cons).mpr ⟨rfl, hp⟩)
            obtain ⟨p, a, b, hab, hpa, hpb⟩ := ih h1' h2'
            exact ⟨x :: p, a, b, hab,
              (List.cons_prefix_cons).mpr ⟨rfl, hpa⟩,
              (List.cons_prefix_cons).mpr ⟨rfl, hpb⟩⟩
          · exact ⟨[], x, x', hx, ⟨t, rfl⟩, ⟨t', rfl⟩⟩

/-! ### The tree metric on addresses -/

/-- **The tree metric of the ambient `ℕ`-ary tree**: the path distance
`|x| + |y| - 2|x ∧ y|` between two addresses. -/
def addrDist (x y : List ℕ) : ℕ := x.length + y.length - 2 * (wedgeN x y).length

/-- The truncation-free form of `addrDist`. -/
lemma addrDist_add_wedgeN_length (x y : List ℕ) :
    addrDist x y + 2 * (wedgeN x y).length = x.length + y.length := by
  have h1 := wedgeN_length_le_left x y
  have h2 := wedgeN_length_le_right x y
  rw [addrDist]
  omega

@[simp] lemma addrDist_self (x : List ℕ) : addrDist x x = 0 := by
  rw [addrDist, wedgeN_self]
  omega

lemma addrDist_comm (x y : List ℕ) : addrDist x y = addrDist y x := by
  rw [addrDist, addrDist, wedgeN_comm]
  omega

/-- The triangle inequality for `addrDist`: the two wedges below `v` are
comparable, and the lower of them is a common prefix of `u` and `w`. -/
lemma addrDist_triangle (u v w : List ℕ) : addrDist u w ≤ addrDist u v + addrDist v w := by
  have h1 := addrDist_add_wedgeN_length u v
  have h2 := addrDist_add_wedgeN_length v w
  have h3 := addrDist_add_wedgeN_length u w
  have key : (wedgeN u v).length + (wedgeN v w).length ≤ v.length + (wedgeN u w).length := by
    rcases le_total (wedgeN u v).length (wedgeN v w).length with h | h
    · have hle : wedgeN u v <+: wedgeN v w :=
        List.prefix_of_prefix_length_le (wedgeN_prefix_right u v) (wedgeN_prefix_left v w) h
      have hw : wedgeN u v <+: wedgeN u w :=
        prefix_wedgeN (wedgeN_prefix_left u v) (hle.trans (wedgeN_prefix_right v w))
      have h4 := hw.length_le
      have h5 := wedgeN_length_le_left v w
      omega
    · have hle : wedgeN v w <+: wedgeN u v :=
        List.prefix_of_prefix_length_le (wedgeN_prefix_left v w) (wedgeN_prefix_right u v) h
      have hw : wedgeN v w <+: wedgeN u w :=
        prefix_wedgeN (hle.trans (wedgeN_prefix_left u v)) (wedgeN_prefix_right v w)
      have h4 := hw.length_le
      have h5 := wedgeN_length_le_right u v
      omega
  omega

lemma addrDist_eq_zero_iff {x y : List ℕ} : addrDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1 := wedgeN_length_le_left x y
    have h2 := wedgeN_length_le_right x y
    rw [addrDist] at h
    have ex : wedgeN x y = x := (wedgeN_prefix_left x y).eq_of_length (by omega)
    have ey : wedgeN x y = y := (wedgeN_prefix_right x y).eq_of_length (by omega)
    exact ex.symm.trans ey
  · rintro rfl
    exact addrDist_self x

/-- The distance to an ancestor is the difference of the depths. -/
lemma addrDist_of_prefix {x y : List ℕ} (h : x <+: y) :
    addrDist x y = y.length - x.length := by
  have := h.length_le
  rw [addrDist, wedgeN_of_prefix h]
  omega

@[simp] lemma addrDist_append_right (x y : List ℕ) : addrDist x (x ++ y) = y.length := by
  rw [addrDist_of_prefix (List.prefix_append x y), List.length_append]
  omega

@[simp] lemma addrDist_append_left (x y : List ℕ) : addrDist (x ++ y) x = y.length := by
  rw [addrDist_comm, addrDist_append_right]

/-- The distance from the root is the depth. -/
@[simp] lemma addrDist_nil_left (w : List ℕ) : addrDist [] w = w.length := by
  simpa using addrDist_append_right [] w

/-- The distance to the root is the depth. -/
@[simp] lemma addrDist_nil_right (w : List ℕ) : addrDist w [] = w.length := by
  rw [addrDist_comm, addrDist_nil_left]

@[simp] lemma addrDist_cons_cons_self (a : ℕ) (x y : List ℕ) :
    addrDist (a :: x) (a :: y) = addrDist x y := by
  have h1 := wedgeN_length_le_left x y
  have h2 := wedgeN_length_le_right x y
  simp only [addrDist, wedgeN_cons_cons_self, List.length_cons]
  omega

/-- Two addresses leaving a common prefix by different letters are joined through
that prefix. -/
lemma addrDist_cons_cons_ne {a b : ℕ} (h : a ≠ b) (x y : List ℕ) :
    addrDist (a :: x) (b :: y) = x.length + y.length + 2 := by
  simp only [addrDist, wedgeN_cons_cons_ne h, List.length_cons, List.length_nil]
  omega

/-- Distances inside one subtree are the distances of the addresses. -/
@[simp] lemma addrDist_append_append (z p q : List ℕ) :
    addrDist (z ++ p) (z ++ q) = addrDist p q := by
  induction z with
  | nil => rfl
  | cons a z ih => simp [ih]

/-- `addrDist` is the graph metric of the parent-child adjacency: the addresses at
distance one are exactly an address and one of its children. -/
lemma addrDist_eq_one_iff {u v : List ℕ} :
    addrDist u v = 1 ↔ (∃ b, v = u ++ [b]) ∨ (∃ b, u = v ++ [b]) := by
  constructor
  · intro h
    have h1 := addrDist_add_wedgeN_length u v
    have h2 := wedgeN_length_le_left u v
    have h3 := wedgeN_length_le_right u v
    rcases Nat.lt_or_ge (wedgeN u v).length u.length with hlt | hge
    · have hv : wedgeN u v = v := (wedgeN_prefix_right u v).eq_of_length (by omega)
      obtain ⟨s, hs⟩ : v <+: u := hv ▸ wedgeN_prefix_left u v
      have hlen : s.length = 1 := by
        have := congrArg List.length hs
        simp only [List.length_append] at this
        omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
      exact Or.inr ⟨b, hs.symm⟩
    · have hu : wedgeN u v = u := (wedgeN_prefix_left u v).eq_of_length (by omega)
      obtain ⟨s, hs⟩ : u <+: v := hu ▸ wedgeN_prefix_right u v
      have hlen : s.length = 1 := by
        have := congrArg List.length hs
        simp only [List.length_append] at this
        omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
      exact Or.inl ⟨b, hs.symm⟩
  · rintro (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · rw [addrDist_of_prefix (List.prefix_append u [b])]
      simp
    · rw [addrDist_comm, addrDist_of_prefix (List.prefix_append v [b])]
      simp

/-! ### The graph metric of a rose tree is the address metric -/

namespace RTree

/-- A prefix of an address is an address. -/
lemma isAddr_of_prefix : ∀ {t : RTree} {p w : List ℕ}, IsAddr t w → p <+: w → IsAddr t p
  | _, [], _, _, _ => isAddr_nil _
  | .node cs, a :: p, w, hw, hp => by
      obtain ⟨s, rfl⟩ := hp
      rw [List.cons_append, isAddr_cons] at hw
      obtain ⟨h, hw⟩ := hw
      rw [isAddr_cons]
      exact ⟨h, isAddr_of_prefix hw (List.prefix_append p s)⟩

/-- The address set is closed under taking prefixes. -/
lemma prefix_mem_addrList (t : RTree) {u p : List ℕ} (hu : u ∈ addrList t) (hp : p <+: u) :
    p ∈ addrList t :=
  mem_addrList_iff.mpr (isAddr_of_prefix (mem_addrList_iff.mp hu) hp)

/-- The wedge of two vertices is a vertex. -/
lemma wedgeN_mem_addrList (t : RTree) {u v : List ℕ} (hu : u ∈ addrList t) :
    wedgeN u v ∈ addrList t :=
  prefix_mem_addrList t hu (wedgeN_prefix_left u v)

/-- The parent-child adjacency of a rose tree, read on addresses: one address is
the other extended by a letter. -/
lemma rtreeGraph_adj_iff {t : RTree} {x y : Vert t} :
    (rtreeGraph t).Adj x y ↔ (∃ b, y.1 = x.1 ++ [b]) ∨ ∃ b, x.1 = y.1 ++ [b] := by
  rw [rtreeGraph_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · have hy : y.1 ≠ [] := by
        intro hc
        exact hne (Subtype.ext (by rw [h, hc]; rfl))
      exact Or.inl ⟨y.1.getLast hy, by rw [h]; exact (List.dropLast_append_getLast hy).symm⟩
    · have hx : x.1 ≠ [] := by
        intro hc
        exact hne (Subtype.ext (by rw [h, hc]; rfl))
      exact Or.inr ⟨x.1.getLast hx, by rw [h]; exact (List.dropLast_append_getLast hx).symm⟩
  · rintro (⟨b, hb⟩ | ⟨b, hb⟩)
    · refine ⟨fun hc => ?_, Or.inl ?_⟩
      · rw [hc] at hb
        have := congrArg List.length hb
        simp at this
      · rw [hb, List.dropLast_concat]
    · refine ⟨fun hc => ?_, Or.inr ?_⟩
      · rw [hc] at hb
        have := congrArg List.length hb
        simp at this
      · rw [hb, List.dropLast_concat]

/-- The parent-child adjacency is the address distance one. -/
lemma rtreeGraph_adj_iff_addrDist {t : RTree} {x y : Vert t} :
    (rtreeGraph t).Adj x y ↔ addrDist x.1 y.1 = 1 := by
  rw [rtreeGraph_adj_iff, addrDist_eq_one_iff]

/-- Walking up to an ancestor: a vertex and a prefix of it are joined by a walk
of length the difference of the depths. -/
lemma exists_walk_of_prefix (t : RTree) :
    ∀ (n : ℕ) (u v : Vert t), u.1 <+: v.1 → v.1.length - u.1.length = n →
      ∃ p : (rtreeGraph t).Walk u v, p.length = n := by
  intro n
  induction n with
  | zero =>
      intro u v huv hlen
      have : u = v := Subtype.ext (huv.eq_of_length (by have := huv.length_le; omega))
      subst this
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
      intro u v huv hlen
      have hvne : v.1 ≠ [] := by
        intro h
        rw [h] at hlen
        simp at hlen
      set s : Vert t := ⟨v.1.dropLast, dropLast_mem_addrList t v.1 v.2⟩ with hs
      have hsv : v.1 = s.1 ++ [v.1.getLast hvne] := (List.dropLast_append_getLast hvne).symm
      have hslen : s.1.length + 1 = v.1.length := by
        rw [hsv]; simp
      have hus : u.1 <+: s.1 := by
        refine List.prefix_of_prefix_length_le huv (hsv ▸ List.prefix_append s.1 _) ?_
        omega
      obtain ⟨p, hp⟩ := ih u s hus (by omega)
      exact ⟨p.concat (rtreeGraph_adj_iff.mpr (Or.inl ⟨_, hsv⟩)),
        by rw [SimpleGraph.Walk.length_concat, hp]⟩

/-- `addrDist` is subadditive along a walk: every edge changes it by one. -/
lemma addrDist_le_walk_length {t : RTree} {u v : Vert t} (p : (rtreeGraph t).Walk u v) :
    addrDist u.1 v.1 ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab _ ih =>
      have h1 : addrDist a.1 b.1 = 1 := rtreeGraph_adj_iff_addrDist.mp hab
      have := addrDist_triangle a.1 b.1 c.1
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- **The graph metric of a rose tree is the address metric.** -/
theorem rtreeGraph_dist (t : RTree) (u v : Vert t) :
    (rtreeGraph t).dist u v = addrDist u.1 v.1 := by
  have hw : wedgeN u.1 v.1 ∈ addrList t := wedgeN_mem_addrList t u.2
  obtain ⟨p, hp⟩ := exists_walk_of_prefix t (u.1.length - (wedgeN u.1 v.1).length)
    ⟨wedgeN u.1 v.1, hw⟩ u (wedgeN_prefix_left u.1 v.1) rfl
  obtain ⟨q, hq⟩ := exists_walk_of_prefix t (v.1.length - (wedgeN u.1 v.1).length)
    ⟨wedgeN u.1 v.1, hw⟩ v (wedgeN_prefix_right u.1 v.1) rfl
  have hle : (rtreeGraph t).dist u v ≤ addrDist u.1 v.1 := by
    have h := SimpleGraph.dist_le (p.reverse.append q)
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hp, hq] at h
    have h1 := wedgeN_length_le_left u.1 v.1
    have h2 := wedgeN_length_le_right u.1 v.1
    have h3 := addrDist_add_wedgeN_length u.1 v.1
    omega
  refine le_antisymm hle ?_
  have hr : (rtreeGraph t).Reachable u v := ⟨p.reverse.append q⟩
  obtain ⟨r, hr'⟩ := hr.exists_walk_length_eq_dist
  have := addrDist_le_walk_length r
  omega

/-- **The metric of a rose tree is the address metric.** -/
theorem dist_vert_eq_addrDist {t : RTree} (x y : Vert t) :
    dist x y = (addrDist x.1 y.1 : ℝ) := by
  rw [dist_vert, rtreeGraph_dist]

end RTree

end ChainClasses
