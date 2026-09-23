import Mathlib.Tactic
import ChainClasses.Chain.Encoding

/-!
`sec:transfer` of `matching_classes_simple.tex`, the abstract-labelling layer:
pure word combinatorics, no probability.

* `iotaL`: the map `ι` locating chain starts for an abstract labelling `lam : 𝔹 → ℕ`, running
  the recursion `eq:phi-def` on `lam`; `iota_eq_iotaL` identifies it with the
  `iota` of `ChainClasses.Chain.Encoding` when `lam` is the label field `lab`.
* `InAssoc`: the associated tree of a labelling; `inTree_iff_inAssoc` is the
  identification of the sample tree with the tree associated to its labels.
* `assoc_rep_unique`: uniqueness of the normal form `eq:normal-form` in an
  associated tree, under the standing hypothesis `∀ w, 1 ≤ lam w`.
* `wedge`, `treeDist`: longest common prefix and the metric of the ambient
  tree `𝒩`, with the truncation-free identity `treeDist_add_wedge_length`.
* `assoc_wedge_same`, `assoc_prefix`, `assoc_wedge_diverge`: the wedge of two
  normal-form vertices in the three relative positions of their words.
-/

namespace ChainClasses

/-! ### Chain starts for an abstract labelling -/

/-- `eq:phi-def` run on an abstract labelling `lam`: the fold carries the
consumed prefix in its first component and the image in its second. -/
def iotaL (lam : Word → ℕ) (w : Word) : Word :=
  (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ List.replicate (lam p.1 - 1) false ++ [j]))
    (([] : Word), ([] : Word))).2

/-- The first fold component records the consumed prefix. -/
lemma iotaL_foldl_fst (lam : Word → ℕ) (w a b : Word) :
    (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ List.replicate (lam p.1 - 1) false ++ [j]))
      (a, b)).1 = a ++ w := by
  induction w generalizing a b with
  | nil => simp
  | cons j t ih =>
      simpa using ih (a ++ [j]) (b ++ List.replicate (lam a - 1) false ++ [j])

@[simp] lemma iotaL_nil (lam : Word → ℕ) : iotaL lam [] = [] := rfl

/-- `eq:phi-def`: the recursion step of `ι` on a labelling. -/
lemma iotaL_concat (lam : Word → ℕ) (w : Word) (j : Bool) :
    iotaL lam (w ++ [j]) = iotaL lam w ++ List.replicate (lam w - 1) false ++ [j] := by
  have h := iotaL_foldl_fst lam w [] []
  simp only [List.nil_append, List.append_assoc] at h
  simp [iotaL, List.foldl_append]
  rw [h]

/-- The recursion only appends: `ι` is monotone for the prefix order. -/
lemma iotaL_prefix (lam : Word → ℕ) {w w' : Word} (h : w <+: w') :
    iotaL lam w <+: iotaL lam w' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc]
      calc iotaL lam w <+: iotaL lam (w ++ u) := ih
        _ <+: iotaL lam (w ++ u ++ [j]) := by
            rw [iotaL_concat]
            exact (List.prefix_append _ _).trans (List.prefix_append _ _)

/-- The length of `ι` grows by exactly `lam w` when the letter after `w` is consumed. -/
lemma iotaL_concat_length (lam : Word → ℕ) {w : Word} (hw : 1 ≤ lam w) (j : Bool) :
    (iotaL lam (w ++ [j])).length = (iotaL lam w).length + lam w := by
  rw [iotaL_concat]
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

/-! ### The bridge to `ChainClasses.Chain.Encoding` -/

variable {χ : Word → Bool}

/-- For a realised tree, `iota` locates the chain starts determined by the label field: `iota`
computes `κ` at the current image vertex, `iotaL` reads `lab` at the consumed
prefix, and the two agree since `lab hχ w = κ (ι w)`. -/
lemma iota_eq_iotaL (hχ : Chains χ) (w : Word) : iota hχ w = iotaL (lab hχ) w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w j ih =>
      rw [iota_concat, iotaL_concat, ih, lab, ih]

/-! ### The associated tree -/

/-- The associated tree of a labelling `lam`: the union of the chains
`ι(w)·1^l`, `0 ≤ l ≤ lam w - 1`. -/
def InAssoc (lam : Word → ℕ) (v : Word) : Prop :=
  ∃ w l, l ≤ lam w - 1 ∧ v = iotaL lam w ++ List.replicate l false

/-- `thm:chains` restated: the sample tree is the tree associated with its
label field. -/
theorem inTree_iff_inAssoc (hχ : Chains χ) (v : Word) :
    InTree χ v ↔ InAssoc (lab hχ) v := by
  rw [tree_eq_chains hχ]
  constructor
  · rintro ⟨w, l, hl, rfl⟩
    exact ⟨w, l, hl, by rw [iota_eq_iotaL]⟩
  · rintro ⟨w, l, hl, rfl⟩
    exact ⟨w, l, hl, by rw [iota_eq_iotaL]⟩

/-! ### Uniqueness of the normal form -/

/-- Part (ii) of `thm:chains` for an abstract labelling: if `w` is not a
prefix of `w'`, the ray of `w` misses the chain of `w'`. -/
theorem assocRay_chain_disjoint (lam : Word → ℕ) (hlam : ∀ u, 1 ≤ lam u)
    {w w' : Word} (h : ¬ w <+: w') {j l : ℕ} (hl : l ≤ lam w' - 1)
    (heq : iotaL lam w ++ List.replicate j false
      = iotaL lam w' ++ List.replicate l false) : False := by
  by_cases h2 : w' <+: w
  · -- `w'` is a strict prefix of `w`: compare lengths.
    obtain ⟨u, rfl⟩ := h2
    cases u with
    | nil => exact h (by simp)
    | cons c rest =>
        have hpre : iotaL lam (w' ++ [c]) <+: iotaL lam (w' ++ c :: rest) :=
          iotaL_prefix lam ⟨rest, by simp⟩
        have hlen1 := hpre.length_le
        have hlen2 : (iotaL lam (w' ++ [c])).length = (iotaL lam w').length + lam w' :=
          iotaL_concat_length lam (hlam w') c
        have hv : (iotaL lam (w' ++ c :: rest)).length + j = (iotaL lam w').length + l := by
          have := congrArg List.length heq
          simpa using this
        have := hlam w'
        omega
  · -- divergent words: the letters after the common prefix differ.
    obtain ⟨p, a, b, hab, hpa, hpb⟩ := exists_diverge h h2
    have hqa : iotaL lam (p ++ [a]) <+: iotaL lam w' ++ List.replicate l false := by
      rw [← heq]
      exact (iotaL_prefix lam hpa).trans (List.prefix_append _ _)
    have hqb : iotaL lam (p ++ [b]) <+: iotaL lam w' ++ List.replicate l false :=
      (iotaL_prefix lam hpb).trans (List.prefix_append _ _)
    have hlen : (iotaL lam (p ++ [a])).length = (iotaL lam (p ++ [b])).length := by
      rw [iotaL_concat, iotaL_concat]
      simp
    have heq' := prefix_eq_of_length hqa hqb hlen
    rw [iotaL_concat, iotaL_concat] at heq'
    have : a = b := by
      have := List.append_cancel_left heq'
      simpa using this
    exact hab this

/-- **Uniqueness of the normal form** in an associated tree: the word and the
level of `eq:normal-form` are determined by the vertex. -/
theorem assoc_rep_unique (lam : Word → ℕ) (hlam : ∀ u, 1 ≤ lam u)
    {w w' : Word} {l l' : ℕ} (hl : l ≤ lam w - 1) (hl' : l' ≤ lam w' - 1)
    (heq : iotaL lam w ++ List.replicate l false
      = iotaL lam w' ++ List.replicate l' false) : w = w' ∧ l = l' := by
  have hw : w = w' := by
    by_contra hne
    by_cases hp : w <+: w'
    · have hp' : ¬ w' <+: w := fun hp' =>
        hne (hp.eq_of_length (Nat.le_antisymm hp.length_le hp'.length_le))
      exact assocRay_chain_disjoint lam hlam hp' hl heq.symm
    · exact assocRay_chain_disjoint lam hlam hp hl' heq
  subst hw
  refine ⟨rfl, ?_⟩
  have := congrArg List.length heq
  simpa using this

/-! ### The metric of the ambient tree -/

/-- The longest common prefix of two words: the wedge point in `𝒩`. -/
def wedge : Word → Word → Word
  | [], _ => []
  | _, [] => []
  | a :: x, b :: y => if a = b then a :: wedge x y else []

@[simp] lemma wedge_nil_left (y : Word) : wedge [] y = [] := rfl

@[simp] lemma wedge_nil_right (x : Word) : wedge x [] = [] := by
  cases x <;> rfl

lemma wedge_cons_cons (a b : Bool) (x y : Word) :
    wedge (a :: x) (b :: y) = if a = b then a :: wedge x y else [] := rfl

lemma wedge_prefix_left (x y : Word) : wedge x y <+: x := by
  induction x generalizing y with
  | nil => exact List.nil_prefix
  | cons a x ih =>
      cases y with
      | nil => simp
      | cons b y =>
          rw [wedge_cons_cons]
          by_cases h : a = b
          · rw [ite_eq_left h]
            exact (List.cons_prefix_cons).mpr ⟨rfl, ih y⟩
          · rw [ite_eq_right h]
            exact List.nil_prefix

lemma wedge_prefix_right (x y : Word) : wedge x y <+: y := by
  induction x generalizing y with
  | nil => exact List.nil_prefix
  | cons a x ih =>
      cases y with
      | nil => simp
      | cons b y =>
          rw [wedge_cons_cons]
          by_cases h : a = b
          · rw [ite_eq_left h, h]
            exact (List.cons_prefix_cons).mpr ⟨rfl, ih y⟩
          · rw [ite_eq_right h]
            exact List.nil_prefix

/-- The wedge is the greatest lower bound for the prefix order. -/
lemma prefix_wedge {p x y : Word} (hx : p <+: x) (hy : p <+: y) : p <+: wedge x y := by
  induction p generalizing x y with
  | nil => exact List.nil_prefix
  | cons c p ih =>
      cases x with
      | nil => simp at hx
      | cons a x =>
          cases y with
          | nil => simp at hy
          | cons b y =>
              rw [List.cons_prefix_cons] at hx hy
              obtain ⟨rfl, hx⟩ := hx
              obtain ⟨rfl, hy⟩ := hy
              rw [wedge_cons_cons, ite_eq_left rfl]
              exact (List.cons_prefix_cons).mpr ⟨rfl, ih hx hy⟩

@[simp] lemma wedge_self (x : Word) : wedge x x = x := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [wedge_cons_cons, ite_eq_left rfl, ih]

lemma wedge_comm (x y : Word) : wedge x y = wedge y x := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
      cases y with
      | nil => simp
      | cons b y =>
          rw [wedge_cons_cons, wedge_cons_cons]
          by_cases h : a = b
          · subst h
            rw [ite_eq_left rfl, ite_eq_left rfl, ih]
          · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

lemma wedge_of_prefix {x y : Word} (h : x <+: y) : wedge x y = x := by
  have h1 := prefix_wedge (List.prefix_refl x) h
  exact (h1.eq_of_length
    (Nat.le_antisymm h1.length_le (wedge_prefix_left x y).length_le)).symm

lemma wedge_length_le_left (x y : Word) : (wedge x y).length ≤ x.length :=
  (wedge_prefix_left x y).length_le

lemma wedge_length_le_right (x y : Word) : (wedge x y).length ≤ y.length :=
  (wedge_prefix_right x y).length_le

/-- The tree metric of `𝒩`: path distance between two vertices. -/
def treeDist (x y : Word) : ℕ := x.length + y.length - 2 * (wedge x y).length

@[simp] lemma treeDist_self (x : Word) : treeDist x x = 0 := by
  simp only [treeDist, wedge_self]
  omega

lemma treeDist_comm (x y : Word) : treeDist x y = treeDist y x := by
  simp only [treeDist, wedge_comm x y]
  omega

/-- The truncation-free form of `treeDist`. -/
lemma treeDist_add_wedge_length (x y : Word) :
    treeDist x y + 2 * (wedge x y).length = x.length + y.length := by
  have h1 := wedge_length_le_left x y
  have h2 := wedge_length_le_right x y
  simp only [treeDist]
  omega

/-- Two prefixes of one word are comparable. -/
lemma prefix_of_prefix_of_length_le {p q v : Word} (hp : p <+: v) (hq : q <+: v)
    (h : p.length ≤ q.length) : p <+: q := by
  rw [List.prefix_iff_eq_take.mp hq]
  exact List.prefix_take_iff.mpr ⟨hp, h⟩

/-- The triangle inequality for `treeDist`: the two wedges below `v` are
comparable, and the lower of them is a common prefix of `u` and `w`. -/
lemma treeDist_triangle (u v w : Word) : treeDist u w ≤ treeDist u v + treeDist v w := by
  have h1 := treeDist_add_wedge_length u v
  have h2 := treeDist_add_wedge_length v w
  have h3 := treeDist_add_wedge_length u w
  have key : (wedge u v).length + (wedge v w).length ≤ v.length + (wedge u w).length := by
    rcases le_total (wedge u v).length (wedge v w).length with h | h
    · have hle : wedge u v <+: wedge v w :=
        prefix_of_prefix_of_length_le (wedge_prefix_right u v) (wedge_prefix_left v w) h
      have hw : wedge u v <+: wedge u w :=
        prefix_wedge (wedge_prefix_left u v) (hle.trans (wedge_prefix_right v w))
      have h4 := hw.length_le
      have h5 := wedge_length_le_left v w
      omega
    · have hle : wedge v w <+: wedge u v :=
        prefix_of_prefix_of_length_le (wedge_prefix_left v w) (wedge_prefix_right u v) h
      have hw : wedge v w <+: wedge u w :=
        prefix_wedge (hle.trans (wedge_prefix_left u v)) (wedge_prefix_right v w)
      have h4 := hw.length_le
      have h5 := wedge_length_le_right u v
      omega
  omega

lemma treeDist_eq_zero_iff {x y : Word} : treeDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1 := wedge_length_le_left x y
    have h2 := wedge_length_le_right x y
    simp only [treeDist] at h
    have ex : wedge x y = x := (wedge_prefix_left x y).eq_of_length (by omega)
    have ey : wedge x y = y := (wedge_prefix_right x y).eq_of_length (by omega)
    exact ex.symm.trans ey
  · rintro rfl
    exact treeDist_self x

lemma treeDist_of_prefix {x y : Word} (h : x <+: y) :
    treeDist x y = y.length - x.length := by
  have := h.length_le
  simp only [treeDist, wedge_of_prefix h]
  omega

/-- Two vertices leaving a common prefix by different letters meet at that
prefix. -/
lemma wedge_of_diverge {p x y : Word} {a b : Bool} (hab : a ≠ b)
    (hx : p ++ [a] <+: x) (hy : p ++ [b] <+: y) : wedge x y = p := by
  have hpx : p <+: x := (List.prefix_append p [a]).trans hx
  have hpy : p <+: y := (List.prefix_append p [b]).trans hy
  have hp : p <+: wedge x y := prefix_wedge hpx hpy
  refine (hp.eq_of_length (le_antisymm ?_ hp.length_le).symm).symm
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hax : p ++ [a] <+: wedge x y :=
    prefix_of_prefix_of_length_le hx (wedge_prefix_left x y) (by simp; omega)
  have hay : p ++ [a] <+: y := hax.trans (wedge_prefix_right x y)
  have : p ++ [a] = p ++ [b] :=
    prefix_of_prefix_of_length_le hay hy (by simp) |>.eq_of_length (by simp)
  exact hab (by simpa using this)

/-- The distance from the root is the depth. -/
@[simp] lemma treeDist_nil_left (w : Word) : treeDist [] w = w.length := by
  simp [treeDist]

/-- The distance to the root is the depth. -/
@[simp] lemma treeDist_nil_right (w : Word) : treeDist w [] = w.length := by
  simp [treeDist]

/-- Distances inside one subtree of the root are unchanged. -/
@[simp] lemma treeDist_cons_cons_self (a : Bool) (u v : Word) :
    treeDist (a :: u) (a :: v) = treeDist u v := by
  have h1 := wedge_length_le_left u v
  have h2 := wedge_length_le_right u v
  have hw : wedge (a :: u) (a :: v) = a :: wedge u v := by rw [wedge_cons_cons, ite_eq_left rfl]
  simp only [treeDist, hw, List.length_cons]
  omega

/-- Two vertices under different children of the root meet at the root. -/
@[simp] lemma treeDist_false_true (u v : Word) :
    treeDist (false :: u) (true :: v) = u.length + v.length + 2 := by
  have hw : wedge (false :: u) (true :: v) = [] := by
    rw [wedge_cons_cons, ite_eq_right (by simp)]
  simp only [treeDist, hw, List.length_cons, List.length_nil]
  omega

/-- Two vertices under different children of the root meet at the root. -/
@[simp] lemma treeDist_true_false (u v : Word) :
    treeDist (true :: u) (false :: v) = u.length + v.length + 2 := by
  have hw : wedge (true :: u) (false :: v) = [] := by
    rw [wedge_cons_cons, ite_eq_right (by simp)]
  simp only [treeDist, hw, List.length_cons, List.length_nil]
  omega

/-- `treeDist` is the graph metric of the parent-child adjacency: the words at
distance one are exactly a word and one of its two children. -/
lemma treeDist_eq_one_iff {u v : Word} :
    treeDist u v = 1 ↔ (∃ b, v = u ++ [b]) ∨ (∃ b, u = v ++ [b]) := by
  constructor
  · intro h
    have h1 := treeDist_add_wedge_length u v
    have h2 := wedge_length_le_left u v
    have h3 := wedge_length_le_right u v
    rcases Nat.lt_or_ge (wedge u v).length u.length with hlt | hge
    · -- the wedge is `v`, one letter below `u`
      have hv : wedge u v = v := (wedge_prefix_right u v).eq_of_length (by omega)
      obtain ⟨s, hs⟩ : v <+: u := hv ▸ wedge_prefix_left u v
      have hlen : s.length = 1 := by
        have := congrArg List.length hs
        simp only [List.length_append] at this
        omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
      exact Or.inr ⟨b, hs.symm⟩
    · have hu : wedge u v = u := (wedge_prefix_left u v).eq_of_length (by omega)
      obtain ⟨s, hs⟩ : u <+: v := hu ▸ wedge_prefix_right u v
      have hlen : s.length = 1 := by
        have := congrArg List.length hs
        simp only [List.length_append] at this
        omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
      exact Or.inl ⟨b, hs.symm⟩
  · rintro (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · rw [treeDist_of_prefix (List.prefix_append u [b])]
      simp
    · rw [treeDist_comm, treeDist_of_prefix (List.prefix_append v [b])]
      simp

/-! ### Wedges of normal-form vertices -/

/-- Extending the replicate tail preserves the prefix relation. -/
lemma append_replicate_prefix (u : Word) (c : Bool) {l m : ℕ} (h : l ≤ m) :
    u ++ List.replicate l c <+: u ++ List.replicate m c :=
  ⟨List.replicate (m - l) c, by
    rw [List.append_assoc, ← List.replicate_add, Nat.add_sub_cancel' h]⟩

/-- The wedge of two vertices on one chain sits at the lower level. -/
lemma wedge_append_replicate (u : Word) (c : Bool) (l l' : ℕ) :
    wedge (u ++ List.replicate l c) (u ++ List.replicate l' c)
      = u ++ List.replicate (min l l') c := by
  have hup := prefix_wedge
    (append_replicate_prefix u c (Nat.min_le_left l l'))
    (append_replicate_prefix u c (Nat.min_le_right l l'))
  have h1 := wedge_length_le_left (u ++ List.replicate l c) (u ++ List.replicate l' c)
  have h2 := wedge_length_le_right (u ++ List.replicate l c) (u ++ List.replicate l' c)
  have h3 := hup.length_le
  refine (hup.eq_of_length ?_).symm
  simp only [List.length_append, List.length_replicate] at h1 h2 h3 ⊢
  omega

/-- Same word: the wedge of two chain vertices of `w` is the lower one. -/
lemma assoc_wedge_same (lam : Word → ℕ) (w : Word) (l l' : ℕ) :
    wedge (iotaL lam w ++ List.replicate l false) (iotaL lam w ++ List.replicate l' false)
      = iotaL lam w ++ List.replicate (min l l') false :=
  wedge_append_replicate _ _ _ _

/-- Strict prefix: the chain vertices of `w` precede those of any extension. -/
lemma assoc_prefix (lam : Word → ℕ) {w w' : Word} (h : w <+: w') (hne : w ≠ w')
    {l : ℕ} (hl : l ≤ lam w - 1) (l' : ℕ) :
    iotaL lam w ++ List.replicate l false
      <+: iotaL lam w' ++ List.replicate l' false := by
  obtain ⟨u, rfl⟩ := h
  cases u with
  | nil => exact absurd (by simp) hne
  | cons j rest =>
      calc iotaL lam w ++ List.replicate l false
          <+: iotaL lam w ++ List.replicate (lam w - 1) false :=
            append_replicate_prefix _ _ hl
        _ <+: iotaL lam (w ++ [j]) := by
            rw [iotaL_concat]
            exact List.prefix_append _ _
        _ <+: iotaL lam (w ++ j :: rest) := iotaL_prefix lam ⟨rest, by simp⟩
        _ <+: iotaL lam (w ++ j :: rest) ++ List.replicate l' false :=
            List.prefix_append _ _

/-- Divergent words: the wedge of the two chains is the branch point over the
common prefix. -/
lemma assoc_wedge_diverge (lam : Word → ℕ) {p w w' : Word} {a b : Bool} (hab : a ≠ b)
    (ha : p ++ [a] <+: w) (hb : p ++ [b] <+: w') (l l' : ℕ) :
    wedge (iotaL lam w ++ List.replicate l false) (iotaL lam w' ++ List.replicate l' false)
      = iotaL lam p ++ List.replicate (lam p - 1) false := by
  have hqa : (iotaL lam p ++ List.replicate (lam p - 1) false) ++ [a]
      <+: iotaL lam w ++ List.replicate l false := by
    rw [← iotaL_concat]
    exact (iotaL_prefix lam ha).trans (List.prefix_append _ _)
  have hqb : (iotaL lam p ++ List.replicate (lam p - 1) false) ++ [b]
      <+: iotaL lam w' ++ List.replicate l' false := by
    rw [← iotaL_concat]
    exact (iotaL_prefix lam hb).trans (List.prefix_append _ _)
  have hqw := prefix_wedge
    ((List.prefix_append _ [a]).trans hqa) ((List.prefix_append _ [b]).trans hqb)
  obtain ⟨t, ht⟩ := hqw
  cases t with
  | nil => rw [← ht, List.append_nil]
  | cons c t' =>
      exfalso
      -- the wedge would extend the branch point by a letter equal to both `a` and `b`
      have hstep : (iotaL lam p ++ List.replicate (lam p - 1) false) ++ [c]
          <+: (iotaL lam p ++ List.replicate (lam p - 1) false) ++ c :: t' :=
        ⟨t', by simp⟩
      have hcx : (iotaL lam p ++ List.replicate (lam p - 1) false) ++ [c]
          <+: iotaL lam w ++ List.replicate l false := by
        refine hstep.trans ?_
        rw [ht]
        exact wedge_prefix_left _ _
      have hcy : (iotaL lam p ++ List.replicate (lam p - 1) false) ++ [c]
          <+: iotaL lam w' ++ List.replicate l' false := by
        refine hstep.trans ?_
        rw [ht]
        exact wedge_prefix_right _ _
      have hac : a = c := by
        have h1 := prefix_eq_of_length hqa hcx (by simp)
        have := List.append_cancel_left h1
        simpa using this
      have hbc : b = c := by
        have h1 := prefix_eq_of_length hqb hcy (by simp)
        have := List.append_cancel_left h1
        simpa using this
      exact hab (hac.trans hbc.symm)

end ChainClasses
