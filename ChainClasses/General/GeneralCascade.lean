import Mathlib.Tactic
import ChainClasses.Chain.WordGraph
import BranchingProcess.Word

/-!
`thm:bushy` (the coding in its proof) of `matching_classes_general.tex`: the cascade
encoding of a `J`-ary tree into the binary tree `𝔹`, and its quasi-isometry constant.

A split of arity `k ≤ 2^L` is replaced by a cascade of binary splits whose `k` slots
sit at depth `L`: the `i`-th outgoing edge becomes the path of length `L` from the
cascade root to the slot coded by the `L`-bit expansion of `i`.  Replacing every split
of a tree of words over `Fin N` by its cascade encodes the tree into `𝔹` letter by
letter, and the geometry of the encoding is controlled by the wedge: two encoded words
meet at the encoding of the wedge of the originals, extended by the common prefix of
the codes of the first differing letters, which has length at most `L - 1`.  This gives
`d ≤ d' ≤ L d` between copies, and every cascade vertex lies within `L - 1` of a copy.

The cascade here places all slots at the uniform depth `L = ⌈log₂ N⌉` (`Nat.clog 2 N`),
within the paper's `⌊log₂ k⌋`/`⌈log₂ k⌉` bound, and the quasi-isometry constant is `L`
in place of the paper's `1 + ⌈log₂ J⌉`.  The balanced variable-depth cascade with
`k - 1` binary splits is not formalised: the quasi-isometry uses the uniform depth only.

* `bitsL`, `length_bitsL`, `bitsL_inj`: the `L`-bit code of a letter, injective below
  `2^L`.
* `cascWord`, `length_cascWord`: the letter-by-letter encoding of a word, of length `L`
  times the length of the word.
* `wedge_cascWord_diverge`, `treeDist_cascWord_diverge`: the wedge identity of encoded
  words, `d' = L d - 2e` with `e ≤ L - 1` the agreement of the two differing codes.
* `treeDist_cascWord_le`, `le_treeDist_cascWord`: **`thm:bushy` (the coding in its proof),
  the metric bounds** `d ≤ d' ≤ L d` between copies.
* `PrefixClosedN`, `cascSet`, `prefixClosed_cascSet`, `exists_copy_near`: the cascade of
  a prefix-closed set of words over `Fin N`, prefix-closed, with every vertex within
  `L - 1` of a copy.
* `wordGraphN`, `wordGraphN_dist`: the parent-child graph of a prefix-closed set of
  words over `Fin N`, with graph metric `BranchingProcess.treeDist`.
* `cascMap`, `cascade_isQIWith`, `cascade_quasiIsometric`, `cascade_isQIWith_clog`:
  **`thm:bushy` (the coding in its proof)**, the cascade encoding is an
  `L`-quasi-isometry of the parent-child graphs in the sense of `def:qi`, at
  `L = ⌈log₂ N⌉` in particular.
-/

namespace ChainClasses

open SimpleGraph

variable {N : ℕ}

/-! ### The letter code -/

/-- The `L`-bit binary expansion of `j`, least significant bit first, padded with
`false` to length `L`: the address of the slot of the `j`-th child in the cascade. -/
def bitsL : ℕ → ℕ → List Bool
  | 0, _ => []
  | L + 1, j => decide (j % 2 = 1) :: bitsL L (j / 2)

@[simp] lemma bitsL_zero (j : ℕ) : bitsL 0 j = [] := rfl

lemma bitsL_succ (L j : ℕ) : bitsL (L + 1) j = decide (j % 2 = 1) :: bitsL L (j / 2) := rfl

/-- Every slot sits at depth exactly `L`. -/
@[simp] lemma length_bitsL (L j : ℕ) : (bitsL L j).length = L := by
  induction L generalizing j with
  | zero => rfl
  | succ L ih => simp [bitsL_succ, ih]

/-- The code is injective on the letters below `2^L`. -/
lemma bitsL_inj {L j j' : ℕ} (hj : j < 2 ^ L) (hj' : j' < 2 ^ L)
    (h : bitsL L j = bitsL L j') : j = j' := by
  induction L generalizing j j' with
  | zero =>
      simp only [pow_zero, Nat.lt_one_iff] at hj hj'
      omega
  | succ L ih =>
      simp only [bitsL_succ, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hj2 : j / 2 < 2 ^ L := by rw [pow_succ] at hj; omega
      have hj'2 : j' / 2 < 2 ^ L := by rw [pow_succ] at hj'; omega
      have h3 := ih hj2 hj'2 h2
      have h4 := decide_eq_decide.mp h1
      omega

/-- Distinct letters below `2^L` have distinct codes. -/
lemma bitsL_ne {L : ℕ} {a b : Fin N} (hN : N ≤ 2 ^ L) (hab : a ≠ b) :
    bitsL L a ≠ bitsL L b := fun h =>
  hab (Fin.ext (bitsL_inj (a.2.trans_le hN) (b.2.trans_le hN) h))

/-- The codes of two distinct letters agree on fewer than `L` bits. -/
lemma wedge_bitsL_length_lt {L : ℕ} {a b : Fin N} (hN : N ≤ 2 ^ L) (hab : a ≠ b) :
    (wedge (bitsL L a) (bitsL L b)).length < L := by
  have h1 := (wedge_prefix_left (bitsL L a) (bitsL L b)).length_le
  rw [length_bitsL] at h1
  refine lt_of_le_of_ne h1 fun heq => bitsL_ne hN hab ?_
  have ha : wedge (bitsL L a) (bitsL L b) = bitsL L a :=
    (wedge_prefix_left _ _).eq_of_length (by rw [heq, length_bitsL])
  have hb : wedge (bitsL L a) (bitsL L b) = bitsL L b :=
    (wedge_prefix_right _ _).eq_of_length (by rw [heq, length_bitsL])
  exact ha.symm.trans hb

/-! ### The word code -/

/-- The cascade encoding of a word over `Fin N`: each letter is replaced by its `L`-bit
code, so the copy of `w` sits at depth `L |w|` in `𝔹`. -/
def cascWord (L : ℕ) (w : BranchingProcess.Word N) : Word :=
  List.flatMap (fun j : Fin N => bitsL L j) w

@[simp] lemma cascWord_nil (L : ℕ) : cascWord L ([] : BranchingProcess.Word N) = [] := rfl

lemma cascWord_cons (L : ℕ) (j : Fin N) (w : BranchingProcess.Word N) :
    cascWord L (j :: w) = bitsL L j ++ cascWord L w := by
  simp [cascWord]

lemma cascWord_append (L : ℕ) (u v : BranchingProcess.Word N) :
    cascWord L (u ++ v) = cascWord L u ++ cascWord L v := by
  simp [cascWord]

/-- The copy of `w` sits at depth `L |w|`. -/
@[simp] lemma length_cascWord (L : ℕ) (w : BranchingProcess.Word N) :
    (cascWord L w).length = L * w.length := by
  induction w with
  | nil => simp
  | cons j w ih =>
      rw [cascWord_cons, List.length_append, length_bitsL, ih, List.length_cons, Nat.mul_succ]
      omega

/-- The encoding is monotone for the prefix order. -/
lemma cascWord_prefix (L : ℕ) {u v : BranchingProcess.Word N} (h : u <+: v) :
    cascWord L u <+: cascWord L v := by
  obtain ⟨s, rfl⟩ := h
  rw [cascWord_append]
  exact List.prefix_append _ _

/-! ### The wedge of two encoded words -/

/-- Wedging commutes with a common prefix. -/
lemma wedge_append_append (p x y : Word) : wedge (p ++ x) (p ++ y) = p ++ wedge x y := by
  induction p with
  | nil => simp
  | cons a p ih => simp [wedge_cons_cons, ih]

/-- Two distinct words of the same length wedge with whatever follows them as they
wedge with each other. -/
lemma wedge_append_of_ne {x y : Word} (hlen : x.length = y.length) (hne : x ≠ y)
    (s t : Word) : wedge (x ++ s) (y ++ t) = wedge x y := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => exact absurd rfl hne
      | cons b y => simp at hlen
  | cons a x ih =>
      cases y with
      | nil => simp at hlen
      | cons b y =>
          simp only [List.cons_append, wedge_cons_cons]
          by_cases hab : a = b
          · subst hab
            rw [ite_eq_left rfl, ite_eq_left rfl, ih (by simpa using hlen) (fun h => hne (by rw [h]))]
          · rw [ite_eq_right hab, ite_eq_right hab]

/-- **The wedge identity.** Two words leaving a common prefix `p` by distinct letters
`a ≠ b` encode to words meeting at the encoding of `p` extended by the common prefix of
the two codes. -/
lemma wedge_cascWord_diverge (L : ℕ) (hN : N ≤ 2 ^ L) {p u v : BranchingProcess.Word N}
    {a b : Fin N} (hab : a ≠ b) :
    wedge (cascWord L (p ++ a :: u)) (cascWord L (p ++ b :: v))
      = cascWord L p ++ wedge (bitsL L a) (bitsL L b) := by
  rw [cascWord_append, cascWord_append, cascWord_cons, cascWord_cons, wedge_append_append,
    wedge_append_of_ne (by simp) (bitsL_ne hN hab)]

/-- The wedge of two words leaving a common prefix by distinct letters. -/
lemma wedgeN_diverge {p u v : BranchingProcess.Word N} {a b : Fin N} (hab : a ≠ b) :
    BranchingProcess.wedge (p ++ a :: u) (p ++ b :: v) = p := by
  rw [BranchingProcess.wedge_append_append, BranchingProcess.wedge_cons_cons, ite_eq_right hab]
  simp

/-- **`thm:bushy` (the coding in its proof), the exact distance of diverging copies**:
`d' + 2e = L d`, where `e < L` is the agreement of the codes of the first differing
letters. -/
theorem treeDist_cascWord_diverge (L : ℕ) (hN : N ≤ 2 ^ L) {p u v : BranchingProcess.Word N}
    {a b : Fin N} (hab : a ≠ b) :
    treeDist (cascWord L (p ++ a :: u)) (cascWord L (p ++ b :: v))
        + 2 * (wedge (bitsL L a) (bitsL L b)).length
      = L * BranchingProcess.treeDist (p ++ a :: u) (p ++ b :: v) := by
  have h1 := treeDist_add_wedge_length (cascWord L (p ++ a :: u)) (cascWord L (p ++ b :: v))
  rw [wedge_cascWord_diverge L hN hab, List.length_append, length_cascWord, length_cascWord,
    length_cascWord] at h1
  have h2 := BranchingProcess.treeDist_add (p ++ a :: u) (p ++ b :: v)
  rw [wedgeN_diverge hab] at h2
  simp only [List.length_append, List.length_cons] at h1 h2
  have h3 : L * BranchingProcess.treeDist (p ++ a :: u) (p ++ b :: v)
      + 2 * (L * p.length) = L * (p.length + (u.length + 1)) + L * (p.length + (v.length + 1)) := by
    calc L * BranchingProcess.treeDist (p ++ a :: u) (p ++ b :: v) + 2 * (L * p.length)
        = L * (BranchingProcess.treeDist (p ++ a :: u) (p ++ b :: v) + 2 * p.length) := by ring
      _ = L * (p.length + (u.length + 1) + (p.length + (v.length + 1))) := by rw [h2]
      _ = L * (p.length + (u.length + 1)) + L * (p.length + (v.length + 1)) := by ring
  have h4 : L * (p.length + (u.length + 1)) = L * p.length + L * u.length + L := by ring
  have h5 : L * (p.length + (v.length + 1)) = L * p.length + L * v.length + L := by ring
  omega

/-! ### The metric bounds -/

/-- **`thm:bushy` (the coding in its proof), the upper bound**: copies are at most `L`
times as far apart as the originals. -/
theorem treeDist_cascWord_le (L : ℕ) (u v : BranchingProcess.Word N) :
    treeDist (cascWord L u) (cascWord L v) ≤ L * BranchingProcess.treeDist u v := by
  have hp : cascWord L (BranchingProcess.wedge u v) <+: wedge (cascWord L u) (cascWord L v) :=
    prefix_wedge (cascWord_prefix L (BranchingProcess.wedge_prefix_left u v))
      (cascWord_prefix L (BranchingProcess.wedge_prefix_right u v))
  have h1 := hp.length_le
  rw [length_cascWord] at h1
  have h2 := treeDist_add_wedge_length (cascWord L u) (cascWord L v)
  rw [length_cascWord, length_cascWord] at h2
  have h3 := BranchingProcess.treeDist_add u v
  have h4 : L * BranchingProcess.treeDist u v + 2 * (L * (BranchingProcess.wedge u v).length)
      = L * u.length + L * v.length := by
    calc L * BranchingProcess.treeDist u v + 2 * (L * (BranchingProcess.wedge u v).length)
        = L * (BranchingProcess.treeDist u v + 2 * (BranchingProcess.wedge u v).length) := by ring
      _ = L * (u.length + v.length) := by rw [h3]
      _ = L * u.length + L * v.length := by ring
  omega

/-- **`thm:bushy` (the coding in its proof), the lower bound**: copies are at least as
far apart as the originals. -/
theorem le_treeDist_cascWord {L : ℕ} (hN : N ≤ 2 ^ L) (hL : 1 ≤ L)
    (u v : BranchingProcess.Word N) :
    BranchingProcess.treeDist u v ≤ treeDist (cascWord L u) (cascWord L v) := by
  obtain ⟨u₁, hu⟩ := BranchingProcess.wedge_prefix_left u v
  obtain ⟨v₁, hv⟩ := BranchingProcess.wedge_prefix_right u v
  have hw : BranchingProcess.wedge u₁ v₁ = [] := by
    have h := BranchingProcess.wedge_append_append (BranchingProcess.wedge u v) u₁ v₁
    rw [hu, hv] at h
    exact List.self_eq_append_right.mp h
  generalize BranchingProcess.wedge u v = p at hu hv
  subst hu hv
  -- the prefix cases
  have hpre : ∀ x y : BranchingProcess.Word N, x <+: y →
      BranchingProcess.treeDist x y ≤ treeDist (cascWord L x) (cascWord L y) := by
    intro x y hxy
    rw [BranchingProcess.treeDist_of_prefix hxy, treeDist_of_prefix (cascWord_prefix L hxy),
      length_cascWord, length_cascWord, ← Nat.mul_sub]
    exact Nat.le_mul_of_pos_left _ hL
  cases u₁ with
  | nil => exact hpre _ _ ((List.prefix_append_right_inj p).mpr List.nil_prefix)
  | cons a u' =>
      cases v₁ with
      | nil =>
          rw [BranchingProcess.treeDist_comm, treeDist_comm]
          exact hpre _ _ ((List.prefix_append_right_inj p).mpr List.nil_prefix)
      | cons b v' =>
          have hab : a ≠ b := by
            intro h
            rw [BranchingProcess.wedge_cons_cons, ite_eq_left h] at hw
            exact List.cons_ne_nil _ _ hw
          have h1 := treeDist_cascWord_diverge L hN (p := p) (u := u') (v := v') hab
          have h2 := wedge_bitsL_length_lt hN hab
          have h3 := BranchingProcess.treeDist_add (p ++ a :: u') (p ++ b :: v')
          rw [wedgeN_diverge hab] at h3
          simp only [List.length_append, List.length_cons] at h3
          have h4 : L * BranchingProcess.treeDist (p ++ a :: u') (p ++ b :: v')
              = L * u'.length + L * v'.length + 2 * L := by
            have : BranchingProcess.treeDist (p ++ a :: u') (p ++ b :: v')
                = u'.length + v'.length + 2 := by omega
            rw [this]; ring
          have h5 := Nat.le_mul_of_pos_left u'.length hL
          have h6 := Nat.le_mul_of_pos_left v'.length hL
          omega


/-! ### The cascade of a prefix-closed set -/

/-- A set of words over `Fin N` closed under taking prefixes: the vertex set of a subtree
of the ambient `N`-ary tree, such as the reduced skeleton of a sample. -/
def PrefixClosedN (T : BranchingProcess.Word N → Prop) : Prop :=
  ∀ ⦃u v : BranchingProcess.Word N⦄, u <+: v → T v → T u

/-- The cascade of a set of words over `Fin N`: every split replaced by its cascade, so
the vertices are the prefixes of the encoded words. The copy of `w` is `cascWord L w`. -/
def cascSet (L : ℕ) (T : BranchingProcess.Word N → Prop) (x : Word) : Prop :=
  ∃ w, T w ∧ x <+: cascWord L w

/-- The cascade is prefix-closed. -/
lemma prefixClosed_cascSet (L : ℕ) (T : BranchingProcess.Word N → Prop) :
    PrefixClosed (cascSet L T) := by
  rintro x y hxy ⟨w, hw, hy⟩
  exact ⟨w, hw, hxy.trans hy⟩

/-- Every vertex keeps a copy. -/
lemma cascSet_cascWord (L : ℕ) {T : BranchingProcess.Word N → Prop}
    {w : BranchingProcess.Word N} (hw : T w) : cascSet L T (cascWord L w) :=
  ⟨w, hw, List.prefix_refl _⟩

/-- A prefix of an encoded word lies below the copy of a prefix of the word, within
`L - 1` of it. -/
lemma exists_prefix_cascWord_near (L : ℕ) :
    ∀ (w : BranchingProcess.Word N) (x : Word), x <+: cascWord L w →
      ∃ w' : BranchingProcess.Word N, w' <+: w ∧ cascWord L w' <+: x ∧
        x.length ≤ L * w'.length + (L - 1) := by
  intro w
  induction w with
  | nil =>
      intro x hx
      rw [cascWord_nil, List.prefix_nil] at hx
      exact ⟨[], List.prefix_refl _, by simp [hx], by simp [hx]⟩
  | cons j w ih =>
      intro x hx
      rw [cascWord_cons] at hx
      by_cases hj : bitsL L j <+: x
      · obtain ⟨x', rfl⟩ := hj
        rw [List.prefix_append_right_inj] at hx
        obtain ⟨w', hw', hx', hlen⟩ := ih x' hx
        refine ⟨j :: w', List.cons_prefix_cons.mpr ⟨rfl, hw'⟩, ?_, ?_⟩
        · rw [cascWord_cons]
          exact (List.prefix_append_right_inj _).mpr hx'
        · simp only [List.length_append, length_bitsL, List.length_cons, Nat.mul_succ]
          omega
      · have hxj : x <+: bitsL L j :=
          (List.prefix_or_prefix_of_prefix hx (List.prefix_append _ _)).resolve_right hj
        have hlt : x.length < L := by
          refine lt_of_le_of_ne (by simpa using hxj.length_le) fun h => hj ?_
          rw [hxj.eq_of_length (by simpa using h)]
        exact ⟨[], List.nil_prefix, List.nil_prefix, by simp; omega⟩

/-- **Every cascade vertex lies within `L - 1` of a copy**, the copy of a prefix of the
word it lies under. -/
theorem exists_copy_near (L : ℕ) {T : BranchingProcess.Word N → Prop} (hT : PrefixClosedN T)
    {x : Word} (hx : cascSet L T x) :
    ∃ w, T w ∧ cascWord L w <+: x ∧ treeDist (cascWord L w) x ≤ L - 1 := by
  obtain ⟨w, hw, hxw⟩ := hx
  obtain ⟨w', hw', hx', hlen⟩ := exists_prefix_cascWord_near L w x hxw
  refine ⟨w', hT hw' hw, hx', ?_⟩
  rw [treeDist_of_prefix hx', length_cascWord]
  omega

/-! ### The parent-child graph of a set of words over `Fin N` -/

/-- The parent-child graph on a set of words over `Fin N`: two vertices are adjacent
when they are at distance one, the `N`-ary counterpart of `wordGraph`. -/
def wordGraphN (T : BranchingProcess.Word N → Prop) :
    SimpleGraph {w : BranchingProcess.Word N // T w} where
  Adj u v := BranchingProcess.treeDist u.1 v.1 = 1
  symm := ⟨fun {_ _} h => by rwa [BranchingProcess.treeDist_comm]⟩
  loopless := ⟨fun {u} h => by
    rw [BranchingProcess.treeDist_self] at h
    exact absurd h (by omega)⟩

variable {T : BranchingProcess.Word N → Prop}

@[simp] lemma wordGraphN_adj {u v : {w : BranchingProcess.Word N // T w}} :
    (wordGraphN T).Adj u v ↔ BranchingProcess.treeDist u.1 v.1 = 1 := Iff.rfl

/-- A vertex and its child are adjacent. -/
lemma wordGraphN_adj_concat {u v : {w : BranchingProcess.Word N // T w}} {j : Fin N}
    (h : v.1 = u.1 ++ [j]) : (wordGraphN T).Adj u v := by
  rw [wordGraphN_adj, h]
  exact BranchingProcess.treeDist_append_singleton u.1 j

/-- Walking up to an ancestor: a vertex and a prefix of it are joined by a walk of length
the difference of the depths. -/
lemma exists_walkN_of_prefix (hT : PrefixClosedN T) :
    ∀ (n : ℕ) (u v : {w : BranchingProcess.Word N // T w}), u.1 <+: v.1 →
      v.1.length - u.1.length = n → ∃ p : (wordGraphN T).Walk u v, p.length = n := by
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
      obtain ⟨j, s, hs⟩ : ∃ (j : Fin N) (s : BranchingProcess.Word N), v.1 = s ++ [j] := by
        rcases List.eq_nil_or_concat v.1 with h | ⟨s, j, hs⟩
        · exact absurd h hvne
        · exact ⟨j, s, by rw [hs]; simp⟩
      have hsT : T s := hT (hs ▸ List.prefix_append s [j]) v.2
      have hslen : s.length + 1 = v.1.length := by
        rw [hs]; simp
      have hus : u.1 <+: s := by
        refine List.prefix_of_prefix_length_le huv (hs ▸ List.prefix_append s [j]) ?_
        omega
      obtain ⟨p, hp⟩ := ih u ⟨s, hsT⟩ hus (by simp only; omega)
      exact ⟨p.concat (wordGraphN_adj_concat (T := T) (u := ⟨s, hsT⟩) (v := v) hs),
        by rw [Walk.length_concat, hp]⟩

/-- `BranchingProcess.treeDist` is subadditive along a walk: every edge changes it by at
most one. -/
lemma treeDistN_le_walk_length {u v : {w : BranchingProcess.Word N // T w}}
    (p : (wordGraphN T).Walk u v) : BranchingProcess.treeDist u.1 v.1 ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab _ ih =>
      have h1 : BranchingProcess.treeDist a.1 b.1 = 1 := hab
      have := BranchingProcess.treeDist_triangle a.1 b.1 c.1
      simp only [Walk.length_cons]
      omega

/-- **The graph metric of `wordGraphN` is `BranchingProcess.treeDist`.** -/
theorem wordGraphN_dist (hT : PrefixClosedN T) (u v : {w : BranchingProcess.Word N // T w}) :
    (wordGraphN T).dist u v = BranchingProcess.treeDist u.1 v.1 := by
  have hw : T (BranchingProcess.wedge u.1 v.1) := hT (BranchingProcess.wedge_prefix_left _ _) u.2
  obtain ⟨p, hp⟩ := exists_walkN_of_prefix hT
    (u.1.length - (BranchingProcess.wedge u.1 v.1).length)
    ⟨BranchingProcess.wedge u.1 v.1, hw⟩ u (BranchingProcess.wedge_prefix_left u.1 v.1) rfl
  obtain ⟨q, hq⟩ := exists_walkN_of_prefix hT
    (v.1.length - (BranchingProcess.wedge u.1 v.1).length)
    ⟨BranchingProcess.wedge u.1 v.1, hw⟩ v (BranchingProcess.wedge_prefix_right u.1 v.1) rfl
  have hle : (wordGraphN T).dist u v ≤ BranchingProcess.treeDist u.1 v.1 := by
    have h := dist_le (p.reverse.append q)
    rw [Walk.length_append, Walk.length_reverse, hp, hq] at h
    have h1 := BranchingProcess.wedge_length_le_left u.1 v.1
    have h2 := BranchingProcess.wedge_length_le_right u.1 v.1
    have h3 := BranchingProcess.treeDist_add u.1 v.1
    omega
  refine le_antisymm hle ?_
  have hr : (wordGraphN T).Reachable u v := ⟨p.reverse.append q⟩
  obtain ⟨r, hr'⟩ := hr.exists_walk_length_eq_dist
  have := treeDistN_le_walk_length r
  omega

/-! ### `thm:bushy`, the quasi-isometry -/

/-- The cascade encoding as a map of vertex sets: every vertex goes to its copy. -/
def cascMap (L : ℕ) (T : BranchingProcess.Word N → Prop) :
    {w : BranchingProcess.Word N // T w} → {x : Word // cascSet L T x} :=
  fun w => ⟨cascWord L w.1, cascSet_cascWord L w.2⟩

@[simp] lemma cascMap_val (L : ℕ) (T : BranchingProcess.Word N → Prop)
    (w : {w : BranchingProcess.Word N // T w}) : (cascMap L T w).1 = cascWord L w.1 := rfl

/-- **`thm:bushy` (the coding in its proof).** Replacing every split of a prefix-closed
set of words over `Fin N` by its cascade of depth `L`, `N ≤ 2^L`, is an
`L`-quasi-isometry of the parent-child graphs in the sense of `def:qi`: copies satisfy
`d ≤ d' ≤ L d`, and every cascade vertex lies within `L - 1` of a copy. -/
theorem cascade_isQIWith {L : ℕ} (hN : N ≤ 2 ^ L) (hL : 1 ≤ L) (hT : PrefixClosedN T) :
    BranchingProcess.IsQIWith L (wordGraphN T) (wordGraph (cascSet L T)) (cascMap L T) where
  upper x y := by
    rw [wordGraph_dist (prefixClosed_cascSet L T), wordGraphN_dist hT]
    exact (treeDist_cascWord_le L x.1 y.1).trans (Nat.le_add_right _ _)
  lower x y := by
    rw [wordGraph_dist (prefixClosed_cascSet L T), wordGraphN_dist hT]
    have h1 := le_treeDist_cascWord hN hL x.1 y.1
    have h2 := Nat.le_mul_of_pos_left (treeDist (cascWord L x.1) (cascWord L y.1)) hL
    simp only [cascMap_val] at h2 ⊢
    omega
  dense y' := by
    obtain ⟨w, hw, -, hdist⟩ := exists_copy_near L hT y'.2
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [wordGraph_dist (prefixClosed_cascSet L T)]
    simp only [cascMap_val]
    omega

/-- **`thm:bushy` (the coding in its proof), as quasi-isometry of graphs.** -/
theorem cascade_quasiIsometric {L : ℕ} (hN : N ≤ 2 ^ L) (hL : 1 ≤ L) (hT : PrefixClosedN T) :
    BranchingProcess.QuasiIsometric (wordGraphN T) (wordGraph (cascSet L T)) :=
  ⟨L, cascMap L T, cascade_isQIWith hN hL hT⟩

/-- **`thm:bushy` (the coding in its proof), at the depth `⌈log₂ N⌉`**: for `2 ≤ N`, the
cascade of depth `Nat.clog 2 N` is a `Nat.clog 2 N`-quasi-isometry, the constant being
at most the paper's `1 + ⌈log₂ J⌉`. -/
theorem cascade_isQIWith_clog (hN : 2 ≤ N) (hT : PrefixClosedN T) :
    BranchingProcess.IsQIWith (Nat.clog 2 N) (wordGraphN T) (wordGraph (cascSet (Nat.clog 2 N) T))
      (cascMap (Nat.clog 2 N) T) :=
  cascade_isQIWith (Nat.le_pow_clog (by norm_num) N)
    (Nat.clog_pos (by norm_num) hN) hT

end ChainClasses
