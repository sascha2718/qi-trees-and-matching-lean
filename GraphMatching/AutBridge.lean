/-
The bridge of design decision D4 (`graph_matching_selfcontained.tex`, `sec:setup`): the
swap group `Aut h` is the automorphism group of the rooted binary tree as a graph.

The tree is the graph on the finite binary words whose edges join a word to its one-letter
extensions, truncated at height `h` by restricting to words of length at most `h`.  A swap
element acts on words letter by letter, the swap bit deciding the image subtree, and the
action is a root-fixing graph automorphism; conversely every root-fixing graph automorphism
preserves lengths and parents, hence descends the levels, and is the action of a unique
swap element.  The matching relations then quantify over graph automorphisms exactly as the
paper states them: `x ≈_h y` holds precisely when some root-fixing graph automorphism `g`
has `x(g v)` compatible with `y(v)` at every vertex, and the infinite matching of `InfMatch`
is one root-fixing automorphism of the infinite tree.

* `treeGraphInf`, `treeGraph`: the infinite tree and its height-`h` truncation as graphs.
* `autAct`, `autInv`: the action of a swap element on words and the inverse element, with
  `autInv_autAct`, `autAct_autInv`, `autAct_append_single`, `autAct_length`.
* `autIso`, `autIso_root`: **the action is a root-fixing graph automorphism**.
* `aut_ext`: the action determines the swap element.
* `exists_aut_of`: **every root-fixing graph automorphism is an action**: a length- and
  child-preserving injection of the truncated tree is the action of a swap element.
* `iso_child`, `exists_aut_of_iso`: the properties hold for every root-fixing graph
  automorphism.
* `fullMatchesA_iff_coord`, `fullSim_iff_graphAut`: **`x ≈_h y` over graph
  automorphisms**, in the form of the paper.
* `infMatch_iff_graphAut`: **the infinite matching over one automorphism of the infinite
  tree**.
* `exists_infinite_tree_matching_graphAut`: the infinite-tree case of `thm:matching` with
  the conclusion quantified over graph automorphisms of the infinite tree.
-/
import GraphMatching.Kolmogorov
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace GraphMatching

open scoped Classical
open MeasureTheory

universe u
variable {V : Type u}

/-! ### The binary tree as a graph -/

/-- The infinite rooted binary tree as a graph: the finite binary words, a word adjacent
to its one-letter extensions. -/
def treeGraphInf : SimpleGraph (List Bool) where
  Adj s t := (∃ c, t = s ++ [c]) ∨ (∃ c, s = t ++ [c])
  symm := by
    constructor
    intro s t h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := by
    constructor
    intro s h
    rcases h with ⟨c, hc⟩ | ⟨c, hc⟩ <;>
      exact absurd (congrArg List.length hc) (by simp)

/-- The tree truncated at height `h`: the induced graph on the words of length at
most `h`. -/
def treeGraph (h : ℕ) : SimpleGraph {s : List Bool // s.length ≤ h} :=
  SimpleGraph.comap Subtype.val treeGraphInf

/-- The root of the truncated tree. -/
def treeRoot (h : ℕ) : {s : List Bool // s.length ≤ h} := ⟨[], by simp⟩

/-! ### The action of the swap group on words -/

/-- **The action of a swap element on words**: the swap bit decides the image subtree, and
the subtree element acts on the rest. -/
def autAct : (h : ℕ) → Aut h → List Bool → List Bool
  | 0, _, s => s
  | _ + 1, _, [] => []
  | h + 1, π, c :: t => xor c π.1 :: autAct h (bif c then π.2.2 else π.2.1) t

/-- The inverse swap element. -/
def autInv : (h : ℕ) → Aut h → Aut h
  | 0, _ => ()
  | h + 1, π => (π.1, autInv h (bif π.1 then π.2.2 else π.2.1),
      autInv h (bif π.1 then π.2.1 else π.2.2))

@[simp] lemma autAct_nil : ∀ (h : ℕ) (π : Aut h), autAct h π [] = []
  | 0, _ => rfl
  | _ + 1, _ => rfl

@[simp] lemma autAct_length : ∀ (h : ℕ) (π : Aut h) (s : List Bool),
    (autAct h π s).length = s.length
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | h + 1, π, c :: t => by
      show (xor c π.1 :: autAct h (bif c then π.2.2 else π.2.1) t).length = (c :: t).length
      simp [autAct_length h]

/-- The inverse element undoes the action. -/
lemma autInv_autAct : ∀ (h : ℕ) (π : Aut h) (s : List Bool),
    autAct h (autInv h π) (autAct h π s) = s
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | h + 1, π, c :: t => by
      show xor (xor c π.1) π.1
          :: autAct h (bif xor c π.1 then autInv h (bif π.1 then π.2.1 else π.2.2)
              else autInv h (bif π.1 then π.2.2 else π.2.1))
            (autAct h (bif c then π.2.2 else π.2.1) t)
        = c :: t
      have hbit : xor (xor c π.1) π.1 = c := by cases c <;> cases π.1 <;> rfl
      have hsel : (bif xor c π.1 then autInv h (bif π.1 then π.2.1 else π.2.2)
          else autInv h (bif π.1 then π.2.2 else π.2.1))
            = autInv h (bif c then π.2.2 else π.2.1) := by
        cases c <;> cases π.1 <;> rfl
      rw [hbit, hsel, autInv_autAct h]

/-- The action undoes the inverse element. -/
lemma autAct_autInv : ∀ (h : ℕ) (π : Aut h) (s : List Bool),
    autAct h π (autAct h (autInv h π) s) = s
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | h + 1, π, c :: t => by
      show xor (xor c π.1) π.1
          :: autAct h (bif xor c π.1 then π.2.2 else π.2.1)
            (autAct h (bif c then autInv h (bif π.1 then π.2.1 else π.2.2)
              else autInv h (bif π.1 then π.2.2 else π.2.1)) t)
        = c :: t
      have hbit : xor (xor c π.1) π.1 = c := by cases c <;> cases π.1 <;> rfl
      have hsel : (bif c then autInv h (bif π.1 then π.2.1 else π.2.2)
          else autInv h (bif π.1 then π.2.2 else π.2.1))
            = autInv h (bif xor c π.1 then π.2.2 else π.2.1) := by
        cases c <;> cases π.1 <;> rfl
      rw [hbit, hsel, autAct_autInv h]

/-- The action sends a one-letter extension to a one-letter extension. -/
lemma autAct_append_single : ∀ (h : ℕ) (π : Aut h) (s : List Bool) (c : Bool),
    ∃ c', autAct h π (s ++ [c]) = autAct h π s ++ [c']
  | 0, _, s, c => ⟨c, rfl⟩
  | _ + 1, π, [], c => ⟨xor c π.1, by simp [autAct]⟩
  | h + 1, π, d :: u, c => by
      obtain ⟨c', hc'⟩ := autAct_append_single h (bif d then π.2.2 else π.2.1) u c
      exact ⟨c', by simp only [List.cons_append, autAct, hc']⟩

/-! ### The action is a graph automorphism -/

/-- The action preserves adjacency. -/
lemma autAct_adj (h : ℕ) (π : Aut h) {s t : List Bool} (hadj : treeGraphInf.Adj s t) :
    treeGraphInf.Adj (autAct h π s) (autAct h π t) := by
  rcases hadj with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨c', hc'⟩ := autAct_append_single h π s c
    exact Or.inl ⟨c', hc'⟩
  · obtain ⟨c', hc'⟩ := autAct_append_single h π t c
    exact Or.inr ⟨c', hc'⟩

/-- **The action is a root-fixing graph automorphism of the truncated tree.** -/
def autIso (h : ℕ) (π : Aut h) : treeGraph h ≃g treeGraph h where
  toEquiv :=
    { toFun := fun v => ⟨autAct h π v.1, by rw [autAct_length]; exact v.2⟩
      invFun := fun v => ⟨autAct h (autInv h π) v.1, by rw [autAct_length]; exact v.2⟩
      left_inv := fun v => Subtype.ext (autInv_autAct h π v.1)
      right_inv := fun v => Subtype.ext (autAct_autInv h π v.1) }
  map_rel_iff' := by
    intro u v
    show treeGraphInf.Adj (autAct h π u.1) (autAct h π v.1) ↔ treeGraphInf.Adj u.1 v.1
    constructor
    · intro hadj
      have h1 := autAct_adj h (autInv h π) hadj
      rwa [autInv_autAct, autInv_autAct] at h1
    · exact autAct_adj h π

@[simp] lemma autIso_apply (h : ℕ) (π : Aut h) (v : {s : List Bool // s.length ≤ h}) :
    (autIso h π v).1 = autAct h π v.1 := rfl

lemma autIso_root (h : ℕ) (π : Aut h) : autIso h π (treeRoot h) = treeRoot h :=
  Subtype.ext (autAct_nil h π)

/-! ### The action determines the swap element -/

/-- Two swap elements with the same action on the truncated tree are equal. -/
lemma aut_ext : ∀ (h : ℕ) (π π' : Aut h),
    (∀ s : List Bool, s.length ≤ h → autAct h π s = autAct h π' s) → π = π'
  | 0, _, _, _ => rfl
  | h + 1, π, π', hact => by
      obtain ⟨b, π₀, π₁⟩ := π
      obtain ⟨b', π₀', π₁'⟩ := π'
      have hb : b = b' := by
        have h1 := hact [false] (by simp)
        simpa [autAct] using h1
      subst hb
      have h₀ : π₀ = π₀' := aut_ext h π₀ π₀' (fun t ht => by
        have h1 := hact (false :: t) (by simpa using Nat.succ_le_succ ht)
        simpa [autAct] using h1)
      have h₁ : π₁ = π₁' := aut_ext h π₁ π₁' (fun t ht => by
        have h1 := hact (true :: t) (by simpa using Nat.succ_le_succ ht)
        simpa [autAct] using h1)
      rw [h₀, h₁]

/-! ### Every root-fixing graph automorphism is an action -/

/-- **The converse construction**: a map of words that fixes the root, sends one-letter
extensions to one-letter extensions below height `h`, and is injective below height `h`,
is the action of a swap element. -/
lemma exists_aut_of : ∀ (h : ℕ) (f : List Bool → List Bool),
    f [] = [] →
    (∀ (s : List Bool) (c : Bool), s.length + 1 ≤ h → ∃ c', f (s ++ [c]) = f s ++ [c']) →
    (∀ s t : List Bool, s.length ≤ h → t.length ≤ h → f s = f t → s = t) →
    ∃ π : Aut h, ∀ s : List Bool, s.length ≤ h → autAct h π s = f s
  | 0, f, hnil, _, _ => by
      refine ⟨(), fun s hs => ?_⟩
      obtain rfl : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hs)
      rw [hnil]
      rfl
  | h + 1, f, hnil, hchild, hinj => by
      obtain ⟨b, hb⟩ := hchild [] false (by simp)
      obtain ⟨b', hb'⟩ := hchild [] true (by simp)
      rw [hnil] at hb hb'
      simp only [List.nil_append] at hb hb'
      have hbb' : b' = !b := by
        by_contra hne
        have heq : b' = b := by cases b <;> cases b' <;> simp_all
        rw [heq] at hb'
        have := hinj [false] [true] (by simp) (by simp) (hb.trans hb'.symm)
        simp at this
      have hhead : ∀ (c : Bool) (t : List Bool), t.length ≤ h →
          ∃ u, f (c :: t) = xor c b :: u := by
        intro c t
        induction t using List.reverseRecOn with
        | nil =>
            intro _
            cases c
            · exact ⟨[], by simpa using hb⟩
            · exact ⟨[], by simp [hb', hbb']⟩
        | append_singleton u d ih =>
            intro hlen
            simp only [List.length_append, List.length_singleton] at hlen
            obtain ⟨v, hv⟩ := ih (by omega)
            obtain ⟨d', hd'⟩ := hchild (c :: u) d (by simp; omega)
            refine ⟨v ++ [d'], ?_⟩
            rw [show c :: (u ++ [d]) = (c :: u) ++ [d] from rfl, hd', hv]
            rfl
      -- the two subtree maps
      have hsub : ∀ c : Bool, ∃ π : Aut h, ∀ t : List Bool, t.length ≤ h →
          autAct h π t = (f (c :: t)).tail := by
        intro c
        refine exists_aut_of h (fun t => (f (c :: t)).tail) ?_ ?_ ?_
        · obtain ⟨u, hu⟩ := hhead c [] (by simp)
          rw [hu]
          obtain ⟨w, hw⟩ : ∃ w, f (c :: ([] : List Bool)) = [xor c b] ++ w := ⟨u, hu⟩
          -- `f [c]` has length 1: it is `f [] ++ [c']` for some `c'`
          obtain ⟨c', hc'⟩ := hchild [] c (by simp)
          rw [hnil] at hc'
          simp only [List.nil_append] at hc'
          rw [hc'] at hu
          have : u = [] := by
            have := congrArg List.tail hu
            simpa using this.symm
          simp [this]
        · intro s c' hs
          obtain ⟨e, he⟩ := hchild (c :: s) c' (by simp; omega)
          obtain ⟨u, hu⟩ := hhead c s (by omega)
          rw [show c :: (s ++ [c']) = (c :: s) ++ [c'] from rfl, he, hu]
          exact ⟨e, rfl⟩
        · intro s t hs ht heq
          obtain ⟨u, hu⟩ := hhead c s (by omega)
          obtain ⟨v, hv⟩ := hhead c t (by omega)
          have h1 : f (c :: s) = f (c :: t) := by
            rw [hu, hv]
            rw [hu, hv] at heq
            simpa using heq
          have := hinj (c :: s) (c :: t) (by simp; omega) (by simp; omega) h1
          simpa using this
      obtain ⟨π₀, hπ₀⟩ := hsub false
      obtain ⟨π₁, hπ₁⟩ := hsub true
      refine ⟨(b, π₀, π₁), fun s hs => ?_⟩
      match s with
      | [] => rw [hnil]; rfl
      | c :: t =>
          have ht : t.length ≤ h := by
            simp only [List.length_cons] at hs
            omega
          obtain ⟨u, hu⟩ := hhead c t ht
          show xor c b :: autAct h (bif c then π₁ else π₀) t = f (c :: t)
          rw [hu]
          cases c
          · rw [show (bif false then π₁ else π₀) = π₀ from rfl, hπ₀ t ht, hu]
            rfl
          · rw [show (bif true then π₁ else π₀) = π₁ from rfl, hπ₁ t ht, hu]
            rfl

/-! ### Root-fixing graph automorphisms preserve children and lengths -/

/-- A root-fixing automorphism of the truncated tree sends the child of a vertex to a
child of its image. -/
lemma iso_child {h : ℕ} (g : treeGraph h ≃g treeGraph h)
    (hroot : g (treeRoot h) = treeRoot h) :
    ∀ (n : ℕ) (s : List Bool) (hs : s.length ≤ h) (c : Bool) (hsc : (s ++ [c]).length ≤ h),
      s.length = n → ∃ c', (g ⟨s ++ [c], hsc⟩).1 = (g ⟨s, hs⟩).1 ++ [c'] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs c hsc hn
    have hadj : (treeGraph h).Adj ⟨s ++ [c], hsc⟩ ⟨s, hs⟩ := Or.inr ⟨c, rfl⟩
    have hmap : (treeGraph h).Adj (g ⟨s ++ [c], hsc⟩) (g ⟨s, hs⟩) := g.map_rel_iff.mpr hadj
    rcases hmap with ⟨c', hc'⟩ | ⟨c', hc'⟩
    · exfalso
      match n, hn with
      | 0, hn =>
          obtain rfl : s = [] := List.eq_nil_of_length_eq_zero hn
          have hrt : (⟨[], hs⟩ : {s : List Bool // s.length ≤ h}) = treeRoot h := rfl
          rw [hrt, hroot] at hc'
          exact absurd (congrArg List.length hc') (by simp [treeRoot])
      | m + 1, hn =>
          obtain ⟨s', d, rfl⟩ : ∃ s' d, s = s' ++ [d] := by
            rcases List.eq_nil_or_concat s with rfl | ⟨s', d, rfl⟩
            · simp at hn
            · exact ⟨s', d, by simp⟩
          have hs' : s'.length ≤ h := by
            simp only [List.length_append, List.length_singleton] at hs
            omega
          have hm : s'.length = m := by
            simp only [List.length_append, List.length_singleton] at hn
            omega
          obtain ⟨d', hd'⟩ := ih m (by omega) s' hs' d hs hm
          rw [hd'] at hc'
          have hlen : (g ⟨s', hs'⟩).1.length = (g ⟨(s' ++ [d]) ++ [c], hsc⟩).1.length := by
            have := congrArg List.length hc'
            simp only [List.length_append, List.length_singleton] at this
            omega
          obtain ⟨heq, -⟩ := List.append_inj hc' (by rw [hlen])
          have hv := g.injective (Subtype.ext heq)
          have := congrArg (fun v => (Subtype.val v : List Bool).length) hv
          simp at this
    · exact ⟨c', hc'⟩

/-- **Every root-fixing graph automorphism of the truncated tree is the action of a swap
element.** -/
lemma exists_aut_of_iso {h : ℕ} (g : treeGraph h ≃g treeGraph h)
    (hroot : g (treeRoot h) = treeRoot h) :
    ∃ π : Aut h, ∀ (s : List Bool) (hs : s.length ≤ h), autAct h π s = (g ⟨s, hs⟩).1 := by
  classical
  obtain ⟨π, hπ⟩ := exists_aut_of h
    (fun s => if hs : s.length ≤ h then (g ⟨s, hs⟩).1 else s)
    (by
      rw [dite_eq_left (by simp : ([] : List Bool).length ≤ h)]
      have hrt : (⟨[], by simp⟩ : {s : List Bool // s.length ≤ h}) = treeRoot h := rfl
      rw [hrt, hroot]
      rfl)
    (fun s c hsc => by
      have hs : s.length ≤ h := by omega
      have hsc' : (s ++ [c]).length ≤ h := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [dite_eq_left hsc', dite_eq_left hs]
      exact iso_child g hroot s.length s hs c hsc' rfl)
    (fun s t hs ht heq => by
      rw [dite_eq_left hs, dite_eq_left ht] at heq
      have := g.injective (Subtype.ext heq)
      exact congrArg Subtype.val this)
  refine ⟨π, fun s hs => ?_⟩
  rw [hπ s hs, dite_eq_left hs]

/-! ### The matching relations over graph automorphisms -/

/-- The full matching under a swap element, read through the coordinates: `x` at `s` is
compatible with `y` at the image of `s` under the action. -/
lemma fullMatchesA_iff_coord (R₀ : V → V → Prop) :
    ∀ (h : ℕ) (π : Aut h) (x y : FullLab V h),
      fullMatchesA R₀ h π x y ↔
        ∀ s : List Bool, s.length ≤ h → R₀ (coord h x s) (coord h y (autAct h π s))
  | 0, π, x, y => by
      constructor
      · intro hm s _
        exact hm
      · intro hcoord
        exact hcoord [] (by simp)
  | h + 1, π, x, y => by
      obtain ⟨b, π₀, π₁⟩ := π
      obtain ⟨a, x₀, x₁⟩ := x
      obtain ⟨a', y₀, y₁⟩ := y
      constructor
      · rintro ⟨hroot, h₀, h₁⟩ s hs
        match s with
        | [] => exact hroot
        | false :: t =>
            have ht : t.length ≤ h := by
              simp only [List.length_cons] at hs
              omega
            have := (fullMatchesA_iff_coord R₀ h π₀ x₀ (bif b then y₁ else y₀)).mp h₀ t ht
            cases b <;> simpa [autAct, coord] using this
        | true :: t =>
            have ht : t.length ≤ h := by
              simp only [List.length_cons] at hs
              omega
            have := (fullMatchesA_iff_coord R₀ h π₁ x₁ (bif b then y₀ else y₁)).mp h₁ t ht
            cases b <;> simpa [autAct, coord] using this
      · intro hcoord
        refine ⟨hcoord [] (by simp), ?_, ?_⟩
        · refine (fullMatchesA_iff_coord R₀ h π₀ x₀ (bif b then y₁ else y₀)).mpr
            fun t ht => ?_
          have := hcoord (false :: t) (by simpa using Nat.succ_le_succ ht)
          cases b <;> simpa [autAct, coord] using this
        · refine (fullMatchesA_iff_coord R₀ h π₁ x₁ (bif b then y₀ else y₁)).mpr
            fun t ht => ?_
          have := hcoord (true :: t) (by simpa using Nat.succ_le_succ ht)
          cases b <;> simpa [autAct, coord] using this

/-- **`x ≈_h y` over graph automorphisms** (`sec:setup`): the full relation holds exactly
when some root-fixing graph automorphism `g` of the truncated tree has `x` at `g v`
compatible with `y` at `v`, at every vertex simultaneously. -/
theorem fullSim_iff_graphAut (R₀ : V → V → Prop) (h : ℕ) (x y : FullLab V h) :
    fullSim R₀ h x y ↔
      ∃ g : treeGraph h ≃g treeGraph h, g (treeRoot h) = treeRoot h ∧
        ∀ v : {s : List Bool // s.length ≤ h}, R₀ (coord h x (g v).1) (coord h y v.1) := by
  constructor
  · rintro ⟨π, hm⟩
    refine ⟨autIso h (autInv h π), autIso_root h _, fun v => ?_⟩
    have h1 := (fullMatchesA_iff_coord R₀ h π x y).mp hm (autAct h (autInv h π) v.1)
      (by rw [autAct_length]; exact v.2)
    rw [autAct_autInv] at h1
    simpa using h1
  · rintro ⟨g, hroot, hg⟩
    obtain ⟨π', hπ'⟩ := exists_aut_of_iso g hroot
    refine ⟨autInv h π', (fullMatchesA_iff_coord R₀ h _ x y).mpr fun s hs => ?_⟩
    have hu : (autAct h (autInv h π') s).length ≤ h := by
      rw [autAct_length]; exact hs
    have h1 := hg ⟨autAct h (autInv h π') s, hu⟩
    rw [← hπ' _ hu, autAct_autInv] at h1
    exact h1

/-! ### Stability of the action under restriction -/

/-- The restricted swap element acts as the original on short words. -/
lemma autAct_restrictAut : ∀ (h : ℕ) (π : Aut (h + 1)) (s : List Bool), s.length ≤ h →
    autAct h (restrictAut h π) s = autAct (h + 1) π s
  | 0, _, s, hs => by
      obtain rfl : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hs)
      rfl
  | _ + 1, _, [], _ => rfl
  | h + 1, π, c :: t, hs => by
      have ht : t.length ≤ h := by
        simp only [List.length_cons] at hs
        omega
      cases c
      · show xor false π.1 :: autAct h (restrictAut h π.2.1) t
            = xor false π.1 :: autAct (h + 1) π.2.1 t
        rw [autAct_restrictAut h π.2.1 t ht]
      · show xor true π.1 :: autAct h (restrictAut h π.2.2) t
            = xor true π.1 :: autAct (h + 1) π.2.2 t
        rw [autAct_restrictAut h π.2.2 t ht]

/-- In a compatible family, the action on a word is the same at every sufficient level. -/
lemma autAct_family_stable (σ : (h : ℕ) → Aut h)
    (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h) :
    ∀ (h : ℕ) (s : List Bool), s.length ≤ h →
      autAct h (σ h) s = autAct s.length (σ s.length) s := by
  intro h
  induction h with
  | zero =>
      intro s hs
      obtain rfl : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hs)
      rfl
  | succ h ih =>
      intro s hs
      rcases Nat.lt_or_ge s.length (h + 1) with hlt | hge
      · have hle : s.length ≤ h := Nat.lt_succ_iff.mp hlt
        rw [← ih s hle, ← hσ h, autAct_restrictAut h _ s hle]
      · have hl : s.length = h + 1 := le_antisymm hs hge
        rw [hl]

/-- Restriction commutes with inversion. -/
lemma restrictAut_autInv (h : ℕ) (π : Aut (h + 1)) :
    restrictAut h (autInv (h + 1) π) = autInv h (restrictAut h π) := by
  refine aut_ext h _ _ (fun s hs => ?_)
  rw [autAct_restrictAut h _ s hs]
  have hy : (autAct (h + 1) (autInv (h + 1) π) s).length ≤ h := by
    rw [autAct_length]; exact hs
  calc autAct (h + 1) (autInv (h + 1) π) s
      = autAct h (autInv h (restrictAut h π))
          (autAct h (restrictAut h π) (autAct (h + 1) (autInv (h + 1) π) s)) :=
        (autInv_autAct h _ _).symm
    _ = autAct h (autInv h (restrictAut h π)) s := by
        rw [autAct_restrictAut h π _ hy, autAct_autInv]

/-- The coordinates of a restricted labelling agree with the original on short words. -/
lemma coord_restrictLab : ∀ (h : ℕ) (x : FullLab V (h + 1)) (s : List Bool),
    s.length ≤ h → coord h (restrictLab h x) s = coord (h + 1) x s
  | 0, x, s, hs => by
      obtain rfl : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hs)
      rfl
  | _ + 1, _, [], _ => rfl
  | h + 1, x, false :: t, hs => by
      have ht : t.length ≤ h := by
        simp only [List.length_cons] at hs
        omega
      exact coord_restrictLab h x.2.1 t ht
  | h + 1, x, true :: t, hs => by
      have ht : t.length ≤ h := by
        simp only [List.length_cons] at hs
        omega
      exact coord_restrictLab h x.2.2 t ht

/-- In a compatible family of labellings, the coordinate at a word is the same at every
sufficient level. -/
lemma coord_family_stable (X : (h : ℕ) → FullLab V h)
    (hX : ∀ h, restrictLab h (X (h + 1)) = X h) :
    ∀ (h : ℕ) (s : List Bool), s.length ≤ h →
      coord h (X h) s = coord s.length (X s.length) s := by
  intro h
  induction h with
  | zero =>
      intro s hs
      obtain rfl : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hs)
      rfl
  | succ h ih =>
      intro s hs
      rcases Nat.lt_or_ge s.length (h + 1) with hlt | hge
      · have hle : s.length ≤ h := Nat.lt_succ_iff.mp hlt
        rw [← ih s hle, ← hX h, coord_restrictLab h _ s hle]
      · have hl : s.length = h + 1 := le_antisymm hs hge
        rw [hl]

/-! ### Compatible families as automorphisms of the infinite tree -/

/-- The level-wise action of a family of swap elements on the infinite tree. -/
def famAct (σ : (h : ℕ) → Aut h) (s : List Bool) : List Bool :=
  autAct s.length (σ s.length) s

@[simp] lemma famAct_length (σ : (h : ℕ) → Aut h) (s : List Bool) :
    (famAct σ s).length = s.length := autAct_length _ _ _

lemma famAct_leftInv (σ : (h : ℕ) → Aut h) (s : List Bool) :
    famAct (fun h => autInv h (σ h)) (famAct σ s) = s := by
  unfold famAct
  rw [autAct_length]
  exact autInv_autAct _ _ _

lemma famAct_rightInv (σ : (h : ℕ) → Aut h) (s : List Bool) :
    famAct σ (famAct (fun h => autInv h (σ h)) s) = s := by
  unfold famAct
  rw [autAct_length]
  exact autAct_autInv _ _ _

/-- A compatible family sends the child of a word to a child of its image. -/
lemma famAct_append_single (σ : (h : ℕ) → Aut h)
    (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h) (s : List Bool) (c : Bool) :
    ∃ c', famAct σ (s ++ [c]) = famAct σ s ++ [c'] := by
  obtain ⟨c', hc'⟩ := autAct_append_single (s ++ [c]).length (σ (s ++ [c]).length) s c
  refine ⟨c', ?_⟩
  show autAct (s ++ [c]).length (σ (s ++ [c]).length) (s ++ [c]) = famAct σ s ++ [c']
  have hle : s.length ≤ (s ++ [c]).length := by simp
  rw [hc', autAct_family_stable σ hσ _ s hle]
  rfl

/-- A compatible family preserves adjacency in the infinite tree. -/
lemma famAct_adj (σ : (h : ℕ) → Aut h) (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h)
    {s t : List Bool} (hadj : treeGraphInf.Adj s t) :
    treeGraphInf.Adj (famAct σ s) (famAct σ t) := by
  rcases hadj with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨c', hc'⟩ := famAct_append_single σ hσ s c
    exact Or.inl ⟨c', hc'⟩
  · obtain ⟨c', hc'⟩ := famAct_append_single σ hσ t c
    exact Or.inr ⟨c', hc'⟩

/-- The compatibility of the inverse family. -/
lemma restrictAut_autInv_family (σ : (h : ℕ) → Aut h)
    (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h) (h : ℕ) :
    restrictAut h (autInv (h + 1) (σ (h + 1))) = autInv h (σ h) := by
  rw [restrictAut_autInv, hσ]

/-- **A compatible family of swap elements is a graph automorphism of the infinite
tree.** -/
def infAutIso (σ : (h : ℕ) → Aut h) (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h) :
    treeGraphInf ≃g treeGraphInf where
  toEquiv :=
    { toFun := famAct σ
      invFun := famAct (fun h => autInv h (σ h))
      left_inv := famAct_leftInv σ
      right_inv := famAct_rightInv σ }
  map_rel_iff' := by
    intro u v
    show treeGraphInf.Adj (famAct σ u) (famAct σ v) ↔ treeGraphInf.Adj u v
    constructor
    · intro hadj
      have h1 := famAct_adj (fun h => autInv h (σ h)) (restrictAut_autInv_family σ hσ) hadj
      rwa [famAct_leftInv, famAct_leftInv] at h1
    · exact famAct_adj σ hσ

@[simp] lemma infAutIso_apply (σ : (h : ℕ) → Aut h)
    (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h) (s : List Bool) :
    infAutIso σ hσ s = famAct σ s := rfl

lemma infAutIso_root (σ : (h : ℕ) → Aut h)
    (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h) : infAutIso σ hσ [] = [] := rfl

/-! ### Every root-fixing automorphism of the infinite tree is such a family -/

/-- A root-fixing automorphism of the infinite tree sends children to children. -/
lemma isoInf_child (g : treeGraphInf ≃g treeGraphInf) (hroot : g [] = []) :
    ∀ (n : ℕ) (s : List Bool) (c : Bool), s.length = n →
      ∃ c', g (s ++ [c]) = g s ++ [c'] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s c hn
    have hadj : treeGraphInf.Adj (s ++ [c]) s := Or.inr ⟨c, rfl⟩
    have hmap : treeGraphInf.Adj (g (s ++ [c])) (g s) := g.map_rel_iff.mpr hadj
    rcases hmap with ⟨c', hc'⟩ | ⟨c', hc'⟩
    · exfalso
      match n, hn with
      | 0, hn =>
          obtain rfl : s = [] := List.eq_nil_of_length_eq_zero hn
          rw [hroot] at hc'
          exact absurd (congrArg List.length hc') (by simp)
      | m + 1, hn =>
          obtain ⟨s', d, rfl⟩ : ∃ s' d, s = s' ++ [d] := by
            rcases List.eq_nil_or_concat s with rfl | ⟨s', d, rfl⟩
            · simp at hn
            · exact ⟨s', d, by simp⟩
          have hm : s'.length = m := by
            simp only [List.length_append, List.length_singleton] at hn
            omega
          obtain ⟨d', hd'⟩ := ih m (by omega) s' d hm
          rw [hd'] at hc'
          have hlen : (g s').length = (g ((s' ++ [d]) ++ [c])).length := by
            have := congrArg List.length hc'
            simp only [List.length_append, List.length_singleton] at this
            omega
          obtain ⟨heq, -⟩ := List.append_inj hc' (by rw [hlen])
          have hv := g.injective heq
          have := congrArg List.length hv
          simp at this
    · exact ⟨c', hc'⟩

/-- **Every root-fixing graph automorphism of the infinite tree is the action of a
compatible family of swap elements.** -/
lemma exists_family_of_isoInf (g : treeGraphInf ≃g treeGraphInf) (hroot : g [] = []) :
    ∃ σ : (h : ℕ) → Aut h, (∀ h, restrictAut h (σ (h + 1)) = σ h) ∧
      ∀ (h : ℕ) (s : List Bool), s.length ≤ h → autAct h (σ h) s = g s := by
  have hπ : ∀ h : ℕ, ∃ π : Aut h, ∀ s : List Bool, s.length ≤ h →
      autAct h π s = (fun t => g t) s := fun h =>
    exists_aut_of h (fun t => g t) hroot
      (fun s c _ => isoInf_child g hroot s.length s c rfl)
      (fun s t _ _ heq => g.injective heq)
  choose σ hσ using hπ
  refine ⟨σ, fun h => ?_, fun h s hs => hσ h s hs⟩
  refine aut_ext h _ _ (fun s hs => ?_)
  rw [autAct_restrictAut h _ s hs, hσ (h + 1) s (by omega), hσ h s hs]

/-! ### The infinite matching over graph automorphisms -/

/-- **The infinite matching over graph automorphisms** (`thm:matching`): for compatible
label families, the matching family of swap elements exists exactly when a single
root-fixing graph automorphism `g` of the infinite tree has `X` at `g v` compatible with
`Y` at `v`, at every vertex simultaneously, each coordinate read at its own depth. -/
theorem infMatch_iff_graphAut (R₀ : V → V → Prop) (X Y : (h : ℕ) → FullLab V h)
    (hX : ∀ h, restrictLab h (X (h + 1)) = X h)
    (hY : ∀ h, restrictLab h (Y (h + 1)) = Y h) :
    InfMatch R₀ X Y ↔
      ∃ g : treeGraphInf ≃g treeGraphInf, g [] = [] ∧
        ∀ s : List Bool, R₀ (coord (g s).length (X (g s).length) (g s))
          (coord s.length (Y s.length) s) := by
  constructor
  · rintro ⟨σ, hcompat, hmatch⟩
    refine ⟨infAutIso (fun h => autInv h (σ h)) (restrictAut_autInv_family σ hcompat),
      infAutIso_root _ _, fun s => ?_⟩
    have h1 := (fullMatchesA_iff_coord R₀ s.length (σ s.length)
        (X s.length) (Y s.length)).mp (hmatch s.length)
      (autAct s.length (autInv s.length (σ s.length)) s) (by simp)
    rw [autAct_autInv] at h1
    have hklen : (infAutIso (fun h => autInv h (σ h))
        (restrictAut_autInv_family σ hcompat) s).length = s.length := by simp
    rw [hklen]
    exact h1
  · rintro ⟨g, hroot, hg⟩
    obtain ⟨σ', hcompat', hσ'⟩ := exists_family_of_isoInf g hroot
    refine ⟨fun h => autInv h (σ' h), restrictAut_autInv_family σ' hcompat', fun h => ?_⟩
    refine (fullMatchesA_iff_coord R₀ h _ (X h) (Y h)).mpr fun s hs => ?_
    have hulen : (autAct h (autInv h (σ' h)) s).length ≤ h := by
      rw [autAct_length]; exact hs
    have hgu : g (autAct h (autInv h (σ' h)) s) = s := by
      rw [← hσ' h _ hulen, autAct_autInv]
    have h1 := hg (autAct h (autInv h (σ' h)) s)
    rw [hgu] at h1
    rw [coord_family_stable X hX h s hs, coord_family_stable Y hY h _ hulen]
    exact h1

/-- **The i.i.d. matching theorem over graph automorphisms** (`thm:matching`): two
independent labellings of the infinite binary tree with marginal `μ` at every vertex
admit, with probability at least `1 - 16 Φ`, a root-fixing graph automorphism of the
infinite binary tree matching every vertex. -/
theorem exists_infinite_tree_matching_graphAut (μ : PMF V) [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hη : Phi μ R₀ ≤ 1 / 10000) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : (h : ℕ) → Ω → FullLab V h),
      (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
      (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
      (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
      (∀ h, P.map (fun ω => (X h ω, Y h ω))
        = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) ∧
      1 - 16 * Phi μ R₀ ≤ P {ω | ∃ g : treeGraphInf ≃g treeGraphInf, g [] = [] ∧
        ∀ s : List Bool, R₀ (coord (g s).length (X (g s).length ω) (g s))
          (coord s.length (Y s.length ω) s)} := by
  obtain ⟨Ω, mΩ, P, hP, X, Y, hX, hY, hmeas, hlaw, hmatch⟩ :=
    exists_infinite_tree_matching μ R₀ hrefl hsymm hη
  refine ⟨Ω, mΩ, P, hP, X, Y, hX, hY, hmeas, hlaw, le_trans hmatch (measure_mono ?_)⟩
  intro ω hω
  exact (infMatch_iff_graphAut R₀ (fun h => X h ω) (fun h => Y h ω)
    (fun h => hX h ω) (fun h => hY h ω)).mp hω

end GraphMatching
