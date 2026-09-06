/-
`sec:words` of `prelims.tex`: the ambient `N`-ary tree `𝒩(N)`, whose vertices are the
finite words over an `N`-letter alphabet and whose edges join `v` to `v ++ [j]`. Pure
word combinatorics, no probability.

* `Word`: a vertex of `𝒩(N)`, a finite word over `Fin N`; the root is the empty word
  `[]`.
* `wedge`: the longest common prefix `v ∧ w`, pinned down by `wedge_prefix_left`,
  `wedge_prefix_right` and the maximality `prefix_wedge_of_prefix`.
* `treeDist`: the graph metric `d(v,w) = |v| + |w| - 2|v ∧ w|` of `𝒩(N)`, with the
  truncation-free identity `treeDist_add`, the vanishing criterion
  `treeDist_eq_zero_iff` and the triangle inequality `treeDist_triangle`.
* `Word.children`: the children `v ++ [j]` of a vertex, at distance one by
  `treeDist_append_singleton`.
* `Subtree`: a subtree of `𝒩(N)`, that is a prefix-closed set of words, taken as a
  term of `Descriptive.tree (Fin N)`; `Subtree.wedge_mem`, `Subtree.mem_subAt` and
  `treeDist_append_left` bridge that interface to the metric layer above.
-/
import Mathlib.SetTheory.Descriptive.Tree
import Mathlib.Tactic

namespace BranchingProcess

/-! ### Words -/

/-- A vertex of the ambient `N`-ary tree `𝒩(N)`: a finite word over the alphabet
`Fin N`. The root is the empty word `[]`, and the children of `v` are the words
`v ++ [j]` with `j : Fin N`. -/
abbrev Word (N : ℕ) : Type := List (Fin N)

variable {N : ℕ}

/-- A proper prefix is shorter. -/
theorem length_lt_of_prefix_ne {v w : Word N} (h : v <+: w) (hne : v ≠ w) :
    v.length < w.length :=
  lt_of_le_of_ne h.length_le fun hlen => hne (h.eq_of_length hlen)

/-! ### The longest common prefix -/

/-- The longest common prefix `v ∧ w` of two words: their wedge point in `𝒩(N)`. -/
def wedge : Word N → Word N → Word N
  | [], _ => []
  | _, [] => []
  | a :: v, b :: w => if a = b then a :: wedge v w else []

@[simp] theorem wedge_nil_left (w : Word N) : wedge [] w = [] := rfl

@[simp] theorem wedge_nil_right (v : Word N) : wedge v [] = [] := by cases v <;> rfl

/-- The recursion step of `wedge`: a common first letter is kept, a mismatch stops. -/
theorem wedge_cons_cons (a b : Fin N) (v w : Word N) :
    wedge (a :: v) (b :: w) = if a = b then a :: wedge v w else [] := rfl

/-- The wedge of a word with itself is that word. -/
@[simp] theorem wedge_self (v : Word N) : wedge v v = v := by
  induction v with
  | nil => rfl
  | cons a v ih => rw [wedge_cons_cons, if_pos rfl, ih]

/-- The wedge is symmetric. -/
theorem wedge_comm (v w : Word N) : wedge v w = wedge w v := by
  induction v generalizing w with
  | nil => simp
  | cons a v ih =>
      cases w with
      | nil => simp
      | cons b w =>
          rw [wedge_cons_cons, wedge_cons_cons]
          by_cases h : a = b
          · subst h; rw [if_pos rfl, if_pos rfl, ih]
          · rw [if_neg h, if_neg (Ne.symm h)]

/-- The wedge is a prefix of its first argument. -/
theorem wedge_prefix_left (v w : Word N) : wedge v w <+: v := by
  induction v generalizing w with
  | nil => exact List.nil_prefix
  | cons a v ih =>
      cases w with
      | nil => simp
      | cons b w =>
          rw [wedge_cons_cons]
          by_cases h : a = b
          · rw [if_pos h]
            exact List.cons_prefix_cons.mpr ⟨rfl, ih w⟩
          · rw [if_neg h]
            exact List.nil_prefix

/-- The wedge is a prefix of its second argument. -/
theorem wedge_prefix_right (v w : Word N) : wedge v w <+: w := by
  rw [wedge_comm]
  exact wedge_prefix_left w v

/-- Maximality: the wedge is the greatest lower bound for the prefix order. -/
theorem prefix_wedge_of_prefix {u v w : Word N} (hv : u <+: v) (hw : u <+: w) :
    u <+: wedge v w := by
  induction u generalizing v w with
  | nil => exact List.nil_prefix
  | cons c u ih =>
      cases v with
      | nil => simp at hv
      | cons a v =>
          cases w with
          | nil => simp at hw
          | cons b w =>
              rw [List.cons_prefix_cons] at hv hw
              obtain ⟨rfl, hv⟩ := hv
              obtain ⟨rfl, hw⟩ := hw
              rw [wedge_cons_cons, if_pos rfl]
              exact List.cons_prefix_cons.mpr ⟨rfl, ih hv hw⟩

/-- A word wedged with an extension of itself is unchanged. -/
theorem wedge_of_prefix {v w : Word N} (h : v <+: w) : wedge v w = v := by
  have h1 := prefix_wedge_of_prefix (List.prefix_refl v) h
  exact (h1.eq_of_length
    (Nat.le_antisymm h1.length_le (wedge_prefix_left v w).length_le)).symm

theorem wedge_length_le_left (v w : Word N) : (wedge v w).length ≤ v.length :=
  (wedge_prefix_left v w).length_le

theorem wedge_length_le_right (v w : Word N) : (wedge v w).length ≤ w.length :=
  (wedge_prefix_right v w).length_le

/-- Wedging commutes with a common prefix. -/
theorem wedge_append_append (u v w : Word N) :
    wedge (u ++ v) (u ++ w) = u ++ wedge v w := by
  induction u with
  | nil => simp
  | cons a u ih => simp [wedge_cons_cons, ih]

/-- Of the three wedges of a triple, the two shortest agree; in the form the triangle
inequality consumes, `|u ∧ v| + |v ∧ w| ≤ |v| + |u ∧ w|`. -/
theorem wedge_length_add_le (u v w : Word N) :
    (wedge u v).length + (wedge v w).length ≤ v.length + (wedge u w).length := by
  rcases List.prefix_or_prefix_of_prefix (wedge_prefix_right u v)
      (wedge_prefix_left v w) with h | h
  · have hu : wedge u v <+: wedge u w :=
      prefix_wedge_of_prefix (wedge_prefix_left u v) (h.trans (wedge_prefix_right v w))
    have h1 := hu.length_le
    have h2 := wedge_length_le_left v w
    omega
  · have hw : wedge v w <+: wedge u w :=
      prefix_wedge_of_prefix (h.trans (wedge_prefix_left u v)) (wedge_prefix_right v w)
    have h1 := hw.length_le
    have h2 := wedge_length_le_right u v
    omega

/-! ### The metric of the ambient tree -/

/-- The graph metric of `𝒩(N)`: the path distance
`d(v,w) = |v| + |w| - 2|v ∧ w|` of `sec:words`. -/
def treeDist (v w : Word N) : ℕ := v.length + w.length - 2 * (wedge v w).length

/-- The subtraction defining `treeDist` does not truncate. -/
theorem two_mul_wedge_length_le (v w : Word N) :
    2 * (wedge v w).length ≤ v.length + w.length := by
  have h1 := wedge_length_le_left v w
  have h2 := wedge_length_le_right v w
  omega

/-- The truncation-free form of the metric. -/
theorem treeDist_add (v w : Word N) :
    treeDist v w + 2 * (wedge v w).length = v.length + w.length := by
  have h := two_mul_wedge_length_le v w
  simp only [treeDist]
  omega

/-- The metric is symmetric. -/
theorem treeDist_comm (v w : Word N) : treeDist v w = treeDist w v := by
  simp only [treeDist, wedge_comm v w]
  omega

@[simp] theorem treeDist_self (v : Word N) : treeDist v v = 0 := by
  simp only [treeDist, wedge_self]
  omega

/-- The metric separates points. -/
theorem treeDist_eq_zero_iff {v w : Word N} : treeDist v w = 0 ↔ v = w := by
  constructor
  · intro h
    have h1 := wedge_length_le_left v w
    have h2 := wedge_length_le_right v w
    simp only [treeDist] at h
    have hv : wedge v w = v := (wedge_prefix_left v w).eq_of_length (by omega)
    have hw : wedge v w = w := (wedge_prefix_right v w).eq_of_length (by omega)
    exact hv.symm.trans hw
  · rintro rfl
    exact treeDist_self v

/-- Along a chain of prefixes the metric is the difference of the lengths. -/
theorem treeDist_of_prefix {v w : Word N} (h : v <+: w) :
    treeDist v w = w.length - v.length := by
  have := h.length_le
  simp only [treeDist, wedge_of_prefix h]
  omega

/-- The triangle inequality. -/
theorem treeDist_triangle (u v w : Word N) :
    treeDist u w ≤ treeDist u v + treeDist v w := by
  have h1 := treeDist_add u w
  have h2 := treeDist_add u v
  have h3 := treeDist_add v w
  have h4 := wedge_length_add_le u v w
  omega

/-- A common prefix is an isometry onto the residual subtree it names. -/
theorem treeDist_append_left (u v w : Word N) :
    treeDist (u ++ v) (u ++ w) = treeDist v w := by
  have h := two_mul_wedge_length_le v w
  simp only [treeDist, wedge_append_append, List.length_append]
  omega

/-! ### Parents and children -/

/-- The children of `v` in `𝒩(N)`: the words obtained from `v` by appending one
letter. -/
def Word.children (v : Word N) : Set (Word N) := {w | ∃ j, w = v ++ [j]}

@[simp] theorem Word.mem_children {v w : Word N} :
    w ∈ v.children ↔ ∃ j : Fin N, w = v ++ [j] := Iff.rfl

/-- A vertex is a prefix of each of its children. -/
theorem Word.prefix_of_mem_children {v w : Word N} (h : w ∈ v.children) : v <+: w := by
  obtain ⟨j, rfl⟩ := h
  exact List.prefix_append v [j]

/-- An edge of `𝒩(N)` has length one. -/
@[simp] theorem treeDist_append_singleton (v : Word N) (j : Fin N) :
    treeDist v (v ++ [j]) = 1 := by
  rw [treeDist_of_prefix (List.prefix_append v [j])]
  simp

/-- Children sit at distance one from their parent. -/
theorem treeDist_of_mem_children {v w : Word N} (h : w ∈ v.children) :
    treeDist v w = 1 := by
  obtain ⟨j, rfl⟩ := h
  exact treeDist_append_singleton v j

/-! ### Subtrees -/

/-- A subtree of `𝒩(N)`: a prefix-closed set of words, taken as a term of
`Descriptive.tree (Fin N)`. That type carries the `SetLike` membership `v ∈ T` and the
complete-lattice structure on prefix-closed sets, so intersections, unions and the
extreme elements come for free. -/
abbrev Subtree (N : ℕ) : Type := Descriptive.tree (Fin N)

namespace Subtree

variable {T : Subtree N}

/-- Prefix closure, in the notation of `𝒩(N)`. -/
theorem mem_of_prefix {v w : Word N} (h : v <+: w) (hw : w ∈ T) : v ∈ T :=
  Descriptive.Tree.mem_of_prefix h hw

/-- A subtree with a vertex contains the root. -/
theorem nil_mem {v : Word N} (hv : v ∈ T) : ([] : Word N) ∈ T :=
  mem_of_prefix List.nil_prefix hv

/-- The wedge of a vertex of a subtree with any word is again a vertex of it: subtrees
are closed under the meet of `𝒩(N)`. -/
theorem wedge_mem {v : Word N} (hv : v ∈ T) (w : Word N) : wedge v w ∈ T :=
  mem_of_prefix (wedge_prefix_left v w) hv

/-- The residual subtree at a node `v`, `Descriptive.Tree.subAt`, read off in the
notation of `𝒩(N)`: it consists of the words `w` with `v ++ w` in `T`. -/
theorem mem_subAt {v w : Word N} : w ∈ Descriptive.Tree.subAt T v ↔ v ++ w ∈ T :=
  Descriptive.Tree.mem_subAt T v w

end Subtree

end BranchingProcess
