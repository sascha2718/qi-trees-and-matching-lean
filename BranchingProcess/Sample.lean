/-
`sec:gw-trees` of `prelims.tex`: the deterministic layer of a Galton-Watson tree.  A
field of offspring counts `c : Word N → ℕ` cuts out of the ambient `N`-ary tree the
subtree in which each vertex `v` keeps its first `c v` children; the randomness enters
later, through a random field `c`, and no measure theory appears here.

* `sample`: the tree cut out by `c`, a `Subtree N`, with `mem_sample_iff'`,
  `nil_mem_sample` and the workhorse `mem_sample_append_singleton`.
* `append_mem_sample_iff` and `subAt_sample`: the branching property, the residual
  subtree at a vertex of the sample is the sample of the shifted field.
* `coe_sample`: the decomposition of a sample into its root and the samples hanging off
  the children of the root, with `finite_sample_of_forall_finite` and its converse
  `exists_infinite_child_of_infinite`.
* `Survives`, `skeleton`: survival and the vertices whose residual subtree is infinite,
  with `skeleton_subset_sample`, `nil_mem_skeleton_iff` and the pigeonhole
  `exists_child_mem_skeleton`.
* `exists_skeleton_ray`: a ray inside the skeleton out of any of its vertices, an
  isometric copy of `ℕ` by `exists_isometric_skeleton_ray`.
-/
import BranchingProcess.Word
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Finite.Lattice

namespace BranchingProcess

variable {N : ℕ}

/-! ### The sample of an offspring field -/

/-- The tree cut out of `𝒩(N)` by a field `c` of offspring counts: the vertex `v` keeps
its children `v ++ [j]` with `j < c v`, so a word belongs to the sample when every one
of its steps is below the offspring count at the vertex it leaves.  Prefix closure is
immediate, a prefix imposing fewer conditions. -/
def sample (c : Word N → ℕ) : Subtree N :=
  ⟨{v | ∀ i, (h : i < v.length) → ((v.get ⟨i, h⟩ : Fin N) : ℕ) < c (v.take i)}, by
    intro v a hv i hi
    have hi' : i < (v ++ [a]).length := by
      rw [List.length_append]
      omega
    have h : (((v ++ [a])[i]'hi' : Fin N) : ℕ) < c ((v ++ [a]).take i) := hv i hi'
    rw [List.getElem_append_left hi, List.take_append_of_le_length hi.le] at h
    exact h⟩

/-- The same condition indexed by `getElem`, the shape the proofs below consume. -/
theorem mem_sample_iff' {c : Word N → ℕ} {v : Word N} :
    v ∈ sample c ↔ ∀ i, (h : i < v.length) → ((v[i]'h : Fin N) : ℕ) < c (v.take i) :=
  Iff.rfl

/-- The root belongs to every sample. -/
@[simp] theorem nil_mem_sample (c : Word N → ℕ) : ([] : Word N) ∈ sample c := by
  intro i hi
  simp at hi

/-- **The one-step criterion.** A child `v ++ [j]` lies in the sample exactly when its
parent does and the offspring count at the parent exceeds `j`. -/
theorem mem_sample_append_singleton {c : Word N → ℕ} {v : Word N} {j : Fin N} :
    v ++ [j] ∈ sample c ↔ v ∈ sample c ∧ (j : ℕ) < c v := by
  have hlen : (v ++ [j]).length = v.length + 1 := by simp
  have hlast : v.length < (v ++ [j]).length := by omega
  have hget : (v ++ [j])[v.length]'hlast = j := by
    rw [List.getElem_append_right le_rfl]
    simp
  have htake : (v ++ [j]).take v.length = v := by
    rw [List.take_append_of_le_length le_rfl, List.take_length]
  constructor
  · intro h
    refine ⟨Subtree.mem_of_prefix (List.prefix_append v [j]) h, ?_⟩
    have h' : (((v ++ [j])[v.length]'hlast : Fin N) : ℕ) < c ((v ++ [j]).take v.length) :=
      h v.length hlast
    rwa [hget, htake] at h'
  · rintro ⟨hv, hj⟩ i hi
    show (((v ++ [j])[i]'hi : Fin N) : ℕ) < c ((v ++ [j]).take i)
    have hi' : i < v.length + 1 := by omega
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with hlt | heq
    · rw [List.getElem_append_left hlt, List.take_append_of_le_length hlt.le]
      exact hv i hlt
    · subst heq
      rw [hget, htake]
      exact hj

/-- A one-letter word lies in the sample exactly when the root has that many children. -/
theorem singleton_mem_sample_iff {c : Word N → ℕ} {j : Fin N} :
    [j] ∈ sample c ↔ (j : ℕ) < c [] := by
  have h : ([j] : Word N) = [] ++ [j] := rfl
  rw [h, mem_sample_append_singleton]
  simp

/-! ### The branching property -/

/-- **Splitting a word at a vertex.** A concatenation lies in the sample exactly when
its head does and its tail lies in the sample of the field shifted to that head. -/
theorem append_mem_sample_iff (c : Word N → ℕ) (v w : Word N) :
    v ++ w ∈ sample c ↔ v ∈ sample c ∧ w ∈ sample fun u ↦ c (v ++ u) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc, mem_sample_append_singleton, mem_sample_append_singleton, ih]
      tauto

/-- **The branching property.** The residual subtree of a sample at one of its vertices
is again a sample, for the offspring field shifted to that vertex.  Every recursion
below runs off this identity. -/
theorem subAt_sample {c : Word N → ℕ} {v : Word N} (hv : v ∈ sample c) :
    Descriptive.Tree.subAt (sample c) v = sample fun w ↦ c (v ++ w) := by
  refine SetLike.ext fun w ↦ ?_
  rw [Subtree.mem_subAt, append_mem_sample_iff]
  simp [hv]

/-! ### Decomposition at the root -/

/-- **The decomposition at the root.** A sample is its root together with the samples of
the shifted fields hanging off the children of the root. -/
theorem coe_sample (c : Word N → ℕ) :
    (sample c : Set (Word N)) =
      {[]} ∪ ⋃ j ∈ {j : Fin N | (j : ℕ) < c []},
        (fun w ↦ [j] ++ w) '' (sample fun w ↦ c ([j] ++ w) : Set (Word N)) := by
  ext v
  cases v with
  | nil =>
      have h : ([] : Word N) ∈ sample c := nil_mem_sample c
      simp [h]
  | cons j u =>
      have hsplit : (j :: u : Word N) = [j] ++ u := rfl
      rw [SetLike.mem_coe, hsplit, append_mem_sample_iff, singleton_mem_sample_iff]
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image,
        Set.mem_ofPred_eq, SetLike.mem_coe]
      constructor
      · rintro ⟨hj, hu⟩
        exact Or.inr ⟨j, hj, u, hu, rfl⟩
      · rintro (h | ⟨i, hi, w, hw, hiw⟩)
        · exact absurd h (by simp)
        · obtain ⟨rfl, rfl⟩ : i = j ∧ w = u := by
            simpa using hiw
          exact ⟨hi, hw⟩

/-- **Finiteness passes up to the root.** A sample all of whose child samples are finite
is finite: the root has at most `N` children, so the union is a finite one. -/
theorem finite_sample_of_forall_finite {c : Word N → ℕ}
    (h : ∀ j : Fin N, (j : ℕ) < c [] →
      (sample fun w ↦ c ([j] ++ w) : Set (Word N)).Finite) :
    (sample c : Set (Word N)).Finite := by
  rw [coe_sample]
  exact (Set.finite_singleton _).union
    (Set.Finite.biUnion (Set.toFinite _) fun j hj ↦ (h j hj).image _)

/-- **The pigeonhole at the root.** An infinite sample has a child whose sample is
infinite. -/
theorem exists_infinite_child_of_infinite {c : Word N → ℕ}
    (h : (sample c : Set (Word N)).Infinite) :
    ∃ j : Fin N, (j : ℕ) < c [] ∧ (sample fun w ↦ c ([j] ++ w) : Set (Word N)).Infinite := by
  by_contra hcon
  refine h (finite_sample_of_forall_finite fun j hj ↦ ?_)
  by_contra hfin
  exact hcon ⟨j, hj, hfin⟩

/-! ### Survival and the skeleton -/

/-- Survival of the sample of `c`: the tree it cuts out is infinite. -/
def Survives (c : Word N → ℕ) : Prop := (sample c : Set (Word N)).Infinite

/-- The skeleton of a sample: the vertices whose residual subtree is infinite, that is
the vertices lying on an infinite ray. -/
def skeleton (c : Word N → ℕ) : Set (Word N) :=
  {v | v ∈ sample c ∧ (Descriptive.Tree.subAt (sample c) v : Set (Word N)).Infinite}

/-- Membership in the skeleton, unfolded. -/
theorem mem_skeleton_iff {c : Word N → ℕ} {v : Word N} :
    v ∈ skeleton c ↔
      v ∈ sample c ∧ (Descriptive.Tree.subAt (sample c) v : Set (Word N)).Infinite :=
  Iff.rfl

/-- The skeleton is a set of vertices of the sample. -/
theorem skeleton_subset_sample (c : Word N → ℕ) :
    skeleton c ⊆ (sample c : Set (Word N)) := fun _ hv ↦ hv.1

/-- The root lies in the skeleton exactly when the sample survives. -/
theorem nil_mem_skeleton_iff {c : Word N → ℕ} : ([] : Word N) ∈ skeleton c ↔ Survives c := by
  simp [mem_skeleton_iff, Survives]

/-- **The skeleton has no leaves.** A skeleton vertex has a child in the skeleton: its
residual subtree is infinite and has finitely many child subtrees, so one of them is
infinite. -/
theorem exists_child_mem_skeleton {c : Word N → ℕ} {v : Word N} (hv : v ∈ skeleton c) :
    ∃ w ∈ Word.children v, w ∈ skeleton c := by
  obtain ⟨hmem, hinf⟩ := hv
  rw [subAt_sample hmem] at hinf
  obtain ⟨j, hj, hinf'⟩ := exists_infinite_child_of_infinite hinf
  have hj' : (j : ℕ) < c v := by simpa using hj
  have hw : v ++ [j] ∈ sample c := mem_sample_append_singleton.mpr ⟨hmem, hj'⟩
  refine ⟨v ++ [j], ⟨j, rfl⟩, hw, ?_⟩
  have hshift : (fun w ↦ c (v ++ [j] ++ w)) = fun w ↦ c (v ++ ([j] ++ w)) := by
    funext w
    rw [List.append_assoc]
  rw [subAt_sample hw, hshift]
  exact hinf'

/-! ### Rays in the skeleton -/

/-- Along a chain of children the lengths grow by one at each step. -/
theorem length_of_chain {r : ℕ → Word N} (hr : ∀ n, r (n + 1) ∈ Word.children (r n)) (n : ℕ) :
    (r n).length = (r 0).length + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨j, hj⟩ := hr n
      rw [hj, List.length_append, ih]
      simp only [List.length_singleton]
      omega

/-- A chain of children is increasing for the prefix order. -/
theorem prefix_of_chain {r : ℕ → Word N} (hr : ∀ n, r (n + 1) ∈ Word.children (r n)) {m n : ℕ}
    (h : m ≤ n) : r m <+: r n := by
  induction n with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp h
      exact List.prefix_refl _
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact List.prefix_refl _
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (Word.prefix_of_mem_children (hr n))

/-- A chain of children is an isometric copy of `ℕ` inside `𝒩(N)`. -/
theorem treeDist_of_chain {r : ℕ → Word N} (hr : ∀ n, r (n + 1) ∈ Word.children (r n))
    (m n : ℕ) : treeDist (r m) (r n) = Nat.dist m n := by
  rcases le_total m n with h | h
  · rw [treeDist_of_prefix (prefix_of_chain hr h), length_of_chain hr m, length_of_chain hr n,
      Nat.dist_eq_sub_of_le h]
    omega
  · rw [treeDist_comm, treeDist_of_prefix (prefix_of_chain hr h), length_of_chain hr m,
      length_of_chain hr n, Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    omega

/-- **Rays out of the skeleton.** Every skeleton vertex starts an infinite ray of
skeleton vertices.  No compactness is needed: `exists_child_mem_skeleton` supplies the
next vertex at each step, and the ray is the resulting recursion. -/
theorem exists_skeleton_ray {c : Word N → ℕ} {v : Word N} (hv : v ∈ skeleton c) :
    ∃ r : ℕ → Word N, r 0 = v ∧ (∀ n, r n ∈ skeleton c) ∧
      ∀ n, r (n + 1) ∈ Word.children (r n) := by
  classical
  choose f hf₁ hf₂ using fun w : {w : Word N // w ∈ skeleton c} ↦ exists_child_mem_skeleton w.2
  let ρ : ℕ → {w : Word N // w ∈ skeleton c} :=
    fun n ↦ Nat.rec (⟨v, hv⟩ : {w : Word N // w ∈ skeleton c}) (fun _ w ↦ ⟨f w, hf₂ w⟩) n
  exact ⟨fun n ↦ (ρ n).1, rfl, fun n ↦ (ρ n).2, fun n ↦ hf₁ (ρ n)⟩

/-- The metric form of `exists_skeleton_ray`: the ray is an isometric copy of `ℕ`. -/
theorem exists_isometric_skeleton_ray {c : Word N → ℕ} {v : Word N} (hv : v ∈ skeleton c) :
    ∃ r : ℕ → Word N, r 0 = v ∧ (∀ n, r n ∈ skeleton c) ∧
      (∀ n, r (n + 1) ∈ Word.children (r n)) ∧ ∀ m n, treeDist (r m) (r n) = Nat.dist m n := by
  obtain ⟨r, hr0, hrmem, hrstep⟩ := exists_skeleton_ray hv
  exact ⟨r, hr0, hrmem, hrstep, treeDist_of_chain hrstep⟩

end BranchingProcess
