/-
The nilpotence certificate for the accessible screen block
(`arbitrary_offspring_matching.tex` `sec:nilpotence`, Theorem
`thm:nilpotence`): the formal half `acyclic ⇒ N^r = 0`, in two forms.

* `nilpotent_of_rank`: a rank function that strictly decreases along the
  support of `N` and stays below `r` makes `N^r` annihilate every vector.
  This discharges the hypothesis `hnil` of `screened_uniform_bound_mono`; the
  rank is supplied by the renewal-depth argument.
* `nilpotent_of_acyclic`: acyclicity of the support graph alone produces
  such a rank (the cardinality of the strictly reachable set), so
  `N^{card ι}` annihilates every vector.

The other half of `thm:nilpotence`, that the accessible screen graph
IS acyclic (renewal depths, list coverage, the numerical semigroup), is
certified in `Grammar/Depths.lean`, `Grammar/Descend.lean`,
`Grammar/SourceRay.lean`, and `Grammar/Accessible.lean`
(`no_anchored_live_path`).
-/
import GraphMarkovMatching.Closure.Block

namespace GraphMarkovMatching

open scoped ENNReal Classical

variable {ι : Type} [Fintype ι]

/-- **Nilpotence from a rank certificate**: if `rank` strictly decreases
along the support of `N` and is everywhere below `r`, then `N^r`
annihilates every vector. -/
theorem nilpotent_of_rank (N : ι → ι → ℝ≥0∞) (rank : ι → ℕ) (r : ℕ)
    (hdec : ∀ i j, N i j ≠ 0 → rank j < rank i)
    (hlt : ∀ i, rank i < r) :
    ∀ x : ι → ℝ≥0∞, (mulVec N)^[r] x = fun _ => 0 := by
  have key : ∀ k (x : ι → ℝ≥0∞) i, rank i < k → (mulVec N)^[k] x i = 0 := by
    intro k
    induction k with
    | zero => exact fun x i h => absurd h (Nat.not_lt_zero _)
    | succ k ih =>
        intro x i hik
        have hunf : (mulVec N)^[k + 1] x i
            = ∑ j, N i j * (mulVec N)^[k] x j := by
          rw [Function.iterate_succ_apply']
          rfl
        rw [hunf]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hNij : N i j = 0
        · rw [hNij, zero_mul]
        · rw [ih x j (lt_of_lt_of_le (hdec i j hNij) (Nat.lt_succ_iff.mp hik)),
            mul_zero]
  intro x
  funext i
  exact key r x i (hlt i)

/-- The support graph of the screen-transfer matrix: `i ⟶ j` when the entry
`N i j` is positive, i.e. when the screen `j` occurs as a linear successor
charge of the screen `i`. -/
def supportRel (N : ι → ι → ℝ≥0∞) : ι → ι → Prop := fun i j => N i j ≠ 0

/-- The reachability rank of a screen: the number of screens strictly
reachable from it in the support graph. -/
noncomputable def reachRank (N : ι → ι → ℝ≥0∞) (i : ι) : ℕ :=
  (Finset.univ.filter fun k => Relation.TransGen (supportRel N) i k).card

lemma reachRank_lt_of_support {N : ι → ι → ℝ≥0∞}
    (hacyc : ∀ i, ¬ Relation.TransGen (supportRel N) i i)
    {i j : ι} (hij : N i j ≠ 0) : reachRank N j < reachRank N i := by
  have hsub : (Finset.univ.filter fun k => Relation.TransGen (supportRel N) j k)
      ⊆ Finset.univ.filter fun k => Relation.TransGen (supportRel N) i k := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_univ _,
      (Relation.TransGen.single (show supportRel N i j from hij)).trans hk.2⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨j, ?_, ?_⟩)
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Relation.TransGen.single (show supportRel N i j from hij)⟩
  · exact fun hmem => hacyc j (Finset.mem_filter.mp hmem).2

lemma reachRank_lt_card {N : ι → ι → ℝ≥0∞}
    (hacyc : ∀ i, ¬ Relation.TransGen (supportRel N) i i) (i : ι) :
    reachRank N i < Fintype.card ι := by
  have hsub : (Finset.univ.filter fun k => Relation.TransGen (supportRel N) i k)
      ⊆ Finset.univ.erase i := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_erase]
    exact ⟨fun hki => hacyc i (hki ▸ hk.2), Finset.mem_univ _⟩
  calc reachRank N i ≤ (Finset.univ.erase i).card := Finset.card_le_card hsub
    _ < Finset.univ.card := Finset.card_erase_lt_of_mem (Finset.mem_univ i)
    _ = Fintype.card ι := Finset.card_univ

/-- **Nilpotence from acyclicity** (`eq:nilpotent`): if the support graph
of the screen-transfer matrix has no directed cycle, then
`N^{card ι}` annihilates every vector.  Entries of `N` may be arbitrarily
large; only the shape of the support enters. -/
theorem nilpotent_of_acyclic (N : ι → ι → ℝ≥0∞)
    (hacyc : ∀ i, ¬ Relation.TransGen (supportRel N) i i) :
    ∀ x : ι → ℝ≥0∞, (mulVec N)^[Fintype.card ι] x = fun _ => 0 :=
  nilpotent_of_rank N (reachRank N) (Fintype.card ι)
    (fun _ _ h => reachRank_lt_of_support hacyc h)
    (reachRank_lt_card hacyc)

end GraphMarkovMatching
