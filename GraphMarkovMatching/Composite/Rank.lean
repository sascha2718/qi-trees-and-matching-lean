/-
Nilpotence from a rank, and a rank from acyclicity
(`arbitrary_offspring_matching.tex`, the rank paragraph in the proof of
`thm:composite-acyclic`), self-contained for the composite subfolder and
stated over any semiring-like scalar type.

* `matApply N v`: one application of a nonnegative transfer matrix;
* `matApply_iter_eq_zero`: a rank that strictly decreases along the
  support of `N` and stays below `r` makes `r` applications annihilate
  every vector;
* `reachRank`: the number of indices strictly reachable in the support
  graph; on an acyclic support it strictly decreases along edges and is
  bounded by the cardinality;
* `nilpotent_of_acyclic`: acyclicity of the support graph alone
  annihilates after `card ι` applications.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

namespace GraphMarkovMatching
namespace Composite

open scoped Classical

variable {ι : Type*} [Fintype ι] {α : Type*} [NonUnitalNonAssocSemiring α]

/-- One application of the transfer matrix `N` to a vector. -/
def matApply (N : ι → ι → α) (v : ι → α) : ι → α := fun i => ∑ j, N i j * v j

/-- **Nilpotence from a rank certificate**, the rank paragraph in the
proof of `thm:composite-acyclic`: if a rank strictly decreases along the
support of `N` and stays below `r`, then `r` applications of `N`
annihilate every vector. -/
theorem matApply_iter_eq_zero (N : ι → ι → α) (rk : ι → ℕ) (r : ℕ)
    (hdec : ∀ i j, N i j ≠ 0 → rk j < rk i) (hlt : ∀ i, rk i < r)
    (v : ι → α) : (matApply N)^[r] v = fun _ => 0 := by
  have key : ∀ k (v : ι → α) (i : ι), rk i < k → (matApply N)^[k] v i = 0 := by
    intro k
    induction k with
    | zero => exact fun v i h => absurd h (Nat.not_lt_zero _)
    | succ k ih =>
        intro v i h
        have hunf : (matApply N)^[k + 1] v i
            = ∑ j, N i j * (matApply N)^[k] v j := by
          rw [Function.iterate_succ_apply']
          rfl
        rw [hunf]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hN : N i j = 0
        · rw [hN, zero_mul]
        · have hj : rk j < k := by
            have := hdec i j hN
            omega
          rw [ih v j hj, mul_zero]
  funext i
  exact key r v i (hlt i)

/-- The reachability rank: the number of indices strictly reachable from
`i` through the relation. -/
noncomputable def reachRank (Nrel : ι → ι → Prop) (i : ι) : ℕ :=
  (Finset.univ.filter fun k => Relation.TransGen Nrel i k).card

lemma reachRank_lt_of_rel {Nrel : ι → ι → Prop}
    (hacyc : ∀ i, ¬ Relation.TransGen Nrel i i) {i j : ι} (hij : Nrel i j) :
    reachRank Nrel j < reachRank Nrel i := by
  have hsub : (Finset.univ.filter fun k => Relation.TransGen Nrel j k)
      ⊆ Finset.univ.filter fun k => Relation.TransGen Nrel i k := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_univ _, (Relation.TransGen.single hij).trans hk.2⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨j, ?_, ?_⟩)
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Relation.TransGen.single hij⟩
  · exact fun hmem => hacyc j (Finset.mem_filter.mp hmem).2

lemma reachRank_lt_card {Nrel : ι → ι → Prop}
    (hacyc : ∀ i, ¬ Relation.TransGen Nrel i i) (i : ι) :
    reachRank Nrel i < Fintype.card ι := by
  have hsub : (Finset.univ.filter fun k => Relation.TransGen Nrel i k)
      ⊆ Finset.univ.erase i := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_erase]
    exact ⟨fun hki => hacyc i (hki ▸ hk.2), Finset.mem_univ _⟩
  calc reachRank Nrel i ≤ (Finset.univ.erase i).card := Finset.card_le_card hsub
    _ < Finset.univ.card := Finset.card_erase_lt_of_mem (Finset.mem_univ i)
    _ = Fintype.card ι := Finset.card_univ

/-- **Nilpotence from acyclicity**: if the support graph of `N` has no
directed cycle, then `card ι` applications annihilate every vector. -/
theorem nilpotent_of_acyclic (N : ι → ι → α)
    (hacyc : ∀ i, ¬ Relation.TransGen (fun i j => N i j ≠ 0) i i)
    (v : ι → α) : (matApply N)^[Fintype.card ι] v = fun _ => 0 :=
  matApply_iter_eq_zero N (reachRank fun i j => N i j ≠ 0) (Fintype.card ι)
    (fun _ _ h => reachRank_lt_of_rel hacyc h) (reachRank_lt_card hacyc) v

end Composite
end GraphMarkovMatching
