/-
Root factorisation of matching degrees in a Markov tree law.
-/
import GraphMarkovMatching.Potential.Degrees

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

lemma rE_succ_branch {S : Type u} (P : S → PMF (S × S)) (R₀ : S → S → Prop)
    (s t : S) (n : ℕ) (xp : FullLab S n × FullLab S n) :
    rE (muM P t (n + 1)) (fullSim R₀ (n + 1)) (branch s xp)
      = if R₀ s t then rE (pairMix P t n) (SquareRel (fullSim R₀ n)) xp
        else 0 := by
  by_cases hst : R₀ s t
  · rw [if_pos hst, muM_succ, rE_map, rE_eq_tsum_mul]
    refine tsum_congr fun yp => ?_
    congr 1
    rw [goodInd, goodInd]
    by_cases h : SquareRel (fullSim R₀ n) xp yp
    · rw [if_pos ((fullSim_branch R₀ n s t xp yp).mpr ⟨hst, h⟩), if_pos h]
    · rw [if_neg (fun hc => h ((fullSim_branch R₀ n s t xp yp).mp hc).2),
        if_neg h]
  · rw [if_neg hst, muM_succ, rE_map]
    refine ENNReal.tsum_eq_zero.mpr fun yp => ?_
    rw [goodInd,
      if_neg (fun hc => hst ((fullSim_branch R₀ n s t xp yp).mp hc).1),
      mul_zero]

end GraphMarkovMatching
