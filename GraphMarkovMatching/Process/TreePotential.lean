/-
The basic quantities of a tree-indexed Markov kernel: the directed tree
potential `Φ_n(s,t)`, the kernel mismatch budget `η(s,t)`, and the two
elementary transport facts they rest on.

Point masses give the expectation `∑' x, δ_a(x)·F(x) = F(a)` and the
identification of the bad degree against a point mass with the bad
indicator.  Attaching a compatible pair of roots contributes nothing, so the bad
degree at height `n+1` against a branched law is the bad degree of the
subtree pair against the pair mixture.  Everything here is generic in the
state space and the root relation; no particular grammar, ceiling route or
offspring law is involved.
-/
import GraphMarkovMatching.Potential.Directed

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {S : Type u}

/-! ### Pure-measure helpers -/

/-- Expectation under a point mass. -/
lemma tsum_pure_mul {A : Type u} (a : A) (F : A → ℝ≥0∞) :
    ∑' x, (PMF.pure a) x * F x = F a := by
  rw [show (∑' x, (PMF.pure a) x * F x) = ∑' x, if x = a then F x else 0 from
    tsum_congr fun x => by by_cases h : x = a <;> simp [PMF.pure_apply, h]]
  exact tsum_ite_eq a F

/-- The bad degree against a point mass is the bad indicator. -/
lemma qE_pure {X : Type u} (b : X) (R : X → X → Prop) (z : X) :
    qE (PMF.pure b) R z = badInd R z b := by
  rw [qE_eq_tsum_mul]
  exact tsum_pure_mul b (badInd R z)

variable (α : ℝ) (P : S → PMF (S × S)) (R₀ : S → S → Prop)

/-! ### The bad degree along the recursion -/

/-- Transport of the bad degree through the root attachment: for compatible
roots the root factor is free and the degree is that of the subtree pair
against the pair mixture. -/
lemma qE_succ_branch {s t : S} (hst : R₀ s t) (n : ℕ)
    (xp : FullLab S n × FullLab S n) :
    qE (muM P t (n + 1)) (fullSim R₀ (n + 1)) (branch s xp)
      = qE (pairMix P t n) (SquareRel (fullSim R₀ n)) xp := by
  rw [muM_succ, qE_map, qE_eq_tsum_mul]
  refine tsum_congr fun yp => ?_
  congr 1
  rw [badInd, badInd]
  by_cases h : SquareRel (fullSim R₀ n) xp yp
  · rw [if_pos ((fullSim_branch R₀ n s t xp yp).mpr ⟨hst, h⟩), if_pos h]
  · rw [if_neg (fun hc => h ((fullSim_branch R₀ n s t xp yp).mp hc).2), if_neg h]

end GraphMarkovMatching
