/-
The abstract renewal-block invariant (from the retired varying-offspring
draft; superseded by the closed recursion `sec:recursion` of
`arbitrary_offspring_matching.tex`): given the block recursion

    Ψ₀ ≤ c·η,   Ψ_{r+1} ≤ c·η + a·Ψ_r + b·(η + Ψ_r)²,

any level `B = K·η` satisfying the closure inequality is invariant, so the
failure quantity is at most `K·η` through every renewal block.  This
certifies the retired draft's reduction of the arbitrary-support
conjecture to its block recursion (the induction with `K = 2c/(1-a)`, here in closure form).

The corrected Step 2 that discharges the lemma's recursion hypotheses is
the conditional-split-plus-four-law argument certified in one-block form in
`Process/Contraction.lean` (the exact factorisation `qE_Tlaw_succ_branch`, the
split `phiE_split`, the change of measure `phiE_q_le_of_between`, and the
heterogeneous contraction `PhiD_fourlaw_le` with linear constant
`A = 2L + 2(1+δ)K`, which at `α = 5/2`, `δ = 1` is the constant `A₄` of
`thm:four-law`).  The per-shape verification for the general renewal grammar
is certified in the general-ν assembly (`Closure/Main.lean`).
-/
import GraphMarkovMatching.Process.Basic

namespace GraphMarkovMatching

open scoped ENNReal

/-- **The renewal invariant**: the closure inequality makes the level `K·η`
invariant for the block recursion, hence a bound uniform in the number of
exposed renewal blocks. -/
theorem renewal_uniform_bound (a b c η K : ℝ≥0∞) (Ψ : ℕ → ℝ≥0∞)
    (hbase : Ψ 0 ≤ c * η)
    (hrec : ∀ r, Ψ (r + 1) ≤ c * η + a * Ψ r + b * (η + Ψ r) ^ 2)
    (hcK : c ≤ K)
    (hclose : c * η + a * (K * η) + b * (η + K * η) ^ 2 ≤ K * η) :
    ∀ r, Ψ r ≤ K * η := by
  intro r
  induction r with
  | zero => exact le_trans hbase (mul_le_mul_left hcK η)
  | succ r ih =>
      refine le_trans (hrec r) (le_trans ?_ hclose)
      refine add_le_add (add_le_add le_rfl (mul_le_mul_right ih a)) ?_
      refine mul_le_mul_right ?_ b
      rw [pow_two, pow_two]
      exact mul_le_mul' (add_le_add le_rfl ih) (add_le_add le_rfl ih)

end GraphMarkovMatching
