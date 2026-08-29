/-
The pure-ternary instantiation `ν = δ₃`
(`arbitrary_offspring_matching.tex` at `ν = δ₃`): the first end-to-end
exercise of the certified ledger.

For `ν = δ₃` the mixture trivialises (`Ξ̄ = Ξ₃`), the fresh cells carry
counter `3` only, and `ν_* = 1`, so no reciprocal weight appears.  The
crossed-context obstruction (`crossed_context_potential_top` in
`Process/CrossedContext.lean`) shows this case CANNOT be handled by
unrestricted potentials; here the restricted ledger goes through:

* `XiBar_delta3`: `Ξ̄ = Ξ₃`;
* `delta3_Tlaw_Tlaw_step`: the principal ordinary coordinate at height
  `h+1` is bounded by `η`, the four-law output of the single square cell
  `(Z₂⊗T → Z₂⊗T)`, its four resolved screens, and the quadratic cross
  term — the complete `Ψ`-step of `screened_uniform_bound` for the
  principal row, as one machine-checked inequality.
-/
import GraphMarkovMatching.Process.Descent

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- For `ν = δ₃` the cascade mixture is the single counter-`3` cell. -/
lemma XiBar_delta3 (h : ℕ) :
    XiBar μ (PMF.pure 3) v0 h = Xi μ (PMF.pure 3) v0 3 h := by
  rw [show XiBar μ (PMF.pure 3) v0 h
      = (PMF.pure 3).bind (fun k => Xi μ (PMF.pure 3) v0 k h) from rfl,
    PMF.pure_bind]

/-- **The principal step for `ν = δ₃`**: the fresh-fresh restricted
coordinate at height `h+1`, bounded by the graph potential, the four-law
output of the `(Z₂⊗T → Z₂⊗T)` cell with its resolved screens, and the
quadratic cross term. -/
theorem delta3_Tlaw_Tlaw_step {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (h : ℕ) (M Z : ℝ≥0∞)
    (hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Tlaw μ (PMF.pure 3) v0 (h + 1))
        (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ etaG α Rv μ
        + (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
          + ENNReal.ofReal
              (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
          + ENNReal.ofReal (2 * (1 + δ)) * Z
          + (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                [Zlaw μ (PMF.pure 3) v0 2 h]
                (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
              + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                [Tlaw μ (PMF.pure 3) v0 h]
                (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h))
              + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
                [Zlaw μ (PMF.pure 3) v0 2 h]
                (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
              + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
                [Tlaw μ (PMF.pure 3) v0 h]
                (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h)))
            * (1 + ENNReal.ofReal α * M))
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
              + ENNReal.ofReal
                  (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
                * M ^ 2
              + ENNReal.ofReal (2 * (1 + δ)) * Z
              + (screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) [Zlaw μ (PMF.pure 3) v0 2 h]
                    (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                    (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) [Zlaw μ (PMF.pure 3) v0 2 h]
                    (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                    (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h)))
                * (1 + ENNReal.ofReal α * M))) := by
  have hsq : PhiDres α (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 3 h)
      (SquareRel (fullSim (labRel Rv) h))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
    rw [Xi_three μ (PMF.pure 3) v0 h]
    exact PhiDres_square_le hα hδ hL0 hL hK0 hK
      (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h)
      (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
      M Z hZZ hZT hTZ hTT hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT
  have hsum : (∑' k, (PMF.pure 3 : PMF ℕ) k
        * PhiDres α (Xi μ (PMF.pure 3) v0 k h) (XiBar μ (PMF.pure 3) v0 h)
            (SquareRel (fullSim (labRel Rv) h)))
      = PhiDres α (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 3 h)
          (SquareRel (fullSim (labRel Rv) h)) := by
    rw [tsum_pure_mul 3 (fun k => PhiDres α (Xi μ (PMF.pure 3) v0 k h)
      (XiBar μ (PMF.pure 3) v0 h) (SquareRel (fullSim (labRel Rv) h))),
      XiBar_delta3 μ v0 h]
  refine le_trans (PhiDres_Tlaw_Tlaw_succ α Rv μ (PMF.pure 3) v0 hα h) ?_
  rw [hsum]
  exact add_le_add (add_le_add le_rfl hsq)
    (mul_le_mul_right (mul_le_mul_right hsq _) _)

end GraphMarkovMatching
