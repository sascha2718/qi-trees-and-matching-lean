/-
The ordinary restricted-potential rows for the quenched target grammar.

Conditioning on the complete counter environment turns every child law into
an honest product of two component laws.  The root split therefore has the
same form as the finite-support proof, but it contains no aggregate
`XiBar` law and hence no inverse of a countable mixture degree.
-/
import GraphMarkovMatching.Tail.QuenchedGrammar
import GraphMarkovMatching.Process.Descent

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-! ### Root/child degree identities -/

/-- Good degree toward an arbitrary child-pair law with a fixed root
attached. -/
lemma rE_map_branch_law {S : Type u} (ρ : PMF (FullLab S h × FullLab S h))
    (R₀ : S → S → Prop) (s t : S) (xp : FullLab S h × FullLab S h) :
    rE (ρ.map (branch t)) (fullSim R₀ (h + 1)) (branch s xp)
      = if R₀ s t then rE ρ (SquareRel (fullSim R₀ h)) xp else 0 := by
  by_cases hst : R₀ s t
  · rw [if_pos hst, rE_map, rE_eq_tsum_mul]
    refine tsum_congr fun yp => ?_
    congr 1
    rw [goodInd, goodInd]
    by_cases hxy : SquareRel (fullSim R₀ h) xp yp
    · rw [if_pos ((fullSim_branch R₀ h s t xp yp).mpr ⟨hst, hxy⟩), if_pos hxy]
    · rw [if_neg (fun hc => hxy ((fullSim_branch R₀ h s t xp yp).mp hc).2),
        if_neg hxy]
  · rw [if_neg hst, rE_map]
    refine ENNReal.tsum_eq_zero.mpr fun yp => ?_
    rw [goodInd,
      if_neg (fun hc => hst ((fullSim_branch R₀ h s t xp yp).mp hc).1),
      mul_zero]

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- Fresh quenched target: its only remaining mixture is the one-site root
law `μ`; the child degree is a single component product. -/
lemma rE_qInterp_F_succ_branch (v : V) (k h : ℕ)
    (e : FullLab ℕ (h + 1))
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    rE (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = rE μ Rv v
          * rE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := by
  rw [qInterp_F_succ, rE_bind]
  calc
    (∑' w, μ w * rE
      ((qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1))).map
        (branch (w, envRoot (h + 1) e)))
      (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp))
        = ∑' w, (if Rv v w then μ w else 0)
            * rE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp := by
          refine tsum_congr fun w => ?_
          rw [rE_map_branch_law]
          by_cases hvw : Rv v w <;> simp [labRel, hvw]
    _ = (∑' w, if Rv v w then μ w else 0)
          * rE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := by
          rw [ENNReal.tsum_mul_right]
    _ = rE μ Rv v
          * rE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := rfl

end GraphMarkovMatching
