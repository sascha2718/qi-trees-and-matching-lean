/-
The screen-descent layer of the composite ledger
(`arbitrary_offspring_matching.tex`, `sec:composite`, the screen rows
entering `thm:composite-ledger`): the height-`(h+1)` zero events and
restricted inverse-degree tilts at the composite laws descend to
height-`h` pair-level objects, mirroring the one-law rows of
`Process/ScreenTilt` at the two-sided composite kernel.

Setting: source side pack `(exc1, μ, ν1, v0)`, target side pack
`(exc2, μ, ν2, v0)`, state relation `cRel Rv`.  The branch
decompositions `rE_cZ_succ_branch`/`rE_cT_succ_branch` and the mixture
identity `rE_cXiBar_eq_zero_iff` are those of `CellStep`; the
ledger-form pruning of the mirrored letter pairs lives in `Bridge`.

* `rE_cXiBar_eq_zero_iff_charged`: the mixture-dead identity in charged
  form, the fresh cell mixture dies exactly when every charged component
  dies; exceptional components stay first-class members of the mixture;
* `rE_cZ_succ_eq_zero_iff`, `rE_cT_succ_eq_zero_iff`: the one-step
  descent of the zero event per target letter;
* `WresD_cZ_succ_branch`, `WresD_cT_succ_branch`: the restricted
  inverse-degree tilts convert across the branch point.
-/
import GraphMarkovMatching.Composite.Support
import GraphMarkovMatching.Composite.CellStep
import GraphMarkovMatching.Process.ZMass

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

section OneSide

variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)
  (Rv : V → V → Prop)

/-! ### The mixture-dead identity -/

/-- The charged form: death against the mixture is joint death against
every charged component. -/
lemma rE_cXiBar_eq_zero_iff_charged (h : ℕ)
    (R : (FullLab (CState V) h × FullLab (CState V) h)
      → (FullLab (CState V) h × FullLab (CState V) h) → Prop)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cXiBar exc μ ν v0 h) R xp = 0
      ↔ ∀ k, (ν k : ℝ≥0∞) ≠ 0
          → rE (cXi exc μ ν v0 (CtrC.ord k) h) R xp = 0 := by
  rw [rE_cXiBar_eq_zero_iff exc μ ν v0 h R xp]
  exact forall_congr' fun k => or_iff_not_imp_left

/-! ### The zero-event descent per target letter -/

/-- The zero event of a frozen target descends across a compatible
root: uniform in the tagged counter. -/
lemma rE_cZ_succ_eq_zero_iff {u : V} (hv0 : Rv u v0) (cs c : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 c (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (cXi exc μ ν v0 c h) (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cZ_succ_branch Rv exc μ ν v0 u cs c h xp, if_pos hv0]

/-- The zero event of the fresh target descends across a charged root
to the mixture zero event. -/
lemma rE_cT_succ_eq_zero_iff {u : V} (hvpos : rE μ Rv u ≠ 0) (cs : CtrC)
    (h : ℕ) (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cT exc μ ν v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (cXiBar exc μ ν v0 h)
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cT_succ_branch Rv exc μ ν v0 u cs h xp]
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 hvpos
    · exact h0
  · intro h0
    rw [h0, mul_zero]

/-! ### The restricted tilt conversions across the branch point -/

/-- **Frozen tilt conversion**: the restricted inverse-degree weight
toward a frozen target law at a branch point is its square form at the
child pair, killed at incompatible roots. -/
lemma WresD_cZ_succ_branch (α : ℝ) (u : V) (cs c : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    WresD α (cZ exc μ ν v0 c (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp)
      = if Rv u v0 then
          WresD α (cXi exc μ ν v0 c h)
            (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 := by
  have h1 := rE_cZ_succ_branch Rv exc μ ν v0 u cs c h xp
  by_cases hv : Rv u v0
  · rw [if_pos hv]
    rw [if_pos hv] at h1
    by_cases hxi : rE (cXi exc μ ν v0 c h)
        (SquareRel (fullSim (cRel Rv) h)) xp = 0
    · rw [WresD, WresD, h1, if_pos hxi, if_pos hxi]
    · have hbr : rE (cZ exc μ ν v0 c (h + 1)) (fullSim (cRel Rv) (h + 1))
          (branch (u, cs) xp) ≠ 0 := by
        rw [h1]
        exact hxi
      rw [← rE_rpow_neg_eq_WresD (cZ exc μ ν v0 c (h + 1))
          (fullSim (cRel Rv) (h + 1)) (branch (u, cs) xp) hbr,
        ← rE_rpow_neg_eq_WresD (cXi exc μ ν v0 c h)
          (SquareRel (fullSim (cRel Rv) h)) xp hxi, h1]
  · rw [if_neg hv]
    rw [if_neg hv] at h1
    rw [WresD, if_pos h1]

/-- **Fresh tilt conversion**: at a charged root the restricted
inverse-degree weight toward the fresh law at a branch point is the
root factor `r_μ(u)^{-α}` times the square mixture weight. -/
lemma WresD_cT_succ_branch (α : ℝ) {u : V} (hvpos : rE μ Rv u ≠ 0)
    (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    WresD α (cT exc μ ν v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp)
      = (rE μ Rv u) ^ (-α)
        * WresD α (cXiBar exc μ ν v0 h)
            (SquareRel (fullSim (cRel Rv) h)) xp := by
  have h1 := rE_cT_succ_branch Rv exc μ ν v0 u cs h xp
  by_cases hbar : rE (cXiBar exc μ ν v0 h)
      (SquareRel (fullSim (cRel Rv) h)) xp = 0
  · have hz : rE (cT exc μ ν v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0 := by
      rw [h1, hbar, mul_zero]
    rw [WresD, if_pos hz, WresD, if_pos hbar, mul_zero]
  · have hbr : rE (cT exc μ ν v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) ≠ 0 := by
      rw [h1]
      exact mul_ne_zero hvpos hbar
    rw [← rE_rpow_neg_eq_WresD (cT exc μ ν v0 (h + 1))
        (fullSim (cRel Rv) (h + 1)) (branch (u, cs) xp) hbr,
      ← rE_rpow_neg_eq_WresD (cXiBar exc μ ν v0 h)
        (SquareRel (fullSim (cRel Rv) h)) xp hbar,
      h1, ENNReal.mul_rpow_of_ne_zero hvpos hbar (-α)]

end OneSide

end Composite
end GraphMarkovMatching
