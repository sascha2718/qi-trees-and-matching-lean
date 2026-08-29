/-
Screen rows with alternative tilts
(`arbitrary_offspring_matching.tex`, `sec:rows`, screen
rows): the height-`(h+1)` dead indicators at a cell root descend to
height-`h` pair-level indicators under an arbitrary tilt `G`, and the
restricted inverse-degree tilts themselves convert across the branch
point.

* `screenG_Zlaw_succ`: the forced dead indicator descends under any
  tilt at a root compatible with the forced label;
* `screenG_Zlaw_succ_far`: at an incompatible root the forced degree
  vanishes identically, so the indicator is one and drops out;
* `screenG_Tlaw_succ`: the fresh dead indicator descends to the mixture
  indicator at a charged root, under any tilt;
* `WresD_Zlaw_succ_branch`: the restricted weight toward a forced law
  converts to its square form, with the root-compatibility indicator;
* `WresD_Tlaw_succ_branch`: the restricted weight toward the fresh law
  converts to the square mixture weight times the root factor
  `r_μ(v)^{-α}` (`eq:decomp-fresh` under the inverse power).
-/
import GraphMarkovMatching.Process.Cells
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ)
  (v0 : V)

/-! ### The screen-descent rows with a generic tilt -/

/-- **Forced screen row, generic tilt** (`sec:rows`, screen rows,
forced member): at a root compatible with the forced label, the
height-`(h+1)` dead indicator toward `Z_j` descends to the height-`h`
square dead indicator toward `Ξ_j`, under any tilt `G`. -/
lemma screenG_Zlaw_succ (v : V) (hv0 : Rv v v0) (k j h : ℕ)
    (G : FullLab (V × ℕ) (h + 1) → ℝ≥0∞) :
    ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * G x)
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (Xi μ ν v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then 1 else 0)
          * G (branch (v, k) xp)) := by
  have hmap : ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * G x)
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp) = 0 then 1 else 0)
          * G (branch (v, k) xp)) := by
    rw [muM_varyK_succ μ ν v0 v k h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_Zlaw_succ_branch μ ν v0 Rv v k j h xp
  rw [if_pos hv0] at h1
  rw [h1]

/-- **Forced screen row, incompatible root**: at a root incompatible
with the forced label the forced degree vanishes identically
(`eq:decomp-forced`), so the dead indicator is one and the tilt passes
through unscreened. -/
lemma screenG_Zlaw_succ_far (v : V) (hv0 : ¬ Rv v v0) (k j h : ℕ)
    (G : FullLab (V × ℕ) (h + 1) → ℝ≥0∞) :
    ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * G x)
      = ∑' xp, Xi μ ν v0 k h xp * G (branch (v, k) xp) := by
  have hmap : ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * G x)
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp) = 0 then 1 else 0)
          * G (branch (v, k) xp)) := by
    rw [muM_varyK_succ μ ν v0 v k h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_Zlaw_succ_branch μ ν v0 Rv v k j h xp
  rw [if_neg hv0] at h1
  rw [h1, if_pos (rfl : (0 : ℝ≥0∞) = 0), one_mul]

/-- **Fresh screen row, generic tilt** (`sec:rows`, screen rows,
fresh member): the fresh degree at a branch point factors as
`r_μ(v) · r_{Ξ̄}` (`eq:decomp-fresh`), so at a charged root the
height-`(h+1)` fresh dead indicator descends to the mixture dead
indicator, under any tilt `G`. -/
lemma screenG_Tlaw_succ (v : V) (hvpos : rE μ Rv v ≠ 0) (k h : ℕ)
    (G : FullLab (V × ℕ) (h + 1) → ℝ≥0∞) :
    ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * G x)
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then 1 else 0)
          * G (branch (v, k) xp)) := by
  have hmap : ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * G x)
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp) = 0 then 1 else 0)
          * G (branch (v, k) xp)) := by
    rw [muM_varyK_succ μ ν v0 v k h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_Tlaw_succ_branch μ ν v0 Rv v k h xp
  rw [h1]
  by_cases hbar : rE (XiBar μ ν v0 h)
      (SquareRel (fullSim (labRel Rv) h)) xp = 0
  · rw [if_pos (mul_eq_zero_of_right (rE μ Rv v) hbar), if_pos hbar]
  · rw [if_neg (mul_ne_zero hvpos hbar), if_neg hbar]

/-! ### Conversion of the alternative tilts across the branch point -/

/-- **Forced tilt conversion** (`sec:rows`, screen rows): the
restricted inverse-degree weight toward a forced law at a branch point
is its square form at the child pair, killed at incompatible roots. -/
lemma WresD_Zlaw_succ_branch (v : V) (u k h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    WresD α (Zlaw μ ν v0 u (h + 1)) (fullSim (labRel Rv) (h + 1))
        (branch (v, k) xp)
      = if Rv v v0 then
          WresD α (Xi μ ν v0 u h) (SquareRel (fullSim (labRel Rv) h)) xp
        else 0 := by
  have h1 := rE_Zlaw_succ_branch μ ν v0 Rv v k u h xp
  by_cases hv : Rv v v0
  · rw [if_pos hv]
    rw [if_pos hv] at h1
    by_cases hxi : rE (Xi μ ν v0 u h)
        (SquareRel (fullSim (labRel Rv) h)) xp = 0
    · rw [WresD, WresD, h1, if_pos hxi, if_pos hxi]
    · have hbr : rE (Zlaw μ ν v0 u (h + 1)) (fullSim (labRel Rv) (h + 1))
          (branch (v, k) xp) ≠ 0 := by
        rw [h1]
        exact hxi
      rw [← rE_rpow_neg_eq_WresD (Zlaw μ ν v0 u (h + 1))
          (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) hbr,
        ← rE_rpow_neg_eq_WresD (Xi μ ν v0 u h)
          (SquareRel (fullSim (labRel Rv) h)) xp hxi, h1]
  · rw [if_neg hv]
    rw [if_neg hv] at h1
    rw [WresD, if_pos h1]

/-- **Fresh tilt conversion** (`sec:rows`, screen rows): at a
charged root the restricted inverse-degree weight toward the fresh law
at a branch point is the root factor `r_μ(v)^{-α}` times the square
mixture weight, by `eq:decomp-fresh` under the inverse power. -/
lemma WresD_Tlaw_succ_branch (v : V) (hvpos : rE μ Rv v ≠ 0) (k h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    WresD α (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
        (branch (v, k) xp)
      = (rE μ Rv v) ^ (-α)
        * WresD α (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp := by
  have h1 := rE_Tlaw_succ_branch μ ν v0 Rv v k h xp
  by_cases hbar : rE (XiBar μ ν v0 h)
      (SquareRel (fullSim (labRel Rv) h)) xp = 0
  · have hz : rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
        (branch (v, k) xp) = 0 := by
      rw [h1, hbar, mul_zero]
    rw [WresD, if_pos hz, WresD, if_pos hbar, mul_zero]
  · have hbr : rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
        (branch (v, k) xp) ≠ 0 := by
      rw [h1]
      exact mul_ne_zero hvpos hbar
    rw [← rE_rpow_neg_eq_WresD (Tlaw μ ν v0 (h + 1))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) hbr,
      ← rE_rpow_neg_eq_WresD (XiBar μ ν v0 h)
        (SquareRel (fullSim (labRel Rv) h)) xp hbar,
      h1, ENNReal.mul_rpow_of_ne_zero hvpos hbar (-α)]

end GraphMarkovMatching
