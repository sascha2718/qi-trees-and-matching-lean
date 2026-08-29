/-
The screen-step rows of the transfer ledger
(`arbitrary_offspring_matching.tex`, `sec:rows`, screen
outputs): a height-`(h+1)` screen integrand at a cell root descends to a
height-`h` pair-level screen integrand through the one-step
decompositions.

* `screen_Zlaw_succ_eq`: a forced member `Z_j` of the zero list descends
  exactly: at a reflexive root compatible with the forced label, the
  dead indicator of `Z_j` at height `h+1` is the dead indicator of the
  square degree toward `Ξ_j` at height `h`, and the diagonal tilt
  descends to the square diagonal tilt (`eq:decomp-forced` on the zero
  event);
* `screen_Tlaw_succ_eq`: a fresh member descends to the mixture: the
  fresh degree factors as `r_μ(v) · r_{Ξ̄}` (`eq:decomp-fresh`), so at a
  charged root the fresh zero event is the mixture zero event;
* `indicator_XiBar_dead_le`: the mixture dead indicator is below the
  dead indicator of any charged component (the zero direction of
  `thm:fresh-mixture`), the move that replaces a `Ξ̄`-zero by a
  successor-screen member `Ξ_j`.
-/
import GraphMarkovMatching.Process.Cells

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ)
  (v0 : V)

/-! ### The two screen-descent rows -/

/-- **Forced screen row** (`sec:rows`, screen outputs, forced
member): at a reflexive root compatible with the forced label, the
height-`(h+1)` dead indicator toward `Z_j`, tilted by the diagonal
inverse degree, integrates to its height-`h` square form. -/
lemma screen_Zlaw_succ_eq (v : V) (hvv : Rv v v) (hv0 : Rv v v0)
    (k j h : ℕ) :
    ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * (rE (muM (varyK μ ν v0) (v, k) (h + 1))
              (fullSim (labRel Rv) (h + 1)) x) ^ (-α))
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (Xi μ ν v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then 1 else 0)
          * (rE (Xi μ ν v0 k h)
              (SquareRel (fullSim (labRel Rv) h)) xp) ^ (-α)) := by
  have hmap : ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * (rE (muM (varyK μ ν v0) (v, k) (h + 1))
              (fullSim (labRel Rv) (h + 1)) x) ^ (-α))
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp) = 0 then 1 else 0)
          * (rE (muM (varyK μ ν v0) (v, k) (h + 1))
              (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)) ^ (-α)) := by
    rw [muM_varyK_succ μ ν v0 v k h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_Zlaw_succ_branch μ ν v0 Rv v k j h xp
  rw [if_pos hv0] at h1
  have h2 := rE_succ_branch (varyK μ ν v0) (labRel Rv) (v, k) (v, k) h xp
  rw [if_pos (show labRel Rv (v, k) (v, k) from hvv),
    pairMix_varyK μ ν v0 v k h] at h2
  rw [h1, h2]

/-- **Fresh screen row** (`sec:rows`, screen outputs, fresh member):
the fresh degree at a branch point factors as `r_μ(v) · r_{Ξ̄}`, so at a
charged reflexive root the height-`(h+1)` dead indicator toward the
fresh law is the dead indicator of the square degree toward the mixture
`Ξ̄`, with the same diagonal tilt descent. -/
lemma screen_Tlaw_succ_eq (v : V) (hvv : Rv v v) (hvpos : rE μ Rv v ≠ 0)
    (k h : ℕ) :
    ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * (rE (muM (varyK μ ν v0) (v, k) (h + 1))
              (fullSim (labRel Rv) (h + 1)) x) ^ (-α))
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then 1 else 0)
          * (rE (Xi μ ν v0 k h)
              (SquareRel (fullSim (labRel Rv) h)) xp) ^ (-α)) := by
  have hmap : ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * ((if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
              then 1 else 0)
          * (rE (muM (varyK μ ν v0) (v, k) (h + 1))
              (fullSim (labRel Rv) (h + 1)) x) ^ (-α))
      = ∑' xp, Xi μ ν v0 k h xp
        * ((if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp) = 0 then 1 else 0)
          * (rE (muM (varyK μ ν v0) (v, k) (h + 1))
              (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)) ^ (-α)) := by
    rw [muM_varyK_succ μ ν v0 v k h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_Tlaw_succ_branch μ ν v0 Rv v k h xp
  have h2 := rE_succ_branch (varyK μ ν v0) (labRel Rv) (v, k) (v, k) h xp
  rw [if_pos (show labRel Rv (v, k) (v, k) from hvv),
    pairMix_varyK μ ν v0 v k h] at h2
  rw [h1, h2]
  by_cases hbar : rE (XiBar μ ν v0 h)
      (SquareRel (fullSim (labRel Rv) h)) xp = 0
  · rw [if_pos (mul_eq_zero_of_right (rE μ Rv v) hbar), if_pos hbar]
  · rw [if_neg (mul_ne_zero hvpos hbar), if_neg hbar]

/-! ### Replacing the mixture zero by a charged component zero -/

/-- **Mixture zero to component zero** (the zero direction of
`thm:fresh-mixture`): the dead indicator of the mixture `Ξ̄` is below the
dead indicator of any component the offspring law charges. -/
lemma indicator_XiBar_dead_le (j : ℕ) (hj : (ν j : ℝ≥0∞) ≠ 0) (h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    (if rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
        then (1 : ℝ≥0∞) else 0)
      ≤ if rE (Xi μ ν v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
          then 1 else 0 := by
  by_cases hbar : rE (XiBar μ ν v0 h)
      (SquareRel (fullSim (labRel Rv) h)) xp = 0
  · have hall : ∀ a, ν a = 0 ∨ rE (Xi μ ν v0 a h)
        (SquareRel (fullSim (labRel Rv) h)) xp = 0 :=
      (show rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
          ↔ ∀ a, ν a = 0 ∨ rE (Xi μ ν v0 a h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0
        from rE_bind_eq_zero_iff ν (fun a => Xi μ ν v0 a h)
          (SquareRel (fullSim (labRel Rv) h)) xp).mp hbar
    have hXi : rE (Xi μ ν v0 j h)
        (SquareRel (fullSim (labRel Rv) h)) xp = 0 :=
      (hall j).resolve_left hj
    exact le_of_eq (by rw [if_pos hbar, if_pos hXi])
  · rw [if_neg hbar]
    exact zero_le

end GraphMarkovMatching
