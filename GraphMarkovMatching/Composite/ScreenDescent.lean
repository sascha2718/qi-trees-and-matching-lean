/-
The screen-descent layer of the composite ledger
(`arbitrary_offspring_matching.tex`, `sec:composite`, the screen rows
entering `thm:composite-ledger`): height-`(h+1)` dead indicators,
screens, and dead masses at the composite laws descend to height-`h`
pair-level objects,
mirroring the one-law rows of `VaryingScreenStep`, `VaryingScreenTilt`,
and `VaryingZMass` at the two-sided composite kernel.

Setting: source side pack `(exc1, μ, ν1, v0)`, target side pack
`(exc2, μ, ν2, v0)`, state relation `cRel Rv`.  The screen functional is
`screenE` of `VaryingScreens`; degrees are the good degree `rE`.  The
branch decompositions `rE_cZ_succ_branch`/`rE_cT_succ_branch` and the
mixture identity `rE_cXiBar_eq_zero_iff` are those of `CellStep`; the
ledger-form pruning of the mirrored letter pairs lives in `Bridge`.

* `cFlaw`, `rE_cFlaw_succ_branch`: the exposed cell law, a `μ`-root
  with the counter fixed, and its one-step branch decomposition;
* `rE_cXiBar_eq_zero_iff_charged`, `indicator_cXiBar_dead_le`: the
  mixture-dead identity in charged form, the fresh cell mixture dies
  exactly when every charged component dies; exceptional components
  stay first-class members of the mixture;
* `rE_cZ_succ_eq_zero_iff`, `rE_cT_succ_eq_zero_iff`,
  `rE_cFlaw_succ_eq_zero_iff`, `memInd_cZ_ord_of_ge` ...
  `memInd_cZ_mark_le_two`: the one-step descent of the zero event per
  target letter, the member pairs read off the cell shapes of `Kernel`,
  marker shapes included;
* `screenG_cZ_succ`, `screenG_cZ_succ_far`, `screenG_cT_succ`,
  `screenG_cFlaw_succ`, `screen_cZ_succ_eq`, `screen_cT_succ_eq`: the
  screen-step rows under a generic tilt and under the diagonal tilt;
* `WresD_cZ_succ_branch`, `WresD_cT_succ_branch`: the restricted
  inverse-degree tilts convert across the branch point;
* `cZMass_cZ_succ`, `cZMass_cT_succ`, `cDeadMass_factorize`: the
  zero-mass rows and the unit-tilt Hall factorization at the composite
  laws;
* `rE_ne_zero_of_rel`, `screenE_muM_mirror_mem`: mirror pruning
  (`thm:exact-pruning` at the screen functional) below an arbitrary safe
  root state, a screen whose zero list contains the mirror partner of
  its source law is exactly zero, by the support witness of `Support`.
-/
import GraphMarkovMatching.Composite.Support
import GraphMarkovMatching.Composite.CellStep
import GraphMarkovMatching.Process.ScreenStep
import GraphMarkovMatching.Process.ScreenTilt
import GraphMarkovMatching.Process.ZMass

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

/-- Witness positivity: a related charged target point makes the good
degree positive. -/
lemma rE_ne_zero_of_rel {X : Type} {ρ : PMF X} {R : X → X → Prop}
    {x y : X} (hxy : R x y) (hy : ρ y ≠ 0) : rE ρ R x ≠ 0 :=
  simDeg_ne_zero hxy hy

section OneSide

variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)
  (Rv : V → V → Prop)

/-- The exposed cell law of a counter: a `μ`-root with the counter
fixed.  The composite analogue of `Flaw`. -/
noncomputable def cFlaw (k h : ℕ) : PMF (FullLab (CState V) h) :=
  μ.bind fun w => muM (compK exc μ ν v0) (w, CtrC.ord k) h

/-- **The exposed branch decomposition**: the degree toward an exposed
cell law at a branch point factors as the root degree times the pair
degree toward the cell of its counter. -/
lemma rE_cFlaw_succ_branch (u : V) (cs : CtrC) (k h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cFlaw exc μ ν v0 k (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp)
      = rE μ Rv u
        * rE (cXi exc μ ν v0 (CtrC.ord k) h)
            (SquareRel (fullSim (cRel Rv) h)) xp := by
  rw [cFlaw, rE_bind]
  calc ∑' w, μ w
        * rE (muM (compK exc μ ν v0) (w, CtrC.ord k) (h + 1))
            (fullSim (cRel Rv) (h + 1)) (branch (u, cs) xp)
      = ∑' w, (if Rv u w then μ w else 0)
          * rE (cXi exc μ ν v0 (CtrC.ord k) h)
              (SquareRel (fullSim (cRel Rv) h)) xp := by
        refine tsum_congr fun w => ?_
        rw [rE_succ_branch (compK exc μ ν v0) (cRel Rv) (u, cs)
            (w, CtrC.ord k) h xp, pairMix_compK]
        by_cases hw : Rv u w
        · rw [if_pos (show cRel Rv (u, cs) (w, CtrC.ord k) from hw),
            if_pos hw]
        · rw [if_neg (show ¬ cRel Rv (u, cs) (w, CtrC.ord k) from hw),
            if_neg hw, mul_zero, zero_mul]
    _ = (∑' w, if Rv u w then μ w else 0)
        * rE (cXi exc μ ν v0 (CtrC.ord k) h)
            (SquareRel (fullSim (cRel Rv) h)) xp :=
      ENNReal.tsum_mul_right
    _ = rE μ Rv u
        * rE (cXi exc μ ν v0 (CtrC.ord k) h)
            (SquareRel (fullSim (cRel Rv) h)) xp := rfl

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

/-- **Mixture zero to component zero**: the dead indicator of the fresh
cell mixture is below the dead indicator of any charged component. -/
lemma indicator_cXiBar_dead_le (j : ℕ) (hj : (ν j : ℝ≥0∞) ≠ 0) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    (if rE (cXiBar exc μ ν v0 h)
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 then (1 : ℝ≥0∞) else 0)
      ≤ if rE (cXi exc μ ν v0 (CtrC.ord j) h)
            (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0 := by
  by_cases hbar : rE (cXiBar exc μ ν v0 h)
      (SquareRel (fullSim (cRel Rv) h)) xp = 0
  · have hXi : rE (cXi exc μ ν v0 (CtrC.ord j) h)
        (SquareRel (fullSim (cRel Rv) h)) xp = 0 :=
      (((rE_cXiBar_eq_zero_iff exc μ ν v0 h
          (SquareRel (fullSim (cRel Rv) h)) xp).mp hbar) j).resolve_left hj
    exact le_of_eq (by rw [if_pos hbar, if_pos hXi])
  · rw [if_neg hbar]
    exact zero_le

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

/-- The zero event of an exposed target descends across a charged root
to the zero event of its cell. -/
lemma rE_cFlaw_succ_eq_zero_iff {u : V} (hvpos : rE μ Rv u ≠ 0) (cs : CtrC)
    (k h : ℕ) (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cFlaw exc μ ν v0 k (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (cXi exc μ ν v0 (CtrC.ord k) h)
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cFlaw_succ_branch exc μ ν v0 Rv u cs k h xp]
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 hvpos
    · exact h0
  · intro h0
    rw [h0, mul_zero]

/-- Forced member, balanced counter at least four: the member pair is
the two balanced halves. -/
lemma memInd_cZ_ord_of_ge {u : V} (hv0 : Rv u v0) {j : ℕ}
    (hj : exc j = none) (h4 : 4 ≤ j) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.ord j) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (prodPMF (cZ exc μ ν v0 (CtrC.ord (j / 2)) h)
            (cZ exc μ ν v0 (CtrC.ord (j - j / 2)) h))
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cZ_succ_eq_zero_iff exc μ ν v0 Rv hv0 cs (CtrC.ord j) h xp,
    cXi_ord_none_of_ge exc μ ν v0 hj h4 h]

/-- Forced member, counter three: the member pair is the forced two and
a fresh subtree. -/
lemma memInd_cZ_ord_three {u : V} (hv0 : Rv u v0) {j : ℕ}
    (hj : exc j = none) (h3 : j = 3) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.ord j) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h) (cT exc μ ν v0 h))
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cZ_succ_eq_zero_iff exc μ ν v0 Rv hv0 cs (CtrC.ord j) h xp,
    cXi_ord_none_three exc μ ν v0 hj h3 h]

/-- Forced member, counter at most two: the member pair is two fresh
subtrees. -/
lemma memInd_cZ_ord_le_two {u : V} (hv0 : Rv u v0) {j : ℕ}
    (hj : exc j = none) (h2 : j ≤ 2) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.ord j) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (prodPMF (cT exc μ ν v0 h) (cT exc μ ν v0 h))
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cZ_succ_eq_zero_iff exc μ ν v0 Rv hv0 cs (CtrC.ord j) h xp,
    cXi_ord_none_le_two exc μ ν v0 hj h2 h]

/-- Exceptional member: the zero event descends to the stage-zero
marker cell of its declared pair. -/
lemma memInd_cZ_ord_exc {u : V} (hv0 : Rv u v0) {z : ℕ} {p : ℕ × ℕ}
    (hz : exc z = some p) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.ord z) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (cXi exc μ ν v0 (CtrC.mark p.1 p.2 0) h)
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cZ_succ_eq_zero_iff exc μ ν v0 Rv hv0 cs (CtrC.ord z) h xp,
    cXi_ord_exc exc μ ν v0 hz h]

/-- Marked member, running value at least four: deterministic children,
the next marker and the balanced remainder. -/
lemma memInd_cZ_mark_of_ge {u : V} (hv0 : Rv u v0) {a b i : ℕ}
    (hval : 4 ≤ val a i) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.mark a b i) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (prodPMF (cZ exc μ ν v0 (CtrC.mark a b (i + 1)) h)
            (cZ exc μ ν v0 (CtrC.ord (val a i - val a i / 2)) h))
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cZ_succ_eq_zero_iff exc μ ν v0 Rv hv0 cs (CtrC.mark a b i) h xp,
    cXi_mark_of_ge exc μ ν v0 hval h]

/-- Marked member, running value three: deterministic children, the
forced two and the port continuation. -/
lemma memInd_cZ_mark_three {u : V} (hv0 : Rv u v0) {a b i : ℕ}
    (hval : val a i = 3) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.mark a b i) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
            (cZ exc μ ν v0 (CtrC.ord b) h))
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cZ_succ_eq_zero_iff exc μ ν v0 Rv hv0 cs (CtrC.mark a b i) h xp,
    cXi_mark_three exc μ ν v0 hval h]

/-- Marked member, running value at most two: the port continuation
plus a fresh subtree. -/
lemma memInd_cZ_mark_le_two {u : V} (hv0 : Rv u v0) {a b i : ℕ}
    (hval : val a i ≤ 2) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.mark a b i) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (u, cs) xp) = 0
      ↔ rE (prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h))
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cZ_succ_eq_zero_iff exc μ ν v0 Rv hv0 cs (CtrC.mark a b i) h xp,
    cXi_mark_le_two exc μ ν v0 hval h]

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

/-! ### The two-sided screen-step rows -/

section TwoSided

variable (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)

/-- **Frozen screen row, generic tilt**: at a root compatible with the
forced label, the height-`(h+1)` dead indicator toward a frozen target
law descends to the height-`h` square dead indicator toward its cell,
under any tilt `G`. -/
lemma screenG_cZ_succ (u : V) (hv0 : Rv u v0) (c₁ c₂ : CtrC) (h : ℕ)
    (G : FullLab (CState V) (h + 1) → ℝ≥0∞) :
    ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * G x)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cXi exc2 μ ν2 v0 c₂ h)
                (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * G (branch (u, c₁) xp)) := by
  have hmap : ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * G x)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1))
                (branch (u, c₁) xp) = 0 then 1 else 0)
          * G (branch (u, c₁) xp)) := by
    rw [muM_compK_succ exc1 μ ν1 v0 u c₁ h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_cZ_succ_branch Rv exc2 μ ν2 v0 u c₁ c₂ h xp
  rw [if_pos hv0] at h1
  rw [h1]

/-- **Frozen screen row, incompatible root**: at a root incompatible
with the forced label the frozen target degree vanishes identically, so
the dead indicator is one and the tilt passes through unscreened. -/
lemma screenG_cZ_succ_far (u : V) (hv0 : ¬ Rv u v0) (c₁ c₂ : CtrC) (h : ℕ)
    (G : FullLab (CState V) (h + 1) → ℝ≥0∞) :
    ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * G x)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp * G (branch (u, c₁) xp) := by
  have hmap : ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * G x)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1))
                (branch (u, c₁) xp) = 0 then 1 else 0)
          * G (branch (u, c₁) xp)) := by
    rw [muM_compK_succ exc1 μ ν1 v0 u c₁ h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_cZ_succ_branch Rv exc2 μ ν2 v0 u c₁ c₂ h xp
  rw [if_neg hv0] at h1
  rw [h1, if_pos (rfl : (0 : ℝ≥0∞) = 0), one_mul]

/-- **Fresh screen row, generic tilt**: at a charged root the
height-`(h+1)` fresh dead indicator descends to the mixture dead
indicator, under any tilt `G`. -/
lemma screenG_cT_succ (u : V) (hvpos : rE μ Rv u ≠ 0) (c₁ : CtrC) (h : ℕ)
    (G : FullLab (CState V) (h + 1) → ℝ≥0∞) :
    ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * G x)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cXiBar exc2 μ ν2 v0 h)
                (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * G (branch (u, c₁) xp)) := by
  have hmap : ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * G x)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
                (branch (u, c₁) xp) = 0 then 1 else 0)
          * G (branch (u, c₁) xp)) := by
    rw [muM_compK_succ exc1 μ ν1 v0 u c₁ h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  rw [rE_cT_succ_branch Rv exc2 μ ν2 v0 u c₁ h xp]
  by_cases hbar : rE (cXiBar exc2 μ ν2 v0 h)
      (SquareRel (fullSim (cRel Rv) h)) xp = 0
  · rw [if_pos (mul_eq_zero_of_right (rE μ Rv u) hbar), if_pos hbar]
  · rw [if_neg (mul_ne_zero hvpos hbar), if_neg hbar]

/-- **Exposed screen row, generic tilt**: at a charged root the
height-`(h+1)` dead indicator toward an exposed cell law descends to
the dead indicator of the cell of its counter, under any tilt `G`. -/
lemma screenG_cFlaw_succ (u : V) (hvpos : rE μ Rv u ≠ 0) (c₁ : CtrC)
    (k h : ℕ) (G : FullLab (CState V) (h + 1) → ℝ≥0∞) :
    ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cFlaw exc2 μ ν2 v0 k (h + 1))
                (fullSim (cRel Rv) (h + 1)) x = 0 then 1 else 0)
          * G x)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cXi exc2 μ ν2 v0 (CtrC.ord k) h)
                (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * G (branch (u, c₁) xp)) := by
  have hmap : ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cFlaw exc2 μ ν2 v0 k (h + 1))
                (fullSim (cRel Rv) (h + 1)) x = 0 then 1 else 0)
          * G x)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cFlaw exc2 μ ν2 v0 k (h + 1))
                (fullSim (cRel Rv) (h + 1)) (branch (u, c₁) xp) = 0
              then 1 else 0)
          * G (branch (u, c₁) xp)) := by
    rw [muM_compK_succ exc1 μ ν1 v0 u c₁ h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  rw [rE_cFlaw_succ_branch exc2 μ ν2 v0 Rv u c₁ k h xp]
  by_cases hxi : rE (cXi exc2 μ ν2 v0 (CtrC.ord k) h)
      (SquareRel (fullSim (cRel Rv) h)) xp = 0
  · rw [if_pos (mul_eq_zero_of_right (rE μ Rv u) hxi), if_pos hxi]
  · rw [if_neg (mul_ne_zero hvpos hxi), if_neg hxi]

/-- **Frozen screen row, diagonal tilt**: at a reflexive root
compatible with the forced label, the height-`(h+1)` dead indicator
toward a frozen target law, tilted by the diagonal inverse degree,
integrates to its height-`h` square form. -/
lemma screen_cZ_succ_eq (α : ℝ) (u : V) (hvv : Rv u u) (hv0 : Rv u v0)
    (c₁ c₂ : CtrC) (h : ℕ) :
    ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * (rE (muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1))
              (fullSim (cRel Rv) (h + 1)) x) ^ (-α))
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cXi exc2 μ ν2 v0 c₂ h)
                (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * (rE (cXi exc1 μ ν1 v0 c₁ h)
              (SquareRel (fullSim (cRel Rv) h)) xp) ^ (-α)) := by
  have hmap : ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * (rE (muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1))
              (fullSim (cRel Rv) (h + 1)) x) ^ (-α))
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1))
                (branch (u, c₁) xp) = 0 then 1 else 0)
          * (rE (muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1))
              (fullSim (cRel Rv) (h + 1)) (branch (u, c₁) xp)) ^ (-α)) := by
    rw [muM_compK_succ exc1 μ ν1 v0 u c₁ h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_cZ_succ_branch Rv exc2 μ ν2 v0 u c₁ c₂ h xp
  rw [if_pos hv0] at h1
  have h2 := rE_succ_branch (compK exc1 μ ν1 v0) (cRel Rv) (u, c₁) (u, c₁)
    h xp
  rw [if_pos (show cRel Rv (u, c₁) (u, c₁) from hvv),
    pairMix_compK exc1 μ ν1 v0 u c₁ h] at h2
  rw [h1, h2]

/-- **Fresh screen row, diagonal tilt**: at a charged reflexive root
the height-`(h+1)` fresh dead indicator, tilted by the diagonal inverse
degree, integrates to the square mixture form. -/
lemma screen_cT_succ_eq (α : ℝ) (u : V) (hvv : Rv u u)
    (hvpos : rE μ Rv u ≠ 0) (c₁ : CtrC) (h : ℕ) :
    ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * (rE (muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1))
              (fullSim (cRel Rv) (h + 1)) x) ^ (-α))
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cXiBar exc2 μ ν2 v0 h)
                (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * (rE (cXi exc1 μ ν1 v0 c₁ h)
              (SquareRel (fullSim (cRel Rv) h)) xp) ^ (-α)) := by
  have hmap : ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * ((if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)) x
              = 0 then 1 else 0)
          * (rE (muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1))
              (fullSim (cRel Rv) (h + 1)) x) ^ (-α))
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
                (branch (u, c₁) xp) = 0 then 1 else 0)
          * (rE (muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1))
              (fullSim (cRel Rv) (h + 1)) (branch (u, c₁) xp)) ^ (-α)) := by
    rw [muM_compK_succ exc1 μ ν1 v0 u c₁ h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  refine tsum_congr fun xp => ?_
  have h1 := rE_cT_succ_branch Rv exc2 μ ν2 v0 u c₁ h xp
  have h2 := rE_succ_branch (compK exc1 μ ν1 v0) (cRel Rv) (u, c₁) (u, c₁)
    h xp
  rw [if_pos (show cRel Rv (u, c₁) (u, c₁) from hvv),
    pairMix_compK exc1 μ ν1 v0 u c₁ h] at h2
  rw [h1, h2]
  by_cases hbar : rE (cXiBar exc2 μ ν2 v0 h)
      (SquareRel (fullSim (cRel Rv) h)) xp = 0
  · rw [if_pos (mul_eq_zero_of_right (rE μ Rv u) hbar), if_pos hbar]
  · rw [if_neg (mul_ne_zero hvpos hbar), if_neg hbar]

/-! ### The zero-mass rows -/

/-- **Frozen zero-mass row**: at a root compatible with the forced
label, the height-`(h+1)` dead mass toward a frozen target law descends
to the height-`h` pair-level dead mass toward its cell; at an
incompatible root it is one. -/
lemma cZMass_cZ_succ (u : V) (c₁ c₂ : CtrC) (h : ℕ) :
    ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * (if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1)) x
            = 0 then 1 else 0)
      = if Rv u v0 then
          ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
            * (if rE (cXi exc2 μ ν2 v0 c₂ h)
                  (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
        else 1 := by
  have hmap : ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * (if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1)) x
            = 0 then 1 else 0)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * (if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1))
              (branch (u, c₁) xp) = 0 then 1 else 0) := by
    rw [muM_compK_succ exc1 μ ν1 v0 u c₁ h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  by_cases hv : Rv u v0
  · rw [if_pos hv]
    refine tsum_congr fun xp => ?_
    have h1 := rE_cZ_succ_branch Rv exc2 μ ν2 v0 u c₁ c₂ h xp
    rw [if_pos hv] at h1
    rw [h1]
  · rw [if_neg hv]
    have hpt : ∀ xp, cXi exc1 μ ν1 v0 c₁ h xp
        * (if rE (cZ exc2 μ ν2 v0 c₂ (h + 1)) (fullSim (cRel Rv) (h + 1))
              (branch (u, c₁) xp) = 0 then 1 else 0)
        = cXi exc1 μ ν1 v0 c₁ h xp := by
      intro xp
      have h1 := rE_cZ_succ_branch Rv exc2 μ ν2 v0 u c₁ c₂ h xp
      rw [if_neg hv] at h1
      rw [if_pos h1, mul_one]
    rw [tsum_congr hpt, PMF.tsum_coe]

/-- **Fresh zero-mass row**: at an uncharged root the dead mass toward
the fresh law is one, and at a charged root it is the height-`h`
pair-level dead mass toward the fresh cell mixture. -/
lemma cZMass_cT_succ (u : V) (c₁ : CtrC) (h : ℕ) :
    ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * (if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)) x
            = 0 then 1 else 0)
      = if rE μ Rv u = 0 then 1
        else ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
          * (if rE (cXiBar exc2 μ ν2 v0 h)
                (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0) := by
  have hmap : ∑' x, muM (compK exc1 μ ν1 v0) (u, c₁) (h + 1) x
        * (if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)) x
            = 0 then 1 else 0)
      = ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * (if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
              (branch (u, c₁) xp) = 0 then 1 else 0) := by
    rw [muM_compK_succ exc1 μ ν1 v0 u c₁ h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  by_cases hv : rE μ Rv u = 0
  · rw [if_pos hv]
    have hpt : ∀ xp, cXi exc1 μ ν1 v0 c₁ h xp
        * (if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
              (branch (u, c₁) xp) = 0 then 1 else 0)
        = cXi exc1 μ ν1 v0 c₁ h xp := by
      intro xp
      have h1 := rE_cT_succ_branch Rv exc2 μ ν2 v0 u c₁ h xp
      rw [hv, zero_mul] at h1
      rw [if_pos h1, mul_one]
    rw [tsum_congr hpt, PMF.tsum_coe]
  · rw [if_neg hv]
    refine tsum_congr fun xp => ?_
    rw [rE_cT_succ_branch Rv exc2 μ ν2 v0 u c₁ h xp]
    by_cases hbar : rE (cXiBar exc2 μ ν2 v0 h)
        (SquareRel (fullSim (cRel Rv) h)) xp = 0
    · rw [if_pos (mul_eq_zero_of_right (rE μ Rv u) hbar), if_pos hbar]
    · rw [if_neg (mul_ne_zero hv hbar), if_neg hbar]

/-- **Unit-tilt Hall factorization at the composite laws**: the dead
mass of a product target cell under a product source cell is at most
the two unit-tilt two-list screens plus the two products of unit-tilt
singleton screens.  The product shapes are supplied by the cell-shape
equations of `Kernel`. -/
lemma cDeadMass_factorize {h : ℕ} {c₁ c₂ : CtrC}
    {ρa ρb ρc ρd : PMF (FullLab (CState V) h)}
    (hs : cXi exc1 μ ν1 v0 c₁ h = prodPMF ρa ρb)
    (ht : cXi exc2 μ ν2 v0 c₂ h = prodPMF ρc ρd)
    (R : FullLab (CState V) h → FullLab (CState V) h → Prop) :
    ∑' xp : FullLab (CState V) h × FullLab (CState V) h,
        cXi exc1 μ ν1 v0 c₁ h xp
          * (if rE (cXi exc2 μ ν2 v0 c₂ h) (SquareRel R) xp = 0
              then 1 else 0)
      ≤ screenE ρa R [ρc, ρd] (fun _ => 1)
          + screenE ρb R [ρc, ρd] (fun _ => 1)
        + screenE ρa R [ρc] (fun _ => 1) * screenE ρb R [ρc] (fun _ => 1)
        + screenE ρa R [ρd] (fun _ => 1) * screenE ρb R [ρd] (fun _ => 1) := by
  rw [hs, ht]
  exact deadMass_factorize ρa ρb ρc ρd R

/-! ### Mirror pruning at the screen functional (`thm:exact-pruning`) -/

variable (N : ℕ)

/-- **Mirror pruning at a frozen source**: a screen on the frozen law
below a safe root whose zero list contains the frozen law below the
mirrored root is exactly zero, by the support witness. -/
theorem screenE_muM_mirror_mem
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (h : ℕ) {s : CState V} (hs : Safe exc1 ν2 N s)
    (zs : List (PMF (FullLab (CState V) h)))
    (hmem : muM (compK exc2 μ ν2 v0) (mirrorC exc1 s) h ∈ zs)
    (g : FullLab (CState V) h → ℝ≥0∞) :
    screenE (muM (compK exc1 μ ν1 v0) s h) (fullSim (cRel Rv) h) zs g
      = 0 := by
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : muM (compK exc1 μ ν1 v0) s h x = 0
  · rw [hx, zero_mul, zero_mul]
  · obtain ⟨y, hy, hsim⟩ := exists_sim_of_muM_ne_zero Rv μ v0 exc1 exc2
      ν1 ν2 N hRv hμ0 hN hpair hcharged h s hs x hx
    have hind : screenInd (fullSim (cRel Rv) h) zs x = 0 := by
      rw [screenInd,
        if_neg (fun hall => rE_ne_zero_of_rel hsim hy (hall _ hmem))]
    rw [hind, mul_zero, zero_mul]

end TwoSided

end Composite
end GraphMarkovMatching
