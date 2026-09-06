/-
The concrete screen-ledger input, part three of six: the descended pair screens, the
one-step descent of every coordinate (`cInterp_cZ_succ_unit` and its tilted forms,
`cInterp_cT_succ_unit_le`, `cInterp_cT_succ_tiltZ_le`) and the multi-member Hall
factorization at the descended pair screens (`cHallOut`).  The routing of the outputs
follows in `StepRouting`.
-/
import GraphMarkovMatching.Composite.StepMatrices

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### The descended pair screens -/

private lemma pmf_exists_ne_zero (ν : PMF ℕ) : ∃ k, (ν k : ℝ≥0∞) ≠ 0 := by
  by_contra hall
  push Not at hall
  have h1 := ν.tsum_coe
  rw [tsum_congr fun k => hall k, tsum_zero] at h1
  exact one_ne_zero h1.symm

section StepRows

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

/-- The descended member cells of a zero-list letter set. -/
noncomputable def cPairLaws (o : Bool) (Z : Finset (Option CtrC))
    (h : ℕ) :
    List (PMF (FullLab (CState V) h × FullLab (CState V) h)) :=
  (cMsL (cKO K1 K2 o) Z).map fun c =>
    cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c h

/-- The descended pair tilt of an optional tilt letter. -/
noncomputable def cPairW (o : Bool) (t : Option (Option CtrC)) (h : ℕ) :
    FullLab (CState V) h × FullLab (CState V) h → ℝ≥0∞ :=
  match t with
  | none => fun _ => 1
  | some (some c3) => WresD α
      (cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c3 h)
      (SquareRel (fullSim (cRel Rv) h))
  | some none => WresD α
      (cXiBar (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 h)
      (SquareRel (fullSim (cRel Rv) h))

/-- The descended pair screen of a source cell. -/
noncomputable def cPairScr (o : Bool) (cs : CtrC)
    (Z : Finset (Option CtrC)) (t : Option (Option CtrC)) (h : ℕ) :
    ℝ≥0∞ :=
  screenE (cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h)
    (SquareRel (fullSim (cRel Rv) h))
    (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h)
    (cPairW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t h)

/-- **The dead-event descent at a compatible charged root**: the joint
height-`(h+1)` dead event of a zero-list letter set descends to the
joint dead event of the member cells. -/
private lemma cDead_descend (o : Bool) {u : V} (hu : Rv u v0)
    (hvpos : rE μ Rv u ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (Z : Finset (Option CtrC)) (h : ℕ) (cs : CtrC)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    (∀ ρ ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1),
        rE ρ (fullSim (cRel Rv) (h + 1)) (branch (u, cs) xp) = 0)
      ↔ ∀ ρ' ∈ cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h,
          rE ρ' (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  constructor
  · intro hall ρ' hρ'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hρ'
    rcases mem_cMsL.mp hc with hz | ⟨hz, k, hk, rfl⟩
    · have h0 := hall _ ((mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
        ⟨some c, hz, rfl⟩)
      rw [cLetO_eq, cLet_some] at h0
      exact (rE_cZ_succ_eq_zero_iff (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv hu cs c h xp).mp h0
    · have h0 := hall _ ((mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
        ⟨none, hz, rfl⟩)
      rw [cLetO_eq, cLet_none] at h0
      have hbar := (rE_cT_succ_eq_zero_iff (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv hvpos cs h xp).mp h0
      exact ((rE_cXiBar_eq_zero_iff_charged (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 h _ xp).mp hbar) k ((hsupB k).mpr hk)
  · intro hcell ρ hρ
    obtain ⟨l, hl, rfl⟩ := (mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mp hρ
    rcases l with _ | c
    · rw [cLetO_eq, cLet_none]
      refine (rE_cT_succ_eq_zero_iff (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv hvpos cs h xp).mpr ?_
      refine (rE_cXiBar_eq_zero_iff_charged (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 h _ xp).mpr fun k hk => ?_
      refine hcell _ (List.mem_map.mpr ⟨CtrC.ord k, ?_, rfl⟩)
      exact mem_cMsL.mpr (Or.inr ⟨hl, k, (hsupB k).mp hk, rfl⟩)
    · rw [cLetO_eq, cLet_some]
      refine (rE_cZ_succ_eq_zero_iff (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv hu cs c h xp).mpr ?_
      exact hcell _ (List.mem_map.mpr
        ⟨c, mem_cMsL.mpr (Or.inl hl), rfl⟩)

/-- **The screen descent below a compatible charged root**, generic
tilt. -/
private lemma cScreen_muM_descend (o : Bool) {u : V} (hu : Rv u v0)
    (hvpos : rE μ Rv u ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (Z : Finset (Option CtrC)) (h : ℕ) (cs : CtrC)
    (G : FullLab (CState V) (h + 1) → ℝ≥0∞) :
    screenE (muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
        (u, cs) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1)) G
      = ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h xp
          * (screenInd (SquareRel (fullSim (cRel Rv) h))
              (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
            * G (branch (u, cs) xp)) := by
  rw [screenE, muM_compK_succ (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
    u cs h,
    tsum_congr fun x => mul_assoc _ _ (G x), tsum_map_mul]
  refine tsum_congr fun xp => ?_
  rw [screenInd, screenInd,
    if_congr (cDead_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hu hvpos
      hsupB Z h cs xp) rfl rfl]

/-- **Frozen-source descent, unit tilt.** -/
lemma cInterp_cZ_succ_unit (o : Bool) (hrefl0 : Rv v0 v0)
    (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (c1 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o (some c1) Z none
      = cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o c1 Z none h := by
  have hvpos : rE μ Rv v0 ≠ 0 := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [cInterp, cTiltW_none, cLetO_eq, cLet_some,
    show cZ (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c1 (h + 1)
      = muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0) (v0, c1)
        (h + 1) from rfl,
    cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hrefl0 hvpos
      hsupB Z h c1 (fun _ => 1),
    cPairScr, screenE]
  exact tsum_congr fun xp => by
    rw [cPairW]
    ring

/-- **Frozen-source descent, frozen tilt.** -/
lemma cInterp_cZ_succ_tiltZ (o : Bool) (hrefl0 : Rv v0 v0)
    (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (c1 c3 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o (some c1) Z
        (some (some c3))
      = cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o c1 Z
          (some (some c3)) h := by
  have hvpos : rE μ Rv v0 ≠ 0 := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [cInterp, cTiltW_some, cLetO_eq, cLet_some,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLet_some,
    show cZ (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c1 (h + 1)
      = muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0) (v0, c1)
        (h + 1) from rfl,
    cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hrefl0 hvpos
      hsupB Z h c1 _,
    cPairScr, screenE]
  refine tsum_congr fun xp => ?_
  have hW := WresD_cZ_succ_branch (cExcO exc1 exc2 (!o)) μ
    (cNuO ν1 ν2 (!o)) v0 Rv α v0 c1 c3 h xp
  rw [if_pos hrefl0] at hW
  rw [hW, cPairW]
  ring

/-- **Frozen-source descent, fresh tilt**: the root price times the
mixture-tilted pair screen. -/
lemma cInterp_cZ_succ_tiltT (o : Bool) (hrefl0 : Rv v0 v0)
    (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (c1 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o (some c1) Z (some none)
      = (rE μ Rv v0) ^ (-α)
        * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o c1 Z
            (some none) h := by
  have hvpos : rE μ Rv v0 ≠ 0 := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [cInterp, cTiltW_some, cLetO_eq, cLet_some,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLet_none,
    show cZ (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c1 (h + 1)
      = muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0) (v0, c1)
        (h + 1) from rfl,
    cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hrefl0 hvpos
      hsupB Z h c1 _,
    cPairScr, screenE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun xp => ?_
  rw [WresD_cT_succ_branch (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
    v0 Rv α hvpos c1 h xp, cPairW]
  ring

/-- **The pair-level weight conversion** (`thm:mixture-tilt-composite`):
the mixture-tilted pair screen splits into `compFloor`-weighted cell
screens. -/
lemma cPairScr_price (o : Bool) (hα0 : 0 ≤ α) (hμ0 : μ v0 ≠ 0)
    (hpairB : ∀ k p, cExcO exc1 exc2 (!o) k = some p →
      ∀ j, j ≤ p.1 → cExcO exc1 exc2 (!o) j = none)
    (hdeclB : ∀ k p, cExcO exc1 exc2 (!o) k = some p →
      cNuO ν1 ν2 (!o) p.1 ≠ 0 ∧ cNuO ν1 ν2 (!o) p.2 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (cs : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z (some none) h
      ≤ ∑ k ∈ cKO K1 K2 (!o), (if cNuO ν1 ν2 (!o) k = 0 then 0
          else compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              k ^ (-α)
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z
                (some (some (CtrC.ord k))) h) := by
  rw [cPairScr]
  exact cPairScreen_price α Rv μ v0 (cExcO exc1 exc2 (!o))
    (cNuO ν1 ν2 (!o)) (cKO K1 K2 (!o)) hα0 hμ0 hpairB hdeclB
    (fun k hk => (hsupB k).mp hk) h _ _

/-- The `PhiDres` moment of a reachable letter pair. -/
private lemma cMomentW_le (hα : 1 ≤ α) (o : Bool) {n h : ℕ}
    {la lb : Option CtrC} (hra : cReachO exc1 exc2 ν1 ν2 o n la)
    (hrb : cReachO exc1 exc2 ν1 ν2 (!o) n lb) :
    ∑' x, cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 la h x
        * WresD α (cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            lb h) (fullSim (cRel Rv) h) x
      ≤ 1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h := by
  rw [show cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 la h
      = cLetO μ v0 exc1 exc2 ν1 ν2 o la h from
      (cLetO_eq μ v0 exc1 exc2 ν1 ν2 o la h).symm,
    show cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 lb h
      = cLetO μ v0 exc1 exc2 ν1 ν2 (!o) lb h from
      (cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o) lb h).symm]
  exact le_trans (tsum_WresD_le hα _ _ _)
    (add_le_add le_rfl (mul_le_mul_right
      (le_cPsi α Rv μ v0 exc1 exc2 ν1 ν2 o n la lb hra hrb h) _))

/-- The restricted pair moment: the cell-tilted moment of a reachable
source cell against a reachable tilt cell. -/
private lemma cPairMomentR (hα : 1 ≤ α) (o : Bool) {n h : ℕ}
    (ca cb : CtrC)
    (hra0 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp0 (cExcO exc1 exc2 o) ca))
    (hra1 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp1 (cExcO exc1 exc2 o) ca))
    (hrb0 : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1)
      (cComp0 (cExcO exc1 exc2 (!o)) cb))
    (hrb1 : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1)
      (cComp1 (cExcO exc1 exc2 (!o)) cb)) :
    ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 ca h xp
        * WresD α (cXi (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            cb h) (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  set R := fullSim (cRel Rv) h
  rw [cXi_eq_prod (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 ca h,
    cXi_eq_prod (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 cb h]
  set ρa := cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
    (cComp0 (cExcO exc1 exc2 o) ca) h
  set ρb := cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
    (cComp1 (cExcO exc1 exc2 o) ca) h
  set ρe := cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
    (cComp0 (cExcO exc1 exc2 (!o)) cb) h
  set ρf := cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
    (cComp1 (cExcO exc1 exc2 (!o)) cb) h
  have hmom : ∀ (la : Option CtrC) (lb : Option CtrC),
      cReachO exc1 exc2 ν1 ν2 o (n + 1) la →
      cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) lb →
      (∑' x, cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 la h x
          * WresD α (cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
              v0 lb h) R x)
        ≤ 1 + ENNReal.ofReal α
            * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h := by
    intro la lb hla hlb
    exact cMomentW_le α Rv μ v0 exc1 exc2 ν1 ν2 hα o hla hlb
  calc ∑' xp, prodPMF ρa ρb xp
        * WresD α (prodPMF ρe ρf) (SquareRel R) xp
      ≤ ∑' xp : FullLab (CState V) h × FullLab (CState V) h,
          (prodPMF ρa ρb xp
              * (WresD α ρe R xp.1 * WresD α ρf R xp.2)
            + prodPMF ρa ρb xp
              * (WresD α ρf R xp.1 * WresD α ρe R xp.2)) := by
        refine ENNReal.tsum_le_tsum fun xp => ?_
        calc prodPMF ρa ρb xp * WresD α (prodPMF ρe ρf) (SquareRel R) xp
            ≤ prodPMF ρa ρb xp
                * (WresD α ρe R xp.1 * WresD α ρf R xp.2
                  + WresD α ρf R xp.1 * WresD α ρe R xp.2) :=
              mul_le_mul_right (WresD_square_le_sum hα0 ρe ρf R xp) _
          _ = _ := by ring
    _ = (∑' xp : FullLab (CState V) h × FullLab (CState V) h,
          prodPMF ρa ρb xp
            * (WresD α ρe R xp.1 * WresD α ρf R xp.2))
        + ∑' xp : FullLab (CState V) h × FullLab (CState V) h,
            prodPMF ρa ρb xp
              * (WresD α ρf R xp.1 * WresD α ρe R xp.2) :=
        ENNReal.tsum_add
    _ ≤ (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          * (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
        + (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          * (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
        refine add_le_add ?_ ?_
        · rw [tsum_congr fun xp : FullLab (CState V) h
                × FullLab (CState V) h => show prodPMF ρa ρb xp
                * (WresD α ρe R xp.1 * WresD α ρf R xp.2)
              = (ρa xp.1 * WresD α ρe R xp.1)
                * (ρb xp.2 * WresD α ρf R xp.2) from by
              rw [prodPMF_apply]
              ring,
            tsum_prod_split (fun x => ρa x * WresD α ρe R x)
              (fun x => ρb x * WresD α ρf R x)]
          exact mul_le_mul' (hmom _ _ hra0 hrb0) (hmom _ _ hra1 hrb1)
        · rw [tsum_congr fun xp : FullLab (CState V) h
                × FullLab (CState V) h => show prodPMF ρa ρb xp
                * (WresD α ρf R xp.1 * WresD α ρe R xp.2)
              = (ρa xp.1 * WresD α ρf R xp.1)
                * (ρb xp.2 * WresD α ρe R xp.2) from by
              rw [prodPMF_apply]
              ring,
            tsum_prod_split (fun x => ρa x * WresD α ρf R x)
              (fun x => ρb x * WresD α ρe R x)]
          exact mul_le_mul' (hmom _ _ hra0 hrb1) (hmom _ _ hra1 hrb0)
    _ = cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
        rw [cPairMoment]
        ring

/-- The zero-list successor set of a nonempty zero list is nonempty. -/
lemma cZSuccR_nonempty (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)
    (Kf : Finset ℕ) (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ Kf)
    {Z : Finset (Option CtrC)} (hZne : Z.Nonempty) :
    (cZSuccR exc Kf Z).Nonempty := by
  obtain ⟨l, hl⟩ := hZne
  rcases l with _ | c
  · obtain ⟨k, hk⟩ := pmf_exists_ne_zero ν
    exact ⟨cComp0 exc (CtrC.ord k), mem_cZSuccR.mpr
      ⟨CtrC.ord k, mem_cMsL.mpr (Or.inr ⟨hl, k, (hsup k).mp hk, rfl⟩),
        Or.inl rfl⟩⟩
  · exact ⟨cComp0 exc c, mem_cZSuccR.mpr
      ⟨c, mem_cMsL.mpr (Or.inl hl), Or.inl rfl⟩⟩

/-- **The Hall output of a descended pair screen** (`thm:hall-factor`
at the composite cells): a product-tilted pair screen of a reachable
source cell splits into the two full-list coordinates of the lifted
successor at the pair moment, plus the quadratic singleton charge. -/
lemma cHallOut (hα : 1 ≤ α) (o : Bool) (n h : ℕ) (c : CtrC)
    {Z : Finset (Option CtrC)}
    (hsc0 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp0 (cExcO exc1 exc2 o) c))
    (hsc1 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp1 (cExcO exc1 exc2 o) c))
    (hZ : ∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l) (hZne : Z.Nonempty)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    {t0 t1 : Option (Option CtrC)}
    (ht0 : ∀ l ∈ t0, cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l)
    (ht1 : ∀ l ∈ t1, cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l)
    (hb0 : cComp0 (cExcO exc1 exc2 o) c ∈ cLetterBox N)
    (hb1 : cComp1 (cExcO exc1 exc2 o) c ∈ cLetterBox N)
    (hZb : ∀ l ∈ Z, l ∈ cLetterBox N)
    (hZSb : ∀ l' ∈ cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z,
      l' ∈ cLetterBox N)
    (ht0b : ∀ l ∈ t0, l ∈ cLetterBox N)
    (ht1b : ∀ l ∈ t1, l ∈ cLetterBox N) :
    ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c h xp
        * (screenInd (SquareRel (fullSim (cRel Rv) h))
            (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
          * (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t0 h xp.1
            * cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t1 h xp.2))
      ≤ (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          * (cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
              (cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o))
                (cKO K1 K2 (!o)) Z) ht0b)
            + cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
              (cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o))
                (cKO K1 K2 (!o)) Z) ht1b))
        + ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          * ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j) := by
  set R := fullSim (cRel Rv) h with hR
  set b := ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j with hbdef
  set a1 := 1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
    with ha1
  set G0 := cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t0 h with hG0
  set G1 := cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t1 h with hG1
  set ZS := cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z with hZS
  set eA := cExcO exc1 exc2 o with heA
  set nA := cNuO ν1 ν2 o with hnA
  set eB := cExcO exc1 exc2 (!o) with heB
  set nB := cNuO ν1 ν2 (!o) with hnB
  set ρa := cLet eA μ nA v0 (cComp0 eA c) h with hρa
  set ρb := cLet eA μ nA v0 (cComp1 eA c) h with hρb
  set ms := (cMsL (cKO K1 K2 (!o)) Z).map fun c' =>
    (cLet eB μ nB v0 (cComp0 eB c') h,
      cLet eB μ nB v0 (cComp1 eB c') h) with hms
  set zsL := (cCompL eB (cKO K1 K2 (!o)) Z).map fun l =>
    cLet eB μ nB v0 l h with hzsL
  have hZSre : ∀ l' ∈ ZS, cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l' :=
    cZSuccR_reach exc1 exc2 ν1 ν2 K1 K2 hZ hsupB
  have hZSne : ZS.Nonempty := cZSuccR_nonempty eB nB (cKO K1 K2 (!o))
    hsupB hZne
  -- the full-list screens are the successor coordinates
  have hfull : ∀ (ρ : PMF (FullLab (CState V) h)) (s' : Option CtrC)
      (hs' : s' ∈ cLetterBox N)
      (hres : cReachO exc1 exc2 ν1 ν2 o (n + 1) s')
      (heq : ρ = cLet eA μ nA v0 s' h)
      (t' : Option (Option CtrC))
      (ht' : ∀ l ∈ t', cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l)
      (ht'b : ∀ l ∈ t', l ∈ cLetterBox N),
      screenE ρ R zsL (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)
        ≤ cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hs' ZS ht'b) := by
    intro ρ s' hs' hres heq t' ht' ht'b
    subst heq
    have hcongr : screenE (cLet eA μ nA v0 s' h) R zsL
        (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)
        = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s' ZS t' := by
      rw [cInterp, cLetO_eq]
      refine screenE_congr_mem _ _ (fun ρ' => ?_) _
      rw [mem_cZLaws, hzsL, List.mem_map]
      constructor
      · rintro ⟨l, hlz, rfl⟩
        exact ⟨l, mem_cZSuccR.mpr (mem_cCompL.mp hlz),
          by rw [cLetO_eq]⟩
      · rintro ⟨l, hlz, rfl⟩
        exact ⟨l, mem_cCompL.mpr (mem_cZSuccR.mp hlz),
          by rw [cLetO_eq]⟩
    rw [hcongr]
    exact cInterp_le_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o hs'
      (fun l hl => hZSb l hl) ht'b (n := n + 1)
      ⟨hres, hZSre, ht', hZSne⟩
  -- the moments
  have hmom : ∀ (ρ : PMF (FullLab (CState V) h)) (s' : Option CtrC)
      (hres : cReachO exc1 exc2 ν1 ν2 o (n + 1) s')
      (heq : ρ = cLet eA μ nA v0 s' h) (t' : Option (Option CtrC))
      (ht' : ∀ l ∈ t', cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l),
      (∑' x, ρ x * cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h x)
        ≤ a1 := by
    intro ρ s' hres heq t' ht'
    subst heq
    rcases t' with _ | l3
    · rw [cTiltW_none]
      refine le_trans (le_of_eq ?_) le_self_add
      rw [tsum_congr fun x =>
        mul_one (cLet eA μ nA v0 s' h x), PMF.tsum_coe]
    · rw [cTiltW_some, cLetO_eq]
      exact cMomentW_le α Rv μ v0 exc1 exc2 ν1 ν2 hα o hres
        (ht' l3 rfl)
  -- the singleton sums
  have hsing : ∀ (ρ : PMF (FullLab (CState V) h)) (s' : Option CtrC)
      (hs' : s' ∈ cLetterBox N)
      (hres : cReachO exc1 exc2 ν1 ν2 o (n + 1) s')
      (heq : ρ = cLet eA μ nA v0 s' h) (t' : Option (Option CtrC))
      (ht' : ∀ l ∈ t', cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l)
      (ht'b : ∀ l ∈ t', l ∈ cLetterBox N),
      ((zsL.map fun ρ' => screenE ρ R [ρ']
          (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).sum)
        ≤ (cLz N K1 K2 : ℝ≥0∞) * b := by
    intro ρ s' hs' hres heq t' ht' ht'b
    subst heq
    have hlen : (zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h) R [ρ']
        (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).length
        ≤ cLz N K1 K2 := by
      rw [List.length_map, hzsL, List.length_map]
      refine le_trans (cCompL_length_le eB (cKO K1 K2 (!o)) Z) ?_
      rw [cLz]
      refine Nat.mul_le_mul_left 2 (Nat.mul_le_mul ?_ ?_)
      · exact Finset.card_le_card fun l hl => hZb l hl
      · exact max_le (cKO_card_le_cMx K1 K2 (!o)) (one_le_cMx K1 K2)
    have hmemb : ∀ x ∈ zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h)
        R [ρ'] (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h), x ≤ b := by
      intro x hx
      obtain ⟨ρ', hρ', rfl⟩ := List.mem_map.mp hx
      rw [hzsL, List.mem_map] at hρ'
      obtain ⟨l, hlz, rfl⟩ := hρ'
      have hlre : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l := by
        obtain ⟨c', hc', hor⟩ := mem_cCompL.mp hlz
        exact cMsL_comp_reach exc1 exc2 ν1 ν2 K1 K2 hZ hsupB hc' hor
      have hlb : l ∈ cLetterBox N :=
        hZSb l (mem_cZSuccR.mpr (mem_cCompL.mp hlz))
      have hval : screenE (cLet eA μ nA v0 s' h) R
          [cLet eB μ nB v0 l h]
          (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)
          = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s' {l} t' := by
        rw [cInterp, cLetO_eq]
        refine screenE_congr_mem _ _ (fun ρ'' => ?_) _
        rw [mem_cZLaws, List.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨l, Finset.mem_singleton_self _, by rw [cLetO_eq]⟩
        · rintro ⟨l', hl', rfl⟩
          rw [Finset.mem_singleton.mp hl', cLetO_eq]
      rw [hval, hbdef]
      refine le_trans (cInterp_le_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o
        hs' (fun l' hl' => by
          rw [Finset.mem_singleton.mp hl']
          exact hlb) ht'b (n := n + 1)
        ⟨hres, fun l' hl' => by
          rw [Finset.mem_singleton.mp hl']
          exact hlre, ht', Finset.singleton_nonempty _⟩) (le_iSup _ _)
    calc (zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h) R [ρ']
          (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).sum
        ≤ (zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h) R [ρ']
            (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).length • b :=
          List.sum_le_card_nsmul _ _ hmemb
      _ = ((zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h) R [ρ']
            (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).length
              : ℝ≥0∞) * b := nsmul_eq_mul _ _
      _ ≤ (cLz N K1 K2 : ℝ≥0∞) * b :=
          mul_le_mul_left (Nat.cast_le.mpr hlen) b
  -- assemble through the Hall factorization
  have hind : ∀ xp : FullLab (CState V) h × FullLab (CState V) h,
      screenInd (SquareRel R)
        (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
      = if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
          then 1 else 0 := by
    intro xp
    rw [screenInd]
    refine if_congr ⟨fun hall p hp => ?_, fun hall ρ hρ => ?_⟩ rfl rfl
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hp
      have := hall _ (List.mem_map.mpr ⟨c', hc', rfl⟩)
      rwa [cXi_eq_prod] at this
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hρ
      rw [cXi_eq_prod]
      exact hall _ (List.mem_map.mpr ⟨c', hc', rfl⟩)
  have hmem : ∀ p ∈ ms, p.1 ∈ zsL ∧ p.2 ∈ zsL := by
    intro p hp
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hp
    exact ⟨List.mem_map.mpr ⟨_, mem_cCompL.mpr ⟨c', hc', Or.inl rfl⟩,
        rfl⟩,
      List.mem_map.mpr ⟨_, mem_cCompL.mpr ⟨c', hc', Or.inr rfl⟩, rfl⟩⟩
  have hcov : ∀ ρ ∈ zsL, ∃ p ∈ ms, ρ = p.1 ∨ ρ = p.2 := by
    intro ρ hρ
    obtain ⟨l, hlz, rfl⟩ := List.mem_map.mp hρ
    obtain ⟨c', hc', hor⟩ := mem_cCompL.mp hlz
    refine ⟨_, List.mem_map.mpr ⟨c', hc', rfl⟩, ?_⟩
    rcases hor with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  calc ∑' xp, cXi eA μ nA v0 c h xp
        * (screenInd (SquareRel R)
            (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
          * (G0 xp.1 * G1 xp.2))
      = ∑' xp, prodPMF ρa ρb xp
          * ((if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
              then 1 else 0) * (G0 xp.1 * G1 xp.2)) := by
        rw [cXi_eq_prod eA μ nA v0 c h]
        exact tsum_congr fun xp => by rw [hind xp]
    _ ≤ screenE ρa R zsL G0 * (∑' x, ρb x * G1 x)
        + (∑' x, ρa x * G0 x) * screenE ρb R zsL G1
        + (zsL.map fun ρ => screenE ρa R [ρ] G0).sum
          * (zsL.map fun ρ' => screenE ρb R [ρ'] G1).sum :=
        hallFactorize ρa ρb R ms zsL hmem hcov G0 G1
    _ ≤ cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hb0 ZS ht0b) * a1
        + a1 * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hb1 ZS ht1b)
        + ((cLz N K1 K2 : ℝ≥0∞) * b) * ((cLz N K1 K2 : ℝ≥0∞) * b) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul'
            (hfull ρa _ hb0 hsc0 hρa t0 ht0 ht0b)
            (hmom ρb _ hsc1 hρb t1 ht1)
        · exact mul_le_mul' (hmom ρa _ hsc0 hρa t0 ht0)
            (hfull ρb _ hb1 hsc1 hρb t1 ht1 ht1b)
        · exact mul_le_mul' (hsing ρa _ hb0 hsc0 hρa t0 ht0 ht0b)
            (hsing ρb _ hb1 hsc1 hρb t1 ht1 ht1b)
    _ ≤ a1 * (cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hb0 ZS ht0b)
          + cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hb1 ZS ht1b))
        + ((cLz N K1 K2 : ℝ≥0∞) * b) * ((cLz N K1 K2 : ℝ≥0∞) * b) := by
        refine add_le_add (le_of_eq ?_) le_rfl
        ring

private lemma mul_ind_mul_le {X : Type} {a w : ℝ≥0∞}
    (R : X → X → Prop) (zs : List (PMF X)) (x : X) :
    a * screenInd R zs x * w ≤ a * w := by
  calc a * screenInd R zs x * w
      ≤ a * 1 * w :=
        mul_le_mul_left (mul_le_mul_right (screenInd_le_one R zs x) a) w
    _ = a * w := by rw [mul_one]

lemma cPairScr_eq_tsum (o : Bool) (cs : CtrC)
    (Z : Finset (Option CtrC)) (t : Option (Option CtrC)) (h : ℕ) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z t h
      = ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h xp
          * (screenInd (SquareRel (fullSim (cRel Rv) h))
              (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
            * cPairW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t h xp) := by
  rw [cPairScr, screenE]
  exact tsum_congr fun xp => mul_assoc _ _ _

/-- **Fresh-source descent, unit tilt**: far roots inject into the far
mass, near roots into the retained mixture of descended pair
screens. -/
lemma cInterp_cT_succ_unit_le (o : Bool) (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o none Z none
      ≤ (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞))
        + ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o (CtrC.ord k) Z
                none h := by
  rw [cInterp, cTiltW_none, cLetO_eq, cLet_none,
    cT_eq_freshQ_bind (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 (h + 1),
    screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ (cNuO ν1 ν2 o) s
        * screenE (muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
            (s.1, CtrC.ord s.2) (h + 1)) (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1)) (fun _ => 1)
      ≤ (if Rv s.1 v0 then 0 else freshQ μ (cNuO ν1 ν2 o) s)
        + freshQ μ (cNuO ν1 ν2 o) s
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z none h := by
    rintro ⟨w, k⟩
    by_cases hw : Rv w v0
    · rw [if_pos hw, zero_add]
      refine mul_le_mul_right (le_of_eq ?_) _
      rw [cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hw
        (rE_near_ne_zero Rv μ v0 hμ0 hw) hsupB Z h (CtrC.ord k)
        (fun _ => 1),
        cPairScr_eq_tsum]
      rfl
    · rw [if_neg hw]
      refine le_trans ?_ le_self_add
      exact le_trans (mul_le_mul_right (screenE_unit_le_one _ _ _) _)
        (le_of_eq (mul_one _))
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · calc ∑' s : V × ℕ, (if Rv s.1 v0 then 0
          else freshQ μ (cNuO ν1 ν2 o) s)
        = ∑' s : V × ℕ,
            (if Rv s.1 v0 then 0 else (μ s.1 : ℝ≥0∞))
              * cNuO ν1 ν2 o s.2 := by
          refine tsum_congr fun s => ?_
          by_cases hv : Rv s.1 v0
          · rw [if_pos hv, if_pos hv, zero_mul]
          · rw [if_neg hv, if_neg hv]
            exact prodPMF_apply μ (cNuO ν1 ν2 o) s
      _ = (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞))
          * ∑' l, (cNuO ν1 ν2 o l : ℝ≥0∞) :=
          tsum_prod_split
            (fun v => if Rv v v0 then 0 else (μ v : ℝ≥0∞))
            (fun l => (cNuO ν1 ν2 o l : ℝ≥0∞))
      _ = ∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞) := by
          rw [(cNuO ν1 ν2 o).tsum_coe, mul_one]
  · calc ∑' s : V × ℕ, freshQ μ (cNuO ν1 ν2 o) s
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z none h
        = ∑' s : V × ℕ, (μ s.1 : ℝ≥0∞) * (cNuO ν1 ν2 o s.2
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord s.2) Z none h) := by
          refine tsum_congr fun s => ?_
          rw [show freshQ μ (cNuO ν1 ν2 o) s
              = μ s.1 * cNuO ν1 ν2 o s.2 from
              prodPMF_apply μ (cNuO ν1 ν2 o) s, mul_assoc]
      _ = (∑' v, (μ v : ℝ≥0∞)) * ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z none h :=
          tsum_prod_split (fun v => (μ v : ℝ≥0∞))
            (fun k => cNuO ν1 ν2 o k
              * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                  (CtrC.ord k) Z none h)
      _ = ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z none h := by
          rw [PMF.tsum_coe, one_mul]

/-- **Fresh-source descent, frozen tilt**: the frozen tilt kills the
far roots. -/
lemma cInterp_cT_succ_tiltZ_le (o : Bool) (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (c3 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o none Z (some (some c3))
      ≤ ∑' k, cNuO ν1 ν2 o k
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o (CtrC.ord k) Z
              (some (some c3)) h := by
  rw [cInterp, cTiltW_some, cLetO_eq, cLet_none,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLet_some,
    cT_eq_freshQ_bind (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 (h + 1),
    screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ (cNuO ν1 ν2 o) s
        * screenE (muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
            (s.1, CtrC.ord s.2) (h + 1)) (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
            (WresD α (cZ (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              c3 (h + 1)) (fullSim (cRel Rv) (h + 1)))
      ≤ freshQ μ (cNuO ν1 ν2 o) s
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z (some (some c3)) h := by
    rintro ⟨w, k⟩
    by_cases hw : Rv w v0
    · refine mul_le_mul_right (le_of_eq ?_) _
      rw [cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hw
        (rE_near_ne_zero Rv μ v0 hμ0 hw) hsupB Z h (CtrC.ord k) _,
        cPairScr_eq_tsum]
      refine tsum_congr fun xp => ?_
      have hW := WresD_cZ_succ_branch (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv α w (CtrC.ord k) c3 h xp
      rw [if_pos hw] at hW
      rw [hW, cPairW]
    · have h0 : screenE (muM (compK (cExcO exc1 exc2 o) μ
          (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1))
          (fullSim (cRel Rv) (h + 1))
          (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
          (WresD α (cZ (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            c3 (h + 1)) (fullSim (cRel Rv) (h + 1))) = 0 := by
        refine le_antisymm ?_ zero_le
        calc screenE (muM (compK (cExcO exc1 exc2 o) μ
              (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1))
              (fullSim (cRel Rv) (h + 1))
              (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
              (WresD α (cZ (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
                v0 c3 (h + 1)) (fullSim (cRel Rv) (h + 1)))
            ≤ ∑' x, muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
                (w, CtrC.ord k) (h + 1) x
                * WresD α (cZ (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0 c3 (h + 1))
                    (fullSim (cRel Rv) (h + 1)) x := by
              rw [screenE]
              exact ENNReal.tsum_le_tsum fun x => mul_ind_mul_le _ _ x
          _ = ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
                (CtrC.ord k) h xp
                * WresD α (cZ (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0 c3 (h + 1))
                    (fullSim (cRel Rv) (h + 1))
                    (branch (w, CtrC.ord k) xp) := by
              rw [muM_compK_succ]
              exact tsum_map_mul _ _ _
          _ = 0 := by
              refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
              have hW := WresD_cZ_succ_branch (cExcO exc1 exc2 (!o)) μ
                (cNuO ν1 ν2 (!o)) v0 Rv α w (CtrC.ord k) c3 h xp
              rw [if_neg hw] at hW
              rw [hW, mul_zero]
      rw [h0, mul_zero]
      exact zero_le
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  calc ∑' s : V × ℕ, freshQ μ (cNuO ν1 ν2 o) s
        * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
            (CtrC.ord s.2) Z (some (some c3)) h
      = ∑' s : V × ℕ, (μ s.1 : ℝ≥0∞) * (cNuO ν1 ν2 o s.2
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z (some (some c3)) h) := by
        refine tsum_congr fun s => ?_
        rw [show freshQ μ (cNuO ν1 ν2 o) s
            = μ s.1 * cNuO ν1 ν2 o s.2 from
            prodPMF_apply μ (cNuO ν1 ν2 o) s, mul_assoc]
    _ = (∑' v, (μ v : ℝ≥0∞)) * ∑' k, cNuO ν1 ν2 o k
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord k) Z (some (some c3)) h :=
        tsum_prod_split (fun v => (μ v : ℝ≥0∞))
          (fun k => cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z (some (some c3)) h)
    _ = ∑' k, cNuO ν1 ν2 o k
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord k) Z (some (some c3)) h := by
        rw [PMF.tsum_coe, one_mul]

/-- **Fresh-source descent, fresh tilt**: far roots inject into the far
tilt at the priced pair moment, near roots into the root price times
the retained mixture of mixture-tilted pair screens. -/
lemma cInterp_cT_succ_tiltT_le (o : Bool) (hα : 1 ≤ α)
    (hμ0 : μ v0 ≠ 0)
    (hpairB : ∀ k p, cExcO exc1 exc2 (!o) k = some p →
      ∀ j, j ≤ p.1 → cExcO exc1 exc2 (!o) j = none)
    (hdeclB : ∀ k p, cExcO exc1 exc2 (!o) k = some p →
      cNuO ν1 ν2 (!o) p.1 ≠ 0 ∧ cNuO ν1 ν2 (!o) p.2 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    {T RT : ℝ≥0∞}
    (hT : cTiltSum α (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    {n : ℕ} (hfrA : cReachO exc1 exc2 ν1 ν2 o n none)
    (hfrB : cReachO exc1 exc2 ν1 ν2 (!o) n none)
    (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o none Z (some none)
      ≤ (∑' v, if Rv v v0 then 0
            else (μ v : ℝ≥0∞) * WresD α μ Rv v)
          * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))
        + RT * ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o (CtrC.ord k) Z
                (some none) h := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hmix : ∀ k : ℕ, (cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0 →
      (∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
          (CtrC.ord k) h xp
        * WresD α (cXiBar (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
            v0 h) (SquareRel (fullSim (cRel Rv) h)) xp)
      ≤ T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
    intro k hk
    refine le_trans (tsum_WresD_cXiBar_le_sum (cExcO exc1 exc2 (!o)) μ
      (cNuO ν1 ν2 (!o)) v0 hpairB hdeclB hμ0 hα0 Rv h _) ?_
    calc ∑' k', (if cNuO ν1 ν2 (!o) k' = 0 then 0 else
          compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              k' ^ (-α)
            * ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
                (CtrC.ord k) h xp
              * WresD α (cXi (cExcO exc1 exc2 (!o)) μ
                  (cNuO ν1 ν2 (!o)) v0 (CtrC.ord k') h)
                  (SquareRel (fullSim (cRel Rv) h)) xp)
        ≤ ∑' k', (if cNuO ν1 ν2 (!o) k' = 0 then 0 else
            compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
                k' ^ (-α))
              * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
          refine ENNReal.tsum_le_tsum fun k' => ?_
          by_cases hk' : cNuO ν1 ν2 (!o) k' = 0
          · rw [if_pos hk', if_pos hk', zero_mul]
          · rw [if_neg hk', if_neg hk']
            refine mul_le_mul_right ?_ _
            refine cPairMomentR α Rv μ v0 exc1 exc2 ν1 ν2 hα o
              (CtrC.ord k) (CtrC.ord k') (n := n) ?_ ?_ ?_ ?_
            · exact cReachO_spawn exc1 exc2 ν1 ν2 hfrA
                ⟨k, hk, Or.inl rfl⟩
            · exact cReachO_spawn exc1 exc2 ν1 ν2 hfrA
                ⟨k, hk, Or.inr rfl⟩
            · exact cReachO_spawn exc1 exc2 ν1 ν2 hfrB
                ⟨k', hk', Or.inl rfl⟩
            · exact cReachO_spawn exc1 exc2 ν1 ν2 hfrB
                ⟨k', hk', Or.inr rfl⟩
      _ = (∑' k', if cNuO ν1 ν2 (!o) k' = 0 then 0 else
            compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
                k' ^ (-α))
            * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) :=
          ENNReal.tsum_mul_right
      _ ≤ T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) :=
          mul_le_mul_left hT _
  rw [cInterp, cTiltW_some, cLetO_eq, cLet_none,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLet_none,
    cT_eq_freshQ_bind (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 (h + 1),
    screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ (cNuO ν1 ν2 o) s
        * screenE (muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
            (s.1, CtrC.ord s.2) (h + 1)) (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
            (WresD α (cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              (h + 1)) (fullSim (cRel Rv) (h + 1)))
      ≤ (if Rv s.1 v0 then 0
          else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1
            * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))
            * cNuO ν1 ν2 o s.2)
        + freshQ μ (cNuO ν1 ν2 o) s
          * (RT * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z (some none) h) := by
    rintro ⟨w, k⟩
    by_cases hνk : (cNuO ν1 ν2 o k : ℝ≥0∞) = 0
    · have hfq : freshQ μ (cNuO ν1 ν2 o) (w, k) = 0 := by
        rw [show freshQ μ (cNuO ν1 ν2 o) (w, k)
            = μ w * cNuO ν1 ν2 o k from
            prodPMF_apply μ (cNuO ν1 ν2 o) (w, k), hνk, mul_zero]
      rw [hfq, zero_mul]
      exact zero_le
    by_cases hw : Rv w v0
    · rw [if_pos hw, zero_add]
      refine mul_le_mul_right ?_ _
      have hvpos : rE μ Rv w ≠ 0 := rE_near_ne_zero Rv μ v0 hμ0 hw
      rw [cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hw hvpos
        hsupB Z h (CtrC.ord k) _]
      calc ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
            (CtrC.ord k) h xp
            * (screenInd (SquareRel (fullSim (cRel Rv) h))
                (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
              * WresD α (cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
                  v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
                  (branch (w, CtrC.ord k) xp))
          = (rE μ Rv w) ^ (-α)
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z (some none) h := by
            rw [cPairScr_eq_tsum, ← ENNReal.tsum_mul_left]
            refine tsum_congr fun xp => ?_
            rw [WresD_cT_succ_branch (cExcO exc1 exc2 (!o)) μ
              (cNuO ν1 ν2 (!o)) v0 Rv α hvpos (CtrC.ord k) h xp,
              cPairW]
            ring
        _ ≤ RT * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord k) Z (some none) h :=
            mul_le_mul_left (hRT w hw) _
    · rw [if_neg hw]
      refine le_trans ?_ le_self_add
      by_cases hvr : rE μ Rv w = 0
      · have h0 : ∀ x, WresD α (cT (cExcO exc1 exc2 (!o)) μ
            (cNuO ν1 ν2 (!o)) v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
            (branch (w, CtrC.ord k)
              x) = 0 := by
          intro x
          rw [WresD, if_pos]
          rw [rE_cT_succ_branch Rv (cExcO exc1 exc2 (!o)) μ
            (cNuO ν1 ν2 (!o)) v0 w (CtrC.ord k) h x, hvr, zero_mul]
        have hz : screenE (muM (compK (cExcO exc1 exc2 o) μ
            (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1))
            (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
            (WresD α (cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              (h + 1)) (fullSim (cRel Rv) (h + 1))) = 0 := by
          refine le_antisymm ?_ zero_le
          calc _ ≤ ∑' x, muM (compK (cExcO exc1 exc2 o) μ
                (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1) x
                * WresD α (cT (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0 (h + 1))
                    (fullSim (cRel Rv) (h + 1)) x := by
                rw [screenE]
                exact ENNReal.tsum_le_tsum fun x => mul_ind_mul_le _ _ x
            _ = ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
                  (CtrC.ord k) h xp
                  * WresD α (cT (cExcO exc1 exc2 (!o)) μ
                      (cNuO ν1 ν2 (!o)) v0 (h + 1))
                      (fullSim (cRel Rv) (h + 1))
                      (branch (w, CtrC.ord k) xp) := by
                rw [muM_compK_succ]
                exact tsum_map_mul _ _ _
            _ = 0 := ENNReal.tsum_eq_zero.mpr fun xp => by
                rw [h0 xp, mul_zero]
        rw [hz, mul_zero]
        exact zero_le
      · have hscr : screenE (muM (compK (cExcO exc1 exc2 o) μ
            (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1))
            (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
            (WresD α (cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              (h + 1)) (fullSim (cRel Rv) (h + 1)))
            ≤ (rE μ Rv w) ^ (-α)
              * (T * cPairMoment α
                  (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)) := by
          calc _ ≤ ∑' x, muM (compK (cExcO exc1 exc2 o) μ
                (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1) x
                * WresD α (cT (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0 (h + 1))
                    (fullSim (cRel Rv) (h + 1)) x := by
                rw [screenE]
                exact ENNReal.tsum_le_tsum fun x => mul_ind_mul_le _ _ x
            _ = (rE μ Rv w) ^ (-α)
                * ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
                    (CtrC.ord k) h xp
                  * WresD α (cXiBar (cExcO exc1 exc2 (!o)) μ
                      (cNuO ν1 ν2 (!o)) v0 h)
                      (SquareRel (fullSim (cRel Rv) h)) xp := by
                rw [muM_compK_succ, tsum_map_mul _ _ _,
                  ← ENNReal.tsum_mul_left]
                refine tsum_congr fun xp => ?_
                rw [WresD_cT_succ_branch (cExcO exc1 exc2 (!o)) μ
                  (cNuO ν1 ν2 (!o)) v0 Rv α hvr (CtrC.ord k) h xp]
                ring
            _ ≤ (rE μ Rv w) ^ (-α)
                * (T * cPairMoment α
                    (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)) :=
                mul_le_mul_right (hmix k hνk) _
        calc freshQ μ (cNuO ν1 ν2 o) (w, k) * _
            ≤ freshQ μ (cNuO ν1 ν2 o) (w, k)
              * ((rE μ Rv w) ^ (-α)
                * (T * cPairMoment α
                    (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))) :=
              mul_le_mul_right hscr _
          _ = (μ w : ℝ≥0∞) * WresD α μ Rv w
              * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))
              * cNuO ν1 ν2 o k := by
              rw [show freshQ μ (cNuO ν1 ν2 o) (w, k)
                  = μ w * cNuO ν1 ν2 o k from
                  prodPMF_apply μ (cNuO ν1 ν2 o) (w, k),
                ← rE_rpow_neg_eq_WresD μ Rv w hvr]
              ring
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · calc ∑' s : V × ℕ, (if Rv s.1 v0 then 0
          else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1
            * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))
            * cNuO ν1 ν2 o s.2)
        = ∑' s : V × ℕ,
            ((if Rv s.1 v0 then 0
              else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1)
              * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)))
              * cNuO ν1 ν2 o s.2 := by
          refine tsum_congr fun s => ?_
          by_cases hv : Rv s.1 v0
          · rw [if_pos hv, if_pos hv, zero_mul, zero_mul]
          · rw [if_neg hv, if_neg hv]
      _ = ((∑' v, if Rv v v0 then 0
            else (μ v : ℝ≥0∞) * WresD α μ Rv v)
          * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)))
          * ∑' l, (cNuO ν1 ν2 o l : ℝ≥0∞) := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_prod_split
            (fun v => (if Rv v v0 then 0
                else (μ v : ℝ≥0∞) * WresD α μ Rv v)
              * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)))
            (fun l => (cNuO ν1 ν2 o l : ℝ≥0∞))
      _ = (∑' v, if Rv v v0 then 0
            else (μ v : ℝ≥0∞) * WresD α μ Rv v)
          * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)) := by
          rw [(cNuO ν1 ν2 o).tsum_coe, mul_one]
  · calc ∑' s : V × ℕ, freshQ μ (cNuO ν1 ν2 o) s
          * (RT * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z (some none) h)
        = ∑' s : V × ℕ, (μ s.1 : ℝ≥0∞) * (RT * (cNuO ν1 ν2 o s.2
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord s.2) Z (some none) h)) := by
          refine tsum_congr fun s => ?_
          rw [show freshQ μ (cNuO ν1 ν2 o) s
              = μ s.1 * cNuO ν1 ν2 o s.2 from
              prodPMF_apply μ (cNuO ν1 ν2 o) s]
          ring
      _ = (∑' v, (μ v : ℝ≥0∞)) * ∑' k, RT * (cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z (some none) h) :=
          tsum_prod_split (fun v => (μ v : ℝ≥0∞))
            (fun k => RT * (cNuO ν1 ν2 o k
              * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                  (CtrC.ord k) Z (some none) h))
      _ = RT * ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z (some none) h := by
          rw [PMF.tsum_coe, one_mul, ENNReal.tsum_mul_left]

end StepRows

end Composite
end GraphMarkovMatching
