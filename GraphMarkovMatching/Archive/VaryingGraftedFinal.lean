/-
Supported-component pruning for the literal grafted 11/13 example.

This file begins the final closure by removing two deliberately crude terms
from the earlier ledger: the component-dead remainder in a fresh target
normalization, and the ordinary-potential charge for a nonlive screen.  Both
terms vanish for the concrete law pair because the selected opposite-side
component supports every charged source atom.
-/
import GraphMarkovMatching.Archive.VaryingGraftedMatrixRoute

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {V : Type}

/-- Supported-component pruning for an inverse-degree mixture.  Unlike the
generic heavy-component estimate, this has no component-dead remainder. -/
lemma screenE_bind_WresD_le_component_of_matching {A X : Type}
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (rhoS : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (a : A) (ha : (w a : ℝ≥0∞) ≠ 0)
    (hsupp : HasMatchingSupport rhoS (f a) R)
    (zs : List (PMF X)) :
    screenE rhoS R zs (WresD alpha (w.bind f) R) ≤
      (w a : ℝ≥0∞) ^ (-alpha) *
        screenE rhoS R zs (WresD alpha (f a) R) := by
  refine (screenE_bind_WresD_le_component_add_screen alpha halpha
    rhoS w f R a ha zs).trans ?_
  rw [screenE_eq_zero_of_matching_mem hsupp (f a :: zs)
    (List.mem_cons_self) (WresD alpha (w.bind f) R), add_zero]

/-- The weaker support condition actually needed by a restricted
fresh-target row: a selected component need only be live on source atoms on
which the whole target mixture is live. -/
lemma screenE_WresD_eq_zero_of_live_support {X : Type}
    (rhoS rhoA rhoT : PMF X) (R : X → X → Prop)
    (hlive : ∀ x, rhoS x ≠ 0 → rE rhoT R x ≠ 0 →
      rE rhoA R x ≠ 0) (alpha : ℝ)
    (zs : List (PMF X)) (hmem : rhoA ∈ zs) :
    screenE rhoS R zs (WresD alpha rhoT R) = 0 := by
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hs : rhoS x = 0
  · simp [hs]
  by_cases ht : rE rhoT R x = 0
  · simp [WresD, ht]
  have ha := hlive x hs ht
  have hi : screenInd R zs x = 0 := by
    rw [screenInd, if_neg]
    intro hall
    exact ha (hall rhoA hmem)
  simp [hi]

/-- Supported-component pruning under the preceding restricted-live
condition.  This is the exact interface still needed for the forced/fresh
ordinary rows of the fixed example. -/
lemma screenE_bind_WresD_le_component_of_live_support {A X : Type}
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (rhoS : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (a : A) (ha : (w a : ℝ≥0∞) ≠ 0)
    (hlive : ∀ x, rhoS x ≠ 0 → rE (w.bind f) R x ≠ 0 →
      rE (f a) R x ≠ 0)
    (zs : List (PMF X)) :
    screenE rhoS R zs (WresD alpha (w.bind f) R) ≤
      (w a : ℝ≥0∞) ^ (-alpha) *
        screenE rhoS R zs (WresD alpha (f a) R) := by
  refine (screenE_bind_WresD_le_component_add_screen alpha halpha
    rhoS w f R a ha zs).trans ?_
  rw [screenE_WresD_eq_zero_of_live_support
    rhoS (f a) (w.bind f) R hlive alpha (f a :: zs)
      List.mem_cons_self, add_zero]

/-- The opposite-side common arity selected for a charged source component.
Common arities are fixed, while the exceptional components use the literal
replacement supports `11 → 7` and `13 → 9`. -/
def graftCompatibleArity (leftSource : Bool) (k : ℕ) : ℕ :=
  if leftSource then (if k = 11 then 7 else k)
  else (if k = 13 then 9 else k)

@[simp] lemma graftCompatibleArity_left_eleven :
    graftCompatibleArity true 11 = 7 := by rfl

@[simp] lemma graftCompatibleArity_right_thirteen :
    graftCompatibleArity false 13 = 9 := by rfl

@[simp] lemma graftCompatibleArity_left_common (i : Fin 4) :
    graftCompatibleArity true (graftCommonArity i) =
      graftCommonArity i := by
  fin_cases i <;> rfl

@[simp] lemma graftCompatibleArity_right_common (i : Fin 4) :
    graftCompatibleArity false (graftCommonArity i) =
      graftCommonArity i := by
  fin_cases i <;> rfl

/-- At every height, each charged source component is supported by the
source-dependent opposite common component selected above. -/
theorem graftXi_compatible_component_support
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (leftSource : Bool) (h k : ℕ)
    (hk : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore) :
    HasMatchingSupport
      (graftXi leftSource mu (if leftSource then nuL else nuR) v0
        (.ordinary k) h)
      (graftXi (!leftSource) mu (if leftSource then nuR else nuL) v0
        (.ordinary (graftCompatibleArity leftSource k)) h)
      (SquareRel (fullSim (graftLabRel Rv) h)) := by
  have hs := graftSupportAt_all Rv mu nuL nuR v0 hrefl hLaw hp11 hp13 h
  rcases hs with ⟨hdiag, hM3, hM5⟩
  cases leftSource with
  | false =>
      change HasMatchingSupport
        (graftXi false mu nuR v0 (.ordinary k) h)
        (graftXi true mu nuL v0
          (.ordinary (if k = 13 then 9 else k)) h)
        (SquareRel (fullSim (graftLabRel Rv) h))
      simp only [graftRareArity, elevenThirteenCommonCore,
        Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · simp only [if_true]
        rw [graftXi_eq_prod_of_fixed_support mu v0 false nuR h 13
            (by simp [graftRareArity]),
          graftXi_eq_prod_of_fixed_support mu v0 true nuL h 9
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .Z4)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hM5 false)
      · simp only [if_neg (by omega : (3 : ℕ) ≠ 13)]
        rw [graftXi_eq_prod_of_fixed_support mu v0 false nuR h 3
            (by simp [elevenThirteenCommonCore]),
          graftXi_eq_prod_of_fixed_support mu v0 true nuL h 3
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .Z2)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .F)
      · simp only [if_neg (by omega : (5 : ℕ) ≠ 13)]
        rw [graftXi_eq_prod_of_fixed_support mu v0 false nuR h 5
            (by simp [elevenThirteenCommonCore]),
          graftXi_eq_prod_of_fixed_support mu v0 true nuL h 5
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .Z2)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .Z3)
      · simp only [if_neg (by omega : (7 : ℕ) ≠ 13)]
        rw [graftXi_eq_prod_of_fixed_support mu v0 false nuR h 7
            (by simp [elevenThirteenCommonCore]),
          graftXi_eq_prod_of_fixed_support mu v0 true nuL h 7
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .Z3)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .Z4)
      · simp only [if_neg (by omega : (9 : ℕ) ≠ 13)]
        rw [graftXi_eq_prod_of_fixed_support mu v0 false nuR h 9
            (by simp [elevenThirteenCommonCore]),
          graftXi_eq_prod_of_fixed_support mu v0 true nuL h 9
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .Z4)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag false .Z5)
  | true =>
      change HasMatchingSupport
        (graftXi true mu nuL v0 (.ordinary k) h)
        (graftXi false mu nuR v0
          (.ordinary (if k = 11 then 7 else k)) h)
        (SquareRel (fullSim (graftLabRel Rv) h))
      simp only [graftRareArity, elevenThirteenCommonCore,
        Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · simp only [if_true]
        rw [graftXi_eq_prod_of_fixed_support mu v0 true nuL h 11
            (by simp [graftRareArity]),
          graftXi_eq_prod_of_fixed_support mu v0 false nuR h 7
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hM3 true)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .Z4)
      · simp only [if_neg (by omega : (3 : ℕ) ≠ 11)]
        rw [graftXi_eq_prod_of_fixed_support mu v0 true nuL h 3
            (by simp [elevenThirteenCommonCore]),
          graftXi_eq_prod_of_fixed_support mu v0 false nuR h 3
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .Z2)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .F)
      · simp only [if_neg (by omega : (5 : ℕ) ≠ 11)]
        rw [graftXi_eq_prod_of_fixed_support mu v0 true nuL h 5
            (by simp [elevenThirteenCommonCore]),
          graftXi_eq_prod_of_fixed_support mu v0 false nuR h 5
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .Z2)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .Z3)
      · simp only [if_neg (by omega : (7 : ℕ) ≠ 11)]
        rw [graftXi_eq_prod_of_fixed_support mu v0 true nuL h 7
            (by simp [elevenThirteenCommonCore]),
          graftXi_eq_prod_of_fixed_support mu v0 false nuR h 7
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .Z3)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .Z4)
      · simp only [if_neg (by omega : (9 : ℕ) ≠ 11)]
        rw [graftXi_eq_prod_of_fixed_support mu v0 true nuL h 9
            (by simp [elevenThirteenCommonCore]),
          graftXi_eq_prod_of_fixed_support mu v0 false nuR h 9
            (by simp [elevenThirteenCommonCore])]
        exact matchingSupport_prod_square
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .Z4)
          (by simpa [graftSupportedPair, graftRarePair, graftBiSource, graftBiTarget] using hdiag true .Z5)

/-- Literal mixture-normalization form of supported-component pruning. -/
theorem graftXiBar_screen_le_compatible_component
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (leftSource : Bool) (h k : ℕ)
    (hk : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore)
    (hmass : ((if leftSource then nuR else nuL)
      (graftCompatibleArity leftSource k) : ℝ≥0∞) ≠ 0)
    (zs : List (PMF
      (FullLab (GraftState V) h × FullLab (GraftState V) h))) :
    screenE
        (graftXi leftSource mu (if leftSource then nuL else nuR) v0
          (.ordinary k) h)
        (SquareRel (fullSim (graftLabRel Rv) h)) zs
        (WresD alpha
          (graftXiBar (!leftSource) mu
            (if leftSource then nuR else nuL) v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h))) ≤
      ((if leftSource then nuR else nuL)
          (graftCompatibleArity leftSource k) : ℝ≥0∞) ^ (-alpha) *
        screenE
          (graftXi leftSource mu (if leftSource then nuL else nuR) v0
            (.ordinary k) h)
          (SquareRel (fullSim (graftLabRel Rv) h)) zs
          (WresD alpha
            (graftXi (!leftSource) mu
              (if leftSource then nuR else nuL) v0
              (.ordinary (graftCompatibleArity leftSource k)) h)
            (SquareRel (fullSim (graftLabRel Rv) h))) := by
  simpa only [graftXiBar] using
    screenE_bind_WresD_le_component_of_matching alpha halpha
      (graftXi leftSource mu (if leftSource then nuL else nuR) v0
        (.ordinary k) h)
      (if leftSource then nuR else nuL)
      (fun j => graftXi (!leftSource) mu
        (if leftSource then nuR else nuL) v0 (.ordinary j) h)
      (SquareRel (fullSim (graftLabRel Rv) h))
      (graftCompatibleArity leftSource k) hmass
      (graftXi_compatible_component_support Rv mu nuL nuR v0 hrefl hLaw
        hp11 hp13 leftSource h k hk) zs

/-- For the fixed law pair, every formally nonlive screen with a nonempty
zero list vanishes exactly.  There is no ordinary-potential remainder. -/
theorem graftNonliveScreen_eq_zero
    (alpha : ℝ) (Rv : V → V → Prop) (mu : PMF V)
    (nuL nuR : PMF ℕ) (v0 : V) {zeta : ℝ≥0∞}
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (sc : GraftScreen)
    (hz : sc.zlist.Nonempty) (hnlive : sc ∉ graftLiveScreens) :
    graftBiScreen alpha Rv mu nuL nuR v0 lr h sc = 0 := by
  have hbad : sc.cell ∈ sc.zlist ∨
      ∃ u, sc.norm = some u ∧ u ∈ sc.zlist := by
    by_contra h
    push Not at h
    apply hnlive
    rw [graftLiveScreens, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hz, h.1, fun u hu => h.2 u hu⟩
  rcases hbad with hcell | ⟨u, hnorm, hu⟩
  · rw [graftBiScreen]
    apply screenE_eq_zero_of_matching_mem
      ((graftSupportAt_all Rv mu nuL nuR v0 hrefl hLaw hp11 hp13 h).1
        lr sc.cell)
    exact List.mem_map.mpr
      ⟨sc.cell, Finset.mem_toList.mpr hcell, rfl⟩
  · rw [graftBiScreen, hnorm, graftBiNorm]
    apply screenE_tilt_mem
    exact List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩

/-- Exact replacement for the earlier common-successor route with an
ordinary-potential charge: nonlive successors are zero. -/
theorem graftSuccessorScreen_le_common_mulVec
    (alpha : ℝ) (Rv : V → V → Prop) (mu : PMF V)
    (nuL nuR : PMF ℕ) (v0 : V) {zeta : ℝ≥0∞}
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (CW : ℝ≥0∞) (i : GraftLedgerIndex) (h : ℕ) (sc' : GraftScreen)
    (hsucc : sc' ∈ graftScreenSuccCommon i.2.val) :
    CW * graftBiScreen alpha Rv mu nuL nuR v0 i.1 h sc' ≤
      mulVecInf (graftCommonN CW)
        (graftE alpha Rv mu nuL nuR v0 h) i := by
  by_cases hlive : sc' ∈ graftLiveScreens
  · exact graftLiveSuccessor_le_common_mulVec alpha Rv mu nuL nuR v0
      CW i h sc' hsucc hlive
  · have hz : sc'.zlist.Nonempty := by
      rw [graftScreenSuccCommon_zlist hsucc]
      exact graftZSuccCommon_nonempty (graftLiveScreen_nonempty i.2)
    rw [graftNonliveScreen_eq_zero alpha Rv mu nuL nuR v0 hrefl hLaw
      hp11 hp13 i.1 h sc' hz hlive, mul_zero]
    exact zero_le

/-- Every nonempty semantic screen is either a live coordinate or is exactly
zero for the fixed law pair. -/
theorem graftScreen_le_graftESup
    (alpha : ℝ) (Rv : V → V → Prop) (mu : PMF V)
    (nuL nuR : PMF ℕ) (v0 : V) {zeta : ℝ≥0∞}
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (sc : GraftScreen) (hz : sc.zlist.Nonempty) :
    graftBiScreen alpha Rv mu nuL nuR v0 lr h sc ≤
      graftESup alpha Rv mu nuL nuR v0 h := by
  by_cases hlive : sc ∈ graftLiveScreens
  · exact graftLiveScreen_le_graftESup alpha Rv mu nuL nuR v0
      lr h sc hlive
  · rw [graftNonliveScreen_eq_zero alpha Rv mu nuL nuR v0 hrefl hLaw
      hp11 hp13 lr h sc hz hlive]
    exact zero_le

/-- List-valued form of `graftScreen_le_graftESup`, convenient for the
factorization lemmas whose zero lists are ordinary lists. -/
theorem graftScreenList_le_graftESup
    (alpha : ℝ) (Rv : V → V → Prop) (mu : PMF V)
    (nuL nuR : PMF ℕ) (v0 : V) {zeta : ℝ≥0∞}
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (s : GraftTgt) (ts : List GraftTgt)
    (hts : ts ≠ []) (norm : Option GraftTgt) :
    screenE (graftBiSource mu nuL nuR v0 lr h s)
        (fullSim (graftLabRel Rv) h)
        (ts.map (graftBiTarget mu nuL nuR v0 lr h))
        (graftBiNorm alpha Rv mu nuL nuR v0 lr h norm) ≤
      graftESup alpha Rv mu nuL nuR v0 h := by
  let sc : GraftScreen := ⟨s, ts.toFinset, norm⟩
  have hz : sc.zlist.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    simpa [sc] using hts
  have hs := graftScreen_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
    hp11 hp13 lr h sc hz
  have hmem : ∀ rho,
      rho ∈ ts.map (graftBiTarget mu nuL nuR v0 lr h) ↔
      rho ∈ sc.zlist.toList.map
        (graftBiTarget mu nuL nuR v0 lr h) := by
    intro rho
    constructor
    · intro hrho
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hrho
      exact List.mem_map.mpr
        ⟨t, Finset.mem_toList.mpr (by simpa [sc] using ht), rfl⟩
    · intro hrho
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hrho
      exact List.mem_map.mpr
        ⟨t, (by simpa [sc] using Finset.mem_toList.mp ht), rfl⟩
  calc
    screenE (graftBiSource mu nuL nuR v0 lr h s)
        (fullSim (graftLabRel Rv) h)
        (ts.map (graftBiTarget mu nuL nuR v0 lr h))
        (graftBiNorm alpha Rv mu nuL nuR v0 lr h norm) =
      screenE (graftBiSource mu nuL nuR v0 lr h s)
        (fullSim (graftLabRel Rv) h)
        (sc.zlist.toList.map (graftBiTarget mu nuL nuR v0 lr h))
        (graftBiNorm alpha Rv mu nuL nuR v0 lr h norm) :=
          screenE_congr_mem _ _ hmem _
    _ = graftBiScreen alpha Rv mu nuL nuR v0 lr h sc := by
      rfl
    _ ≤ _ := hs

/-- Each reverse zero-interface term required by the square-cell inequality
is a singleton screen, hence belongs to the screen envelope. -/
theorem graftBiZMass_le_graftESup
    (alpha : ℝ) (Rv : V → V → Prop) (mu : PMF V)
    (nuL nuR : PMF ℕ) (v0 : V) {zeta : ℝ≥0∞}
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (s t : GraftTgt) :
    graftBiZMass Rv mu nuL nuR v0 lr h (s, t) ≤
      graftESup alpha Rv mu nuL nuR v0 h := by
  let sc : GraftScreen := ⟨s, {t}, none⟩
  have hs := graftScreen_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
    hp11 hp13 lr h sc (Finset.singleton_nonempty t)
  simpa [sc, graftBiScreen, graftBiNorm, graftBiZMass,
    screenE_singleton, zMass] using hs

/-- The literal grafted square-cell row.  All eight directed component
potentials are bounded by `graftPsi`; the four reverse zero masses and the
four resolved singleton screens are bounded by `graftESup`. -/
theorem graftSquare_le_cellCB
    {alpha delta L K : ℝ} (halpha : 1 ≤ alpha) (hdelta : 0 < delta)
    (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ alpha ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * (1 - t) ^ alpha ≤ K)
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ v w, Rv v w → Rv w v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (a b c d : GraftTgt) :
    PhiDres alpha
        (prodPMF (graftBiSource mu nuL nuR v0 lr h a)
          (graftBiSource mu nuL nuR v0 lr h b))
        (prodPMF (graftBiTarget mu nuL nuR v0 lr h c)
          (graftBiTarget mu nuL nuR v0 lr h d))
        (SquareRel (fullSim (graftLabRel Rv) h)) ≤
      cellCB alpha delta L K
        (graftPsi alpha Rv mu nuL nuR v0 h)
        (graftESup alpha Rv mu nuL nuR v0 h)
        (graftESup alpha Rv mu nuL nuR v0 h) := by
  let P := graftPsi alpha Rv mu nuL nuR v0 h
  let E := graftESup alpha Rv mu nuL nuR v0 h
  let R := fullSim (graftLabRel Rv) h
  have hphi : ∀ s t,
      PhiDres alpha
        (graftBiSource mu nuL nuR v0 lr h s)
        (graftBiTarget mu nuL nuR v0 lr h t) R ≤ P := by
    intro s t
    exact graftBiPhi_le_graftPsi alpha Rv mu nuL nuR v0 lr h (s, t)
  have hphirev : ∀ t s,
      PhiDres alpha
        (graftBiTarget mu nuL nuR v0 lr h t)
        (graftBiSource mu nuL nuR v0 lr h s) R ≤ P := by
    intro t s
    cases lr with
    | false =>
        simpa [P, R, graftBiPhi, graftBiSource, graftBiTarget] using
          (graftBiPhi_le_graftPsi alpha Rv mu nuL nuR v0 true h (t, s))
    | true =>
        simpa [P, R, graftBiPhi, graftBiSource, graftBiTarget] using
          (graftBiPhi_le_graftPsi alpha Rv mu nuL nuR v0 false h (t, s))
  have hz : ∀ t s,
      zMass (graftBiTarget mu nuL nuR v0 lr h t)
        (graftBiSource mu nuL nuR v0 lr h s) R ≤ E := by
    intro t s
    cases lr with
    | false =>
        simpa [E, R, graftBiZMass, graftBiSource, graftBiTarget] using
          (graftBiZMass_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
            hp11 hp13 true h t s)
    | true =>
        simpa [E, R, graftBiZMass, graftBiSource, graftBiTarget] using
          (graftBiZMass_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
            hp11 hp13 false h t s)
  have hscr : ∀ s t u,
      screenE (graftBiSource mu nuL nuR v0 lr h s) R
        [graftBiTarget mu nuL nuR v0 lr h t]
        (WresD alpha (graftBiTarget mu nuL nuR v0 lr h u) R) ≤ E := by
    intro s t u
    let sc : GraftScreen := ⟨s, {t}, some u⟩
    have hs := graftScreen_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
      hp11 hp13 lr h sc (Finset.singleton_nonempty t)
    simpa [E, R, sc, graftBiScreen, graftBiNorm] using hs
  refine (PhiDres_square_le halpha hdelta hL0 hL hK0 hK
    (graftBiSource mu nuL nuR v0 lr h a)
    (graftBiSource mu nuL nuR v0 lr h b)
    (graftBiTarget mu nuL nuR v0 lr h c)
    (graftBiTarget mu nuL nuR v0 lr h d) R
    (fullSim_symm (graftLabRel Rv)
      (fun x y hxy => hsymm x.1 y.1 hxy) h) P E
    (hphi a c) (hphi a d) (hphi b c) (hphi b d)
    (hphirev c a) (hphirev c b) (hphirev d a) (hphirev d b)
    (hz c a) (hz c b) (hz d a) (hz d b)).trans ?_
  rw [cellCB]
  refine add_le_add le_rfl ?_
  have hsum :
      screenE (graftBiSource mu nuL nuR v0 lr h a) R
            [graftBiTarget mu nuL nuR v0 lr h c]
            (WresD alpha (graftBiTarget mu nuL nuR v0 lr h d) R) +
          screenE (graftBiSource mu nuL nuR v0 lr h a) R
            [graftBiTarget mu nuL nuR v0 lr h d]
            (WresD alpha (graftBiTarget mu nuL nuR v0 lr h c) R) +
        screenE (graftBiSource mu nuL nuR v0 lr h b) R
          [graftBiTarget mu nuL nuR v0 lr h c]
          (WresD alpha (graftBiTarget mu nuL nuR v0 lr h d) R) +
      screenE (graftBiSource mu nuL nuR v0 lr h b) R
        [graftBiTarget mu nuL nuR v0 lr h d]
        (WresD alpha (graftBiTarget mu nuL nuR v0 lr h c) R) ≤ 4 * E := by
    calc
      _ ≤ E + E + E + E :=
        add_le_add (add_le_add (add_le_add
          (hscr a c d) (hscr a d c)) (hscr b c d)) (hscr b d c)
      _ = 4 * E := by ring
  simpa [P, E, mul_comm] using
    (mul_le_mul_right hsum (1 + ENNReal.ofReal alpha * P))

/-- Jensen decomposition for an arbitrary mixture target.  The second term
is deliberately an existential dead-component screen; it will be replaced
below by the literal five-component union for the fixed laws. -/
lemma PhiDres_bind_le_average_add_dead {A X : Type}
    (alpha : ℝ) (halpha : 1 ≤ alpha)
    (rhoS : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) :
    PhiDres alpha rhoS (w.bind f) R ≤
      (∑' a, (w a : ℝ≥0∞) * PhiDres alpha rhoS (f a) R) +
        ∑' x, rhoS x *
          ((if ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
            then 1 else 0) * WresD alpha (w.bind f) R x) := by
  have halphapos : (0 : ℝ) < alpha := lt_of_lt_of_le one_pos halpha
  have hpt : ∀ x,
      rhoS x *
        (if rE (w.bind f) R x = 0 then 0
          else phiE alpha (q (w.bind f) R x)) ≤
      rhoS x * ∑' a, (w a : ℝ≥0∞) *
          (if rE (f a) R x = 0 then 0 else phiE alpha (q (f a) R x)) +
        rhoS x *
          ((if ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
            then 1 else 0) * WresD alpha (w.bind f) R x) := by
    intro x
    by_cases hres : rE (w.bind f) R x = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      by_cases hdead : ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
      · have hb : phiE alpha (q (w.bind f) R x) ≤
            WresD alpha (w.bind f) R x := by
          rw [phiE_eq_qE_mul_rpow alpha R (w.bind f) halphapos x,
            rE_rpow_neg_eq_WresD (w.bind f) R x hres]
          exact (mul_le_mul_left qE_le_one _).trans_eq (one_mul _)
        refine (mul_le_mul_right hb _).trans ?_
        rw [if_pos hdead, one_mul]
        exact le_add_left le_rfl
      · push Not at hdead
        have hjen : phiE alpha (q (w.bind f) R x) ≤
            ∑' a, (w a : ℝ≥0∞) * phiE alpha (q (f a) R x) := by
          have hq : q (w.bind f) R x =
              (∑' a, (w a : ℝ≥0∞) *
                ENNReal.ofReal (q (f a) R x)).toReal := by
            rw [q, qE_bind]
            congr 1
            exact tsum_congr fun a => by
              rw [show ENNReal.ofReal (q (f a) R x) = qE (f a) R x
                from ENNReal.ofReal_toReal qE_ne_top]
          rw [hq]
          exact phiE_tsum_jensen halpha
            (fun a => (w a : ℝ≥0∞)) (fun a => q (f a) R x)
            w.tsum_coe (fun _ => q_nonneg) (fun _ => q_le_one)
        have hterm : (∑' a, (w a : ℝ≥0∞) * phiE alpha (q (f a) R x)) =
            ∑' a, (w a : ℝ≥0∞) *
              (if rE (f a) R x = 0 then 0 else phiE alpha (q (f a) R x)) := by
          refine tsum_congr fun a => ?_
          by_cases ha : (w a : ℝ≥0∞) = 0
          · simp [ha]
          · rw [if_neg (hdead a ha)]
        rw [if_neg (by simpa using hdead)]
        exact (mul_le_mul_right (hjen.trans_eq hterm) _).trans le_self_add
  calc
    PhiDres alpha rhoS (w.bind f) R ≤
        ∑' x, (rhoS x * ∑' a, (w a : ℝ≥0∞) *
            (if rE (f a) R x = 0 then 0 else phiE alpha (q (f a) R x)) +
          rhoS x *
            ((if ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
              then 1 else 0) * WresD alpha (w.bind f) R x)) := by
          rw [PhiDres]
          exact ENNReal.tsum_le_tsum hpt
    _ = (∑' x, rhoS x * ∑' a, (w a : ℝ≥0∞) *
          (if rE (f a) R x = 0 then 0 else phiE alpha (q (f a) R x))) +
        ∑' x, rhoS x *
          ((if ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
            then 1 else 0) * WresD alpha (w.bind f) R x) := ENNReal.tsum_add
    _ = (∑' a, (w a : ℝ≥0∞) * PhiDres alpha rhoS (f a) R) +
        ∑' x, rhoS x *
          ((if ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
            then 1 else 0) * WresD alpha (w.bind f) R x) := by
      congr 1
      rw [tsum_congr fun x => (ENNReal.tsum_mul_left).symm,
        ENNReal.tsum_comm]
      refine tsum_congr fun a => ?_
      rw [tsum_congr fun x => show
          rhoS x * ((w a : ℝ≥0∞) *
            (if rE (f a) R x = 0 then 0 else phiE alpha (q (f a) R x))) =
          (w a : ℝ≥0∞) * (rhoS x *
            (if rE (f a) R x = 0 then 0 else phiE alpha (q (f a) R x)))
          from by ring,
        ENNReal.tsum_mul_left, PhiDres]

/-- A finitely supported mixture's existential dead-component charge is at
most the union of the singleton dead-component screens. -/
lemma bindDeadCharge_le_finsetScreens {A X : Type} [DecidableEq A]
    (rhoS : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (S : Finset A)
    (hsupp : ∀ a, (w a : ℝ≥0∞) ≠ 0 → a ∈ S)
    (W : X → ℝ≥0∞) :
    (∑' x, rhoS x *
      ((if ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
        then 1 else 0) * W x)) ≤
      ∑ a ∈ S, screenE rhoS R [f a] W := by
  calc
    (∑' x, rhoS x *
        ((if ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
          then 1 else 0) * W x)) ≤
      ∑' x, ∑ a ∈ S,
        rhoS x * ((if rE (f a) R x = 0 then 1 else 0) * W x) := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hd : ∃ a, (w a : ℝ≥0∞) ≠ 0 ∧ rE (f a) R x = 0
      · rw [if_pos hd]
        obtain ⟨a, ha, hdead⟩ := hd
        have haS := hsupp a ha
        calc
          rhoS x * (1 * W x) =
              rhoS x * ((if rE (f a) R x = 0 then 1 else 0) * W x) := by
                rw [if_pos hdead]
          _ ≤ ∑ a ∈ S,
              rhoS x * ((if rE (f a) R x = 0 then 1 else 0) * W x) := by
                exact Finset.single_le_sum (s := S)
                  (fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) haS
      · rw [if_neg hd, zero_mul, mul_zero]
        exact zero_le
    _ = ∑ a ∈ S, ∑' x,
        rhoS x * ((if rE (f a) R x = 0 then 1 else 0) * W x) := by
      clear hsupp
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih =>
          simp only [Finset.sum_insert ha]
          rw [ENNReal.tsum_add, ih]
    _ = ∑ a ∈ S, screenE rhoS R [f a] W := by
      simp_rw [screenE_singleton]

/-- One dead product target, normalized by a second product target, factors
entirely through the finite screen ledger.  This is the component estimate
used in the corrected five-term union bound for a fresh target. -/
theorem graftOneSidedProduct_le
    (alpha : ℝ) (halpha : 1 ≤ alpha)
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (a b c d e f : GraftTgt) :
    (∑' xp,
      prodPMF (graftBiSource mu nuL nuR v0 lr h a)
        (graftBiSource mu nuL nuR v0 lr h b) xp *
        ((if rE
            (prodPMF (graftBiTarget mu nuL nuR v0 lr h c)
              (graftBiTarget mu nuL nuR v0 lr h d))
            (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
          then 1 else 0) *
        WresD alpha
          (prodPMF (graftBiTarget mu nuL nuR v0 lr h e)
            (graftBiTarget mu nuL nuR v0 lr h f))
          (SquareRel (fullSim (graftLabRel Rv) h)) xp)) ≤
      4 * graftESup alpha Rv mu nuL nuR v0 h *
          (1 + ENNReal.ofReal alpha *
            graftPsi alpha Rv mu nuL nuR v0 h) +
        4 * (graftESup alpha Rv mu nuL nuR v0 h *
          graftESup alpha Rv mu nuL nuR v0 h) := by
  let P := graftPsi alpha Rv mu nuL nuR v0 h
  let E := graftESup alpha Rv mu nuL nuR v0 h
  let R := fullSim (graftLabRel Rv) h
  let sa := graftBiSource mu nuL nuR v0 lr h a
  let sb := graftBiSource mu nuL nuR v0 lr h b
  let tc := graftBiTarget mu nuL nuR v0 lr h c
  let td := graftBiTarget mu nuL nuR v0 lr h d
  let te := graftBiTarget mu nuL nuR v0 lr h e
  let tf := graftBiTarget mu nuL nuR v0 lr h f
  let W0 := WresD alpha te R
  let W1 := WresD alpha tf R
  have hmom : ∀ s t,
      (∑' x, graftBiSource mu nuL nuR v0 lr h s x *
        WresD alpha (graftBiTarget mu nuL nuR v0 lr h t) R x) ≤
        1 + ENNReal.ofReal alpha * P := by
    intro s t
    exact (tsum_WresD_le halpha _ _ _).trans
      (add_le_add le_rfl (mul_le_mul_right
        (graftBiPhi_le_graftPsi alpha Rv mu nuL nuR v0 lr h (s, t)) _))
  have hpair : ∀ s t u,
      screenE (graftBiSource mu nuL nuR v0 lr h s) R
        [graftBiTarget mu nuL nuR v0 lr h t,
          graftBiTarget mu nuL nuR v0 lr h u]
        (WresD alpha (graftBiTarget mu nuL nuR v0 lr h e) R) ≤ E := by
    intro s t u
    simpa [E, R, graftBiNorm] using
      (graftScreenList_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
        hp11 hp13 lr h s [t, u] (by simp) (some e))
  have hpair' : ∀ s t u,
      screenE (graftBiSource mu nuL nuR v0 lr h s) R
        [graftBiTarget mu nuL nuR v0 lr h t,
          graftBiTarget mu nuL nuR v0 lr h u]
        (WresD alpha (graftBiTarget mu nuL nuR v0 lr h f) R) ≤ E := by
    intro s t u
    simpa [E, R, graftBiNorm] using
      (graftScreenList_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
        hp11 hp13 lr h s [t, u] (by simp) (some f))
  have hsingle : ∀ s t,
      screenE (graftBiSource mu nuL nuR v0 lr h s) R
        [graftBiTarget mu nuL nuR v0 lr h t]
        (WresD alpha (graftBiTarget mu nuL nuR v0 lr h e) R) ≤ E := by
    intro s t
    simpa [E, R, graftBiNorm] using
      (graftScreenList_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
        hp11 hp13 lr h s [t] (by simp) (some e))
  have hsingle' : ∀ s t,
      screenE (graftBiSource mu nuL nuR v0 lr h s) R
        [graftBiTarget mu nuL nuR v0 lr h t]
        (WresD alpha (graftBiTarget mu nuL nuR v0 lr h f) R) ≤ E := by
    intro s t
    simpa [E, R, graftBiNorm] using
      (graftScreenList_le_graftESup alpha Rv mu nuL nuR v0 hrefl hLaw
        hp11 hp13 lr h s [t] (by simp) (some f))
  have hsplit : ∀ xp,
      prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            WresD alpha (prodPMF te tf) (SquareRel R) xp) ≤
        prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            (W0 xp.1 * W1 xp.2)) +
        prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            (W1 xp.1 * W0 xp.2)) := by
    intro xp
    have hW := WresD_square_le_sum (le_trans zero_le_one halpha)
      te tf R xp
    exact (mul_le_mul_right (mul_le_mul_right hW _) _).trans_eq (by ring)
  have hfac1 :
      (∑' xp, prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            (W0 xp.1 * W1 xp.2))) ≤
        E * (1 + ENNReal.ofReal alpha * P) +
          (1 + ENNReal.ofReal alpha * P) * E + E * E + E * E := by
    refine (deadScreen_factorize sa sb tc td R W0 W1).trans ?_
    exact add_le_add (add_le_add (add_le_add
      (mul_le_mul'
        (by simpa [sa, tc, td, W0, R] using hpair a c d)
        (by simpa [sb, W1, tf, R] using hmom b f))
      (mul_le_mul'
        (by simpa [sa, W0, te, R] using hmom a e)
        (by simpa [sb, tc, td, W1, R] using hpair' b c d)))
      (mul_le_mul'
        (by simpa [sa, tc, W0, R] using hsingle a c)
        (by simpa [sb, tc, W1, R] using hsingle' b c)))
      (mul_le_mul'
        (by simpa [sa, td, W0, R] using hsingle a d)
        (by simpa [sb, td, W1, R] using hsingle' b d))
  have hfac2 :
      (∑' xp, prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            (W1 xp.1 * W0 xp.2))) ≤
        E * (1 + ENNReal.ofReal alpha * P) +
          (1 + ENNReal.ofReal alpha * P) * E + E * E + E * E := by
    refine (deadScreen_factorize sa sb tc td R W1 W0).trans ?_
    exact add_le_add (add_le_add (add_le_add
      (mul_le_mul'
        (by simpa [sa, tc, td, W1, R] using hpair' a c d)
        (by simpa [sb, W0, te, R] using hmom b e))
      (mul_le_mul'
        (by simpa [sa, W1, tf, R] using hmom a f)
        (by simpa [sb, tc, td, W0, R] using hpair b c d)))
      (mul_le_mul'
        (by simpa [sa, tc, W1, R] using hsingle' a c)
        (by simpa [sb, tc, W0, R] using hsingle b c)))
      (mul_le_mul'
        (by simpa [sa, td, W1, R] using hsingle' a d)
        (by simpa [sb, td, W0, R] using hsingle b d))
  calc
    (∑' xp, prodPMF sa sb xp *
        ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
          WresD alpha (prodPMF te tf) (SquareRel R) xp)) ≤
      ∑' xp, (prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            (W0 xp.1 * W1 xp.2)) +
        prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            (W1 xp.1 * W0 xp.2))) := ENNReal.tsum_le_tsum hsplit
    _ = (∑' xp, prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            (W0 xp.1 * W1 xp.2))) +
        (∑' xp, prodPMF sa sb xp *
          ((if rE (prodPMF tc td) (SquareRel R) xp = 0 then 1 else 0) *
            (W1 xp.1 * W0 xp.2))) := ENNReal.tsum_add
    _ ≤ (E * (1 + ENNReal.ofReal alpha * P) +
          (1 + ENNReal.ofReal alpha * P) * E + E * E + E * E) +
        (E * (1 + ENNReal.ofReal alpha * P) +
          (1 + ENNReal.ofReal alpha * P) * E + E * E + E * E) :=
      add_le_add hfac1 hfac2
    _ = 4 * E * (1 + ENNReal.ofReal alpha * P) + 4 * (E * E) := by ring
    _ = _ := by rfl

/-- One literal dead target component against a charged source component.
The fresh normalization is first pruned to the compatible common component,
then all three component laws are rewritten as their actual product laws. -/
theorem graftXi_dead_component_le
    (alpha : ℝ) (halpha : 1 ≤ alpha)
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (lr : Bool) (h k j : ℕ)
    (hk : k ∈ insert (graftRareArity lr) elevenThirteenCommonCore)
    (hj : j ∈ insert (graftRareArity (!lr)) elevenThirteenCommonCore)
    (hsel : ((if lr then nuR else nuL)
      (graftCompatibleArity lr k) : ℝ≥0∞) ≠ 0) :
    screenE
        (graftXi lr mu (if lr then nuL else nuR) v0 (.ordinary k) h)
        (SquareRel (fullSim (graftLabRel Rv) h))
        [graftXi (!lr) mu (if lr then nuR else nuL) v0
          (.ordinary j) h]
        (WresD alpha
          (graftXiBar (!lr) mu (if lr then nuR else nuL) v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h))) ≤
      ((if lr then nuR else nuL)
          (graftCompatibleArity lr k) : ℝ≥0∞) ^ (-alpha) *
        (4 * graftESup alpha Rv mu nuL nuR v0 h *
            (1 + ENNReal.ofReal alpha *
              graftPsi alpha Rv mu nuL nuR v0 h) +
          4 * (graftESup alpha Rv mu nuL nuR v0 h *
            graftESup alpha Rv mu nuL nuR v0 h)) := by
  have hprune := graftXiBar_screen_le_compatible_component
    alpha (le_trans zero_le_one halpha) Rv mu nuL nuR v0 hrefl hLaw
    hp11 hp13 lr h k hk hsel
    [graftXi (!lr) mu (if lr then nuR else nuL) v0 (.ordinary j) h]
  refine hprune.trans (mul_le_mul_right ?_ _)
  have hsrc := graftXi_eq_prod_of_fixed_support mu v0 lr
    (if lr then nuL else nuR) h k hk
  have htgt := graftXi_eq_prod_of_fixed_support mu v0 (!lr)
    (if lr then nuR else nuL) h j hj
  have hselmem : graftCompatibleArity lr k ∈
      insert (graftRareArity (!lr)) elevenThirteenCommonCore := by
    cases lr with
    | false =>
        simp only [Bool.not_false, graftRareArity]
        simp only [graftRareArity, elevenThirteenCommonCore,
          Finset.mem_insert, Finset.mem_singleton] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [graftCompatibleArity]
    | true =>
        simp only [Bool.not_true, graftRareArity]
        simp only [graftRareArity, elevenThirteenCommonCore,
          Finset.mem_insert, Finset.mem_singleton] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [graftCompatibleArity]
  have hnorm := graftXi_eq_prod_of_fixed_support mu v0 (!lr)
    (if lr then nuR else nuL) h (graftCompatibleArity lr k) hselmem
  rw [hsrc, htgt, hnorm, screenE_singleton]
  cases lr with
  | false =>
      simpa [graftBiSource, graftBiTarget] using
        (graftOneSidedProduct_le alpha halpha Rv mu nuL nuR v0 hrefl
          hLaw hp11 hp13 false h
          (graftSupportedPair false k).1 (graftSupportedPair false k).2
          (graftSupportedPair true j).1 (graftSupportedPair true j).2
          (graftSupportedPair true (graftCompatibleArity false k)).1
          (graftSupportedPair true (graftCompatibleArity false k)).2)
  | true =>
      simpa [graftBiSource, graftBiTarget] using
        (graftOneSidedProduct_le alpha halpha Rv mu nuL nuR v0 hrefl
          hLaw hp11 hp13 true h
          (graftSupportedPair true k).1 (graftSupportedPair true k).2
          (graftSupportedPair false j).1 (graftSupportedPair false j).2
          (graftSupportedPair false (graftCompatibleArity true k)).1
          (graftSupportedPair false (graftCompatibleArity true k)).2)

/-- Correct five-component fresh-target estimate for the fixed law pair.
The Jensen part is an average of genuine square cells and hence keeps the
ordinary cell coefficient unchanged.  The existential correction is a
five-term union and is entirely screen-valued. -/
theorem graftXi_to_XiBar_le_cell_add_screen
    {alpha delta L K : ℝ} (halpha : 1 ≤ alpha) (hdelta : 0 < delta)
    (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ alpha ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * (1 - t) ^ alpha ≤ K)
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ v w, Rv v w → Rv w v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (lr : Bool) (h k : ℕ)
    (hk : k ∈ insert (graftRareArity lr) elevenThirteenCommonCore)
    (hsel : ((if lr then nuR else nuL)
      (graftCompatibleArity lr k) : ℝ≥0∞) ≠ 0) :
    PhiDres alpha
        (graftXi lr mu (if lr then nuL else nuR) v0 (.ordinary k) h)
        (graftXiBar (!lr) mu (if lr then nuR else nuL) v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) ≤
      cellCB alpha delta L K
          (graftPsi alpha Rv mu nuL nuR v0 h)
          (graftESup alpha Rv mu nuL nuR v0 h)
          (graftESup alpha Rv mu nuL nuR v0 h) +
        5 * (((if lr then nuR else nuL)
            (graftCompatibleArity lr k) : ℝ≥0∞) ^ (-alpha) *
          (4 * graftESup alpha Rv mu nuL nuR v0 h *
              (1 + ENNReal.ofReal alpha *
                graftPsi alpha Rv mu nuL nuR v0 h) +
            4 * (graftESup alpha Rv mu nuL nuR v0 h *
              graftESup alpha Rv mu nuL nuR v0 h))) := by
  let nuS := if lr then nuL else nuR
  let nuT := if lr then nuR else nuL
  let rhoS := graftXi lr mu nuS v0 (.ordinary k) h
  let f : ℕ → PMF
      (FullLab (GraftState V) h × FullLab (GraftState V) h) :=
    fun j => graftXi (!lr) mu nuT v0 (.ordinary j) h
  let R := SquareRel (fullSim (graftLabRel Rv) h)
  let C := cellCB alpha delta L K
    (graftPsi alpha Rv mu nuL nuR v0 h)
    (graftESup alpha Rv mu nuL nuR v0 h)
    (graftESup alpha Rv mu nuL nuR v0 h)
  let B := 4 * graftESup alpha Rv mu nuL nuR v0 h *
        (1 + ENNReal.ofReal alpha * graftPsi alpha Rv mu nuL nuR v0 h) +
      4 * (graftESup alpha Rv mu nuL nuR v0 h *
        graftESup alpha Rv mu nuL nuR v0 h)
  let S : Finset ℕ :=
    insert (graftRareArity (!lr)) elevenThirteenCommonCore
  have htarget : ∀ j, (nuT j : ℝ≥0∞) ≠ 0 → j ∈ S := by
    intro j hj
    cases lr with
    | false => exact hLaw.2.2.2.1 j hj
    | true => exact hLaw.2.2.2.2 j hj
  have havg : (∑' j, (nuT j : ℝ≥0∞) *
        PhiDres alpha rhoS (f j) R) ≤ C := by
    calc
      (∑' j, (nuT j : ℝ≥0∞) * PhiDres alpha rhoS (f j) R) ≤
          ∑' j, (nuT j : ℝ≥0∞) * C := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases hj0 : (nuT j : ℝ≥0∞) = 0
        · simp [hj0]
        · apply mul_le_mul_right
          have hj := htarget j hj0
          have hsrc := graftXi_eq_prod_of_fixed_support mu v0 lr nuS h k hk
          have htgt := graftXi_eq_prod_of_fixed_support mu v0 (!lr) nuT h j hj
          dsimp [rhoS, f]
          rw [hsrc, htgt]
          cases lr with
          | false =>
              simpa [rhoS, f, R, C, nuS, nuT, graftBiSource,
                graftBiTarget] using
                (graftSquare_le_cellCB halpha hdelta hL0 hL hK0 hK
                  Rv mu nuL nuR v0 hrefl hsymm hLaw hp11 hp13 false h
                  (graftSupportedPair false k).1
                  (graftSupportedPair false k).2
                  (graftSupportedPair true j).1
                  (graftSupportedPair true j).2)
          | true =>
              simpa [rhoS, f, R, C, nuS, nuT, graftBiSource,
                graftBiTarget] using
                (graftSquare_le_cellCB halpha hdelta hL0 hL hK0 hK
                  Rv mu nuL nuR v0 hrefl hsymm hLaw hp11 hp13 true h
                  (graftSupportedPair true k).1
                  (graftSupportedPair true k).2
                  (graftSupportedPair false j).1
                  (graftSupportedPair false j).2)
      _ = C := by rw [ENNReal.tsum_mul_right, nuT.tsum_coe, one_mul]
  have hdead : (∑' x, rhoS x *
        ((if ∃ j, (nuT j : ℝ≥0∞) ≠ 0 ∧ rE (f j) R x = 0
          then 1 else 0) * WresD alpha (nuT.bind f) R x)) ≤
      5 * (((if lr then nuR else nuL)
          (graftCompatibleArity lr k) : ℝ≥0∞) ^ (-alpha) * B) := by
    calc
      _ ≤ ∑ j ∈ S,
          screenE rhoS R [f j] (WresD alpha (nuT.bind f) R) :=
        bindDeadCharge_le_finsetScreens rhoS nuT f R S htarget _
      _ ≤ ∑ _j ∈ S,
          ((if lr then nuR else nuL)
            (graftCompatibleArity lr k) : ℝ≥0∞) ^ (-alpha) * B := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hrow := graftXi_dead_component_le alpha halpha Rv mu nuL nuR
          v0 hrefl hLaw hp11 hp13 lr h k j hk hj hsel
        simpa [rhoS, f, R, B, nuS, nuT, graftXiBar] using hrow
      _ = 5 * (((if lr then nuR else nuL)
            (graftCompatibleArity lr k) : ℝ≥0∞) ^ (-alpha) * B) := by
        cases lr <;>
          simp [S, elevenThirteenCommonCore, graftRareArity]
  have hsplit := PhiDres_bind_le_average_add_dead alpha halpha
    rhoS nuT f R
  simpa [rhoS, f, R, C, B, nuS, nuT, graftXiBar] using
    hsplit.trans (add_le_add havg hdead)

/-- Restricted potential between two laws with compatible deterministic
roots is exactly the child-pair restricted potential. -/
lemma PhiDres_map_branch_map_branch {S : Type}
    (alpha : ℝ) (R0 : S → S → Prop)
    (rhoS rhoT : PMF (FullLab S h × FullLab S h))
    (s t : S) (hst : R0 s t) :
    PhiDres alpha (rhoS.map (branch s)) (rhoT.map (branch t))
        (fullSim R0 (h + 1)) =
      PhiDres alpha rhoS rhoT (SquareRel (fullSim R0 h)) := by
  rw [PhiDres, tsum_map_mul, PhiDres]
  refine tsum_congr fun xp => ?_
  rw [rE_map_branch_law, if_pos hst, q, q, qE_map_branch_law,
    if_pos hst]

/-- Root/child split for the actual grafted fresh target. -/
lemma phiE_graftTlaw_branch_le
    (alpha : ℝ) (halpha : 1 ≤ alpha)
    (Rv : V → V → Prop) (mu : PMF V) (v0 : V)
    (left : Bool) (nu : PMF ℕ) (v : V) (c : GraftCounter)
    (h : ℕ) (xp : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    phiE alpha
        (q (graftTlaw left mu nu v0 (h + 1))
          (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp)) ≤
      phiE alpha (q mu Rv v) +
        phiE alpha
          (q (graftXiBar left mu nu v0 h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp) +
        ENNReal.ofReal (2 * alpha) *
          (phiE alpha (q mu Rv v) *
            phiE alpha
              (q (graftXiBar left mu nu v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp)) := by
  have hroot := rE_graftTlaw_succ_branch Rv mu v0 left nu v c h xp
  have hkey :
      q (graftTlaw left mu nu v0 (h + 1))
          (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp) =
        q mu Rv v + (1 - q mu Rv v) *
          q (graftXiBar left mu nu v0 h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
    have ht := toReal_rE_add_toReal_qE
      (graftTlaw left mu nu v0 (h + 1))
      (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp)
    have hr := toReal_rE_add_toReal_qE mu Rv v
    have hc := toReal_rE_add_toReal_qE
      (graftXiBar left mu nu v0 h)
      (SquareRel (fullSim (graftLabRel Rv) h)) xp
    rw [hroot, ENNReal.toReal_mul] at ht
    simp only [q]
    have ht' :
        (qE (graftTlaw left mu nu v0 (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (branch (v, c) xp)).toReal =
        1 - (rE mu Rv v).toReal *
          (rE (graftXiBar left mu nu v0 h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp).toReal := by
      linarith
    have hr' : (rE mu Rv v).toReal = 1 - (qE mu Rv v).toReal := by
      linarith
    have hc' :
        (rE (graftXiBar left mu nu v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp).toReal =
        1 - (qE (graftXiBar left mu nu v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp).toReal := by
      linarith
    rw [ht', hr', hc']
    ring
  rw [hkey]
  exact phiE_split halpha q_nonneg q_le_one q_nonneg q_le_one

/-- A fixed-root grafted source against a fresh grafted target. -/
lemma PhiDres_map_branch_graftTlaw_le
    (alpha : ℝ) (halpha : 1 ≤ alpha)
    (Rv : V → V → Prop) (mu : PMF V) (v0 : V)
    (leftTarget : Bool) (nuT : PMF ℕ)
    (h : ℕ)
    (rhoS : PMF (FullLab (GraftState V) h × FullLab (GraftState V) h))
    (v : V) (c : GraftCounter) :
    PhiDres alpha (rhoS.map (branch (v, c)))
        (graftTlaw leftTarget mu nuT v0 (h + 1))
        (fullSim (graftLabRel Rv) (h + 1)) ≤
      phiE alpha (q mu Rv v) +
        PhiDres alpha rhoS (graftXiBar leftTarget mu nuT v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) +
        ENNReal.ofReal (2 * alpha) *
          (phiE alpha (q mu Rv v) *
            PhiDres alpha rhoS (graftXiBar leftTarget mu nuT v0 h)
              (SquareRel (fullSim (graftLabRel Rv) h))) := by
  rw [PhiDres, tsum_map_mul]
  have hpt : ∀ xp,
      rhoS xp *
        (if rE (graftTlaw leftTarget mu nuT v0 (h + 1))
            (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp) = 0
          then 0 else phiE alpha
            (q (graftTlaw leftTarget mu nuT v0 (h + 1))
              (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp))) ≤
      rhoS xp * phiE alpha (q mu Rv v) +
        rhoS xp *
          (if rE (graftXiBar leftTarget mu nuT v0 h)
              (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
            then 0 else phiE alpha
              (q (graftXiBar leftTarget mu nuT v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp)) +
        ENNReal.ofReal (2 * alpha) *
          (phiE alpha (q mu Rv v) *
            (rhoS xp *
              (if rE (graftXiBar leftTarget mu nuT v0 h)
                  (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
                then 0 else phiE alpha
                  (q (graftXiBar leftTarget mu nuT v0 h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp)))) := by
    intro xp
    by_cases hres : rE (graftTlaw leftTarget mu nuT v0 (h + 1))
        (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp) = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      have hfac := rE_graftTlaw_succ_branch Rv mu v0 leftTarget nuT
        v c h xp
      rw [hfac] at hres
      obtain ⟨-, hchild⟩ := mul_ne_zero_iff.mp hres
      rw [if_neg hchild]
      calc
        rhoS xp * phiE alpha
            (q (graftTlaw leftTarget mu nuT v0 (h + 1))
              (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp)) ≤
          rhoS xp * (phiE alpha (q mu Rv v) +
            phiE alpha
              (q (graftXiBar leftTarget mu nuT v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp) +
            ENNReal.ofReal (2 * alpha) *
              (phiE alpha (q mu Rv v) *
                phiE alpha
                  (q (graftXiBar leftTarget mu nuT v0 h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp))) :=
              mul_le_mul_right
                (phiE_graftTlaw_branch_le alpha halpha Rv mu v0
                  leftTarget nuT v c h xp) _
        _ = _ := by ring
  calc
    _ ≤ ∑' xp, (rhoS xp * phiE alpha (q mu Rv v) +
        rhoS xp *
          (if rE (graftXiBar leftTarget mu nuT v0 h)
              (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
            then 0 else phiE alpha
              (q (graftXiBar leftTarget mu nuT v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp)) +
        ENNReal.ofReal (2 * alpha) *
          (phiE alpha (q mu Rv v) *
            (rhoS xp *
              (if rE (graftXiBar leftTarget mu nuT v0 h)
                  (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
                then 0 else phiE alpha
                  (q (graftXiBar leftTarget mu nuT v0 h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp))))) :=
      ENNReal.tsum_le_tsum hpt
    _ = _ := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
        rhoS.tsum_coe, one_mul, ENNReal.tsum_mul_left,
        ENNReal.tsum_mul_left, PhiDres]

/-- Near a compatible root, a fresh target normalization is pruned to a
source-dependent supporting common component.  The component-dead term from
the earlier heavy-row theorem is exactly zero. -/
theorem graftComponentScreen_some_fresh_le_supported_hall
    (alpha : ℝ) (halpha : 0 < alpha) (Rv : V → V → Prop)
    (mu : PMF V) (v0 : V)
    (leftSource leftTarget : Bool) (nuS nuT : PMF ℕ)
    (hcommon : ∀ i : Fin 4,
      (nuT (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    {v : V} (hv0 : Rv v v0) (hvpos : rE mu Rv v ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) (k : ℕ)
    (hksupp : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore)
    (i : Fin 4)
    (hcompat : HasMatchingSupport
      (graftXi leftSource mu nuS v0 (.ordinary k) h)
      (graftXi leftTarget mu nuT v0
        (.ordinary (graftCommonArity i)) h)
      (SquareRel (fullSim (graftLabRel Rv) h))) :
    screenE
        (muM (graftK leftSource mu nuS v0) (v, .ordinary k) (h + 1))
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
        (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      (rE mu Rv v) ^ (-alpha) *
        ((nuT (graftCommonArity i) : ℝ≥0∞) ^ (-alpha) *
          graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
            h z (graftSupportedPair leftSource k).1
              (graftSupportedPair leftSource k).2 (graftCommonArity i)) := by
  let R1 := fullSim (graftLabRel Rv) (h + 1)
  let R2 := SquareRel (fullSim (graftLabRel Rv) h)
  let rho := graftXi leftSource mu nuS v0 (.ordinary k) h
  let mix := graftXiBar leftTarget mu nuT v0 h
  let ms := graftMemPairs mu v0 leftTarget nuT h z
  let childzs := ms.map (fun p => prodPMF p.1 p.2)
  let rootTilt := (rE mu Rv v) ^ (-alpha)
  have hind : ∀ xp,
      screenInd R1
          (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
          (branch (v, .ordinary k) xp) ≤
        screenInd R2 childzs xp := by
    intro xp
    rw [screenInd, screenInd]
    by_cases hzdead : ∀ target ∈
        z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)),
        rE target R1 (branch (v, .ordinary k) xp) = 0
    · rw [if_pos hzdead, if_pos]
      intro target htarget
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp htarget
      exact graftMemInd_branch Rv mu v0 leftTarget nuT hcommon hv0 hvpos
        (.ordinary k) h z xp hzdead p hp
    · rw [if_neg hzdead]
      exact zero_le
  rw [graftComponentScreen_branch mu v0 leftSource nuS v k h]
  calc
    (∑' xp, rho xp *
        (screenInd R1
          (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
          (branch (v, .ordinary k) xp) *
        WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F) R1
          (branch (v, .ordinary k) xp))) ≤
      ∑' xp, rho xp *
        (screenInd R2 childzs xp *
          (rootTilt * WresD alpha mix R2 xp)) := by
        refine ENNReal.tsum_le_tsum fun xp => ?_
        rw [show graftInterp mu v0 leftTarget nuT (h + 1) .F =
            graftTlaw leftTarget mu nuT v0 (h + 1) by rfl,
          WresD_graftTlaw_succ_branch Rv mu v0 alpha leftTarget nuT v
            hvpos (.ordinary k) h xp]
        change rho xp *
            (screenInd R1
              (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
              (branch (v, .ordinary k) xp) *
              (rootTilt * WresD alpha mix R2 xp)) ≤
          rho xp * (screenInd R2 childzs xp *
            (rootTilt * WresD alpha mix R2 xp))
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_right
            (mul_le_mul_right (hind xp) (rootTilt * WresD alpha mix R2 xp))
            (rho xp)
    _ = rootTilt * screenE rho R2 childzs (WresD alpha mix R2) := by
      rw [screenE]
      calc
        (∑' xp, rho xp *
            (screenInd R2 childzs xp *
              (rootTilt * WresD alpha mix R2 xp))) =
          ∑' xp, rootTilt *
            (rho xp * screenInd R2 childzs xp * WresD alpha mix R2 xp) := by
              refine tsum_congr fun xp => by ring
        _ = rootTilt * ∑' xp,
            rho xp * screenInd R2 childzs xp * WresD alpha mix R2 xp :=
          ENNReal.tsum_mul_left
    _ ≤ rootTilt *
        ((nuT (graftCommonArity i) : ℝ≥0∞) ^ (-alpha) *
          screenE rho R2 childzs
            (WresD alpha
              (graftXi leftTarget mu nuT v0
                (.ordinary (graftCommonArity i)) h) R2)) := by
      apply mul_le_mul_right
      simpa [rho, mix, R2, graftXiBar] using
        (screenE_bind_WresD_le_component_of_matching alpha halpha.le
          rho nuT
          (fun j => graftXi leftTarget mu nuT v0 (.ordinary j) h)
          R2 (graftCommonArity i) (hcommon i) hcompat childzs)
    _ ≤ rootTilt *
        ((nuT (graftCommonArity i) : ℝ≥0∞) ^ (-alpha) *
          graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
            h z (graftSupportedPair leftSource k).1
              (graftSupportedPair leftSource k).2
              (graftCommonArity i)) := by
      apply mul_le_mul_right
      exact mul_le_mul_right
        (graftXi_screen_common_component_le_freshHallTerm
          alpha halpha.le Rv mu v0 leftSource leftTarget nuS nuT h z k
            hksupp i) _
    _ = _ := rfl

private lemma graftScreenInd_le_one_final {X : Type} (R : X → X → Prop)
    (zs : List (PMF X)) (x : X) : screenInd R zs x ≤ 1 := by
  rw [screenInd]
  split <;> simp

/-- Integrated fresh/fresh screen row with a supporting target component
chosen separately for every charged source arity.  Compatible roots produce
only Hall outputs; the ordinary potential occurs only on the graph-label
far-root event and is therefore multiplied by the graph tail. -/
theorem graftFreshScreen_some_fresh_le_supported_far_add_hall
    (alpha : ℝ) (halpha : 1 ≤ alpha) (Rv : V → V → Prop)
    (mu : PMF V) (v0 : V)
    (leftSource leftTarget : Bool) (nuS nuT : PMF ℕ)
    (hssupp : ∀ k, (nuS k : ℝ≥0∞) ≠ 0 →
      k ∈ insert (graftRareArity leftSource) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4,
      (nuT (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl : ∀ v, Rv v v)
    (h : ℕ) (z : Finset GraftTgt) (choose : ℕ → Fin 4)
    (hcompat : ∀ k, (nuS k : ℝ≥0∞) ≠ 0 →
      HasMatchingSupport
        (graftXi leftSource mu nuS v0 (.ordinary k) h)
        (graftXi leftTarget mu nuT v0
          (.ordinary (graftCommonArity (choose k))) h)
        (SquareRel (fullSim (graftLabRel Rv) h)))
    (RT FT M : ℝ≥0∞)
    (hRT : (∑' v, (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) ≤ RT)
    (hFT : (∑' v, if Rv v v0 then 0 else
      (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) ≤ FT)
    (hMom : ∀ k, (nuS k : ℝ≥0∞) ≠ 0 →
      PhiDres alpha (graftXi leftSource mu nuS v0 (.ordinary k) h)
        (graftXiBar leftTarget mu nuT v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) ≤ M) :
    screenE (graftInterp mu v0 leftSource nuS (h + 1) .F)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
        (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      FT * (1 + ENNReal.ofReal alpha * M) +
        RT * ∑' k, (nuS k : ℝ≥0∞) *
          ((nuT (graftCommonArity (choose k)) : ℝ≥0∞) ^ (-alpha) *
            graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
              h z (graftSupportedPair leftSource k).1
                (graftSupportedPair leftSource k).2
                (graftCommonArity (choose k))) := by
  have halpha0 : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  rw [graftInterp_F, graftFreshScreen_split mu v0 leftSource nuS (h + 1)]
  let H : ℕ → ℝ≥0∞ := fun k =>
    graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
      h z (graftSupportedPair leftSource k).1
        (graftSupportedPair leftSource k).2
        (graftCommonArity (choose k))
  let C : ℝ≥0∞ := 1 + ENNReal.ofReal alpha * M
  let D : ℕ → ℝ≥0∞ := fun k =>
    (nuT (graftCommonArity (choose k)) : ℝ≥0∞) ^ (-alpha) * H k
  have hinner : ∀ k, (nuS k : ℝ≥0∞) ≠ 0 →
      (∑' v, (mu v : ℝ≥0∞) *
        screenE (muM (graftK leftSource mu nuS v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
          (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
            (fullSim (graftLabRel Rv) (h + 1)))) ≤
        RT * D k + FT * C := by
    intro k hk
    have hksupp := hssupp k hk
    have hnear : ∀ v, Rv v v0 → (mu v : ℝ≥0∞) ≠ 0 →
        screenE (muM (graftK leftSource mu nuS v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
          (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
            (fullSim (graftLabRel Rv) (h + 1))) ≤
          (rE mu Rv v) ^ (-alpha) * D k := by
      intro v hv hmu
      have hvpos : rE mu Rv v ≠ 0 := by
        intro hr
        exact hmu (le_antisymm (hr ▸ le_rE_of_refl (hrefl v)) zero_le)
      simpa [D, H] using
        (graftComponentScreen_some_fresh_le_supported_hall
          alpha halpha0 Rv mu v0 leftSource leftTarget nuS nuT hcommon
          hv hvpos h z k hksupp (choose k) (hcompat k hk))
    have hfar : ∀ v, ¬ Rv v v0 → (mu v : ℝ≥0∞) ≠ 0 →
        screenE (muM (graftK leftSource mu nuS v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
          (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
            (fullSim (graftLabRel Rv) (h + 1))) ≤
          (rE mu Rv v) ^ (-alpha) * C := by
      intro v _hv hmu
      have hvpos : rE mu Rv v ≠ 0 := by
        intro hr
        exact hmu (le_antisymm (hr ▸ le_rE_of_refl (hrefl v)) zero_le)
      rw [graftComponentScreen_branch mu v0 leftSource nuS v k h]
      calc
        (∑' xp, graftXi leftSource mu nuS v0 (.ordinary k) h xp *
            (screenInd (fullSim (graftLabRel Rv) (h + 1))
              (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
              (branch (v, .ordinary k) xp) *
              WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
                (fullSim (graftLabRel Rv) (h + 1))
                (branch (v, .ordinary k) xp))) ≤
          ∑' xp, graftXi leftSource mu nuS v0 (.ordinary k) h xp *
            ((rE mu Rv v) ^ (-alpha) *
              WresD alpha (graftXiBar leftTarget mu nuT v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
            refine ENNReal.tsum_le_tsum fun xp => ?_
            rw [graftInterp_F,
              WresD_graftTlaw_succ_branch Rv mu v0 alpha leftTarget nuT v
                hvpos (.ordinary k) h xp]
            simpa only [mul_comm, mul_left_comm, mul_assoc, one_mul] using
              mul_le_mul_right
                (mul_le_mul_right
                  (graftScreenInd_le_one_final
                    (fullSim (graftLabRel Rv) (h + 1))
                    (z.toList.map
                      (graftInterp mu v0 leftTarget nuT (h + 1)))
                    (branch (v, .ordinary k) xp))
                  ((rE mu Rv v) ^ (-alpha) *
                    WresD alpha (graftXiBar leftTarget mu nuT v0 h)
                      (SquareRel (fullSim (graftLabRel Rv) h)) xp))
                (graftXi leftSource mu nuS v0 (.ordinary k) h xp)
        _ = (rE mu Rv v) ^ (-alpha) *
            ∑' xp, graftXi leftSource mu nuS v0 (.ordinary k) h xp *
              WresD alpha (graftXiBar leftTarget mu nuT v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
          calc
            (∑' xp, graftXi leftSource mu nuS v0 (.ordinary k) h xp *
                ((rE mu Rv v) ^ (-alpha) *
                  WresD alpha (graftXiBar leftTarget mu nuT v0 h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp)) =
              ∑' xp, (rE mu Rv v) ^ (-alpha) *
                (graftXi leftSource mu nuS v0 (.ordinary k) h xp *
                  WresD alpha (graftXiBar leftTarget mu nuT v0 h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
                refine tsum_congr fun xp => by ring
            _ = _ := ENNReal.tsum_mul_left
        _ ≤ (rE mu Rv v) ^ (-alpha) *
            (1 + ENNReal.ofReal alpha *
              PhiDres alpha
                (graftXi leftSource mu nuS v0 (.ordinary k) h)
                (graftXiBar leftTarget mu nuT v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h))) := by
          exact mul_le_mul_right
            (tsum_WresD_le halpha
              (graftXi leftSource mu nuS v0 (.ordinary k) h)
              (graftXiBar leftTarget mu nuT v0 h)
              (SquareRel (fullSim (graftLabRel Rv) h))) _
        _ ≤ (rE mu Rv v) ^ (-alpha) * C := by
          exact mul_le_mul_right
            (add_le_add le_rfl
              (mul_le_mul_right (hMom k hk) (ENNReal.ofReal alpha))) _
    calc
      (∑' v, (mu v : ℝ≥0∞) *
          screenE (muM (graftK leftSource mu nuS v0)
              (v, .ordinary k) (h + 1))
            (fullSim (graftLabRel Rv) (h + 1))
            (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
            (WresD alpha
              (graftInterp mu v0 leftTarget nuT (h + 1) .F)
              (fullSim (graftLabRel Rv) (h + 1)))) ≤
        ∑' v, ((mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha) * D k +
          (if Rv v v0 then 0 else
            (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha) * C)) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hmu : (mu v : ℝ≥0∞) = 0
        · simp [hmu]
        · by_cases hv : Rv v v0
          · rw [if_pos hv, add_zero]
            simpa only [mul_assoc] using mul_le_mul_right (hnear v hv hmu) _
          · rw [if_neg hv]
            calc
              (mu v : ℝ≥0∞) *
                  screenE (muM (graftK leftSource mu nuS v0)
                      (v, .ordinary k) (h + 1))
                    (fullSim (graftLabRel Rv) (h + 1))
                    (z.toList.map
                      (graftInterp mu v0 leftTarget nuT (h + 1)))
                    (WresD alpha
                      (graftInterp mu v0 leftTarget nuT (h + 1) .F)
                      (fullSim (graftLabRel Rv) (h + 1))) ≤
                (mu v : ℝ≥0∞) * ((rE mu Rv v) ^ (-alpha) * C) :=
                  mul_le_mul_right (hfar v hv hmu) _
              _ ≤ (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha) * D k +
                  (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha) * C := by
                simpa only [mul_assoc] using le_add_left
                  (le_refl ((mu v : ℝ≥0∞) *
                    (rE mu Rv v) ^ (-alpha) * C))
      _ = (∑' v, (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) * D k +
          (∑' v, if Rv v v0 then 0 else
            (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) * C := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        congr 1
        calc
          (∑' v, if Rv v v0 then 0 else
              (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha) * C) =
            ∑' v, (if Rv v v0 then 0 else
              (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) * C := by
                refine tsum_congr fun v => ?_
                by_cases hv : Rv v v0 <;> simp [hv]
          _ = _ := ENNReal.tsum_mul_right
      _ ≤ RT * D k + FT * C := by
        apply add_le_add
        · simpa [mul_comm] using mul_le_mul_right hRT (D k)
        · simpa [mul_comm] using mul_le_mul_right hFT C
  calc
    (∑' k, (nuS k : ℝ≥0∞) * ∑' v, (mu v : ℝ≥0∞) *
        screenE (muM (graftK leftSource mu nuS v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
          (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
            (fullSim (graftLabRel Rv) (h + 1)))) ≤
      ∑' k, (nuS k : ℝ≥0∞) * (RT * D k + FT * C) := by
      refine ENNReal.tsum_le_tsum fun k => ?_
      by_cases hk : (nuS k : ℝ≥0∞) = 0
      · simp [hk]
      · exact mul_le_mul_right (hinner k hk) _
    _ = FT * C + RT * ∑' k, (nuS k : ℝ≥0∞) * D k := by
      calc
        (∑' k, (nuS k : ℝ≥0∞) * (RT * D k + FT * C)) =
            (∑' k, (nuS k : ℝ≥0∞) * (RT * D k)) +
              ∑' k, (nuS k : ℝ≥0∞) * (FT * C) := by
          rw [← ENNReal.tsum_add]
          refine tsum_congr fun k => by ring
        _ = RT * (∑' k, (nuS k : ℝ≥0∞) * D k) + FT * C := by
          rw [show (∑' k, (nuS k : ℝ≥0∞) * (RT * D k)) =
              ∑' k, RT * ((nuS k : ℝ≥0∞) * D k) by
                refine tsum_congr fun k => by ring,
            ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
            nuS.tsum_coe, one_mul]
        _ = _ := by ring
    _ = _ := by rfl

/-! ### Fixed-law numerical threshold

The semantic row assembly is separate from the following elementary
calculation.  Once `nuL` and `nuR` have been fixed, all coefficients in the
two rows are fixed finite real numbers.  These definitions give a concrete
strictly positive range for the graph potential; no uniformity in the rare
offspring mass is asserted. -/

/-- The fixed example with all five atoms on each side genuinely charged.
This strengthens `IsElevenThirteenLawPair` only by positivity; it does not
introduce a lower bound uniform over a family of laws. -/
def IsFixedPositiveElevenThirteenLawPair
    (nuL nuR : PMF ℕ) (zeta : ℝ≥0∞) : Prop :=
  IsElevenThirteenLawPair nuL nuR zeta ∧
    zeta ≠ 0 ∧
    ∀ k ∈ elevenThirteenCommonCore, (nuL k : ℝ≥0∞) ≠ 0

lemma IsFixedPositiveElevenThirteenLawPair.left_common_pos
    {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsFixedPositiveElevenThirteenLawPair nuL nuR zeta)
    {k : ℕ} (hk : k ∈ elevenThirteenCommonCore) :
    (nuL k : ℝ≥0∞) ≠ 0 :=
  hLaw.2.2 k hk

lemma IsFixedPositiveElevenThirteenLawPair.right_common_pos
    {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsFixedPositiveElevenThirteenLawPair nuL nuR zeta)
    {k : ℕ} (hk : k ∈ elevenThirteenCommonCore) :
    (nuR k : ℝ≥0∞) ≠ 0 := by
  rw [← hLaw.1.2.2.1 k hk]
  exact hLaw.2.2 k hk

lemma IsFixedPositiveElevenThirteenLawPair.left_rare_pos
    {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsFixedPositiveElevenThirteenLawPair nuL nuR zeta) :
    (nuL 11 : ℝ≥0∞) ≠ 0 := by
  rw [hLaw.1.1]
  exact hLaw.2.1

lemma IsFixedPositiveElevenThirteenLawPair.right_rare_pos
    {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsFixedPositiveElevenThirteenLawPair nuL nuR zeta) :
    (nuR 13 : ℝ≥0∞) ≠ 0 := by
  rw [hLaw.1.2.1]
  exact hLaw.2.1

/-- The graph-potential smallness regime is inhabited: a point mass at the
distinguished label has zero total potential under a reflexive relation. -/
lemma etaG_pure_eq_zero (alpha : ℝ) (Rv : V → V → Prop) (v0 : V)
    (hrefl : Rv v0 v0) :
    etaG alpha Rv (PMF.pure v0) = 0 := by
  rw [etaG, PhiD]
  simp [q, qE_pure, badInd, hrefl]

/-- Screen envelope corresponding to the fixed-law Green multiplier. -/
noncomputable def graftFixedX (A Gamma : ℝ) : ℝ := 2 * A * Gamma

/-- Ordinary barrier coefficient after reserving half of the contraction
slack for the linear inhomogeneous and screen terms. -/
noncomputable def graftFixedK (A Gamma lambda : ℝ) : ℝ :=
  1 + 2 * A * (1 + graftFixedX A Gamma) / (1 - lambda)

/-- Explicit graph-potential threshold for one fixed offspring-law pair.
The three entries respectively close the screen quadratic terms, close the
ordinary quadratic terms, and make the final probability lower bound at
least `1/2`. -/
noncomputable def graftFixedEtaThreshold (A Gamma lambda : ℝ) : ℝ :=
  let X := graftFixedX A Gamma
  let K := graftFixedK A Gamma lambda
  min (1 / (1 + K + K * X + X ^ 2))
    (min
      ((1 - lambda) * K /
        (2 * A * (1 + K ^ 2 + K * X + X ^ 2)))
      (1 / (2 * K)))

lemma graftFixedX_nonneg {A Gamma : ℝ}
    (hA : 0 ≤ A) (hGamma : 0 ≤ Gamma) :
    0 ≤ graftFixedX A Gamma := by
  rw [graftFixedX]
  positivity

lemma graftFixedK_pos {A Gamma lambda : ℝ}
    (hA : 0 < A) (hGamma : 0 ≤ Gamma) (hlambda : lambda < 1) :
    0 < graftFixedK A Gamma lambda := by
  rw [graftFixedK]
  have hX : 0 ≤ graftFixedX A Gamma :=
    graftFixedX_nonneg hA.le hGamma
  positivity

/-- The chosen ordinary barrier reserves half of the contraction slack for
the linear inhomogeneous and screen terms. -/
lemma graftFixedK_linear_reserve {A Gamma lambda : ℝ}
    (hlambda : lambda < 1) :
    2 * A * (1 + graftFixedX A Gamma) ≤
      (1 - lambda) * graftFixedK A Gamma lambda := by
  have hs : 0 < 1 - lambda := sub_pos.mpr hlambda
  have heq :
      (1 - lambda) * graftFixedK A Gamma lambda =
        (1 - lambda) + 2 * A * (1 + graftFixedX A Gamma) := by
    rw [graftFixedK]
    field_simp
  rw [heq]
  exact le_add_of_nonneg_left hs.le

/-- The displayed fixed-law threshold is non-vacuous. -/
theorem graftFixedEtaThreshold_pos {A Gamma lambda : ℝ}
    (hA : 0 < A) (hGamma : 0 ≤ Gamma) (hlambda : lambda < 1) :
    0 < graftFixedEtaThreshold A Gamma lambda := by
  have hX : 0 ≤ graftFixedX A Gamma :=
    graftFixedX_nonneg hA.le hGamma
  have hK : 0 < graftFixedK A Gamma lambda :=
    graftFixedK_pos hA hGamma hlambda
  rw [graftFixedEtaThreshold]
  exact lt_min
    (div_pos zero_lt_one (by positivity))
    (lt_min
      (div_pos (mul_pos (sub_pos.mpr hlambda) hK) (by positivity))
      (div_pos zero_lt_one (by positivity)))

/-- Any nonnegative graph potential below the fixed-law threshold satisfies
the three scalar inequalities used in the invariant argument. -/
theorem graftFixedEtaThreshold_absorbs {A Gamma lambda eta : ℝ}
    (hA : 0 < A) (hGamma : 0 ≤ Gamma)
    (hlambda : lambda < 1) (heta0 : 0 ≤ eta)
    (heta : eta ≤ graftFixedEtaThreshold A Gamma lambda) :
    let X := graftFixedX A Gamma
    let K := graftFixedK A Gamma lambda
    eta * (K + K * X + X ^ 2) ≤ 1 ∧
      A * (K ^ 2 + K * X + X ^ 2) * eta ≤
        (1 - lambda) * K / 2 ∧
      K * eta ≤ 2⁻¹ := by
  dsimp only
  let X := graftFixedX A Gamma
  let K := graftFixedK A Gamma lambda
  let Q1 := K + K * X + X ^ 2
  let Q2 := K ^ 2 + K * X + X ^ 2
  have hX : 0 ≤ X := by
    dsimp [X]
    exact graftFixedX_nonneg hA.le hGamma
  have hK : 0 < K := by
    dsimp [K]
    exact graftFixedK_pos hA hGamma hlambda
  have hQ1 : 0 ≤ Q1 := by
    dsimp [Q1]
    positivity
  have hQ2 : 0 ≤ Q2 := by
    dsimp [Q2]
    positivity
  rw [graftFixedEtaThreshold] at heta
  change eta ≤
    min (1 / (1 + K + K * X + X ^ 2))
      (min ((1 - lambda) * K /
          (2 * A * (1 + K ^ 2 + K * X + X ^ 2)))
        (1 / (2 * K))) at heta
  have hfirst : eta ≤ 1 / (1 + K + K * X + X ^ 2) := by
    exact heta.trans (min_le_left _ _)
  have hsecond : eta ≤
      (1 - lambda) * K /
        (2 * A * (1 + K ^ 2 + K * X + X ^ 2)) := by
    exact heta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hthird : eta ≤ 1 / (2 * K) := by
    exact heta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmul1 : eta * (1 + K + K * X + X ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity :
      0 < 1 + K + K * X + X ^ 2)).mp hfirst
  have hmul2 : eta *
      (2 * A * (1 + K ^ 2 + K * X + X ^ 2)) ≤
        (1 - lambda) * K :=
    (le_div_iff₀ (by positivity :
      0 < 2 * A * (1 + K ^ 2 + K * X + X ^ 2))).mp hsecond
  have hmul3 : eta * (2 * K) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * K)).mp hthird
  change eta * Q1 ≤ 1 ∧ A * Q2 * eta ≤
      (1 - lambda) * K / 2 ∧ K * eta ≤ 2⁻¹
  constructor
  · nlinarith
  constructor
  · have htwo : 0 < (2 : ℝ) := by norm_num
    apply (le_div_iff₀ htwo).2
    nlinarith
  · norm_num at ⊢
    nlinarith

end GraphMarkovMatching
