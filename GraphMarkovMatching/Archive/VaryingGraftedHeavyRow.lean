/-
Heavy-component normalization for the literal grafted 11/13 laws.

This is the quantitative replacement for the invalid expansion of the
fresh target inverse degree into all five offspring components.  The latter
contains the exceptional coefficient `zeta ^ (-alpha)`.  Here we select a
single common component of mass at least `1/8`.  On its live set it controls
the mixture inverse degree at cost `8 ^ alpha`; on its dead set the remainder
is returned to the aggregate ordinary potential at cost `8`.  Consequently
no inverse exceptional mass appears.
-/
import GraphMarkovMatching.Archive.VaryingGraftedAssembly
import GraphMarkovMatching.Archive.VaryingHeavyCoreWeighted

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {V : Type}

/-- A closed version of the generic heavy-component screen split.  The
component-dead remainder with an arbitrary pre-existing zero list is no
larger than the singleton component-dead screen, hence is paid by the
aggregate ordinary potential. -/
lemma screenE_bind_WresD_le_eight_rpow_add_PhiDres
    {A X : Type} (alpha : ℝ) (halpha : 0 < alpha)
    (rho : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (a : A) (ha : 8⁻¹ ≤ (w a : ℝ≥0∞))
    (zs : List (PMF X)) :
    screenE rho R zs (WresD alpha (w.bind f) R) ≤
      (8 : ℝ≥0∞) ^ alpha * screenE rho R zs (WresD alpha (f a) R) +
        8 * PhiDres alpha rho (w.bind f) R := by
  refine (screenE_bind_WresD_le_eight_rpow_add_screen alpha halpha.le
    rho w f R a ha zs).trans (add_le_add le_rfl ?_)
  refine (screenE_le_of_subset rho R (zs₁ := [f a])
    (zs₂ := f a :: zs) ?_ (WresD alpha (w.bind f) R)).trans ?_
  · intro z hz
    rw [List.mem_singleton] at hz
    simp [hz]
  · exact screen_bind_WresD_component_dead_le_eight_PhiDres
      alpha halpha rho w f R a ha

/-- The four common weights of one offspring law, indexed by the literal
arities `3,5,7,9`. -/
noncomputable def graftCommonWeights (nu : PMF ℕ) : Fin 4 → ℝ≥0∞ :=
  fun i => nu (graftCommonArity i)

lemma graftCommonWeights_sum_eq_explicit (nu : PMF ℕ) :
    (∑ i, graftCommonWeights nu i) =
      (nu 3 : ℝ≥0∞) + nu 5 + nu 7 + nu 9 := by
  simp [graftCommonWeights, graftCommonArity, Fin.sum_univ_four]

/-- The left common mass is exactly `1-zeta`; this follows from the actual
support statement in `IsElevenThirteenLawPair`, not from an informal support
enumeration. -/
lemma elevenThirteen_left_common_total {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta) :
    (∑ i, graftCommonWeights nuL i) = 1 - zeta := by
  have hout : ∀ k ∉ insert 11 elevenThirteenCommonCore,
      (nuL k : ℝ≥0∞) = 0 := by
    intro k hk
    by_contra hne
    exact hk (hLaw.2.2.2.1 k hne)
  have htotal := nuL.tsum_coe
  rw [tsum_eq_sum hout] at htotal
  have hadd : (∑ i, graftCommonWeights nuL i) + zeta = 1 := by
    rw [graftCommonWeights_sum_eq_explicit, ← hLaw.1]
    simpa [elevenThirteenCommonCore, add_assoc, add_left_comm, add_comm]
      using htotal
  have hzeta_top : zeta ≠ ⊤ := by
    rw [← hLaw.1]
    exact PMF.apply_ne_top nuL 11
  exact ENNReal.eq_sub_of_add_eq hzeta_top hadd

/-- The right common mass is exactly `1-zeta`. -/
lemma elevenThirteen_right_common_total {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta) :
    (∑ i, graftCommonWeights nuR i) = 1 - zeta := by
  have hout : ∀ k ∉ insert 13 elevenThirteenCommonCore,
      (nuR k : ℝ≥0∞) = 0 := by
    intro k hk
    by_contra hne
    exact hk (hLaw.2.2.2.2 k hne)
  have htotal := nuR.tsum_coe
  rw [tsum_eq_sum hout] at htotal
  have hadd : (∑ i, graftCommonWeights nuR i) + zeta = 1 := by
    rw [graftCommonWeights_sum_eq_explicit, ← hLaw.2.1]
    simpa [elevenThirteenCommonCore, add_assoc, add_left_comm, add_comm]
      using htotal
  have hzeta_top : zeta ≠ ⊤ := by
    rw [← hLaw.2.1]
    exact PMF.apply_ne_top nuR 13
  exact ENNReal.eq_sub_of_add_eq hzeta_top hadd

/-- If `zeta <= 1/2`, the left law has a common arity of mass at least
`1/8`.  No lower bound on every common weight is used. -/
lemma elevenThirteen_left_has_heavy_common {nuL nuR : PMF ℕ}
    {zeta : ℝ≥0∞} (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hzeta : zeta ≤ 2⁻¹) :
    8⁻¹ ≤ (nuL (graftCommonArity
      (heavyCoreIndex (graftCommonWeights nuL))) : ℝ≥0∞) := by
  exact eighth_le_heavyCoreWeight (graftCommonWeights nuL) hzeta
    (elevenThirteen_left_common_total hLaw)

/-- If `zeta <= 1/2`, the right law has a common arity of mass at least
`1/8`. -/
lemma elevenThirteen_right_has_heavy_common {nuL nuR : PMF ℕ}
    {zeta : ℝ≥0∞} (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hzeta : zeta ≤ 2⁻¹) :
    8⁻¹ ≤ (nuR (graftCommonArity
      (heavyCoreIndex (graftCommonWeights nuR))) : ℝ≥0∞) := by
  exact eighth_le_heavyCoreWeight (graftCommonWeights nuR) hzeta
    (elevenThirteen_right_common_total hLaw)

/-- Literal tagged specialization of the heavy-component split. -/
lemma graftXiBar_screen_le_heavy_component
    (alpha : ℝ) (halpha : 0 ≤ alpha) (Rv : V → V → Prop)
    (mu : PMF V) (nu : PMF ℕ) (v0 : V) (left : Bool)
    (h : ℕ) (rho : PMF
      (FullLab (GraftState V) h × FullLab (GraftState V) h))
    (zs : List (PMF
      (FullLab (GraftState V) h × FullLab (GraftState V) h)))
    (i : Fin 4) (hi : 8⁻¹ ≤ (nu (graftCommonArity i) : ℝ≥0∞)) :
    screenE rho (SquareRel (fullSim (graftLabRel Rv) h)) zs
        (WresD alpha (graftXiBar left mu nu v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h))) ≤
      (8 : ℝ≥0∞) ^ alpha *
        screenE rho (SquareRel (fullSim (graftLabRel Rv) h)) zs
          (WresD alpha
            (graftXi left mu nu v0 (.ordinary (graftCommonArity i)) h)
            (SquareRel (fullSim (graftLabRel Rv) h))) +
      screenE rho (SquareRel (fullSim (graftLabRel Rv) h))
        (graftXi left mu nu v0 (.ordinary (graftCommonArity i)) h :: zs)
        (WresD alpha (graftXiBar left mu nu v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h))) := by
  simpa only [graftXiBar] using
    screenE_bind_WresD_le_eight_rpow_add_screen alpha halpha rho nu
      (fun k => graftXi left mu nu v0 (.ordinary k) h)
      (SquareRel (fullSim (graftLabRel Rv) h))
      (graftCommonArity i) hi zs

/-- Closed literal tagged heavy-component estimate.  Its only target-mixture
costs are `8^alpha` and an ordinary-potential coefficient `8`; in particular
there is no `zeta^(-alpha)` term. -/
lemma graftXiBar_screen_le_heavy_component_add_PhiDres
    (alpha : ℝ) (halpha : 0 < alpha) (Rv : V → V → Prop)
    (mu : PMF V) (nu : PMF ℕ) (v0 : V) (left : Bool)
    (h : ℕ) (rho : PMF
      (FullLab (GraftState V) h × FullLab (GraftState V) h))
    (zs : List (PMF
      (FullLab (GraftState V) h × FullLab (GraftState V) h)))
    (i : Fin 4) (hi : 8⁻¹ ≤ (nu (graftCommonArity i) : ℝ≥0∞)) :
    screenE rho (SquareRel (fullSim (graftLabRel Rv) h)) zs
        (WresD alpha (graftXiBar left mu nu v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h))) ≤
      (8 : ℝ≥0∞) ^ alpha *
        screenE rho (SquareRel (fullSim (graftLabRel Rv) h)) zs
          (WresD alpha
            (graftXi left mu nu v0 (.ordinary (graftCommonArity i)) h)
            (SquareRel (fullSim (graftLabRel Rv) h))) +
      8 * PhiDres alpha rho (graftXiBar left mu nu v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) := by
  simpa only [graftXiBar] using
    screenE_bind_WresD_le_eight_rpow_add_PhiDres alpha halpha rho nu
      (fun k => graftXi left mu nu v0 (.ordinary k) h)
      (SquareRel (fullSim (graftLabRel Rv) h))
      (graftCommonArity i) hi zs

private lemma graftCommonArity_mem_core (i : Fin 4) :
    graftCommonArity i ∈ elevenThirteenCommonCore := by
  fin_cases i <;> simp [graftCommonArity, elevenThirteenCommonCore]

/-- A source offspring component screened by the child members of the
successor zero list and normalized by one common target component is bounded
by the literal straight/crossed Hall outputs. -/
theorem graftXi_screen_common_component_le_freshHallTerm
    (alpha : ℝ) (halpha : 0 ≤ alpha) (Rv : V → V → Prop)
    (mu : PMF V) (v0 : V)
    (leftSource leftTarget : Bool) (nuS nuT : PMF ℕ)
    (h : ℕ) (z : Finset GraftTgt) (k : ℕ)
    (hksupp : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore) (i : Fin 4) :
    screenE (graftXi leftSource mu nuS v0 (.ordinary k) h)
        (SquareRel (fullSim (graftLabRel Rv) h))
        ((graftMemPairs mu v0 leftTarget nuT h z).map
          (fun p => prodPMF p.1 p.2))
        (WresD alpha
          (graftXi leftTarget mu nuT v0
            (.ordinary (graftCommonArity i)) h)
          (SquareRel (fullSim (graftLabRel Rv) h))) ≤
      graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT h z
        (graftSupportedPair leftSource k).1
        (graftSupportedPair leftSource k).2 (graftCommonArity i) := by
  let R := fullSim (graftLabRel Rv) h
  let ms := graftMemPairs mu v0 leftTarget nuT h z
  let zs := (graftZSuccCommon z).toList.map
    (graftInterp mu v0 leftTarget nuT h)
  let sa := graftSupportedPair leftSource k
  let ta := graftSupportedPair leftTarget (graftCommonArity i)
  let rhoA := graftInterp mu v0 leftSource nuS h sa.1
  let rhoB := graftInterp mu v0 leftSource nuS h sa.2
  let W0 := WresD alpha (graftInterp mu v0 leftTarget nuT h ta.1) R
  let W1 := WresD alpha (graftInterp mu v0 leftTarget nuT h ta.2) R
  have hsource : graftXi leftSource mu nuS v0 (.ordinary k) h =
      prodPMF rhoA rhoB := by
    simpa [rhoA, rhoB, sa] using
      graftXi_eq_prod_of_fixed_support mu v0 leftSource nuS h k hksupp
  have htarget : graftXi leftTarget mu nuT v0
      (.ordinary (graftCommonArity i)) h =
      prodPMF (graftInterp mu v0 leftTarget nuT h ta.1)
        (graftInterp mu v0 leftTarget nuT h ta.2) := by
    apply graftXi_eq_prod_of_fixed_support
    exact Finset.mem_insert_of_mem (graftCommonArity_mem_core i)
  have hind : ∀ xp,
      screenInd (SquareRel R) (ms.map (fun p => prodPMF p.1 p.2)) xp =
        if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
          then 1 else 0 := by
    intro xp
    rw [screenInd]
    congr 1
    apply propext
    constructor
    · intro hall p hp
      exact hall _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    · intro hall rho hrho
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrho
      exact hall p hp
  have htilt : ∀ xp,
      WresD alpha
          (graftXi leftTarget mu nuT v0
            (.ordinary (graftCommonArity i)) h)
          (SquareRel R) xp ≤
        W0 xp.1 * W1 xp.2 + W1 xp.1 * W0 xp.2 := by
    intro xp
    rw [htarget]
    exact WresD_square_le_sum halpha _ _ R xp
  rw [hsource, screenE]
  change (∑' xp, prodPMF rhoA rhoB xp *
      screenInd (SquareRel R) (ms.map (fun p => prodPMF p.1 p.2)) xp *
      WresD alpha
        (graftXi leftTarget mu nuT v0
          (.ordinary (graftCommonArity i)) h)
        (SquareRel R) xp) ≤ _
  calc
    (∑' xp, prodPMF rhoA rhoB xp *
        screenInd (SquareRel R) (ms.map (fun p => prodPMF p.1 p.2)) xp *
        WresD alpha
          (graftXi leftTarget mu nuT v0
            (.ordinary (graftCommonArity i)) h)
          (SquareRel R) xp) ≤
      (∑' xp, prodPMF rhoA rhoB xp *
        ((if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
          then 1 else 0) * (W0 xp.1 * W1 xp.2))) +
      (∑' xp, prodPMF rhoA rhoB xp *
        ((if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
          then 1 else 0) * (W1 xp.1 * W0 xp.2))) := by
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun xp => ?_
        rw [hind xp]
        calc
          prodPMF rhoA rhoB xp *
              (if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
                then 1 else 0) *
              WresD alpha
                (graftXi leftTarget mu nuT v0
                  (.ordinary (graftCommonArity i)) h)
                (SquareRel R) xp ≤
            prodPMF rhoA rhoB xp *
              ((if ∀ p ∈ ms,
                  rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
                then 1 else 0) *
                (W0 xp.1 * W1 xp.2 + W1 xp.1 * W0 xp.2)) := by
                  simpa only [mul_assoc] using
                    mul_le_mul_right
                      (mul_le_mul_right (htilt xp)
                        (if ∀ p ∈ ms,
                          rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
                        then 1 else 0))
                      (prodPMF rhoA rhoB xp)
          _ = prodPMF rhoA rhoB xp *
                ((if ∀ p ∈ ms,
                    rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
                  then 1 else 0) * (W0 xp.1 * W1 xp.2)) +
              prodPMF rhoA rhoB xp *
                ((if ∀ p ∈ ms,
                    rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
                  then 1 else 0) * (W1 xp.1 * W0 xp.2)) := by ring
    _ ≤ graftHallRHS Rv mu v0 leftSource leftTarget nuS nuT h z
          sa.1 sa.2 W0 W1 +
        graftHallRHS Rv mu v0 leftSource leftTarget nuS nuT h z
          sa.1 sa.2 W1 W0 := by
      apply add_le_add
      · exact hallFactorize rhoA rhoB R ms zs
          (graftMemPairs_mem mu v0 leftTarget nuT h z)
          (graftMemPairs_cov mu v0 leftTarget nuT h z) W0 W1
      · exact hallFactorize rhoA rhoB R ms zs
          (graftMemPairs_mem mu v0 leftTarget nuT h z)
          (graftMemPairs_cov mu v0 leftTarget nuT h z) W1 W0
    _ = _ := by
      rfl

/-- The near-root fresh/fresh row with the heavy-common normalization
inserted.  The source component coefficient is untouched.  The fixed common
target component produces the ordinary Hall output, while the heavy-dead
remainder is returned to the component-to-mixture ordinary potential.
Neither term contains an inverse exceptional mass. -/
theorem graftComponentScreen_some_fresh_le_heavy_hall
    (alpha : ℝ) (halpha : 0 < alpha) (Rv : V → V → Prop)
    (mu : PMF V) (v0 : V)
    (leftSource leftTarget : Bool) (nuS nuT : PMF ℕ)
    (hcommon : ∀ i : Fin 4,
      (nuT (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    {v : V} (hv0 : Rv v v0) (hvpos : rE mu Rv v ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) (k : ℕ)
    (hksupp : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore)
    (i : Fin 4) (hi : 8⁻¹ ≤ (nuT (graftCommonArity i) : ℝ≥0∞)) :
    screenE
        (muM (graftK leftSource mu nuS v0) (v, .ordinary k) (h + 1))
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
        (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      (rE mu Rv v) ^ (-alpha) *
        ((8 : ℝ≥0∞) ^ alpha *
          graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
            h z (graftSupportedPair leftSource k).1
              (graftSupportedPair leftSource k).2 (graftCommonArity i) +
        8 * PhiDres alpha
          (graftXi leftSource mu nuS v0 (.ordinary k) h)
          (graftXiBar leftTarget mu nuT v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h))) := by
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
        ((8 : ℝ≥0∞) ^ alpha *
          screenE rho R2 childzs
            (WresD alpha
              (graftXi leftTarget mu nuT v0
                (.ordinary (graftCommonArity i)) h) R2) +
          8 * PhiDres alpha rho mix R2) := by
      apply mul_le_mul_right
      exact graftXiBar_screen_le_heavy_component_add_PhiDres
        alpha halpha Rv mu nuT v0 leftTarget h rho childzs i hi
    _ ≤ rootTilt *
        ((8 : ℝ≥0∞) ^ alpha *
          graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
            h z (graftSupportedPair leftSource k).1
              (graftSupportedPair leftSource k).2 (graftCommonArity i) +
          8 * PhiDres alpha rho mix R2) := by
      apply mul_le_mul_right
      exact add_le_add
        (mul_le_mul_right
          (graftXi_screen_common_component_le_freshHallTerm
            alpha halpha.le Rv mu v0 leftSource leftTarget nuS nuT h z k
              hksupp i) ((8 : ℝ≥0∞) ^ alpha))
        le_rfl
    _ = _ := by rfl

end GraphMarkovMatching
