import GraphMarkovMatching.Archive.VaryingGraftedHeavyRow

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {V : Type}

private lemma screenInd_le_one {X : Type} (R : X → X → Prop)
    (zs : List (PMF X)) (x : X) : screenInd R zs x ≤ 1 := by
  rw [screenInd]
  split <;> simp

theorem graftFreshScreen_some_fresh_le_heavy_far_add_hall
    (alpha : ℝ) (halpha : 1 ≤ alpha) (Rv : V → V → Prop)
    (mu : PMF V) (v0 : V)
    (leftSource leftTarget : Bool) (nuS nuT : PMF ℕ)
    (hssupp : ∀ k, (nuS k : ℝ≥0∞) ≠ 0 →
      k ∈ insert (graftRareArity leftSource) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4,
      (nuT (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl : ∀ v, Rv v v)
    (h : ℕ) (z : Finset GraftTgt) (i : Fin 4)
    (hi : 8⁻¹ ≤ (nuT (graftCommonArity i) : ℝ≥0∞))
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
        RT * ((8 : ℝ≥0∞) ^ alpha *
          ∑' k, (nuS k : ℝ≥0∞) *
            graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
              h z (graftSupportedPair leftSource k).1
                (graftSupportedPair leftSource k).2 (graftCommonArity i) +
          8 * M) := by
  have halpha0 : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  rw [graftInterp_F, graftFreshScreen_split mu v0 leftSource nuS (h + 1)]
  let H : ℕ → ℝ≥0∞ := fun k =>
    graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
      h z (graftSupportedPair leftSource k).1
        (graftSupportedPair leftSource k).2 (graftCommonArity i)
  let C : ℝ≥0∞ := 1 + ENNReal.ofReal alpha * M
  let D : ℕ → ℝ≥0∞ := fun k => (8 : ℝ≥0∞) ^ alpha * H k + 8 * M
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
      refine (graftComponentScreen_some_fresh_le_heavy_hall
        alpha halpha0 Rv mu v0 leftSource leftTarget nuS nuT hcommon
        hv hvpos h z k hksupp i hi).trans ?_
      apply mul_le_mul_right
      exact add_le_add le_rfl
        (mul_le_mul_right (hMom k hk) (8 : ℝ≥0∞))
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
                  (screenInd_le_one
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
            (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
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
                  (le_refl ((mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha) * C))
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
          calc
            (∑' k, (nuS k : ℝ≥0∞) * (RT * D k)) +
                ∑' k, (nuS k : ℝ≥0∞) * (FT * C) =
              (∑' k, RT * ((nuS k : ℝ≥0∞) * D k)) +
                ∑' k, (nuS k : ℝ≥0∞) * (FT * C) := by
                  congr 1
                  refine tsum_congr fun k => by ring
            _ = RT * (∑' k, (nuS k : ℝ≥0∞) * D k) +
                ∑' k, (nuS k : ℝ≥0∞) * (FT * C) := by
              rw [ENNReal.tsum_mul_left]
            _ = RT * (∑' k, (nuS k : ℝ≥0∞) * D k) + FT * C := by
              rw [ENNReal.tsum_mul_right, nuS.tsum_coe, one_mul]
        _ = _ := by ring
    _ ≤ FT * C + RT *
        ((8 : ℝ≥0∞) ^ alpha *
          ∑' k, (nuS k : ℝ≥0∞) * H k + 8 * M) := by
      apply add_le_add le_rfl
      apply mul_le_mul_right
      calc
        (∑' k, (nuS k : ℝ≥0∞) * D k) =
          ∑' k, ((nuS k : ℝ≥0∞) * ((8 : ℝ≥0∞) ^ alpha * H k) +
            (nuS k : ℝ≥0∞) * (8 * M)) := by
              refine tsum_congr fun k => by simp [D]; ring
        _ = (∑' k, (nuS k : ℝ≥0∞) *
              ((8 : ℝ≥0∞) ^ alpha * H k)) +
            ∑' k, (nuS k : ℝ≥0∞) * (8 * M) :=
              ENNReal.tsum_add
        _ = (8 : ℝ≥0∞) ^ alpha *
              ∑' k, (nuS k : ℝ≥0∞) * H k +
            ∑' k, (nuS k : ℝ≥0∞) * (8 * M) := by
              congr 1
              calc
                (∑' k, (nuS k : ℝ≥0∞) *
                    ((8 : ℝ≥0∞) ^ alpha * H k)) =
                  ∑' k, (8 : ℝ≥0∞) ^ alpha *
                    ((nuS k : ℝ≥0∞) * H k) := by
                      refine tsum_congr fun k => by ring
                _ = _ := ENNReal.tsum_mul_left
        _ = (8 : ℝ≥0∞) ^ alpha *
              ∑' k, (nuS k : ℝ≥0∞) * H k + 8 * M := by
              rw [ENNReal.tsum_mul_right, nuS.tsum_coe, one_mul]
        _ ≤ _ := le_rfl
    _ = _ := by rfl

theorem graftFreshScreen_some_fresh_le_heavy_eta_add_hall
    (alpha : ℝ) (halpha : 1 ≤ alpha) (Rv : V → V → Prop)
    (mu : PMF V) (v0 : V)
    (leftSource leftTarget : Bool) (nuS nuT : PMF ℕ)
    (hssupp : ∀ k, (nuS k : ℝ≥0∞) ≠ 0 →
      k ∈ insert (graftRareArity leftSource) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4,
      (nuT (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ v w, Rv v w → Rv w v)
    (hhalf : 2⁻¹ ≤ (mu v0 : ℝ≥0∞))
    (h : ℕ) (z : Finset GraftTgt) (i : Fin 4)
    (hi : 8⁻¹ ≤ (nuT (graftCommonArity i) : ℝ≥0∞))
    (M : ℝ≥0∞)
    (hMom : ∀ k, (nuS k : ℝ≥0∞) ≠ 0 →
      PhiDres alpha (graftXi leftSource mu nuS v0 (.ordinary k) h)
        (graftXiBar leftTarget mu nuT v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) ≤ M) :
    screenE (graftInterp mu v0 leftSource nuS (h + 1) .F)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp mu v0 leftTarget nuT (h + 1)))
        (WresD alpha (graftInterp mu v0 leftTarget nuT (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      (2 * etaG alpha Rv mu) * (1 + ENNReal.ofReal alpha * M) +
        ((2 : ℝ≥0∞) ^ alpha + 2 * etaG alpha Rv mu) *
          ((8 : ℝ≥0∞) ^ alpha *
            ∑' k, (nuS k : ℝ≥0∞) *
              graftFreshHallTerm Rv mu v0 alpha leftSource leftTarget nuS nuT
                h z (graftSupportedPair leftSource k).1
                  (graftSupportedPair leftSource k).2
                  (graftCommonArity i) + 8 * M) := by
  apply graftFreshScreen_some_fresh_le_heavy_far_add_hall
    alpha halpha Rv mu v0 leftSource leftTarget nuS nuT hssupp hcommon
      hrefl h z i hi
      ((2 : ℝ≥0∞) ^ alpha + 2 * etaG alpha Rv mu)
      (2 * etaG alpha Rv mu) M
  · exact tilt_le_pow_add alpha Rv mu v0 (by linarith) hsymm hhalf
  · calc
      (∑' v, if Rv v v0 then 0 else
          (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) =
        ∑' v, if Rv v0 v then 0 else
          (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha) := by
            refine tsum_congr fun v => ?_
            have hviff : Rv v v0 ↔ Rv v0 v :=
              ⟨hsymm v v0, hsymm v0 v⟩
            by_cases hv : Rv v v0
            · rw [if_pos hv, if_pos (hviff.mp hv)]
            · rw [if_neg hv, if_neg (fun hc => hv (hviff.mpr hc))]
      _ ≤ 2 * etaG alpha Rv mu :=
        far_tilt_le alpha Rv mu v0 (by linarith) hsymm hhalf
  · exact hMom

end GraphMarkovMatching

