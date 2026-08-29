/- Asymmetric ordinary one-step decompositions and a source-generic fresh-target mixture split. -/
import GraphMarkovMatching.Process.Descent

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (alpha : ℝ) (Rv : V → V → Prop) (mu : PMF V)
  (nuL nuR : PMF ℕ) (v0 : V)

lemma PhiDres_muM_Zlaw_cross_succ (v : V) (k j h : ℕ) :
    PhiDres alpha (muM (varyK mu nuL v0) (v, k) (h + 1)) (Zlaw mu nuR v0 j (h + 1))
        (fullSim (labRel Rv) (h + 1))
      = if Rv v v0 then
          PhiDres alpha (Xi mu nuL v0 k h) (Xi mu nuR v0 j h)
            (SquareRel (fullSim (labRel Rv) h))
        else 0 := by
  rw [muM_varyK_succ mu nuL v0 v k h, PhiDres, tsum_map_mul]
  by_cases hv : Rv v v0
  · rw [if_pos hv, PhiDres]
    refine tsum_congr fun xp => ?_
    congr 1
    have hrE := rE_Zlaw_succ_branch mu nuR v0 Rv v k j h xp
    rw [if_pos hv] at hrE
    have hq : q (Zlaw mu nuR v0 j (h + 1)) (fullSim (labRel Rv) (h + 1))
          (branch (v, k) xp)
        = q (Xi mu nuR v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp := by
      rw [q, q, qE_Zlaw_succ_branch mu nuR v0 Rv hv k j h xp]
    rw [hrE, hq]
  · rw [if_neg hv]
    refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
    have hrE := rE_Zlaw_succ_branch mu nuR v0 Rv v k j h xp
    rw [if_neg hv] at hrE
    rw [hrE]
    simp

/-- **Fresh target, one cell root**: the split bound at a root `(v,k)`. -/

lemma PhiDres_muM_Tlaw_cross_succ (halpha : 1 ≤ alpha) (v : V) (k h : ℕ) :
    PhiDres alpha (muM (varyK mu nuL v0) (v, k) (h + 1)) (Tlaw mu nuR v0 (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ phiE alpha (q mu Rv v)
        + PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * alpha)
          * (phiE alpha (q mu Rv v)
            * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
  rw [muM_varyK_succ mu nuL v0 v k h, PhiDres, tsum_map_mul]
  have hpt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi mu nuL v0 k h xp
        * (if rE (Tlaw mu nuR v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp) = 0 then 0
            else phiE alpha (q (Tlaw mu nuR v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp)))
      ≤ Xi mu nuL v0 k h xp * phiE alpha (q mu Rv v)
        + Xi mu nuL v0 k h xp
          * (if rE (XiBar mu nuR v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then 0
              else phiE alpha (q (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp))
        + ENNReal.ofReal (2 * alpha) * (phiE alpha (q mu Rv v)
            * (Xi mu nuL v0 k h xp
              * (if rE (XiBar mu nuR v0 h) (SquareRel (fullSim (labRel Rv) h)) xp
                    = 0 then 0
                  else phiE alpha (q (XiBar mu nuR v0 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)))) := by
    intro xp
    by_cases hres : rE (Tlaw mu nuR v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
        (branch (v, k) xp) = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      have hfac := rE_Tlaw_succ_branch mu nuR v0 Rv v k h xp
      rw [hfac] at hres
      obtain ⟨-, hXi⟩ := mul_ne_zero_iff.mp hres
      rw [if_neg hXi]
      calc Xi mu nuL v0 k h xp
            * phiE alpha (q (Tlaw mu nuR v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp))
          ≤ Xi mu nuL v0 k h xp * (phiE alpha (q mu Rv v)
              + phiE alpha (q (XiBar mu nuR v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)
              + ENNReal.ofReal (2 * alpha) * (phiE alpha (q mu Rv v)
                  * phiE alpha (q (XiBar mu nuR v0 h)
                      (SquareRel (fullSim (labRel Rv) h)) xp))) :=
            mul_le_mul_right (phiE_branch_le alpha Rv mu nuR v0 halpha v k h xp) _
        _ = Xi mu nuL v0 k h xp * phiE alpha (q mu Rv v)
              + Xi mu nuL v0 k h xp
                * phiE alpha (q (XiBar mu nuR v0 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)
              + ENNReal.ofReal (2 * alpha) * (phiE alpha (q mu Rv v)
                  * (Xi mu nuL v0 k h xp
                    * phiE alpha (q (XiBar mu nuR v0 h)
                        (SquareRel (fullSim (labRel Rv) h)) xp))) := by ring
  calc ∑' xp, Xi mu nuL v0 k h xp
        * (if rE (Tlaw mu nuR v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp) = 0 then 0
            else phiE alpha (q (Tlaw mu nuR v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp)))
      ≤ ∑' xp, (Xi mu nuL v0 k h xp * phiE alpha (q mu Rv v)
          + Xi mu nuL v0 k h xp
            * (if rE (XiBar mu nuR v0 h) (SquareRel (fullSim (labRel Rv) h)) xp
                  = 0 then 0
                else phiE alpha (q (XiBar mu nuR v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp))
          + ENNReal.ofReal (2 * alpha) * (phiE alpha (q mu Rv v)
              * (Xi mu nuL v0 k h xp
                * (if rE (XiBar mu nuR v0 h)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
                    else phiE alpha (q (XiBar mu nuR v0 h)
                      (SquareRel (fullSim (labRel Rv) h)) xp))))) :=
        ENNReal.tsum_le_tsum hpt
    _ = phiE alpha (q mu Rv v)
        + PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * alpha)
          * (phiE alpha (q mu Rv v)
            * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          PMF.tsum_coe, one_mul, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          PhiDres]

/-- The forced-forced pair step (`s = Z_k`, `t = Z_j`): an exact identity. -/

lemma PhiDres_Zlaw_Zlaw_cross_succ (hrefl : Rv v0 v0) (k j h : ℕ) :
    PhiDres alpha (Zlaw mu nuL v0 k (h + 1)) (Zlaw mu nuR v0 j (h + 1))
        (fullSim (labRel Rv) (h + 1))
      = PhiDres alpha (Xi mu nuL v0 k h) (Xi mu nuR v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) := by
  rw [show Zlaw mu nuL v0 k (h + 1)
      = muM (varyK mu nuL v0) (v0, k) (h + 1) from rfl,
    PhiDres_muM_Zlaw_cross_succ alpha Rv mu nuL nuR v0 v0 k j h, if_pos hrefl]

/-- The forced-fresh pair step (`s = Z_k`, `t = F`). -/

lemma PhiDres_Zlaw_Tlaw_cross_succ (halpha : 1 ≤ alpha) (k h : ℕ) :
    PhiDres alpha (Zlaw mu nuL v0 k (h + 1)) (Tlaw mu nuR v0 (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ phiE alpha (q mu Rv v0)
        + PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * alpha)
          * (phiE alpha (q mu Rv v0)
            * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h))) :=
  PhiDres_muM_Tlaw_cross_succ alpha Rv mu nuL nuR v0 halpha v0 k h

/-- The fresh-forced pair step (`s = F`, `t = Z_j`): the root mass is at
most one, so the mixture of square coordinates bounds the coordinate. -/

lemma PhiDres_Tlaw_Zlaw_cross_succ (j h : ℕ) :
    PhiDres alpha (Tlaw mu nuL v0 (h + 1)) (Zlaw mu nuR v0 j (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ ∑' k, nuL k * PhiDres alpha (Xi mu nuL v0 k h) (Xi mu nuR v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) := by
  rw [show Tlaw mu nuL v0 (h + 1)
      = (freshQ mu nuL).bind (fun s => muM (varyK mu nuL v0) s (h + 1)) from rfl,
    PhiDres_bind_left]
  calc ∑' s : V × ℕ, freshQ mu nuL s
        * PhiDres alpha (muM (varyK mu nuL v0) s (h + 1)) (Zlaw mu nuR v0 j (h + 1))
            (fullSim (labRel Rv) (h + 1))
      = ∑' s : V × ℕ, (mu s.1 * (if Rv s.1 v0 then 1 else 0))
          * (nuL s.2 * PhiDres alpha (Xi mu nuL v0 s.2 h) (Xi mu nuR v0 j h)
              (SquareRel (fullSim (labRel Rv) h))) := by
        refine tsum_congr fun s => ?_
        obtain ⟨v, k⟩ := s
        rw [PhiDres_muM_Zlaw_cross_succ alpha Rv mu nuL nuR v0 v k j h]
        by_cases hv : Rv v v0
        · rw [if_pos hv, if_pos hv]
          simp only [freshQ, prodPMF_apply]
          ring
        · rw [if_neg hv, if_neg hv]
          simp
    _ = (∑' v, mu v * (if Rv v v0 then 1 else 0))
        * ∑' k, nuL k * PhiDres alpha (Xi mu nuL v0 k h) (Xi mu nuR v0 j h)
            (SquareRel (fullSim (labRel Rv) h)) :=
        tsum_prod_split (fun v => mu v * (if Rv v v0 then 1 else 0))
          (fun k => nuL k * PhiDres alpha (Xi mu nuL v0 k h) (Xi mu nuR v0 j h)
            (SquareRel (fullSim (labRel Rv) h)))
    _ ≤ 1 * ∑' k, nuL k * PhiDres alpha (Xi mu nuL v0 k h) (Xi mu nuR v0 j h)
            (SquareRel (fullSim (labRel Rv) h)) := by
        refine mul_le_mul_left ?_ _
        calc ∑' v, mu v * (if Rv v v0 then 1 else 0)
            ≤ ∑' v, mu v * 1 := ENNReal.tsum_le_tsum fun v =>
              mul_le_mul_right (by split_ifs <;> simp) _
          _ = 1 := by rw [tsum_congr fun v => mul_one (mu v), PMF.tsum_coe]
    _ = ∑' k, nuL k * PhiDres alpha (Xi mu nuL v0 k h) (Xi mu nuR v0 j h)
            (SquareRel (fullSim (labRel Rv) h)) := one_mul _

/-- The fresh-fresh pair step (`s = F`, `t = F`): the root integrates to
the graph potential `η`, the cascade mixture to the `nuL`-average of square
coordinates, and the cross term is quadratic. -/

lemma PhiDres_Tlaw_Tlaw_cross_succ (halpha : 1 ≤ alpha) (h : ℕ) :
    PhiDres alpha (Tlaw mu nuL v0 (h + 1)) (Tlaw mu nuR v0 (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ etaG alpha Rv mu
        + (∑' k, nuL k * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
            (SquareRel (fullSim (labRel Rv) h)))
        + ENNReal.ofReal (2 * alpha)
          * (etaG alpha Rv mu
            * ∑' k, nuL k * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
  rw [show Tlaw mu nuL v0 (h + 1)
      = (freshQ mu nuL).bind (fun s => muM (varyK mu nuL v0) s (h + 1)) from rfl,
    PhiDres_bind_left]
  calc ∑' s : V × ℕ, freshQ mu nuL s
        * PhiDres alpha (muM (varyK mu nuL v0) s (h + 1)) (Tlaw mu nuR v0 (h + 1))
            (fullSim (labRel Rv) (h + 1))
      ≤ ∑' s : V × ℕ, freshQ mu nuL s
          * (phiE alpha (q mu Rv s.1)
            + PhiDres alpha (Xi mu nuL v0 s.2 h) (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h))
            + ENNReal.ofReal (2 * alpha)
              * (phiE alpha (q mu Rv s.1)
                * PhiDres alpha (Xi mu nuL v0 s.2 h) (XiBar mu nuR v0 h)
                    (SquareRel (fullSim (labRel Rv) h)))) := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
        obtain ⟨v, k⟩ := s
        exact PhiDres_muM_Tlaw_cross_succ alpha Rv mu nuL nuR v0 halpha v k h
    _ = (∑' s : V × ℕ, (mu s.1 * phiE alpha (q mu Rv s.1)) * nuL s.2)
        + (∑' s : V × ℕ, mu s.1 * (nuL s.2
            * PhiDres alpha (Xi mu nuL v0 s.2 h) (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h))))
        + ENNReal.ofReal (2 * alpha)
          * ∑' s : V × ℕ, (mu s.1 * phiE alpha (q mu Rv s.1))
              * (nuL s.2 * PhiDres alpha (Xi mu nuL v0 s.2 h) (XiBar mu nuR v0 h)
                  (SquareRel (fullSim (labRel Rv) h))) := by
        rw [tsum_congr fun s : V × ℕ => show freshQ mu nuL s
            * (phiE alpha (q mu Rv s.1)
              + PhiDres alpha (Xi mu nuL v0 s.2 h) (XiBar mu nuR v0 h)
                  (SquareRel (fullSim (labRel Rv) h))
              + ENNReal.ofReal (2 * alpha)
                * (phiE alpha (q mu Rv s.1)
                  * PhiDres alpha (Xi mu nuL v0 s.2 h) (XiBar mu nuR v0 h)
                      (SquareRel (fullSim (labRel Rv) h))))
            = (mu s.1 * phiE alpha (q mu Rv s.1)) * nuL s.2
              + mu s.1 * (nuL s.2
                * PhiDres alpha (Xi mu nuL v0 s.2 h) (XiBar mu nuR v0 h)
                    (SquareRel (fullSim (labRel Rv) h)))
              + ENNReal.ofReal (2 * alpha)
                * ((mu s.1 * phiE alpha (q mu Rv s.1))
                  * (nuL s.2 * PhiDres alpha (Xi mu nuL v0 s.2 h) (XiBar mu nuR v0 h)
                      (SquareRel (fullSim (labRel Rv) h))))
            from by simp only [freshQ, prodPMF_apply]; ring,
          ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ = etaG alpha Rv mu
        + (∑' k, nuL k * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
            (SquareRel (fullSim (labRel Rv) h)))
        + ENNReal.ofReal (2 * alpha)
          * (etaG alpha Rv mu
            * ∑' k, nuL k * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
        rw [tsum_prod_split (fun v => mu v * phiE alpha (q mu Rv v)) (fun k => nuL k),
          tsum_prod_split (fun v => mu v)
            (fun k => nuL k * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
              (SquareRel (fullSim (labRel Rv) h))),
          tsum_prod_split (fun v => mu v * phiE alpha (q mu Rv v))
            (fun k => nuL k * PhiDres alpha (Xi mu nuL v0 k h) (XiBar mu nuR v0 h)
              (SquareRel (fullSim (labRel Rv) h))),
          PMF.tsum_coe, PMF.tsum_coe, mul_one, one_mul, etaG, PhiD]

/-- **The fresh-target mixture** (the two-sided/one-sided split of the
cell step): the restricted square coordinate toward `Ξ̄` is bounded by the
`nuR`-average of the restricted square coordinates toward the components
plus a pair-level one-sided screen, normalized by the mixture degree
itself.  Two-sided points go through the countable mixture Jensen
inequality; on a one-sided point the potential summand is at most the
inverse mixture degree. -/

lemma PhiDres_rho_XiBar_le (h : ℕ) (rhoS : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h)) (halpha : 1 ≤ alpha) :
    PhiDres alpha (rhoS) (XiBar mu nuR v0 h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ (∑' j, nuR j * PhiDres alpha (rhoS) (Xi mu nuR v0 j h)
            (SquareRel (fullSim (labRel Rv) h)))
        + ∑' xp, rhoS xp
            * ((if ∃ j, nuR j ≠ 0 ∧ rE (Xi mu nuR v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * WresD alpha (XiBar mu nuR v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp) := by
  have halphapos : (0 : ℝ) < alpha := lt_of_lt_of_le one_pos halpha
  have hpt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      rhoS xp
        * (if rE (XiBar mu nuR v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
            then 0
            else phiE alpha (q (XiBar mu nuR v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp))
      ≤ rhoS xp
          * ∑' j, nuR j * (if rE (Xi mu nuR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
              else phiE alpha (q (Xi mu nuR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp))
        + rhoS xp
          * ((if ∃ j, nuR j ≠ 0 ∧ rE (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD alpha (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
    intro xp
    by_cases hres : rE (XiBar mu nuR v0 h)
        (SquareRel (fullSim (labRel Rv) h)) xp = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      by_cases hos : ∃ j, nuR j ≠ 0 ∧ rE (Xi mu nuR v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) xp = 0
      · have hb : phiE alpha (q (XiBar mu nuR v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
            ≤ WresD alpha (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp := by
          rw [phiE_eq_qE_mul_rpow alpha (SquareRel (fullSim (labRel Rv) h))
              (XiBar mu nuR v0 h) halphapos xp,
            rE_rpow_neg_eq_WresD (XiBar mu nuR v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp hres]
          exact le_trans (mul_le_mul_left qE_le_one _)
            (le_of_eq (one_mul _))
        refine le_trans ?_ le_add_self
        calc rhoS xp * phiE alpha (q (XiBar mu nuR v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
            ≤ rhoS xp * WresD alpha (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp :=
              mul_le_mul_right hb _
          _ = rhoS xp
              * ((if ∃ j, nuR j ≠ 0 ∧ rE (Xi mu nuR v0 j h)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0
                    then 1 else 0)
                * WresD alpha (XiBar mu nuR v0 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp) := by
              rw [if_pos hos, one_mul]
      · push Not at hos
        have hjen : phiE alpha (q (XiBar mu nuR v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
            ≤ ∑' j, nuR j * phiE alpha (q (Xi mu nuR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
          have hq : q (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp
              = (∑' j, nuR j * ENNReal.ofReal (q (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)).toReal := by
            rw [q, show qE (XiBar mu nuR v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp
                = ∑' j, nuR j * qE (Xi mu nuR v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp
              from qE_bind nuR _ _ xp]
            congr 1
            exact tsum_congr fun j => by
              rw [show ENNReal.ofReal (q (Xi mu nuR v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)
                  = qE (Xi mu nuR v0 j h)
                      (SquareRel (fullSim (labRel Rv) h)) xp
                from ENNReal.ofReal_toReal qE_ne_top]
          rw [hq]
          exact phiE_tsum_jensen halpha (fun j => (nuR j : ℝ≥0∞))
            (fun j => q (Xi mu nuR v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
            nuR.tsum_coe (fun j => q_nonneg) (fun j => q_le_one)
        have hterm : (∑' j, nuR j * phiE alpha (q (Xi mu nuR v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp))
            = ∑' j, nuR j * (if rE (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
                else phiE alpha (q (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)) := by
          refine tsum_congr fun j => ?_
          by_cases hj : nuR j = 0
          · rw [hj, zero_mul, zero_mul]
          · rw [if_neg (hos j hj)]
        exact le_trans (mul_le_mul_right (le_of_le_of_eq hjen hterm) _)
          le_self_add
  calc PhiDres alpha (rhoS) (XiBar mu nuR v0 h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ ∑' xp, (rhoS xp
          * ∑' j, nuR j * (if rE (Xi mu nuR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
              else phiE alpha (q (Xi mu nuR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp))
        + rhoS xp
          * ((if ∃ j, nuR j ≠ 0 ∧ rE (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD alpha (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp)) := by
        rw [PhiDres]
        exact ENNReal.tsum_le_tsum hpt
    _ = (∑' xp, rhoS xp
          * ∑' j, nuR j * (if rE (Xi mu nuR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
              else phiE alpha (q (Xi mu nuR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp)))
        + ∑' xp, rhoS xp
          * ((if ∃ j, nuR j ≠ 0 ∧ rE (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD alpha (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp) :=
        ENNReal.tsum_add
    _ ≤ (∑' j, nuR j * PhiDres alpha (rhoS) (Xi mu nuR v0 j h)
            (SquareRel (fullSim (labRel Rv) h)))
        + ∑' xp, rhoS xp
          * ((if ∃ j, nuR j ≠ 0 ∧ rE (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD alpha (XiBar mu nuR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
        refine add_le_add (le_of_eq ?_) le_rfl
        rw [tsum_congr fun xp => (ENNReal.tsum_mul_left).symm,
          ENNReal.tsum_comm]
        refine tsum_congr fun j => ?_
        rw [tsum_congr fun xp => show rhoS xp
            * (nuR j * (if rE (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
                else phiE alpha (q (Xi mu nuR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)))
            = nuR j * (rhoS xp
              * (if rE (Xi mu nuR v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
                  else phiE alpha (q (Xi mu nuR v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)))
            from by ring,
          ENNReal.tsum_mul_left, PhiDres]

end GraphMarkovMatching
