/-
The per-state-pair step of the transfer ledger
(`arbitrary_offspring_matching.tex`, `sec:rows`, ordinary
outputs): each height-`(h+1)` restricted ordinary coordinate reduces to
height-`h` restricted *square* coordinates
`Φres(Ξ_k → Ξ_j; R^□)`, `Φres(Ξ_k → Ξ̄; R^□)` through the one-step
decompositions and the split lemma.  The square coordinates are then
instances of the one-cell ledger row `PhiDres_square_le` through the
product identities `Xi_of_four_le`/`Xi_three`/`Xi_of_le_two`.

* `PhiDres_bind_left`: source linearity of the restricted potential;
* `PhiDres_muM_Zlaw_succ`: forced target: the coordinate at a cell root
  `(v,k)` EQUALS the root indicator times the square coordinate
  (`eq:decomp-forced` at the potential level; incompatible roots contribute
  nothing because the restriction removes them);
* `PhiDres_muM_Tlaw_succ`: fresh target: the split bound
  `≤ φ(q(v)) + Φres(Ξ_k → Ξ̄) + 2α·φ(q(v))·Φres(Ξ_k → Ξ̄)`
  (`eq:decomp-split` plus `eq:split`, restricted);
* `PhiDres_Zlaw_Zlaw_succ` / `PhiDres_Zlaw_Tlaw_succ`: the forced-source
  instances at the root `v0`;
* `PhiDres_Tlaw_Zlaw_succ` / `PhiDres_Tlaw_Tlaw_succ`: the fresh-source
  mixtures: the root integrates to the graph potential `η = etaG` and
  the cascade mixture to `∑_k ν_k Φres(Ξ_k → ·)`.
-/
import GraphMarkovMatching.Process.Cells
import GraphMarkovMatching.Process.Contraction
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-- Source linearity of the restricted potential. -/
lemma PhiDres_bind_left {A X : Type u} (α : ℝ) (w : PMF A) (f : A → PMF X)
    (ρt : PMF X) (R : X → X → Prop) :
    PhiDres α (w.bind f) ρt R = ∑' a, w a * PhiDres α (f a) ρt R := by
  rw [PhiDres, tsum_bind_mul]
  exact tsum_congr fun a => by rw [PhiDres]

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ)
  (v0 : V)

/-- **Forced target, one cell root**: at a root `(v,k)` the restricted
coordinate toward `Z_j` is the root indicator times the restricted square
coordinate. -/
lemma PhiDres_muM_Zlaw_succ (v : V) (k j h : ℕ) :
    PhiDres α (muM (varyK μ ν v0) (v, k) (h + 1)) (Zlaw μ ν v0 j (h + 1))
        (fullSim (labRel Rv) (h + 1))
      = if Rv v v0 then
          PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h))
        else 0 := by
  rw [muM_varyK_succ μ ν v0 v k h, PhiDres, tsum_map_mul]
  by_cases hv : Rv v v0
  · rw [if_pos hv, PhiDres]
    refine tsum_congr fun xp => ?_
    congr 1
    have hrE := rE_Zlaw_succ_branch μ ν v0 Rv v k j h xp
    rw [if_pos hv] at hrE
    have hq : q (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1))
          (branch (v, k) xp)
        = q (Xi μ ν v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp := by
      rw [q, q, qE_Zlaw_succ_branch μ ν v0 Rv hv k j h xp]
    rw [hrE, hq]
  · rw [if_neg hv]
    refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
    have hrE := rE_Zlaw_succ_branch μ ν v0 Rv v k j h xp
    rw [if_neg hv] at hrE
    rw [hrE]
    simp

/-- **Fresh target, one cell root**: the split bound at a root `(v,k)`. -/
lemma PhiDres_muM_Tlaw_succ (hα : 1 ≤ α) (v : V) (k h : ℕ) :
    PhiDres α (muM (varyK μ ν v0) (v, k) (h + 1)) (Tlaw μ ν v0 (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v)
        + PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
  rw [muM_varyK_succ μ ν v0 v k h, PhiDres, tsum_map_mul]
  have hpt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi μ ν v0 k h xp
        * (if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp) = 0 then 0
            else phiE α (q (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp)))
      ≤ Xi μ ν v0 k h xp * phiE α (q μ Rv v)
        + Xi μ ν v0 k h xp
          * (if rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then 0
              else phiE α (q (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp))
        + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
            * (Xi μ ν v0 k h xp
              * (if rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp
                    = 0 then 0
                  else phiE α (q (XiBar μ ν v0 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)))) := by
    intro xp
    by_cases hres : rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
        (branch (v, k) xp) = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      have hfac := rE_Tlaw_succ_branch μ ν v0 Rv v k h xp
      rw [hfac] at hres
      obtain ⟨-, hXi⟩ := mul_ne_zero_iff.mp hres
      rw [if_neg hXi]
      calc Xi μ ν v0 k h xp
            * phiE α (q (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp))
          ≤ Xi μ ν v0 k h xp * (phiE α (q μ Rv v)
              + phiE α (q (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)
              + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
                  * phiE α (q (XiBar μ ν v0 h)
                      (SquareRel (fullSim (labRel Rv) h)) xp))) :=
            mul_le_mul_right (phiE_branch_le α Rv μ ν v0 hα v k h xp) _
        _ = Xi μ ν v0 k h xp * phiE α (q μ Rv v)
              + Xi μ ν v0 k h xp
                * phiE α (q (XiBar μ ν v0 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)
              + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
                  * (Xi μ ν v0 k h xp
                    * phiE α (q (XiBar μ ν v0 h)
                        (SquareRel (fullSim (labRel Rv) h)) xp))) := by ring
  calc ∑' xp, Xi μ ν v0 k h xp
        * (if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp) = 0 then 0
            else phiE α (q (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp)))
      ≤ ∑' xp, (Xi μ ν v0 k h xp * phiE α (q μ Rv v)
          + Xi μ ν v0 k h xp
            * (if rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp
                  = 0 then 0
                else phiE α (q (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp))
          + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
              * (Xi μ ν v0 k h xp
                * (if rE (XiBar μ ν v0 h)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
                    else phiE α (q (XiBar μ ν v0 h)
                      (SquareRel (fullSim (labRel Rv) h)) xp))))) :=
        ENNReal.tsum_le_tsum hpt
    _ = phiE α (q μ Rv v)
        + PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          PMF.tsum_coe, one_mul, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          PhiDres]

/-- The forced-forced pair step (`s = Z_k`, `t = Z_j`): an exact identity. -/
lemma PhiDres_Zlaw_Zlaw_succ (hrefl : Rv v0 v0) (k j h : ℕ) :
    PhiDres α (Zlaw μ ν v0 k (h + 1)) (Zlaw μ ν v0 j (h + 1))
        (fullSim (labRel Rv) (h + 1))
      = PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) := by
  rw [show Zlaw μ ν v0 k (h + 1)
      = muM (varyK μ ν v0) (v0, k) (h + 1) from rfl,
    PhiDres_muM_Zlaw_succ α Rv μ ν v0 v0 k j h, if_pos hrefl]

/-- The forced-fresh pair step (`s = Z_k`, `t = F`). -/
lemma PhiDres_Zlaw_Tlaw_succ (hα : 1 ≤ α) (k h : ℕ) :
    PhiDres α (Zlaw μ ν v0 k (h + 1)) (Tlaw μ ν v0 (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v0)
        + PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v0)
            * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))) :=
  PhiDres_muM_Tlaw_succ α Rv μ ν v0 hα v0 k h

/-- The fresh-forced pair step (`s = F`, `t = Z_j`): the root mass is at
most one, so the mixture of square coordinates bounds the coordinate. -/
lemma PhiDres_Tlaw_Zlaw_succ (j h : ℕ) :
    PhiDres α (Tlaw μ ν v0 (h + 1)) (Zlaw μ ν v0 j (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ ∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) := by
  rw [show Tlaw μ ν v0 (h + 1)
      = (freshQ μ ν).bind (fun s => muM (varyK μ ν v0) s (h + 1)) from rfl,
    PhiDres_bind_left]
  calc ∑' s : V × ℕ, freshQ μ ν s
        * PhiDres α (muM (varyK μ ν v0) s (h + 1)) (Zlaw μ ν v0 j (h + 1))
            (fullSim (labRel Rv) (h + 1))
      = ∑' s : V × ℕ, (μ s.1 * (if Rv s.1 v0 then 1 else 0))
          * (ν s.2 * PhiDres α (Xi μ ν v0 s.2 h) (Xi μ ν v0 j h)
              (SquareRel (fullSim (labRel Rv) h))) := by
        refine tsum_congr fun s => ?_
        obtain ⟨v, k⟩ := s
        rw [PhiDres_muM_Zlaw_succ α Rv μ ν v0 v k j h]
        by_cases hv : Rv v v0
        · rw [if_pos hv, if_pos hv]
          simp only [freshQ, prodPMF_apply]
          ring
        · rw [if_neg hv, if_neg hv]
          simp
    _ = (∑' v, μ v * (if Rv v v0 then 1 else 0))
        * ∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h)) :=
        tsum_prod_split (fun v => μ v * (if Rv v v0 then 1 else 0))
          (fun k => ν k * PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h)))
    _ ≤ 1 * ∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h)) := by
        refine mul_le_mul_left ?_ _
        calc ∑' v, μ v * (if Rv v v0 then 1 else 0)
            ≤ ∑' v, μ v * 1 := ENNReal.tsum_le_tsum fun v =>
              mul_le_mul_right (by split_ifs <;> simp) _
          _ = 1 := by rw [tsum_congr fun v => mul_one (μ v), PMF.tsum_coe]
    _ = ∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h)) := one_mul _

/-- The fresh-fresh pair step (`s = F`, `t = F`): the root integrates to
the graph potential `η`, the cascade mixture to the `ν`-average of square
coordinates, and the cross term is quadratic. -/
lemma PhiDres_Tlaw_Tlaw_succ (hα : 1 ≤ α) (h : ℕ) :
    PhiDres α (Tlaw μ ν v0 (h + 1)) (Tlaw μ ν v0 (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ etaG α Rv μ
        + (∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h)))
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * ∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
  rw [show Tlaw μ ν v0 (h + 1)
      = (freshQ μ ν).bind (fun s => muM (varyK μ ν v0) s (h + 1)) from rfl,
    PhiDres_bind_left]
  calc ∑' s : V × ℕ, freshQ μ ν s
        * PhiDres α (muM (varyK μ ν v0) s (h + 1)) (Tlaw μ ν v0 (h + 1))
            (fullSim (labRel Rv) (h + 1))
      ≤ ∑' s : V × ℕ, freshQ μ ν s
          * (phiE α (q μ Rv s.1)
            + PhiDres α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))
            + ENNReal.ofReal (2 * α)
              * (phiE α (q μ Rv s.1)
                * PhiDres α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                    (SquareRel (fullSim (labRel Rv) h)))) := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
        obtain ⟨v, k⟩ := s
        exact PhiDres_muM_Tlaw_succ α Rv μ ν v0 hα v k h
    _ = (∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1)) * ν s.2)
        + (∑' s : V × ℕ, μ s.1 * (ν s.2
            * PhiDres α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))))
        + ENNReal.ofReal (2 * α)
          * ∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1))
              * (ν s.2 * PhiDres α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h))) := by
        rw [tsum_congr fun s : V × ℕ => show freshQ μ ν s
            * (phiE α (q μ Rv s.1)
              + PhiDres α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h))
              + ENNReal.ofReal (2 * α)
                * (phiE α (q μ Rv s.1)
                  * PhiDres α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                      (SquareRel (fullSim (labRel Rv) h))))
            = (μ s.1 * phiE α (q μ Rv s.1)) * ν s.2
              + μ s.1 * (ν s.2
                * PhiDres α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                    (SquareRel (fullSim (labRel Rv) h)))
              + ENNReal.ofReal (2 * α)
                * ((μ s.1 * phiE α (q μ Rv s.1))
                  * (ν s.2 * PhiDres α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                      (SquareRel (fullSim (labRel Rv) h))))
            from by simp only [freshQ, prodPMF_apply]; ring,
          ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ = etaG α Rv μ
        + (∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h)))
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * ∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
        rw [tsum_prod_split (fun v => μ v * phiE α (q μ Rv v)) (fun k => ν k),
          tsum_prod_split (fun v => μ v)
            (fun k => ν k * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h))),
          tsum_prod_split (fun v => μ v * phiE α (q μ Rv v))
            (fun k => ν k * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h))),
          PMF.tsum_coe, PMF.tsum_coe, mul_one, one_mul, etaG, PhiD]

/-- **The fresh-target mixture** (the two-sided/one-sided split of the
cell step): the restricted square coordinate toward `Ξ̄` is bounded by the
`ν`-average of the restricted square coordinates toward the components
plus a pair-level one-sided screen, normalized by the mixture degree
itself.  Two-sided points go through the countable mixture Jensen
inequality; on a one-sided point the potential summand is at most the
inverse mixture degree. -/
lemma PhiDres_Xi_XiBar_le (hα : 1 ≤ α) (k h : ℕ) :
    PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ (∑' j, ν j * PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h)))
        + ∑' xp, Xi μ ν v0 k h xp
            * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * WresD α (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp) := by
  have hαpos : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα
  have hpt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi μ ν v0 k h xp
        * (if rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
            then 0
            else phiE α (q (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp))
      ≤ Xi μ ν v0 k h xp
          * ∑' j, ν j * (if rE (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
              else phiE α (q (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp))
        + Xi μ ν v0 k h xp
          * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
    intro xp
    by_cases hres : rE (XiBar μ ν v0 h)
        (SquareRel (fullSim (labRel Rv) h)) xp = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      by_cases hos : ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) xp = 0
      · have hb : phiE α (q (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
            ≤ WresD α (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp := by
          rw [phiE_eq_qE_mul_rpow α (SquareRel (fullSim (labRel Rv) h))
              (XiBar μ ν v0 h) hαpos xp,
            rE_rpow_neg_eq_WresD (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp hres]
          exact le_trans (mul_le_mul_left qE_le_one _)
            (le_of_eq (one_mul _))
        refine le_trans ?_ le_add_self
        calc Xi μ ν v0 k h xp * phiE α (q (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
            ≤ Xi μ ν v0 k h xp * WresD α (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp :=
              mul_le_mul_right hb _
          _ = Xi μ ν v0 k h xp
              * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0
                    then 1 else 0)
                * WresD α (XiBar μ ν v0 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp) := by
              rw [if_pos hos, one_mul]
      · push Not at hos
        have hjen : phiE α (q (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
            ≤ ∑' j, ν j * phiE α (q (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
          have hq : q (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp
              = (∑' j, ν j * ENNReal.ofReal (q (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)).toReal := by
            rw [q, show qE (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp
                = ∑' j, ν j * qE (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp
              from qE_bind ν _ _ xp]
            congr 1
            exact tsum_congr fun j => by
              rw [show ENNReal.ofReal (q (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)
                  = qE (Xi μ ν v0 j h)
                      (SquareRel (fullSim (labRel Rv) h)) xp
                from ENNReal.ofReal_toReal qE_ne_top]
          rw [hq]
          exact phiE_tsum_jensen hα (fun j => (ν j : ℝ≥0∞))
            (fun j => q (Xi μ ν v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
            ν.tsum_coe (fun j => q_nonneg) (fun j => q_le_one)
        have hterm : (∑' j, ν j * phiE α (q (Xi μ ν v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp))
            = ∑' j, ν j * (if rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
                else phiE α (q (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)) := by
          refine tsum_congr fun j => ?_
          by_cases hj : ν j = 0
          · rw [hj, zero_mul, zero_mul]
          · rw [if_neg (hos j hj)]
        exact le_trans (mul_le_mul_right (le_of_le_of_eq hjen hterm) _)
          le_self_add
  calc PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ ∑' xp, (Xi μ ν v0 k h xp
          * ∑' j, ν j * (if rE (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
              else phiE α (q (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp))
        + Xi μ ν v0 k h xp
          * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp)) := by
        rw [PhiDres]
        exact ENNReal.tsum_le_tsum hpt
    _ = (∑' xp, Xi μ ν v0 k h xp
          * ∑' j, ν j * (if rE (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
              else phiE α (q (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp)))
        + ∑' xp, Xi μ ν v0 k h xp
          * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp) :=
        ENNReal.tsum_add
    _ ≤ (∑' j, ν j * PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h)))
        + ∑' xp, Xi μ ν v0 k h xp
          * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
        refine add_le_add (le_of_eq ?_) le_rfl
        rw [tsum_congr fun xp => (ENNReal.tsum_mul_left).symm,
          ENNReal.tsum_comm]
        refine tsum_congr fun j => ?_
        rw [tsum_congr fun xp => show Xi μ ν v0 k h xp
            * (ν j * (if rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
                else phiE α (q (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)))
            = ν j * (Xi μ ν v0 k h xp
              * (if rE (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
                  else phiE α (q (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)))
            from by ring,
          ENNReal.tsum_mul_left, PhiDres]

/-- **Mixture to diagonal reserve** (`def:screen`, `u = ∅`): for a charged
source counter, the pair-level one-sided screen normalized by the mixture
degree is at most `ν_k^{-α}` times the same screen normalized by the
diagonal reserve of the source pair law.  Off the support the diagonal
tilt may be `⊤`, but there the source weight vanishes; on the support the
diagonal reserve is positive by reflexivity. -/
lemma pairScreen_mix_le_diag (hα0 : 0 ≤ α) {k : ℕ}
    (hk : (ν k : ℝ≥0∞) ≠ 0) (h : ℕ)
    (hrefl : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      SquareRel (fullSim (labRel Rv) h) xp xp)
    (ind : FullLab (V × ℕ) h × FullLab (V × ℕ) h → ℝ≥0∞) :
    ∑' xp, Xi μ ν v0 k h xp
        * (ind xp * WresD α (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ (ν k : ℝ≥0∞) ^ (-α)
        * ∑' xp, Xi μ ν v0 k h xp
            * (ind xp * (rE (Xi μ ν v0 k h)
                (SquareRel (fullSim (labRel Rv) h)) xp) ^ (-α)) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun xp => ?_
  by_cases hxp : Xi μ ν v0 k h xp = 0
  · rw [hxp, zero_mul]
    exact zero_le
  · have hdiag : rE (Xi μ ν v0 k h)
        (SquareRel (fullSim (labRel Rv) h)) xp ≠ 0 := by
      intro h0
      exact hxp (le_antisymm (h0 ▸ le_rE_of_refl (hrefl xp)) zero_le)
    have htilt : WresD α (XiBar μ ν v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp
        ≤ (ν k : ℝ≥0∞) ^ (-α)
          * (rE (Xi μ ν v0 k h)
              (SquareRel (fullSim (labRel Rv) h)) xp) ^ (-α) := by
      by_cases hres : rE (XiBar μ ν v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp = 0
      · rw [WresD, if_pos hres]
        exact zero_le
      · rw [← rE_rpow_neg_eq_WresD (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h)) xp hres,
          ← ENNReal.mul_rpow_of_ne_zero hk hdiag]
        exact rpow_neg_antitone hα0
          (mul_rE_le_rE_bind ν (fun j => Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h)) xp k)
    calc Xi μ ν v0 k h xp * (ind xp * WresD α (XiBar μ ν v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp)
        ≤ Xi μ ν v0 k h xp * (ind xp * ((ν k : ℝ≥0∞) ^ (-α)
            * (rE (Xi μ ν v0 k h)
                (SquareRel (fullSim (labRel Rv) h)) xp) ^ (-α))) := by
          exact mul_le_mul_right (mul_le_mul_right htilt _) _
      _ = (ν k : ℝ≥0∞) ^ (-α) * (Xi μ ν v0 k h xp
            * (ind xp * (rE (Xi μ ν v0 k h)
                (SquareRel (fullSim (labRel Rv) h)) xp) ^ (-α))) := by
          ring

/-- **Union bound over the dead components**: the existential one-sided
indicator of the mixture is dominated by the sum of per-component dead
indicators, for any nonnegative tilt. -/
lemma pairScreen_exists_le (k h : ℕ)
    (W : FullLab (V × ℕ) h × FullLab (V × ℕ) h → ℝ≥0∞) :
    ∑' xp, Xi μ ν v0 k h xp
        * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * W xp)
      ≤ ∑' j, ∑' xp, Xi μ ν v0 k h xp
          * ((if ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * W xp) := by
  have hpt : ∀ xp, Xi μ ν v0 k h xp
      * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
            (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
        * W xp)
      ≤ ∑' j, Xi μ ν v0 k h xp
          * ((if ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * W xp) := by
    intro xp
    by_cases hex : ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
        (SquareRel (fullSim (labRel Rv) h)) xp = 0
    · obtain ⟨j₀, hj₀⟩ := hex
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum j₀)
      rw [if_pos ⟨j₀, hj₀⟩, if_pos hj₀]
    · rw [if_neg hex, zero_mul, mul_zero]
      exact zero_le
  exact le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ENNReal.tsum_comm)

/-- **The one-sided tilt mass in diagonal form**: for a charged source
counter, the one-sided pair screen of the fresh-target mixture is at most
`ν_k^{-α}` times the sum over components of the diagonal-reserve pair
screens.  Each summand with a concrete product component then factorizes
through `diagPairScreen_le`. -/
lemma oneSidedScreen_le_diag (hα0 : 0 ≤ α) {k : ℕ}
    (hk : (ν k : ℝ≥0∞) ≠ 0) (h : ℕ)
    (hrefl : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      SquareRel (fullSim (labRel Rv) h) xp xp) :
    ∑' xp, Xi μ ν v0 k h xp
        * ((if ∃ j, ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ (ν k : ℝ≥0∞) ^ (-α)
        * ∑' j, ∑' xp, Xi μ ν v0 k h xp
            * ((if ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (rE (Xi μ ν v0 k h)
                  (SquareRel (fullSim (labRel Rv) h)) xp) ^ (-α)) := by
  refine le_trans (pairScreen_exists_le Rv μ ν v0 k h
    (WresD α (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)))) ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun j => ?_
  exact pairScreen_mix_le_diag α Rv μ ν v0 hα0 hk h hrefl
    (fun xp => if ν j ≠ 0 ∧ rE (Xi μ ν v0 j h)
      (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)

/-! ### The base case -/

/-- At height zero the fresh bad degree is the label bad degree: the
counters integrate out. -/
lemma qE_Tlaw_zero (v : V) (k : ℕ) :
    qE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf (v, k)) = qE μ Rv v := by
  rw [show Tlaw μ ν v0 0
      = (freshQ μ ν).bind (fun s => muM (varyK μ ν v0) s 0) from rfl,
    qE_bind]
  calc ∑' s : V × ℕ, freshQ μ ν s
        * qE (muM (varyK μ ν v0) s 0) (fullSim (labRel Rv) 0) (leaf (v, k))
      = ∑' s : V × ℕ, (if Rv v s.1 then 0 else μ s.1) * ν s.2 := by
        refine tsum_congr fun s => ?_
        rw [show muM (varyK μ ν v0) s 0 = PMF.pure (leaf s) from rfl,
          qE_pure, badInd]
        by_cases hb : fullSim (labRel Rv) 0 (leaf (v, k)) (leaf s)
        · rw [if_pos hb,
            if_pos (show Rv v s.1 from
              (fullSim_leaf (labRel Rv) (v, k) s).mp hb),
            mul_zero, zero_mul]
        · rw [if_neg hb,
            if_neg (show ¬ Rv v s.1 from fun hr =>
              hb ((fullSim_leaf (labRel Rv) (v, k) s).mpr hr)),
            mul_one, show freshQ μ ν s = μ s.1 * ν s.2 from rfl]
    _ = (∑' w, if Rv v w then 0 else μ w) * ∑' l, (ν l : ℝ≥0∞) :=
        tsum_prod_split (fun w => if Rv v w then 0 else μ w)
          (fun l => (ν l : ℝ≥0∞))
    _ = qE μ Rv v := by rw [ν.tsum_coe, mul_one]; rfl

/-- Dropping a conjunct from an indicator. -/
lemma indicator_and_le {p q : Prop} :
    (if p ∧ q then (1 : ℝ≥0∞) else 0) ≤ if q then 1 else 0 := by
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd h1.2 h2
  · exact zero_le
  · exact le_rfl

/-- The good-degree form of the height-zero fresh identity. -/
lemma rE_Tlaw_zero (v : V) (k : ℕ) :
    rE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf (v, k)) = rE μ Rv v := by
  have h1 := rE_add_qE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf (v, k))
  have h2 := rE_add_qE μ Rv v
  rw [qE_Tlaw_zero Rv μ ν v0 v k] at h1
  calc rE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf (v, k))
      = 1 - qE μ Rv v := ENNReal.eq_sub_of_add_eq qE_ne_top h1
    _ = rE μ Rv v := (ENNReal.eq_sub_of_add_eq qE_ne_top h2).symm

/-- The forced-forced base coordinates vanish: compatible roots start at
zero potential. -/
lemma PhiDres_Zlaw_Zlaw_zero (hrefl : Rv v0 v0) (k j : ℕ) :
    PhiDres α (Zlaw μ ν v0 k 0) (Zlaw μ ν v0 j 0)
      (fullSim (labRel Rv) 0) = 0 := by
  rw [show Zlaw μ ν v0 k 0 = PMF.pure (leaf (v0, k)) from rfl, PhiDres,
    tsum_pure_mul]
  have hq : qE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
      (leaf (v0, k)) = 0 := by
    rw [show Zlaw μ ν v0 j 0 = PMF.pure (leaf (v0, j)) from rfl,
      qE_pure, badInd,
      if_pos ((fullSim_leaf (labRel Rv) (v0, k) (v0, j)).mpr hrefl)]
  have hr : rE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
      (leaf (v0, k)) ≠ 0 := by
    intro h0
    have hone := rE_add_qE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
      (leaf (v0, k))
    rw [h0, hq, zero_add] at hone
    exact zero_ne_one hone
  rw [if_neg hr, q, hq]
  simp

/-- The fresh-fresh base coordinate is at most the graph potential. -/
lemma PhiDres_Tlaw_Tlaw_zero_le :
    PhiDres α (Tlaw μ ν v0 0) (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
      ≤ etaG α Rv μ := by
  rw [show Tlaw μ ν v0 0
      = (freshQ μ ν).bind (fun s => muM (varyK μ ν v0) s 0) from rfl,
    PhiDres_bind_left]
  calc ∑' s : V × ℕ, freshQ μ ν s
        * PhiDres α (muM (varyK μ ν v0) s 0) (Tlaw μ ν v0 0)
            (fullSim (labRel Rv) 0)
      ≤ ∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1)) * ν s.2 := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        obtain ⟨v, k⟩ := s
        have hP : PhiDres α (muM (varyK μ ν v0) (v, k) 0) (Tlaw μ ν v0 0)
            (fullSim (labRel Rv) 0) ≤ phiE α (q μ Rv v) := by
          rw [show muM (varyK μ ν v0) (v, k) 0
              = PMF.pure (leaf (v, k)) from rfl, PhiDres, tsum_pure_mul]
          have hq : q (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
              (leaf (v, k)) = q μ Rv v := by
            rw [q, q, qE_Tlaw_zero Rv μ ν v0 v k]
          by_cases hr : rE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
              (leaf (v, k)) = 0
          · rw [if_pos hr]
            exact zero_le
          · rw [if_neg hr, hq]
        calc freshQ μ ν (v, k)
              * PhiDres α (muM (varyK μ ν v0) (v, k) 0) (Tlaw μ ν v0 0)
                  (fullSim (labRel Rv) 0)
            ≤ freshQ μ ν (v, k) * phiE α (q μ Rv v) :=
              mul_le_mul_right hP _
          _ = (μ v * phiE α (q μ Rv v)) * ν k := by
              rw [show freshQ μ ν (v, k) = μ v * ν k from rfl]
              ring
    _ = etaG α Rv μ := by
        rw [tsum_prod_split (fun v => μ v * phiE α (q μ Rv v))
          (fun l => (ν l : ℝ≥0∞)), ν.tsum_coe, mul_one, etaG, PhiD]

end GraphMarkovMatching
