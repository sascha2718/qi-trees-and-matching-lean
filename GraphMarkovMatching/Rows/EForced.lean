/-
The forced-source screen rows of the general-ν transfer lemma
(`arbitrary_offspring_matching.tex`, `thm:screen-rows` in `sec:rows`,
at a forced source cell `Z_i`): the height-`(h+1)` interpreted
screen descends through the branch point at the root `v0` to the member
pairs of its zero list, the Hall factorization routes the zero
requirements through the two cascade children, and the normalization
converts by cases.

* `interpScreen_forced_step`: the one-step descent: the interpreted
  screen at `Z_i` equals the pair-level dead-member mass under the
  descended normalization;
* `eRowZ_none`: the unit normalization: two full-list successor screens
  plus a quadratic product of singleton charges;
* `eRowZ_forced`: a forced normalization `Z_m`: the tilt converts to
  the square weight of `Ξ_m`, and each order of the survivor split contributes
  a successor screen, a moment charge, and a quadratic term;
* `eRowZ_fresh`: the fresh normalization `F`: the tilt converts to the
  mixture weight times `RT · Tν` (the root factor and the charged
  tilt sum), and each charged counter contributes one forced-normalization
  cell.
-/
import GraphMarkovMatching.Rows.ECore

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (ν : PMF ℕ) (v0 : V)

/-! ### Bridges between successor screens and screen values -/

/-- A successor screen with unit normalization is the full-list screen
of the interpreted successor zero list. -/
private lemma interpScreen_zsucc_none (S : Finset ℕ) (h : ℕ) (c' : Tgt)
    (z : Finset Tgt) :
    interpScreen α Rv μ ν v0 h ⟨c', zsucc S z, none⟩
      = screenE (interpT μ ν v0 h c') (fullSim (labRel Rv) h)
          (((zsucc S z).toList).map (interpT μ ν v0 h))
          (fun _ => (1 : ℝ≥0∞)) := rfl

/-- A successor screen with a forced normalization is the full-list
screen tilted by the restricted inverse degree of the normalization. -/
private lemma interpScreen_zsucc_some (S : Finset ℕ) (h : ℕ) (c' w' : Tgt)
    (z : Finset Tgt) :
    interpScreen α Rv μ ν v0 h ⟨c', zsucc S z, some w'⟩
      = screenE (interpT μ ν v0 h c') (fullSim (labRel Rv) h)
          (((zsucc S z).toList).map (interpT μ ν v0 h))
          (WresD α (interpT μ ν v0 h w') (fullSim (labRel Rv) h)) := rfl

/-! ### The one-step descent -/

/-- **The one-step descent at a forced source** (`sec:rows`,
`thm:screen-rows`): the height-`(h+1)` interpreted screen at the cell `Z_i`
equals the `Ξ_i`-mass of the dead event of the member pairs, tilted by
the normalization descended through the branch point. -/
lemma interpScreen_forced_step (S : Finset ℕ)
    (hSsupp : ∀ j : ℕ, (ν j : ℝ≥0∞) ≠ 0 ↔ j ∈ S) (hrefl : Rv v0 v0)
    (hpos : rE μ Rv v0 ≠ 0) (i : ℕ) (z : Finset Tgt)
    (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) (u : Option Tgt) (h : ℕ) :
    interpScreen α Rv μ ν v0 (h + 1) ⟨Tgt.Z i, z, u⟩
      = ∑' xp, Xi μ ν v0 i h xp
          * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * interpNorm α Rv μ ν v0 (h + 1) u (branch (v0, i) xp)) := by
  have hstep : interpScreen α Rv μ ν v0 (h + 1) ⟨Tgt.Z i, z, u⟩
      = ∑' x, muM (varyK μ ν v0) (v0, i) (h + 1) x
          * (screenInd (fullSim (labRel Rv) (h + 1))
              ((z.toList).map (interpT μ ν v0 (h + 1))) x
            * interpNorm α Rv μ ν v0 (h + 1) u x) := by
    rw [interpScreen, screenE]
    exact tsum_congr fun x => mul_assoc _ _ _
  have hmap : (∑' x, muM (varyK μ ν v0) (v0, i) (h + 1) x
        * (screenInd (fullSim (labRel Rv) (h + 1))
            ((z.toList).map (interpT μ ν v0 (h + 1))) x
          * interpNorm α Rv μ ν v0 (h + 1) u x))
      = ∑' xp, Xi μ ν v0 i h xp
          * (screenInd (fullSim (labRel Rv) (h + 1))
              ((z.toList).map (interpT μ ν v0 (h + 1))) (branch (v0, i) xp)
            * interpNorm α Rv μ ν v0 (h + 1) u (branch (v0, i) xp)) := by
    rw [muM_varyK_succ μ ν v0 v0 i h]
    exact tsum_map_mul _ _ _
  rw [hstep, hmap]
  refine tsum_congr fun xp => ?_
  rw [screenInd, if_congr
    (memInd_branch_iff μ ν v0 Rv S hSsupp hrefl hpos i h z hzf xp) rfl rfl]

/-! ### The unit-normalization row -/

/-- **The forced-source screen row, unit normalization**
(`sec:rows`, `thm:screen-rows`, row `⟨Z_i; z ↛ ⋄⟩`): the descended dead
event factorizes through the Hall routing into two full-list
successor screens and a quadratic product of singleton charges. -/
lemma eRowZ_none (S : Finset ℕ)
    (hSsupp : ∀ j : ℕ, (ν j : ℝ≥0∞) ≠ 0 ↔ j ∈ S) (hrefl : Rv v0 v0)
    (hpos : rE μ Rv v0 ≠ 0) (i : ℕ) (z : Finset Tgt)
    (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) (_hz : z.Nonempty) (h : ℕ)
    (E' : ℝ≥0∞)
    (hscrS : ∀ t' ∈ zsucc S z, ∀ c' ∈ gpair i,
      screenE (interpT μ ν v0 h c') (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t'] (fun _ => (1 : ℝ≥0∞)) ≤ E') :
    interpScreen α Rv μ ν v0 (h + 1) ⟨Tgt.Z i, z, none⟩
      ≤ 2 * (∑ sc' ∈ screenSucc S ⟨Tgt.Z i, z, none⟩,
            interpScreen α Rv μ ν v0 h sc')
        + ((zsucc S z).card * E') * ((zsucc S z).card * E') := by
  have hLHS : interpScreen α Rv μ ν v0 (h + 1) ⟨Tgt.Z i, z, none⟩
      = ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
          prodPMF (interpT μ ν v0 h (gcomp0 i))
            (interpT μ ν v0 h (gcomp1 i)) xp
          * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * ((fun _ => (1 : ℝ≥0∞)) xp.1
              * (fun _ => (1 : ℝ≥0∞)) xp.2)) := by
    rw [interpScreen_forced_step α Rv μ ν v0 S hSsupp hrefl hpos i z hzf
      none h, ← Xi_eq_prod μ ν v0 i h]
    refine tsum_congr fun xp => ?_
    show Xi μ ν v0 i h xp
        * ((if ∀ p ∈ memPairs μ ν v0 S h z,
              rE (prodPMF p.1 p.2)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0
            then (1 : ℝ≥0∞) else 0) * (1 : ℝ≥0∞))
      = Xi μ ν v0 i h xp
        * ((if ∀ p ∈ memPairs μ ν v0 S h z,
              rE (prodPMF p.1 p.2)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0
            then (1 : ℝ≥0∞) else 0) * ((1 : ℝ≥0∞) * (1 : ℝ≥0∞)))
    rw [one_mul]
  have hMF := hallFactorize (interpT μ ν v0 h (gcomp0 i))
    (interpT μ ν v0 h (gcomp1 i)) (fullSim (labRel Rv) h)
    (memPairs μ ν v0 S h z)
    (((zsucc S z).toList).map (interpT μ ν v0 h))
    (memPairs_mem μ ν v0 S h z) (memPairs_cov μ ν v0 S h z)
    (fun _ => (1 : ℝ≥0∞)) (fun _ => (1 : ℝ≥0∞))
  refine le_trans (le_of_eq hLHS) (le_trans hMF ?_)
  have hmass0 : (∑' x, interpT μ ν v0 h (gcomp0 i) x
      * (fun _ => (1 : ℝ≥0∞)) x) = 1 := by
    simp only [mul_one]
    exact (interpT μ ν v0 h (gcomp0 i)).tsum_coe
  have hmass1 : (∑' x, interpT μ ν v0 h (gcomp1 i) x
      * (fun _ => (1 : ℝ≥0∞)) x) = 1 := by
    simp only [mul_one]
    exact (interpT μ ν v0 h (gcomp1 i)).tsum_coe
  have h1 : screenE (interpT μ ν v0 h (gcomp0 i)) (fullSim (labRel Rv) h)
      (((zsucc S z).toList).map (interpT μ ν v0 h))
      (fun _ => (1 : ℝ≥0∞))
      * (∑' x, interpT μ ν v0 h (gcomp1 i) x * (fun _ => (1 : ℝ≥0∞)) x)
      ≤ ∑ sc' ∈ screenSucc S (⟨Tgt.Z i, z, none⟩ : GScreen),
          interpScreen α Rv μ ν v0 h sc' := by
    rw [hmass1, mul_one,
      ← interpScreen_zsucc_none α Rv μ ν v0 S h (gcomp0 i) z]
    exact interp_le_succ_sum μ ν v0 Rv α h
      (mem_screenSucc_mk (gcomp_mem_gpair i).1 (none_mem_normSucc S))
  have h2 : (∑' x, interpT μ ν v0 h (gcomp0 i) x
      * (fun _ => (1 : ℝ≥0∞)) x)
      * screenE (interpT μ ν v0 h (gcomp1 i)) (fullSim (labRel Rv) h)
        (((zsucc S z).toList).map (interpT μ ν v0 h))
        (fun _ => (1 : ℝ≥0∞))
      ≤ ∑ sc' ∈ screenSucc S (⟨Tgt.Z i, z, none⟩ : GScreen),
          interpScreen α Rv μ ν v0 h sc' := by
    rw [hmass0, one_mul,
      ← interpScreen_zsucc_none α Rv μ ν v0 S h (gcomp1 i) z]
    exact interp_le_succ_sum μ ν v0 Rv α h
      (mem_screenSucc_mk (gcomp_mem_gpair i).2 (none_mem_normSucc S))
  have hsum0 : ((((zsucc S z).toList).map (interpT μ ν v0 h)).map
      fun ρ => screenE (interpT μ ν v0 h (gcomp0 i))
        (fullSim (labRel Rv) h) [ρ] (fun _ => (1 : ℝ≥0∞))).sum
      ≤ (zsucc S z).card * E' := by
    refine le_trans (list_map_sum_le _ _ E' fun ρ hρ => ?_) (le_of_eq ?_)
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hρ
      exact hscrS t' (Finset.mem_toList.mp ht') (gcomp0 i)
        (gcomp_mem_gpair i).1
    · rw [zsucc_map_length μ ν v0 S h z]
  have hsum1 : ((((zsucc S z).toList).map (interpT μ ν v0 h)).map
      fun ρ' => screenE (interpT μ ν v0 h (gcomp1 i))
        (fullSim (labRel Rv) h) [ρ'] (fun _ => (1 : ℝ≥0∞))).sum
      ≤ (zsucc S z).card * E' := by
    refine le_trans (list_map_sum_le _ _ E' fun ρ hρ => ?_) (le_of_eq ?_)
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hρ
      exact hscrS t' (Finset.mem_toList.mp ht') (gcomp1 i)
        (gcomp_mem_gpair i).2
    · rw [zsucc_map_length μ ν v0 S h z]
  refine le_trans (add_le_add (add_le_add h1 h2) (mul_le_mul' hsum0 hsum1))
    (le_of_eq ?_)
  rw [two_mul]

/-! ### The common tilted cell -/

/-- The common tilted cell of the forced and fresh normalization rows:
the descended dead-member mass tilted by the square weight of `Ξ_m`
splits over the survivor orders, and each order factorizes through the
Hall routing into a tilted successor screen (`≤ Eplus`, and `≤ E'` under
the moment factor), a moment charge, and a quadratic product of
singleton charges. -/
private lemma eRowZ_W_cell (hα : 1 ≤ α) (S : Finset ℕ) (i m h : ℕ)
    (z : Finset Tgt) (M E' Eplus : ℝ≥0∞)
    (hMom : ∀ c' ∈ gpair i, ∀ w' ∈ gpair m,
      interpPhi α Rv μ ν v0 h (c', w') ≤ M)
    (hscrS : ∀ t' ∈ zsucc S z, ∀ c' ∈ gpair i, ∀ w' ∈ gpair m,
      screenE (interpT μ ν v0 h c') (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t']
        (WresD α (interpT μ ν v0 h w') (fullSim (labRel Rv) h)) ≤ E')
    (hEplus : ∀ c' ∈ gpair i, ∀ w' ∈ gpair m,
      interpScreen α Rv μ ν v0 h ⟨c', zsucc S z, some w'⟩ ≤ Eplus)
    (hEplusE : ∀ c' ∈ gpair i, ∀ w' ∈ gpair m,
      interpScreen α Rv μ ν v0 h ⟨c', zsucc S z, some w'⟩ ≤ E') :
    ∑' xp, Xi μ ν v0 i h xp
        * ((if ∀ p ∈ memPairs μ ν v0 S h z,
              rE (prodPMF p.1 p.2)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0
            then (1 : ℝ≥0∞) else 0)
          * WresD α (Xi μ ν v0 m h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ 4 * Eplus + 4 * (ENNReal.ofReal α * M * E')
        + 2 * (((zsucc S z).card * E') * ((zsucc S z).card * E')) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hsplit : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi μ ν v0 i h xp
        * ((if ∀ p ∈ memPairs μ ν v0 S h z,
              rE (prodPMF p.1 p.2)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0
            then (1 : ℝ≥0∞) else 0)
          * WresD α (Xi μ ν v0 m h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ Xi μ ν v0 i h xp
          * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * (WresD α (interpT μ ν v0 h (gcomp0 m))
                (fullSim (labRel Rv) h) xp.1
              * WresD α (interpT μ ν v0 h (gcomp1 m))
                  (fullSim (labRel Rv) h) xp.2))
        + Xi μ ν v0 i h xp
          * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * (WresD α (interpT μ ν v0 h (gcomp1 m))
                (fullSim (labRel Rv) h) xp.1
              * WresD α (interpT μ ν v0 h (gcomp0 m))
                  (fullSim (labRel Rv) h) xp.2)) := by
    intro xp
    have hW : WresD α (Xi μ ν v0 m h)
        (SquareRel (fullSim (labRel Rv) h)) xp
        ≤ WresD α (interpT μ ν v0 h (gcomp0 m))
            (fullSim (labRel Rv) h) xp.1
            * WresD α (interpT μ ν v0 h (gcomp1 m))
                (fullSim (labRel Rv) h) xp.2
          + WresD α (interpT μ ν v0 h (gcomp1 m))
              (fullSim (labRel Rv) h) xp.1
            * WresD α (interpT μ ν v0 h (gcomp0 m))
                (fullSim (labRel Rv) h) xp.2 := by
      rw [Xi_eq_prod μ ν v0 m h]
      exact WresD_square_le_sum hα0 _ _ _ xp
    refine le_trans (mul_le_mul_right (mul_le_mul_right hW _) _)
      (le_of_eq ?_)
    ring
  refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
  rw [ENNReal.tsum_add]
  have horder : ∀ wa ∈ gpair m, ∀ wb ∈ gpair m,
      (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ ν v0 i h xp
          * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * (WresD α (interpT μ ν v0 h wa)
                (fullSim (labRel Rv) h) xp.1
              * WresD α (interpT μ ν v0 h wb)
                  (fullSim (labRel Rv) h) xp.2)))
      ≤ (Eplus + ENNReal.ofReal α * M * E')
        + (Eplus + ENNReal.ofReal α * M * E')
        + ((zsucc S z).card * E') * ((zsucc S z).card * E') := by
    intro wa hwa wb hwb
    have hMF := hallFactorize (interpT μ ν v0 h (gcomp0 i))
      (interpT μ ν v0 h (gcomp1 i)) (fullSim (labRel Rv) h)
      (memPairs μ ν v0 S h z)
      (((zsucc S z).toList).map (interpT μ ν v0 h))
      (memPairs_mem μ ν v0 S h z) (memPairs_cov μ ν v0 S h z)
      (WresD α (interpT μ ν v0 h wa) (fullSim (labRel Rv) h))
      (WresD α (interpT μ ν v0 h wb) (fullSim (labRel Rv) h))
    refine le_trans (le_of_eq (tsum_congr fun xp => by
      rw [Xi_eq_prod μ ν v0 i h])) (le_trans hMF ?_)
    have hmomW : ∀ c' ∈ gpair i, ∀ w' ∈ gpair m,
        (∑' x, interpT μ ν v0 h c' x
          * WresD α (interpT μ ν v0 h w') (fullSim (labRel Rv) h) x)
        ≤ 1 + ENNReal.ofReal α * M := fun c' hc' w' hw' =>
      le_trans (tsum_WresD_le hα _ _ _)
        (add_le_add le_rfl (mul_le_mul_right (hMom c' hc' w' hw') _))
    have hout1 : screenE (interpT μ ν v0 h (gcomp0 i))
        (fullSim (labRel Rv) h)
        (((zsucc S z).toList).map (interpT μ ν v0 h))
        (WresD α (interpT μ ν v0 h wa) (fullSim (labRel Rv) h))
        * (∑' x, interpT μ ν v0 h (gcomp1 i) x
            * WresD α (interpT μ ν v0 h wb) (fullSim (labRel Rv) h) x)
        ≤ Eplus + ENNReal.ofReal α * M * E' := by
      rw [← interpScreen_zsucc_some α Rv μ ν v0 S h (gcomp0 i) wa z]
      calc interpScreen α Rv μ ν v0 h ⟨gcomp0 i, zsucc S z, some wa⟩
          * (∑' x, interpT μ ν v0 h (gcomp1 i) x
              * WresD α (interpT μ ν v0 h wb) (fullSim (labRel Rv) h) x)
          ≤ interpScreen α Rv μ ν v0 h ⟨gcomp0 i, zsucc S z, some wa⟩
            * (1 + ENNReal.ofReal α * M) :=
            mul_le_mul_right
              (hmomW (gcomp1 i) (gcomp_mem_gpair i).2 wb hwb) _
        _ = interpScreen α Rv μ ν v0 h ⟨gcomp0 i, zsucc S z, some wa⟩
            + ENNReal.ofReal α * M
              * interpScreen α Rv μ ν v0 h
                  ⟨gcomp0 i, zsucc S z, some wa⟩ := by ring
        _ ≤ Eplus + ENNReal.ofReal α * M * E' := by
            exact add_le_add (hEplus (gcomp0 i) (gcomp_mem_gpair i).1 wa hwa)
              (mul_le_mul_right
                (hEplusE (gcomp0 i) (gcomp_mem_gpair i).1 wa hwa) _)
    have hout2 : (∑' x, interpT μ ν v0 h (gcomp0 i) x
          * WresD α (interpT μ ν v0 h wa) (fullSim (labRel Rv) h) x)
        * screenE (interpT μ ν v0 h (gcomp1 i)) (fullSim (labRel Rv) h)
          (((zsucc S z).toList).map (interpT μ ν v0 h))
          (WresD α (interpT μ ν v0 h wb) (fullSim (labRel Rv) h))
        ≤ Eplus + ENNReal.ofReal α * M * E' := by
      rw [← interpScreen_zsucc_some α Rv μ ν v0 S h (gcomp1 i) wb z]
      calc (∑' x, interpT μ ν v0 h (gcomp0 i) x
            * WresD α (interpT μ ν v0 h wa) (fullSim (labRel Rv) h) x)
          * interpScreen α Rv μ ν v0 h ⟨gcomp1 i, zsucc S z, some wb⟩
          ≤ (1 + ENNReal.ofReal α * M)
            * interpScreen α Rv μ ν v0 h ⟨gcomp1 i, zsucc S z, some wb⟩ :=
            mul_le_mul_left
              (hmomW (gcomp0 i) (gcomp_mem_gpair i).1 wa hwa) _
        _ = interpScreen α Rv μ ν v0 h ⟨gcomp1 i, zsucc S z, some wb⟩
            + ENNReal.ofReal α * M
              * interpScreen α Rv μ ν v0 h
                  ⟨gcomp1 i, zsucc S z, some wb⟩ := by ring
        _ ≤ Eplus + ENNReal.ofReal α * M * E' := by
            exact add_le_add (hEplus (gcomp1 i) (gcomp_mem_gpair i).2 wb hwb)
              (mul_le_mul_right
                (hEplusE (gcomp1 i) (gcomp_mem_gpair i).2 wb hwb) _)
    have hsum0 : ((((zsucc S z).toList).map (interpT μ ν v0 h)).map
        fun ρ => screenE (interpT μ ν v0 h (gcomp0 i))
          (fullSim (labRel Rv) h) [ρ]
          (WresD α (interpT μ ν v0 h wa) (fullSim (labRel Rv) h))).sum
        ≤ (zsucc S z).card * E' := by
      refine le_trans (list_map_sum_le _ _ E' fun ρ hρ => ?_)
        (le_of_eq ?_)
      · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hρ
        exact hscrS t' (Finset.mem_toList.mp ht') (gcomp0 i)
          (gcomp_mem_gpair i).1 wa hwa
      · rw [zsucc_map_length μ ν v0 S h z]
    have hsum1 : ((((zsucc S z).toList).map (interpT μ ν v0 h)).map
        fun ρ' => screenE (interpT μ ν v0 h (gcomp1 i))
          (fullSim (labRel Rv) h) [ρ']
          (WresD α (interpT μ ν v0 h wb) (fullSim (labRel Rv) h))).sum
        ≤ (zsucc S z).card * E' := by
      refine le_trans (list_map_sum_le _ _ E' fun ρ hρ => ?_)
        (le_of_eq ?_)
      · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hρ
        exact hscrS t' (Finset.mem_toList.mp ht') (gcomp1 i)
          (gcomp_mem_gpair i).2 wb hwb
      · rw [zsucc_map_length μ ν v0 S h z]
    exact add_le_add (add_le_add hout1 hout2) (mul_le_mul' hsum0 hsum1)
  refine le_trans (add_le_add
    (horder (gcomp0 m) (gcomp_mem_gpair m).1 (gcomp1 m)
      (gcomp_mem_gpair m).2)
    (horder (gcomp1 m) (gcomp_mem_gpair m).2 (gcomp0 m)
      (gcomp_mem_gpair m).1))
    (le_of_eq ?_)
  ring

/-! ### The forced-normalization row -/

/-- **The forced-source screen row, forced normalization**
(`sec:rows`, `thm:screen-rows`, row `⟨Z_i; z ↛ Z_m⟩`): the tilt converts
across the branch point to the square weight of `Ξ_m`, and the common
tilted cell contributes four successor screens, four moment charges, and two
quadratic terms. -/
lemma eRowZ_forced (hα : 1 ≤ α) (S : Finset ℕ)
    (hSsupp : ∀ j : ℕ, (ν j : ℝ≥0∞) ≠ 0 ↔ j ∈ S) (hrefl : Rv v0 v0)
    (hpos : rE μ Rv v0 ≠ 0) (i : ℕ) (z : Finset Tgt)
    (hzf : ∀ t ∈ z, ∀ m', t ≠ Tgt.Fk m') (_hz : z.Nonempty) (m : ℕ)
    (h : ℕ) (M E' : ℝ≥0∞)
    (hMom : ∀ c' ∈ gpair i, ∀ w' ∈ gpair m,
      interpPhi α Rv μ ν v0 h (c', w') ≤ M)
    (hscrS : ∀ t' ∈ zsucc S z, ∀ c' ∈ gpair i, ∀ w' ∈ gpair m,
      screenE (interpT μ ν v0 h c') (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t']
        (WresD α (interpT μ ν v0 h w') (fullSim (labRel Rv) h)) ≤ E')
    (hE : ∀ sc' ∈ screenSucc S ⟨Tgt.Z i, z, some (Tgt.Z m)⟩,
      interpScreen α Rv μ ν v0 h sc' ≤ E') :
    interpScreen α Rv μ ν v0 (h + 1) ⟨Tgt.Z i, z, some (Tgt.Z m)⟩
      ≤ 4 * (∑ sc' ∈ screenSucc S ⟨Tgt.Z i, z, some (Tgt.Z m)⟩,
            interpScreen α Rv μ ν v0 h sc')
        + 4 * (ENNReal.ofReal α * M * E')
        + 2 * (((zsucc S z).card * E') * ((zsucc S z).card * E')) := by
  have hdesc : interpScreen α Rv μ ν v0 (h + 1) ⟨Tgt.Z i, z, some (Tgt.Z m)⟩
      = ∑' xp, Xi μ ν v0 i h xp
          * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * WresD α (Xi μ ν v0 m h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
    rw [interpScreen_forced_step α Rv μ ν v0 S hSsupp hrefl hpos i z hzf
      (some (Tgt.Z m)) h]
    refine tsum_congr fun xp => ?_
    have h1 := WresD_Zlaw_succ_branch α Rv μ ν v0 v0 m i h xp
    rw [if_pos hrefl] at h1
    rw [show interpNorm α Rv μ ν v0 (h + 1) (some (Tgt.Z m))
        (branch (v0, i) xp)
        = WresD α (Zlaw μ ν v0 m (h + 1)) (fullSim (labRel Rv) (h + 1))
            (branch (v0, i) xp) from rfl, h1]
  rw [hdesc]
  exact eRowZ_W_cell α Rv μ ν v0 hα S i m h z M E'
    (∑ sc' ∈ screenSucc S ⟨Tgt.Z i, z, some (Tgt.Z m)⟩,
      interpScreen α Rv μ ν v0 h sc')
    hMom hscrS
    (fun c' hc' w' hw' => interp_le_succ_sum μ ν v0 Rv α h
      (mem_screenSucc_mk hc' (some_mem_normSucc hw')))
    (fun c' hc' w' hw' => hE _
      (mem_screenSucc_mk hc' (some_mem_normSucc hw')))

/-! ### The fresh-normalization row -/

/-- Exchange of a charged tilt sum against a weighted bound: the
weighted, indicated form of the pointwise mixture tilt bound. -/
private lemma tilt_exchange (w c W : ℝ≥0∞) (g : ℕ → ℝ≥0∞)
    (hW : W ≤ ∑' j, (if (ν j : ℝ≥0∞) = 0 then 0
        else (ν j : ℝ≥0∞) ^ (-α) * g j)) :
    w * (c * W)
      ≤ ∑' j, (if (ν j : ℝ≥0∞) = 0 then 0
          else (ν j : ℝ≥0∞) ^ (-α) * (w * (c * g j))) := by
  calc w * (c * W)
      ≤ w * (c * ∑' j, (if (ν j : ℝ≥0∞) = 0 then 0
          else (ν j : ℝ≥0∞) ^ (-α) * g j)) :=
        mul_le_mul_right (mul_le_mul_right hW _) _
    _ = ∑' j, w * (c * (if (ν j : ℝ≥0∞) = 0 then 0
          else (ν j : ℝ≥0∞) ^ (-α) * g j)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ = ∑' j, (if (ν j : ℝ≥0∞) = 0 then 0
          else (ν j : ℝ≥0∞) ^ (-α) * (w * (c * g j))) :=
        tsum_congr fun j => by
          by_cases hj0 : (ν j : ℝ≥0∞) = 0
          · rw [if_pos hj0, if_pos hj0, mul_zero, mul_zero]
          · rw [if_neg hj0, if_neg hj0]; ring

/-- **The forced-source screen row, fresh normalization**
(`sec:rows`, `thm:screen-rows`, row `⟨Z_i; z ↛ F⟩`): the tilt converts
across the branch point to the root factor times the mixture weight,
the mixture weight converts pointwise into charged component weights
weighted by `ν_j^{-α}`, and each charged counter contributes one common tilted
cell, so the row contributes `RT · Tν` times the forced-normalization
output. -/
lemma eRowZ_fresh (hα : 1 ≤ α) (S : Finset ℕ)
    (hSsupp : ∀ j : ℕ, (ν j : ℝ≥0∞) ≠ 0 ↔ j ∈ S) (hrefl : Rv v0 v0)
    (hpos : rE μ Rv v0 ≠ 0) (i : ℕ) (z : Finset Tgt)
    (hzf : ∀ t ∈ z, ∀ m', t ≠ Tgt.Fk m') (_hz : z.Nonempty) (h : ℕ)
    (M E' Tν RT : ℝ≥0∞)
    (hRT : (rE μ Rv v0) ^ (-α) ≤ RT)
    (hTν : (∑' j, if (ν j : ℝ≥0∞) = 0 then 0
        else (ν j : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hMom : ∀ j ∈ S, ∀ c' ∈ gpair i, ∀ w' ∈ gpair j,
      interpPhi α Rv μ ν v0 h (c', w') ≤ M)
    (hscrS : ∀ j ∈ S, ∀ t' ∈ zsucc S z, ∀ c' ∈ gpair i, ∀ w' ∈ gpair j,
      screenE (interpT μ ν v0 h c') (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t']
        (WresD α (interpT μ ν v0 h w') (fullSim (labRel Rv) h)) ≤ E')
    (hE : ∀ sc' ∈ screenSucc S ⟨Tgt.Z i, z, some Tgt.F⟩,
      interpScreen α Rv μ ν v0 h sc' ≤ E') :
    interpScreen α Rv μ ν v0 (h + 1) ⟨Tgt.Z i, z, some Tgt.F⟩
      ≤ RT * Tν
        * (4 * (∑ sc' ∈ screenSucc S ⟨Tgt.Z i, z, some Tgt.F⟩,
              interpScreen α Rv μ ν v0 h sc')
          + 4 * (ENNReal.ofReal α * M * E')
          + 2 * (((zsucc S z).card * E') * ((zsucc S z).card * E'))) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hdesc : interpScreen α Rv μ ν v0 (h + 1) ⟨Tgt.Z i, z, some Tgt.F⟩
      = ∑' xp, Xi μ ν v0 i h xp
          * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * ((rE μ Rv v0) ^ (-α)
              * WresD α (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)) := by
    rw [interpScreen_forced_step α Rv μ ν v0 S hSsupp hrefl hpos i z hzf
      (some Tgt.F) h]
    refine tsum_congr fun xp => ?_
    rw [show interpNorm α Rv μ ν v0 (h + 1) (some Tgt.F)
        (branch (v0, i) xp)
        = WresD α (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
            (branch (v0, i) xp) from rfl,
      WresD_Tlaw_succ_branch α Rv μ ν v0 v0 hpos i h xp]
  have hpt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi μ ν v0 i h xp
        * ((if ∀ p ∈ memPairs μ ν v0 S h z,
              rE (prodPMF p.1 p.2)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0
            then (1 : ℝ≥0∞) else 0)
          * ((rE μ Rv v0) ^ (-α)
            * WresD α (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp))
      ≤ ∑' j, (if (ν j : ℝ≥0∞) = 0 then 0
          else (ν j : ℝ≥0∞) ^ (-α)
            * (Xi μ ν v0 i h xp
              * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                    rE (prodPMF p.1 p.2)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0
                  then (1 : ℝ≥0∞) else 0)
                * ((rE μ Rv v0) ^ (-α)
                  * WresD α (Xi μ ν v0 j h)
                      (SquareRel (fullSim (labRel Rv) h)) xp)))) := by
    intro xp
    refine tilt_exchange α ν _ _ _ _ ?_
    calc (rE μ Rv v0) ^ (-α)
        * WresD α (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h)) xp
        ≤ (rE μ Rv v0) ^ (-α)
          * ∑' j, (if (ν j : ℝ≥0∞) = 0 then 0
              else (ν j : ℝ≥0∞) ^ (-α)
                * WresD α (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp) :=
          mul_le_mul_right (WresD_XiBar_le_sum α Rv μ ν v0 hα0 h xp) _
      _ = ∑' j, (rE μ Rv v0) ^ (-α)
            * (if (ν j : ℝ≥0∞) = 0 then 0
              else (ν j : ℝ≥0∞) ^ (-α)
                * WresD α (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp) :=
          ENNReal.tsum_mul_left.symm
      _ = ∑' j, (if (ν j : ℝ≥0∞) = 0 then 0
            else (ν j : ℝ≥0∞) ^ (-α)
              * ((rE μ Rv v0) ^ (-α)
                * WresD α (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)) :=
          tsum_congr fun j => by
            by_cases hj0 : (ν j : ℝ≥0∞) = 0
            · rw [if_pos hj0, if_pos hj0, mul_zero]
            · rw [if_neg hj0, if_neg hj0]; ring
  have hterm : ∀ j : ℕ,
      (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        (if (ν j : ℝ≥0∞) = 0 then 0
          else (ν j : ℝ≥0∞) ^ (-α)
            * (Xi μ ν v0 i h xp
              * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                    rE (prodPMF p.1 p.2)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0
                  then (1 : ℝ≥0∞) else 0)
                * ((rE μ Rv v0) ^ (-α)
                  * WresD α (Xi μ ν v0 j h)
                      (SquareRel (fullSim (labRel Rv) h)) xp)))))
      ≤ (if (ν j : ℝ≥0∞) = 0 then 0 else (ν j : ℝ≥0∞) ^ (-α))
        * (RT * (4 * (∑ sc' ∈ screenSucc S ⟨Tgt.Z i, z, some Tgt.F⟩,
              interpScreen α Rv μ ν v0 h sc')
            + 4 * (ENNReal.ofReal α * M * E')
            + 2 * (((zsucc S z).card * E')
              * ((zsucc S z).card * E')))) := by
    intro j
    by_cases hj0 : (ν j : ℝ≥0∞) = 0
    · exact le_trans (le_of_eq (tsum_congr fun xp => if_pos hj0))
        (le_trans (le_of_eq tsum_zero) zero_le)
    · have hjS : j ∈ S := (hSsupp j).mp hj0
      refine le_trans (le_of_eq (tsum_congr fun xp => if_neg hj0)) ?_
      rw [ENNReal.tsum_mul_left, if_neg hj0]
      refine mul_le_mul_right ?_ _
      have hswap : (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
          Xi μ ν v0 i h xp
            * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                  rE (prodPMF p.1 p.2)
                    (SquareRel (fullSim (labRel Rv) h)) xp = 0
                then (1 : ℝ≥0∞) else 0)
              * ((rE μ Rv v0) ^ (-α)
                * WresD α (Xi μ ν v0 j h)
                    (SquareRel (fullSim (labRel Rv) h)) xp)))
          = ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
            (rE μ Rv v0) ^ (-α)
              * (Xi μ ν v0 i h xp
                * ((if ∀ p ∈ memPairs μ ν v0 S h z,
                      rE (prodPMF p.1 p.2)
                        (SquareRel (fullSim (labRel Rv) h)) xp = 0
                    then (1 : ℝ≥0∞) else 0)
                  * WresD α (Xi μ ν v0 j h)
                      (SquareRel (fullSim (labRel Rv) h)) xp)) :=
        tsum_congr fun xp => by ring
      rw [hswap, ENNReal.tsum_mul_left]
      exact mul_le_mul' hRT (eRowZ_W_cell α Rv μ ν v0 hα S i j h z M E'
        (∑ sc' ∈ screenSucc S ⟨Tgt.Z i, z, some Tgt.F⟩,
          interpScreen α Rv μ ν v0 h sc')
        (hMom j hjS) (hscrS j hjS)
        (fun c' hc' w' hw' => interp_le_succ_sum μ ν v0 Rv α h
          (mem_screenSucc_mk hc'
            (some_mem_normSucc (Finset.mem_biUnion.mpr ⟨j, hjS, hw'⟩))))
        (fun c' hc' w' hw' => hE _
          (mem_screenSucc_mk hc'
            (some_mem_normSucc (Finset.mem_biUnion.mpr ⟨j, hjS, hw'⟩)))))
  rw [hdesc]
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_comm]
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_right]
  refine le_trans (mul_le_mul_left hTν _) (le_of_eq ?_)
  ring

end GraphMarkovMatching
