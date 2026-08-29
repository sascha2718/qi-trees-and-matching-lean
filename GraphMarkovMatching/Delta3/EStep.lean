/-
The assembled screen step of the `ν = δ₃` closure
(`arbitrary_offspring_matching.tex`, `sec:rows` screen and
zero-mass rows massaged into the monotone step function `g`): the five
screen rows, with their diagonal screens pruned and the survivors read
off as coordinates of the screen vector, give the `E`-step hypothesis
of the closure keystone `delta3_failure_uniform` in the split form
`delta3G` plus the nilpotent part `N·E`.  The fresh-tilt coordinate
`e₄` vanishes identically (`screenE_tilt_self`: its zero list is its
own tilt law), so its row needs no `g`-budget and the `δ₃` screen
system is effectively four-dimensional.
-/
import GraphMarkovMatching.Delta3.StepFun

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- **The assembled screen step**: every screen coordinate at height
`h + 1` is bounded by the screen step function `delta3G`, evaluated at
the ordinary supremum and the screen supremum of height `h`, plus the
matching row of the nilpotent screen matrix applied to the height-`h`
screen vector. -/
theorem delta3_E_step_assembled {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (hrefl : ∀ v, Rv v v)
    (hhalf : 2⁻¹ ≤ μ v0) (h : ℕ) (i : Fin 5) :
    delta3E α Rv μ v0 (h + 1) i
      ≤ delta3G α Rv μ v0 δ L K (delta3Psi α Rv μ v0 h)
          (⨆ j, delta3E α Rv μ v0 h j)
        + mulVec (delta3N α Rv μ) (delta3E α Rv μ v0 h) i := by
  have hreflh : ∀ x : FullLab (V × ℕ) h, fullSim (labRel Rv) h x x :=
    fullSim_refl (labRel Rv) (fun s => hrefl s.1) h
  -- the root is charged: half the mass sits at `v0` itself
  have hle : (2⁻¹ : ℝ≥0∞) ≤ rE μ Rv v0 :=
    le_trans hhalf (le_rE_of_refl (hrefl v0))
  have hvpos : rE μ Rv v0 ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 2⁻¹) hle).ne'
  -- the four coordinates of the ordinary supremum at height `h`
  have hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      ≤ delta3Psi α Rv μ v0 h := by
    rw [delta3Psi]
    exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      ≤ delta3Psi α Rv μ v0 h := by
    rw [delta3Psi]
    exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      ≤ delta3Psi α Rv μ v0 h := by
    rw [delta3Psi]
    exact le_sup_of_le_left le_sup_right
  have hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      ≤ delta3Psi α Rv μ v0 h := by
    rw [delta3Psi]
    exact le_sup_right
  -- the four zero masses against the screen supremum
  have hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      ≤ ⨆ j, delta3E α Rv μ v0 h j :=
    le_trans (le_of_eq (zMass_self (Zlaw μ (PMF.pure 3) v0 2 h)
      (fullSim (labRel Rv) h) hreflh)) zero_le
  have hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      ≤ ⨆ j, delta3E α Rv μ v0 h j :=
    le_iSup (delta3E α Rv μ v0 h) 2
  have hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      ≤ ⨆ j, delta3E α Rv μ v0 h j :=
    le_iSup (delta3E α Rv μ v0 h) 4
  have hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      ≤ ⨆ j, delta3E α Rv μ v0 h j :=
    le_trans (le_of_eq (zMass_self (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h) hreflh)) zero_le
  -- the surviving screen entries against the screen supremum
  have hb0 : screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
      ≤ ⨆ j, delta3E α Rv μ v0 h j :=
    le_iSup (delta3E α Rv μ v0 h) 0
  have hb1 : screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
      ≤ ⨆ j, delta3E α Rv μ v0 h j :=
    le_iSup (delta3E α Rv μ v0 h) 1
  have hb3 : screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      [Zlaw μ (PMF.pure 3) v0 2 h]
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
      ≤ ⨆ j, delta3E α Rv μ v0 h j :=
    le_iSup (delta3E α Rv μ v0 h) 3
  -- the collapsed square cell against the square-cell bound
  have hsq33 : PhiDres α (Xi μ (PMF.pure 3) v0 3 h)
      (Xi μ (PMF.pure 3) v0 3 h) (SquareRel (fullSim (labRel Rv) h))
      ≤ delta3CB α δ L K (delta3Psi α Rv μ v0 h)
          (⨆ j, delta3E α Rv μ v0 h j) := by
    rw [Xi_three μ (PMF.pure 3) v0 h]
    refine le_trans (PhiDres_square_le hα hδ hL0 hL hK0 hK
      (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h)
      (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
      (delta3Psi α Rv μ v0 h) (⨆ j, delta3E α Rv μ v0 h j)
      hZZ hZT hTZ hTT hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT) ?_
    rw [screenE_self_mem (Zlaw μ (PMF.pure 3) v0 2 h)
        (fullSim (labRel Rv) h) [Zlaw μ (PMF.pure 3) v0 2 h]
        (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
        (by simp) hreflh,
      screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
        [Tlaw μ (PMF.pure 3) v0 h]
        (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
        (by simp) hreflh]
    simp only [zero_add, add_zero]
    rw [delta3CB]
    exact add_le_add le_rfl (mul_le_mul_left
      (le_trans (add_le_add hb1 hb3) (le_of_eq (two_mul _).symm)) _)
  match i with
  | 0 =>
    -- the fresh-tilt screen row vanishes identically: its zero list is
    -- its own tilt law
    exact le_trans (le_of_eq (show delta3E α Rv μ v0 (h + 1) 0 = 0 from
      screenE_tilt_self α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
        (fullSim (labRel Rv) (h + 1)) (Tlaw μ (PMF.pure 3) v0 (h + 1))))
      zero_le
  | 1 =>
    -- the forced-tilt screen row: the quadratic screens
    refine le_trans (show delta3E α Rv μ v0 (h + 1) 1 ≤ _ from
      delta3_e6_row α Rv μ v0 hα hrefl hvpos h) ?_
    refine le_trans (add_le_add (mul_le_mul' hb3 hb3)
      (mul_le_mul' hb3 hb3)) ?_
    refine le_trans (le_of_eq (show (⨆ j, delta3E α Rv μ v0 h j)
          * (⨆ j, delta3E α Rv μ v0 h j)
        + (⨆ j, delta3E α Rv μ v0 h j) * (⨆ j, delta3E α Rv μ v0 h j)
        = 2 * (⨆ j, delta3E α Rv μ v0 h j) ^ 2 from by ring)) ?_
    refine le_trans (mul_le_mul_left
      (by norm_num : (2 : ℝ≥0∞) ≤ 3) _) ?_
    exact le_trans (le_trans le_add_self le_self_add) le_self_add
  | 2 =>
    -- the forced zero-mass row: the squared reversed zero mass
    refine le_trans (show delta3E α Rv μ v0 (h + 1) 2 ≤ _ from
      delta3_zZT_row α Rv μ v0 hα hrefl hvpos h) ?_
    refine le_trans (mul_le_mul' hzTZ hzTZ) ?_
    refine le_trans (le_of_eq (show (⨆ j, delta3E α Rv μ v0 h j)
          * (⨆ j, delta3E α Rv μ v0 h j)
        = 1 * (⨆ j, delta3E α Rv μ v0 h j) ^ 2 from by ring)) ?_
    refine le_trans (mul_le_mul_left
      (by norm_num : (1 : ℝ≥0∞) ≤ 3) _) ?_
    exact le_trans (le_trans le_add_self le_self_add) le_self_add
  | 3 =>
    -- the fresh-source screen row: far tilt, split quadratic, and the
    -- two forced-source screens carried by the nilpotent matrix
    have hFarLe : delta3Far α Rv μ v0
        * (1 + ENNReal.ofReal α
            * PhiDres α (Xi μ (PMF.pure 3) v0 3 h)
                (Xi μ (PMF.pure 3) v0 3 h)
                (SquareRel (fullSim (labRel Rv) h)))
        ≤ delta3Far α Rv μ v0
          * (1 + ENNReal.ofReal α
              * delta3CB α δ L K (delta3Psi α Rv μ v0 h)
                  (⨆ j, delta3E α Rv μ v0 h j)) :=
      mul_le_mul_right (add_le_add le_rfl (mul_le_mul_right hsq33 _)) _
    have hQuadLe : delta3Tilt α Rv μ
        * ((screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                (fullSim (labRel Rv) h))
            + screenE (Zlaw μ (PMF.pure 3) v0 2 h)
              (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                (fullSim (labRel Rv) h)))
          * (ENNReal.ofReal α
              * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                  (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
                + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                  (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h))))
        ≤ 4 * (ENNReal.ofReal α * (delta3Tilt α Rv μ
            * (delta3Psi α Rv μ v0 h
              * (⨆ j, delta3E α Rv μ v0 h j)))) := by
      refine le_trans (mul_le_mul_right (mul_le_mul'
        (add_le_add hb1 hb0)
        (mul_le_mul_right (add_le_add hTT hTZ) _)) _) (le_of_eq ?_)
      ring
    calc delta3E α Rv μ v0 (h + 1) 3
        ≤ delta3Far α Rv μ v0
            * (1 + ENNReal.ofReal α
                * PhiDres α (Xi μ (PMF.pure 3) v0 3 h)
                    (Xi μ (PMF.pure 3) v0 3 h)
                    (SquareRel (fullSim (labRel Rv) h)))
          + delta3Tilt α Rv μ
            * ((screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h))
                + screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h)))
              * (1 + ENNReal.ofReal α
                  * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                      (Tlaw μ (PMF.pure 3) v0 h)
                      (fullSim (labRel Rv) h)
                    + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                      (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h)))) :=
          delta3_e2_row α Rv μ v0 hα hrefl h
      _ ≤ (delta3Far α Rv μ v0
            * (1 + ENNReal.ofReal α
                * delta3CB α δ L K (delta3Psi α Rv μ v0 h)
                    (⨆ j, delta3E α Rv μ v0 h j))
          + 4 * (ENNReal.ofReal α * (delta3Tilt α Rv μ
              * (delta3Psi α Rv μ v0 h
                * (⨆ j, delta3E α Rv μ v0 h j)))))
          + (delta3Tilt α Rv μ
              * screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h))
            + delta3Tilt α Rv μ
              * screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h))) := by
          refine le_trans (le_of_eq ?_)
            (add_le_add (add_le_add hFarLe hQuadLe) le_rfl)
          ring
      _ ≤ delta3G α Rv μ v0 δ L K (delta3Psi α Rv μ v0 h)
            (⨆ j, delta3E α Rv μ v0 h j)
          + (delta3Tilt α Rv μ
              * screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h))
            + delta3Tilt α Rv μ
              * screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h))) :=
          add_le_add (le_trans le_self_add le_self_add) le_rfl
      _ ≤ delta3G α Rv μ v0 δ L K (delta3Psi α Rv μ v0 h)
            (⨆ j, delta3E α Rv μ v0 h j)
          + mulVec (delta3N α Rv μ) (delta3E α Rv μ v0 h) 3 :=
          add_le_add le_rfl (le_of_eq
            (delta3N_mulVec_three α Rv μ (delta3E α Rv μ v0 h)).symm)
  | 4 =>
    -- the fresh zero-mass row: far mass plus the reversed zero mass
    refine le_trans (show delta3E α Rv μ v0 (h + 1) 4
        ≤ delta3FarMass Rv μ v0
          + zMass (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
              (fullSim (labRel Rv) h)
      from delta3_zTZ_row Rv μ v0 hrefl h) ?_
    exact add_le_add le_add_self
      (le_of_eq (delta3N_mulVec_four α Rv μ (delta3E α Rv μ v0 h)).symm)

end GraphMarkovMatching
