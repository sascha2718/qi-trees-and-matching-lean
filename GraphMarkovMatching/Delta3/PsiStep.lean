/-
The assembled ordinary step of the `ν = δ₃` closure
(`arbitrary_offspring_matching.tex`, `sec:rows` massaged into the
monotone step function `f`): the four ordinary rows, with their screens
pruned on the diagonal and the survivors read off as coordinates of the
screen vector, give the `Ψ`-step hypothesis of the closure keystone
`delta3_failure_uniform`.
-/
import GraphMarkovMatching.Delta3.StepFun

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- **The assembled ordinary step**: every ordinary coordinate at height
`h + 1` is bounded by the ordinary step function `delta3F`, evaluated at
the ordinary supremum and the screen supremum of height `h`.  Diagonal
pruning kills the self-screens of each row, and every surviving screen
is a coordinate of the screen vector `delta3E`. -/
theorem delta3_Psi_step_assembled {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (hrefl : ∀ v, Rv v v) (h : ℕ) :
    delta3Psi α Rv μ v0 (h + 1)
      ≤ delta3F α Rv μ v0 δ L K (delta3Psi α Rv μ v0 h)
          (⨆ i, delta3E α Rv μ v0 h i) := by
  have hreflh : ∀ x : FullLab (V × ℕ) h, fullSim (labRel Rv) h x x :=
    fullSim_refl (labRel Rv) (fun s => hrefl s.1) h
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
      ≤ ⨆ i, delta3E α Rv μ v0 h i :=
    le_trans (le_of_eq (zMass_self (Zlaw μ (PMF.pure 3) v0 2 h)
      (fullSim (labRel Rv) h) hreflh)) zero_le
  have hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      ≤ ⨆ i, delta3E α Rv μ v0 h i :=
    le_iSup (delta3E α Rv μ v0 h) 2
  have hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      ≤ ⨆ i, delta3E α Rv μ v0 h i :=
    le_iSup (delta3E α Rv μ v0 h) 4
  have hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      ≤ ⨆ i, delta3E α Rv μ v0 h i :=
    le_trans (le_of_eq (zMass_self (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h) hreflh)) zero_le
  -- the surviving screen entries against the screen supremum
  have hb0 : screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
      ≤ ⨆ i, delta3E α Rv μ v0 h i :=
    le_iSup (delta3E α Rv μ v0 h) 0
  have hb1 : screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
      ≤ ⨆ i, delta3E α Rv μ v0 h i :=
    le_iSup (delta3E α Rv μ v0 h) 1
  have hb3 : screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      [Zlaw μ (PMF.pure 3) v0 2 h]
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
      ≤ ⨆ i, delta3E α Rv μ v0 h i :=
    le_iSup (delta3E α Rv μ v0 h) 3
  -- the `(Z₂ → F)` square cell against the square-cell bound
  have hSQZT : ENNReal.ofReal (2 * L + 2 * (1 + δ) * K)
        * delta3Psi α Rv μ v0 h
      + ENNReal.ofReal
          (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
        * delta3Psi α Rv μ v0 h ^ 2
      + ENNReal.ofReal (2 * (1 + δ)) * (⨆ i, delta3E α Rv μ v0 h i)
      + (screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Zlaw μ (PMF.pure 3) v0 2 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
              (fullSim (labRel Rv) h))
          + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Zlaw μ (PMF.pure 3) v0 2 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
              (fullSim (labRel Rv) h)))
        * (1 + ENNReal.ofReal α * delta3Psi α Rv μ v0 h)
      ≤ delta3CB α δ L K (delta3Psi α Rv μ v0 h)
          (⨆ i, delta3E α Rv μ v0 h i) := by
    rw [screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
      (by simp) hreflh]
    simp only [add_zero]
    rw [delta3CB]
    exact add_le_add le_rfl (mul_le_mul_left
      (le_trans (add_le_add hb3 hb3) (le_of_eq (two_mul _).symm)) _)
  -- the `(F → F)` square cell against the square-cell bound
  have hSQTT : ENNReal.ofReal (2 * L + 2 * (1 + δ) * K)
        * delta3Psi α Rv μ v0 h
      + ENNReal.ofReal
          (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
        * delta3Psi α Rv μ v0 h ^ 2
      + ENNReal.ofReal (2 * (1 + δ)) * (⨆ i, delta3E α Rv μ v0 h i)
      + (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Zlaw μ (PMF.pure 3) v0 2 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
              (fullSim (labRel Rv) h))
          + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Zlaw μ (PMF.pure 3) v0 2 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
              (fullSim (labRel Rv) h)))
        * (1 + ENNReal.ofReal α * delta3Psi α Rv μ v0 h)
      ≤ delta3CB α δ L K (delta3Psi α Rv μ v0 h)
          (⨆ i, delta3E α Rv μ v0 h i) := by
    rw [screenE_self_mem (Zlaw μ (PMF.pure 3) v0 2 h)
        (fullSim (labRel Rv) h) [Zlaw μ (PMF.pure 3) v0 2 h]
        (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
        (by simp) hreflh,
      screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h)
        (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
        (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
        (by simp) hreflh]
    simp only [zero_add, add_zero]
    rw [delta3CB]
    exact add_le_add le_rfl (mul_le_mul_left
      (le_trans (add_le_add hb1 hb3) (le_of_eq (two_mul _).symm)) _)
  -- the forced-forced row `(Z₂ → Z₂)`
  have hrow22 : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
      (Zlaw μ (PMF.pure 3) v0 2 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ delta3F α Rv μ v0 δ L K (delta3Psi α Rv μ v0 h)
          (⨆ i, delta3E α Rv μ v0 h i) := by
    refine le_trans (delta3_Zlaw_Zlaw_step_22 α Rv μ v0 hα hδ hL0 hL hK0
      hK hRvsymm (hrefl v0) h (delta3Psi α Rv μ v0 h)
      (⨆ i, delta3E α Rv μ v0 h i)
      hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT) ?_
    rw [screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
      (by simp) hreflh]
    simp only [add_zero, zero_mul]
    refine le_trans ?_ (delta3CB_le_F α Rv μ v0 δ L K
      (delta3Psi α Rv μ v0 h) (⨆ i, delta3E α Rv μ v0 h i))
    rw [delta3CB]
    exact le_self_add
  -- the forced-fresh row `(Z₂ → F)`
  have hrowZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
      (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ delta3F α Rv μ v0 δ L K (delta3Psi α Rv μ v0 h)
          (⨆ i, delta3E α Rv μ v0 h i) := by
    refine le_trans (delta3_Zlaw_Tlaw_step_2 α Rv μ v0 hα hδ hL0 hL hK0
      hK hRvsymm h (delta3Psi α Rv μ v0 h)
      (⨆ i, delta3E α Rv μ v0 h i)
      hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT) ?_
    rw [delta3F]
    exact add_le_add (add_le_add le_add_self hSQZT)
      (mul_le_mul_right (mul_le_mul' le_add_self hSQZT) _)
  -- the fresh-forced row `(F → Z₂)`
  have hrowTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 (h + 1))
      (Zlaw μ (PMF.pure 3) v0 2 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ delta3F α Rv μ v0 δ L K (delta3Psi α Rv μ v0 h)
          (⨆ i, delta3E α Rv μ v0 h i) := by
    refine le_trans (delta3_Tlaw_Zlaw_step_2 α Rv μ v0 hα hδ hL0 hL hK0
      hK hRvsymm h (delta3Psi α Rv μ v0 h)
      (⨆ i, delta3E α Rv μ v0 h i)
      hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT) ?_
    rw [screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
      (by simp) hreflh]
    simp only [add_zero]
    refine le_trans ?_ (delta3CB_le_F α Rv μ v0 δ L K
      (delta3Psi α Rv μ v0 h) (⨆ i, delta3E α Rv μ v0 h i))
    rw [delta3CB]
    exact add_le_add le_rfl (mul_le_mul_left
      (le_trans (add_le_add hb0 hb0) (le_of_eq (two_mul _).symm)) _)
  -- the principal fresh-fresh row `(F → F)`
  have hrowTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 (h + 1))
      (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ delta3F α Rv μ v0 δ L K (delta3Psi α Rv μ v0 h)
          (⨆ i, delta3E α Rv μ v0 h i) := by
    refine le_trans (delta3_Tlaw_Tlaw_step α Rv μ v0 hα hδ hL0 hL hK0
      hK hRvsymm h (delta3Psi α Rv μ v0 h)
      (⨆ i, delta3E α Rv μ v0 h i)
      hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT) ?_
    rw [delta3F]
    exact add_le_add (add_le_add le_self_add hSQTT)
      (mul_le_mul_right (mul_le_mul' le_self_add hSQTT) _)
  conv_lhs => rw [delta3Psi]
  exact sup_le (sup_le (sup_le hrow22 hrowZT) hrowTZ) hrowTT

end GraphMarkovMatching
