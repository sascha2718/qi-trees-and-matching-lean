/-
The forced-source screen rows of the `ν = δ₃` instantiation
(`arbitrary_offspring_matching.tex`, `sec:rows` at
`ν = δ₃`, screen rows): the source cell is `(v0, 2)`, and after
diagonal pruning all outputs are quadratic.

The forced-source screens start at the counter-`2` cell
`Z₂(h+1) = muM(v0,2)(h+1)`, whose child pair is the fresh product
`Ξ₂ = T ⊗ T`; the collapsed mixture is `Ξ̄ = Ξ₃ = Z₂ ⊗ T`.  Every
two-list screen produced by the Hall factorization contains the fresh
law itself, so diagonal pruning (`screenE_self_mem`) removes all row
terms and the `[T]`-column products; only the `[Z₂]`-column products
survive:

* `delta3_e6_row`: the forced-tilt screen row: the forced tilt
  converts without a root factor (`WresD_Zlaw_succ_branch` at the
  reflexive root), and the fresh-product survivor split leaves the
  same quadratic product twice;
* `delta3_zZT_row`: the zero-mass row: the reversed dead mass of the
  forced cell against the fresh law descends to the pair level
  (`zMass_Tlaw_succ`), Hall-factorizes with unit tilts, and prunes to
  the square of the reversed zero-interface mass toward the
  counter-`2` law (`screenE_one_eq_zMass`).
-/
import GraphMarkovMatching.Process.ScreenTilt
import GraphMarkovMatching.Process.ScreenBridges
import GraphMarkovMatching.Process.ZMass
import GraphMarkovMatching.Delta3.Step

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-! ### The forced-tilt screen row -/

/-- **Forced-source screen row, forced tilt** (`sec:rows` at
`ν = δ₃`, screen rows, entry `E₆`): the forced tilt converts across
the branch point without a root factor, and the fresh-product
survivor split with diagonal pruning leaves the squared counter-`2`
screen, once per pairing. -/
theorem delta3_e6_row (hα : 1 ≤ α) (hrefl : ∀ v, Rv v v)
    (hvpos : rE μ Rv v0 ≠ 0) (h : ℕ) :
    screenE (Zlaw μ (PMF.pure 3) v0 2 (h + 1)) (fullSim (labRel Rv) (h + 1))
        [Tlaw μ (PMF.pure 3) v0 (h + 1)]
        (WresD α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
          (fullSim (labRel Rv) (h + 1)))
      ≤ screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Zlaw μ (PMF.pure 3) v0 2 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          * screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Zlaw μ (PMF.pure 3) v0 2 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
        + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Zlaw μ (PMF.pure 3) v0 2 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          * screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
            [Zlaw μ (PMF.pure 3) v0 2 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hreflh : ∀ x : FullLab (V × ℕ) h, fullSim (labRel Rv) h x x :=
    fun x => fullSim_refl (labRel Rv) (fun s => hrefl s.1) h x
  have hfac : ∀ G₀ G₁ : FullLab (V × ℕ) h → ℝ≥0∞,
      (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
          prodPMF (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h) xp
            * ((if rE (prodPMF (Zlaw μ (PMF.pure 3) v0 2 h)
                    (Tlaw μ (PMF.pure 3) v0 h))
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (G₀ xp.1 * G₁ xp.2)))
        ≤ screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h] G₀
            * screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h] G₁ := by
    intro G₀ G₁
    refine le_trans (deadScreen_factorize (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) G₀ G₁)
      (le_of_eq ?_)
    rw [screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
        [Zlaw μ (PMF.pure 3) v0 2 h, Tlaw μ (PMF.pure 3) v0 h] G₀
        (by simp) hreflh,
      screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
        [Zlaw μ (PMF.pure 3) v0 2 h, Tlaw μ (PMF.pure 3) v0 h] G₁
        (by simp) hreflh,
      screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
        [Tlaw μ (PMF.pure 3) v0 h] G₀ (by simp) hreflh]
    ring
  have hdesc : screenE (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
        (fullSim (labRel Rv) (h + 1)) [Tlaw μ (PMF.pure 3) v0 (h + 1)]
        (WresD α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
          (fullSim (labRel Rv) (h + 1)))
      = ∑' xp, Xi μ (PMF.pure 3) v0 2 h xp
          * ((if rE (XiBar μ (PMF.pure 3) v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
                (fullSim (labRel Rv) (h + 1)) (branch (v0, 2) xp)) := by
    rw [screenE_singleton]
    exact screenG_Tlaw_succ Rv μ (PMF.pure 3) v0 v0 hvpos 2 h
      (WresD α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
        (fullSim (labRel Rv) (h + 1)))
  -- the forced tilt converts at the reflexive root, no root factor
  have htilt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi μ (PMF.pure 3) v0 2 h xp
          * ((if rE (XiBar μ (PMF.pure 3) v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
                (fullSim (labRel Rv) (h + 1)) (branch (v0, 2) xp))
        = Xi μ (PMF.pure 3) v0 2 h xp
          * ((if rE (Xi μ (PMF.pure 3) v0 3 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (Xi μ (PMF.pure 3) v0 2 h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
    intro xp
    rw [WresD_Zlaw_succ_branch α Rv μ (PMF.pure 3) v0 v0 2 2 h xp,
      if_pos (hrefl v0), XiBar_delta3 μ v0 h]
  have hpt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      prodPMF (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h) xp
          * ((if rE (prodPMF (Zlaw μ (PMF.pure 3) v0 2 h)
                  (Tlaw μ (PMF.pure 3) v0 h))
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (prodPMF (Tlaw μ (PMF.pure 3) v0 h)
                  (Tlaw μ (PMF.pure 3) v0 h))
                (SquareRel (fullSim (labRel Rv) h)) xp)
        ≤ prodPMF (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h) xp
            * ((if rE (prodPMF (Zlaw μ (PMF.pure 3) v0 2 h)
                    (Tlaw μ (PMF.pure 3) v0 h))
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.1
                * WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.2))
          + prodPMF (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h) xp
            * ((if rE (prodPMF (Zlaw μ (PMF.pure 3) v0 2 h)
                    (Tlaw μ (PMF.pure 3) v0 h))
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.1
                * WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.2)) := by
    intro xp
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_right (mul_le_mul_right
      (WresD_square_le_sum hα0 (Tlaw μ (PMF.pure 3) v0 h)
        (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) xp) _) _
  rw [hdesc, tsum_congr htilt,
    Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h,
    Xi_three μ (PMF.pure 3) v0 h]
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  exact add_le_add
    (hfac (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))
    (hfac (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))

/-! ### The zero-mass row -/

/-- **Forced-source zero-mass row** (`sec:rows` at `ν = δ₃`,
zero-mass outputs): the reversed dead mass of the forced cell against
the fresh law descends to the pair level, Hall-factorizes with unit
tilts, and after diagonal pruning only the `[Z₂]`-column survives: the
square of the reversed zero-interface mass toward the counter-`2`
law. -/
theorem delta3_zZT_row (_hα : 1 ≤ α) (hrefl : ∀ v, Rv v v)
    (hvpos : rE μ Rv v0 ≠ 0) (h : ℕ) :
    zMass (Zlaw μ (PMF.pure 3) v0 2 (h + 1)) (Tlaw μ (PMF.pure 3) v0 (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ zMass (Tlaw μ (PMF.pure 3) v0 h) (Zlaw μ (PMF.pure 3) v0 2 h)
            (fullSim (labRel Rv) h)
          * zMass (Tlaw μ (PMF.pure 3) v0 h) (Zlaw μ (PMF.pure 3) v0 2 h)
            (fullSim (labRel Rv) h) := by
  have hreflh : ∀ x : FullLab (V × ℕ) h, fullSim (labRel Rv) h x x :=
    fun x => fullSim_refl (labRel Rv) (fun s => hrefl s.1) h x
  -- the fresh zero-mass row at the cell root `(v0, 2)`, charged root
  have hdesc : zMass (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
        (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
      = ∑' xp, Xi μ (PMF.pure 3) v0 2 h xp
          * (if rE (XiBar μ (PMF.pure 3) v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0) := by
    rw [zMass_eq_tsum]
    have hz := zMass_Tlaw_succ Rv μ (PMF.pure 3) v0 v0 2 h
    rw [if_neg hvpos] at hz
    exact hz
  rw [hdesc, XiBar_delta3 μ v0 h,
    Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h,
    Xi_three μ (PMF.pure 3) v0 h]
  refine le_trans (deadMass_factorize (Tlaw μ (PMF.pure 3) v0 h)
    (Tlaw μ (PMF.pure 3) v0 h) (Zlaw μ (PMF.pure 3) v0 2 h)
    (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)) (le_of_eq ?_)
  rw [screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      [Zlaw μ (PMF.pure 3) v0 2 h, Tlaw μ (PMF.pure 3) v0 h] (fun _ => 1)
      (by simp) hreflh,
    screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      [Tlaw μ (PMF.pure 3) v0 h] (fun _ => 1) (by simp) hreflh,
    screenE_one_eq_zMass (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      (Zlaw μ (PMF.pure 3) v0 2 h)]
  ring

end GraphMarkovMatching
