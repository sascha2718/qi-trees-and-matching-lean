/-
The fresh-source screen rows of the `ν = δ₃` instantiation
(`arbitrary_offspring_matching.tex`, `sec:rows` at `ν = δ₃`,
fresh-source screen and zero-mass outputs): at a fresh height-`(h+1)`
source the root integrates out against `Q = μ ⊗ δ₃`, so the screen toward
the forced law and the reversed zero mass reduce, one level down, to root
factors times height-`h` quantities of the `δ₃`-ledger.

* `tsum_freshQ_pure3`: fresh sampling against `ν = δ₃` integrates the
  counter out at `3`;
* `delta3_e2_row`: the fresh-source screen row toward `Z₂`: far roots contribute
  their tilted mass against the collapsed-mixture moment
  `1 + α·Φres(Ξ₃ → Ξ₃)`, near roots contribute the root factor `r_μ(v)^{-α}`
  times the two surviving `(Z₂ ↛ T)`-screens with their restricted
  inverse moments (`thm:hall` on the dead pair target, diagonal screens
  pruned by `thm:pruning`);
* `delta3_zTZ_row`: the fresh-source zero-mass row toward `Z₂`: the
  reversed dead mass is the far root mass plus the surviving `(Z₂ ↛ T)`
  zero mass one level down.
-/
import GraphMarkovMatching.Process.ScreenTilt
import GraphMarkovMatching.Process.ScreenBridges
import GraphMarkovMatching.Process.ZMass
import GraphMarkovMatching.Delta3.Step

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- Fresh sampling against `ν = δ₃`: the counter integrates out at `3`. -/
lemma tsum_freshQ_pure3 (F : V × ℕ → ℝ≥0∞) :
    ∑' s : V × ℕ, freshQ μ (PMF.pure 3) s * F s = ∑' v, μ v * F (v, 3) := by
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun v => ?_
  have hpt : ∀ k : ℕ, freshQ μ (PMF.pure 3) (v, k) * F (v, k)
      = μ v * ((PMF.pure 3 : PMF ℕ) k * F (v, k)) := by
    intro k
    rw [show freshQ μ (PMF.pure 3) (v, k)
        = μ v * (PMF.pure 3 : PMF ℕ) k from rfl]
    ring
  rw [tsum_congr hpt, ENNReal.tsum_mul_left,
    tsum_pure_mul 3 (fun k => F (v, k))]

/-- **The fresh-source screen row for `ν = δ₃`** (`sec:rows`, screen
rows, fresh source toward the forced member): the height-`(h+1)` screen
`𝓔(F; Z₂ ↛ ·)` with the fresh inverse-degree tilt splits at the root.
Far roots pass unscreened and contribute their tilted mass against the
collapsed-mixture moment `1 + α·Φres(Ξ₃ → Ξ₃)`; near roots contribute the root
factor `r_μ(v)^{-α}` times the Hall factorization of the dead pair
target, whose diagonal screens vanish by `thm:pruning`, leaving the two
`(Z₂ ↛ T)`-screens with their restricted inverse moments. -/
theorem delta3_e2_row (hα : 1 ≤ α) (hrefl : ∀ v, Rv v v) (h : ℕ) :
    screenE (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
        [Zlaw μ (PMF.pure 3) v0 2 (h + 1)]
        (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
          (fullSim (labRel Rv) (h + 1)))
      ≤ (∑' v, if Rv v v0 then 0 else μ v * (rE μ Rv v) ^ (-α))
          * (1 + ENNReal.ofReal α
              * PhiDres α (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 3 h)
                  (SquareRel (fullSim (labRel Rv) h)))
        + (∑' v, μ v * (rE μ Rv v) ^ (-α))
          * ((screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                [Tlaw μ (PMF.pure 3) v0 h]
                (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
              + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                [Tlaw μ (PMF.pure 3) v0 h]
                (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))
            * (1 + ENNReal.ofReal α
                * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                    (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
                  + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                    (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h)))) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hR0refl : ∀ x : FullLab (V × ℕ) h, fullSim (labRel Rv) h x x :=
    fullSim_refl (labRel Rv) (fun s => hrefl s.1) h
  -- the far moment: the collapsed-mixture tilt integrates against `Ξ₃`
  have hFar : (∑' xp, Xi μ (PMF.pure 3) v0 3 h xp
        * WresD α (Xi μ (PMF.pure 3) v0 3 h)
            (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ 1 + ENNReal.ofReal α
          * PhiDres α (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 3 h)
              (SquareRel (fullSim (labRel Rv) h)) :=
    tsum_WresD_le hα (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 3 h)
      (SquareRel (fullSim (labRel Rv) h))
  -- the near pair screen: split the collapsed tilt and Hall-factorize
  have hS : (∑' xp, Xi μ (PMF.pure 3) v0 3 h xp
        * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (Xi μ (PMF.pure 3) v0 3 h)
              (SquareRel (fullSim (labRel Rv) h)) xp))
      ≤ (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
          + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))
        * (1 + ENNReal.ofReal α
            * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
                (fullSim (labRel Rv) h)
              + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))) := by
    -- pointwise survivor split of the collapsed tilt
    have hsplit : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ (PMF.pure 3) v0 3 h xp
          * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (Xi μ (PMF.pure 3) v0 3 h)
                (SquareRel (fullSim (labRel Rv) h)) xp)
        ≤ Xi μ (PMF.pure 3) v0 3 h xp
            * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) xp.1
                * WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.2))
          + Xi μ (PMF.pure 3) v0 3 h xp
            * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.1
                * WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) xp.2)) := by
      intro xp
      have hW : WresD α (Xi μ (PMF.pure 3) v0 3 h)
            (SquareRel (fullSim (labRel Rv) h)) xp
          ≤ WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) xp.1
              * WresD α (Tlaw μ (PMF.pure 3) v0 h)
                  (fullSim (labRel Rv) h) xp.2
            + WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) xp.1
              * WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) xp.2 := by
        rw [Xi_three μ (PMF.pure 3) v0 h]
        exact WresD_square_le_sum hα0 (Zlaw μ (PMF.pure 3) v0 2 h)
          (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) xp
      refine le_trans (mul_le_mul_right (mul_le_mul_right hW _) _)
        (le_of_eq ?_)
      ring
    -- the straight pairing Hall-factorizes; the diagonal screens vanish
    have hA : (∑' xp, Xi μ (PMF.pure 3) v0 3 h xp
          * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) xp.1
              * WresD α (Tlaw μ (PMF.pure 3) v0 h)
                  (fullSim (labRel Rv) h) xp.2)))
        ≤ screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
          * (1 + ENNReal.ofReal α
              * PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
                  (fullSim (labRel Rv) h)) := by
      rw [Xi_three μ (PMF.pure 3) v0 h,
        Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h]
      refine le_trans (deadScreen_factorize (Zlaw μ (PMF.pure 3) v0 2 h)
        (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
        (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
        (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
        (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))) ?_
      rw [screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
          [Tlaw μ (PMF.pure 3) v0 h, Tlaw μ (PMF.pure 3) v0 h]
          (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          (by simp) hR0refl,
        screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
          [Tlaw μ (PMF.pure 3) v0 h]
          (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          (by simp) hR0refl,
        mul_zero, mul_zero, add_zero, add_zero, add_zero,
        screenE_pair_self (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
          (Tlaw μ (PMF.pure 3) v0 h)
          (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))]
      exact mul_le_mul_right (tsum_WresD_le hα (Tlaw μ (PMF.pure 3) v0 h)
        (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)) _
    -- the crossed pairing, with the reversed tilts
    have hB : (∑' xp, Xi μ (PMF.pure 3) v0 3 h xp
          * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                  (fullSim (labRel Rv) h) xp.1
              * WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                  (fullSim (labRel Rv) h) xp.2)))
        ≤ screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          * (1 + ENNReal.ofReal α
              * PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                  (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)) := by
      rw [Xi_three μ (PMF.pure 3) v0 h,
        Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h]
      refine le_trans (deadScreen_factorize (Zlaw μ (PMF.pure 3) v0 2 h)
        (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
        (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
        (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
        (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))) ?_
      rw [screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
          [Tlaw μ (PMF.pure 3) v0 h, Tlaw μ (PMF.pure 3) v0 h]
          (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
          (by simp) hR0refl,
        screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
          [Tlaw μ (PMF.pure 3) v0 h]
          (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
          (by simp) hR0refl,
        mul_zero, mul_zero, add_zero, add_zero, add_zero,
        screenE_pair_self (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
          (Tlaw μ (PMF.pure 3) v0 h)
          (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))]
      exact mul_le_mul_right (tsum_WresD_le hα (Tlaw μ (PMF.pure 3) v0 h)
        (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)) _
    calc (∑' xp, Xi μ (PMF.pure 3) v0 3 h xp
          * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (Xi μ (PMF.pure 3) v0 3 h)
                (SquareRel (fullSim (labRel Rv) h)) xp))
        ≤ ∑' xp, (Xi μ (PMF.pure 3) v0 3 h xp
            * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) xp.1
                * WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.2))
          + Xi μ (PMF.pure 3) v0 3 h xp
            * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.1
                * WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) xp.2))) :=
          ENNReal.tsum_le_tsum hsplit
      _ = (∑' xp, Xi μ (PMF.pure 3) v0 3 h xp
            * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) xp.1
                * WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.2)))
          + ∑' xp, Xi μ (PMF.pure 3) v0 3 h xp
            * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
              * (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) xp.1
                * WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) xp.2)) :=
          ENNReal.tsum_add
      _ ≤ screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
          * (1 + ENNReal.ofReal α
              * PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
                  (fullSim (labRel Rv) h))
          + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          * (1 + ENNReal.ofReal α
              * PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                  (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)) :=
          add_le_add hA hB
      _ ≤ screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
          * (1 + ENNReal.ofReal α
              * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
                  (fullSim (labRel Rv) h)
                + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                    (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)))
          + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
            [Tlaw μ (PMF.pure 3) v0 h]
            (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
          * (1 + ENNReal.ofReal α
              * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
                  (fullSim (labRel Rv) h)
                + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                    (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))) :=
          add_le_add
            (mul_le_mul_right
              (add_le_add le_rfl (mul_le_mul_right le_self_add _)) _)
            (mul_le_mul_right
              (add_le_add le_rfl (mul_le_mul_right le_add_self _)) _)
      _ = (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
            + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α
              * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
                  (fullSim (labRel Rv) h)
                + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                    (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))) :=
          (add_mul _ _ _).symm
  -- the per-root cell bound
  have hcell : ∀ v : V,
      μ v * screenE (muM (varyK μ (PMF.pure 3) v0) (v, 3) (h + 1))
          (fullSim (labRel Rv) (h + 1)) [Zlaw μ (PMF.pure 3) v0 2 (h + 1)]
          (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
            (fullSim (labRel Rv) (h + 1)))
        ≤ (if Rv v v0 then 0 else μ v * (rE μ Rv v) ^ (-α))
            * (1 + ENNReal.ofReal α
                * PhiDres α (Xi μ (PMF.pure 3) v0 3 h)
                    (Xi μ (PMF.pure 3) v0 3 h)
                    (SquareRel (fullSim (labRel Rv) h)))
          + (μ v * (rE μ Rv v) ^ (-α))
            * ((screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                  [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h))
                + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                  [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h)))
              * (1 + ENNReal.ofReal α
                  * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
                    + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                      (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h)))) := by
    intro v
    rw [screenE_singleton (muM (varyK μ (PMF.pure 3) v0) (v, 3) (h + 1))
      (fullSim (labRel Rv) (h + 1)) (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
      (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1)))]
    by_cases hv : Rv v v0
    · -- near root: the screen descends to the pair screen
      rw [if_pos hv, zero_mul, zero_add,
        screenG_Zlaw_succ Rv μ (PMF.pure 3) v0 v hv 3 2 h
          (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
            (fullSim (labRel Rv) (h + 1)))]
      by_cases hvv : rE μ Rv v = 0
      · -- uncharged root: the fresh tilt vanishes identically
        have hzero : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
            Xi μ (PMF.pure 3) v0 3 h xp
              * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
                * WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
                    (fullSim (labRel Rv) (h + 1)) (branch (v, 3) xp)) = 0 := by
          intro xp
          have hr0 : rE (Tlaw μ (PMF.pure 3) v0 (h + 1))
              (fullSim (labRel Rv) (h + 1)) (branch (v, 3) xp) = 0 := by
            rw [rE_Tlaw_succ_branch μ (PMF.pure 3) v0 Rv v 3 h xp, hvv,
              zero_mul]
          rw [WresD, if_pos hr0, mul_zero, mul_zero]
        rw [tsum_congr hzero, tsum_zero, mul_zero]
        exact zero_le
      · -- charged root: convert the tilt and factor the root out
        have hconv : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
            Xi μ (PMF.pure 3) v0 3 h xp
              * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
                * WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
                    (fullSim (labRel Rv) (h + 1)) (branch (v, 3) xp))
            = (rE μ Rv v) ^ (-α)
              * (Xi μ (PMF.pure 3) v0 3 h xp
                * ((if rE (Xi μ (PMF.pure 3) v0 2 h)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
                  * WresD α (Xi μ (PMF.pure 3) v0 3 h)
                      (SquareRel (fullSim (labRel Rv) h)) xp)) := by
          intro xp
          rw [WresD_Tlaw_succ_branch α Rv μ (PMF.pure 3) v0 v hvv 3 h xp,
            XiBar_delta3 μ v0 h]
          ring
        rw [tsum_congr hconv, ENNReal.tsum_mul_left, ← mul_assoc]
        exact mul_le_mul_right hS _
    · -- far root: the dead indicator is one and the tilt passes through
      rw [if_neg hv,
        screenG_Zlaw_succ_far Rv μ (PMF.pure 3) v0 v hv 3 2 h
          (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
            (fullSim (labRel Rv) (h + 1)))]
      by_cases hvv : rE μ Rv v = 0
      · have hzero : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
            Xi μ (PMF.pure 3) v0 3 h xp
              * WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
                  (fullSim (labRel Rv) (h + 1)) (branch (v, 3) xp) = 0 := by
          intro xp
          have hr0 : rE (Tlaw μ (PMF.pure 3) v0 (h + 1))
              (fullSim (labRel Rv) (h + 1)) (branch (v, 3) xp) = 0 := by
            rw [rE_Tlaw_succ_branch μ (PMF.pure 3) v0 Rv v 3 h xp, hvv,
              zero_mul]
          rw [WresD, if_pos hr0, mul_zero]
        rw [tsum_congr hzero, tsum_zero, mul_zero]
        exact zero_le
      · have hconv : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
            Xi μ (PMF.pure 3) v0 3 h xp
              * WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
                  (fullSim (labRel Rv) (h + 1)) (branch (v, 3) xp)
            = (rE μ Rv v) ^ (-α)
              * (Xi μ (PMF.pure 3) v0 3 h xp
                * WresD α (Xi μ (PMF.pure 3) v0 3 h)
                    (SquareRel (fullSim (labRel Rv) h)) xp) := by
          intro xp
          rw [WresD_Tlaw_succ_branch α Rv μ (PMF.pure 3) v0 v hvv 3 h xp,
            XiBar_delta3 μ v0 h]
          ring
        rw [tsum_congr hconv, ENNReal.tsum_mul_left, ← mul_assoc]
        exact le_trans (mul_le_mul_right hFar _) le_self_add
  -- sum the cell bounds over the fresh root
  calc screenE (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
        [Zlaw μ (PMF.pure 3) v0 2 (h + 1)]
        (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
          (fullSim (labRel Rv) (h + 1)))
      = ∑' s : V × ℕ, freshQ μ (PMF.pure 3) s
          * screenE (muM (varyK μ (PMF.pure 3) v0) s (h + 1))
              (fullSim (labRel Rv) (h + 1)) [Zlaw μ (PMF.pure 3) v0 2 (h + 1)]
              (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
                (fullSim (labRel Rv) (h + 1))) :=
        screenE_bind_left (freshQ μ (PMF.pure 3))
          (fun s => muM (varyK μ (PMF.pure 3) v0) s (h + 1))
          (fullSim (labRel Rv) (h + 1)) [Zlaw μ (PMF.pure 3) v0 2 (h + 1)]
          (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
            (fullSim (labRel Rv) (h + 1)))
    _ = ∑' v, μ v * screenE (muM (varyK μ (PMF.pure 3) v0) (v, 3) (h + 1))
          (fullSim (labRel Rv) (h + 1)) [Zlaw μ (PMF.pure 3) v0 2 (h + 1)]
          (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
            (fullSim (labRel Rv) (h + 1))) :=
        tsum_freshQ_pure3 μ (fun s =>
          screenE (muM (varyK μ (PMF.pure 3) v0) s (h + 1))
            (fullSim (labRel Rv) (h + 1)) [Zlaw μ (PMF.pure 3) v0 2 (h + 1)]
            (WresD α (Tlaw μ (PMF.pure 3) v0 (h + 1))
              (fullSim (labRel Rv) (h + 1))))
    _ ≤ ∑' v, ((if Rv v v0 then 0 else μ v * (rE μ Rv v) ^ (-α))
            * (1 + ENNReal.ofReal α
                * PhiDres α (Xi μ (PMF.pure 3) v0 3 h)
                    (Xi μ (PMF.pure 3) v0 3 h)
                    (SquareRel (fullSim (labRel Rv) h)))
          + (μ v * (rE μ Rv v) ^ (-α))
            * ((screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                  [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h))
                + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                  [Tlaw μ (PMF.pure 3) v0 h]
                  (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h)))
              * (1 + ENNReal.ofReal α
                  * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
                    + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                      (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h))))) :=
        ENNReal.tsum_le_tsum hcell
    _ = (∑' v, if Rv v v0 then 0 else μ v * (rE μ Rv v) ^ (-α))
          * (1 + ENNReal.ofReal α
              * PhiDres α (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 3 h)
                  (SquareRel (fullSim (labRel Rv) h)))
        + (∑' v, μ v * (rE μ Rv v) ^ (-α))
          * ((screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                [Tlaw μ (PMF.pure 3) v0 h]
                (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
              + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
                [Tlaw μ (PMF.pure 3) v0 h]
                (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))
            * (1 + ENNReal.ofReal α
                * (PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                    (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
                  + PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
                    (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h)))) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]

/-- **The fresh-source zero-mass row for `ν = δ₃`** (`sec:rows`,
zero-mass outputs, fresh source toward the forced member): the reversed
dead mass of the forced law under the height-`(h+1)` fresh law is the far
root mass plus, at near roots, the pair-level dead mass, which
Hall-factorizes into the surviving `(Z₂ ↛ T)` zero mass; the diagonal
unit-tilt screens vanish by `thm:pruning`. -/
theorem delta3_zTZ_row (hrefl : ∀ v, Rv v v) (h : ℕ) :
    zMass (Tlaw μ (PMF.pure 3) v0 (h + 1)) (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
        (fullSim (labRel Rv) (h + 1))
      ≤ (∑' v, if Rv v v0 then 0 else μ v)
        + zMass (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
            (fullSim (labRel Rv) h) := by
  have hR0refl : ∀ x : FullLab (V × ℕ) h, fullSim (labRel Rv) h x x :=
    fullSim_refl (labRel Rv) (fun s => hrefl s.1) h
  -- the pair-level dead mass Hall-factorizes into the surviving screen
  have hpair : (∑' xp, Xi μ (PMF.pure 3) v0 3 h xp
        * (if rE (Xi μ (PMF.pure 3) v0 2 h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0))
      ≤ zMass (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
          (fullSim (labRel Rv) h) := by
    rw [Xi_three μ (PMF.pure 3) v0 h,
      Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h]
    refine le_trans (deadMass_factorize (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)) (le_of_eq ?_)
    rw [screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
        [Tlaw μ (PMF.pure 3) v0 h, Tlaw μ (PMF.pure 3) v0 h] (fun _ => 1)
        (by simp) hR0refl,
      screenE_self_mem (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
        [Tlaw μ (PMF.pure 3) v0 h] (fun _ => 1) (by simp) hR0refl,
      mul_zero, add_zero, add_zero, add_zero,
      screenE_pair_self (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
        (Tlaw μ (PMF.pure 3) v0 h) (fun _ => 1),
      screenE_one_eq_zMass (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
        (Tlaw μ (PMF.pure 3) v0 h)]
  -- the per-root cell bound
  have hcell : ∀ v : V,
      μ v * (∑' x, muM (varyK μ (PMF.pure 3) v0) (v, 3) (h + 1) x
          * (if rE (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
                (fullSim (labRel Rv) (h + 1)) x = 0 then 1 else 0))
        ≤ (if Rv v v0 then 0 else μ v)
          + μ v * zMass (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
              (fullSim (labRel Rv) h) := by
    intro v
    rw [zMass_Zlaw_succ Rv μ (PMF.pure 3) v0 v 3 2 h]
    by_cases hv : Rv v v0
    · rw [if_pos hv, if_pos hv, zero_add]
      exact mul_le_mul_right hpair _
    · rw [if_neg hv, if_neg hv, mul_one]
      exact le_self_add
  -- sum the cell bounds over the fresh root
  calc zMass (Tlaw μ (PMF.pure 3) v0 (h + 1))
        (Zlaw μ (PMF.pure 3) v0 2 (h + 1)) (fullSim (labRel Rv) (h + 1))
      = ∑' v, μ v * (∑' x, muM (varyK μ (PMF.pure 3) v0) (v, 3) (h + 1) x
          * (if rE (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
                (fullSim (labRel Rv) (h + 1)) x = 0 then 1 else 0)) := by
        rw [show Tlaw μ (PMF.pure 3) v0 (h + 1)
            = (freshQ μ (PMF.pure 3)).bind
                (fun s => muM (varyK μ (PMF.pure 3) v0) s (h + 1)) from rfl,
          zMass_eq_tsum, tsum_bind_mul]
        exact tsum_freshQ_pure3 μ (fun s =>
          ∑' x, muM (varyK μ (PMF.pure 3) v0) s (h + 1) x
            * (if rE (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
                  (fullSim (labRel Rv) (h + 1)) x = 0 then 1 else 0))
    _ ≤ ∑' v, ((if Rv v v0 then 0 else μ v)
          + μ v * zMass (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
              (fullSim (labRel Rv) h)) :=
        ENNReal.tsum_le_tsum hcell
    _ = (∑' v, if Rv v v0 then 0 else μ v)
        + zMass (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
            (fullSim (labRel Rv) h) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end GraphMarkovMatching
