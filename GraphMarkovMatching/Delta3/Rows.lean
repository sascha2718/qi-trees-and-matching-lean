/-
The remaining rows of the `ν = δ₃` transfer step
(`arbitrary_offspring_matching.tex`, `sec:rows` at
`ν = δ₃`): the forced-forced, forced-fresh and fresh-forced state pairs
accompanying the principal row `delta3_Tlaw_Tlaw_step`.

For `ν = δ₃` only the counters `k ∈ {2, 3}` occur, with product shapes
`Ξ₂ = T ⊗ T` and `Ξ₃ = Z₂ ⊗ T`, and the mixture collapses (`Ξ̄ = Ξ₃`).
Every row is a single square cell fed into the certified ledger row
`PhiDres_square_le`:

* `delta3_Zlaw_Zlaw_step_22/_23/_32/_33`: the four forced-forced rows,
  exact reductions through `PhiDres_Zlaw_Zlaw_succ`;
* `delta3_Zlaw_Tlaw_step_2/_3`: the forced-fresh rows through the split
  bound `PhiDres_Zlaw_Tlaw_succ` at the root `v0`;
* `delta3_Tlaw_Zlaw_step_2/_3`: the fresh-forced rows through the
  root-mass bound `PhiDres_Tlaw_Zlaw_succ` and the collapsed mixture.
-/
import GraphMarkovMatching.Delta3.Step

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-! ### The forced-forced rows -/

/-- The forced-forced row `(Z₂ → Z₂)`: one square cell
`(T⊗T → T⊗T)` with its resolved screens. -/
theorem delta3_Zlaw_Zlaw_step_22 {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (hrefl : Rv v0 v0) (h : ℕ)
    (M Z : ℝ≥0∞)
    (_hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (_hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (_hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (_hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (_hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (_hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
        (Zlaw μ (PMF.pure 3) v0 2 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
  rw [PhiDres_Zlaw_Zlaw_succ α Rv μ (PMF.pure 3) v0 hrefl 2 2 h,
    Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h]
  exact PhiDres_square_le hα hδ hL0 hL hK0 hK
    (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
    (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
    (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
    M Z hTT hTT hTT hTT hTT hTT hTT hTT hzTT hzTT hzTT hzTT

/-- The forced-forced row `(Z₂ → Z₃)`: one square cell
`(T⊗T → Z₂⊗T)` with its resolved screens. -/
theorem delta3_Zlaw_Zlaw_step_23 {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (hrefl : Rv v0 v0) (h : ℕ)
    (M Z : ℝ≥0∞)
    (_hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (_hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (_hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
        (Zlaw μ (PMF.pure 3) v0 3 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
  rw [PhiDres_Zlaw_Zlaw_succ α Rv μ (PMF.pure 3) v0 hrefl 2 3 h,
    Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h,
    Xi_three μ (PMF.pure 3) v0 h]
  exact PhiDres_square_le hα hδ hL0 hL hK0 hK
    (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
    (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
    (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
    M Z hTZ hTT hTZ hTT hZT hZT hTT hTT hzZT hzZT hzTT hzTT

/-- The forced-forced row `(Z₃ → Z₂)`: one square cell
`(Z₂⊗T → T⊗T)` with its resolved screens. -/
theorem delta3_Zlaw_Zlaw_step_32 {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (hrefl : Rv v0 v0) (h : ℕ)
    (M Z : ℝ≥0∞)
    (_hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (_hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (_hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Zlaw μ (PMF.pure 3) v0 3 (h + 1))
        (Zlaw μ (PMF.pure 3) v0 2 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
  rw [PhiDres_Zlaw_Zlaw_succ α Rv μ (PMF.pure 3) v0 hrefl 3 2 h,
    Xi_three μ (PMF.pure 3) v0 h,
    Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h]
  exact PhiDres_square_le hα hδ hL0 hL hK0 hK
    (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
    (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
    (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
    M Z hZT hZT hTT hTT hTZ hTT hTZ hTT hzTZ hzTT hzTZ hzTT

/-- The forced-forced row `(Z₃ → Z₃)`: one square cell
`(Z₂⊗T → Z₂⊗T)` with its resolved screens. -/
theorem delta3_Zlaw_Zlaw_step_33 {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (hrefl : Rv v0 v0) (h : ℕ)
    (M Z : ℝ≥0∞)
    (hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Zlaw μ (PMF.pure 3) v0 3 (h + 1))
        (Zlaw μ (PMF.pure 3) v0 3 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
  rw [PhiDres_Zlaw_Zlaw_succ α Rv μ (PMF.pure 3) v0 hrefl 3 3 h,
    Xi_three μ (PMF.pure 3) v0 h]
  exact PhiDres_square_le hα hδ hL0 hL hK0 hK
    (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
    (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
    (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
    M Z hZZ hZT hTZ hTT hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT

/-! ### The forced-fresh rows -/

/-- The forced-fresh row `(Z₂ → F)`: the split bound at the root `v0`,
the square cell `(T⊗T → Z₂⊗T)` toward the collapsed mixture, and the
quadratic cross term. -/
theorem delta3_Zlaw_Tlaw_step_2 {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (h : ℕ) (M Z : ℝ≥0∞)
    (_hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (_hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (_hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Zlaw μ (PMF.pure 3) v0 2 (h + 1))
        (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v0)
        + (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
          + ENNReal.ofReal
              (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
          + ENNReal.ofReal (2 * (1 + δ)) * Z
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
            * (1 + ENNReal.ofReal α * M))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v0)
            * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
              + ENNReal.ofReal
                  (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
                * M ^ 2
              + ENNReal.ofReal (2 * (1 + δ)) * Z
              + (screenE (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) [Zlaw μ (PMF.pure 3) v0 2 h]
                    (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                    (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) [Zlaw μ (PMF.pure 3) v0 2 h]
                    (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                    (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h)))
                * (1 + ENNReal.ofReal α * M))) := by
  have hsq : PhiDres α (Xi μ (PMF.pure 3) v0 2 h) (Xi μ (PMF.pure 3) v0 3 h)
      (SquareRel (fullSim (labRel Rv) h))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
    rw [Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h,
      Xi_three μ (PMF.pure 3) v0 h]
    exact PhiDres_square_le hα hδ hL0 hL hK0 hK
      (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h)
      (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
      M Z hTZ hTT hTZ hTT hZT hZT hTT hTT hzZT hzZT hzTT hzTT
  refine le_trans (PhiDres_Zlaw_Tlaw_succ α Rv μ (PMF.pure 3) v0 hα 2 h) ?_
  rw [XiBar_delta3 μ v0 h]
  exact add_le_add (add_le_add le_rfl hsq)
    (mul_le_mul_right (mul_le_mul_right hsq _) _)

/-- The forced-fresh row `(Z₃ → F)`: the split bound at the root `v0`,
the square cell `(Z₂⊗T → Z₂⊗T)` toward the collapsed mixture, and the
quadratic cross term. -/
theorem delta3_Zlaw_Tlaw_step_3 {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (h : ℕ) (M Z : ℝ≥0∞)
    (hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Zlaw μ (PMF.pure 3) v0 3 (h + 1))
        (Tlaw μ (PMF.pure 3) v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v0)
        + (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
          + ENNReal.ofReal
              (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
          + ENNReal.ofReal (2 * (1 + δ)) * Z
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
            * (1 + ENNReal.ofReal α * M))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v0)
            * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
              + ENNReal.ofReal
                  (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
                * M ^ 2
              + ENNReal.ofReal (2 * (1 + δ)) * Z
              + (screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) [Zlaw μ (PMF.pure 3) v0 2 h]
                    (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Zlaw μ (PMF.pure 3) v0 2 h)
                    (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                    (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) [Zlaw μ (PMF.pure 3) v0 2 h]
                    (WresD α (Tlaw μ (PMF.pure 3) v0 h)
                      (fullSim (labRel Rv) h))
                  + screenE (Tlaw μ (PMF.pure 3) v0 h)
                    (fullSim (labRel Rv) h) [Tlaw μ (PMF.pure 3) v0 h]
                    (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                      (fullSim (labRel Rv) h)))
                * (1 + ENNReal.ofReal α * M))) := by
  have hsq : PhiDres α (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 3 h)
      (SquareRel (fullSim (labRel Rv) h))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
    rw [Xi_three μ (PMF.pure 3) v0 h]
    exact PhiDres_square_le hα hδ hL0 hL hK0 hK
      (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h)
      (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
      M Z hZZ hZT hTZ hTT hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT
  refine le_trans (PhiDres_Zlaw_Tlaw_succ α Rv μ (PMF.pure 3) v0 hα 3 h) ?_
  rw [XiBar_delta3 μ v0 h]
  exact add_le_add (add_le_add le_rfl hsq)
    (mul_le_mul_right (mul_le_mul_right hsq _) _)

/-! ### The fresh-forced rows -/

/-- The fresh-forced row `(F → Z₂)`: the cascade mixture collapses to the
counter-`3` cell, so the row is the square cell `(Z₂⊗T → T⊗T)` with its
resolved screens. -/
theorem delta3_Tlaw_Zlaw_step_2 {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (h : ℕ) (M Z : ℝ≥0∞)
    (_hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (_hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (_hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Tlaw μ (PMF.pure 3) v0 (h + 1))
        (Zlaw μ (PMF.pure 3) v0 2 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
  have hsum : (∑' k, (PMF.pure 3 : PMF ℕ) k
        * PhiDres α (Xi μ (PMF.pure 3) v0 k h) (Xi μ (PMF.pure 3) v0 2 h)
            (SquareRel (fullSim (labRel Rv) h)))
      = PhiDres α (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 2 h)
          (SquareRel (fullSim (labRel Rv) h)) := by
    rw [tsum_pure_mul 3 (fun k => PhiDres α (Xi μ (PMF.pure 3) v0 k h)
      (Xi μ (PMF.pure 3) v0 2 h) (SquareRel (fullSim (labRel Rv) h)))]
  refine le_trans (PhiDres_Tlaw_Zlaw_succ α Rv μ (PMF.pure 3) v0 2 h) ?_
  rw [hsum, Xi_three μ (PMF.pure 3) v0 h,
    Xi_of_le_two μ (PMF.pure 3) v0 (le_refl 2) h]
  exact PhiDres_square_le hα hδ hL0 hL hK0 hK
    (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
    (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
    (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
    M Z hZT hZT hTT hTT hTZ hTT hTZ hTT hzTZ hzTT hzTZ hzTT

/-- The fresh-forced row `(F → Z₃)`: the cascade mixture collapses to the
counter-`3` cell, so the row is the square cell `(Z₂⊗T → Z₂⊗T)` with its
resolved screens. -/
theorem delta3_Tlaw_Zlaw_step_3 {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRvsymm : ∀ a b, Rv a b → Rv b a) (h : ℕ) (M Z : ℝ≥0∞)
    (hZZ : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hZT : PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hTZ : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ M)
    (hTT : PhiDres α (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ M)
    (hzZZ : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzZT : zMass (Zlaw μ (PMF.pure 3) v0 2 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTZ : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h) ≤ Z)
    (hzTT : zMass (Tlaw μ (PMF.pure 3) v0 h)
      (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) ≤ Z) :
    PhiDres α (Tlaw μ (PMF.pure 3) v0 (h + 1))
        (Zlaw μ (PMF.pure 3) v0 3 (h + 1)) (fullSim (labRel Rv) (h + 1))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Zlaw μ (PMF.pure 3) v0 2 h]
              (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h))
            + screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
              [Tlaw μ (PMF.pure 3) v0 h]
              (WresD α (Zlaw μ (PMF.pure 3) v0 2 h)
                (fullSim (labRel Rv) h)))
          * (1 + ENNReal.ofReal α * M) := by
  have hsum : (∑' k, (PMF.pure 3 : PMF ℕ) k
        * PhiDres α (Xi μ (PMF.pure 3) v0 k h) (Xi μ (PMF.pure 3) v0 3 h)
            (SquareRel (fullSim (labRel Rv) h)))
      = PhiDres α (Xi μ (PMF.pure 3) v0 3 h) (Xi μ (PMF.pure 3) v0 3 h)
          (SquareRel (fullSim (labRel Rv) h)) := by
    rw [tsum_pure_mul 3 (fun k => PhiDres α (Xi μ (PMF.pure 3) v0 k h)
      (Xi μ (PMF.pure 3) v0 3 h) (SquareRel (fullSim (labRel Rv) h)))]
  refine le_trans (PhiDres_Tlaw_Zlaw_succ α Rv μ (PMF.pure 3) v0 3 h) ?_
  rw [hsum, Xi_three μ (PMF.pure 3) v0 h]
  exact PhiDres_square_le hα hδ hL0 hL hK0 hK
    (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
    (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
    (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (fun a b hab => hRvsymm a.1 b.1 hab) h)
    M Z hZZ hZT hTZ hTT hZZ hZT hTZ hTT hzZZ hzZT hzTZ hzTT

end GraphMarkovMatching
