/-
Shared interface of the general-ν assembly
(`arbitrary_offspring_matching.tex`, `sec:rows` for arbitrary
finitely supported offspring laws): the ordinary coordinates over the
formal grammar, elementary zero-list calculus for screens, and the
pointwise mixture-tilt conversion that replaces a fresh normalization
by charged component normalizations.

* `interpPhi`: the ordinary coordinates: restricted potentials between
  interpreted formal targets;
* `screenE_congr_mem` / `screenE_le_of_subset`: screens depend on the
  zero list only through membership, and grow when the list shrinks;
* `WresD_XiBar_le_sum`: the restricted inverse degree of the fresh
  mixture is pointwise below the charged sum of component inverse
  degrees weighted by `ν_j^{-α}` (the `ν_*^{-5/2}` insertion of
  `thm:mixture-tilt`, in pointwise form).
-/
import GraphMarkovMatching.Grammar.Interp
import GraphMarkovMatching.Potential.ZeroInterface

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (ν : PMF ℕ) (v0 : V)

/-- The ordinary coordinates of the general ledger: restricted
potentials between interpreted formal targets. -/
noncomputable def interpPhi (h : ℕ) (p : Tgt × Tgt) : ℝ≥0∞ :=
  PhiDres α (interpT μ ν v0 h p.1) (interpT μ ν v0 h p.2)
    (fullSim (labRel Rv) h)

/-- Screens depend on the zero list only through membership. -/
lemma screenE_congr_mem {X : Type} (ρs : PMF X) (R : X → X → Prop)
    {zs₁ zs₂ : List (PMF X)} (hmem : ∀ ρ, ρ ∈ zs₁ ↔ ρ ∈ zs₂)
    (g : X → ℝ≥0∞) :
    screenE ρs R zs₁ g = screenE ρs R zs₂ g := by
  unfold screenE
  refine tsum_congr fun x => ?_
  have hind : screenInd R zs₁ x = screenInd R zs₂ x := by
    unfold screenInd
    have hiff : (∀ ρ ∈ zs₁, rE ρ R x = 0) ↔ ∀ ρ ∈ zs₂, rE ρ R x = 0 :=
      ⟨fun h ρ hρ => h ρ ((hmem ρ).mpr hρ),
        fun h ρ hρ => h ρ ((hmem ρ).mp hρ)⟩
    exact if_congr hiff rfl rfl
  rw [hind]

/-- Enlarging the zero list shrinks the screen. -/
lemma screenE_le_of_subset {X : Type} (ρs : PMF X) (R : X → X → Prop)
    {zs₁ zs₂ : List (PMF X)} (hsub : ∀ ρ ∈ zs₁, ρ ∈ zs₂)
    (g : X → ℝ≥0∞) :
    screenE ρs R zs₂ g ≤ screenE ρs R zs₁ g := by
  refine ENNReal.tsum_le_tsum fun x => ?_
  refine mul_le_mul_left (mul_le_mul_right ?_ _) _
  unfold screenInd
  by_cases h2 : ∀ ρ ∈ zs₂, rE ρ R x = 0
  · rw [if_pos h2, if_pos fun ρ hρ => h2 ρ (hsub ρ hρ)]
  · rw [if_neg h2]
    exact zero_le

/-- **The pointwise mixture-tilt conversion**: the restricted inverse
degree of the fresh mixture is below the charged sum of component
inverse degrees, each weighted by `ν_j^{-α}`.  On the mixture's dead
set both sides vanish; on the live set some charged component is
alive, and the minorization `ν_j·r_j ≤ r̄` inverts. -/
lemma WresD_XiBar_le_sum (hα0 : 0 ≤ α) (h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    WresD α (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp
      ≤ ∑' j, (if (ν j : ℝ≥0∞) = 0 then 0 else
          (ν j : ℝ≥0∞) ^ (-α)
            * WresD α (Xi μ ν v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp) := by
  by_cases hbar : rE (XiBar μ ν v0 h)
      (SquareRel (fullSim (labRel Rv) h)) xp = 0
  · rw [WresD, if_pos hbar]
    exact zero_le
  · have hnall : ¬ ∀ a, (ν a : ℝ≥0∞) = 0
        ∨ rE (Xi μ ν v0 a h) (SquareRel (fullSim (labRel Rv) h)) xp = 0 :=
      fun hall => hbar ((rE_bind_eq_zero_iff ν (fun k => Xi μ ν v0 k h)
        (SquareRel (fullSim (labRel Rv) h)) xp).mpr hall)
    push Not at hnall
    obtain ⟨j, hν, hXi⟩ := hnall
    have hmin : (ν j : ℝ≥0∞)
        * rE (Xi μ ν v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp
        ≤ rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp :=
      mul_rE_le_rE_bind ν (fun k => Xi μ ν v0 k h)
        (SquareRel (fullSim (labRel Rv) h)) xp j
    have hstep : WresD α (XiBar μ ν v0 h)
        (SquareRel (fullSim (labRel Rv) h)) xp
        ≤ (ν j : ℝ≥0∞) ^ (-α)
          * WresD α (Xi μ ν v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp := by
      rw [← rE_rpow_neg_eq_WresD (XiBar μ ν v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp hbar,
        ← rE_rpow_neg_eq_WresD (Xi μ ν v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) xp hXi,
        ← ENNReal.mul_rpow_of_ne_zero hν hXi (-α)]
      exact rpow_neg_antitone hα0 hmin
    refine le_trans hstep ?_
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum j)
    rw [if_neg hν]

end GraphMarkovMatching
