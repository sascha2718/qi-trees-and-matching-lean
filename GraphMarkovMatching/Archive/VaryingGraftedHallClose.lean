/-
Concrete recursive Hall closure for the grafted 11/13 counters.

The source exceptional macro is compared with the literal common two-stage
replacement cylinder.  A finite product estimate discharges support
positivity and bounds all recursive frontier coordinates.  Consequently the
rare row pays exactly one inverse replacement probability and no Green or
resolvent denominator.
-/
import GraphMarkovMatching.Archive.VaryingGraftedProduct

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

noncomputable def graftedMacroLaw {V X : Type} (μ : PMF V) (ρ : PMF X)
    (n : ℕ) : PMF (V × ProductPower X n) :=
  prodPMF μ (iidProductPower ρ n)

def graftedMacroRel {V X : Type} (Rv : V → V → Prop) (R : X → X → Prop)
    (n : ℕ) : (V × ProductPower X n) → (V × ProductPower X n) → Prop :=
  ProdRel Rv (productPowerRel R n)

noncomputable def graftedMacroBound (α : ℝ) (η M : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  η + iteratedProductBound α M n +
    ENNReal.ofReal (2 * α) * (η * iteratedProductBound α M n)

theorem PhiD_graftedMacroLaw_le {V X : Type} {α : ℝ} (hα : 1 ≤ α)
    (μs μt : PMF V) (ρs ρt : PMF X)
    (Rv : V → V → Prop) (R : X → X → Prop) (η M : ℝ≥0∞)
    (hη : PhiD α μs μt Rv ≤ η) (hM : PhiD α ρs ρt R ≤ M) (n : ℕ) :
    PhiD α (graftedMacroLaw μs ρs n) (graftedMacroLaw μt ρt n)
        (graftedMacroRel Rv R n) ≤ graftedMacroBound α η M n := by
  calc
    PhiD α (graftedMacroLaw μs ρs n) (graftedMacroLaw μt ρt n)
        (graftedMacroRel Rv R n)
      ≤ PhiD α μs μt Rv +
          PhiD α (iidProductPower ρs n) (iidProductPower ρt n)
            (productPowerRel R n) +
        ENNReal.ofReal (2 * α) *
          (PhiD α μs μt Rv *
            PhiD α (iidProductPower ρs n) (iidProductPower ρt n)
              (productPowerRel R n)) := by
          exact PhiD_prodPMF_le hα μs μt
            (iidProductPower ρs n) (iidProductPower ρt n)
            Rv (productPowerRel R n)
    _ ≤ η + iteratedProductBound α M n +
        ENNReal.ofReal (2 * α) * (η * iteratedProductBound α M n) := by
      have hn := PhiD_iidProductPower_le hα ρs ρt R M hM n
      gcongr
    _ = graftedMacroBound α η M n := rfl

lemma graftedMacroBound_ne_top {α : ℝ} {η M : ℝ≥0∞}
    (hη : η ≠ ⊤) (hM : M ≠ ⊤) (n : ℕ) :
    graftedMacroBound α η M n ≠ ⊤ := by
  dsimp [graftedMacroBound]
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.add_ne_top.2 ⟨hη, iteratedProductBound_ne_top hM n⟩,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hη (iteratedProductBound_ne_top hM n))⟩

theorem graftedMacroLaw_support_positive {V X : Type} {α : ℝ}
    (hα : 1 ≤ α) (μs μt : PMF V) (ρs ρt : PMF X)
    (Rv : V → V → Prop) (R : X → X → Prop) (η M : ℝ≥0∞)
    (hηtop : η ≠ ⊤) (hMtop : M ≠ ⊤)
    (hη : PhiD α μs μt Rv ≤ η) (hM : PhiD α ρs ρt R ≤ M) (n : ℕ) :
    ∀ x, graftedMacroLaw μs ρs n x ≠ 0 →
      rE (graftedMacroLaw μt ρt n) (graftedMacroRel Rv R n) x ≠ 0 := by
  have hprod := PhiD_graftedMacroLaw_le hα μs μt ρs ρt Rv R η M hη hM n
  have hfin : PhiD α (graftedMacroLaw μs ρs n)
      (graftedMacroLaw μt ρt n) (graftedMacroRel Rv R n) ≠ ⊤ :=
    ne_top_of_le_ne_top (graftedMacroBound_ne_top hηtop hMtop n) hprod
  exact fun _ hx => rE_ne_zero_of_PhiD_ne_top hfin hx

section ConcreteMacroHall

variable {V X : Type}

/-- The complete direct Hall estimate for the grafted `11` macro.  Its
replacement is the literal `7`-then-`5` component and its recursive frontier
cost is the explicit eleven-fold product bound. -/
theorem rare_elevenGraftedMacro_PhiDres_le {α : ℝ} (hα : 1 ≤ α)
    (μ : PMF V) (νR : PMF ℕ) (v0 : V) (ρL ρR : PMF X)
    (Rv : V → V → Prop) (R : X → X → Prop)
    (f : (ℕ × (V × ℕ)) → PMF (V × ProductPower X 11))
    (η M : ℝ≥0∞) {ε c : ℝ≥0∞}
    (hηtop : η ≠ ⊤) (hMtop : M ≠ ⊤)
    (hη : PhiD α μ μ Rv ≤ η) (hM : PhiD α ρL ρR R ≤ M)
    (hp : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hsmall : ε ≤ c * (replacementMass (νR 7) (μ v0) (νR 5)) ^ α)
    (hcomponent : f (elevenReplacementChoice v0) = graftedMacroLaw μ ρR 11) :
    ε * PhiDres α (graftedMacroLaw μ ρL 11)
        ((twoStageCounterChoice μ νR).bind f) (graftedMacroRel Rv R 11)
      ≤ c * (1 + ENNReal.ofReal α * graftedMacroBound α η M 11) := by
  have hsupp : ∀ x, graftedMacroLaw μ ρL 11 x ≠ 0 →
      rE (f (elevenReplacementChoice v0)) (graftedMacroRel Rv R 11) x ≠ 0 := by
    rw [hcomponent]
    exact graftedMacroLaw_support_positive hα μ μ ρL ρR Rv R η M
      hηtop hMtop hη hM 11
  calc
    ε * PhiDres α (graftedMacroLaw μ ρL 11)
        ((twoStageCounterChoice μ νR).bind f) (graftedMacroRel Rv R 11)
      ≤ c * (1 + ENNReal.ofReal α *
          PhiDres α (graftedMacroLaw μ ρL 11)
            (f (elevenReplacementChoice v0)) (graftedMacroRel Rv R 11)) :=
        rare_elevenReplacement_PhiDres_le hα μ νR v0
          (graftedMacroLaw μ ρL 11) f (graftedMacroRel Rv R 11)
          hp hsmall hsupp
    _ ≤ c * (1 + ENNReal.ofReal α * graftedMacroBound α η M 11) := by
      rw [hcomponent]
      gcongr
      exact (PhiDres_le_PhiD α _ _ _).trans
        (PhiD_graftedMacroLaw_le hα μ μ ρL ρR Rv R η M hη hM 11)

/-- Reverse-orientation direct Hall estimate for the grafted `13` macro. -/
theorem rare_thirteenGraftedMacro_PhiDres_le {α : ℝ} (hα : 1 ≤ α)
    (μ : PMF V) (νL : PMF ℕ) (v0 : V) (ρL ρR : PMF X)
    (Rv : V → V → Prop) (R : X → X → Prop)
    (f : (ℕ × (V × ℕ)) → PMF (V × ProductPower X 13))
    (η M : ℝ≥0∞) {ε c : ℝ≥0∞}
    (hηtop : η ≠ ⊤) (hMtop : M ≠ ⊤)
    (hη : PhiD α μ μ Rv ≤ η) (hM : PhiD α ρR ρL R ≤ M)
    (hp : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (hsmall : ε ≤ c * (replacementMass (νL 9) (μ v0) (νL 5)) ^ α)
    (hcomponent : f (thirteenReplacementChoice v0) = graftedMacroLaw μ ρL 13) :
    ε * PhiDres α (graftedMacroLaw μ ρR 13)
        ((twoStageCounterChoice μ νL).bind f) (graftedMacroRel Rv R 13)
      ≤ c * (1 + ENNReal.ofReal α * graftedMacroBound α η M 13) := by
  have hsupp : ∀ x, graftedMacroLaw μ ρR 13 x ≠ 0 →
      rE (f (thirteenReplacementChoice v0)) (graftedMacroRel Rv R 13) x ≠ 0 := by
    rw [hcomponent]
    exact graftedMacroLaw_support_positive hα μ μ ρR ρL Rv R η M
      hηtop hMtop hη hM 13
  calc
    ε * PhiDres α (graftedMacroLaw μ ρR 13)
        ((twoStageCounterChoice μ νL).bind f) (graftedMacroRel Rv R 13)
      ≤ c * (1 + ENNReal.ofReal α *
          PhiDres α (graftedMacroLaw μ ρR 13)
            (f (thirteenReplacementChoice v0)) (graftedMacroRel Rv R 13)) :=
        rare_thirteenReplacement_PhiDres_le hα μ νL v0
          (graftedMacroLaw μ ρR 13) f (graftedMacroRel Rv R 13)
          hp hsmall hsupp
    _ ≤ c * (1 + ENNReal.ofReal α * graftedMacroBound α η M 13) := by
      rw [hcomponent]
      gcongr
      exact (PhiDres_le_PhiD α _ _ _).trans
        (PhiD_graftedMacroLaw_le hα μ μ ρR ρL Rv R η M hη hM 13)

/-- Weight-only form of the grafted `11` estimate.  Under `μ(v0) ≥ 1/2`,
the sufficient rare-mass condition is
`ε ≤ c (2⁻¹ νR(7) νR(5))^α`. -/
theorem rare_elevenGraftedMacro_PhiDres_le_of_half {α : ℝ} (hα : 1 ≤ α)
    (μ : PMF V) (νR : PMF ℕ) (v0 : V) (ρL ρR : PMF X)
    (Rv : V → V → Prop) (R : X → X → Prop)
    (f : (ℕ × (V × ℕ)) → PMF (V × ProductPower X 11))
    (η M : ℝ≥0∞) {ε c : ℝ≥0∞}
    (hηtop : η ≠ ⊤) (hMtop : M ≠ ⊤)
    (hη : PhiD α μ μ Rv ≤ η) (hM : PhiD α ρL ρR R ≤ M)
    (hhalf : 2⁻¹ ≤ (μ v0 : ℝ≥0∞))
    (hp : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hsmall : ε ≤ c * (2⁻¹ * ((νR 7 : ℝ≥0∞) * νR 5)) ^ α)
    (hcomponent : f (elevenReplacementChoice v0) = graftedMacroLaw μ ρR 11) :
    ε * PhiDres α (graftedMacroLaw μ ρL 11)
        ((twoStageCounterChoice μ νR).bind f) (graftedMacroRel Rv R 11)
      ≤ c * (1 + ENNReal.ofReal α * graftedMacroBound α η M 11) := by
  exact rare_elevenGraftedMacro_PhiDres_le hα μ νR v0 ρL ρR Rv R f η M
    hηtop hMtop hη hM hp
    (eleven_weight_smallness_implies_replacement (by linarith) μ νR v0
      hhalf hsmall)
    hcomponent

/-- Weight-only reverse-orientation form for the grafted `13` estimate. -/
theorem rare_thirteenGraftedMacro_PhiDres_le_of_half {α : ℝ} (hα : 1 ≤ α)
    (μ : PMF V) (νL : PMF ℕ) (v0 : V) (ρL ρR : PMF X)
    (Rv : V → V → Prop) (R : X → X → Prop)
    (f : (ℕ × (V × ℕ)) → PMF (V × ProductPower X 13))
    (η M : ℝ≥0∞) {ε c : ℝ≥0∞}
    (hηtop : η ≠ ⊤) (hMtop : M ≠ ⊤)
    (hη : PhiD α μ μ Rv ≤ η) (hM : PhiD α ρR ρL R ≤ M)
    (hhalf : 2⁻¹ ≤ (μ v0 : ℝ≥0∞))
    (hp : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (hsmall : ε ≤ c * (2⁻¹ * ((νL 9 : ℝ≥0∞) * νL 5)) ^ α)
    (hcomponent : f (thirteenReplacementChoice v0) = graftedMacroLaw μ ρL 13) :
    ε * PhiDres α (graftedMacroLaw μ ρR 13)
        ((twoStageCounterChoice μ νL).bind f) (graftedMacroRel Rv R 13)
      ≤ c * (1 + ENNReal.ofReal α * graftedMacroBound α η M 13) := by
  exact rare_thirteenGraftedMacro_PhiDres_le hα μ νL v0 ρL ρR Rv R f η M
    hηtop hMtop hη hM hp
    (thirteen_weight_smallness_implies_replacement (by linarith) μ νL v0
      hhalf hsmall)
    hcomponent

end ConcreteMacroHall

end GraphMarkovMatching
