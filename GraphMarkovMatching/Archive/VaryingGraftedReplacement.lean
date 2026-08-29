/-
Literal two-stage replacement-cylinder probabilities for the grafted 11/13
templates and their direct Hall estimates.
-/
import GraphMarkovMatching.Archive.VaryingGraftedCounters

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- The literal two-stage random choice used by a grafted replacement:
first the common root counter, then the label/counter state at the designated
fresh leaf. -/
noncomputable def twoStageCounterChoice {V : Type} (μ : PMF V)
    (ν : PMF ℕ) : PMF (ℕ × (V × ℕ)) :=
  prodPMF ν (freshQ μ ν)

@[simp] theorem twoStageCounterChoice_apply {V : Type} (μ : PMF V)
    (ν : PMF ℕ) (r : ℕ) (v : V) (k : ℕ) :
    twoStageCounterChoice μ ν (r, (v, k)) = ν r * μ v * ν k := by
  simp [twoStageCounterChoice, freshQ, prodPMF_apply]
  ring

def elevenReplacementChoice {V : Type} (v0 : V) : ℕ × (V × ℕ) :=
  (7, (v0, 5))

def thirteenReplacementChoice {V : Type} (v0 : V) : ℕ × (V × ℕ) :=
  (9, (v0, 5))

@[simp] theorem elevenReplacementChoice_mass {V : Type} (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) :
    twoStageCounterChoice μ ν (elevenReplacementChoice v0)
      = replacementMass (ν 7) (μ v0) (ν 5) := by
  simp [elevenReplacementChoice, replacementMass]

@[simp] theorem thirteenReplacementChoice_mass {V : Type} (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) :
    twoStageCounterChoice μ ν (thirteenReplacementChoice v0)
      = replacementMass (ν 9) (μ v0) (ν 5) := by
  simp [thirteenReplacementChoice, replacementMass]

theorem elevenReplacementChoice_mass_half_lower {V : Type}
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) (hhalf : 2⁻¹ ≤ (μ v0 : ℝ≥0∞)) :
    2⁻¹ * ((ν 7 : ℝ≥0∞) * ν 5)
      ≤ twoStageCounterChoice μ ν (elevenReplacementChoice v0) := by
  rw [elevenReplacementChoice_mass]
  exact replacementMass_half_lower hhalf

theorem thirteenReplacementChoice_mass_half_lower {V : Type}
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) (hhalf : 2⁻¹ ≤ (μ v0 : ℝ≥0∞)) :
    2⁻¹ * ((ν 9 : ℝ≥0∞) * ν 5)
      ≤ twoStageCounterChoice μ ν (thirteenReplacementChoice v0) := by
  rw [thirteenReplacementChoice_mass]
  exact replacementMass_half_lower hhalf

section ConcreteHall

variable {V X : Type}

/-- The literal `7`-then-`5` cylinder is a component of the two-stage target
mixture with exactly the advertised mass. -/
theorem elevenReplacement_minorization (μ : PMF V) (ν : PMF ℕ) (v0 : V)
    (f : (ℕ × (V × ℕ)) → PMF X) (R : X → X → Prop) (x : X) :
    replacementMass (ν 7) (μ v0) (ν 5) *
        rE (f (elevenReplacementChoice v0)) R x
      ≤ rE ((twoStageCounterChoice μ ν).bind f) R x := by
  simpa using mul_rE_le_rE_bind (twoStageCounterChoice μ ν) f R x
    (elevenReplacementChoice v0)

/-- The literal `9`-then-`5` cylinder gives the reverse replacement. -/
theorem thirteenReplacement_minorization (μ : PMF V) (ν : PMF ℕ) (v0 : V)
    (f : (ℕ × (V × ℕ)) → PMF X) (R : X → X → Prop) (x : X) :
    replacementMass (ν 9) (μ v0) (ν 5) *
        rE (f (thirteenReplacementChoice v0)) R x
      ≤ rE ((twoStageCounterChoice μ ν).bind f) R x := by
  simpa using mul_rE_le_rE_bind (twoStageCounterChoice μ ν) f R x
    (thirteenReplacementChoice v0)

/-- **Concrete grafted-11 Hall bound.**  `ρ11` may carry the left recursive
frontier laws and the replacement component the right recursive frontier
laws.  The only semantic input is positivity of the component degree on the
charged source support; the target minorization and its coefficient are now
the literal `7`-then-`5` cylinder rather than an abstract premise. -/
theorem rare_elevenReplacement_PhiDres_le {α : ℝ} (hα : 1 ≤ α)
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) (ρ11 : PMF X)
    (f : (ℕ × (V × ℕ)) → PMF X) (R : X → X → Prop)
    {ε c : ℝ≥0∞}
    (hp : replacementMass (ν 7) (μ v0) (ν 5) ≠ 0)
    (hsmall : ε ≤ c * (replacementMass (ν 7) (μ v0) (ν 5)) ^ α)
    (hsupp : ∀ x, ρ11 x ≠ 0 →
      rE (f (elevenReplacementChoice v0)) R x ≠ 0) :
    ε * PhiDres α ρ11 ((twoStageCounterChoice μ ν).bind f) R
      ≤ c * (1 + ENNReal.ofReal α *
        PhiDres α ρ11 (f (elevenReplacementChoice v0)) R) := by
  exact rare_mul_PhiDres_le_of_replacement_component hα ρ11
    (f (elevenReplacementChoice v0)) ((twoStageCounterChoice μ ν).bind f) R
    hp (by rw [← elevenReplacementChoice_mass μ ν v0]
           exact PMF.apply_ne_top _ _) hsmall hsupp
    (elevenReplacement_minorization μ ν v0 f R)

/-- The reverse-orientation `13` bound. -/
theorem rare_thirteenReplacement_PhiDres_le {α : ℝ} (hα : 1 ≤ α)
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) (ρ13 : PMF X)
    (f : (ℕ × (V × ℕ)) → PMF X) (R : X → X → Prop)
    {ε c : ℝ≥0∞}
    (hp : replacementMass (ν 9) (μ v0) (ν 5) ≠ 0)
    (hsmall : ε ≤ c * (replacementMass (ν 9) (μ v0) (ν 5)) ^ α)
    (hsupp : ∀ x, ρ13 x ≠ 0 →
      rE (f (thirteenReplacementChoice v0)) R x ≠ 0) :
    ε * PhiDres α ρ13 ((twoStageCounterChoice μ ν).bind f) R
      ≤ c * (1 + ENNReal.ofReal α *
        PhiDres α ρ13 (f (thirteenReplacementChoice v0)) R) := by
  exact rare_mul_PhiDres_le_of_replacement_component hα ρ13
    (f (thirteenReplacementChoice v0)) ((twoStageCounterChoice μ ν).bind f) R
    hp (by rw [← thirteenReplacementChoice_mass μ ν v0]
           exact PMF.apply_ne_top _ _) hsmall hsupp
    (thirteenReplacement_minorization μ ν v0 f R)

/-- Under `μ(v0) ≥ 1/2`, the simpler weight-only smallness condition implies
the exact eleven-cylinder condition. -/
theorem eleven_weight_smallness_implies_replacement {α : ℝ} (hα : 0 ≤ α)
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) {ε c : ℝ≥0∞}
    (hhalf : 2⁻¹ ≤ (μ v0 : ℝ≥0∞))
    (hsmall : ε ≤ c * (2⁻¹ * ((ν 7 : ℝ≥0∞) * ν 5)) ^ α) :
    ε ≤ c * (replacementMass (ν 7) (μ v0) (ν 5)) ^ α := by
  refine hsmall.trans (mul_le_mul_right ?_ c)
  exact ENNReal.rpow_le_rpow (replacementMass_half_lower hhalf) hα

/-- The corresponding weight-only implication for the thirteen cylinder. -/
theorem thirteen_weight_smallness_implies_replacement {α : ℝ} (hα : 0 ≤ α)
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) {ε c : ℝ≥0∞}
    (hhalf : 2⁻¹ ≤ (μ v0 : ℝ≥0∞))
    (hsmall : ε ≤ c * (2⁻¹ * ((ν 9 : ℝ≥0∞) * ν 5)) ^ α) :
    ε ≤ c * (replacementMass (ν 9) (μ v0) (ν 5)) ^ α := by
  refine hsmall.trans (mul_le_mul_right ?_ c)
  exact ENNReal.rpow_le_rpow (replacementMass_half_lower hhalf) hα

end ConcreteHall

end GraphMarkovMatching
