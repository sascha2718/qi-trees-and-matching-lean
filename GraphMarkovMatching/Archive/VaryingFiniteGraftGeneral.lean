/-
Quantitative bookkeeping for a finite common offspring core with finitely
many graftable exceptional atoms.

This file deliberately separates the numerical Hall price of a graft from
the semantic fact that a proposed finite prefix tree is a valid,
level-synchronous replacement.  The latter is the finite certificate that a
concrete application must supply.  Once a cylinder floor `p x` is certified,
the exponent `5 / 2` bookkeeping below is completely general.
-/
import GraphMarkovMatching.Archive.VaryingGraftedFinal

namespace GraphMarkovMatching

open scoped ENNReal Classical BigOperators

/-! ### A ranked joint-termination certificate -/

/-- Primitive joint-termination data for a finite graft screen grammar.
Only common transitions must decrease the rank.  Exceptional transitions
are deliberately absent from this certificate: they may reset the rank,
but their Hall charge is handled by `twoSidedFiniteGraftLoad`. -/
structure RankedFiniteGraftScreens
    (ι : Type) [Fintype ι] where
  commonN : ι → ι → ℝ≥0∞
  rank : ι → ℕ
  steps : ℕ
  rank_lt_steps : ∀ i, rank i < steps
  common_decreases : ∀ i j, commonN i j ≠ 0 → rank j < rank i

/-- A supplied rank certificate makes the common-only screen block
nilpotent.  This is the formal content of “jointly terminating”. -/
theorem RankedFiniteGraftScreens.common_nilpotent
    {ι : Type} [Fintype ι] (cert : RankedFiniteGraftScreens ι) :
    ∀ x : ι → ℝ≥0∞,
      (mulVec cert.commonN)^[cert.steps] x = fun _ => 0 :=
  nilpotent_of_rank cert.commonN cert.rank cert.steps
    cert.common_decreases cert.rank_lt_steps

/-- The concrete tagged `11/13` grammar supplies an instance of the
abstract ranked certificate.  Its rank is the number of strictly reachable
live screens; acyclicity of the literal common transition graph makes this
rank decrease. -/
noncomputable def elevenThirteenRankedGraftScreens (CW : ℝ≥0∞) :
    RankedFiniteGraftScreens
      (Bool × {sc // sc ∈ graftLiveScreens}) where
  commonN := graftCommonN CW
  rank := reachRank (graftCommonN CW)
  steps := Fintype.card (Bool × {sc // sc ∈ graftLiveScreens})
  rank_lt_steps := reachRank_lt_card (graftCommonN_acyclic CW)
  common_decreases := fun _ _ h =>
    reachRank_lt_of_support (graftCommonN_acyclic CW) h

theorem elevenThirteenRankedGraftScreens_nilpotent (CW : ℝ≥0∞) :
    ∀ x : (Bool × {sc // sc ∈ graftLiveScreens}) → ℝ≥0∞,
      (mulVec (elevenThirteenRankedGraftScreens CW).commonN)^[
          (elevenThirteenRankedGraftScreens CW).steps] x = fun _ => 0 :=
  (elevenThirteenRankedGraftScreens CW).common_nilpotent

/-- A finite common-core/two-exceptional-set description of two offspring
laws.  The last two inequalities are the precise version of “common mass at
least `1 - zeta`”: since the laws are supported on the displayed disjoint
unions, the exceptional mass is at most `zeta` on each side. -/
def IsFiniteCommonExceptionalPair
    (nuL nuR : PMF ℕ) (S EL ER : Finset ℕ) (zeta : ℝ≥0∞) : Prop :=
  Disjoint S EL ∧ Disjoint S ER ∧
    (∀ k, (nuL k : ℝ≥0∞) ≠ 0 → k ∈ S ∪ EL) ∧
    (∀ k, (nuR k : ℝ≥0∞) ≠ 0 → k ∈ S ∪ ER) ∧
    (∀ k ∈ S, nuL k = nuR k) ∧
    (∑ k ∈ EL, (nuL k : ℝ≥0∞)) ≤ zeta ∧
    (∑ k ∈ ER, (nuR k : ℝ≥0∞)) ≤ zeta

/-- A convenient explicit lower bound for a graft cylinder.  `word` lists
the common offspring arities prescribed at its internal vertices and
`labelCount` is the number of prescribed graph labels.  Under
`mu v0 ≥ 1/2`, independence gives this product as a lower bound for the
cylinder probability. -/
noncomputable def finiteGraftCylinderFloor
    (commonWeight : ℕ → ℝ≥0∞) (labelCount : ℕ) (word : List ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞)⁻¹) ^ labelCount * (word.map commonWeight).prod

lemma finiteGraftCylinderFloor_ne_zero
    {commonWeight : ℕ → ℝ≥0∞} {labelCount : ℕ} {word : List ℕ}
    (hweight : ∀ k ∈ word, commonWeight k ≠ 0) :
    finiteGraftCylinderFloor commonWeight labelCount word ≠ 0 := by
  rw [finiteGraftCylinderFloor]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · induction word with
    | nil => simp
    | cons a word ih =>
        simp only [List.map_cons, List.prod_cons]
        apply mul_ne_zero
        · exact hweight a (by simp)
        · apply ih
          intro k hk
          exact hweight k (by simp [hk])

lemma finiteGraftCylinderFloor_ne_top
    {commonWeight : ℕ → ℝ≥0∞} {labelCount : ℕ} {word : List ℕ}
    (hweight : ∀ k ∈ word, commonWeight k ≠ ⊤) :
    finiteGraftCylinderFloor commonWeight labelCount word ≠ ⊤ := by
  rw [finiteGraftCylinderFloor]
  apply ENNReal.mul_ne_top
  · exact ENNReal.pow_ne_top (by norm_num)
  · induction word with
    | nil => simp
    | cons a word ih =>
        simp only [List.map_cons, List.prod_cons]
        apply ENNReal.mul_ne_top
        · exact hweight a (by simp)
        · apply ih
          intro k hk
          exact hweight k (by simp [hk])

/-- The inverse-cylinder Hall load of finitely many exceptional atoms. -/
noncomputable def finiteGraftLoad
    (nu : PMF ℕ) (E : Finset ℕ) (p : ℕ → ℝ≥0∞) (α : ℝ) : ℝ≥0∞ :=
  ∑ x ∈ E, (nu x : ℝ≥0∞) * p x ^ (-α)

/-- If every exceptional atom is cheaper than `c x` times the `α`-power
of its certified graft cylinder, its entire inverse-cylinder Hall load is at
most the sum of the budgets `c x`. -/
theorem finiteGraftLoad_le_budget
    {nu : PMF ℕ} {E : Finset ℕ} {p c : ℕ → ℝ≥0∞} {α : ℝ}
    (hp0 : ∀ x ∈ E, p x ≠ 0)
    (hpTop : ∀ x ∈ E, p x ≠ ⊤)
    (hprice : ∀ x ∈ E, (nu x : ℝ≥0∞) ≤ c x * p x ^ α) :
    finiteGraftLoad nu E p α ≤ ∑ x ∈ E, c x := by
  rw [finiteGraftLoad]
  exact Finset.sum_le_sum fun x hx =>
    rare_rpow_price_le (hp0 x hx) (hpTop x hx) (hprice x hx)

/-- The exponent used by the matching potential in the manuscript. -/
theorem finiteGraftLoad_fiveHalves_le_budget
    {nu : PMF ℕ} {E : Finset ℕ} {p c : ℕ → ℝ≥0∞}
    (hp0 : ∀ x ∈ E, p x ≠ 0)
    (hpTop : ∀ x ∈ E, p x ≠ ⊤)
    (hprice : ∀ x ∈ E,
      (nu x : ℝ≥0∞) ≤ c x * p x ^ (5 / 2 : ℝ)) :
    finiteGraftLoad nu E p (5 / 2 : ℝ) ≤ ∑ x ∈ E, c x := by
  apply finiteGraftLoad_le_budget hp0 hpTop hprice

/-- The combined left/right exceptional load entering the finite ledger. -/
noncomputable def twoSidedFiniteGraftLoad
    (nuL nuR : PMF ℕ) (EL ER : Finset ℕ)
    (pL pR : ℕ → ℝ≥0∞) (α : ℝ) : ℝ≥0∞ :=
  finiteGraftLoad nuL EL pL α + finiteGraftLoad nuR ER pR α

theorem twoSidedFiniteGraftLoad_fiveHalves_le_budget
    {nuL nuR : PMF ℕ} {EL ER : Finset ℕ}
    {pL pR cL cR : ℕ → ℝ≥0∞}
    (hpL0 : ∀ x ∈ EL, pL x ≠ 0)
    (hpLTop : ∀ x ∈ EL, pL x ≠ ⊤)
    (hpR0 : ∀ x ∈ ER, pR x ≠ 0)
    (hpRTop : ∀ x ∈ ER, pR x ≠ ⊤)
    (hpriceL : ∀ x ∈ EL,
      (nuL x : ℝ≥0∞) ≤ cL x * pL x ^ (5 / 2 : ℝ))
    (hpriceR : ∀ x ∈ ER,
      (nuR x : ℝ≥0∞) ≤ cR x * pR x ^ (5 / 2 : ℝ)) :
    twoSidedFiniteGraftLoad nuL nuR EL ER pL pR (5 / 2 : ℝ) ≤
      (∑ x ∈ EL, cL x) + ∑ x ∈ ER, cR x := by
  rw [twoSidedFiniteGraftLoad]
  exact add_le_add
    (finiteGraftLoad_fiveHalves_le_budget hpL0 hpLTop hpriceL)
    (finiteGraftLoad_fiveHalves_le_budget hpR0 hpRTop hpriceR)

/-! ### Explicit total-potential threshold for the finite graft system -/

/-- The common-plus-exceptional linear coefficient in the ordinary row. -/
noncomputable def finiteGraftLambda
    (lambdaS L chi₀ : ℝ) : ℝ :=
  lambdaS + L * chi₀

/-- Green multiplier obtained from an `r`-step nilpotent common screen
matrix when the exceptional block contracts by at least one half. -/
noncomputable def finiteGraftGamma (C : ℝ) (r : ℕ) : ℝ :=
  2 * ∑ j ∈ Finset.range r, (2 * C) ^ j

lemma finiteGraftGamma_nonneg {C : ℝ} {r : ℕ} (hC : 0 ≤ C) :
    0 ≤ finiteGraftGamma C r := by
  rw [finiteGraftGamma]
  positivity

/-- The explicit admissible range for the graph potential in the general
finite-graft theorem. -/
noncomputable def finiteGraftEtaThreshold
    (A C : ℝ) (r : ℕ) (lambdaS L chi₀ : ℝ) : ℝ :=
  graftFixedEtaThreshold A (finiteGraftGamma C r)
    (finiteGraftLambda lambdaS L chi₀)

theorem finiteGraftEtaThreshold_pos
    {A C lambdaS L chi₀ : ℝ} {r : ℕ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hlambda : finiteGraftLambda lambdaS L chi₀ < 1) :
    0 < finiteGraftEtaThreshold A C r lambdaS L chi₀ := by
  exact graftFixedEtaThreshold_pos hA (finiteGraftGamma_nonneg hC) hlambda

/-- Every graph potential below the displayed general finite-graft
threshold satisfies exactly the three scalar absorption inequalities used
in the induction. -/
theorem finiteGraftEtaThreshold_absorbs
    {A C lambdaS L chi₀ eta : ℝ} {r : ℕ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hlambda : finiteGraftLambda lambdaS L chi₀ < 1)
    (heta0 : 0 ≤ eta)
    (heta : eta ≤ finiteGraftEtaThreshold A C r lambdaS L chi₀) :
    let Gamma := finiteGraftGamma C r
    let lambda := finiteGraftLambda lambdaS L chi₀
    let X := graftFixedX A Gamma
    let K := graftFixedK A Gamma lambda
    eta * (K + K * X + X ^ 2) ≤ 1 ∧
      A * (K ^ 2 + K * X + X ^ 2) * eta ≤
        (1 - lambda) * K / 2 ∧
      K * eta ≤ 2⁻¹ := by
  exact graftFixedEtaThreshold_absorbs hA (finiteGraftGamma_nonneg hC)
    hlambda heta0 heta

end GraphMarkovMatching
