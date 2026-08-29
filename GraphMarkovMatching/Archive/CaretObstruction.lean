/-
**The caret budget obstruction**: the kernel budgets of the caret encoding
are infinite; the tex records the parallel frozen-pattern obstruction as
`thm:obstruction` of `arbitrary_offspring_matching.tex`.

Terminal caret states (arity-2 tops, last comb positions) emit two fresh
children, while continuing states always emit one forced level-0 child. For
the compatible pair `s = comb(3,2)` (terminal) and `t = top(3,0)`
(continuing), the pattern from `s` has both children at level `≥ 2` with
positive probability, and every pattern in the support of the kernel at `t`
contains a level-0 comb child; no pairing is then compatible, the mismatch
degree is exactly one, and the kernel budget is infinite:

    `etaD (caretKernel â p) caretRel (comb 3 2) (top 3 0) = ⊤`

whenever the level law charges any level `≥ 2`. Consequently the budget
hypothesis of the caret matching theorems is unsatisfiable for the intended
level laws: the caret encoding needs pattern-rich redesign (every pattern in
the support of `P s` must be pairable with positive `P t`-probability for
all compatible `(s,t)` — the Markov analogue of reflexivity-on-support).
-/
import GraphMarkovMatching.Archive.Caret

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### Support facts -/

/-- The fresh-top law charges every `(arity, level)` pair it should. -/
lemma freshTop_ne_zero (arity p : PMF ℕ) {m ℓ : ℕ}
    (hm : arity m ≠ 0) (hℓ : p ℓ ≠ 0) :
    freshTop arity p (mkTop m ℓ) ≠ 0 := by
  rw [← PMF.mem_support_iff, freshTop, PMF.support_bind]
  refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨(PMF.mem_support_iff _ _).mpr hm, ?_⟩⟩
  rw [PMF.support_map]
  exact ⟨ℓ, (PMF.mem_support_iff _ _).mpr hℓ, rfl⟩

/-- Every pattern in the support of the kernel at a continuing state has a
level-`0` component in every pairing position. -/
lemma caretKernel_support_cont (arity p : PMF ℕ) {t c : CaretState}
    (hc : contOf t = some c) {τ : CaretState × CaretState}
    (hτ : caretKernel arity p t τ ≠ 0) :
    τ.1 = c ∨ τ.2 = c := by
  rw [← PMF.mem_support_iff] at hτ
  rw [caretKernel, hc] at hτ
  simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_map, Set.mem_image] at hτ
  obtain ⟨b, _, f, _, hf⟩ := hτ
  cases b
  · right
    rw [← hf]
    rfl
  · left
    rw [← hf]
    rfl

/-- Interior comb positions have level zero. -/
lemma lev_contOf (t c : CaretState) (hc : contOf t = some c) : lev c = 0 := by
  match t with
  | Sum.inl (m, ℓ) =>
      rw [contOf] at hc
      by_cases h : 3 ≤ m
      · rw [if_pos h] at hc
        rw [← Option.some_inj.mp hc]
        rfl
      · rw [if_neg h] at hc
        exact absurd hc (by simp)
  | Sum.inr (m, j) =>
      rw [contOf] at hc
      by_cases h : j + 2 ≤ m
      · rw [if_pos h] at hc
        rw [← Option.some_inj.mp hc]
        rfl
      · rw [if_neg h] at hc
        exact absurd hc (by simp)

/-! ### The obstruction -/

/-- **Certain mismatch**: a both-high pattern is incompatible with every
pattern in the support of the kernel at a continuing state, so its mismatch
degree is exactly one. -/
lemma qE_pattern_eq_one (arity p : PMF ℕ) {t c : CaretState}
    (hc : contOf t = some c) {σ : CaretState × CaretState}
    (h0 : 2 ≤ lev σ.1) (h1 : 2 ≤ lev σ.2) :
    qE (caretKernel arity p t) (SquareRel caretRel) σ = 1 := by
  have hr : rE (caretKernel arity p t) (SquareRel caretRel) σ = 0 := by
    rw [rE]
    refine ENNReal.tsum_eq_zero.mpr fun τ => ?_
    by_cases hsq : SquareRel caretRel σ τ
    · rw [if_pos hsq]
      by_contra hτ
      have hcc := caretKernel_support_cont arity p hc hτ
      have hlevc : lev c = 0 := lev_contOf t c hc
      rcases hsq with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hcc with hcc | hcc
      · -- straight pairing, τ.1 = c: σ.1 ~ c impossible
        rw [hcc] at hp1
        exact absurd hp1.1 (by rw [hlevc]; omega)
      · rw [hcc] at hp2
        exact absurd hp2.1 (by rw [hlevc]; omega)
      · rw [hcc] at hp2
        exact absurd hp2.1 (by rw [hlevc]; omega)
      · rw [hcc] at hp1
        exact absurd hp1.1 (by rw [hlevc]; omega)
    · rw [if_neg hsq]
  have h := rE_add_qE (caretKernel arity p t) (SquareRel caretRel) σ
  rw [hr, zero_add] at h
  exact h

/-- **The caret budget obstruction**: for the compatible pair
`(comb 3 2, top 3 0)` the kernel mismatch potential is infinite whenever the
level law charges a level `≥ 2`. The budget hypothesis of the caret matching
theorems is therefore unsatisfiable for the intended (quantised geometric)
level laws: the caret encoding requires redesign. -/
theorem caret_etaD_eq_top (α : ℝ) (arity p : PMF ℕ)
    {m₁ ℓ' : ℕ} (hm₁ : arity m₁ ≠ 0) (hℓ' : p ℓ' ≠ 0) (hℓ2 : 2 ≤ ℓ') :
    etaD α (caretKernel arity p) caretRel (mkComb 3 2) (mkTop 3 0) = ⊤ := by
  -- the compatible pair
  have hcompat : caretRel (mkComb 3 2) (mkTop 3 0) := by
    constructor <;> simp [lev_mkComb, lev_mkTop]
  -- the both-high witness pattern
  set σ : CaretState × CaretState := (mkTop m₁ ℓ', mkTop m₁ ℓ') with hσ
  -- the source state is terminal: both children fresh
  have hterm : contOf (mkComb 3 2) = none := by
    rw [mkComb, contOf]
    norm_num
  have hker : caretKernel arity p (mkComb 3 2)
      = prodPMF (freshTop arity p) (freshTop arity p) := by
    rw [caretKernel, hterm]
  -- the witness pattern has positive mass
  have hmass : caretKernel arity p (mkComb 3 2) σ ≠ 0 := by
    rw [hker, hσ, prodPMF_apply]
    exact mul_ne_zero (freshTop_ne_zero arity p hm₁ hℓ')
      (freshTop_ne_zero arity p hm₁ hℓ')
  -- the target state is continuing
  have hcont : contOf (mkTop 3 0) = some (mkComb 3 2) := by
    rw [mkTop, contOf]
    norm_num
  -- the mismatch degree at the witness is one
  have hq1 : q (caretKernel arity p (mkTop 3 0)) (SquareRel caretRel) σ = 1 := by
    rw [q, qE_pattern_eq_one arity p hcont (by rw [hσ]; simpa using hℓ2)
      (by rw [hσ]; simpa using hℓ2), ENNReal.toReal_one]
  -- the potential dominates the infinite witness summand
  have hle : caretKernel arity p (mkComb 3 2) σ
      * phiE α (q (caretKernel arity p (mkTop 3 0)) (SquareRel caretRel) σ)
      ≤ etaD α (caretKernel arity p) caretRel (mkComb 3 2) (mkTop 3 0) := by
    rw [etaD, PhiD]
    exact ENNReal.le_tsum σ
  rw [hq1, phiE_one, ENNReal.mul_top hmass] at hle
  exact top_le_iff.mp hle

end GraphMarkovMatching
