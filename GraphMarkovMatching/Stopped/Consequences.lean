/-
The explicit consequences of `thm:markov-matching` in `arbitrary_offspring_matching.tex` at the
rational parameters of `sec:two-exponent-values` and `sec:exponent-four-thirds`.

* `paramsTwo`: the parameters `α = 2`, `β = 1/16`, `u = 1/2`, `L = 1/4`, `K = 125/1024`,
  `L0 = 1/4`, with `a = 381/512`, `b = 38`, `γ = 17/8` (`eq:mean-exponent-two`);
* `paramsFourThirds`: the parameters `α = 4/3`, `β = 11/40`, `u = 1/2`, `L = 403/1000`,
  `K = 12/125`, `L0 = 2^{-4/3}`, with `a = 499/500` and `b < 28`
  (`sec:exponent-four-thirds`);
* `two_exponent_consequence`, `two_exponent_consequence_infinite`: the explicit consequence
  at exponent two, `η_2(μ) ≤ 1/2500` gives failure probability at most `(1024/131) η_2(μ)`
  for every pair of types, at every height and at infinite height, over all countable
  zero-compatible models (`sec:two-exponent-values`);
* `markov_matching_fourThirds`, `markov_matching_two`,
  `markov_matching_zero_fourThirds`, `markov_matching_zero_two`: `thm:markov-matching` at
  the exponents `4/3` and `2` from the rational parameters, in both alternatives, with no
  numerical optimisation.
-/
import GraphMarkovMatching.Stopped.Main
import GraphMarkovMatching.Stopped.Numerics

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Model
open scoped ENNReal Classical

/-! ### The rational parameters (`sec:two-exponent-values`, `sec:exponent-four-thirds`) -/

/-- The rational parameters at exponent `2` (`sec:two-exponent-values`): `β = 1/16`,
`u = 1/2`, `L = 1/4`, `K = 125/1024`, `L0 = 1/4`, with `a = 381/512`, `b = 38`, `γ = 17/8`. -/
noncomputable def paramsTwo : Params where
  α := 2
  β := 1 / 16
  u := 1 / 2
  L := 1 / 4
  K := 125 / 1024
  L0 := 1 / 4
  hα := by norm_num
  hβ0 := by norm_num
  hβ1 := by norm_num
  hu0 := by norm_num
  hu1 := by norm_num
  hL := fun q hq0 hq1 =>
    (le_Lfun (by norm_num) (by norm_num) hq0 hq1).trans Lfun_two_sixteenth.le
  hK := fun q hq0 hq1 =>
    (Kfun_bound (by norm_num) (by norm_num) (by norm_num) hq0 hq1).trans Kfun_two_sixteenth.le
  hL0 := fun q hq0 hq1 => (le_Lfun (by norm_num) le_rfl hq0 hq1).trans Lfun_two_zero.le
  ha := by norm_num

/-- The exponent of `paramsTwo` is `2`. -/
lemma paramsTwo_α : paramsTwo.α = 2 := rfl

/-- `a = 381/512` at exponent `2` (`eq:mean-exponent-two`). -/
lemma paramsTwo_a : paramsTwo.a = 381 / 512 := by
  unfold Params.a
  norm_num [paramsTwo]

/-- `b = C_2(1/2) = 38` at exponent `2` (`eq:mean-exponent-two`). -/
lemma paramsTwo_b : paramsTwo.b = 38 := by
  unfold Params.b
  exact Cfun_two

/-- `γ = 2 + 2β = 17/8` at exponent `2` (`eq:mean-exponent-two`). -/
lemma paramsTwo_γ : paramsTwo.γ = 17 / 8 := by
  unfold Params.γ
  norm_num [paramsTwo]

/-- The rational parameters at exponent `4/3` (`sec:exponent-four-thirds`): `β = 11/40`,
`u = 1/2`, `L = 403/1000`, `K = 12/125`, `L0 = 2^{-4/3}`, with `a = 499/500`. -/
noncomputable def paramsFourThirds : Params where
  α := 4 / 3
  β := 11 / 40
  u := 1 / 2
  L := 403 / 1000
  K := 12 / 125
  L0 := (2 : ℝ) ^ (-(4 / 3 : ℝ))
  hα := by norm_num
  hβ0 := by norm_num
  hβ1 := by norm_num
  hu0 := by norm_num
  hu1 := by norm_num
  hL := fun q hq0 hq1 =>
    (le_Lfun (by norm_num) (by norm_num) hq0 hq1).trans Lfun_fourThirds_lt.le
  hK := fun q hq0 hq1 =>
    (Kfun_bound (by norm_num) (by norm_num) (by norm_num) hq0 hq1).trans Kfun_fourThirds_lt.le
  hL0 := fun q hq0 hq1 => (le_Lfun (by norm_num) le_rfl hq0 hq1).trans
    (Lfun_zero_eq_of_le_two (by norm_num) (by norm_num)).le
  ha := by norm_num

/-- The exponent of `paramsFourThirds` is `4/3`. -/
lemma paramsFourThirds_α : paramsFourThirds.α = 4 / 3 := rfl

/-- `a = 499/500` at exponent `4/3` (`sec:exponent-four-thirds`). -/
lemma paramsFourThirds_a : paramsFourThirds.a = 499 / 500 := by
  unfold Params.a
  norm_num [paramsFourThirds]

/-- `b = C_{4/3}(1/2) < 28` at exponent `4/3` (`sec:exponent-four-thirds`). -/
lemma paramsFourThirds_b_lt : paramsFourThirds.b < 28 := by
  unfold Params.b
  exact Cfun_fourThirds_lt

/-! ### The explicit consequence at exponent two (`sec:two-exponent-values`) -/

namespace Model

variable {V I : Type} (M : Model V I)

/-- The four-law input at exponent `2` with the rational coefficients `a = 381/512`,
`b = 38` when `δ = 0` (`eq:mean-exponent-two`). -/
private lemma fourLawAtZero_two (hc : M.IsCompat) (hδ : M.delta = 0) (h : ℕ) (Mb : ℝ≥0∞) :
    M.FourLawAtZero 2 h (ENNReal.ofReal (381 / 512)) (ENNReal.ofReal 38) Mb := by
  have key := M.fourLawAtZero_of_params hc hδ paramsTwo.hα paramsTwo.hβ0 paramsTwo.hβ1
    paramsTwo.hu0 paramsTwo.hu1 paramsTwo.hL paramsTwo.hK paramsTwo.hL0 h Mb
  have e1 : ENNReal.ofReal (2 * (paramsTwo.L + paramsTwo.K)) = ENNReal.ofReal (381 / 512) := by
    norm_num [paramsTwo]
  have e2 : ENNReal.ofReal (Cfun paramsTwo.α paramsTwo.L0 paramsTwo.u) = ENNReal.ofReal 38 := by
    show ENNReal.ofReal (Cfun 2 (1 / 4) (1 / 2)) = ENNReal.ofReal 38
    rw [Cfun_two]
  rw [e1, e2] at key
  exact key

end Model

/-- **The explicit consequence at exponent two** (`sec:two-exponent-values`): for every
model with `δ = 0` (countably many types, no return or transition-bound assumption) and
`η_2(μ) ≤ 1/2500`, the failure probability of every pair of types at every height is at
most `(1024/131) η_2(μ)`. The scalar barrier `η + (1 + 3η)(aM + bM²) ≤ M` holds at
`M = (1024/131) η` by `two_exponent_criterion`. -/
theorem two_exponent_consequence {V I : Type} (M : Model V I) (hc : M.IsCompat)
    (hδ : M.delta = 0) (hη : M.eta 2 ≤ ENNReal.ofReal (1 / 2500)) :
    ∀ s t h, M.failProb s t h ≤ ENNReal.ofReal (1024 / 131) * M.eta 2 := by
  have hζη : M.zeta 2 = M.eta 2 := M.zeta_eq_eta_of_delta_zero hδ
  have hfin : M.eta 2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hη
  set η := (M.eta 2).toReal with hη_def
  have hη_eq : M.eta 2 = ENNReal.ofReal η := (ENNReal.ofReal_toReal hfin).symm
  have hη0 : 0 ≤ η := ENNReal.toReal_nonneg
  have hηle : η ≤ 1 / 2500 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hη
  have hM0 : 0 ≤ 1024 / 131 * η := by positivity
  -- the root coefficient `D_μ ≤ 1 + 3η`
  have hD : M.DmuC 2 ≤ ENNReal.ofReal (1 + 3 * η) := by
    calc M.DmuC 2 ≤ 1 + ENNReal.ofReal (2 * 2 - 1) * M.zeta 2 := M.DmuC_le hc (by norm_num)
      _ = ENNReal.ofReal (1 + 3 * η) := by
          rw [hζη, hη_eq, ← ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
          norm_num
  -- the real barrier at `M = (1024/131) η`
  have hcrit := two_exponent_criterion hη0 hηle
  have key : η + (1 + 3 * η) * (381 / 512 * (1024 / 131 * η) + 38 * (1024 / 131 * η) ^ 2)
      ≤ 1024 / 131 * η := by
    have := mul_le_mul_of_nonneg_left hcrit hη0
    nlinarith [this]
  have hq0 : 0 ≤ 381 / 512 * (1024 / 131 * η) + 38 * (1024 / 131 * η) ^ 2 := by positivity
  have hbar : M.zeta 2 + M.DmuC 2 * (ENNReal.ofReal (381 / 512) * ENNReal.ofReal (1024 / 131 * η)
      + ENNReal.ofReal 38 * ENNReal.ofReal (1024 / 131 * η) ^ 2)
      ≤ ENNReal.ofReal (1024 / 131 * η) := by
    calc M.zeta 2 + M.DmuC 2 * (ENNReal.ofReal (381 / 512) * ENNReal.ofReal (1024 / 131 * η)
          + ENNReal.ofReal 38 * ENNReal.ofReal (1024 / 131 * η) ^ 2)
        ≤ ENNReal.ofReal η + ENNReal.ofReal (1 + 3 * η)
            * ENNReal.ofReal (381 / 512 * (1024 / 131 * η) + 38 * (1024 / 131 * η) ^ 2) := by
          refine add_le_add ?_ (mul_le_mul' hD (le_of_eq ?_))
          · rw [hζη, hη_eq]
          · rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 381 / 512) (by norm_num),
              ENNReal.ofReal_mul (p := 38) (by norm_num), ENNReal.ofReal_pow hM0]
      _ = ENNReal.ofReal (η + (1 + 3 * η)
            * (381 / 512 * (1024 / 131 * η) + 38 * (1024 / 131 * η) ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add hη0 (mul_nonneg (by positivity) hq0)]
      _ ≤ ENNReal.ofReal (1024 / 131 * η) := ENNReal.ofReal_le_ofReal key
  have hMb : ENNReal.ofReal (1024 / 131 * η) = ENNReal.ofReal (1024 / 131) * M.eta 2 := by
    rw [ENNReal.ofReal_mul (by norm_num), hη_eq]
  intro s t h
  rw [← hMb]
  exact M.failProb_le_zero hc hδ (by norm_num) _ _ (M.fourLawAtZero_two hc hδ) hbar h s t

/-- **The explicit consequence at exponent two, at infinite height**
(`sec:two-exponent-values`): with `δ = 0` and `η_2(μ) ≤ 1/2500`, a single rooted
automorphism of the infinite binary tree fails to match with probability at most
`(1024/131) η_2(μ)`. -/
theorem two_exponent_consequence_infinite {V I : Type} [Countable V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (M : Model V I) (hc : M.IsCompat) (hδ : M.delta = 0)
    (hη : M.eta 2 ≤ ENNReal.ofReal (1 / 2500)) :
    ∀ s t, M.trajPair s t (M.InfMatchEv s t)ᶜ ≤ ENNReal.ofReal (1024 / 131) * M.eta 2 :=
  fun s t => M.trajPair_infFail_le s t (two_exponent_consequence M hc hδ hη s t)

/-! ### `thm:markov-matching` at the exponents `4/3` and `2` -/

set_option linter.unusedVariables false in
/-- **`thm:markov-matching` at exponent `4/3`, finite alternative** (`sec:exponent-four-thirds`),
from the rational parameters `paramsFourThirds`: constants depending only on `H`, `T`,
`B`. -/
theorem markov_matching_fourThirds (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Model V I) (hc : M.IsCompat) {g : ℕ}
      (Θ : Model.Phase M g), (∀ i, Θ.count i ≤ T) → ∀ (Sel : Model.Selection M),
      (∀ t, Sel.inverseSum (4 / 3) t ≤ ENNReal.ofReal B) → M.FreshPositive →
      M.CommonReturns Θ H → M.zeta (4 / 3) ≤ ENNReal.ofReal ε → ∀ s t, Θ.θ s = Θ.θ t →
        ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta (4 / 3) :=
  markov_matching_finite_exists paramsFourThirds H T hT B hB

set_option linter.unusedVariables false in
/-- **`thm:markov-matching` at exponent `2`, finite alternative** (`sec:two-exponent-values`),
from the rational parameters `paramsTwo`: constants depending only on `H`, `T`, `B`. -/
theorem markov_matching_two (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Model V I) (hc : M.IsCompat) {g : ℕ}
      (Θ : Model.Phase M g), (∀ i, Θ.count i ≤ T) → ∀ (Sel : Model.Selection M),
      (∀ t, Sel.inverseSum 2 t ≤ ENNReal.ofReal B) → M.FreshPositive →
      M.CommonReturns Θ H → M.zeta 2 ≤ ENNReal.ofReal ε → ∀ s t, Θ.θ s = Θ.θ t →
        ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta 2 :=
  markov_matching_finite_exists paramsTwo H T hT B hB

set_option linter.unusedVariables false in
/-- **`thm:markov-matching` at exponent `4/3`, zero-compatible alternative**
(`sec:exponent-four-thirds`): absolute constants. -/
theorem markov_matching_zero_fourThirds :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Model V I) (hc : M.IsCompat), M.delta = 0 →
      M.zeta (4 / 3) ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta (4 / 3) :=
  markov_matching_zero_exists paramsFourThirds

set_option linter.unusedVariables false in
/-- **`thm:markov-matching` at exponent `2`, zero-compatible alternative**
(`sec:two-exponent-values`): absolute constants. -/
theorem markov_matching_zero_two :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Model V I) (hc : M.IsCompat), M.delta = 0 →
      M.zeta 2 ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta 2 :=
  markov_matching_zero_exists paramsTwo

end GraphMarkovMatching.Stopped
