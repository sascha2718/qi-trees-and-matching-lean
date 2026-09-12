import ChainClasses.Bushy.Trichotomy
import ChainClasses.General.GeneralHarris

/-!
`thm:cross-relabel` and transitivity of quasi-isometry (`thm:trichotomy`) of `trichotomy.tex`, the law level:
the bushy-regime pair of reduced laws sits inside the hypotheses of
the two-law application of `thm:markov-matching` in `sec:common-presentations` at `J' ≤ 2J - 1`, and almost sure quasi-isometry
composes across independent samples.

* `hairyCross_chart`: **the chart of
  `thm:cross-relabel`**: the exceptional arities
  are `{J+1, …, J'}`, each carrying the composite pair `(z + 1 - J, J)` in the
  core `{2, …, J}`, with no chart below `J + 1`.
* `hairyCross_core_charged`, `hairyCross_pair_floor`: **the full-support
  clauses**: both reduced laws charge every core arity by `thm:full-support`,
  and every composite pair carries a positive tilt floor depending on the two
  laws alone.
* the composition `QuasiIsometric.trans` lives in `Trichotomy.lean` with the
  reflexivity and the quasi-inverse.
* `pairQI_trans`: **transitivity of quasi-isometry (`thm:trichotomy`)**, the composition step: if two
  independent samples of `P₀, P₁` are almost surely quasi-isometric and
  likewise for `P₁, P₂`, then so are two independent samples of `P₀, P₂`,
  realised through the triple product and one Fubini slice.

The label-law half of `thm:cross-relabel` is the scalar layer of `Relabel`
(`relabel_law`, `product_of_constant_conditional`); its comparability clause
is `crossRelabel_qi` of `GeneralShapeMetric`.
-/

namespace ChainClasses

/-! ### The chart of the bushy cross-law -/

/-- **The chart of `thm:cross-relabel`**: at `J' ≤ 2J - 1` the exceptional
arities `{J+1, …, J'}` carry the composite pairs `(z + 1 - J, J)`, both
components in the core `{2, …, J}`, and nothing else is charted. -/
theorem hairyCross_chart {J J' : ℕ} (hJ2 : 2 ≤ J)
    (hJ'2 : J' ≤ 2 * J - 1) :
    ∃ exc : ℕ → Option (ℕ × ℕ),
      (∀ j, j ≤ J → exc j = none) ∧
      (∀ z p, exc z = some p →
        p.1 = z + 1 - J ∧ p.2 = J ∧ 2 ≤ p.1 ∧ p.1 ≤ J ∧ 2 ≤ p.2 ∧ p.2 ≤ J ∧
          p.1 + p.2 - 1 = z) ∧
      (∀ z, exc z ≠ none ↔ J + 1 ≤ z ∧ z ≤ J') := by
  classical
  refine ⟨fun z ↦ if h : J + 1 ≤ z ∧ z ≤ J' then some (z + 1 - J, J) else none,
    ?_, ?_, ?_⟩
  · intro j hj
    exact dif_neg fun hcon ↦ absurd hcon.1 (by omega)
  · intro z p hp
    by_cases h : J + 1 ≤ z ∧ z ≤ J'
    · have hp' : (if h' : J + 1 ≤ z ∧ z ≤ J' then some ((z + 1 - J, J) : ℕ × ℕ)
          else none) = some p := hp
      rw [dif_pos h] at hp'
      have hpair := Option.some.inj hp'
      have hpa : p.1 = z + 1 - J := by rw [← hpair]
      have hpb : p.2 = J := by rw [← hpair]
      exact ⟨hpa, hpb, by omega, by omega, by omega, by omega, by omega⟩
    · have hp' : (if h' : J + 1 ≤ z ∧ z ≤ J' then some ((z + 1 - J, J) : ℕ × ℕ)
          else none) = some p := hp
      rw [dif_neg h] at hp'
      simp at hp'
  · intro z
    by_cases h : J + 1 ≤ z ∧ z ≤ J'
    · constructor
      · intro _
        exact h
      · intro _
        show (if h' : J + 1 ≤ z ∧ z ≤ J' then some ((z + 1 - J, J) : ℕ × ℕ)
          else none) ≠ none
        rw [dif_pos h]
        exact Option.some_ne_none _
    · constructor
      · intro hne
        exact absurd (dif_neg h) hne
      · intro hcon
        exact absurd hcon h

/-- **The common core is charged by both reduced laws**, by
`thm:full-support`. -/
theorem hairyCross_core_charged {J J' : ℕ} (θ θ' : ℕ → ℝ) {q q' : ℝ}
    (hnn : ∀ j, 0 ≤ θ j) (hnn' : ∀ j, 0 ≤ θ' j)
    (hJ : 0 < θ J) (hJ' : 0 < θ' J')
    (hq0 : 0 < q) (hq1 : q < 1) (hq'0 : 0 < q') (hq'1 : q' < 1)
    (hsub : genDeriv J θ q < 1) (hsub' : genDeriv J' θ' q' < 1)
    (hJJ' : J ≤ J') {k : ℕ} (hk2 : 2 ≤ k) (hkJ : k ≤ J) :
    0 < reducedLaw J θ q k ∧ 0 < reducedLaw J' θ' q' k :=
  ⟨reducedLaw_pos J θ hnn hJ hq0 hq1 hsub (by omega) hkJ,
    reducedLaw_pos J' θ' hnn' hJ' hq'0 hq'1 hsub' (by omega) (by omega)⟩

/-- **The floor of a composite pair of `thm:cross-relabel`**: the tilt floor
`(1/2) ν̃'_{z+1-J} ν̃'_J` is positive and depends on the two laws alone. -/
theorem hairyCross_pair_floor {J J' : ℕ} (θ' : ℕ → ℝ) {q' : ℝ}
    (hnn' : ∀ j, 0 ≤ θ' j) (hJ' : 0 < θ' J')
    (hq'0 : 0 < q') (hq'1 : q' < 1) (hsub' : genDeriv J' θ' q' < 1)
    (hJ2 : 2 ≤ J) (hJJ' : J ≤ J')
    {z : ℕ} (hz1 : J + 1 ≤ z) (hz2 : z ≤ J') :
    0 < (1 / 2) * (reducedLaw J' θ' q' (z + 1 - J) * reducedLaw J' θ' q' J) := by
  have h1 : 0 < reducedLaw J' θ' q' (z + 1 - J) :=
    reducedLaw_pos J' θ' hnn' hJ' hq'0 hq'1 hsub' (by omega) (by omega)
  have h2 : 0 < reducedLaw J' θ' q' J :=
    reducedLaw_pos J' θ' hnn' hJ' hq'0 hq'1 hsub' (by omega) (by omega)
  positivity

/-! ### Transitivity across independent samples -/

open MeasureTheory
open BranchingProcess (QuasiIsometric IsQIWith)

/-- **transitivity of quasi-isometry (`thm:trichotomy`)**, the composition step: almost sure quasi-isometry
of independent samples composes through the triple product. -/
theorem pairQI_trans (L0 L1 L2 : SampleLaw)
    (h01 : ∀ᵐ ω ∂(L0.law.prod L1.law), PairQI L0 L1 ω)
    (h12 : ∀ᵐ ω ∂(L1.law.prod L2.law), PairQI L1 L2 ω) :
    ∀ᵐ ω ∂(L0.law.prod L2.law), PairQI L0 L2 ω := by
  have hlift01 := ae_pair_fst (τ := L2.law) h01
  have hlift12 : ∀ᵐ ω ∂(L0.law.prod (L1.law.prod L2.law)), PairQI L1 L2 ω.2 :=
    ae_of_snd h12
  have htrip : ∀ᵐ ω ∂(L0.law.prod (L1.law.prod L2.law)),
      PairQI L0 L2 (ω.1, ω.2.2) := by
    filter_upwards [hlift01, hlift12] with ω h1 h2
    exact QuasiIsometric.trans
      (wordGraph_connected (L2.prefixClosed ω.2.2) ⟨⟨[], L2.root ω.2.2⟩⟩) h1 h2
  exact ae_pair_outer htrip

end ChainClasses
