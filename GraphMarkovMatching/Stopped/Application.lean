/-
The application of `thm:markov-matching` to two product laws with a common core
(`arbitrary_offspring_matching.tex`, `sec:common-presentations`,
`sec:types-degrees`, `sec:return-times`, `thm:common-semigroup-matching`, and the
"In particular" after `thm:markov-matching`).

* `liveOf`, `TcountOf`, `coreDepthsOf`, `gPhaseOf`, `returnThresholdOf`, `ellOf`, `HretOf`,
  `inverseSumOf`: the constants `T`, `H`, `B` of the finite alternative as functions of the
  profile data and the core floor alone, with `Presentation.Tcount`, `Presentation.Hret`,
  `Presentation.coreInverseSum` their values at a presentation;
* `Presentation.commonReturns_Hret`, `Presentation.commonReturns_exists`: the return bound
  `thm:bounded-return` at `H = c_Γ + 2ℓ` with the explicit return threshold;
* `Presentation.inverseSum_le_of_floor`: the bound `B ≤ #S c^{-α}` from a floor `c` on the core
  probabilities (`thm:atomic-normalisation`);
* `Presentation.presentation_matching_explicit`, `presentation_matching`,
  `presentation_matching_infinite`, `presentation_matching_eta`,
  `presentation_matching_of_lambda`: `thm:markov-matching` for the Markov model of a
  presentation, with the explicit constants, in existential form, on the infinite tree,
  in the `η` form and under the exponent condition alone;
* `presentation_matching_uniform`, `presentation_matching_uniform_infinite`: uniformity
  over all arity laws with the same supports, the same profiles and the same core floor;
* `spine`, `atomsFinset`, `atomCore`, `atomExpr`, `atomicPresentation`,
  `exists_presentation`: the common atomic presentation of two supports with equal
  branching semigroups (`sec:common-generators`);
* `Presentation.exists_floor`, `presentation_matching_auto`, `two_laws_matching`: the floor
  is automatically positive for a fixed pair of laws, and the headline "In particular".
-/
import GraphMarkovMatching.Stopped.Main
import GraphMarkovMatching.Stopped.Returns
import GraphMarkovMatching.Stopped.Semigroup

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Model
open scoped ENNReal Classical

/-! ### The constants as functions of the profile data -/

/-- The live types of profile data (`sec:types-degrees`): the two fresh types and the forced types
at the proper subtrees, other than leaves, of the supported profiles. This is the body of
`Presentation.live`, as a function of the supports and profiles alone. -/
noncomputable def liveOf (supp : Bool → Finset ℕ) (C : Bool → ℕ → MTree) : Finset PType :=
  ({(false, none), (true, none)} : Finset PType)
    ∪ (Finset.univ (α := Bool)).biUnion fun σ =>
        (supp σ).biUnion fun k =>
          ((C σ k).subtrees.filter fun τ => τ ≠ C σ k ∧ τ ≠ MTree.leaf).image fun τ =>
            (σ, some τ)

/-- The type count `T = #live` of profile data (`eq:transition-budget`). -/
noncomputable def TcountOf (supp : Bool → Finset ℕ) (C : Bool → ℕ → MTree) : ℕ :=
  (liveOf supp C).card

/-- The core leaf depths `R_0` of profile data (`sec:return-times`). -/
noncomputable def coreDepthsOf (S : Finset ℕ) (D : ℕ → MTree) : Finset ℕ :=
  S.biUnion fun a => (D a).leafDepths

/-- `g = gcd R_0` of profile data (`sec:return-times`). -/
noncomputable def gPhaseOf (S : Finset ℕ) (D : ℕ → MTree) : ℕ := (coreDepthsOf S D).gcd id

/-- The explicit return threshold `g (a_0 - 1)(b_0 - 1)` of `sec:return-times`
(`thm:bounded-return`),
zero when the core is empty. -/
noncomputable def returnThresholdOf (S : Finset ℕ) (D : ℕ → MTree) : ℕ :=
  if h : (coreDepthsOf S D).Nonempty then
    gPhaseOf S D * (((coreDepthsOf S D).min' h / gPhaseOf S D - 1)
      * ((coreDepthsOf S D).max' h / gPhaseOf S D - 1))
  else 0

/-- The maximal profile height `ℓ` of profile data (`sec:common-presentations`). -/
noncomputable def ellOf (supp : Bool → Finset ℕ) (C : Bool → ℕ → MTree) : ℕ :=
  (Finset.univ (α := Bool)).sup fun σ => (supp σ).sup fun k => (C σ k).height

/-- The return bound `H = g (a_0 - 1)(b_0 - 1) + 2ℓ` of profile data
(`thm:bounded-return`). -/
noncomputable def HretOf (S : Finset ℕ) (D : ℕ → MTree) (supp : Bool → Finset ℕ)
    (C : Bool → ℕ → MTree) : ℕ :=
  returnThresholdOf S D + 2 * ellOf supp C

/-- The bound `B = #S c^{-α}` from the core floor `c` (`thm:atomic-normalisation`). -/
noncomputable def inverseSumOf (S : Finset ℕ) (c α : ℝ) : ℝ := S.card * c ^ (-α)

/-- The live types of profile data contain the left fresh type. -/
lemma fresh_mem_liveOf (supp : Bool → Finset ℕ) (C : Bool → ℕ → MTree) (σ : Bool) :
    (σ, none) ∈ liveOf supp C := by
  cases σ <;> simp [liveOf]

/-- `1 ≤ T`. -/
lemma one_le_TcountOf (supp : Bool → Finset ℕ) (C : Bool → ℕ → MTree) :
    1 ≤ TcountOf supp C :=
  Finset.card_pos.mpr ⟨_, fresh_mem_liveOf supp C false⟩

/-- `1 ≤ #S c^{-α}` for a nonempty core and a floor `0 < c ≤ 1`
(`thm:atomic-normalisation`). -/
lemma one_le_inverseSumOf {S : Finset ℕ} (hS : S.Nonempty) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) : 1 ≤ inverseSumOf S c α := by
  unfold inverseSumOf
  have h1 : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have h2 : (1 : ℝ) ≤ c ^ (-α) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc0 hc1 (by linarith)
  calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
    _ ≤ S.card * c ^ (-α) := mul_le_mul h1 h2 zero_le_one (by linarith)

namespace Presentation

variable (P : Presentation) {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V)

/-- The live types are those of the profile data. -/
lemma live_eq : P.live = liveOf P.supp P.C := rfl

/-- `T = #live` (`eq:transition-budget`, `sec:types-degrees`). -/
noncomputable def Tcount : ℕ := TcountOf P.supp P.C

/-- `T = #live`. -/
lemma Tcount_eq : P.Tcount = P.live.card := rfl

/-- `1 ≤ T`: the fresh types are live. -/
lemma one_le_Tcount : 1 ≤ P.Tcount := one_le_TcountOf P.supp P.C

/-- The core leaf depths are those of the profile data. -/
lemma coreDepths_eq : P.coreDepths = coreDepthsOf P.S P.D := rfl

/-- The explicit return threshold of a presentation (`thm:bounded-return`). -/
noncomputable def returnThreshold : ℕ := returnThresholdOf P.S P.D

/-- The return-threshold bound (`thm:bounded-return`, `sec:return-times`): every multiple of `g` at
least the return threshold lies in `Γ`. -/
theorem returnThreshold_spec : ∀ n, P.returnThreshold ≤ n → P.gPhase ∣ n → n ∈ P.Gamma := by
  have h := P.returnThreshold_bound P.S_nonempty
  have hne : (coreDepthsOf P.S P.D).Nonempty := P.coreDepths_nonempty P.S_nonempty
  unfold returnThreshold returnThresholdOf
  rw [dite_eq_left hne]
  exact h

/-- The return bound `H = c_Γ + 2ℓ` of a presentation (`thm:bounded-return`), a function of
the profile data alone. -/
noncomputable def Hret : ℕ := HretOf P.S P.D P.supp P.C

/-- `H = c_Γ + 2ℓ`. -/
lemma Hret_eq : P.Hret = P.returnThreshold + 2 * P.ell := rfl

/-- **`thm:bounded-return`** at `H = c_Γ + 2ℓ`: common returns for every state space. -/
theorem commonReturns_Hret :
    (P.toModel R zero μ).CommonReturns (P.phase R zero μ) P.Hret :=
  P.commonReturns_explicit R zero μ P.S_nonempty P.returnThreshold_spec

/-- **`thm:bounded-return`**, existential form: a return bound depending only on the
profiles, valid for every state space. -/
theorem commonReturns_exists :
    ∃ H : ℕ, ∀ {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V),
      (P.toModel R zero μ).CommonReturns (P.phase R zero μ) H :=
  ⟨P.Hret, fun R zero μ => P.commonReturns_Hret R zero μ⟩

/-- The bound `B = #S c^{-α}` of a presentation from the core floor `c`
(`thm:atomic-normalisation`). -/
noncomputable def coreInverseSum (c α : ℝ) : ℝ := inverseSumOf P.S c α

/-- `1 ≤ B` for a floor `0 < c ≤ 1`. -/
lemma one_le_coreInverseSum {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {α : ℝ} (hα : 0 ≤ α) :
    1 ≤ P.coreInverseSum c α :=
  one_le_inverseSumOf P.S_nonempty hc0 hc1 hα

/-- **The bound `B` from a core floor** (`thm:atomic-normalisation`): if every core probability on
either side is at least `c`, the inverse-probability sum of the core selection is at most `#S c^{-α}`. -/
theorem inverseSum_le_of_floor (hc : (P.toModel R zero μ).IsCompat) (hb0 : rE μ R zero ≠ 0)
    {α : ℝ} (hα : 0 ≤ α) {c : ℝ} (hc0 : 0 < c)
    (hfloor : ∀ σ a, a ∈ P.S → ENNReal.ofReal c ≤ P.ν σ a) (t : P.Live) :
    (P.selection R zero μ hc hb0).inverseSum α t ≤ ENNReal.ofReal (P.coreInverseSum c α) := by
  refine (P.inverseSum_le R zero μ hc hb0 hα t).trans ?_
  have key : ∀ σ, ∑ a ∈ P.S, (P.ν σ a) ^ (-α) ≤ ENNReal.ofReal (P.coreInverseSum c α) := by
    intro σ
    calc ∑ a ∈ P.S, (P.ν σ a) ^ (-α)
        ≤ ∑ _a ∈ P.S, (ENNReal.ofReal c) ^ (-α) :=
          Finset.sum_le_sum fun a ha => rpow_neg_antitone hα (hfloor σ a ha)
      _ = P.S.card * (ENNReal.ofReal c) ^ (-α) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (P.coreInverseSum c α) := by
          rw [coreInverseSum, inverseSumOf, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos hc0]
  exact max_le (key false) (key true)

/-- The fresh live types are fresh in the model. -/
lemma fresh_freshL (σ : Bool) : (P.toModel R zero μ).fresh (P.freshL σ) := rfl

/-- The phase of a fresh live type is zero (`sec:return-times`). -/
lemma phase_freshL (σ : Bool) : (P.phase R zero μ).θ (P.freshL σ) = 0 :=
  (P.phase R zero μ).fresh_zero _ (P.fresh_freshL R zero μ σ)

/-- Any two fresh live types form an equal-phase pair. -/
lemma phase_freshL_eq (σ σ' : Bool) :
    (P.phase R zero μ).θ (P.freshL σ) = (P.phase R zero μ).θ (P.freshL σ') := by
  rw [P.phase_freshL, P.phase_freshL]

/-! ### The matching theorem for a presentation (`thm:markov-matching`, "In particular") -/

/-- **`thm:markov-matching` for the Markov model of a presentation, with the explicit
constants** (the verification leading to `thm:common-semigroup-matching`): with `T = #live`,
`H = c_Γ + 2ℓ` and `B = #S c^{-α}` from a floor `c` on the core probabilities, if
`ζ_α ≤ ε_K` then every equal-phase pair fails at every height with probability at most
`K_match ζ_α`, the fresh pairs with probability at most `K ζ_α`, and every equal-phase
restricted potential is at most `K ζ_α`. -/
theorem presentation_matching_explicit (p : Params) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hfloor : ∀ σ a, a ∈ P.S → ENNReal.ofReal c ≤ P.ν σ a) (Kc : ℝ)
    (hK : finiteK0 p P.Hret (P.coreInverseSum c p.α) < Kc)
    (hcompat : (P.toModel R zero μ).IsCompat)
    (hζ : (P.toModel R zero μ).zeta p.α
      ≤ ENNReal.ofReal (finiteEps p P.Hret P.Tcount (P.coreInverseSum c p.α) Kc)) :
    (∀ s t, (P.phase R zero μ).θ s = (P.phase R zero μ).θ t → ∀ h,
        (P.toModel R zero μ).failProb s t h
          ≤ ENNReal.ofReal (finiteKmatch P.Hret Kc) * (P.toModel R zero μ).zeta p.α)
    ∧ (∀ σ σ' h, (P.toModel R zero μ).failProb (P.freshL σ) (P.freshL σ') h
          ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta p.α)
    ∧ (∀ s t, (P.phase R zero μ).θ s = (P.phase R zero μ).θ t → ∀ h,
        (P.toModel R zero μ).P p.α s t h ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta p.α) := by
  have hζtop : (P.toModel R zero μ).zeta p.α ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hζ
  have hb0 : rE μ R zero ≠ 0 := (P.toModel R zero μ).rE_zero_ne_zero_of_zeta_ne_top hζtop
  obtain ⟨h1, h2, h3⟩ := markov_matching_finite p P.Hret P.Tcount P.one_le_Tcount
    (P.coreInverseSum c p.α) (P.one_le_coreInverseSum hc0 hc1 p.α_nonneg) Kc hK (P.toModel R zero μ)
    hcompat (P.phase R zero μ) (P.count_le_card R zero μ) (P.selection R zero μ hcompat hb0)
    (P.inverseSum_le_of_floor R zero μ hcompat hb0 p.α_nonneg hc0 hfloor)
    (P.freshPositive R zero μ hcompat hb0) (P.commonReturns_Hret R zero μ) hζ
  exact ⟨h1, fun σ σ' h => h2 _ _ (P.fresh_freshL R zero μ σ) (P.fresh_freshL R zero μ σ') h,
    h3⟩

/-- **`thm:markov-matching` for a presentation** (the "In particular" after
`thm:markov-matching`): for every presentation and every floor `c` on its core
probabilities, constants depending only on the exponent parameters, the profiles and the
floor, such that for every state space with `ζ_α ≤ ε` the two fresh initial types match at
every height with failure probability at most `K ζ_α`. -/
theorem presentation_matching (p : Params) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hfloor : ∀ σ a, a ∈ P.S → ENNReal.ofReal c ≤ P.ν σ a) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V),
      (P.toModel R zero μ).IsCompat →
      (P.toModel R zero μ).zeta p.α ≤ ENNReal.ofReal ε →
        ∀ σ σ' h, (P.toModel R zero μ).failProb (P.freshL σ) (P.freshL σ') h
          ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta p.α := by
  set K0 := finiteK0 p P.Hret (P.coreInverseSum c p.α) with hK0
  have hK : K0 < K0 + 1 := by linarith
  refine ⟨K0 + 1, finiteEps p P.Hret P.Tcount (P.coreInverseSum c p.α) (K0 + 1),
    finiteEps_pos p P.Hret P.Tcount P.one_le_Tcount _ (P.one_le_coreInverseSum hc0 hc1 p.α_nonneg)
      _ hK, ?_⟩
  intro V R zero μ hcompat hζ
  exact (P.presentation_matching_explicit R zero μ p hc0 hc1 hfloor _ hK hcompat hζ).2.1

/-- The discrete σ-algebra on the live types. -/
instance : MeasurableSpace P.Live := ⊤

/-- Every singleton of live types is measurable. -/
instance : MeasurableSingletonClass P.Live := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- **`thm:markov-matching` for a presentation, on the infinite tree**: the two fresh
initial types match on the whole tree with failure probability at most `K ζ_α`. -/
theorem presentation_matching_infinite (p : Params) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hfloor : ∀ σ a, a ∈ P.S → ENNReal.ofReal c ≤ P.ν σ a) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V : Type} [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V] (R : V → V → Prop) (zero : V) (μ : PMF V),
      (P.toModel R zero μ).IsCompat →
      (P.toModel R zero μ).zeta p.α ≤ ENNReal.ofReal ε →
        ∀ σ σ', (P.toModel R zero μ).trajPair (P.freshL σ) (P.freshL σ')
            ((P.toModel R zero μ).InfMatchEv (P.freshL σ) (P.freshL σ'))ᶜ
          ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta p.α := by
  obtain ⟨Kc, ε, hε, hbound⟩ := P.presentation_matching p hc0 hc1 hfloor
  refine ⟨Kc, ε, hε, ?_⟩
  intro V _ _ _ R zero μ hcompat hζ σ σ'
  exact (P.toModel R zero μ).trajPair_infFail_le _ _ (hbound R zero μ hcompat hζ σ σ')

/-- **The `η` form for a presentation** (`thm:markov-matching`, last sentence): with
`μ(0) ≥ p₀ > 0`, the constant `K_match/p₀` and the threshold `p₀ ε_K`, every equal-phase
pair fails with probability at most `(K_match/p₀) η_α`. -/
theorem presentation_matching_eta (p : Params) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hfloor : ∀ σ a, a ∈ P.S → ENNReal.ofReal c ≤ P.ν σ a) (Kc : ℝ)
    (hK : finiteK0 p P.Hret (P.coreInverseSum c p.α) < Kc)
    (hcompat : (P.toModel R zero μ).IsCompat) {p0 : ℝ} (hp0 : 0 < p0) (hp1 : p0 ≤ 1)
    (hμ : ENNReal.ofReal p0 ≤ μ zero)
    (hη : (P.toModel R zero μ).eta p.α
      ≤ ENNReal.ofReal (p0 * finiteEps p P.Hret P.Tcount (P.coreInverseSum c p.α) Kc)) :
    ∀ s t, (P.phase R zero μ).θ s = (P.phase R zero μ).θ t → ∀ h,
      (P.toModel R zero μ).failProb s t h
        ≤ ENNReal.ofReal (finiteKmatch P.Hret Kc / p0) * (P.toModel R zero μ).eta p.α := by
  have hp : ENNReal.ofReal p0 ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hp1' : ENNReal.ofReal p0 ≤ 1 := ENNReal.ofReal_le_one.mpr hp1
  have hζη : (P.toModel R zero μ).zeta p.α ≤ (P.toModel R zero μ).eta p.α / ENNReal.ofReal p0 :=
    (P.toModel R zero μ).zeta_le_eta_div hcompat p.α_nonneg hp hp1' hμ
  have hζtop : (P.toModel R zero μ).zeta p.α ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hζη
    exact ENNReal.div_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hη) hp
  have hb0 : rE μ R zero ≠ 0 := (P.toModel R zero μ).rE_zero_ne_zero_of_zeta_ne_top hζtop
  exact markov_matching_finite_eta p P.Hret P.Tcount P.one_le_Tcount (P.coreInverseSum c p.α)
    (P.one_le_coreInverseSum hc0 hc1 p.α_nonneg) Kc hK (P.toModel R zero μ) hcompat
    (P.phase R zero μ) (P.count_le_card R zero μ) (P.selection R zero μ hcompat hb0)
    (P.inverseSum_le_of_floor R zero μ hcompat hb0 p.α_nonneg hc0 hfloor)
    (P.freshPositive R zero μ hcompat hb0) (P.commonReturns_Hret R zero μ) hp0 hp1 hμ hη

/-- **The `η` form for a presentation, existential**: with `μ(0) ≥ p₀ > 0`, constants
depending also on `p₀` such that the fresh pairs fail with probability at most `K η_α`
whenever `η_α ≤ ε`. -/
theorem presentation_matching_eta_exists (p : Params) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hfloor : ∀ σ a, a ∈ P.S → ENNReal.ofReal c ≤ P.ν σ a) {p0 : ℝ} (hp0 : 0 < p0)
    (hp1 : p0 ≤ 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V),
      (P.toModel R zero μ).IsCompat → ENNReal.ofReal p0 ≤ μ zero →
      (P.toModel R zero μ).eta p.α ≤ ENNReal.ofReal ε →
        ∀ σ σ' h, (P.toModel R zero μ).failProb (P.freshL σ) (P.freshL σ') h
          ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).eta p.α := by
  set K0 := finiteK0 p P.Hret (P.coreInverseSum c p.α) with hK0
  have hK : K0 < K0 + 1 := by linarith
  have hεpos := finiteEps_pos p P.Hret P.Tcount P.one_le_Tcount _
    (P.one_le_coreInverseSum hc0 hc1 p.α_nonneg) _ hK
  refine ⟨finiteKmatch P.Hret (K0 + 1) / p0,
    p0 * finiteEps p P.Hret P.Tcount (P.coreInverseSum c p.α) (K0 + 1), by positivity, ?_⟩
  intro V R zero μ hcompat hμ hη σ σ' h
  exact P.presentation_matching_eta R zero μ p hc0 hc1 hfloor _ hK hcompat hp0 hp1 hμ hη _ _
    (P.phase_freshL_eq R zero μ σ σ') h

/-- **`thm:markov-matching` for a presentation under the exponent condition alone**
(`sec:admissible-exponent`): `α ≥ 1` with `λ_α < 1`. -/
theorem presentation_matching_of_lambda {α : ℝ} (hα : 1 ≤ α) (hlam : lambda α < 1) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hfloor : ∀ σ a, a ∈ P.S → ENNReal.ofReal c ≤ P.ν σ a) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V),
      (P.toModel R zero μ).IsCompat →
      (P.toModel R zero μ).zeta α ≤ ENNReal.ofReal ε →
        ∀ σ σ' h, (P.toModel R zero μ).failProb (P.freshL σ) (P.freshL σ') h
          ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta α :=
  P.presentation_matching (Params.ofLambda hα hlam) hc0 hc1 hfloor

/-! ### Uniformity over the arity masses (`thm:common-semigroup-matching`) -/

/-- **Uniformity** (`thm:common-semigroup-matching`): the constants depend only on the finite supports, the
atomic floor and the exponent"): for fixed supports, profiles and a floor `c`, constants
uniform over all presentations with these data and all core probabilities at least `c`. -/
theorem presentation_matching_uniform (p : Params) (S : Finset ℕ) (D : ℕ → MTree)
    (supp : Bool → Finset ℕ) (C : Bool → ℕ → MTree) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ P : Presentation, P.S = S → P.D = D → P.supp = supp → P.C = C →
      (∀ σ a, a ∈ S → ENNReal.ofReal c ≤ P.ν σ a) →
      ∀ {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V),
        (P.toModel R zero μ).IsCompat →
        (P.toModel R zero μ).zeta p.α ≤ ENNReal.ofReal ε →
          ∀ σ σ' h, (P.toModel R zero μ).failProb (P.freshL σ) (P.freshL σ') h
            ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta p.α := by
  by_cases hS : S.Nonempty
  · set K0 := finiteK0 p (HretOf S D supp C) (inverseSumOf S c p.α) with hK0
    have hK : K0 < K0 + 1 := by linarith
    refine ⟨finiteKmatch (HretOf S D supp C) (K0 + 1),
      finiteEps p (HretOf S D supp C) (TcountOf supp C) (inverseSumOf S c p.α) (K0 + 1),
      finiteEps_pos p _ _ (one_le_TcountOf supp C) _ (one_le_inverseSumOf hS hc0 hc1 p.α_nonneg)
        _ hK, ?_⟩
    intro P hPS hPD hPsupp hPC hfloor V R zero μ hcompat hζ σ σ' h
    subst hPS hPD hPsupp hPC
    exact (P.presentation_matching_explicit R zero μ p hc0 hc1 hfloor _ hK hcompat hζ).1 _ _
      (P.phase_freshL_eq R zero μ σ σ') h
  · refine ⟨0, 1, one_pos, ?_⟩
    intro P hPS
    exact absurd (hPS ▸ P.S_nonempty) hS

/-- **Uniformity on the infinite tree** (`thm:common-semigroup-matching`). -/
theorem presentation_matching_uniform_infinite (p : Params) (S : Finset ℕ) (D : ℕ → MTree)
    (supp : Bool → Finset ℕ) (C : Bool → ℕ → MTree) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ P : Presentation, P.S = S → P.D = D → P.supp = supp → P.C = C →
      (∀ σ a, a ∈ S → ENNReal.ofReal c ≤ P.ν σ a) →
      ∀ {V : Type} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
        (R : V → V → Prop) (zero : V) (μ : PMF V),
        (P.toModel R zero μ).IsCompat →
        (P.toModel R zero μ).zeta p.α ≤ ENNReal.ofReal ε →
          ∀ σ σ', (P.toModel R zero μ).trajPair (P.freshL σ) (P.freshL σ')
              ((P.toModel R zero μ).InfMatchEv (P.freshL σ) (P.freshL σ'))ᶜ
            ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta p.α := by
  obtain ⟨Kc, ε, hε, hbound⟩ := presentation_matching_uniform p S D supp C hc0 hc1
  refine ⟨Kc, ε, hε, ?_⟩
  intro P hPS hPD hPsupp hPC hfloor V _ _ _ R zero μ hcompat hζ σ σ'
  exact (P.toModel R zero μ).trajPair_infFail_le _ _
    (hbound P hPS hPD hPsupp hPC hfloor R zero μ hcompat hζ σ σ')

end Presentation

/-! ### The common atomic presentation (`sec:common-generators`) -/

/-- The spine with `n + 1` leaves: a leaf at depth one on the left at every internal
vertex (a graft-free `(a+1)`-leaf profile `D_a` of `sec:common-generators`). -/
def spine : ℕ → MTree
  | 0 => MTree.leaf
  | n + 1 => MTree.node MTree.leaf (spine n)

/-- The spine with `n + 1` leaves has `n + 1` leaves. -/
lemma leaves_spine (n : ℕ) : (spine n).leaves = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [spine, MTree.leaves, ih]
    omega

/-- The spine is graft-free. -/
lemma noGraft_spine (n : ℕ) : (spine n).NoGraft := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨trivial, ih⟩

/-- A spine with at least two leaves is a node. -/
lemma spine_node {n : ℕ} (hn : 1 ≤ n) : ∃ l r, spine n = MTree.node l r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨_, _, rfl⟩

/-- A spine with at least two leaves has a leaf at depth one. -/
lemma one_mem_leafDepths_spine {n : ℕ} (hn : 1 ≤ n) : 1 ∈ (spine n).leafDepths := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [spine, MTree.leafDepths]

/-- The atoms of the branching semigroup of a finite support, as a finite set: the shifted
arities which are atoms (`thm:common-atoms`). -/
noncomputable def atomsFinset (supp : Finset ℕ) : Finset ℕ :=
  (supp.image fun k => k - 1).filter (IsAtom (shiftSemigroup ↑supp))

/-- The finite atom set is the set of atoms (`thm:common-atoms`: every atom is a shifted
arity). -/
lemma coe_atomsFinset (supp : Finset ℕ) :
    (↑(atomsFinset supp) : Set ℕ) = atoms (shiftSemigroup ↑supp) := by
  ext a
  simp only [atomsFinset, Finset.coe_filter, Finset.mem_image, Set.mem_ofPred_eq, mem_atoms]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨k, hk, hka⟩ := isAtom_mem_generators (G := (fun k => k - 1) '' ↑supp) h
  exact ⟨k, Finset.mem_coe.mp hk, hka⟩

/-- Membership in the finite atom set. -/
lemma mem_atomsFinset {supp : Finset ℕ} {a : ℕ} :
    a ∈ atomsFinset supp ↔ IsAtom (shiftSemigroup ↑supp) a := by
  rw [← Finset.mem_coe, coe_atomsFinset, mem_atoms]

/-- The common core `{a + 1 : a an atom}` (`sec:common-generators`). -/
noncomputable def atomCore (supp : Finset ℕ) : Finset ℕ := (atomsFinset supp).image fun a => a + 1

/-- The common core as a set. -/
lemma coe_atomCore (supp : Finset ℕ) :
    (↑(atomCore supp) : Set ℕ) = (fun a => a + 1) '' atoms (shiftSemigroup ↑supp) := by
  rw [atomCore, Finset.coe_image, coe_atomsFinset]

/-- Membership in the common core. -/
lemma mem_atomCore {supp : Finset ℕ} {k : ℕ} :
    k ∈ atomCore supp ↔ ∃ a, IsAtom (shiftSemigroup ↑supp) a ∧ k = a + 1 := by
  simp only [atomCore, Finset.mem_image, mem_atomsFinset]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩⟩

/-- A submonoid of `ℕ` with a positive element has an atom (`thm:common-atoms`: the atoms
generate). -/
lemma atoms_nonempty (Λ : AddSubmonoid ℕ) (h : ∃ n ∈ Λ, 0 < n) : (atoms Λ).Nonempty := by
  obtain ⟨n, hn, hpos⟩ := h
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have := mem_closure_atoms Λ hn
  rw [hempty, AddSubmonoid.closure_empty, AddSubmonoid.mem_bot] at this
  omega

/-- The shifted arity of a supported arity lies in the branching semigroup. -/
lemma sub_one_mem_shiftSemigroup {supp : Finset ℕ} {k : ℕ} (hk : k ∈ supp) :
    k - 1 ∈ shiftSemigroup ↑supp :=
  AddSubmonoid.subset_closure ⟨k, Finset.mem_coe.mpr hk, rfl⟩

/-- An expression of an element of a submonoid of `ℕ` as a sum of atoms, chosen once
(`sec:common-generators`: "All choices can be deterministic"); the empty list outside the
submonoid. -/
noncomputable def atomExpr (Λ : AddSubmonoid ℕ) (n : ℕ) : List ℕ :=
  if h : n ∈ Λ then
    Classical.choose (AddSubmonoid.exists_list_of_mem_closure (mem_closure_atoms Λ h))
  else []

/-- The chosen expression consists of atoms and sums to the element. -/
lemma atomExpr_spec {Λ : AddSubmonoid ℕ} {n : ℕ} (h : n ∈ Λ) :
    (∀ y ∈ atomExpr Λ n, y ∈ atoms Λ) ∧ (atomExpr Λ n).sum = n := by
  rw [atomExpr, dite_eq_left h]
  exact Classical.choose_spec (AddSubmonoid.exists_list_of_mem_closure (mem_closure_atoms Λ h))

/-- The chosen expression of a positive element is nonempty. -/
lemma atomExpr_ne_nil {Λ : AddSubmonoid ℕ} {n : ℕ} (h : n ∈ Λ) (hpos : 0 < n) :
    atomExpr Λ n ≠ [] := by
  intro hnil
  have := (atomExpr_spec h).2
  rw [hnil, List.sum_nil] at this
  omega

/-- Shifting the core index: a composite over the atoms with the shifted profiles is a
composite over the core arities with the original profiles. -/
lemma allComp_shift {A : Finset ℕ} {D D' : ℕ → MTree} (hD : ∀ a, D' a = D (a + 1)) :
    ∀ t : MTree, MTree.AllComp A D' t → MTree.AllComp (A.image fun a => a + 1) D t := by
  intro t
  induction t with
  | leaf => exact fun _ => trivial
  | node l r ihl ihr => exact fun h => ⟨ihl h.1, ihr h.2⟩
  | gnode l r ihl ihr =>
    rintro ⟨⟨a, ha, hDa⟩, hl, hr⟩
    exact ⟨⟨a + 1, Finset.mem_image_of_mem _ ha, hDa.trans (hD a)⟩, ihl hl, ihr hr⟩

/-- The composite profile of a supported arity `k` of the atomic presentation: the marked
core profile at a core arity, the composite of the chosen atomic expression of `k - 1`
otherwise (`sec:common-generators`). The same profile serves both sides. -/
noncomputable def atomicProfile (supp : Finset ℕ) (k : ℕ) : MTree :=
  if k ∈ atomCore supp then MTree.markRoot (spine (k - 1))
  else MTree.composite spine (atomExpr (shiftSemigroup ↑supp) (k - 1))

/-- **The common atomic presentation** of two arity laws with finite supports in
`{2, 3, …}` and equal branching semigroups (`sec:common-generators`): the core
`S = {a + 1 : a ∈ 𝒜}`, the spine profiles `D_{a+1}`, and the composites of the chosen
atomic expressions. -/
noncomputable def atomicPresentation (νL νR : PMF ℕ) (suppL suppR : Finset ℕ)
    (hL : ∀ k, νL k ≠ 0 ↔ k ∈ suppL) (hR : ∀ k, νR k ≠ 0 ↔ k ∈ suppR)
    (h2L : ∀ k ∈ suppL, 2 ≤ k) (h2R : ∀ k ∈ suppR, 2 ≤ k) (hne : suppL.Nonempty)
    (hsem : shiftSemigroup ↑suppL = shiftSemigroup ↑suppR) : Presentation where
  S := atomCore suppL
  D := fun a => spine (a - 1)
  ν := fun σ => if σ then νR else νL
  supp := fun σ => if σ then suppR else suppL
  C := fun _ k => atomicProfile suppL k
  mem_supp := by
    intro σ k
    cases σ
    · simpa using hL k
    · simpa using hR k
  S_nonempty := by
    obtain ⟨k, hk⟩ := hne
    have hpos : 0 < k - 1 := by have := h2L k hk; omega
    obtain ⟨a, ha⟩ := atoms_nonempty (shiftSemigroup ↑suppL)
      ⟨k - 1, sub_one_mem_shiftSemigroup hk, hpos⟩
    exact ⟨a + 1, mem_atomCore.mpr ⟨a, ha, rfl⟩⟩
  two_le_S := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_atomCore.mp ha
    have := ha'.pos
    omega
  D_leaves := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_atomCore.mp ha
    simp [leaves_spine]
  D_noGraft := fun a _ => noGraft_spine _
  D_node := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_atomCore.mp ha
    exact spine_node (by have := ha'.pos; omega)
  S_subset_supp := by
    intro σ a ha
    obtain ⟨a', ha', rfl⟩ := mem_atomCore.mp ha
    have h := atoms_subset_inter hsem a' ha'
    cases σ
    · simpa using h.1
    · simpa using h.2
  two_le_supp := by
    intro σ k hk
    cases σ
    · exact h2L k (by simpa using hk)
    · exact h2R k (by simpa using hk)
  C_leaves := by
    intro σ k hk
    have hk2 : 2 ≤ k := by
      cases σ
      · exact h2L k (by simpa using hk)
      · exact h2R k (by simpa using hk)
    have hkΛ : k - 1 ∈ shiftSemigroup ↑suppL := by
      cases σ
      · exact sub_one_mem_shiftSemigroup (by simpa using hk)
      · rw [hsem]
        exact sub_one_mem_shiftSemigroup (by simpa using hk)
    unfold atomicProfile
    split_ifs with hS
    · rw [MTree.leaves_markRoot, leaves_spine]
      omega
    · rw [MTree.leaves_composite spine _ fun a _ => leaves_spine a, (atomExpr_spec hkΛ).2]
      omega
  C_gnode := by
    intro σ k hk
    have hk2 : 2 ≤ k := by
      cases σ
      · exact h2L k (by simpa using hk)
      · exact h2R k (by simpa using hk)
    have hkΛ : k - 1 ∈ shiftSemigroup ↑suppL := by
      cases σ
      · exact sub_one_mem_shiftSemigroup (by simpa using hk)
      · rw [hsem]
        exact sub_one_mem_shiftSemigroup (by simpa using hk)
    unfold atomicProfile
    split_ifs with hS
    · obtain ⟨l, r, hlr⟩ := spine_node (n := k - 1) (by omega)
      exact ⟨l, r, by rw [hlr]; rfl⟩
    · have hne' := atomExpr_ne_nil hkΛ (by omega)
      obtain ⟨a, as, has⟩ := List.exists_cons_of_ne_nil hne'
      rw [has]
      refine MTree.composite_cons spine a as fun b hb => spine_node ?_
      have hb' := (atomExpr_spec hkΛ).1 b (has ▸ hb)
      exact (mem_atoms.mp hb').pos
  C_allComp := by
    intro σ k hk
    have hkΛ : k - 1 ∈ shiftSemigroup ↑suppL := by
      cases σ
      · exact sub_one_mem_shiftSemigroup (by simpa using hk)
      · rw [hsem]
        exact sub_one_mem_shiftSemigroup (by simpa using hk)
    unfold atomicProfile
    split_ifs with hS
    · obtain ⟨a', ha', rfl⟩ := mem_atomCore.mp hS
      obtain ⟨l, r, hlr⟩ := spine_node (n := a' + 1 - 1) (by have := ha'.pos; omega)
      have hng := noGraft_spine (a' + 1 - 1)
      rw [hlr] at hng ⊢
      refine ⟨⟨a' + 1, hS, ?_⟩, MTree.allComp_of_noGraft hng.1, MTree.allComp_of_noGraft hng.2⟩
      rw [MTree.flatten_eq_self_of_noGraft hng.1, MTree.flatten_eq_self_of_noGraft hng.2]
      exact hlr.symm
    · refine allComp_shift (A := atomsFinset suppL) (D := fun a => spine (a - 1)) (D' := spine)
        (fun a => by simp) _ ?_
      refine MTree.allComp_composite _ spine _ ?_ ?_
      · intro a ha
        have ha' := (atomExpr_spec hkΛ).1 a ha
        exact ⟨noGraft_spine a, spine_node (mem_atoms.mp ha').pos⟩
      · intro a ha
        exact mem_atomsFinset.mpr (mem_atoms.mp ((atomExpr_spec hkΛ).1 a ha))
  C_core := by
    intro σ a ha
    unfold atomicProfile
    rw [ite_eq_left ha]

/-- The core of the atomic presentation. -/
lemma atomicPresentation_S (νL νR : PMF ℕ) (suppL suppR : Finset ℕ)
    (hL : ∀ k, νL k ≠ 0 ↔ k ∈ suppL) (hR : ∀ k, νR k ≠ 0 ↔ k ∈ suppR)
    (h2L : ∀ k ∈ suppL, 2 ≤ k) (h2R : ∀ k ∈ suppR, 2 ≤ k) (hne : suppL.Nonempty)
    (hsem : shiftSemigroup ↑suppL = shiftSemigroup ↑suppR) :
    (atomicPresentation νL νR suppL suppR hL hR h2L h2R hne hsem).S = atomCore suppL := rfl

/-- The atomic presentation has a core profile with a leaf at depth one, so `g = 1` and
`H = 2ℓ` (`sec:return-times`: "For the atomic profiles with a depth-one leaf, the return
argument has no periodicity"). -/
lemma atomicPresentation_depthOne (νL νR : PMF ℕ) (suppL suppR : Finset ℕ)
    (hL : ∀ k, νL k ≠ 0 ↔ k ∈ suppL) (hR : ∀ k, νR k ≠ 0 ↔ k ∈ suppR)
    (h2L : ∀ k ∈ suppL, 2 ≤ k) (h2R : ∀ k ∈ suppR, 2 ≤ k) (hne : suppL.Nonempty)
    (hsem : shiftSemigroup ↑suppL = shiftSemigroup ↑suppR) :
    ∃ a ∈ (atomicPresentation νL νR suppL suppR hL hR h2L h2R hne hsem).S,
      1 ∈ ((atomicPresentation νL νR suppL suppR hL hR h2L h2R hne hsem).D a).leafDepths := by
  obtain ⟨a, ha⟩ := (atomicPresentation νL νR suppL suppR hL hR h2L h2R hne hsem).S_nonempty
  refine ⟨a, ha, ?_⟩
  obtain ⟨a', ha', rfl⟩ := mem_atomCore.mp ha
  exact one_mem_leafDepths_spine (n := a' + 1 - 1) (by have := ha'.pos; omega)

/-- **Existence of a common presentation** (`sec:common-generators`): two arity laws with
finite supports in `{2, 3, …}` and equal branching semigroups admit a presentation with the
given laws and supports and the core `{a + 1 : a an atom}`. -/
theorem exists_presentation (νL νR : PMF ℕ) (suppL suppR : Finset ℕ)
    (hL : ∀ k, νL k ≠ 0 ↔ k ∈ suppL) (hR : ∀ k, νR k ≠ 0 ↔ k ∈ suppR)
    (h2L : ∀ k ∈ suppL, 2 ≤ k) (h2R : ∀ k ∈ suppR, 2 ≤ k) (hne : suppL.Nonempty)
    (hsem : shiftSemigroup ↑suppL = shiftSemigroup ↑suppR) :
    ∃ P : Presentation, P.ν = (fun σ => if σ then νR else νL)
      ∧ P.supp = (fun σ => if σ then suppR else suppL)
      ∧ (↑P.S : Set ℕ) = (fun a => a + 1) '' atoms (shiftSemigroup ↑suppL) :=
  ⟨atomicPresentation νL νR suppL suppR hL hR h2L h2R hne hsem, rfl, rfl, coe_atomCore suppL⟩

/-! ### The floor of a fixed pair of laws (`thm:common-semigroup-matching`) -/

namespace Presentation

variable (P : Presentation)

/-- **The core floor is automatically positive** (the paragraph following
`thm:common-semigroup-matching`): for each fixed pair of
arity laws this floor is automatically positive, since the finite atomic core belongs to
both supports"): some `0 < c ≤ 1` is a lower bound for every core probability on either
side. -/
theorem exists_floor : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ σ a, a ∈ P.S → ENNReal.ofReal c ≤ P.ν σ a := by
  have hne : (P.S ×ˢ (Finset.univ : Finset Bool)).Nonempty :=
    P.S_nonempty.product Finset.univ_nonempty
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image (P.S ×ˢ Finset.univ) (fun x => (P.ν x.2 x.1).toReal) hne
  have hpos : ∀ σ a, a ∈ P.S → 0 < (P.ν σ a).toReal := by
    intro σ a ha
    have h0 : P.ν σ a ≠ 0 := (P.mem_supp σ a).mpr (P.S_subset_supp σ ha)
    exact ENNReal.toReal_pos h0 (PMF.apply_ne_top _ _)
  have hx' : x.1 ∈ P.S := (Finset.mem_product.mp hx).1
  refine ⟨(P.ν x.2 x.1).toReal, hpos x.2 x.1 hx', ?_, ?_⟩
  · calc (P.ν x.2 x.1).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
      _ = 1 := ENNReal.toReal_one
  · intro σ a ha
    calc ENNReal.ofReal (P.ν x.2 x.1).toReal ≤ ENNReal.ofReal (P.ν σ a).toReal :=
          ENNReal.ofReal_le_ofReal
            (hmin (a, σ) (Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩))
      _ = P.ν σ a := ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)

/-- **`thm:markov-matching` for a presentation without a prescribed floor**: constants
depending only on the exponent parameters and the presentation. -/
theorem presentation_matching_auto (p : Params) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V),
      (P.toModel R zero μ).IsCompat →
      (P.toModel R zero μ).zeta p.α ≤ ENNReal.ofReal ε →
        ∀ σ σ' h, (P.toModel R zero μ).failProb (P.freshL σ) (P.freshL σ') h
          ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta p.α := by
  obtain ⟨c, hc0, hc1, hfloor⟩ := P.exists_floor
  exact P.presentation_matching p hc0 hc1 hfloor

end Presentation

/-- **The headline application** (the "In particular" after `thm:markov-matching`): two
product laws with finite arity supports in `{2, 3, …}` and the same branching semigroup admit
a common presentation, and for it there are constants such that, for every state space with
`ζ_α ≤ ε`, the two fresh initial types match at every height with failure probability at
most `K ζ_α`. -/
theorem two_laws_matching (p : Params) (νL νR : PMF ℕ) (suppL suppR : Finset ℕ)
    (hL : ∀ k, νL k ≠ 0 ↔ k ∈ suppL) (hR : ∀ k, νR k ≠ 0 ↔ k ∈ suppR)
    (h2L : ∀ k ∈ suppL, 2 ≤ k) (h2R : ∀ k ∈ suppR, 2 ≤ k) (hne : suppL.Nonempty)
    (hsem : shiftSemigroup ↑suppL = shiftSemigroup ↑suppR) :
    ∃ P : Presentation, P.ν = (fun σ => if σ then νR else νL)
      ∧ P.supp = (fun σ => if σ then suppR else suppL)
      ∧ ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V),
          (P.toModel R zero μ).IsCompat →
          (P.toModel R zero μ).zeta p.α ≤ ENNReal.ofReal ε →
            ∀ σ σ' h, (P.toModel R zero μ).failProb (P.freshL σ) (P.freshL σ') h
              ≤ ENNReal.ofReal Kc * (P.toModel R zero μ).zeta p.α :=
  ⟨atomicPresentation νL νR suppL suppR hL hR h2L h2R hne hsem, rfl, rfl,
    (atomicPresentation νL νR suppL suppR hL hR h2L h2R hne hsem).presentation_matching_auto p⟩

end GraphMarkovMatching.Stopped
