/-
`sec:reduction` of `graph_matching_selfcontained.tex`, the infinite-tree / measure step.
Two independent infinite labelled trees carry, at each finite level `h`, the pair
of restrictions `(X_h, Y_h)`; the height-`h` matching event is
`𝓜_h = {ω : fullSim R₀ h (X_h ω) (Y_h ω)}`, written `E h` in the proofs below.
Restriction gives `𝓜_{h+1} ⊆ 𝓜_h` (`fullSim_restrict`), and König's lemma gives
`M = ⋂ 𝓜_h` (`infMatch_iff_forall_level`, the `←` being
`infinite_matching_of_forall_level`). Continuity from above (`prob_iInter_ge`) then
lifts the finite bound `P(𝓜_h) ≥ 1 - 16Φ₀` (`full_matching_bound`) to
`P(M) ≥ 1 - 16Φ₀` (`infinite_tree_matching_prob`).

The probability space and its level projections enter as an interface: `hmeas`
(the `𝓜_h` are measurable) and `hfail` (the level-`h` failure event has the finite
i.i.d. failure probability). Both hold for the standard Kolmogorov / product
measure on the infinite tree; `hfail` is exactly the statement that the level-`h`
projections are two independent `fullMu`-labellings.
-/
import GraphMatching.Konig
import GraphMatching.Reduction
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace GraphMatching

open scoped ENNReal Classical Topology
open MeasureTheory Filter

/-! ### Continuity from above -/

/-- **Continuity from above**: for a decreasing sequence of measurable events each
of probability `≥ c`, the intersection also has probability `≥ c`. -/
lemma prob_iInter_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E : ℕ → Set Ω} (hmeas : ∀ n, MeasurableSet (E n)) (hanti : Antitone E)
    {c : ℝ≥0∞} (hbound : ∀ n, c ≤ P (E n)) :
    c ≤ P (⋂ n, E n) := by
  have htend : Tendsto (fun n => P (E n)) atTop (𝓝 (P (⋂ n, E n))) :=
    tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top P _⟩
  exact ge_of_tendsto' htend hbound

/-! ### The König set-identity -/

universe u
variable {V : Type u}

/-- Restriction preserves the full relation: a level-`(h+1)` matching restricts to
a level-`h` one. -/
lemma fullSim_restrict (R₀ : V → V → Prop) (h : ℕ) (x y : FullLab V (h + 1))
    (hsim : fullSim R₀ (h + 1) x y) :
    fullSim R₀ h (restrictLab h x) (restrictLab h y) := by
  obtain ⟨π, hπ⟩ := hsim
  exact ⟨restrictAut h π, fullMatchesA_restrict R₀ h π x y hπ⟩

/-- **`M = ⋂ 𝓜_h` in pointwise form**: for compatible infinite labellings, an
infinite-tree matching exists iff there is a matching at every finite level. The
`←` direction is König's lemma (`infinite_matching_of_forall_level`). -/
lemma infMatch_iff_forall_level (R₀ : V → V → Prop) (X Y : (h : ℕ) → FullLab V h)
    (hX : ∀ h, restrictLab h (X (h + 1)) = X h) (hY : ∀ h, restrictLab h (Y (h + 1)) = Y h) :
    InfMatch R₀ X Y ↔ ∀ h, fullSim R₀ h (X h) (Y h) := by
  constructor
  · rintro ⟨σ, _, hgood⟩ h
    exact ⟨σ h, hgood h⟩
  · intro hlevel
    exact infinite_matching_of_forall_level R₀ X Y hX hY hlevel

/-! ### The packaged measure-layer theorem -/

/-- **The infinite-tree matching bound (`sec:reduction`, infinite-tree paragraph).**
Given a probability space carrying two infinite labellings via compatible level
projections `X, Y`, with each level-`h` matching event of probability `≥ c`, the
event that a single automorphism of the infinite tree matches every vertex also
has probability `≥ c`. `𝓜_{h+1} ⊆ 𝓜_h` and `M = ⋂ 𝓜_h` are proved here from
restriction and König; `hbound` is the finite-level input. -/
theorem infinite_tree_matching_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R₀ : V → V → Prop)
    (X Y : (h : ℕ) → Ω → FullLab V h)
    (hX : ∀ h ω, restrictLab h (X (h + 1) ω) = X h ω)
    (hY : ∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω)
    (hmeas : ∀ h, MeasurableSet {ω | fullSim R₀ h (X h ω) (Y h ω)})
    (c : ℝ≥0∞) (hbound : ∀ h, c ≤ P {ω | fullSim R₀ h (X h ω) (Y h ω)}) :
    c ≤ P {ω | InfMatch R₀ (fun h => X h ω) (fun h => Y h ω)} := by
  set E : ℕ → Set Ω := fun h => {ω | fullSim R₀ h (X h ω) (Y h ω)} with hE
  have hanti : Antitone E := by
    apply antitone_nat_of_succ_le
    intro h ω hω
    have hr := fullSim_restrict R₀ h (X (h + 1) ω) (Y (h + 1) ω) hω
    rw [hX h ω, hY h ω] at hr
    exact hr
  have hM : {ω | InfMatch R₀ (fun h => X h ω) (fun h => Y h ω)} = ⋂ h, E h := by
    ext ω
    simp only [Set.mem_iInter, hE, Set.mem_ofPred_eq]
    exact infMatch_iff_forall_level R₀ (fun h => X h ω) (fun h => Y h ω)
      (fun h => hX h ω) (fun h => hY h ω)
  rw [hM]
  exact prob_iInter_ge P hmeas hanti hbound

/-- **The infinite-tree matching bound with the explicit constant (`thm:matching`,
infinite-tree statement).** When the level-`h` projections are distributed as two
independent i.i.d. labellings (so the failure event has the finite i.i.d. failure
probability, `hfail`), `full_matching_bound` gives `P(𝓜_h) ≥ 1 - 16Φ₀`, and the
previous theorem lifts it: `P(some automorphism of the infinite tree matches every
vertex) ≥ 1 - 16Φ₀`. -/
theorem infinite_tree_matching_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a) (hη : Phi μ R₀ ≤ 1 / 10000)
    (X Y : (h : ℕ) → Ω → FullLab V h)
    (hX : ∀ h ω, restrictLab h (X (h + 1) ω) = X h ω)
    (hY : ∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω)
    (hmeas : ∀ h, MeasurableSet {ω | fullSim R₀ h (X h ω) (Y h ω)})
    (hfail : ∀ h, P {ω | ¬ fullSim R₀ h (X h ω) (Y h ω)}
        = ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim R₀ h) x) :
    1 - 16 * Phi μ R₀ ≤ P {ω | InfMatch R₀ (fun h => X h ω) (fun h => Y h ω)} := by
  refine infinite_tree_matching_ge P R₀ X Y hX hY hmeas (1 - 16 * Phi μ R₀) (fun h => ?_)
  set s : Set Ω := {ω | fullSim R₀ h (X h ω) (Y h ω)} with hs
  have hsmeas : MeasurableSet s := hmeas h
  have hcompl : sᶜ = {ω | ¬ fullSim R₀ h (X h ω) (Y h ω)} := by rw [hs, Set.compl_ofPred]
  have h2 : P sᶜ ≤ 16 * Phi μ R₀ := by
    rw [hcompl, hfail h]; exact full_matching_bound μ R₀ hrefl hsymm hη h
  have h3 : (1 : ℝ≥0∞) - P sᶜ = P s := by
    rw [prob_compl_eq_one_sub hsmeas]; exact ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one
  calc (1 : ℝ≥0∞) - 16 * Phi μ R₀ ≤ 1 - P sᶜ := tsub_le_tsub_left h2 1
    _ = P s := h3

/-! ### The `hfail` hypothesis from the product law

`hfail` above is the statement that the level-`h` projections have the i.i.d.
product law. Here that is reduced to the pushforward law
`P.map (X_h, Y_h) = μ_h ⊗ μ_h` (the Kolmogorov marginals), via a `PMF.toMeasure`
computation identifying the measure of the failure set with the mean bad degree.
Everything is discrete, so measurability is automatic (`FullLab V h` is countable
with all singletons measurable). -/

/-- The product-PMF measure of the "not related" set is the mean bad degree
`𝔼[q]`. -/
lemma prodPMF_toMeasure_not_rel {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W]
    [Countable W] (ν : PMF W) (R : W → W → Prop) :
    (prodPMF ν ν).toMeasure {p : W × W | ¬ R p.1 p.2} = ∑' x, ν x * qE ν R x := by
  rw [(prodPMF ν ν).toMeasure_apply ((Set.to_countable _).measurableSet), ENNReal.tsum_prod']
  refine tsum_congr fun x => ?_
  rw [qE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  rw [Set.indicator_apply]
  by_cases h : R x y
  · simp [Set.mem_ofPred_eq, h]
  · simp [Set.mem_ofPred_eq, prodPMF_apply, h]

instance instCountableFullLab [Countable V] : (h : ℕ) → Countable (FullLab V h)
  | 0 => ‹Countable V›
  | h + 1 => by
      have := instCountableFullLab h
      exact inferInstanceAs (Countable (V × (FullLab V h × FullLab V h)))

instance instMeasurableFullLab [MeasurableSpace V] : (h : ℕ) → MeasurableSpace (FullLab V h)
  | 0 => ‹MeasurableSpace V›
  | h + 1 => by
      haveI := instMeasurableFullLab h
      exact inferInstanceAs (MeasurableSpace (V × (FullLab V h × FullLab V h)))

instance instMeasurableSingletonFullLab [MeasurableSpace V] [MeasurableSingletonClass V] :
    (h : ℕ) → MeasurableSingletonClass (FullLab V h)
  | 0 => ‹MeasurableSingletonClass V›
  | h + 1 => by
      have : MeasurableSingletonClass (FullLab V h) := instMeasurableSingletonFullLab h
      exact inferInstanceAs (MeasurableSingletonClass (V × (FullLab V h × FullLab V h)))

/-- **`thm:matching`, infinite-tree statement, from the product law.** If the level-`h`
projections `(X_h, Y_h)` have the i.i.d. product law `μ_h ⊗ μ_h` (the Kolmogorov
marginals), then `P(some automorphism of the infinite tree matches every vertex)
≥ 1 - 16Φ₀`. This closes the infinite-tree case of `thm:matching` up to the standard
existence of the i.i.d. product measure. -/
theorem infinite_tree_matching_prob_of_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a) (hη : Phi μ R₀ ≤ 1 / 10000)
    (X Y : (h : ℕ) → Ω → FullLab V h)
    (hX : ∀ h ω, restrictLab h (X (h + 1) ω) = X h ω)
    (hY : ∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω)
    (hpair : ∀ h, Measurable (fun ω => (X h ω, Y h ω)))
    (hlaw : ∀ h, P.map (fun ω => (X h ω, Y h ω))
        = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) :
    1 - 16 * Phi μ R₀ ≤ P {ω | InfMatch R₀ (fun h => X h ω) (fun h => Y h ω)} := by
  refine infinite_tree_matching_prob P μ R₀ hrefl hsymm hη X Y hX hY (fun h => ?_) (fun h => ?_)
  · exact (hpair h)
      ((Set.to_countable {p : FullLab V h × FullLab V h | fullSim R₀ h p.1 p.2}).measurableSet)
  · rw [show {ω | ¬ fullSim R₀ h (X h ω) (Y h ω)}
          = (fun ω => (X h ω, Y h ω)) ⁻¹' {p | ¬ fullSim R₀ h p.1 p.2} from rfl,
      ← Measure.map_apply (hpair h) ((Set.to_countable _).measurableSet), hlaw h,
      prodPMF_toMeasure_not_rel]

end GraphMatching
