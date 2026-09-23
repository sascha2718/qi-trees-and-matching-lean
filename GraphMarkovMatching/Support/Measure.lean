/-
Uniform finite-height matching bounds pass to the infinite tree. Restriction makes the
finite matching events decrease; König's lemma identifies their intersection with the
infinite matching event, and continuity of probability gives a matching probability of
at least `1 - b` from a uniform finite failure bound `b`.

The probability space and consistent measurable level projections are arbitrary.
`Support.Trajectory` constructs such a space from consistent finite laws, while
`Stopped.Transfer` applies the estimate on a prescribed probability space.
-/
import GraphMarkovMatching.Support.Konig
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace GraphMarkovMatching.Support

open scoped ENNReal Classical Topology
open MeasureTheory Filter

/-! ### Continuity from above -/

/-- **Continuity from above**: for a decreasing sequence of measurable events
each of probability `≥ c`, the intersection also has probability `≥ c`. -/
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

/-- Restriction preserves the relation: a height-`(n+1)` matching restricts to
a height-`n` one, at every phase. -/
lemma fullSimK_restrict (R₀ : V → V → Prop) (k m n : ℕ) (x y : FullLab V (n + 1))
    (h : fullSimK R₀ k m (n + 1) x y) :
    fullSimK R₀ k m n (restrictLab n x) (restrictLab n y) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨restrictAutK k m n π, fullMatchesK_restrict R₀ k n m π x y hπ⟩

/-- **`M = ⋂ E_n` in pointwise form**: for compatible infinite labellings, an
infinite-tree matching in `G_k` exists iff there is a matching at every finite
height. The `←` direction is König's lemma. -/
lemma infMatchK_iff_forall_level (R₀ : V → V → Prop) (k m : ℕ)
    (X Y : (n : ℕ) → FullLab V n)
    (hX : ∀ n, restrictLab n (X (n + 1)) = X n)
    (hY : ∀ n, restrictLab n (Y (n + 1)) = Y n) :
    InfMatchK R₀ k m X Y ↔ ∀ n, fullSimK R₀ k m n (X n) (Y n) := by
  constructor
  · rintro ⟨σ, _, hgood⟩ n
    exact ⟨σ n, hgood n⟩
  · intro hlevel
    exact infinite_matchingK_of_forall_level R₀ k m X Y hX hY hlevel

/-! ### The packaged measure-layer theorems -/

/-- **The infinite-tree matching bound (abstract form).** Given a probability
space carrying two infinite labellings via compatible level projections, with
each height-`n` matching event of probability `≥ c`, the event that a single
element of `G_k` matches every vertex also has probability `≥ c`. -/
theorem infinite_tree_matchingK_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R₀ : V → V → Prop) (k m : ℕ)
    (X Y : (n : ℕ) → Ω → FullLab V n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hmeas : ∀ n, MeasurableSet {ω | fullSimK R₀ k m n (X n ω) (Y n ω)})
    (c : ℝ≥0∞) (hbound : ∀ n, c ≤ P {ω | fullSimK R₀ k m n (X n ω) (Y n ω)}) :
    c ≤ P {ω | InfMatchK R₀ k m (fun n => X n ω) (fun n => Y n ω)} := by
  set E : ℕ → Set Ω := fun n => {ω | fullSimK R₀ k m n (X n ω) (Y n ω)} with hE
  have hanti : Antitone E := by
    apply antitone_nat_of_succ_le
    intro n ω hω
    have hr := fullSimK_restrict R₀ k m n (X (n + 1) ω) (Y (n + 1) ω) hω
    rw [hX n ω, hY n ω] at hr
    exact hr
  have hM : {ω | InfMatchK R₀ k m (fun n => X n ω) (fun n => Y n ω)} = ⋂ n, E n := by
    ext ω
    simp only [Set.mem_iInter, hE, Set.mem_ofPred_eq]
    exact infMatchK_iff_forall_level R₀ k m (fun n => X n ω) (fun n => Y n ω)
      (fun n => hX n ω) (fun n => hY n ω)
  rw [hM]
  exact prob_iInter_ge P hmeas hanti hbound

/-- The complement form: a uniform bound `b` on the height-`n` failure
probabilities gives `P(infinite matching) ≥ 1 - b`. -/
theorem infinite_tree_matchingK_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R₀ : V → V → Prop) (k m : ℕ)
    (X Y : (n : ℕ) → Ω → FullLab V n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hmeas : ∀ n, MeasurableSet {ω | fullSimK R₀ k m n (X n ω) (Y n ω)})
    (b : ℝ≥0∞)
    (hfail : ∀ n, P {ω | ¬ fullSimK R₀ k m n (X n ω) (Y n ω)} ≤ b) :
    1 - b ≤ P {ω | InfMatchK R₀ k m (fun n => X n ω) (fun n => Y n ω)} := by
  refine infinite_tree_matchingK_ge P R₀ k m X Y hX hY hmeas (1 - b) (fun n => ?_)
  set s : Set Ω := {ω | fullSimK R₀ k m n (X n ω) (Y n ω)} with hs
  have hsmeas : MeasurableSet s := hmeas n
  have hcompl : sᶜ = {ω | ¬ fullSimK R₀ k m n (X n ω) (Y n ω)} := by
    rw [hs, Set.compl_ofPred]
  have h2 : P sᶜ ≤ b := by rw [hcompl]; exact hfail n
  have h3 : (1 : ℝ≥0∞) - P sᶜ = P s := by
    rw [prob_compl_eq_one_sub hsmeas]
    exact ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one
  calc (1 : ℝ≥0∞) - b ≤ 1 - P sᶜ := tsub_le_tsub_left h2 1
    _ = P s := h3

/-! ### The failure probability from the product law -/

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

instance instCountableFullLab [Countable V] : (n : ℕ) → Countable (FullLab V n)
  | 0 => ‹Countable V›
  | n + 1 => by
      have := instCountableFullLab n
      exact inferInstanceAs (Countable (V × (FullLab V n × FullLab V n)))

instance instMeasurableFullLab [MeasurableSpace V] : (n : ℕ) → MeasurableSpace (FullLab V n)
  | 0 => ‹MeasurableSpace V›
  | n + 1 => by
      haveI := instMeasurableFullLab n
      exact inferInstanceAs (MeasurableSpace (V × (FullLab V n × FullLab V n)))

instance instMeasurableSingletonFullLab [MeasurableSpace V] [MeasurableSingletonClass V] :
    (n : ℕ) → MeasurableSingletonClass (FullLab V n)
  | 0 => ‹MeasurableSingletonClass V›
  | n + 1 => by
      have : MeasurableSingletonClass (FullLab V n) := instMeasurableSingletonFullLab n
      exact inferInstanceAs (MeasurableSingletonClass (V × (FullLab V n × FullLab V n)))

end GraphMarkovMatching.Support
