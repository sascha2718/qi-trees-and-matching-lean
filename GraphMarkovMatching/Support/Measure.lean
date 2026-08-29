/-
The infinite-tree / measure step for `G_k` (the measure half of
`thm:konig` in `arbitrary_offspring_matching.tex`). Two independent infinite labelled
trees carry, at each finite height `n`, the pair of restrictions `(X_n, Y_n)`;
the height-`n` matching event is `E_n = {ω : fullSimK R₀ k m n (X_n ω) (Y_n ω)}`.
Restriction gives `E_{n+1} ⊆ E_n` (`fullSimK_restrict`), König's lemma gives
`M = ⋂ E_n` (`infMatchK_iff_forall_level`), and continuity from above lifts the
uniform finite bound of `ConcreteBlock.lean` to the infinite tree:

    P(some g ∈ G_k matches every vertex) ≥ 1 - (2+ρ)^(k-1)·41e.

The probability space and its level projections enter as an interface (`hmeas`,
`hlaw`); the Kolmogorov-type construction discharging them is supplied at the
point of use (`Closure/Measure.lean`, `Archive/Extension.lean`).
-/
import GraphMarkovMatching.Support.Konig
import GraphMarkovMatching.Support.ConcreteBlock
import Mathlib.MeasureTheory.Measure.MeasureSpace
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
    simp only [Set.mem_iInter, hE, Set.mem_setOf_eq]
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
    rw [hs, Set.compl_setOf]
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
  · simp [Set.mem_setOf_eq, h]
  · simp [Set.mem_setOf_eq, prodPMF_apply, h]

instance instCountableFullLab [Countable V] : (n : ℕ) → Countable (FullLab V n)
  | 0 => ‹Countable V›
  | n + 1 => by
      haveI := instCountableFullLab n
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
      haveI : MeasurableSingletonClass (FullLab V n) := instMeasurableSingletonFullLab n
      exact inferInstanceAs (MeasurableSingletonClass (V × (FullLab V n × FullLab V n)))

/-- **The `G_k` matching theorem on the infinite tree, from the product law.**
If the height-`n` projections `(X_n, Y_n)` have the i.i.d. pair law
`fullMuK ⊗ fullMuK` at the root phase `k-1` (the Kolmogorov marginals), then
under the parameter and numeric hypotheses of `ConcreteBlock.lean`,

    P(some g ∈ G_k matches every vertex) ≥ 1 - (2+ρ)^(k-1)·41e.

This closes the infinite-tree case up to the standard existence of the i.i.d.
product measure (the pending `GraphMatching/Kolmogorov.lean` port). -/
theorem karyMatching_infinite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    {α δ L K ρ e : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (he : 0 ≤ e)
    (ν : ℕ → PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a) (k : ℕ)
    (hη : ∀ m, m ≤ k - 1 → Phi α (ν m) R₀ ≤ ENNReal.ofReal e)
    (hsmall : 2 * α * ((2 + ρ) ^ (k - 1) * (41 * e)) ≤ ρ / 2)
    (hAm : (2 * L + 2 * (1 + δ) * K) * ((2 + ρ) ^ (k - 1) * 41) ≤ 35)
    (hCm : (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
        * ((2 + ρ) ^ (k - 1) * (41 * e)) * ((2 + ρ) ^ (k - 1) * 41) ≤ 1)
    (X Y : (n : ℕ) → Ω → FullLab V n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, P.map (fun ω => (X n ω, Y n ω))
        = (prodPMF (fullMuK ν k (k - 1) n) (fullMuK ν k (k - 1) n)).toMeasure) :
    1 - ENNReal.ofReal ((2 + ρ) ^ (k - 1) * (41 * e))
      ≤ P {ω | InfMatchK R₀ k (k - 1) (fun n => X n ω) (fun n => Y n ω)} := by
  refine infinite_tree_matchingK_prob P R₀ k (k - 1) X Y hX hY (fun n => ?_) _ (fun n => ?_)
  · exact (hpair n)
      ((Set.to_countable
        {p : FullLab V n × FullLab V n | fullSimK R₀ k (k - 1) n p.1 p.2}).measurableSet)
  · rw [show {ω | ¬ fullSimK R₀ k (k - 1) n (X n ω) (Y n ω)}
          = (fun ω => (X n ω, Y n ω)) ⁻¹' {p | ¬ fullSimK R₀ k (k - 1) n p.1 p.2} from rfl,
      ← Measure.map_apply (hpair n) ((Set.to_countable _).measurableSet), hlaw n,
      prodPMF_toMeasure_not_rel]
    exact karyMatching_failure_le hα hδ hL0 hK0 hL hK hρ0 hρ1 he ν R₀ hrefl hsymm k
      hη hsmall hAm hCm n

end GraphMarkovMatching.Support
