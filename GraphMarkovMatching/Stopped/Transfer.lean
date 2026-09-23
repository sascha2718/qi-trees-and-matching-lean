/-
Transfer of a uniform finite-height matching bound to any probability space carrying
two consistent Markov labellings with the specified independent finite marginals.
-/
import GraphMarkovMatching.Stopped.Projection
import GraphMarkovMatching.Stopped.Infinite

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

namespace Model

variable {V I : Type} (M : Model V I)
  [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Forgetting the type coordinates preserves the finite failure probability. -/
lemma state_prodPMF_toMeasure_not_sim (s t : I) (n : ℕ) :
    (prodPMF ((M.rho s n).map (statesOf' n)) ((M.rho t n).map (statesOf' n))).toMeasure
        {p : FullLab V n × FullLab V n | ¬ fullSim M.R n p.1 p.2}
      = M.failProb s t n := by
  rw [← prodPMF_map_prod, PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  have heq : (Prod.map (statesOf' n) (statesOf' n)) ⁻¹'
      {p : FullLab V n × FullLab V n | ¬ fullSim M.R n p.1 p.2}
      = {p : FullLab (I × V) n × FullLab (I × V) n | ¬ M.sim n p.1 p.2} := by
    ext p
    exact not_congr (fullSim_srel_iff M n p.1 p.2).symm
  rw [heq, M.prodPMF_toMeasure_not_sim]

/-- A uniform failure bound applies to any consistent pair with the model's finite
product marginals, independently of the construction of its probability space. -/
theorem infFail_le_of_marginals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s t : I)
    (X Y : (n : ℕ) → Ω → FullLab (I × V) n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hmeas : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, P.map (fun ω => (X n ω, Y n ω))
      = (prodPMF (M.rho s n) (M.rho t n)).toMeasure)
    (b : ℝ≥0∞) (hfail : ∀ n, M.failProb s t n ≤ b) :
    P {ω | ¬ InfMatch M.srel (fun n => X n ω) (fun n => Y n ω)} ≤ b := by
  let E : ℕ → Set Ω := fun n => {ω | ¬ M.sim n (X n ω) (Y n ω)}
  have hmono : Monotone E := by
    apply monotone_nat_of_le_succ
    intro n ω hn hnext
    apply hn
    have hr := fullSimK_restrict M.srel 1 0 n (X (n + 1) ω) (Y (n + 1) ω) hnext
    simpa only [hX n ω, hY n ω, sim, fullSim] using hr
  have hbound : ∀ n, P (E n) ≤ b := by
    intro n
    have hset : E n = (fun ω => (X n ω, Y n ω)) ⁻¹'
        {p : FullLab (I × V) n × FullLab (I × V) n | ¬ M.sim n p.1 p.2} := rfl
    rw [hset, ← Measure.map_apply (hmeas n) (Set.to_countable _).measurableSet,
      hlaw n, M.prodPMF_toMeasure_not_sim s t n]
    exact hfail n
  have hEq : {ω | ¬ InfMatch M.srel (fun n => X n ω) (fun n => Y n ω)} = ⋃ n, E n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
    change (¬ InfMatchK M.srel 1 0 (fun n => X n ω) (fun n => Y n ω)) ↔ _
    rw [infMatchK_iff_forall_level M.srel 1 0 (fun n => X n ω) (fun n => Y n ω)
      (fun n => hX n ω) (fun n => hY n ω)]
    simp only [not_forall, sim, fullSim]
  rw [hEq, hmono.measure_iUnion]
  exact iSup_le hbound

/-- The matching-probability form of `infFail_le_of_marginals`. -/
theorem infMatch_ge_of_marginals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s t : I)
    (X Y : (n : ℕ) → Ω → FullLab (I × V) n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hmeas : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, P.map (fun ω => (X n ω, Y n ω))
      = (prodPMF (M.rho s n) (M.rho t n)).toMeasure)
    (b : ℝ≥0∞) (hfail : ∀ n, M.failProb s t n ≤ b) :
    1 - b ≤ P {ω | InfMatch M.srel (fun n => X n ω) (fun n => Y n ω)} := by
  refine infinite_tree_matchingK_prob P M.srel 1 0 X Y hX hY ?_ b ?_
  · intro n
    exact (hmeas n) (Set.to_countable
      {p : FullLab (I × V) n × FullLab (I × V) n | M.sim n p.1 p.2}).measurableSet
  · intro n
    change P ((fun ω => (X n ω, Y n ω)) ⁻¹'
      {p : FullLab (I × V) n × FullLab (I × V) n | ¬ M.sim n p.1 p.2}) ≤ b
    rw [← Measure.map_apply (hmeas n) (Set.to_countable _).measurableSet,
      hlaw n, M.prodPMF_toMeasure_not_sim s t n]
    exact hfail n

/-- A uniform failure bound applies to any consistent state pair with the model's projected finite
product marginals, independently of the construction of its probability space. -/
theorem state_infFail_le_of_marginals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s t : I)
    (X Y : (n : ℕ) → Ω → FullLab V n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hmeas : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, P.map (fun ω => (X n ω, Y n ω))
      = (prodPMF ((M.rho s n).map (statesOf' n))
        ((M.rho t n).map (statesOf' n))).toMeasure)
    (b : ℝ≥0∞) (hfail : ∀ n, M.failProb s t n ≤ b) :
    P {ω | ¬ InfMatch M.R (fun n => X n ω) (fun n => Y n ω)} ≤ b := by
  let E : ℕ → Set Ω := fun n => {ω | ¬ fullSim M.R n (X n ω) (Y n ω)}
  have hmono : Monotone E := by
    apply monotone_nat_of_le_succ
    intro n ω hn hnext
    apply hn
    have hr := fullSimK_restrict M.R 1 0 n (X (n + 1) ω) (Y (n + 1) ω) hnext
    simpa only [hX n ω, hY n ω, fullSim] using hr
  have hbound : ∀ n, P (E n) ≤ b := by
    intro n
    have hset : E n = (fun ω => (X n ω, Y n ω)) ⁻¹'
        {p : FullLab V n × FullLab V n | ¬ fullSim M.R n p.1 p.2} := rfl
    rw [hset, ← Measure.map_apply (hmeas n) (Set.to_countable _).measurableSet,
      hlaw n, M.state_prodPMF_toMeasure_not_sim s t n]
    exact hfail n
  have hEq : {ω | ¬ InfMatch M.R (fun n => X n ω) (fun n => Y n ω)} = ⋃ n, E n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
    change (¬ InfMatchK M.R 1 0 (fun n => X n ω) (fun n => Y n ω)) ↔ _
    rw [infMatchK_iff_forall_level M.R 1 0 (fun n => X n ω) (fun n => Y n ω)
      (fun n => hX n ω) (fun n => hY n ω)]
    simp only [not_forall, fullSim]
  rw [hEq, hmono.measure_iUnion]
  exact iSup_le hbound

/-- The matching-probability form of `state_infFail_le_of_marginals`. -/
theorem state_infMatch_ge_of_marginals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s t : I)
    (X Y : (n : ℕ) → Ω → FullLab V n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hmeas : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, P.map (fun ω => (X n ω, Y n ω))
      = (prodPMF ((M.rho s n).map (statesOf' n))
        ((M.rho t n).map (statesOf' n))).toMeasure)
    (b : ℝ≥0∞) (hfail : ∀ n, M.failProb s t n ≤ b) :
    1 - b ≤ P {ω | InfMatch M.R (fun n => X n ω) (fun n => Y n ω)} := by
  refine infinite_tree_matchingK_prob P M.R 1 0 X Y hX hY ?_ b ?_
  · intro n
    exact (hmeas n) (Set.to_countable
      {p : FullLab V n × FullLab V n | fullSim M.R n p.1 p.2}).measurableSet
  · intro n
    change P ((fun ω => (X n ω, Y n ω)) ⁻¹'
      {p : FullLab V n × FullLab V n | ¬ fullSim M.R n p.1 p.2}) ≤ b
    rw [← Measure.map_apply (hmeas n) (Set.to_countable _).measurableSet,
      hlaw n, M.state_prodPMF_toMeasure_not_sim s t n]
    exact hfail n

end Model
end GraphMarkovMatching.Stopped
