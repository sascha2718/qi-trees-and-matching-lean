/-
The infinite-tree conclusion of `arbitrary_offspring_matching.tex` (`sec:completion`, the
König step).  Two independent infinite samples of the Markov label model, started at the
types `s` and `t`, are realised on the product of the two trajectory measures over the
level laws `ρ_{s,·}` and `ρ_{t,·}`.  The finite-height matching events decrease with the
height, their intersection is the infinite matching event by König's lemma, and continuity
of probability turns a uniform bound on the finite failure probabilities into the same bound
at infinite height.

* `trajPair`: the law of the two independent infinite samples;
* `InfMatchEv`, `MatchEv`: the events `M_∞(s,t)` and `M_h(s,t)` on the trajectory space,
  measurable, decreasing, with `M_∞ = ⋂_h M_h` (`infMatchEv_eq_iInter`);
* `trajPair_fail_eq`: the finite failure event has probability `failProb s t h`;
* `trajPair_infFail_eq`, `trajPair_infFail_le`, `trajPair_infMatch_ge`: the infinite
  failure probability is the supremum of the finite ones, and the bounds it inherits.
-/
import GraphMarkovMatching.Stopped.Paths
import GraphMarkovMatching.Support.Trajectory
import GraphMarkovMatching.Support.Measure
import GraphMarkovMatching.Process.Consistency

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

namespace Model

variable {V I : Type} (M : Model V I)

/-! ### The two independent infinite samples -/

section Traj

variable [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The two independent infinite processes started at `s` and `t` (`sec:completion`): the
product of the two trajectory measures over the level laws `ρ_{s,·}` and `ρ_{t,·}`. -/
noncomputable def trajPair (s t : I) :
    Measure ((Π n, FullLab (I × V) n) × (Π n, FullLab (I × V) n)) :=
  trajPairLab (M.rho s) (M.rho_map_restrictLab s) (M.rho t) (M.rho_map_restrictLab t)

instance (s t : I) : IsProbabilityMeasure (M.trajPair s t) := by
  rw [trajPair]
  infer_instance

end Traj

/-! ### The matching events -/

set_option linter.unusedVariables false in
/-- The infinite matching event `M_∞(s,t)` (`sec:completion`): a single rooted automorphism
of the infinite binary tree matches every vertex of the two level processes.  The starting
types `s` and `t` name the pair measure `trajPair s t` the event is evaluated under; the
event itself is a set of trajectory pairs and does not depend on them. -/
def InfMatchEv (s t : I) : Set ((Π n, FullLab (I × V) n) × (Π n, FullLab (I × V) n)) :=
  {ω | InfMatch M.srel (fun n => consLab n ω.1) (fun n => consLab n ω.2)}

set_option linter.unusedVariables false in
/-- The finite-height matching event `M_h(s,t)` (`sec:completion`) on the trajectory
space; as for `InfMatchEv`, the starting types name the pair measure only. -/
def MatchEv (s t : I) (h : ℕ) :
    Set ((Π n, FullLab (I × V) n) × (Π n, FullLab (I × V) n)) :=
  {ω | M.sim h (consLab h ω.1) (consLab h ω.2)}

/-- The finite matching event is the preimage of the height-`h` matching pairs under the
pair of level processes. -/
lemma matchEv_eq_preimage (s t : I) (h : ℕ) :
    M.MatchEv s t h
      = (fun ω : (Π n, FullLab (I × V) n) × (Π n, FullLab (I × V) n) =>
          (consLab h ω.1, consLab h ω.2)) ⁻¹'
        {p : FullLab (I × V) h × FullLab (I × V) h | M.sim h p.1 p.2} := rfl

/-- `M_∞ = ⋂_h M_h` (`sec:completion`): König's lemma, `infMatchK_iff_forall_level`, on the
everywhere consistent level processes. -/
lemma infMatchEv_eq_iInter (s t : I) : M.InfMatchEv s t = ⋂ h, M.MatchEv s t h := by
  ext ω
  simp only [InfMatchEv, MatchEv, Set.mem_setOf_eq, Set.mem_iInter]
  exact infMatchK_iff_forall_level M.srel 1 0 (fun n => consLab n ω.1)
    (fun n => consLab n ω.2) (fun n => restrictLab_consLab n ω.1)
    (fun n => restrictLab_consLab n ω.2)

/-- The finite matching events decrease with the height (`sec:completion`): a height-`(h+1)`
matching restricts to a height-`h` one. -/
lemma matchEv_antitone (s t : I) : Antitone (M.MatchEv s t) := by
  refine antitone_nat_of_succ_le fun h ω hω => ?_
  have hr := fullSimK_restrict M.srel 1 0 h (consLab (h + 1) ω.1) (consLab (h + 1) ω.2) hω
  rw [restrictLab_consLab, restrictLab_consLab] at hr
  exact hr

section Measurable

variable [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma measurableSet_matchEv (s t : I) (h : ℕ) : MeasurableSet (M.MatchEv s t h) := by
  rw [matchEv_eq_preimage]
  exact (measurable_consLab_pair h) (Set.to_countable _).measurableSet

lemma measurableSet_infMatchEv (s t : I) : MeasurableSet (M.InfMatchEv s t) := by
  rw [infMatchEv_eq_iInter]
  exact MeasurableSet.iInter fun h => M.measurableSet_matchEv s t h

/-- The product-law mass of the non-matching pairs is the failure probability
(`sec:completion`). -/
lemma prodPMF_toMeasure_not_sim (s t : I) (h : ℕ) :
    (prodPMF (M.rho s h) (M.rho t h)).toMeasure
        {p : FullLab (I × V) h × FullLab (I × V) h | ¬ M.sim h p.1 p.2}
      = M.failProb s t h := by
  rw [PMF.toMeasure_apply _ (Set.to_countable _).measurableSet, failProb_eq_prodPMF]
  refine tsum_congr fun p => ?_
  rw [Set.indicator_apply]
  by_cases hp : M.sim h p.1 p.2
  · simp [hp]
  · simp [hp]

/-- The finite failure event has probability `failProb s t h` under the pair measure
(`sec:completion`). -/
lemma trajPair_fail_eq (s t : I) (h : ℕ) :
    M.trajPair s t (M.MatchEv s t h)ᶜ = M.failProb s t h := by
  rw [matchEv_eq_preimage, ← Set.preimage_compl, Set.compl_setOf,
    ← Measure.map_apply (measurable_consLab_pair h) (Set.to_countable _).measurableSet,
    trajPair, trajPairLab_map_consLab, prodPMF_toMeasure_not_sim]

/-- **The infinite failure probability is the supremum of the finite ones**
(`sec:completion`, continuity of probability): the complements of the decreasing finite
matching events increase to the complement of the infinite one. -/
theorem trajPair_infFail_eq (s t : I) :
    M.trajPair s t (M.InfMatchEv s t)ᶜ = ⨆ h, M.failProb s t h := by
  have hmono : Monotone fun h => (M.MatchEv s t h)ᶜ :=
    fun a b hab => Set.compl_subset_compl.mpr (M.matchEv_antitone s t hab)
  rw [infMatchEv_eq_iInter, Set.compl_iInter, hmono.measure_iUnion]
  exact iSup_congr fun h => M.trajPair_fail_eq s t h

/-- **The infinite failure bound** (`sec:completion`): a uniform bound on the finite failure
probabilities bounds the infinite one. -/
theorem trajPair_infFail_le (s t : I) {b : ℝ≥0∞} (hfail : ∀ h, M.failProb s t h ≤ b) :
    M.trajPair s t (M.InfMatchEv s t)ᶜ ≤ b := by
  rw [trajPair_infFail_eq]
  exact iSup_le hfail

/-- **The infinite matching bound** (`sec:completion`): a single rooted automorphism of the
infinite binary tree matches every vertex with probability at least `1 - b` whenever every
finite height fails with probability at most `b`. -/
theorem trajPair_infMatch_ge (s t : I) {b : ℝ≥0∞} (hfail : ∀ h, M.failProb s t h ≤ b) :
    1 - b ≤ M.trajPair s t (M.InfMatchEv s t) := by
  have h2 : M.trajPair s t (M.InfMatchEv s t)ᶜ ≤ b := M.trajPair_infFail_le s t hfail
  calc (1 : ℝ≥0∞) - b ≤ 1 - M.trajPair s t (M.InfMatchEv s t)ᶜ := tsub_le_tsub_left h2 1
    _ = M.trajPair s t (M.InfMatchEv s t) := by
      rw [prob_compl_eq_one_sub (M.measurableSet_infMatchEv s t)]
      exact ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one

end Measurable

end Model

end GraphMarkovMatching.Stopped
