/-
The infinite-tree matching theorem for the `ν = δ₃` varying-offspring
process (`arbitrary_offspring_matching.tex`, `thm:konig` at `ν = δ₃`,
with the König packaging): two independent infinite pure-ternary varying-offspring
labellings, presented through compatible measurable level projections
whose height-`n` pair law is the product of two process laws, admit a
single automorphism of the infinite binary tree matching every vertex
with probability at least `1 - 16384·η`.

* `Tlaw_map_restrictLab`: the marginal consistency of the process law
  (the fact any trajectory construction must verify), from the generic
  root-mixture consistency of the Markov tree law;
* `delta3Matching_infinite`: the infinite-tree theorem, an instance of
  the generic interface `infinite_tree_matchingK_prob` with the level
  failure bounds supplied by `delta3_failure_le`.
-/
import GraphMarkovMatching.Delta3.NumericClose
import GraphMarkovMatching.Closure.Measure
import GraphMarkovMatching.Support.Trajectory

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- **Marginal consistency of the process law**: restricting a
height-`(n + 1)` sample of the varying-offspring process to height `n`
recovers the height-`n` law. -/
lemma Tlaw_map_restrictLab (ν : PMF ℕ) (n : ℕ) :
    (Tlaw μ ν v0 (n + 1)).map (restrictLab n) = Tlaw μ ν v0 n :=
  mix_map_restrictLab (varyK μ ν v0) (freshQ μ ν) n

/-- **The `δ₃` matching theorem on the infinite tree.**  Two
independent infinite pure-ternary varying-offspring labellings, given
through compatible measurable level projections whose height-`n` pair
law is the product of two process laws, admit a single automorphism of
the infinite binary tree matching every vertex, with probability at
least `1 - 16384·η`, whenever the label graph is reflexive and
symmetric, the root label carries at least half the mass, and
`2³⁰·η ≤ 1`. -/
theorem delta3Matching_infinite {Ω : Type*} [MeasurableSpace Ω]
    (Pm : Measure Ω) [IsProbabilityMeasure Pm] [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hsmall : (2 : ℝ≥0∞) ^ (30 : ℕ) * etaG (5 / 2) Rv μ ≤ 1)
    (X Y : (n : ℕ) → Ω → FullLab (V × ℕ) n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Pm.map (fun ω => (X n ω, Y n ω))
        = (prodPMF (Tlaw μ (PMF.pure 3) v0 n)
            (Tlaw μ (PMF.pure 3) v0 n)).toMeasure) :
    1 - 16384 * etaG (5 / 2) Rv μ
      ≤ Pm {ω | InfMatch (labRel Rv)
          (fun n => X n ω) (fun n => Y n ω)} := by
  refine infinite_tree_matchingK_prob Pm (labRel Rv) 1 0 X Y hX hY
    (fun n => ?_) _ (fun n => ?_)
  · exact (hpair n)
      ((Set.to_countable
        {p : FullLab (V × ℕ) n × FullLab (V × ℕ) n
          | fullSimK (labRel Rv) 1 0 n p.1 p.2}).measurableSet)
  · rw [show {ω | ¬ fullSimK (labRel Rv) 1 0 n (X n ω) (Y n ω)}
          = (fun ω => (X n ω, Y n ω)) ⁻¹'
              {p | ¬ fullSimK (labRel Rv) 1 0 n p.1 p.2} from rfl,
      ← Measure.map_apply (hpair n) ((Set.to_countable _).measurableSet),
      hlaw n, prodPMF_toMeasure_not_rel]
    exact delta3_failure_le Rv μ v0 hRv hsymm hhalf hsmall n

/-- **The `δ₃` matching theorem on the infinite tree, with the trajectory space
constructed**: on the product of the two trajectory measures over the pure-ternary level
laws, the consistent level processes realise the two independent infinite labellings, and
one binary-tree automorphism matches them with probability at least `1 - 16384·η`.  No
probability space is assumed. -/
theorem delta3Matching_infinite_traj [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hsmall : (2 : ℝ≥0∞) ^ (30 : ℕ) * etaG (5 / 2) Rv μ ≤ 1) :
    1 - 16384 * etaG (5 / 2) Rv μ
      ≤ trajPairLab (Tlaw μ (PMF.pure 3) v0)
          (fun n => Tlaw_map_restrictLab (μ := μ) (v0 := v0) (PMF.pure 3) n)
          (Tlaw μ (PMF.pure 3) v0)
          (fun n => Tlaw_map_restrictLab (μ := μ) (v0 := v0) (PMF.pure 3) n)
          {ω | InfMatch (labRel Rv)
            (fun n => consLab n ω.1) (fun n => consLab n ω.2)} :=
  delta3Matching_infinite Rv μ v0
    (trajPairLab (Tlaw μ (PMF.pure 3) v0)
      (fun n => Tlaw_map_restrictLab (μ := μ) (v0 := v0) (PMF.pure 3) n)
      (Tlaw μ (PMF.pure 3) v0)
      (fun n => Tlaw_map_restrictLab (μ := μ) (v0 := v0) (PMF.pure 3) n))
    hRv hsymm hhalf hsmall
    (fun n ω => consLab n ω.1) (fun n ω => consLab n ω.2)
    (fun n ω => restrictLab_consLab n ω.1) (fun n ω => restrictLab_consLab n ω.2)
    (fun n => measurable_consLab_pair n)
    (fun n => trajPairLab_map_consLab _ _ _ _ n)

end GraphMarkovMatching
