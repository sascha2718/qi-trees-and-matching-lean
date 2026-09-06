/-
The infinite-tree matching theorem for the varying-offspring process
with an arbitrary offspring law (`arbitrary_offspring_matching.tex`,
`thm:konig`, feeding `thm:main-matching`): two independent infinite
varying-offspring labellings, presented through compatible measurable
level projections whose height-`n` pair law is the product of two
process laws, admit a single automorphism of the infinite binary tree
matching every vertex, with probability at least `1 - ε` whenever
every finite height fails with probability at most `ε`.

* `Tlaw_map_restrictLab`: the marginal consistency of the process law,
  from the root-mixture consistency of the Markov tree law;
* `varyingMatching_infinite`: the interface form: the level failure
  bounds are hypotheses, to be supplied by the general closure
  theorem; marginal consistency comes from `Tlaw_map_restrictLab`;
* `TlawPair`, `varyingMatching_infinite_traj`: the law of two
  independent infinite samples, constructed as the product of two
  trajectory measures, and the matching theorem on it, with no
  probability space assumed.
-/
import GraphMarkovMatching.Process.Kernel
import GraphMarkovMatching.Closure.Measure
import GraphMarkovMatching.Support.Trajectory

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type} (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- **Marginal consistency of the process law**: restricting a
height-`(n + 1)` sample of the varying-offspring process to height `n`
recovers the height-`n` law. -/
lemma Tlaw_map_restrictLab (n : ℕ) :
    (Tlaw μ ν v0 (n + 1)).map (restrictLab n) = Tlaw μ ν v0 n :=
  mix_map_restrictLab (varyK μ ν v0) (freshQ μ ν) n

/-- **The general varying-offspring matching theorem on the infinite
tree**, in interface form.  Two independent infinite varying-offspring
labellings with offspring law `ν`, given through compatible measurable
level projections whose height-`n` pair law is the product of two
process laws, admit a single automorphism of the infinite binary tree
matching every vertex with probability at least `1 - ε`, provided the
expected bad degree of every finite height is at most `ε`.  The level
bounds are exactly the conclusion of the general closure theorem. -/
theorem varyingMatching_infinite {Ω : Type*} [MeasurableSpace Ω]
    (Pm : Measure Ω) [IsProbabilityMeasure Pm] [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (eps : ℝ≥0∞)
    (hfail : ∀ n, (∑' x, Tlaw μ ν v0 n x
        * qE (Tlaw μ ν v0 n) (fullSim (labRel Rv) n) x) ≤ eps)
    (X Y : (n : ℕ) → Ω → FullLab (V × ℕ) n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Pm.map (fun ω => (X n ω, Y n ω))
        = (prodPMF (Tlaw μ ν v0 n) (Tlaw μ ν v0 n)).toMeasure) :
    1 - eps
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
    exact hfail n

/-! ### The constructed pair of infinite samples -/

variable [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **The law of two independent infinite varying-offspring samples**: the product of two
trajectory measures over the level laws. -/
noncomputable def TlawPair : Measure ((Π n, FullLab (V × ℕ) n) × (Π n, FullLab (V × ℕ) n)) :=
  trajPairLab (Tlaw μ ν v0) (fun n => Tlaw_map_restrictLab (μ := μ) (v0 := v0) ν n)
    (Tlaw μ ν v0) (fun n => Tlaw_map_restrictLab (μ := μ) (v0 := v0) ν n)

instance : MeasureTheory.IsProbabilityMeasure (TlawPair μ ν v0) := by
  rw [TlawPair]
  infer_instance

/-- **The general varying-offspring matching theorem on the infinite tree, with the
trajectory space constructed**: on the product of the two trajectory measures, the
consistent level processes realise the two independent infinite labellings, and a single
automorphism of the infinite binary tree matches every vertex with probability at least
`1 - ε`, provided the expected bad degree of every finite height is at most `ε`.  No
probability space is assumed. -/
theorem varyingMatching_infinite_traj (eps : ℝ≥0∞)
    (hfail : ∀ n, (∑' x, Tlaw μ ν v0 n x
        * qE (Tlaw μ ν v0 n) (fullSim (labRel Rv) n) x) ≤ eps) :
    1 - eps
      ≤ TlawPair μ ν v0 {ω | InfMatch (labRel Rv)
          (fun n => consLab n ω.1) (fun n => consLab n ω.2)} :=
  varyingMatching_infinite Rv μ ν v0 (TlawPair μ ν v0) eps hfail
    (fun n ω => consLab n ω.1) (fun n ω => consLab n ω.2)
    (fun n ω => restrictLab_consLab n ω.1) (fun n ω => restrictLab_consLab n ω.2)
    (fun n => measurable_consLab_pair n)
    (fun n => trajPairLab_map_consLab _ _ _ _ n)

end GraphMarkovMatching
