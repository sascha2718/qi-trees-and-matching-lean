/-
The infinite-tree matching theorem for the `ν = δ₃` varying-offspring
process (`arbitrary_offspring_matching.tex`, `thm:konig` at `ν = δ₃`,
with the König packaging): two independent infinite pure-ternary varying-offspring
labellings, presented through compatible measurable level projections
whose height-`n` pair law is the product of two process laws, admit a
single automorphism of the infinite binary tree matching every vertex
with probability at least `1 - 16384·η`.

* `delta3Matching_infinite`: the infinite-tree theorem, the instance of
  `varyingMatching_infinite` with the level failure bounds supplied by
  `delta3_failure_le`.
-/
import GraphMarkovMatching.Delta3.NumericClose
import GraphMarkovMatching.Closure.Infinite

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

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
          (fun n => X n ω) (fun n => Y n ω)} :=
  varyingMatching_infinite Rv μ (PMF.pure 3) v0 Pm _
    (fun n => delta3_failure_le Rv μ v0 hRv hsymm hhalf hsmall n) X Y hX hY hpair hlaw

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
  varyingMatching_infinite_traj Rv μ (PMF.pure 3) v0 _
    (fun n => delta3_failure_le Rv μ v0 hRv hsymm hhalf hsmall n)

end GraphMarkovMatching
