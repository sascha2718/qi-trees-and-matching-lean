/-
The infinite-tree matching theorem for the per-state ceiling route.

`markovMatching_infinite` packages the closed invariance of `TwoCeiling` with
the Konig/measure interface: two independent infinite Markov labellings,
given through compatible measurable level projections whose height-`n` pair
law is the product of two root-mixture Markov tree laws, admit one
automorphism of the infinite binary tree matching every vertex with
probability at least `1 - (eta_iota + B)`.

The theorem is complete and audited.  It is archived with the route it
closes: the varying-offspring processes the paper studies have infinite
kernel budgets `eta`, so the hypothesis `hEta` is never satisfiable there,
and the live endpoints instead build directly on the projective consistency
of `Closure/Measure.lean`.
-/
import GraphMarkovMatching.Archive.TwoCeiling
import GraphMarkovMatching.Closure.Measure

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

universe u
variable {S : Type u}

/-- **The Markov matching theorem on the infinite tree.** Two independent
infinite Markov labellings, given through compatible measurable level
projections whose height-`n` pair law is the product of two root-mixture
Markov tree laws, admit a single automorphism of the infinite binary tree
matching every vertex with probability at least `1 - (η_ι + B)`, under the
budgets and the closure inequality of the closed invariance. -/
theorem markovMatching_infinite {Ω : Type*} [MeasurableSpace Ω] (Pm : Measure Ω)
    [IsProbabilityMeasure Pm] [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : S → PMF (S × S)) (R₀ : S → S → Prop)
    {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (ε β B : ℝ≥0∞)
    (hEta : ∀ s t, R₀ s t → etaD α P R₀ s t ≤ ε)
    (hBeta : ∀ s t, R₀ s t → betaD P R₀ s t ≤ β)
    (hclose : ε
        + ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
          + β * (B + B + ENNReal.ofReal (2 * α) * (B * B)))
        + ENNReal.ofReal (2 * α) * (ε
            * ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
              + (B + B + ENNReal.ofReal (2 * α) * (B * B)))) ≤ B)
    (ι : PMF S)
    (X Y : (n : ℕ) → Ω → FullLab S n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Pm.map (fun ω => (X n ω, Y n ω))
        = (prodPMF (ι.bind fun s => muM P s n) (ι.bind fun s => muM P s n)).toMeasure) :
    1 - ((∑' s, ι s * qE ι R₀ s) + B)
      ≤ Pm {ω | InfMatch R₀ (fun n => X n ω) (fun n => Y n ω)} := by
  refine infinite_tree_matchingK_prob Pm R₀ 1 0 X Y hX hY (fun n => ?_) _ (fun n => ?_)
  · exact (hpair n)
      ((Set.to_countable
        {p : FullLab S n × FullLab S n | fullSimK R₀ 1 0 n p.1 p.2}).measurableSet)
  · rw [show {ω | ¬ fullSimK R₀ 1 0 n (X n ω) (Y n ω)}
          = (fun ω => (X n ω, Y n ω)) ⁻¹' {p | ¬ fullSimK R₀ 1 0 n p.1 p.2} from rfl,
      ← Measure.map_apply (hpair n) ((Set.to_countable _).measurableSet), hlaw n,
      prodPMF_toMeasure_not_rel]
    exact markovMatching_failure_le_closed P R₀ hα hδ hL0 hL hK0 hK hsymm ε β B
      hEta hBeta hclose ι n

end GraphMarkovMatching
