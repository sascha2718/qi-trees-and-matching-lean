/-
Comparator solution file: the headline theorems of the four libraries,
restated with the same text as `Challenge.lean` and proved by the library
declarations.  Comparator checks each statement against `Challenge.lean`,
audits the axioms of the proofs, and replays them through the kernel.  The
statement text must stay character-for-character identical to
`Challenge.lean`.
-/
import GraphMatching.Graph
import GraphMatching.Kolmogorov
import GraphMatching.AutBridge
import GraphMarkovMatching.Closure.Infinite
import GraphMarkovMatching.Closure.Numeric
import GraphMarkovMatching.Composite.Numeric
import BranchingProcess.Law
import BranchingProcess.Field
import ChainClasses.TwoValue
import ChainClasses.CrossLaw
import ChainClasses.ThreeRays
import ChainClasses.ShapeCouplingBuild
import ChainClasses.ShapePairEta
import ChainClasses.Classification

/-! ### `GraphMatching`: `thm:matching` of `graph_matching_selfcontained.tex` -/

namespace GraphMatching

open scoped ENNReal Classical
open MeasureTheory

universe u

/-- `graph_leaf_matching_bound` (`thm:matching`(1)). -/
theorem audit_graph_leaf_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (h0 : etaG μ G ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * etaG μ G :=
  graph_leaf_matching_bound μ G h0 h

/-- `graph_full_matching_bound` (`thm:matching`(2)). -/
theorem audit_graph_full_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (hη : etaG μ G ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim (compat G) h) x ≤ 16 * etaG μ G :=
  graph_full_matching_bound μ G hη h

/-- `exists_infinite_tree_matching` (`thm:matching`, infinite tree, with the two level
processes consistent under restriction, jointly measurable, and carrying the i.i.d. pair
law at every height). -/
theorem audit_exists_infinite_tree_matching {V : Type u} (μ : PMF V) [MeasurableSpace V]
    [MeasurableSingletonClass V]
    [Countable V] (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hη : Phi μ R₀ ≤ 1 / 10000) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : (h : ℕ) → Ω → FullLab V h),
      (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
      (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
      (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
      (∀ h, P.map (fun ω => (X h ω, Y h ω))
        = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) ∧
      1 - 16 * Phi μ R₀ ≤ P {ω | InfMatch R₀ (fun h => X h ω) (fun h => Y h ω)} :=
  exists_infinite_tree_matching μ R₀ hrefl hsymm hη


/-- `exists_infinite_tree_matching_graphAut` (`thm:matching`, infinite tree, the
automorphism as a root-fixing graph automorphism of the infinite binary tree). -/
theorem audit_exists_infinite_tree_matching_graphAut {V : Type u} (μ : PMF V)
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hη : Phi μ R₀ ≤ 1 / 10000) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : (h : ℕ) → Ω → FullLab V h),
      (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
      (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
      (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
      (∀ h, P.map (fun ω => (X h ω, Y h ω))
        = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) ∧
      1 - 16 * Phi μ R₀ ≤ P {ω | ∃ g : treeGraphInf ≃g treeGraphInf, g [] = [] ∧
        ∀ s : List Bool, R₀ (coord (g s).length (X (g s).length ω) (g s))
          (coord s.length (Y s.length ω) s)} :=
  exists_infinite_tree_matching_graphAut μ R₀ hrefl hsymm hη

end GraphMatching

/-! ### `GraphMarkovMatching`: the engine of `arbitrary_offspring_matching.tex` -/

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

/-- `varyingMatching_infinite` (`thm:konig`, feeding `thm:main-matching`). -/
theorem audit_varyingMatching_infinite {V : Type} (Rv : V → V → Prop) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) {Ω : Type*} [MeasurableSpace Ω]
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
          (fun n => X n ω) (fun n => Y n ω)} :=
  varyingMatching_infinite Rv μ ν v0 Pm eps hfail X Y hX hY hpair hlaw


/-- `varying_matching_le_traj` (`thm:main-matching`, `eq:main-bound-infinite`, on the
constructed product of two trajectory measures). -/
theorem audit_varying_matching_le_traj {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T * etaG (5 / 2) Rv μ ≤ 1) :
    1 - genKcC cN S.card T * etaG (5 / 2) Rv μ
      ≤ TlawPair μ ν v0 {ω | InfMatch (labRel Rv)
          (fun n => consLab n ω.1) (fun n => consLab n ω.2)} :=
  varying_matching_le_traj Rv μ v0 ν N S hrefl hsymm hhalf hN hS hSne hSsupp
    T hT cN nA hcN hnA hsmall


/-- `varying_failure_le` with `genKcC_le_third` (`thm:main-matching`, `eq:main-bound` at
every finite height, uniformly in the height, with the `1/3` barrier giving the `2/3`
clause). -/
theorem audit_varying_failure_le {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T * etaG (5 / 2) Rv μ ≤ 1) :
    genKcC cN S.card T * etaG (5 / 2) Rv μ ≤ 3⁻¹
      ∧ ∀ h, (∑' x, Tlaw μ ν v0 h x
          * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x)
        ≤ genKcC cN S.card T * etaG (5 / 2) Rv μ :=
  ⟨genKcC_le_third cN S.card nA T (etaG (5 / 2) Rv μ) hsmall,
    varying_failure_le Rv μ v0 ν N S hrefl hsymm hhalf hN hS hSne hSsupp
      T hT cN nA hcN hnA hsmall⟩


/-- `main_matching_failure_le` (`thm:main-matching` at the constants of
`eq:card-constants` and `eq:K-eps`, with the threshold in the form `η ≤ ε_ν`). -/
theorem audit_main_matching_failure_le {V : Type} (Rv : V → V → Prop) (μ : PMF V)
    (v0 : V) (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (heta : etaG (5 / 2) Rv μ
      ≤ (genSmallC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card
          (2 * N + 3) T)⁻¹) :
    genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
        * etaG (5 / 2) Rv μ ≤ 3⁻¹
      ∧ ∀ h, (∑' x, Tlaw μ ν v0 h x
          * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x)
        ≤ genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
            * etaG (5 / 2) Rv μ :=
  main_matching_failure_le Rv μ v0 ν N S hrefl hsymm hhalf hN hS hSne hSsupp T hT heta


/-- `main_matching_le_traj` (`thm:main-matching`, `eq:main-bound-infinite` at
`eq:card-constants` and `eq:K-eps`, on the constructed trajectory space). -/
theorem audit_main_matching_le_traj {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (heta : etaG (5 / 2) Rv μ
      ≤ (genSmallC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card
          (2 * N + 3) T)⁻¹) :
    1 - genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
        * etaG (5 / 2) Rv μ
      ≤ TlawPair μ ν v0 {ω | InfMatch (labRel Rv)
          (fun n => consLab n ω.1) (fun n => consLab n ω.2)} :=
  main_matching_le_traj Rv μ v0 ν N S hrefl hsymm hhalf hN hS hSne hSsupp T hT heta

namespace Composite

private lemma audit_mu0_ne_zero {V : Type} (μ : PMF V) (v0 : V)
    (hhalf : 2⁻¹ ≤ μ v0) : μ v0 ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by norm_num) hhalf)

/-- `composite_matching_bound_massfree_no_exceptions` (`thm:composite-matching`
at empty exceptional charts, the one-law specialisation of `thm:main-matching`). -/
theorem audit_composite_matching_bound_massfree_no_exceptions
    {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega)
    [IsProbabilityMeasure Pm]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (ν : PMF ℕ) (K : Finset ℕ)
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ K)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM (fun _ => none) (fun _ => none) ν ν K K
          (K.sup id))
    (Xs Ys : (n : ℕ) → Omega → FullLab (CState V) n)
    (hXs : ∀ n omega, restrictLab n (Xs (n + 1) omega) = Xs n omega)
    (hYs : ∀ n omega, restrictLab n (Ys (n + 1) omega) = Ys n omega)
    (hpairM : ∀ n, Measurable (fun omega => (Xs n omega, Ys n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (Xs n omega, Ys n omega)) =
      (prodPMF (cT (fun _ => none) μ ν v0 n)
        (cT (fun _ => none) μ ν v0 n)).toMeasure) :
    compKcFinalM (fun _ => none) (fun _ => none) ν ν K K (K.sup id)
        * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalM (fun _ => none) (fun _ => none) ν ν K K
            (K.sup id) * etaG (5 / 2) Rv μ
        ≤ Pm {omega | InfMatch (cRel Rv)
            (fun n => Xs n omega) (fun n => Ys n omega)} :=
  composite_matching_bound_massfree_no_exceptions Rv μ v0 Pm hRv hsymm
    (audit_mu0_ne_zero μ v0 hhalf) hhalf ν K hsup heta Xs Ys hXs hYs hpairM hlaw

/-- `composite_matching_bound_massfree_traj` (`thm:composite-matching`,
`eq:composite-bound-infinite`, on the constructed product of two trajectory measures). -/
theorem audit_composite_matching_bound_massfree_traj
    {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ
        ≤ cTPair μ v0 exc1 exc2 ν1 ν2 {omega | InfMatch (cRel Rv)
            (fun n => consLab n omega.1) (fun n => consLab n omega.2)} :=
  composite_matching_bound_massfree_traj Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
    hRv hsymm (audit_mu0_ne_zero μ v0 hhalf) hhalf hN hdeclN1 hcharged1 hdeclN2
    hcharged2 hpair1 hpair2
    hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 heta

/-- `composite_matching_bound_massfree_no_exceptions_traj` (`thm:main-matching` as a
special case of `thm:composite-matching`, on the constructed product of two trajectory
measures). -/
theorem audit_composite_matching_bound_massfree_no_exceptions_traj
    {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (ν : PMF ℕ) (K : Finset ℕ)
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ K)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM (fun _ => none) (fun _ => none) ν ν K K
          (K.sup id)) :
    compKcFinalM (fun _ => none) (fun _ => none) ν ν K K (K.sup id)
        * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalM (fun _ => none) (fun _ => none) ν ν K K
            (K.sup id) * etaG (5 / 2) Rv μ
        ≤ cTPair μ v0 (fun _ => none) (fun _ => none) ν ν {omega | InfMatch (cRel Rv)
            (fun n => consLab n omega.1) (fun n => consLab n omega.2)} :=
  composite_matching_bound_massfree_no_exceptions_traj Rv μ v0 hRv hsymm
    (audit_mu0_ne_zero μ v0 hhalf) hhalf ν K hsup heta

/-- `composite_failure_bound_massfree` with `compKcFinalM_mul_le_half`
(`thm:composite-matching`, `eq:composite-bound` at every finite height, uniformly in the
height, with the half barrier). -/
theorem audit_composite_failure_bound_massfree
    {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ ∀ h, failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
          (fullSim (cRel Rv) h)
        ≤ compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ :=
  ⟨compKcFinalM_mul_le_half exc1 exc2 ν1 ν2 K1 K2 N heta,
    composite_failure_bound_massfree Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
      hRv hsymm (audit_mu0_ne_zero μ v0 hhalf) hhalf hN hdeclN1 hcharged1 hdeclN2
      hcharged2 hpair1 hpair2
      hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 heta⟩

/-- `compEtaStarM_pos` (`thm:composite-matching`, the clause `ε_ν⃗ > 0`). -/
theorem audit_compEtaStarM_pos
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ) (N : ℕ)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    0 < compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N :=
  compEtaStarM_pos exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1 hsup2 hdecl2

/-- `compEtaStarMT_pos` (`thm:composite-matching`, the clause `ε_ν⃗(T) > 0`
at an arbitrary finite tilt budget). -/
theorem audit_compEtaStarMT_pos (T : ℝ≥0∞) (hT : T ≠ ⊤)
    (K1 K2 : Finset ℕ) (N : ℕ) :
    0 < compEtaStarMT T K1 K2 N :=
  compEtaStarMT_pos hT K1 K2 N

/-- `cLetterBox_card` (`eq:composite-cardinals`, the alphabet count
`n_A = (N+1)³ + N + 2`). -/
theorem audit_cLetterBox_card (N : ℕ) :
    (cLetterBox N).card = (N + 1) ^ 3 + N + 2 :=
  cLetterBox_card N

/-- `cRank_eq` (`eq:composite-cardinals`, the rank `r = n_A · 2^{n_A} · (n_A + 1)`). -/
theorem audit_cRank_eq (N : ℕ) :
    cRank N = ((N + 1) ^ 3 + N + 2) * 2 ^ ((N + 1) ^ 3 + N + 2)
      * ((N + 1) ^ 3 + N + 2 + 1) :=
  cRank_eq N

/-- `compCM_eq` (`eq:composite-K-eps`, the closed form for `C_W`). -/
theorem audit_compCM_eq (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ) :
    compCM exc1 exc2 ν1 ν2 K1 K2
      = 32 * (cMx K1 K2 : ℝ≥0∞)
        + 256 * (cMx K1 K2 : ℝ≥0∞) ^ 2 * compT exc1 exc2 ν1 ν2 K1 K2 :=
  compCM_eq exc1 exc2 ν1 ν2 K1 K2

/-- `compXM_eq` (`eq:composite-K-eps`, the closed form for `Xi`). -/
theorem audit_compXM_eq (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ) (N : ℕ) :
    compXM exc1 exc2 ν1 ν2 K1 K2 N
      = 2 * (16 * compT exc1 exc2 ν1 ν2 K1 K2 + 3)
        * ∑ j : Fin (cRank N), (2 * compCM exc1 exc2 ν1 ν2 K1 K2) ^ (j : ℕ) :=
  compXM_eq exc1 exc2 ν1 ν2 K1 K2 N

/-- `compKcFinalM_eq` (`eq:composite-K-eps`, the closed form for `K`). -/
theorem audit_compKcFinalM_eq (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ) (N : ℕ) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N
      = 6 * (4 + (25 / 4 + 4 * compT exc1 exc2 ν1 ν2 K1 K2 * (cMx K1 K2 : ℝ≥0∞))
          * compXM exc1 exc2 ν1 ν2 K1 K2 N) :=
  compKcFinalM_eq exc1 exc2 ν1 ν2 K1 K2 N

/-- `compB2Of_eq` (`eq:composite-K-eps`, the closed form for `B`). -/
theorem audit_compB2Of_eq (T kappa X : ℝ≥0∞) :
    compB2Of T kappa X
      = 160 * compKcOf T kappa X ^ 2
        + 12 * compKcOf T kappa X * X * (1 + T * kappa) + 4 * T * kappa * X ^ 2 :=
  compB2Of_eq T kappa X

/-- `compAM_eq` (`eq:composite-K-eps`, the closed form for `A`). -/
theorem audit_compAM_eq (T kappa X : ℝ≥0∞) :
    compC2Of T kappa X + compC3Of T kappa X + 1
      = 16 * compB2Of T kappa X
        + 15 * (compKcOf T kappa X + (25 / 4 + 4 * T * kappa) * X) + 1 :=
  compAM_eq T kappa X

/-- `compHuCOf_eq` (`eq:composite-K-eps`, the closed form for `H`). -/
theorem audit_compHuCOf_eq (T kappa X : ℝ≥0∞) (nA m : ℕ) :
    compHuCOf T kappa X (2 * (nA * m))
      = 3 * compKcOf T kappa X
        + (1 + 8 * T) * (24 * (compKcOf T kappa X * X)
            + 16 * ((nA : ℝ≥0∞) * (m : ℝ≥0∞) * X) ^ 2) :=
  compHuCOf_eq T kappa X nA m

/-- `compEtaStarM_eq` (`eq:composite-K-eps`, the closed form for `epsilon`). -/
theorem audit_compEtaStarM_eq (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ) (N : ℕ) :
    compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N
      = (max (compC2Of (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
            (compXM exc1 exc2 ν1 ν2 K1 K2 N)
          + compC3Of (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
              (compXM exc1 exc2 ν1 ν2 K1 K2 N) + 1)
        (max (compHuCOf (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
            (compXM exc1 exc2 ν1 ν2 K1 K2 N) (cLz N K1 K2))
          (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)))⁻¹ :=
  compEtaStarM_eq exc1 exc2 ν1 ν2 K1 K2 N

/-- `compKcFinalM_mul_le_half` (the half barrier of `eq:composite-bound`). -/
theorem audit_compKcFinalM_mul_le_half (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) {eta : ℝ≥0∞}
    (heta : eta ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * eta ≤ 2⁻¹ :=
  compKcFinalM_mul_le_half exc1 exc2 ν1 ν2 K1 K2 N heta

/-- `composite_failure_bound_massfree_T` (`thm:composite-matching` at any tilt budget
`T` bounding the two floor sums of `eq:composite-tilt`, with the constants of
`eq:composite-K-eps` built from `T`: the half barrier and `eq:composite-bound` at
every finite height, uniformly in the height). -/
theorem audit_composite_failure_bound_massfree_T
    {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)
    (T : ℝ≥0∞)
    (hT1 : compTiltBound exc1 ν1 K1 ≤ T)
    (hT2 : compTiltBound exc2 ν2 K2 ≤ T)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ ≤ compEtaStarMT T K1 K2 N) :
    compKcFinalMT T K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ ∀ h, failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
          (fullSim (cRel Rv) h)
        ≤ compKcFinalMT T K1 K2 N * etaG (5 / 2) Rv μ :=
  composite_failure_bound_massfree_T Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N T hT1 hT2
    hRv hsymm (audit_mu0_ne_zero μ v0 hhalf) hhalf hN hdeclN1 hcharged1 hdeclN2
    hcharged2 hpair1 hpair2
    hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 heta

/-- `composite_matching_bound_massfree_traj_T` (`thm:composite-matching`,
`eq:composite-bound-infinite` at any tilt budget `T` bounding the two floor sums,
on the constructed product of two trajectory measures). -/
theorem audit_composite_matching_bound_massfree_traj_T
    {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (T : ℝ≥0∞)
    (hT1 : compTiltBound exc1 ν1 K1 ≤ T)
    (hT2 : compTiltBound exc2 ν2 K2 ≤ T)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ ≤ compEtaStarMT T K1 K2 N) :
    compKcFinalMT T K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalMT T K1 K2 N * etaG (5 / 2) Rv μ
        ≤ cTPair μ v0 exc1 exc2 ν1 ν2 {omega | InfMatch (cRel Rv)
            (fun n => consLab n omega.1) (fun n => consLab n omega.2)} :=
  composite_matching_bound_massfree_traj_T Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N T hT1 hT2
    hRv hsymm (audit_mu0_ne_zero μ v0 hhalf) hhalf hN hdeclN1 hcharged1 hdeclN2
    hcharged2 hpair1 hpair2
    hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 heta

end Composite

end GraphMarkovMatching

/-! ### `BranchingProcess`: the Galton-Watson foundation -/

namespace BranchingProcess

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

universe u

/-- `gen_extinctionProb`: the extinction probability is a fixed point of the
generating function. -/
theorem audit_gen_extinctionProb {J N : ℕ} (θ : Offspring J) (hJN : J ≤ N) :
    Offspring.gen θ (sampleMeasure (N := N) θ {c : Word N → ℕ | ¬ Survives c}).toReal
      = (sampleMeasure (N := N) θ {c : Word N → ℕ | ¬ Survives c}).toReal :=
  gen_extinctionProb θ hJN

/-- `exists_bernoulli_field`: the i.i.d. Bernoulli field in the packaged shape. -/
theorem audit_exists_bernoulli_field (ι : Type u) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ι → Ω → Bool),
      (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
      (∀ i, P {ω | X i ω = true} = ENNReal.ofReal t) :=
  exists_bernoulli_field ι ht ht1

end BranchingProcess

/-! ### `ChainClasses`: quasi-isometry classification endpoints -/

namespace ChainClasses

section

open MeasureTheory ProbabilityTheory GraphMatching
open scoped ENNReal

/-- `twovalue_ae_tree` (`thm:twovalue` on the sample trees). -/
theorem audit_twovalue_ae_tree {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    twoSampleMeasure ht ht1.le
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K (InTree ω.1) (InTree ω.2) f} = 0 :=
  twovalue_ae_tree ht ht1


/-- `twovalue_ae_tree_family` (`thm:twovalue` on the whole two-value family, the
endpoints included). -/
theorem audit_twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((BranchingProcess.bernoulliField (ι := Word) ht0 ht1).prod
        (BranchingProcess.bernoulliField ht0 ht1))
      {ω | ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K (InTree ω.1) (InTree ω.2) f} = 0 :=
  twovalue_ae_tree_family ht0 ht1


/-- `exists_twovalue_rate_tree` (`eq:rate` past one threshold). -/
theorem audit_exists_twovalue_rate_tree {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      twoSampleMeasure ht ht1.le
          {ω | ¬ ∃ f : Word → Word, IsQIWith (D ^ 2 + 3) (InTree ω.1) (InTree ω.2) f}
        ≤ ENNReal.ofReal (256 * qBound (1 - t) D) :=
  exists_twovalue_rate_tree ht ht1

/-- `crosslaw_ae_tree` (`thm:cross-law` on the sample trees). -/
theorem audit_crosslaw_ae_tree {t t' : ℝ} (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t')
    (ht1' : t' < 1) :
    crossMeasure ht ht1.le ht' ht1'.le
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K (InTree ω.1) (InTree ω.2.1) f} = 0 :=
  crosslaw_ae_tree ht ht1 ht' ht1'


/-- `exists_crosslaw_rate_tree` (`eq:rate-cross` past one threshold, at the real
constant `gammaStar · D² + 3`). -/
theorem audit_exists_crosslaw_rate_tree {t t' : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (ht' : 0 < t') (ht1' : t' < 1) :
    ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D →
      crossMeasure ht ht1.le ht' ht1'.le
          {ω | ¬ ∃ f : Word → Word, IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
            (InTree ω.1) (InTree ω.2.1) f}
        ≤ ENNReal.ofReal (256 * qBound (1 - t) D) :=
  exists_crosslaw_rate_tree ht ht1 ht' ht1'

end

section

open MeasureTheory ProbabilityTheory
open BranchingProcess (QuasiIsometric rayGraph)

/-- `converse_ae` (`thm:converse` on the constructed space). -/
theorem audit_converse_ae {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂(chainMeasure ht ht1.le),
      ¬ QuasiIsometric (wordGraph (InTree ω)) (wordGraph fun _ : Word => True)
        ∧ ¬ QuasiIsometric (wordGraph (InTree ω)) rayGraph :=
  converse_ae ht ht1

/-- `simple_classification` (`thm:trichotomy-simple`, the four simple-support classes). -/
theorem audit_trichotomy_simple
    (r r' : Regime) (hr : r.Valid) (hr' : r'.Valid) :
    (r.kind = r'.kind → ∀ᵐ ω ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
        PairQI (r.sampleLaw hr) (r'.sampleLaw hr') ω)
      ∧ (r.kind ≠ r'.kind → ∀ᵐ ω ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
        ¬ PairQI (r.sampleLaw hr) (r'.sampleLaw hr') ω)
      ∧ (r ≠ Regime.ray → ∀ᵐ ω ∂(r.sampleLaw hr).law,
          ¬ QuasiIsometric ((r.sampleLaw hr).graph ω) rayGraph) :=
  simple_classification r r' hr hr'

end

section

open MeasureTheory ProbabilityTheory GraphMatching
open BranchingProcess (sample survivalMeasure Offspring)
open scoped ENNReal Classical

/-- `hairy_ae_shape_tree_two_law` (`thm:hairy` across two laws). -/
theorem audit_hairy_ae_shape_tree_two_law (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) :
    twoHairyMeasure θ θ'
      {ω | ¬ ∃ (L : ℝ) (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}),
        IsSampleQI L F} = 0 :=
  hairy_ae_shape_tree_two_law θ θ' hq hq0 h2 hq' hq0' h2'


/-- `hairy_rate_two_law` (`eq:hairy-rate` across two laws). -/
theorem audit_hairy_rate_two_law (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → ∃ π : PMF (Shape × Shape),
      IsShapeCoupling (D : ℝ) (shapePMF θ hq hq0 h2) (shapePMF θ' hq' hq0' h2') π ∧
      twoHairyMeasure θ θ'
          {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
            IsSampleQI (8 * 972 ^ 2 * (D : ℝ) ^ 8) F}
        ≤ 16 * etaG π (pairNetS π (D : ℝ)) ∧
      etaG π (pairNetS π (D : ℝ)) ≤ ENNReal.ofReal (Real.exp (-(c₃ * (D : ℝ) ^ 2))) :=
  hairy_rate_two_law θ θ' hq hq0 h2 hq' hq0' h2'

end

section

open MeasureTheory ProbabilityTheory
open BranchingProcess (sample survivalMeasure Offspring QuasiIsometric)

/-- `chainSeparation` (`thm:chain-separation`), the hypothesis `ChainSeparation`
unfolded. -/
theorem audit_chainSeparation {J J' N N' : ℕ} (θ : Offspring J) (hJN : J ≤ N)
    (hθ0 : θ 0 = 0) (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0) (hθ1'₀ : 0 < θ' 1)
    (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      ≠ AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) :
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      ¬ QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) :=
    chainSeparation θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hJN' hθ0' hθ1'₀ hθ1'' hJ2' hθJ' hsem

/-- `classification_ae_iff` (`thm:trichotomy`, with the same-class and different-class conclusions
retained eventwise). -/
theorem audit_trichotomy (R R' : GRegime) :
    ∀ᵐ ω ∂(R.sampleLaw.law.prod R'.sampleLaw.law),
      GPairQI R.sampleLaw R'.sampleLaw ω ↔
        (R.kind = R'.kind ∧
          (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup)) :=
  classification_ae_iff R R'

/-- `classification_not_ray_ae` (a one-sample corollary of the different-class clause). -/
theorem audit_trichotomy_not_ray (R : GRegime) (hR : R.kind ≠ 0) :
    ∀ᵐ omega ∂R.sampleLaw.law,
      ¬ QuasiIsometric (R.sampleLaw.graph omega) BranchingProcess.rayGraph :=
  classification_not_ray_ae R hR

/-- `offspring_classification_ae_iff` (`thm:trichotomy` quantified over raw offspring laws
written with their true top support). -/
theorem audit_trichotomy_exact {J J' N N' : ℕ}
    (theta : Offspring J) (hJN : J ≤ N)
    (hvalid : theta.IsSupercritical ∨ theta 1 = 1)
    (htop : theta 1 = 1 ∨ (2 ≤ J ∧ 0 < theta J))
    (theta' : Offspring J') (hJN' : J' ≤ N')
    (hvalid' : theta'.IsSupercritical ∨ theta' 1 = 1)
    (htop' : theta' 1 = 1 ∨ (2 ≤ J' ∧ 0 < theta' J')) :
    let R := GRegime.ofExact theta hJN hvalid htop
    let R' := GRegime.ofExact theta' hJN' hvalid' htop'
    ∀ᵐ omega ∂(R.sampleLaw.law.prod R'.sampleLaw.law),
      GPairQI R.sampleLaw R'.sampleLaw omega ↔
        (theta 1 = 1 ∧ theta' 1 = 1) ∨
        (theta 0 = 0 ∧ theta 1 = 0 ∧ theta' 0 = 0 ∧ theta' 1 = 0) ∨
        ((theta 0 = 0 ∧ 0 < theta 1 ∧ theta 1 < 1) ∧
          (theta' 0 = 0 ∧ 0 < theta' 1 ∧ theta' 1 < 1) ∧
          AddSubmonoid.closure (shiftSupp theta : Set ℕ) =
            AddSubmonoid.closure (shiftSupp theta' : Set ℕ)) ∨
        (0 < theta 0 ∧ 0 < theta' 0) :=
  offspring_classification_ae_iff theta hJN hvalid htop theta' hJN' hvalid' htop'

/-- `offspring_classification_not_ray_ae` (the raw-law form of the one-sample corollary). -/
theorem audit_trichotomy_exact_not_ray {J N : ℕ}
    (theta : Offspring J) (hJN : J ≤ N)
    (hvalid : theta.IsSupercritical ∨ theta 1 = 1)
    (htop : theta 1 = 1 ∨ (2 ≤ J ∧ 0 < theta J)) (h1 : theta 1 ≠ 1) :
    let R := GRegime.ofExact theta hJN hvalid htop
    ∀ᵐ omega ∂R.sampleLaw.law,
      ¬ QuasiIsometric (R.sampleLaw.graph omega) BranchingProcess.rayGraph :=
  offspring_classification_not_ray_ae theta hJN hvalid htop h1

end

end ChainClasses
