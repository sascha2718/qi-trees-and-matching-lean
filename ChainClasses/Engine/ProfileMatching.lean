import ChainClasses.Engine.ProfileProjection
import GraphMarkovMatching.Stopped.Application
import GraphMarkovMatching.Stopped.Transfer

/-! The common-profile matching theorem on the original geometric probability space. -/

namespace ChainClasses.Profile

open MeasureTheory
open GraphMarkovMatching GraphMarkovMatching.Support GraphMarkovMatching.Stopped
open scoped ENNReal Classical

variable {N : ℕ}

/-- Complete a supported presentation by arbitrary binary profiles off its support. -/
noncomputable def presentationFamily (P : Presentation) (σ : Bool) : Family where
  tree k := if k ∈ P.supp σ then P.C σ k else MTree.node (spine (k - 2)) MTree.leaf
  leaves k hk := by
    split_ifs with hs
    · exact P.C_leaves σ k hs
    · simp only [MTree.leaves, leaves_spine]
      omega
  root k := by
    split_ifs with hs
    · obtain ⟨l, r, h⟩ := P.C_gnode σ k hs
      exact ⟨l, r, Or.inr h⟩
    · exact ⟨_, _, Or.inl rfl⟩

lemma presentationFamily_tree (P : Presentation) (σ : Bool) {k : ℕ} (hk : k ∈ P.supp σ) :
    (presentationFamily P σ).tree k = P.C σ k := ite_eq_left hk

noncomputable def encodedStates (C : Family) (lab ar : GWord N → ℕ) (v0 n : ℕ) : FullLab ℕ n :=
  statesOf n (encLab C lab ar v0 n)

lemma restrict_statesOf {V X : Type} (n : ℕ) (x : FullLab (V × X) (n + 1)) :
    restrictLab n (statesOf (n + 1) x) = statesOf n (restrictLab n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun p => (x.1.1, p)) (Prod.ext (ih x.2.1) (ih x.2.2))

lemma restrict_encodedStates (C : Family) (lab ar : GWord N → ℕ) (v0 n : ℕ) :
    restrictLab n (encodedStates C lab ar v0 (n + 1)) = encodedStates C lab ar v0 n := by
  rw [encodedStates, restrict_statesOf, restrictLab_encLab]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurableSet_infMatch (R : ℕ → ℕ → Prop)
    (X Y : (n : ℕ) → Ω → FullLab ℕ n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hM : ∀ n, Measurable fun ω => (X n ω, Y n ω)) :
    MeasurableSet {ω | InfMatch R (fun n => X n ω) (fun n => Y n ω)} := by
  have heq : {ω | InfMatch R (fun n => X n ω) (fun n => Y n ω)} =
      ⋂ n, (fun ω => (X n ω, Y n ω)) ⁻¹' {p | fullSimK R 1 0 n p.1 p.2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    exact infMatchK_iff_forall_level R 1 0 _ _ (fun n => hX n ω) (fun n => hY n ω)
  rw [heq]
  exact MeasurableSet.iInter fun n => (hM n) (Set.to_countable _).measurableSet

lemma measurable_encodedStates {lab ar : Ω → GWord N → ℕ}
    (hlab : ∀ w a, MeasurableSet {ω | lab ω w = a})
    (har : ∀ w k, MeasurableSet {ω | ar ω w = k}) (C : Family) (v0 n : ℕ) :
    Measurable fun ω => encodedStates C (lab ω) (ar ω) v0 n :=
  (measurable_of_countable (statesOf n)).comp (measurable_encLab_of hlab har C v0 n)

/-- Product law on every finite compatible probe of the original reduced skeleton. -/
def ProductPatterns (Q : Measure Ω) (lab ar : Ω → GWord N → ℕ) (μ ν : PMF ℕ) : Prop :=
  ∀ F : Finset (GWord N), (∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) →
    ∀ a k : GWord N → ℕ, (∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) →
      Q (⋂ u ∈ F, ({ω | lab ω u = a u} ∩ {ω | ar ω u = k u})) =
        ∏ u ∈ F, μ (a u) * ν (k u)

/-- The state law of the encoded geometric sample is the state law of the Markov model. -/
theorem map_encodedStates (P : Presentation) (C : Family) (σ : Bool)
    (hC : ∀ k, k ∈ P.supp σ → C.tree k = P.C σ k)
    (Q : Measure Ω) {lab ar : Ω → GWord N → ℕ}
    (hlab : ∀ w a, MeasurableSet {ω | lab ω w = a})
    (har : ∀ w k, MeasurableSet {ω | ar ω w = k}) (μ : PMF ℕ)
    (hpat : ProductPatterns Q lab ar μ (P.ν σ))
    (hN : ∀ k, k ∈ P.supp σ → k ≤ N) (R : ℕ → ℕ → Prop) (v0 n : ℕ) :
    Q.map (fun ω => encodedStates C (lab ω) (ar ω) v0 n) =
      (((P.toModel R v0 μ).rho (P.freshL σ) n).map (statesOf' n)).toMeasure := by
  have hm := measurable_encLab_of hlab har C v0 n
  have hs := measurable_of_countable (statesOf (V := ℕ) (X := RawType) n)
  change Q.map ((statesOf n) ∘ (fun ω => encLab C (lab ω) (ar ω) v0 n)) = _
  rw [← Measure.map_map hs hm, map_encLab_of_pattern Q hlab har μ (P.ν σ) hpat
    (fun k hk => ⟨P.two_le_supp σ k ((P.mem_supp σ k).mp hk), hN k ((P.mem_supp σ k).mp hk)⟩)
      C v0 n]
  rw [PMF.toMeasure_map _ _ hs, rawLaw_states P C σ R v0 μ hC n]

lemma map_prod_of_map_eq {Ω₁ Ω₂ α β : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace α] [MeasurableSpace β] [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [SFinite P₁] [SFinite P₂] {X : Ω₁ → α} {Y : Ω₂ → β}
    (hX : Measurable X) (hY : Measurable Y) (p₁ : PMF α) (p₂ : PMF β)
    (h₁ : P₁.map X = p₁.toMeasure) (h₂ : P₂.map Y = p₂.toMeasure) :
    (P₁.prod P₂).map (fun ω => (X ω.1, Y ω.2)) = (prodPMF p₁ p₂).toMeasure := by
  refine Measure.ext_of_singleton fun z => ?_
  obtain ⟨x, y⟩ := z
  have hmeas : Measurable fun ω : Ω₁ × Ω₂ => (X ω.1, Y ω.2) :=
    (hX.comp measurable_fst).prodMk (hY.comp measurable_snd)
  rw [Measure.map_apply hmeas (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), prodPMF_apply]
  have hpre : (fun ω : Ω₁ × Ω₂ => (X ω.1, Y ω.2)) ⁻¹' {(x, y)} =
      (X ⁻¹' {x}) ×ˢ (Y ⁻¹' {y}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Prod.mk.injEq]
  rw [hpre, Measure.prod_prod, ← Measure.map_apply hX (measurableSet_singleton x),
    ← Measure.map_apply hY (measurableSet_singleton y), h₁, h₂,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]

/-- A finite-height Markov failure bound transfers to the original independent geometric
samples, with one binary automorphism matching their complete encoded state fields. -/
theorem infMatch_of_patterns {N₁ N₂ : ℕ} {Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P : Presentation) (C₁ C₂ : Family)
    (hC₁ : ∀ k, k ∈ P.supp false → C₁.tree k = P.C false k)
    (hC₂ : ∀ k, k ∈ P.supp true → C₂.tree k = P.C true k)
    (Q₁ : Measure Ω₁) (Q₂ : Measure Ω₂) [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    {lab₁ ar₁ : Ω₁ → GWord N₁ → ℕ} {lab₂ ar₂ : Ω₂ → GWord N₂ → ℕ}
    (hlab₁ : ∀ w a, MeasurableSet {ω | lab₁ ω w = a})
    (har₁ : ∀ w k, MeasurableSet {ω | ar₁ ω w = k})
    (hlab₂ : ∀ w a, MeasurableSet {ω | lab₂ ω w = a})
    (har₂ : ∀ w k, MeasurableSet {ω | ar₂ ω w = k}) (μ : PMF ℕ)
    (hpat₁ : ProductPatterns Q₁ lab₁ ar₁ μ (P.ν false))
    (hpat₂ : ProductPatterns Q₂ lab₂ ar₂ μ (P.ν true))
    (hN₁ : ∀ k, k ∈ P.supp false → k ≤ N₁)
    (hN₂ : ∀ k, k ∈ P.supp true → k ≤ N₂) (R : ℕ → ℕ → Prop) (v0 : ℕ)
    (b : ℝ≥0∞) (hfail : ∀ n, (P.toModel R v0 μ).failProb (P.freshL false) (P.freshL true) n ≤ b) :
    1 - b ≤ (Q₁.prod Q₂) {ω | InfMatch R
      (fun n => encodedStates C₁ (lab₁ ω.1) (ar₁ ω.1) v0 n)
      (fun n => encodedStates C₂ (lab₂ ω.2) (ar₂ ω.2) v0 n)} := by
  exact (P.toModel R v0 μ).state_infMatch_ge_of_marginals (Q₁.prod Q₂) _ _ _ _
    (fun n ω => restrict_encodedStates C₁ _ _ v0 n)
    (fun n ω => restrict_encodedStates C₂ _ _ v0 n)
    (fun n => ((measurable_encodedStates hlab₁ har₁ C₁ v0 n).comp measurable_fst).prodMk
      ((measurable_encodedStates hlab₂ har₂ C₂ v0 n).comp measurable_snd))
    (fun n => map_prod_of_map_eq Q₁ Q₂
      (measurable_encodedStates hlab₁ har₁ C₁ v0 n) (measurable_encodedStates hlab₂ har₂ C₂ v0 n) _ _
      (map_encodedStates P C₁ false hC₁ Q₁ hlab₁ har₁ μ hpat₁ hN₁ R v0 n)
      (map_encodedStates P C₂ true hC₂ Q₂ hlab₂ har₂ μ hpat₂ hN₂ R v0 n)) b hfail

end ChainClasses.Profile
