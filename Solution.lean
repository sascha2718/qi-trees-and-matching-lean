import Solution.Transport

/-!
# Proofs of the audited statements

Proofs of the thirteen theorems stated in `Challenge.lean`, for J. S. Athreya and S. Troscheit,
*The quasi-isometry classes of Galton–Watson trees*, arXiv:2609.23882. Theorem, equation and
condition numbers refer to version 1 of that paper. Each proof applies the corresponding
theorem of `Solution.Infrastructure`, which is proved from the four libraries, through the
identifications of `Solution.Transport`. `Solution.Definitions` repeats the challenge
vocabulary without importing `Challenge.lean`.
-/

namespace Challenge

open scoped ENNReal Classical
open MeasureTheory

/-! ## The i.i.d. matching theorem -/

/-- Theorem 5.1(1), the leaf bound (5.2). Let `μ` be a law on the vertex set of a graph `G`,
and call two labels compatible when they are equal or adjacent. If `η_{5/2}(μ) ≤ 1/256`, then
two independent leaf labellings of the binary tree of height `h`, each with i.i.d. labels of
law `μ`, admit no automorphism carrying every leaf to a leaf with a compatible label with
probability at most `(253/256)^h η_{5/2}(μ)`. The left side is this probability, written as
the expected mass of second labellings that the first labelling fails to match. -/
theorem audit_graph_leaf_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (h0 : potential (5 / 2) μ (compat G) ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * potential (5 / 2) μ (compat G) := by
  rw [Solution.Transport.potential_eq_graph] at h0 ⊢
  exact Solution.Infrastructure.audit_graph_leaf_matching_bound μ G h0 h

/-- Theorem 5.1(2), the full bound (5.3) at finite height. In the setting of the leaf bound,
with every vertex labelled, `η_{5/2}(μ) ≤ 10⁻⁴` implies that two independent labellings of the
binary tree of height `h` admit no automorphism matching every vertex with probability at most
`16 η_{5/2}(μ)`, uniformly in `h`. -/
theorem audit_graph_full_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (hη : potential (5 / 2) μ (compat G) ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim (compat G) h) x
      ≤ 16 * potential (5 / 2) μ (compat G) := by
  rw [Solution.Transport.potential_eq_graph] at hη ⊢
  exact Solution.Infrastructure.audit_graph_full_matching_bound μ G hη h

/-- Theorem 5.1(2) at infinite height. Let `R₀` be a reflexive symmetric compatibility
relation on a countable label set, which is compatibility in the graph joining distinct related
labels, and let `η_{5/2}(μ) ≤ 10⁻⁴`. There is a probability space carrying two sequences of
full labellings `X h`, `Y h` of all heights, each restricting to the previous one, such that
`(X h, Y h)` has the law of two independent labellings of height `h` with i.i.d. labels of law
`μ`. With probability at least `1 - 16 η_{5/2}(μ)`, there is one root-fixing automorphism `g`
of the infinite binary tree such that, at every vertex `s`, the label of `X` at `g s` is
compatible with the label of `Y` at `s`. -/
theorem audit_exists_infinite_tree_matching_graphAut {V : Type u} (μ : PMF V)
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hη : potential (5 / 2) μ R₀ ≤ 1 / 10000) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : (h : ℕ) → Ω → FullLab V h),
      (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
      (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
      (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
      (∀ h, P.map (fun ω => (X h ω, Y h ω))
        = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) ∧
      1 - 16 * potential (5 / 2) μ R₀ ≤ P {ω | ∃ g : List Bool ≃ List Bool, IsTreeAut g ∧
        ∀ s : List Bool, R₀ (coord (g s).length (X (g s).length ω) (g s))
          (coord s.length (Y s.length ω) s)} := by
  rw [Solution.Transport.potential_eq_iid μ R₀ hrefl] at hη ⊢
  exact Solution.Infrastructure.audit_exists_infinite_tree_matching_graphAut μ R₀ hrefl hsymm hη

/-! ## The finite class and the complete classification -/

/-- The finite class of Theorem 1.2, geometric input: a connected graph of bounded diameter is
quasi-isometric to the one-vertex graph. In particular, all finite trees are quasi-isometric to
one another. -/
theorem audit_bounded_graph_qi_point {V : Type u} (G : SimpleGraph V) (hconn : G.Connected)
    (hbdd : ∃ D : ℕ, ∀ x y, G.dist x y ≤ D) :
    GraphQuasiIsometric G (⊥ : SimpleGraph Unit) := by
  exact Solution.Infrastructure.audit_bounded_graph_qi_point G hconn hbdd

/-- The finite class of Theorem 1.2, probabilistic input: an offspring distribution with mean
at most one, other than the deterministic single child `θ(1) = 1`, gives an almost surely
finite Galton–Watson tree. Hence only the laws admitted in Theorem 1.2 survive with positive
probability. -/
theorem audit_extinction_of_not_supercritical {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hmean : ¬ theta.IsSupercritical) (h1 : theta 1 ≠ 1) :
    ∀ᵐ c ∂(gwField (N := N) theta), ¬ gwSurvives c := by
  exact Solution.Infrastructure.audit_extinction_of_not_supercritical theta hJN hmean h1

/-- Theorem 1.2, including the finite class, over the unconditioned laws. Let `θ` and `θ'` be
finitely supported offspring distributions and consider the trees cut out by independent
offspring fields. Almost surely, a root-preserving quasi-isometry between the two trees exists
exactly when both trees are finite, or both are infinite and `SameInfiniteClass θ θ'` holds;
and any quasi-isometry, root-preserving or not, forces the same alternative. The paper
conditions both trees on infinite diameter; here that conditioning is expressed through the
survival events, and the laws are unrestricted. -/
theorem audit_full_classification_ae_iff {J J' N N' : ℕ}
    (theta : Offspring J) (hJN : J ≤ N) (theta' : Offspring J') (hJN' : J' ≤ N') :
    ∀ᵐ omega ∂((gwField (N := N) theta).prod (gwField (N := N') theta')),
      (GraphQuasiIsometricRooted (wordGraph (inGWSample omega.1)) (wordGraph (inGWSample omega.2))
          (gwRoot omega.1) (gwRoot omega.2) ↔
        (¬ gwSurvives omega.1 ∧ ¬ gwSurvives omega.2) ∨
        (gwSurvives omega.1 ∧ gwSurvives omega.2 ∧ SameInfiniteClass theta theta')) ∧
      (GraphQuasiIsometric (wordGraph (inGWSample omega.1)) (wordGraph (inGWSample omega.2)) →
        (¬ gwSurvives omega.1 ∧ ¬ gwSurvives omega.2) ∨
        (gwSurvives omega.1 ∧ gwSurvives omega.2 ∧ SameInfiniteClass theta theta')) := by
  simpa only [Solution.Transport.sampleGraph_eq] using
    Solution.Infrastructure.audit_full_classification_ae_iff theta hJN theta' hJN'

/-! ## Mutual embeddability -/

/-- Theorem 1.3, mutual embeddability: a Galton–Watson tree with a finitely supported
supercritical offspring distribution, conditioned on infinite diameter, almost surely admits a
quasi-isometric embedding into the binary tree and receives one from it. The binary tree is
the parent–child graph of all words over a two-letter alphabet, and the conditioning is
expressed by quantifying over the surviving samples of the unconditioned law. -/
theorem audit_mutual_embeddability {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hsup : theta.IsSupercritical) :
    ∀ᵐ c ∂(gwField (N := N) theta), gwSurvives c →
      GraphQIEmbeddable (wordGraph (inGWSample c)) (wordGraph (fun _ : GWWord 2 => True)) ∧
      GraphQIEmbeddable (wordGraph (fun _ : GWWord 2 => True)) (wordGraph (inGWSample c)) := by
  simpa only [Solution.Transport.sampleGraph_eq] using
    Solution.Infrastructure.audit_mutual_embeddability theta hJN hsup

/-! ## Universality in the two-value family -/

/-- Theorem 1.4, almost-sure part. Let every vertex independently have two children with
probability `t` and one child otherwise. For every `t ∈ [0, 1]`, two independent such trees
almost surely admit a root-preserving quasi-isometry. -/
theorem audit_twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((bernoulliField ht0 ht1).prod (bernoulliField ht0 ht1))
      {ω | ¬ GraphQuasiIsometricRooted (wordGraph (InTree ω.1)) (wordGraph (InTree ω.2))
        ⟨[], InTree.root⟩ ⟨[], InTree.root⟩} = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ ((bernoulliField ht0 ht1).prod (bernoulliField ht0 ht1))
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
          Solution.Infrastructure.IsQIWith K (InTree ω.1) (InTree ω.2) f ∧ f [] = []} := by
      apply measure_mono
      rintro ω h ⟨K, f, hf, hroot⟩
      obtain ⟨g, hg, hgr⟩ := Solution.Transport.twovalue_qi hf hroot
      exact h ⟨K, g, hg, hgr⟩
    _ = 0 := Solution.Infrastructure.audit_twovalue_ae_tree_family ht0 ht1

/-- Theorem 1.4, the rate (1.1). For `0 < t < 1` there is `D₀` such that, for every `D ≥ D₀`,
the probability that two independent trees of the two-value family admit no root-preserving
`(D² + 3)`-quasi-isometry is at most `256 √((1 - t)^(D(2D - 5)))`. For `D ≥ 3` this equals
`256 θ(1)^(D(D - 5/2))` with `θ(1) = 1 - t`, so the constant `C` of (1.1) is `256`. -/
theorem audit_twovalue_rate_tree {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ((bernoulliField ht0.le ht1.le).prod (bernoulliField ht0.le ht1.le))
          {ω | ¬ ∃ f : {w // InTree ω.1 w} → {w // InTree ω.2 w},
            GraphQIWith (D ^ 2 + 3) (wordGraph (InTree ω.1)) (wordGraph (InTree ω.2)) f ∧
              f ⟨[], InTree.root⟩ = ⟨[], InTree.root⟩}
        ≤ ENNReal.ofReal (256 * Real.sqrt ((1 - t) ^ (D * (2 * D - 5)))) := by
  obtain ⟨D₀, hD⟩ := Solution.Infrastructure.audit_twovalue_rate_tree ht0 ht1
  refine ⟨D₀, fun D hd => le_trans (measure_mono ?_) (hD D hd)⟩
  rintro ω h ⟨f, hf, hroot⟩
  exact h (Solution.Transport.twovalue_qi hf hroot)

/-! ## The stopped Markov matching theorem -/

/-- Theorem 6.1, finite-type alternative at finite height. Fix `α ≥ 1` with `λ_α < 1` and
bounds `H`, `T ≥ 1` and `B ≥ 1`. There are constants `K` and `ε > 0`, depending only on
`α, H, T, B`, with the following property. Take any model with finitely many types and
reflexive symmetric compatibility, with a partition into cyclic classes of at most `T` types
each, transition sums `∑_{j ∈ supp P_t} P_t(j)^(-α) ≤ B`, conditions (M1) and (M2) with return
bound `H`, and `ζ_α ≤ ε`. Then two independent processes started at types of the same class
fail to match with probability at most `K ζ_α`, at every height. -/
theorem audit_markov_matching_finite {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1)
    (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Stopped.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Stopped.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      (∀ t, M.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t → ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := by
  obtain ⟨Kc, ε, hε, hb⟩ := Solution.Infrastructure.audit_markov_matching_finite hα hlam H T hT B hB
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I _ M hc g Θ hT' hB' hFP hCR hζ s t hst h
  rw [Solution.Transport.failProb_eq]
  exact hb M.toOld (M.toOld_compat hc) Θ.toOld hT' (Solution.Transport.fullSelection M) hB'
    (Solution.Transport.freshPositive_toOld M hFP) (M.returns_toOld Θ H hCR) hζ s t hst h

/-- Theorem 6.1, zero-compatible alternative at finite height. Fix `α ≥ 1` with `λ_α < 1`.
There are constants `K` and `ε > 0`, depending only on `α`, such that for every model with
reflexive symmetric compatibility, `δ = 0` (that is, `b(0) = 1`) and `ζ_α ≤ ε`, two independent
processes started at any two types fail to match with probability at most `K ζ_α`, at every
height. No finiteness, class or return hypothesis is imposed on the types. -/
theorem audit_markov_matching_zero {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Stopped.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := by
  obtain ⟨Kc, ε, hε, hb⟩ := Solution.Infrastructure.audit_markov_matching_zero hα hlam
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I M hc hδ hζ s t h
  rw [Solution.Transport.failProb_eq]
  exact hb M.toOld (M.toOld_compat hc) hδ hζ s t h

/-- Theorem 6.1, finite-type alternative at infinite height. Under the hypotheses of
`audit_markov_matching_finite`, with a countable state set, let `s` and `t` be types of the
same class. There is a probability space carrying two sequences of state labellings `X n`,
`Y n` of all heights, each restricting to the previous one, such that `(X n, Y n)` has the law
of two independent labellings of height `n` started at `s` and `t`. With probability at least
`1 - K ζ_α`, one root-fixing automorphism of the infinite binary tree matches their states at
every vertex. -/
theorem audit_markov_matching_finite_infinite {α : ℝ} (hα : 1 ≤ α)
    (hlam : Stopped.lambda α < 1) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V]
      (M : Stopped.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Stopped.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      (∀ t, M.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t →
      ∃ (Omega : Type) (_ : MeasurableSpace Omega) (P : Measure Omega)
        (_ : IsProbabilityMeasure P) (X Y : (n : ℕ) → Omega → FullLab V n),
        (∀ n omega, restrictLab n (X (n + 1) omega) = X n omega) ∧
        (∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega) ∧
        (∀ n, Measurable (fun omega => (X n omega, Y n omega))) ∧
        (∀ n, P.map (fun omega => (X n omega, Y n omega))
          = (prodPMF (M.rho s n) (M.rho t n)).toMeasure) ∧
        1 - ENNReal.ofReal Kc * M.zeta α
          ≤ P {omega | ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧
            ∀ w : List Bool, M.R
              (coord (aut w).length (X (aut w).length omega) (aut w))
              (coord w.length (Y w.length omega) w)} := by
  obtain ⟨Kc, ε, hε, hb⟩ :=
    Solution.Infrastructure.audit_markov_matching_finite_infinite hα hlam H T hT B hB
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I _ _ _ _ M hc g Θ hT' hB' hFP hCR hζ s t hst
  let : MeasurableSpace I := ⊤
  let : MeasurableSingletonClass I := ⟨fun _ => trivial⟩
  exact Solution.Transport.matchingProcess_erase M s t _
    (hb M.toOld (M.toOld_compat hc) Θ.toOld hT' (Solution.Transport.fullSelection M) hB'
      (Solution.Transport.freshPositive_toOld M hFP) (M.returns_toOld Θ H hCR) hζ s t hst)

/-- Theorem 6.1, zero-compatible alternative at infinite height. Under the hypotheses of
`audit_markov_matching_zero`, with countable state and type sets, the conclusion of
`audit_markov_matching_finite_infinite` holds for any two types `s` and `t`. -/
theorem audit_markov_matching_zero_infinite {α : ℝ} (hα : 1 ≤ α)
    (hlam : Stopped.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V] [Countable I] (M : Stopped.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t,
      ∃ (Omega : Type) (_ : MeasurableSpace Omega) (P : Measure Omega)
        (_ : IsProbabilityMeasure P) (X Y : (n : ℕ) → Omega → FullLab V n),
        (∀ n omega, restrictLab n (X (n + 1) omega) = X n omega) ∧
        (∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega) ∧
        (∀ n, Measurable (fun omega => (X n omega, Y n omega))) ∧
        (∀ n, P.map (fun omega => (X n omega, Y n omega))
          = (prodPMF (M.rho s n) (M.rho t n)).toMeasure) ∧
        1 - ENNReal.ofReal Kc * M.zeta α
          ≤ P {omega | ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧
            ∀ w : List Bool, M.R
              (coord (aut w).length (X (aut w).length omega) (aut w))
              (coord w.length (Y w.length omega) w)} := by
  obtain ⟨Kc, ε, hε, hb⟩ := Solution.Infrastructure.audit_markov_matching_zero_infinite hα hlam
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I _ _ _ _ M hc hδ hζ s t
  let : MeasurableSpace I := ⊤
  let : MeasurableSingletonClass I := ⟨fun _ => trivial⟩
  exact Solution.Transport.matchingProcess_erase M s t _
    (hb M.toOld (M.toOld_compat hc) hδ hζ s t)

end Challenge
