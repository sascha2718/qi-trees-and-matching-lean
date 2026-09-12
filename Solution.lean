/- The twelve challenge theorems, proved using the internal transports.
Solution.Definitions repeats the independent challenge vocabulary. -/
import Solution.Transport

namespace Challenge

open scoped ENNReal Classical
open MeasureTheory

/-! ## The i.i.d. matching theorem -/

/-- `thm:matching`(1): the leaf bound. -/
theorem audit_graph_leaf_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (h0 : potential (5 / 2) μ (compat G) ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * potential (5 / 2) μ (compat G) := by
  rw [Solution.Transport.potential_eq_graph] at h0 ⊢
  exact Solution.Infrastructure.audit_graph_leaf_matching_bound μ G h0 h

/-- `thm:matching`(2): the full bound. -/
theorem audit_graph_full_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (hη : potential (5 / 2) μ (compat G) ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim (compat G) h) x
      ≤ 16 * potential (5 / 2) μ (compat G) := by
  rw [Solution.Transport.potential_eq_graph] at hη ⊢
  exact Solution.Infrastructure.audit_graph_full_matching_bound μ G hη h

/-- `thm:matching`, the infinite tree: the matching automorphism as a root-fixing
automorphism of the infinite binary tree. -/
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

/-- Bounded connected graphs form one quasi-isometry class: each is quasi-isometric to a
single vertex. -/
theorem audit_bounded_graph_qi_point {V : Type u} (G : SimpleGraph V) (hconn : G.Connected)
    (hbdd : ∃ D : ℕ, ∀ x y, G.dist x y ≤ D) :
    GraphQuasiIsometric G (⊥ : SimpleGraph Unit) := by
  exact Solution.Infrastructure.audit_bounded_graph_qi_point G hconn hbdd

/-- A law with mean at most one dies out almost surely, unless it is the deterministic
single child `θ_1 = 1`. -/
theorem audit_extinction_of_not_supercritical {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hmean : ¬ theta.IsSupercritical) (h1 : theta 1 ≠ 1) :
    ∀ᵐ c ∂(gwField (N := N) theta), ¬ gwSurvives c := by
  exact Solution.Infrastructure.audit_extinction_of_not_supercritical theta hJN hmean h1

/-- `thm:trichotomy` in full: for two independent Galton--Watson trees with finitely supported
offspring laws, almost surely a root-preserving quasi-isometry exists exactly when both are
finite, or both are infinite and the two laws lie in the same infinite class, and otherwise no
quasi-isometry exists at all. -/
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

/-! ## Universality in the two-value family -/

/-- `thm:twovalue`: two independent Galton--Watson trees whose offspring law is
supported on `{1,2}` almost surely admit a root-preserving quasi-isometry. -/
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

/-- The quantitative half of `thm:twovalue`: above a threshold, failure of a root-preserving
`(D²+3)`-quasi-isometry has probability at most the explicit rate. -/
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

/-- `thm:markov-matching`, finite alternative: under the exponent condition `λ_α < 1`,
there are constants `K`, `ε > 0` depending only on `α, H, T, B` such that every finite
model with type classes of size at most `T`, full-support transition inverse sums at most
`B`, fresh positivity and common returns within `H`, and one-site defect `ζ_α ≤ ε`, has
every same-class pair failing to match at every height with probability at most `K ζ_α`. -/
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

/-- `thm:markov-matching`, zero-compatible alternative: under the exponent condition
`λ_α < 1`, there are constants `K`, `ε > 0` depending only on `α` such that every model
with `δ = 0` and `ζ_α ≤ ε` has every pair of types failing to match at every height with
probability at most `K ζ_α`. -/
theorem audit_markov_matching_zero {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Stopped.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := by
  obtain ⟨Kc, ε, hε, hb⟩ := Solution.Infrastructure.audit_markov_matching_zero hα hlam
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I M hc hδ hζ s t h
  rw [Solution.Transport.failProb_eq]
  exact hb M.toOld (M.toOld_compat hc) hδ hζ s t h

/-- `thm:markov-matching`, finite alternative at infinite height: two independent
consistent processes of same-class types admit one root-fixing infinite-tree
automorphism matching their states at every vertex with probability at least
`1 - K ζ_α`. -/
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
  letI : MeasurableSpace I := ⊤
  letI : MeasurableSingletonClass I := ⟨fun _ => trivial⟩
  exact Solution.Transport.matchingProcess_erase M s t _
    (hb M.toOld (M.toOld_compat hc) Θ.toOld hT' (Solution.Transport.fullSelection M) hB'
      (Solution.Transport.freshPositive_toOld M hFP) (M.returns_toOld Θ H hCR) hζ s t hst)

/-- `thm:markov-matching`, zero-compatible alternative at infinite height: two independent
consistent processes of any two types admit one root-fixing infinite-tree automorphism
matching their states at every vertex with probability at least `1 - K ζ_α`. -/
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
  letI : MeasurableSpace I := ⊤
  letI : MeasurableSingletonClass I := ⟨fun _ => trivial⟩
  exact Solution.Transport.matchingProcess_erase M s t _
    (hb M.toOld (M.toOld_compat hc) hδ hζ s t)

end Challenge
