import ChainClasses.Engine.ProfileMatching
import ChainClasses.Engine.ProfileAssembly
import ChainClasses.Engine.ChainWitnesses
import ChainClasses.Universality.ChainPieces
import ChainClasses.Regime.DirectChainLabels
import ChainClasses.Chain.Eta
import ChainClasses.Universality.ChainGeneral
import ChainClasses.Universality.ChainSeparationProof
import GraphMarkovMatching.Stopped.Perturbation

/-! The common-core weight obstruction: finite-profile laws remain continuous when a
positive core mass tends to zero, even though the limiting arity supports need not have
the same branching semigroup. -/

namespace ChainClasses.Profile

open MeasureTheory
open GraphMarkovMatching GraphMarkovMatching.Support GraphMarkovMatching.Stopped
open scoped ENNReal NNReal Classical

lemma tvDist_freshRaw_le (μ ν ν' : PMF ℕ) :
    tvDist (freshRaw μ ν) (freshRaw μ ν') ≤ tvDist ν ν' := by
  exact (tvDist_map_le _ _ _).trans (by simpa [tvDist_self] using (tvDist_prodPMF_le μ μ ν ν'))

lemma tvDist_childLaw_le (μ ν ν' : PMF ℕ) (v0 : ℕ) (c : ChildK) :
    tvDist (childLaw μ ν v0 c) (childLaw μ ν' v0 c) ≤ tvDist ν ν' := by
  cases c with
  | internal off t => simp [childLaw, tvDist_self]
  | slot j => exact tvDist_freshRaw_le μ ν ν'

lemma tvDist_rawKernel_le (C : Family) (μ ν ν' : PMF ℕ) (v0 : ℕ) (s : RawState ℕ) :
    tvDist (rawKernel C μ ν v0 s) (rawKernel C μ ν' v0 s) ≤ 2 * tvDist ν ν' := by
  refine (tvDist_prodPMF_le _ _ _ _).trans ?_
  exact (add_le_add (tvDist_childLaw_le μ ν ν' v0 _) (tvDist_childLaw_le μ ν ν' v0 _)).trans_eq
    (two_mul _).symm

/-- A finite binary restriction reads at most `2^(h+1)-1` independently sampled arities. -/
theorem tvDist_rawLaw_le (C : Family) (μ ν ν' : PMF ℕ) (v0 h : ℕ) :
    tvDist (rawLaw C μ ν v0 h) (rawLaw C μ ν' v0 h)
      ≤ ((2 ^ (h + 1) - 1 : ℕ) : ℝ≥0∞) * tvDist ν ν' :=
  tvDist_mix_muM_le_addresses _ _ _ _ _ (tvDist_freshRaw_le μ ν ν')
    (tvDist_rawKernel_le C μ ν ν' v0) h

noncomputable def stateLaw (C : Family) (μ ν : PMF ℕ) (v0 h : ℕ) : PMF (FullLab ℕ h) :=
  (rawLaw C μ ν v0 h).map (statesOf h)

noncomputable def profileFailure (C C' : Family) (μ ν ν' : PMF ℕ) (v0 h : ℕ)
    (R : ℕ → ℕ → Prop) : ℝ≥0∞ :=
  failureD (stateLaw C μ ν v0 h) (stateLaw C' μ ν' v0 h) (fullSim R h)

/-- Perturbing just the target arity law changes any finite matching failure by at most
its finite-address total-variation bound. -/
theorem profileFailure_le_add (C C' : Family) (μ ν ν₁ ν₂ : PMF ℕ) (v0 h : ℕ)
    (R : ℕ → ℕ → Prop) :
    profileFailure C C' μ ν ν₁ v0 h R ≤ profileFailure C C' μ ν ν₂ v0 h R
      + ((2 ^ (h + 1) - 1 : ℕ) : ℝ≥0∞) * tvDist ν₁ ν₂ := by
  unfold profileFailure
  refine (failureD_le_add_tvDist_right _ _ _ _).trans (add_le_add le_rfl ?_)
  exact (tvDist_map_le _ _ _).trans (tvDist_rawLaw_le C' μ ν₁ ν₂ v0 h)

/-- The target law `t δ₂ + (1-t) δ₃`; this definition also includes the boundary `t=0`. -/
noncomputable def arityMix (t : ℝ≥0) (ht : t ≤ 1) : PMF ℕ :=
  (PMF.ofFintype (fun b : Bool => if b then (t : ℝ≥0∞) else ↑(1 - t)) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    exact_mod_cast add_tsub_cancel_of_le ht)).map (fun b => if b then 2 else 3)

lemma arityMix_apply (t : ℝ≥0) (ht : t ≤ 1) (k : ℕ) :
    arityMix t ht k = (if k = 2 then (t : ℝ≥0∞) else 0)
      + (if k = 3 then (↑(1 - t) : ℝ≥0∞) else 0) := by
  rw [arityMix, PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp only [PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]

lemma tvDist_arityMix_pure (t : ℝ≥0) (ht : t ≤ 1) :
    tvDist (arityMix t ht) (PMF.pure 3) = t := by
  rw [tvDist]
  have hterm : ∀ k, arityMix t ht k - PMF.pure 3 k = if k = 2 then (t : ℝ≥0∞) else 0 := by
    intro k
    rw [arityMix_apply]
    by_cases hk2 : k = 2
    · subst k; simp
    · by_cases hk3 : k = 3
      · subst k
        have hw : (↑(1 - t) : ℝ≥0∞) ≤ 1 := by
          exact_mod_cast (tsub_le_self : (1 - t : ℝ≥0) ≤ 1)
        norm_num only [PMF.pure_apply_self, show ¬(3 : ℕ) = 2 by decide,
          if_false, if_true, zero_add]
        exact tsub_eq_zero_of_le hw
      · simp [hk2, hk3, PMF.pure_apply]
  simp_rw [hterm]
  simp

/-- Any bound uniform in the positive common-core mass passes to its zero-mass boundary
at each fixed height. No presentation or positivity condition is used at the boundary. -/
theorem profileFailure_boundary_le (C C' : Family) (μ ν : PMF ℕ) (v0 h : ℕ)
    (R : ℕ → ℕ → Prop) (b : ℝ≥0∞)
    (hbound : ∀ (t : ℝ≥0) (_ht0 : 0 < t) (ht1 : t < 1),
      profileFailure C C' μ ν (arityMix t ht1.le) v0 h R ≤ b) :
    profileFailure C C' μ ν (PMF.pure 3) v0 h R ≤ b := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let a : ℝ≥0 := (2 ^ (h + 1) - 1 : ℕ)
  let t : ℝ≥0 := min (1 / 2) (ε / (a + 1))
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ha1 : 0 < a + 1 := by positivity
  have hta : (a + 1) * t ≤ ε := by
    have := min_le_right (1 / 2 : ℝ≥0) (ε / (a + 1))
    exact (mul_comm t (a + 1)).symm ▸ (le_div_iff₀ ha1).mp this
  have hat : a * t ≤ ε := (mul_le_mul_of_nonneg_right (by simp : a ≤ a + 1) (show 0 ≤ t from zero_le)).trans hta
  have hpert := profileFailure_le_add C C' μ ν (PMF.pure 3) (arityMix t ht1.le) v0 h R
  rw [tvDist_comm, tvDist_arityMix_pure] at hpert
  refine hpert.trans (add_le_add (hbound t ht0 ht1) ?_)
  exact_mod_cast hat

/-- The fixed binary and ternary profiles of the obstruction. The unused arities are
completed by left spines. -/
def binaryTernaryFamily : Family where
  tree k := MTree.node (spine (k - 2)) MTree.leaf
  leaves k hk := by simp only [MTree.leaves, leaves_spine]; omega
  root k := ⟨_, _, Or.inl rfl⟩

@[simp] lemma binaryTernaryFamily_two :
    binaryTernaryFamily.tree 2 = MTree.node MTree.leaf MTree.leaf := rfl

@[simp] lemma binaryTernaryFamily_three :
    binaryTernaryFamily.tree 3 = MTree.node (MTree.node MTree.leaf MTree.leaf) MTree.leaf := rfl

lemma prodPMF_not_rel_eq_failureD {W : Type} [MeasurableSpace W]
    [MeasurableSingletonClass W] [Countable W] (p q : PMF W) (R : W → W → Prop) :
    (prodPMF p q).toMeasure {z : W × W | ¬ R z.1 z.2} = failureD p q R := by
  rw [PMF.toMeasure_apply _ (Set.to_countable _).measurableSet, ENNReal.tsum_prod', failureD]
  refine tsum_congr fun x => ?_
  rw [qE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  rw [Set.indicator_apply]
  by_cases h : R x y
  · simp [Set.mem_setOf_eq, h]
  · simp [Set.mem_setOf_eq, prodPMF_apply, h]

/-- Product patterns identify the encoded state law without a common-core assumption. -/
theorem map_encodedStates_raw {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (Q : Measure Ω) {lab ar : Ω → GWord N → ℕ}
    (hlab : ∀ w a, MeasurableSet {ω | lab ω w = a})
    (har : ∀ w k, MeasurableSet {ω | ar ω w = k}) (μ ν : PMF ℕ)
    (hpat : ProductPatterns Q lab ar μ ν)
    (hsupp : ∀ k, ν k ≠ 0 → 2 ≤ k ∧ k ≤ N) (C : Family) (v0 n : ℕ) :
    Q.map (fun ω => encodedStates C (lab ω) (ar ω) v0 n) = (stateLaw C μ ν v0 n).toMeasure := by
  have hm := measurable_encLab_of hlab har C v0 n
  have hs := measurable_of_countable (statesOf (V := ℕ) (X := RawType) n)
  change Q.map ((statesOf n) ∘ (fun ω => encLab C (lab ω) (ar ω) v0 n)) = _
  rw [← Measure.map_map hs hm, map_encLab_of_pattern Q hlab har μ ν hpat hsupp C v0 n]
  exact PMF.toMeasure_map _ _ hs

/-- The finite-branching passage to infinite matching for arbitrary realised state fields. -/
theorem infFailure_le_of_finite {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (R : ℕ → ℕ → Prop) (X Y : (n : ℕ) → Ω → FullLab ℕ n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (b : ℝ≥0∞) (hfinite : ∀ n, Q {ω | ¬ fullSim R n (X n ω) (Y n ω)} ≤ b) :
    Q {ω | ¬ InfMatch R (fun n => X n ω) (fun n => Y n ω)} ≤ b := by
  let E : ℕ → Set Ω := fun n => {ω | ¬ fullSim R n (X n ω) (Y n ω)}
  have hmono : Monotone E := by
    apply monotone_nat_of_le_succ
    intro n ω hn hnext
    apply hn
    have hr := fullSimK_restrict R 1 0 n (X (n + 1) ω) (Y (n + 1) ω) hnext
    simpa only [hX n ω, hY n ω, fullSim] using hr
  have hEq : {ω | ¬ InfMatch R (fun n => X n ω) (fun n => Y n ω)} = ⋃ n, E n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
    change (¬ InfMatchK R 1 0 (fun n => X n ω) (fun n => Y n ω)) ↔ _
    rw [infMatchK_iff_forall_level R 1 0 (fun n => X n ω) (fun n => Y n ω)
      (fun n => hX n ω) (fun n => hY n ω)]
    simp only [not_forall, fullSim]
  rw [hEq, hmono.measure_iUnion]
  exact iSup_le hfinite

/-- If the boundary has almost surely no infinite matching, its finite failures cannot
all satisfy any constant bound strictly below one. -/
theorem boundaryFailure_ge_one {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (C C' : Family) (μ : PMF ℕ)
    (R : ℕ → ℕ → Prop) (X Y : (n : ℕ) → Ω → FullLab ℕ n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hmeas : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Q.map (fun ω => (X n ω, Y n ω)) =
      (prodPMF (stateLaw C μ (PMF.pure 2) 0 n) (stateLaw C' μ (PMF.pure 3) 0 n)).toMeasure)
    (hnull : ∀ᵐ ω ∂Q, ¬ InfMatch R (fun n => X n ω) (fun n => Y n ω))
    (b : ℝ≥0∞) (hbound : ∀ n, profileFailure C C' μ (PMF.pure 2) (PMF.pure 3) 0 n R ≤ b) :
    1 ≤ b := by
  have hprob : Q {ω | ¬ InfMatch R (fun n => X n ω) (fun n => Y n ω)} = 1 :=
    calc Q {ω | ¬ InfMatch R (fun n => X n ω) (fun n => Y n ω)} = Q Set.univ :=
      measure_congr (by
        filter_upwards [hnull] with ω hω
        exact propext (iff_true_intro hω))
      _ = 1 := measure_univ
  rw [← hprob]
  apply infFailure_le_of_finite Q R X Y hX hY b
  intro n
  change Q ((fun ω => (X n ω, Y n ω)) ⁻¹'
    {p : FullLab ℕ n × FullLab ℕ n | ¬ fullSim R n p.1 p.2}) ≤ b
  rw [← Measure.map_apply (hmeas n) (Set.to_countable _).measurableSet,
    hlaw n, prodPMF_not_rel_eq_failureD]
  exact hbound n

/-- A matching of pure quantised neck labels gives a quasi-isometry for any prescribed
bounded profiles, regardless of the branching semigroups of their arity laws. -/
theorem sample_qi_of_pure_chain_match {N N' L L' D : ℕ} [NeZero N] [NeZero N']
    (C C' : Family) {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    (hc : IsGHairySample c) (hc' : IsGHairySample c')
    (h1 : ∀ v, 1 ≤ c v) (h1' : ∀ v, 1 ≤ c' v)
    (hs : SkelBounded L (gArityAt c)) (hs' : SkelBounded L' (gArityAt c'))
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hD : 2 ≤ D)
    (hm : InfMatch (GraphMatching.compat GraphMatching.pathGraph)
      (fun n => encodedStates C (directChainLab D c) (gArityAt c) 0 n)
      (fun n => encodedStates C' (directChainLab D c') (gArityAt c') 0 n)) :
    BranchingProcess.QuasiIsometric (wordGraphN (· ∈ BranchingProcess.sample c))
      (wordGraphN (· ∈ BranchingProcess.sample c')) := by
  let A : GShape → ℕ → Prop := fun τ x => ∃ n, τ = flatG n ∧ x = levelMap D (n + 1)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  have hR : (1 : ℝ) ≤ (D : ℝ) ^ 2 := one_le_pow₀ hD1
  have hK : (1 : ℝ) ≤ 2 * (D : ℝ) ^ 2 + 1 := by nlinarith
  have h0 : A gOne 0 := by
    refine ⟨0, rfl, ?_⟩
    exact ((level_eq_iff hD (by omega : 1 ≤ 0 + 1)).mpr (by simp; omega)).symm
  have hcomp : ∀ τ τ' x y, A τ x → A τ' y →
      GraphMatching.compat GraphMatching.pathGraph x y →
        MarkedQI (2 * (D : ℝ) ^ 2 + 1) (gShapeSpace τ) (gShapeSpace τ') := by
    rintro τ τ' x y ⟨n, rfl, rfl⟩ ⟨n', rfl, rfl⟩ hxy
    have hclose : levelMap D (n + 1) ≤ levelMap D (n' + 1) + 1 ∧
        levelMap D (n' + 1) ≤ levelMap D (n + 1) + 1 := by
      rcases hxy with heq | hadj
      · omega
      · rw [GraphMatching.pathGraph_adj] at hadj
        omega
    obtain ⟨hr1, hr2⟩ := level_close_comparable hD (by omega) (by omega) hclose.1 hclose.2
    apply flatG_markedQI hR
    · exact_mod_cast hr2.le
    · exact_mod_cast hr1.le
  obtain ⟨F, hF⟩ := sample_qi_of_encoded_match C C' hc hc' hs hs' hL hL' hK A A
    (GraphMatching.compat GraphMatching.pathGraph) 0 h0 h0 hcomp
    (fun u hu => ⟨neckAt c u, gShapeAt_eq_flatG hc h1 hu, rfl⟩)
    (fun u hu => ⟨neckAt c' u, gShapeAt_eq_flatG hc' h1' hu, rfl⟩) hm
  exact ⟨_, F, hF⟩

/-- The proposed uniform estimate, already restricted to the path compatibility graph. -/
def UniformCoreWeightBound (K ε : ℝ) : Prop :=
  ∀ μ : PMF ℕ, ENNReal.ofReal (1 / 2 : ℝ) ≤ μ 0 →
    GraphMatching.etaG μ GraphMatching.pathGraph ≤ ENNReal.ofReal ε →
    ∀ (t : ℝ≥0) (_ht0 : 0 < t) (ht1 : t < 1) (h : ℕ),
      profileFailure binaryTernaryFamily binaryTernaryFamily μ (PMF.pure 2)
        (arityMix t ht1.le) 0 h (GraphMatching.compat GraphMatching.pathGraph)
          ≤ ENNReal.ofReal K * GraphMatching.etaG μ GraphMatching.pathGraph

/-- Arbitrarily small quantised one-site potentials turn boundary non-matching into
failure of every proposed uniform common-weight estimate. -/
theorem no_uniform_core_weight_bound_of_boundary
    (hboundary : ∀ (D : ℕ) (hD : 2 ≤ D) (b : ℝ≥0∞),
      (∀ h, profileFailure binaryTernaryFamily binaryTernaryFamily
        (qPMF (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hD)
        (PMF.pure 2) (PMF.pure 3) 0 h (GraphMatching.compat GraphMatching.pathGraph) ≤ b) → 1 ≤ b) :
    ¬ ∃ (K ε : ℝ), 0 < ε ∧ UniformCoreWeightBound K ε := by
  rintro ⟨K, ε, hε, hbound⟩
  have hK : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have he : 0 < min ε ((1 / 2) / max K 1) := lt_min hε (div_pos (by norm_num) hK)
  obtain ⟨D, hD, -, h1, h2, h3, -, hB⟩ :=
    exists_scale (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) he 2
  have hD2 : 2 ≤ D := by omega
  let μ := qPMF (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hD2
  have hB' : 16 * qBound (1 / 2) D ≤ min ε ((1 / 2) / max K 1) := by
    have := qBound_nonneg (1 / 2) D
    linarith
  have hμ : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ 0 := by
    rw [qPMF_apply, qF_zero]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have heta : GraphMatching.etaG μ GraphMatching.pathGraph ≤ ENNReal.ofReal (16 * qBound (1 / 2) D) :=
    quantised_eta_le (by norm_num) (by norm_num) hD h1 h2 h3
  have hetaε : GraphMatching.etaG μ GraphMatching.pathGraph ≤ ENNReal.ofReal ε :=
    heta.trans (ENNReal.ofReal_le_ofReal (hB'.trans (min_le_left _ _)))
  have hsmall : ENNReal.ofReal K * GraphMatching.etaG μ GraphMatching.pathGraph ≤ 1 / 2 := by
    have hreal : max K 1 * (16 * qBound (1 / 2) D) ≤ 1 / 2 := by
      have := (le_div_iff₀ hK).mp (hB'.trans (min_le_right _ _))
      nlinarith
    calc _ ≤ ENNReal.ofReal (max K 1) * ENNReal.ofReal (16 * qBound (1 / 2) D) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) heta
      _ = ENNReal.ofReal (max K 1 * (16 * qBound (1 / 2) D)) :=
        (ENNReal.ofReal_mul hK.le).symm
      _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hreal
      _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have hlarge := hboundary D hD2 (ENNReal.ofReal K * GraphMatching.etaG μ GraphMatching.pathGraph)
    (fun h => profileFailure_boundary_le binaryTernaryFamily binaryTernaryFamily μ (PMF.pure 2)
      0 h (GraphMatching.compat GraphMatching.pathGraph) _
      (fun t ht0 ht1 => hbound μ hμ hetaε t ht0 ht1 h))
  have : (1 : ℝ≥0∞) ≤ 1 / 2 := hlarge.trans hsmall
  norm_num at this

/-! ### Realising the boundary on independent original chain trees -/

open ChainWitnesses

noncomputable def boundaryLeftMeasure : Measure (GWord 3 → ℕ) :=
  BranchingProcess.survivalMeasure theta2

noncomputable def boundaryRightMeasure : Measure (GWord 3 → ℕ) :=
  BranchingProcess.survivalMeasure theta3

instance : IsProbabilityMeasure boundaryLeftMeasure :=
  BranchingProcess.isProbabilityMeasure_survivalMeasure theta2 (by decide)
    (extinction_lt_one_of_chain theta2 theta2_zero)

instance : IsProbabilityMeasure boundaryRightMeasure :=
  BranchingProcess.isProbabilityMeasure_survivalMeasure theta3 (by decide)
    (extinction_lt_one_of_chain theta3 theta3_zero)

noncomputable def boundaryField (D n : ℕ) (c : GWord 3 → ℕ) : FullLab ℕ n :=
  encodedStates binaryTernaryFamily (directChainLab D c) (gArityAt c) 0 n

noncomputable def boundaryMu (D : ℕ) (hD : 2 ≤ D) : PMF ℕ :=
  qPMF (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hD

lemma measurable_boundaryField (D n : ℕ) : Measurable (boundaryField D n) :=
  measurable_encodedStates (measurableSet_directChainLab_fibre D)
    fibreMeasurableG_gArityAt binaryTernaryFamily 0 n

lemma boundaryPattern_two (D : ℕ) (hD : 2 ≤ D) :
    ProductPatterns boundaryLeftMeasure (directChainLab D) gArityAt
      (boundaryMu D hD) (PMF.pure 2) := by
  intro F hpc a j hcomp
  have h := directChainPattern theta2 (N := 3) (by decide) theta2_zero theta2_one_lt_one
    (by decide) hD F hpc a j hcomp
  rw [reducedPMF_theta2] at h
  have hμ : qPMF (theta2.nonneg 1) theta2_one_lt_one hD = boundaryMu D hD := by
    ext k
    simp only [qPMF_apply, boundaryMu, theta2_one]
  rw [hμ] at h
  exact h

lemma boundaryPattern_three (D : ℕ) (hD : 2 ≤ D) :
    ProductPatterns boundaryRightMeasure (directChainLab D) gArityAt
      (boundaryMu D hD) (PMF.pure 3) := by
  intro F hpc a j hcomp
  have h := directChainPattern theta3 (N := 3) (by decide) theta3_zero theta3_one_lt_one
    (by decide) hD F hpc a j hcomp
  rw [reducedPMF_theta3] at h
  have hμ : qPMF (theta3.nonneg 1) theta3_one_lt_one hD = boundaryMu D hD := by
    ext k
    simp only [qPMF_apply, boundaryMu, theta3_one]
  rw [hμ] at h
  exact h

lemma map_boundaryField_left (D : ℕ) (hD : 2 ≤ D) (n : ℕ) :
    boundaryLeftMeasure.map (boundaryField D n) =
      (stateLaw binaryTernaryFamily (boundaryMu D hD) (PMF.pure 2) 0 n).toMeasure := by
  exact map_encodedStates_raw boundaryLeftMeasure (measurableSet_directChainLab_fibre D)
    fibreMeasurableG_gArityAt _ _ (boundaryPattern_two D hD)
    (by
      intro k hk
      have : k = 2 := by simpa [PMF.pure_apply] using hk
      omega)
    binaryTernaryFamily 0 n

lemma map_boundaryField_right (D : ℕ) (hD : 2 ≤ D) (n : ℕ) :
    boundaryRightMeasure.map (boundaryField D n) =
      (stateLaw binaryTernaryFamily (boundaryMu D hD) (PMF.pure 3) 0 n).toMeasure := by
  exact map_encodedStates_raw boundaryRightMeasure (measurableSet_directChainLab_fibre D)
    fibreMeasurableG_gArityAt _ _ (boundaryPattern_three D hD)
    (by
      intro k hk
      have : k = 3 := by simpa [PMF.pure_apply] using hk
      omega)
    binaryTernaryFamily 0 n

lemma map_boundaryField_pair (D : ℕ) (hD : 2 ≤ D) (n : ℕ) :
    (boundaryLeftMeasure.prod boundaryRightMeasure).map
      (fun ω => (boundaryField D n ω.1, boundaryField D n ω.2)) =
      (prodPMF (stateLaw binaryTernaryFamily (boundaryMu D hD) (PMF.pure 2) 0 n)
        (stateLaw binaryTernaryFamily (boundaryMu D hD) (PMF.pure 3) 0 n)).toMeasure :=
  map_prod_of_map_eq boundaryLeftMeasure boundaryRightMeasure
    (measurable_boundaryField D n) (measurable_boundaryField D n) _ _
    (map_boundaryField_left D hD n) (map_boundaryField_right D hD n)

/-- At the pure binary/ternary boundary, an infinite matching would contradict the
almost-sure separation of the two independent original chain trees. -/
theorem boundary_match_null (D : ℕ) (hD : 2 ≤ D) :
    ∀ᵐ ω ∂(boundaryLeftMeasure.prod boundaryRightMeasure),
      ¬ InfMatch (GraphMatching.compat GraphMatching.pathGraph)
        (fun n => boundaryField D n ω.1) (fun n => boundaryField D n ω.2) := by
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure theta2 (N := 3) (by decide)
    (extinction_lt_one_of_chain theta2 theta2_zero)
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure theta3 (N := 3) (by decide)
    (extinction_lt_one_of_chain theta3 theta3_zero)
  have hm : 1 ∈ AddSubmonoid.closure (shiftSupp theta2 : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp)
  have hm' : 1 ∉ AddSubmonoid.closure (shiftSupp theta3 : Set ℕ) := by
    rw [shiftSupp_theta3, Finset.coe_singleton]
    intro h
    obtain ⟨n, hn⟩ := AddSubmonoid.mem_closure_singleton.mp h
    simp only [nsmul_eq_mul] at hn
    omega
  have hsep := chainSeparation_side theta2 theta3 (N := 3) (N' := 3)
    (by decide) theta2_zero theta2_one_pos (by decide) theta3_zero hm hm'
  have hleft := ae_of_fst (ν := boundaryRightMeasure)
    (ae_direct_chain_good theta2 (N := 3) (by decide) theta2_zero theta2_one_lt_one (by decide))
  have hright := ae_of_snd (μ := boundaryLeftMeasure)
    (ae_direct_chain_good theta3 (N := 3) (by decide) theta3_zero theta3_one_lt_one (by decide))
  filter_upwards [hleft, hright, hsep] with ω h2 h3 hsep hmatch
  exact hsep (sample_qi_of_pure_chain_match binaryTernaryFamily binaryTernaryFamily
    h2.1 h3.1 h2.2.1 h3.2.1 h2.2.2 h3.2.2 (by decide) (by decide) hD hmatch)

/-- The explicit boundary laws have finite matching failures approaching one. -/
theorem binary_ternary_boundaryFailure_ge_one (D : ℕ) (hD : 2 ≤ D) (b : ℝ≥0∞)
    (hbound : ∀ h, profileFailure binaryTernaryFamily binaryTernaryFamily (boundaryMu D hD)
      (PMF.pure 2) (PMF.pure 3) 0 h (GraphMatching.compat GraphMatching.pathGraph) ≤ b) : 1 ≤ b := by
  exact boundaryFailure_ge_one (boundaryLeftMeasure.prod boundaryRightMeasure)
    binaryTernaryFamily binaryTernaryFamily (boundaryMu D hD)
    (GraphMatching.compat GraphMatching.pathGraph)
    (fun n ω => boundaryField D n ω.1) (fun n ω => boundaryField D n ω.2)
    (fun n ω => restrict_encodedStates _ _ _ _ n)
    (fun n ω => restrict_encodedStates _ _ _ _ n)
    (fun n => ((measurable_boundaryField D n).comp measurable_fst).prodMk
      ((measurable_boundaryField D n).comp measurable_snd))
    (map_boundaryField_pair D hD) (boundary_match_null D hD) b hbound

/-- `thm:core-weight-obstruction`: no constants work uniformly as the common binary
arity mass tends to zero, even for the path graph and profiles of height at most two. -/
theorem no_uniform_core_weight_bound :
    ¬ ∃ (K ε : ℝ), 0 < ε ∧ UniformCoreWeightBound K ε :=
  no_uniform_core_weight_bound_of_boundary binary_ternary_boundaryFailure_ge_one

/-! ### The same obstruction for infinite matching -/

lemma stateLaw_map_restrictLab (C : Family) (μ ν : PMF ℕ) (v0 h : ℕ) :
    (stateLaw C μ ν v0 (h + 1)).map (restrictLab h) = stateLaw C μ ν v0 h := by
  rw [stateLaw, PMF.map_comp]
  have heq : restrictLab h ∘ statesOf (V := ℕ) (X := RawType) (h + 1) =
      statesOf h ∘ restrictLab h := by
    funext x
    exact restrict_statesOf h x
  rw [heq, ← PMF.map_comp, rawLaw, mix_map_restrictLab]
  rfl

/-- The canonical law of two independent infinite state fields with these profile laws. -/
noncomputable def profileTrajectory (C C' : Family) (μ ν ν' : PMF ℕ) (v0 : ℕ) :
    Measure ((Π n, FullLab ℕ n) × (Π n, FullLab ℕ n)) :=
  trajPairLab (stateLaw C μ ν v0) (stateLaw_map_restrictLab C μ ν v0)
    (stateLaw C' μ ν' v0) (stateLaw_map_restrictLab C' μ ν' v0)

noncomputable def profileInfiniteFailure (C C' : Family) (μ ν ν' : PMF ℕ) (v0 : ℕ)
    (R : ℕ → ℕ → Prop) : ℝ≥0∞ :=
  profileTrajectory C C' μ ν ν' v0
    {ω | ¬ InfMatch R (fun n => consLab n ω.1) (fun n => consLab n ω.2)}

/-- A failed finite restriction rules out infinite matching. -/
lemma profileFailure_le_infiniteFailure (C C' : Family) (μ ν ν' : PMF ℕ) (v0 h : ℕ)
    (R : ℕ → ℕ → Prop) :
    profileFailure C C' μ ν ν' v0 h R ≤ profileInfiniteFailure C C' μ ν ν' v0 R := by
  have heq : profileTrajectory C C' μ ν ν' v0
      {ω | ¬ fullSim R h (consLab h ω.1) (consLab h ω.2)} =
      profileFailure C C' μ ν ν' v0 h R := by
    change profileTrajectory C C' μ ν ν' v0
      ((fun ω => (consLab h ω.1, consLab h ω.2)) ⁻¹'
        {p : FullLab ℕ h × FullLab ℕ h | ¬ fullSim R h p.1 p.2}) = _
    rw [← Measure.map_apply (measurable_consLab_pair h) (Set.to_countable _).measurableSet,
      profileTrajectory, trajPairLab_map_consLab, prodPMF_not_rel_eq_failureD]
    rfl
  rw [← heq]
  apply measure_mono
  intro ω hfail hinf
  have hall := (infMatchK_iff_forall_level R 1 0 (fun n => consLab n ω.1)
    (fun n => consLab n ω.2) (fun n => restrictLab_consLab n ω.1)
    (fun n => restrictLab_consLab n ω.2)).mp hinf
  exact hfail (hall h)

/-- The proposed uniform bound in its infinite-matching form. -/
def UniformCoreWeightInfiniteBound (K ε : ℝ) : Prop :=
  ∀ μ : PMF ℕ, ENNReal.ofReal (1 / 2 : ℝ) ≤ μ 0 →
    GraphMatching.etaG μ GraphMatching.pathGraph ≤ ENNReal.ofReal ε →
    ∀ (t : ℝ≥0) (_ht0 : 0 < t) (ht1 : t < 1),
      profileInfiniteFailure binaryTernaryFamily binaryTernaryFamily μ (PMF.pure 2)
        (arityMix t ht1.le) 0 (GraphMatching.compat GraphMatching.pathGraph)
          ≤ ENNReal.ofReal K * GraphMatching.etaG μ GraphMatching.pathGraph

/-- The infinite-matching conclusion of `thm:core-weight-obstruction`. -/
theorem no_uniform_core_weight_infinite_bound :
    ¬ ∃ (K ε : ℝ), 0 < ε ∧ UniformCoreWeightInfiniteBound K ε := by
  rintro ⟨K, ε, hε, hbound⟩
  apply no_uniform_core_weight_bound
  refine ⟨K, ε, hε, ?_⟩
  intro μ hμ heta t ht0 ht1 h
  exact (profileFailure_le_infiniteFailure _ _ _ _ _ _ h _).trans
    (hbound μ hμ heta t ht0 ht1)

end ChainClasses.Profile
