import ChainClasses.Regime.ChainNeckLaw
import ChainClasses.Engine.SkeletonPatterns
import ChainClasses.Regime.UniformField
import ChainClasses.Chain.Coupling

/-! Quantised labels on the original reduced necks. The arity distribution is the
original reduced law and is independent of the geometric quantisation scale. -/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure)

variable {J N : ℕ}

/-- The quantised length of the original reduced neck. -/
noncomputable def directChainLab (D : ℕ) (c : GWord N → ℕ) (u : GWord N) : ℕ :=
  levelMap D (neckAt c u + 1)

lemma measurableSet_directChainLab_fibre (D : ℕ) (u : GWord N) (k : ℕ) :
    MeasurableSet {c : GWord N → ℕ | directChainLab D c u = k} :=
  (fibreMeasurableG_neckAt u).preimage {n | levelMap D (n + 1) = k}

lemma measurable_directChainLab (D : ℕ) (u : GWord N) :
    Measurable fun c : GWord N → ℕ => directChainLab D c u :=
  measurable_to_countable' fun k => measurableSet_directChainLab_fibre D u k

/-- The coupled class of an original reduced neck, using the uniform at its address. -/
noncomputable def directCrossLab (a b : ℝ) (D : ℕ)
    (ω : (GWord N → ℕ) × (GWord N → ℝ)) (u : GWord N) : ℕ :=
  ellQ a b D (neckAt ω.1 u + 1) (ω.2 u)

lemma measurableSet_directCrossLab_fibre (a b : ℝ) (D : ℕ) (u : GWord N) (k : ℕ) :
    MeasurableSet {ω : (GWord N → ℕ) × (GWord N → ℝ) | directCrossLab a b D ω u = k} := by
  have hset : {ω : (GWord N → ℕ) × (GWord N → ℝ) | directCrossLab a b D ω u = k}
      = ⋃ n : ℕ, {c : GWord N → ℕ | neckAt c u = n}
          ×ˢ {U : GWord N → ℝ | ellQ a b D (n + 1) (U u) = k} := by
    ext ⟨c, U⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, directCrossLab]
    exact ⟨fun h => ⟨_, rfl, h⟩, by rintro ⟨n, h1, h2⟩; rw [h1]; exact h2⟩
  rw [hset]
  exact MeasurableSet.iUnion fun n => (fibreMeasurableG_neckAt u n).prod
    (BranchingProcess.measurable_coord (α := ℝ) u (ellQ_section_measurable a b D (n + 1) k))

lemma measurable_directCrossLab (a b : ℝ) (D : ℕ) (u : GWord N) :
    Measurable fun ω : (GWord N → ℕ) × (GWord N → ℝ) => directCrossLab a b D ω u :=
  measurable_to_countable' fun k => measurableSet_directCrossLab_fibre a b D u k

lemma direct_level_succ_eq_iff {D n k : ℕ} (hD : 2 ≤ D) :
    levelMap D (n + 1) = k ↔ n ∈ Finset.Ico (D ^ k - 1) (D ^ (k + 1) - 1) := by
  rw [level_eq_iff hD (by omega), Finset.mem_Ico]
  have h1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ D ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  omega

/-- `eq:qk` on the neck: the geometric weights `a^n` over the necks
`n = m - 1` of class `k` sum to `p^{(D)}_k/(1-a)`, the split probability `1 - a` left to the
rule mass. -/
lemma direct_chain_class_sum {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    ∑ n ∈ Finset.Ico (D ^ k - 1) (D ^ (k + 1) - 1), a ^ n = qF a D k / (1 - a) := by
  have hpos : 0 < 1 - a := by linarith
  rw [eq_div_iff hpos.ne', Finset.sum_mul, ← class_sum ha hD k]
  have h1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : D ^ k ≤ D ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show D ^ (k + 1) - 1 - (D ^ k - 1) = D ^ (k + 1) - D ^ k by omega]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show D ^ k - 1 + i = D ^ k + i - 1 by omega]

/-- The class mass in `ℝ≥0∞`, as the sum over all neck lengths selected by the
level label. -/
lemma direct_chain_class_tsum {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    ∑' n : ℕ, (if levelMap D (n + 1) = k then ENNReal.ofReal a ^ n else 0)
      = ENNReal.ofReal (qF a D k) / ENNReal.ofReal (1 - a) := by
  have hpos : 0 < 1 - a := by linarith
  rw [tsum_eq_sum (s := Finset.Ico (D ^ k - 1) (D ^ (k + 1) - 1))
      (fun n hn ↦ by rw [if_neg fun h ↦ hn ((direct_level_succ_eq_iff hD).mp h)]),
    Finset.sum_congr rfl (fun n hn ↦ by
      rw [if_pos ((direct_level_succ_eq_iff hD).mpr hn), ← ENNReal.ofReal_pow ha]),
    ← ENNReal.ofReal_sum_of_nonneg (fun n _ ↦ pow_nonneg ha n), direct_chain_class_sum ha ha1 hD k,
    ENNReal.ofReal_div_of_pos hpos]

lemma direct_cross_class_sum {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) :
    ∑ n ∈ Finset.Ico (DQ a b D k - 1) (DQ a b D (k + 1)), b ^ n * uWeight a b D k (n + 1)
      = qF a D k / (1 - b) := by
  have hpos : 0 < 1 - b := by linarith
  have hm1 := one_le_DQ (cgamma_pos ha ha1 hb hb1) hD k
  rw [eq_div_iff hpos.ne', Finset.sum_mul, ← coupling_sum ha ha1 hb hb1 hD hgD k]
  have hshift := Finset.sum_Ico_add' (fun m ↦ uWeight a b D k m * gmass b m)
    (DQ a b D k - 1) (DQ a b D (k + 1)) 1
  rw [show DQ a b D k - 1 + 1 = DQ a b D k by omega] at hshift
  rw [← hshift]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [gmass_succ]
  ring

/-- The same computation in `ℝ≥0∞`, summed over all neck lengths. -/
lemma direct_cross_class_tsum {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) :
    ∑' n : ℕ, ENNReal.ofReal b ^ n * ENNReal.ofReal (uWeight a b D k (n + 1))
      = ENNReal.ofReal (qF a D k) / ENNReal.ofReal (1 - b) := by
  have hpos : 0 < 1 - b := by linarith
  have hm1 := one_le_DQ (cgamma_pos ha ha1 hb hb1) hD k
  have hDQ := DQ_lt_succ ha ha1 hb hb1 hD hgD k
  have hvan : ∀ n ∉ Finset.Ico (DQ a b D k - 1) (DQ a b D (k + 1)),
      ENNReal.ofReal b ^ n * ENNReal.ofReal (uWeight a b D k (n + 1)) = 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have e1 : ¬n + 1 = DQ a b D k := by omega
    have e2 : ¬n + 1 = DQ a b D (k + 1) := by omega
    have e3 : ¬(DQ a b D k < n + 1 ∧ n + 1 < DQ a b D (k + 1)) := by omega
    have hz : uWeight a b D k (n + 1) = 0 := by
      unfold uWeight
      rw [if_neg e1, if_neg e2, if_neg e3]
    rw [hz, ENNReal.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hvan, Finset.sum_congr rfl (fun n _ ↦ by
      rw [← ENNReal.ofReal_pow hb.le, ← ENNReal.ofReal_mul (pow_nonneg hb.le n)]),
    ← ENNReal.ofReal_sum_of_nonneg (fun n _ ↦
      mul_nonneg (pow_nonneg hb.le n) (uWeight_nonneg ha ha1 hb hb1 hD k (n + 1))),
    direct_cross_class_sum ha ha1 hb hb1 hD hgD k, ENNReal.ofReal_div_of_pos hpos]

/-- The joint product law of the quantised original necks and their reduced arities. -/
theorem directChainPattern_of_two_le (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) {D : ℕ} (hD : 2 ≤ D) (F : Finset (GWord N))
    (hpc : ∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) (a j : GWord N → ℕ)
    (hj2 : ∀ u ∈ F, 2 ≤ j u)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < j u) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, ({c : GWord N → ℕ | directChainLab D c u = a u}
          ∩ {c : GWord N → ℕ | gArityAt c u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (qF (θ 1) D (a u)) * ENNReal.ofReal (reducedWeight θ (j u)) := by
  classical
  have hq := extinction_lt_one_of_chain θ hθ0
  have hs1 : θ.skeletonWeight 1 < 1 := by
    rw [skeletonWeight_one_eq_of_chain θ hθ0]
    exact hθ1
  have ha0 : 0 ≤ θ 1 := θ.nonneg 1
  set rext : (↥F → ℕ) → GWord N → ℕ :=
    fun g u ↦ if h : u ∈ F then g ⟨u, h⟩ else 0 with hrext
  have hrext_apply : ∀ (g : ↥F → ℕ) (u : ↥F), rext g u = g u := by
    intro g u
    simp only [hrext, dif_pos u.2]
  set S : Set (↥F → ℕ) := {g | ∀ u : ↥F, levelMap D (g u + 1) = a u} with hS
  set E : (↥F → ℕ) → Set (GWord N → ℕ) := fun g ↦
    ⋂ u ∈ F, ({ω : GWord N → ℕ | neckAt ω u = rext g u}
      ∩ {ω : GWord N → ℕ | gArityAt ω u = j u}) with hE
  have hcover : (⋂ u ∈ F, ({ω : GWord N → ℕ | directChainLab D ω u = a u}
        ∩ {ω : GWord N → ℕ | gArityAt ω u = j u}))
      = ⋃ g : ↥S, E g := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, directChainLab,
      hE, hS, Subtype.exists, exists_prop]
    constructor
    · intro h
      refine ⟨fun u ↦ neckAt ω u, fun u ↦ (h u u.2).1, fun u hu ↦ ⟨?_, (h u hu).2⟩⟩
      simp only [hrext, dif_pos hu]
    · rintro ⟨g, hgS, hg⟩ u hu
      obtain ⟨h1, h2⟩ := hg u hu
      refine ⟨?_, h2⟩
      rw [h1]
      simp only [hrext, dif_pos hu]
      exact hgS ⟨u, hu⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun g : ↥S ↦ E g) := by
    intro g g' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne (Subtype.ext (funext fun u ↦ ?_))
    simp only [hE, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hω hω'
    have e1 := (hω u u.2).1
    have e2 := (hω' u u.2).1
    rw [hrext_apply] at e1 e2
    rw [← e1, ← e2]
  have hmeas : ∀ g : ↥S, MeasurableSet (E g) := fun g ↦
    MeasurableSet.biInter F.countable_toSet fun u _ ↦
      (fibreMeasurableG_neckAt u _).inter (fibreMeasurableG_gArityAt u _)
  rw [hcover, measure_iUnion hdisj hmeas,
    tsum_congr fun g : ↥S ↦ survivalMeasure_neckArity θ hJN hq F hpc (rext g) j hj2 hcomp]
  simp only [neckPairMass]
  -- Sum the independent neck lengths over each prescribed class.
  have h1 : ∀ g : ↥F → ℕ, (∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (rext g u)
        * ENNReal.ofReal (θ.skeletonWeight (j u)))
      = ∏ u : ↥F, ENNReal.ofReal (θ 1) ^ (g u)
          * ENNReal.ofReal (θ.skeletonWeight (j u)) := by
    intro g
    rw [← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun u _ ↦ by
      rw [hrext_apply g u, skeletonWeight_one_eq_of_chain θ hθ0]
  have h2 : ∀ g : ↥S, (∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (rext g u)
        * ENNReal.ofReal (θ.skeletonWeight (j u)))
      = ∏ u : ↥F, (if levelMap D ((g : ↥F → ℕ) u + 1) = a u
          then ENNReal.ofReal (θ 1) ^ ((g : ↥F → ℕ) u) else 0)
          * ENNReal.ofReal (θ.skeletonWeight (j u)) := by
    intro g
    rw [h1]
    exact Finset.prod_congr rfl fun u _ ↦ by rw [if_pos (g.2 u)]
  rw [tsum_congr h2]
  rw [tsum_subtype_eq_of_support_subset (s := S) (f := fun g : ↥F → ℕ ↦
    ∏ u : ↥F, (if levelMap D (g u + 1) = a u then ENNReal.ofReal (θ 1) ^ (g u) else 0)
      * ENNReal.ofReal (θ.skeletonWeight (j u))) ?_]
  · rw [tsum_pi_prod fun (u : ↥F) (n : ℕ) ↦
        (if levelMap D (n + 1) = a u then ENNReal.ofReal (θ 1) ^ n else 0)
          * ENNReal.ofReal (θ.skeletonWeight (j u)), ← Finset.prod_coe_sort F]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    rw [ENNReal.tsum_mul_right, direct_chain_class_tsum ha0 hθ1 hD (a u), reducedWeight_def,
      skeletonWeight_one_eq_of_chain θ hθ0, ENNReal.ofReal_div_of_pos (sub_pos.mpr hθ1),
      div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, mul_assoc]
  · intro g hg
    by_contra hgS
    apply hg
    simp only [hS, Set.mem_setOf_eq, not_forall] at hgS
    obtain ⟨u, hu⟩ := hgS
    exact Finset.prod_eq_zero (Finset.mem_univ u) (by rw [if_neg hu, zero_mul])


/-- Coupled labels have the first law's quantised class law and the second law's
original reduced arity law. -/
theorem directCrossPattern_of_two_le (θ' : Offspring J) (hJN' : J ≤ N) (hθ0' : θ' 0 = 0)
    (hθ1' : 0 < θ' 1) (hθ1'' : θ' 1 < 1) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a (θ' 1) * ((D : ℝ) - 1))
    (F : Finset (GWord N)) (hpc : ∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F)
    (x j : GWord N → ℕ) (hj2 : ∀ u ∈ F, 2 ≤ j u)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < j u) :
    labelMeasure θ'
        (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (GWord N → ℝ) |
            directCrossLab a (θ' 1) D ω u = x u}
          ∩ {ω : (GWord N → ℕ) × (GWord N → ℝ) | gArityAt ω.1 u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (qF a D (x u)) * ENNReal.ofReal (reducedWeight θ' (j u)) := by
  classical
  have hq := extinction_lt_one_of_chain θ' hθ0'
  have hs1 : θ'.skeletonWeight 1 < 1 := by
    rw [skeletonWeight_one_eq_of_chain θ' hθ0']
    exact hθ1''
  -- the event as a probe of the labels `lab u (X u) (U u)`
  set X : (GWord N → ℕ) → GWord N → ℕ × ℕ :=
    fun ω u ↦ (neckAt ω u, gArityAt ω u) with hX
  set lab : GWord N → ℕ × ℕ → ℝ → ℕ × ℕ :=
    fun _ p r ↦ (ellQ a (θ' 1) D (p.1 + 1) r, p.2) with hlab
  set v : GWord N → ℕ × ℕ := fun u ↦ (x u, j u) with hv
  have hevent : (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (GWord N → ℝ) |
          directCrossLab a (θ' 1) D ω u = x u}
        ∩ {ω : (GWord N → ℕ) × (GWord N → ℝ) |
          gArityAt ω.1 u = j u}))
      = ⋂ u ∈ F, {ω : (GWord N → ℕ) × (GWord N → ℝ) |
          lab u (X ω.1 u) (ω.2 u) = v u} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, hlab, hX, hv, directCrossLab,
      Prod.mk.injEq]
  have hXm : ∀ u (t : ℕ × ℕ),
      MeasurableSet {ω : GWord N → ℕ | X ω u = t} := by
    intro u t
    have : {ω : GWord N → ℕ | X ω u = t}
        = {ω : GWord N → ℕ | neckAt ω u = t.1}
          ∩ {ω : GWord N → ℕ | gArityAt ω u = t.2} := by
      ext ω
      simp [hX, Prod.ext_iff]
    rw [this]
    exact (fibreMeasurableG_neckAt u t.1).inter
      (fibreMeasurableG_gArityAt u t.2)
  have hlabm : ∀ u (t w : ℕ × ℕ), MeasurableSet {r : ℝ | lab u t r = w} := by
    intro u t w
    by_cases h : t.2 = w.2
    · have : {r : ℝ | lab u t r = w} = {r : ℝ | ellQ a (θ' 1) D (t.1 + 1) r = w.1} := by
        ext r
        simp [hlab, Prod.ext_iff, h]
      rw [this]
      exact ellQ_section_measurable a (θ' 1) D (t.1 + 1) w.1
    · have : {r : ℝ | lab u t r = w} = ∅ := by
        ext r
        simp [hlab, Prod.ext_iff, h]
      rw [this]
      exact MeasurableSet.empty
  rw [hevent, labelMeasure,
    prod_uniformField_pattern (survivalMeasure (N := N) θ') X hXm lab hlabm F v]
  -- only the patterns with the prescribed arities contribute
  set emb : (↥F → ℕ) → (↥F → ℕ × ℕ) := fun g u ↦ (g u, j u) with hemb
  have hemb_inj : Function.Injective emb := by
    intro g g' h
    funext u
    have := congrFun h u
    simp only [hemb, Prod.mk.injEq] at this
    exact this.1
  set G : (↥F → ℕ × ℕ) → ℝ≥0∞ := fun f ↦
    survivalMeasure (N := N) θ' (⋂ u : ↥F, {ω : GWord N → ℕ | X ω u = f u})
      * ∏ u : ↥F, volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = v u} with hG
  have hsupp : Function.support G ⊆ Set.range emb := by
    intro f hf
    refine ⟨fun u ↦ (f u).1, ?_⟩
    by_contra hne
    apply hf
    have hu : ∃ u : ↥F, (f u).2 ≠ j u := by
      by_contra hall
      push Not at hall
      apply hne
      funext u
      simp only [hemb]
      exact Prod.ext rfl (hall u).symm
    obtain ⟨u, hu⟩ := hu
    have hzero : volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = v u} = 0 := by
      have : {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = v u} = ∅ := by
        ext r
        simp [hlab, hv, Prod.ext_iff, hu]
      rw [this, measure_empty]
    simp only [hG]
    rw [Finset.prod_eq_zero (Finset.mem_univ u) hzero, mul_zero]
  rw [← hemb_inj.tsum_eq hsupp]
  -- The neck/arity pattern is independent of the uniform class choices.
  set rext : (↥F → ℕ) → GWord N → ℕ :=
    fun g u ↦ if h : u ∈ F then g ⟨u, h⟩ else 0 with hrext
  have hrext_apply : ∀ (g : ↥F → ℕ) (u : ↥F), rext g u = g u := by
    intro g u
    simp only [hrext, dif_pos u.2]
  have hterm : ∀ g : ↥F → ℕ, G (emb g)
      = ∏ u : ↥F, ENNReal.ofReal (θ' 1) ^ (g u)
          * (ENNReal.ofReal (θ'.skeletonWeight (j u)))
          * ENNReal.ofReal (uWeight a (θ' 1) D (x u) (g u + 1)) := by
    intro g
    have hXset : (⋂ u : ↥F, {ω : GWord N → ℕ | X ω u = emb g u})
        = ⋂ u ∈ F, ({ω : GWord N → ℕ | neckAt ω u = rext g u}
            ∩ {ω : GWord N → ℕ | gArityAt ω u = j u}) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, hX, hemb, Prod.mk.injEq]
      constructor
      · intro h u hu
        obtain ⟨h1, h2⟩ := h ⟨u, hu⟩
        exact ⟨by rw [h1, hrext_apply g ⟨u, hu⟩], h2⟩
      · intro h u
        obtain ⟨h1, h2⟩ := h u u.2
        exact ⟨by rw [h1, hrext_apply g u], h2⟩
    have hvol : ∀ u : ↥F, volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (emb g u) r = v u}
        = ENNReal.ofReal (uWeight a (θ' 1) D (x u) (g u + 1)) := by
      intro u
      rw [← ellQ_section_volume ha ha1 hθ1' hθ1'' hD hgD (x u) (Nat.succ_pos (g u)),
        Measure.restrict_apply (ellQ_section_measurable a (θ' 1) D (g u + 1) (x u))]
      congr 1
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hlab, hemb, hv, Prod.mk.injEq, and_true]
      exact and_comm
    simp only [hG]
    rw [hXset, survivalMeasure_neckArity θ' hJN' hq F hpc (rext g) j hj2 hcomp,
      Finset.prod_congr rfl fun u _ ↦ hvol u, ← Finset.prod_coe_sort F,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    rw [neckPairMass, hrext_apply g u, skeletonWeight_one_eq_of_chain θ' hθ0']
  -- sum the patterns: one class mass per vertex
  rw [tsum_congr hterm, tsum_pi_prod fun (u : ↥F) (n : ℕ) ↦
      ENNReal.ofReal (θ' 1) ^ n * (ENNReal.ofReal (θ'.skeletonWeight (j u)))
        * ENNReal.ofReal (uWeight a (θ' 1) D (x u) (n + 1)), ← Finset.prod_coe_sort F]
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  have hre : ∀ n : ℕ, ENNReal.ofReal (θ' 1) ^ n
        * (ENNReal.ofReal (θ'.skeletonWeight (j u)))
        * ENNReal.ofReal (uWeight a (θ' 1) D (x u) (n + 1))
      = ENNReal.ofReal (θ' 1) ^ n * ENNReal.ofReal (uWeight a (θ' 1) D (x u) (n + 1))
        * ENNReal.ofReal (θ'.skeletonWeight (j u)) := fun n ↦ by ring
  rw [tsum_congr hre, ENNReal.tsum_mul_right, direct_cross_class_tsum ha ha1 hθ1' hθ1'' hD hgD (x u),
    reducedWeight_def, skeletonWeight_one_eq_of_chain θ' hθ0',
    ENNReal.ofReal_div_of_pos (sub_pos.mpr hθ1''), div_eq_mul_inv, div_eq_mul_inv,
    mul_right_comm, mul_assoc]


/-- The original reduced-neck product law, including arity patterns of zero mass. -/
theorem directChainPattern (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (hJ2 : 2 ≤ J) {D : ℕ} (hD : 2 ≤ D) (F : Finset (GWord N))
    (hpc : ∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) (a j : GWord N → ℕ)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < j u) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, ({c : GWord N → ℕ | directChainLab D c u = a u}
          ∩ {c : GWord N → ℕ | gArityAt c u = j u}))
      = ∏ u ∈ F, qPMF (θ.nonneg 1) hθ1 hD (a u) *
          reducedPMF θ (extinction_lt_one_of_chain θ hθ0) (chain_hs1 θ hθ0 hθ1) hJ2 (j u) := by
  by_cases hall : ∀ u ∈ F, 2 ≤ j u ∧ j u ≤ J
  · rw [directChainPattern_of_two_le θ hJN hθ0 hθ1 hD F hpc a j
      (fun u hu => (hall u hu).1) hcomp]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [qPMF_apply, reducedPMF_of_le θ _ _ hJ2 (hall u hu).1]
  · simp only [not_forall] at hall
    obtain ⟨t, ht, hbad⟩ := hall
    rw [Finset.prod_eq_zero ht (by rw [reducedPMF_eq_zero θ _ _ hJ2 hbad, mul_zero])]
    refine measure_mono_null ?_ (survivalMeasure_compat_bad_null θ hJN
      (extinction_lt_one_of_chain θ hθ0) (chain_hs1 θ hθ0 hθ1) hJ2 t)
    intro c hc
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hc
    refine ⟨?_, ?_⟩
    · rw [gCompat_iff]
      intro p i hpi
      have hmem : p ++ [i] ∈ F := hpc t ht _ hpi
      have hp : p ∈ F := hpc _ hmem p (List.prefix_append _ _)
      rw [(hc p hp).2]
      exact hcomp p hp i hmem
    · rw [(hc t ht).2]
      exact hbad

/-- The coupled original-neck product law, including arity patterns of zero mass. -/
theorem directCrossPattern (θ' : Offspring J) (hJN' : J ≤ N) (hθ0' : θ' 0 = 0)
    (hθ1' : 0 < θ' 1) (hθ1'' : θ' 1 < 1) (hJ2 : 2 ≤ J) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a (θ' 1) * ((D : ℝ) - 1))
    (F : Finset (GWord N)) (hpc : ∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F)
    (x j : GWord N → ℕ)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < j u) :
    labelMeasure θ'
        (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (GWord N → ℝ) |
            directCrossLab a (θ' 1) D ω u = x u}
          ∩ {ω : (GWord N → ℕ) × (GWord N → ℝ) | gArityAt ω.1 u = j u}))
      = ∏ u ∈ F, qPMF ha.le ha1 hD (x u) *
          reducedPMF θ' (extinction_lt_one_of_chain θ' hθ0')
            (chain_hs1 θ' hθ0' hθ1'') hJ2 (j u) := by
  by_cases hall : ∀ u ∈ F, 2 ≤ j u ∧ j u ≤ J
  · rw [directCrossPattern_of_two_le θ' hJN' hθ0' hθ1' hθ1'' ha ha1 hD hgD F hpc x j
      (fun u hu => (hall u hu).1) hcomp]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [qPMF_apply, reducedPMF_of_le θ' _ _ hJ2 (hall u hu).1]
  · simp only [not_forall] at hall
    obtain ⟨t, ht, hbad⟩ := hall
    rw [Finset.prod_eq_zero ht (by rw [reducedPMF_eq_zero θ' _ _ hJ2 hbad, mul_zero])]
    refine measure_mono_null ?_ (labelMeasure_compat_bad_null θ' hJN'
      (extinction_lt_one_of_chain θ' hθ0') (chain_hs1 θ' hθ0' hθ1'') hJ2 t)
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hω
    refine ⟨?_, ?_⟩
    · rw [gCompat_iff]
      intro p i hpi
      have hmem : p ++ [i] ∈ F := hpc t ht _ hpi
      have hp : p ∈ F := hpc _ hmem p (List.prefix_append _ _)
      rw [(hω p hp).2]
      exact hcomp p hp i hmem
    · rw [(hω t ht).2]
      exact hbad

end ChainClasses
