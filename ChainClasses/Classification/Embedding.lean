/-
`thm:embedding-hierarchy` of `prelims.tex`, proved in `quasi_isometric_embeddings.tex`:
a Galton-Watson tree with a finitely supported supercritical offspring law, conditioned
on infinite diameter, almost surely admits quasi-isometric embeddings into the binary
tree `𝔹 = 𝒩(2)` and from it; and the strict hierarchy `Fin ≺ Ray ≺ Supercritical` that
follows.

The embedding into `𝔹` is the isometric inclusion of the sample in `𝒩(N)` followed by
the quasi-isometry `𝒩(N) ≃ 𝔹` of `thm:bushy`.  For the embedding of `𝔹` the
classification is the tool: the law is replaced by a representative in the same class
which is concentrated at a large arity, `θ' = (7/8) δ_{J₁} + (1/8) θ` with
`J₁ - 1` a multiple of a generator of the branching semigroup, the pruning of
`ConcentratedPruning` places an isometric copy of `𝔹` in the representative's sample,
and `thm:trichotomy` transfers it through a quasi-isometry to the original sample.  One
representative serves the full-tree, chain and bushy classes alike, so the skeleton of
a bushy sample is not needed.

* `Offspring.concentrate`, `sameInfiniteClass_concentrate`: the representative and its
  class.
* `qiEmbeddable_ambient`, `quasiIsometric_ambient_binary`, `qiEmbeddable_sample_binary`:
  `𝒯 ≼ 𝔹`.
* `ae_qiEmbeddable_binary_sample`: `𝔹 ≼ 𝒯` almost surely on survival.
* `embedding_hierarchy_ae`: **`thm:embedding-hierarchy`**.
* `mutual_embeddability_ae`: two independent survival-conditioned samples embed into
  each other.
* `qiEmbeddable_rayGraph_of_not_survives`, `not_qiEmbeddable_rayGraph_of_not_survives`,
  `qiEmbeddable_rayGraph_of_survives`, `ae_not_qiEmbeddable_rayGraph`: the strict
  comparisons `Fin ≺ Ray ≺ Supercritical`.
-/
import ChainClasses.Classification.Finite
import ChainClasses.Universality.FullTree
import ChainClasses.Universality.ConcentratedPruning

/-! ### The concentrated representative -/

namespace BranchingProcess.Offspring

open ChainClasses

variable {J : ℕ} (θ : Offspring J)

/-- The concentrated representative of a law: mass `7/8` at the arity `J₁` and the law
scaled by `1/8`. -/
noncomputable def concentrate (J₁ : ℕ) (hJ : J ≤ J₁) : Offspring J₁ where
  mass k := (if k = J₁ then 7 / 8 else 0) + θ k / 8
  nonneg k := by
    have := θ.nonneg k
    split_ifs <;> linarith
  vanishing k hk := by
    rw [ite_eq_right (by omega), θ.vanishing k (by omega)]
    norm_num
  total := by
    have h1 : ∑ k ∈ Finset.range (J₁ + 1), θ k = 1 := by
      rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : J + 1 ≤ J₁ + 1))
        (fun k _ hk ↦ θ.vanishing k (by rw [Finset.mem_range] at hk; omega))]
      exact θ.total
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (J₁ + 1)) J₁
      (fun _ ↦ (7 / 8 : ℝ)), ite_eq_left (Finset.mem_range.2 (by omega)), ← Finset.sum_div, h1]
    norm_num

variable {J₁ : ℕ} (hJ : J ≤ J₁)

@[simp] lemma concentrate_apply (k : ℕ) :
    θ.concentrate J₁ hJ k = (if k = J₁ then 7 / 8 else 0) + θ k / 8 := rfl

lemma concentrate_zero (hJ₁ : 1 ≤ J₁) : θ.concentrate J₁ hJ 0 = θ 0 / 8 := by
  rw [concentrate_apply, ite_eq_right (by omega), zero_add]

lemma concentrate_one (hJ₁ : 2 ≤ J₁) : θ.concentrate J₁ hJ 1 = θ 1 / 8 := by
  rw [concentrate_apply, ite_eq_right (by omega), zero_add]

lemma concentrate_top : 7 / 8 ≤ θ.concentrate J₁ hJ J₁ := by
  rw [concentrate_apply, ite_eq_left rfl]
  have := θ.nonneg J₁
  linarith

lemma concentrate_top_pos : 0 < θ.concentrate J₁ hJ J₁ :=
  lt_of_lt_of_le (by norm_num) (θ.concentrate_top hJ)

/-- The representative is supercritical: its mean is at least `7 J₁ / 8`. -/
lemma concentrate_supercritical (hJ₁ : 2 ≤ J₁) : (θ.concentrate J₁ hJ).IsSupercritical := by
  unfold BranchingProcess.Offspring.IsSupercritical BranchingProcess.Offspring.mean
  have hnonneg : ∀ k ∈ Finset.range (J₁ + 1), (0 : ℝ) ≤ (k : ℝ) * θ.concentrate J₁ hJ k :=
    fun k _ ↦ mul_nonneg (Nat.cast_nonneg k) ((θ.concentrate J₁ hJ).nonneg k)
  have hterm := Finset.single_le_sum hnonneg (Finset.self_mem_range_succ J₁)
  have htop := θ.concentrate_top hJ
  have h2 : (2 : ℝ) ≤ J₁ := by exact_mod_cast hJ₁
  nlinarith

lemma concentrate_ne_zero_iff (k : ℕ) : θ.concentrate J₁ hJ k ≠ 0 ↔ k = J₁ ∨ θ k ≠ 0 := by
  rw [concentrate_apply]
  have := θ.nonneg k
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    rw [ite_eq_right hcon.1, hcon.2] at h
    norm_num at h
  · rintro (rfl | h)
    · rw [ite_eq_left rfl]
      positivity
    · split_ifs
      · positivity
      · rw [zero_add]
        exact div_ne_zero h (by norm_num)

/-- The shifted support of the representative: the original one and `J₁ - 1`. -/
lemma shiftSupp_concentrate (hJ₁ : 2 ≤ J₁) :
    shiftSupp (θ.concentrate J₁ hJ) = insert (J₁ - 1) (shiftSupp θ) := by
  ext x
  rw [Finset.mem_insert, mem_shiftSupp, mem_shiftSupp, concentrate_ne_zero_iff]
  constructor
  · rintro ⟨hx, h | h⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hx, h⟩
  · rintro (rfl | ⟨hx, h⟩)
    · exact ⟨by omega, Or.inl (by omega)⟩
    · exact ⟨hx, Or.inr h⟩

/-- The representative generates the same branching semigroup once `J₁ - 1` lies in
the original one. -/
lemma closure_shiftSupp_concentrate (hJ₁ : 2 ≤ J₁)
    (hmem : J₁ - 1 ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ)) :
    AddSubmonoid.closure (shiftSupp (θ.concentrate J₁ hJ) : Set ℕ)
      = AddSubmonoid.closure (shiftSupp θ : Set ℕ) := by
  rw [shiftSupp_concentrate θ hJ hJ₁, Finset.coe_insert]
  exact le_antisymm (AddSubmonoid.closure_le.2 (Set.insert_subset hmem AddSubmonoid.subset_closure))
    (AddSubmonoid.closure_mono (Set.subset_insert _ _))

/-- A supercritical law is not the deterministic single child. -/
lemma one_lt_one_of_supercritical (hsup : θ.IsSupercritical) : θ 1 < 1 := by
  have htop2 := θ.two_le_top_of_supercritical hsup
  have htop := θ.top_pos
  have hsub : ({1, θ.top} : Finset ℕ) ⊆ Finset.range (J + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have := θ.top_le
    rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ ↦ θ.nonneg j)
  rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ θ.top), θ.total] at hle
  linarith

/-- **The representative lies in the class of the law**, for every supercritical law. -/
theorem sameInfiniteClass_concentrate (hsup : θ.IsSupercritical) (hJ₁ : 2 ≤ J₁)
    (hmem : J₁ - 1 ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ)) :
    SameInfiniteClass θ (θ.concentrate J₁ hJ) := by
  unfold SameInfiniteClass
  rw [θ.concentrate_zero hJ (by omega), θ.concentrate_one hJ hJ₁,
    closure_shiftSupp_concentrate θ hJ hJ₁ hmem]
  have h0 := θ.nonneg 0
  have h1 := θ.nonneg 1
  have h1' := θ.one_lt_one_of_supercritical hsup
  rcases lt_or_eq_of_le h0 with h0 | h0
  · exact Or.inr (Or.inr (Or.inr ⟨h0, by positivity⟩))
  rcases lt_or_eq_of_le h1 with h1 | h1
  · refine Or.inr (Or.inr (Or.inl ⟨⟨h0.symm, h1, h1'⟩, ⟨by rw [← h0]; norm_num, by positivity,
      by linarith⟩, rfl⟩))
  · exact Or.inr (Or.inl ⟨h0.symm, h1.symm, by rw [← h0]; norm_num, by rw [← h1]; norm_num⟩)

end BranchingProcess.Offspring

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BranchingProcess (Offspring sample survivalMeasure sampleMeasure Survives QIEmbeddable
  QuasiIsometric rayGraph)

variable {J N : ℕ}

/-! ### `𝒯 ≼ 𝔹` -/

/-- The inclusion of a prefix-closed set of words in the ambient tree is isometric. -/
theorem qiEmbeddable_ambient {T : GWord N → Prop} (hT : PrefixClosedN T) :
    QIEmbeddable (wordGraphN T) (wordGraphN fun _ : GWord N ↦ True) :=
  BranchingProcess.qiEmbeddable_of_isometry (f := fun x ↦ ⟨x.1, trivial⟩) fun x y ↦ by
    rw [wordGraphN_dist prefixClosedN_true, wordGraphN_dist hT]

/-- `𝒩(N) ≃ 𝒩(2)` for `N ≥ 2`, through `thm:bushy` on both sides. -/
theorem quasiIsometric_ambient_binary (hN : 2 ≤ N) :
    QuasiIsometric (wordGraphN fun _ : GWord N ↦ True) (wordGraphN fun _ : GWord 2 ↦ True) :=
  QuasiIsometric.trans (wordGraphN_connected prefixClosedN_true ⟨⟨[], trivial⟩⟩)
    (fullTree_quasiIsometric_binary hN _ prefixClosedN_true trivial fun _ _ ↦ ⟨trivial, trivial⟩)
    (QuasiIsometric.symm (wordGraph_connected prefixClosed_true ⟨⟨[], trivial⟩⟩)
      (fullTree_quasiIsometric_binary le_rfl _ prefixClosedN_true trivial
        fun _ _ ↦ ⟨trivial, trivial⟩))

/-- **`𝒯 ≼ 𝔹`**: every sample over an alphabet with at least two letters embeds
quasi-isometrically into the binary tree. -/
theorem qiEmbeddable_sample_binary (hN : 2 ≤ N) (c : GWord N → ℕ) :
    QIEmbeddable (wordGraphN fun w : GWord N ↦ w ∈ sample c) (wordGraphN fun _ : GWord 2 ↦ True) :=
  (qiEmbeddable_ambient (prefixClosedN_sample c)).trans_quasiIsometric
    (quasiIsometric_ambient_binary hN)

/-! ### `𝔹 ≼ 𝒯` -/

section Product

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite ν]

/-- An almost sure statement about the first coordinate lifts to the product law. -/
lemma ae_prod_of_ae_fst {P : α → Prop} (h : ∀ᵐ a ∂μ, P a) :
    ∀ᵐ ω ∂μ.prod ν, P ω.1 := by
  rw [ae_iff] at h ⊢
  have hset : {ω : α × β | ¬ P ω.1} = {a | ¬ P a} ×ˢ Set.univ := by
    ext ω
    simp
  rw [hset, Measure.prod_prod, h, zero_mul]

/-- An almost sure statement about the second coordinate lifts to the product law. -/
lemma ae_prod_of_ae_snd {P : β → Prop} (h : ∀ᵐ b ∂ν, P b) :
    ∀ᵐ ω ∂μ.prod ν, P ω.2 := by
  rw [ae_iff] at h ⊢
  have hset : {ω : α × β | ¬ P ω.2} = Set.univ ×ˢ {b | ¬ P b} := by
    ext ω
    simp
  rw [hset, Measure.prod_prod, h, mul_zero]

end Product

/-- **`𝔹 ≼ 𝒯` almost surely on survival.**  The representative
`(7/8) δ_{J₁} + (1/8) θ` of the trimmed law, with `J₁ - 1 = 24 (J - 1)` a multiple of the
generator `J - 1` of the branching semigroup, lies in the class of `θ`; its sample carries
an isometric copy of `𝔹` almost surely on survival, and the classification transports it
through a quasi-isometry to the sample of `θ`. -/
theorem ae_qiEmbeddable_binary_sample (θ : Offspring J) (hJN : J ≤ N)
    (hsup : θ.IsSupercritical) :
    ∀ᵐ c ∂sampleMeasure (N := N) θ, Survives c →
      QIEmbeddable (wordGraphN fun _ : GWord 2 ↦ True)
        (wordGraphN fun w : GWord N ↦ w ∈ sample c) := by
  have hJ₀N : θ.top ≤ N := θ.top_le.trans hJN
  have hsup₀ : θ.trim.IsSupercritical := by
    unfold BranchingProcess.Offspring.IsSupercritical
    rw [BranchingProcess.Offspring.mean_trim]
    exact hsup
  have htop2 : 2 ≤ θ.top := θ.two_le_top_of_supercritical hsup
  have hJ₁ : θ.top ≤ 24 * (θ.top - 1) + 1 := by omega
  set J₁ := 24 * (θ.top - 1) + 1 with hJ₁def
  set θ₁ := θ.trim.concentrate J₁ hJ₁ with hθ₁
  have hmem : J₁ - 1 ∈ AddSubmonoid.closure (shiftSupp θ.trim : Set ℕ) := by
    have h : θ.top - 1 ∈ shiftSupp θ.trim :=
      max_mem_shiftSupp θ.trim htop2 (by rw [BranchingProcess.Offspring.trim_apply]; exact θ.top_pos)
    have hJ : J₁ - 1 = 24 • (θ.top - 1) := by
      rw [hJ₁def, smul_eq_mul]
      omega
    rw [hJ]
    exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure h) 24
  have hsame : SameInfiniteClass θ.trim θ₁ :=
    θ.trim.sameInfiniteClass_concentrate hJ₁ hsup₀ (by omega) hmem
  have hq₁ : θ₁.extinction < 1 :=
    θ₁.extinction_lt_one_of_supercritical (θ.trim.concentrate_supercritical hJ₁ (by omega))
  -- the representative carries the binary tree almost surely on survival
  have hprune : ∀ᵐ c' ∂sampleMeasure (N := J₁) θ₁, Survives c' →
      QIEmbeddable (wordGraphN fun _ : GWord 2 ↦ True)
        (wordGraphN fun w : GWord J₁ ↦ w ∈ sample c') :=
    ae_sampleMeasure_of_ae_survivalMeasure θ₁
      (ae_qiEmbeddable_binary_of_concentrated θ₁ le_rfl hq₁ (by omega) (θ.trim.concentrate_top hJ₁))
  -- the classification transports it
  have hcls := full_classification_ae_iff θ.trim hJ₀N θ₁ le_rfl
  rw [BranchingProcess.Offspring.sampleMeasure_trim] at hcls
  have hae : ∀ᵐ ω ∂((sampleMeasure (N := N) θ).prod (sampleMeasure (N := J₁) θ₁)),
      Survives ω.1 → Survives ω.2 →
        QIEmbeddable (wordGraphN fun _ : GWord 2 ↦ True)
          (wordGraphN fun w : GWord N ↦ w ∈ sample ω.1) := by
    filter_upwards [hcls, ae_prod_of_ae_snd (μ := sampleMeasure (N := N) θ) hprune]
      with ω hω hω' h1 h2
    have hqi : QuasiIsometric (wordGraphN fun w : GWord N ↦ w ∈ sample ω.1)
        (wordGraphN fun w : GWord J₁ ↦ w ∈ sample ω.2) := hω.2 (Or.inr ⟨h1, h2, hsame⟩)
    exact (hω' h2).trans_quasiIsometric (QuasiIsometric.symm
      (wordGraphN_connected (prefixClosedN_sample _) ⟨⟨[], BranchingProcess.nil_mem_sample _⟩⟩) hqi)
  -- the representative survives with positive probability, so its coordinate can be dropped
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with c hc hsurv
  by_contra hnot
  have hdead : ∀ᵐ c' ∂sampleMeasure (N := J₁) θ₁, ¬ Survives c' := by
    filter_upwards [hc] with c' hc' hs
    exact hnot (hc' hsurv hs)
  rw [ae_iff] at hdead
  simp only [not_not] at hdead
  exact BranchingProcess.sampleMeasure_survives_ne_zero θ₁ le_rfl hq₁ hdead

/-! ### The theorem -/

/-- **`thm:embedding-hierarchy`.**  A Galton-Watson tree with a finitely supported
supercritical offspring law almost surely admits, on survival, quasi-isometric
embeddings into the binary tree `𝒩(2)` and from it. -/
theorem embedding_hierarchy_ae (θ : Offspring J) (hJN : J ≤ N) (hsup : θ.IsSupercritical) :
    ∀ᵐ c ∂sampleMeasure (N := N) θ, Survives c →
      QIEmbeddable (wordGraphN fun w : GWord N ↦ w ∈ sample c)
          (wordGraphN fun _ : GWord 2 ↦ True) ∧
        QIEmbeddable (wordGraphN fun _ : GWord 2 ↦ True)
          (wordGraphN fun w : GWord N ↦ w ∈ sample c) := by
  have hN : 2 ≤ N := (θ.two_le_top_of_supercritical hsup).trans (θ.top_le.trans hJN)
  filter_upwards [ae_qiEmbeddable_binary_sample θ hJN hsup] with c hc hsurv
  exact ⟨qiEmbeddable_sample_binary hN c, hc hsurv⟩

/-- **Mutual embeddability.**  Two independent survival-conditioned samples of finitely
supported supercritical laws embed quasi-isometrically into each other, almost surely,
by composition through `𝔹`. -/
theorem mutual_embeddability_ae {J' N' : ℕ} (θ : Offspring J) (hJN : J ≤ N)
    (hsup : θ.IsSupercritical) (θ' : Offspring J') (hJN' : J' ≤ N') (hsup' : θ'.IsSupercritical) :
    ∀ᵐ ω ∂((sampleMeasure (N := N) θ).prod (sampleMeasure (N := N') θ')),
      Survives ω.1 → Survives ω.2 →
        QIEmbeddable (wordGraphN fun w : GWord N ↦ w ∈ sample ω.1)
            (wordGraphN fun w : GWord N' ↦ w ∈ sample ω.2) ∧
          QIEmbeddable (wordGraphN fun w : GWord N' ↦ w ∈ sample ω.2)
            (wordGraphN fun w : GWord N ↦ w ∈ sample ω.1) := by
  filter_upwards [ae_prod_of_ae_fst (ν := sampleMeasure (N := N') θ')
      (embedding_hierarchy_ae θ hJN hsup),
    ae_prod_of_ae_snd (μ := sampleMeasure (N := N) θ) (embedding_hierarchy_ae θ' hJN' hsup')]
    with ω h h' h1 h2
  exact ⟨(h h1).1.trans (h' h2).2, (h' h2).1.trans (h h1).2⟩

/-! ### The strict hierarchy `Fin ≺ Ray ≺ Supercritical` -/

/-- **`Fin ≼ Ray`**: a finite sample embeds into the ray. -/
theorem qiEmbeddable_rayGraph_of_not_survives {c : GWord N → ℕ} (hc : ¬ Survives c) :
    QIEmbeddable (wordGraphN fun w : GWord N ↦ w ∈ sample c) rayGraph :=
  BranchingProcess.qiEmbeddable_of_bounded (isBoundedGraph_sample_of_not_survives hc)

/-- **`Ray ⋠ Fin`**: the ray does not embed into a finite sample. -/
theorem not_qiEmbeddable_rayGraph_of_not_survives {c : GWord N → ℕ} (hc : ¬ Survives c) :
    ¬ QIEmbeddable rayGraph (wordGraphN fun w : GWord N ↦ w ∈ sample c) :=
  BranchingProcess.not_qiEmbeddable_of_not_bounded BranchingProcess.not_isBoundedGraph_rayGraph
    (isBoundedGraph_sample_of_not_survives hc)

/-- **`Ray ≼ 𝒯`**: an infinite sample carries a ray from its root, whose inclusion is
isometric. -/
theorem qiEmbeddable_rayGraph_of_survives {c : GWord N → ℕ} (hc : Survives c) :
    QIEmbeddable rayGraph (wordGraphN fun w : GWord N ↦ w ∈ sample c) := by
  obtain ⟨r, -, hrmem, hrstep, -⟩ :=
    BranchingProcess.exists_isometric_skeleton_ray (BranchingProcess.nil_mem_skeleton_iff.2 hc)
  exact BranchingProcess.qiEmbeddable_rayGraph_of_isRay (isRayN_of_chain (prefixClosedN_sample c)
    hrstep fun n ↦ BranchingProcess.skeleton_subset_sample _ (hrmem n))

/-- **`𝒯 ⋠ Ray`**: a survival-conditioned supercritical sample almost surely carries
three rays meeting only at their initial vertex, so it does not embed into the ray. -/
theorem ae_not_qiEmbeddable_rayGraph (θ : Offspring J) (hJN : J ≤ N)
    (hsup : θ.IsSupercritical) :
    ∀ᵐ c ∂sampleMeasure (N := N) θ, Survives c →
      ¬ QIEmbeddable (wordGraphN fun w : GWord N ↦ w ∈ sample c) rayGraph := by
  have hsup₀ : θ.trim.IsSupercritical := by
    unfold BranchingProcess.Offspring.IsSupercritical
    rw [BranchingProcess.Offspring.mean_trim]
    exact hsup
  have hq : θ.trim.extinction < 1 := θ.trim.extinction_lt_one_of_supercritical hsup₀
  have h := ae_sampleMeasure_of_ae_survivalMeasure θ.trim
    (threeRays_ae_of_top θ.trim (θ.top_le.trans hJN) hq (θ.two_le_top_of_supercritical hsup)
      (by rw [BranchingProcess.Offspring.trim_apply]; exact θ.top_pos))
  rw [BranchingProcess.Offspring.sampleMeasure_trim] at h
  filter_upwards [h] with c hc hsurv
  obtain ⟨v, ray, hray, hbase, hmeet⟩ := hc hsurv
  exact BranchingProcess.not_qiEmbeddable_rayGraph (wordGraphN_isTree (prefixClosedN_sample c) ⟨v⟩)
    hray hbase hmeet

end ChainClasses
