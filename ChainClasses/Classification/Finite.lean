/-
The finite class and the complete classification.

`thm:trichotomy` opens with the finite realisations: they form one quasi-isometry class,
and no finite tree is quasi-isometric to an infinite one. This module supplies these facts
for Galton--Watson samples, the tightening of an offspring law to its actual top support,
and the complete classification over the unconditioned product law: two independent trees
are almost surely quasi-isometric exactly when both are finite, or both are infinite and the
two laws lie in the same infinite class.
-/
import BranchingProcess.Geometry
import BranchingProcess.Law
import BranchingProcess.Conditioned
import ChainClasses.Classification.Complete
import ChainClasses.Universality.GeneralObstructions

open MeasureTheory

/-! ### Tightening an offspring law to its top support -/

namespace BranchingProcess.Offspring

variable {J : ℕ} (θ : Offspring J)

/-- Some child count carries positive mass: the masses sum to one. -/
lemma support_nonempty : ((Finset.range (J + 1)).filter fun j => θ j ≠ 0).Nonempty := by
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (θ.total.trans_ne one_ne_zero)
  exact ⟨j, Finset.mem_filter.2 ⟨hj, hne⟩⟩

/-- The largest child count of positive mass. -/
noncomputable def top : ℕ :=
  ((Finset.range (J + 1)).filter fun j => θ j ≠ 0).max' θ.support_nonempty

lemma top_le : θ.top ≤ J := by
  have h := Finset.max'_mem _ θ.support_nonempty
  rw [Finset.mem_filter, Finset.mem_range] at h
  exact Nat.lt_succ_iff.1 h.1

lemma top_pos : 0 < θ θ.top := by
  have h := Finset.max'_mem _ θ.support_nonempty
  rw [Finset.mem_filter] at h
  exact lt_of_le_of_ne (θ.nonneg _) (Ne.symm h.2)

lemma vanishing_top {j : ℕ} (hj : θ.top < j) : θ j = 0 := by
  by_cases hJ : j ≤ J
  · by_contra hne
    have hmem : j ∈ (Finset.range (J + 1)).filter fun j => θ j ≠ 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hne⟩
    have hle : j ≤ θ.top := Finset.le_max' _ j hmem
    omega
  · exact θ.vanishing j (by omega)

/-- The same law with its support bound tightened to `top`. -/
noncomputable def trim : Offspring θ.top where
  mass := θ.mass
  nonneg := θ.nonneg
  vanishing := fun _ hj => θ.vanishing_top hj
  total := by
    refine (Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ θ.top_le))
      fun j hj hnot => ?_).trans θ.total
    rw [Finset.mem_range] at hj hnot
    exact θ.vanishing_top (by omega)

@[simp] lemma trim_apply (j : ℕ) : θ.trim j = θ j := rfl

lemma mean_trim : θ.trim.mean = θ.mean := by
  unfold mean
  refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ θ.top_le))
    fun j hj hnot => ?_
  rw [Finset.mem_range] at hj hnot
  rw [trim_apply, θ.vanishing_top (by omega), mul_zero]

/-- A supercritical law has positive mass at some child count of at least two. -/
lemma two_le_top_of_supercritical (h : θ.IsSupercritical) : 2 ≤ θ.top := by
  by_contra hlt
  have hmean : θ.mean = ∑ j ∈ Finset.range 2, (j : ℝ) * θ j := by
    rw [← θ.mean_trim]
    unfold mean
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hnot => ?_
    rw [Finset.mem_range] at hj hnot
    rw [trim_apply, θ.vanishing_top (by omega), mul_zero]
  rw [Finset.sum_range_succ, Finset.sum_range_one] at hmean
  norm_num at hmean
  have h1 := θ.mass_le_one 1
  unfold IsSupercritical at h
  linarith

lemma toPMF_trim : θ.trim.toPMF = θ.toPMF :=
  PMF.ext fun _ => rfl

lemma law_trim : θ.trim.law = θ.law := by
  unfold law
  rw [toPMF_trim]

lemma sampleMeasure_trim {N : ℕ} :
    sampleMeasure (N := N) θ.trim = sampleMeasure (N := N) θ := by
  unfold sampleMeasure
  simp only [law_trim]

lemma survivalMeasure_trim {N : ℕ} :
    survivalMeasure (N := N) θ.trim = survivalMeasure (N := N) θ := by
  unfold survivalMeasure
  rw [sampleMeasure_trim]

end BranchingProcess.Offspring

namespace ChainClasses

open BranchingProcess

/-! ### Finite and infinite samples -/

/-- The tree of a finite sample is bounded. -/
theorem isBoundedGraph_sample_of_not_survives {N : ℕ} {c : BranchingProcess.Word N → ℕ}
    (h : ¬ Survives c) :
    IsBoundedGraph (wordGraphN (fun w => w ∈ sample c)) := by
  have hfin : (sample c : Set (BranchingProcess.Word N)).Finite := Set.not_infinite.1 h
  obtain ⟨D, hD⟩ := (hfin.image List.length).bddAbove
  refine ⟨2 * D, fun u v => ?_⟩
  rw [wordGraphN_dist (prefixClosedN_sample c)]
  have hu : u.1.length ≤ D := hD ⟨u.1, u.2, rfl⟩
  have hv : v.1.length ≤ D := hD ⟨v.1, v.2, rfl⟩
  unfold BranchingProcess.treeDist
  omega

/-- The tree of an infinite sample is unbounded: infinitely many words over a finite
alphabet have unbounded length, and the root is at distance the length. -/
theorem not_isBoundedGraph_sample_of_survives {N : ℕ} {c : BranchingProcess.Word N → ℕ}
    (h : Survives c) :
    ¬ IsBoundedGraph (wordGraphN (fun w => w ∈ sample c)) := by
  rintro ⟨D, hD⟩
  obtain ⟨v, hlen, hmem⟩ := survives_iff_forall_level.1 h (D + 1)
  have hdist := hD ⟨[], nil_mem_sample c⟩ ⟨v, hmem⟩
  rw [wordGraphN_dist (prefixClosedN_sample c),
    BranchingProcess.treeDist_of_prefix (List.nil_prefix (l := v))] at hdist
  simp only [List.length_nil, Nat.sub_zero] at hdist
  omega

/-- **The finite class.** Two finite samples are quasi-isometric. -/
theorem quasiIsometric_sample_of_not_survives {N N' : ℕ} {c : BranchingProcess.Word N → ℕ}
    {c' : BranchingProcess.Word N' → ℕ} (hc : ¬ Survives c) (hc' : ¬ Survives c') :
    QuasiIsometric (wordGraphN (fun w => w ∈ sample c))
      (wordGraphN (fun w => w ∈ sample c')) := by
  have : Nonempty {w : BranchingProcess.Word N // w ∈ sample c} :=
    ⟨⟨[], nil_mem_sample c⟩⟩
  have : Nonempty {w : BranchingProcess.Word N' // w ∈ sample c'} :=
    ⟨⟨[], nil_mem_sample c'⟩⟩
  exact quasiIsometric_of_bounded (isBoundedGraph_sample_of_not_survives hc)
    (isBoundedGraph_sample_of_not_survives hc')

/-- No infinite sample is quasi-isometric to a finite one. -/
theorem not_quasiIsometric_sample_of_survives_left {N N' : ℕ}
    {c : BranchingProcess.Word N → ℕ} {c' : BranchingProcess.Word N' → ℕ}
    (hc : Survives c) (hc' : ¬ Survives c') :
    ¬ QuasiIsometric (wordGraphN (fun w => w ∈ sample c))
      (wordGraphN (fun w => w ∈ sample c')) :=
  fun hqi => not_isBoundedGraph_sample_of_survives hc
    (IsBoundedGraph.of_quasiIsometric hqi (isBoundedGraph_sample_of_not_survives hc'))

/-- No finite sample is quasi-isometric to an infinite one. -/
theorem not_quasiIsometric_sample_of_survives_right {N N' : ℕ}
    {c : BranchingProcess.Word N → ℕ} {c' : BranchingProcess.Word N' → ℕ}
    (hc : ¬ Survives c) (hc' : Survives c') :
    ¬ QuasiIsometric (wordGraphN (fun w => w ∈ sample c))
      (wordGraphN (fun w => w ∈ sample c')) :=
  fun hqi => not_isBoundedGraph_sample_of_survives hc'
    (IsBoundedGraph.of_quasiIsometric_of_connected
      (wordGraphN_connected (prefixClosedN_sample c') ⟨⟨[], nil_mem_sample c'⟩⟩) hqi
      (isBoundedGraph_sample_of_not_survives hc))

/-! ### The complete classification -/

lemma shiftSupp_trim {J : ℕ} (θ : Offspring J) : shiftSupp θ.trim = shiftSupp θ := by
  ext x
  rw [mem_shiftSupp, mem_shiftSupp, Offspring.trim_apply]

/-- Two laws lie in the same infinite class: both ray, both full tree, both chain with the
same branching semigroup, or both bushy. -/
def SameInfiniteClass {J J' : ℕ} (θ : Offspring J) (θ' : Offspring J') : Prop :=
  (θ 1 = 1 ∧ θ' 1 = 1) ∨
  (θ 0 = 0 ∧ θ 1 = 0 ∧ θ' 0 = 0 ∧ θ' 1 = 0) ∨
  ((θ 0 = 0 ∧ 0 < θ 1 ∧ θ 1 < 1) ∧ (θ' 0 = 0 ∧ 0 < θ' 1 ∧ θ' 1 < 1) ∧
    AddSubmonoid.closure (shiftSupp θ : Set ℕ) =
      AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) ∨
  (0 < θ 0 ∧ 0 < θ' 0)

lemma sameInfiniteClass_trim {J J' : ℕ} (θ : Offspring J) (θ' : Offspring J') :
    SameInfiniteClass θ.trim θ'.trim ↔ SameInfiniteClass θ θ' := by
  unfold SameInfiniteClass
  rw [shiftSupp_trim, shiftSupp_trim]
  exact Iff.rfl

/-- The conditioned classification written over the survival measures and the sample
graphs: `offspring_classification_ae_iff` with its packaged laws unfolded. -/
theorem offspring_classification_survival_ae_iff {J J' N N' : ℕ}
    (θ : Offspring J) (hJN : J ≤ N)
    (hvalid : θ.IsSupercritical ∨ θ 1 = 1)
    (htop : θ 1 = 1 ∨ (2 ≤ J ∧ 0 < θ J))
    (θ' : Offspring J') (hJN' : J' ≤ N')
    (hvalid' : θ'.IsSupercritical ∨ θ' 1 = 1)
    (htop' : θ' 1 = 1 ∨ (2 ≤ J' ∧ 0 < θ' J')) :
    ∀ᵐ omega ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      QuasiIsometric (wordGraphN (fun w => w ∈ sample omega.1))
          (wordGraphN (fun w => w ∈ sample omega.2)) ↔
        SameInfiniteClass θ θ' := by
  classical
  have hsource :=
    ChainClasses.offspring_classification_ae_iff θ hJN hvalid htop θ' hJN' hvalid' htop'
  unfold SameInfiniteClass
  unfold ChainClasses.GRegime.ofExact at hsource
  split_ifs at hsource <;>
    simp only [ChainClasses.GRegime.sampleLaw, ChainClasses.gRayLaw,
      ChainClasses.gFullLaw, ChainClasses.gChainLaw, ChainClasses.gBushyLaw,
      ChainClasses.gwLaw, ChainClasses.GSampleLaw.graph, ChainClasses.GPairQI] at hsource <;>
    convert hsource using 1 <;> rfl

/-- The conditioned statement transported to the unconditioned product law: on the
survival rectangle, quasi-isometry is the class condition. The top-support normalisation
is supplied by tightening. -/
theorem quasiIsometric_sample_ae_iff_of_valid {J J' N N' : ℕ}
    (θ : Offspring J) (hJN : J ≤ N) (hvalid : θ.IsSupercritical ∨ θ 1 = 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hvalid' : θ'.IsSupercritical ∨ θ' 1 = 1) :
    ∀ᵐ omega ∂((sampleMeasure (N := N) θ).prod (sampleMeasure (N := N') θ')),
      Survives omega.1 → Survives omega.2 →
        (QuasiIsometric (wordGraphN (fun w => w ∈ sample omega.1))
            (wordGraphN (fun w => w ∈ sample omega.2)) ↔
          SameInfiniteClass θ θ') := by
  have hvalid₀ : θ.trim.IsSupercritical ∨ θ.trim 1 = 1 := by
    rcases hvalid with h | h
    · left
      unfold Offspring.IsSupercritical at h ⊢
      rwa [Offspring.mean_trim]
    · exact Or.inr h
  have hvalid₀' : θ'.trim.IsSupercritical ∨ θ'.trim 1 = 1 := by
    rcases hvalid' with h | h
    · left
      unfold Offspring.IsSupercritical at h ⊢
      rwa [Offspring.mean_trim]
    · exact Or.inr h
  have htop₀ : θ.trim 1 = 1 ∨ (2 ≤ θ.top ∧ 0 < θ.trim θ.top) := by
    rcases hvalid with h | h
    · exact Or.inr ⟨θ.two_le_top_of_supercritical h, θ.top_pos⟩
    · exact Or.inl h
  have htop₀' : θ'.trim 1 = 1 ∨ (2 ≤ θ'.top ∧ 0 < θ'.trim θ'.top) := by
    rcases hvalid' with h | h
    · exact Or.inr ⟨θ'.two_le_top_of_supercritical h, θ'.top_pos⟩
    · exact Or.inl h
  have hcond := offspring_classification_survival_ae_iff θ.trim (θ.top_le.trans hJN)
    hvalid₀ htop₀ θ'.trim (θ'.top_le.trans hJN') hvalid₀' htop₀'
  rw [Offspring.survivalMeasure_trim, Offspring.survivalMeasure_trim] at hcond
  simp only [sameInfiniteClass_trim] at hcond
  -- The product of the conditional laws is a nonzero multiple of the product law restricted
  -- to the survival rectangle.
  have hS : MeasurableSet {c : BranchingProcess.Word N → ℕ | Survives c} :=
    measurableSet_survives
  have hS' : MeasurableSet {c : BranchingProcess.Word N' → ℕ | Survives c} :=
    measurableSet_survives
  have hprod : (survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ') =
      ((sampleMeasure (N := N) θ {c | Survives c})⁻¹ *
        (sampleMeasure (N := N') θ' {c | Survives c})⁻¹) •
        ((sampleMeasure (N := N) θ).prod (sampleMeasure (N := N') θ')).restrict
          ({c | Survives c} ×ˢ {c | Survives c}) := by
    unfold survivalMeasure ProbabilityTheory.cond
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict]
  have hne : (sampleMeasure (N := N) θ {c | Survives c})⁻¹ *
      (sampleMeasure (N := N') θ' {c | Survives c})⁻¹ ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
      (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
  rw [hprod, ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hcond
  rcases hcond with h0 | hcond
  · exact absurd h0 hne
  rw [← ae_iff, ae_restrict_iff' (hS.prod hS')] at hcond
  filter_upwards [hcond] with omega homega h1 h2
  exact homega ⟨h1, h2⟩

/-- Under a law of mean at most one, other than the deterministic single child, the first
coordinate of the product law is almost surely finite. -/
private lemma ae_not_survives_fst {J J' N N' : ℕ} (θ : Offspring J) (hJN : J ≤ N)
    (θ' : Offspring J') (hdead : θ.mean ≤ 1 ∧ θ 1 ≠ 1) :
    ∀ᵐ omega ∂((sampleMeasure (N := N) θ).prod (sampleMeasure (N := N') θ')),
      ¬ Survives omega.1 := by
  rw [ae_iff]
  simp only [not_not]
  have hset : {omega : (BranchingProcess.Word N → ℕ) × (BranchingProcess.Word N' → ℕ) |
      Survives omega.1} = {c | Survives c} ×ˢ Set.univ := by
    ext omega
    simp
  rw [hset, Measure.prod_prod, sampleMeasure_survives_eq_zero θ hJN hdead.1 hdead.2,
    zero_mul]

/-- The second-coordinate counterpart of `ae_not_survives_fst`. -/
private lemma ae_not_survives_snd {J J' N N' : ℕ} (θ : Offspring J) (θ' : Offspring J')
    (hJN' : J' ≤ N') (hdead : θ'.mean ≤ 1 ∧ θ' 1 ≠ 1) :
    ∀ᵐ omega ∂((sampleMeasure (N := N) θ).prod (sampleMeasure (N := N') θ')),
      ¬ Survives omega.2 := by
  rw [ae_iff]
  simp only [not_not]
  have hset : {omega : (BranchingProcess.Word N → ℕ) × (BranchingProcess.Word N' → ℕ) |
      Survives omega.2} = Set.univ ×ˢ {c | Survives c} := by
    ext omega
    simp
  rw [hset, Measure.prod_prod, sampleMeasure_survives_eq_zero θ' hJN' hdead.1 hdead.2,
    mul_zero]

/-- The pointwise dichotomy: given the class condition on the survival rectangle, a pair
of samples is quasi-isometric exactly when both are finite, or both are infinite and the
class condition holds. -/
private lemma quasiIsometric_sample_iff_of_imp {N N' : ℕ}
    {c : BranchingProcess.Word N → ℕ} {c' : BranchingProcess.Word N' → ℕ} {P : Prop}
    (h : Survives c → Survives c' →
      (QuasiIsometric (wordGraphN (fun w => w ∈ sample c))
        (wordGraphN (fun w => w ∈ sample c')) ↔ P)) :
    QuasiIsometric (wordGraphN (fun w => w ∈ sample c))
        (wordGraphN (fun w => w ∈ sample c')) ↔
      (¬ Survives c ∧ ¬ Survives c') ∨ (Survives c ∧ Survives c' ∧ P) := by
  by_cases hc : Survives c <;> by_cases hc' : Survives c'
  · rw [h hc hc']
    tauto
  · exact iff_of_false (not_quasiIsometric_sample_of_survives_left hc hc') (by tauto)
  · exact iff_of_false (not_quasiIsometric_sample_of_survives_right hc hc') (by tauto)
  · exact iff_of_true (quasiIsometric_sample_of_not_survives hc hc') (Or.inl ⟨hc, hc'⟩)

/-- **The complete classification** (`thm:trichotomy`). Two independent Galton--Watson
trees with finitely supported offspring laws are almost surely quasi-isometric exactly when
both are finite, or both are infinite and their laws lie in the same infinite class. -/
theorem full_classification_ae_iff {J J' N N' : ℕ}
    (θ : Offspring J) (hJN : J ≤ N) (θ' : Offspring J') (hJN' : J' ≤ N') :
    ∀ᵐ omega ∂((sampleMeasure (N := N) θ).prod (sampleMeasure (N := N') θ')),
      QuasiIsometric (wordGraphN (fun w => w ∈ sample omega.1))
          (wordGraphN (fun w => w ∈ sample omega.2)) ↔
        (¬ Survives omega.1 ∧ ¬ Survives omega.2) ∨
        (Survives omega.1 ∧ Survives omega.2 ∧ SameInfiniteClass θ θ') := by
  have hae : ∀ᵐ omega ∂((sampleMeasure (N := N) θ).prod (sampleMeasure (N := N') θ')),
      Survives omega.1 → Survives omega.2 →
        (QuasiIsometric (wordGraphN (fun w => w ∈ sample omega.1))
            (wordGraphN (fun w => w ∈ sample omega.2)) ↔
          SameInfiniteClass θ θ') := by
    by_cases hd : θ.mean ≤ 1 ∧ θ 1 ≠ 1
    · filter_upwards [ae_not_survives_fst θ hJN θ' hd] with omega h h1 _
      exact absurd h1 h
    by_cases hd' : θ'.mean ≤ 1 ∧ θ' 1 ≠ 1
    · filter_upwards [ae_not_survives_snd θ θ' hJN' hd'] with omega h _ h2
      exact absurd h2 h
    have hvalid : θ.IsSupercritical ∨ θ 1 = 1 := by
      rcases lt_or_ge 1 θ.mean with h | h
      · exact Or.inl h
      · exact Or.inr (not_not.1 fun h1 => hd ⟨h, h1⟩)
    have hvalid' : θ'.IsSupercritical ∨ θ' 1 = 1 := by
      rcases lt_or_ge 1 θ'.mean with h | h
      · exact Or.inl h
      · exact Or.inr (not_not.1 fun h1 => hd' ⟨h, h1⟩)
    exact quasiIsometric_sample_ae_iff_of_valid θ hJN hvalid θ' hJN' hvalid'
  filter_upwards [hae] with omega homega
  exact quasiIsometric_sample_iff_of_imp homega

/-- The root of a sample, as a vertex of its tree. -/
def sampleRoot {N : ℕ} (c : BranchingProcess.Word N → ℕ) : {w // w ∈ sample c} :=
  ⟨[], nil_mem_sample c⟩

/-- **The complete classification with root preservation** (`thm:trichotomy`). Almost surely,
a root-preserving quasi-isometry exists exactly when both trees are finite or both are infinite
with laws in the same class, and no quasi-isometry at all exists otherwise. -/
theorem full_classification_rooted_ae_iff {J J' N N' : ℕ}
    (θ : Offspring J) (hJN : J ≤ N) (θ' : Offspring J') (hJN' : J' ≤ N') :
    ∀ᵐ omega ∂((sampleMeasure (N := N) θ).prod (sampleMeasure (N := N') θ')),
      ((∃ (D : ℕ) (f : {w // w ∈ sample omega.1} → {w // w ∈ sample omega.2}),
          BranchingProcess.IsQIWith D (wordGraphN (fun w => w ∈ sample omega.1))
            (wordGraphN (fun w => w ∈ sample omega.2)) f ∧
          f (sampleRoot omega.1) = sampleRoot omega.2) ↔
        (¬ Survives omega.1 ∧ ¬ Survives omega.2) ∨
        (Survives omega.1 ∧ Survives omega.2 ∧ SameInfiniteClass θ θ')) ∧
      (QuasiIsometric (wordGraphN (fun w => w ∈ sample omega.1))
          (wordGraphN (fun w => w ∈ sample omega.2)) →
        (¬ Survives omega.1 ∧ ¬ Survives omega.2) ∨
        (Survives omega.1 ∧ Survives omega.2 ∧ SameInfiniteClass θ θ')) := by
  filter_upwards [full_classification_ae_iff θ hJN θ' hJN'] with omega h
  refine ⟨⟨fun ⟨D, f, hf, _⟩ => h.1 ⟨D, f, hf⟩, fun hP => ?_⟩, h.1⟩
  exact QuasiIsometric.exists_rooted
    (wordGraphN_connected (prefixClosedN_sample omega.2) ⟨sampleRoot omega.2⟩) (h.2 hP)
    (sampleRoot omega.1) (sampleRoot omega.2)

end ChainClasses
