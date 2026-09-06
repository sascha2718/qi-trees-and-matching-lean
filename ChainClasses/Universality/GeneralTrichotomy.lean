import ChainClasses.Universality.GeneralObstructions
import ChainClasses.Universality.FullTree
import ChainClasses.Universality.HairyGeneral
import ChainClasses.Engine.ChainEngineBridge
import ChainClasses.Universality.ChainGeneral
import ChainClasses.Bushy.Trichotomy

/-!
Core assembly for `thm:trichotomy` of `prelims.tex`, the complete quasi-isometry classification
for finitely supported offspring laws.  The hypothesis-free public result names are exported by
`ChainClasses.Classification.Complete`.

Everything is stated for the graph `wordGraphN (· ∈ sample c)` of the sample tree of an
offspring field `c : GWord N → ℕ` under the conditioned law `survivalMeasure θ`, the
setting of `GeneralObstructions.lean`. The four coarse regimes are hypotheses on the law,
and the chain regime splits into one class for each branching semigroup:

* (R) `θ₁ = 1`: the sample is almost surely the ray;
* (F) `θ₀ = θ₁ = 0`: the sample is almost surely quasi-isometric to the binary tree;
* (C) `θ₀ = 0 < θ₁ < 1`: the chain regime, classified by the branching semigroup
  `Λ_θ = ⟨k - 1 : θ_k > 0⟩`;
* (B) `θ₀ > 0`: the bushy regime.

The law of a pair is the product of the two conditioned laws, so the regimes sit on one
probabilistic footing.  Two statements of the chain regime enter as named hypotheses,
the universality `thm:chain-general` and the separation `thm:chain-separation`;
`chainUniversality` below discharges the first, while `ChainSeparationProof.lean` discharges the
second.  `Classification/Complete.lean` exports the hypothesis-free classification through
`same_class_ae`, `different_class_ae`, and `classification_ae_iff`.

* `RayN`, `prefixClosedN_rayN`, `treeDist_rayN`, `quasiIsometric_rayN_rayGraph`: the ray
  as a set of words over `Fin N`, isometric to `rayGraph`.
* `ae_forall_eq_one`, `mem_sample_iff_rayN`, `ray_gSample`: **regime (R)**, the sample of
  a law with `θ₁ = 1` is almost surely the ray.
* `skeletonWeight_one_lt_one_of_full`, `skeletonWeight_one_lt_one_of_chain`: the neck
  weight is below one in regimes (F) and (C).
* `GSampleLaw`, `gwLaw`, `gRayLaw`, `gFullLaw`, `gChainLaw`, `gBushyLaw`, `GPairQI`:
  **the four coarse regimes as laws of a random tree**.
* `ae_not_gPairQI_symm`: almost sure failure of quasi-isometry of a pair, read
  backwards.
* `ChainUniversality`, `ChainSeparation`: **`thm:chain-general` and
  `thm:chain-separation` as hypotheses**, over all chain-regime laws over all alphabets.
* `gRay_gRay_ae`, `gFull_gFull_ae`, `gChain_gChain_ae`, `gBushy_gBushy_ae`: **the four
  positive statements**, and `gRay_gFull_ae`, `gRay_gChain_ae`, `gRay_gBushy_ae`,
  `gBushy_gFull_ae`, `gBushy_gChain_ae`, `gChain_gFull_ae`, `gChain_gChain_sep_ae` with
  their reversals the separations.
* `not_ray_gFull`, `not_ray_gChain`, `not_ray_gBushy`: the ray against the other three
  regimes, one sample at a time.
* `GRegime`, `GRegime.sampleLaw`, `GRegime.kind`, `GRegime.IsChain`, `GRegime.semigroup`,
  `same_gRegime_ae`, `diff_gRegime_ae`, `not_ray_gRegime_ae`, `not_ae_of_ae_not`,
  `trichotomy_general`: the infinite classes of **`thm:trichotomy`**, encoded by the coarse
  regime and the branching semigroup.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (Offspring QuasiIsometric rayGraph sample survivalMeasure Survives)

variable {J N : ℕ}

/-! ### The ray as a set of words -/

/-- The ray as a set of words over `Fin N`: the words all of whose letters are `0`. -/
def RayN (N : ℕ) (w : GWord N) : Prop := ∀ j ∈ w, (j : ℕ) = 0

lemma prefixClosedN_rayN : PrefixClosedN (RayN N) :=
  fun _ _ huv hv j hj ↦ hv j (huv.subset hj)

lemma rayN_nil : RayN N [] := fun _ hj ↦ absurd hj List.not_mem_nil

/-- Two words of the ray are comparable: the shorter is a prefix of the longer. -/
lemma rayN_prefix_of_length_le {u v : GWord N} (hu : RayN N u) (hv : RayN N v)
    (h : u.length ≤ v.length) : u <+: v := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_take]
    exact Fin.ext ((hu _ (List.getElem_mem _)).trans (hv _ (List.getElem_mem _)).symm)

/-- Along the ray the tree metric is the distance of the depths. -/
lemma treeDist_rayN {u v : GWord N} (hu : RayN N u) (hv : RayN N v) :
    BranchingProcess.treeDist u v = Nat.dist u.length v.length := by
  rcases le_total u.length v.length with h | h
  · rw [BranchingProcess.treeDist_of_prefix (rayN_prefix_of_length_le hu hv h),
      Nat.dist_eq_sub_of_le h]
  · rw [BranchingProcess.treeDist_comm,
      BranchingProcess.treeDist_of_prefix (rayN_prefix_of_length_le hv hu h),
      Nat.dist_eq_sub_of_le_right h]

/-- **The ray as a set of words is quasi-isometric to `rayGraph`**: the depth is an
isometry. -/
theorem quasiIsometric_rayN_rayGraph (hN : 0 < N) :
    QuasiIsometric (wordGraphN (RayN N)) rayGraph := by
  refine ⟨1, fun w ↦ w.1.length, fun x y ↦ ?_, fun x y ↦ ?_, fun n ↦ ?_⟩
  · rw [BranchingProcess.rayGraph_dist, wordGraphN_dist prefixClosedN_rayN,
      treeDist_rayN x.2 y.2]
    omega
  · rw [BranchingProcess.rayGraph_dist, wordGraphN_dist prefixClosedN_rayN,
      treeDist_rayN x.2 y.2]
    omega
  · refine ⟨⟨List.replicate n ⟨0, hN⟩, fun j hj ↦ ?_⟩, ?_⟩
    · rw [List.eq_of_mem_replicate hj]
    · simp

/-! ### Regime (R): the sample is the ray -/

section Ray

variable (θ : Offspring J)

/-- A law with `θ₁ = 1` has no mass at zero. -/
lemma zero_of_one (h1 : θ 1 = 1) : θ 0 = 0 := by
  have htot := θ.total
  have hJ : 1 ≤ J := by
    by_contra hJ
    rw [θ.vanishing 1 (by omega)] at h1
    exact zero_ne_one h1
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (J + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ ↦ θ.nonneg j)
  rw [Finset.sum_pair (by omega : (0 : ℕ) ≠ 1), htot, h1] at hle
  have := θ.nonneg 0
  linarith

/-- The alphabet is nonempty once the law has all its mass at one. -/
lemma pos_of_one (hJN : J ≤ N) (h1 : θ 1 = 1) : 0 < N :=
  pos_of_zero θ hJN (zero_of_one θ h1)

/-- At `θ₁ = 1` every vertex has exactly one child, almost surely. -/
lemma ae_forall_eq_one (h1 : θ 1 = 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v : GWord N, c v = 1 := by
  refine ae_all_iff.mpr fun v ↦ ?_
  rw [ae_iff]
  have hs : BranchingProcess.sampleMeasure (N := N) θ {c : GWord N → ℕ | ¬ c v = 1} = 0 := by
    have he : {c : GWord N → ℕ | ¬ c v = 1} = {c : GWord N → ℕ | c v = 1}ᶜ := rfl
    rw [he, prob_compl_eq_one_sub (measurableSet_eq_fun (measurable_pi_apply v)
      measurable_const), BranchingProcess.sampleMeasure_coord θ v 1, h1, ENNReal.ofReal_one,
      tsub_self]
  rw [BranchingProcess.survivalMeasure_apply]
  exact mul_eq_zero.mpr (Or.inr (measure_mono_null Set.inter_subset_right hs))

/-- The sample of a field with one child everywhere is the ray. -/
lemma mem_sample_iff_rayN {c : GWord N → ℕ} (hc : ∀ v, c v = 1) (w : GWord N) :
    w ∈ sample c ↔ RayN N w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨fun _ ↦ rayN_nil, fun _ ↦ BranchingProcess.nil_mem_sample c⟩
  | append_singleton u j ih =>
      rw [BranchingProcess.mem_sample_append_singleton, ih, hc]
      constructor
      · rintro ⟨hu, hj⟩ x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hu x hx
        · rw [List.mem_singleton.mp hx]
          omega
      · intro h
        exact ⟨fun x hx ↦ h x (List.mem_append_left _ hx),
          by have := h j (List.mem_append_right _ (List.mem_singleton_self j)); omega⟩

/-- **Regime (R)**: at `θ₁ = 1` the sample tree is almost surely the ray, so it is
almost surely quasi-isometric to `rayGraph`. -/
theorem ray_gSample (hJN : J ≤ N) (h1 : θ 1 = 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ,
      QuasiIsometric (wordGraphN (fun w : GWord N ↦ w ∈ sample c)) rayGraph := by
  filter_upwards [ae_forall_eq_one θ h1] with c hc
  have heq : (fun w : GWord N ↦ w ∈ sample c) = RayN N :=
    funext fun w ↦ propext (mem_sample_iff_rayN hc w)
  rw [heq]
  exact quasiIsometric_rayN_rayGraph (pos_of_one θ hJN h1)

end Ray

/-! ### The neck weight in the regimes without leaves -/

section Weights

variable (θ : Offspring J)

/-- In regime (F) the neck weight vanishes. -/
lemma skeletonWeight_one_lt_one_of_full (h0 : θ 0 = 0) (h1 : θ 1 = 0) :
    θ.skeletonWeight 1 < 1 := by
  rw [skeletonWeight_one_eq_of_chain θ h0, h1]
  exact zero_lt_one

/-- In regime (C) the neck weight is `θ₁ < 1`. -/
lemma skeletonWeight_one_lt_one_of_chain (h0 : θ 0 = 0) (h1 : θ 1 < 1) :
    θ.skeletonWeight 1 < 1 := by
  rw [skeletonWeight_one_eq_of_chain θ h0]
  exact h1

end Weights

/-! ### The four regimes as laws of a random tree -/

/-- **A law of a random tree over an alphabet**: a probability space carrying a
prefix-closed set of words over `Fin N`, the vertex set of the sample. -/
structure GSampleLaw : Type 1 where
  /-- The alphabet. -/
  N : ℕ
  /-- The sample space. -/
  Ω : Type
  /-- Its measurable structure. -/
  meas : MeasurableSpace Ω
  /-- The law of the sample. -/
  law : Measure Ω
  /-- The law is a probability measure. -/
  isProb : IsProbabilityMeasure law
  /-- The sample tree, as a set of words over `Fin N`. -/
  tree : Ω → GWord N → Prop
  /-- The sample tree is prefix-closed. -/
  prefixClosed : ∀ ω, PrefixClosedN (tree ω)
  /-- The sample tree contains the root. -/
  root : ∀ ω, tree ω []

attribute [instance] GSampleLaw.meas GSampleLaw.isProb

/-- The graph of the sample. -/
abbrev GSampleLaw.graph (L : GSampleLaw) (ω : L.Ω) : SimpleGraph {w : GWord L.N // L.tree ω w} :=
  wordGraphN (L.tree ω)

lemma GSampleLaw.connected (L : GSampleLaw) (ω : L.Ω) : (L.graph ω).Connected :=
  wordGraphN_connected (L.prefixClosed ω) ⟨⟨[], L.root ω⟩⟩

/-- **The conditioned Galton-Watson law** of an offspring law over the alphabet `Fin N`,
as a law of a random tree: the sample of the field under `survivalMeasure θ`. -/
noncomputable def gwLaw (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1) :
    GSampleLaw where
  N := N
  Ω := GWord N → ℕ
  meas := inferInstance
  law := survivalMeasure (N := N) θ
  isProb := BranchingProcess.isProbabilityMeasure_survivalMeasure θ hJN hq
  tree := fun c w ↦ w ∈ sample c
  prefixClosed := prefixClosedN_sample
  root := BranchingProcess.nil_mem_sample

/-- **Regime (R)**: `θ₁ = 1`. -/
noncomputable def gRayLaw (θ : Offspring J) (hJN : J ≤ N) (h1 : θ 1 = 1) : GSampleLaw :=
  gwLaw θ hJN (extinction_lt_one_of_chain θ (zero_of_one θ h1))

/-- **Regime (F)**: `θ₀ = θ₁ = 0`. -/
noncomputable def gFullLaw (θ : Offspring J) (hJN : J ≤ N) (h0 : θ 0 = 0) : GSampleLaw :=
  gwLaw θ hJN (extinction_lt_one_of_chain θ h0)

/-- **Regime (C)**: `θ₀ = 0 < θ₁ < 1`. -/
noncomputable def gChainLaw (θ : Offspring J) (hJN : J ≤ N) (h0 : θ 0 = 0) : GSampleLaw :=
  gwLaw θ hJN (extinction_lt_one_of_chain θ h0)

/-- **Regime (B)**: `θ₀ > 0`, supercritical. -/
noncomputable def gBushyLaw (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1) :
    GSampleLaw :=
  gwLaw θ hJN hq

/-- Quasi-isometry of the two sample trees of a pair of laws. -/
def GPairQI (L L' : GSampleLaw) (ω : L.Ω × L'.Ω) : Prop :=
  QuasiIsometric (L.graph ω.1) (L'.graph ω.2)

/-- Quasi-isometry of a pair read backwards. -/
lemma GPairQI.symm {L L' : GSampleLaw} {ω : L.Ω × L'.Ω} (h : GPairQI L L' ω) :
    GPairQI L' L ω.swap :=
  QuasiIsometric.symm (L'.connected _) h

/-- Almost sure failure of quasi-isometry of a pair of laws is symmetric. -/
lemma ae_not_gPairQI_symm {L L' : GSampleLaw}
    (h : ∀ᵐ ω ∂(L'.law.prod L.law), ¬ GPairQI L' L ω) :
    ∀ᵐ ω ∂(L.law.prod L'.law), ¬ GPairQI L L' ω := by
  refine ae_prod_swap ?_
  filter_upwards [h] with ω hω hqi
  exact hω hqi.symm

/-! ### The two hypotheses of the chain regime -/

/-- **`thm:chain-general` as a hypothesis**: two chain-regime laws with the same branching
semigroup give almost surely quasi-isometric samples. -/
def ChainUniversality : Prop :=
  ∀ {J J' N N' : ℕ} (θ : Offspring J) (_hJN : J ≤ N) (_hθ0 : θ 0 = 0) (_hθ1 : 0 < θ 1)
    (_hθ1' : θ 1 < 1) (_hJ2 : 2 ≤ J) (_hθJ : 0 < θ J)
    (θ' : Offspring J') (_hJN' : J' ≤ N') (_hθ0' : θ' 0 = 0) (_hθ1'₀ : 0 < θ' 1)
    (_hθ1'' : θ' 1 < 1) (_hJ2' : 2 ≤ J') (_hθJ' : 0 < θ' J')
    (_hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      = AddSubmonoid.closure (shiftSupp θ' : Set ℕ)),
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      QuasiIsometric (wordGraphN (· ∈ sample cc.1)) (wordGraphN (· ∈ sample cc.2))

/-- **`thm:chain-separation` as a hypothesis**: two chain-regime laws with different
branching semigroups give almost surely non-quasi-isometric samples. -/
def ChainSeparation : Prop :=
  ∀ {J J' N N' : ℕ} (θ : Offspring J) (_hJN : J ≤ N) (_hθ0 : θ 0 = 0) (_hθ1 : 0 < θ 1)
    (_hθ1' : θ 1 < 1) (_hJ2 : 2 ≤ J) (_hθJ : 0 < θ J)
    (θ' : Offspring J') (_hJN' : J' ≤ N') (_hθ0' : θ' 0 = 0) (_hθ1'₀ : 0 < θ' 1)
    (_hθ1'' : θ' 1 < 1) (_hJ2' : 2 ≤ J') (_hθJ' : 0 < θ' J')
    (_hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      ≠ AddSubmonoid.closure (shiftSupp θ' : Set ℕ)),
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      ¬ QuasiIsometric (wordGraphN (· ∈ sample cc.1)) (wordGraphN (· ∈ sample cc.2))

/-! ### The four positive statements -/

section Positive

variable {J' N' : ℕ} (θ : Offspring J) (θ' : Offspring J')

/-- **Universality in regime (R)**: both samples are the ray. -/
theorem gRay_gRay_ae (hJN : J ≤ N) (h1 : θ 1 = 1) (hJN' : J' ≤ N') (h1' : θ' 1 = 1) :
    ∀ᵐ ω ∂((gRayLaw θ hJN h1).law.prod (gRayLaw θ' hJN' h1').law),
      GPairQI (gRayLaw θ hJN h1) (gRayLaw θ' hJN' h1') ω := by
  filter_upwards [ae_of_fst (ν := (gRayLaw θ' hJN' h1').law) (ray_gSample θ hJN h1),
    ae_of_snd (μ := (gRayLaw θ hJN h1).law) (ray_gSample θ' hJN' h1')] with ω hr hr'
  exact QuasiIsometric.trans ((gRayLaw θ' hJN' h1').connected ω.2) hr
    (QuasiIsometric.symm BranchingProcess.rayGraph_connected hr')

/-- **Universality in regime (F)**, `thm:bushy`: both samples are quasi-isometric to the
binary tree. -/
theorem gFull_gFull_ae (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : θ 1 = 0) (hJN' : J' ≤ N')
    (h0' : θ' 0 = 0) (h1' : θ' 1 = 0) :
    ∀ᵐ ω ∂((gFullLaw θ hJN h0).law.prod (gFullLaw θ' hJN' h0').law),
      GPairQI (gFullLaw θ hJN h0) (gFullLaw θ' hJN' h0') ω := by
  filter_upwards [ae_of_fst (ν := (gFullLaw θ' hJN' h0').law) (fullTree_gSample θ hJN h0 h1),
    ae_of_snd (μ := (gFullLaw θ hJN h0).law) (fullTree_gSample θ' hJN' h0' h1')] with ω hf hf'
  exact QuasiIsometric.trans ((gFullLaw θ' hJN' h0').connected ω.2) hf
    (QuasiIsometric.symm (wordGraph_connected prefixClosed_true ⟨⟨[], trivial⟩⟩) hf')

/-- **Universality in regime (C)**, `thm:chain-general`, under the hypothesis
`ChainUniversality`. -/
theorem gChain_gChain_ae (hUniv : ChainUniversality) (hJN : J ≤ N) (h0 : θ 0 = 0)
    (h1 : 0 < θ 1) (h1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (hJN' : J' ≤ N') (h0' : θ' 0 = 0) (h1'₀ : 0 < θ' 1) (h1'' : θ' 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      = AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) :
    ∀ᵐ ω ∂((gChainLaw θ hJN h0).law.prod (gChainLaw θ' hJN' h0').law),
      GPairQI (gChainLaw θ hJN h0) (gChainLaw θ' hJN' h0') ω :=
  hUniv θ hJN h0 h1 h1' hJ2 hθJ θ' hJN' h0' h1'₀ h1'' hJ2' hθJ' hsem

/-- **Universality in regime (B)**, `thm:hairy-general`. -/
theorem gBushy_gBushy_ae (hJN : J ≤ N) (hq : θ.extinction < 1) (h0 : 0 < θ 0)
    (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (h0' : 0 < θ' 0) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J') :
    ∀ᵐ ω ∂((gBushyLaw θ hJN hq).law.prod (gBushyLaw θ' hJN' hq').law),
      GPairQI (gBushyLaw θ hJN hq) (gBushyLaw θ' hJN' hq') ω :=
  hairy_general_ae θ hJN hq (θ.extinction_pos h0) h0 hθJ hJ2 θ' hJN' hq'
    (θ'.extinction_pos h0') h0' hθJ' hJ2'

end Positive

/-! ### The separations -/

section Separations

variable {J' N' : ℕ} (θ : Offspring J) (θ' : Offspring J')

/-- **The ray against three rays**, `thm:three-rays`: a sample quasi-isometric to the ray
is not quasi-isometric to a sample carrying three rays out of one vertex. -/
lemma not_gPairQI_of_ray_of_threeRays {L L' : GSampleLaw} {ω : L.Ω × L'.Ω}
    (hr : QuasiIsometric (L.graph ω.1) rayGraph) (h3 : HasThreeRaysN (L'.tree ω.2)) :
    ¬ GPairQI L L' ω := fun hqi ↦
  not_quasiIsometric_rayGraph_of_threeRaysN (L'.prefixClosed ω.2) h3
    (QuasiIsometric.trans BranchingProcess.rayGraph_connected
      (QuasiIsometric.symm (L'.connected ω.2) hqi) hr)

/-- **Regime (R) against regime (F)**. -/
theorem gRay_gFull_ae (hJN : J ≤ N) (h1 : θ 1 = 1) (hJN' : J' ≤ N') (h0' : θ' 0 = 0)
    (h1' : θ' 1 = 0) :
    ∀ᵐ ω ∂((gRayLaw θ hJN h1).law.prod (gFullLaw θ' hJN' h0').law),
      ¬ GPairQI (gRayLaw θ hJN h1) (gFullLaw θ' hJN' h0') ω := by
  filter_upwards [ae_of_fst (ν := (gFullLaw θ' hJN' h0').law) (ray_gSample θ hJN h1),
    ae_of_snd (μ := (gRayLaw θ hJN h1).law) (threeRays_ae θ' hJN'
      (extinction_lt_one_of_chain θ' h0') (skeletonWeight_one_lt_one_of_full θ' h0' h1'))]
    with ω hr h3
  exact not_gPairQI_of_ray_of_threeRays hr h3

/-- **Regime (R) against regime (C)**. -/
theorem gRay_gChain_ae (hJN : J ≤ N) (h1 : θ 1 = 1) (hJN' : J' ≤ N') (h0' : θ' 0 = 0)
    (h1' : θ' 1 < 1) :
    ∀ᵐ ω ∂((gRayLaw θ hJN h1).law.prod (gChainLaw θ' hJN' h0').law),
      ¬ GPairQI (gRayLaw θ hJN h1) (gChainLaw θ' hJN' h0') ω := by
  filter_upwards [ae_of_fst (ν := (gChainLaw θ' hJN' h0').law) (ray_gSample θ hJN h1),
    ae_of_snd (μ := (gRayLaw θ hJN h1).law) (threeRays_ae θ' hJN'
      (extinction_lt_one_of_chain θ' h0') (skeletonWeight_one_lt_one_of_chain θ' h0' h1'))]
    with ω hr h3
  exact not_gPairQI_of_ray_of_threeRays hr h3

/-- **Regime (R) against regime (B)**. -/
theorem gRay_gBushy_ae (hJN : J ≤ N) (h1 : θ 1 = 1) (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J') :
    ∀ᵐ ω ∂((gRayLaw θ hJN h1).law.prod (gBushyLaw θ' hJN' hq').law),
      ¬ GPairQI (gRayLaw θ hJN h1) (gBushyLaw θ' hJN' hq') ω := by
  filter_upwards [ae_of_fst (ν := (gBushyLaw θ' hJN' hq').law) (ray_gSample θ hJN h1),
    ae_of_snd (μ := (gRayLaw θ hJN h1).law) (threeRays_ae_of_top θ' hJN' hq' hJ2' hθJ')]
    with ω hr h3
  exact not_gPairQI_of_ray_of_threeRays hr h3

/-- **Hairs against lines**, `thm:hair-separation`, on a pair of laws. -/
lemma not_gPairQI_of_hairs_of_nearLine {L L' : GSampleLaw} {ω : L.Ω × L'.Ω}
    (hh : UnboundedHairsN (L.tree ω.1)) (hl : NearLineN (L'.tree ω.2)) :
    ¬ GPairQI L L' ω :=
  not_quasiIsometric_of_hairsN_of_nearLineN (L.prefixClosed ω.1) (L'.prefixClosed ω.2)
    (L.root ω.1) (L'.root ω.2) hh hl

/-- **Regime (B) against regime (F)**: hairs of unbounded depth against a tree near a
line. -/
theorem gBushy_gFull_ae (hJN : J ≤ N) (hq : θ.extinction < 1) (h0 : 0 < θ 0) (hJ2 : 2 ≤ J)
    (hθJ : 0 < θ J) (hJN' : J' ≤ N') (h0' : θ' 0 = 0) (h1' : θ' 1 = 0) :
    ∀ᵐ ω ∂((gBushyLaw θ hJN hq).law.prod (gFullLaw θ' hJN' h0').law),
      ¬ GPairQI (gBushyLaw θ hJN hq) (gFullLaw θ' hJN' h0') ω := by
  filter_upwards [ae_of_fst (ν := (gFullLaw θ' hJN' h0').law)
      (unbounded_hairs_gSample_ae θ hJN hq (θ.extinction_pos h0) hJ2 hθJ),
    ae_of_snd (μ := (gBushyLaw θ hJN hq).law) (nearLine_gSample_ae θ' hJN'
      (extinction_lt_one_of_chain θ' h0') h0' (skeletonWeight_one_lt_one_of_full θ' h0' h1'))]
    with ω hh hl
  exact not_gPairQI_of_hairs_of_nearLine hh hl

/-- **Regime (B) against regime (C)**. -/
theorem gBushy_gChain_ae (hJN : J ≤ N) (hq : θ.extinction < 1) (h0 : 0 < θ 0) (hJ2 : 2 ≤ J)
    (hθJ : 0 < θ J) (hJN' : J' ≤ N') (h0' : θ' 0 = 0) (h1' : θ' 1 < 1) :
    ∀ᵐ ω ∂((gBushyLaw θ hJN hq).law.prod (gChainLaw θ' hJN' h0').law),
      ¬ GPairQI (gBushyLaw θ hJN hq) (gChainLaw θ' hJN' h0') ω := by
  filter_upwards [ae_of_fst (ν := (gChainLaw θ' hJN' h0').law)
      (unbounded_hairs_gSample_ae θ hJN hq (θ.extinction_pos h0) hJ2 hθJ),
    ae_of_snd (μ := (gBushyLaw θ hJN hq).law) (nearLine_gSample_ae θ' hJN'
      (extinction_lt_one_of_chain θ' h0') h0' (skeletonWeight_one_lt_one_of_chain θ' h0' h1'))]
    with ω hh hl
  exact not_gPairQI_of_hairs_of_nearLine hh hl

/-- **Regime (C) against regime (F)**, `thm:bottleneck`: thin balls against a tree
quasi-isometric to the binary tree. -/
theorem gChain_gFull_ae (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : 0 < θ 1) (hJN' : J' ≤ N')
    (h0' : θ' 0 = 0) (h1' : θ' 1 = 0) :
    ∀ᵐ ω ∂((gChainLaw θ hJN h0).law.prod (gFullLaw θ' hJN' h0').law),
      ¬ GPairQI (gChainLaw θ hJN h0) (gFullLaw θ' hJN' h0') ω := by
  filter_upwards [ae_of_fst (ν := (gFullLaw θ' hJN' h0').law)
      (thinBalls_gSample_ae θ hJN (extinction_lt_one_of_chain θ h0) h0 h1),
    ae_of_snd (μ := (gChainLaw θ hJN h0).law) (fullTree_gSample θ' hJN' h0' h1')]
    with ω ht hf
  exact not_quasiIsometric_of_thinBallsN_of_binary (prefixClosedN_sample _) ht hf

/-- **Regime (C) against itself across semigroups**, `thm:chain-separation`, under the
hypothesis `ChainSeparation`. -/
theorem gChain_gChain_sep_ae (hSep : ChainSeparation) (hJN : J ≤ N) (h0 : θ 0 = 0)
    (h1 : 0 < θ 1) (h1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (hJN' : J' ≤ N') (h0' : θ' 0 = 0) (h1'₀ : 0 < θ' 1) (h1'' : θ' 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      ≠ AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) :
    ∀ᵐ ω ∂((gChainLaw θ hJN h0).law.prod (gChainLaw θ' hJN' h0').law),
      ¬ GPairQI (gChainLaw θ hJN h0) (gChainLaw θ' hJN' h0') ω :=
  hSep θ hJN h0 h1 h1' hJ2 hθJ θ' hJN' h0' h1'₀ h1'' hJ2' hθJ' hsem

end Separations

/-! ### The ray against the other three regimes -/

section Ray

variable (θ : Offspring J)

/-- **The ray against regime (F)**: a full sample carries three rays. -/
theorem not_ray_gFull (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : θ 1 = 0) :
    ∀ᵐ ω ∂(gFullLaw θ hJN h0).law, ¬ QuasiIsometric ((gFullLaw θ hJN h0).graph ω) rayGraph := by
  filter_upwards [threeRays_ae θ hJN (extinction_lt_one_of_chain θ h0)
    (skeletonWeight_one_lt_one_of_full θ h0 h1)] with c h3
  exact not_quasiIsometric_rayGraph_of_threeRaysN (prefixClosedN_sample c) h3

/-- **The ray against regime (C)**. -/
theorem not_ray_gChain (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : θ 1 < 1) :
    ∀ᵐ ω ∂(gChainLaw θ hJN h0).law,
      ¬ QuasiIsometric ((gChainLaw θ hJN h0).graph ω) rayGraph := by
  filter_upwards [threeRays_ae θ hJN (extinction_lt_one_of_chain θ h0)
    (skeletonWeight_one_lt_one_of_chain θ h0 h1)] with c h3
  exact not_quasiIsometric_rayGraph_of_threeRaysN (prefixClosedN_sample c) h3

/-- **The ray against regime (B)**. -/
theorem not_ray_gBushy (hJN : J ≤ N) (hq : θ.extinction < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) :
    ∀ᵐ ω ∂(gBushyLaw θ hJN hq).law,
      ¬ QuasiIsometric ((gBushyLaw θ hJN hq).graph ω) rayGraph := by
  filter_upwards [threeRays_ae_of_top θ hJN hq hJ2 hθJ] with c h3
  exact not_quasiIsometric_rayGraph_of_threeRaysN (prefixClosedN_sample c) h3

end Ray

/-! ### The classification -/

/-- **The four coarse regimes underlying `thm:trichotomy`**, each carrying its offspring law,
an alphabet containing its support, and the inequalities defining the regime. -/
inductive GRegime : Type
  /-- (R) `θ₁ = 1`. -/
  | ray {J N : ℕ} (θ : Offspring J) (hJN : J ≤ N) (h1 : θ 1 = 1) : GRegime
  /-- (F) `θ₀ = θ₁ = 0`. -/
  | full {J N : ℕ} (θ : Offspring J) (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : θ 1 = 0) : GRegime
  /-- (C) `θ₀ = 0 < θ₁ < 1`, with `θ_J > 0` for the bound `J ≥ 2`. -/
  | chain {J N : ℕ} (θ : Offspring J) (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : 0 < θ 1)
      (h1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) : GRegime
  /-- (B) `θ₀ > 0`, supercritical, with `θ_J > 0` for the bound `J ≥ 2`. -/
  | bushy {J N : ℕ} (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1) (h0 : 0 < θ 0)
      (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) : GRegime

/-- The law of the sample in a regime. -/
noncomputable def GRegime.sampleLaw : GRegime → GSampleLaw
  | .ray θ hJN h1 => gRayLaw θ hJN h1
  | .full θ hJN h0 _ => gFullLaw θ hJN h0
  | .chain θ hJN h0 _ _ _ _ => gChainLaw θ hJN h0
  | .bushy θ hJN hq _ _ _ => gBushyLaw θ hJN hq

/-- The name of the regime, the first invariant of the classification. -/
def GRegime.kind : GRegime → ℕ
  | .ray .. => 0
  | .full .. => 1
  | .chain .. => 2
  | .bushy .. => 3

/-- The chain regime. -/
def GRegime.IsChain : GRegime → Prop
  | .chain .. => True
  | _ => False

/-- The branching semigroup `Λ_θ` of `eq:branching-semigroup`, the second invariant of the
classification, carried by the chain regime; the whole of `ℕ` elsewhere. -/
noncomputable def GRegime.semigroup : GRegime → AddSubmonoid ℕ
  | .chain θ .. => AddSubmonoid.closure (shiftSupp θ : Set ℕ)
  | _ => ⊤

/-- **The same-class clause of `thm:trichotomy`**: two laws in the same coarse regime, with
equal branching semigroups in the chain regime, give almost surely quasi-isometric samples. -/
theorem same_gRegime_ae (hUniv : ChainUniversality) (R R' : GRegime) (hk : R.kind = R'.kind)
    (hsem : R.IsChain → R'.IsChain → R.semigroup = R'.semigroup) :
    ∀ᵐ ω ∂(R.sampleLaw.law.prod R'.sampleLaw.law), GPairQI R.sampleLaw R'.sampleLaw ω := by
  cases R with
  | ray θ hJN h1 =>
      cases R' with
      | ray θ' hJN' h1' => exact gRay_gRay_ae θ θ' hJN h1 hJN' h1'
      | full => simp [GRegime.kind] at hk
      | chain => simp [GRegime.kind] at hk
      | bushy => simp [GRegime.kind] at hk
  | full θ hJN h0 h1 =>
      cases R' with
      | ray => simp [GRegime.kind] at hk
      | full θ' hJN' h0' h1' => exact gFull_gFull_ae θ θ' hJN h0 h1 hJN' h0' h1'
      | chain => simp [GRegime.kind] at hk
      | bushy => simp [GRegime.kind] at hk
  | chain θ hJN h0 h1 h1' hJ2 hθJ =>
      cases R' with
      | ray => simp [GRegime.kind] at hk
      | full => simp [GRegime.kind] at hk
      | chain θ' hJN' h0' h1'₀ h1'' hJ2' hθJ' =>
          exact gChain_gChain_ae θ θ' hUniv hJN h0 h1 h1' hJ2 hθJ hJN' h0' h1'₀ h1'' hJ2' hθJ'
            (hsem trivial trivial)
      | bushy => simp [GRegime.kind] at hk
  | bushy θ hJN hq h0 hJ2 hθJ =>
      cases R' with
      | ray => simp [GRegime.kind] at hk
      | full => simp [GRegime.kind] at hk
      | chain => simp [GRegime.kind] at hk
      | bushy θ' hJN' hq' h0' hJ2' hθJ' =>
          exact gBushy_gBushy_ae θ θ' hJN hq h0 hJ2 hθJ hJN' hq' h0' hJ2' hθJ'

/-- **The different-class clause of `thm:trichotomy`**: two laws in different coarse regimes,
or in the chain regime with different branching semigroups, give samples that are almost surely
not quasi-isometric. -/
theorem diff_gRegime_ae (hSep : ChainSeparation) (R R' : GRegime)
    (h : R.kind ≠ R'.kind ∨ (R.IsChain ∧ R'.IsChain ∧ R.semigroup ≠ R'.semigroup)) :
    ∀ᵐ ω ∂(R.sampleLaw.law.prod R'.sampleLaw.law), ¬ GPairQI R.sampleLaw R'.sampleLaw ω := by
  cases R with
  | ray θ hJN h1 =>
      cases R' with
      | ray => simp [GRegime.kind, GRegime.IsChain] at h
      | full θ' hJN' h0' h1' => exact gRay_gFull_ae θ θ' hJN h1 hJN' h0' h1'
      | chain θ' hJN' h0' _ h1'' _ _ => exact gRay_gChain_ae θ θ' hJN h1 hJN' h0' h1''
      | bushy θ' hJN' hq' _ hJ2' hθJ' => exact gRay_gBushy_ae θ θ' hJN h1 hJN' hq' hJ2' hθJ'
  | full θ hJN h0 h1 =>
      cases R' with
      | ray θ' hJN' h1' => exact ae_not_gPairQI_symm (gRay_gFull_ae θ' θ hJN' h1' hJN h0 h1)
      | full => simp [GRegime.kind, GRegime.IsChain] at h
      | chain θ' hJN' h0' h1'₀ _ _ _ =>
          exact ae_not_gPairQI_symm (gChain_gFull_ae θ' θ hJN' h0' h1'₀ hJN h0 h1)
      | bushy θ' hJN' hq' h0' hJ2' hθJ' =>
          exact ae_not_gPairQI_symm (gBushy_gFull_ae θ' θ hJN' hq' h0' hJ2' hθJ' hJN h0 h1)
  | chain θ hJN h0 h1 h1' hJ2 hθJ =>
      cases R' with
      | ray θ' hJN' h1'' => exact ae_not_gPairQI_symm (gRay_gChain_ae θ' θ hJN' h1'' hJN h0 h1')
      | full θ' hJN' h0' h1'' => exact gChain_gFull_ae θ θ' hJN h0 h1 hJN' h0' h1''
      | chain θ' hJN' h0' h1'₀ h1'' hJ2' hθJ' =>
          refine gChain_gChain_sep_ae θ θ' hSep hJN h0 h1 h1' hJ2 hθJ hJN' h0' h1'₀ h1'' hJ2'
            hθJ' ?_
          simpa [GRegime.kind, GRegime.IsChain, GRegime.semigroup] using h
      | bushy θ' hJN' hq' h0' hJ2' hθJ' =>
          exact ae_not_gPairQI_symm (gBushy_gChain_ae θ' θ hJN' hq' h0' hJ2' hθJ' hJN h0 h1')
  | bushy θ hJN hq h0 hJ2 hθJ =>
      cases R' with
      | ray θ' hJN' h1' => exact ae_not_gPairQI_symm (gRay_gBushy_ae θ' θ hJN' h1' hJN hq hJ2 hθJ)
      | full θ' hJN' h0' h1' => exact gBushy_gFull_ae θ θ' hJN hq h0 hJ2 hθJ hJN' h0' h1'
      | chain θ' hJN' h0' _ h1'' _ _ => exact gBushy_gChain_ae θ θ' hJN hq h0 hJ2 hθJ hJN' h0' h1''
      | bushy => simp [GRegime.kind, GRegime.IsChain] at h

/-- **The ray is separated from the other three regimes**: no sample outside regime (R) is
quasi-isometric to the ray. -/
theorem not_ray_gRegime_ae (R : GRegime) (hR : R.kind ≠ 0) :
    ∀ᵐ ω ∂R.sampleLaw.law, ¬ QuasiIsometric (R.sampleLaw.graph ω) rayGraph := by
  cases R with
  | ray => simp [GRegime.kind] at hR
  | full θ hJN h0 h1 => exact not_ray_gFull θ hJN h0 h1
  | chain θ hJN h0 _ h1' _ _ => exact not_ray_gChain θ hJN h0 h1'
  | bushy θ hJN hq _ hJ2 hθJ => exact not_ray_gBushy θ hJN hq hJ2 hθJ

/-- Almost sure failure excludes almost sure truth on a probability space. -/
lemma not_ae_of_ae_not {L L' : GSampleLaw}
    (hnot : ∀ᵐ ω ∂(L.law.prod L'.law), ¬ GPairQI L L' ω) :
    ¬ ∀ᵐ ω ∂(L.law.prod L'.law), GPairQI L L' ω := by
  intro hqi
  have hfalse : ∀ᵐ ω ∂(L.law.prod L'.law), False := by
    filter_upwards [hqi, hnot] with ω h1 h2
    exact h2 h1
  exact IsProbabilityMeasure.ne_zero (L.law.prod L'.law)
    (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse))

/-- An auxiliary law-level equivalence underlying **`thm:trichotomy`**. Two independent samples
are almost surely quasi-isometric if and only if their laws have the same class invariant.
The hypotheses `ChainUniversality` and `ChainSeparation` represent `thm:chain-general` and
`thm:chain-separation`. The separate same-class and different-class declarations above retain
the stronger eventwise conclusions used in the paper. -/
theorem trichotomy_general (hUniv : ChainUniversality) (hSep : ChainSeparation)
    (R R' : GRegime) :
    (∀ᵐ ω ∂(R.sampleLaw.law.prod R'.sampleLaw.law), GPairQI R.sampleLaw R'.sampleLaw ω) ↔
      (R.kind = R'.kind ∧ (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup)) := by
  constructor
  · intro hqi
    by_contra hne
    refine not_ae_of_ae_not (diff_gRegime_ae hSep R R' ?_) hqi
    by_cases hk : R.kind = R'.kind
    · right
      have hsem : ¬ (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup) :=
        fun hsem ↦ hne ⟨hk, hsem⟩
      obtain ⟨hc, hsem⟩ := Classical.not_imp.mp hsem
      obtain ⟨hc', hsem⟩ := Classical.not_imp.mp hsem
      exact ⟨hc, hc', hsem⟩
    · exact Or.inl hk
  · rintro ⟨hk, hsem⟩
    exact same_gRegime_ae hUniv R R' hk hsem

/-! ### The chain universality discharged -/

/-- **`thm:chain-general` discharges the universality hypothesis**: `ChainUniversality`
holds, by `chain_general_ae`. -/
theorem chainUniversality : ChainUniversality := fun θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hJN' hθ0'
    hθ1'₀ hθ1'' hJ2' hθJ' hsem =>
  chain_general_ae θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hJN' hθ0' hθ1'₀ hθ1'' hJ2' hθJ' hsem

/-- The auxiliary law-level equivalence with universality within a chain class supplied by
`thm:chain-general`. The only remaining hypothesis is `thm:chain-separation`, discharged by
`chainSeparation` in `ChainSeparationProof.lean`. -/
theorem trichotomy_general' (hSep : ChainSeparation) (R R' : GRegime) :
    (∀ᵐ ω ∂(R.sampleLaw.law.prod R'.sampleLaw.law), GPairQI R.sampleLaw R'.sampleLaw ω) ↔
      (R.kind = R'.kind ∧ (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup)) :=
  trichotomy_general chainUniversality hSep R R'

/-- `same_gRegime_ae` with no hypothesis: two laws in the same class give almost surely
quasi-isometric samples. -/
theorem same_gRegime_ae' (R R' : GRegime) (hk : R.kind = R'.kind)
    (hsem : R.IsChain → R'.IsChain → R.semigroup = R'.semigroup) :
    ∀ᵐ ω ∂(R.sampleLaw.law.prod R'.sampleLaw.law), GPairQI R.sampleLaw R'.sampleLaw ω :=
  same_gRegime_ae chainUniversality R R' hk hsem

end ChainClasses
