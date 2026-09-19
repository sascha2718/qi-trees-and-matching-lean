/-
`thm:concentrated-regular-subtree` under the conditioned law: a sample of an offspring
law concentrated at a large arity almost surely contains, on survival, a retained
vertex and hence an isometric copy of the binary tree `𝒩(2)`.

`BranchingProcess.Pruning` supplies the retained vertices and the lower bound `4/5` on
the probability that the root is retained.  The retained vertex is found along the
neck descent of the Harris decomposition, through the iteration scheme of
`GeneralObstructions`: the step is the passage to the first surviving subtree of the
root, which preserves the conditioned law, and the root event asks that the root be a
split whose second surviving subtree has a retained root.  Conditioned on survival the
surviving subtrees of the root are independent conditioned samples, so the event is
independent of the stepped field and has positive mass, and some iterate realises it
almost surely.  The paper instead walks down the first-child ray of a law without mass
at zero; the descent along the skeleton covers every supercritical law, mass at zero
included, which is what the bushy class needs.

* `retainedEvent`, `survivalMeasure_retainedEvent_inter`: the root event and its
  product mass.
* `ae_exists_retained_vertex`: a retained vertex of the sample exists almost surely.
* `qiEmbeddable_binary_of_retainedInf`, `ae_qiEmbeddable_binary_of_concentrated`:
  the binary tree embeds isometrically below it, almost surely.
* `ae_sampleMeasure_of_ae_survivalMeasure`: an almost sure statement under the
  conditioned law holds almost surely on survival under the unconditioned law.
-/
import BranchingProcess.Pruning
import BranchingProcess.Embedding
import ChainClasses.Universality.GeneralObstructions

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BranchingProcess (Offspring sample survivalMeasure sampleMeasure Survives skeletonDegree
  skeleton bushAt RetainedInf QIEmbeddable)

variable {J N : ℕ} (θ : Offspring J)

/-! ### The root event of the descent -/

/-- The root is a split, and the root of its second surviving subtree is retained. -/
def retainedEvent (J m : ℕ) : Set (GWord N → ℕ) :=
  {c | 2 ≤ skeletonDegree c} ∩ {c | RetainedInf J m (bushAt c 1) []}

lemma measurableSet_retainedEvent (J m : ℕ) : MeasurableSet (retainedEvent (N := N) J m) :=
  (BranchingProcess.measurable_skeletonDegree measurableSet_Ici).inter
    (BranchingProcess.measurable_bushAt 1 (BranchingProcess.measurableSet_retainedInf []))

/-- **The root event is independent of the first surviving subtree**, with mass the
product of the probability of at least two skeleton children and the conditioned
probability that the root is retained. -/
theorem survivalMeasure_retainedEvent_inter (hJN : J ≤ N) (hq : θ.extinction < 1) (m : ℕ)
    {A : Set (GWord N → ℕ)} (hA : MeasurableSet A) :
    survivalMeasure (N := N) θ (retainedEvent J m ∩ (fun c ↦ bushAt c 0) ⁻¹' A)
      = (ENNReal.ofReal ((θ.reduced hq).tailGe 2)
          * survivalMeasure (N := N) θ {d | RetainedInf J m d []})
        * survivalMeasure (N := N) θ A := by
  set A' : ℕ → Set (GWord N → ℕ) := fun i ↦
    if i = 0 then A else if i = 1 then {d | RetainedInf J m d []} else Set.univ with hA'
  have hA'meas : ∀ i, MeasurableSet (A' i) := by
    intro i
    simp only [hA']
    split_ifs
    · exact hA
    · exact BranchingProcess.measurableSet_retainedInf []
    · exact MeasurableSet.univ
  have hAtop : ∀ i, 2 ≤ i → A' i = Set.univ := by
    intro i hi
    simp only [hA']
    rw [if_neg (by omega), if_neg (by omega)]
  have hset : retainedEvent J m ∩ (fun c ↦ bushAt c 0) ⁻¹' A
      = {c | 2 ≤ skeletonDegree c} ∩ {c | ∀ i, i < skeletonDegree c → bushAt c i ∈ A' i} := by
    ext c
    simp only [retainedEvent, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, hA']
    constructor
    · rintro ⟨⟨h2, hr⟩, hA0⟩
      refine ⟨h2, fun i _ ↦ ?_⟩
      rcases i with _ | _ | i
      · simpa using hA0
      · simpa using hr
      · simp
    · rintro ⟨h2, h⟩
      have h0 := h 0 (by omega)
      have h1 := h 1 (by omega)
      simp at h0 h1
      exact ⟨⟨h2, h1⟩, h0⟩
  rw [hset, BranchingProcess.survivalMeasure_bushes θ hJN hq 2 hA'meas hAtop]
  simp only [hA', Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  simp only [↓reduceIte, one_ne_zero]
  ring

/-! ### The retained vertex -/

/-- The mass of the reduced law on at least two skeleton children is positive once the
top arity is charged. -/
lemma tailGe_two_pos (hq : θ.extinction < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) :
    0 < (θ.reduced hq).tailGe 2 := by
  have hpos := skeletonWeight_top_pos θ hq (by omega) hθJ
  have hnonneg : ∀ k ∈ Finset.range (J + 1),
      (0 : ℝ) ≤ if 2 ≤ k then (θ.reduced hq) k else 0 := by
    intro k _
    split_ifs
    · exact (θ.reduced hq).nonneg k
    · exact le_rfl
  have hterm : (if 2 ≤ J then (θ.reduced hq) J else 0) = θ.skeletonWeight J := by
    rw [if_pos hJ2, BranchingProcess.Offspring.reduced_apply]
  calc (0 : ℝ) < θ.skeletonWeight J := hpos
    _ = if 2 ≤ J then (θ.reduced hq) J else 0 := hterm.symm
    _ ≤ (θ.reduced hq).tailGe 2 :=
        Finset.single_le_sum hnonneg (Finset.self_mem_range_succ J)

/-- The conditioned probability of a retained root is at least the unconditioned one:
a retained root survives. -/
lemma ofReal_le_survivalMeasure_retainedInf (hJN : J ≤ N) (hJ : 24 ≤ J)
    (hθJ : 7 / 8 ≤ θ J) :
    ENNReal.ofReal (4 / 5)
      ≤ survivalMeasure (N := N) θ {d : GWord N → ℕ | RetainedInf J (J / 2 + 1) d []} := by
  refine (BranchingProcess.ofReal_le_sampleMeasure_retainedInf θ hJN hJ hθJ).trans ?_
  rw [BranchingProcess.survivalMeasure_apply]
  have hsub : {d : GWord N → ℕ | RetainedInf J (J / 2 + 1) d []} ⊆ {c | Survives c} :=
    fun d hd ↦ BranchingProcess.survives_of_retainedInf (by omega) hd
  rw [Set.inter_eq_right.mpr hsub]
  calc sampleMeasure (N := N) θ {d : GWord N → ℕ | RetainedInf J (J / 2 + 1) d []}
      = 1 * sampleMeasure (N := N) θ {d : GWord N → ℕ | RetainedInf J (J / 2 + 1) d []} := by
        rw [one_mul]
    _ ≤ _ := mul_le_mul' (ENNReal.one_le_inv.2 prob_le_one) le_rfl

/-- **A retained vertex of the sample exists almost surely** under the conditioned law of
a law with `J ≥ 24` and `θ_J ≥ 7/8`: some step of the neck descent reaches a split whose
second surviving subtree has a retained root. -/
theorem ae_exists_retained_vertex (hJN : J ≤ N) (hq : θ.extinction < 1) (hJ : 24 ≤ J)
    (hθJ : 7 / 8 ≤ θ J) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, ∃ y ∈ sample c, RetainedInf J (J / 2 + 1) c y := by
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have hp : ENNReal.ofReal ((θ.reduced hq).tailGe 2)
      * survivalMeasure (N := N) θ {d : GWord N → ℕ | RetainedInf J (J / 2 + 1) d []} ≠ 0 := by
    refine mul_ne_zero (ENNReal.ofReal_pos.2 (tailGe_two_pos θ hq (by omega) (by linarith))).ne' ?_
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num))
      (ofReal_le_survivalMeasure_retainedInf θ hJN hJ hθJ)).ne'
  filter_upwards [ae_survives θ hJN hq, ae_exists_iterate_mem (μ := survivalMeasure (N := N) θ)
    (Φ := fun c ↦ bushAt c 0) (D := retainedEvent J (J / 2 + 1))
    (BranchingProcess.measurable_bushAt 0)
    (fun A hA ↦ survivalMeasure_bushAt_zero_preimage θ hJN hq hA)
    (measurableSet_retainedEvent _ _)
    (fun A hA ↦ survivalMeasure_retainedEvent_inter θ hJN hq _ hA) hp] with c hsurv hc
  obtain ⟨k, hk⟩ := hc
  rw [iterate_bushAt_zero] at hk
  obtain ⟨h2, hr⟩ := hk
  obtain ⟨hx, -, hxeq⟩ := neckVertex_spec hsurv k
  have hxs : neckVertex c k ∈ sample c := BranchingProcess.skeleton_subset_sample _ hx
  simp only [Set.mem_setOf_eq] at h2 hr
  rw [hxeq] at h2 hr
  obtain ⟨_, i₁, -, -, hi₁, -, hb₁⟩ := exists_two_skeleton_children h2
  rw [hb₁, ambSub_ambSub] at hr
  refine ⟨neckVertex c k ++ [i₁],
    BranchingProcess.skeleton_subset_sample _ ((mem_skeleton_ambSub_iff hxs).mp hi₁), ?_⟩
  rw [BranchingProcess.retainedInf_append, ← List.append_nil [i₁],
    BranchingProcess.retainedInf_append,
    show (fun u ↦ c (neckVertex c k ++ ([i₁] ++ u))) = ambSub c (neckVertex c k ++ [i₁]) by
      funext u
      simp [ambSub, List.append_assoc]]
  exact hr

/-! ### The binary tree below a retained vertex -/

/-- The whole ambient tree is prefix-closed. -/
lemma prefixClosedN_true : PrefixClosedN (fun _ : GWord N ↦ True) := fun _ _ _ _ ↦ trivial

/-- **The binary tree embeds isometrically below a retained vertex of the sample.** -/
theorem qiEmbeddable_binary_of_retainedInf {m : ℕ} (hm : 2 ≤ m) {c : GWord N → ℕ}
    {y : GWord N} (hr : RetainedInf J m c y) (hy : y ∈ sample c) :
    QIEmbeddable (wordGraphN fun _ : GWord 2 ↦ True) (wordGraphN fun w : GWord N ↦ w ∈ sample c) := by
  obtain ⟨e, he, hd⟩ := BranchingProcess.exists_binary_embedding_of_retainedInf hm hr hy
  refine BranchingProcess.qiEmbeddable_of_isometry (f := fun x ↦ ⟨e x.1, he x.1⟩) fun x y ↦ ?_
  rw [wordGraphN_dist (prefixClosedN_sample c), wordGraphN_dist prefixClosedN_true, hd]

/-- **`thm:concentrated-regular-subtree` under the conditioned law**: the sample of a law
with `J ≥ 24` and `θ_J ≥ 7/8` almost surely contains an isometric copy of the binary
tree. -/
theorem ae_qiEmbeddable_binary_of_concentrated (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hJ : 24 ≤ J) (hθJ : 7 / 8 ≤ θ J) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ,
      QIEmbeddable (wordGraphN fun _ : GWord 2 ↦ True)
        (wordGraphN fun w : GWord N ↦ w ∈ sample c) := by
  filter_upwards [ae_exists_retained_vertex θ hJN hq hJ hθJ] with c hc
  obtain ⟨y, hy, hr⟩ := hc
  exact qiEmbeddable_binary_of_retainedInf (by omega) hr hy

/-! ### From the conditioned law to the survival event -/

/-- An almost sure statement under the conditioned law holds almost surely on survival
under the unconditioned law. -/
theorem ae_sampleMeasure_of_ae_survivalMeasure {P : (GWord N → ℕ) → Prop}
    (h : ∀ᵐ c ∂survivalMeasure (N := N) θ, P c) :
    ∀ᵐ c ∂sampleMeasure (N := N) θ, Survives c → P c := by
  rw [ae_iff] at h ⊢
  rw [BranchingProcess.survivalMeasure_apply] at h
  have hne : (sampleMeasure (N := N) θ {c | Survives c})⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
  have h' := (mul_eq_zero.1 h).resolve_left hne
  refine measure_mono_null (fun c hc ↦ ?_) h'
  simp only [Set.mem_setOf_eq, Classical.not_imp] at hc
  exact ⟨hc.1, hc.2⟩

end ChainClasses
