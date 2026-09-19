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

The paper's own argument, the trials along the first-child ray of a law without mass at
zero, is formalised as well.  The step is the shift to the first child, which preserves
the unconditioned law, and the event `A_0` asks that the root have `J` children and the
root of the subtree at its second child be retained; the splitting at the root makes
`A_0` independent of the shifted field, with mass `θ_J p`.

* `spineShift`, `spineEvent`, `sampleMeasure_spineShift_preimage`,
  `sampleMeasure_spineEvent_inter`, `sampleMeasure_spineEvent_iterate`: the step, the
  event, the invariance of the law, the product mass and `ℙ(A_n) = θ_J p`.
* `measure_iterFail_eq`, `sampleMeasure_spine_fail`, `sampleMeasure_spine_fail_le`:
  `ℙ(τ ≥ N) = (1 - θ_J p)^N ≤ (11/32)^N` for the first success time `τ`.
* `ae_exists_spine_retained`, `ae_exists_spine_binary`: almost surely some `1^n 2` is
  a retained vertex of the sample, and the binary tree embeds below it.
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

/-! ### The first-child ray -/

section Spine

variable (hN : 2 ≤ N)

/-- The shift to the first child of the root: the field of the subtree under the letter
`0`, one step down the first-child ray `1^n` of the paper. -/
def spineShift (c : GWord N → ℕ) : GWord N → ℕ := fun w ↦ c (⟨0, by omega⟩ :: w)

/-- The event `A_0`: the root has `J` children, and the root of the subtree at its second
child is retained. -/
def spineEvent (J m : ℕ) : Set (GWord N → ℕ) :=
  {c | c [] = J ∧ RetainedInf J m (fun w ↦ c (⟨1, by omega⟩ :: w)) []}

lemma measurable_spineShift : Measurable (spineShift (N := N) hN) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

lemma measurableSet_spineEvent (J m : ℕ) : MeasurableSet (spineEvent (N := N) hN J m) := by
  have hshift : Measurable fun c : GWord N → ℕ ↦ fun w ↦ c (⟨1, by omega⟩ :: w) :=
    measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  exact (BranchingProcess.measurableSet_coord_eq [] J).inter
    (hshift (BranchingProcess.measurableSet_retainedInf []))

/-- The product event constraining the subtree at the first child alone. -/
def shiftBox (A : Set (GWord N → ℕ)) :
    (i : Option (Fin N)) → Set (BranchingProcess.Branch N i → ℕ)
  | none => Set.univ
  | some i => if i = ⟨0, by omega⟩ then A else Set.univ

lemma shiftBox_some (A : Set (GWord N → ℕ)) (i : Fin N) :
    shiftBox hN A (some i) = if i = ⟨0, by omega⟩ then A else Set.univ := rfl

lemma measurableSet_shiftBox {A : Set (GWord N → ℕ)} (hA : MeasurableSet A) :
    ∀ i, MeasurableSet (shiftBox (N := N) hN A i)
  | none => MeasurableSet.univ
  | some i => by
      rw [shiftBox_some]
      split_ifs
      · exact hA
      · exact MeasurableSet.univ

/-- The product event is the constraint on the shifted field. -/
lemma split_preimage_shiftBox (A : Set (GWord N → ℕ)) :
    BranchingProcess.split ⁻¹' Set.univ.pi (shiftBox (N := N) hN A) = spineShift hN ⁻¹' A := by
  ext c
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro h
    have h0 := h (some ⟨0, by omega⟩)
    rw [shiftBox_some, if_pos rfl] at h0
    exact h0
  · intro h i
    cases i with
    | none => exact Set.mem_univ _
    | some i =>
        rw [shiftBox_some]
        by_cases h0 : i = ⟨0, by omega⟩
        · rw [if_pos h0]
          subst h0
          exact h
        · rw [if_neg h0]
          exact Set.mem_univ _

/-- **The shift preserves the law**: the subtree at the first child is again a sample, by
the splitting at the root. -/
theorem sampleMeasure_spineShift_preimage {A : Set (GWord N → ℕ)} (hA : MeasurableSet A) :
    sampleMeasure (N := N) θ (spineShift hN ⁻¹' A) = sampleMeasure (N := N) θ A := by
  have hfac : ∀ i : Fin N,
      Measure.infinitePi (fun _ : BranchingProcess.Branch N (some i) ↦ θ.law)
          (shiftBox hN A (some i))
        = if i = ⟨0, by omega⟩ then sampleMeasure (N := N) θ A else 1 := by
    intro i
    rw [shiftBox_some]
    split_ifs
    · exact BranchingProcess.infinitePi_branch_some θ i A
    · exact measure_univ
  rw [← split_preimage_shiftBox hN A, ← Measure.map_apply BranchingProcess.measurable_split
    (MeasurableSet.univ_pi (measurableSet_shiftBox hN hA)), BranchingProcess.map_split,
    ← Finset.coe_univ, Measure.infinitePi_pi _ (fun i _ ↦ measurableSet_shiftBox hN hA i),
    Fintype.prod_option, show shiftBox hN A none = Set.univ from rfl, measure_univ, one_mul,
    Finset.prod_congr rfl fun i _ ↦ hfac i, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]

/-- The product event: the root has `J` children, the subtree at the first child lies in
`A`, and the root of the subtree at the second child is retained. -/
def spineBox (J m : ℕ) (A : Set (GWord N → ℕ)) :
    (i : Option (Fin N)) → Set (BranchingProcess.Branch N i → ℕ)
  | none => {u | u BranchingProcess.rootIdx = J}
  | some i =>
      if i = ⟨0, by omega⟩ then A
      else if i = ⟨1, by omega⟩ then {d : GWord N → ℕ | RetainedInf J m d []} else Set.univ

lemma spineBox_some (J m : ℕ) (A : Set (GWord N → ℕ)) (i : Fin N) :
    spineBox hN J m A (some i)
      = if i = ⟨0, by omega⟩ then A
        else if i = ⟨1, by omega⟩ then {d : GWord N → ℕ | RetainedInf J m d []}
        else Set.univ := rfl

lemma measurableSet_spineBox (J m : ℕ) {A : Set (GWord N → ℕ)} (hA : MeasurableSet A) :
    ∀ i, MeasurableSet (spineBox (N := N) hN J m A i)
  | none => BranchingProcess.measurableSet_rootIdx_preimage {J}
  | some i => by
      rw [spineBox_some]
      split_ifs
      · exact hA
      · exact BranchingProcess.measurableSet_retainedInf []
      · exact MeasurableSet.univ

/-- **The product event is `A_0` together with a constraint on the shifted field.** -/
lemma split_preimage_spineBox {m : ℕ} (A : Set (GWord N → ℕ)) :
    BranchingProcess.split ⁻¹' Set.univ.pi (spineBox (N := N) hN J m A)
      = spineEvent hN J m ∩ spineShift hN ⁻¹' A := by
  have hab : (⟨1, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by simp
  ext c
  simp only [Set.mem_preimage, Set.mem_univ_pi, spineEvent, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 := h (some ⟨0, by omega⟩)
    have h1 := h (some ⟨1, by omega⟩)
    rw [spineBox_some, if_pos rfl] at h0
    rw [spineBox_some, if_neg hab, if_pos rfl] at h1
    exact ⟨⟨h none, h1⟩, h0⟩
  · rintro ⟨⟨hroot, hret⟩, hA0⟩ i
    cases i with
    | none => exact hroot
    | some i =>
        rw [spineBox_some]
        by_cases h0 : i = ⟨0, by omega⟩
        · rw [if_pos h0]
          subst h0
          exact hA0
        · rw [if_neg h0]
          by_cases h1 : i = ⟨1, by omega⟩
          · rw [if_pos h1]
            subst h1
            exact hret
          · rw [if_neg h1]
            exact Set.mem_univ _

/-- **`A_0` is independent of the shifted field**, with mass `θ_J p`: the splitting at the
root makes the root count, the subtree at the first child and the subtree at the second
child independent. -/
theorem sampleMeasure_spineEvent_inter {m : ℕ} {A : Set (GWord N → ℕ)} (hA : MeasurableSet A) :
    sampleMeasure (N := N) θ (spineEvent hN J m ∩ spineShift hN ⁻¹' A)
      = (ENNReal.ofReal (θ J) * sampleMeasure (N := N) θ {d | RetainedInf J m d []})
        * sampleMeasure (N := N) θ A := by
  have hab : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  have hfac : ∀ i : Fin N,
      Measure.infinitePi (fun _ : BranchingProcess.Branch N (some i) ↦ θ.law)
          (spineBox hN J m A (some i))
        = if i = ⟨0, by omega⟩ then sampleMeasure (N := N) θ A
          else if i = ⟨1, by omega⟩ then sampleMeasure (N := N) θ {d | RetainedInf J m d []}
          else 1 := by
    intro i
    rw [spineBox_some]
    split_ifs
    · exact BranchingProcess.infinitePi_branch_some θ i A
    · exact BranchingProcess.infinitePi_branch_some θ i _
    · exact measure_univ
  have hrest : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      i ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin N)) →
        (if i = ⟨0, by omega⟩ then sampleMeasure (N := N) θ A
          else if i = ⟨1, by omega⟩ then sampleMeasure (N := N) θ {d | RetainedInf J m d []}
          else 1) = 1 := by
    intro i _ hi
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [if_neg hi.1, if_neg hi.2]
  rw [← split_preimage_spineBox hN A, ← Measure.map_apply BranchingProcess.measurable_split
    (MeasurableSet.univ_pi (measurableSet_spineBox hN J m hA)), BranchingProcess.map_split,
    ← Finset.coe_univ, Measure.infinitePi_pi _ (fun i _ ↦ measurableSet_spineBox hN J m hA i),
    Fintype.prod_option,
    show spineBox hN J m A none = {u | u BranchingProcess.rootIdx = J} from rfl,
    BranchingProcess.infinitePi_root_apply θ J, Finset.prod_congr rfl fun i _ ↦ hfac i,
    ← Finset.prod_subset (Finset.subset_univ _) hrest, Finset.prod_pair hab, if_pos rfl,
    if_neg hab.symm, if_pos rfl]
  ring

/-- **Every `A_n` has mass `θ_J p`.** -/
theorem sampleMeasure_spineEvent_iterate {m : ℕ} (n : ℕ) :
    sampleMeasure (N := N) θ ((spineShift hN)^[n] ⁻¹' spineEvent hN J m)
      = ENNReal.ofReal (θ J) * sampleMeasure (N := N) θ {d | RetainedInf J m d []} := by
  induction n with
  | zero =>
      have h := sampleMeasure_spineEvent_inter θ hN (m := m) MeasurableSet.univ
      rw [Set.preimage_univ, Set.inter_univ, measure_univ, mul_one] at h
      simpa using h
  | succ n ih =>
      rw [Function.iterate_succ, Set.preimage_comp, sampleMeasure_spineShift_preimage θ hN
        ((measurable_spineShift hN).iterate n (measurableSet_spineEvent hN J m))]
      exact ih

/-- Off the failure event some iterate lies in `D`, and conversely: membership in
`iterFail Φ D k` is failure at the first `k + 1` iterates. -/
lemma mem_iterFail_iff {Ω : Type*} {Φ : Ω → Ω} {D : Set Ω} :
    ∀ (k : ℕ) (ω : Ω), ω ∈ iterFail Φ D k ↔ ∀ i ≤ k, Φ^[i] ω ∉ D
  | 0, ω => by
      simp only [iterFail, Set.mem_compl_iff]
      constructor
      · intro h i hi
        rw [Nat.le_zero.1 hi]
        simpa using h
      · intro h
        simpa using h 0 le_rfl
  | k + 1, ω => by
      simp only [iterFail, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage,
        mem_iterFail_iff k]
      constructor
      · rintro ⟨h0, h⟩ i hi
        cases i with
        | zero => simpa using h0
        | succ i =>
            rw [Function.iterate_succ_apply]
            exact h i (by omega)
      · intro h
        refine ⟨by simpa using h 0 (by omega), fun i hi ↦ ?_⟩
        rw [← Function.iterate_succ_apply]
        exact h (i + 1) (by omega)

/-- **The failure event has the exact geometric mass**, the equality behind
`measure_iterFail_le`. -/
lemma measure_iterFail_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Φ : Ω → Ω} {D : Set Ω} (hΦ : Measurable Φ)
    (hpres : ∀ A, MeasurableSet A → μ (Φ ⁻¹' A) = μ A) (hD : MeasurableSet D) {p : ℝ≥0∞}
    (hind : ∀ A, MeasurableSet A → μ (D ∩ Φ ⁻¹' A) = p * μ A) :
    ∀ k, μ (iterFail Φ D k) = (1 - p) ^ (k + 1) := by
  have hpD : μ D = p := by
    have h := hind Set.univ MeasurableSet.univ
    rwa [Set.preimage_univ, Set.inter_univ, measure_univ, mul_one] at h
  intro k
  induction k with
  | zero =>
      show μ Dᶜ = (1 - p) ^ 1
      rw [pow_one, prob_compl_eq_one_sub hD, hpD]
  | succ k ih =>
      have hF := measurableSet_iterFail hΦ hD k
      have hsplit := measure_inter_add_sdiff (μ := μ) (Φ ⁻¹' iterFail Φ D k) hD
      rw [Set.sdiff_eq, Set.inter_comm (Φ ⁻¹' iterFail Φ D k) D, hind _ hF,
        hpres _ hF, Set.inter_comm] at hsplit
      have hpne : p ≠ ⊤ := hpD ▸ measure_ne_top μ D
      have heq : μ (iterFail Φ D (k + 1)) = μ (iterFail Φ D k) - p * μ (iterFail Φ D k) := by
        show μ (Dᶜ ∩ Φ ⁻¹' iterFail Φ D k) = _
        exact ENNReal.eq_sub_of_add_eq (ENNReal.mul_ne_top hpne (measure_ne_top _ _))
          (by rw [add_comm]; exact hsplit)
      calc μ (iterFail Φ D (k + 1)) = (1 - p) * μ (iterFail Φ D k) := by
            rw [heq, ENNReal.sub_mul (fun _ _ ↦ measure_ne_top _ _), one_mul]
        _ = (1 - p) ^ (k + 1 + 1) := by rw [ih]; ring

/-- **`ℙ(τ ≥ n) = (1 - θ_J p)^n`**: the first `n` trials along the first-child ray all
fail with the geometric mass, the trials being independent with common mass `θ_J p`. -/
theorem sampleMeasure_spine_fail {m : ℕ} (n : ℕ) :
    sampleMeasure (N := N) θ
        {c | ∀ i < n, (spineShift hN)^[i] c ∉ spineEvent hN J m}
      = (1 - ENNReal.ofReal (θ J) * sampleMeasure (N := N) θ {d | RetainedInf J m d []}) ^ n := by
  cases n with
  | zero =>
      have hset : {c : GWord N → ℕ | ∀ i < 0, (spineShift hN)^[i] c ∉ spineEvent hN J m}
          = Set.univ := by
        ext c
        simp
      rw [hset, measure_univ, pow_zero]
  | succ k =>
      have hset : {c : GWord N → ℕ | ∀ i < k + 1, (spineShift hN)^[i] c ∉ spineEvent hN J m}
          = iterFail (spineShift hN) (spineEvent hN J m) k := by
        ext c
        rw [Set.mem_setOf_eq, mem_iterFail_iff]
        exact forall_congr' fun i ↦ imp_congr_left Nat.lt_succ_iff
      rw [hset]
      exact measure_iterFail_eq (measurable_spineShift hN)
        (fun A hA ↦ sampleMeasure_spineShift_preimage θ hN hA) (measurableSet_spineEvent hN J m)
        (fun A hA ↦ sampleMeasure_spineEvent_inter θ hN hA) k

/-- **`ℙ(τ ≥ n) ≤ (11/32)^n`** at `m = ⌊J/2⌋ + 1`, `J ≥ 24` and `θ_J ≥ 7/8`: the common
mass of the trials is at least `7/10`. -/
theorem sampleMeasure_spine_fail_le (hJN : J ≤ N) (hJ : 24 ≤ J) (hθJ : 7 / 8 ≤ θ J) (n : ℕ) :
    sampleMeasure (N := N) θ
        {c | ∀ i < n, (spineShift hN)^[i] c ∉ spineEvent hN J (J / 2 + 1)}
      ≤ ENNReal.ofReal (11 / 32) ^ n := by
  rw [sampleMeasure_spine_fail]
  have hp := BranchingProcess.ofReal_le_sampleMeasure_retainedInf θ hJN hJ hθJ
  have hprod : ENNReal.ofReal (7 / 10)
      ≤ ENNReal.ofReal (θ J)
        * sampleMeasure (N := N) θ {d | RetainedInf J (J / 2 + 1) d []} := by
    calc ENNReal.ofReal (7 / 10) = ENNReal.ofReal (7 / 8) * ENNReal.ofReal (4 / 5) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          norm_num
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hθJ) hp
  have h1 : 1 - ENNReal.ofReal (θ J)
        * sampleMeasure (N := N) θ {d | RetainedInf J (J / 2 + 1) d []}
      ≤ ENNReal.ofReal (11 / 32) := by
    calc 1 - ENNReal.ofReal (θ J)
          * sampleMeasure (N := N) θ {d | RetainedInf J (J / 2 + 1) d []}
        ≤ 1 - ENNReal.ofReal (7 / 10) := tsub_le_tsub_left hprod 1
      _ = ENNReal.ofReal (3 / 10) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
          norm_num
      _ ≤ ENNReal.ofReal (11 / 32) := ENNReal.ofReal_le_ofReal (by norm_num)
  exact pow_le_pow_left' h1 n

/-- At `θ₀ = 0` every vertex has a child, almost surely under the unconditioned law. -/
lemma ae_forall_pos_of_zero_sample (h0 : θ 0 = 0) :
    ∀ᵐ c ∂sampleMeasure (N := N) θ, ∀ v : GWord N, 1 ≤ c v := by
  refine ae_all_iff.mpr fun v ↦ ?_
  rw [ae_iff]
  have he : {c : GWord N → ℕ | ¬ 1 ≤ c v} = {c : GWord N → ℕ | c v = 0} := by
    ext c
    simp
  rw [he, BranchingProcess.sampleMeasure_coord θ v 0, h0, ENNReal.ofReal_zero]

/-- The iterates of the shift are the fields at the vertices `1^n` of the first-child ray. -/
lemma spineShift_iterate (c : GWord N → ℕ) :
    ∀ n, (spineShift hN)^[n] c = ambSub c (List.replicate n ⟨0, by omega⟩)
  | 0 => by simp
  | n + 1 => by
      rw [Function.iterate_succ_apply', spineShift_iterate c n, List.replicate_succ']
      funext w
      simp [spineShift, ambSub, List.append_assoc]

/-- **A retained vertex `1^n 2` of the sample exists almost surely**, for a law without
mass at zero: some trial along the first-child ray succeeds, the ray lies in the sample
since every vertex has a child, and the second child of a root with `J` children lies in
the sample. -/
theorem ae_exists_spine_retained (hJN : J ≤ N) (hJ : 24 ≤ J) (hθJ : 7 / 8 ≤ θ J)
    (h0 : θ 0 = 0) :
    ∀ᵐ c ∂sampleMeasure (N := N) θ, ∃ n : ℕ,
      (spineShift hN)^[n] c ∈ spineEvent hN J (J / 2 + 1) ∧
      List.replicate n (⟨0, by omega⟩ : Fin N) ++ [⟨1, by omega⟩] ∈ sample c ∧
      RetainedInf J (J / 2 + 1) c (List.replicate n (⟨0, by omega⟩ : Fin N) ++ [⟨1, by omega⟩]) := by
  have hp : ENNReal.ofReal (θ J)
      * sampleMeasure (N := N) θ {d : GWord N → ℕ | RetainedInf J (J / 2 + 1) d []} ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (by linarith)).ne'
      (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num))
        (BranchingProcess.ofReal_le_sampleMeasure_retainedInf θ hJN hJ hθJ)).ne'
  filter_upwards [ae_forall_pos_of_zero_sample θ h0,
    ae_exists_iterate_mem (μ := sampleMeasure (N := N) θ) (Φ := spineShift hN)
      (D := spineEvent hN J (J / 2 + 1)) (measurable_spineShift hN)
      (fun A hA ↦ sampleMeasure_spineShift_preimage θ hN hA) (measurableSet_spineEvent hN J _)
      (fun A hA ↦ sampleMeasure_spineEvent_inter θ hN hA) hp] with c hpos hc
  obtain ⟨n, hn⟩ := hc
  have hrep : ∀ k, List.replicate k (⟨0, by omega⟩ : Fin N) ∈ sample c := by
    intro k
    induction k with
    | zero => exact BranchingProcess.nil_mem_sample c
    | succ k ih =>
        rw [List.replicate_succ']
        refine BranchingProcess.mem_sample_append_singleton.2 ⟨ih, ?_⟩
        have := hpos (List.replicate k ⟨0, by omega⟩)
        show 0 < c _
        omega
  refine ⟨n, hn, ?_, ?_⟩
  · rw [spineShift_iterate] at hn
    obtain ⟨hroot, -⟩ := hn
    refine BranchingProcess.mem_sample_append_singleton.2 ⟨hrep n, ?_⟩
    have hJc : c (List.replicate n ⟨0, by omega⟩) = J := by simpa [ambSub] using hroot
    show 1 < c _
    omega
  · rw [spineShift_iterate] at hn
    obtain ⟨-, hret⟩ := hn
    rw [BranchingProcess.retainedInf_append, ← List.append_nil [(⟨1, by omega⟩ : Fin N)],
      BranchingProcess.retainedInf_append]
    exact hret

/-- **`thm:concentrated-regular-subtree` along the first-child ray**: for a law without
mass at zero, the binary tree almost surely embeds isometrically below a retained vertex
`1^n 2` of the sample. -/
theorem ae_exists_spine_binary (hJN : J ≤ N) (hJ : 24 ≤ J) (hθJ : 7 / 8 ≤ θ J) (h0 : θ 0 = 0) :
    ∀ᵐ c ∂sampleMeasure (N := N) θ,
      QIEmbeddable (wordGraphN fun _ : GWord 2 ↦ True)
        (wordGraphN fun w : GWord N ↦ w ∈ sample c) := by
  have hN' : 2 ≤ N := by omega
  filter_upwards [ae_exists_spine_retained θ hN' hJN hJ hθJ h0] with c hc
  obtain ⟨n, -, hmem, hret⟩ := hc
  exact qiEmbeddable_binary_of_retainedInf (by omega) hret hmem

end Spine

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
