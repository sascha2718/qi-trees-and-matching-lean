/-
`sec:gw-trees` of `prelims.tex` and `thm:harris` of `matching_classes_simple.tex`:
the law of the sample conditioned on survival, and the first structural step of the
Harris-Sevastyanov decomposition, the law of the number of surviving children of the
root.  The arithmetic of the transform lives elsewhere; what is proved here is the
probabilistic content, that the splitting `map_split` turns the survival pattern of the
children of the root into a product event and the count into a binomial sum.

* `survivors`, `skeletonDegree`: the children of the root founding an infinite subtree
  and their number, with `survives_iff_exists_child`,
  `survives_iff_skeletonDegree_ne_zero`, the bridge
  `mem_survivors_iff_mem_skeleton` to the `skeleton` of `Sample`, and
  `measurable_skeletonDegree`.
* `childSet`, `prod_ite_survivors`: the letters naming a child of a root with `j`
  children, and the product over them of a factor depending on survival.
* `skelBox`, `split_preimage_skelBox`, `sampleMeasure_root_survivors`: the event that
  the root has `j` children of which exactly those in `S` survive, read through the
  splitting as a product event, of mass `θ_j (1-q)^{|S|} q^{j-|S|}`.
* `Offspring.surviveWeight`, `sampleMeasure_root_skeletonDegree` and
  `sampleMeasure_skeletonDegree`: the binomial count over the surviving children,
  `P(k survive) = ∑_j θ_j C(j,k) (1-q)^k q^{j-k}`, with `surviveWeight_zero` reading
  the case `k = 0` as the fixed point `f(q) = q`.
* `survivalMeasure`: **the law conditioned on survival**, with
  `isProbabilityMeasure_survivalMeasure`, `survivalMeasure_apply` and
  `survivalMeasure_survives`.
* `Offspring.skeletonWeight` and `survivalMeasure_skeletonDegree`: **the skeleton law
  at the root**, `thm:harris`\labelcref{it:harris-skeleton} and
  `eq:hs-transform`, the surviving-children weights renormalised by the survival
  probability `1-q`, and zero at `k = 0`.
* `bushMeasure` and `bushMeasure_root`: **the conjugate law**, the offspring count at
  the root of a subtree conditioned to die, the tilt `θ_j q^{j-1}` of
  `thm:harris`\labelcref{it:harris-bushes}.

The alphabet has to be wide enough to carry the law: every statement about the measure
hypothesises `J ≤ N`, as in `Law`.
-/
import BranchingProcess.Law
import Mathlib.Probability.ConditionalProbability

namespace BranchingProcess

open MeasureTheory ProbabilityTheory ENNReal

variable {J N : ℕ}

/-! ### The surviving children of the root -/

open scoped Classical in
/-- The children of the root that found an infinite subtree: the letters `i` below the
offspring count at the root whose shifted field survives. -/
noncomputable def survivors (c : Word N → ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N ↦ (i : ℕ) < c [] ∧ Survives fun w ↦ c (i :: w)

/-- Membership in `survivors`, unfolded. -/
theorem mem_survivors {c : Word N → ℕ} {i : Fin N} :
    i ∈ survivors c ↔ (i : ℕ) < c [] ∧ Survives fun w ↦ c (i :: w) := by
  classical
  simp [survivors]

/-- **The arity of the root in the skeleton**: the number of children of the root whose
own subtree is infinite.  Under the conditioning this is the quantity the
Harris-Sevastyanov transform is the law of. -/
noncomputable def skeletonDegree (c : Word N → ℕ) : ℕ := (survivors c).card

/-- **Survival is survival of a child.** One direction is the pigeonhole
`exists_infinite_child_of_infinite`; the other is the injection of a child subtree into
the sample. -/
theorem survives_iff_exists_child {c : Word N → ℕ} :
    Survives c ↔ ∃ i : Fin N, (i : ℕ) < c [] ∧ Survives fun w ↦ c (i :: w) := by
  constructor
  · intro h
    obtain ⟨i, hi, hinf⟩ := exists_infinite_child_of_infinite h
    exact ⟨i, hi, hinf⟩
  · rintro ⟨i, hi, hinf⟩
    have hinf' : (sample fun w : Word N ↦ c (i :: w) : Set (Word N)).Infinite := hinf
    have hinj : Set.InjOn (fun w : Word N ↦ i :: w)
        (sample fun w : Word N ↦ c (i :: w) : Set (Word N)) := by
      intro x _ y _ hxy
      simpa using hxy
    have himg := Set.Infinite.image hinj hinf'
    have hsub : (fun w : Word N ↦ i :: w) ''
        (sample fun w : Word N ↦ c (i :: w) : Set (Word N)) ⊆ (sample c : Set (Word N)) := by
      rintro _ ⟨w, hw, rfl⟩
      exact (append_mem_sample_iff c [i] w).mpr ⟨singleton_mem_sample_iff.mpr hi, hw⟩
    show (sample c : Set (Word N)).Infinite
    exact Set.Infinite.mono hsub himg

/-- **Survival is a positive skeleton degree at the root.** -/
theorem survives_iff_skeletonDegree_ne_zero {c : Word N → ℕ} :
    Survives c ↔ skeletonDegree c ≠ 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := survives_iff_exists_child.mp h
    have hmem : i ∈ survivors c := mem_survivors.mpr hi
    refine fun hzero ↦ ?_
    rw [skeletonDegree, Finset.card_eq_zero] at hzero
    rw [hzero] at hmem
    exact absurd hmem (Finset.notMem_empty i)
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    exact survives_iff_exists_child.mpr ⟨i, mem_survivors.mp hi⟩

/-- Extinction is the absence of a surviving child. -/
theorem not_survives_iff_survivors_eq_empty {c : Word N → ℕ} :
    ¬ Survives c ↔ survivors c = ∅ := by
  rw [survives_iff_skeletonDegree_ne_zero, not_ne_iff, skeletonDegree, Finset.card_eq_zero]

/-- **The surviving children are the skeleton children of the root**: the branching
property identifies the shifted field with the residual subtree. -/
theorem mem_survivors_iff_mem_skeleton {c : Word N → ℕ} {i : Fin N} :
    i ∈ survivors c ↔ [i] ∈ skeleton c := by
  rw [mem_survivors, mem_skeleton_iff]
  constructor
  · rintro ⟨hi, hsurv⟩
    have hmem : [i] ∈ sample c := singleton_mem_sample_iff.mpr hi
    refine ⟨hmem, ?_⟩
    rw [subAt_sample hmem]
    exact hsurv
  · rintro ⟨hmem, hinf⟩
    rw [subAt_sample hmem] at hinf
    exact ⟨singleton_mem_sample_iff.mp hmem, hinf⟩

/-! ### Measurability of the skeleton degree -/

/-- The offspring field of a child subtree is a measurable function of the field. -/
lemma measurable_shift (i : Fin N) :
    Measurable fun c : Word N → ℕ ↦ (fun w : Word N ↦ c (i :: w)) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- A single letter belonging to the surviving children is a measurable event: the
offspring count at the root is a coordinate, and survival of the child subtree is
`measurableSet_survives` pulled back along `measurable_shift`. -/
lemma measurableSet_mem_survivors (i : Fin N) :
    MeasurableSet {c : Word N → ℕ | i ∈ survivors c} := by
  have h : {c : Word N → ℕ | i ∈ survivors c}
      = (coord ([] : Word N) ⁻¹' {k : ℕ | (i : ℕ) < k})
        ∩ ((fun c : Word N → ℕ ↦ fun w : Word N ↦ c (i :: w)) ⁻¹' {c : Word N → ℕ | Survives c})
      := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, mem_survivors, coord]
  rw [h]
  exact (measurable_coord _ MeasurableSet.of_discrete).inter
    (measurable_shift i measurableSet_survives)

/-- The surviving children form a prescribed set on a measurable event: a finite
intersection, one condition per letter. -/
theorem measurableSet_survivors_eq (S : Finset (Fin N)) :
    MeasurableSet {c : Word N → ℕ | survivors c = S} := by
  classical
  have h : {c : Word N → ℕ | survivors c = S}
      = ⋂ i : Fin N, (if i ∈ S then {c : Word N → ℕ | i ∈ survivors c}
          else {c : Word N → ℕ | i ∈ survivors c}ᶜ) := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · rintro rfl i
      by_cases hi : i ∈ survivors c
      · rw [ite_eq_left hi]; exact hi
      · rw [ite_eq_right hi]; exact hi
    · intro h
      ext i
      by_cases hi : i ∈ S
      · have hc := h i
        rw [ite_eq_left hi] at hc
        simp only [Set.mem_ofPred_eq] at hc
        simp [hi, hc]
      · have hc := h i
        rw [ite_eq_right hi] at hc
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hc
        simp [hi, hc]
  rw [h]
  refine MeasurableSet.iInter fun i ↦ ?_
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]; exact measurableSet_mem_survivors i
  · rw [ite_eq_right hi]; exact (measurableSet_mem_survivors i).compl

/-- **The skeleton degree is measurable at each value**: the event is the union, over
the finitely many candidate sets of surviving children, of the events of
`measurableSet_survivors_eq`. -/
theorem measurableSet_skeletonDegree_eq (k : ℕ) :
    MeasurableSet {c : Word N → ℕ | skeletonDegree c = k} := by
  have h : {c : Word N → ℕ | skeletonDegree c = k}
      = ⋃ S ∈ {S : Finset (Fin N) | S.card = k}, {c : Word N → ℕ | survivors c = S} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hc
      exact ⟨survivors c, hc, rfl⟩
    · rintro ⟨S, hcard, rfl⟩
      exact hcard
  rw [h]
  exact MeasurableSet.biUnion (Set.to_countable _) fun S _ ↦ measurableSet_survivors_eq S

/-- **The skeleton degree is a measurable function.** -/
theorem measurable_skeletonDegree : Measurable (skeletonDegree : (Word N → ℕ) → ℕ) :=
  measurable_to_countable' fun k ↦ measurableSet_skeletonDegree_eq k

/-! ### The letters naming a child -/

/-- The letters naming a child of a root with `j` children. -/
def childSet (N j : ℕ) : Finset (Fin N) := Finset.univ.filter fun i : Fin N ↦ (i : ℕ) < j

@[simp] lemma mem_childSet {j : ℕ} {i : Fin N} : i ∈ childSet N j ↔ (i : ℕ) < j := by
  simp [childSet]

/-- An alphabet wide enough to carry `j` children names exactly `j` of them. -/
lemma card_childSet {j : ℕ} (hj : j ≤ N) : (childSet N j).card = j := by
  have h : Finset.image (Fin.val) (childSet N j) = Finset.range j := by
    ext m
    simp only [Finset.mem_image, mem_childSet, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hm
      exact ⟨⟨m, by omega⟩, hm, rfl⟩
  have hcard : (Finset.image (Fin.val) (childSet N j)).card = (childSet N j).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  rw [h, Finset.card_range] at hcard
  exact hcard.symm

/-- The surviving children are children. -/
lemma survivors_subset (c : Word N → ℕ) : survivors c ⊆ childSet N (c []) := by
  intro i hi
  exact mem_childSet.mpr (mem_survivors.mp hi).1

/-- **The product over the children of a root with `j` children** of a factor that is
`A` at a surviving child, `B` at a dying one and `1` at a letter naming no child. -/
lemma prod_ite_survivors {j : ℕ} (hj : j ≤ N) {S : Finset (Fin N)} (hS : S ⊆ childSet N j)
    (A B : ℝ≥0∞) :
    ∏ i : Fin N, (if i ∈ S then A else if (i : ℕ) < j then B else 1)
      = A ^ S.card * B ^ (j - S.card) := by
  classical
  have houter : ∏ i ∈ Finset.univ \ childSet N j,
      (if i ∈ S then A else if (i : ℕ) < j then B else 1) = 1 := by
    refine Finset.prod_eq_one fun i hi ↦ ?_
    rw [Finset.mem_sdiff, mem_childSet] at hi
    rw [ite_eq_right fun hc ↦ hi.2 (mem_childSet.mp (hS hc)), ite_eq_right hi.2]
  have hdying : ∏ i ∈ childSet N j \ S,
      (if i ∈ S then A else if (i : ℕ) < j then B else 1) = B ^ (j - S.card) := by
    have hfac : ∀ i ∈ childSet N j \ S,
        (if i ∈ S then A else if (i : ℕ) < j then B else 1) = B := by
      intro i hi
      rw [Finset.mem_sdiff, mem_childSet] at hi
      rw [ite_eq_right hi.2, ite_eq_left hi.1]
    rw [Finset.prod_congr rfl hfac, Finset.prod_const, Finset.card_sdiff_of_subset hS,
      card_childSet hj]
  have hsurviving : ∏ i ∈ S, (if i ∈ S then A else if (i : ℕ) < j then B else 1) = A ^ S.card := by
    rw [Finset.prod_congr rfl fun i hi ↦ ite_eq_left hi, Finset.prod_const]
  rw [← Finset.prod_sdiff (Finset.subset_univ (childSet N j)), houter, one_mul,
    ← Finset.prod_sdiff hS, hdying, hsurviving, mul_comm]

/-! ### The survival pattern of the children as a product event -/

/-- The product event at the root: the root has `j` children, those named by `S` found
infinite subtrees, and the remaining children die. -/
def skelBox (j : ℕ) (S : Finset (Fin N)) : (i : Option (Fin N)) → Set (Branch N i → ℕ)
  | none => {u | u rootIdx = j}
  | some i =>
      if i ∈ S then {c : Word N → ℕ | Survives c}
      else if (i : ℕ) < j then {c : Word N → ℕ | ¬ Survives c} else Set.univ

@[simp] lemma skelBox_none (j : ℕ) (S : Finset (Fin N)) :
    skelBox (N := N) j S none = {u : Branch N none → ℕ | u rootIdx = j} := rfl

@[simp] lemma skelBox_some (j : ℕ) (S : Finset (Fin N)) (i : Fin N) :
    skelBox j S (some i)
      = if i ∈ S then {c : Word N → ℕ | Survives c}
        else if (i : ℕ) < j then {c : Word N → ℕ | ¬ Survives c} else Set.univ := rfl

lemma measurableSet_skelBox (j : ℕ) (S : Finset (Fin N)) (i : Option (Fin N)) :
    MeasurableSet (skelBox (N := N) j S i) := by
  cases i with
  | none =>
      exact measurableSet_rootIdx_preimage {j}
  | some i =>
      rw [skelBox_some]
      split
      · exact measurableSet_survives
      · split
        · exact measurableSet_survives.compl
        · exact MeasurableSet.univ

/-- **The product event is the survival pattern.** The root has `j` children with `S`
the set of those founding an infinite subtree exactly when the offspring count at the
root is `j`, the subtrees under `S` survive and the remaining ones below `j` die. -/
lemma split_preimage_skelBox (j : ℕ) (S : Finset (Fin N)) (hS : S ⊆ childSet N j) :
    split ⁻¹' Set.univ.pi (skelBox (N := N) j S)
      = {c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S} := by
  ext c
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · intro h
    have hroot : c [] = j := h none
    refine ⟨hroot, ?_⟩
    ext i
    rw [mem_survivors, hroot]
    constructor
    · rintro ⟨hij, hsurv⟩
      by_contra hiS
      have hchild := h (some i)
      rw [skelBox_some, ite_eq_right hiS, ite_eq_left hij] at hchild
      exact hchild hsurv
    · intro hiS
      refine ⟨mem_childSet.mp (hS hiS), ?_⟩
      have hchild := h (some i)
      rw [skelBox_some, ite_eq_left hiS] at hchild
      exact hchild
  · rintro ⟨hroot, hsurv⟩ i
    cases i with
    | none => exact hroot
    | some i =>
        rw [skelBox_some]
        by_cases hiS : i ∈ S
        · rw [ite_eq_left hiS]
          have hmem : i ∈ survivors c := by rw [hsurv]; exact hiS
          exact (mem_survivors.mp hmem).2
        · rw [ite_eq_right hiS]
          by_cases hij : (i : ℕ) < j
          · rw [ite_eq_left hij]
            intro hc
            refine hiS ?_
            rw [← hsurv]
            exact mem_survivors.mpr ⟨by rw [hroot]; exact hij, hc⟩
          · rw [ite_eq_right hij]
            exact Set.mem_univ _

/-- The root factor of the product: the offspring count at the root has the offspring
law. -/
lemma infinitePi_root_apply (θ : Offspring J) (j : ℕ) :
    Measure.infinitePi (fun _ : Branch N none ↦ θ.law) {u : Branch N none → ℕ | u rootIdx = j}
      = ENNReal.ofReal (θ j) :=
  infinitePi_levelBox_none θ 0 j

/-- **The mass of a survival pattern.** The root has `j` children of which exactly those
named by `S` survive with probability `θ_j (1-q)^{|S|} q^{j-|S|}`: the splitting makes
the subtrees independent, each surviving with probability `1-q`. -/
theorem sampleMeasure_root_survivors (θ : Offspring J) (hJN : J ≤ N) {j : ℕ} (hj : j ≤ N)
    {S : Finset (Fin N)} (hS : S ⊆ childSet N j) :
    sampleMeasure (N := N) θ
        ({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
      = ENNReal.ofReal (θ j) * ENNReal.ofReal (1 - θ.extinction) ^ S.card
          * ENNReal.ofReal θ.extinction ^ (j - S.card) := by
  rw [← split_preimage_skelBox j S hS, ← Measure.map_apply measurable_split
      (MeasurableSet.univ_pi (measurableSet_skelBox j S)), map_split, ← Finset.coe_univ,
    Measure.infinitePi_pi _ (fun i _ ↦ measurableSet_skelBox j S i), Fintype.prod_option,
    mul_assoc]
  congr 1
  · exact infinitePi_root_apply θ j
  · rw [← prod_ite_survivors hj hS (ENNReal.ofReal (1 - θ.extinction))
      (ENNReal.ofReal θ.extinction)]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [skelBox_some]
    by_cases hiS : i ∈ S
    · rw [ite_eq_left hiS, ite_eq_left hiS]
      exact (infinitePi_branch_some θ i _).trans (sampleMeasure_survives θ hJN)
    · rw [ite_eq_right hiS, ite_eq_right hiS]
      by_cases hij : (i : ℕ) < j
      · rw [ite_eq_left hij, ite_eq_left hij]
        exact (infinitePi_branch_some θ i _).trans (sampleMeasure_not_survives θ hJN)
      · rw [ite_eq_right hij, ite_eq_right hij]
        exact (infinitePi_branch_some θ i Set.univ).trans measure_univ

/-! ### The binomial count over the surviving children -/

namespace Offspring

/-- **The surviving-children weights** `∑_j θ_j C(j,k) (1-q)^k q^{j-k}`: the law of the
number of children of the root founding an infinite subtree, before the conditioning. -/
noncomputable def surviveWeight (θ : Offspring J) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k)

/-- Each weight is nonnegative. -/
lemma surviveWeight_nonneg (θ : Offspring J) (k : ℕ) : 0 ≤ θ.surviveWeight k := by
  refine Finset.sum_nonneg fun j _ ↦ ?_
  have h1 : (0 : ℝ) ≤ 1 - θ.extinction := by linarith [θ.extinction_le_one]
  exact mul_nonneg (mul_nonneg (mul_nonneg (θ.nonneg j) (Nat.cast_nonneg _))
    (pow_nonneg h1 k)) (pow_nonneg θ.extinction_nonneg _)

/-- **No surviving child is extinction**: the weight at `k = 0` is `f(q) = q`, which is
what the conditioning removes. -/
lemma surviveWeight_zero (θ : Offspring J) : θ.surviveWeight 0 = θ.extinction := by
  have h : ∀ j ∈ Finset.range (J + 1),
      θ j * (j.choose 0 : ℝ) * (1 - θ.extinction) ^ 0 * θ.extinction ^ (j - 0)
        = θ j * θ.extinction ^ j := by
    intro j _
    simp
  rw [surviveWeight, Finset.sum_congr rfl h]
  exact θ.gen_extinction

/-- **The skeleton law at the root**, `eq:hs-transform`: the surviving-children weights
renormalised by the survival probability `1-q`, and zero at `k = 0`. -/
noncomputable def skeletonWeight (θ : Offspring J) (k : ℕ) : ℝ :=
  if k = 0 then 0 else θ.surviveWeight k / (1 - θ.extinction)

/-- Off zero the skeleton law is the quotient. -/
lemma skeletonWeight_of_ne_zero (θ : Offspring J) {k : ℕ} (hk : k ≠ 0) :
    θ.skeletonWeight k = θ.surviveWeight k / (1 - θ.extinction) := by
  rw [skeletonWeight, ite_eq_right hk]

@[simp] lemma skeletonWeight_zero (θ : Offspring J) : θ.skeletonWeight 0 = 0 := by
  rw [skeletonWeight, ite_eq_left rfl]

end Offspring

/-- The offspring count at the root is a measurable coordinate. -/
lemma measurableSet_root_eq (j : ℕ) : MeasurableSet {c : Word N → ℕ | c [] = j} := by
  have h : {c : Word N → ℕ | c [] = j} = (fun c : Word N → ℕ ↦ c []) ⁻¹' {j} := rfl
  rw [h]
  exact measurable_pi_apply ([] : Word N) MeasurableSet.of_discrete

/-- **Decomposition over the survival patterns.**  An event asking that the root have
`j` children of which `k` survive, refined by a condition that may read the survivor
set, is the disjoint union over the `k`-subsets `S` of the `j` children of the events
naming `S` as the survivors. -/
lemma measure_root_skeletonDegree_eq_sum (μ : MeasureTheory.Measure (Word N → ℕ))
    (j k : ℕ) {X : Set (Word N → ℕ)} (Q : Finset (Fin N) → Set (Word N → ℕ))
    (hQ : ∀ S, MeasurableSet (Q S))
    (hX : ∀ c, c [] = j → skeletonDegree c = k → (c ∈ X ↔ c ∈ Q (survivors c))) :
    μ (({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = k}) ∩ X)
      = ∑ S ∈ (childSet N j).powersetCard k,
          μ (({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S}) ∩ Q S) := by
  classical
  have hdecomp : (({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = k}) ∩ X)
      = ⋃ S ∈ (childSet N j).powersetCard k,
          (({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S}) ∩ Q S) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_powersetCard,
      exists_prop]
    constructor
    · rintro ⟨⟨hroot, hk⟩, hXc⟩
      refine ⟨survivors c, ⟨?_, hk⟩, ⟨hroot, rfl⟩, (hX c hroot hk).mp hXc⟩
      rw [← hroot]
      exact survivors_subset c
    · rintro ⟨S, ⟨-, hcard⟩, ⟨hroot, rfl⟩, hQc⟩
      exact ⟨⟨hroot, hcard⟩, (hX c hroot hcard).mpr hQc⟩
  have hdisj : ((childSet N j).powersetCard k : Set (Finset (Fin N))).PairwiseDisjoint
      (fun S ↦ ({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S}) ∩ Q S) := by
    intro S _ T _ hST
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hST ?_
    rw [← hc.1.2]
    exact hc'.1.2
  have hmeas : ∀ S ∈ (childSet N j).powersetCard k,
      MeasurableSet (({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S}) ∩ Q S) :=
    fun S _ ↦ ((measurableSet_root_eq j).inter (measurableSet_survivors_eq S)).inter (hQ S)
  rw [hdecomp, MeasureTheory.measure_biUnion_finset hdisj hmeas]

/-- **The mass of a survival pattern, summed over the patterns**: `j` children with `k`
survivors carry `θ_j C(j,k) (1-q)^k q^{j-k}`. -/
lemma sum_powersetCard_pattern (θ : Offspring J) {j : ℕ} (hj : j ≤ N) (k : ℕ) :
    ∑ _S ∈ (childSet N j).powersetCard k,
        ENNReal.ofReal (θ j) * ENNReal.ofReal (1 - θ.extinction) ^ k
          * ENNReal.ofReal θ.extinction ^ (j - k)
      = ENNReal.ofReal
          (θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k)) := by
  have hnn1 : (0 : ℝ) ≤ 1 - θ.extinction := by linarith [θ.extinction_le_one]
  have hnn2 : (0 : ℝ) ≤ θ j * (j.choose k : ℝ) :=
    mul_nonneg (θ.nonneg j) (Nat.cast_nonneg _)
  have hnn3 : (0 : ℝ) ≤ θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k :=
    mul_nonneg hnn2 (pow_nonneg hnn1 k)
  rw [Finset.sum_const, Finset.card_powersetCard, card_childSet hj, nsmul_eq_mul,
    ENNReal.ofReal_mul hnn3, ENNReal.ofReal_mul hnn2, ENNReal.ofReal_mul (θ.nonneg j),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow hnn1, ENNReal.ofReal_pow θ.extinction_nonneg]
  ring

/-- **The one-root count.** The root has `j` children of which `k` survive with
probability `θ_j C(j,k) (1-q)^k q^{j-k}`: the survival patterns of `j` children with `k`
survivors are the `k`-element subsets of the `j` letters, and each carries the mass of
`sampleMeasure_root_survivors`. -/
theorem sampleMeasure_root_skeletonDegree (θ : Offspring J) (hJN : J ≤ N) {j : ℕ}
    (hj : j ≤ N) (k : ℕ) :
    sampleMeasure (N := N) θ
        ({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = k})
      = ENNReal.ofReal
          (θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k)) := by
  classical
  have h := measure_root_skeletonDegree_eq_sum (sampleMeasure (N := N) θ) j k
    (X := Set.univ) (fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ) (fun _ _ _ ↦ Iff.rfl)
  simp only [Set.inter_univ] at h
  have hterm : ∀ S ∈ (childSet N j).powersetCard k,
      sampleMeasure (N := N) θ
          ({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
        = ENNReal.ofReal (θ j) * ENNReal.ofReal (1 - θ.extinction) ^ k
            * ENNReal.ofReal θ.extinction ^ (j - k) := by
    intro S hSmem
    rw [Finset.mem_powersetCard] at hSmem
    rw [sampleMeasure_root_survivors θ hJN hj hSmem.1, hSmem.2]
  rw [h, Finset.sum_congr rfl hterm, sum_powersetCard_pattern θ hj k]

/-- **The law of the skeleton degree.** Summing the one-root count over the offspring
count at the root, the number of surviving children of the root is `k` with probability
`∑_j θ_j C(j,k) (1-q)^k q^{j-k}`. -/
theorem sampleMeasure_skeletonDegree (θ : Offspring J) (hJN : J ≤ N) (k : ℕ) :
    sampleMeasure (N := N) θ {c : Word N → ℕ | skeletonDegree c = k}
      = ENNReal.ofReal (θ.surviveWeight k) := by
  have hroot : ∀ m : ℕ, MeasurableSet {c : Word N → ℕ | c [] = m} := by
    intro m
    have h : {c : Word N → ℕ | c [] = m} = (fun c : Word N → ℕ ↦ c []) ⁻¹' {m} := rfl
    rw [h]
    exact measurable_pi_apply ([] : Word N) MeasurableSet.of_discrete
  have hmeas : ∀ m : ℕ,
      MeasurableSet ({c : Word N → ℕ | c [] = m} ∩ {c : Word N → ℕ | skeletonDegree c = k}) :=
    fun m ↦ (hroot m).inter (measurableSet_skeletonDegree_eq k)
  have hdisj : Pairwise (Function.onFun Disjoint
      fun m : ℕ ↦ {c : Word N → ℕ | c [] = m} ∩ {c : Word N → ℕ | skeletonDegree c = k}) := by
    intro m l hml
    refine Set.disjoint_left.mpr fun c hc hc' ↦ ?_
    exact hml (hc.1.symm.trans hc'.1)
  have hdecomp : {c : Word N → ℕ | skeletonDegree c = k}
      = ⋃ m : ℕ, ({c : Word N → ℕ | c [] = m} ∩ {c : Word N → ℕ | skeletonDegree c = k}) := by
    ext c
    simp
  have hvanish : ∀ m ∉ Finset.range (J + 1),
      sampleMeasure (N := N) θ
        ({c : Word N → ℕ | c [] = m} ∩ {c : Word N → ℕ | skeletonDegree c = k}) = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    refine nonpos_iff_eq_zero.mp ?_
    calc sampleMeasure (N := N) θ
          ({c : Word N → ℕ | c [] = m} ∩ {c : Word N → ℕ | skeletonDegree c = k})
        ≤ sampleMeasure (N := N) θ {c : Word N → ℕ | c [] = m} :=
          measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal (θ m) := sampleMeasure_coord θ [] m
      _ = 0 := by rw [θ.vanishing m (by omega), ENNReal.ofReal_zero]
  have hnn : ∀ m ∈ Finset.range (J + 1),
      (0 : ℝ) ≤ θ m * (m.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (m - k) := by
    intro m _
    have h1 : (0 : ℝ) ≤ 1 - θ.extinction := by linarith [θ.extinction_le_one]
    exact mul_nonneg (mul_nonneg (mul_nonneg (θ.nonneg m) (Nat.cast_nonneg _))
      (pow_nonneg h1 k)) (pow_nonneg θ.extinction_nonneg _)
  rw [hdecomp, measure_iUnion hdisj hmeas, tsum_eq_sum hvanish, Offspring.surviveWeight,
    ENNReal.ofReal_sum_of_nonneg hnn]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  exact sampleMeasure_root_skeletonDegree θ hJN
    (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hJN) k

/-! ### The law conditioned on survival -/

/-- **The law conditioned on survival**, the measure `ℙ*` the paper works under: the
sample law conditioned on the event that the tree is infinite. -/
noncomputable def survivalMeasure (θ : Offspring J) : Measure (Word N → ℕ) :=
  ProbabilityTheory.cond (sampleMeasure θ) {c : Word N → ℕ | Survives c}

/-- The conditioning event has positive mass exactly for `q < 1`. -/
lemma sampleMeasure_survives_ne_zero (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) :
    sampleMeasure (N := N) θ {c : Word N → ℕ | Survives c} ≠ 0 := by
  rw [sampleMeasure_survives θ hJN]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  linarith

/-- **The conditioned law is a probability measure** once the tree survives with
positive probability. -/
theorem isProbabilityMeasure_survivalMeasure (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) : IsProbabilityMeasure (survivalMeasure (N := N) θ) :=
  ProbabilityTheory.cond_isProbabilityMeasure (sampleMeasure_survives_ne_zero θ hJN hq)

/-- The conditioned law, unfolded: the mass of the intersection with the survival event,
divided by the survival probability. -/
theorem survivalMeasure_apply (θ : Offspring J) (t : Set (Word N → ℕ)) :
    survivalMeasure (N := N) θ t
      = (sampleMeasure (N := N) θ {c : Word N → ℕ | Survives c})⁻¹
        * sampleMeasure (N := N) θ ({c : Word N → ℕ | Survives c} ∩ t) :=
  ProbabilityTheory.cond_apply measurableSet_survives _ t

/-- **The conditioned law is carried by survival.** -/
theorem survivalMeasure_survives (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1) :
    survivalMeasure (N := N) θ {c : Word N → ℕ | Survives c} = 1 :=
  ProbabilityTheory.cond_apply_self (sampleMeasure_survives_ne_zero θ hJN hq)
    (measure_ne_top _ _)

/-- **The skeleton law at the root**, `thm:harris`\labelcref{it:harris-skeleton} for
the arity of the root: conditioned on survival, the number of surviving children of the
root is `k` with probability `θ̃_k`, the surviving-children weight renormalised by the
survival probability `1-q`.  The value `k = 0` is what the conditioning removes. -/
theorem survivalMeasure_skeletonDegree (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (k : ℕ) :
    survivalMeasure (N := N) θ {c : Word N → ℕ | skeletonDegree c = k}
      = ENNReal.ofReal (θ.skeletonWeight k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [survivalMeasure_apply]
    have hempty : {c : Word N → ℕ | Survives c} ∩ {c : Word N → ℕ | skeletonDegree c = 0}
        = (∅ : Set (Word N → ℕ)) := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h ↦ survives_iff_skeletonDegree_ne_zero.mp h
    rw [hempty, measure_empty, mul_zero, Offspring.skeletonWeight_zero, ENNReal.ofReal_zero]
  · rw [survivalMeasure_apply]
    have hinter : {c : Word N → ℕ | Survives c} ∩ {c : Word N → ℕ | skeletonDegree c = k}
        = {c : Word N → ℕ | skeletonDegree c = k} := by
      refine Set.inter_eq_right.mpr fun c hc ↦ ?_
      refine survives_iff_skeletonDegree_ne_zero.mpr ?_
      rw [show skeletonDegree c = k from hc]
      exact hk
    rw [hinter, sampleMeasure_skeletonDegree θ hJN k, sampleMeasure_survives θ hJN,
      Offspring.skeletonWeight_of_ne_zero θ hk,
      ENNReal.ofReal_div_of_pos (by linarith), ENNReal.div_eq_inv_mul]

/-! ### The conjugate law of a dying subtree -/

/-- **The law conditioned on extinction**, the law of a bush: the sample law conditioned
on the event that the tree is finite. -/
noncomputable def bushMeasure (θ : Offspring J) : Measure (Word N → ℕ) :=
  ProbabilityTheory.cond (sampleMeasure θ) {c : Word N → ℕ | ¬ Survives c}

/-- **The conjugate law**, `thm:harris`\labelcref{it:harris-bushes}: conditioned on
dying, the root of a subtree has `j` children with probability `θ_j q^{j-1}`, the law
tilted by the extinction probability.  The quotient carries the case `j = 0`. -/
theorem bushMeasure_root (θ : Offspring J) (hJN : J ≤ N) (hq : 0 < θ.extinction) {j : ℕ}
    (hj : j ≤ N) :
    bushMeasure (N := N) θ {c : Word N → ℕ | c [] = j}
      = ENNReal.ofReal (θ j * θ.extinction ^ j / θ.extinction) := by
  have hns : MeasurableSet {c : Word N → ℕ | ¬ Survives c} := measurableSet_survives.compl
  rw [bushMeasure, ProbabilityTheory.cond_apply hns]
  have hinter : {c : Word N → ℕ | ¬ Survives c} ∩ {c : Word N → ℕ | c [] = j}
      = {c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = ∅} := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_survives_iff_survivors_eq_empty]
    exact And.comm
  rw [hinter, sampleMeasure_root_survivors θ hJN hj (Finset.empty_subset _),
    sampleMeasure_not_survives θ hJN, Finset.card_empty, pow_zero, mul_one, Nat.sub_zero,
    ENNReal.ofReal_div_of_pos hq, ENNReal.ofReal_mul (θ.nonneg j),
    ENNReal.ofReal_pow θ.extinction_nonneg, ENNReal.div_eq_inv_mul]

end BranchingProcess
