/-
`thm:harris` of `matching_classes_simple.tex` in its joint form, at general bounded
support: conditionally on the skeleton, the decorations are independent conjugate
samples, as one identity of laws.

`Skeleton` proves the two halves separately: the skeleton is a reduced-law sample
(`skeletonTreeLaw_eq_treeLaw`) and a dying subtree is a conjugate sample
(`bushTreeLaw_eq_treeLaw`).  `Decorated` constrains both families of one root at once
(`sampleMeasure_root_joint`).  This file iterates the joint root step down the
skeleton: probing the skeleton on a finite prefix-closed set of skeleton addresses and
constraining the decoration of each probed vertex, the mass factorises into one
decoration weight per vertex, each carrying its dying subtrees as independent
conjugate samples.

* `dyingAt`, `measurable_dyingAt`: the dying subtrees of the root, re-addressed by
  their rank among the dying children, as `bushAt` re-addresses the surviving ones.
* `rankSets`, `rankSets_coe`: a rank-indexed family read at a letter, the bridge
  between the letter-indexed constraint of `sampleMeasure_root_joint` and the
  rank-indexed one.
* `decorationEvent`, `decorationMass`: **the decoration of one skeleton vertex**: the
  offspring count, the number of survivors, and the dying subtrees by rank; and its
  conditional weight, the count law tilted by the survival pattern times one bush mass
  per dying child.
* `sampleMeasure_root_decorated`, `survivalMeasure_root_decorated`: the joint root
  step at a fixed survivor count, summed over the survival patterns.
* `consSub`, `prod_cons_decomp`: a prefix-closed finite set of addresses decomposed at
  the root, and the product decomposition it induces.
* `survivalMeasure_decorations`: **the joint Harris decomposition**.  Conditioned on
  survival, the decorations of the probed skeleton vertices are independent, each of
  mass `decorationMass`.
* `bushMeasure_sample_preimage`, `survivalMeasure_decorations_treeLaw`: **the same
  identity as a law on trees**: the dying subtrees enter through their sampled trees,
  and each factor is the conjugate tree law, by `bushTreeLaw_eq_treeLaw`.
-/
import BranchingProcess.Decorated

namespace BranchingProcess

open MeasureTheory ProbabilityTheory ENNReal

variable {J N : ℕ}

/-! ### The dying subtrees, re-addressed by rank -/

/-- **The `m`-th dying subtree of the root**: the dying children are the children
outside the survivors, and `dyingAt c m` reads the subtree of the `m`-th of them in
letter order, as `bushAt` does for the surviving children. -/
noncomputable def dyingAt (c : Word N → ℕ) (m : ℕ) : Word N → ℕ :=
  bushOf (childSet N (c []) \ survivors c) m c

/-- **The dying subtrees are measurable**: the root count and the pattern of survivors
take countably many values, and on each of the corresponding events the subtree is a
shift. -/
lemma measurable_dyingAt (m : ℕ) : Measurable (fun c : Word N → ℕ ↦ dyingAt c m) := by
  intro t ht
  have h : (fun c : Word N → ℕ ↦ dyingAt c m) ⁻¹' t
      = ⋃ j : ℕ, ⋃ S : Finset (Fin N),
          (({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
            ∩ (fun c : Word N → ℕ ↦ bushOf (childSet N j \ S) m c) ⁻¹' t) := by
    ext c
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hc
      exact ⟨c [], survivors c, ⟨rfl, rfl⟩, hc⟩
    · rintro ⟨j, S, ⟨hj, hS⟩, hc⟩
      show bushOf (childSet N (c []) \ survivors c) m c ∈ t
      rw [hj, hS]
      exact hc
  rw [h]
  exact MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun S ↦
    ((measurableSet_root_eq j).inter (measurableSet_survivors_eq S)).inter
      (measurable_bushOf _ m ht)

/-- Constraining the first `k` dying subtrees is a measurable event. -/
lemma measurableSet_forall_dyingAt (k : ℕ) {B : ℕ → Set (Word N → ℕ)}
    (hB : ∀ m, MeasurableSet (B m)) :
    MeasurableSet {c : Word N → ℕ | ∀ m : ℕ, m < k → dyingAt c m ∈ B m} := by
  have h : {c : Word N → ℕ | ∀ m : ℕ, m < k → dyingAt c m ∈ B m}
      = ⋂ m : ℕ, ⋂ _ : m < k, (fun c : Word N → ℕ ↦ dyingAt c m) ⁻¹' (B m) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun _ ↦ measurable_dyingAt m (hB m)

/-- A rank-indexed family read at a letter: the set of the rank of the letter in `D`,
and everything off the alphabet. -/
def rankSets (D : Finset (Fin N)) (B : ℕ → Set (Word N → ℕ)) : ℕ → Set (Word N → ℕ) :=
  fun i ↦ if h : i < N then B (rankOf D ⟨i, h⟩) else Set.univ

lemma measurableSet_rankSets (D : Finset (Fin N)) {B : ℕ → Set (Word N → ℕ)}
    (hB : ∀ m, MeasurableSet (B m)) (i : ℕ) : MeasurableSet (rankSets D B i) := by
  rw [rankSets]
  split
  · exact hB _
  · exact MeasurableSet.univ

/-- At a letter of the alphabet the rank-indexed family reads the rank. -/
lemma rankSets_coe (D : Finset (Fin N)) (B : ℕ → Set (Word N → ℕ)) (i : Fin N) :
    rankSets D B (i : ℕ) = B (rankOf D i) := by
  rw [rankSets, dif_pos i.isLt, Fin.eta]

/-! ### The decoration of one skeleton vertex -/

/-- **The decoration of the root**: `j` children of which `k` survive, the dying
subtrees constrained by their rank. -/
def decorationEvent (j k : ℕ) (B : ℕ → Set (Word N → ℕ)) : Set (Word N → ℕ) :=
  ({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = k})
    ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m}

lemma measurableSet_decorationEvent (j k : ℕ) {B : ℕ → Set (Word N → ℕ)}
    (hB : ∀ m, MeasurableSet (B m)) :
    MeasurableSet (decorationEvent (N := N) j k B) :=
  ((measurableSet_root_eq j).inter (measurableSet_skeletonDegree_eq k)).inter
    (measurableSet_forall_dyingAt (j - k) hB)

/-- **The weight of a decoration**: the count law tilted by the survival pattern,
normalised by survival, times one bush mass per dying child. -/
noncomputable def decorationMass (θ : Offspring J) (j k : ℕ)
    (B : ℕ → Set (Word N → ℕ)) : ℝ≥0∞ :=
  ENNReal.ofReal (θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k)
      / (1 - θ.extinction))
    * ∏ m ∈ Finset.range (j - k), bushMeasure (N := N) θ (B m)

/-! ### The joint root step -/

/-- **The mass of a root count and survivor count with both families of subtrees
constrained by rank**: the survival patterns are summed, each contributing the mass of
`sampleMeasure_root_joint`, the dying product freed of the pattern by the rank
re-indexing. -/
theorem sampleMeasure_root_decorated (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) {j : ℕ} (hj : j ≤ N) (k : ℕ)
    {A B : ℕ → Set (Word N → ℕ)} (hA : ∀ m, MeasurableSet (A m))
    (hB : ∀ m, MeasurableSet (B m)) :
    sampleMeasure (N := N) θ
        ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = k})
            ∩ {c : Word N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m})
          ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m})
      = ENNReal.ofReal
          (θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k))
        * (∏ m ∈ Finset.range k, survivalMeasure θ (A m))
        * ∏ m ∈ Finset.range (j - k), bushMeasure θ (B m) := by
  classical
  have h := measure_root_skeletonDegree_eq_sum (sampleMeasure (N := N) θ) j k
    (X := {c : Word N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m}
      ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m})
    (fun S ↦ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A m}
      ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m})
    (fun S ↦ (measurableSet_forall_bushOf S hA).inter (measurableSet_forall_dyingAt (j - k) hB))
    (fun c _ hk ↦ by subst hk; exact Iff.rfl)
  simp only [← Set.inter_assoc] at h
  have hterm : ∀ S ∈ (childSet N j).powersetCard k,
      sampleMeasure (N := N) θ
          ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
              ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A m})
            ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m})
        = ENNReal.ofReal (θ j) * ENNReal.ofReal (1 - θ.extinction) ^ k
            * ENNReal.ofReal θ.extinction ^ (j - k)
            * (∏ m ∈ Finset.range k, survivalMeasure θ (A m))
            * ∏ m ∈ Finset.range (j - k), bushMeasure θ (B m) := by
    intro S hSmem
    rw [Finset.mem_powersetCard] at hSmem
    obtain ⟨hSsub, hScard⟩ := hSmem
    have hDcard : (childSet N j \ S).card = j - k := by
      rw [Finset.card_sdiff_of_subset hSsub, card_childSet hj, hScard]
    have hset : ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
            ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A m})
          ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m})
        = ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
            ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A m})
          ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
              (fun w : Word N ↦ c (i :: w)) ∈ rankSets (childSet N j \ S) B (i : ℕ)}) := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff]
      rintro ⟨⟨hroot, hS⟩, -⟩
      have hdyeq : ∀ m : ℕ, dyingAt c m = bushOf (childSet N j \ S) m c := by
        intro m
        rw [dyingAt, hroot, hS]
      constructor
      · intro hdy i hiS hij
        have hiD : i ∈ childSet N j \ S := Finset.mem_sdiff.mpr ⟨mem_childSet.mpr hij, hiS⟩
        have hall : ∀ m : ℕ, m < (childSet N j \ S).card
            → bushOf (childSet N j \ S) m c ∈ B m := by
          intro m hm
          rw [← hdyeq]
          exact hdy m (hDcard ▸ hm)
        rw [rankSets_coe]
        exact (forall_bushOf_iff (childSet N j \ S) B c).mp hall i hiD
      · intro hdy m hm
        rw [hdyeq]
        refine (forall_bushOf_iff (childSet N j \ S) B c).mpr ?_ m (hDcard ▸ hm)
        intro i hiD
        obtain ⟨hij, hiS⟩ := Finset.mem_sdiff.mp hiD
        rw [← rankSets_coe (childSet N j \ S) B i]
        exact hdy i hiS (mem_childSet.mp hij)
    rw [hset, sampleMeasure_root_joint θ hJN hq hq0 hj hSsub hA
        (measurableSet_rankSets _ hB), hScard]
    have hdying : ∏ i ∈ childSet N j \ S, bushMeasure (N := N) θ (rankSets (childSet N j \ S) B (i : ℕ))
        = ∏ m ∈ Finset.range (j - k), bushMeasure (N := N) θ (B m) := by
      rw [Finset.prod_congr rfl fun i _ ↦ by rw [rankSets_coe],
        prod_rankOf (childSet N j \ S) fun m ↦ bushMeasure (N := N) θ (B m), hDcard]
    rw [hdying]
  rw [h, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_powersetCard_pattern θ hj k]

/-- **The joint root step under the conditioned law**: the decoration of the root
carries the weight `decorationMass`, and the surviving subtrees are independent
conditioned samples. -/
theorem survivalMeasure_root_decorated (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) {j k : ℕ} (hj : j ≤ N) (hk : k ≠ 0)
    {A B : ℕ → Set (Word N → ℕ)} (hA : ∀ m, MeasurableSet (A m))
    (hB : ∀ m, MeasurableSet (B m)) :
    survivalMeasure (N := N) θ
        (decorationEvent j k B ∩ {c : Word N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m})
      = decorationMass θ j k B * ∏ m ∈ Finset.range k, survivalMeasure θ (A m) := by
  have hnn : (0 : ℝ) ≤ 1 - θ.extinction := by linarith [θ.extinction_le_one]
  have hpos : (0 : ℝ) < 1 - θ.extinction := by linarith
  have hne : ENNReal.ofReal (1 - θ.extinction) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hset : decorationEvent j k B
        ∩ {c : Word N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m}
      = ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = k})
          ∩ {c : Word N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m})
        ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m}) := by
    rw [decorationEvent]
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  have hsurv : {c : Word N → ℕ | Survives c}
        ∩ ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = k})
            ∩ {c : Word N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m})
          ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m})
      = ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = k})
            ∩ {c : Word N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m})
          ∩ {c : Word N → ℕ | ∀ m : ℕ, m < j - k → dyingAt c m ∈ B m}) := by
    refine Set.inter_eq_right.mpr fun c hc ↦ ?_
    refine survives_iff_skeletonDegree_ne_zero.mpr ?_
    rw [show skeletonDegree c = k from hc.1.1.2]
    exact hk
  have h0 : (1 : ℝ) - θ.extinction ≠ 0 := ne_of_gt hpos
  have hfac : ENNReal.ofReal
        (θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k))
      = ENNReal.ofReal (1 - θ.extinction)
        * ENNReal.ofReal (θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k
            * θ.extinction ^ (j - k) / (1 - θ.extinction)) := by
    rw [← ENNReal.ofReal_mul hnn]
    congr 1
    rw [mul_comm ((1 : ℝ) - θ.extinction), div_mul_cancel₀ _ h0]
  rw [hset, survivalMeasure_apply, hsurv,
    sampleMeasure_root_decorated θ hJN hq hq0 hj k hA hB, sampleMeasure_survives θ hJN,
    hfac, decorationMass]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
    ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
  ring

/-! ### A prefix-closed set of addresses, decomposed at the root -/

/-- The addresses continuing a first letter. -/
noncomputable def consSub (i : Fin N) (F : Finset (Word N)) : Finset (Word N) :=
  F.preimage (i :: ·) (List.cons_injective.injOn)

@[simp] lemma mem_consSub {i : Fin N} {F : Finset (Word N)} {u : Word N} :
    u ∈ consSub i F ↔ i :: u ∈ F := Finset.mem_preimage

/-- A prefix-closed finite set of addresses containing the root is the root together
with its continuations. -/
lemma finset_cons_decomp [DecidableEq (Word N)] {F : Finset (Word N)} (h : [] ∈ F) :
    F = insert []
      (Finset.univ.biUnion fun i : Fin N ↦ (consSub i F).image (i :: ·)) := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
    mem_consSub, true_and]
  constructor
  · intro hv
    cases v with
    | nil => exact Or.inl rfl
    | cons i u => exact Or.inr ⟨i, u, hv, rfl⟩
  · rintro (rfl | ⟨i, u, hu, rfl⟩)
    · exact h
    · exact hu

/-- The product over a prefix-closed finite set of addresses, decomposed at the
root. -/
lemma prod_cons_decomp {M : Type*} [CommMonoid M] {F : Finset (Word N)} (h : [] ∈ F)
    (g : Word N → M) :
    ∏ u ∈ F, g u = g [] * ∏ i : Fin N, ∏ u ∈ consSub i F, g (i :: u) := by
  classical
  have hdisj : ((Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
      (fun i : Fin N ↦ (consSub i F).image (i :: ·)) := by
    intro i _ i' _ hii
    show Disjoint ((consSub i F).image (i :: ·)) ((consSub i' F).image (i' :: ·))
    refine Finset.disjoint_left.mpr fun v hv hv' ↦ ?_
    simp only [Finset.mem_image, mem_consSub] at hv hv'
    obtain ⟨u, -, rfl⟩ := hv
    obtain ⟨u', -, heq⟩ := hv'
    exact hii ((List.cons_eq_cons.mp heq).1.symm)
  have hnotmem : ([] : Word N)
      ∉ Finset.univ.biUnion fun i : Fin N ↦ (consSub i F).image (i :: ·) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and, not_exists]
    rintro i u ⟨-, h⟩
    exact List.cons_ne_nil i u h
  conv_lhs => rw [finset_cons_decomp h]
  rw [Finset.prod_insert hnotmem, Finset.prod_biUnion hdisj]
  refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
  exact Finset.prod_image fun u _ u' _ heq ↦ (List.cons_eq_cons.mp heq).2

/-! ### The joint Harris decomposition -/

/-- **The joint Harris decomposition.**  Conditioned on survival, probe the skeleton
on a finite prefix-closed set of skeleton addresses, prescribing at each probed vertex
its offspring count, its number of surviving children, and constraints on its dying
subtrees.  The mass factorises into one `decorationMass` per probed vertex: the
decorations are independent, and each carries its dying subtrees as independent
conjugate samples.  The letters of an address name surviving children, which is the
compatibility hypothesis `hcomp`. -/
theorem survivalMeasure_decorations (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) :
    ∀ (n : ℕ) (F : Finset (Word N)), (∀ v ∈ F, v.length ≤ n) →
      (∀ v ∈ F, ∀ p : Word N, p <+: v → p ∈ F) →
      ∀ (j k : Word N → ℕ) (B : Word N → ℕ → Set (Word N → ℕ)),
        (∀ u ∈ F, j u ≤ N) → (∀ u ∈ F, k u ≠ 0) →
        (∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) →
        (∀ u m, MeasurableSet (B u m)) →
        survivalMeasure (N := N) θ
            (⋂ u ∈ F, {c : Word N → ℕ | skelSub c u ∈ decorationEvent (j u) (k u) (B u)})
          = ∏ u ∈ F, decorationMass θ (j u) (k u) (B u) := by
  classical
  have _ := isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  intro n
  induction n with
  | zero =>
      intro F hlen hpc j k B hj hk hcomp hB
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : Word N) ∈ F := hpc v hv [] List.nil_prefix
        have hF : F = {[]} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hroot, fun v' hv' ↦ ?_⟩
          exact List.length_eq_zero_iff.mp (Nat.le_zero.mp (hlen v' hv'))
        subst hF
        have hset : (⋂ u ∈ ({[]} : Finset (Word N)),
              {c : Word N → ℕ | skelSub c u ∈ decorationEvent (j u) (k u) (B u)})
            = decorationEvent (j []) (k []) (B [])
              ∩ {c : Word N → ℕ | ∀ m : ℕ, m < k [] → bushAt c m ∈ Set.univ} := by
          ext c
          simp [skelSub_nil]
        rw [hset, survivalMeasure_root_decorated θ hJN hq hq0
          (hj [] hroot) (hk [] hroot) (fun _ ↦ MeasurableSet.univ) (hB []),
          Finset.prod_singleton]
        simp
  | succ n ih =>
      intro F hlen hpc j k B hj hk hcomp hB
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : Word N) ∈ F := hpc v hv [] List.nil_prefix
        -- the recursive event and its collapse for the letters above the root degree
        set E : Fin N → Set (Word N → ℕ) := fun i ↦
          ⋂ u ∈ consSub i F,
            {d : Word N → ℕ | skelSub d u ∈ decorationEvent (j (i :: u)) (k (i :: u)) (B (i :: u))}
          with hE
        have hconsEmpty : ∀ i : Fin N, k [] ≤ (i : ℕ) → consSub i F = ∅ := by
          intro i hi
          rw [Finset.eq_empty_iff_forall_notMem]
          intro u hu
          have h1 : [i] ∈ F := hpc _ (mem_consSub.mp hu) [i] ⟨u, rfl⟩
          have h2 := hcomp [] hroot i (by simpa using h1)
          omega
        have hEuniv : ∀ i : Fin N, k [] ≤ (i : ℕ) → E i = Set.univ := by
          intro i hi
          rw [hE]
          simp [hconsEmpty i hi]
        set A : ℕ → Set (Word N → ℕ) :=
          fun m ↦ if h : m < N then E ⟨m, h⟩ else Set.univ with hA
        have hAmeas : ∀ m, MeasurableSet (A m) := by
          intro m
          simp only [hA]
          split
          · exact MeasurableSet.biInter (consSub _ F).countable_toSet fun u _ ↦
              measurable_skelSub u (measurableSet_decorationEvent _ _ (hB _))
          · exact MeasurableSet.univ
        -- the event decomposed at the root
        have hset : (⋂ u ∈ F,
              {c : Word N → ℕ | skelSub c u ∈ decorationEvent (j u) (k u) (B u)})
            = decorationEvent (j []) (k []) (B [])
              ∩ {c : Word N → ℕ | ∀ m : ℕ, m < k [] → bushAt c m ∈ A m} := by
          ext c
          simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro h
            refine ⟨by simpa [skelSub_nil] using h [] hroot, fun m hm ↦ ?_⟩
            simp only [hA]
            split
            · rename_i hmN
              simp only [hE, Set.mem_iInter, Set.mem_setOf_eq]
              intro u hu
              have := h (⟨m, hmN⟩ :: u) (mem_consSub.mp hu)
              rwa [skelSub_cons] at this
            · exact Set.mem_univ _
          · rintro ⟨h0, hrest⟩ u hu
            cases u with
            | nil => simpa [skelSub_nil] using h0
            | cons i u =>
                rw [skelSub_cons]
                by_cases hik : (i : ℕ) < k []
                · have hm := hrest (i : ℕ) hik
                  simp only [hA] at hm
                  rw [dif_pos i.isLt, Fin.eta] at hm
                  simp only [hE, Set.mem_iInter, Set.mem_setOf_eq] at hm
                  exact hm u (mem_consSub.mpr hu)
                · exact absurd (mem_consSub.mpr hu)
                    (by rw [hconsEmpty i (not_lt.mp hik)]; exact Finset.notMem_empty u)
        -- the root step, and the recursion in each surviving subtree
        have hstep := survivalMeasure_root_decorated θ hJN hq hq0
          (hj [] hroot) (hk [] hroot) hAmeas (hB [])
        set G : ℕ → ℝ≥0∞ := fun m ↦ if h : m < N then
            ∏ u ∈ consSub ⟨m, h⟩ F,
              decorationMass θ (j (⟨m, h⟩ :: u)) (k (⟨m, h⟩ :: u)) (B (⟨m, h⟩ :: u))
          else 1 with hGdef
        have hrec : ∀ m : ℕ, survivalMeasure (N := N) θ (A m) = G m := by
          intro m
          simp only [hA, hGdef]
          split
          · rename_i hmN
            simp only [hE]
            refine ih (consSub ⟨m, hmN⟩ F) (fun u hu ↦ ?_) (fun u hu p hp ↦ ?_)
              (fun u ↦ j (⟨m, hmN⟩ :: u)) (fun u ↦ k (⟨m, hmN⟩ :: u))
              (fun u ↦ B (⟨m, hmN⟩ :: u)) (fun u hu ↦ hj _ (mem_consSub.mp hu))
              (fun u hu ↦ hk _ (mem_consSub.mp hu)) (fun u hu i hi ↦ ?_) (fun u ↦ hB _)
            · have := hlen _ (mem_consSub.mp hu)
              simpa using this
            · exact mem_consSub.mpr
                (hpc _ (mem_consSub.mp hu) _ (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))
            · exact hcomp _ (mem_consSub.mp hu) i (mem_consSub.mp hi)
          · exact measure_univ
        -- reassemble the product
        have hG : ∀ i : Fin N,
            ∏ u ∈ consSub i F, decorationMass θ (j (i :: u)) (k (i :: u)) (B (i :: u))
              = G (i : ℕ) := by
          intro i
          simp only [hGdef, dif_pos i.isLt, Fin.eta]
        have hGone : ∀ m : ℕ, k [] ≤ m → G m = 1 := by
          intro m hm
          simp only [hGdef]
          split
          · rename_i h
            rw [hconsEmpty ⟨m, h⟩ hm, Finset.prod_empty]
          · rfl
        rw [hset, hstep, prod_cons_decomp hroot]
        refine congrArg _ ?_
        rw [Finset.prod_congr rfl fun i _ ↦ hG i, Fin.prod_univ_eq_prod_range G N,
          Finset.prod_congr rfl fun m _ ↦ hrec m]
        rcases le_total (k []) N with hkN | hNk
        · exact Finset.prod_subset
            (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
            fun m _ hm' ↦ hGone m (not_lt.mp fun hc ↦ hm' (Finset.mem_range.mpr hc))
        · have hsub : Finset.range N ⊆ Finset.range (k []) := by
            intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          have hone : ∀ m ∈ Finset.range (k []), m ∉ Finset.range N → G m = 1 := by
            intro m _ hm'
            simp only [hGdef]
            exact dif_neg fun hc ↦ hm' (Finset.mem_range.mpr hc)
          exact (Finset.prod_subset hsub hone).symm

/-! ### The skeleton degree pattern

Marginalising the offspring counts and the dying subtrees out of the joint
decomposition leaves `thm:harris-general`\labelcref{it:harris-general-reduced}
in its probabilistic form: probed on a finite prefix-closed set of skeleton
addresses, the skeleton degrees are independent with the reduced law. -/

/-- The root count of a skeleton subfield is a coordinate of the field, or
zero. -/
lemma skelSub_root_cases (c : Word N → ℕ) :
    ∀ u, (∃ v, skelSub c u [] = c v) ∨ skelSub c u [] = 0 := by
  intro u
  induction u generalizing c with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons j u ih =>
      rw [skelSub_cons]
      rcases ih (bushAt c (j : ℕ)) with ⟨v, hv⟩ | hv
      · rw [hv, bushAt]
        by_cases h : (j : ℕ) < (survivors c).card
        · rw [bushOf, dif_pos h]
          exact Or.inl ⟨_, rfl⟩
        · rw [bushOf, dif_neg h]
          exact Or.inr rfl
      · exact Or.inr hv

/-- Coordinates above the support bound are null under the conditioned law. -/
lemma survivalMeasure_coord_gt (θ : Offspring J) (hJN : J ≤ N) (v : Word N) :
    survivalMeasure (N := N) θ {c : Word N → ℕ | N < c v} = 0 := by
  have hsample : sampleMeasure (N := N) θ {c : Word N → ℕ | N < c v} = 0 := by
    have hdecomp : {c : Word N → ℕ | N < c v}
        = ⋃ j : ℕ, {c : Word N → ℕ | c v = N + 1 + j} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨c v - N - 1, by omega⟩
      · rintro ⟨j, hj⟩
        omega
    rw [hdecomp]
    refine measure_iUnion_null fun j ↦ ?_
    rw [sampleMeasure_coord θ v (N + 1 + j), θ.vanishing _ (by omega),
      ENNReal.ofReal_zero]
  rw [survivalMeasure_apply]
  refine mul_eq_zero.mpr (Or.inr (measure_mono_null Set.inter_subset_right hsample))

/-- A skeleton subfield with root count above the support bound is null. -/
lemma survivalMeasure_skelSub_root_gt (θ : Offspring J) (hJN : J ≤ N) (u : Word N) :
    survivalMeasure (N := N) θ {c : Word N → ℕ | N < skelSub c u []} = 0 := by
  refine measure_mono_null (fun c hc ↦ ?_)
    (measure_iUnion_null fun v : Word N ↦ survivalMeasure_coord_gt θ hJN v)
  rcases skelSub_root_cases c u with ⟨v, hv⟩ | hv
  · exact Set.mem_iUnion.mpr ⟨v, by rw [Set.mem_setOf_eq, ← hv]; exact hc⟩
  · rw [Set.mem_setOf_eq, hv] at hc
    omega

/-- **The skeleton degree pattern**, `thm:harris-general` in its probabilistic
form: probed on a finite prefix-closed set of skeleton addresses whose letters
name surviving children, the skeleton degrees are independent, each with the
reduced law. -/
theorem survivalMeasure_skelField_pattern (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (n : ℕ) (F : Finset (Word N)) (hlen : ∀ v ∈ F, v.length ≤ n)
    (hpc : ∀ v ∈ F, ∀ p : Word N, p <+: v → p ∈ F)
    (k : Word N → ℕ) (hk : ∀ u ∈ F, k u ≠ 0)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, {c : Word N → ℕ | skeletonDegree (skelSub c u) = k u})
      = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight (k u)) := by
  classical
  have _ := isProbabilityMeasure_bushMeasure (N := N) θ hJN hq0
  set Bu : Word N → ℕ → Set (Word N → ℕ) := fun _ _ ↦ Set.univ with hBu
  -- the third clause of a decoration event with trivial constraints is trivial
  have hdec : ∀ j' k' : ℕ, decorationEvent (N := N) j' k' (fun _ ↦ Set.univ)
      = {c : Word N → ℕ | c [] = j'} ∩ {c : Word N → ℕ | skeletonDegree c = k'} := by
    intro j' k'
    rw [decorationEvent]
    ext c
    simp
  -- split the event over the root counts at the probed addresses
  have hcover : (⋂ u ∈ F, {c : Word N → ℕ | skeletonDegree (skelSub c u) = k u})
      = (⋃ f : ↥F → Fin (N + 1),
          ⋂ u ∈ F, {c : Word N → ℕ | skelSub c u ∈
            decorationEvent (N := N) (if h : u ∈ F then (f ⟨u, h⟩ : ℕ) else 0) (k u)
              (fun _ ↦ Set.univ)})
        ∪ ((⋂ u ∈ F, {c : Word N → ℕ | skeletonDegree (skelSub c u) = k u})
          ∩ ⋃ u ∈ F, {c : Word N → ℕ | N < skelSub c u []}) := by
    ext c
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq,
      Set.mem_inter_iff]
    constructor
    · intro h
      by_cases hbig : ∃ u ∈ F, N < skelSub c u []
      · exact Or.inr ⟨h, by
          obtain ⟨u, hu, hgt⟩ := hbig
          exact ⟨u, hu, hgt⟩⟩
      · push Not at hbig
        refine Or.inl ⟨fun u ↦ ⟨skelSub c u.1 [], by have := hbig u.1 u.2; omega⟩,
          fun u hu ↦ ?_⟩
        rw [hdec, dif_pos hu]
        exact ⟨rfl, h u hu⟩
    · rintro (⟨f, hf⟩ | ⟨h, -⟩)
      · intro u hu
        have := hf u hu
        rw [hdec] at this
        exact this.2
      · exact h
  rw [hcover]
  -- the large-root part is null
  have hnull : survivalMeasure (N := N) θ
      ((⋂ u ∈ F, {c : Word N → ℕ | skeletonDegree (skelSub c u) = k u})
        ∩ ⋃ u ∈ F, {c : Word N → ℕ | N < skelSub c u []}) = 0 := by
    refine measure_mono_null Set.inter_subset_right ?_
    refine measure_mono_null (Set.iUnion₂_subset fun u _ ↦
      Set.subset_iUnion (fun u : Word N ↦ {c : Word N → ℕ | N < skelSub c u []}) u) ?_
    exact measure_iUnion_null fun u ↦ survivalMeasure_skelSub_root_gt θ hJN u
  have hunion : ∀ s t : Set (Word N → ℕ), survivalMeasure (N := N) θ t = 0 →
      survivalMeasure (N := N) θ (s ∪ t) = survivalMeasure (N := N) θ s := by
    intro s t ht
    refine le_antisymm ?_ (measure_mono Set.subset_union_left)
    calc survivalMeasure (N := N) θ (s ∪ t)
        ≤ survivalMeasure (N := N) θ s + survivalMeasure (N := N) θ t :=
          measure_union_le s t
      _ = survivalMeasure (N := N) θ s := by rw [ht, add_zero]
  rw [hunion _ _ hnull]
  -- the good part is a finite disjoint union of joint events
  have hdisj : Pairwise (Function.onFun Disjoint fun f : ↥F → Fin (N + 1) ↦
      ⋂ u ∈ F, {c : Word N → ℕ | skelSub c u ∈
        decorationEvent (N := N) (if h : u ∈ F then (f ⟨u, h⟩ : ℕ) else 0) (k u)
          (fun _ ↦ Set.univ)}) := by
    intro f f' hff
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hff ?_
    funext u
    have h1 := Set.mem_iInter₂.mp hc u.1 u.2
    have h2 := Set.mem_iInter₂.mp hc' u.1 u.2
    rw [hdec, dif_pos u.2] at h1 h2
    have : ((f u : ℕ)) = ((f' u : ℕ)) := by
      rw [← h1.1, ← h2.1]
    exact Fin.ext this
  have hmeas : ∀ f : ↥F → Fin (N + 1), MeasurableSet
      (⋂ u ∈ F, {c : Word N → ℕ | skelSub c u ∈
        decorationEvent (N := N) (if h : u ∈ F then (f ⟨u, h⟩ : ℕ) else 0) (k u)
          (fun _ ↦ Set.univ)}) := by
    intro f
    refine MeasurableSet.biInter F.countable_toSet fun u hu ↦ ?_
    exact measurable_skelSub u
      (measurableSet_decorationEvent _ _ fun _ ↦ MeasurableSet.univ)
  rw [measure_iUnion hdisj hmeas]
  -- each joint event factorises by the joint decomposition
  have hterm : ∀ f : ↥F → Fin (N + 1),
      survivalMeasure (N := N) θ
        (⋂ u ∈ F, {c : Word N → ℕ | skelSub c u ∈
          decorationEvent (N := N) (if h : u ∈ F then (f ⟨u, h⟩ : ℕ) else 0) (k u)
            (fun _ ↦ Set.univ)})
      = ∏ u ∈ F.attach, ENNReal.ofReal (θ ((f u : ℕ))
          * (((f u : ℕ)).choose (k u.1) : ℝ) * (1 - θ.extinction) ^ (k u.1)
          * θ.extinction ^ ((f u : ℕ) - k u.1) / (1 - θ.extinction)) := by
    intro f
    have h := survivalMeasure_decorations θ hJN hq hq0 n F hlen hpc
      (fun u ↦ if h : u ∈ F then (f ⟨u, h⟩ : ℕ) else 0) k
      (fun _ _ ↦ Set.univ)
      (fun u hu ↦ by rw [dif_pos hu]; exact Nat.lt_succ_iff.mp (f ⟨u, hu⟩).isLt)
      hk hcomp (fun _ _ ↦ MeasurableSet.univ)
    rw [h, ← Finset.prod_attach F (fun u ↦ decorationMass (N := N) θ
      (if h : u ∈ F then (f ⟨u, h⟩ : ℕ) else 0) (k u) fun _ ↦ Set.univ)]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    rw [decorationMass, dif_pos u.2]
    have hbush : ∀ m ∈ Finset.range ((f u : ℕ) - k u.1),
        bushMeasure (N := N) θ Set.univ = 1 := fun m _ ↦ measure_univ
    rw [Finset.prod_congr rfl hbush, Finset.prod_const_one, mul_one]
  rw [tsum_fintype, Finset.sum_congr rfl fun f _ ↦ hterm f]
  -- swap the sum over root-count patterns with the product over the addresses
  have hattach : F.attach = (Finset.univ : Finset ↥F) :=
    Finset.eq_univ_of_forall (Finset.mem_attach F)
  have hswap := Finset.prod_univ_sum
    (t := fun _ : ↥F ↦ (Finset.univ : Finset (Fin (N + 1))))
    (f := fun u j ↦ ENNReal.ofReal (θ ((j : ℕ))
      * (((j : ℕ)).choose (k u.1) : ℝ) * (1 - θ.extinction) ^ (k u.1)
      * θ.extinction ^ ((j : ℕ) - k u.1) / (1 - θ.extinction)))
  rw [Fintype.piFinset_univ] at hswap
  rw [hattach, ← hswap]
  -- per address, the root counts sum to the reduced weight
  have hcol : ∀ u : ↥F, (∑ j ∈ (Finset.univ : Finset (Fin (N + 1))),
      ENNReal.ofReal (θ ((j : ℕ))
        * (((j : ℕ)).choose (k u.1) : ℝ) * (1 - θ.extinction) ^ (k u.1)
        * θ.extinction ^ ((j : ℕ) - k u.1) / (1 - θ.extinction)))
      = ENNReal.ofReal (θ.skeletonWeight (k u.1)) := by
    intro u
    have hnn : ∀ j ∈ Finset.range (N + 1), (0 : ℝ) ≤ θ j * (j.choose (k u.1) : ℝ)
        * (1 - θ.extinction) ^ (k u.1) * θ.extinction ^ (j - k u.1)
        / (1 - θ.extinction) := by
      intro j _
      have h1 : (0 : ℝ) ≤ 1 - θ.extinction := by linarith [θ.extinction_le_one]
      have h2 := θ.nonneg j
      have h3 := θ.extinction_nonneg
      positivity
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ ENNReal.ofReal (θ j
        * ((j).choose (k u.1) : ℝ) * (1 - θ.extinction) ^ (k u.1)
        * θ.extinction ^ (j - k u.1) / (1 - θ.extinction))) (N + 1),
      ← ENNReal.ofReal_sum_of_nonneg hnn]
    congr 1
    rw [Offspring.skeletonWeight_of_ne_zero θ (hk u.1 u.2), Offspring.surviveWeight,
      Finset.sum_div]
    exact (Finset.sum_subset
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      (fun j hjN hj ↦ by
        rw [θ.vanishing j (by
          simp only [Finset.mem_range] at hjN hj
          omega)]
        ring)).symm
  rw [Finset.prod_congr rfl fun u _ ↦ hcol u, ← hattach,
    Finset.prod_attach F fun u ↦ ENNReal.ofReal (θ.skeletonWeight (k u))]

/-! ### The decorations as laws on trees -/

/-- A dying subtree probed through its sampled tree carries the conjugate tree law. -/
lemma bushMeasure_sample_preimage (θ : Offspring J) (hJN : J ≤ N) (hq0 : 0 < θ.extinction)
    {𝒯 : Set (Subtree N)} (h𝒯 : MeasurableSet 𝒯) :
    bushMeasure (N := N) θ (sample ⁻¹' 𝒯) = treeLaw (N := N) (θ.conjugate hq0) 𝒯 := by
  rw [← bushTreeLaw_eq_treeLaw θ hJN hq0, bushTreeLaw,
    Measure.map_apply measurable_sample h𝒯]

/-- **The joint Harris decomposition, as an identity of laws on trees.**  Conditioned
on survival and conditionally on the skeleton, probed on a finite prefix-closed set of
skeleton addresses with its degrees, the decorations are independent, and the dying
subtrees of each probed vertex are independent Galton-Watson trees with the conjugate
law. -/
theorem survivalMeasure_decorations_treeLaw (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (n : ℕ) (F : Finset (Word N))
    (hlen : ∀ v ∈ F, v.length ≤ n) (hpc : ∀ v ∈ F, ∀ p : Word N, p <+: v → p ∈ F)
    (j k : Word N → ℕ) (𝒯 : Word N → ℕ → Set (Subtree N))
    (hj : ∀ u ∈ F, j u ≤ N) (hk : ∀ u ∈ F, k u ≠ 0)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u)
    (h𝒯 : ∀ u m, MeasurableSet (𝒯 u m)) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, {c : Word N → ℕ | skelSub c u ∈ decorationEvent (j u) (k u)
            (fun m ↦ sample ⁻¹' 𝒯 u m)})
      = ∏ u ∈ F, (ENNReal.ofReal (θ (j u) * ((j u).choose (k u) : ℝ)
            * (1 - θ.extinction) ^ k u * θ.extinction ^ (j u - k u) / (1 - θ.extinction))
          * ∏ m ∈ Finset.range (j u - k u), treeLaw (N := N) (θ.conjugate hq0) (𝒯 u m)) := by
  rw [survivalMeasure_decorations θ hJN hq hq0 n F hlen hpc j k _ hj hk hcomp
    (fun u m ↦ measurable_sample (h𝒯 u m))]
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  rw [decorationMass]
  exact congrArg _ (Finset.prod_congr rfl fun m _ ↦
    bushMeasure_sample_preimage θ hJN hq0 (h𝒯 u m))

end BranchingProcess
