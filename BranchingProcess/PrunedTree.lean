/-
`thm:concentrated-regular-subtree`, the probabilistic assertions of the pruning: the exact
binomial recursion `eq:pruned-subtree-recursion` for the probability that the root survives
the rounds, its fixed point for the retained root, and **the retained descendant tree is a
Galton-Watson tree** with the binomial law conditioned to be at least `m`, under the law
conditioned on the root being retained.

The argument is the Harris decomposition of `Skeleton`, with "the subtree at a child is
retained" in place of "the subtree at a child survives": the splitting of the field at the
root makes the subtrees independent, so the pattern of retained children of a root with `J`
children has the binomial mass, and the retained subtrees, re-addressed by rank as in
`skelTree`, are independent copies of the conditioned field.  The tree law is identified on
the containment π-system of `Skeleton`, by the same induction on the height of a finite
prefix-closed set of words, the sample side of which is `sampleMeasure_subset_sample_step`.

* `childPattern`, `patternBox`, `sampleMeasure_pattern`, `sampleMeasure_pattern_card`,
  `sampleMeasure_root_pattern_ge`: the children of the root whose subfield has a property,
  their pattern mass `θ_J p^{|S|} (1-p)^{J-|S|}` and its binomial counts.
* `binomialTail`, `retainedProb_succ`: **`eq:pruned-subtree-recursion`**,
  `p_{n+1} = θ_J ℙ(Bin(J, p_n) ≥ m)`; `sampleMeasure_retainedInf_eq`: its fixed point
  `p = θ_J ℙ(Bin(J, p) ≥ m)` for the retained root.
* `retDegree`, `retAt`, `retSub`, `retField`, `retTree`: the retained descendant tree of the
  root, re-addressed, and its measurability.
* `retainedMeasure`: the law conditioned on the root being retained; `Offspring.pruned`: the
  binomial law conditioned to be at least `m`, supported on `{m, …, J}`.
* `sampleMeasure_root_retDegree_bushes`, `retainedMeasure_retDegree_bushes`,
  `retainedMeasure_bushes`: the branching property of the retained tree at the root.
* `retainedTreeLaw_eq_treeLaw`: **the retained descendant tree is a Galton-Watson tree** with
  law `Offspring.pruned`.
-/
import BranchingProcess.Pruning
import BranchingProcess.Skeleton

namespace BranchingProcess

open MeasureTheory ProbabilityTheory ENNReal
open scoped Classical

variable {J N : ℕ}

/-! ### Patterns of children with a property -/

section Pattern

/-- The children of the root, among the first `J` letters, whose subfield lies in `E`. -/
noncomputable def childPattern (J : ℕ) (E : Set (Word N → ℕ)) (c : Word N → ℕ) :
    Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N ↦ (i : ℕ) < J ∧ (fun w ↦ c (i :: w)) ∈ E

lemma mem_childPattern {E : Set (Word N → ℕ)} {c : Word N → ℕ} {i : Fin N} :
    i ∈ childPattern J E c ↔ (i : ℕ) < J ∧ (fun w ↦ c (i :: w)) ∈ E := by
  simp [childPattern]

lemma childPattern_subset (E : Set (Word N → ℕ)) (c : Word N → ℕ) :
    childPattern J E c ⊆ childSet N J :=
  fun _ hi ↦ mem_childSet.2 (mem_childPattern.1 hi).1

lemma card_childPattern_le (hJN : J ≤ N) (E : Set (Word N → ℕ)) (c : Word N → ℕ) :
    (childPattern J E c).card ≤ J :=
  (Finset.card_le_card (childPattern_subset E c)).trans (card_childSet hJN).le

lemma measurableSet_childPattern_eq {E : Set (Word N → ℕ)} (hE : MeasurableSet E)
    (S : Finset (Fin N)) :
    MeasurableSet {c : Word N → ℕ | childPattern J E c = S} := by
  have h : {c : Word N → ℕ | childPattern J E c = S}
      = ⋂ i : Fin N, {c | i ∈ S ↔ ((i : ℕ) < J ∧ (fun w ↦ c (i :: w)) ∈ E)} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff, mem_childPattern]
    exact forall_congr' fun i ↦ Iff.comm
  rw [h]
  refine MeasurableSet.iInter fun i ↦ ?_
  have hm : MeasurableSet {c : Word N → ℕ | (i : ℕ) < J ∧ (fun w ↦ c (i :: w)) ∈ E} := by
    by_cases hij : (i : ℕ) < J
    · simp only [hij, true_and]
      exact measurable_shift i hE
    · simp only [hij, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  by_cases hiS : i ∈ S
  · simp only [hiS, true_iff]
    exact hm
  · simp only [hiS, false_iff]
    exact hm.compl

/-- The product event: the root has `J` children, and among the first `J` letters exactly
those in `S` have their subfield in `E`. -/
def patternBox (J : ℕ) (E : Set (Word N → ℕ)) (S : Finset (Fin N)) :
    (i : Option (Fin N)) → Set (Branch N i → ℕ)
  | none => {u | u rootIdx = J}
  | some i => if i ∈ S then E else if (i : ℕ) < J then Eᶜ else Set.univ

lemma measurableSet_patternBox {E : Set (Word N → ℕ)} (hE : MeasurableSet E)
    (S : Finset (Fin N)) :
    ∀ i, MeasurableSet (patternBox (N := N) J E S i)
  | none => measurableSet_rootIdx_preimage {J}
  | some i => by
      simp only [patternBox]
      split_ifs
      · exact hE
      · exact hE.compl
      · exact MeasurableSet.univ

/-- **The product event is the pattern.** -/
lemma split_preimage_patternBox (E : Set (Word N → ℕ)) {S : Finset (Fin N)}
    (hS : S ⊆ childSet N J) :
    split ⁻¹' Set.univ.pi (patternBox (N := N) J E S)
      = {c : Word N → ℕ | c [] = J} ∩ {c | childPattern J E c = S} := by
  ext c
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨h none, ?_⟩
    ext i
    rw [mem_childPattern]
    have hi := h (some i)
    constructor
    · rintro ⟨hij, hE⟩
      by_contra hiS
      simp only [patternBox, if_neg hiS, if_pos hij] at hi
      exact hi hE
    · intro hiS
      refine ⟨mem_childSet.1 (hS hiS), ?_⟩
      simp only [patternBox, if_pos hiS] at hi
      exact hi
  · rintro ⟨hroot, hpat⟩ i
    cases i with
    | none => exact hroot
    | some i =>
        by_cases hiS : i ∈ S
        · simp only [patternBox, if_pos hiS]
          exact (mem_childPattern.1 (by rw [hpat]; exact hiS)).2
        · by_cases hij : (i : ℕ) < J
          · simp only [patternBox, if_neg hiS, if_pos hij]
            intro hE'
            exact hiS (by rw [← hpat]; exact mem_childPattern.2 ⟨hij, hE'⟩)
          · simp only [patternBox, if_neg hiS, if_neg hij]
            exact Set.mem_univ _

variable (θ : Offspring J) {E : Set (Word N → ℕ)}

/-- **The mass of a pattern.**  The root has `J` children, and exactly the letters in `S`
have their subfield in `E`, with probability `θ_J p^{|S|} (1-p)^{J-|S|}`, where `p` is
the probability of `E`: the splitting makes the subtrees independent. -/
theorem sampleMeasure_pattern (hJN : J ≤ N) (hE : MeasurableSet E) {S : Finset (Fin N)}
    (hS : S ⊆ childSet N J) :
    sampleMeasure (N := N) θ ({c : Word N → ℕ | c [] = J} ∩ {c | childPattern J E c = S})
      = ENNReal.ofReal (θ J) * (sampleMeasure (N := N) θ E) ^ S.card
        * (1 - sampleMeasure (N := N) θ E) ^ (J - S.card) := by
  rw [← split_preimage_patternBox E hS, ← Measure.map_apply measurable_split
    (MeasurableSet.univ_pi (measurableSet_patternBox hE S)), map_split, ← Finset.coe_univ,
    Measure.infinitePi_pi _ (fun i _ ↦ measurableSet_patternBox hE S i), Fintype.prod_option,
    show patternBox (N := N) J E S none = {u | u rootIdx = J} from rfl, infinitePi_root_apply θ J]
  have hfac : ∀ i : Fin N,
      Measure.infinitePi (fun _ : Branch N (some i) ↦ θ.law) (patternBox J E S (some i))
        = if i ∈ S then sampleMeasure (N := N) θ E
          else if (i : ℕ) < J then 1 - sampleMeasure (N := N) θ E else 1 := by
    intro i
    simp only [patternBox]
    split_ifs
    · rfl
    · show sampleMeasure (N := N) θ Eᶜ = _
      rw [prob_compl_eq_one_sub hE]
    · exact measure_univ
  rw [Finset.prod_congr rfl fun i _ ↦ hfac i, prod_ite_survivors hJN hS]
  ring

/-- **The count of a pattern.**  The root has `J` children of which exactly `k` have their
subfield in `E`, with probability `θ_J C(J,k) p^k (1-p)^{J-k}`. -/
theorem sampleMeasure_pattern_card (hJN : J ≤ N) (hE : MeasurableSet E) (k : ℕ) :
    sampleMeasure (N := N) θ
        ({c : Word N → ℕ | c [] = J} ∩ {c | (childPattern J E c).card = k})
      = ENNReal.ofReal (θ J) * (J.choose k : ℝ≥0∞) * (sampleMeasure (N := N) θ E) ^ k
        * (1 - sampleMeasure (N := N) θ E) ^ (J - k) := by
  have hdecomp : {c : Word N → ℕ | c [] = J} ∩ {c | (childPattern J E c).card = k}
      = ⋃ S ∈ (childSet N J).powersetCard k,
          ({c : Word N → ℕ | c [] = J} ∩ {c | childPattern J E c = S}) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard,
      exists_prop]
    constructor
    · rintro ⟨hroot, hk⟩
      exact ⟨_, ⟨childPattern_subset E c, hk⟩, hroot, rfl⟩
    · rintro ⟨S, ⟨-, hcard⟩, hroot, rfl⟩
      exact ⟨hroot, hcard⟩
  have hdisj : ((childSet N J).powersetCard k : Set (Finset (Fin N))).PairwiseDisjoint
      (fun S ↦ {c : Word N → ℕ | c [] = J} ∩ {c | childPattern J E c = S}) := by
    intro S _ T _ hST
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hST ?_
    rw [← hc.2]
    exact hc'.2
  have hmeas : ∀ S ∈ (childSet N J).powersetCard k,
      MeasurableSet ({c : Word N → ℕ | c [] = J} ∩ {c | childPattern J E c = S}) :=
    fun S _ ↦ (measurableSet_coord_eq [] J).inter (measurableSet_childPattern_eq hE S)
  have hterm : ∀ S ∈ (childSet N J).powersetCard k,
      sampleMeasure (N := N) θ ({c : Word N → ℕ | c [] = J} ∩ {c | childPattern J E c = S})
        = ENNReal.ofReal (θ J) * (sampleMeasure (N := N) θ E) ^ k
          * (1 - sampleMeasure (N := N) θ E) ^ (J - k) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [sampleMeasure_pattern θ hJN hE hS.1, hS.2]
  rw [hdecomp, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hterm, Finset.sum_const,
    Finset.card_powersetCard, card_childSet hJN, nsmul_eq_mul]
  ring

/-- `ℙ(Bin(J, p) ≥ m) = ∑_{k ≥ m} C(J,k) p^k (1-p)^{J-k}`, in `ℝ≥0∞`. -/
noncomputable def binomialTail (J m : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ k ∈ (Finset.range (J + 1)).filter (m ≤ ·), (J.choose k : ℝ≥0∞) * p ^ k * (1 - p) ^ (J - k)

/-- **The binomial count of a pattern.**  The root has `J` children of which at least `m`
have their subfield in `E`, with probability `θ_J ℙ(Bin(J, p) ≥ m)`. -/
theorem sampleMeasure_root_pattern_ge (hJN : J ≤ N) (hE : MeasurableSet E) (m : ℕ) :
    sampleMeasure (N := N) θ
        ({c : Word N → ℕ | c [] = J} ∩ {c | m ≤ (childPattern J E c).card})
      = ENNReal.ofReal (θ J) * binomialTail J m (sampleMeasure (N := N) θ E) := by
  have hdecomp : {c : Word N → ℕ | c [] = J} ∩ {c | m ≤ (childPattern J E c).card}
      = ⋃ k ∈ (Finset.range (J + 1)).filter (m ≤ ·),
          ({c : Word N → ℕ | c [] = J} ∩ {c | (childPattern J E c).card = k}) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨hroot, hm⟩
      exact ⟨_, ⟨Nat.lt_succ_of_le (card_childPattern_le hJN E c), hm⟩, hroot, rfl⟩
    · rintro ⟨k, ⟨-, hmk⟩, hroot, hk⟩
      exact ⟨hroot, hk ▸ hmk⟩
  have hdisj : (((Finset.range (J + 1)).filter (m ≤ ·) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k ↦ {c : Word N → ℕ | c [] = J} ∩ {c | (childPattern J E c).card = k}) := by
    intro k _ l _ hkl
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hkl ?_
    rw [← hc.2]
    exact hc'.2
  have hmeas : ∀ k ∈ (Finset.range (J + 1)).filter (m ≤ ·),
      MeasurableSet ({c : Word N → ℕ | c [] = J} ∩ {c | (childPattern J E c).card = k}) := by
    intro k _
    refine (measurableSet_coord_eq [] J).inter ?_
    have h : {c : Word N → ℕ | (childPattern J E c).card = k}
        = ⋃ S ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun S ↦ S.card = k),
            {c | childPattern J E c = S} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
        true_and, exists_prop]
      exact ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨S, hS, hc⟩ ↦ hc ▸ hS⟩
    rw [h]
    exact MeasurableSet.biUnion (Finset.countable_toSet _)
      fun S _ ↦ measurableSet_childPattern_eq hE S
  rw [hdecomp, measure_biUnion_finset hdisj hmeas, binomialTail, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [sampleMeasure_pattern_card θ hJN hE k]
  ring

end Pattern

/-! ### The exact recursion and its fixed point -/

section Recursion

variable {m : ℕ}

/-- The children surviving `n` rounds form the pattern of the event "the root survives `n`
rounds". -/
lemma retainedChildren_nil_eq (c : Word N → ℕ) (n : ℕ) :
    retainedChildren J m c n [] = childPattern J {d : Word N → ℕ | Retained J m d n []} c := by
  ext i
  rw [mem_retainedChildren, mem_childPattern, List.nil_append]
  exact and_congr Iff.rfl (retained_split_some c i n).symm

/-- The retained children form the pattern of the event "the root is retained". -/
lemma retainedInfChildren_nil_eq (c : Word N → ℕ) :
    retainedInfChildren J m c [] = childPattern J {d : Word N → ℕ | RetainedInf J m d []} c := by
  ext i
  rw [mem_retainedInfChildren, mem_childPattern, List.nil_append]
  refine and_congr Iff.rfl ?_
  have h := retainedInf_append (J := J) (m := m) c [i] []
  rw [List.append_nil] at h
  exact h

variable (N) (θ : Offspring J)

/-- **`eq:pruned-subtree-recursion`.**  The root survives `n + 1` rounds exactly when it
has `J` children of which at least `m` survive `n` rounds:
`p_{n+1} = θ_J ℙ(Bin(J, p_n) ≥ m)`. -/
theorem retainedProb_succ (hJN : J ≤ N) (n : ℕ) :
    retainedProb N θ m (n + 1) = ENNReal.ofReal (θ J) * binomialTail J m (retainedProb N θ m n) := by
  have hset : {c : Word N → ℕ | Retained J m c (n + 1) []}
      = {c : Word N → ℕ | c [] = J}
        ∩ {c | m ≤ (childPattern J {d : Word N → ℕ | Retained J m d n []} c).card} := by
    ext c
    rw [Set.mem_setOf_eq, retained_succ_iff, retainedChildren_nil_eq]
    rfl
  rw [retainedProb, hset, sampleMeasure_root_pattern_ge θ hJN (measurableSet_retained n []) m]
  rfl

/-- **The fixed point of the recursion**: the retained-root probability `p` satisfies
`p = θ_J ℙ(Bin(J, p) ≥ m)`, the retained root having `J` children of which at least `m`
are retained. -/
theorem sampleMeasure_retainedInf_eq (hJN : J ≤ N) :
    sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []}
      = ENNReal.ofReal (θ J)
        * binomialTail J m (sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []}) := by
  have hset : {c : Word N → ℕ | RetainedInf J m c []}
      = {c : Word N → ℕ | c [] = J}
        ∩ {c | m ≤ (childPattern J {d : Word N → ℕ | RetainedInf J m d []} c).card} := by
    ext c
    rw [Set.mem_setOf_eq, retainedInf_iff, retainedInfChildren_nil_eq]
    rfl
  have h := sampleMeasure_root_pattern_ge θ hJN (measurableSet_retainedInf (J := J) (m := m) []) m
  rw [← hset] at h
  exact h

end Recursion

/-! ### The retained descendant tree, re-addressed -/

section RetainedTree

variable {m : ℕ}

/-- The number of retained children of the root. -/
noncomputable def retDegree (J m : ℕ) (c : Word N → ℕ) : ℕ := (retainedInfChildren J m c []).card

/-- The offspring field of the `i`-th retained subtree of the root, the retained children
being ordered by the alphabet; the zero field when there are at most `i` of them. -/
noncomputable def retAt (J m : ℕ) (c : Word N → ℕ) (i : ℕ) : Word N → ℕ :=
  bushOf (retainedInfChildren J m c []) i c

/-- **The subtree of the retained tree at an address.**  The letters of `u` name successive
retained children, the letter `i` selecting the `i`-th of them. -/
noncomputable def retSub (J m : ℕ) : (Word N → ℕ) → Word N → (Word N → ℕ)
  | c, [] => c
  | c, (j :: u) => retSub J m (retAt J m c j) u

@[simp] lemma retSub_nil (c : Word N → ℕ) : retSub J m c [] = c := rfl

@[simp] lemma retSub_cons (c : Word N → ℕ) (j : Fin N) (u : Word N) :
    retSub J m c (j :: u) = retSub J m (retAt J m c j) u := rfl

/-- **The offspring field of the retained tree**: the number of retained children of the
retained vertex an address leads to. -/
noncomputable def retField (J m : ℕ) (c : Word N → ℕ) : Word N → ℕ :=
  fun u ↦ retDegree J m (retSub J m c u)

@[simp] lemma retField_nil (c : Word N → ℕ) : retField J m c [] = retDegree J m c := rfl

@[simp] lemma retField_cons (c : Word N → ℕ) (j : Fin N) (u : Word N) :
    retField J m c (j :: u) = retField J m (retAt J m c j) u := rfl

/-- **The retained descendant tree of the root, re-addressed**: the tree cut out by the
offspring field of the retained tree, an isomorphic copy of the retained descendant tree
of the root inside `𝒩(N)`. -/
noncomputable def retTree (J m : ℕ) (c : Word N → ℕ) : Subtree N := sample (retField J m c)

/-- **The one-step criterion for the retained tree.** -/
lemma mem_retTree_cons {c : Word N → ℕ} {j : Fin N} {u : Word N} :
    j :: u ∈ retTree J m c ↔ (j : ℕ) < retDegree J m c ∧ u ∈ retTree J m (retAt J m c (j : ℕ)) := by
  show (([j] : Word N) ++ u) ∈ sample (retField J m c) ↔ _
  rw [append_mem_sample_iff, singleton_mem_sample_iff]
  exact Iff.rfl

@[simp] lemma nil_mem_retTree (c : Word N → ℕ) : ([] : Word N) ∈ retTree J m c :=
  nil_mem_sample _

/-- The retained children are among the first `J` letters. -/
lemma retainedInfChildren_nil_subset (c : Word N → ℕ) :
    retainedInfChildren J m c [] ⊆ childSet N J := by
  rw [retainedInfChildren_nil_eq]
  exact childPattern_subset _ c

lemma measurableSet_retainedInfChildren_eq (S : Finset (Fin N)) :
    MeasurableSet {c : Word N → ℕ | retainedInfChildren J m c [] = S} := by
  simp only [retainedInfChildren_nil_eq]
  exact measurableSet_childPattern_eq (measurableSet_retainedInf []) S

lemma measurableSet_retDegree_eq (k : ℕ) :
    MeasurableSet {c : Word N → ℕ | retDegree J m c = k} := by
  have h : {c : Word N → ℕ | retDegree J m c = k}
      = ⋃ S ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun S ↦ S.card = k),
          {c : Word N → ℕ | retainedInfChildren J m c [] = S} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop, retDegree]
    exact ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨S, hS, hc⟩ ↦ hc ▸ hS⟩
  rw [h]
  exact MeasurableSet.biUnion (Finset.countable_toSet _)
    fun S _ ↦ measurableSet_retainedInfChildren_eq S

lemma measurable_retDegree : Measurable (retDegree J m : (Word N → ℕ) → ℕ) :=
  measurable_to_countable' fun k ↦ measurableSet_retDegree_eq k

/-- **The retained subtrees are measurable**: the set of retained children takes finitely
many values, and on each of the corresponding events the subtree is a shift. -/
lemma measurable_retAt (i : ℕ) : Measurable (fun c : Word N → ℕ ↦ retAt J m c i) := by
  intro t ht
  have h : (fun c : Word N → ℕ ↦ retAt J m c i) ⁻¹' t
      = ⋃ S : Finset (Fin N),
          ({c : Word N → ℕ | retainedInfChildren J m c [] = S}
            ∩ (fun c : Word N → ℕ ↦ bushOf S i c) ⁻¹' t) := by
    ext c
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hc
      exact ⟨retainedInfChildren J m c [], rfl, hc⟩
    · rintro ⟨S, rfl, hc⟩
      exact hc
  rw [h]
  exact MeasurableSet.iUnion fun S ↦
    (measurableSet_retainedInfChildren_eq S).inter (measurable_bushOf S i ht)

lemma measurable_retSub (u : Word N) : Measurable (fun c : Word N → ℕ ↦ retSub J m c u) := by
  induction u with
  | nil => exact measurable_id
  | cons j u ih =>
      have h : (fun c : Word N → ℕ ↦ retSub J m c (j :: u))
          = (fun d : Word N → ℕ ↦ retSub J m d u) ∘ (fun c : Word N → ℕ ↦ retAt J m c j) := rfl
      rw [h]
      exact ih.comp (measurable_retAt (j : ℕ))

lemma measurable_retField : Measurable (retField J m : (Word N → ℕ) → Word N → ℕ) :=
  measurable_pi_lambda _ fun u ↦ measurable_retDegree.comp (measurable_retSub u)

/-- **The retained tree is a random tree.** -/
lemma measurable_retTree : Measurable (retTree J m : (Word N → ℕ) → Subtree N) :=
  measurable_sample.comp measurable_retField

lemma measurableSet_mem_retTree (u : Word N) :
    MeasurableSet {c : Word N → ℕ | u ∈ retTree J m c} :=
  measurable_retTree (measurableSet_mem_subtree u)

lemma measurableSet_forall_retAt (k : ℕ) {A : ℕ → Set (Word N → ℕ)}
    (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i} := by
  have h : {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i}
      = ⋂ i : ℕ, ⋂ _ : i < k, (fun c : Word N → ℕ ↦ retAt J m c i) ⁻¹' (A i) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦ measurable_retAt i (hA i)

end RetainedTree

/-! ### The branching property of the retained tree -/

section Law

variable {m : ℕ} (θ : Offspring J)

/-- The product event constraining every retained subtree: the root has `J` children, those
named by `S` are retained, the remaining children among the first `J` are not, and the
subtree under a retained letter lies in the set indexed by its rank. -/
def retainedBushesBox (J m : ℕ) (S : Finset (Fin N)) (A : ℕ → Set (Word N → ℕ)) :
    (i : Option (Fin N)) → Set (Branch N i → ℕ)
  | none => {u | u rootIdx = J}
  | some i =>
      if i ∈ S then {d : Word N → ℕ | RetainedInf J m d []} ∩ A (rankOf S i)
      else if (i : ℕ) < J then {d : Word N → ℕ | RetainedInf J m d []}ᶜ else Set.univ

lemma measurableSet_retainedBushesBox (S : Finset (Fin N)) {A : ℕ → Set (Word N → ℕ)}
    (hA : ∀ i, MeasurableSet (A i)) :
    ∀ i, MeasurableSet (retainedBushesBox (N := N) J m S A i)
  | none => measurableSet_rootIdx_preimage {J}
  | some i => by
      simp only [retainedBushesBox]
      split_ifs
      · exact (measurableSet_retainedInf []).inter (hA _)
      · exact (measurableSet_retainedInf []).compl
      · exact MeasurableSet.univ

lemma retainedBushesBox_eq_inter (S : Finset (Fin N)) (A : ℕ → Set (Word N → ℕ)) :
    ∀ i, retainedBushesBox (N := N) J m S A i
      = patternBox J {d : Word N → ℕ | RetainedInf J m d []} S i ∩ bushesOnly S A i
  | none => by
      ext u
      simp [retainedBushesBox, patternBox, bushesOnly]
  | some i => by
      by_cases hi : i ∈ S
      · simp only [retainedBushesBox, patternBox, bushesOnly, if_pos hi]
        rfl
      · simp only [retainedBushesBox, patternBox, bushesOnly, if_neg hi, Set.inter_univ]
        rfl

/-- **The product event constrains every retained subtree.** -/
lemma split_preimage_retainedBushesBox {S : Finset (Fin N)} (hS : S ⊆ childSet N J)
    (A : ℕ → Set (Word N → ℕ)) :
    split ⁻¹' Set.univ.pi (retainedBushesBox (N := N) J m S A)
      = ({c : Word N → ℕ | c [] = J} ∩ {c | retainedInfChildren J m c [] = S})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < S.card → bushOf S i c ∈ A i} := by
  have hbox : Set.univ.pi (retainedBushesBox (N := N) J m S A)
      = Set.univ.pi (patternBox J {d : Word N → ℕ | RetainedInf J m d []} S)
        ∩ Set.univ.pi (bushesOnly (N := N) S A) := by
    rw [← Set.pi_inter_distrib]
    exact Set.pi_congr rfl fun i _ ↦ retainedBushesBox_eq_inter S A i
  rw [hbox, Set.preimage_inter, split_preimage_patternBox _ hS, split_preimage_bushesOnly]
  ext c
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, forall_bushOf_iff S A c,
    retainedInfChildren_nil_eq]

/-- **The mass of a retained pattern with every retained subtree constrained.**  The
splitting makes the subtrees independent: each retained one contributes the mass of the
retained event intersected with the set of its rank, each of the remaining children among
the first `J` the probability `1 - p` of not being retained. -/
theorem sampleMeasure_root_retainedPattern_bushes (hJN : J ≤ N) {S : Finset (Fin N)}
    (hS : S ⊆ childSet N J) {A : ℕ → Set (Word N → ℕ)} (hA : ∀ i, MeasurableSet (A i)) :
    sampleMeasure (N := N) θ
        (({c : Word N → ℕ | c [] = J} ∩ {c | retainedInfChildren J m c [] = S})
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < S.card → bushOf S i c ∈ A i})
      = ENNReal.ofReal (θ J)
        * (1 - sampleMeasure (N := N) θ {d : Word N → ℕ | RetainedInf J m d []}) ^ (J - S.card)
        * ∏ i ∈ Finset.range S.card,
            sampleMeasure (N := N) θ ({d : Word N → ℕ | RetainedInf J m d []} ∩ A i) := by
  have hfac : ∀ i : Fin N,
      Measure.infinitePi (fun _ : Branch N (some i) ↦ θ.law)
          (retainedBushesBox (N := N) J m S A (some i))
        = if i ∈ S then
            sampleMeasure (N := N) θ ({d : Word N → ℕ | RetainedInf J m d []} ∩ A (rankOf S i))
          else if (i : ℕ) < J then
            1 - sampleMeasure (N := N) θ {d : Word N → ℕ | RetainedInf J m d []}
          else 1 := by
    intro i
    simp only [retainedBushesBox]
    split_ifs
    · rfl
    · show sampleMeasure (N := N) θ {d : Word N → ℕ | RetainedInf J m d []}ᶜ = _
      rw [prob_compl_eq_one_sub (measurableSet_retainedInf [])]
    · exact measure_univ
  rw [← split_preimage_retainedBushesBox hS A, ← Measure.map_apply measurable_split
    (MeasurableSet.univ_pi (measurableSet_retainedBushesBox S hA)), map_split,
    ← Finset.coe_univ, Measure.infinitePi_pi _ (fun i _ ↦ measurableSet_retainedBushesBox S hA i),
    Fintype.prod_option,
    show retainedBushesBox (N := N) J m S A none = {u | u rootIdx = J} from rfl,
    infinitePi_root_apply θ J, Finset.prod_congr rfl fun i _ ↦ hfac i,
    prod_ite_survivors_family hJN hS
      (fun i ↦ sampleMeasure (N := N) θ ({d : Word N → ℕ | RetainedInf J m d []} ∩ A i))
      (1 - sampleMeasure (N := N) θ {d : Word N → ℕ | RetainedInf J m d []})]
  ring

/-- **The retained count with every retained subtree constrained.** -/
theorem sampleMeasure_root_retDegree_bushes (hJN : J ≤ N) (k : ℕ) {A : ℕ → Set (Word N → ℕ)}
    (hA : ∀ i, MeasurableSet (A i)) :
    sampleMeasure (N := N) θ
        (({c : Word N → ℕ | c [] = J} ∩ {c | retDegree J m c = k})
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i})
      = ENNReal.ofReal (θ J) * (J.choose k : ℝ≥0∞)
        * (1 - sampleMeasure (N := N) θ {d : Word N → ℕ | RetainedInf J m d []}) ^ (J - k)
        * ∏ i ∈ Finset.range k,
            sampleMeasure (N := N) θ ({d : Word N → ℕ | RetainedInf J m d []} ∩ A i) := by
  have hdecomp : ({c : Word N → ℕ | c [] = J} ∩ {c | retDegree J m c = k})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i}
      = ⋃ S ∈ (childSet N J).powersetCard k,
          (({c : Word N → ℕ | c [] = J} ∩ {c | retainedInfChildren J m c [] = S})
            ∩ {c : Word N → ℕ | ∀ i : ℕ, i < S.card → bushOf S i c ∈ A i}) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard,
      exists_prop, retDegree, retAt]
    constructor
    · rintro ⟨⟨hroot, hk⟩, hbush⟩
      exact ⟨_, ⟨retainedInfChildren_nil_subset c, hk⟩, ⟨hroot, rfl⟩, fun i hi ↦ hbush i (by omega)⟩
    · rintro ⟨S, ⟨-, hcard⟩, ⟨hroot, rfl⟩, hbush⟩
      exact ⟨⟨hroot, hcard⟩, fun i hi ↦ hbush i (by omega)⟩
  have hdisj : ((childSet N J).powersetCard k : Set (Finset (Fin N))).PairwiseDisjoint
      (fun S ↦ ({c : Word N → ℕ | c [] = J} ∩ {c | retainedInfChildren J m c [] = S})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < S.card → bushOf S i c ∈ A i}) := by
    intro S _ T _ hST
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hST ?_
    rw [← hc.1.2]
    exact hc'.1.2
  have hmeas : ∀ S ∈ (childSet N J).powersetCard k,
      MeasurableSet (({c : Word N → ℕ | c [] = J} ∩ {c | retainedInfChildren J m c [] = S})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < S.card → bushOf S i c ∈ A i}) :=
    fun S _ ↦ ((measurableSet_coord_eq [] J).inter (measurableSet_retainedInfChildren_eq S)).inter
      (measurableSet_forall_bushOf S hA)
  have hterm : ∀ S ∈ (childSet N J).powersetCard k,
      sampleMeasure (N := N) θ
          (({c : Word N → ℕ | c [] = J} ∩ {c | retainedInfChildren J m c [] = S})
            ∩ {c : Word N → ℕ | ∀ i : ℕ, i < S.card → bushOf S i c ∈ A i})
        = ENNReal.ofReal (θ J)
          * (1 - sampleMeasure (N := N) θ {d : Word N → ℕ | RetainedInf J m d []}) ^ (J - k)
          * ∏ i ∈ Finset.range k,
              sampleMeasure (N := N) θ ({d : Word N → ℕ | RetainedInf J m d []} ∩ A i) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [sampleMeasure_root_retainedPattern_bushes θ hJN hS.1 hA, hS.2]
  rw [hdecomp, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hterm, Finset.sum_const,
    Finset.card_powersetCard, card_childSet hJN, nsmul_eq_mul]
  ring

/-! ### The law conditioned on a retained root, and the pruned law -/

variable (N)

/-- **The law conditioned on the root being retained.** -/
noncomputable def retainedMeasure (θ : Offspring J) (m : ℕ) : Measure (Word N → ℕ) :=
  ProbabilityTheory.cond (sampleMeasure (N := N) θ) {c : Word N → ℕ | RetainedInf J m c []}

variable {N}

lemma retainedMeasure_apply (t : Set (Word N → ℕ)) :
    retainedMeasure N θ m t
      = (sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []})⁻¹
        * sampleMeasure (N := N) θ ({c : Word N → ℕ | RetainedInf J m c []} ∩ t) :=
  ProbabilityTheory.cond_apply (measurableSet_retainedInf []) _ t

lemma isProbabilityMeasure_retainedMeasure
    (hp : sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []} ≠ 0) :
    IsProbabilityMeasure (retainedMeasure N θ m) :=
  ProbabilityTheory.cond_isProbabilityMeasure hp

/-- The unconditioned mass of a retained event is the retained probability times the
conditioned mass. -/
lemma sampleMeasure_retainedInf_inter
    (hp : sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []} ≠ 0)
    (t : Set (Word N → ℕ)) :
    sampleMeasure (N := N) θ ({c : Word N → ℕ | RetainedInf J m c []} ∩ t)
      = sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []}
        * retainedMeasure N θ m t := by
  rw [retainedMeasure_apply, ← mul_assoc, ENNReal.mul_inv_cancel hp (measure_ne_top _ _), one_mul]

namespace Offspring

/-- `ℙ(Bin(J, p) ≥ m) = ∑_{k ≥ m} C(J,k) p^k (1-p)^{J-k}`, as a real number. -/
noncomputable def binomialTailR (J m : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (J + 1)).filter (m ≤ ·), (J.choose k : ℝ) * p ^ k * (1 - p) ^ (J - k)

lemma binomialTailR_nonneg (J m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomialTailR J m p :=
  Finset.sum_nonneg fun k _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (by linarith) _)

/-- The tail is positive once `p > 0` and `m ≤ J`: the term `k = J` is `p^J`. -/
lemma binomialTailR_pos (J m : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hmJ : m ≤ J) :
    0 < binomialTailR J m p := by
  have hterm : (0 : ℝ) < (J.choose J : ℝ) * p ^ J * (1 - p) ^ (J - J) := by
    rw [Nat.choose_self, Nat.sub_self, pow_zero]
    simp only [Nat.cast_one, one_mul, mul_one]
    exact pow_pos hp0 J
  have hnn : ∀ k ∈ (Finset.range (J + 1)).filter (m ≤ ·),
      (0 : ℝ) ≤ (J.choose k : ℝ) * p ^ k * (1 - p) ^ (J - k) := fun k _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0.le _)) (pow_nonneg (by linarith) _)
  unfold binomialTailR
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum hnn (Finset.mem_filter.2 ⟨Finset.self_mem_range_succ J, hmJ⟩))

/-- The two binomial tails agree. -/
lemma binomialTail_ofReal (J m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialTail J m (ENNReal.ofReal p) = ENNReal.ofReal (binomialTailR J m p) := by
  rw [binomialTailR, binomialTail, ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)) (pow_nonneg (by linarith) _))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)),
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_pow hp0,
    ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_sub _ hp0, ENNReal.ofReal_one]

/-- The retained-root probability `p` as a real number. -/
noncomputable def retProbR (N : ℕ) (θ : Offspring J) (m : ℕ) : ℝ :=
  (sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []}).toReal

lemma ofReal_retProbR (θ : Offspring J) (m : ℕ) :
    ENNReal.ofReal (retProbR N θ m)
      = sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []} :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)

lemma retProbR_nonneg (θ : Offspring J) (m : ℕ) : 0 ≤ retProbR N θ m := ENNReal.toReal_nonneg

lemma retProbR_le_one (θ : Offspring J) (m : ℕ) : retProbR N θ m ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

/-- **The fixed point in real terms**: `p = θ_J ℙ(Bin(J, p) ≥ m)`. -/
lemma retProbR_eq (θ : Offspring J) (hJN : J ≤ N) (m : ℕ) :
    retProbR N θ m = θ J * binomialTailR J m (retProbR N θ m) := by
  have h := sampleMeasure_retainedInf_eq (m := m) N θ hJN
  rw [← ofReal_retProbR, binomialTail_ofReal J m (retProbR_nonneg θ m) (retProbR_le_one θ m),
    ← ENNReal.ofReal_mul (θ.nonneg J)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (retProbR_nonneg θ m)
    (mul_nonneg (θ.nonneg J) (binomialTailR_nonneg J m (retProbR_nonneg θ m)
      (retProbR_le_one θ m)))).1 h

/-- **The weights of the law of the retained tree**: the binomial law with parameters `J`
and `p` conditioned to be at least `m`. -/
noncomputable def prunedWeight (N : ℕ) (θ : Offspring J) (m k : ℕ) : ℝ :=
  if m ≤ k then
    (J.choose k : ℝ) * retProbR N θ m ^ k * (1 - retProbR N θ m) ^ (J - k)
      / binomialTailR J m (retProbR N θ m)
  else 0

/-- **The law of the retained descendant tree**, `eq:pruned-subtree-law`: the binomial law
with parameters `J` and `p` conditioned to be at least `m`, supported on `{m, …, J}`. -/
noncomputable def pruned (N : ℕ) (θ : Offspring J) (m : ℕ)
    (hZ : 0 < binomialTailR J m (retProbR N θ m)) : Offspring J where
  mass := prunedWeight N θ m
  nonneg k := by
    unfold prunedWeight
    split_ifs
    · have h0 := retProbR_nonneg (N := N) θ m
      have h1 := retProbR_le_one (N := N) θ m
      exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _))
        (pow_nonneg (by linarith) _)) hZ.le
    · exact le_rfl
  vanishing k hk := by
    unfold prunedWeight
    split_ifs
    · rw [Nat.choose_eq_zero_of_lt hk]
      simp
    · rfl
  total := by
    unfold prunedWeight
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_div, div_eq_one_iff_eq hZ.ne']
    rfl

@[simp] lemma pruned_apply (θ : Offspring J) (m : ℕ) (hZ : 0 < binomialTailR J m (retProbR N θ m))
    (k : ℕ) : pruned N θ m hZ k = prunedWeight N θ m k := rfl

/-- The law of the retained tree is supported on `{m, …, J}`. -/
lemma pruned_eq_zero_of_lt (θ : Offspring J) (m : ℕ) (hZ : 0 < binomialTailR J m (retProbR N θ m))
    {k : ℕ} (hk : k < m) : pruned N θ m hZ k = 0 := by
  rw [pruned_apply, prunedWeight, if_neg (by omega)]

end Offspring

/-- The scalar identity of the conditioned branching property, in real terms. -/
lemma prunedWeight_eq_of_le (θ : Offspring J) (hJN : J ≤ N) {k : ℕ} (hk : m ≤ k)
    (hp : 0 < Offspring.retProbR N θ m) :
    Offspring.prunedWeight N θ m k
      = (θ J * Offspring.binomialTailR J m (Offspring.retProbR N θ m))⁻¹
        * (θ J * ((J.choose k : ℝ)
          * ((1 - Offspring.retProbR N θ m) ^ (J - k) * Offspring.retProbR N θ m ^ k))) := by
  have hZ : θ J * Offspring.binomialTailR J m (Offspring.retProbR N θ m) ≠ 0 := by
    rw [← Offspring.retProbR_eq θ hJN m]
    exact hp.ne'
  have hθ : θ J ≠ 0 := left_ne_zero_of_mul hZ
  have hZ' : Offspring.binomialTailR J m (Offspring.retProbR N θ m) ≠ 0 := right_ne_zero_of_mul hZ
  rw [Offspring.prunedWeight, if_pos hk]
  field_simp
  try ring

/-- **The branching property of the retained tree at the root.**  Conditioned on the root
being retained, it has `k` retained children with probability `θ̂_k`, the binomial mass
conditioned to be at least `m`, and the `k` retained subtrees are independent copies of the
conditioned field. -/
theorem retainedMeasure_retDegree_bushes (hJN : J ≤ N)
    (hp : sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []} ≠ 0)
    (hZ : 0 < Offspring.binomialTailR J m (Offspring.retProbR N θ m)) (k : ℕ)
    {A : ℕ → Set (Word N → ℕ)} (hA : ∀ i, MeasurableSet (A i)) :
    retainedMeasure N θ m
        ({c : Word N → ℕ | retDegree J m c = k}
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i})
      = ENNReal.ofReal (Offspring.pruned N θ m hZ k)
        * ∏ i ∈ Finset.range k, retainedMeasure N θ m (A i) := by
  set R := {c : Word N → ℕ | RetainedInf J m c []} with hR
  set p := Offspring.retProbR N θ m with hpdef
  have hp0 : 0 ≤ p := Offspring.retProbR_nonneg θ m
  have hp1 : p ≤ 1 := Offspring.retProbR_le_one θ m
  have hPR : sampleMeasure (N := N) θ R = ENNReal.ofReal p := (Offspring.ofReal_retProbR θ m).symm
  have hppos : 0 < p := by
    rcases lt_or_eq_of_le hp0 with h | h
    · exact h
    · exact absurd (by rw [hPR, ← h, ENNReal.ofReal_zero]) hp
  rw [retainedMeasure_apply]
  by_cases hk : m ≤ k
  · have hset : R ∩ ({c : Word N → ℕ | retDegree J m c = k}
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i})
        = ({c : Word N → ℕ | c [] = J} ∩ {c | retDegree J m c = k})
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i} := by
      ext c
      simp only [hR, Set.mem_inter_iff, Set.mem_setOf_eq, retainedInf_iff]
      constructor
      · rintro ⟨⟨hroot, -⟩, hd, hbush⟩
        exact ⟨⟨hroot, hd⟩, hbush⟩
      · rintro ⟨⟨hroot, hd⟩, hbush⟩
        exact ⟨⟨hroot, by change m ≤ retDegree J m c; omega⟩, hd, hbush⟩
    rw [hset, sampleMeasure_root_retDegree_bushes θ hJN k hA,
      Finset.prod_congr rfl fun i _ ↦ sampleMeasure_retainedInf_inter θ hp (A i),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have hscalar : (sampleMeasure (N := N) θ R)⁻¹
        * (ENNReal.ofReal (θ J) * (J.choose k : ℝ≥0∞) * (1 - sampleMeasure (N := N) θ R) ^ (J - k)
          * sampleMeasure (N := N) θ R ^ k)
        = ENNReal.ofReal (Offspring.pruned N θ m hZ k) := by
      have h1p : (0 : ℝ) ≤ 1 - p := by linarith
      have h1 : (0 : ℝ) ≤ θ J * (J.choose k : ℝ) := mul_nonneg (θ.nonneg J) (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ θ J * (J.choose k : ℝ) * (1 - p) ^ (J - k) :=
        mul_nonneg h1 (pow_nonneg h1p _)
      rw [Offspring.pruned_apply, prunedWeight_eq_of_le θ hJN hk hppos, ← hpdef, hPR,
        ← ENNReal.ofReal_inv_of_pos hppos, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp0,
        ← ENNReal.ofReal_pow h1p, ← ENNReal.ofReal_pow hp0, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (θ.nonneg J), ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
        ← ENNReal.ofReal_mul (inv_nonneg.2 hp0)]
      congr 1
      rw [show p⁻¹ = (θ J * Offspring.binomialTailR J m p)⁻¹ by
        rw [← Offspring.retProbR_eq θ hJN m]]
      ring
    calc (sampleMeasure (N := N) θ R)⁻¹
          * (ENNReal.ofReal (θ J) * (J.choose k : ℝ≥0∞)
            * (1 - sampleMeasure (N := N) θ R) ^ (J - k)
            * (sampleMeasure (N := N) θ R ^ k * ∏ i ∈ Finset.range k, retainedMeasure N θ m (A i)))
        = ((sampleMeasure (N := N) θ R)⁻¹
            * (ENNReal.ofReal (θ J) * (J.choose k : ℝ≥0∞)
              * (1 - sampleMeasure (N := N) θ R) ^ (J - k) * sampleMeasure (N := N) θ R ^ k))
          * ∏ i ∈ Finset.range k, retainedMeasure N θ m (A i) := by ring
      _ = _ := by rw [hscalar]
  · have hset : R ∩ ({c : Word N → ℕ | retDegree J m c = k}
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i}) = ∅ := by
      ext c
      simp only [hR, Set.mem_inter_iff, Set.mem_setOf_eq, retainedInf_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hr hd
      exact absurd (hd ▸ hr.2) hk
    rw [hset, measure_empty, mul_zero, Offspring.pruned_eq_zero_of_lt θ m hZ (by omega),
      ENNReal.ofReal_zero, zero_mul]

/-- **The branching property with every retained subtree constrained**, for at least `n`
retained children: the sets above `n` impose nothing, so only the first `n` factors
survive. -/
theorem retainedMeasure_bushes (hJN : J ≤ N)
    (hp : sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []} ≠ 0)
    (hZ : 0 < Offspring.binomialTailR J m (Offspring.retProbR N θ m)) (n : ℕ)
    {A : ℕ → Set (Word N → ℕ)} (hA : ∀ i, MeasurableSet (A i))
    (hAtop : ∀ i : ℕ, n ≤ i → A i = Set.univ) :
    retainedMeasure N θ m
        ({c : Word N → ℕ | n ≤ retDegree J m c}
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < retDegree J m c → retAt J m c i ∈ A i})
      = ENNReal.ofReal ((Offspring.pruned N θ m hZ).tailGe n)
        * ∏ i ∈ Finset.range n, retainedMeasure N θ m (A i) := by
  have _ := isProbabilityMeasure_retainedMeasure θ hp
  have hge : MeasurableSet {c : Word N → ℕ | n ≤ retDegree J m c} :=
    measurable_retDegree measurableSet_Ici
  have hmeas : ∀ k : ℕ, MeasurableSet
      (({c : Word N → ℕ | n ≤ retDegree J m c} ∩ {c : Word N → ℕ | retDegree J m c = k})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i}) :=
    fun k ↦ (hge.inter (measurableSet_retDegree_eq k)).inter (measurableSet_forall_retAt k hA)
  have hdisj : Pairwise (Function.onFun Disjoint
      fun k : ℕ ↦ (({c : Word N → ℕ | n ≤ retDegree J m c}
        ∩ {c : Word N → ℕ | retDegree J m c = k})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i})) := by
    intro k l hkl
    refine Set.disjoint_left.mpr fun c hc hc' ↦ ?_
    exact hkl (hc.1.2.symm.trans hc'.1.2)
  have hdecomp : ({c : Word N → ℕ | n ≤ retDegree J m c}
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < retDegree J m c → retAt J m c i ∈ A i})
      = ⋃ k : ℕ, (({c : Word N → ℕ | n ≤ retDegree J m c}
        ∩ {c : Word N → ℕ | retDegree J m c = k})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i}) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hgec, hbush⟩
      exact ⟨retDegree J m c, ⟨hgec, rfl⟩, hbush⟩
    · rintro ⟨k, ⟨hgec, hd⟩, hbush⟩
      exact ⟨hgec, fun i hi ↦ hbush i (hd ▸ hi)⟩
  have hunit : ∀ i : ℕ, n ≤ i → retainedMeasure N θ m (A i) = 1 := by
    intro i hi
    rw [hAtop i hi, measure_univ]
  have hprodeq : ∀ k : ℕ, n ≤ k →
      ∏ i ∈ Finset.range k, retainedMeasure N θ m (A i)
        = ∏ i ∈ Finset.range n, retainedMeasure N θ m (A i) := by
    intro k hk
    refine (Finset.prod_subset (Finset.range_subset_range.mpr hk) fun i _ hin ↦ ?_).symm
    rw [Finset.mem_range, not_lt] at hin
    exact hunit i hin
  have hval : ∀ k : ℕ, retainedMeasure N θ m
      (({c : Word N → ℕ | n ≤ retDegree J m c} ∩ {c : Word N → ℕ | retDegree J m c = k})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i})
      = ENNReal.ofReal (if n ≤ k then Offspring.pruned N θ m hZ k else 0)
        * ∏ i ∈ Finset.range n, retainedMeasure N θ m (A i) := by
    intro k
    by_cases hk : n ≤ k
    · have hset : (({c : Word N → ℕ | n ≤ retDegree J m c}
          ∩ {c : Word N → ℕ | retDegree J m c = k})
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i})
          = {c : Word N → ℕ | retDegree J m c = k}
            ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i} := by
        ext c
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨-, hd⟩, hbush⟩
          exact ⟨hd, hbush⟩
        · rintro ⟨hd, hbush⟩
          exact ⟨⟨by rw [hd]; exact hk, hd⟩, hbush⟩
      rw [hset, retainedMeasure_retDegree_bushes θ hJN hp hZ k hA, if_pos hk, hprodeq k hk]
    · have hset : (({c : Word N → ℕ | n ≤ retDegree J m c}
          ∩ {c : Word N → ℕ | retDegree J m c = k})
          ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i})
          = (∅ : Set (Word N → ℕ)) := by
        ext c
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hgec, hd⟩, -⟩
        exact hk (hd ▸ hgec)
      rw [hset, measure_empty, if_neg hk, ENNReal.ofReal_zero, zero_mul]
  have hvanish : ∀ k ∉ Finset.range (J + 1), retainedMeasure N θ m
      (({c : Word N → ℕ | n ≤ retDegree J m c} ∩ {c : Word N → ℕ | retDegree J m c = k})
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < k → retAt J m c i ∈ A i}) = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hval k]
    by_cases hnk : n ≤ k
    · rw [if_pos hnk, (Offspring.pruned N θ m hZ).vanishing k (by omega), ENNReal.ofReal_zero,
        zero_mul]
    · rw [if_neg hnk, ENNReal.ofReal_zero, zero_mul]
  have hnn : ∀ k ∈ Finset.range (J + 1),
      (0 : ℝ) ≤ if n ≤ k then Offspring.pruned N θ m hZ k else 0 := by
    intro k _
    split
    · exact (Offspring.pruned N θ m hZ).nonneg k
    · exact le_rfl
  rw [hdecomp, measure_iUnion hdisj hmeas, tsum_eq_sum hvanish,
    Finset.sum_congr rfl fun k _ ↦ hval k, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg hnn,
    Offspring.tailGe]

/-! ### The retained tree is a Galton-Watson tree -/

/-- **The one-step criterion for containment in the retained tree.** -/
lemma subset_retTree_iff {F : Set (Word N)} (hF : PrefixClosed F) (c : Word N → ℕ) :
    F ⊆ (retTree J m c : Set (Word N)) ↔ rootDeg F ≤ retDegree J m c
      ∧ ∀ i : ℕ, i < retDegree J m c →
          wordSub F i ⊆ (retTree J m (retAt J m c i) : Set (Word N)) := by
  constructor
  · intro h
    refine ⟨rootDeg_le_iff.mpr fun i hi ↦ (mem_retTree_cons.mp (h hi)).1, ?_⟩
    rintro i - u ⟨j, rfl, hmem⟩
    exact (mem_retTree_cons.mp (h hmem)).2
  · rintro ⟨hdeg, hsub⟩ v hv
    cases v with
    | nil => exact nil_mem_retTree c
    | cons j u =>
        have hroot : [j] ∈ F := hF hv (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
        have hlt : (j : ℕ) < retDegree J m c := lt_of_lt_of_le (lt_rootDeg hroot) hdeg
        exact mem_retTree_cons.mpr ⟨hlt, hsub (j : ℕ) hlt (mem_wordSub.mpr hv)⟩

/-- Containment in the retained tree is a measurable event. -/
lemma measurableSet_subset_retTree (G : Set (Word N)) :
    MeasurableSet {c : Word N → ℕ | G ⊆ (retTree J m c : Set (Word N))} := by
  have h : {c : Word N → ℕ | G ⊆ (retTree J m c : Set (Word N))}
      = ⋂ v ∈ G, {c : Word N → ℕ | v ∈ retTree J m c} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.subset_def, SetLike.mem_coe]
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable G) fun v _ ↦ measurableSet_mem_retTree v

/-- **The recursion for the retained tree.**  Conditioned on a retained root, the root must
have enough retained children to carry the demand of `F`, and the retained subtrees must
carry the residual sets, independently. -/
theorem retainedMeasure_subset_retTree_step (hJN : J ≤ N)
    (hp : sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []} ≠ 0)
    (hZ : 0 < Offspring.binomialTailR J m (Offspring.retProbR N θ m)) {F : Set (Word N)}
    (hF : PrefixClosed F) :
    retainedMeasure N θ m {c : Word N → ℕ | F ⊆ (retTree J m c : Set (Word N))}
      = ENNReal.ofReal ((Offspring.pruned N θ m hZ).tailGe (rootDeg F))
        * ∏ i ∈ Finset.range (rootDeg F), retainedMeasure N θ m
            {d : Word N → ℕ | wordSub F i ⊆ (retTree J m d : Set (Word N))} := by
  have hA : ∀ i : ℕ,
      MeasurableSet {d : Word N → ℕ | wordSub F i ⊆ (retTree J m d : Set (Word N))} :=
    fun i ↦ measurableSet_subset_retTree (wordSub F i)
  have hAtop : ∀ i : ℕ, rootDeg F ≤ i →
      {d : Word N → ℕ | wordSub F i ⊆ (retTree J m d : Set (Word N))} = Set.univ := by
    intro i hi
    rw [wordSub_eq_empty hF hi]
    ext d
    simp
  have hset : {c : Word N → ℕ | F ⊆ (retTree J m c : Set (Word N))}
      = {c : Word N → ℕ | rootDeg F ≤ retDegree J m c}
        ∩ {c : Word N → ℕ | ∀ i : ℕ, i < retDegree J m c →
            retAt J m c i ∈ {d : Word N → ℕ | wordSub F i ⊆ (retTree J m d : Set (Word N))}} := by
    ext c
    rw [Set.mem_setOf_eq, subset_retTree_iff hF c]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [hset, retainedMeasure_bushes θ hJN hp hZ (rootDeg F) hA hAtop]

/-- **The retained tree is a Galton-Watson tree with the pruned law, on every finite
prefix-closed set of words.**  Both sides satisfy the same recursion, the retained one by
`retainedMeasure_subset_retTree_step` and the sample one by
`sampleMeasure_subset_sample_step`, so the induction on the height of `F` closes. -/
theorem retainedMeasure_subset_retTree (hJN : J ≤ N)
    (hp : sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []} ≠ 0)
    (hZ : 0 < Offspring.binomialTailR J m (Offspring.retProbR N θ m)) :
    ∀ (n : ℕ) (F : Set (Word N)), PrefixClosed F → (∀ v ∈ F, v.length ≤ n) →
      retainedMeasure N θ m {c : Word N → ℕ | F ⊆ (retTree J m c : Set (Word N))}
        = sampleMeasure (N := N) (Offspring.pruned N θ m hZ)
            {c : Word N → ℕ | F ⊆ (sample c : Set (Word N))} := by
  have _ := isProbabilityMeasure_retainedMeasure θ hp
  intro n
  induction n with
  | zero =>
      intro F _ hn
      have hnil : ∀ v ∈ F, v = ([] : Word N) := by
        intro v hv
        exact List.length_eq_zero_iff.mp (Nat.le_zero.mp (hn v hv))
      have h1 : {c : Word N → ℕ | F ⊆ (retTree J m c : Set (Word N))} = Set.univ := by
        ext c
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro v hv
        rw [hnil v hv]
        exact nil_mem_retTree c
      have h2 : {c : Word N → ℕ | F ⊆ (sample c : Set (Word N))} = Set.univ := by
        ext c
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro v hv
        rw [hnil v hv]
        exact nil_mem_sample c
      rw [h1, h2, measure_univ, measure_univ]
  | succ n ih =>
      intro F hF hn
      have hterm : ∀ i : ℕ,
          retainedMeasure N θ m {d : Word N → ℕ | wordSub F i ⊆ (retTree J m d : Set (Word N))}
            = sampleMeasure (N := N) (Offspring.pruned N θ m hZ)
              {d : Word N → ℕ | wordSub F i ⊆ (sample d : Set (Word N))} :=
        fun i ↦ ih (wordSub F i) (hF.wordSub i) fun u hu ↦ length_le_of_mem_wordSub hn hu
      have hunit : ∀ i : ℕ, rootDeg F ≤ i →
          sampleMeasure (N := N) (Offspring.pruned N θ m hZ)
            {d : Word N → ℕ | wordSub F i ⊆ (sample d : Set (Word N))} = 1 := by
        intro i hi
        rw [wordSub_eq_empty hF hi]
        have hset : {d : Word N → ℕ | (∅ : Set (Word N)) ⊆ (sample d : Set (Word N))}
            = Set.univ := by
          ext d
          simp
        rw [hset, measure_univ]
      rw [retainedMeasure_subset_retTree_step θ hJN hp hZ hF,
        sampleMeasure_subset_sample_step (Offspring.pruned N θ m hZ) hF,
        Finset.prod_congr rfl fun i _ ↦ hterm i]
      congr 1
      rw [Fin.prod_univ_eq_prod_range (fun i ↦ sampleMeasure (N := N) (Offspring.pruned N θ m hZ)
        {d : Word N → ℕ | wordSub F i ⊆ (sample d : Set (Word N))}) N]
      refine Finset.prod_subset (Finset.range_subset_range.mpr (rootDeg_le_card F)) ?_
      intro i _ hin
      rw [Finset.mem_range, not_lt] at hin
      exact hunit i hin

/-- **The law of the retained descendant tree**: the law of the re-addressed retained tree of
the root, conditioned on the root being retained. -/
noncomputable def retainedTreeLaw (N : ℕ) (θ : Offspring J) (m : ℕ) : Measure (Subtree N) :=
  (retainedMeasure N θ m).map (retTree J m)

/-- **`thm:concentrated-regular-subtree`, the Galton-Watson assertion.**  Conditioned on the
root being retained, its retained descendant tree is a Galton-Watson tree whose offspring law
is the binomial law with parameters `J` and `p` conditioned to be at least `m`, supported on
`{m, …, J}`.  The two laws agree on the containment π-system generating the measurable
structure on subtrees. -/
theorem retainedTreeLaw_eq_treeLaw (hJN : J ≤ N)
    (hp : sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J m c []} ≠ 0)
    (hZ : 0 < Offspring.binomialTailR J m (Offspring.retProbR N θ m)) :
    retainedTreeLaw N θ m = treeLaw (N := N) (Offspring.pruned N θ m hZ) := by
  have _ := isProbabilityMeasure_retainedMeasure θ hp
  have hprob : IsProbabilityMeasure (retainedTreeLaw N θ m) := by
    rw [retainedTreeLaw]
    exact Measure.isProbabilityMeasure_map measurable_retTree.aemeasurable
  refine ext_of_generate_finite (containmentSets N) generateFrom_containmentSets
    isPiSystem_containmentSets ?_ ?_
  · rintro _ ⟨F, hFfin, hF, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ v ∈ F, v.length ≤ n := by
      obtain ⟨n, hn⟩ := (hFfin.image fun v : Word N ↦ v.length).bddAbove
      exact ⟨n, fun v hv ↦ hn ⟨v, hv, rfl⟩⟩
    rw [retainedTreeLaw, Measure.map_apply measurable_retTree (measurableSet_subset_subtree F),
      treeLaw, Measure.map_apply measurable_sample (measurableSet_subset_subtree F)]
    exact retainedMeasure_subset_retTree θ hJN hp hZ n F hF hn
  · rw [measure_univ, measure_univ]

/-- **`thm:concentrated-regular-subtree`, the Galton-Watson assertion under its hypotheses**:
for `J ≥ 24`, `θ_J ≥ 7/8` and `m = ⌊J/2⌋ + 1`, the root is retained with positive
probability and the pruned law is defined, and the retained descendant tree is a
Galton-Watson tree with that law. -/
theorem retainedTreeLaw_eq_treeLaw_of_concentrated (hJN : J ≤ N) (hJ : 24 ≤ J)
    (hθJ : 7 / 8 ≤ θ J) :
    ∃ hZ : 0 < Offspring.binomialTailR J (J / 2 + 1) (Offspring.retProbR N θ (J / 2 + 1)),
      retainedTreeLaw N θ (J / 2 + 1) = treeLaw (N := N) (Offspring.pruned N θ (J / 2 + 1) hZ) := by
  have hp : ENNReal.ofReal (4 / 5)
      ≤ sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J (J / 2 + 1) c []} :=
    ofReal_le_sampleMeasure_retainedInf θ hJN hJ hθJ
  have hp' : sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J (J / 2 + 1) c []} ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) hp).ne'
  have hpr : 0 < Offspring.retProbR N θ (J / 2 + 1) := by
    rcases lt_or_eq_of_le (Offspring.retProbR_nonneg θ (J / 2 + 1)) with h | h
    · exact h
    · exact absurd (by rw [← Offspring.ofReal_retProbR, ← h, ENNReal.ofReal_zero]) hp'
  have hZ := Offspring.binomialTailR_pos J (J / 2 + 1) hpr (Offspring.retProbR_le_one θ _)
    (by omega)
  exact ⟨hZ, retainedTreeLaw_eq_treeLaw θ hJN hp' hZ⟩

end Law

end BranchingProcess
