/-
`thm:harris`\labelcref{it:harris-bushes} of `matching_classes_simple.tex` in its joint
form: the surviving and the dying subtrees of one root at once.

`Skeleton` constrains the surviving subtrees (`survivalMeasure_bushes`, through
`bushesBox`) and, under the conditioning on extinction, the dying ones
(`bushMeasure_dying`, through `dyingBox`).  A decorated neck vertex asks for both at
once: its surviving child founds the rest of the chain and its dying child founds the
bush hanging there.  The route is the one of `bushesBox`: a product event over the
blocks of the splitting, its preimage identified vertex by vertex, and the mass read off
the product measure.  The surviving branches are indexed by their rank among the
survivors, as `rankOf` does, the dying ones by their letter.

* `dyingOnly`, `split_preimage_dyingOnly`: the extra factors constraining the dying
  subtrees.
* `jointBox`, `jointBox_eq_inter`, `split_preimage_jointBox`: **the joint product
  event**, the survival pattern together with both families of subtrees.
* `prod_ite_joint`: the product over the letters of a factor indexed by the rank at a
  surviving child and by the letter at a dying one.
* `sampleMeasure_root_joint`: **the mass of a survival pattern with both families
  constrained**, a conditioned factor per surviving subtree and a bush factor per dying
  one.
* `sampleMeasure_root_one_survivor` and `survivalMeasure_root_one_survivor`: **the neck
  step**, one surviving child out of `j`, which is the case the shapes of
  `thm:shape-iid` are built from; the surviving child can be any of the `j` letters,
  which is the factor `j` in the weight `θ_j j q^{j-1}`.
-/
import BranchingProcess.Skeleton

namespace BranchingProcess

open MeasureTheory ProbabilityTheory ENNReal

variable {J N : ℕ}

/-! ### Constraining the dying subtrees alongside the surviving ones -/

/-- The extra factors constraining the dying subtrees: a letter naming a child outside
the surviving pattern carries the set indexed by that letter, and the letters naming no
child carry nothing. -/
def dyingOnly (j : ℕ) (S : Finset (Fin N)) (B : ℕ → Set (Word N → ℕ)) :
    (i : Option (Fin N)) → Set (Branch N i → ℕ)
  | none => Set.univ
  | some i => if i ∈ S then Set.univ else if (i : ℕ) < j then B (i : ℕ) else Set.univ

@[simp] lemma dyingOnly_none (j : ℕ) (S : Finset (Fin N)) (B : ℕ → Set (Word N → ℕ)) :
    dyingOnly (N := N) j S B none = Set.univ := rfl

@[simp] lemma dyingOnly_some (j : ℕ) (S : Finset (Fin N)) (B : ℕ → Set (Word N → ℕ))
    (i : Fin N) :
    dyingOnly j S B (some i)
      = if i ∈ S then Set.univ else if (i : ℕ) < j then B (i : ℕ) else Set.univ := rfl

/-- The extra factors, read through the splitting. -/
lemma split_preimage_dyingOnly (j : ℕ) (S : Finset (Fin N)) (B : ℕ → Set (Word N → ℕ)) :
    split ⁻¹' Set.univ.pi (dyingOnly (N := N) j S B)
      = {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
          (fun w : Word N ↦ c (i :: w)) ∈ B (i : ℕ)} := by
  ext c
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq]
  constructor
  · intro h i hiS hij
    have hval := h (some i)
    rw [dyingOnly_some, ite_eq_right hiS, ite_eq_left hij] at hval
    exact hval
  · intro h i
    cases i with
    | none => exact Set.mem_univ _
    | some i =>
        rw [dyingOnly_some]
        by_cases hiS : i ∈ S
        · rw [ite_eq_left hiS]
          exact Set.mem_univ _
        · rw [ite_eq_right hiS]
          by_cases hij : (i : ℕ) < j
          · rw [ite_eq_left hij]
            exact h i hiS hij
          · rw [ite_eq_right hij]
            exact Set.mem_univ _

/-- **The joint product event**: the root has `j` children, those named by `S` found
infinite subtrees and lie in the sets indexed by their rank, and the remaining children
die and lie in the sets indexed by their letter. -/
def jointBox (j : ℕ) (S : Finset (Fin N)) (A B : ℕ → Set (Word N → ℕ)) :
    (i : Option (Fin N)) → Set (Branch N i → ℕ)
  | none => {u | u rootIdx = j}
  | some i =>
      if i ∈ S then {c : Word N → ℕ | Survives c} ∩ A (rankOf S i)
      else if (i : ℕ) < j then {c : Word N → ℕ | ¬ Survives c} ∩ B (i : ℕ) else Set.univ

@[simp] lemma jointBox_none (j : ℕ) (S : Finset (Fin N)) (A B : ℕ → Set (Word N → ℕ)) :
    jointBox j S A B none = {u : Branch N none → ℕ | u rootIdx = j} := rfl

@[simp] lemma jointBox_some (j : ℕ) (S : Finset (Fin N)) (A B : ℕ → Set (Word N → ℕ))
    (i : Fin N) :
    jointBox j S A B (some i)
      = if i ∈ S then {c : Word N → ℕ | Survives c} ∩ A (rankOf S i)
        else if (i : ℕ) < j then {c : Word N → ℕ | ¬ Survives c} ∩ B (i : ℕ)
        else Set.univ := rfl

lemma measurableSet_jointBox (j : ℕ) (S : Finset (Fin N)) {A B : ℕ → Set (Word N → ℕ)}
    (hA : ∀ m, MeasurableSet (A m)) (hB : ∀ m, MeasurableSet (B m)) (i : Option (Fin N)) :
    MeasurableSet (jointBox (N := N) j S A B i) := by
  cases i with
  | none =>
      exact measurableSet_rootIdx_preimage {j}
  | some i =>
      rw [jointBox_some]
      split
      · exact measurableSet_survives.inter (hA _)
      · split
        · exact measurableSet_survives.compl.inter (hB _)
        · exact MeasurableSet.univ

/-- The three product events cut out the joint one. -/
lemma jointBox_eq_inter (j : ℕ) (S : Finset (Fin N)) (A B : ℕ → Set (Word N → ℕ))
    (i : Option (Fin N)) :
    jointBox j S A B i = skelBox j S i ∩ bushesOnly S A i ∩ dyingOnly j S B i := by
  cases i with
  | none =>
      ext u
      simp [jointBox, skelBox, bushesOnly, dyingOnly]
  | some i =>
      ext c
      by_cases hi : i ∈ S
      · simp [jointBox, skelBox, bushesOnly, dyingOnly, hi]
      · by_cases hij : (i : ℕ) < j
        · simp [jointBox, skelBox, bushesOnly, dyingOnly, hi, hij]
        · simp [jointBox, skelBox, bushesOnly, dyingOnly, hi, hij]

/-- **The joint product event constrains both families of subtrees.** -/
lemma split_preimage_jointBox {j : ℕ} {S : Finset (Fin N)} (hS : S ⊆ childSet N j)
    (A B : ℕ → Set (Word N → ℕ)) :
    split ⁻¹' Set.univ.pi (jointBox (N := N) j S A B)
      = (({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
          ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A m})
        ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
            (fun w : Word N ↦ c (i :: w)) ∈ B (i : ℕ)} := by
  have hbox : Set.univ.pi (jointBox (N := N) j S A B)
      = (Set.univ.pi (skelBox (N := N) j S) ∩ Set.univ.pi (bushesOnly (N := N) S A))
        ∩ Set.univ.pi (dyingOnly (N := N) j S B) := by
    rw [← Set.pi_inter_distrib, ← Set.pi_inter_distrib]
    exact Set.pi_congr rfl fun i _ ↦ jointBox_eq_inter j S A B i
  rw [hbox, Set.preimage_inter, Set.preimage_inter, split_preimage_skelBox j S hS,
    split_preimage_bushesOnly, split_preimage_dyingOnly]
  ext c
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, forall_bushOf_iff S A c]

/-- **The product over the children of a root with `j` children** of a factor indexed by
the rank at a surviving child, by the letter at a dying one, and trivial at a letter
naming no child. -/
lemma prod_ite_joint {j : ℕ} {S : Finset (Fin N)} (hS : S ⊆ childSet N j)
    (X : ℕ → ℝ≥0∞) (Y : Fin N → ℝ≥0∞) :
    ∏ i : Fin N, (if i ∈ S then X (rankOf S i) else if (i : ℕ) < j then Y i else 1)
      = (∏ m ∈ Finset.range S.card, X m) * ∏ i ∈ childSet N j \ S, Y i := by
  classical
  set f : Fin N → ℝ≥0∞ :=
    fun i ↦ if i ∈ S then X (rankOf S i) else if (i : ℕ) < j then Y i else 1 with hf
  have houter : ∏ i ∈ Finset.univ \ childSet N j, f i = 1 := by
    refine Finset.prod_eq_one fun i hi ↦ ?_
    rw [Finset.mem_sdiff, mem_childSet] at hi
    have hiS : i ∉ S := fun hc ↦ hi.2 (mem_childSet.mp (hS hc))
    rw [hf]
    simp only
    rw [ite_eq_right hiS, ite_eq_right hi.2]
  have hdying : ∏ i ∈ childSet N j \ S, f i = ∏ i ∈ childSet N j \ S, Y i := by
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_sdiff, mem_childSet] at hi
    rw [hf]
    simp only
    rw [ite_eq_right hi.2, ite_eq_left hi.1]
  have hsurv : ∏ i ∈ S, f i = ∏ m ∈ Finset.range S.card, X m := by
    have hfac : ∀ i ∈ S, f i = X (rankOf S i) := by
      intro i hi
      rw [hf]
      simp only
      rw [ite_eq_left hi]
    rw [Finset.prod_congr rfl hfac, prod_rankOf]
  rw [← Finset.prod_sdiff (Finset.subset_univ (childSet N j)), houter, one_mul,
    ← Finset.prod_sdiff hS, hdying, hsurv]
  ring

/-- **The mass of a survival pattern with both families of subtrees constrained.**  The
splitting makes the subtrees independent: a surviving one contributes the conditioned
mass of the set of its rank, a dying one the bush mass of the set of its letter. -/
theorem sampleMeasure_root_joint (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) {j : ℕ} (hj : j ≤ N) {S : Finset (Fin N)}
    (hS : S ⊆ childSet N j) {A B : ℕ → Set (Word N → ℕ)} (hA : ∀ m, MeasurableSet (A m))
    (hB : ∀ m, MeasurableSet (B m)) :
    sampleMeasure (N := N) θ
        ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
            ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A m})
          ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
              (fun w : Word N ↦ c (i :: w)) ∈ B (i : ℕ)})
      = ENNReal.ofReal (θ j) * ENNReal.ofReal (1 - θ.extinction) ^ S.card
          * ENNReal.ofReal θ.extinction ^ (j - S.card)
          * (∏ m ∈ Finset.range S.card, survivalMeasure θ (A m))
          * ∏ i ∈ childSet N j \ S, bushMeasure θ (B (i : ℕ)) := by
  have hprod : ∏ i : Fin N, Measure.infinitePi (fun _ : Branch N (some i) ↦ θ.law)
        (jointBox (N := N) j S A B (some i))
      = ENNReal.ofReal (1 - θ.extinction) ^ S.card
          * ENNReal.ofReal θ.extinction ^ (j - S.card)
          * (∏ m ∈ Finset.range S.card, survivalMeasure θ (A m))
          * ∏ i ∈ childSet N j \ S, bushMeasure θ (B (i : ℕ)) := by
    have hfac : ∀ i : Fin N, Measure.infinitePi (fun _ : Branch N (some i) ↦ θ.law)
        (jointBox (N := N) j S A B (some i))
        = (if i ∈ S then
              ENNReal.ofReal (1 - θ.extinction) * survivalMeasure (N := N) θ (A (rankOf S i))
            else if (i : ℕ) < j then
              ENNReal.ofReal θ.extinction * bushMeasure (N := N) θ (B (i : ℕ)) else 1) := by
      intro i
      rw [jointBox_some]
      by_cases hiS : i ∈ S
      · rw [ite_eq_left hiS, ite_eq_left hiS]
        exact (infinitePi_branch_some θ i _).trans
          (sampleMeasure_survives_inter θ hJN hq (A (rankOf S i)))
      · rw [ite_eq_right hiS, ite_eq_right hiS]
        by_cases hij : (i : ℕ) < j
        · rw [ite_eq_left hij, ite_eq_left hij]
          exact (infinitePi_branch_some θ i _).trans
            (sampleMeasure_notSurvives_inter θ hJN hq0 (B (i : ℕ)))
        · rw [ite_eq_right hij, ite_eq_right hij]
          exact (infinitePi_branch_some θ i Set.univ).trans measure_univ
    rw [Finset.prod_congr rfl fun i _ ↦ hfac i,
      prod_ite_joint hS
        (fun m ↦ ENNReal.ofReal (1 - θ.extinction) * survivalMeasure (N := N) θ (A m))
        (fun i ↦ ENNReal.ofReal θ.extinction * bushMeasure (N := N) θ (B (i : ℕ))),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      Finset.card_range, Finset.card_sdiff_of_subset hS, card_childSet hj]
    ring
  rw [← split_preimage_jointBox hS A B, ← Measure.map_apply measurable_split
      (MeasurableSet.univ_pi (measurableSet_jointBox j S hA hB)), map_split, ← Finset.coe_univ,
    Measure.infinitePi_pi _ (fun i _ ↦ measurableSet_jointBox j S hA hB i), Fintype.prod_option,
    jointBox_none, infinitePi_root_apply θ j, hprod]
  ring

/-! ### One surviving child -/

/-- The dying constraint is an event: one condition per letter. -/
lemma measurableSet_forall_dying (j : ℕ) (S : Finset (Fin N)) {B : Set (Word N → ℕ)}
    (hB : MeasurableSet B) :
    MeasurableSet {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
      (fun w : Word N ↦ c (i :: w)) ∈ B} := by
  have h : {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
        (fun w : Word N ↦ c (i :: w)) ∈ B}
      = ⋂ i : Fin N, ⋂ _ : i ∉ S, ⋂ _ : (i : ℕ) < j,
          (fun c : Word N → ℕ ↦ (fun w : Word N ↦ c (i :: w))) ⁻¹' B := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
    MeasurableSet.iInter fun _ ↦ measurable_shift i hB

/-- **The neck step of `thm:harris`**: the root has `j` children of which exactly one
survives, its subtree lying in `A` and every dying subtree in `B`.  The surviving child
can be any of the `j` letters, which is the factor `j`. -/
theorem sampleMeasure_root_one_survivor (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) {j : ℕ} (hj : j ≤ N)
    {A B : Set (Word N → ℕ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    sampleMeasure (N := N) θ
        ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = 1})
            ∩ {c : Word N → ℕ | bushAt c 0 ∈ A})
          ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ survivors c → (i : ℕ) < j →
              (fun w : Word N ↦ c (i :: w)) ∈ B})
      = ENNReal.ofReal (θ j * j * (1 - θ.extinction) * θ.extinction ^ (j - 1))
          * survivalMeasure θ A * bushMeasure θ B ^ (j - 1) := by
  classical
  have hdecomp : ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = 1})
        ∩ {c : Word N → ℕ | bushAt c 0 ∈ A})
      ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ survivors c → (i : ℕ) < j →
          (fun w : Word N ↦ c (i :: w)) ∈ B})
      = ⋃ S ∈ (childSet N j).powersetCard 1,
          ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
              ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A})
            ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
                (fun w : Word N ↦ c (i :: w)) ∈ B}) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_powersetCard,
      exists_prop]
    constructor
    · rintro ⟨⟨⟨hroot, hdeg⟩, hbush⟩, hdying⟩
      refine ⟨survivors c, ⟨?_, hdeg⟩, ⟨⟨hroot, rfl⟩, ?_⟩, hdying⟩
      · rw [← hroot]
        exact survivors_subset c
      · intro m hm
        rw [skeletonDegree_eq_card, hdeg] at *
        have hm0 : m = 0 := by omega
        rw [hm0]
        exact hbush
    · rintro ⟨S, ⟨-, hcard⟩, ⟨⟨hroot, rfl⟩, hbush⟩, hdying⟩
      refine ⟨⟨⟨hroot, ?_⟩, ?_⟩, hdying⟩
      · rw [skeletonDegree_eq_card, hcard]
      · exact hbush 0 (by rw [hcard]; omega)
  have hdisj : ((childSet N j).powersetCard 1 : Set (Finset (Fin N))).PairwiseDisjoint
      (fun S ↦ (({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
          ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A})
        ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
            (fun w : Word N ↦ c (i :: w)) ∈ B}) := by
    intro S _ T _ hST
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hST ?_
    rw [← hc.1.1.2]
    exact hc'.1.1.2
  have hmeas : ∀ S ∈ (childSet N j).powersetCard 1,
      MeasurableSet ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
          ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A})
        ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
            (fun w : Word N ↦ c (i :: w)) ∈ B}) := fun S _ ↦
    (((measurableSet_root_eq j).inter (measurableSet_survivors_eq S)).inter
      (measurableSet_forall_bushOf S fun _ ↦ hA)).inter (measurableSet_forall_dying j S hB)
  have hterm : ∀ S ∈ (childSet N j).powersetCard 1,
      sampleMeasure (N := N) θ
          ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | survivors c = S})
              ∩ {c : Word N → ℕ | ∀ m : ℕ, m < S.card → bushOf S m c ∈ A})
            ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ S → (i : ℕ) < j →
                (fun w : Word N ↦ c (i :: w)) ∈ B})
        = ENNReal.ofReal (θ j) * ENNReal.ofReal (1 - θ.extinction)
            * ENNReal.ofReal θ.extinction ^ (j - 1)
            * survivalMeasure θ A * bushMeasure θ B ^ (j - 1) := by
    intro S hSmem
    rw [Finset.mem_powersetCard] at hSmem
    rw [sampleMeasure_root_joint θ hJN hq hq0 hj hSmem.1 (fun _ ↦ hA) (fun _ ↦ hB), hSmem.2,
      Finset.prod_range_one, Finset.prod_const, Finset.card_sdiff_of_subset hSmem.1,
      card_childSet hj, hSmem.2]
    ring
  have hnn1 : (0 : ℝ) ≤ 1 - θ.extinction := by linarith [θ.extinction_le_one]
  have hnn2 : (0 : ℝ) ≤ θ j * j := mul_nonneg (θ.nonneg j) (Nat.cast_nonneg _)
  have hnn3 : (0 : ℝ) ≤ θ j * j * (1 - θ.extinction) := mul_nonneg hnn2 hnn1
  rw [hdecomp, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hterm,
    Finset.sum_const, Finset.card_powersetCard, card_childSet hj, Nat.choose_one_right,
    nsmul_eq_mul, ENNReal.ofReal_mul hnn3, ENNReal.ofReal_mul hnn2,
    ENNReal.ofReal_mul (θ.nonneg j), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow θ.extinction_nonneg]
  ring

/-- **The neck step under the conditioned law**: the same event, conditioned on
survival, its mass the reduced weight `θ_j j q^{j-1}` times the conditioned mass of the
surviving subtree and the bush masses of the dying ones. -/
theorem survivalMeasure_root_one_survivor (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) {j : ℕ} (hj : j ≤ N)
    {A B : Set (Word N → ℕ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    survivalMeasure (N := N) θ
        ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = 1})
            ∩ {c : Word N → ℕ | bushAt c 0 ∈ A})
          ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ survivors c → (i : ℕ) < j →
              (fun w : Word N ↦ c (i :: w)) ∈ B})
      = ENNReal.ofReal (θ j * j * θ.extinction ^ (j - 1))
          * survivalMeasure θ A * bushMeasure θ B ^ (j - 1) := by
  have hnn : (0 : ℝ) ≤ 1 - θ.extinction := by linarith [θ.extinction_le_one]
  have hne : ENNReal.ofReal (1 - θ.extinction) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hsurv : {c : Word N → ℕ | Survives c}
      ∩ ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = 1})
            ∩ {c : Word N → ℕ | bushAt c 0 ∈ A})
          ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ survivors c → (i : ℕ) < j →
              (fun w : Word N ↦ c (i :: w)) ∈ B})
      = ((({c : Word N → ℕ | c [] = j} ∩ {c : Word N → ℕ | skeletonDegree c = 1})
            ∩ {c : Word N → ℕ | bushAt c 0 ∈ A})
          ∩ {c : Word N → ℕ | ∀ i : Fin N, i ∉ survivors c → (i : ℕ) < j →
              (fun w : Word N ↦ c (i :: w)) ∈ B}) := by
    refine Set.inter_eq_right.mpr fun c hc ↦ ?_
    refine survives_iff_skeletonDegree_ne_zero.mpr ?_
    rw [show skeletonDegree c = 1 from hc.1.1.2]
    omega
  have hfac : ENNReal.ofReal (θ j * j * (1 - θ.extinction) * θ.extinction ^ (j - 1))
      = ENNReal.ofReal (1 - θ.extinction)
        * ENNReal.ofReal (θ j * j * θ.extinction ^ (j - 1)) := by
    rw [← ENNReal.ofReal_mul hnn]
    congr 1
    ring
  rw [survivalMeasure_apply, hsurv,
    sampleMeasure_root_one_survivor θ hJN hq hq0 hj hA hB, sampleMeasure_survives θ hJN, hfac]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top,
    one_mul]

end BranchingProcess
