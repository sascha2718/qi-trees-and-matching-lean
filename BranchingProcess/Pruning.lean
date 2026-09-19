/-
`thm:concentrated-regular-subtree` of `quasi_isometric_embeddings.tex`: pruning a
Galton-Watson tree whose offspring law is concentrated at a large arity `J` leaves,
with probability at least `3/4`, an infinite subtree in which every vertex keeps at
least `m = ⌊J/2⌋ + 1` children, and hence an isometric copy of the binary tree.

The pruning rounds `V_n` are defined on the whole ambient tree from the offspring
field, including at words outside the sample.  A vertex survives round `n + 1` when it
has offspring count `J` and at least `m` of its first `J` children survived round
`n`; the rounds decrease, and the vertices surviving every round are the retained
ones.  The retained vertices in the sample have at least `m` retained children in the
sample, which is what the binary subtree is read off.

The probabilistic content is the lower bound `p_n ≥ 4/5` on the probability that the
root survives `n` rounds.  The recursion of the paper is
`p_{n+1} = θ_J ℙ(Bin(J, p_n) ≥ m)`; here only the inequality is proved, and the
binomial lower tail is bounded by the union bound over the patterns of at most
`m - 1` surviving children rather than by Chebyshev's inequality:
`ℙ(Bin(J, p) < m) ≤ 2^J (1 - p)^{J - ⌊J/2⌋} ≤ 7/100` once `p ≥ 4/5` and
`J ≥ 24`, and `θ_J ≥ 7/8` closes the induction at the level `4/5`.

* `Retained`, `retainedChildren`, `retained_append`, `retained_antitone`: the rounds,
  their shift invariance and monotonicity.
* `RetainedInf`, `retainedInf_iff`: the retained vertices and their fixed-point
  description `eq:pruned-subtree-fixed-point`.
* `measurableSet_retained`, `measurableSet_retainedInf`: the rounds are events.
* `pruneBox`, `sampleMeasure_pruneEvent`, `sampleMeasure_bad_le`,
  `ofReal_le_retainedProb_succ_add`: one step of the recursion through the splitting
  of the field at the root.
* `ofReal_le_retainedProb`, `ofReal_le_sampleMeasure_retainedInf`: the induction
  `p_n ≥ 4/5` and its limit, the root is retained with probability at least `4/5`.
* `HasTwoChildren`, `ChildChoice`, `exists_binary_embedding`,
  `exists_binary_embedding_of_retainedInf`, `survives_of_retainedInf`: the isometric
  copy of `𝔹 = 𝒩(2)` below a retained vertex of the sample.
-/
import BranchingProcess.Conditioned

namespace BranchingProcess

open MeasureTheory ProbabilityTheory ENNReal
open scoped Classical

variable {J N : ℕ}

/-! ### The pruning rounds -/

/-- `Retained J m c n v`: the vertex `v` survives `n` rounds of pruning.  Every vertex
survives round `0`; `v` survives round `n + 1` when its offspring count is `J` and at
least `m` of its first `J` children survive round `n`. -/
noncomputable def Retained (J m : ℕ) (c : Word N → ℕ) : ℕ → Word N → Prop
  | 0, _ => True
  | n + 1, v => c v = J ∧
      m ≤ (Finset.univ.filter fun j : Fin N ↦ (j : ℕ) < J ∧ Retained J m c n (v ++ [j])).card

/-- The children of `v`, among the first `J` letters, that survive `n` rounds. -/
noncomputable def retainedChildren (J m : ℕ) (c : Word N → ℕ) (n : ℕ) (v : Word N) :
    Finset (Fin N) :=
  Finset.univ.filter fun j : Fin N ↦ (j : ℕ) < J ∧ Retained J m c n (v ++ [j])

variable {m : ℕ}

lemma mem_retainedChildren {c : Word N → ℕ} {n : ℕ} {v : Word N} {j : Fin N} :
    j ∈ retainedChildren J m c n v ↔ (j : ℕ) < J ∧ Retained J m c n (v ++ [j]) := by
  simp [retainedChildren]

@[simp] lemma retained_zero (c : Word N → ℕ) (v : Word N) : Retained J m c 0 v := trivial

lemma retained_succ_iff {c : Word N → ℕ} {n : ℕ} {v : Word N} :
    Retained J m c (n + 1) v ↔ c v = J ∧ m ≤ (retainedChildren J m c n v).card := Iff.rfl

/-- **Shift invariance.** Surviving `n` rounds at `v ++ w` is surviving `n` rounds at
`w` for the field shifted to `v`. -/
lemma retained_append (c : Word N → ℕ) (v : Word N) :
    ∀ (n : ℕ) (w : Word N),
      Retained J m c n (v ++ w) ↔ Retained J m (fun u ↦ c (v ++ u)) n w
  | 0, _ => Iff.rfl
  | n + 1, w => by
      rw [retained_succ_iff, retained_succ_iff]
      have hc : retainedChildren J m c n (v ++ w)
          = retainedChildren J m (fun u ↦ c (v ++ u)) n w := by
        ext j
        rw [mem_retainedChildren, mem_retainedChildren, List.append_assoc,
          retained_append c v n (w ++ [j])]
      rw [hc]

/-- The field of the subtree at the letter `j`, as the splitting at the root produces it. -/
lemma retained_split_some (c : Word N → ℕ) (j : Fin N) (n : ℕ) :
    Retained J m (split c (some j)) n [] ↔ Retained J m c n [j] := by
  have h := retained_append (J := J) (m := m) c [j] n []
  rw [List.append_nil] at h
  exact h.symm

/-- **The rounds decrease.** -/
lemma retained_of_succ (c : Word N → ℕ) :
    ∀ (n : ℕ) (v : Word N), Retained J m c (n + 1) v → Retained J m c n v
  | 0, _, _ => trivial
  | n + 1, v, h => by
      rw [retained_succ_iff] at h ⊢
      refine ⟨h.1, h.2.trans (Finset.card_le_card fun j hj ↦ ?_)⟩
      rw [mem_retainedChildren] at hj ⊢
      exact ⟨hj.1, retained_of_succ c n _ hj.2⟩

lemma retained_antitone (c : Word N → ℕ) {n n' : ℕ} (h : n ≤ n') (v : Word N) :
    Retained J m c n' v → Retained J m c n v := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun h' ↦ ih (retained_of_succ c _ v h')

lemma retainedChildren_antitone (c : Word N → ℕ) (v : Word N) {n n' : ℕ} (h : n ≤ n') :
    retainedChildren J m c n' v ⊆ retainedChildren J m c n v := by
  intro j hj
  rw [mem_retainedChildren] at hj ⊢
  exact ⟨hj.1, retained_antitone c h _ hj.2⟩

/-! ### The retained vertices -/

/-- A vertex is retained when it survives every round. -/
def RetainedInf (J m : ℕ) (c : Word N → ℕ) (v : Word N) : Prop := ∀ n, Retained J m c n v

/-- The retained children of `v`, among the first `J` letters. -/
noncomputable def retainedInfChildren (J m : ℕ) (c : Word N → ℕ) (v : Word N) :
    Finset (Fin N) :=
  Finset.univ.filter fun j : Fin N ↦ (j : ℕ) < J ∧ RetainedInf J m c (v ++ [j])

lemma mem_retainedInfChildren {c : Word N → ℕ} {v : Word N} {j : Fin N} :
    j ∈ retainedInfChildren J m c v ↔ (j : ℕ) < J ∧ RetainedInf J m c (v ++ [j]) := by
  simp [retainedInfChildren]

lemma retainedInf_append (c : Word N → ℕ) (v w : Word N) :
    RetainedInf J m c (v ++ w) ↔ RetainedInf J m (fun u ↦ c (v ++ u)) w :=
  forall_congr' fun n ↦ retained_append c v n w

lemma retainedInfChildren_subset (c : Word N → ℕ) (v : Word N) (n : ℕ) :
    retainedInfChildren J m c v ⊆ retainedChildren J m c n v := by
  intro j hj
  rw [mem_retainedInfChildren] at hj
  rw [mem_retainedChildren]
  exact ⟨hj.1, hj.2 n⟩

/-- A decreasing sequence of finite sets of letters stabilises. -/
lemma exists_retainedChildren_eq (c : Word N → ℕ) (v : Word N) :
    ∃ n₀, ∀ n, n₀ ≤ n → retainedChildren J m c n v = retainedChildren J m c n₀ v := by
  have hP : ∃ k, ∃ n, (retainedChildren J m c n v).card = k := ⟨_, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.find_spec hP
  refine ⟨n₀, fun n hn ↦ ?_⟩
  refine Finset.eq_of_subset_of_card_le (retainedChildren_antitone c v hn) ?_
  rw [hn₀]
  exact Nat.find_min' hP ⟨n, rfl⟩

/-- The retained children are the children surviving a late enough round. -/
lemma retainedInfChildren_eq (c : Word N → ℕ) (v : Word N) :
    ∃ n₀, retainedInfChildren J m c v = retainedChildren J m c n₀ v := by
  obtain ⟨n₀, hn₀⟩ := exists_retainedChildren_eq (J := J) (m := m) c v
  refine ⟨n₀, Finset.Subset.antisymm (retainedInfChildren_subset c v n₀) fun j hj ↦ ?_⟩
  rw [mem_retainedInfChildren]
  refine ⟨(mem_retainedChildren.1 hj).1, fun n ↦ ?_⟩
  rcases le_or_gt n₀ n with h | h
  · have hj' : j ∈ retainedChildren J m c n v := by
      rw [hn₀ n h]
      exact hj
    exact (mem_retainedChildren.1 hj').2
  · exact retained_antitone c h.le _ (mem_retainedChildren.1 hj).2

/-- **The fixed point, `eq:pruned-subtree-fixed-point`.** A vertex is retained exactly
when it has offspring count `J` and at least `m` retained children. -/
theorem retainedInf_iff {c : Word N → ℕ} {v : Word N} :
    RetainedInf J m c v ↔ c v = J ∧ m ≤ (retainedInfChildren J m c v).card := by
  constructor
  · intro h
    obtain ⟨n₀, hn₀⟩ := retainedInfChildren_eq (J := J) (m := m) c v
    refine ⟨(retained_succ_iff.1 (h 1)).1, ?_⟩
    rw [hn₀]
    exact (retained_succ_iff.1 (h (n₀ + 1))).2
  · rintro ⟨hc, hm⟩ n
    cases n with
    | zero => trivial
    | succ n =>
        exact retained_succ_iff.2
          ⟨hc, hm.trans (Finset.card_le_card (retainedInfChildren_subset c v n))⟩

/-! ### Measurability -/

lemma le_card_filter_iff {P : Fin N → Prop} [DecidablePred P] :
    m ≤ (Finset.univ.filter P).card ↔ ∃ S : Finset (Fin N), m ≤ S.card ∧ ∀ j ∈ S, P j := by
  constructor
  · intro h
    exact ⟨_, h, fun j hj ↦ (Finset.mem_filter.1 hj).2⟩
  · rintro ⟨S, hS, hP⟩
    exact hS.trans (Finset.card_le_card fun j hj ↦
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hP j hj⟩)

lemma measurableSet_coord_eq (v : Word N) (k : ℕ) :
    MeasurableSet {c : Word N → ℕ | c v = k} := by
  show MeasurableSet ((fun c : Word N → ℕ ↦ c v) ⁻¹' {k})
  exact measurable_pi_apply v (measurableSet_singleton k)

/-- **Surviving `n` rounds is an event**: it is decided by finitely many coordinates. -/
theorem measurableSet_retained :
    ∀ (n : ℕ) (v : Word N), MeasurableSet {c : Word N → ℕ | Retained J m c n v}
  | 0, _ => by
      simp only [retained_zero, Set.setOf_true]
      exact MeasurableSet.univ
  | n + 1, v => by
      have h : {c : Word N → ℕ | Retained J m c (n + 1) v}
          = {c | c v = J} ∩ ⋃ S : Finset (Fin N), ⋃ (_ : m ≤ S.card),
              ⋂ j ∈ S, {c | (j : ℕ) < J ∧ Retained J m c n (v ++ [j])} := by
        ext c
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
          exists_prop]
        rw [retained_succ_iff, retainedChildren, le_card_filter_iff]
      rw [h]
      refine (measurableSet_coord_eq v J).inter (MeasurableSet.iUnion fun S ↦
        MeasurableSet.iUnion fun _ ↦ MeasurableSet.biInter S.countable_toSet fun j _ ↦ ?_)
      by_cases hj : (j : ℕ) < J
      · simp only [hj, true_and]
        exact measurableSet_retained n (v ++ [j])
      · simp only [hj, false_and, Set.setOf_false]
        exact MeasurableSet.empty

theorem measurableSet_retainedInf (v : Word N) :
    MeasurableSet {c : Word N → ℕ | RetainedInf J m c v} := by
  have h : {c : Word N → ℕ | RetainedInf J m c v} = ⋂ n, {c | Retained J m c n v} := by
    ext c
    simp [RetainedInf]
  rw [h]
  exact MeasurableSet.iInter fun n ↦ measurableSet_retained n v

/-! ### The recursion at the root -/

section Probability

variable (N) (θ : Offspring J)

/-- The probability `p_n` that the root survives `n` rounds. -/
noncomputable def retainedProb (m n : ℕ) : ℝ≥0∞ :=
  sampleMeasure (N := N) θ {c : Word N → ℕ | Retained J m c n []}

@[simp] lemma retainedProb_zero : retainedProb N θ m 0 = 1 := by
  simp [retainedProb]

lemma retainedProb_le_one (n : ℕ) : retainedProb N θ m n ≤ 1 := prob_le_one

variable {N}

/-- The product event of one pruning step: the root has `J` children, and no child
outside `S` among the first `J` survives `n` rounds. -/
def pruneBox (J m n : ℕ) (S : Finset (Fin N)) : (i : Option (Fin N)) → Set (Branch N i → ℕ)
  | none => {u | u rootIdx = J}
  | some j =>
      if j ∈ childSet N J \ S then {d : Word N → ℕ | ¬ Retained J m d n []} else Set.univ

lemma measurableSet_pruneBox (n : ℕ) (S : Finset (Fin N)) :
    ∀ i, MeasurableSet (pruneBox (N := N) J m n S i)
  | none => measurableSet_rootIdx_preimage {J}
  | some j => by
      simp only [pruneBox]
      split_ifs
      · exact (measurableSet_retained (J := J) (m := m) n []).compl
      · exact MeasurableSet.univ

/-- The pruning step event, read through the splitting at the root. -/
lemma split_preimage_pruneBox (n : ℕ) (S : Finset (Fin N)) :
    split ⁻¹' (Set.univ.pi (pruneBox (N := N) J m n S))
      = {c : Word N → ℕ | c [] = J}
        ∩ {c | ∀ j ∈ childSet N J \ S, ¬ Retained J m c n [j]} := by
  ext c
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨h none, fun j hj ↦ ?_⟩
    have hj' := h (some j)
    simp only [pruneBox, if_pos hj] at hj'
    have hj'' : ¬ Retained J m (split c (some j)) n [] := hj'
    rwa [retained_split_some] at hj''
  · rintro ⟨hroot, h⟩ i
    cases i with
    | none => exact hroot
    | some j =>
        by_cases hj : j ∈ childSet N J \ S
        · simp only [pruneBox, if_pos hj]
          show ¬ Retained J m (split c (some j)) n []
          rw [retained_split_some]
          exact h j hj
        · simp only [pruneBox, if_neg hj]
          exact Set.mem_univ _

/-- **The mass of a pruning pattern.** The root has `J` children and no child outside
`S` survives `n` rounds with probability `θ_J (1 - p_n)^{J - |S|}`: the splitting makes
the subtrees independent, each surviving `n` rounds with probability `p_n`. -/
theorem sampleMeasure_pruneEvent (hJN : J ≤ N) (n : ℕ) {S : Finset (Fin N)}
    (hS : S ⊆ childSet N J) :
    sampleMeasure (N := N) θ
        ({c : Word N → ℕ | c [] = J} ∩ {c | ∀ j ∈ childSet N J \ S, ¬ Retained J m c n [j]})
      = ENNReal.ofReal (θ J) * (1 - retainedProb N θ m n) ^ (J - S.card) := by
  rw [← split_preimage_pruneBox, ← Measure.map_apply measurable_split
    (MeasurableSet.univ_pi (measurableSet_pruneBox n S)), map_split, ← Finset.coe_univ,
    Measure.infinitePi_pi _ (fun i _ ↦ measurableSet_pruneBox n S i), Fintype.prod_option,
    show pruneBox (N := N) J m n S none = {u | u rootIdx = J} from rfl,
    infinitePi_root_apply θ J]
  congr 1
  have hfac : ∀ j : Fin N,
      Measure.infinitePi (fun _ : Branch N (some j) ↦ θ.law) (pruneBox J m n S (some j))
        = if j ∈ childSet N J \ S then 1 - retainedProb N θ m n else 1 := by
    intro j
    simp only [pruneBox]
    split_ifs
    · rw [infinitePi_branch_some]
      show sampleMeasure θ {d : Word N → ℕ | Retained J m d n []}ᶜ = _
      rw [prob_compl_eq_one_sub (measurableSet_retained n [])]
      rfl
    · exact measure_univ
  rw [Finset.prod_congr rfl fun j _ ↦ hfac j, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const, Finset.card_sdiff_of_subset hS, card_childSet hJN]

/-- **The union bound for the lower tail.** The root has `J` children but fewer than
`m` of them survive `n` rounds with probability at most
`2^J θ_J (1 - p_n)^{J + 1 - m}`: each pattern of at most `m - 1` surviving children
has mass at most `θ_J (1 - p_n)^{J + 1 - m}`, and there are at most `2^J` patterns. -/
theorem sampleMeasure_bad_le (hJN : J ≤ N) (n : ℕ) :
    sampleMeasure (N := N) θ
        {c : Word N → ℕ | c [] = J ∧ ¬ m ≤ (retainedChildren J m c n []).card}
      ≤ 2 ^ J * (ENNReal.ofReal (θ J) * (1 - retainedProb N θ m n) ^ (J + 1 - m)) := by
  set T := (childSet N J).powerset.filter fun S : Finset (Fin N) ↦ S.card < m with hT
  have hsub : {c : Word N → ℕ | c [] = J ∧ ¬ m ≤ (retainedChildren J m c n []).card}
      ⊆ ⋃ S ∈ T, ({c : Word N → ℕ | c [] = J}
          ∩ {c | ∀ j ∈ childSet N J \ S, ¬ Retained J m c n [j]}) := by
    rintro c ⟨hc, hcard⟩
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    refine ⟨retainedChildren J m c n [], Finset.mem_filter.2 ⟨Finset.mem_powerset.2
      fun j hj ↦ mem_childSet.2 (mem_retainedChildren.1 hj).1, not_le.1 hcard⟩, hc,
      fun j hj hr ↦ ?_⟩
    rw [Finset.mem_sdiff, mem_childSet, mem_retainedChildren] at hj
    exact hj.2 ⟨hj.1, hr⟩
  have hcardT : (T.card : ℝ≥0∞) ≤ 2 ^ J := by
    have h : T.card ≤ 2 ^ J := by
      calc T.card ≤ (childSet N J).powerset.card := Finset.card_filter_le _ _
        _ = 2 ^ J := by rw [Finset.card_powerset, card_childSet hJN]
    exact_mod_cast h
  calc sampleMeasure (N := N) θ
        {c : Word N → ℕ | c [] = J ∧ ¬ m ≤ (retainedChildren J m c n []).card}
      ≤ sampleMeasure (N := N) θ (⋃ S ∈ T, ({c : Word N → ℕ | c [] = J}
          ∩ {c | ∀ j ∈ childSet N J \ S, ¬ Retained J m c n [j]})) := measure_mono hsub
    _ ≤ ∑ S ∈ T, sampleMeasure (N := N) θ ({c : Word N → ℕ | c [] = J}
          ∩ {c | ∀ j ∈ childSet N J \ S, ¬ Retained J m c n [j]}) :=
        measure_biUnion_finset_le T _
    _ ≤ ∑ _S ∈ T, ENNReal.ofReal (θ J) * (1 - retainedProb N θ m n) ^ (J + 1 - m) := by
        refine Finset.sum_le_sum fun S hS ↦ ?_
        rw [Finset.mem_filter, Finset.mem_powerset] at hS
        rw [sampleMeasure_pruneEvent θ hJN n hS.1]
        exact mul_le_mul' le_rfl (pow_le_pow_of_le_one zero_le tsub_le_self (by omega))
    _ = T.card * (ENNReal.ofReal (θ J) * (1 - retainedProb N θ m n) ^ (J + 1 - m)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ J * (ENNReal.ofReal (θ J) * (1 - retainedProb N θ m n) ^ (J + 1 - m)) := by
        gcongr

/-- **One step of the recursion, as an inequality**: `θ_J ≤ p_{n+1} + 2^J θ_J (1-p_n)^{J+1-m}`. -/
theorem ofReal_le_retainedProb_succ_add (hJN : J ≤ N) (n : ℕ) :
    ENNReal.ofReal (θ J) ≤ retainedProb N θ m (n + 1)
      + 2 ^ J * (ENNReal.ofReal (θ J) * (1 - retainedProb N θ m n) ^ (J + 1 - m)) := by
  have hsub : {c : Word N → ℕ | c [] = J}
      ⊆ {c : Word N → ℕ | Retained J m c (n + 1) []}
        ∪ {c | c [] = J ∧ ¬ m ≤ (retainedChildren J m c n []).card} := by
    intro c hc
    by_cases h : m ≤ (retainedChildren J m c n []).card
    · exact Or.inl (retained_succ_iff.2 ⟨hc, h⟩)
    · exact Or.inr ⟨hc, h⟩
  calc ENNReal.ofReal (θ J) = sampleMeasure (N := N) θ {c : Word N → ℕ | c [] = J} :=
        (sampleMeasure_coord θ [] J).symm
    _ ≤ sampleMeasure (N := N) θ ({c : Word N → ℕ | Retained J m c (n + 1) []}
        ∪ {c | c [] = J ∧ ¬ m ≤ (retainedChildren J m c n []).card}) := measure_mono hsub
    _ ≤ retainedProb N θ m (n + 1)
        + sampleMeasure (N := N) θ
          {c : Word N → ℕ | c [] = J ∧ ¬ m ≤ (retainedChildren J m c n []).card} :=
        measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl (sampleMeasure_bad_le θ hJN n)

/-! ### The induction `p_n ≥ 4/5` -/

/-- The numerical estimate closing the induction: for `q ≤ 1/5` and `J ≥ 24`,
`2^J q^{J - ⌊J/2⌋} ≤ 7/100`. -/
lemma two_pow_mul_pow_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 5) (hJ : 24 ≤ J) :
    (2 : ℝ) ^ J * q ^ (J - J / 2) ≤ 7 / 100 := by
  have hk : 12 ≤ J - J / 2 := by omega
  have hJk : J ≤ 2 * (J - J / 2) := by omega
  have h1 : (2 : ℝ) ^ J ≤ 4 ^ (J - J / 2) := by
    calc (2 : ℝ) ^ J ≤ 2 ^ (2 * (J - J / 2)) := pow_le_pow_right₀ (by norm_num) hJk
      _ = 4 ^ (J - J / 2) := by rw [pow_mul]; norm_num
  have h3 : (4 * q) ^ (J - J / 2) ≤ (4 / 5 : ℝ) ^ (J - J / 2) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have h4 : (4 / 5 : ℝ) ^ (J - J / 2) ≤ (4 / 5) ^ 12 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have h5 : (4 / 5 : ℝ) ^ 12 ≤ 7 / 100 := by norm_num
  calc (2 : ℝ) ^ J * q ^ (J - J / 2) ≤ 4 ^ (J - J / 2) * q ^ (J - J / 2) := by gcongr
    _ = (4 * q) ^ (J - J / 2) := (mul_pow _ _ _).symm
    _ ≤ 7 / 100 := h3.trans (h4.trans h5)

/-- **The root survives every round with probability at least `4/5`**, at
`m = ⌊J/2⌋ + 1`, for `J ≥ 24` and `θ_J ≥ 7/8`. -/
theorem ofReal_le_retainedProb (hJN : J ≤ N) (hJ : 24 ≤ J) (hθJ : 7 / 8 ≤ θ J) :
    ∀ n, ENNReal.ofReal (4 / 5) ≤ retainedProb N θ (J / 2 + 1) n
  | 0 => by
      rw [retainedProb_zero]
      exact ENNReal.ofReal_le_one.2 (by norm_num)
  | n + 1 => by
      have ih := ofReal_le_retainedProb hJN hJ hθJ n
      have hstep := ofReal_le_retainedProb_succ_add (m := J / 2 + 1) θ hJN n
      have hexp : J + 1 - (J / 2 + 1) = J - J / 2 := by omega
      rw [hexp] at hstep
      have hq : 1 - retainedProb N θ (J / 2 + 1) n ≤ ENNReal.ofReal (1 / 5) := by
        calc 1 - retainedProb N θ (J / 2 + 1) n ≤ 1 - ENNReal.ofReal (4 / 5) :=
              tsub_le_tsub_left ih 1
          _ = ENNReal.ofReal (1 / 5) := by
              rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
              norm_num
      have hcast : (2 : ℝ≥0∞) ^ J * (ENNReal.ofReal (θ J) * ENNReal.ofReal (1 / 5) ^ (J - J / 2))
          = ENNReal.ofReal (θ J * (2 ^ J * (1 / 5) ^ (J - J / 2))) := by
        rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (θ.nonneg J),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      have herr : (2 : ℝ≥0∞) ^ J
          * (ENNReal.ofReal (θ J) * (1 - retainedProb N θ (J / 2 + 1) n) ^ (J - J / 2))
          ≤ ENNReal.ofReal (θ J * (7 / 100)) := by
        calc (2 : ℝ≥0∞) ^ J
              * (ENNReal.ofReal (θ J) * (1 - retainedProb N θ (J / 2 + 1) n) ^ (J - J / 2))
            ≤ (2 : ℝ≥0∞) ^ J
              * (ENNReal.ofReal (θ J) * ENNReal.ofReal (1 / 5) ^ (J - J / 2)) := by gcongr
          _ = ENNReal.ofReal (θ J * (2 ^ J * (1 / 5) ^ (J - J / 2))) := hcast
          _ ≤ ENNReal.ofReal (θ J * (7 / 100)) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have := two_pow_mul_pow_le (q := 1 / 5) (by norm_num) le_rfl hJ
              have h0 := θ.nonneg J
              nlinarith
      have h1 : ENNReal.ofReal (θ J)
          ≤ retainedProb N θ (J / 2 + 1) (n + 1) + ENNReal.ofReal (θ J * (7 / 100)) :=
        hstep.trans (add_le_add le_rfl herr)
      have h2 : ENNReal.ofReal (θ J) - ENNReal.ofReal (θ J * (7 / 100))
          ≤ retainedProb N θ (J / 2 + 1) (n + 1) := tsub_le_iff_right.2 h1
      refine le_trans ?_ h2
      rw [← ENNReal.ofReal_sub _ (by have := θ.nonneg J; positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- **The root is retained with probability at least `4/5`**: the rounds decrease to the
retained event, and each has probability at least `4/5`. -/
theorem ofReal_le_sampleMeasure_retainedInf (hJN : J ≤ N) (hJ : 24 ≤ J) (hθJ : 7 / 8 ≤ θ J) :
    ENNReal.ofReal (4 / 5)
      ≤ sampleMeasure (N := N) θ {c : Word N → ℕ | RetainedInf J (J / 2 + 1) c []} := by
  have hset : {c : Word N → ℕ | RetainedInf J (J / 2 + 1) c []}
      = ⋂ n, {c : Word N → ℕ | Retained J (J / 2 + 1) c n []} := by
    ext c
    simp [RetainedInf]
  have hanti : Antitone fun n ↦ {c : Word N → ℕ | Retained J (J / 2 + 1) c n []} :=
    fun n n' h c hc ↦ retained_antitone c h [] hc
  rw [hset, hanti.measure_iInter (fun n ↦ (measurableSet_retained n []).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  exact le_iInf fun n ↦ ofReal_le_retainedProb θ hJN hJ hθJ n

end Probability

/-! ### The binary subtree below a retained vertex -/

section BinaryEmbedding

/-- Every vertex of `R` has two distinct children in `R`. -/
def HasTwoChildren (R : Word N → Prop) : Prop :=
  ∀ v, R v → ∃ j₀ j₁ : Fin N, j₀ ≠ j₁ ∧ R (v ++ [j₀]) ∧ R (v ++ [j₁])

variable {R : Word N → Prop}

/-- A choice of two distinct children in `R` at each vertex of `R`, indexed by the two
letters of `𝔹`. -/
structure ChildChoice (R : Word N → Prop) where
  child : {v : Word N // R v} → Fin 2 → Fin N
  mem : ∀ x b, R (x.1 ++ [child x b])
  ne : ∀ x, child x 0 ≠ child x 1

/-- The choice supplied by `HasTwoChildren`. -/
noncomputable def HasTwoChildren.choice (h : HasTwoChildren R) : ChildChoice R := by
  choose j₀ j₁ hne h₀ h₁ using h
  exact ⟨fun x b ↦ if b = 0 then j₀ x.1 x.2 else j₁ x.1 x.2,
    fun x b ↦ by
      split_ifs
      · exact h₀ _ _
      · exact h₁ _ _,
    fun x ↦ by simp [hne]⟩

namespace ChildChoice

variable (f : ChildChoice R)

/-- One step of the embedding: the child chosen for the letter `b`. -/
def step (x : {v : Word N // R v}) (b : Fin 2) : {v : Word N // R v} :=
  ⟨x.1 ++ [f.child x b], f.mem x b⟩

/-- The embedding of `𝔹` from a base vertex, following the chosen children letter by
letter. -/
def embedFrom (x : {v : Word N // R v}) (w : Word 2) : {v : Word N // R v} :=
  w.foldl f.step x

@[simp] lemma embedFrom_nil (x : {v : Word N // R v}) : f.embedFrom x [] = x := rfl

lemma embedFrom_cons (x : {v : Word N // R v}) (b : Fin 2) (w : Word 2) :
    f.embedFrom x (b :: w) = f.embedFrom (f.step x b) w := rfl

lemma embedFrom_append (x : {v : Word N // R v}) (u w : Word 2) :
    f.embedFrom x (u ++ w) = f.embedFrom (f.embedFrom x u) w :=
  List.foldl_append

lemma embedFrom_length : ∀ (w : Word 2) (x : {v : Word N // R v}),
    (f.embedFrom x w).1.length = x.1.length + w.length
  | [], _ => by simp
  | b :: w, x => by
      rw [embedFrom_cons, embedFrom_length w (f.step x b)]
      simp [step]
      omega

lemma prefix_embedFrom : ∀ (w : Word 2) (x : {v : Word N // R v}),
    x.1 <+: (f.embedFrom x w).1
  | [], _ => List.prefix_refl _
  | b :: w, x => by
      rw [embedFrom_cons]
      exact (List.prefix_append x.1 [f.child x b]).trans (prefix_embedFrom w (f.step x b))

/-- The embedding sends the letters of `𝔹` to distinct children: `a ≠ b` in `Fin 2` is
`{a, b} = {0, 1}`. -/
lemma child_ne (x : {v : Word N // R v}) {a b : Fin 2} (hab : a ≠ b) :
    f.child x a ≠ f.child x b := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact f.ne x
  · exact (f.ne x).symm
  · exact absurd rfl hab

/-- **The embedding preserves wedges.** -/
theorem wedge_embedFrom : ∀ (u w : Word 2) (x : {v : Word N // R v}),
    wedge (f.embedFrom x u).1 (f.embedFrom x w).1 = (f.embedFrom x (wedge u w)).1
  | [], w, x => by
      rw [embedFrom_nil, wedge_nil_left, embedFrom_nil]
      exact wedge_of_prefix (f.prefix_embedFrom w x)
  | a :: u, [], x => by
      rw [embedFrom_nil, wedge_nil_right, embedFrom_nil, wedge_comm]
      exact wedge_of_prefix (f.prefix_embedFrom (a :: u) x)
  | a :: u, b :: w, x => by
      rw [embedFrom_cons, embedFrom_cons, wedge_cons_cons]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, embedFrom_cons]
        exact wedge_embedFrom u w (f.step x a)
      · rw [if_neg hab, embedFrom_nil]
        obtain ⟨t, ht⟩ := f.prefix_embedFrom u (f.step x a)
        obtain ⟨t', ht'⟩ := f.prefix_embedFrom w (f.step x b)
        rw [← ht, ← ht']
        simp only [step, List.append_assoc, List.singleton_append]
        rw [wedge_append_append, wedge_cons_cons, if_neg (f.child_ne x hab), List.append_nil]

/-- **The embedding is isometric.** -/
theorem treeDist_embedFrom (u w : Word 2) (x : {v : Word N // R v}) :
    treeDist (f.embedFrom x u).1 (f.embedFrom x w).1 = treeDist u w := by
  have h1 := treeDist_add (f.embedFrom x u).1 (f.embedFrom x w).1
  have h2 := treeDist_add u w
  rw [wedge_embedFrom, embedFrom_length, embedFrom_length, embedFrom_length] at h1
  omega

end ChildChoice

/-- **An isometric copy of `𝔹` in a set with two children below every vertex**, rooted
at any of its vertices. -/
theorem exists_binary_embedding (h : HasTwoChildren R) {v₀ : Word N} (hv₀ : R v₀) :
    ∃ e : Word 2 → Word N, (∀ w, R (e w)) ∧ ∀ u w, treeDist (e u) (e w) = treeDist u w :=
  ⟨fun w ↦ (h.choice.embedFrom ⟨v₀, hv₀⟩ w).1, fun w ↦ (h.choice.embedFrom ⟨v₀, hv₀⟩ w).2,
    fun u w ↦ h.choice.treeDist_embedFrom u w _⟩

/-- **The retained vertices of the sample have two retained children in the sample**, once
`m ≥ 2`: a retained vertex has `J` children in the sample and at least `m` retained
ones among them. -/
theorem hasTwoChildren_retainedInf {c : Word N → ℕ} (hm : 2 ≤ m) :
    HasTwoChildren fun v : Word N ↦ RetainedInf J m c v ∧ v ∈ sample c := by
  rintro v ⟨hr, hv⟩
  obtain ⟨hc, hcard⟩ := retainedInf_iff.1 hr
  obtain ⟨j₀, hj₀, j₁, hj₁, hne⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le one_lt_two (hm.trans hcard))
  rw [mem_retainedInfChildren] at hj₀ hj₁
  exact ⟨j₀, j₁, hne, ⟨hj₀.2, mem_sample_append_singleton.2 ⟨hv, hc ▸ hj₀.1⟩⟩,
    ⟨hj₁.2, mem_sample_append_singleton.2 ⟨hv, hc ▸ hj₁.1⟩⟩⟩

/-- **`thm:concentrated-regular-subtree`, the deterministic conclusion**: below a
retained vertex of the sample there is an isometric copy of the binary tree `𝒩(2)`,
with the original unit edges. -/
theorem exists_binary_embedding_of_retainedInf {c : Word N → ℕ} (hm : 2 ≤ m) {v₀ : Word N}
    (hr : RetainedInf J m c v₀) (hv₀ : v₀ ∈ sample c) :
    ∃ e : Word 2 → Word N, (∀ w, e w ∈ sample c) ∧ ∀ u w, treeDist (e u) (e w) = treeDist u w := by
  obtain ⟨e, he, hd⟩ := exists_binary_embedding (hasTwoChildren_retainedInf hm) ⟨hr, hv₀⟩
  exact ⟨e, fun w ↦ (he w).2, hd⟩

/-- A sample whose root is retained is infinite. -/
theorem survives_of_retainedInf {c : Word N → ℕ} (hm : 2 ≤ m) (hr : RetainedInf J m c []) :
    Survives c := by
  obtain ⟨e, he, hd⟩ := exists_binary_embedding_of_retainedInf hm hr (nil_mem_sample c)
  have hinj : Function.Injective e := by
    intro u w huw
    have h := hd u w
    rw [huw, treeDist_self] at h
    exact (treeDist_eq_zero_iff.1 h.symm)
  exact Set.infinite_of_injective_forall_mem hinj he

end BinaryEmbedding

end BranchingProcess
