/-
`sec:gw-trees` of `prelims.tex` and `thm:shape-mass` of `matching_classes_simple.tex`:
a finite sample, the probability that the tree is exactly a prescribed one, and the
number of its vertices.

A finite tree is presented by a field cutting it out.  Two fields agreeing at the
vertices of one of their samples cut out the same tree, so the point mass of a finite
tree is the mass of a cylinder event over its vertices, and the field being independent
that mass is the product of the offspring weights along the tree.  The size of the tree
is the other quantity `thm:shape-mass` reads off, and for a subcritical law it has an
exponential moment: the truncations of the sample satisfy the progeny recursion
`F_{k+1}(s) = s f(F_k(s))`, and a fixed point of `s f(y) = y` above one bounds them all.

* `agreeOn`, `sample_eq_of_agreeOn`: **agreement on a tree cuts out that tree**.
* `sampleMeasure_agreeOn`: **the point mass of a finite tree**, the product of the
  offspring weights over its vertices.
* `ofReal_pow_le_sampleMeasure_sample_eq`, `sampleMeasure_le_bushMeasure` and
  `ofReal_pow_le_bushMeasure_sample_eq`: the point mass in the form
  `thm:shape-mass`\labelcref{it:shape-mass-point} consumes it, a factor `p` per vertex,
  under the sample law and under the law of a bush.
* `progenyTree`, `progeny`, `mem_progenyTree`, `progeny_succ`, `progeny_eq_ncard` and
  `measurable_progeny`: **the truncated progeny**, the number of vertices of the sample
  within the first `k` generations, its recursion at the root, its value once the fuel
  exceeds the height, and its measurability.
* `map_split_apply`, `map_shift` and `iIndepFun_split`: the laws of the blocks of the
  splitting, and their independence.
* `progenyFactor`, `prod_progenyFactor`, `lintegral_progeny_root` and
  `lintegral_pow_progeny_succ`: **the progeny recursion** `F_{k+1}(s) = s f(F_k(s))`, the
  one-step event read through the splitting as a product.
* `lintegral_pow_progeny_le`: the truncated moments stay below a fixed point of the
  progeny equation.
* `Offspring.exists_gen_lt_self` and `Offspring.exists_progeny_fixedPoint`: **the progeny
  equation**.  A subcritical generating function drops below the diagonal above one, so
  `s f(y) = y` has a solution with `s, y > 1`.
* `lintegral_pow_ncard_le` and `exists_exponential_moment`: **the exponential moment of
  the total progeny** of a subcritical law.
* `measurableSet_subtree_eq`, `measurableSet_ncard_eq` and `measurable_pow_ncard`: the
  number of vertices of a random tree is a random variable.
* `lintegral_pow_ncard_bushMeasure_le` and `exists_exponential_moment_bushMeasure`: **the
  exponential moment of the size of a bush**, the input
  `thm:shape-mass`\labelcref{it:shape-mass-tail} takes from
  `thm:harris`\labelcref{it:harris-bushes}; the moment at the conjugate law transports
  along `bushTreeLaw_eq_treeLaw`.

The alphabet has to be wide enough to carry the law, so `J ≤ N` runs through the
statements about the moment as it does in `Law`.
-/
import BranchingProcess.Skeleton

namespace BranchingProcess

open MeasureTheory ProbabilityTheory ENNReal

variable {J N : ℕ}

/-! ### Fields that agree on a tree -/

/-- The event that a field agrees with `e` at every vertex of the sample of `e`; the
coordinates off that tree are left free. -/
def agreeOn (e : Word N → ℕ) : Set (Word N → ℕ) := {c : Word N → ℕ | ∀ v ∈ sample e, c v = e v}

@[simp] lemma mem_agreeOn {e c : Word N → ℕ} :
    c ∈ agreeOn e ↔ ∀ v ∈ sample e, c v = e v := Iff.rfl

/-- **Agreement on a tree cuts out that tree.**  Whether a child of a vertex of the
sample of `e` is kept is decided by the offspring count there, and the two fields carry
the same one; the induction on the word never leaves the tree. -/
theorem sample_eq_of_agreeOn {e c : Word N → ℕ} (h : c ∈ agreeOn e) :
    (sample c : Set (Word N)) = (sample e : Set (Word N)) := by
  refine Set.ext fun v ↦ ?_
  induction v using List.reverseRecOn with
  | nil => exact iff_of_true (nil_mem_sample c) (nil_mem_sample e)
  | append_singleton u j ih =>
      simp only [SetLike.mem_coe] at ih ⊢
      rw [mem_sample_append_singleton, mem_sample_append_singleton]
      constructor
      · rintro ⟨hu, hj⟩
        have hue : u ∈ sample e := ih.mp hu
        rw [h u hue] at hj
        exact ⟨hue, hj⟩
      · rintro ⟨hu, hj⟩
        rw [← h u hu] at hj
        exact ⟨ih.mpr hu, hj⟩

/-- The agreement event lies inside the event that the sample is the prescribed tree. -/
theorem agreeOn_subset (e : Word N → ℕ) :
    agreeOn e ⊆ {c : Word N → ℕ | (sample c : Set (Word N)) = (sample e : Set (Word N))} :=
  fun _ h ↦ sample_eq_of_agreeOn h

/-- A field cutting out a finite tree dies out. -/
theorem not_survives_of_sample_eq {e c : Word N → ℕ} (hfin : (sample e : Set (Word N)).Finite)
    (h : (sample c : Set (Word N)) = (sample e : Set (Word N))) : ¬ Survives c := by
  rw [Survives, h]
  exact Set.not_infinite.mpr hfin

/-! ### The point mass of a finite tree -/

/-- **The point mass of a finite tree.**  A field agrees with `e` at the vertices of the
sample of `e` with probability the product of the offspring weights along that tree: the
agreement is a cylinder event over those finitely many coordinates, and the coordinates
are independent. -/
theorem sampleMeasure_agreeOn (θ : Offspring J) {e : Word N → ℕ}
    (hfin : (sample e : Set (Word N)).Finite) :
    sampleMeasure (N := N) θ (agreeOn e) = ∏ v ∈ hfin.toFinset, ENNReal.ofReal (θ (e v)) := by
  have hset : agreeOn e = ⋂ v ∈ hfin.toFinset, (coord v : (Word N → ℕ) → ℕ) ⁻¹' {e v} := by
    ext c
    simp only [mem_agreeOn, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
      Set.Finite.mem_toFinset, SetLike.mem_coe, coord]
  have hind := (coord_iIndepFun (ι := Word N) θ.law).measure_inter_preimage_eq_mul
    hfin.toFinset (sets := fun v ↦ ({e v} : Set ℕ)) fun v _ ↦ measurableSet_singleton (e v)
  show fieldMeasure θ.law (agreeOn e) = _
  rw [hset, hind]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [coord_law θ.law v (measurableSet_singleton (e v)), Offspring.law_singleton]

/-- **One factor per vertex.**  A finite tree whose offspring weights are all at least
`p` has point mass at least `p` to its number of vertices. -/
theorem ofReal_pow_le_sampleMeasure_agreeOn (θ : Offspring J) {p : ℝ} {e : Word N → ℕ}
    (hfin : (sample e : Set (Word N)).Finite) (hmass : ∀ v ∈ sample e, p ≤ θ (e v)) :
    ENNReal.ofReal p ^ (sample e : Set (Word N)).ncard
      ≤ sampleMeasure (N := N) θ (agreeOn e) := by
  rw [sampleMeasure_agreeOn θ hfin, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]
  refine Finset.prod_le_prod' fun v hv ↦ ENNReal.ofReal_le_ofReal (hmass v ?_)
  rwa [Set.Finite.mem_toFinset] at hv

/-- **`thm:shape-mass`\labelcref{it:shape-mass-point} under the sample law**: the sample
is a prescribed finite tree with probability at least `p` to its number of vertices. -/
theorem ofReal_pow_le_sampleMeasure_sample_eq (θ : Offspring J) {p : ℝ} {e : Word N → ℕ}
    (hfin : (sample e : Set (Word N)).Finite) (hmass : ∀ v ∈ sample e, p ≤ θ (e v)) :
    ENNReal.ofReal p ^ (sample e : Set (Word N)).ncard
      ≤ sampleMeasure (N := N) θ
          {c : Word N → ℕ | (sample c : Set (Word N)) = (sample e : Set (Word N))} :=
  le_trans (ofReal_pow_le_sampleMeasure_agreeOn θ hfin hmass)
    (measure_mono (agreeOn_subset e))

/-- Conditioning on extinction only increases the mass of an event carried by
extinction. -/
theorem sampleMeasure_le_bushMeasure (θ : Offspring J) {S : Set (Word N → ℕ)}
    (hS : S ⊆ {c : Word N → ℕ | ¬ Survives c}) :
    sampleMeasure (N := N) θ S ≤ bushMeasure (N := N) θ S := by
  rw [bushMeasure_apply, Set.inter_eq_right.mpr hS]
  refine le_mul_of_one_le_left' ?_
  have h : sampleMeasure (N := N) θ {c : Word N → ℕ | ¬ Survives c} ≤ 1 := prob_le_one
  simpa using (ENNReal.inv_le_inv (a := 1)
    (b := sampleMeasure (N := N) θ {c : Word N → ℕ | ¬ Survives c})).mpr h

/-- **`thm:shape-mass`\labelcref{it:shape-mass-point} under the law of a bush**: a bush
is a prescribed finite tree with probability at least `p` to its number of vertices. -/
theorem ofReal_pow_le_bushMeasure_sample_eq (θ : Offspring J) {p : ℝ} {e : Word N → ℕ}
    (hfin : (sample e : Set (Word N)).Finite) (hmass : ∀ v ∈ sample e, p ≤ θ (e v)) :
    ENNReal.ofReal p ^ (sample e : Set (Word N)).ncard
      ≤ bushMeasure (N := N) θ
          {c : Word N → ℕ | (sample c : Set (Word N)) = (sample e : Set (Word N))} :=
  le_trans (ofReal_pow_le_sampleMeasure_sample_eq θ hfin hmass)
    (sampleMeasure_le_bushMeasure θ fun _ hc ↦ not_survives_of_sample_eq hfin hc)

/-! ### The truncated progeny -/

/-- A child of the root of a sample, unfolded. -/
lemma mem_sample_cons_iff {c : Word N → ℕ} {i : Fin N} {u : Word N} :
    i :: u ∈ sample c ↔ (i : ℕ) < c [] ∧ u ∈ sample fun w ↦ c (i :: w) := by
  have h : (i :: u : Word N) = [i] ++ u := rfl
  rw [h, append_mem_sample_iff, singleton_mem_sample_iff]
  exact Iff.rfl

/-- The vertices of the sample within the first `k` generations: the root together with
the truncations of the subtrees at the children of the root, each one generation
shorter. -/
def progenyTree : ℕ → (Word N → ℕ) → Finset (Word N)
  | 0, _ => ∅
  | k + 1, c =>
      insert [] ((childSet N (c [])).biUnion fun i ↦
        (progenyTree k fun w ↦ c (i :: w)).image fun u ↦ i :: u)

/-- **The truncation is the sample cut at a generation.** -/
lemma mem_progenyTree : ∀ (k : ℕ) (c : Word N → ℕ) (v : Word N),
    v ∈ progenyTree k c ↔ v ∈ sample c ∧ v.length < k := by
  intro k
  induction k with
  | zero => intro c v; simp [progenyTree]
  | succ k ih =>
      intro c v
      rw [progenyTree]
      cases v with
      | nil =>
          exact iff_of_true (Finset.mem_insert_self _ _)
            ⟨nil_mem_sample c, Nat.succ_pos k⟩
      | cons i u =>
          rw [Finset.mem_insert, Finset.mem_biUnion, mem_sample_cons_iff, List.length_cons,
            Nat.succ_lt_succ_iff]
          simp only [List.cons_ne_nil, false_or]
          constructor
          · rintro ⟨i', hi', hmem⟩
            rw [Finset.mem_image] at hmem
            obtain ⟨u', hu', heq⟩ := hmem
            obtain ⟨rfl, rfl⟩ : i' = i ∧ u' = u := by simpa using heq
            rw [ih] at hu'
            exact ⟨⟨mem_childSet.mp hi', hu'.1⟩, hu'.2⟩
          · rintro ⟨⟨hi, hu⟩, hlen⟩
            exact ⟨i, mem_childSet.mpr hi,
              Finset.mem_image.mpr ⟨u, (ih _ _).mpr ⟨hu, hlen⟩, rfl⟩⟩

/-- **The truncated progeny**: the number of vertices of the sample within the first `k`
generations. -/
def progeny (k : ℕ) (c : Word N → ℕ) : ℕ := (progenyTree k c).card

@[simp] lemma progeny_zero (c : Word N → ℕ) : progeny 0 c = 0 := rfl

/-- **The recursion at the root**: the root, and the truncations of the subtrees at its
children.  This is the identity the progeny equation is read off. -/
lemma progeny_succ (k : ℕ) (c : Word N → ℕ) :
    progeny (k + 1) c = 1 + ∑ i ∈ childSet N (c []), progeny k fun w ↦ c (i :: w) := by
  classical
  have hcons : ∀ i : Fin N, Function.Injective fun u : Word N ↦ i :: u := by
    intro i u u' h
    simpa using h
  have hnil : ([] : Word N) ∉ (childSet N (c [])).biUnion fun i ↦
      (progenyTree k fun w ↦ c (i :: w)).image fun u ↦ i :: u := by
    simp only [Finset.mem_biUnion, Finset.mem_image, not_exists]
    rintro i ⟨-, u, -, heq⟩
    exact absurd heq (List.cons_ne_nil _ _)
  have hdisj : ∀ i ∈ childSet N (c []), ∀ i' ∈ childSet N (c []), i ≠ i' →
      Disjoint ((progenyTree k fun w ↦ c (i :: w)).image fun u ↦ i :: u)
        ((progenyTree k fun w ↦ c (i' :: w)).image fun u ↦ i' :: u) := by
    rintro i - i' - hii'
    refine Finset.disjoint_left.mpr fun v hv hv' ↦ hii' ?_
    rw [Finset.mem_image] at hv hv'
    obtain ⟨u, -, rfl⟩ := hv
    obtain ⟨u', -, heq⟩ := hv'
    have h2 : i = i' ∧ u = u' := by simpa using heq.symm
    exact h2.1
  rw [progeny, progenyTree, Finset.card_insert_of_notMem hnil, Finset.card_biUnion hdisj,
    Nat.add_comm]
  refine congrArg (1 + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact Finset.card_image_of_injective _ (hcons i)

/-- The truncations increase with the generation. -/
lemma progenyTree_subset {k l : ℕ} (h : k ≤ l) (c : Word N → ℕ) :
    progenyTree k c ⊆ progenyTree l c := by
  intro v hv
  rw [mem_progenyTree] at hv ⊢
  exact ⟨hv.1, lt_of_lt_of_le hv.2 h⟩

/-- The truncated progeny increases with the generation. -/
lemma progeny_mono (c : Word N → ℕ) : Monotone fun k ↦ progeny k c :=
  fun _ _ h ↦ Finset.card_le_card (progenyTree_subset h c)

/-- **The truncation stops at the height**: once the fuel exceeds the length of every
vertex, the truncated progeny is the number of vertices of the sample. -/
lemma progeny_eq_ncard {c : Word N → ℕ} {k : ℕ} (h : ∀ u ∈ sample c, u.length < k) :
    progeny k c = (sample c : Set (Word N)).ncard := by
  have hcoe : ((progenyTree k c : Finset (Word N)) : Set (Word N))
      = (sample c : Set (Word N)) := by
    ext v
    simp only [mem_progenyTree, SetLike.mem_coe]
    exact ⟨fun hv ↦ hv.1, fun hv ↦ ⟨hv, h v hv⟩⟩
  rw [progeny, ← Set.ncard_coe_finset, hcoe]

/-- A finite sample is exhausted by its truncations. -/
lemma exists_progeny_eq_ncard {c : Word N → ℕ} (hfin : (sample c : Set (Word N)).Finite) :
    ∃ k, progeny k c = (sample c : Set (Word N)).ncard := by
  obtain ⟨n, hn⟩ := (hfin.image List.length).bddAbove
  exact ⟨n + 1, progeny_eq_ncard fun u hu ↦ Nat.lt_succ_of_le (hn ⟨u, hu, rfl⟩)⟩

/-- The truncated progeny is a measurable function of the field: it reads finitely many
coordinates, one recursion step at a time. -/
lemma measurable_progeny (k : ℕ) : Measurable (progeny k : (Word N → ℕ) → ℕ) := by
  induction k with
  | zero =>
      have h : (progeny 0 : (Word N → ℕ) → ℕ) = fun _ ↦ 0 := funext fun c ↦ rfl
      rw [h]
      exact measurable_const
  | succ k ih =>
      have hrw : (progeny (k + 1) : (Word N → ℕ) → ℕ)
          = fun c ↦ 1 + ∑ i : Fin N,
              if (i : ℕ) < c [] then progeny k (fun w ↦ c (i :: w)) else 0 := by
        funext c
        rw [progeny_succ, childSet, Finset.sum_filter]
      rw [hrw]
      refine measurable_const.add (Finset.measurable_sum _ fun i _ ↦ ?_)
      refine Measurable.ite ?_ (ih.comp (measurable_shift i)) measurable_const
      exact measurable_pi_apply ([] : Word N) MeasurableSet.of_discrete

/-! ### The blocks of the splitting -/

/-- The law of one block of the splitting, read off `map_split`. -/
lemma map_split_apply (θ : Offspring J) (i : Option (Fin N)) :
    (sampleMeasure (N := N) θ).map (fun c ↦ split c i)
      = Measure.infinitePi (fun _ : Branch N i ↦ θ.law) := by
  have h : (fun c : Word N → ℕ ↦ split c i)
      = (fun x : (i : Option (Fin N)) → Branch N i → ℕ ↦ x i) ∘ split := rfl
  rw [h, ← Measure.map_map (measurable_pi_apply i) measurable_split, map_split,
    Measure.infinitePi_map_eval]

/-- **The shift to a child is measure preserving**: the field of a subtree at the root is
a copy of the whole field. -/
lemma map_shift (θ : Offspring J) (i : Fin N) :
    (sampleMeasure (N := N) θ).map (fun c w ↦ c (i :: w)) = sampleMeasure θ :=
  map_split_apply θ (some i)

/-- **The blocks of the splitting are independent**: the offspring count at the root and
the fields of the `N` subtrees hanging off it. -/
theorem iIndepFun_split (θ : Offspring J) :
    iIndepFun (fun (i : Option (Fin N)) (c : Word N → ℕ) ↦ split c i) (sampleMeasure θ) := by
  have hmeas : ∀ i : Option (Fin N), Measurable (fun c : Word N → ℕ ↦ split c i) :=
    fun i ↦ (measurable_pi_apply i).comp measurable_split
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hmeas]
  simp only [map_split_apply θ]
  exact map_split θ

/-! ### The progeny recursion -/

/-- The offspring count at the root is a measurable coordinate of the root block. -/
lemma measurableSet_rootIdx_eq (j : ℕ) :
    MeasurableSet {u : Branch N none → ℕ | u rootIdx = j} := by
  have h : {u : Branch N none → ℕ | u rootIdx = j}
      = (fun u : Branch N none → ℕ ↦ u rootIdx) ⁻¹' {j} := rfl
  rw [h]
  exact measurable_pi_apply rootIdx MeasurableSet.of_discrete

/-- The factors of the one-step product for the truncated progeny: the root block carries
the offspring count `j` together with one power of `s`, and each child block below `j` the
truncation one generation shorter. -/
noncomputable def progenyFactor (s : ℝ≥0∞) (k j : ℕ) :
    (i : Option (Fin N)) → (Branch N i → ℕ) → ℝ≥0∞
  | none => Set.indicator {u : Branch N none → ℕ | u rootIdx = j} fun _ ↦ s
  | some i => fun d ↦ if (i : ℕ) < j then s ^ progeny k d else 1

@[simp] lemma progenyFactor_none (s : ℝ≥0∞) (k j : ℕ) :
    progenyFactor (N := N) s k j none
      = Set.indicator {u : Branch N none → ℕ | u rootIdx = j} fun _ ↦ s := rfl

@[simp] lemma progenyFactor_some (s : ℝ≥0∞) (k j : ℕ) (i : Fin N) :
    progenyFactor s k j (some i) = fun d ↦ if (i : ℕ) < j then s ^ progeny k d else 1 := rfl

lemma measurable_progenyFactor (s : ℝ≥0∞) (k j : ℕ) (i : Option (Fin N)) :
    Measurable (progenyFactor (N := N) s k j i) := by
  cases i with
  | none => exact measurable_const.indicator (measurableSet_rootIdx_eq j)
  | some i =>
      rw [progenyFactor_some]
      by_cases hij : (i : ℕ) < j
      · simp only [if_pos hij]
        exact Measurable.of_discrete.comp (measurable_progeny k)
      · simp only [if_neg hij]
        exact measurable_const

/-- The root factor is the indicator of the offspring count at the root. -/
lemma progenyFactor_none_split (s : ℝ≥0∞) (k j : ℕ) (c : Word N → ℕ) :
    progenyFactor (N := N) s k j none (split c none)
      = Set.indicator {c : Word N → ℕ | c [] = j} (fun _ ↦ s) c := by
  by_cases hc : c [] = j
  · have h1 : split c none ∈ {u : Branch N none → ℕ | u rootIdx = j} := hc
    have h2 : c ∈ {c : Word N → ℕ | c [] = j} := hc
    rw [progenyFactor_none, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h1 : split c none ∉ {u : Branch N none → ℕ | u rootIdx = j} := hc
    have h2 : c ∉ {c : Word N → ℕ | c [] = j} := hc
    rw [progenyFactor_none, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- **The one-step product.**  On the event that the root has `j` children the power of
the truncated progeny is the product over the blocks of the splitting of the factors, one
power of `s` for the root and the truncation of each of its subtrees. -/
lemma prod_progenyFactor (s : ℝ≥0∞) (k j : ℕ) (c : Word N → ℕ) :
    ∏ i : Option (Fin N), progenyFactor s k j i (split c i)
      = Set.indicator {c : Word N → ℕ | c [] = j} (fun c ↦ s ^ progeny (k + 1) c) c := by
  have hfac : ∀ i : Fin N, progenyFactor (N := N) s k j (some i) (split c (some i))
      = if (i : ℕ) < j then s ^ progeny k (fun w ↦ c (i :: w)) else 1 := fun _ ↦ rfl
  rw [Fintype.prod_option, progenyFactor_none_split,
    Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) ↦ hfac i,
    prod_ite_childSet _ _ fun _ _ ↦ rfl, Finset.prod_pow_eq_pow_sum]
  by_cases hc : c [] = j
  · have h2 : c ∈ {c : Word N → ℕ | c [] = j} := hc
    rw [Set.indicator_of_mem h2, Set.indicator_of_mem h2, progeny_succ, hc, pow_add, pow_one]
  · have h2 : c ∉ {c : Word N → ℕ | c [] = j} := hc
    rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h2, zero_mul]

/-- **One step of the progeny recursion at a fixed offspring count.**  The root has `j`
children and its truncation one generation longer has moment `s θ_j` times the `j`-th
power of the truncated moment: the blocks of the splitting are independent. -/
lemma lintegral_progeny_root (θ : Offspring J) (s : ℝ≥0∞) (k : ℕ) {j : ℕ} (hj : j ≤ N) :
    ∫⁻ c in {c : Word N → ℕ | c [] = j}, s ^ progeny (k + 1) c ∂(sampleMeasure θ)
      = s * ENNReal.ofReal (θ j)
        * (∫⁻ c, s ^ progeny k c ∂(sampleMeasure (N := N) θ)) ^ j := by
  set X : Option (Fin N) → (Word N → ℕ) → ℝ≥0∞ :=
    fun i ↦ progenyFactor (N := N) s k j i ∘ fun c ↦ split c i
  have hX : ∀ i : Option (Fin N), Measurable (X i) := fun i ↦
    (measurable_progenyFactor s k j i).comp ((measurable_pi_apply i).comp measurable_split)
  have hindep : iIndepFun X (sampleMeasure (N := N) θ) :=
    (iIndepFun_split θ).comp (progenyFactor (N := N) s k j) (measurable_progenyFactor s k j)
  have hprod : ∀ c : Word N → ℕ, ∏ i : Option (Fin N), X i c
      = Set.indicator {c : Word N → ℕ | c [] = j} (fun c ↦ s ^ progeny (k + 1) c) c :=
    fun c ↦ prod_progenyFactor s k j c
  have hnone : ∫⁻ c, X none c ∂(sampleMeasure (N := N) θ) = s * ENNReal.ofReal (θ j) := by
    have hfun : ∀ c : Word N → ℕ, X none c
        = Set.indicator {c : Word N → ℕ | c [] = j} (fun _ ↦ s) c :=
      fun c ↦ progenyFactor_none_split s k j c
    rw [lintegral_congr hfun, lintegral_indicator_const (measurableSet_root_eq j),
      sampleMeasure_coord θ [] j]
  have hsome : ∀ i : Fin N, ∫⁻ c, X (some i) c ∂(sampleMeasure (N := N) θ)
      = if (i : ℕ) < j then ∫⁻ c, s ^ progeny k c ∂(sampleMeasure (N := N) θ) else 1 := by
    intro i
    have hfun : ∀ c : Word N → ℕ, X (some i) c
        = if (i : ℕ) < j then s ^ progeny k (fun w ↦ c (i :: w)) else 1 := fun _ ↦ rfl
    rw [lintegral_congr hfun]
    by_cases hij : (i : ℕ) < j
    · have hfm : Measurable (fun d : Word N → ℕ ↦ s ^ progeny k d) :=
        Measurable.of_discrete.comp (measurable_progeny k)
      simp only [if_pos hij]
      rw [← lintegral_map hfm (measurable_shift i), map_shift θ i]
    · simp only [if_neg hij]
      simp
  rw [← lintegral_indicator (measurableSet_root_eq j),
    lintegral_congr fun c ↦ (hprod c).symm,
    lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ X hindep hX, Fintype.prod_option,
    hnone, Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) ↦ hsome i,
    prod_ite_lt (∫⁻ c, s ^ progeny k c ∂(sampleMeasure (N := N) θ)) hj]

/-- **The progeny recursion** `F_{k+1}(s) = s f(F_k(s))`: summing the one-step masses over
the offspring count at the root. -/
theorem lintegral_pow_progeny_succ (θ : Offspring J) (hJN : J ≤ N) (s : ℝ≥0∞) (k : ℕ) :
    ∫⁻ c, s ^ progeny (k + 1) c ∂(sampleMeasure (N := N) θ)
      = ∑ j ∈ Finset.range (J + 1), s * ENNReal.ofReal (θ j)
          * (∫⁻ c, s ^ progeny k c ∂(sampleMeasure (N := N) θ)) ^ j := by
  have hmeas : ∀ j : ℕ, MeasurableSet {c : Word N → ℕ | c [] = j} := measurableSet_root_eq
  have hdisj : Pairwise (Function.onFun Disjoint fun j : ℕ ↦ {c : Word N → ℕ | c [] = j}) := by
    intro m l hml
    exact Set.disjoint_left.mpr fun c hc hc' ↦ hml (hc.symm.trans hc')
  have hcover : (⋃ j : ℕ, {c : Word N → ℕ | c [] = j}) = (Set.univ : Set (Word N → ℕ)) := by
    ext c
    simp
  have hsplit := lintegral_iUnion (μ := sampleMeasure (N := N) θ) hmeas hdisj
    (fun c ↦ s ^ progeny (k + 1) c)
  rw [hcover, Measure.restrict_univ] at hsplit
  have hvanish : ∀ j ∉ Finset.range (J + 1),
      ∫⁻ c in {c : Word N → ℕ | c [] = j}, s ^ progeny (k + 1) c
        ∂(sampleMeasure (N := N) θ) = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    refine setLIntegral_measure_zero _ _ ?_
    rw [sampleMeasure_coord θ [] j, θ.vanishing j (by omega), ENNReal.ofReal_zero]
  rw [hsplit, tsum_eq_sum hvanish]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  exact lintegral_progeny_root θ s k
    (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hJN)

/-! ### The moment of a truncation -/

/-- **The truncated moments are bounded by a fixed point of the progeny equation.**  The
recursion turns the bound at one generation into the same bound at the next, the fixed
point being exactly what the generating function returns. -/
theorem lintegral_pow_progeny_le (θ : Offspring J) (hJN : J ≤ N) {σ y : ℝ} (hσ : 0 ≤ σ)
    (hy : 1 ≤ y) (hfix : σ * Offspring.gen θ y = y) (k : ℕ) :
    ∫⁻ c, ENNReal.ofReal σ ^ progeny k c ∂(sampleMeasure (N := N) θ) ≤ ENNReal.ofReal y := by
  have hy0 : (0 : ℝ) ≤ y := le_trans zero_le_one hy
  induction k with
  | zero =>
      have hcst : ∀ c : Word N → ℕ, ENNReal.ofReal σ ^ progeny 0 c = 1 := by
        intro c
        rw [progeny_zero, pow_zero]
      rw [lintegral_congr hcst, lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hy
  | succ k ih =>
      rw [lintegral_pow_progeny_succ θ hJN]
      have hstep : ∀ j ∈ Finset.range (J + 1),
          ENNReal.ofReal σ * ENNReal.ofReal (θ j)
              * (∫⁻ c, ENNReal.ofReal σ ^ progeny k c ∂(sampleMeasure (N := N) θ)) ^ j
            ≤ ENNReal.ofReal σ * ENNReal.ofReal (θ j) * ENNReal.ofReal y ^ j :=
        fun j _ ↦ mul_le_mul' le_rfl (pow_le_pow_left' ih j)
      refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
      have hterm : ∀ j ∈ Finset.range (J + 1),
          ENNReal.ofReal σ * ENNReal.ofReal (θ j) * ENNReal.ofReal y ^ j
            = ENNReal.ofReal (σ * θ j * y ^ j) := by
        intro j _
        rw [ENNReal.ofReal_mul (mul_nonneg hσ (θ.nonneg j)), ENNReal.ofReal_mul hσ,
          ENNReal.ofReal_pow hy0]
      have hnn : ∀ j ∈ Finset.range (J + 1), (0 : ℝ) ≤ σ * θ j * y ^ j :=
        fun j _ ↦ mul_nonneg (mul_nonneg hσ (θ.nonneg j)) (pow_nonneg hy0 j)
      have hsum : ∑ j ∈ Finset.range (J + 1), σ * θ j * y ^ j = y := by
        conv_rhs => rw [← hfix]
        rw [Offspring.gen, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg hnn, hsum]

/-! ### The progeny equation -/

namespace Offspring

variable (θ : Offspring J)

/-- **A subcritical generating function drops below the diagonal.**  The difference
quotient of `one_sub_gen` takes the value `m < 1` at one, so it stays below one nearby,
and above one that reads `f(y) < y`. -/
theorem exists_gen_lt_self (h : θ.IsSubcritical) : ∃ y : ℝ, 1 < y ∧ gen θ y < y := by
  have hmean : mean θ < 1 := h
  have hopen : IsOpen {s : ℝ | genSlope θ s < 1} :=
    isOpen_lt θ.continuous_genSlope continuous_const
  have hone : (1 : ℝ) ∈ {s : ℝ | genSlope θ s < 1} := by
    show genSlope θ 1 < 1
    rw [θ.genSlope_one]
    exact hmean
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
  refine ⟨1 + ε / 2, by linarith, ?_⟩
  have hmem : 1 + ε / 2 ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have hslope : genSlope θ (1 + ε / 2) < 1 := hball hmem
  have hquot := θ.one_sub_gen (1 + ε / 2)
  have hrw : (1 - (1 + ε / 2)) * genSlope θ (1 + ε / 2)
      = -(ε / 2 * genSlope θ (1 + ε / 2)) := by ring
  rw [hrw] at hquot
  have hlt : ε / 2 * genSlope θ (1 + ε / 2) < ε / 2 * 1 :=
    mul_lt_mul_of_pos_left hslope (by linarith)
  linarith

/-- **The progeny equation has a fixed point above one.**  A subcritical law has `y > 1`
with `f(y) < y`, and then `s = y / f(y)` exceeds one and solves `s f(y) = y`. -/
theorem exists_progeny_fixedPoint (h : θ.IsSubcritical) :
    ∃ s y : ℝ, 1 < s ∧ 1 < y ∧ s * gen θ y = y := by
  obtain ⟨y, hy1, hlt⟩ := θ.exists_gen_lt_self h
  have hf1 : 1 ≤ gen θ y := by
    calc (1 : ℝ) = gen θ 1 := θ.gen_one.symm
      _ ≤ gen θ y := θ.gen_mono zero_le_one hy1.le
  have hne : gen θ y ≠ 0 := by linarith
  refine ⟨y / gen θ y, y, (one_lt_div (by linarith)).mpr hlt, hy1, ?_⟩
  field_simp

end Offspring

/-! ### The exponential moment of the total progeny -/

/-- **The exponential moment of the total progeny**, at a fixed point of the progeny
equation: the truncations exhaust a finite sample, so the monotone convergence theorem
carries the uniform bound of `lintegral_pow_progeny_le` to the number of vertices. -/
theorem lintegral_pow_ncard_le (θ : Offspring J) (hJN : J ≤ N) {σ y : ℝ} (hσ : 1 ≤ σ)
    (hy : 1 ≤ y) (hfix : σ * Offspring.gen θ y = y) :
    ∫⁻ c, ENNReal.ofReal σ ^ ((sample c : Set (Word N)).ncard) ∂(sampleMeasure (N := N) θ)
      ≤ ENNReal.ofReal y := by
  have hs1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal σ := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hσ
  have hmeasf : ∀ k : ℕ,
      Measurable fun c : Word N → ℕ ↦ ENNReal.ofReal σ ^ progeny k c :=
    fun k ↦ Measurable.of_discrete.comp (measurable_progeny k)
  have hmono : Monotone fun (k : ℕ) (c : Word N → ℕ) ↦ ENNReal.ofReal σ ^ progeny k c :=
    fun _ _ hkl c ↦ pow_le_pow_right' hs1 (progeny_mono c hkl)
  have hpt : ∀ c : Word N → ℕ, ENNReal.ofReal σ ^ ((sample c : Set (Word N)).ncard)
      ≤ ⨆ k, ENNReal.ofReal σ ^ progeny k c := by
    intro c
    by_cases hfin : (sample c : Set (Word N)).Finite
    · obtain ⟨k, hk⟩ := exists_progeny_eq_ncard hfin
      rw [← hk]
      exact le_iSup (fun k ↦ ENNReal.ofReal σ ^ progeny k c) k
    · rw [Set.Infinite.ncard hfin, pow_zero]
      refine le_trans (le_of_eq ?_) (le_iSup (fun k ↦ ENNReal.ofReal σ ^ progeny k c) 0)
      rw [progeny_zero, pow_zero]
  calc ∫⁻ c, ENNReal.ofReal σ ^ ((sample c : Set (Word N)).ncard)
        ∂(sampleMeasure (N := N) θ)
      ≤ ∫⁻ c, ⨆ k, ENNReal.ofReal σ ^ progeny k c ∂(sampleMeasure (N := N) θ) :=
        lintegral_mono hpt
    _ = ⨆ k, ∫⁻ c, ENNReal.ofReal σ ^ progeny k c ∂(sampleMeasure (N := N) θ) :=
        lintegral_iSup hmeasf hmono
    _ ≤ ENNReal.ofReal y :=
        iSup_le fun k ↦ lintegral_pow_progeny_le θ hJN (le_trans zero_le_one hσ) hy hfix k

/-- **The total progeny of a subcritical law has an exponential moment.**  This is the
input `thm:shape-mass`\labelcref{it:shape-mass-tail} takes from the conjugate law: the
number of vertices of a bush is exponentially integrable. -/
theorem exists_exponential_moment (θ : Offspring J) (hJN : J ≤ N) (h : θ.IsSubcritical) :
    ∃ σ : ℝ, 1 < σ ∧
      ∫⁻ c, ENNReal.ofReal σ ^ ((sample c : Set (Word N)).ncard)
        ∂(sampleMeasure (N := N) θ) < ⊤ := by
  obtain ⟨s, y, hs, hy, hfix⟩ := θ.exists_progeny_fixedPoint h
  exact ⟨s, hs,
    lt_of_le_of_lt (lintegral_pow_ncard_le θ hJN hs.le hy.le hfix) ENNReal.ofReal_lt_top⟩

/-! ### The number of vertices of a random tree -/

/-- A subtree is a prescribed finite set of words on a measurable event: it contains that
set and nothing else. -/
lemma measurableSet_subtree_eq (F : Finset (Word N)) :
    MeasurableSet {T : Subtree N | (T : Set (Word N)) = (F : Set (Word N))} := by
  have h : {T : Subtree N | (T : Set (Word N)) = (F : Set (Word N))}
      = {T : Subtree N | (F : Set (Word N)) ⊆ (T : Set (Word N))}
        ∩ ⋂ v : Word N, ⋂ _ : v ∉ (F : Set (Word N)), {T : Subtree N | v ∈ T}ᶜ := by
    ext T
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      SetLike.mem_coe]
    constructor
    · intro hT
      refine ⟨hT.ge, fun v hv hmem ↦ hv ?_⟩
      have hvF : v ∈ (F : Set (Word N)) := by rw [← hT]; exact hmem
      exact Finset.mem_coe.mp hvF
    · rintro ⟨hsub, hout⟩
      refine Set.Subset.antisymm (fun v hv ↦ ?_) hsub
      by_contra hvF
      exact hout v hvF hv
  rw [h]
  exact (measurableSet_subset_subtree _).inter
    (MeasurableSet.iInter fun v ↦ MeasurableSet.iInter fun _ ↦ (measurableSet_mem_subtree v).compl)

/-- **The number of vertices is a random variable.**  A positive value is attained exactly
on the countably many finite sets of words of that size, and the value zero on the
complement of the others. -/
lemma measurableSet_ncard_eq (n : ℕ) :
    MeasurableSet {T : Subtree N | (T : Set (Word N)).ncard = n} := by
  have hpos : ∀ m : ℕ, 0 < m → MeasurableSet {T : Subtree N | (T : Set (Word N)).ncard = m} := by
    intro m hm
    have h : {T : Subtree N | (T : Set (Word N)).ncard = m}
        = ⋃ F : {F : Finset (Word N) // F.card = m},
            {T : Subtree N | (T : Set (Word N)) = ((F : Finset (Word N)) : Set (Word N))} := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hT
        have hfin : (T : Set (Word N)).Finite := by
          by_contra hinf
          rw [Set.Infinite.ncard hinf] at hT
          omega
        refine ⟨⟨hfin.toFinset, ?_⟩, ?_⟩
        · rw [← Set.ncard_eq_toFinset_card _ hfin]
          exact hT
        · rw [hfin.coe_toFinset]
      · rintro ⟨⟨F, hF⟩, hT⟩
        rw [hT, Set.ncard_coe_finset, hF]
    rw [h]
    exact MeasurableSet.iUnion fun F ↦ measurableSet_subtree_eq _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : {T : Subtree N | (T : Set (Word N)).ncard = 0}
        = (⋃ m : ℕ, {T : Subtree N | (T : Set (Word N)).ncard = m + 1})ᶜ := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      constructor
      · intro hT m
        omega
      · intro hT
        by_contra hne
        exact hT ((T : Set (Word N)).ncard - 1) (by omega)
    rw [h]
    exact (MeasurableSet.iUnion fun m ↦ hpos (m + 1) (Nat.succ_pos m)).compl
  · exact hpos n hn

/-- The power of the number of vertices is a measurable function of the tree. -/
lemma measurable_pow_ncard (s : ℝ≥0∞) :
    Measurable fun T : Subtree N ↦ s ^ ((T : Set (Word N)).ncard) := by
  refine Measurable.comp (f := fun T : Subtree N ↦ (T : Set (Word N)).ncard)
    (g := fun n : ℕ ↦ s ^ n) Measurable.of_discrete ?_
  exact measurable_to_countable' fun n ↦ measurableSet_ncard_eq n

/-! ### The exponential moment of a bush -/

/-- **The exponential moment of the size of a bush.**  A sample conditioned to die is a
Galton-Watson tree with the conjugate law, so the moment of `lintegral_pow_ncard_le` at
that law transports along `bushTreeLaw_eq_treeLaw`. -/
theorem lintegral_pow_ncard_bushMeasure_le (θ : Offspring J) (hJN : J ≤ N)
    (hq0 : 0 < θ.extinction) {σ y : ℝ} (hσ : 1 ≤ σ) (hy : 1 ≤ y)
    (hfix : σ * Offspring.gen (θ.conjugate hq0) y = y) :
    ∫⁻ c, ENNReal.ofReal σ ^ ((sample c : Set (Word N)).ncard) ∂(bushMeasure (N := N) θ)
      ≤ ENNReal.ofReal y := by
  have hg := measurable_pow_ncard (N := N) (ENNReal.ofReal σ)
  have hbush : ∫⁻ c, ENNReal.ofReal σ ^ ((sample c : Set (Word N)).ncard)
      ∂(bushMeasure (N := N) θ)
      = ∫⁻ T, ENNReal.ofReal σ ^ ((T : Set (Word N)).ncard) ∂(bushTreeLaw (N := N) θ) :=
    (lintegral_map hg measurable_sample).symm
  rw [hbush, bushTreeLaw_eq_treeLaw θ hJN hq0, treeLaw, lintegral_map hg measurable_sample]
  exact lintegral_pow_ncard_le _ hJN hσ hy hfix

/-- **The size of a bush has an exponential moment** once the conjugate law is subcritical:
the input `thm:shape-mass`\labelcref{it:shape-mass-tail} takes from the bushes of
`thm:harris`\labelcref{it:harris-bushes}. -/
theorem exists_exponential_moment_bushMeasure (θ : Offspring J) (hJN : J ≤ N)
    (hq0 : 0 < θ.extinction) (h : (θ.conjugate hq0).IsSubcritical) :
    ∃ σ : ℝ, 1 < σ ∧
      ∫⁻ c, ENNReal.ofReal σ ^ ((sample c : Set (Word N)).ncard)
        ∂(bushMeasure (N := N) θ) < ⊤ := by
  obtain ⟨s, y, hs, hy, hfix⟩ := (θ.conjugate hq0).exists_progeny_fixedPoint h
  exact ⟨s, hs, lt_of_le_of_lt
    (lintegral_pow_ncard_bushMeasure_le θ hJN hq0 hs.le hy.le hfix) ENNReal.ofReal_lt_top⟩

end BranchingProcess


