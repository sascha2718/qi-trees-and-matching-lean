/-
`sec:gw-trees` of `prelims.tex`: the law of the Galton-Watson sample.  The
offspring layer of `Offspring` and the genealogy of `Sample` are joined here:
the i.i.d. field of `Field` is fed the offspring law, and the extinction
probability, defined as the least fixed point of the generating function, is
identified with the probability that the sample dies out.

* `Offspring.toPMF` and `Offspring.law`: the offspring law as a `PMF ℕ` and as a
  measure on `ℕ`, with `toPMF_apply` and `law_singleton`.
* `Offspring.genIter`: the iterates `f^n(0)` of the generating function, with
  `genIter_mono`, `genIter_le_extinction` and `tendsto_genIter`, their
  convergence to the least fixed point.
* `sampleMeasure`: the law of the offspring field on `Word N → ℕ`, a probability
  measure, with `sampleMeasure_coord` for the law at a single vertex.
* `measurableSet_mem_sample`, `measurableSet_noLevel`, `measurableSet_survives`:
  the events the theorem needs are measurable.
* `noLevel`, `finite_sample_of_noLevel`, `survives_iff_forall_level`: extinction
  is the exhaustion by the events that a generation is empty.
* `Branch`, `rootSplit`, `split`, `map_split`: the field splits at the root into
  the offspring count there and `N` independent copies of itself, one per
  letter.
* `levelBox`, `split_preimage_levelBox`, `sampleMeasure_root_noLevel`: the
  one-step event as a product event, of mass `θ_k q_n^k`.
* `sampleMeasure_noLevel_succ` and `sampleMeasure_noLevel`: the recursion
  `q_{n+1} = f(q_n)`, and the masses read off as the iterates.
* `sampleMeasure_not_survives`: **the extinction probability is the probability
  of extinction**, `P(¬ Survives) = q`, with `sampleMeasure_survives`.

The alphabet has to be wide enough to carry the law: the theorems of the last
three groups hypothesise `J ≤ N`, without which a vertex of the sample keeps
only its first `N` children.
-/
import BranchingProcess.Offspring
import BranchingProcess.Sample
import BranchingProcess.Field
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Order.MonotoneConvergence

namespace BranchingProcess

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

variable {J N : ℕ}

/-! ### The offspring law as a probability mass function -/

namespace Offspring

/-- The offspring law read as a probability mass function on `ℕ`: the real
masses `θ_j` transported to `ℝ≥0∞`.  Summability is the finite sum `θ.total`,
the masses above `J` vanishing. -/
noncomputable def toPMF (θ : Offspring J) : PMF ℕ :=
  ⟨fun j ↦ ENNReal.ofReal (θ j), by
    have hzero : ∀ j ∉ Finset.range (J + 1), ENNReal.ofReal (θ j) = 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [θ.vanishing j (by omega), ENNReal.ofReal_zero]
    have hsum : HasSum (fun j ↦ ENNReal.ofReal (θ j))
        (∑ j ∈ Finset.range (J + 1), ENNReal.ofReal (θ j)) :=
      hasSum_sum_of_ne_finset_zero hzero
    rwa [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ θ.nonneg j), θ.total,
      ENNReal.ofReal_one] at hsum⟩

/-- The mass function of `toPMF` is the offspring law. -/
@[simp] lemma toPMF_apply (θ : Offspring J) (j : ℕ) : θ.toPMF j = ENNReal.ofReal (θ j) := rfl

/-- The one-vertex law: the measure on `ℕ` with mass `θ_j` at `j`. -/
noncomputable def law (θ : Offspring J) : Measure ℕ := θ.toPMF.toMeasure

instance isProbabilityMeasure_law (θ : Offspring J) : IsProbabilityMeasure θ.law :=
  inferInstanceAs (IsProbabilityMeasure θ.toPMF.toMeasure)

/-- The one-vertex law gives mass `θ_k` to `{k}`. -/
@[simp] lemma law_singleton (θ : Offspring J) (k : ℕ) :
    θ.law {k} = ENNReal.ofReal (θ k) := by
  rw [law, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k), toPMF_apply]

end Offspring

/-! ### The iterates of the generating function -/

namespace Offspring

variable (θ : Offspring J)

/-- The iterates `f^n(0)` of the generating function at zero: the probability
that the tree dies out by generation `n`. -/
noncomputable def genIter (n : ℕ) : ℝ := (gen θ)^[n] 0

@[simp] lemma genIter_zero : θ.genIter 0 = 0 := rfl

/-- One step of the recursion `q_{n+1} = f(q_n)`. -/
lemma genIter_succ (n : ℕ) : θ.genIter (n + 1) = gen θ (θ.genIter n) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterates stay in `[0,1]`, where `f` maps `[0,1]` to itself. -/
lemma genIter_mem (n : ℕ) : θ.genIter n ∈ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero => exact ⟨le_rfl, zero_le_one⟩
  | succ n ih =>
      rw [genIter_succ]
      exact ⟨θ.gen_nonneg ih.1, θ.gen_le_one ih⟩

lemma genIter_nonneg (n : ℕ) : 0 ≤ θ.genIter n := (θ.genIter_mem n).1

lemma genIter_le_one (n : ℕ) : θ.genIter n ≤ 1 := (θ.genIter_mem n).2

/-- The iterates increase, `f` being monotone and `f(0) ≥ 0`. -/
lemma genIter_mono : Monotone θ.genIter := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  induction n with
  | zero =>
      rw [genIter_zero, genIter_succ, genIter_zero]
      exact θ.gen_nonneg le_rfl
  | succ n ih =>
      have h := θ.gen_mono (θ.genIter_nonneg n) ih
      rwa [← θ.genIter_succ n, ← θ.genIter_succ (n + 1)] at h

/-- Every iterate lies below the extinction probability, that being a fixed
point of `f`. -/
lemma genIter_le_extinction (n : ℕ) : θ.genIter n ≤ θ.extinction := by
  induction n with
  | zero => exact θ.extinction_nonneg
  | succ n ih =>
      rw [genIter_succ, ← θ.gen_extinction]
      exact θ.gen_mono (θ.genIter_nonneg n) ih

/-- **The iterates converge to the extinction probability.** They increase, so
they converge; the limit is a fixed point of `f` in `[0,1]` by continuity, hence
at least `q` by minimality, and at most `q` termwise. -/
theorem tendsto_genIter : Filter.Tendsto θ.genIter Filter.atTop (𝓝 θ.extinction) := by
  have hbdd : BddAbove (Set.range θ.genIter) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact θ.genIter_le_one n⟩
  set L : ℝ := ⨆ n, θ.genIter n with hL
  have htend : Filter.Tendsto θ.genIter Filter.atTop (𝓝 L) :=
    tendsto_atTop_ciSup θ.genIter_mono hbdd
  have hfix : gen θ L = L := by
    have h1 : Filter.Tendsto (fun n ↦ θ.genIter (n + 1)) Filter.atTop (𝓝 L) :=
      htend.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun n ↦ gen θ (θ.genIter n)) Filter.atTop (𝓝 (gen θ L)) :=
      (θ.continuous_gen.tendsto L).comp htend
    simp only [genIter_succ] at h1
    exact tendsto_nhds_unique h2 h1
  have hLmem : L ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨le_ciSup_of_le hbdd 0 (le_of_eq θ.genIter_zero.symm), ?_⟩
    exact ciSup_le fun n ↦ θ.genIter_le_one n
  have hle : θ.extinction ≤ L := θ.extinction_le_of_fixed hLmem hfix
  have hge : L ≤ θ.extinction := ciSup_le fun n ↦ θ.genIter_le_extinction n
  rwa [le_antisymm hge hle] at htend

end Offspring

/-! ### The law of the offspring field -/

/-- **The law of the offspring field.** The i.i.d. field on `Word N → ℕ` whose
coordinates are independent with the offspring law `θ`; the sample of `Sample`
under this measure is the Galton-Watson tree of `θ`. -/
noncomputable def sampleMeasure (θ : Offspring J) : Measure (Word N → ℕ) :=
  fieldMeasure θ.law

instance isProbabilityMeasure_sampleMeasure (θ : Offspring J) :
    IsProbabilityMeasure (sampleMeasure (N := N) θ) :=
  inferInstanceAs (IsProbabilityMeasure (fieldMeasure θ.law))

/-- Each vertex has the offspring law: the coordinate at `v` takes the value `k`
with probability `θ_k`. -/
theorem sampleMeasure_coord (θ : Offspring J) (v : Word N) (k : ℕ) :
    sampleMeasure θ {c : Word N → ℕ | c v = k} = ENNReal.ofReal (θ k) := by
  show fieldMeasure θ.law (coord v ⁻¹' {k}) = ENNReal.ofReal (θ k)
  rw [coord_law _ v (measurableSet_singleton k), Offspring.law_singleton]

/-! ### Measurability of the events -/

/-- Membership of a fixed word in the sample is a measurable event: it is the
finite intersection, one condition per letter, of conditions on single
coordinates, and `ℕ` is discrete. -/
theorem measurableSet_mem_sample (v : Word N) :
    MeasurableSet {c : Word N → ℕ | v ∈ sample c} := by
  induction v using List.reverseRecOn with
  | nil =>
      have h : {c : Word N → ℕ | ([] : Word N) ∈ sample c} = Set.univ := by
        ext c; simp
      rw [h]
      exact MeasurableSet.univ
  | append_singleton u j ih =>
      have h : {c : Word N → ℕ | u ++ [j] ∈ sample c}
          = {c : Word N → ℕ | u ∈ sample c} ∩ coord u ⁻¹' {k : ℕ | (j : ℕ) < k} := by
        ext c
        simp [mem_sample_append_singleton, coord]
      rw [h]
      exact ih.inter (measurable_coord u MeasurableSet.of_discrete)

/-! ### Extinction as the exhaustion by empty generations -/

/-- The event that generation `n` is empty: no word of length `n` lies in the
sample.  These events increase to extinction. -/
def noLevel (n : ℕ) : Set (Word N → ℕ) :=
  {c : Word N → ℕ | ∀ v : Word N, v.length = n → v ∉ sample c}

/-- Membership in `noLevel`, unfolded. -/
theorem mem_noLevel_iff {c : Word N → ℕ} {n : ℕ} :
    c ∈ noLevel n ↔ ∀ v : Word N, v.length = n → v ∉ sample c := Iff.rfl

/-- **An empty generation kills the sample.** A sample missing a whole generation is
finite: the recursion runs down the `N` subtrees at the root. -/
theorem finite_sample_of_noLevel :
    ∀ (n : ℕ) (c : Word N → ℕ), c ∈ noLevel n → (sample c : Set (Word N)).Finite := by
  intro n
  induction n with
  | zero => exact fun c hc ↦ absurd (nil_mem_sample c) (hc [] rfl)
  | succ n ih =>
      intro c hc
      refine finite_sample_of_forall_finite fun j hj ↦ ih _ fun u hu hmem ↦ ?_
      refine hc (j :: u) (by simp [hu]) ?_
      exact (append_mem_sample_iff c [j] u).mpr ⟨singleton_mem_sample_iff.mpr hj, hmem⟩

/-- **Survival is reaching every generation.** -/
theorem survives_iff_forall_level {c : Word N → ℕ} :
    Survives c ↔ ∀ n, ∃ v : Word N, v.length = n ∧ v ∈ sample c := by
  constructor
  · intro h n
    by_contra hn
    push Not at hn
    exact h (finite_sample_of_noLevel n c hn)
  · intro h
    choose f hlen hmem using h
    refine Set.infinite_of_injective_forall_mem (f := f) (fun m n hmn ↦ ?_) hmem
    rw [← hlen m, ← hlen n, hmn]

/-- Extinction is the failure of some generation to be reached. -/
theorem not_survives_iff_exists_noLevel {c : Word N → ℕ} :
    ¬ Survives c ↔ ∃ n, c ∈ noLevel n := by
  rw [survives_iff_forall_level]
  push Not
  simp only [mem_noLevel_iff]

/-- The empty generations increase: a missing generation makes every later one
missing, the sample being prefix-closed. -/
theorem noLevel_mono : Monotone (noLevel (N := N)) := by
  refine monotone_nat_of_le_succ fun n c hc v hv hmem ↦ ?_
  refine hc (v.take n) (by simp [hv]) ?_
  exact Subtree.mem_of_prefix (List.take_prefix n v) hmem

/-- Extinction is the union of the empty-generation events. -/
theorem notSurvives_eq_iUnion :
    {c : Word N → ℕ | ¬ Survives c} = ⋃ n, noLevel (N := N) n := by
  ext c
  simpa using not_survives_iff_exists_noLevel

/-- The empty-generation event is measurable: a countable intersection over the
words of the generation, `Word N` being countable. -/
theorem measurableSet_noLevel (n : ℕ) : MeasurableSet (noLevel (N := N) n) := by
  have h : noLevel (N := N) n
      = ⋂ v : Word N, ⋂ _ : v.length = n, {c : Word N → ℕ | v ∈ sample c}ᶜ := by
    ext c
    simp [mem_noLevel_iff]
  rw [h]
  exact MeasurableSet.iInter fun v ↦
    MeasurableSet.iInter fun _ ↦ (measurableSet_mem_sample v).compl

/-- **Survival is a measurable event.** -/
theorem measurableSet_survives : MeasurableSet {c : Word N → ℕ | Survives c} := by
  have h : {c : Word N → ℕ | Survives c} = (⋃ n, noLevel (N := N) n)ᶜ := by
    rw [← notSurvives_eq_iUnion]
    ext c
    simp
  rw [h]
  exact (MeasurableSet.iUnion fun n ↦ measurableSet_noLevel n).compl

/-! ### The splitting of the field at the root -/

/-- The index of the splitting of the ambient tree at the root: `none` names the
root, which carries a single coordinate, and `some j` the copy of the tree
hanging under the letter `j`. -/
@[implicit_reducible] def Branch (N : ℕ) : Option (Fin N) → Type
  | none => Unit
  | some _ => Word N

/-- The splitting bijection: a word is either the root or a letter followed by a
word. -/
def rootSplit : (i : Option (Fin N)) → Branch N i → Word N
  | none, _ => []
  | some j, w => j :: w

/-- The single coordinate carried by the root block. -/
def rootIdx : Branch N none := ()

/-- Constraining the root coordinate of the branch space is a measurable event. -/
lemma measurableSet_rootIdx_preimage (s : Set ℕ) :
    MeasurableSet ((fun u : Branch N none → ℕ ↦ u rootIdx) ⁻¹' s) :=
  measurable_pi_apply (X := fun _ : Branch N none ↦ ℕ) rootIdx MeasurableSet.of_discrete

@[simp] lemma rootSplit_none (u : Branch N none) : rootSplit none u = ([] : Word N) := rfl

@[simp] lemma rootSplit_some (j : Fin N) (w : Branch N (some j)) :
    rootSplit (some j) w = j :: w := rfl

/-- The splitting is injective, `[]` being the one word that is not a letter
followed by a word. -/
lemma injective_rootSplit :
    Function.Injective fun p : (i : Option (Fin N)) × Branch N i ↦ rootSplit p.1 p.2 := by
  rintro ⟨(_ | j), w⟩ ⟨(_ | j'), w'⟩ h
  · rfl
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [rootSplit_some] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- **The splitting map**: the offspring count at the root together with the
offspring fields of the `N` subtrees at the children of the root. -/
def split (c : Word N → ℕ) : (i : Option (Fin N)) → Branch N i → ℕ :=
  fun i x ↦ c (rootSplit i x)

@[simp] lemma split_none (c : Word N → ℕ) (u : Branch N none) : split c none u = c [] := rfl

@[simp] lemma split_some (c : Word N → ℕ) (j : Fin N) (w : Branch N (some j)) :
    split c (some j) w = c (j :: w) := rfl

lemma measurable_split : Measurable (split : (Word N → ℕ) → ∀ i, Branch N i → ℕ) :=
  Measurable.of_eval fun _ ↦ Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- **The branching property of the law.** Under the splitting the field becomes
the offspring count at the root together with `N` independent copies of itself,
one for each letter. -/
theorem map_split (θ : Offspring J) :
    (sampleMeasure (N := N) θ).map split
      = Measure.infinitePi (fun i : Option (Fin N) ↦
          Measure.infinitePi (fun _ : Branch N i ↦ θ.law)) := by
  have h1 : (Measure.infinitePi (fun _ : Word N ↦ θ.law)).map
      (fun c (p : (i : Option (Fin N)) × Branch N i) ↦ c (rootSplit p.1 p.2))
      = Measure.infinitePi (fun _ : (i : Option (Fin N)) × Branch N i ↦ θ.law) :=
    Measure.map_infinitePi_infinitePi_of_inj injective_rootSplit
  have h2 := Measure.infinitePi_map_piCurry
    (X := fun (i : Option (Fin N)) (_ : Branch N i) ↦ ℕ)
    (μ := fun (_ : Option (Fin N)) (_ : Branch N _) ↦ θ.law)
  have hcomp : (split : (Word N → ℕ) → ∀ i, Branch N i → ℕ)
      = (MeasurableEquiv.piCurry (fun (i : Option (Fin N)) (_ : Branch N i) ↦ ℕ))
        ∘ (fun c (p : (i : Option (Fin N)) × Branch N i) ↦ c (rootSplit p.1 p.2)) := rfl
  show (Measure.infinitePi (fun _ : Word N ↦ θ.law)).map split = _
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.piCurry _).measurable
    (Measurable.of_eval fun _ ↦ measurable_pi_apply _), h1, h2]

/-! ### One step of the recursion -/

/-- The product event at the root: the root has `k` children, and generation `n`
is empty in the subtree hanging under each of the first `k` of them. -/
def levelBox (n k : ℕ) : (i : Option (Fin N)) → Set (Branch N i → ℕ)
  | none => {u | u rootIdx = k}
  | some j => if (j : ℕ) < k then noLevel n else Set.univ

@[simp] lemma levelBox_none (n k : ℕ) :
    levelBox (N := N) n k none = {u : Branch N none → ℕ | u rootIdx = k} := rfl

@[simp] lemma levelBox_some (n k : ℕ) (j : Fin N) :
    levelBox n k (some j) = if (j : ℕ) < k then noLevel n else Set.univ := rfl

lemma measurableSet_levelBox (n k : ℕ) (i : Option (Fin N)) :
    MeasurableSet (levelBox (N := N) n k i) := by
  cases i with
  | none =>
      exact measurableSet_rootIdx_preimage {k}
  | some j =>
      rw [levelBox_some]
      split
      · exact measurableSet_noLevel n
      · exact MeasurableSet.univ

/-- **The product event is the one-step event.** The sample misses generation
`n+1` and has `k` children at the root exactly when it has `k` children at the
root and each of the corresponding subtrees misses generation `n`. -/
lemma split_preimage_levelBox (n k : ℕ) :
    split ⁻¹' Set.univ.pi (levelBox (N := N) n k)
      = {c : Word N → ℕ | c [] = k} ∩ noLevel (n + 1) := by
  ext c
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · intro h
    have hroot : c [] = k := h none
    refine ⟨hroot, fun v hv hmem ↦ ?_⟩
    cases v with
    | nil => simp at hv
    | cons j u =>
        have hu : u.length = n := by simpa using hv
        have hsplit : ([j] ++ u) ∈ sample c := hmem
        rw [append_mem_sample_iff] at hsplit
        have hj : (j : ℕ) < k := by
          rw [← hroot]
          exact singleton_mem_sample_iff.mp hsplit.1
        have hchild := h (some j)
        rw [levelBox_some, ite_eq_left hj] at hchild
        exact hchild u hu hsplit.2
  · rintro ⟨hroot, hlev⟩ i
    cases i with
    | none => exact hroot
    | some j =>
        rw [levelBox_some]
        by_cases hj : (j : ℕ) < k
        · rw [ite_eq_left hj]
          intro u hu hmem
          refine hlev (j :: u) (by simp [hu]) ?_
          exact (append_mem_sample_iff c [j] u).mpr
            ⟨singleton_mem_sample_iff.mpr (hroot ▸ hj), hmem⟩
        · rw [ite_eq_right hj]
          exact Set.mem_univ _

/-- The root factor of the product: the offspring count at the root has the
offspring law. -/
lemma infinitePi_levelBox_none (θ : Offspring J) (n k : ℕ) :
    Measure.infinitePi (fun _ : Branch N none ↦ θ.law) (levelBox (N := N) n k none)
      = ENNReal.ofReal (θ k) := by
  rw [levelBox_none, show {u : Branch N none → ℕ | u rootIdx = k}
      = (fun u : Branch N none → ℕ ↦ u rootIdx) ⁻¹' {k} from rfl,
    ← Measure.map_apply (measurable_pi_apply (X := fun _ : Branch N none ↦ ℕ) rootIdx)
      (measurableSet_singleton k),
    Measure.infinitePi_map_eval (fun _ : Branch N none ↦ θ.law) rootIdx,
    Offspring.law_singleton]

/-- A child factor of the product is a copy of the field measure. -/
lemma infinitePi_branch_some (θ : Offspring J) (j : Fin N) (s : Set (Word N → ℕ)) :
    Measure.infinitePi (fun _ : Branch N (some j) ↦ θ.law) s = sampleMeasure θ s := rfl

/-- The product of the child factors: only the first `k` letters contribute. -/
lemma prod_ite_lt (x : ℝ≥0∞) {k : ℕ} (hk : k ≤ N) :
    ∏ j : Fin N, (if (j : ℕ) < k then x else 1) = x ^ k := by
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ if i < k then x else 1) N,
    ← Finset.prod_sdiff (Finset.range_subset_range.mpr hk)]
  have h1 : ∏ i ∈ Finset.range N \ Finset.range k, (if i < k then x else 1) = 1 := by
    refine Finset.prod_eq_one fun i hi ↦ ?_
    simp only [Finset.mem_sdiff, Finset.mem_range] at hi
    exact ite_eq_right hi.2
  have h2 : ∏ i ∈ Finset.range k, (if i < k then x else 1) = x ^ k := by
    rw [Finset.prod_congr rfl (fun i hi ↦ ite_eq_left (Finset.mem_range.mp hi)), Finset.prod_const,
      Finset.card_range]
  rw [h1, h2, one_mul]

/-- **The one-step measure.** The event that the root has `k` children and
generation `n+1` is empty has probability `θ_k q_n^k`. -/
theorem sampleMeasure_root_noLevel (θ : Offspring J) (n : ℕ) {k : ℕ} (hk : k ≤ N) :
    sampleMeasure (N := N) θ ({c : Word N → ℕ | c [] = k} ∩ noLevel (n + 1))
      = ENNReal.ofReal (θ k) * sampleMeasure (N := N) θ (noLevel n) ^ k := by
  rw [← split_preimage_levelBox, ← Measure.map_apply measurable_split
      (MeasurableSet.univ_pi (measurableSet_levelBox n k)), map_split, ← Finset.coe_univ,
    Measure.infinitePi_pi _ (fun i _ ↦ measurableSet_levelBox n k i), Fintype.prod_option]
  congr 1
  · exact infinitePi_levelBox_none θ n k
  · rw [← prod_ite_lt (sampleMeasure (N := N) θ (noLevel n)) hk]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [levelBox_some]
    by_cases hj : (j : ℕ) < k
    · rw [ite_eq_left hj, ite_eq_left hj]
      exact infinitePi_branch_some θ j (noLevel n)
    · rw [ite_eq_right hj, ite_eq_right hj]
      exact (infinitePi_branch_some θ j Set.univ).trans measure_univ

/-! ### The law of extinction -/

/-- **The recursion.** Splitting at the root, the probability that generation
`n+1` is empty is the generating function evaluated at the probability that
generation `n` is empty.  The bound `J ≤ N` makes the ambient alphabet wide
enough to carry the whole offspring law. -/
theorem sampleMeasure_noLevel_succ (θ : Offspring J) (hJN : J ≤ N) (n : ℕ) :
    sampleMeasure (N := N) θ (noLevel (n + 1))
      = ∑ k ∈ Finset.range (J + 1),
          ENNReal.ofReal (θ k) * sampleMeasure (N := N) θ (noLevel n) ^ k := by
  have hroot : ∀ k : ℕ, MeasurableSet {c : Word N → ℕ | c [] = k} := by
    intro k
    have h : {c : Word N → ℕ | c [] = k} = (fun c : Word N → ℕ ↦ c []) ⁻¹' {k} := rfl
    rw [h]
    exact measurable_pi_apply ([] : Word N) MeasurableSet.of_discrete
  have hmeas : ∀ k : ℕ, MeasurableSet ({c : Word N → ℕ | c [] = k} ∩ noLevel (n + 1)) :=
    fun k ↦ (hroot k).inter (measurableSet_noLevel (n + 1))
  have hdisj : Pairwise (Function.onFun Disjoint
      fun k : ℕ ↦ {c : Word N → ℕ | c [] = k} ∩ noLevel (n + 1)) := by
    intro k l hkl
    refine Set.disjoint_left.mpr fun c hc hc' ↦ ?_
    exact hkl (hc.1.symm.trans hc'.1)
  have hdecomp : noLevel (N := N) (n + 1)
      = ⋃ k : ℕ, ({c : Word N → ℕ | c [] = k} ∩ noLevel (n + 1)) := by
    ext c
    simp
  have hvanish : ∀ k ∉ Finset.range (J + 1),
      sampleMeasure (N := N) θ ({c : Word N → ℕ | c [] = k} ∩ noLevel (n + 1)) = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    refine nonpos_iff_eq_zero.mp ?_
    calc sampleMeasure (N := N) θ ({c : Word N → ℕ | c [] = k} ∩ noLevel (n + 1))
        ≤ sampleMeasure (N := N) θ {c : Word N → ℕ | c [] = k} :=
          measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal (θ k) := sampleMeasure_coord θ [] k
      _ = 0 := by rw [θ.vanishing k (by omega), ENNReal.ofReal_zero]
  rw [hdecomp, measure_iUnion hdisj hmeas, tsum_eq_sum hvanish]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  exact sampleMeasure_root_noLevel θ n
    (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hJN)

/-- **The masses of the empty-generation events are the iterates of the
generating function**: the sample dies out by generation `n` with probability
`f^n(0)`. -/
theorem sampleMeasure_noLevel (θ : Offspring J) (hJN : J ≤ N) (n : ℕ) :
    sampleMeasure (N := N) θ (noLevel n) = ENNReal.ofReal (θ.genIter n) := by
  induction n with
  | zero =>
      have h : noLevel (N := N) 0 = (∅ : Set (Word N → ℕ)) := by
        ext c
        simp only [mem_noLevel_iff, Set.mem_empty_iff_false, iff_false, Classical.not_forall]
        exact ⟨[], by simp [nil_mem_sample c]⟩
      rw [h, measure_empty, Offspring.genIter_zero, ENNReal.ofReal_zero]
  | succ n ih =>
      rw [sampleMeasure_noLevel_succ θ hJN n, ih, θ.genIter_succ]
      simp only [Offspring.gen]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun k _ ↦ mul_nonneg (θ.nonneg k) (pow_nonneg (θ.genIter_nonneg n) k))]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [ENNReal.ofReal_mul (θ.nonneg k), ENNReal.ofReal_pow (θ.genIter_nonneg n)]

/-- **The extinction probability is the probability of extinction.** The events
that a generation is empty increase to extinction, and their masses are the
iterates `f^n(0)`, which converge to the least fixed point `q` of `f`. -/
theorem sampleMeasure_not_survives (θ : Offspring J) (hJN : J ≤ N) :
    sampleMeasure (N := N) θ {c : Word N → ℕ | ¬ Survives c}
      = ENNReal.ofReal θ.extinction := by
  have h1 : Filter.Tendsto (fun n ↦ sampleMeasure (N := N) θ (noLevel n)) Filter.atTop
      (𝓝 (sampleMeasure (N := N) θ (⋃ n, noLevel (N := N) n))) :=
    tendsto_measure_iUnion_atTop noLevel_mono
  have h2 : Filter.Tendsto (fun n ↦ sampleMeasure (N := N) θ (noLevel n)) Filter.atTop
      (𝓝 (ENNReal.ofReal θ.extinction)) := by
    simp only [sampleMeasure_noLevel θ hJN]
    exact (ENNReal.continuous_ofReal.tendsto _).comp θ.tendsto_genIter
  rw [notSurvives_eq_iUnion]
  exact tendsto_nhds_unique h1 h2

/-- **The survival probability** is `1 - q`; it is positive exactly for a
supercritical law, by `extinction_lt_one_of_supercritical`. -/
theorem sampleMeasure_survives (θ : Offspring J) (hJN : J ≤ N) :
    sampleMeasure (N := N) θ {c : Word N → ℕ | Survives c}
      = ENNReal.ofReal (1 - θ.extinction) := by
  have hns : MeasurableSet {c : Word N → ℕ | ¬ Survives c} := measurableSet_survives.compl
  have h : {c : Word N → ℕ | Survives c} = {c : Word N → ℕ | ¬ Survives c}ᶜ := by
    ext c
    simp
  rw [h, prob_compl_eq_one_sub hns, sampleMeasure_not_survives θ hJN,
    ENNReal.ofReal_sub 1 θ.extinction_nonneg, ENNReal.ofReal_one]

/-- **A law with mean at most one dies out almost surely**, unless it is the deterministic
single child: the survival event is null. -/
theorem sampleMeasure_survives_eq_zero (θ : Offspring J) (hJN : J ≤ N) (h : θ.mean ≤ 1)
    (h1 : θ 1 ≠ 1) : sampleMeasure (N := N) θ {c : Word N → ℕ | Survives c} = 0 := by
  rw [sampleMeasure_survives θ hJN, θ.extinction_eq_one_of_mean_le_one h h1, sub_self,
    ENNReal.ofReal_zero]

/-- The almost-sure form: almost every sample of such a law is finite. -/
theorem ae_not_survives_of_mean_le_one (θ : Offspring J) (hJN : J ≤ N) (h : θ.mean ≤ 1)
    (h1 : θ 1 ≠ 1) : ∀ᵐ c ∂(sampleMeasure (N := N) θ), ¬ Survives c := by
  rw [MeasureTheory.ae_iff]
  simp only [not_not]
  exact sampleMeasure_survives_eq_zero θ hJN h h1

end BranchingProcess
