/-
`sec:shape-harris` of `matching_classes_simple.tex`: the law of `thm:shape-iid` on the
constructed space, over the sample of `BranchingProcess`.

`ShapeDecomposition` carries the deterministic half over the hypotheses `IsHairySample`.
Two of the three are almost sure for elementary reasons; the third, that every ray of the
skeleton meets a split, is the event `Ω₀` of `thm:chains` read for the skeleton, and it is
proved here.  The argument stays in the coordinates of the sample.  The neck ray of a
vertex is the neck ray of the root of its subtree, and the field is shift invariant, so
the event that some skeleton vertex has a ray without a split is a countable union of
copies of the event at the root; at the root the branching property of the skeleton,
`survivalMeasure_skeletonDegree_bushes` at one surviving child, turns `n` steps without a
split into `θ̃₁ⁿ`, which vanishes since `θ̃₁ < 1`.  The same recursion is the neck length
of `thm:shape-iid`: the chain of the root is geometric with success probability `θ̃₂`.

The remaining clause of `thm:shape-iid`, that the shapes are i.i.d., needs the joint law
of the skeleton and its bushes.  `BranchingProcess.Skeleton` constrains the surviving
subtrees (`survivalMeasure_bushes`) and, under the dying conditioning, the dying ones
(`bushMeasure_dying`), but not both at once, which is what a decorated neck vertex asks
for.

* `sampleMeasure_map_shift`: **the field is shift invariant**, the coordinates of a
  subtree being a subfamily read along an injection.
* `neckLetter_shift`, `neckRay_shift`, `shift_neckRay`, `neckRay_succ_left`: the neck ray
  of a vertex read in its own subtree, and started one step down.
* `bushAt_zero_eq_shift`: at a neck vertex the surviving subtree of the branching property
  is the subtree along the neck letter.
* `noSplit`, `noSplit_succ`, `survivalMeasure_noSplit`: the event that the neck ray of the
  root has no split in its first `n` steps, its recursion, and its mass `θ̃₁ⁿ`.
* `skeletonWeight_two_pos` and `skeletonWeight_one_lt_one`: **the chain regime of
  `thm:harris`**, a split having positive probability as soon as the law charges two
  children.
* `survivalMeasure_iInter_noSplit`, `neverSplits`, `sampleMeasure_neverSplits` and
  `ae_splits`: **`Ω₀` for the skeleton**, almost surely every skeleton vertex has a split
  on its neck ray.
* `ae_isHairySample_of_pos` and `ae_assembly_isometric_sample`: **`thm:shape-iid`, the
  last clause, almost surely**.  Almost every sample conditioned on survival meets the
  hypotheses of `sec:shapes` and is isometric to the assembly of its own shapes.
* `splitDepth_nil_ge_iff`, `survivalMeasure_splitDepth_ge` and `survivalMeasure_neckLen`:
  **`thm:shape-iid`, the neck length**.  The chain of the root is geometric, the shape at
  the root having a neck of `k` vertices with probability `θ̃₁^{k-1}θ̃₂`.
-/
import ChainClasses.ShapeDecomposition

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (sample Survives survivors skeletonDegree Offspring sampleMeasure
  survivalMeasure bushAt)

variable {J : ℕ}

/-! ### The field seen from a vertex -/

/-- **The field is shift invariant**: the coordinates are i.i.d., and the coordinates of
the subtree at a vertex are a subfamily of them, read along an injection. -/
lemma sampleMeasure_map_shift (θ : Offspring J) (v : Amb) :
    (sampleMeasure (N := 2) θ).map (fun c ↦ shift c v) = sampleMeasure (N := 2) θ := by
  have hinj : Function.Injective (fun w : Amb ↦ v ++ w) := fun a a' h ↦ List.append_cancel_left h
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : Amb ↦ θ.law) hinj

/-- The letter continuing the neck is read in the subtree it sits in. -/
lemma neckLetter_shift (c : Amb → ℕ) (v u : Amb) :
    neckLetter (shift c v) u = neckLetter c (v ++ u) := by
  rw [neckLetter, neckLetter, shift_shift]

/-- The neck ray of a vertex is the neck ray of the root of its subtree. -/
lemma neckRay_shift (c : Amb → ℕ) (v : Amb) (k : ℕ) :
    neckRay c v k = v ++ neckRay (shift c v) [] k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [neckRay_succ, neckRay_succ, ih, neckLetter_shift, List.append_assoc]

/-- The same statement read through the shift. -/
lemma shift_neckRay (c : Amb → ℕ) (v : Amb) (k : ℕ) :
    shift c (neckRay c v k) = shift (shift c v) (neckRay (shift c v) [] k) := by
  rw [neckRay_shift, shift_shift]

/-- The neck ray started one step down. -/
lemma neckRay_succ_left (c : Amb → ℕ) (v : Amb) (k : ℕ) :
    neckRay c v (k + 1) = neckRay c (v ++ [neckLetter c v]) k := by
  induction k with
  | zero => rw [neckRay_succ, neckRay_zero, neckRay_zero]
  | succ k ih => rw [neckRay_succ, ih, neckRay_succ]

/-- At a neck vertex the surviving subtree of `survivalMeasure_bushes` is the subtree
along the neck letter. -/
lemma bushAt_zero_eq_shift {d : Amb → ℕ} (h : skeletonDegree d = 1) :
    bushAt d 0 = shift d [neckLetter d []] := by
  have hcard : (survivors d).card = 1 := by
    rw [← BranchingProcess.skeletonDegree_eq_card]; exact h
  have h0 : 0 < (survivors d).card := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hmem : (survivors d).orderEmbOfFin rfl ⟨0, h0⟩ ∈ survivors d :=
    Finset.orderEmbOfFin_mem _ _ _
  have hsurv : Survives d :=
    BranchingProcess.survives_iff_skeletonDegree_ne_zero.mpr (by omega)
  have hn : neckLetter d [] ∈ survivors d := by
    have := neckLetter_mem_survivors (c := d) (v := []) (by simpa using hsurv)
    simpa using this
  have hmem' : (survivors d).orderEmbOfFin rfl ⟨0, h0⟩ = a := by
    have hx : (survivors d).orderEmbOfFin rfl ⟨0, h0⟩ ∈ ({a} : Finset (Fin 2)) := by
      rw [← ha]; exact hmem
    simpa using hx
  have hn' : neckLetter d [] = a := by
    have hx : neckLetter d [] ∈ ({a} : Finset (Fin 2)) := by rw [← ha]; exact hn
    simpa using hx
  rw [BranchingProcess.bushAt_of_lt h0]
  funext w
  rw [shift_apply, hmem', hn']
  rfl

/-! ### The neck ray of a surviving root splits -/

/-- The event that the neck ray of the root has no split in its first `n` steps. -/
def noSplit (n : ℕ) : Set (Amb → ℕ) :=
  {d : Amb → ℕ | ∀ k < n, skeletonDegree (shift d (neckRay d [] k)) = 1}

lemma measurableSet_skeletonDegree_neckRay (k : ℕ) (s : Set ℕ) :
    MeasurableSet {d : Amb → ℕ | skeletonDegree (shift d (neckRay d [] k)) ∈ s} :=
  FibreMeasurable.preimage
    (FibreMeasurable.comp (h := fun u c ↦ skeletonDegree (shift c u))
      (fibreMeasurable_neckRay [] k) fun u ↦ fibreMeasurable_skeletonDegree u) s

lemma measurableSet_noSplit (n : ℕ) : MeasurableSet (noSplit n) := by
  have he : noSplit n
      = ⋂ k ∈ Finset.range n,
          {d : Amb → ℕ | skeletonDegree (shift d (neckRay d [] k)) ∈ ({1} : Set ℕ)} := by
    ext d
    simp only [noSplit, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
      Set.mem_singleton_iff]
  rw [he]
  exact MeasurableSet.biInter (Set.to_countable _)
    fun k _ ↦ measurableSet_skeletonDegree_neckRay k _

@[simp] lemma noSplit_zero : noSplit 0 = Set.univ := by
  ext d
  simp [noSplit]

/-- **The neck ray of the root, one step down**: past its first vertex it is the neck ray
of the root of the surviving subtree. -/
lemma shift_neckRay_succ {d : Amb → ℕ} (h : skeletonDegree d = 1) (k : ℕ) :
    shift d (neckRay d [] (k + 1))
      = shift (bushAt d 0) (neckRay (bushAt d 0) [] k) := by
  rw [neckRay_succ_left, List.nil_append, shift_neckRay, bushAt_zero_eq_shift h]

/-- The recursion of the event: no split in `n+1` steps is no split at the root together
with no split in `n` steps of its surviving subtree. -/
lemma noSplit_succ (n : ℕ) :
    noSplit (n + 1)
      = {d : Amb → ℕ | skeletonDegree d = 1} ∩ {d : Amb → ℕ | bushAt d 0 ∈ noSplit n} := by
  ext d
  simp only [noSplit, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    have h0 : skeletonDegree d = 1 := by
      have := h 0 (by omega)
      simpa using this
    refine ⟨h0, fun k hk ↦ ?_⟩
    have hk1 := h (k + 1) (by omega)
    rwa [shift_neckRay_succ h0 k] at hk1
  · rintro ⟨h0, h1⟩ k hk
    rcases k with _ | k
    · simpa using h0
    · rw [shift_neckRay_succ h0 k]
      exact h1 k (by omega)

/-- **The chain of the root is geometric**: conditioned on survival, the neck ray runs
`n` steps without splitting with probability `θ̃₁ⁿ`. -/
theorem survivalMeasure_noSplit (θ : Offspring 2) (hq : θ.extinction < 1) (n : ℕ) :
    survivalMeasure (N := 2) θ (noSplit n) = ENNReal.ofReal (θ.skeletonWeight 1) ^ n := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  induction n with
  | zero => simp
  | succ n ih =>
      have hAmeas : ∀ m : ℕ,
          MeasurableSet (if m = 0 then noSplit n else (Set.univ : Set (Amb → ℕ))) := by
        intro m
        by_cases hm : m = 0
        · rw [if_pos hm]; exact measurableSet_noSplit n
        · rw [if_neg hm]; exact MeasurableSet.univ
      have hkey := BranchingProcess.survivalMeasure_skeletonDegree_bushes θ le_rfl hq 1
        (A := fun m ↦ if m = 0 then noSplit n else Set.univ) hAmeas
      have hbox : {c : Amb → ℕ | ∀ m : ℕ, m < 1 →
            bushAt c m ∈ (if m = 0 then noSplit n else (Set.univ : Set (Amb → ℕ)))}
          = {c : Amb → ℕ | bushAt c 0 ∈ noSplit n} := by
        ext c
        simp only [Set.mem_setOf_eq, Nat.lt_one_iff]
        constructor
        · intro h
          have hc := h 0 rfl
          rwa [if_pos rfl] at hc
        · rintro h m rfl
          rwa [if_pos rfl]
      rw [hbox] at hkey
      have hprod : ∏ m ∈ Finset.range 1,
          survivalMeasure (N := 2) θ (if m = 0 then noSplit n else Set.univ)
          = survivalMeasure (N := 2) θ (noSplit n) := by simp
      rw [noSplit_succ, hkey, hprod, ih, pow_succ, mul_comm]

/-- The skeleton law is not carried by the neck alone: a split has positive probability
as soon as the offspring law charges two children. -/
lemma skeletonWeight_two_pos (θ : Offspring 2) (hq : θ.extinction < 1) (h2 : 0 < θ 2) :
    0 < θ.skeletonWeight 2 := by
  have hsurv : θ.surviveWeight 2 = θ 2 * (1 - θ.extinction) ^ 2 := by
    rw [BranchingProcess.Offspring.surviveWeight]
    simp [Finset.sum_range_succ]
  rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ (by norm_num), hsurv]
  have hpos : 0 < 1 - θ.extinction := by linarith
  positivity

/-- **The chain regime of `thm:harris`**: the skeleton law is not the point mass at one
child, so the neck ray splits with positive probability at every step. -/
lemma skeletonWeight_one_lt_one (θ : Offspring 2) (hq : θ.extinction < 1) (h2 : 0 < θ 2) :
    θ.skeletonWeight 1 < 1 := by
  have hsum := BranchingProcess.Offspring.sum_skeletonWeight θ hq
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, BranchingProcess.Offspring.skeletonWeight_zero] at hsum
  have h2' := skeletonWeight_two_pos θ hq h2
  linarith

/-- **The neck ray of a surviving root splits almost surely**: the probability of running
`n` steps without a split is `θ̃₁ⁿ`, and `θ̃₁ < 1`. -/
theorem survivalMeasure_iInter_noSplit (θ : Offspring 2) (hq : θ.extinction < 1)
    (hs : θ.skeletonWeight 1 < 1) :
    survivalMeasure (N := 2) θ (⋂ n : ℕ, noSplit n) = 0 := by
  have hle : ∀ n : ℕ, survivalMeasure (N := 2) θ (⋂ n : ℕ, noSplit n)
      ≤ ENNReal.ofReal (θ.skeletonWeight 1) ^ n := by
    intro n
    rw [← survivalMeasure_noSplit θ hq n]
    exact measure_mono (Set.iInter_subset _ n)
  have hlt : ENNReal.ofReal (θ.skeletonWeight 1) < 1 := ENNReal.ofReal_lt_one.mpr hs
  have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' htend hle)

/-! ### The splitting hypothesis under the conditioned law -/

/-- The event that a vertex is a skeleton vertex whose neck ray never splits. -/
def neverSplits (v : Amb) : Set (Amb → ℕ) :=
  {c : Amb → ℕ | Survives (shift c v) ∧ ∀ k, skeletonDegree (shift c (neckRay c v k)) ≤ 1}

lemma measurableSet_neverSplits (v : Amb) : MeasurableSet (neverSplits v) := by
  have he : neverSplits v
      = {c : Amb → ℕ | shift c v ∈ {d : Amb → ℕ | Survives d}}
        ∩ ⋂ k : ℕ, {c : Amb → ℕ | shift c v ∈
            {d : Amb → ℕ | skeletonDegree (shift d (neckRay d [] k)) ∈ {m : ℕ | m ≤ 1}}} := by
    ext c
    simp only [neverSplits, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      shift_neckRay c v]
  rw [he]
  refine MeasurableSet.inter (measurable_shiftMap v BranchingProcess.measurableSet_survives)
    (MeasurableSet.iInter fun k ↦ ?_)
  exact measurable_shiftMap v (measurableSet_skeletonDegree_neckRay k _)

/-- The event at the root is carried by the survival event, and its conditioned mass
vanishes. -/
lemma sampleMeasure_neverSplits_nil (θ : Offspring 2) (hq : θ.extinction < 1)
    (hs : θ.skeletonWeight 1 < 1) : sampleMeasure (N := 2) θ (neverSplits []) = 0 := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  have hsub : neverSplits ([] : Amb) ⊆ ⋂ n : ℕ, noSplit n := by
    rintro d ⟨hsurv, hdeg⟩
    refine Set.mem_iInter.mpr fun n ↦ fun k _ ↦ ?_
    have hpos : skeletonDegree (shift d (neckRay d [] k)) ≠ 0 :=
      BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp
        (survives_neckRay (by simpa using hsurv) k)
    have := hdeg k
    omega
  have hcond : survivalMeasure (N := 2) θ (neverSplits []) = 0 :=
    measure_mono_null hsub (survivalMeasure_iInter_noSplit θ hq hs)
  rw [BranchingProcess.survivalMeasure_apply] at hcond
  have hinter : {c : Amb → ℕ | Survives c} ∩ neverSplits ([] : Amb) = neverSplits ([] : Amb) := by
    refine Set.inter_eq_right.mpr fun c hc ↦ ?_
    simpa using hc.1
  rw [hinter] at hcond
  rcases mul_eq_zero.mp hcond with hzero | hzero
  · exact absurd (ENNReal.inv_eq_zero.mp hzero) (by
      simp [BranchingProcess.sampleMeasure_survives θ le_rfl])
  · exact hzero

/-- The same event at an arbitrary vertex: it is the event at the root, read through the
shift, which preserves the law. -/
lemma sampleMeasure_neverSplits (θ : Offspring 2) (hq : θ.extinction < 1)
    (hs : θ.skeletonWeight 1 < 1) (v : Amb) :
    sampleMeasure (N := 2) θ (neverSplits v) = 0 := by
  have he : neverSplits v = (fun c ↦ shift c v) ⁻¹' neverSplits [] := by
    ext c
    simp only [neverSplits, Set.mem_setOf_eq, Set.mem_preimage, shift_neckRay c v]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, fun k ↦ by simpa using h2 k⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, fun k ↦ by simpa using h2 k⟩
  rw [he, ← Measure.map_apply (measurable_shiftMap v) (measurableSet_neverSplits []),
    sampleMeasure_map_shift]
  exact sampleMeasure_neverSplits_nil θ hq hs

/-- **`Ω₀` for the skeleton**: conditioned on survival, almost surely every skeleton
vertex has a split on its neck ray. -/
theorem ae_splits (θ : Offspring 2) (hq : θ.extinction < 1) (hs : θ.skeletonWeight 1 < 1) :
    ∀ᵐ c ∂(survivalMeasure (N := 2) θ), ∀ v : Amb, Survives (shift c v) →
      ∃ k, 2 ≤ skeletonDegree (shift c (neckRay c v k)) := by
  rw [ae_iff]
  have he : {c : Amb → ℕ | ¬ ∀ v : Amb, Survives (shift c v) →
        ∃ k, 2 ≤ skeletonDegree (shift c (neckRay c v k))}
      = ⋃ v : Amb, neverSplits v := by
    ext c
    constructor
    · intro hc
      obtain ⟨v, hv⟩ : ∃ v : Amb, ¬ (Survives (shift c v) →
          ∃ k, 2 ≤ skeletonDegree (shift c (neckRay c v k))) := by
        by_contra hno
        exact hc fun v ↦ not_not.mp fun h ↦ hno ⟨v, h⟩
      refine Set.mem_iUnion.mpr ⟨v, ?_, fun k ↦ ?_⟩
      · by_contra hsurv
        exact hv fun h ↦ absurd h hsurv
      · by_contra hk
        exact hv fun _ ↦ ⟨k, by omega⟩
    · intro hc hall
      obtain ⟨v, hsurv, hdeg⟩ := Set.mem_iUnion.mp hc
      obtain ⟨k, hk⟩ := hall v hsurv
      have := hdeg k
      omega
  rw [he]
  refine measure_iUnion_null fun v ↦ ?_
  exact (survivalMeasure_absolutelyContinuous θ) (sampleMeasure_neverSplits θ hq hs v)

/-! ### The hypotheses of `sec:shapes` almost surely -/

/-- **`thm:shape-iid`, the standing hypotheses, almost surely**: for a supercritical
offspring law on `{0,1,2}` charging two children, almost every sample conditioned on
survival meets the hypotheses of `sec:shapes`. -/
theorem ae_isHairySample_of_pos (θ : Offspring 2) (hq : θ.extinction < 1) (h2 : 0 < θ 2) :
    ∀ᵐ c ∂(survivalMeasure (N := 2) θ), IsHairySample c :=
  ae_isHairySample θ hq (ae_splits θ hq (skeletonWeight_one_lt_one θ hq h2))

/-- **`thm:shape-iid`, the last clause, almost surely**: almost every hairy sample
conditioned on survival is isometric to the assembly of its own shapes. -/
theorem ae_assembly_isometric_sample (θ : Offspring 2) (hq : θ.extinction < 1)
    (h2 : 0 < θ 2) :
    ∀ᵐ c ∂(survivalMeasure (N := 2) θ),
      ∃ Φ : Assembly (shapeAt c) → {v : Amb // v ∈ sample c}, Function.Bijective Φ ∧
        ∀ x y : Assembly (shapeAt c),
          (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y := by
  filter_upwards [ae_isHairySample_of_pos θ hq h2] with c hc
  exact assembly_isometric_sample hc

/-! ### The neck length of the shape at the root -/

/-- The two skeleton weights sum to one: the skeleton law of an offspring law on
`{0,1,2}` is carried by one or two children. -/
lemma skeletonWeight_sum_two (θ : Offspring 2) (hq : θ.extinction < 1) :
    θ.skeletonWeight 1 + θ.skeletonWeight 2 = 1 := by
  have hsum := BranchingProcess.Offspring.sum_skeletonWeight θ hq
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, BranchingProcess.Offspring.skeletonWeight_zero] at hsum
  linarith

/-- **`thm:geometric` for the skeleton**: on the hypotheses of `sec:shapes` the chain of
the root runs at least `n` steps exactly when it has no split in its first `n`. -/
lemma splitDepth_nil_ge_iff {c : Amb → ℕ} (hc : IsHairySample c) (n : ℕ) :
    n ≤ splitDepth c [] ↔ c ∈ noSplit n := by
  have hsurv : Survives (shift c []) := by simpa using hc.survives
  constructor
  · intro h k hk
    have hnot : ¬ (2 ≤ skeletonDegree (shift c (neckRay c [] k))) := by
      intro hmem
      have hle : splitDepth c [] ≤ k :=
        Nat.sInf_le (m := k)
          (show k ∈ {k | 2 ≤ skeletonDegree (shift c (neckRay c [] k))} from hmem)
      omega
    have hpos : skeletonDegree (shift c (neckRay c [] k)) ≠ 0 :=
      BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp (survives_neckRay hsurv k)
    omega
  · intro h
    obtain ⟨k₀, hk₀⟩ := hc.splits [] hsurv
    by_contra hlt
    have hlt' : splitDepth c [] < n := by omega
    have hmem : splitDepth c [] ∈ {k | 2 ≤ skeletonDegree (shift c (neckRay c [] k))} :=
      Nat.sInf_mem ⟨k₀, hk₀⟩
    have := h (splitDepth c []) hlt'
    simp only [Set.mem_setOf_eq] at hmem
    omega

lemma measurableSet_splitDepth_ge (n : ℕ) :
    MeasurableSet {c : Amb → ℕ | n ≤ splitDepth c []} :=
  (fibreMeasurable_splitDepth []).preimage {m : ℕ | n ≤ m}

/-- **The chain of the root is geometric**: its length is at least `n` with probability
`θ̃₁ⁿ`. -/
theorem survivalMeasure_splitDepth_ge (θ : Offspring 2) (hq : θ.extinction < 1)
    (h2 : 0 < θ 2) (n : ℕ) :
    survivalMeasure (N := 2) θ {c : Amb → ℕ | n ≤ splitDepth c []}
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ n := by
  have hae : {c : Amb → ℕ | n ≤ splitDepth c []} =ᵐ[survivalMeasure (N := 2) θ] noSplit n := by
    refine Filter.eventuallyEq_set.mpr ?_
    filter_upwards [ae_isHairySample_of_pos θ hq h2] with c hc
    exact splitDepth_nil_ge_iff hc n
  rw [measure_congr hae, survivalMeasure_noSplit θ hq n]

/-- **`thm:shape-iid`, the neck length**: the shape at the root has a neck of `k`
vertices with probability `θ̃₁^{k-1}θ̃₂`. -/
theorem survivalMeasure_neckLen (θ : Offspring 2) (hq : θ.extinction < 1) (h2 : 0 < θ 2)
    (k : ℕ) (hk : 1 ≤ k) :
    survivalMeasure (N := 2) θ {c : Amb → ℕ | (shapeAt c []).neckLen = k}
      = ENNReal.ofReal (θ.skeletonWeight 1 ^ (k - 1) * θ.skeletonWeight 2) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  have hnonneg : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hshape : {c : Amb → ℕ | (shapeAt c []).neckLen = j + 1}
      = {c : Amb → ℕ | j ≤ splitDepth c []} \ {c : Amb → ℕ | j + 1 ≤ splitDepth c []} := by
    ext c
    have hne : (shapeAt c []).neckLen = splitDepth c [] + 1 := by
      rw [Shape.neckLen, shapeAt_necks, entryV_nil]
    simp only [Set.mem_setOf_eq, Set.mem_sdiff, hne]
    omega
  have hsub : {c : Amb → ℕ | j + 1 ≤ splitDepth c []}
      ⊆ {c : Amb → ℕ | j ≤ splitDepth c []} := by
    intro c hc
    simp only [Set.mem_setOf_eq] at hc ⊢
    omega
  rw [hshape, measure_sdiff hsub (measurableSet_splitDepth_ge (j + 1)).nullMeasurableSet
      (measure_ne_top _ _),
    survivalMeasure_splitDepth_ge θ hq h2, survivalMeasure_splitDepth_ge θ hq h2,
    ← ENNReal.ofReal_pow hnonneg, ← ENNReal.ofReal_pow hnonneg,
    ← ENNReal.ofReal_sub _ (pow_nonneg hnonneg (j + 1))]
  congr 1
  have hs2 : θ.skeletonWeight 2 = 1 - θ.skeletonWeight 1 := by
    have := skeletonWeight_sum_two θ hq
    linarith
  simp only [Nat.add_sub_cancel, hs2]
  ring

end ChainClasses
