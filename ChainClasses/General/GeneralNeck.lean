import ChainClasses.General.GeneralShapeIID

/-! Unary-neck survival, memorylessness, and the null event of an infinite neck.
These facts concern the original reduced skeleton and do not use a presentation. -/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure bushAt)

variable {J N : ℕ}

lemma neckIter_succ_right (d : GWord N → ℕ) : ∀ n : ℕ,
    neckIter d (n + 1) = bushAt (neckIter d n) 0
  | 0 => rfl
  | n + 1 => by
      rw [neckIter_succ, neckIter_succ_right (bushAt d 0) n, neckIter_succ]

lemma survives_gSplitBush {c : GWord N → ℕ} {m : ℕ} (h : m < gArity c) :
    Survives (gSplitBush c m) :=
  BranchingProcess.survives_bushAt h

lemma survives_neckIter_of_le {d : GWord N → ℕ} (hd : Survives d) {n : ℕ}
    (h : ∀ k, k < n → skeletonDegree (neckIter d k) ≤ 1) :
    ∀ k, k ≤ n → Survives (neckIter d k) := by
  intro k
  induction k with
  | zero => exact fun _ ↦ hd
  | succ k ih =>
      intro hk
      have hks : Survives (neckIter d k) := ih (by omega)
      have h1 : skeletonDegree (neckIter d k) = 1 := by
        have hle := h k (by omega)
        have hne := BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp hks
        omega
      have hstep : neckIter d (k + 1) = bushAt (neckIter d k) 0 := by
        rw [neckIter_succ_right]
      rw [hstep]
      exact BranchingProcess.survives_bushAt (by omega)

lemma deg_eq_one_of_no_split {d : GWord N → ℕ} (hd : Survives d) {R : ℕ}
    (h : ∀ n, n < R → ¬ 2 ≤ skeletonDegree (neckIter d n)) :
    ∀ n, n < R → skeletonDegree (neckIter d n) = 1 := by
  intro n hn
  have hle : ∀ k, k < R → skeletonDegree (neckIter d k) ≤ 1 := by
    intro k hk
    have := h k hk
    omega
  have hs := survives_neckIter_of_le hd (fun k hk ↦ hle k (by omega : k < R)) n (by omega)
  have hne := BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp hs
  have := hle n hn
  omega

def missEvent (R : ℕ) (B : Set (GWord N → ℕ)) : Set (GWord N → ℕ) :=
  {d : GWord N → ℕ | ∀ n, n < R → skeletonDegree (neckIter d n) = 1}
    ∩ (fun d : GWord N → ℕ ↦ neckIter d R) ⁻¹' B

lemma measurableSet_missEvent (R : ℕ) {B : Set (GWord N → ℕ)} (hB : MeasurableSet B) :
    MeasurableSet (missEvent (N := N) R B) := by
  refine MeasurableSet.inter ?_ (measurable_neckIter R hB)
  have he : {d : GWord N → ℕ | ∀ n, n < R → skeletonDegree (neckIter d n) = 1}
      = ⋂ n ∈ Finset.range R,
          (fun d : GWord N → ℕ ↦ neckIter d n) ⁻¹'
            {e : GWord N → ℕ | skeletonDegree e = 1} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
  rw [he]
  exact MeasurableSet.biInter (Set.to_countable _) fun n _ ↦
    measurable_neckIter n (fibreMeasurableG_skeletonDegree 1)

theorem survivalMeasure_missEvent (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (R : ℕ) {B : Set (GWord N → ℕ)} (hB : MeasurableSet B) :
    survivalMeasure (N := N) θ (missEvent (N := N) R B)
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ R * survivalMeasure (N := N) θ B := by
  induction R with
  | zero =>
      have he : missEvent (N := N) 0 B = B := by
        ext d
        simp [missEvent]
      rw [he, pow_zero, one_mul]
  | succ R ih =>
      have hset : missEvent (N := N) (R + 1) B
          = {c : GWord N → ℕ | skeletonDegree c = 1}
            ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < 1 →
                bushAt c m ∈ (if m = 0 then missEvent (N := N) R B else Set.univ)} := by
        ext d
        simp only [missEvent, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
          Nat.lt_one_iff]
        constructor
        · rintro ⟨hneck, hres⟩
          have h0 : skeletonDegree d = 1 := by
            have := hneck 0 (by omega)
            rwa [neckIter_zero] at this
          refine ⟨h0, ?_⟩
          rintro m rfl
          rw [if_pos rfl]
          refine ⟨fun n hn ↦ ?_, ?_⟩
          · have := hneck (n + 1) (by omega)
            rwa [neckIter_succ] at this
          · exact hres
        · rintro ⟨h0, hrest⟩
          have hmem := hrest 0 rfl
          rw [if_pos rfl] at hmem
          obtain ⟨hneck, hres⟩ := hmem
          refine ⟨?_, ?_⟩
          · intro n hn
            cases n with
            | zero => rwa [neckIter_zero]
            | succ n =>
                rw [neckIter_succ]
                exact hneck n (by omega)
          · exact hres
      have hAmeas : ∀ m : ℕ,
          MeasurableSet (if m = 0 then missEvent (N := N) R B
            else (Set.univ : Set (GWord N → ℕ))) := by
        intro m
        split
        · exact measurableSet_missEvent R hB
        · exact MeasurableSet.univ
      rw [hset, BranchingProcess.survivalMeasure_skeletonDegree_bushes θ hJN hq 1 hAmeas,
        Finset.prod_range_one, if_pos rfl, ih, pow_succ]
      ring

lemma one_le_gArity_of_survives {c : GWord N → ℕ} (h : Survives c) : 1 ≤ gArity c := by
  by_cases hne : {n | 2 ≤ skeletonDegree (neckIter c n)}.Nonempty
  · have hmem := Nat.sInf_mem hne
    have : 2 ≤ skeletonDegree (neckIter c (gSplitDepth c)) := hmem
    have harity : 2 ≤ gArity c := this
    omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : gSplitDepth c = 0 := by rw [gSplitDepth, hne, Nat.sInf_empty]
    have harity : gArity c = skeletonDegree c := by
      rw [gArity, gSplitField_of_depth_zero h0]
    have hdeg := BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp h
    omega

theorem survivalMeasure_gArity_eq_one (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) :
    survivalMeasure (N := N) θ {c : GWord N → ℕ | gArity c = 1} = 0 := by
  have hnull := survivalMeasure_compl_survives θ hJN hq
  have hsub : ∀ n : ℕ, {c : GWord N → ℕ | gArity c = 1} ∩ {c : GWord N → ℕ | Survives c}
      ⊆ missEvent (N := N) n Set.univ := by
    intro n c hc
    obtain ⟨h1, hsurv⟩ := hc
    have hno : ∀ k, ¬ 2 ≤ skeletonDegree (neckIter c k) := by
      intro k hk
      have hne : {m | 2 ≤ skeletonDegree (neckIter c m)}.Nonempty := ⟨k, hk⟩
      have hmem := Nat.sInf_mem hne
      have harity : 2 ≤ gArity c := hmem
      rw [Set.mem_setOf_eq] at h1
      omega
    refine ⟨fun k hk ↦ ?_, Set.mem_univ _⟩
    exact deg_eq_one_of_no_split hsurv (R := n) (fun m _ ↦ hno m) k hk
  have hswle : ∀ n : ℕ, survivalMeasure (N := N) θ {c : GWord N → ℕ | gArity c = 1}
      ≤ ENNReal.ofReal (θ.skeletonWeight 1) ^ n := by
    intro n
    have hinter : survivalMeasure (N := N) θ {c : GWord N → ℕ | gArity c = 1}
        = survivalMeasure (N := N) θ
            ({c : GWord N → ℕ | gArity c = 1} ∩ {c : GWord N → ℕ | Survives c}) :=
      measure_eq_of_inter_ae hnull (by rw [Set.inter_assoc, Set.inter_self])
    rw [hinter]
    refine le_trans (measure_mono (hsub n)) ?_
    rw [survivalMeasure_missEvent θ hJN hq n MeasurableSet.univ]
    have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
    rw [measure_univ, mul_one]
  have hlt : ENNReal.ofReal (θ.skeletonWeight 1) < 1 := ENNReal.ofReal_lt_one.mpr hs1
  have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' htend hswle)

end ChainClasses
