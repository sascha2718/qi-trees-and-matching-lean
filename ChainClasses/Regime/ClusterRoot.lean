import ChainClasses.Regime.ClusterField

/-!
`sec:general-chain` of `matching_classes_general.tex`: the root step of
`thm:cluster-law` at a fixed coin.

At a closed coin the presented pair is the pair of `gArityDepthEvent`, and the step is
step 1's neck series.  At an open coin the event splits into the hit atoms, one per
arity of the root's split, and the miss atom: a hit absorbs the split below the first
child, whose depth runs over the revealing window and whose children take the leading
slots; a miss absorbs the first `R` neck vertices, which is the memorylessness of the
geometric law, `survivalMeasure_missEvent`.  The two junk events, extinction and a
descent that never splits, are null, the latter by the geometric decay of the neck.

* `missEvent`, `survivalMeasure_missEvent`: the first `R` steps are necks and the
  residual field is free: the weight is `θ̃₁^R`.
* `one_le_gArity_of_survives`, `survivalMeasure_gArity_eq_one`: on survival the arity
  is positive, and arity one, the descent that never splits, is null.
* `clCoinMassE`: **the presented arity mass at a fixed coin**: the split weight when
  the coin is closed; the window sum against the shifted convolution plus the missed
  split when it is open.
* `cluster_root_coin_false`, `cluster_root_coin_true`: **the root step**: the
  presented neck and arity carry their masses and the presented children are
  independent conditioned samples.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure
  bushAt)

variable {J N : ℕ}

/-! ### The neck residual -/

/-- The first `R` steps of the descent are necks, and the residual field is
constrained. -/
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

/-- **The memorylessness of the neck**: running `R` neck steps costs `θ̃₁^R` and hands
on an independent conditioned sample. -/
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

/-! ### The two junk events are null -/

/-- On survival the arity of the terminating split is positive. -/
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

/-- **The descent that never splits is null**: arity one survives only on the event
that every step is a neck, whose mass `θ̃₁^n` vanishes. -/
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

/-! ### The presented arity mass at a fixed coin -/

/-- **The presented arity mass at a fixed coin**: the split weight when the coin is
closed; when it is open, the window sum against the merged pairs plus the missed
split. -/
noncomputable def clCoinMassE (θ : Offspring J) (R : ℕ) (b0 : Bool) (j : ℕ) : ℝ≥0∞ :=
  if b0 then
    (∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d)
        * ∑ p ∈ Finset.Icc 2 (j - 1),
            ENNReal.ofReal (θ.skeletonWeight p)
              * ENNReal.ofReal (θ.skeletonWeight (j + 1 - p))
      + ENNReal.ofReal (θ.skeletonWeight 1) ^ R * ENNReal.ofReal (θ.skeletonWeight j)
  else ENNReal.ofReal (θ.skeletonWeight j)

/-! ### The root step at a closed coin -/

/-- **The root step at a closed coin**: nothing is absorbed, so the presented pair is
the pair of the split and the presented children are its subtrees. -/
theorem cluster_root_coin_false (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    {R : ℕ} {b : List ℕ → Bool} (hb : b [] = false) {r j : ℕ} (hj : 2 ≤ j)
    {E : ℕ → Set (GWord N → ℕ)} (hE : ∀ m, MeasurableSet (E m)) :
    survivalMeasure (N := N) θ
        (({c : GWord N → ℕ | gSplitDepth c = r}
            ∩ {c : GWord N → ℕ | clArityC R (c, b) = j})
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j → (clSubC R (c, b) m).1 ∈ E m})
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ r
          * (clCoinMassE θ R (b []) j
            * ∏ m ∈ Finset.range j, survivalMeasure (N := N) θ (E m)) := by
  have hset : (({c : GWord N → ℕ | gSplitDepth c = r}
        ∩ {c : GWord N → ℕ | clArityC R (c, b) = j})
      ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j → (clSubC R (c, b) m).1 ∈ E m})
      = gArityDepthEvent (N := N) j r E := by
    ext c
    simp only [gArityDepthEvent, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hd, ha⟩, hbox⟩
      rw [clArityC_coin_false hb] at ha
      refine ⟨⟨hd, ha⟩, fun m hm ↦ ?_⟩
      have := hbox m hm
      rwa [clSubC_fst_coin_false hb m] at this
    · rintro ⟨⟨hd, ha⟩, hbox⟩
      refine ⟨⟨hd, ?_⟩, fun m hm ↦ ?_⟩
      · rw [clArityC_coin_false hb]
        exact ha
      · rw [clSubC_fst_coin_false hb m]
        exact hbox m hm
  rw [hset, survivalMeasure_gArityDepthEvent θ hJN hq hj hE r, hb]
  rfl


/-! ### The root step at an open coin -/

/-- The hit window: the split below the first child sits at some depth inside the
revealing window, with the prescribed slots below it. -/
def hitInner (R k₁ : ℕ) (E : ℕ → Set (GWord N → ℕ)) : Set (GWord N → ℕ) :=
  ⋃ d₁ ∈ Finset.range R, gArityDepthEvent (N := N) k₁ d₁ E

/-- The slot sets of a hit atom: the absorbed split's children lead, the remaining
children of the root's split follow. -/
def hitSlots (R j k₀ : ℕ) (E : ℕ → Set (GWord N → ℕ)) : ℕ → Set (GWord N → ℕ) :=
  fun m ↦ if m = 0 then hitInner (N := N) R (j + 1 - k₀) E else E (j - k₀ + m)

/-- The slot sets of the miss atom: the first slot passes through the revealing
window. -/
def missSlots (R : ℕ) (E : ℕ → Set (GWord N → ℕ)) : ℕ → Set (GWord N → ℕ) :=
  fun m ↦ if m = 0 then missEvent (N := N) R (E 0) else E m

lemma measurableSet_gArityDepthEvent {κ n : ℕ} {A : ℕ → Set (GWord N → ℕ)}
    (hA : ∀ m, MeasurableSet (A m)) :
    MeasurableSet (gArityDepthEvent (N := N) κ n A) :=
  ((fibreMeasurableG_gSplitDepth n).inter (fibreMeasurableG_gArity κ)).inter
    (measurableSet_gSplitBush_box hA)

lemma measurableSet_hitSlots {R j k₀ : ℕ} {E : ℕ → Set (GWord N → ℕ)}
    (hE : ∀ m, MeasurableSet (E m)) (m : ℕ) :
    MeasurableSet (hitSlots (N := N) R j k₀ E m) := by
  rw [hitSlots]
  split
  · exact MeasurableSet.biUnion (Set.to_countable _) fun d₁ _ ↦
      measurableSet_gArityDepthEvent hE
  · exact hE _

lemma measurableSet_missSlots {R : ℕ} {E : ℕ → Set (GWord N → ℕ)}
    (hE : ∀ m, MeasurableSet (E m)) (m : ℕ) :
    MeasurableSet (missSlots (N := N) R E m) := by
  rw [missSlots]
  split
  · exact measurableSet_missEvent R (hE 0)
  · exact hE _

/-- **The root event at an open coin, atomised**: modulo survival and the null descent
that never splits, the event splits into one hit atom per arity of the root's split and
the miss atom. -/
lemma cluster_root_coin_true_atoms (R : ℕ) {b : List ℕ → Bool} (hb : b [] = true)
    {r j : ℕ} (hj : 2 ≤ j) (E : ℕ → Set (GWord N → ℕ)) :
    ((({c : GWord N → ℕ | gSplitDepth c = r}
          ∩ {c : GWord N → ℕ | clArityC R (c, b) = j})
        ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j → (clSubC R (c, b) m).1 ∈ E m})
      ∩ ({c : GWord N → ℕ | Survives c} ∩ {c : GWord N → ℕ | gArity c = 1}ᶜ))
      = (((⋃ k₀ ∈ Finset.Icc 2 (j - 1), gArityDepthEvent (N := N) k₀ r
              (hitSlots (N := N) R j k₀ E))
          ∪ gArityDepthEvent (N := N) j r (missSlots (N := N) R E))
        ∩ ({c : GWord N → ℕ | Survives c} ∩ {c : GWord N → ℕ | gArity c = 1}ᶜ)) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion,
    Set.mem_compl_iff, gArityDepthEvent, exists_prop]
  constructor
  · rintro ⟨⟨⟨hd, ha⟩, hbox⟩, hsurv, hne1⟩
    refine ⟨?_, hsurv, hne1⟩
    by_cases hh : clHitCond R c
    · left
      rw [clArityC_hit hb hh] at ha
      have hk₁2 : 2 ≤ gArity (gSplitBush c 0) := two_le_gArity_of_clHitCond hh
      have hk₀1 : 1 ≤ gArity c := one_le_gArity_of_survives hsurv
      have hk₀2 : 2 ≤ gArity c := by omega
      refine ⟨gArity c, by rw [Finset.mem_Icc]; omega, ⟨⟨hd, rfl⟩, ?_⟩⟩
      intro m hm
      rw [hitSlots]
      by_cases hm0 : m = 0
      · subst hm0
        rw [if_pos rfl, hitInner]
        simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, gArityDepthEvent,
          Set.mem_inter_iff, Set.mem_setOf_eq]
        refine ⟨gSplitDepth (gSplitBush c 0), gSplitDepth_lt_of_clHitCond hh,
          ⟨rfl, by omega⟩, ?_⟩
        intro l hl
        have hlj : l < j := by omega
        have hval := hbox l hlj
        rwa [clSubC_fst_hit hb hh l, if_pos (by omega)] at hval
      · rw [if_neg hm0]
        have hij : gArity (gSplitBush c 0) + m - 1 < j := by omega
        have hval := hbox (gArity (gSplitBush c 0) + m - 1) hij
        rw [clSubC_fst_hit hb hh _, if_neg (by omega)] at hval
        have hidx1 : gArity (gSplitBush c 0) + m - 1 - gArity (gSplitBush c 0) + 1 = m := by
          omega
        have hidx2 : gArity (gSplitBush c 0) + m - 1 = j - gArity c + m := by omega
        rw [hidx1, hidx2] at hval
        exact hval
    · right
      rw [clArityC_miss hb hh] at ha
      refine ⟨⟨hd, ha⟩, ?_⟩
      intro m hm
      rw [missSlots]
      by_cases hm0 : m = 0
      · subst hm0
        rw [if_pos rfl, missEvent]
        have hsurv0 : Survives (gSplitBush c 0) := survives_gSplitBush (by omega)
        have hno : ∀ n, n < R → ¬ 2 ≤ skeletonDegree (neckIter (gSplitBush c 0) n) := by
          intro n hn h2
          exact hh ⟨n, hn, h2⟩
        refine ⟨deg_eq_one_of_no_split hsurv0 hno, ?_⟩
        have hval := hbox 0 (by omega)
        rwa [clSubC_fst_miss hb hh 0, if_pos rfl] at hval
      · rw [if_neg hm0]
        have hval := hbox m hm
        rwa [clSubC_fst_miss hb hh m, if_neg hm0] at hval
  · rintro ⟨hmem, hsurv, hne1⟩
    refine ⟨?_, hsurv, hne1⟩
    rcases hmem with ⟨k₀, hk₀mem, ⟨⟨hd, hk₀⟩, hbox⟩⟩ | ⟨⟨hd, hja⟩, hbox⟩
    · rw [Finset.mem_Icc] at hk₀mem
      have hbush0 := hbox 0 (by omega)
      rw [hitSlots, if_pos rfl, hitInner] at hbush0
      simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, gArityDepthEvent,
        Set.mem_inter_iff, Set.mem_setOf_eq] at hbush0
      obtain ⟨d₁, hd₁R, ⟨⟨hdep, har⟩, ibox⟩⟩ := hbush0
      have hh : clHitCond R c :=
        clHitCond_of_depth_lt (by omega) (by omega)
      refine ⟨⟨hd, ?_⟩, ?_⟩
      · rw [clArityC_hit hb hh, hk₀, har]
        omega
      · intro i hi
        rw [clSubC_fst_hit hb hh i]
        by_cases hik : i < gArity (gSplitBush c 0)
        · rw [if_pos hik]
          exact ibox i (by omega)
        · rw [if_neg hik]
          have hval := hbox (i - gArity (gSplitBush c 0) + 1) (by omega)
          rw [hitSlots, if_neg (by omega)] at hval
          have hidx : j - k₀ + (i - gArity (gSplitBush c 0) + 1) = i := by omega
          rw [hidx] at hval
          exact hval
    · have hbush0 := hbox 0 (by omega)
      rw [missSlots, if_pos rfl, missEvent] at hbush0
      obtain ⟨hneck, hres⟩ := hbush0
      have hh : ¬ clHitCond R c := by
        rintro ⟨n, hnR, h2⟩
        have := hneck n hnR
        omega
      refine ⟨⟨hd, ?_⟩, ?_⟩
      · rw [clArityC_miss hb hh]
        exact hja
      · intro i hi
        rw [clSubC_fst_miss hb hh i]
        by_cases hi0 : i = 0
        · subst hi0
          rw [if_pos rfl]
          exact hres
        · rw [if_neg hi0]
          have hval := hbox i hi
          rwa [missSlots, if_neg hi0] at hval


lemma clCoinMassE_true (θ : Offspring J) (R j : ℕ) :
    clCoinMassE (θ := θ) R true j
      = (∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d)
          * ∑ p ∈ Finset.Icc 2 (j - 1),
              ENNReal.ofReal (θ.skeletonWeight p)
                * ENNReal.ofReal (θ.skeletonWeight (j + 1 - p))
        + ENNReal.ofReal (θ.skeletonWeight 1) ^ R
            * ENNReal.ofReal (θ.skeletonWeight j) := by
  simp [clCoinMassE]

lemma clCoinMassE_false (θ : Offspring J) (R j : ℕ) :
    clCoinMassE (θ := θ) R false j = ENNReal.ofReal (θ.skeletonWeight j) := by
  simp [clCoinMassE]

/-- The mass of the hit window: the split below the first child sweeps the revealing
window, and its children are independent conditioned samples. -/
lemma survivalMeasure_hitInner (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    {R k₁ : ℕ} (hk₁ : 2 ≤ k₁) {E : ℕ → Set (GWord N → ℕ)}
    (hE : ∀ m, MeasurableSet (E m)) :
    survivalMeasure (N := N) θ (hitInner (N := N) R k₁ E)
      = (∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d)
          * (ENNReal.ofReal (θ.skeletonWeight k₁)
            * ∏ m ∈ Finset.range k₁, survivalMeasure (N := N) θ (E m)) := by
  have hdisj : (↑(Finset.range R) : Set ℕ).PairwiseDisjoint
      (fun d₁ ↦ gArityDepthEvent (N := N) k₁ d₁ E) := by
    intro a _ a' _ haa
    refine Set.disjoint_left.mpr fun c hc hc' ↦ haa ?_
    rw [← hc.1.1, ← hc'.1.1]
  rw [hitInner, measure_biUnion_finset hdisj
      fun d₁ _ ↦ measurableSet_gArityDepthEvent hE,
    Finset.sum_congr rfl fun d₁ _ ↦ survivalMeasure_gArityDepthEvent θ hJN hq hk₁ hE d₁,
    ← Finset.sum_mul]

/-- The mass of a hit atom. -/
lemma survivalMeasure_hitAtom (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    {R r j : ℕ} {k₀ : ℕ} (hk₀ : k₀ ∈ Finset.Icc 2 (j - 1)) (hj : 2 ≤ j)
    {E : ℕ → Set (GWord N → ℕ)} (hE : ∀ m, MeasurableSet (E m)) :
    survivalMeasure (N := N) θ
        (gArityDepthEvent (N := N) k₀ r (hitSlots (N := N) R j k₀ E))
      = (∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d)
          * (ENNReal.ofReal (θ.skeletonWeight k₀)
            * ENNReal.ofReal (θ.skeletonWeight (j + 1 - k₀)))
          * (ENNReal.ofReal (θ.skeletonWeight 1) ^ r
            * ∏ i ∈ Finset.range j, survivalMeasure (N := N) θ (E i)) := by
  rw [Finset.mem_Icc] at hk₀
  obtain ⟨k₀', rfl⟩ : ∃ k₀', k₀ = k₀' + 1 := ⟨k₀ - 1, by omega⟩
  rw [survivalMeasure_gArityDepthEvent θ hJN hq (by omega)
      (measurableSet_hitSlots hE) r, Finset.prod_range_succ']
  have hf0 : hitSlots (N := N) R j (k₀' + 1) E 0
      = hitInner (N := N) R (j + 1 - (k₀' + 1)) E := by
    rw [hitSlots, if_pos rfl]
  have hfm : ∀ m ∈ Finset.range k₀',
      survivalMeasure (N := N) θ (hitSlots (N := N) R j (k₀' + 1) E (m + 1))
        = survivalMeasure (N := N) θ (E (j + 1 - (k₀' + 1) + m)) := by
    intro m _
    rw [hitSlots, if_neg (by omega)]
    have hidx : j - (k₀' + 1) + (m + 1) = j + 1 - (k₀' + 1) + m := by omega
    rw [hidx]
  rw [hf0, survivalMeasure_hitInner θ hJN hq (by omega) hE, Finset.prod_congr rfl hfm]
  have hprod : (∏ m ∈ Finset.range k₀',
        survivalMeasure (N := N) θ (E (j + 1 - (k₀' + 1) + m)))
      * ∏ l ∈ Finset.range (j + 1 - (k₀' + 1)), survivalMeasure (N := N) θ (E l)
      = ∏ i ∈ Finset.range j, survivalMeasure (N := N) θ (E i) := by
    rw [mul_comm, ← Finset.prod_range_add]
    have hidx : j + 1 - (k₀' + 1) + k₀' = j := by omega
    rw [hidx]
  rw [← hprod]
  ring

/-- The mass of the miss atom. -/
lemma survivalMeasure_missAtom (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    {R r j : ℕ} (hj : 2 ≤ j) {E : ℕ → Set (GWord N → ℕ)}
    (hE : ∀ m, MeasurableSet (E m)) :
    survivalMeasure (N := N) θ
        (gArityDepthEvent (N := N) j r (missSlots (N := N) R E))
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ R * ENNReal.ofReal (θ.skeletonWeight j)
          * (ENNReal.ofReal (θ.skeletonWeight 1) ^ r
            * ∏ i ∈ Finset.range j, survivalMeasure (N := N) θ (E i)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [survivalMeasure_gArityDepthEvent θ hJN hq hj (measurableSet_missSlots hE) r,
    Finset.prod_range_succ']
  have hf0 : missSlots (N := N) R E 0 = missEvent (N := N) R (E 0) := by
    rw [missSlots, if_pos rfl]
  have hfm : ∀ m ∈ Finset.range j',
      survivalMeasure (N := N) θ (missSlots (N := N) R E (m + 1))
        = survivalMeasure (N := N) θ (E (m + 1)) := by
    intro m _
    rw [missSlots, if_neg (by omega)]
  rw [hf0, survivalMeasure_missEvent θ hJN hq R (hE 0), Finset.prod_congr rfl hfm]
  have hprod : (∏ m ∈ Finset.range j', survivalMeasure (N := N) θ (E (m + 1)))
      * survivalMeasure (N := N) θ (E 0)
      = ∏ i ∈ Finset.range (j' + 1), survivalMeasure (N := N) θ (E i) :=
    (Finset.prod_range_succ' (fun i ↦ survivalMeasure (N := N) θ (E i)) j').symm
  rw [← hprod]
  ring

/-- **The root step at an open coin**: the presented neck and arity carry the window
mass, and the presented children are independent conditioned samples. -/
theorem cluster_root_coin_true (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) {R : ℕ} {b : List ℕ → Bool} (hb : b [] = true)
    {r j : ℕ} (hj : 2 ≤ j) {E : ℕ → Set (GWord N → ℕ)}
    (hE : ∀ m, MeasurableSet (E m)) :
    survivalMeasure (N := N) θ
        (({c : GWord N → ℕ | gSplitDepth c = r}
            ∩ {c : GWord N → ℕ | clArityC R (c, b) = j})
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j → (clSubC R (c, b) m).1 ∈ E m})
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ r
          * (clCoinMassE (θ := θ) R (b []) j
            * ∏ m ∈ Finset.range j, survivalMeasure (N := N) θ (E m)) := by
  have hnull : survivalMeasure (N := N) θ
      ({c : GWord N → ℕ | Survives c} ∩ {c : GWord N → ℕ | gArity c = 1}ᶜ)ᶜ = 0 := by
    rw [Set.compl_inter, compl_compl]
    exact measure_union_null (survivalMeasure_compl_survives θ hJN hq)
      (survivalMeasure_gArity_eq_one θ hJN hq hs1)
  rw [measure_eq_of_inter_ae hnull (cluster_root_coin_true_atoms R hb hj E)]
  have hdisjU : Disjoint
      (⋃ k₀ ∈ Finset.Icc 2 (j - 1),
        gArityDepthEvent (N := N) k₀ r (hitSlots (N := N) R j k₀ E))
      (gArityDepthEvent (N := N) j r (missSlots (N := N) R E)) := by
    refine Set.disjoint_left.mpr fun c hc hc' ↦ ?_
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨k₀, hk₀mem, hcmem⟩ := hc
    rw [Finset.mem_Icc] at hk₀mem
    have h1 : gArity c = k₀ := hcmem.1.2
    have h2 : gArity c = j := hc'.1.2
    omega
  have hmeasU : MeasurableSet (⋃ k₀ ∈ Finset.Icc 2 (j - 1),
      gArityDepthEvent (N := N) k₀ r (hitSlots (N := N) R j k₀ E)) :=
    MeasurableSet.biUnion (Set.to_countable _)
      fun k₀ _ ↦ measurableSet_gArityDepthEvent (measurableSet_hitSlots hE)
  have hdisj : (↑(Finset.Icc 2 (j - 1)) : Set ℕ).PairwiseDisjoint
      (fun k₀ ↦ gArityDepthEvent (N := N) k₀ r (hitSlots (N := N) R j k₀ E)) := by
    intro a _ a' _ haa
    refine Set.disjoint_left.mpr fun c hc hc' ↦ haa ?_
    rw [← hc.1.2, ← hc'.1.2]
  rw [Set.union_comm, measure_union hdisjU.symm hmeasU,
    measure_biUnion_finset hdisj
      fun k₀ _ ↦ measurableSet_gArityDepthEvent (measurableSet_hitSlots hE),
    Finset.sum_congr rfl fun k₀ hk₀ ↦ survivalMeasure_hitAtom θ hJN hq hk₀ hj hE,
    survivalMeasure_missAtom θ hJN hq hj hE, ← Finset.sum_mul, ← Finset.mul_sum, hb,
    clCoinMassE_true]
  ring

end ChainClasses
