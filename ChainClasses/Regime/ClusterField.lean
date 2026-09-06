import ChainClasses.General.GeneralShapeIID

/-!
`sec:general-chain` of `matching_classes_general.tex`: the deterministic layer of the
cluster presentation of `def:cluster`, read off the skeleton recursion of
`GeneralDecomposition`.

The rule of `def:cluster` inspects one uniform variable per cluster root, and only
through the event `U(w) < β`, so the randomisation is carried as a Boolean coin field
indexed by the addresses of the presented skeleton: a state is a pair of an offspring
field and a coin field, a letter passes to a presented child and shifts the coins, and
the coin consumed at a presented address is the coin at that address.  Presented
addresses are words over `ℕ`, since a presented arity may exceed the ambient alphabet.

The absorption test is the genuine-split condition `clHitCond`: the first child of the
terminating split has a split within the revealing depth.  This is `m(w₁) ≤ R` read
with `m(w₁) = ∞` when the descent below `w₁` never splits, so no splitting hypothesis
enters the definitions, and on the never-splitting junk the rule falls into the miss
case.

* `clHitCond` with the two readings
  `gSplitDepth_lt_of_clHitCond`, `two_le_gArity_of_clHitCond`,
  `clHitCond_of_depth_lt`: the absorption test.
* `clArityC`, `clSubC`, `clAtC`, `clNeckAtC`, `clArityAtC`: **`def:cluster`**, the
  presented arity, the presented children with their shifted coins, and the presented
  fields along an address.
* the coin unfoldings `clArityC_coin_false`, `clArityC_hit`, `clArityC_miss`,
  `clSubC_fst_coin_false`, `clSubC_fst_hit`, `clSubC_fst_miss`, and `clAtC_snd`: the
  rule read case by case, and the coins along an address.
* `survives_gSplitBush`, `survives_neckIter_of_le`, `deg_eq_one_of_no_split`: the
  surviving descent, which resolves the miss case to a neck of ones.
* `clNeckAtC_congr`, `clArityAtC_congr`: **the rule reads only the coins at the
  prefixes of the address**, which is what decomposes a probe over coin patterns.
* `measurableSet_clHitCond`, `measurable_clAtC_fst`, `measurableSet_clNeckAtC_eq`,
  `measurableSet_clArityAtC_eq`: at a fixed coin field the presented fields are
  measurable in the sample.
-/

namespace ChainClasses

open MeasureTheory
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure
  bushAt)

variable {N : ℕ}

/-- The descent, one step at a time from the right. -/
lemma neckIter_succ_right (d : GWord N → ℕ) : ∀ n : ℕ,
    neckIter d (n + 1) = bushAt (neckIter d n) 0
  | 0 => rfl
  | n + 1 => by
      rw [neckIter_succ, neckIter_succ_right (bushAt d 0) n, neckIter_succ]

/-! ### The absorption test -/

/-- **The absorption test of `def:cluster`**: the first child of the terminating split
has a split within the revealing depth.  This is `m(w₁) ≤ R`, reading `m(w₁) = ∞` when
the descent below `w₁` never splits. -/
def clHitCond (R : ℕ) (c : GWord N → ℕ) : Prop :=
  ∃ n, n < R ∧ 2 ≤ skeletonDegree (neckIter (gSplitBush c 0) n)

/-- A hit certifies that the split below the first child is genuine and within the
revealing depth. -/
lemma gSplitDepth_lt_of_clHitCond {R : ℕ} {c : GWord N → ℕ} (h : clHitCond R c) :
    gSplitDepth (gSplitBush c 0) < R := by
  obtain ⟨n, hnR, hn⟩ := h
  exact lt_of_le_of_lt (Nat.sInf_le hn) hnR

lemma two_le_gArity_of_clHitCond {R : ℕ} {c : GWord N → ℕ} (h : clHitCond R c) :
    2 ≤ gArity (gSplitBush c 0) := by
  obtain ⟨n, hnR, hn⟩ := h
  have hne : {m | 2 ≤ skeletonDegree (neckIter (gSplitBush c 0) m)}.Nonempty := ⟨n, hn⟩
  exact Nat.sInf_mem hne

/-- A genuine split within the revealing depth is a hit. -/
lemma clHitCond_of_depth_lt {R : ℕ} {c : GWord N → ℕ}
    (hd : gSplitDepth (gSplitBush c 0) < R) (ha : 2 ≤ gArity (gSplitBush c 0)) :
    clHitCond R c := by
  have hne := splitSet_nonempty_of_arity ha
  exact ⟨gSplitDepth (gSplitBush c 0), hd, Nat.sInf_mem hne⟩

noncomputable instance (R : ℕ) (c : GWord N → ℕ) : Decidable (clHitCond R c) :=
  decidable_of_iff
    (∃ n ∈ Finset.range R, 2 ≤ skeletonDegree (neckIter (gSplitBush c 0) n)) (by
      simp [clHitCond])

/-! ### The presented arity and the presented children -/

/-- **`def:cluster`, the presented arity**: on a hit the arities of the two merged
splits combine to `k(w) + k(w₁) - 1`; otherwise the arity of the root's split. -/
noncomputable def clArityC (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) : ℕ :=
  if ω.2 [] = true ∧ clHitCond R ω.1
  then gArity ω.1 + gArity (gSplitBush ω.1 0) - 1
  else gArity ω.1

/-- **`def:cluster`, the presented children**: on a hit the children of the absorbed
split come first and the remaining children of the root's split follow; on a miss the
first child is replaced by the vertex at the revealing depth on its branch; with the
coin closed nothing moves.  In every case the coins shift by the letter. -/
noncomputable def clSubC (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) (i : ℕ) :
    (GWord N → ℕ) × (List ℕ → Bool) :=
  (if ω.2 [] = true then
      if clHitCond R ω.1 then
        if i < gArity (gSplitBush ω.1 0) then gSplitBush (gSplitBush ω.1 0) i
        else gSplitBush ω.1 (i - gArity (gSplitBush ω.1 0) + 1)
      else
        if i = 0 then neckIter (gSplitBush ω.1 0) R else gSplitBush ω.1 i
    else gSplitBush ω.1 i,
   fun w ↦ ω.2 (i :: w))

/-- The presented field at a presented address: each letter passes to a presented
child. -/
noncomputable def clAtC (R : ℕ) :
    (GWord N → ℕ) × (List ℕ → Bool) → List ℕ → (GWord N → ℕ) × (List ℕ → Bool)
  | ω, [] => ω
  | ω, (i :: u) => clAtC R (clSubC R ω i) u

@[simp] lemma clAtC_nil (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) :
    clAtC R ω [] = ω := rfl

lemma clAtC_cons (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) (i : ℕ) (u : List ℕ) :
    clAtC R ω (i :: u) = clAtC R (clSubC R ω i) u := rfl

/-- **The presented neck at an address**: the depth of the split terminating the neck
of the cluster root, the paper's `m(w) - 1`. -/
noncomputable def clNeckAtC (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool))
    (u : List ℕ) : ℕ :=
  gSplitDepth (clAtC R ω u).1

/-- **The presented arity at an address.** -/
noncomputable def clArityAtC (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool))
    (u : List ℕ) : ℕ :=
  clArityC R (clAtC R ω u)

@[simp] lemma clNeckAtC_nil (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) :
    clNeckAtC R ω [] = gSplitDepth ω.1 := rfl

@[simp] lemma clArityAtC_nil (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) :
    clArityAtC R ω [] = clArityC R ω := rfl

lemma clNeckAtC_cons (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) (i : ℕ)
    (u : List ℕ) : clNeckAtC R ω (i :: u) = clNeckAtC R (clSubC R ω i) u := rfl

lemma clArityAtC_cons (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) (i : ℕ)
    (u : List ℕ) : clArityAtC R ω (i :: u) = clArityAtC R (clSubC R ω i) u := rfl

/-- The coins along a presented address: the second component of the presented field is
the coin field shifted by the address. -/
lemma clAtC_snd (R : ℕ) :
    ∀ (u : List ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)),
      (clAtC R ω u).2 = fun w ↦ ω.2 (u ++ w)
  | [], ω => by simp
  | i :: u, ω => by
      rw [clAtC_cons, clAtC_snd R u]
      rfl

/-! ### The rule, case by case -/

lemma clArityC_coin_false {R : ℕ} {c : GWord N → ℕ} {b : List ℕ → Bool}
    (h : b [] = false) : clArityC R (c, b) = gArity c := by
  simp [clArityC, h]

lemma clArityC_hit {R : ℕ} {c : GWord N → ℕ} {b : List ℕ → Bool} (h : b [] = true)
    (hh : clHitCond R c) :
    clArityC R (c, b) = gArity c + gArity (gSplitBush c 0) - 1 := by
  simp [clArityC, h, hh]

lemma clArityC_miss {R : ℕ} {c : GWord N → ℕ} {b : List ℕ → Bool} (h : b [] = true)
    (hh : ¬ clHitCond R c) : clArityC R (c, b) = gArity c := by
  simp [clArityC, h, hh]

lemma clSubC_fst_coin_false {R : ℕ} {c : GWord N → ℕ} {b : List ℕ → Bool}
    (h : b [] = false) (i : ℕ) : (clSubC R (c, b) i).1 = gSplitBush c i := by
  simp [clSubC, h]

lemma clSubC_fst_hit {R : ℕ} {c : GWord N → ℕ} {b : List ℕ → Bool} (h : b [] = true)
    (hh : clHitCond R c) (i : ℕ) :
    (clSubC R (c, b) i).1
      = if i < gArity (gSplitBush c 0) then gSplitBush (gSplitBush c 0) i
        else gSplitBush c (i - gArity (gSplitBush c 0) + 1) := by
  simp [clSubC, h, hh]

lemma clSubC_fst_miss {R : ℕ} {c : GWord N → ℕ} {b : List ℕ → Bool} (h : b [] = true)
    (hh : ¬ clHitCond R c) (i : ℕ) :
    (clSubC R (c, b) i).1
      = if i = 0 then neckIter (gSplitBush c 0) R else gSplitBush c i := by
  simp [clSubC, h, hh]

lemma clSubC_snd (R : ℕ) (ω : (GWord N → ℕ) × (List ℕ → Bool)) (i : ℕ) :
    (clSubC R ω i).2 = fun w ↦ ω.2 (i :: w) := rfl

/-- The presented arity reads only the coin at the root. -/
lemma clArityC_congr_coin {R : ℕ} {c : GWord N → ℕ} {b b' : List ℕ → Bool}
    (h : b [] = b' []) : clArityC R (c, b) = clArityC R (c, b') := by
  cases hb : b' [] with
  | false =>
      rw [clArityC_coin_false hb, clArityC_coin_false (h.trans hb)]
  | true =>
      by_cases hh : clHitCond R c
      · rw [clArityC_hit (h.trans hb) hh, clArityC_hit hb hh]
      · rw [clArityC_miss (h.trans hb) hh, clArityC_miss hb hh]

/-! ### The surviving descent -/

/-- A presented child of a genuine split survives. -/
lemma survives_gSplitBush {c : GWord N → ℕ} {m : ℕ} (h : m < gArity c) :
    Survives (gSplitBush c m) :=
  BranchingProcess.survives_bushAt h

/-- Along a descent with at most one surviving child per step, survival propagates. -/
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

/-- On a surviving descent, no split within the window resolves to a neck of ones. -/
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

/-! ### The rule reads only the coins at the prefixes -/

lemma clSubC_fst_congr {R : ℕ} {c : GWord N → ℕ} {b b' : List ℕ → Bool}
    (h : b [] = b' []) (i : ℕ) : (clSubC R (c, b) i).1 = (clSubC R (c, b') i).1 := by
  simp only [clSubC, h]

/-- The presented neck at an address reads only the coins at its proper prefixes. -/
lemma clNeckAtC_congr (R : ℕ) :
    ∀ (u : List ℕ) (c : GWord N → ℕ) (b b' : List ℕ → Bool),
      (∀ p : List ℕ, p <+: u → b p = b' p) →
      clNeckAtC R (c, b) u = clNeckAtC R (c, b') u
  | [], c, b, b', _ => rfl
  | i :: u, c, b, b', h => by
      rw [clNeckAtC_cons, clNeckAtC_cons]
      have hnil : b [] = b' [] := h [] List.nil_prefix
      have hfst : (clSubC R (c, b) i).1 = (clSubC R (c, b') i).1 := clSubC_fst_congr hnil i
      have hb : ∀ p : List ℕ, p <+: u → b (i :: p) = b' (i :: p) := fun p hp ↦
        h (i :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
      calc clNeckAtC R (clSubC R (c, b) i) u
          = clNeckAtC R ((clSubC R (c, b) i).1, fun w ↦ b (i :: w)) u := rfl
        _ = clNeckAtC R ((clSubC R (c, b') i).1, fun w ↦ b' (i :: w)) u := by
            rw [hfst]
            exact clNeckAtC_congr R u _ _ _ hb
        _ = clNeckAtC R (clSubC R (c, b') i) u := rfl

/-- The presented arity at an address reads only the coins at its prefixes. -/
lemma clArityAtC_congr (R : ℕ) :
    ∀ (u : List ℕ) (c : GWord N → ℕ) (b b' : List ℕ → Bool),
      (∀ p : List ℕ, p <+: u → b p = b' p) →
      clArityAtC R (c, b) u = clArityAtC R (c, b') u
  | [], c, b, b', h => by
      have hnil : b [] = b' [] := h [] List.nil_prefix
      rw [clArityAtC_nil, clArityAtC_nil]
      exact clArityC_congr_coin hnil
  | i :: u, c, b, b', h => by
      rw [clArityAtC_cons, clArityAtC_cons]
      have hnil : b [] = b' [] := h [] List.nil_prefix
      have hfst : (clSubC R (c, b) i).1 = (clSubC R (c, b') i).1 := clSubC_fst_congr hnil i
      have hb : ∀ p : List ℕ, p <+: u → b (i :: p) = b' (i :: p) := fun p hp ↦
        h (i :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
      calc clArityAtC R (clSubC R (c, b) i) u
          = clArityAtC R ((clSubC R (c, b) i).1, fun w ↦ b (i :: w)) u := rfl
        _ = clArityAtC R ((clSubC R (c, b') i).1, fun w ↦ b' (i :: w)) u := by
            rw [hfst]
            exact clArityAtC_congr R u _ _ _ hb
        _ = clArityAtC R (clSubC R (c, b') i) u := rfl

/-! ### Measurability at a fixed coin field -/

lemma measurableSet_clHitCond (R : ℕ) :
    MeasurableSet {c : GWord N → ℕ | clHitCond R c} := by
  have he : {c : GWord N → ℕ | clHitCond R c}
      = ⋃ n ∈ Finset.range R,
          (fun c : GWord N → ℕ ↦ neckIter (gSplitBush c 0) n) ⁻¹'
            {d : GWord N → ℕ | 2 ≤ skeletonDegree d} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Finset.mem_range,
      clHitCond]
    constructor
    · rintro ⟨n, hnR, hn⟩
      exact ⟨n, hnR, hn⟩
    · rintro ⟨n, hnR, hn⟩
      exact ⟨n, hnR, hn⟩
  rw [he]
  refine MeasurableSet.biUnion (Set.to_countable _) fun n _ ↦ ?_
  exact ((measurable_neckIter n).comp (measurable_gSplitBush 0))
    (fibreMeasurableG_skeletonDegree.preimage {m : ℕ | 2 ≤ m})

/-- The countable-index composition: reading a subfield at a countably valued index is
measurable. -/
lemma measurable_gSplitBush_at_index {g : (GWord N → ℕ) → ℕ}
    (hg : FibreMeasurableG g) :
    Measurable (fun c : GWord N → ℕ ↦ gSplitBush c (g c)) := by
  intro t ht
  have he : (fun c : GWord N → ℕ ↦ gSplitBush c (g c)) ⁻¹' t
      = ⋃ m : ℕ, ({c : GWord N → ℕ | g c = m}
          ∩ (fun c : GWord N → ℕ ↦ gSplitBush c m) ⁻¹' t) := by
    ext c
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hc
      exact ⟨g c, rfl, hc⟩
    · rintro ⟨m, hm, hc⟩
      rwa [hm]
  rw [he]
  exact MeasurableSet.iUnion fun m ↦ (hg m).inter (measurable_gSplitBush m ht)

lemma fibreMeasurableG_gArity_bush0 :
    FibreMeasurableG (fun c : GWord N → ℕ ↦ gArity (gSplitBush c 0)) := fun m ↦
  measurable_gSplitBush 0 (fibreMeasurableG_gArity m)

lemma measurable_clSubC_fst (R : ℕ) (b : List ℕ → Bool) (i : ℕ) :
    Measurable (fun c : GWord N → ℕ ↦ (clSubC R (c, b) i).1) := by
  cases hb : b [] with
  | false =>
      have he : (fun c : GWord N → ℕ ↦ (clSubC R (c, b) i).1)
          = fun c ↦ gSplitBush c i := funext fun c ↦ clSubC_fst_coin_false hb i
      rw [he]
      exact measurable_gSplitBush i
  | true =>
      have he : (fun c : GWord N → ℕ ↦ (clSubC R (c, b) i).1)
          = fun c ↦ if clHitCond R c then
              (if i < gArity (gSplitBush c 0) then gSplitBush (gSplitBush c 0) i
               else gSplitBush c (i - gArity (gSplitBush c 0) + 1))
            else (if i = 0 then neckIter (gSplitBush c 0) R else gSplitBush c i) := by
        funext c
        by_cases hh : clHitCond R c
        · rw [clSubC_fst_hit hb hh, if_pos hh]
        · rw [clSubC_fst_miss hb hh, if_neg hh]
      rw [he]
      classical
      refine Measurable.ite (measurableSet_clHitCond R) ?_ ?_
      · refine Measurable.ite ?_ ?_ ?_
        · have hpre : {c : GWord N → ℕ | i < gArity (gSplitBush c 0)}
              = (fun c : GWord N → ℕ ↦ gSplitBush c 0) ⁻¹'
                  {d : GWord N → ℕ | i < gArity d} := rfl
          rw [hpre]
          exact measurable_gSplitBush 0
            (fibreMeasurableG_gArity.preimage {m : ℕ | i < m})
        · exact (measurable_gSplitBush i).comp (measurable_gSplitBush 0)
        · exact measurable_gSplitBush_at_index
            (fibreMeasurableG_gArity_bush0.map fun m ↦ i - m + 1)
      · by_cases h0 : i = 0
        · have he2 : (fun c : GWord N → ℕ ↦
              if i = 0 then neckIter (gSplitBush c 0) R else gSplitBush c i)
              = fun c ↦ neckIter (gSplitBush c 0) R := by
            funext c
            rw [if_pos h0]
          rw [he2]
          exact (measurable_neckIter R).comp (measurable_gSplitBush 0)
        · have he2 : (fun c : GWord N → ℕ ↦
              if i = 0 then neckIter (gSplitBush c 0) R else gSplitBush c i)
              = fun c ↦ gSplitBush c i := by
            funext c
            rw [if_neg h0]
          rw [he2]
          exact measurable_gSplitBush i

lemma measurable_clAtC_fst (R : ℕ) :
    ∀ (u : List ℕ) (b : List ℕ → Bool),
      Measurable (fun c : GWord N → ℕ ↦ (clAtC R (c, b) u).1)
  | [], _ => measurable_id
  | i :: u, b => by
      have he : (fun c : GWord N → ℕ ↦ (clAtC R (c, b) (i :: u)).1)
          = (fun d : GWord N → ℕ ↦ (clAtC R (d, fun w ↦ b (i :: w)) u).1)
            ∘ fun c ↦ (clSubC R (c, b) i).1 := by
        funext c
        have hsub : clSubC R (c, b) i = ((clSubC R (c, b) i).1, fun w ↦ b (i :: w)) := by
          rw [Prod.ext_iff]
          exact ⟨rfl, clSubC_snd R (c, b) i⟩
        rw [Function.comp_apply, clAtC_cons, hsub]
      rw [he]
      exact (measurable_clAtC_fst R u _).comp (measurable_clSubC_fst R b i)

lemma measurableSet_clNeckAtC_eq (R : ℕ) (b : List ℕ → Bool) (u : List ℕ) (r : ℕ) :
    MeasurableSet {c : GWord N → ℕ | clNeckAtC R (c, b) u = r} := by
  have he : {c : GWord N → ℕ | clNeckAtC R (c, b) u = r}
      = (fun c : GWord N → ℕ ↦ (clAtC R (c, b) u).1) ⁻¹'
          {d : GWord N → ℕ | gSplitDepth d = r} := rfl
  rw [he]
  exact measurable_clAtC_fst R u b (fibreMeasurableG_gSplitDepth r)

lemma measurableSet_clArityC_eq (R : ℕ) (b0 : Bool) (j : ℕ) :
    MeasurableSet {c : GWord N → ℕ | clArityC R (c, fun _ ↦ b0) = j} := by
  cases b0 with
  | false =>
      have he : {c : GWord N → ℕ | clArityC R (c, fun _ : List ℕ ↦ false) = j}
          = {c : GWord N → ℕ | gArity c = j} := by
        ext c
        rw [Set.mem_setOf_eq, clArityC_coin_false rfl, Set.mem_setOf_eq]
      rw [he]
      exact fibreMeasurableG_gArity j
  | true =>
      have he : {c : GWord N → ℕ | clArityC R (c, fun _ : List ℕ ↦ true) = j}
          = ({c : GWord N → ℕ | clHitCond R c}
              ∩ {c : GWord N → ℕ | gArity c + gArity (gSplitBush c 0) - 1 = j})
            ∪ ({c : GWord N → ℕ | clHitCond R c}ᶜ ∩ {c : GWord N → ℕ | gArity c = j}) := by
        ext c
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        by_cases hh : clHitCond R c
        · rw [clArityC_hit rfl hh]
          tauto
        · rw [clArityC_miss rfl hh]
          tauto
      rw [he]
      have hsum : MeasurableSet
          {c : GWord N → ℕ | gArity c + gArity (gSplitBush c 0) - 1 = j} := by
        have hf : FibreMeasurableG
            (fun c : GWord N → ℕ ↦ (gArity c, gArity (gSplitBush c 0))) :=
          fibreMeasurableG_gArity.prod
            fun m ↦ (measurable_gSplitBush 0) (fibreMeasurableG_gArity m)
        exact (hf.map fun p ↦ p.1 + p.2 - 1) j
      exact ((measurableSet_clHitCond R).inter hsum).union
        ((measurableSet_clHitCond R).compl.inter (fibreMeasurableG_gArity j))

lemma measurableSet_clArityAtC_eq (R : ℕ) (b : List ℕ → Bool) (u : List ℕ) (j : ℕ) :
    MeasurableSet {c : GWord N → ℕ | clArityAtC R (c, b) u = j} := by
  have hb : ∀ c : GWord N → ℕ, clArityAtC R (c, b) u
      = clArityC R ((clAtC R (c, b) u).1, fun _ ↦ b u) := by
    intro c
    have hsnd : (clAtC R (c, b) u).2 = fun w ↦ b (u ++ w) := clAtC_snd R u (c, b)
    show clArityC R (clAtC R (c, b) u) = _
    have hpair : clAtC R (c, b) u = ((clAtC R (c, b) u).1, fun w ↦ b (u ++ w)) := by
      rw [Prod.ext_iff]
      exact ⟨rfl, hsnd⟩
    rw [hpair]
    exact clArityC_congr_coin (by simp)
  have he : {c : GWord N → ℕ | clArityAtC R (c, b) u = j}
      = (fun c : GWord N → ℕ ↦ (clAtC R (c, b) u).1) ⁻¹'
          {d : GWord N → ℕ | clArityC R (d, fun _ ↦ b u) = j} := by
    ext c
    rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_setOf_eq, hb c]
  rw [he]
  exact measurable_clAtC_fst R u b (measurableSet_clArityC_eq R (b u) j)

end ChainClasses
