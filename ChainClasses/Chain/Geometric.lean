import ChainClasses.Chain.Encoding
import ChainClasses.Chain.Quantise
import Mathlib.Tactic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
`thm:geometric` of `matching_classes_simple.tex`, the probabilistic layer of the
chain encoding, over an abstract i.i.d. offspring field `X : Word → Ω → Bool`
with `P {X v = true} = θ₂ = t`.

* `kappaAux`, `iotaAux`, `labAux`: junk-valued totalisations of `kappa`, `iota`,
  `lab`, defined for every field; on the good event they agree with the
  `Encoding` versions (`kappaAux_eq`, `iotaAux_eq`, `labAux_eq`).
* `measurableSet_labAux`, `measurable_labAux`: the label events are measurable.
* `not_chains_null`, `chains_ae`: the event `Ω₀`, that every chain terminates,
  has full probability.
* `exploration`: `eq:exploration`, the product formula for the label events of
  a prefix-closed finite set of binary words.
* `label_prod`: the same product formula for an arbitrary finite set, by
  summing out the missing prefixes.
* `label_marginal`: the geometric law `ℙ(λ(w) = m) = θ₁^(m-1) θ₂`.
* `label_iIndepFun`: the labels form an independent family; together with
  `label_marginal` this is `thm:geometric`.
* `quantised_label_iIndepFun`: the quantised labels `ℓ_D(λ(w))` inherit the
  independence, the independence clause of `thm:quantised-law`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical

/-! ### The totalised encoding -/

/-- The junk-valued chain length: `kappa` extended to every field, with value
`0` on a chain that never terminates. -/
noncomputable def kappaAux (χ : Word → Bool) (v : Word) : ℕ :=
  if h : ∃ k, χ (v ++ List.replicate k false) = true then Nat.find h + 1 else 0

/-- The junk-valued projection: the fold of `eq:phi-def` through `kappaAux`. -/
noncomputable def iotaAux (χ : Word → Bool) (w : Word) : Word :=
  w.foldl (fun v j => v ++ List.replicate (kappaAux χ v - 1) false ++ [j]) []

/-- The junk-valued labelling `eq:lambda-def`. -/
noncomputable def labAux (χ : Word → Bool) (w : Word) : ℕ := kappaAux χ (iotaAux χ w)

lemma labAux_def (χ : Word → Bool) (w : Word) : labAux χ w = kappaAux χ (iotaAux χ w) := rfl

@[simp] lemma iotaAux_nil (χ : Word → Bool) : iotaAux χ [] = [] := rfl

/-- On the good event the totalised chain length is the chain length. -/
lemma kappaAux_eq {χ : Word → Bool} (hχ : Chains χ) : kappaAux χ = kappa hχ := by
  funext v
  show (if h : ∃ k, χ (v ++ List.replicate k false) = true then Nat.find h + 1 else 0)
      = Nat.find (hχ v) + 1
  rw [dite_eq_left (hχ v)]

/-- On the good event the totalised projection is the projection. -/
lemma iotaAux_eq {χ : Word → Bool} (hχ : Chains χ) : iotaAux χ = iota hχ := by
  funext w
  simp only [iotaAux, iota, kappaAux_eq hχ]

/-- On the good event the totalised labelling is the labelling. -/
lemma labAux_eq {χ : Word → Bool} (hχ : Chains χ) : labAux χ = lab hχ := by
  funext w
  simp only [labAux_def, lab, iotaAux_eq hχ, kappaAux_eq hχ]

lemma one_le_labAux {χ : Word → Bool} (hχ : Chains χ) (w : Word) : 1 ≤ labAux χ w := by
  rw [labAux_eq hχ]
  exact lab_pos hχ w

/-- `eq:phi-def` for the totalised projection. -/
lemma iotaAux_concat (χ : Word → Bool) (w : Word) (j : Bool) :
    iotaAux χ (w ++ [j])
      = iotaAux χ w ++ List.replicate (labAux χ w - 1) false ++ [j] := by
  simp [iotaAux, labAux_def, List.foldl_append]

/-- A positive value of `kappaAux` reads off a coordinate pattern along the ray:
`κ(v) = m` exactly when the branch letter sits at `v·1^(m-1)` and nowhere before. -/
lemma kappaAux_eq_iff {χ : Word → Bool} {v : Word} {m : ℕ} (hm : 1 ≤ m) :
    kappaAux χ v = m ↔
      χ (v ++ List.replicate (m - 1) false) = true ∧
        ∀ l < m - 1, χ (v ++ List.replicate l false) = false := by
  unfold kappaAux
  by_cases hex : ∃ k, χ (v ++ List.replicate k false) = true
  · rw [dite_eq_left hex]
    constructor
    · intro h
      have hfind : Nat.find hex = m - 1 := by omega
      refine ⟨hfind ▸ Nat.find_spec hex, fun l hl => ?_⟩
      have := Nat.find_min hex (m := l) (by omega)
      simpa using this
    · intro ⟨h1, h2⟩
      have : Nat.find hex = m - 1 :=
        (Nat.find_eq_iff hex).mpr ⟨h1, fun l hl => by simp [h2 l hl]⟩
      omega
  · rw [dite_eq_right hex]
    constructor
    · intro h
      omega
    · intro ⟨h1, _⟩
      exact absurd ⟨m - 1, h1⟩ hex

/-- `kappaAux` vanishes exactly on a non-terminating chain. -/
lemma kappaAux_eq_zero_iff {χ : Word → Bool} {v : Word} :
    kappaAux χ v = 0 ↔ ∀ k, χ (v ++ List.replicate k false) = false := by
  unfold kappaAux
  by_cases hex : ∃ k, χ (v ++ List.replicate k false) = true
  · rw [dite_eq_left hex]
    constructor
    · intro h
      omega
    · intro hall
      obtain ⟨k, hk⟩ := hex
      rw [hall k] at hk
      exact absurd hk Bool.false_ne_true
  · rw [dite_eq_right hex]
    refine ⟨fun _ k => ?_, fun _ => rfl⟩
    have := not_exists.mp hex k
    simpa using this

/-! ### The deterministic bridge

The projection of a deterministic labelling `n : Word → ℕ` through the encoding
fold, `eq:normal-form` read off `n` alone; everything in this layer is private. -/

private noncomputable def iotaN (n : Word → ℕ) (w : Word) : Word :=
  (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ List.replicate (n p.1 - 1) false ++ [j]))
    (([] : Word), ([] : Word))).2

private lemma iotaN_foldl_fst (n : Word → ℕ) :
    ∀ (w p q : Word),
      (w.foldl (fun s j => (s.1 ++ [j], s.2 ++ List.replicate (n s.1 - 1) false ++ [j]))
        (p, q)).1 = p ++ w := by
  intro w
  induction w with
  | nil => intro p q; simp
  | cons a w ih =>
      intro p q
      simp only [List.foldl_cons]
      rw [ih]
      simp

private lemma iotaN_concat (n : Word → ℕ) (w : Word) (j : Bool) :
    iotaN n (w ++ [j]) = iotaN n w ++ List.replicate (n w - 1) false ++ [j] := by
  have h := iotaN_foldl_fst n w [] []
  simp only [List.nil_append] at h
  simp only [iotaN, List.foldl_append, List.foldl_cons, List.foldl_nil, h]

private lemma iotaN_prefix (n : Word → ℕ) {w w' : Word} (h : w <+: w') :
    iotaN n w <+: iotaN n w' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc]
      calc iotaN n w <+: iotaN n (w ++ u) := ih
        _ <+: iotaN n (w ++ u ++ [j]) := by
            rw [iotaN_concat]
            exact (List.prefix_append _ _).trans (List.prefix_append _ _)

private lemma iotaN_concat_length (n : Word → ℕ) {w : Word} (hn : 1 ≤ n w) (j : Bool) :
    (iotaN n (w ++ [j])).length = (iotaN n w).length + n w := by
  rw [iotaN_concat]
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

/-- The analogue of `ray_chain_disjoint` for the deterministic projection: the
ray of `w` avoids the chain of `w'` when `w` is not a prefix of `w'`. -/
private lemma iotaN_ray_chain_disjoint (n : Word → ℕ) {w w' : Word} (h : ¬ w <+: w')
    {j l : ℕ} (hl : l < n w')
    (heq : iotaN n w ++ List.replicate j false = iotaN n w' ++ List.replicate l false) :
    False := by
  by_cases h2 : w' <+: w
  · obtain ⟨u, rfl⟩ := h2
    cases u with
    | nil => exact h (by simp)
    | cons c rest =>
        have hpre : iotaN n (w' ++ [c]) <+: iotaN n (w' ++ c :: rest) :=
          iotaN_prefix n ⟨rest, by simp⟩
        have hlen1 : (iotaN n (w' ++ [c])).length ≤ (iotaN n (w' ++ c :: rest)).length :=
          hpre.length_le
        have hlen2 : (iotaN n (w' ++ [c])).length = (iotaN n w').length + n w' :=
          iotaN_concat_length n (by omega) c
        have hv := congrArg List.length heq
        simp only [List.length_append, List.length_replicate] at hv
        omega
  · obtain ⟨p, a, b, hab, hpa, hpb⟩ := exists_diverge h h2
    have hqa : iotaN n (p ++ [a]) <+: iotaN n w ++ List.replicate j false :=
      (iotaN_prefix n hpa).trans ⟨List.replicate j false, rfl⟩
    have hqb : iotaN n (p ++ [b]) <+: iotaN n w ++ List.replicate j false := by
      rw [heq]
      exact (iotaN_prefix n hpb).trans ⟨List.replicate l false, rfl⟩
    have hlen : (iotaN n (p ++ [a])).length = (iotaN n (p ++ [b])).length := by
      rw [iotaN_concat, iotaN_concat]
      simp
    have heq2 := prefix_eq_of_length hqa hqb hlen
    rw [iotaN_concat, iotaN_concat] at heq2
    have : a = b := by
      have := List.append_cancel_left heq2
      simpa using this
    exact hab this

/-- Within one chain the level determines the coordinate. -/
private lemma iotaN_coord_inj (n : Word → ℕ) (w : Word) {l l' : ℕ}
    (h : iotaN n w ++ List.replicate l false = iotaN n w ++ List.replicate l' false) :
    l = l' := by
  have := congrArg List.length h
  simpa using this

/-- Coordinates of distinct chains are distinct. -/
private lemma iotaN_coord_ne (n : Word → ℕ) {w w' : Word} (hne : w ≠ w') {l l' : ℕ}
    (hl : l < n w) (hl' : l' < n w') :
    iotaN n w ++ List.replicate l false ≠ iotaN n w' ++ List.replicate l' false := by
  intro heq
  by_cases hp : w <+: w'
  · have hp' : ¬ w' <+: w := fun hp' =>
      hne (List.IsPrefix.eq_of_length hp (Nat.le_antisymm hp.length_le hp'.length_le))
    exact iotaN_ray_chain_disjoint n hp' hl heq.symm
  · exact iotaN_ray_chain_disjoint n hp hl' heq

/-- The bridging lemma: once the labels at the strict prefixes of `w` are
prescribed by `n`, the projection at `w` is the deterministic one. -/
private lemma iotaAux_eq_iotaN (χ : Word → Bool) (n : Word → ℕ) :
    ∀ w : Word, (∀ p, p <+: w → p ≠ w → labAux χ p = n p) → iotaAux χ w = iotaN n w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => exact fun _ => rfl
  | append_singleton w j ih =>
      intro h
      have hw : labAux χ w = n w := by
        refine h w (List.prefix_append _ _) ?_
        intro hcontra
        have := congrArg List.length hcontra
        simp at this
      have hpre : ∀ p, p <+: w → p ≠ w → labAux χ p = n p := by
        intro p hp _
        refine h p (hp.trans (List.prefix_append _ _)) ?_
        intro hcontra
        have h1 := hp.length_le
        have h2 := congrArg List.length hcontra
        simp only [List.length_append, List.length_singleton] at h2
        omega
      rw [iotaAux_concat, iotaN_concat, ih hpre, hw]

/-- Under prescribed strict-prefix labels, the label event at `w` is a
coordinate pattern along the deterministic chain of `w`. -/
private lemma labAux_eq_iff_pattern (χ : Word → Bool) (n : Word → ℕ) {w : Word}
    (hw : 1 ≤ n w) (hpre : ∀ p, p <+: w → p ≠ w → labAux χ p = n p) :
    labAux χ w = n w ↔
      χ (iotaN n w ++ List.replicate (n w - 1) false) = true ∧
        ∀ l < n w - 1, χ (iotaN n w ++ List.replicate l false) = false := by
  rw [labAux_def, iotaAux_eq_iotaN χ n w hpre]
  exact kappaAux_eq_iff hw

/-- The full label prescription on a prefix-closed finite set is exactly the
coordinate pattern along all its chains; the reverse direction is the
exploration induction of `thm:geometric`. -/
private lemma labAux_forall_iff_pattern (χ : Word → Bool) (s : Finset Word)
    (hs : ∀ w ∈ s, ∀ p, p <+: w → p ∈ s) (n : Word → ℕ) (hn : ∀ w ∈ s, 1 ≤ n w) :
    (∀ w ∈ s, labAux χ w = n w) ↔
      ∀ w ∈ s, χ (iotaN n w ++ List.replicate (n w - 1) false) = true ∧
        ∀ l < n w - 1, χ (iotaN n w ++ List.replicate l false) = false := by
  constructor
  · intro h w hw
    have hpre : ∀ p, p <+: w → p ≠ w → labAux χ p = n p := fun p hp _ =>
      h p (hs w hw p hp)
    exact (labAux_eq_iff_pattern χ n (hn w hw) hpre).mp (h w hw)
  · intro h
    have key : ∀ k, ∀ w ∈ s, w.length ≤ k → labAux χ w = n w := by
      intro k
      induction k with
      | zero =>
          intro w hw hk
          have hpre : ∀ p, p <+: w → p ≠ w → labAux χ p = n p := by
            intro p hp hne
            exact absurd (hp.eq_of_length (by have := hp.length_le; omega)) hne
          exact (labAux_eq_iff_pattern χ n (hn w hw) hpre).mpr (h w hw)
      | succ k ih =>
          intro w hw hk
          have hpre : ∀ p, p <+: w → p ≠ w → labAux χ p = n p := by
            intro p hp hne
            have hlt : p.length < w.length :=
              lt_of_le_of_ne hp.length_le fun hl => hne (hp.eq_of_length hl)
            exact ih p (hs w hw p hp) (by omega)
          exact (labAux_eq_iff_pattern χ n (hn w hw) hpre).mpr (h w hw)
    exact fun w hw => key w.length w hw le_rfl

/-- The coordinates participating in the exploration of `s`. -/
private noncomputable def coordSet (n : Word → ℕ) (s : Finset Word) : Finset Word :=
  s.biUnion fun w => (Finset.range (n w)).image fun l => iotaN n w ++ List.replicate l false

/-- The value each participating coordinate is required to read: `true` at the
end of a chain, `false` inside it. -/
private noncomputable def coordVal (n : Word → ℕ) (s : Finset Word) (v : Word) : Bool :=
  decide (v ∈ s.image fun w => iotaN n w ++ List.replicate (n w - 1) false)

private lemma mem_coordSet {n : Word → ℕ} {s : Finset Word} {v : Word} :
    v ∈ coordSet n s ↔ ∃ w ∈ s, ∃ l < n w, v = iotaN n w ++ List.replicate l false := by
  simp only [coordSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  exact exists_congr fun w => and_congr_right fun _ =>
    ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩⟩

private lemma coordVal_last (n : Word → ℕ) (s : Finset Word) {w : Word} (hw : w ∈ s) :
    coordVal n s (iotaN n w ++ List.replicate (n w - 1) false) = true := by
  simp only [coordVal, decide_eq_true_eq]
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

private lemma coordVal_chain (n : Word → ℕ) (s : Finset Word) (hn : ∀ w ∈ s, 1 ≤ n w)
    {w : Word} (hw : w ∈ s) {l : ℕ} (hl : l < n w - 1) :
    coordVal n s (iotaN n w ++ List.replicate l false) = false := by
  simp only [coordVal, decide_eq_false_iff_not]
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨w', hw', heq⟩
  by_cases hww' : w' = w
  · subst hww'
    have := iotaN_coord_inj n w' heq
    omega
  · have h1 := hn w' hw'
    exact iotaN_coord_ne n hww' (by omega) (by omega) heq

private lemma coordSet_pairwiseDisjoint (n : Word → ℕ) (s : Finset Word) :
    (↑s : Set Word).PairwiseDisjoint fun w =>
      (Finset.range (n w)).image fun l => iotaN n w ++ List.replicate l false := by
  intro w _ w' _ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hv hv'
  rcases Finset.mem_image.mp hv with ⟨l, hl, rfl⟩
  rcases Finset.mem_image.mp hv' with ⟨l', hl', heq⟩
  exact iotaN_coord_ne n hne (Finset.mem_range.mp hl) (Finset.mem_range.mp hl') heq.symm

/-! ### The measure layer -/

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable (X : Word → Ω → Bool) (t : ℝ)

private lemma measurableSet_coord (hmeas : ∀ v, Measurable (X v)) (v : Word) (e : Bool) :
    MeasurableSet {ω | X v ω = e} :=
  hmeas v (measurableSet_singleton e)

/-- The `kappaAux` events are measurable: countably many coordinate events. -/
lemma measurableSet_kappaAux (hmeas : ∀ v, Measurable (X v)) (u : Word) (m : ℕ) :
    MeasurableSet {ω | kappaAux (fun v => X v ω) u = m} := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hset : {ω | kappaAux (fun v => X v ω) u = 0}
        = ⋂ k : ℕ, {ω | X (u ++ List.replicate k false) ω = false} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact kappaAux_eq_zero_iff
    rw [hset]
    exact MeasurableSet.iInter fun k => measurableSet_coord X hmeas _ false
  · have hset : {ω | kappaAux (fun v => X v ω) u = m}
        = {ω | X (u ++ List.replicate (m - 1) false) ω = true} ∩
            ⋂ (l : ℕ), ⋂ (_ : l < m - 1), {ω | X (u ++ List.replicate l false) ω = false} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact kappaAux_eq_iff hm
    rw [hset]
    exact (measurableSet_coord X hmeas _ true).inter
      (MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
        measurableSet_coord X hmeas _ false)

/-- The `iotaAux` events are measurable. -/
lemma measurableSet_iotaAux (hmeas : ∀ v, Measurable (X v)) (w u : Word) :
    MeasurableSet {ω | iotaAux (fun v => X v ω) w = u} := by
  induction w using List.reverseRecOn generalizing u with
  | nil =>
      by_cases h : u = ([] : Word)
      · subst h
        have hset : {ω | iotaAux (fun v => X v ω) [] = ([] : Word)} = Set.univ := by
          ext ω
          simp
        rw [hset]
        exact MeasurableSet.univ
      · have hset : {ω | iotaAux (fun v => X v ω) [] = u} = ∅ := by
          ext ω
          simp only [iotaAux_nil, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun hcontra => h hcontra.symm
        rw [hset]
        exact MeasurableSet.empty
  | append_singleton w j ih =>
      have hset : {ω | iotaAux (fun v => X v ω) (w ++ [j]) = u}
          = ⋃ (p : Word), ⋃ (m : ℕ),
              ⋃ (_ : p ++ List.replicate (m - 1) false ++ [j] = u),
                ({ω | iotaAux (fun v => X v ω) w = p} ∩
                  {ω | kappaAux (fun v => X v ω) p = m}) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
        constructor
        · intro h
          exact ⟨iotaAux (fun v => X v ω) w, labAux (fun v => X v ω) w,
            by rw [← iotaAux_concat]; exact h, rfl, (labAux_def _ w).symm⟩
        · rintro ⟨p, m, hcond, hp, hm⟩
          rw [iotaAux_concat, labAux_def, hp, hm]
          exact hcond
      rw [hset]
      exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun m =>
        MeasurableSet.iUnion fun _ =>
          (ih p).inter (measurableSet_kappaAux X hmeas p m)

/-- The label events are measurable. -/
lemma measurableSet_labAux (hmeas : ∀ v, Measurable (X v)) (w : Word) (m : ℕ) :
    MeasurableSet {ω | labAux (fun v => X v ω) w = m} := by
  have hset : {ω | labAux (fun v => X v ω) w = m}
      = ⋃ u : Word, ({ω | iotaAux (fun v => X v ω) w = u} ∩
          {ω | kappaAux (fun v => X v ω) u = m}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨iotaAux (fun v => X v ω) w, rfl, h⟩
    · rintro ⟨u, hu, hk⟩
      rw [labAux_def, hu]
      exact hk
  rw [hset]
  exact MeasurableSet.iUnion fun u =>
    (measurableSet_iotaAux X hmeas w u).inter (measurableSet_kappaAux X hmeas u m)

/-- Each label is a measurable function. -/
lemma measurable_labAux (hmeas : ∀ v, Measurable (X v)) (w : Word) :
    Measurable fun ω => labAux (fun v => X v ω) w :=
  measurable_to_countable' fun m => measurableSet_labAux X hmeas w m

omit [IsProbabilityMeasure P] in
/-- Independence evaluates finite intersections of coordinate events. -/
private lemma meas_biInter_coord (hindep : iIndepFun X P) (T : Finset Word)
    (b : Word → Bool) :
    P (⋂ v ∈ T, X v ⁻¹' {b v}) = ∏ v ∈ T, P (X v ⁻¹' {b v}) :=
  hindep.measure_inter_preimage_eq_mul T fun v _ => measurableSet_singleton (b v)

omit [IsProbabilityMeasure P] in
private lemma prob_coord_true (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t)
    (v : Word) : P (X v ⁻¹' {true}) = ENNReal.ofReal t := htrue v

private lemma prob_coord_false (hmeas : ∀ v, Measurable (X v))
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht0 : 0 ≤ t) (v : Word) :
    P (X v ⁻¹' {false}) = ENNReal.ofReal (1 - t) := by
  have hcompl : X v ⁻¹' {false} = (X v ⁻¹' {true})ᶜ := by
    ext ω
    simp
  rw [hcompl, prob_compl_eq_one_sub (hmeas v (measurableSet_singleton true)),
    prob_coord_true P X t htrue v, ENNReal.ofReal_sub 1 ht0, ENNReal.ofReal_one]

omit [MeasurableSpace Ω] in
/-- The label event of a prefix-closed finite set is exactly the coordinate
pattern along its chains. -/
private lemma labEvent_eq_coordEvent (s : Finset Word)
    (hs : ∀ w ∈ s, ∀ p, p <+: w → p ∈ s) (n : Word → ℕ) (hn : ∀ w ∈ s, 1 ≤ n w) :
    (⋂ w ∈ s, {ω | labAux (fun v => X v ω) w = n w})
      = ⋂ v ∈ coordSet n s, X v ⁻¹' {coordVal n s v} := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  rw [labAux_forall_iff_pattern (fun v => X v ω) s hs n hn]
  constructor
  · intro h v hv
    rcases mem_coordSet.mp hv with ⟨w, hw, l, hl, rfl⟩
    by_cases hcase : l = n w - 1
    · subst hcase
      rw [coordVal_last n s hw]
      exact (h w hw).1
    · have hl' : l < n w - 1 := by
        have := hn w hw
        omega
      rw [coordVal_chain n s hn hw hl']
      exact (h w hw).2 l hl'
  · intro h w hw
    have h1 := hn w hw
    constructor
    · have hv : iotaN n w ++ List.replicate (n w - 1) false ∈ coordSet n s :=
        mem_coordSet.mpr ⟨w, hw, n w - 1, by omega, rfl⟩
      rw [h _ hv, coordVal_last n s hw]
    · intro l hl
      have hv : iotaN n w ++ List.replicate l false ∈ coordSet n s :=
        mem_coordSet.mpr ⟨w, hw, l, by omega, rfl⟩
      rw [h _ hv, coordVal_chain n s hn hw hl]

/-- The probability of the coordinate pattern, regrouped chain by chain. -/
private lemma prob_coordEvent (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (s : Finset Word) (n : Word → ℕ) (hn : ∀ w ∈ s, 1 ≤ n w) :
    P (⋂ v ∈ coordSet n s, X v ⁻¹' {coordVal n s v})
      = ∏ w ∈ s, ENNReal.ofReal ((1 - t) ^ (n w - 1) * t) := by
  have h0 : (0 : ℝ) ≤ 1 - t := by linarith
  rw [meas_biInter_coord P X hindep _ _]
  simp only [coordSet]
  rw [Finset.prod_biUnion (coordSet_pairwiseDisjoint n s)]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Finset.prod_image fun l _ l' _ h => iotaN_coord_inj n w h]
  obtain ⟨k, hk⟩ : ∃ k, n w = k + 1 := ⟨n w - 1, by have := hn w hw; omega⟩
  rw [hk, Nat.add_sub_cancel, Finset.prod_range_succ]
  have hlast : coordVal n s (iotaN n w ++ List.replicate k false) = true := by
    have hk1 : k = n w - 1 := by omega
    rw [hk1]
    exact coordVal_last n s hw
  have hchain : ∀ l ∈ Finset.range k,
      P (X (iotaN n w ++ List.replicate l false)
          ⁻¹' {coordVal n s (iotaN n w ++ List.replicate l false)})
        = ENNReal.ofReal (1 - t) := by
    intro l hl
    rw [coordVal_chain n s hn hw (by have := Finset.mem_range.mp hl; omega)]
    exact prob_coord_false P X t hmeas htrue ht0 _
  rw [hlast, prob_coord_true P X t htrue, Finset.prod_congr rfl hchain, Finset.prod_const,
    Finset.card_range, ← ENNReal.ofReal_pow h0, ← ENNReal.ofReal_mul (pow_nonneg h0 k)]

/-- **`eq:exploration`**: for a prefix-closed finite set of binary words the
label events factorise into the geometric masses. -/
theorem exploration (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht1 : t ≤ 1)
    (ht0 : 0 ≤ t) (s : Finset Word) (hs : ∀ w ∈ s, ∀ p, p <+: w → p ∈ s)
    (n : Word → ℕ) (hn : ∀ w ∈ s, 1 ≤ n w) :
    P (⋂ w ∈ s, {ω | labAux (fun v => X v ω) w = n w})
      = ∏ w ∈ s, ENNReal.ofReal ((1 - t) ^ (n w - 1) * t) := by
  rw [labEvent_eq_coordEvent X s hs n hn]
  exact prob_coordEvent P X t hmeas hindep htrue ht0 ht1 s n hn

/-! ### The good event has full probability -/

/-- A single non-terminating chain is a null event. -/
private lemma bad_ray_null (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) (v : Word) :
    P (⋂ k : ℕ, X (v ++ List.replicate k false) ⁻¹' {false}) = 0 := by
  have hmass : ∀ K : ℕ,
      P (⋂ k : ℕ, X (v ++ List.replicate k false) ⁻¹' {false})
        ≤ ENNReal.ofReal (1 - t) ^ K := by
    intro K
    have hsub : (⋂ k : ℕ, X (v ++ List.replicate k false) ⁻¹' {false})
        ⊆ ⋂ k ∈ Finset.range K, X (v ++ List.replicate k false) ⁻¹' {false} := by
      intro ω hω
      simp only [Set.mem_iInter] at hω ⊢
      exact fun k _ => hω k
    refine (measure_mono hsub).trans ?_
    have hinj : Set.InjOn (fun k : ℕ => v ++ List.replicate k false) ↑(Finset.range K) := by
      intro k _ k' _ h
      have := congrArg List.length h
      simpa using this
    have hcalc := meas_biInter_coord P X hindep
      ((Finset.range K).image fun k => v ++ List.replicate k false) fun _ => false
    rw [Finset.set_biInter_finset_image, Finset.prod_image hinj] at hcalc
    rw [hcalc, Finset.prod_congr rfl fun k _ => prob_coord_false P X t hmeas htrue ht.le _,
      Finset.prod_const, Finset.card_range]
  have hlt : ENNReal.ofReal (1 - t) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  exact le_antisymm
    (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hmass)
    _root_.zero_le

/-- The complement of the good event `Ω₀` is null. -/
lemma not_chains_null (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) :
    P {ω | ¬ Chains (fun v => X v ω)} = 0 := by
  have hdecomp : {ω | ¬ Chains (fun v => X v ω)}
      = ⋃ v : Word, ⋂ k : ℕ, X (v ++ List.replicate k false) ⁻¹' {false} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Chains, not_forall, not_exists, Bool.not_eq_true,
      Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hdecomp]
  exact measure_iUnion_null fun v => bad_ray_null P X t hmeas hindep htrue ht v

/-- **`Ω₀` has full probability**: almost surely every chain terminates. -/
theorem chains_ae (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) :
    P {ω | Chains (fun v => X v ω)} = 1 := by
  have hae : {ω | Chains (fun v => X v ω)} =ᵐ[P] (Set.univ : Set Ω) := by
    rw [ae_eq_univ, Set.compl_ofPred]
    exact not_chains_null P X t hmeas hindep htrue ht
  rw [measure_congr hae, measure_univ]

/-- The junk value never occurs: a vanishing label forces a non-terminating chain. -/
lemma labAux_zero_null (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) (w : Word) :
    P {ω | labAux (fun v => X v ω) w = 0} = 0 := by
  refine measure_mono_null ?_ (not_chains_null P X t hmeas hindep htrue ht)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hχ
  have := one_le_labAux hχ w
  omega

/-! ### Arbitrary finite sets: summing out the missing prefixes -/

/-- The geometric masses have total mass one. -/
private lemma tsum_geometric_mass (ht : 0 < t) (ht1 : t ≤ 1) :
    ∑' m : ℕ, ENNReal.ofReal ((1 - t) ^ m * t) = 1 := by
  have h0 : (0 : ℝ) ≤ 1 - t := by linarith
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - t) = ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 h0, sub_sub_cancel]
  calc ∑' m : ℕ, ENNReal.ofReal ((1 - t) ^ m * t)
      = ∑' m : ℕ, ENNReal.ofReal (1 - t) ^ m * ENNReal.ofReal t := by
        refine tsum_congr fun m => ?_
        rw [ENNReal.ofReal_mul (pow_nonneg h0 m), ENNReal.ofReal_pow h0]
    _ = (1 - ENNReal.ofReal (1 - t))⁻¹ * ENNReal.ofReal t := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    _ = 1 := by
        rw [hsub]
        exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top

/-- The prefix closure of a finite set of binary words. -/
private def closureF (s : Finset Word) : Finset Word :=
  s.biUnion fun w => w.inits.toFinset

private lemma mem_closureF {s : Finset Word} {p : Word} :
    p ∈ closureF s ↔ ∃ w ∈ s, p <+: w := by
  simp [closureF, List.mem_inits]

/-- **`thm:geometric`, the product formula**: over an arbitrary finite set of
binary words the label events factorise into the geometric masses. -/
theorem label_prod (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) (ht1 : t ≤ 1)
    (s : Finset Word) (n : Word → ℕ) (hn : ∀ w ∈ s, 1 ≤ n w) :
    P (⋂ w ∈ s, {ω | labAux (fun v => X v ω) w = n w})
      = ∏ w ∈ s, ENNReal.ofReal ((1 - t) ^ (n w - 1) * t) := by
  suffices H : ∀ (d : ℕ) (s : Finset Word) (n : Word → ℕ), (∀ w ∈ s, 1 ≤ n w) →
      (closureF s \ s).card = d →
      P (⋂ w ∈ s, {ω | labAux (fun v => X v ω) w = n w})
        = ∏ w ∈ s, ENNReal.ofReal ((1 - t) ^ (n w - 1) * t) from H _ s n hn rfl
  intro d
  induction d with
  | zero =>
      intro s n hn hd
      have hsub : closureF s ⊆ s :=
        Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hd)
      have hs : ∀ w ∈ s, ∀ p, p <+: w → p ∈ s := fun w hw p hp =>
        hsub (mem_closureF.mpr ⟨w, hw, hp⟩)
      exact exploration P X t hmeas hindep htrue ht1 ht.le s hs n hn
  | succ d ih =>
      intro s n hn hd
      obtain ⟨p, hp⟩ : (closureF s \ s).Nonempty := by
        rw [← Finset.card_pos, hd]
        omega
      obtain ⟨hpc, hps⟩ := Finset.mem_sdiff.mp hp
      have hclos : closureF (insert p s) = closureF s := by
        rw [closureF, Finset.biUnion_insert]
        refine Finset.union_eq_right.mpr fun q hq => ?_
        rw [List.mem_toFinset, List.mem_inits] at hq
        obtain ⟨w₀, hw₀, hpw₀⟩ := mem_closureF.mp hpc
        exact mem_closureF.mpr ⟨w₀, hw₀, hq.trans hpw₀⟩
      have hcard : (closureF (insert p s) \ insert p s).card = d := by
        rw [hclos, Finset.sdiff_insert, Finset.card_erase_of_mem hp, hd]
        omega
      have hpart : (⋂ w ∈ s, {ω | labAux (fun v => X v ω) w = n w})
          = ⋃ m : ℕ, ⋂ w ∈ insert p s,
              {ω | labAux (fun v => X v ω) w = Function.update n p m w} := by
        ext ω
        simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
        constructor
        · intro h
          refine ⟨labAux (fun v => X v ω) p, fun w hw => ?_⟩
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · rw [Function.update_self]
          · rw [Function.update_of_ne (ne_of_mem_of_not_mem hw' hps)]
            exact h w hw'
        · rintro ⟨m, h⟩ w hw
          have hthis := h w (Finset.mem_insert_of_mem hw)
          rwa [Function.update_of_ne (ne_of_mem_of_not_mem hw hps)] at hthis
      have hmeasF : ∀ m : ℕ, MeasurableSet (⋂ w ∈ insert p s,
          {ω | labAux (fun v => X v ω) w = Function.update n p m w}) := fun m =>
        MeasurableSet.iInter fun w => MeasurableSet.iInter fun _ =>
          measurableSet_labAux X hmeas w _
      have hdisj : Pairwise (Function.onFun Disjoint fun m : ℕ =>
          ⋂ w ∈ insert p s,
            {ω | labAux (fun v => X v ω) w = Function.update n p m w}) := by
        intro m m' hmm'
        simp only [Function.onFun]
        rw [Set.disjoint_left]
        intro ω hω hω'
        have h1 := Set.mem_iInter₂.mp hω p (Finset.mem_insert_self p s)
        have h2 := Set.mem_iInter₂.mp hω' p (Finset.mem_insert_self p s)
        rw [Set.mem_ofPred_eq, Function.update_self] at h1 h2
        exact hmm' (h1.symm.trans h2)
      have hterm : ∀ m : ℕ,
          P (⋂ w ∈ insert p s,
              {ω | labAux (fun v => X v ω) w = Function.update n p (m + 1) w})
            = ENNReal.ofReal ((1 - t) ^ m * t)
                * ∏ w ∈ s, ENNReal.ofReal ((1 - t) ^ (n w - 1) * t) := by
        intro m
        have hn' : ∀ w ∈ insert p s, 1 ≤ Function.update n p (m + 1) w := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · rw [Function.update_self]
            omega
          · rw [Function.update_of_ne (ne_of_mem_of_not_mem hw' hps)]
            exact hn w hw'
        rw [ih (insert p s) (Function.update n p (m + 1)) hn' hcard,
          Finset.prod_insert hps, Function.update_self, Nat.add_sub_cancel]
        congr 1
        exact Finset.prod_congr rfl fun w hw => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hw hps)]
      have hzero : P (⋂ w ∈ insert p s,
          {ω | labAux (fun v => X v ω) w = Function.update n p 0 w}) = 0 := by
        refine measure_mono_null (fun ω hω => ?_)
          (labAux_zero_null P X t hmeas hindep htrue ht p)
        have := Set.mem_iInter₂.mp hω p (Finset.mem_insert_self p s)
        rwa [Set.mem_ofPred_eq, Function.update_self] at this
      rw [hpart, measure_iUnion hdisj hmeasF, tsum_eq_zero_add' ENNReal.summable, hzero,
        zero_add, tsum_congr hterm, ENNReal.tsum_mul_right, tsum_geometric_mass t ht ht1,
        one_mul]

/-- **`thm:geometric`, the marginal law**: each label is geometric,
`ℙ(λ(w) = m) = θ₁^(m-1) θ₂`. -/
theorem label_marginal (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) (ht1 : t ≤ 1)
    (w : Word) {m : ℕ} (hm : 1 ≤ m) :
    P {ω | labAux (fun v => X v ω) w = m}
      = ENNReal.ofReal ((1 - t) ^ (m - 1) * t) := by
  have h := label_prod P X t hmeas hindep htrue ht ht1 {w} (fun _ => m) fun _ _ => hm
  rwa [Finset.set_biInter_singleton, Finset.prod_singleton] at h

/-- The label events factorise over every finite set, junk values included. -/
theorem label_meas_biInter (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) (ht1 : t ≤ 1)
    (S : Finset Word) (n : Word → ℕ) :
    P (⋂ w ∈ S, {ω | labAux (fun v => X v ω) w = n w})
      = ∏ w ∈ S, P {ω | labAux (fun v => X v ω) w = n w} := by
  by_cases hall : ∀ w ∈ S, 1 ≤ n w
  · rw [label_prod P X t hmeas hindep htrue ht ht1 S n hall]
    exact (Finset.prod_congr rfl fun w hw =>
      label_marginal P X t hmeas hindep htrue ht ht1 w (hall w hw)).symm
  · simp only [not_forall] at hall
    obtain ⟨w₀, hw₀, hn₀⟩ := hall
    have hz : P {ω | labAux (fun v => X v ω) w₀ = n w₀} = 0 := by
      rw [show n w₀ = 0 by omega]
      exact labAux_zero_null P X t hmeas hindep htrue ht w₀
    rw [Finset.prod_eq_zero hw₀ hz]
    exact measure_mono_null
      (fun ω hω => Set.mem_iInter₂.mp hω w₀ hw₀) hz

/-! ### Independence of the labels -/

/-- The π-system of label-value events at `w`. -/
private def labelPi (X : Word → Ω → Bool) (w : Word) : Set (Set Ω) :=
  {A | ∃ m : ℕ, A = (fun ω => labAux (fun v => X v ω) w) ⁻¹' {m}}

omit [MeasurableSpace Ω] in
private lemma labelPi_isPiSystem (w : Word) : IsPiSystem (labelPi X w) := by
  rintro A ⟨m, rfl⟩ B ⟨m', rfl⟩ hAB
  obtain ⟨ω, hω, hω'⟩ := hAB
  have hm : m = m' := by
    have h1 : labAux (fun v => X v ω) w = m := hω
    have h2 : labAux (fun v => X v ω) w = m' := hω'
    omega
  subst hm
  rw [Set.inter_self]
  exact ⟨m, rfl⟩

omit [MeasurableSpace Ω] in
private lemma comap_label_eq (w : Word) :
    MeasurableSpace.comap (fun ω => labAux (fun v => X v ω) w) inferInstance
      = MeasurableSpace.generateFrom (labelPi X w) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · rw [MeasurableSpace.le_def]
    rintro A ⟨S, -, rfl⟩
    have hdecomp : (fun ω => labAux (fun v => X v ω) w) ⁻¹' S
        = ⋃ m ∈ S, (fun ω => labAux (fun v => X v ω) w) ⁻¹' {m} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨_, h, rfl⟩, by rintro ⟨m, hm, rfl⟩; exact hm⟩
    rw [hdecomp]
    exact MeasurableSet.biUnion (Set.to_countable S) fun m _ =>
      MeasurableSpace.measurableSet_generateFrom ⟨m, rfl⟩
  · rintro A ⟨m, rfl⟩
    exact ⟨{m}, measurableSet_singleton m, rfl⟩

private lemma labelPi_iIndepSets (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) (ht1 : t ≤ 1) :
    iIndepSets (labelPi X) P := by
  rw [iIndepSets_iff]
  intro S f hf
  have hf' : ∀ w, ∃ m : ℕ, w ∈ S →
      f w = (fun ω => labAux (fun v => X v ω) w) ⁻¹' {m} := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨m, hm⟩ := hf w hw
      exact ⟨m, fun _ => hm⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose n hn using hf'
  have hset : ∀ w (hw : w ∈ S), f w = {ω | labAux (fun v => X v ω) w = n w} :=
    fun w hw => hn w hw
  rw [Set.iInter₂_congr hset,
    label_meas_biInter P X t hmeas hindep htrue ht ht1 S n]
  exact (Finset.prod_congr rfl fun w hw => by rw [hset w hw]).symm

/-- **`thm:geometric`, independence**: the chain labels of an i.i.d. offspring
field form an independent family. Together with `label_marginal` this is the
statement of the lemma, and it certifies the independence clause of
`thm:quantised-law` at its root. -/
theorem label_iIndepFun (hmeas : ∀ v, Measurable (X v)) (hindep : iIndepFun X P)
    (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) (ht : 0 < t) (ht1 : t ≤ 1) :
    iIndepFun (fun w ω => labAux (fun v => X v ω) w) P := by
  rw [iIndepFun_iff_iIndep]
  exact iIndepSets.iIndep
    (fun w => (measurable_labAux X hmeas w).comap_le) (labelPi X)
    (fun w => labelPi_isPiSystem X w) (fun w => comap_label_eq X w)
    (labelPi_iIndepSets P X t hmeas hindep htrue ht ht1)

/-- **The independence clause of `thm:quantised-law`**: the quantised labels
`ℓ_D(λ(w))`, `w ∈ 𝔹`, form an independent family. -/
theorem quantised_label_iIndepFun (D : ℕ) (hmeas : ∀ v, Measurable (X v))
    (hindep : iIndepFun X P) (htrue : ∀ v, P {ω | X v ω = true} = ENNReal.ofReal t)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    iIndepFun (fun w ω => levelMap D (labAux (fun v => X v ω) w)) P :=
  (label_iIndepFun P X t hmeas hindep htrue ht ht1).comp
    (fun _ => levelMap D) (fun _ => measurable_from_top)

end ChainClasses
