/-
`thm:hairy-general` of `trichotomy.tex`, the assembly: two finitely supported supercritical
laws with `θ₀, θ₀' > 0`, sampled independently and conditioned on survival, are almost
surely quasi-isometric.

The engine of `EngineBridge` aligns the encoded label fields of two independent labelled
samples in the bushy regime `J' ≤ 2J - 1` with probability at least `1 - Ke^{-cD²}`.  The
alignment lives on `𝔹`: a skeleton vertex sits at the root of its cascade and its
children at the slots, and this file reads the engine's slot geometry as a `CascadeEnc` of
`BAssembly`, the slot of a child being the path through the cascade the balanced halving
and the marker chains prescribe.  The matching automorphism is a projective family of
swaps, hence a portrait of `𝔹`, and matched labels are equal or adjacent classes of `G_D`,
whose shapes are `3¹⁵D¹⁶`-comparable by `thm:cross-relabel`.  The glued transfer of
`it:general-glued` then yields a quasi-isometry of the two samples at a constant
polynomial in `D`, the failure probabilities are summable over `D`, and the general case
chains through the laws `θ^{(i)}` with `θ^{(i)}_0 = ε` and `θ^{(i)}_{J+i} = 1 - ε`.

* `cChild`, `CPos`, `walk`, `walk_append`, `slotPathF`, `walk_slotPathF`,
  `walk_atSlot_range`, `walk_atSlot_unique`, `walk_inside_valid`: **the slot geometry as
  paths**: the descent through a cascade along a binary word, the path to a slot, its
  range and its uniqueness, every internal vertex serving strictly fewer slots than its
  parent.
* `engineSlot`, `engineEncWord`, `ArityBounded`, `engineEnc`: **the engine's encoding as
  a `CascadeEnc`**, of depth the bound on the arities.
* `labOfK`, `labelAt`, `encAt`, `labelAt_encSub`, `encField`, `labelAt_encLab`,
  `SkelBounded`, `encField_enc`, `exists_enc_inside`, `encField_of_not_image`,
  `engineEnc_inClosure`: **reading the encoded label field**: the label of a skeleton
  vertex sits at its encoding, the class `0` of the one-vertex shape everywhere else, and
  the prefix closure of the encoded skeleton is `𝔹`.
* `autOfK`, `fullMatchesA_of_fullMatchesK`, `exists_portrait_of_infMatchK`: **the portrait
  of an infinite matching** in the engine's automorphism tower.
* `mem_sample_iff_prefix`, `gArityAt_of_not_mem_sample`, `gArityAt_le_alphabet`,
  `two_le_gArityAt_of_isGHairySample`: the arity field vanishes off the skeleton, is
  bounded by the alphabet, and is at least two on the skeleton of a hairy sample.
* `gNetLab_gOne`, `exists_partner_bFamily`, `sample_qi_of_engine_match`: **the
  deterministic core of `thm:hairy-general`**: an alignment of the encoded label fields of
  two hairy samples whose labels are the classes of `9D³`-comparable partners gives a
  `⌈216 L L'² (3·(3¹⁵D¹⁶)²)²⌉`-quasi-isometry of the samples.
* `map_ambSub`, `survivalMeasure_ambSub_null`, `ae_isGHairySample`, `ae_skeleton_good`,
  `ae_uniform_mem_Ico`, `condDraw_ne_zero`, `ae_partner_comparable`: **the almost sure
  events**: a conditioned sample is hairy, its skeleton arities lie in `{2, …, J'}` with
  shapes of positive conditional mass, and every partner is `9D³`-comparable to its
  shape.
* `measurableSet_engine_match`, `exists_gCouplings_all`, `hairy_general_rate`,
  `hairy_general_ae_small`, `ae_prod_fst_fst`, `hairy_general_ae_small'`:
  **`thm:hairy-general` at `J' ≤ 2J - 1`**, the failure rate `Ke^{-cD²}` of the
  quasi-isometry at scale `D` and the almost sure statement on the two survival measures.
* `gSampleQI_trans`, `gSampleQI_symm`, `bridgeLaw`, `bridgeLaw_supercritical`:
  **`thm:qi-transitive`** across independent samples at general arity and the
  intermediate laws of the chain.
* `hairy_general_ae_of_le`, `hairy_general_ae`: **`thm:hairy-general`**.
-/
import ChainClasses.EngineBridge
import ChainClasses.BAssembly
import ChainClasses.GeneralObstructions
import ChainClasses.GeneralShapeEta
import ChainClasses.HairyUniversality

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure sample Survives skeletonDegree bushAt)
open GraphMarkovMatching.Support (FullLab restrictLab AutK restrictAutK fullMatchesK InfMatchK)
open GraphMarkovMatching.Composite (CtrC CState cRel)

variable {N N' : ℕ}

/-! ### The slot geometry as paths -/

/-- The child of a tagged counter in the direction `b`, serving the slots from `off` on:
the left child at `false`, the right child at `true`. -/
def cChild (exc : ℕ → Option (ℕ × ℕ)) (off : ℕ) (t : CtrC) (b : Bool) : ChildK :=
  bif b then (stepKind exc off (0, t)).2 else (stepKind exc off (0, t)).1

/-- The step geometry reads the counter only. -/
lemma stepKind_eq_zero (exc : ℕ → Option (ℕ × ℕ)) (off : ℕ) (s : CState ℕ) :
    stepKind exc off s = stepKind exc off (0, s.2) := by
  obtain ⟨v, t⟩ := s
  cases t <;> rfl

/-- The position reached by a descent through a cascade: an internal vertex with its
counter and slot offset, or a slot together with the rest of the path. -/
inductive CPos where
  | inside (t : CtrC) (off : ℕ) : CPos
  | atSlot (j : ℕ) (q : List Bool) : CPos

/-- **The descent through a cascade** along a binary word, from an internal vertex of
counter `t` serving the slots from `off` on. -/
def walk (exc : ℕ → Option (ℕ × ℕ)) : CtrC → ℕ → List Bool → CPos
  | t, off, [] => CPos.inside t off
  | t, off, b :: p =>
      match cChild exc off t b with
      | ChildK.internal o t' => walk exc t' o p
      | ChildK.slot j => CPos.atSlot j p

lemma walk_nil (exc : ℕ → Option (ℕ × ℕ)) (t : CtrC) (off : ℕ) :
    walk exc t off [] = CPos.inside t off := rfl

lemma walk_cons_internal {exc : ℕ → Option (ℕ × ℕ)} {t : CtrC} {off : ℕ} {b : Bool}
    {o : ℕ} {t' : CtrC} (h : cChild exc off t b = ChildK.internal o t') (p : List Bool) :
    walk exc t off (b :: p) = walk exc t' o p := by
  simp only [walk, h]

lemma walk_cons_slot {exc : ℕ → Option (ℕ × ℕ)} {t : CtrC} {off : ℕ} {b : Bool} {j : ℕ}
    (h : cChild exc off t b = ChildK.slot j) (p : List Bool) :
    walk exc t off (b :: p) = CPos.atSlot j p := by
  simp only [walk, h]

/-- The descent along a concatenation continues from the position the first word
reaches. -/
lemma walk_append (exc : ℕ → Option (ℕ × ℕ)) :
    ∀ (p q : List Bool) (t : CtrC) (off : ℕ),
      walk exc t off (p ++ q) = match walk exc t off p with
        | CPos.inside t' o => walk exc t' o q
        | CPos.atSlot j r => CPos.atSlot j (r ++ q)
  | [], q, t, off => rfl
  | b :: p, q, t, off => by
      rcases h : cChild exc off t b with ⟨o, t'⟩ | j
      · rw [List.cons_append, walk_cons_internal h, walk_cons_internal h, walk_append exc p q]
      · rw [List.cons_append, walk_cons_slot h, walk_cons_slot h]

/-- A valid child serves at least one slot. -/
lemma one_le_servedK_of_validK {v0 : ℕ} {c : ChildK} (h : validK v0 c) : 1 ≤ servedK c := by
  cases c with
  | slot j => exact le_rfl
  | internal o t =>
      cases t with
      | ord k => simp only [validK, validS] at h; simpa [servedK, servedC] using (by omega : 1 ≤ k)
      | mark a b i =>
          simp only [validK, validS] at h
          simp only [servedK, servedC]
          omega

/-- The slot range of a child of a tagged counter: the left child serves the slots from
`off` to `off + servedK`, the right child the following ones. -/
lemma cChild_range {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) {t : CtrC}
    (ht : validS (0, t)) (off : ℕ) (b : Bool) :
    off ≤ startK (cChild exc off t b) ∧
      startK (cChild exc off t b) + servedK (cChild exc off t b) ≤ off + servedC t ∧
      validK 0 (cChild exc off t b) ∧
      (b = false → startK (cChild exc off t b) = off) ∧
      (b = true → startK (cChild exc off t b) = off + servedK (stepKind exc off (0, t)).1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stepKind_spec hexc 0 off ht
  have h3' : servedK (stepKind exc off (0, t)).1 + servedK (stepKind exc off (0, t)).2
      = servedC t := h3
  cases b
  · simp only [cChild, cond_false]
    exact ⟨h1.ge, by omega, h4, fun _ => h1, fun h => absurd h (by decide)⟩
  · simp only [cChild, cond_true]
    exact ⟨by omega, by omega, h5, fun h => absurd h (by decide), fun _ => h2⟩

/-- **The range of a slot reached by a descent**: a valid counter serving the slots from
`off` on reaches slots in `[off, off + servedC t)` only. -/
lemma walk_atSlot_range {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) :
    ∀ (p : List Bool) {t : CtrC}, validS (0, t) → ∀ {off j : ℕ} {q : List Bool},
      walk exc t off p = CPos.atSlot j q → off ≤ j ∧ j < off + servedC t
  | [], t, _, off, j, q, h => by simp [walk_nil] at h
  | b :: p, t, ht, off, j, q, h => by
      obtain ⟨hr1, hr2, hv, -, -⟩ := cChild_range hexc ht off b
      rcases hc : cChild exc off t b with ⟨o, t'⟩ | j'
      · rw [walk_cons_internal hc] at h
        rw [hc] at hr1 hr2 hv
        simp only [startK, servedK] at hr1 hr2
        have hv' : validS (0, t') := hv
        have := walk_atSlot_range hexc p hv' h
        omega
      · rw [walk_cons_slot hc, CPos.atSlot.injEq] at h
        rw [hc] at hr1 hr2
        simp only [startK, servedK] at hr1 hr2
        omega

/-- A descent reaching a slot lies in the slot range of its first child. -/
lemma walk_cons_atSlot_range {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) {t : CtrC}
    (ht : validS (0, t)) {off : ℕ} {b : Bool} {p : List Bool} {j : ℕ} {q : List Bool}
    (h : walk exc t off (b :: p) = CPos.atSlot j q) :
    startK (cChild exc off t b) ≤ j ∧
      j < startK (cChild exc off t b) + servedK (cChild exc off t b) := by
  obtain ⟨-, -, hv, -, -⟩ := cChild_range hexc ht off b
  rcases hc : cChild exc off t b with ⟨o, t'⟩ | j'
  · rw [walk_cons_internal hc] at h
    rw [hc] at hv
    have := walk_atSlot_range hexc p hv h
    simpa [startK, servedK] using this
  · rw [walk_cons_slot hc, CPos.atSlot.injEq] at h
    simp only [startK, servedK]
    omega

/-- **The path to a slot is unique.** -/
lemma walk_atSlot_unique {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) :
    ∀ (p p' : List Bool) {t : CtrC}, validS (0, t) → ∀ {off j : ℕ},
      walk exc t off p = CPos.atSlot j [] → walk exc t off p' = CPos.atSlot j [] → p = p'
  | [], _, t, _, off, j, h, _ => by simp [walk_nil] at h
  | _ :: _, [], t, _, off, j, _, h' => by simp [walk_nil] at h'
  | b :: p, b' :: p', t, ht, off, j, h, h' => by
      obtain ⟨-, -, hv, hl, hr⟩ := cChild_range hexc ht off b
      obtain ⟨-, -, hv', hl', hr'⟩ := cChild_range hexc ht off b'
      by_cases hb : b = b'
      · subst hb
        rcases hc : cChild exc off t b with ⟨o, t'⟩ | j'
        · rw [walk_cons_internal hc] at h h'
          rw [hc] at hv
          rw [walk_atSlot_unique hexc p p' hv h h']
        · rw [walk_cons_slot hc, CPos.atSlot.injEq] at h h'
          rw [h.2, h'.2]
      · exfalso
        have h1 := walk_cons_atSlot_range hexc ht h
        have h2 := walk_cons_atSlot_range hexc ht h'
        obtain ⟨s1, s2, s3, s4, s5⟩ := stepKind_spec hexc 0 off ht
        cases b <;> cases b' <;> simp at hb
        · have e1 := hl rfl
          have e2 := hr' rfl
          simp only [cChild, cond_false, cond_true] at h1 h2 e1 e2
          omega
        · have e1 := hr rfl
          have e2 := hl' rfl
          simp only [cChild, cond_false, cond_true] at h1 h2 e1 e2
          omega

/-- **The path to a slot**, with a fuel: descend into the child whose slot range
contains the slot. -/
def slotPathF (exc : ℕ → Option (ℕ × ℕ)) : ℕ → CtrC → ℕ → ℕ → List Bool
  | 0, _, _, _ => []
  | d + 1, t, off, j =>
      if j < startK (stepKind exc off (0, t)).2 then
        match (stepKind exc off (0, t)).1 with
        | ChildK.slot _ => [false]
        | ChildK.internal o t' => false :: slotPathF exc d t' o j
      else
        match (stepKind exc off (0, t)).2 with
        | ChildK.slot _ => [true]
        | ChildK.internal o t' => true :: slotPathF exc d t' o j

lemma slotPathF_length_le (exc : ℕ → Option (ℕ × ℕ)) :
    ∀ (d : ℕ) (t : CtrC) (off j : ℕ), (slotPathF exc d t off j).length ≤ d
  | 0, _, _, _ => le_rfl
  | d + 1, t, off, j => by
      simp only [slotPathF]
      split_ifs
      · rcases (stepKind exc off (0, t)).1 with ⟨o, t'⟩ | _
        · simp only [List.length_cons]
          exact Nat.succ_le_succ (slotPathF_length_le exc d t' o j)
        · simp
      · rcases (stepKind exc off (0, t)).2 with ⟨o, t'⟩ | _
        · simp only [List.length_cons]
          exact Nat.succ_le_succ (slotPathF_length_le exc d t' o j)
        · simp

lemma slotPathF_ne_nil (exc : ℕ → Option (ℕ × ℕ)) (d : ℕ) (t : CtrC) (off j : ℕ) :
    slotPathF exc (d + 1) t off j ≠ [] := by
  simp only [slotPathF]
  split_ifs
  · rcases (stepKind exc off (0, t)).1 with ⟨o, t'⟩ | _ <;> simp
  · rcases (stepKind exc off (0, t)).2 with ⟨o, t'⟩ | _ <;> simp

/-- **The path to a slot reaches it**, once the fuel is at least the number of slots
served: every internal vertex serves strictly fewer slots than its parent. -/
lemma walk_slotPathF {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) :
    ∀ (d : ℕ) {t : CtrC}, validS (0, t) → servedC t ≤ d → ∀ {off j : ℕ},
      off ≤ j → j < off + servedC t → walk exc t off (slotPathF exc d t off j) = CPos.atSlot j []
  | 0, t, ht, hd, off, j, h1, h2 => by
      exfalso
      cases t with
      | ord k => simp only [validS] at ht; simp only [servedC] at hd; omega
      | mark a b i => simp only [validS] at ht; simp only [servedC] at hd; omega
  | d + 1, t, ht, hd, off, j, h1, h2 => by
      obtain ⟨s1, s2, s3, s4, s5⟩ := stepKind_spec hexc 0 off ht
      have hL := one_le_servedK_of_validK s4
      have hR := one_le_servedK_of_validK s5
      replace s3 : servedK (stepKind exc off (0, t)).1 + servedK (stepKind exc off (0, t)).2
        = servedC t := s3
      have hcl : cChild exc off t false = (stepKind exc off (0, t)).1 := rfl
      have hcr : cChild exc off t true = (stepKind exc off (0, t)).2 := rfl
      simp only [slotPathF]
      rcases hst : stepKind exc off (0, t) with ⟨c1, c2⟩
      rw [hst] at s1 s2 s3 s4 s5 hL hR hcl hcr
      simp only at s1 s2 s3 s4 s5 hL hR hcl hcr ⊢
      split_ifs with hj
      · rcases c1 with ⟨o, t'⟩ | j'
        · rw [walk_cons_internal hcl]
          have e1 : startK (ChildK.internal o t') = o := rfl
          have e2 : servedK (ChildK.internal o t') = servedC t' := rfl
          have e3 : validS (0, t') := s4
          rw [e1] at s1
          rw [e2] at s2 s3
          exact walk_slotPathF hexc d e3 (by omega) (by omega) (by omega)
        · rw [walk_cons_slot hcl]
          have e1 : startK (ChildK.slot j') = j' := rfl
          have e2 : servedK (ChildK.slot j') = 1 := rfl
          rw [e1] at s1
          rw [e2] at s2
          congr 1
          omega
      · rcases c2 with ⟨o, t'⟩ | j'
        · rw [walk_cons_internal hcr]
          have e1 : startK (ChildK.internal o t') = o := rfl
          have e2 : servedK (ChildK.internal o t') = servedC t' := rfl
          have e3 : validS (0, t') := s5
          rw [e1] at s2 hj
          rw [e2] at s3
          exact walk_slotPathF hexc d e3 (by omega) (by omega) (by omega)
        · rw [walk_cons_slot hcr]
          have e1 : startK (ChildK.slot j') = j' := rfl
          have e2 : servedK (ChildK.slot j') = 1 := rfl
          rw [e1] at s2 hj
          rw [e2] at s3
          congr 1
          omega

/-- A descent stays inside valid counters serving no more slots than the root, within
the root's slot range. -/
lemma walk_inside_valid {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) :
    ∀ (p : List Bool) {t₀ : CtrC}, validS (0, t₀) → ∀ {off : ℕ} {t : CtrC} {o : ℕ},
      walk exc t₀ off p = CPos.inside t o →
        validS (0, t) ∧ off ≤ o ∧ o + servedC t ≤ off + servedC t₀
  | [], t₀, ht, off, t, o, h => by
      rw [walk_nil, CPos.inside.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ht, le_rfl, le_rfl⟩
  | b :: p, t₀, ht, off, t, o, h => by
      obtain ⟨hr1, hr2, hv, -, -⟩ := cChild_range hexc ht off b
      rcases hc : cChild exc off t₀ b with ⟨o', t'⟩ | j'
      · rw [walk_cons_internal hc] at h
        rw [hc] at hr1 hr2 hv
        have e1 : startK (ChildK.internal o' t') = o' := rfl
        have e2 : servedK (ChildK.internal o' t') = servedC t' := rfl
        rw [e1] at hr1 hr2
        rw [e2] at hr2
        have hv' : validS (0, t') := hv
        obtain ⟨h1, h2, h3⟩ := walk_inside_valid hexc p hv' h
        exact ⟨h1, by omega, by omega⟩
      · rw [walk_cons_slot hc] at h
        cases h

/-! ### The engine's encoding as a `CascadeEnc` -/

/-- **The slot word of the `j`-th child of `u`**: the path through the cascade of `u`
to its `j`-th slot. -/
def engineSlot (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ) (u : GWord N)
    (j : ℕ) : List Bool :=
  slotPathF exc L (CtrC.ord (ar u)) 0 j

/-- The encoding of a skeleton address below a prefix: one slot word per letter. -/
def engineEncAux (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ) :
    GWord N → GWord N → List Bool
  | _, [] => []
  | p, i :: rest => engineSlot exc L ar p (i : ℕ) ++ engineEncAux exc L ar (p ++ [i]) rest

lemma engineEncAux_append (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ) :
    ∀ (u v p : GWord N), engineEncAux exc L ar p (u ++ v)
      = engineEncAux exc L ar p u ++ engineEncAux exc L ar (p ++ u) v
  | [], v, p => by simp [engineEncAux]
  | i :: u, v, p => by
      simp only [List.cons_append, engineEncAux, List.append_assoc]
      rw [engineEncAux_append exc L ar u v (p ++ [i])]
      simp

/-- **The encoding of a skeleton address**: the concatenation of the slot words along
the address. -/
def engineEncWord (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ) (u : GWord N) :
    List Bool :=
  engineEncAux exc L ar [] u

@[simp] lemma engineEncWord_nil (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ) :
    engineEncWord exc L ar [] = [] := rfl

lemma engineEncWord_concat (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ)
    (u : GWord N) (i : Fin N) :
    engineEncWord exc L ar (u ++ [i]) = engineEncWord exc L ar u ++ engineSlot exc L ar u (i : ℕ) := by
  rw [engineEncWord, engineEncWord, engineEncAux_append]
  simp [engineEncAux]

/-- The arity field admits the encoding: every nonzero arity lies in `{2, …, L}`. -/
def ArityBounded (L : ℕ) (ar : GWord N → ℕ) : Prop := ∀ u, ar u ≠ 0 → 2 ≤ ar u ∧ ar u ≤ L

/-- The root of a cascade of a bounded nonzero arity is a valid state. -/
lemma validS_of_arityBounded {L : ℕ} {ar : GWord N → ℕ} (har : ArityBounded L ar) {u : GWord N}
    (hu : ar u ≠ 0) : validS (0, CtrC.ord (ar u)) :=
  (har u hu).1

/-- **The slot word reaches its slot.** -/
lemma walk_engineSlot {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) {L : ℕ}
    {ar : GWord N → ℕ} (har : ArityBounded L ar) {u : GWord N} {j : ℕ} (hj : j < ar u) :
    walk exc (CtrC.ord (ar u)) 0 (engineSlot exc L ar u j) = CPos.atSlot j [] := by
  obtain ⟨h2, hL⟩ := har u (by omega)
  exact walk_slotPathF hexc L (t := CtrC.ord (ar u)) h2 hL (Nat.zero_le j) (by simpa [servedC])

/-- **The engine's encoding as a `CascadeEnc`** (`thm:hairy-general`): the slot of a
child is its path through the cascade, of length at most the bound on the arities. -/
def engineEnc (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ) (hexc : ExcCompat exc)
    (har : ArityBounded L ar) : CascadeEnc N L where
  k := ar
  enc := engineEncWord exc L ar
  slot := engineSlot exc L ar
  enc_nil := rfl
  enc_concat := engineEncWord_concat exc L ar
  slot_ne_nil := fun u i hi => by
    obtain ⟨h2, hL⟩ := har u (by omega)
    cases L with
    | zero => omega
    | succ L' => exact slotPathF_ne_nil exc L' _ 0 i
  slot_length_le := fun u i _ => slotPathF_length_le exc L _ 0 i
  slot_prefix := fun u i j hi hj hp => by
    have hi' := walk_engineSlot hexc har hi
    have hj' := walk_engineSlot hexc har hj
    obtain ⟨q, hq⟩ := hp
    rw [← hq, walk_append, hi'] at hj'
    simp only [List.nil_append, CPos.atSlot.injEq] at hj'
    exact hj'.1

@[simp] lemma engineEnc_k (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ)
    (hexc : ExcCompat exc) (har : ArityBounded L ar) : (engineEnc exc L ar hexc har).k = ar := rfl

@[simp] lemma engineEnc_enc (exc : ℕ → Option (ℕ × ℕ)) (L : ℕ) (ar : GWord N → ℕ)
    (hexc : ExcCompat exc) (har : ArityBounded L ar) :
    (engineEnc exc L ar hexc har).enc = engineEncWord exc L ar := rfl

/-! ### Reading the encoded label field -/

/-- A full labelling of the engine read as a full labelling of `GraphMatching`; the two
types are the same recursion. -/
def labOfK {V : Type} : (n : ℕ) → FullLab V n → GraphMatching.FullLab V n
  | 0, x => x
  | n + 1, x => (x.1, labOfK n x.2.1, labOfK n x.2.2)

/-- **The label of a full labelling at a binary address**, junk beyond the depth. -/
def labelAt {V : Type} (n : ℕ) (X : FullLab V n) (w : List Bool) : V :=
  GraphMatching.coord n (labOfK n X) w

/-- **The encoded label field below a cascade vertex, read along a path**: the state at
the end of the descent from the vertex of state `s` working at `u` and `off`. -/
def encAt (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N → ℕ) (v0 : ℕ) :
    GWord N → ℕ → CState ℕ → List Bool → CState ℕ
  | _, _, s, [] => s
  | u, off, s, b :: p =>
      encAt exc lab ar v0 (childAddr u (cChild exc off s.2 b)).1
        (childAddr u (cChild exc off s.2 b)).2 (childState lab ar v0 u (cChild exc off s.2 b)) p

lemma encAt_nil (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N → ℕ) (v0 : ℕ) (u : GWord N)
    (off : ℕ) (s : CState ℕ) : encAt exc lab ar v0 u off s [] = s := rfl

lemma encAt_cons (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N → ℕ) (v0 : ℕ) (u : GWord N)
    (off : ℕ) (s : CState ℕ) (b : Bool) (p : List Bool) :
    encAt exc lab ar v0 u off s (b :: p)
      = encAt exc lab ar v0 (childAddr u (cChild exc off s.2 b)).1
        (childAddr u (cChild exc off s.2 b)).2 (childState lab ar v0 u (cChild exc off s.2 b)) p :=
  rfl

/-- **Reading the encoding**: the label of the height-`n` encoding at an address of
length at most `n` is the state the descent reaches. -/
lemma labelAt_encSub (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N → ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (p : List Bool), p.length ≤ n → ∀ (u : GWord N) (off : ℕ) (s : CState ℕ),
      labelAt n (encSub exc lab ar v0 n u off s) p = encAt exc lab ar v0 u off s p
  | 0, [], _, u, off, s => rfl
  | 0, _ :: _, h, _, _, _ => by simp at h
  | _ + 1, [], _, u, off, s => rfl
  | n + 1, b :: p, h, u, off, s => by
      have hp : p.length ≤ n := by simpa using h
      rw [encAt_cons]
      cases b
      · have e : cChild exc off s.2 false = (stepKind exc off s).1 := by
          rw [cChild, cond_false, ← stepKind_eq_zero]
        rw [e]
        exact labelAt_encSub exc lab ar v0 n p hp _ _ _
      · have e : cChild exc off s.2 true = (stepKind exc off s).2 := by
          rw [cChild, cond_true, ← stepKind_eq_zero]
        rw [e]
        exact labelAt_encSub exc lab ar v0 n p hp _ _ _

/-- **The encoded label field on `𝔹`**: the descent from the root. -/
def encField (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N → ℕ) (v0 : ℕ) (w : List Bool) :
    CState ℕ :=
  encAt exc lab ar v0 [] 0 (lab [], CtrC.ord (ar [])) w

lemma labelAt_encLab (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N → ℕ) (v0 : ℕ) {n : ℕ}
    {w : List Bool} (hw : w.length ≤ n) :
    labelAt n (encLab exc lab ar v0 n) w = encField exc lab ar v0 w :=
  labelAt_encSub exc lab ar v0 n w hw [] 0 _

/-- A descent ending inside the cascade reads the state `(v₀, t)` of the internal vertex. -/
lemma encAt_of_walk_inside (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N → ℕ) (v0 : ℕ) :
    ∀ (p : List Bool) (u : GWord N) (off : ℕ) (s : CState ℕ) {t : CtrC} {o : ℕ},
      walk exc s.2 off p = CPos.inside t o → p ≠ [] → encAt exc lab ar v0 u off s p = (v0, t)
  | [], _, _, _, _, _, _, hne => absurd rfl hne
  | b :: p, u, off, s, t, o, h, _ => by
      rw [encAt_cons]
      rcases hc : cChild exc off s.2 b with ⟨o', t'⟩ | j
      · rw [walk_cons_internal hc] at h
        simp only [childAddr, childState]
        rcases p with _ | ⟨b', p⟩
        · rw [walk_nil, CPos.inside.injEq] at h
          rw [encAt_nil, h.1]
        · exact encAt_of_walk_inside exc lab ar v0 (b' :: p) u o' (v0, t') h (by simp)
      · rw [walk_cons_slot hc] at h
        cases h

/-- A descent through a slot continues in the cascade of the skeleton child there. -/
lemma encAt_of_walk_atSlot (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N → ℕ) (v0 : ℕ) :
    ∀ (p : List Bool) (u : GWord N) (off : ℕ) (s : CState ℕ) {j : ℕ} {q : List Bool},
      walk exc s.2 off p = CPos.atSlot j q →
        encAt exc lab ar v0 u off s p
          = encAt exc lab ar v0 (gChild u j) 0 (lab (gChild u j), CtrC.ord (ar (gChild u j))) q
  | [], _, _, _, _, _, h => by simp [walk_nil] at h
  | b :: p, u, off, s, j, q, h => by
      rw [encAt_cons]
      rcases hc : cChild exc off s.2 b with ⟨o', t'⟩ | j'
      · rw [walk_cons_internal hc] at h
        exact encAt_of_walk_atSlot exc lab ar v0 p u o' (v0, t') h
      · rw [walk_cons_slot hc, CPos.atSlot.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl

/-- The arity field is bounded on the skeleton: the hypothesis the reading uses. -/
def SkelBounded (L : ℕ) (ar : GWord N → ℕ) : Prop :=
  ∀ u, u ∈ sample ar → 2 ≤ ar u ∧ ar u ≤ L

lemma arityBounded_of_skelBounded {L : ℕ} {ar : GWord N → ℕ} (hs : SkelBounded L ar)
    (hoff : ∀ u, u ∉ sample ar → ar u = 0) : ArityBounded L ar := by
  intro u hu
  by_cases h : u ∈ sample ar
  · exact hs u h
  · exact absurd (hoff u h) hu

/-- **The descent from the root reaches the cascade of a skeleton vertex at its
encoding**, and continues from there. -/
lemma encAt_nil_enc {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) {L : ℕ}
    (lab : GWord N → ℕ) {ar : GWord N → ℕ} (har : ArityBounded L ar) (v0 : ℕ) :
    ∀ (u : GWord N), u ∈ sample ar → ∀ (q : List Bool),
      encAt exc lab ar v0 [] 0 (lab [], CtrC.ord (ar [])) (engineEncWord exc L ar u ++ q)
        = encAt exc lab ar v0 u 0 (lab u, CtrC.ord (ar u)) q := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro _ q; simp
  | append_singleton u i ih =>
      intro hu q
      obtain ⟨hu', hi⟩ := BranchingProcess.mem_sample_append_singleton.mp hu
      rw [engineEncWord_concat, List.append_assoc, ih hu']
      have hw : walk exc (CtrC.ord (ar u)) 0 (engineSlot exc L ar u (i : ℕ) ++ q)
          = CPos.atSlot (i : ℕ) q := by
        simp only [walk_append, walk_engineSlot hexc har hi, List.nil_append]
      rw [encAt_of_walk_atSlot exc lab ar v0 _ u 0 _ hw, gChild_of_lt u i.2]

/-- **The label of a skeleton vertex sits at its encoding.** -/
lemma encField_enc {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) {L : ℕ}
    (lab : GWord N → ℕ) {ar : GWord N → ℕ} (har : ArityBounded L ar) (v0 : ℕ) {u : GWord N}
    (hu : u ∈ sample ar) :
    encField exc lab ar v0 (engineEncWord exc L ar u) = (lab u, CtrC.ord (ar u)) := by
  have h := encAt_nil_enc hexc lab har v0 u hu []
  rw [List.append_nil] at h
  exact h

/-- **Every binary word lies in the cascade of a skeleton vertex**: it is the encoding of
the vertex followed by a path ending inside the cascade. -/
lemma exists_enc_inside {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) {L : ℕ}
    {ar : GWord N → ℕ} (har : ArityBounded L ar) (hs : SkelBounded L ar)
    (harN : ∀ u, ar u ≤ N) (w : List Bool) :
    ∃ u, u ∈ sample ar ∧ ∃ p, w = engineEncWord exc L ar u ++ p ∧
      ∃ t o, walk exc (CtrC.ord (ar u)) 0 p = CPos.inside t o := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨[], BranchingProcess.nil_mem_sample _, [], by simp, _, _, walk_nil _ _ _⟩
  | append_singleton w b ih =>
      obtain ⟨u, hu, p, rfl, t, o, hw⟩ := ih
      have hv : validS (0, CtrC.ord (ar u)) := (hs u hu).1
      obtain ⟨hvt, -, -⟩ := walk_inside_valid hexc p hv hw
      rcases hc : cChild exc o t b with ⟨o', t'⟩ | j
      · refine ⟨u, hu, p ++ [b], by rw [List.append_assoc], t', o', ?_⟩
        simp only [walk_append, hw, walk_cons_internal hc, walk_nil]
      · have hslot : walk exc (CtrC.ord (ar u)) 0 (p ++ [b]) = CPos.atSlot j [] := by
          simp only [walk_append, hw, walk_cons_slot hc]
        have hj : j < ar u := by
          have := walk_atSlot_range hexc (p ++ [b]) hv hslot
          change 0 ≤ j ∧ j < 0 + ar u at this
          omega
        have hjN : j < N := lt_of_lt_of_le hj (harN u)
        have huj : u ++ [⟨j, hjN⟩] ∈ sample ar :=
          BranchingProcess.mem_sample_append_singleton.mpr ⟨hu, hj⟩
        refine ⟨u ++ [⟨j, hjN⟩], huj, [], ?_, _, _, walk_nil _ _ _⟩
        rw [List.append_nil, List.append_assoc, engineEncWord_concat]
        congr 1
        exact walk_atSlot_unique hexc _ _ hv hslot (walk_engineSlot hexc har hj)

/-- **Off the encoded skeleton the label is `v₀`**: an internal cascade vertex carries
the state of the one-vertex shape. -/
lemma encField_of_not_image {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) {L : ℕ}
    (lab : GWord N → ℕ) {ar : GWord N → ℕ} (har : ArityBounded L ar) (hs : SkelBounded L ar)
    (harN : ∀ u, ar u ≤ N) (v0 : ℕ) {w : List Bool}
    (hw : ¬ ∃ u, u ∈ sample ar ∧ w = engineEncWord exc L ar u) :
    (encField exc lab ar v0 w).1 = v0 := by
  obtain ⟨u, hu, p, rfl, t, o, hwalk⟩ := exists_enc_inside hexc har hs harN w
  rcases p with _ | ⟨b, p⟩
  · exact absurd ⟨u, hu, by simp⟩ hw
  · rw [encField, encAt_nil_enc hexc lab har v0 u hu,
      encAt_of_walk_inside exc lab ar v0 (b :: p) u 0 _ hwalk (by simp)]

/-- **The prefix closure of the encoded skeleton is `𝔹`**: every binary word is a prefix
of the encoding of a skeleton vertex. -/
lemma engineEnc_inClosure {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) {L : ℕ}
    {ar : GWord N → ℕ} (har : ArityBounded L ar) (hs : SkelBounded L ar)
    (harN : ∀ u, ar u ≤ N) (w : List Bool) :
    (engineEnc exc L ar hexc har).InClosure (bnat w) := by
  obtain ⟨u, hu, p, rfl, t, o, hwalk⟩ := exists_enc_inside hexc har hs harN w
  have hv : validS (0, CtrC.ord (ar u)) := (hs u hu).1
  obtain ⟨hvt, ho1, ho2⟩ := walk_inside_valid hexc p hv hwalk
  have ht2 : 2 ≤ servedC t := by
    cases t with
    | ord k => simpa [validS, servedC] using hvt
    | mark a b i => simp only [validS] at hvt; simp only [servedC]; omega
  change o + servedC t ≤ 0 + ar u at ho2
  have hL : ar u ≤ L := (hs u hu).2
  -- the slot `o` lies below the internal vertex
  have hpath := walk_slotPathF hexc L hvt (by omega) (le_refl o) (by omega)
  have hslot : walk exc (CtrC.ord (ar u)) 0 (p ++ slotPathF exc L t o o) = CPos.atSlot o [] := by
    simp only [walk_append, hwalk, hpath]
  have hj : o < ar u := by omega
  have hjN : o < N := lt_of_lt_of_le hj (harN u)
  have huj : u ++ [⟨o, hjN⟩] ∈ sample ar :=
    BranchingProcess.mem_sample_append_singleton.mpr ⟨hu, hj⟩
  refine ⟨u ++ [⟨o, hjN⟩], huj, ?_⟩
  rw [bnat_prefix_iff, engineEnc_enc, engineEncWord_concat]
  refine List.prefix_append_right_inj _ |>.mpr ?_
  refine ⟨slotPathF exc L t o o, ?_⟩
  exact walk_atSlot_unique hexc _ _ hv hslot (walk_engineSlot hexc har hj)

/-! ### The portrait of an infinite matching -/

/-- An automorphism of the engine's tower at `k = 1` read as an automorphism of
`GraphMatching`; the two types are the same recursion. -/
def autOfK : (n : ℕ) → AutK 1 0 n → GraphMatching.Aut n
  | 0, _ => ()
  | n + 1, π => (π.1, autOfK n π.2.1, autOfK n π.2.2)

lemma restrictAut_autOfK : ∀ (n : ℕ) (π : AutK 1 0 (n + 1)),
    GraphMatching.restrictAut n (autOfK (n + 1) π) = autOfK n (restrictAutK 1 0 n π)
  | 0, _ => rfl
  | n + 1, π => by
      show (π.1, GraphMatching.restrictAut n (autOfK (n + 1) π.2.1),
          GraphMatching.restrictAut n (autOfK (n + 1) π.2.2))
        = (π.1, autOfK n (restrictAutK 1 0 n π.2.1), autOfK n (restrictAutK 1 0 n π.2.2))
      rw [restrictAut_autOfK n, restrictAut_autOfK n]

lemma labOfK_cond {V : Type} (n : ℕ) (b : Bool) (x y : FullLab V n) :
    labOfK n (bif b then x else y) = bif b then labOfK n x else labOfK n y := by
  cases b <;> rfl

/-- A matching in the engine's tower is a matching of `GraphMatching`. -/
lemma fullMatchesA_of_fullMatchesK {V : Type} (R₀ : V → V → Prop) :
    ∀ (n : ℕ) (π : AutK 1 0 n) (x y : FullLab V n), fullMatchesK R₀ 1 0 n π x y →
      GraphMatching.fullMatchesA R₀ n (autOfK n π) (labOfK n x) (labOfK n y)
  | 0, _, x, y, h => h
  | n + 1, π, x, y, h => by
      obtain ⟨hroot, hl, hr⟩ := h
      refine ⟨hroot, ?_, ?_⟩
      · have := fullMatchesA_of_fullMatchesK R₀ n π.2.1 x.2.1 _ hl
        rwa [labOfK_cond] at this
      · have := fullMatchesA_of_fullMatchesK R₀ n π.2.2 x.2.2 _ hr
        rwa [labOfK_cond] at this

/-- **The portrait of an infinite matching**: a projective family of matching
automorphisms of the engine's tower is a portrait of `𝔹` relating the label at every
vertex `w` to the label at its image `autOf π w`. -/
theorem exists_portrait_of_infMatchK {V : Type} (R₀ : V → V → Prop)
    {X Y : (n : ℕ) → FullLab V n} (hm : InfMatchK R₀ 1 0 X Y) :
    ∃ π : Word → Bool ≃ Bool, ∀ w : Word,
      R₀ (labelAt w.length (X w.length) w) (labelAt w.length (Y w.length) (autOf π w)) := by
  obtain ⟨σ, hproj, hgood⟩ := hm
  set σ' : (n : ℕ) → GraphMatching.Aut n := fun n => autOfK n (σ n) with hσ'
  have hproj' : ∀ n, GraphMatching.restrictAut n (σ' (n + 1)) = σ' n := fun n => by
    simp only [hσ']
    rw [restrictAut_autOfK, hproj]
  refine ⟨portraitOf σ', fun w => ?_⟩
  have hw : w ∈ GraphMatching.Vtx w.length := mem_Vtx_of_length_le _ w le_rfl
  have hkey := rel_coord_autAddr R₀ w.length (σ' w.length) _ _
    (fullMatchesA_of_fullMatchesK R₀ w.length (σ w.length) _ _ (hgood w.length)) w hw
  rw [← autOf_portraitOf hproj' w w.length le_rfl] at hkey
  exact hkey

/-! ### The arity field off the skeleton -/

/-- Membership in the skeleton cut out by an arity field, letter by letter. -/
lemma mem_sample_iff_prefix {k : GWord N → ℕ} (u : GWord N) :
    u ∈ sample k ↔ ∀ (p : GWord N) (i : Fin N), p ++ [i] <+: u → (i : ℕ) < k p := by
  induction u using List.reverseRecOn with
  | nil =>
      simp only [BranchingProcess.nil_mem_sample, true_iff]
      intro p i h
      rw [List.prefix_nil] at h
      exact absurd h (by simp)
  | append_singleton u j ih =>
      rw [BranchingProcess.mem_sample_append_singleton, ih]
      constructor
      · rintro ⟨h1, h2⟩ p i hpi
        rcases List.prefix_concat_iff.mp hpi with h | h
        · obtain ⟨rfl, h'⟩ := List.append_inj' h rfl
          rw [List.singleton_inj] at h'
          rw [h']
          exact h2
        · exact h1 p i h
      · intro h
        exact ⟨fun p i hpi => h p i (hpi.trans (List.prefix_append _ _)),
          h u j (List.prefix_refl _)⟩

lemma skeletonDegree_zero_field : skeletonDegree (fun _ : GWord N => 0) = 0 := by
  rw [BranchingProcess.skeletonDegree, Finset.card_eq_zero, BranchingProcess.survivors,
    Finset.filter_eq_empty_iff]
  intro i _
  simp

/-- Beyond the skeleton degree the bushes are the zero field. -/
lemma bushAt_of_le {d : GWord N → ℕ} {m : ℕ} (h : skeletonDegree d ≤ m) :
    bushAt d m = fun _ => 0 := by
  have h' : ¬ m < (BranchingProcess.survivors d).card := not_lt.mpr h
  rw [bushAt, BranchingProcess.bushOf, dif_neg h']

lemma neckIter_zero_field : ∀ n : ℕ, neckIter (fun _ : GWord N => 0) n = fun _ => 0
  | 0 => rfl
  | n + 1 => by
      rw [neckIter_succ, bushAt_of_le (by rw [skeletonDegree_zero_field])]
      exact neckIter_zero_field n

lemma gArity_zero_field : gArity (fun _ : GWord N => 0) = 0 := by
  rw [gArity, gSplitField, neckIter_zero_field, skeletonDegree_zero_field]

lemma gSplitBush_zero_field (m : ℕ) : gSplitBush (fun _ : GWord N => 0) m = fun _ => 0 := by
  rw [gSplitBush, gSplitField, neckIter_zero_field, bushAt_of_le]
  rw [skeletonDegree_zero_field]
  exact Nat.zero_le m

lemma redSub_zero_field : ∀ u : GWord N, redSub (fun _ : GWord N => 0) u = fun _ => 0
  | [] => rfl
  | i :: u => by rw [redSub_cons, gSplitBush_zero_field]; exact redSub_zero_field u

/-- Beyond the arity the copies are the zero field. -/
lemma gSplitBush_of_le {d : GWord N → ℕ} {m : ℕ} (h : gArity d ≤ m) :
    gSplitBush d m = fun _ => 0 :=
  bushAt_of_le h

lemma redSub_append (c : GWord N → ℕ) : ∀ (u v : GWord N),
    redSub c (u ++ v) = redSub (redSub c u) v
  | [], v => rfl
  | i :: u, v => by rw [List.cons_append, redSub_cons, redSub_cons]; exact redSub_append _ u v

/-- **Off the skeleton the arity field vanishes.** -/
lemma gArityAt_of_not_mem_sample {c : GWord N → ℕ} {u : GWord N}
    (h : u ∉ sample (gArityAt c)) : gArityAt c u = 0 := by
  rw [mem_sample_iff_prefix] at h
  push Not at h
  obtain ⟨p, i, ⟨v, rfl⟩, hi⟩ := h
  rw [gArityAt, redSub_append, redSub_append, redSub_cons, redSub_nil,
    gSplitBush_of_le hi, redSub_zero_field, gArity_zero_field]

/-- The arity field is bounded by the alphabet. -/
lemma gArityAt_le_alphabet (c : GWord N → ℕ) (u : GWord N) : gArityAt c u ≤ N :=
  skeletonDegree_le_alphabet _

/-- On the skeleton of a hairy sample every arity is at least two. -/
lemma two_le_gArityAt_of_isGHairySample {c : GWord N → ℕ} (hc : IsGHairySample c) {u : GWord N}
    (hu : u ∈ sample (gArityAt c)) : 2 ≤ gArityAt c u := by
  obtain ⟨heq, hsurv⟩ := redSub_eq_ambSub_gEntryV' hc hu
  rw [heq] at hsurv
  have := hc.splits _ hsurv
  rw [gArityAt, heq]
  exact two_le_gArity_of_splits this

/-- The skeleton arities of a hairy sample bounded by `L` give a bounded arity field. -/
lemma arityBounded_gArityAt {L : ℕ} {c : GWord N → ℕ} (hs : SkelBounded L (gArityAt c)) :
    ArityBounded L (gArityAt c) :=
  arityBounded_of_skelBounded hs fun _ hu => gArityAt_of_not_mem_sample hu

/-! ### The deterministic core -/

/-- The one-vertex shape has size one. -/
lemma gOne_size : gOne.size = 1 := size_bareNeck 0

/-- The one-vertex shape carries the class `v₀ = 0`. -/
lemma gNetLab_gOne {D : ℝ} (hD : 1 ≤ D) : gNetLab D gOne = 0 :=
  gNetLab_eq_zero_of_size_le hD (by rw [gOne_size]; push_cast; nlinarith)

/-- **The shape over `𝔹` at a vertex reaches a partner carrying its label**: at an
encoded skeleton vertex the partner of the coupling, at an internal cascade vertex the
one-vertex shape itself. -/
lemma exists_partner_bFamily {L : ℕ} {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc)
    {c : GWord N → ℕ} (hs : SkelBounded L (gArityAt c)) {D : ℝ} (hD : 1 ≤ D)
    {lab : GWord N → ℕ} {τ : GWord N → GShape}
    (hlab : ∀ u, u ∈ sample (gArityAt c) → lab u = gNetLab D (τ u))
    (hτ : ∀ u, u ∈ sample (gArityAt c) →
      MarkedQI (9 * D ^ 3) (gShapeSpace (gShapeAt c u)) (gShapeSpace (τ u)))
    (w : Word) :
    ∃ ρ : GShape, MarkedQI (9 * D ^ 3)
        (gShapeSpace ((engineEnc exc L (gArityAt c) hexc (arityBounded_gArityAt hs)).bFamily
          (gShapeAt c) (bnat w)))
        (gShapeSpace ρ) ∧
      gNetLab D ρ = (encField exc lab (gArityAt c) 0 w).1 := by
  set E := engineEnc exc L (gArityAt c) hexc (arityBounded_gArityAt hs) with hE
  have h9 : (1 : ℝ) ≤ 9 * D ^ 3 := by
    have := one_le_pow₀ (n := 3) hD
    nlinarith
  by_cases h : ∃ u, u ∈ sample (gArityAt c) ∧ w = engineEncWord exc L (gArityAt c) u
  · obtain ⟨u, hu, rfl⟩ := h
    refine ⟨τ u, ?_, ?_⟩
    · have hb : E.bFamily (gShapeAt c) (bnat (E.enc u)) = gShapeAt c u :=
        CascadeEnc.bFamily_enc (E := E) hu
      rw [hE, engineEnc_enc] at hb
      rw [hb]
      exact hτ u hu
    · rw [encField_enc hexc lab (arityBounded_gArityAt hs) 0 hu, hlab u hu]
  · refine ⟨gOne, ?_, ?_⟩
    · have hb : E.bFamily (gShapeAt c) (bnat w) = gOne := by
        refine CascadeEnc.bFamily_of_not_isImage ?_
        rintro ⟨u, hu, hw⟩
        exact h ⟨u, hu, bnat_injective hw⟩
      rw [hb]
      exact markedQI_id h9 _
    · rw [gNetLab_gOne hD, encField_of_not_image hexc lab (arityBounded_gArityAt hs) hs
        (gArityAt_le_alphabet c) 0 h]

/-- **The deterministic core of `thm:hairy-general`**: an alignment of the encoded label
fields of two hairy samples to within one class of `G_D`, the labels being the classes
of partners `9D³`-comparable to the shapes, gives a quasi-isometry of the two samples at
the constant `⌈216 L L'² (3·(3¹⁵D¹⁶)²)²⌉`. -/
theorem sample_qi_of_engine_match {L L' : ℕ} {exc exc' : ℕ → Option (ℕ × ℕ)}
    (hexc : ExcCompat exc) (hexc' : ExcCompat exc') {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    (hc : IsGHairySample c) (hc' : IsGHairySample c')
    (hs : SkelBounded L (gArityAt c)) (hs' : SkelBounded L' (gArityAt c'))
    (hL : 1 ≤ L) (hL' : 1 ≤ L') {D : ℝ} (hD : 1 ≤ D)
    {lab : GWord N → ℕ} {lab' : GWord N' → ℕ} {τ : GWord N → GShape} {τ' : GWord N' → GShape}
    (hlab : ∀ u, u ∈ sample (gArityAt c) → lab u = gNetLab D (τ u))
    (hlab' : ∀ u, u ∈ sample (gArityAt c') → lab' u = gNetLab D (τ' u))
    (hτ : ∀ u, u ∈ sample (gArityAt c) →
      MarkedQI (9 * D ^ 3) (gShapeSpace (gShapeAt c u)) (gShapeSpace (τ u)))
    (hτ' : ∀ u, u ∈ sample (gArityAt c') →
      MarkedQI (9 * D ^ 3) (gShapeSpace (gShapeAt c' u)) (gShapeSpace (τ' u)))
    (hm : InfMatchK (cRel (GraphMatching.compat (gNetGraph D))) 1 0
      (fun n => encLab exc lab (gArityAt c) 0 n) (fun n => encLab exc' lab' (gArityAt c') 0 n)) :
    ∃ F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'},
      BranchingProcess.IsQIWith ⌈216 * L * L' ^ 2 * (3 * (14348907 * D ^ 16) ^ 2) ^ 2⌉₊
        (wordGraphN (· ∈ sample c)) (wordGraphN (· ∈ sample c')) F := by
  obtain ⟨π, hπ⟩ := exists_portrait_of_infMatchK _ hm
  set E := engineEnc exc L (gArityAt c) hexc (arityBounded_gArityAt hs) with hE
  set E' := engineEnc exc' L' (gArityAt c') hexc' (arityBounded_gArityAt hs') with hE'
  have hC : (1 : ℝ) ≤ 14348907 * D ^ 16 := by
    have := one_le_pow₀ (n := 16) hD
    nlinarith
  have hK : (1 : ℝ) ≤ 3 * (14348907 * D ^ 16) ^ 2 := by nlinarith
  refine sample_qi_of_bShape_matching hc hc' E E' rfl rfl hL hL' hK π (fun w => ?_) (fun w => ?_)
  · exact ⟨fun _ => engineEnc_inClosure hexc' _ hs' (gArityAt_le_alphabet c') _,
      fun _ => engineEnc_inClosure hexc _ hs (gArityAt_le_alphabet c) _⟩
  · obtain ⟨ρ, hρ, hρl⟩ := exists_partner_bFamily hexc hs hD hlab hτ w
    obtain ⟨ρ', hρ', hρl'⟩ := exists_partner_bFamily hexc' hs' hD hlab' hτ' (autOf π w)
    have hrel := hπ w
    rw [labelAt_encLab _ _ _ _ le_rfl, labelAt_encLab _ _ _ _ (by rw [autOf_length])] at hrel
    have hcompat : gNetLab D ρ = gNetLab D ρ' ∨ (gNetGraph D).Adj (gNetLab D ρ) (gNetLab D ρ') := by
      rw [hρl, hρl']
      exact hrel
    rcases crossRelabel_qi_compat hD hρ hρ' hcompat with h | h
    · exact h.mono (by positivity) (by nlinarith)
    · exact markedQI_symm hC h

/-! ### The almost sure events -/

section AlmostSure

variable {J J' : ℕ}

/-- **The shift to a subtree preserves the sample law.** -/
lemma map_ambSub (θ : Offspring J) : ∀ v : GWord N,
    (BranchingProcess.sampleMeasure (N := N) θ).map (fun c => ambSub c v)
      = BranchingProcess.sampleMeasure (N := N) θ
  | [] => by
      have h : (fun c : GWord N → ℕ => ambSub c []) = id := by
        funext c
        exact ambSub_nil c
      rw [h, Measure.map_id]
  | i :: v => by
      have h : (fun c : GWord N → ℕ => ambSub c (i :: v))
          = (fun c => ambSub c v) ∘ (fun c w => c (i :: w)) := by
        funext c w
        rfl
      rw [h, ← Measure.map_map (measurable_ambSub v) (BranchingProcess.measurable_shift i),
        BranchingProcess.map_shift, map_ambSub θ v]

/-- A null event of the conditioned law is null at every surviving subtree. -/
lemma survivalMeasure_ambSub_null (θ : Offspring J) {S : Set (GWord N → ℕ)}
    (hS : survivalMeasure (N := N) θ S = 0) (v : GWord N) :
    survivalMeasure (N := N) θ {c | Survives (ambSub c v) ∧ ambSub c v ∈ S} = 0 := by
  have hP : BranchingProcess.sampleMeasure (N := N) θ ({c | Survives c} ∩ S) = 0 := by
    rw [BranchingProcess.survivalMeasure_apply] at hS
    rcases mul_eq_zero.mp hS with h | h
    · exact absurd h (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    · exact h
  have hP' : BranchingProcess.sampleMeasure (N := N) θ
      {c | Survives (ambSub c v) ∧ ambSub c v ∈ S} = 0 := by
    refine le_antisymm ?_ bot_le
    calc BranchingProcess.sampleMeasure (N := N) θ {c | Survives (ambSub c v) ∧ ambSub c v ∈ S}
        = BranchingProcess.sampleMeasure (N := N) θ
            ((fun c => ambSub c v) ⁻¹' ({c | Survives c} ∩ S)) := rfl
      _ ≤ (BranchingProcess.sampleMeasure (N := N) θ).map (fun c => ambSub c v)
            ({c | Survives c} ∩ S) :=
          Measure.le_map_apply (measurable_ambSub v).aemeasurable _
      _ = 0 := by rw [map_ambSub, hP]
  exact ProbabilityTheory.cond_absolutelyContinuous hP'

/-- **A conditioned sample is hairy almost surely**: its offspring counts lie within the
alphabet, it survives, and every neck ray below a surviving vertex meets a split. -/
theorem ae_isGHairySample (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, IsGHairySample c := by
  have h1 : ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v, c v ≤ N := by
    refine ae_all_iff.mpr fun v => ?_
    rw [ae_iff]
    have := BranchingProcess.survivalMeasure_coord_gt θ hJN v
    simpa [not_le] using this
  have h2 := ae_survives θ hJN hq
  have hsplit : survivalMeasure (N := N) θ {d | ¬ ∃ n, 2 ≤ skeletonDegree (neckIter d n)} = 0 := by
    refine measure_mono_null (fun d hd => ?_) (ae_iff.mp (ae_gArity_ge_two θ hJN hq hs1))
    simp only [Set.mem_setOf_eq, not_exists, not_le] at hd ⊢
    by_contra h2
    obtain ⟨n, hn⟩ := splitSet_nonempty_of_arity (not_lt.mp h2)
    exact absurd hn (not_le.mpr (hd n))
  have h3 : ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v, Survives (ambSub c v) →
      ∃ n, 2 ≤ skeletonDegree (neckIter (ambSub c v) n) := by
    refine ae_all_iff.mpr fun v => ?_
    rw [ae_iff]
    have := survivalMeasure_ambSub_null θ hsplit v
    simpa [Set.mem_setOf_eq, Classical.not_imp] using this
  filter_upwards [h1, h2, h3] with c hc1 hc2 hc3
  exact ⟨hc1, hc2, hc3⟩

/-- Compatibility with a sample is membership in the reduced skeleton. -/
lemma gCompat_iff_mem_sample (c : GWord N → ℕ) (w : GWord N) :
    GCompat c w ↔ w ∈ sample (gArityAt c) := by
  rw [gCompat_iff, mem_sample_iff_prefix]

/-- **The skeleton is well formed almost surely**: every arity lies in `{2, …, J'}` and
every shape has positive conditional mass at its arity. -/
theorem ae_skeleton_good (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J') :
    ∀ᵐ c ∂survivalMeasure (N := N') θ', ∀ u, u ∈ sample (gArityAt c) →
      (2 ≤ gArityAt c u ∧ gArityAt c u ≤ J') ∧
        gCondMass (N := N') θ' (gArityAt c u) (gShapeAt c u) ≠ 0 := by
  have hs1' : θ'.skeletonWeight 1 < 1 := skeletonWeight_one_lt_one_of θ' hq' hq0' hJ2' hθJ'
  refine ae_all_iff.mpr fun u => ?_
  rw [ae_iff]
  -- the probe: the prefixes of `u`
  set F : Finset (GWord N') := u.inits.toFinset with hF
  have hmemF : ∀ p, p ∈ F ↔ p <+: u := fun p => by
    rw [hF, List.mem_toFinset, List.mem_inits]
  have huF : u ∈ F := (hmemF u).mpr (List.prefix_refl u)
  have hpc : ∀ p ∈ F, ∀ q : GWord N', q <+: p → q ∈ F := fun p hp q hq =>
    (hmemF q).mpr (hq.trans ((hmemF p).mp hp))
  -- the patterns of shapes and arities over the probe
  let ext : (↥F → GShape × ℕ) → (GWord N' → GShape) × (GWord N' → ℕ) := fun g =>
    (fun p => if h : p ∈ F then (g ⟨p, h⟩).1 else gOne,
      fun p => if h : p ∈ F then (g ⟨p, h⟩).2 else 0)
  let Good : (↥F → GShape × ℕ) → Prop := fun g =>
    (∀ p : ↥F, 2 ≤ (g p).2 ∧ (g p).2 ≤ J') ∧
      (∀ (p : ↥F) (i : Fin N'), (p : GWord N') ++ [i] ∈ F → (i : ℕ) < (g p).2) ∧
      gCondMass (N := N') θ' (g ⟨u, huF⟩).2 (g ⟨u, huF⟩).1 = 0
  let A : (↥F → GShape × ℕ) → Set (GWord N' → ℕ) := fun g =>
    ⋂ p ∈ F, ({c : GWord N' → ℕ | gShapeAt c p = (ext g).1 p}
      ∩ {c : GWord N' → ℕ | gArityAt c p = (ext g).2 p})
  have hA : ∀ g, Good g → survivalMeasure (N := N') θ' (A g) = 0 := by
    intro g hg
    have hext1 : ∀ p : ↥F, (ext g).1 p = (g p).1 := fun p => by
      simp only [ext, dif_pos p.2]
    have hext2 : ∀ p : ↥F, (ext g).2 p = (g p).2 := fun p => by
      simp only [ext, dif_pos p.2]
    rw [conditional_iid θ' hJN' hq' hq0' hJ2' hθJ' F hpc (ext g).1 (ext g).2
      (fun p hp => by rw [hext2 ⟨p, hp⟩]; exact (hg.1 ⟨p, hp⟩).1)
      (fun p hp => by rw [hext2 ⟨p, hp⟩]; exact (hg.1 ⟨p, hp⟩).2)
      (fun p hp i hpi => by rw [hext2 ⟨p, hp⟩]; exact hg.2.1 ⟨p, hp⟩ i hpi)]
    rw [Finset.prod_eq_zero huF, zero_mul]
    rw [hext1 ⟨u, huF⟩, hext2 ⟨u, huF⟩]
    exact hg.2.2
  have hN1 : survivalMeasure (N := N') θ' (⋃ p ∈ F, {c : GWord N' → ℕ |
      GCompat c p ∧ ¬ (2 ≤ gArityAt c p ∧ gArityAt c p ≤ J')}) = 0 :=
    measure_biUnion_null_iff F.countable_toSet |>.mpr fun p _ =>
      survivalMeasure_compat_bad_null θ' hJN' hq' hs1' hJ2' p
  have hN2 : survivalMeasure (N := N') θ' (⋃ (g : ↥F → GShape × ℕ) (_ : Good g), A g) = 0 :=
    measure_iUnion_null fun g => measure_iUnion_null fun hg => hA g hg
  refine measure_mono_null (fun c hc => ?_) (measure_union_null hN1 hN2)
  simp only [Set.mem_setOf_eq, Classical.not_imp] at hc
  obtain ⟨hu, hbad⟩ := hc
  rw [not_and, not_not] at hbad
  by_cases hrange : ∀ p ∈ F, 2 ≤ gArityAt c p ∧ gArityAt c p ≤ J'
  · right
    refine Set.mem_iUnion.mpr ⟨fun p => (gShapeAt c p, gArityAt c p), Set.mem_iUnion.mpr
      ⟨⟨fun p => hrange p p.2, fun p i hpi => ?_, hbad (hrange u huF)⟩, ?_⟩⟩
    · have := (mem_sample_iff_prefix u).mp hu p i ((hmemF _).mp hpi)
      exact this
    · simp only [A, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, ext]
      intro p hp
      simp only [dif_pos hp, and_self]
  · left
    push Not at hrange
    obtain ⟨p, hp, hpbad⟩ := hrange
    refine Set.mem_biUnion hp ⟨?_, fun h => absurd (hpbad h.1) (not_lt.mpr h.2)⟩
    rw [gCompat_iff_mem_sample]
    exact BranchingProcess.Subtree.mem_of_prefix ((hmemF p).mp hp) hu

/-- **The uniform field lies in `[0,1)` at every index almost surely.** -/
lemma ae_uniform_mem_Ico (ι : Type*) [Countable ι] :
    ∀ᵐ U ∂uniformField ι, ∀ u, U u ∈ Set.Ico (0 : ℝ) 1 := by
  refine ae_all_iff.mpr fun u => ?_
  rw [ae_iff]
  have h : {U : ι → ℝ | ¬ U u ∈ Set.Ico (0 : ℝ) 1}
      = (BranchingProcess.coord u : (ι → ℝ) → ℝ) ⁻¹' (Set.Ico (0 : ℝ) 1)ᶜ := rfl
  rw [h, uniformField, BranchingProcess.coord_law _ u measurableSet_Ico.compl,
    Measure.restrict_apply measurableSet_Ico.compl, Set.compl_inter_self, measure_empty]

/-- The draw of an atom by a uniform variable in `[0,1)` lands in the support. -/
lemma drawBy_ne_zero {T : Type*} [Encodable T] (ν : PMF T) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) : ν (drawBy ν r) ≠ 0 := by
  have h := (drawBy_eq_iff ν hr (drawBy ν r)).mp rfl
  have h2 := (drawNat_eq_iff (tsum_encMass ν) hr).mp h
  rw [cumMass_succ (tsum_encMass ν), encMass_encode] at h2
  intro h0
  rw [h0, ENNReal.toReal_zero, add_zero] at h2
  exact absurd h2.2 (not_lt.mpr h2.1)

/-- The conditional draw by a uniform variable in `[0,1)` lands in the support of the
coupling, once the condition carries mass. -/
lemma condDraw_ne_zero {T : Type*} [Encodable T] (π : PMF (T × T)) {σ : T}
    (h : margFstT π σ ≠ 0) {r : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) :
    π (σ, condDraw π σ r) ≠ 0 := by
  rw [condDraw, dif_pos h]
  have := drawBy_ne_zero (condPMF π σ h) hr
  rw [condPMF_apply] at this
  intro h0
  apply this
  rw [h0, ENNReal.zero_div]

/-- **Every partner is comparable to its shape almost surely**: on the labelled space the
pair of the shape and its partner lies in the support of the coupling at every skeleton
vertex, so `thm:relabel` makes them `9D³`-comparable. -/
theorem ae_partner_comparable (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν)) :
    ∀ᵐ ω ∂labelMeasure (N' := N') θ', ∀ u, u ∈ sample (gArityAt ω.1) →
      MarkedQI (9 * D ^ 3) (gShapeSpace (gShapeAt ω.1 u)) (gShapeSpace (gPartner π ω u)) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  filter_upwards [ae_of_fst (ν := uniformField (GWord N'))
      (ae_skeleton_good θ' hJN' hq' hq0' hJ2' hθJ'),
    ae_of_snd (μ := survivalMeasure (N := N') θ') (ae_uniform_mem_Ico (GWord N'))] with ω h1 h2
  intro u hu
  obtain ⟨⟨hκ2, hκJ⟩, hmass⟩ := h1 u hu
  have hν : 0 < reducedWeight θ' (gArityAt ω.1 u) :=
    reducedWeight_pos θ' hq' hq0' hJ2' hθJ' hκ2 hκJ
  have hdraw : gPartner π ω u
      = condDraw (π (gArityAt ω.1 u) hκ2 hν) (gShapeAt ω.1 u) (ω.2 u) := by
    rw [gPartner, gDraw, dif_pos ⟨hκ2, hν⟩]
  have hmarg : margFstT (π (gArityAt ω.1 u) hκ2 hν) (gShapeAt ω.1 u) ≠ 0 := by
    rw [(hπ _ hκ2 hν).marg₁, gCondPMF_apply]
    exact hmass
  rw [hdraw]
  exact (hπ _ hκ2 hν).qi _ (condDraw_ne_zero _ hmarg (h2 u))

end AlmostSure

/-! ### The rate and the almost sure statement at `J' ≤ 2J - 1` -/

section Rate

variable {J J' : ℕ}

/-- **The matching event is measurable**: the intersection over the heights of the
preimages of countable sets. -/
lemma measurableSet_engine_match (θ : Offspring J) (θ' : Offspring J') {D : ℝ}
    (π₁ : GCouplings θ) (π₂ : GCouplings θ') (exc1 exc2 : ℕ → Option (ℕ × ℕ)) :
    MeasurableSet {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
      GraphMarkovMatching.InfMatch (cRel (GraphMatching.compat (gNetGraph D)))
        (fun n => encLab exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
        (fun n => encLab exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)} := by
  set R := cRel (GraphMatching.compat (gNetGraph D)) with hR
  have hset : {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
        GraphMarkovMatching.InfMatch R
          (fun n => encLab exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
          (fun n => encLab exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)}
      = ⋂ n, (fun ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) =>
          (encLab exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n,
            encLab exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)) ⁻¹'
          {p | GraphMarkovMatching.Support.fullSimK R 1 0 n p.1 p.2} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact GraphMarkovMatching.Support.infMatchK_iff_forall_level R 1 0 _ _
      (fun n => restrictLab_encLab exc1 _ _ 0 n) (fun n => restrictLab_encLab exc2 _ _ 0 n)
  rw [hset]
  refine MeasurableSet.iInter fun n => ?_
  exact (((measurable_encLab D π₁ exc1 0 n).comp measurable_fst).prodMk
    ((measurable_encLab D π₂ exc2 0 n).comp measurable_snd))
    ((Set.to_countable _).measurableSet)

/-- **The couplings of `thm:relabel` exist at every arity past one threshold**: the
thresholds of the finitely many arities of positive reduced weight are dominated by
their maximum. -/
lemma exists_gCouplings_all (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (h0' : 0 < θ' 0)
    (hθJ' : 0 < θ' J') :
    ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → ∃ π : GCouplings θ',
      ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
        IsGShapeCoupling (D : ℝ) (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν)
          (gMixPMF θ hJN hq hq0 hs1) (π κ hκ hν) := by
  have hκJ : ∀ κ, 0 < reducedWeight θ' κ → κ ≤ J' := fun κ hν => by
    by_contra h
    rw [reducedWeight_eq_zero_of_gt θ' (not_le.mp h)] at hν
    exact lt_irrefl _ hν
  have hex : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ), ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D →
      ∃ π : PMF (GShape × GShape), IsGShapeCoupling (D : ℝ) (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν)
        (gMixPMF θ hJN hq hq0 hs1) π := fun κ hκ hν =>
    exists_gShapeCoupling_cond_mix θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1' h0' hθJ'
      hκ hν (hκJ κ hν)
  choose thr hthr using hex
  set f : ℕ → ℕ := fun κ => if h : 2 ≤ κ ∧ 0 < reducedWeight θ' κ then thr κ h.1 h.2 else 0
    with hf
  refine ⟨(Finset.Icc 2 J').sup f, fun D hD => ?_⟩
  have hD' : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ), thr κ hκ hν ≤ D := by
    intro κ hκ hν
    have hmem : κ ∈ Finset.Icc 2 J' := Finset.mem_Icc.mpr ⟨hκ, hκJ κ hν⟩
    have := Finset.le_sup (f := f) hmem
    rw [hf] at this
    simp only [dif_pos (And.intro hκ hν)] at this
    exact this.trans hD
  choose π hπ using fun κ hκ hν => hthr κ hκ hν D (hD' κ hκ hν)
  exact ⟨π, hπ⟩

/-- **`thm:hairy-general` at `J' ≤ 2J - 1`, the rate**: past a threshold depending on the
two laws alone, two independent labelled samples fail to be
`⌈216 J J'² (3·(3¹⁵D¹⁶)²)²⌉`-quasi-isometric with probability at most `Ke^{-cD²}`. -/
theorem hairy_general_rate (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (h0' : 0 < θ' 0)
    (hθJ' : 0 < θ' J') (hJJ' : J ≤ J') (hJ'2 : J' ≤ 2 * J - 1) :
    ∃ (D₆ : ℕ) (K c : ℝ), 0 < c ∧ ∀ D : ℕ, D₆ ≤ D →
      twoLabelMeasure (N := N) (N' := N') θ θ'
        {ω | ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1},
          BranchingProcess.IsQIWith ⌈216 * J * J' ^ 2 * (3 * (14348907 * (D : ℝ) ^ 16) ^ 2) ^ 2⌉₊
            (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1)) F}
        ≤ ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) := by
  have hJ2' : 2 ≤ J' := le_trans hJ2 hJJ'
  obtain ⟨D₆, K, c, hc, hmatch⟩ :=
    exists_engine_match θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1' hθJ' hJJ' hJ'2
  obtain ⟨D₁, hD₁⟩ := exists_gCouplings_all θ hJN hq hq0 hs1 h0 hθJ hJ2 θ hJN hq hq0 hs1 h0 hθJ
  obtain ⟨D₂, hD₂⟩ := exists_gCouplings_all θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1'
    h0' hθJ'
  refine ⟨max (max D₆ D₁) (max D₂ 1), K, c, hc, fun D hD => ?_⟩
  have hD6 : D₆ ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD
  have hD1 : D₁ ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD
  have hD2 : D₂ ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hD
  have hD1' : 1 ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hD
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1'
  obtain ⟨π₁, hπ₁⟩ := hD₁ D hD1
  obtain ⟨π₂, hπ₂⟩ := hD₂ D hD2
  have hbound := hmatch D hD6 π₁ hπ₁ π₂ hπ₂
  have _ := isProbabilityMeasure_twoLabelMeasure (N := N) (N' := N') θ hJN hq θ' hJN' hq'
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  have _ := isProbabilityMeasure_labelMeasure (N' := N) θ hJN hq
  have _ := isProbabilityMeasure_labelMeasure (N' := N') θ' hJN' hq'
  -- the matching event fails with probability at most `K e^{-cD²}`
  set M := {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
    GraphMarkovMatching.InfMatch (cRel (GraphMatching.compat (gNetGraph D)))
      (fun n => encLab (fun _ => none) (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
      (fun n => encLab (bushyExc J J') (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)} with hM
  have hfail : twoLabelMeasure (N := N) (N' := N') θ θ' Mᶜ
      ≤ ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) := by
    rw [prob_compl_eq_one_sub (measurableSet_engine_match θ θ' π₁ π₂ _ _)]
    have h1 := tsub_le_iff_right.mp hbound
    rw [add_comm] at h1
    exact tsub_le_iff_right.mpr h1
  -- the good event
  have hgood₁ : ∀ᵐ ω ∂labelMeasure (N' := N) θ, IsGHairySample ω.1 ∧
      SkelBounded J (gArityAt ω.1) ∧ ∀ u, u ∈ sample (gArityAt ω.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.1 u))
          (gShapeSpace (gPartner π₁ ω u)) := by
    filter_upwards [ae_of_fst (ν := uniformField (GWord N)) (ae_isGHairySample θ hJN hq hs1),
      ae_of_fst (ν := uniformField (GWord N)) (ae_skeleton_good θ hJN hq hq0 hJ2 hθJ),
      ae_partner_comparable θ hJN hq hq0 hs1 θ hJN hq hq0 hs1 hJ2 hθJ π₁ hπ₁] with ω h1 h2 h3
    exact ⟨h1, fun u hu => (h2 u hu).1, h3⟩
  have hgood₂ : ∀ᵐ ω ∂labelMeasure (N' := N') θ', IsGHairySample ω.1 ∧
      SkelBounded J' (gArityAt ω.1) ∧ ∀ u, u ∈ sample (gArityAt ω.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.1 u))
          (gShapeSpace (gPartner π₂ ω u)) := by
    filter_upwards [ae_of_fst (ν := uniformField (GWord N')) (ae_isGHairySample θ' hJN' hq' hs1'),
      ae_of_fst (ν := uniformField (GWord N')) (ae_skeleton_good θ' hJN' hq' hq0' hJ2' hθJ'),
      ae_partner_comparable θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1' hJ2' hθJ' π₂ hπ₂] with ω h1 h2 h3
    exact ⟨h1, fun u hu => (h2 u hu).1, h3⟩
  have hgood : ∀ᵐ ω ∂twoLabelMeasure (N := N) (N' := N') θ θ', (IsGHairySample ω.1.1 ∧
      SkelBounded J (gArityAt ω.1.1) ∧ ∀ u, u ∈ sample (gArityAt ω.1.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.1.1 u))
          (gShapeSpace (gPartner π₁ ω.1 u))) ∧ (IsGHairySample ω.2.1 ∧
      SkelBounded J' (gArityAt ω.2.1) ∧ ∀ u, u ∈ sample (gArityAt ω.2.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.2.1 u))
          (gShapeSpace (gPartner π₂ ω.2 u))) := by
    filter_upwards [ae_of_fst (ν := labelMeasure (N' := N') θ') hgood₁,
      ae_of_snd (μ := labelMeasure (N' := N) θ) hgood₂] with ω h1 h2
    exact ⟨h1, h2⟩
  -- on the good matching event the samples are quasi-isometric
  have hsub : {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
        ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1},
          BranchingProcess.IsQIWith ⌈216 * J * J' ^ 2 * (3 * (14348907 * (D : ℝ) ^ 16) ^ 2) ^ 2⌉₊
            (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1)) F}
      ⊆ Mᶜ ∪ {ω | ¬ ((IsGHairySample ω.1.1 ∧
      SkelBounded J (gArityAt ω.1.1) ∧ ∀ u, u ∈ sample (gArityAt ω.1.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.1.1 u))
          (gShapeSpace (gPartner π₁ ω.1 u))) ∧ (IsGHairySample ω.2.1 ∧
      SkelBounded J' (gArityAt ω.2.1) ∧ ∀ u, u ∈ sample (gArityAt ω.2.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.2.1 u))
          (gShapeSpace (gPartner π₂ ω.2 u))))} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hm, ⟨hc, hs, hτ⟩, ⟨hc', hs', hτ'⟩⟩ := hcon
    apply hω
    exact sample_qi_of_engine_match excCompat_none (excCompat_bushyExc hJ2) hc hc' hs hs'
      (by omega) (by omega) hDR (fun u _ => rfl) (fun u _ => rfl) hτ hτ' hm
  calc twoLabelMeasure (N := N) (N' := N') θ θ' _
      ≤ twoLabelMeasure (N := N) (N' := N') θ θ' (Mᶜ ∪ _) := measure_mono hsub
    _ ≤ twoLabelMeasure (N := N) (N' := N') θ θ' Mᶜ
        + twoLabelMeasure (N := N) (N' := N') θ θ' _ := measure_union_le _ _
    _ = twoLabelMeasure (N := N) (N' := N') θ θ' Mᶜ + 0 := by rw [ae_iff.mp hgood]
    _ ≤ ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) := by rw [add_zero]; exact hfail

/-- **`thm:hairy-general` at `J' ≤ 2J - 1`, the almost sure statement on the labelled
space**: the failure rates `Ke^{-cD²}` fall below every threshold, so almost surely some
scale succeeds. -/
theorem hairy_general_ae_small (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (h0' : 0 < θ' 0)
    (hθJ' : 0 < θ' J') (hJJ' : J ≤ J') (hJ'2 : J' ≤ 2 * J - 1) :
    ∀ᵐ ω ∂twoLabelMeasure (N := N) (N' := N') θ θ',
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1.1))
        (wordGraphN (· ∈ sample ω.2.1)) := by
  obtain ⟨D₆, K, c, hc, hrate⟩ := hairy_general_rate θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq'
    hq0' hs1' h0' hθJ' hJJ' hJ'2
  rw [ae_iff]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  have hεpos : (0 : ℝ) < ε := hε
  have hKpos : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨D₀, hD₀⟩ := hairy_rate_to_one hc (ε := 16 * ε / max K 1) (by positivity)
  set D := max D₀ D₆ with hD
  have hsmall : K * Real.exp (-(c * (D : ℝ) ^ 2)) ≤ ε := by
    have h1 := hD₀ D (le_max_left _ _)
    have h2 : K ≤ max K 1 := le_max_left _ _
    have h3 : 0 < Real.exp (-(c * (D : ℝ) ^ 2)) := Real.exp_pos _
    rw [lt_div_iff₀ hKpos] at h1
    nlinarith
  have hsub : {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
        ¬ BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1.1))
          (wordGraphN (· ∈ sample ω.2.1))}
      ⊆ {ω | ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1},
          BranchingProcess.IsQIWith ⌈216 * J * J' ^ 2 * (3 * (14348907 * (D : ℝ) ^ 16) ^ 2) ^ 2⌉₊
            (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1)) F} := by
    rintro ω hω ⟨F, hF⟩
    exact hω ⟨_, F, hF⟩
  calc twoLabelMeasure (N := N) (N' := N') θ θ' _
      ≤ twoLabelMeasure (N := N) (N' := N') θ θ' _ := measure_mono hsub
    _ ≤ ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) := hrate D (le_max_right _ _)
    _ ≤ (ε : ℝ≥0∞) := ENNReal.ofReal_le_of_le_toReal (by simpa using hsmall)
    _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm

/-- An almost sure property of the first coordinates of two products descends to the
product of the first factors: one reassociation and two Fubini slices. -/
lemma ae_prod_fst_fst {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] {μ : Measure α} {ν : Measure β} {μ' : Measure γ}
    {ν' : Measure δ} [SFinite μ] [IsProbabilityMeasure ν] [SFinite μ'] [IsProbabilityMeasure ν']
    {p : α × γ → Prop} (h : ∀ᵐ ω ∂((μ.prod ν).prod (μ'.prod ν')), p (ω.1.1, ω.2.1)) :
    ∀ᵐ ω ∂(μ.prod μ'), p ω := by
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc.symm) (μ.prod (ν.prod (μ'.prod ν')))
      ((μ.prod ν).prod (μ'.prod ν')) :=
    (measurePreserving_prodAssoc μ ν (μ'.prod ν')).symm MeasurableEquiv.prodAssoc
  rw [← hmp.map_eq] at h
  have h1 := ae_of_ae_map hmp.measurable.aemeasurable h
  have h2 : ∀ᵐ ω ∂(μ.prod (ν.prod (μ'.prod ν'))), p (ω.1, ω.2.2.1) := h1
  have h3 := ae_pair_outer (p := fun z : α × (γ × δ) => p (z.1, z.2.1)) h2
  rw [ae_iff] at h3 ⊢
  exact null_of_prod_assoc μ μ' ν' h3

/-- **`thm:hairy-general` at `J' ≤ 2J - 1`**: two independent samples conditioned on
survival are almost surely quasi-isometric, the uniform fields integrated out. -/
theorem hairy_general_ae_small' (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (h0' : 0 < θ' 0)
    (hθJ' : 0 < θ' J') (hJJ' : J ≤ J') (hJ'2 : J' ≤ 2 * J - 1) :
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  have h := hairy_general_ae_small θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1' h0' hθJ'
    hJJ' hJ'2
  exact ae_prod_fst_fst (μ := survivalMeasure (N := N) θ) (ν := uniformField (GWord N))
    (μ' := survivalMeasure (N := N') θ') (ν' := uniformField (GWord N')) h

end Rate

/-! ### Transitivity and the chain of intermediate laws -/

section Chain

/-- **`thm:qi-transitive` at general arity**: almost sure quasi-isometry of independent
samples composes through the triple product. -/
theorem gSampleQI_trans {N₀ N₁ N₂ : ℕ} {μ₀ : Measure (GWord N₀ → ℕ)} {μ₁ : Measure (GWord N₁ → ℕ)}
    {μ₂ : Measure (GWord N₂ → ℕ)} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂]
    (h01 : ∀ᵐ ω ∂(μ₀.prod μ₁), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2)))
    (h12 : ∀ᵐ ω ∂(μ₁.prod μ₂), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2))) :
    ∀ᵐ ω ∂(μ₀.prod μ₂), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2)) := by
  have hlift01 := ae_pair_fst (τ := μ₂) h01
  have hlift12 : ∀ᵐ ω ∂(μ₀.prod (μ₁.prod μ₂)),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.2.1))
        (wordGraphN (· ∈ sample ω.2.2)) := ae_of_snd h12
  have htrip : ∀ᵐ ω ∂(μ₀.prod (μ₁.prod μ₂)),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
        (wordGraphN (· ∈ sample ω.2.2)) := by
    filter_upwards [hlift01, hlift12] with ω h1 h2
    exact QuasiIsometric.trans (wordGraphN_connected (prefixClosedN_sample _)
      ⟨⟨[], BranchingProcess.nil_mem_sample _⟩⟩) h1 h2
  exact ae_pair_outer (p := fun z : (GWord N₀ → ℕ) × (GWord N₂ → ℕ) =>
    BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample z.1)) (wordGraphN (· ∈ sample z.2)))
    htrip

/-- An almost sure property of a product, read through the swap. -/
lemma ae_prod_swap {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {p : α × β → Prop}
    (h : ∀ᵐ ω ∂(ν.prod μ), p ω.swap) : ∀ᵐ ω ∂(μ.prod ν), p ω := by
  rw [← Measure.prod_swap] at h
  have := ae_of_ae_map measurable_swap.aemeasurable h
  simpa using this

/-- Almost sure quasi-isometry of independent samples is symmetric. -/
theorem gSampleQI_symm {N₀ N₁ : ℕ} {μ₀ : Measure (GWord N₀ → ℕ)} {μ₁ : Measure (GWord N₁ → ℕ)}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (h : ∀ᵐ ω ∂(μ₁.prod μ₀), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2))) :
    ∀ᵐ ω ∂(μ₀.prod μ₁), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2)) := by
  refine ae_prod_swap ?_
  filter_upwards [h] with ω hω
  exact QuasiIsometric.symm (wordGraphN_connected (prefixClosedN_sample _)
    ⟨⟨[], BranchingProcess.nil_mem_sample _⟩⟩) hω

/-- **The intermediate laws of the chain**: mass `ε` at `0` and `1 - ε` at `m`. -/
noncomputable def bridgeLaw (m : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 1 ≤ m) :
    Offspring m where
  mass := fun j => if j = 0 then ε else if j = m then 1 - ε else 0
  nonneg := fun j => by
    split_ifs
    · exact hε0
    · linarith
    · exact le_rfl
  vanishing := fun j hj => by
    rw [if_neg (by omega), if_neg (by omega)]
  total := by
    have hm0 : m ≠ 0 := by omega
    rw [Finset.sum_range_succ, Finset.sum_eq_single 0]
    · simp [hm0]
    · intro j hj hj0
      rw [if_neg hj0, if_neg (Finset.mem_range.mp hj).ne]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h

lemma bridgeLaw_zero (m : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 1 ≤ m) :
    bridgeLaw m ε hε0 hε1 hm 0 = ε := by
  show (if (0 : ℕ) = 0 then ε else if (0 : ℕ) = m then 1 - ε else 0) = ε
  rw [if_pos rfl]

lemma bridgeLaw_top (m : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 1 ≤ m) :
    bridgeLaw m ε hε0 hε1 hm m = 1 - ε := by
  show (if m = 0 then ε else if m = m then 1 - ε else 0) = 1 - ε
  rw [if_neg (by omega), if_pos rfl]

/-- The mean of a bridge law is `m(1 - ε)`. -/
lemma bridgeLaw_mean (m : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 1 ≤ m) :
    (bridgeLaw m ε hε0 hε1 hm).mean = m * (1 - ε) := by
  have hm0 : m ≠ 0 := by omega
  rw [Offspring.mean, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, bridgeLaw_top]
  intro j hj
  have hjm : j ≠ m := (Finset.mem_range.mp hj).ne
  by_cases hj0 : j = 0
  · rw [hj0]; simp
  · show (j : ℝ) * (if j = 0 then ε else if j = m then 1 - ε else 0) = 0
    rw [if_neg hj0, if_neg hjm, mul_zero]

/-- **The bridge laws are supercritical** for `ε < ½` and `m ≥ 2`. -/
lemma bridgeLaw_supercritical (m : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) (hm : 2 ≤ m) :
    (bridgeLaw m ε hε0 (by linarith) (by omega)).IsSupercritical := by
  show 1 < (bridgeLaw m ε hε0 (by linarith) (by omega)).mean
  rw [bridgeLaw_mean]
  have : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

end Chain

/-! ### `thm:hairy-general` -/

/-- **`thm:hairy-general` for `J ≤ J'`**, by strong induction on `J' - J`: at `J' ≤ 2J - 1`
the bushy regime applies directly, and otherwise the chain passes through the bridge law
at `2J - 1`, which `thm:qi-transitive` composes. -/
theorem hairy_general_ae_of_le : ∀ (d : ℕ) {J J' N N' : ℕ} (θ : Offspring J) (_ : J ≤ N)
    (_ : θ.extinction < 1) (_ : 0 < θ.extinction) (_ : 0 < θ 0) (_ : 0 < θ J) (_ : 2 ≤ J)
    (θ' : Offspring J') (_ : J' ≤ N') (_ : θ'.extinction < 1) (_ : 0 < θ'.extinction)
    (_ : 0 < θ' 0) (_ : 0 < θ' J') (_ : J ≤ J') (_ : J' - J = d),
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro J J' N N' θ hJN hq hq0 h0 hθJ hJ2 θ' hJN' hq' hq0' h0' hθJ' hJJ' hd
    have hJ2' : 2 ≤ J' := le_trans hJ2 hJJ'
    have hs1 : θ.skeletonWeight 1 < 1 := skeletonWeight_one_lt_one_of θ hq hq0 hJ2 hθJ
    have hs1' : θ'.skeletonWeight 1 < 1 := skeletonWeight_one_lt_one_of θ' hq' hq0' hJ2' hθJ'
    by_cases hsmall : J' ≤ 2 * J - 1
    · exact hairy_general_ae_small' θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1' h0' hθJ'
        hJJ' hsmall
    · -- the bridge law at `J₁ = 2J - 1`
      set J₁ := 2 * J - 1 with hJ₁
      have hJ₁2 : 2 ≤ J₁ := by omega
      set θ₁ : Offspring J₁ := bridgeLaw J₁ (1 / 4) (by norm_num) (by norm_num) (by omega)
        with hθ₁
      have hq₁ : θ₁.extinction < 1 :=
        Offspring.extinction_lt_one_of_supercritical _
          (bridgeLaw_supercritical J₁ (1 / 4) (by norm_num) (by norm_num) hJ₁2)
      have h0₁ : 0 < θ₁ 0 := by rw [hθ₁, bridgeLaw_zero]; norm_num
      have hθJ₁ : 0 < θ₁ J₁ := by rw [hθ₁, bridgeLaw_top]; norm_num
      have hq0₁ : 0 < θ₁.extinction := Offspring.extinction_pos _ h0₁
      have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
      have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := J₁) θ₁ le_rfl hq₁
      have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
      have h01 := hairy_general_ae_small' θ hJN hq hq0 hs1 h0 hθJ hJ2 θ₁ le_rfl hq₁ hq0₁
        (skeletonWeight_one_lt_one_of θ₁ hq₁ hq0₁ hJ₁2 hθJ₁) h0₁ hθJ₁ (by omega) le_rfl
      have h12 := ih (J' - J₁) (by omega) θ₁ le_rfl hq₁ hq0₁ h0₁ hθJ₁ hJ₁2 θ' hJN' hq' hq0'
        h0' hθJ' (by omega) rfl
      exact gSampleQI_trans h01 h12

/-- **`thm:hairy-general`**: two finitely supported supercritical offspring laws with
`θ₀, θ₀' > 0`, sampled independently and conditioned on survival, are almost surely
quasi-isometric. -/
theorem hairy_general_ae {J J' : ℕ} (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h0 : 0 < θ 0) (hθJ : 0 < θ J)
    (hJ2 : 2 ≤ J) (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h0' : 0 < θ' 0) (hθJ' : 0 < θ' J') (hJ2' : 2 ≤ J') :
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) := by
  rcases le_or_gt J J' with hJJ' | hJJ'
  · exact hairy_general_ae_of_le (J' - J) θ hJN hq hq0 h0 hθJ hJ2 θ' hJN' hq' hq0' h0' hθJ'
      hJJ' rfl
  · have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
    have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
    exact gSampleQI_symm (hairy_general_ae_of_le (J - J') θ' hJN' hq' hq0' h0' hθJ' hJ2' θ hJN
      hq hq0 h0 hθJ hJJ'.le rfl)

end ChainClasses
