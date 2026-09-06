import ChainClasses.General.GeneralLabelField
import ChainClasses.General.GeneralShapeEta
import ChainClasses.Universality.HairyCross
import GraphMarkovMatching.Composite.Numeric

/-!
`thm:hairy-general` of `trichotomy.tex`, the identification with the engine's process:
the labelled reduced skeleton of `GeneralLabelField`, whose pairs of a label and an arity
are i.i.d. with the product law `μ_D ⊗ ν̃`, is encoded on the binary tree `𝔹` as the
composite process of `thm:composite-matching` (`arbitrary_offspring_matching.tex`,
`sec:composite`, `def:composite-kernel`), at every height, and the two-law matching theorem
is read off for two independent labelled samples.

The composite kernel is a Markov chain on `𝔹`.  A skeleton vertex of arity `k` sits at
the root of its cascade: a core arity descends by the balanced halving, `k ≥ 4` splitting
into the counters `k/2` on the left and `k - k/2` on the right, `k = 3` into the counter
`2` on the left and a fresh slot on the right, `k = 2` into two fresh slots; an
exceptional arity `z` with the declared pair `(a, b)` descends along the marker chain of
the `a`-cascade, to the left while the running value is at least `4`, and the port
carrying the forced `b`-cascade is the right child at value `3` and the left child at
value `2`, the other child being an ordinary counter or a fresh slot.  The slots are the
leaves of the cascade in left-to-right order, and the slot `j` of a vertex `u` carries
the child `u ++ [j]` of the reduced skeleton; every internal vertex of a cascade carries
the class `v₀` of the one-vertex shape.

* `gChild`, `ChildK`, `markKind`, `stepKind`, `servedC`, `validS`, `ExcCompat`,
  `stepKind_spec`: **the slot geometry**, the two children of a tagged state as internal
  cascade vertices or fresh slots, the slots a state serves, and the compatibility
  `a - 1 + b = z` of a chart with the arities.
* `encSub`, `encLab`, `restrictLab_encSub`, `restrictLab_encLab`: **the encoded label
  field**, the projective family of labellings of `𝔹_n` read off a label field and an
  arity field over the reduced skeleton.
* `childRec`, `dec`, `decTop`, `encSub_eq_iff`, `encLab_eq_iff`: **the decoder**, the
  records of skeleton addresses with labels and arities a labelling of `𝔹_n` prescribes;
  a labelling is the encoding of a field exactly when the field takes the prescribed
  values.
* `muM_succ_apply`, `compK_apply_eq`, `muM_eq_recMass`, `cT_eq_recMass`: **the mass of a
  labelling under the process law** is the product of one fresh mass `μ(a) ν(k)` per
  decoded record.
* `WFL`, `wfl_dec`, `decTop_some`, `prefixClosed_of_wfl`, `compat_of_wfl`, `recLab`,
  `recAr`, `levent_iff_probe`, `recMass_eq_prod`: the decoded records form a
  prefix-closed probe respecting the arities, over which the records are the product
  formula's data.
* `measurableSet_levent_of`, `measurable_encLab_of`, `encLab_apply_of_pattern`,
  `map_encLab_of_pattern`: **the projective identification from a product formula**: over
  any probability space carrying a label field and an arity field whose pairs are i.i.d.
  with the product law `μ ⊗ ν` over every prefix-closed probe respecting the prescribed
  arities, the arity law supported in the letter range, the encoded label field at
  height `n` has the law `cT` at height `n`.  Both regimes read their identification off
  this lemma: the bushy one here, the chain one in `ChainEngineBridge`.
* `reducedPMF`, `reducedPMF_ne_zero_iff`, `gClassMass_eq_gClassPMF`: the reduced law
  `ν̃` as a probability law with support `{2, …, J'}` and the class law as the mass of
  a class.
* `GCompat`, `gCompat_iff`, `survivalMeasure_compat_bad_null`,
  `labelMeasure_compat_bad_null`: the arities at compatible addresses lie in the reduced
  support almost surely.
* `measurable_encLab`, `labelMeasure_label_pattern'`, `labelMeasure_encLab_apply`,
  `labelMeasure_map_encLab`: **the projective identification**, the product formula of
  `GeneralLabelField` freed of its support condition through the null sets above, and
  the law of the encoded label field at height `n` as the composite process law `cT` at
  height `n`, with the class law `μ_D` and the reduced law `ν̃`.
* `etaG_compat_eq`, `bushyExc`, `excCompat_bushyExc`, `twoLabelMeasure`,
  `twoLabelMeasure_map_encLab`, `exists_engine_match`: **`thm:hairy-general`, the
  matching step**, two independent labelled samples in the bushy regime `J' ≤ 2J - 1`
  admit one automorphism of `𝔹` matching their encodings to within one class of `G_D`
  with probability at least `1 - K e^{-cD²}`, by `thm:composite-matching` at the chart
  of `thm:hairy-cross`.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure)
open GraphMarkovMatching.Support (FullLab restrictLab prodPMF)
open GraphMarkovMatching (leaf rootLab muM)
open GraphMarkovMatching.Composite (CtrC CState compK cT freshC markK val cRel)

variable {N' : ℕ}

/-! ### The slot geometry -/

/-- The child `u ++ [j]` of a reduced-skeleton address, `u` itself when `j` exceeds the
letter range. -/
def gChild (u : GWord N') (j : ℕ) : GWord N' :=
  if h : j < N' then u ++ [⟨j, h⟩] else u

lemma gChild_of_lt (u : GWord N') {j : ℕ} (h : j < N') : gChild u j = u ++ [⟨j, h⟩] :=
  dif_pos h

/-- A child of a cascade vertex: an internal cascade vertex starting at a slot offset with
a tagged counter, or a fresh slot at a slot index. -/
inductive ChildK where
  | internal (o : ℕ) (t : CtrC) : ChildK
  | slot (j : ℕ) : ChildK

/-- The two children of a marker vertex of the pair `(a, b)` at stage `i`, serving the
slots from `off` on (`def:composite-kernel`, rules (ii) and (iii)). -/
def markKind (off a b i : ℕ) : ChildK × ChildK :=
  if val a i ≤ 2 then (ChildK.internal off (CtrC.ord b), ChildK.slot (off + b))
  else if val a i = 3 then
    (ChildK.internal off (CtrC.ord 2), ChildK.internal (off + 2) (CtrC.ord b))
  else (ChildK.internal off (CtrC.mark a b (i + 1)),
    ChildK.internal (off + val a i / 2 - 1 + b) (CtrC.ord (val a i - val a i / 2)))

/-- The two children of a tagged state serving the slots from `off` on: the balanced rule
at an ordinary counter, the marker chain at an exceptional counter or a marker. -/
def stepKind (exc : ℕ → Option (ℕ × ℕ)) (off : ℕ) : CState ℕ → ChildK × ChildK
  | (_, CtrC.mark a b i) => markKind off a b i
  | (_, CtrC.ord k) =>
      match exc k with
      | some p => markKind off p.1 p.2 0
      | none =>
          if 4 ≤ k then
            (ChildK.internal off (CtrC.ord (k / 2)),
              ChildK.internal (off + k / 2) (CtrC.ord (k - k / 2)))
          else if k = 3 then (ChildK.internal off (CtrC.ord 2), ChildK.slot (off + 2))
          else (ChildK.slot off, ChildK.slot (off + 1))

/-- The number of slots the subtree of a tagged counter serves: an ordinary counter `k`
serves `k` slots, a marker of the pair `(a, b)` at value `m` serves `m - 1 + b`. -/
def servedC : CtrC → ℕ
  | CtrC.ord k => k
  | CtrC.mark a b i => val a i - 1 + b

/-- The valid tagged states: counters at least `2`, markers of value at least `2` with a
port continuation at least `2`. -/
def validS : CState ℕ → Prop
  | (_, CtrC.ord k) => 2 ≤ k
  | (_, CtrC.mark a b i) => 2 ≤ val a i ∧ 2 ≤ b

/-- The slots served by a child. -/
def servedK : ChildK → ℕ
  | ChildK.internal _ t => servedC t
  | ChildK.slot _ => 1

/-- The first slot served by a child. -/
def startK : ChildK → ℕ
  | ChildK.internal o _ => o
  | ChildK.slot j => j

/-- Validity of a child: an internal child is a valid state. -/
def validK (v0 : ℕ) : ChildK → Prop
  | ChildK.internal _ t => validS (v0, t)
  | ChildK.slot _ => True

/-- The compatibility of the exceptional chart with the arities: a declared pair `(a, b)`
of `z` has both members at least `2` and `a - 1 + b = z` (`eq:composite-pair`). -/
def ExcCompat (exc : ℕ → Option (ℕ × ℕ)) : Prop :=
  ∀ z p, exc z = some p → 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 - 1 + p.2 = z

lemma markKind_spec (v0 off a b i : ℕ) (hm : 2 ≤ val a i) (hb : 2 ≤ b) :
    startK (markKind off a b i).1 = off ∧
      startK (markKind off a b i).2 = off + servedK (markKind off a b i).1 ∧
      servedK (markKind off a b i).1 + servedK (markKind off a b i).2 = val a i - 1 + b ∧
      validK v0 (markKind off a b i).1 ∧ validK v0 (markKind off a b i).2 := by
  rcases Nat.lt_or_ge (val a i) 3 with h2 | h3
  · have e : markKind off a b i = (ChildK.internal off (CtrC.ord b), ChildK.slot (off + b)) := by
      rw [markKind, if_pos (by omega)]
    rw [e]
    simp only [startK, servedK, servedC, validK, validS, true_and, and_true]
    first | trivial | omega
  · rcases Nat.lt_or_ge (val a i) 4 with h4 | h4
    · have e : markKind off a b i =
          (ChildK.internal off (CtrC.ord 2), ChildK.internal (off + 2) (CtrC.ord b)) := by
        rw [markKind, if_neg (by omega), if_pos (by omega)]
      rw [e]
      simp only [startK, servedK, servedC, validK, validS, true_and]
      first | trivial | omega
    · have e : markKind off a b i =
          (ChildK.internal off (CtrC.mark a b (i + 1)),
            ChildK.internal (off + val a i / 2 - 1 + b) (CtrC.ord (val a i - val a i / 2))) := by
        rw [markKind, if_neg (by omega), if_neg (by omega)]
      rw [e]
      simp only [startK, servedK, servedC, validK, validS,
        GraphMarkovMatching.Composite.val_succ, true_and]
      first | trivial | omega

/-- **The slot geometry of a step**: the left child serves the slots from `off` on, the
right child the following ones, together all the slots of the state, and both children
are valid. -/
lemma stepKind_spec {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (v0 off : ℕ)
    {s : CState ℕ} (hs : validS s) :
    startK (stepKind exc off s).1 = off ∧
      startK (stepKind exc off s).2 = off + servedK (stepKind exc off s).1 ∧
      servedK (stepKind exc off s).1 + servedK (stepKind exc off s).2 = servedC s.2 ∧
      validK v0 (stepKind exc off s).1 ∧ validK v0 (stepKind exc off s).2 := by
  obtain ⟨v, c⟩ := s
  cases c with
  | mark a b i =>
      simp only [validS] at hs
      simpa [stepKind, servedC] using markKind_spec v0 off a b i hs.1 hs.2
  | ord k =>
      simp only [validS] at hs
      rcases hp : exc k with _ | p
      · rcases Nat.lt_or_ge k 3 with h2 | h3
        · have e : stepKind exc off (v, CtrC.ord k) = (ChildK.slot off, ChildK.slot (off + 1)) := by
            simp only [stepKind, hp]
            rw [if_neg (by omega), if_neg (by omega)]
          rw [e]
          simp only [startK, servedK, servedC, validK, true_and, and_true]
          first | trivial | omega
        · rcases Nat.lt_or_ge k 4 with h4 | h4
          · have e : stepKind exc off (v, CtrC.ord k) =
                (ChildK.internal off (CtrC.ord 2), ChildK.slot (off + 2)) := by
              simp only [stepKind, hp]
              rw [if_neg (by omega), if_pos (by omega)]
            rw [e]
            simp only [startK, servedK, servedC, validK, validS, true_and, and_true]
            first | trivial | omega
          · have e : stepKind exc off (v, CtrC.ord k) =
                (ChildK.internal off (CtrC.ord (k / 2)),
                  ChildK.internal (off + k / 2) (CtrC.ord (k - k / 2))) := by
              simp only [stepKind, hp]
              rw [if_pos h4]
            rw [e]
            simp only [startK, servedK, servedC, validK, validS, true_and]
            first | trivial | omega
      · obtain ⟨ha, hb, hk⟩ := hexc k p hp
        have h := markKind_spec v0 off p.1 p.2 0 (by simpa using ha) hb
        simp only [GraphMarkovMatching.Composite.val_zero] at h
        have e : stepKind exc off (v, CtrC.ord k) = markKind off p.1 p.2 0 := by
          simp only [stepKind, hp]
        rw [e]
        simp only [servedC]
        rw [← hk]
        exact h

/-! ### The encoding -/

/-- The address and slot offset a child of the cascade vertex `u` works at. -/
def childAddr (u : GWord N') : ChildK → GWord N' × ℕ
  | ChildK.internal o _ => (u, o)
  | ChildK.slot j => (gChild u j, 0)

/-- The state of a child of the cascade vertex `u` read off the fields: an internal child
carries `v₀` with its counter, a slot carries the label and the arity of the skeleton
child it holds. -/
def childState (lab ar : GWord N' → ℕ) (v0 : ℕ) (u : GWord N') : ChildK → CState ℕ
  | ChildK.internal _ t => (v0, t)
  | ChildK.slot j => (lab (gChild u j), CtrC.ord (ar (gChild u j)))

/-- **The encoded label field below a cascade vertex**: the labelling of `𝔹_n` below the
vertex of state `s` working at the address `u` and the slot offset `off`. -/
noncomputable def encSub (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 : ℕ) :
    (n : ℕ) → GWord N' → ℕ → CState ℕ → FullLab (CState ℕ) n
  | 0, _, _, s => leaf s
  | n + 1, u, off, s =>
      GraphMarkovMatching.branch s
        (encSub exc lab ar v0 n (childAddr u (stepKind exc off s).1).1
            (childAddr u (stepKind exc off s).1).2
            (childState lab ar v0 u (stepKind exc off s).1),
          encSub exc lab ar v0 n (childAddr u (stepKind exc off s).2).1
            (childAddr u (stepKind exc off s).2).2
            (childState lab ar v0 u (stepKind exc off s).2))

/-- **The encoded label field**: the root of the reduced skeleton at the root of `𝔹`. -/
noncomputable def encLab (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 : ℕ)
    (n : ℕ) : FullLab (CState ℕ) n :=
  encSub exc lab ar v0 n [] 0 (lab [], CtrC.ord (ar []))

lemma encSub_zero (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 : ℕ)
    (u : GWord N') (off : ℕ) (s : CState ℕ) : encSub exc lab ar v0 0 u off s = leaf s := rfl

lemma encSub_succ (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 n : ℕ)
    (u : GWord N') (off : ℕ) (s : CState ℕ) :
    encSub exc lab ar v0 (n + 1) u off s =
      GraphMarkovMatching.branch s
        (encSub exc lab ar v0 n (childAddr u (stepKind exc off s).1).1
            (childAddr u (stepKind exc off s).1).2
            (childState lab ar v0 u (stepKind exc off s).1),
          encSub exc lab ar v0 n (childAddr u (stepKind exc off s).2).1
            (childAddr u (stepKind exc off s).2).2
            (childState lab ar v0 u (stepKind exc off s).2)) := rfl

lemma rootLab_encSub (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : CState ℕ),
      rootLab n (encSub exc lab ar v0 n u off s) = s
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl

lemma restrictLab_branch_succ {V : Type} (n : ℕ) (s : V)
    (p : FullLab V (n + 1) × FullLab V (n + 1)) :
    restrictLab (n + 1) (GraphMarkovMatching.branch s p) =
      GraphMarkovMatching.branch s (restrictLab n p.1, restrictLab n p.2) := rfl

/-- The encoded field is projective: the restriction of the height-`(n+1)` encoding is the
height-`n` encoding. -/
lemma restrictLab_encSub (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : CState ℕ),
      restrictLab n (encSub exc lab ar v0 (n + 1) u off s) = encSub exc lab ar v0 n u off s
  | 0, _, _, _ => rfl
  | n + 1, u, off, s => by
      rw [encSub_succ exc lab ar v0 (n + 1) u off s, restrictLab_branch_succ,
        encSub_succ exc lab ar v0 n u off s]
      simp only
      rw [restrictLab_encSub exc lab ar v0 n, restrictLab_encSub exc lab ar v0 n]

lemma restrictLab_encLab (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 n : ℕ) :
    restrictLab n (encLab exc lab ar v0 (n + 1)) = encLab exc lab ar v0 n :=
  restrictLab_encSub exc lab ar v0 n [] 0 _

/-! ### Labellings of `𝔹_{n+1}` -/

section Labellings

variable {V : Type}

/-- The left subtree of a labelling of `𝔹_{n+1}`. -/
def subL {n : ℕ} (ℓ : FullLab V (n + 1)) : FullLab V n := ℓ.2.1

/-- The right subtree of a labelling of `𝔹_{n+1}`. -/
def subR {n : ℕ} (ℓ : FullLab V (n + 1)) : FullLab V n := ℓ.2.2

lemma branch_eta {n : ℕ} (ℓ : FullLab V (n + 1)) :
    GraphMarkovMatching.branch (rootLab (n + 1) ℓ) (subL ℓ, subR ℓ) = ℓ := rfl

/-- A labelling is a branch exactly when its root and its two subtrees agree. -/
lemma branch_eq_iff {n : ℕ} (s : V) (p : FullLab V n × FullLab V n) (ℓ : FullLab V (n + 1)) :
    GraphMarkovMatching.branch s p = ℓ ↔ rootLab (n + 1) ℓ = s ∧ p.1 = subL ℓ ∧ p.2 = subR ℓ := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    calc GraphMarkovMatching.branch s p
        = GraphMarkovMatching.branch (rootLab (n + 1) ℓ) (subL ℓ, subR ℓ) := by
          rw [h1]
          congr 1
          exact Prod.ext h2 h3
      _ = ℓ := branch_eta ℓ

/-- **The mass of a labelling under the tree law**: the root state is forced, the child
pair is drawn from the kernel, and the two subtrees carry their own masses. -/
lemma muM_succ_apply (P : V → PMF (V × V)) (s : V) (n : ℕ) (ℓ : FullLab V (n + 1)) :
    muM P s (n + 1) ℓ =
      if rootLab (n + 1) ℓ = s then
        P s (rootLab n (subL ℓ), rootLab n (subR ℓ)) *
          (muM P (rootLab n (subL ℓ)) n (subL ℓ) * muM P (rootLab n (subR ℓ)) n (subR ℓ))
      else 0 := by
  rw [GraphMarkovMatching.muM_succ, PMF.map_apply]
  by_cases hroot : rootLab (n + 1) ℓ = s
  · rw [if_pos hroot]
    have hiff : ∀ p : FullLab V n × FullLab V n,
        (ℓ = GraphMarkovMatching.branch s p) ↔ p = (subL ℓ, subR ℓ) := by
      intro p
      rw [eq_comm, branch_eq_iff]
      constructor
      · rintro ⟨-, h2, h3⟩
        exact Prod.ext h2 h3
      · rintro rfl
        exact ⟨hroot, rfl, rfl⟩
    simp_rw [hiff]
    rw [tsum_ite_eq, GraphMarkovMatching.pairMix, PMF.bind_apply]
    rw [tsum_eq_single (rootLab n (subL ℓ), rootLab n (subR ℓ))]
    · rw [GraphMarkovMatching.Support.prodPMF_apply]
    · intro στ hne
      rcases στ with ⟨σ, τ⟩
      rw [GraphMarkovMatching.Support.prodPMF_apply]
      by_cases hσ : σ = rootLab n (subL ℓ)
      · have hτ : τ ≠ rootLab n (subR ℓ) := fun h => hne (by rw [hσ, h])
        rw [GraphMarkovMatching.muM_eq_zero_of_rootLab_ne P (Ne.symm hτ), mul_zero, mul_zero]
      · rw [GraphMarkovMatching.muM_eq_zero_of_rootLab_ne P (Ne.symm hσ), zero_mul, mul_zero]
  · rw [if_neg hroot]
    refine ENNReal.tsum_eq_zero.mpr fun p => ?_
    rw [if_neg]
    intro h
    exact hroot (by rw [h]; rfl)

end Labellings

/-! ### The decoder -/

/-- A decoded record: a reduced-skeleton address with the label and the arity a labelling
prescribes there. -/
abbrev Rec (N' : ℕ) : Type := GWord N' × ℕ × ℕ

/-- The field takes the prescribed values on every record. -/
def Levent (L : List (Rec N')) (lab ar : GWord N' → ℕ) : Prop :=
  ∀ t ∈ L, lab t.1 = t.2.1 ∧ ar t.1 = t.2.2

lemma Levent_append {L₁ L₂ : List (Rec N')} {lab ar : GWord N' → ℕ} :
    Levent (L₁ ++ L₂) lab ar ↔ Levent L₁ lab ar ∧ Levent L₂ lab ar := by
  simp only [Levent, List.forall_mem_append]

lemma Levent_nil {lab ar : GWord N' → ℕ} : Levent ([] : List (Rec N')) lab ar := by
  simp [Levent]

/-- The mass of a list of records: one fresh mass `μ(a) ν(k)` per record. -/
noncomputable def recMass (μ : PMF ℕ) (ν : PMF ℕ) (L : List (Rec N')) : ℝ≥0∞ :=
  (L.map fun t => μ t.2.1 * ν t.2.2).prod

lemma recMass_append (μ ν : PMF ℕ) (L₁ L₂ : List (Rec N')) :
    recMass μ ν (L₁ ++ L₂) = recMass μ ν L₁ * recMass μ ν L₂ := by
  simp [recMass, List.map_append, List.prod_append]

/-- The mass of a list of records, with a mixture-dependent option. -/
noncomputable def optMass (μ ν : PMF ℕ) : Option (List (Rec N')) → ℝ≥0∞
  | some L => recMass μ ν L
  | none => 0

/-- The record a child of the cascade vertex `u` prescribes, given the root state found
below it: an internal child must carry `v₀` with its counter and prescribes nothing, a
slot must carry an ordinary counter and prescribes the label and the arity of the
skeleton child it holds. -/
def childRec (v0 : ℕ) (u : GWord N') : ChildK → CState ℕ → Option (List (Rec N'))
  | ChildK.internal _ t, r => if r = (v0, t) then some [] else none
  | ChildK.slot j, (a, CtrC.ord m) => some [(gChild u j, a, m)]
  | ChildK.slot _, (_, CtrC.mark _ _ _) => none

/-- The mass a child contributes, given the root state found below it: an internal child
forces its state, a slot draws a fresh state. -/
noncomputable def childMass (μ ν : PMF ℕ) (v0 : ℕ) : ChildK → CState ℕ → ℝ≥0∞
  | ChildK.internal _ t, r => if r = (v0, t) then 1 else 0
  | ChildK.slot _, r => freshC μ ν r

/-- **The decoder**: the records a labelling of `𝔹_n` prescribes below the cascade vertex
of state `s` working at `u` and `off`, or `none` when the labelling is not an encoding. -/
noncomputable def dec (exc : ℕ → Option (ℕ × ℕ)) (v0 : ℕ) :
    (n : ℕ) → GWord N' → ℕ → CState ℕ → FullLab (CState ℕ) n → Option (List (Rec N'))
  | 0, _, _, s, ℓ => if ℓ = leaf s then some [] else none
  | n + 1, u, off, s, ℓ =>
      if rootLab (n + 1) ℓ = s then
        ((childRec v0 u (stepKind exc off s).1 (rootLab n (subL ℓ))).bind fun M₁ =>
          (dec exc v0 n (childAddr u (stepKind exc off s).1).1
              (childAddr u (stepKind exc off s).1).2 (rootLab n (subL ℓ)) (subL ℓ)).map
            fun L₁ => M₁ ++ L₁).bind fun L₁ =>
          ((childRec v0 u (stepKind exc off s).2 (rootLab n (subR ℓ))).bind fun M₂ =>
            (dec exc v0 n (childAddr u (stepKind exc off s).2).1
                (childAddr u (stepKind exc off s).2).2 (rootLab n (subR ℓ)) (subR ℓ)).map
              fun L₂ => M₂ ++ L₂).map fun L₂ => L₁ ++ L₂
      else none

/-- The records of one child: the record of the child itself and the records below it. -/
noncomputable def decChild (exc : ℕ → Option (ℕ × ℕ)) (v0 n : ℕ) (u : GWord N') (c : ChildK)
    (x : FullLab (CState ℕ) n) : Option (List (Rec N')) :=
  (childRec v0 u c (rootLab n x)).bind fun M =>
    (dec exc v0 n (childAddr u c).1 (childAddr u c).2 (rootLab n x) x).map fun L => M ++ L

lemma dec_zero (exc : ℕ → Option (ℕ × ℕ)) (v0 : ℕ) (u : GWord N') (off : ℕ) (s : CState ℕ)
    (ℓ : FullLab (CState ℕ) 0) :
    dec exc v0 0 u off s ℓ = if ℓ = leaf s then some [] else none := rfl

lemma dec_succ (exc : ℕ → Option (ℕ × ℕ)) (v0 n : ℕ) (u : GWord N') (off : ℕ) (s : CState ℕ)
    (ℓ : FullLab (CState ℕ) (n + 1)) :
    dec exc v0 (n + 1) u off s ℓ =
      if rootLab (n + 1) ℓ = s then
        (decChild exc v0 n u (stepKind exc off s).1 (subL ℓ)).bind fun L₁ =>
          (decChild exc v0 n u (stepKind exc off s).2 (subR ℓ)).map fun L₂ => L₁ ++ L₂
      else none := rfl

/-- **The decoder at the root**: the root must carry an ordinary counter, which with its
label is the first record. -/
noncomputable def decTop (exc : ℕ → Option (ℕ × ℕ)) (v0 n : ℕ) (ℓ : FullLab (CState ℕ) n) :
    Option (List (Rec N')) :=
  match rootLab n ℓ with
  | (a, CtrC.ord k) => (dec exc v0 n [] 0 (a, CtrC.ord k) ℓ).map fun L => ([], a, k) :: L
  | (_, CtrC.mark _ _ _) => none

/-! ### The local step -/

/-- A child's record is realised by the fields exactly when the state found below it is
the encoded state. -/
lemma childRec_iff (lab ar : GWord N' → ℕ) (v0 : ℕ) (u : GWord N') (c : ChildK)
    (r : CState ℕ) :
    (∃ M, childRec v0 u c r = some M ∧ Levent M lab ar) ↔ r = childState lab ar v0 u c := by
  cases c with
  | internal o t =>
      simp only [childRec, childState]
      constructor
      · rintro ⟨M, hM, -⟩
        by_contra h
        rw [if_neg h] at hM
        exact Option.some_ne_none M hM.symm
      · intro h
        exact ⟨[], by rw [if_pos h], Levent_nil⟩
  | slot j =>
      obtain ⟨a, m⟩ := r
      cases m with
      | ord m =>
          simp only [childRec, childState]
          constructor
          · rintro ⟨M, hM, hL⟩
            rw [Option.some.injEq] at hM
            subst hM
            obtain ⟨h1, h2⟩ := hL _ (List.mem_singleton_self _)
            simp only at h1 h2
            rw [h1, h2]
          · intro h
            simp only [Prod.mk.injEq, CtrC.ord.injEq] at h
            refine ⟨_, rfl, ?_⟩
            intro t ht
            rw [List.mem_singleton] at ht
            subst ht
            exact ⟨h.1.symm, h.2.symm⟩
      | mark a' b' i' =>
          simp only [childRec, childState, Prod.mk.injEq, reduceCtorEq, and_false, iff_false,
            not_exists, not_and]
          intro M hM
          exact hM.elim

/-- A child's mass is the mass of its record. -/
lemma childMass_eq (μ ν : PMF ℕ) (v0 : ℕ) (u : GWord N') (c : ChildK) (r : CState ℕ) :
    childMass μ ν v0 c r = optMass μ ν (childRec v0 u c r) := by
  cases c with
  | internal o t =>
      simp only [childMass, childRec]
      split_ifs <;> rfl
  | slot j =>
      obtain ⟨a, m⟩ := r
      cases m with
      | ord m =>
          simp only [childMass, childRec, optMass, recMass, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one]
          exact GraphMarkovMatching.Composite.freshC_ord_apply μ ν a m
      | mark a' b' i' =>
          simp only [childMass, childRec, optMass]
          exact GraphMarkovMatching.Composite.freshC_mark_apply μ ν a a' b' i'

lemma map_pair_left_apply {A : Type} (ρ : PMF A) (c r₁ r₂ : A) :
    (ρ.map fun f => (c, f)) (r₁, r₂) = if r₁ = c then ρ r₂ else 0 := by
  rw [PMF.map_apply]
  by_cases h : r₁ = c
  · subst h
    rw [if_pos rfl]
    have hiff : ∀ f : A, ((r₁, r₂) = (r₁, f)) ↔ f = r₂ := by
      intro f
      simp only [Prod.mk.injEq, true_and]
      exact eq_comm
    simp_rw [hiff]
    rw [tsum_ite_eq]
  · rw [if_neg h]
    refine ENNReal.tsum_eq_zero.mpr fun f => ?_
    rw [if_neg]
    intro hf
    exact h (congrArg Prod.fst hf)

lemma pure_pair_apply {A : Type} (c₁ c₂ r₁ r₂ : A) :
    (PMF.pure (c₁, c₂)) (r₁, r₂) = (if r₁ = c₁ then 1 else 0) * (if r₂ = c₂ then 1 else 0) := by
  rw [PMF.pure_apply]
  by_cases h1 : r₁ = c₁ <;> by_cases h2 : r₂ = c₂ <;> simp [h1, h2]

lemma markK_apply_eq (μ ν : PMF ℕ) (v0 off a b i : ℕ) (r₁ r₂ : CState ℕ) :
    markK μ ν v0 a b i (r₁, r₂) =
      childMass μ ν v0 (markKind off a b i).1 r₁ * childMass μ ν v0 (markKind off a b i).2 r₂ := by
  rcases Nat.lt_or_ge (val a i) 3 with h2 | h3
  · rw [GraphMarkovMatching.Composite.markK_le_two (by omega), map_pair_left_apply]
    simp only [markKind, if_pos (by omega : val a i ≤ 2), childMass]
    split_ifs <;> simp
  · rcases Nat.lt_or_ge (val a i) 4 with h4 | h4
    · have h : val a i = 3 := by omega
      rw [GraphMarkovMatching.Composite.markK_three h, pure_pair_apply]
      simp only [markKind, if_neg (by omega : ¬ val a i ≤ 2), if_pos h, childMass]
      split_ifs <;> simp
    · rw [GraphMarkovMatching.Composite.markK_of_ge h4, pure_pair_apply]
      simp only [markKind, if_neg (by omega : ¬ val a i ≤ 2), if_neg (by omega : val a i ≠ 3),
        childMass]
      split_ifs <;> simp

/-- **The kernel as a product of child masses**: the composite kernel at a child pair is
the product of the two child masses of the step. -/
lemma compK_apply_eq (exc : ℕ → Option (ℕ × ℕ)) (μ ν : PMF ℕ) (v0 off : ℕ) (s : CState ℕ)
    (r₁ r₂ : CState ℕ) :
    compK exc μ ν v0 s (r₁, r₂) =
      childMass μ ν v0 (stepKind exc off s).1 r₁ * childMass μ ν v0 (stepKind exc off s).2 r₂ := by
  obtain ⟨v, c⟩ := s
  cases c with
  | mark a b i =>
      rw [GraphMarkovMatching.Composite.compK_mark, markK_apply_eq μ ν v0 off]
      rfl
  | ord k =>
      rcases hp : exc k with _ | p
      · rcases Nat.lt_or_ge k 3 with h2 | h3
        · rw [GraphMarkovMatching.Composite.compK_ord_none_le_two exc μ ν v0 hp (by omega),
            GraphMarkovMatching.Support.prodPMF_apply]
          simp only [stepKind, hp, if_neg (by omega : ¬ 4 ≤ k), if_neg (by omega : k ≠ 3),
            childMass]
        · rcases Nat.lt_or_ge k 4 with h4 | h4
          · have h : k = 3 := by omega
            rw [GraphMarkovMatching.Composite.compK_ord_none_three exc μ ν v0 hp h,
              map_pair_left_apply]
            simp only [stepKind, hp, if_neg (by omega : ¬ 4 ≤ k), if_pos h, childMass]
            split_ifs <;> simp
          · rw [GraphMarkovMatching.Composite.compK_ord_none_of_ge exc μ ν v0 hp h4,
              pure_pair_apply]
            simp only [stepKind, hp, if_pos h4, childMass]
            split_ifs <;> simp
      · rw [GraphMarkovMatching.Composite.compK_ord_exc exc μ ν v0 hp, markK_apply_eq μ ν v0 off]
        simp only [stepKind, hp]

/-! ### The decoder characterises the encoding -/

lemma exists_bind_map_append_iff (o₁ o₂ : Option (List (Rec N'))) (lab ar : GWord N' → ℕ) :
    (∃ L, (o₁.bind fun L₁ => o₂.map fun L₂ => L₁ ++ L₂) = some L ∧ Levent L lab ar) ↔
      (∃ L₁, o₁ = some L₁ ∧ Levent L₁ lab ar) ∧ ∃ L₂, o₂ = some L₂ ∧ Levent L₂ lab ar := by
  rcases o₁ with _ | L₁ <;> rcases o₂ with _ | L₂ <;> simp [Levent_append]

lemma optMass_bind_map_append (μ ν : PMF ℕ) (o₁ o₂ : Option (List (Rec N'))) :
    optMass μ ν (o₁.bind fun L₁ => o₂.map fun L₂ => L₁ ++ L₂) =
      optMass μ ν o₁ * optMass μ ν o₂ := by
  rcases o₁ with _ | L₁ <;> rcases o₂ with _ | L₂ <;> simp [optMass, recMass_append]

lemma optMass_decChild (exc : ℕ → Option (ℕ × ℕ)) (μ ν : PMF ℕ) (v0 n : ℕ) (u : GWord N')
    (c : ChildK) (x : FullLab (CState ℕ) n) :
    optMass μ ν (decChild exc v0 n u c x) =
      optMass μ ν (childRec v0 u c (rootLab n x)) *
        optMass μ ν (dec exc v0 n (childAddr u c).1 (childAddr u c).2 (rootLab n x) x) := by
  rw [decChild]
  rcases childRec v0 u c (rootLab n x) with _ | M
  · simp [optMass]
  · rcases dec exc v0 n (childAddr u c).1 (childAddr u c).2 (rootLab n x) x with _ | L
    · simp [optMass]
    · simp [optMass, recMass_append]

/-- A child's subtree is the encoding exactly when the child's records are realised by the
fields, given the characterisation one level down. -/
lemma decChild_iff (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 n : ℕ)
    (ih : ∀ (u : GWord N') (off : ℕ) (s : CState ℕ) (ℓ : FullLab (CState ℕ) n),
      encSub exc lab ar v0 n u off s = ℓ ↔
        ∃ L, dec exc v0 n u off s ℓ = some L ∧ Levent L lab ar)
    (u : GWord N') (c : ChildK) (x : FullLab (CState ℕ) n) :
    encSub exc lab ar v0 n (childAddr u c).1 (childAddr u c).2 (childState lab ar v0 u c) = x ↔
      ∃ L, decChild exc v0 n u c x = some L ∧ Levent L lab ar := by
  constructor
  · intro h
    have hroot : rootLab n x = childState lab ar v0 u c := by
      rw [← h, rootLab_encSub]
    obtain ⟨M, hM, hMe⟩ := (childRec_iff lab ar v0 u c (rootLab n x)).mpr hroot
    obtain ⟨L, hL, hLe⟩ := (ih _ _ _ x).mp h
    refine ⟨M ++ L, ?_, Levent_append.mpr ⟨hMe, hLe⟩⟩
    rw [decChild, hM, hroot, hL]
    rfl
  · rintro ⟨L, hL, hLe⟩
    rw [decChild] at hL
    obtain ⟨M, hM, hmap⟩ := Option.bind_eq_some_iff.mp hL
    obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.mp hmap
    obtain ⟨hMe, hLe'⟩ := Levent_append.mp hLe
    have hroot : rootLab n x = childState lab ar v0 u c :=
      (childRec_iff lab ar v0 u c (rootLab n x)).mp ⟨M, hM, hMe⟩
    rw [hroot] at hL'
    exact (ih _ _ _ x).mpr ⟨L', hL', hLe'⟩

/-- **The decoder characterises the encoding**: a labelling of `𝔹_n` is the encoding below
a cascade vertex exactly when it decodes to records the fields realise. -/
theorem encSub_eq_iff (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : CState ℕ) (ℓ : FullLab (CState ℕ) n),
      encSub exc lab ar v0 n u off s = ℓ ↔
        ∃ L, dec exc v0 n u off s ℓ = some L ∧ Levent L lab ar := by
  intro n
  induction n with
  | zero =>
      intro u off s ℓ
      rw [encSub_zero, dec_zero]
      constructor
      · intro h
        exact ⟨[], by rw [if_pos h.symm], Levent_nil⟩
      · rintro ⟨L, hL, -⟩
        by_contra h
        rw [if_neg (Ne.symm h)] at hL
        exact Option.some_ne_none L hL.symm
  | succ n ih =>
      intro u off s ℓ
      rw [encSub_succ, dec_succ, branch_eq_iff]
      by_cases hroot : rootLab (n + 1) ℓ = s
      · rw [if_pos hroot, exists_bind_map_append_iff, ← decChild_iff exc lab ar v0 n ih,
          ← decChild_iff exc lab ar v0 n ih]
        simp only [hroot, true_and]
      · rw [if_neg hroot]
        simp only [hroot, false_and, false_iff, not_exists, not_and]
        intro L hL
        exact (Option.some_ne_none L hL.symm).elim

/-- **The encoded field at the root**: a labelling is the encoding exactly when its root
record and the records below are realised. -/
theorem encLab_eq_iff (exc : ℕ → Option (ℕ × ℕ)) (lab ar : GWord N' → ℕ) (v0 n : ℕ)
    (ℓ : FullLab (CState ℕ) n) :
    encLab exc lab ar v0 n = ℓ ↔ ∃ L, decTop exc v0 n ℓ = some L ∧ Levent L lab ar := by
  rw [encLab]
  constructor
  · intro h
    have hroot : rootLab n ℓ = (lab [], CtrC.ord (ar [])) := by
      rw [← h, rootLab_encSub]
    obtain ⟨L, hL, hLe⟩ := (encSub_eq_iff exc lab ar v0 n [] 0 _ ℓ).mp h
    refine ⟨([], lab [], ar []) :: L, ?_, ?_⟩
    · simp only [decTop, hroot, hL, Option.map_some]
    · intro t ht
      rw [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨rfl, rfl⟩
      · exact hLe t ht
  · rintro ⟨L, hL, hLe⟩
    rcases hr : rootLab n ℓ with ⟨a, c⟩
    cases c with
    | ord k =>
        simp only [decTop, hr] at hL
        obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.mp hL
        have hhead := hLe ([], a, k) (List.mem_cons_self)
        simp only at hhead
        have hLe' : Levent L' lab ar := fun t ht => hLe t (List.mem_cons_of_mem _ ht)
        rw [hhead.1, hhead.2]
        exact (encSub_eq_iff exc lab ar v0 n [] 0 _ ℓ).mpr ⟨L', hL', hLe'⟩
    | mark a' b' i' =>
        simp only [decTop, hr] at hL
        exact (Option.some_ne_none L hL.symm).elim

/-! ### The mass of a labelling -/

/-- **The tree law as a product of record masses**: the mass of a labelling below a
cascade vertex is the product of the fresh masses of the records it decodes to. -/
theorem muM_eq_recMass (exc : ℕ → Option (ℕ × ℕ)) (μ ν : PMF ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : CState ℕ) (ℓ : FullLab (CState ℕ) n),
      muM (compK exc μ ν v0) s n ℓ = optMass μ ν (dec exc v0 n u off s ℓ) := by
  intro n
  induction n with
  | zero =>
      intro u off s ℓ
      rw [GraphMarkovMatching.muM_zero, dec_zero, PMF.pure_apply]
      split_ifs <;> rfl
  | succ n ih =>
      intro u off s ℓ
      rw [muM_succ_apply, dec_succ]
      by_cases hroot : rootLab (n + 1) ℓ = s
      · rw [if_pos hroot, if_pos hroot, optMass_bind_map_append, optMass_decChild,
          optMass_decChild, compK_apply_eq exc μ ν v0 off, childMass_eq μ ν v0 u,
          childMass_eq μ ν v0 u, ih, ih]
        ring
      · rw [if_neg hroot, if_neg hroot]
        rfl

lemma decTop_ord (exc : ℕ → Option (ℕ × ℕ)) (v0 n : ℕ) (ℓ : FullLab (CState ℕ) n) {a k : ℕ}
    (h : rootLab n ℓ = (a, CtrC.ord k)) :
    decTop exc v0 n ℓ =
      (dec exc v0 n [] 0 (a, CtrC.ord k) ℓ).map fun L => (([] : GWord N'), a, k) :: L := by
  simp only [decTop, h]

lemma decTop_mark (exc : ℕ → Option (ℕ × ℕ)) (v0 n : ℕ) (ℓ : FullLab (CState ℕ) n)
    {a a' b' i' : ℕ} (h : rootLab n ℓ = (a, CtrC.mark a' b' i')) :
    decTop exc v0 n ℓ = (none : Option (List (Rec N'))) := by
  simp only [decTop, h]

lemma optMass_map_cons (μ ν : PMF ℕ) (t : Rec N') (o : Option (List (Rec N'))) :
    optMass μ ν (o.map fun L => t :: L) = μ t.2.1 * ν t.2.2 * optMass μ ν o := by
  rcases o with _ | L <;> simp [optMass, recMass]

/-- **The fresh law as a product of record masses**: the mass of a labelling under the
composite process law is the product of the fresh masses of the records of its decoding
at the root. -/
theorem cT_eq_recMass (exc : ℕ → Option (ℕ × ℕ)) (μ ν : PMF ℕ) (v0 n : ℕ)
    (ℓ : FullLab (CState ℕ) n) :
    cT exc μ ν v0 n ℓ = optMass μ ν (decTop exc v0 n ℓ : Option (List (Rec N'))) := by
  rw [cT, PMF.bind_apply, tsum_eq_single (rootLab n ℓ)]
  · rcases hr : rootLab n ℓ with ⟨a, c⟩
    cases c with
    | ord k =>
        rw [decTop_ord exc v0 n ℓ hr, optMass_map_cons,
          GraphMarkovMatching.Composite.freshC_ord_apply,
          muM_eq_recMass exc μ ν v0 n [] 0 (a, CtrC.ord k) ℓ]
    | mark a' b' i' =>
        rw [decTop_mark exc v0 n ℓ hr, GraphMarkovMatching.Composite.freshC_mark_apply,
          zero_mul]
        rfl
  · intro s hs
    rw [GraphMarkovMatching.muM_eq_zero_of_rootLab_ne _ (Ne.symm hs), mul_zero]

/-! ### The decoded probe -/

lemma length_gChild (u : GWord N') {j : ℕ} (h : j < N') : (gChild u j).length = u.length + 1 := by
  rw [gChild_of_lt u h, List.length_append, List.length_singleton]

lemma gChild_inj (u : GWord N') {j j' : ℕ} (h : j < N') (h' : j' < N')
    (e : gChild u j = gChild u j') : j = j' := by
  rw [gChild_of_lt u h, gChild_of_lt u h'] at e
  have := (List.append_inj' e rfl).2
  simpa using this

lemma eq_of_gChild_prefix (u : GWord N') {j j' : ℕ} (h : j < N') (h' : j' < N')
    (e : gChild u j <+: gChild u j') : j = j' :=
  gChild_inj u h h' (e.eq_of_length (by rw [length_gChild u h, length_gChild u h']))

/-- **A well-formed list of records** below the cascade vertex `u` serving the slots
`lo ≤ j < hi`: every address lies below a served slot, every address is a slot of `u` or a
child of a recorded address within its arity, and the addresses are distinct. -/
structure WFL (u : GWord N') (lo hi : ℕ) (L : List (Rec N')) : Prop where
  below : ∀ t ∈ L, ∃ j, lo ≤ j ∧ j < hi ∧ j < N' ∧ gChild u j <+: t.1
  closed : ∀ t ∈ L, (∃ j, j < N' ∧ t.1 = gChild u j) ∨
    ∃ t' ∈ L, ∃ j, j < N' ∧ j < t'.2.2 ∧ t.1 = gChild t'.1 j
  nodup : (L.map Prod.fst).Nodup

lemma WFL.nil (u : GWord N') (lo hi : ℕ) : WFL u lo hi [] :=
  ⟨fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (List.not_mem_nil), List.nodup_nil⟩

/-- Two sibling lists serving consecutive slot ranges merge. -/
lemma WFL.append {u : GWord N'} {lo mid hi : ℕ} (h1 : lo ≤ mid) (h2 : mid ≤ hi)
    {L₁ L₂ : List (Rec N')} (w₁ : WFL u lo mid L₁) (w₂ : WFL u mid hi L₂) :
    WFL u lo hi (L₁ ++ L₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := w₁.below t ht
      exact ⟨j, hj1, by omega, hj3, hj4⟩
    · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := w₂.below t ht
      exact ⟨j, by omega, hj2, hj3, hj4⟩
  · intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · rcases w₁.closed t ht with h | ⟨t', ht', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t', List.mem_append_left _ ht', h⟩
    · rcases w₂.closed t ht with h | ⟨t', ht', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t', List.mem_append_right _ ht', h⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨w₁.nodup, w₂.nodup, ?_⟩
    intro w hw₁ w' hw₂ hww
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw₁
    obtain ⟨t', ht', e⟩ := List.mem_map.mp hw₂
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ := w₁.below t ht
    obtain ⟨j', hj1', hj2', hj3', hj4'⟩ := w₂.below t' ht'
    rw [e, ← hww] at hj4'
    rcases List.prefix_or_prefix_of_prefix hj4 hj4' with h | h
    · have := eq_of_gChild_prefix u hj3 hj3' h
      omega
    · have := eq_of_gChild_prefix u hj3' hj3 h
      omega

/-- A slot record with the well-formed list below it is well formed for its one slot. -/
lemma WFL.slot {u : GWord N'} {j : ℕ} (hj : j < N') {a m : ℕ} {L : List (Rec N')}
    (w : WFL (gChild u j) 0 m L) : WFL u j (j + 1) ((gChild u j, a, m) :: L) := by
  have hstrict : ∀ t ∈ L, ∃ j', j' < N' ∧ gChild (gChild u j) j' <+: t.1 := by
    intro t ht
    obtain ⟨j', -, -, hj', h⟩ := w.below t ht
    exact ⟨j', hj', h⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨j, le_rfl, by omega, hj, List.prefix_rfl⟩
    · obtain ⟨j', hj', h⟩ := hstrict t ht
      refine ⟨j, le_rfl, by omega, hj, ?_⟩
      rw [gChild_of_lt (gChild u j) hj'] at h
      exact (List.prefix_append _ _).trans h
  · intro t ht
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact Or.inl ⟨j, hj, rfl⟩
    · rcases w.closed t ht with ⟨j', hj', h⟩ | ⟨t', ht', j', hj', hlt, h⟩
      · obtain ⟨j'', -, hj''m, hj'', h''⟩ := w.below t ht
        rw [h] at h''
        have := eq_of_gChild_prefix (gChild u j) hj'' hj' h''
        refine Or.inr ⟨(gChild u j, a, m), List.mem_cons_self, j', hj', ?_, h⟩
        show j' < m
        omega
      · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', j', hj', hlt, h⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, w.nodup⟩
    intro hmem
    obtain ⟨t, ht, e⟩ := List.mem_map.mp hmem
    simp only at e
    obtain ⟨j', hj', h⟩ := hstrict t ht
    rw [e] at h
    have := h.length_le
    rw [length_gChild _ hj'] at this
    omega

/-- A record with an arity in the letter range. -/
def GoodRec (N' : ℕ) (t : Rec N') : Prop := 2 ≤ t.2.2 ∧ t.2.2 ≤ N'

/-- The well-formedness of a child's records, given well-formedness one level down: a
well-formed sublist, the whole list when the sublist has its arities in the letter
range. -/
lemma wfl_decChild (exc : ℕ → Option (ℕ × ℕ)) (v0 n : ℕ)
    (ih : ∀ (u : GWord N') (off : ℕ) (s : CState ℕ) (ℓ : FullLab (CState ℕ) n)
      (L : List (Rec N')), dec exc v0 n u off s ℓ = some L → validS s →
      off + servedC s.2 ≤ N' → ∃ L' : List (Rec N'), (∀ t ∈ L', t ∈ L) ∧
        WFL u off (off + servedC s.2) L' ∧ ((∀ t ∈ L', GoodRec N' t) → L' = L))
    (u : GWord N') (c : ChildK) (x : FullLab (CState ℕ) n) (Lc : List (Rec N'))
    (hc : decChild exc v0 n u c x = some Lc) (hv : validK v0 c)
    (hN : startK c + servedK c ≤ N') :
    ∃ Lc' : List (Rec N'), (∀ t ∈ Lc', t ∈ Lc) ∧
      WFL u (startK c) (startK c + servedK c) Lc' ∧ ((∀ t ∈ Lc', GoodRec N' t) → Lc' = Lc) := by
  rw [decChild] at hc
  obtain ⟨M, hM, hmap⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.mp hmap
  cases c with
  | internal o t =>
      simp only [childRec] at hM
      have hroot : rootLab n x = (v0, t) := by
        by_contra h
        rw [if_neg h] at hM
        exact Option.some_ne_none M hM.symm
      rw [if_pos hroot, Option.some.injEq] at hM
      subst hM
      rw [hroot] at hL'
      simp only [List.nil_append, startK, servedK]
      simpa using ih u o (v0, t) x L' hL' hv hN
  | slot j =>
      simp only [startK, servedK] at hN ⊢
      rcases hr : rootLab n x with ⟨a, m⟩
      rw [hr] at hM hL'
      cases m with
      | ord m =>
          simp only [childRec, Option.some.injEq] at hM
          subst hM
          simp only [List.singleton_append]
          by_cases hm : 2 ≤ m ∧ m ≤ N'
          · obtain ⟨L'', hsub, hw, hgood⟩ := ih (gChild u j) 0 (a, CtrC.ord m) x L' hL'
              (by simpa [validS] using hm.1) (by simpa [servedC] using hm.2)
            simp only [servedC, Nat.zero_add] at hw
            refine ⟨(gChild u j, a, m) :: L'', ?_, WFL.slot (by omega) hw, ?_⟩
            · intro t ht
              rw [List.mem_cons] at ht ⊢
              rcases ht with rfl | ht
              · exact Or.inl rfl
              · exact Or.inr (hsub t ht)
            · intro hall
              rw [hgood fun t ht => hall t (List.mem_cons_of_mem _ ht)]
          · refine ⟨[(gChild u j, a, m)], ?_, ?_, ?_⟩
            · intro t ht
              rw [List.mem_singleton] at ht
              rw [ht]
              exact List.mem_cons_self
            · exact WFL.slot (by omega) (WFL.nil _ _ _)
            · intro hall
              exact absurd (hall _ List.mem_cons_self) hm
      | mark a' b' i' =>
          simp only [childRec] at hM
          exact (Option.some_ne_none M hM.symm).elim

/-- **The decoded records are well formed**: below a valid state with its slots in the
letter range, the records of a labelling contain a well-formed sublist, the whole list when
the sublist has its arities in the letter range. -/
theorem wfl_dec {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : CState ℕ) (ℓ : FullLab (CState ℕ) n)
      (L : List (Rec N')), dec exc v0 n u off s ℓ = some L → validS s →
      off + servedC s.2 ≤ N' → ∃ L' : List (Rec N'), (∀ t ∈ L', t ∈ L) ∧
        WFL u off (off + servedC s.2) L' ∧ ((∀ t ∈ L', GoodRec N' t) → L' = L) := by
  intro n
  induction n with
  | zero =>
      intro u off s ℓ L hL hs hN
      rw [dec_zero] at hL
      split_ifs at hL
      rw [Option.some.injEq] at hL
      subst hL
      exact ⟨[], fun _ h => h, WFL.nil u off _, fun _ => rfl⟩
  | succ n ih =>
      intro u off s ℓ L hL hs hN
      rw [dec_succ] at hL
      split_ifs at hL with hroot
      obtain ⟨L₁, hL₁, hmap⟩ := Option.bind_eq_some_iff.mp hL
      obtain ⟨L₂, hL₂, rfl⟩ := Option.map_eq_some_iff.mp hmap
      obtain ⟨hst1, hst2, hsum, hv1, hv2⟩ := stepKind_spec hexc v0 off hs
      obtain ⟨L₁', hsub₁, w₁, hg₁⟩ :=
        wfl_decChild exc v0 n ih u _ (subL ℓ) L₁ hL₁ hv1 (by omega)
      obtain ⟨L₂', hsub₂, w₂, hg₂⟩ :=
        wfl_decChild exc v0 n ih u _ (subR ℓ) L₂ hL₂ hv2 (by omega)
      rw [hst1] at w₁
      rw [hst2] at w₂
      have e : off + servedK (stepKind exc off s).1 + servedK (stepKind exc off s).2 =
          off + servedC s.2 := by omega
      rw [e] at w₂
      refine ⟨L₁' ++ L₂', ?_, WFL.append (by omega) (by omega) w₁ w₂, ?_⟩
      · intro t ht
        rw [List.mem_append] at ht ⊢
        rcases ht with ht | ht
        · exact Or.inl (hsub₁ t ht)
        · exact Or.inr (hsub₂ t ht)
      · intro hall
        rw [hg₁ fun t ht => hall t (List.mem_append_left _ ht),
          hg₂ fun t ht => hall t (List.mem_append_right _ ht)]

/-! ### Lookups in the records -/

/-- The label a list of records prescribes at an address. -/
def recLab (L : List (Rec N')) (w : GWord N') : ℕ :=
  match L.find? (fun t => decide (t.1 = w)) with
  | some t => t.2.1
  | none => 0

/-- The arity a list of records prescribes at an address. -/
def recAr (L : List (Rec N')) (w : GWord N') : ℕ :=
  match L.find? (fun t => decide (t.1 = w)) with
  | some t => t.2.2
  | none => 0

lemma find?_eq_of_nodup : ∀ {L : List (Rec N')}, (L.map Prod.fst).Nodup →
    ∀ {t : Rec N'}, t ∈ L → L.find? (fun t' => decide (t'.1 = t.1)) = some t
  | [], _, _, ht => absurd ht List.not_mem_nil
  | t' :: L, hnd, t, ht => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rw [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact List.find?_cons_of_pos (by simp)
      · have hne : t'.1 ≠ t.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem ht)
        rw [List.find?_cons_of_neg (by simpa using hne)]
        exact find?_eq_of_nodup hnd.2 ht

lemma recLab_eq {L : List (Rec N')} (hnd : (L.map Prod.fst).Nodup) {t : Rec N'} (ht : t ∈ L) :
    recLab L t.1 = t.2.1 := by
  rw [recLab, find?_eq_of_nodup hnd ht]

lemma recAr_eq {L : List (Rec N')} (hnd : (L.map Prod.fst).Nodup) {t : Rec N'} (ht : t ∈ L) :
    recAr L t.1 = t.2.2 := by
  rw [recAr, find?_eq_of_nodup hnd ht]

lemma mem_toFinset_map_fst {L : List (Rec N')} {w : GWord N'} :
    w ∈ (L.map Prod.fst).toFinset ↔ ∃ t ∈ L, t.1 = w := by
  rw [List.mem_toFinset, List.mem_map]

/-- The records are realised exactly when the fields take the prescribed values on the
probe. -/
lemma levent_iff_probe {L : List (Rec N')} (hnd : (L.map Prod.fst).Nodup)
    (lab ar : GWord N' → ℕ) :
    Levent L lab ar ↔
      ∀ w ∈ (L.map Prod.fst).toFinset, lab w = recLab L w ∧ ar w = recAr L w := by
  constructor
  · intro h w hw
    obtain ⟨t, ht, rfl⟩ := mem_toFinset_map_fst.mp hw
    rw [recLab_eq hnd ht, recAr_eq hnd ht]
    exact h t ht
  · intro h t ht
    have := h t.1 (mem_toFinset_map_fst.mpr ⟨t, ht, rfl⟩)
    rw [recLab_eq hnd ht, recAr_eq hnd ht] at this
    exact this

/-- The mass of the records as a product over the probe. -/
lemma recMass_eq_prod (μ ν : PMF ℕ) {L : List (Rec N')} (hnd : (L.map Prod.fst).Nodup) :
    recMass μ ν L = ∏ w ∈ (L.map Prod.fst).toFinset, μ (recLab L w) * ν (recAr L w) := by
  rw [List.prod_toFinset _ hnd, List.map_map, recMass]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  simp only [Function.comp]
  rw [recLab_eq hnd ht, recAr_eq hnd ht]

/-! ### The probe at the root -/

/-- The data of a decoding at the root: the root record heads the list, and the rest
contains a well-formed sublist below the root serving the root's arity, the whole rest
when the sublist has its arities in the letter range. -/
lemma decTop_some {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (v0 n : ℕ)
    (ℓ : FullLab (CState ℕ) n) {L : List (Rec N')} (hL : decTop exc v0 n ℓ = some L) :
    ∃ (a k : ℕ) (L₀ : List (Rec N')), rootLab n ℓ = (a, CtrC.ord k) ∧
      L = ([], a, k) :: L₀ ∧ (2 ≤ k ∧ k ≤ N' → ∃ L₀' : List (Rec N'),
        (∀ t ∈ L₀', t ∈ L₀) ∧ WFL [] 0 k L₀' ∧ ((∀ t ∈ L₀', GoodRec N' t) → L₀' = L₀)) := by
  rcases hr : rootLab n ℓ with ⟨a, c⟩
  cases c with
  | ord k =>
      rw [decTop_ord exc v0 n ℓ hr] at hL
      obtain ⟨L₀, hL₀, rfl⟩ := Option.map_eq_some_iff.mp hL
      refine ⟨a, k, L₀, rfl, rfl, fun hk => ?_⟩
      have := wfl_dec hexc v0 n [] 0 (a, CtrC.ord k) ℓ L₀ hL₀ (by simpa [validS] using hk.1)
        (by simpa [servedC] using hk.2)
      simpa [servedC] using this
  | mark a' b' i' =>
      rw [decTop_mark exc v0 n ℓ hr] at hL
      exact (Option.some_ne_none L hL.symm).elim

lemma nil_not_mem_of_wfl {k : ℕ} {L₀ : List (Rec N')} (w : WFL [] 0 k L₀) :
    ([] : GWord N') ∉ L₀.map Prod.fst := by
  intro h
  obtain ⟨t, ht, e⟩ := List.mem_map.mp h
  obtain ⟨j, -, -, hj, hpre⟩ := w.below t ht
  rw [e] at hpre
  have := hpre.length_le
  rw [length_gChild _ hj] at this
  simp at this

/-- The probe of a root decoding has distinct addresses. -/
lemma nodup_of_wfl {a k : ℕ} {L₀ : List (Rec N')} (w : WFL [] 0 k L₀) :
    ((([], a, k) :: L₀).map Prod.fst).Nodup := by
  rw [List.map_cons, List.nodup_cons]
  exact ⟨nil_not_mem_of_wfl w, w.nodup⟩

/-- **The probe is prefix-closed.** -/
lemma prefixClosed_of_wfl {a k : ℕ} {L₀ : List (Rec N')} (w : WFL [] 0 k L₀) :
    ∀ u ∈ ((([], a, k) :: L₀).map Prod.fst).toFinset, ∀ p : GWord N', p <+: u →
      p ∈ ((([], a, k) :: L₀).map Prod.fst).toFinset := by
  suffices h : ∀ (m : ℕ) (u : GWord N'), u.length ≤ m →
      u ∈ ((([], a, k) :: L₀).map Prod.fst).toFinset → ∀ p : GWord N', p <+: u →
        p ∈ ((([], a, k) :: L₀).map Prod.fst).toFinset from
    fun u hu p hp => h u.length u le_rfl hu p hp
  intro m
  induction m with
  | zero =>
      intro u hu _ p hp
      have : u = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hu)
      subst this
      rw [List.prefix_nil] at hp
      subst hp
      exact List.mem_toFinset.mpr (List.mem_map_of_mem List.mem_cons_self)
  | succ m ih =>
      intro u hu hmem p hp
      obtain ⟨t, ht, rfl⟩ := mem_toFinset_map_fst.mp hmem
      rw [List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp only at hp
        rw [List.prefix_nil] at hp
        subst hp
        exact hmem
      · rcases w.closed t ht with ⟨j, hj, h⟩ | ⟨t', ht', j, hj, -, h⟩
        · have ht1 : t.1 = [⟨j, hj⟩] := by rw [h, gChild_of_lt _ hj, List.nil_append]
          rw [ht1] at hp hmem
          rw [List.prefix_cons_iff] at hp
          rcases hp with rfl | ⟨q, rfl, hq⟩
          · exact List.mem_toFinset.mpr (List.mem_map_of_mem List.mem_cons_self)
          · rw [List.prefix_nil] at hq
            subst hq
            exact hmem
        · have ht1 : t.1 = t'.1 ++ [⟨j, hj⟩] := by rw [h, gChild_of_lt _ hj]
          rw [ht1] at hp hmem hu
          rw [List.prefix_concat_iff] at hp
          rcases hp with rfl | hp
          · exact hmem
          · have hlen : t'.1.length ≤ m := by
              rw [List.length_append, List.length_singleton] at hu
              omega
            exact ih t'.1 hlen (mem_toFinset_map_fst.mpr ⟨t', List.mem_cons_of_mem _ ht', rfl⟩)
              p hp

/-- **The probe respects the arities**: a child `u ++ [i]` in the probe has `i` below the
arity recorded at `u`. -/
lemma compat_of_wfl {a k : ℕ} {L₀ : List (Rec N')} (w : WFL [] 0 k L₀) :
    ∀ u ∈ ((([], a, k) :: L₀).map Prod.fst).toFinset, ∀ i : Fin N',
      u ++ [i] ∈ ((([], a, k) :: L₀).map Prod.fst).toFinset →
        (i : ℕ) < recAr (([], a, k) :: L₀) u := by
  have hnd := nodup_of_wfl (a := a) w
  have hk0 : recAr (([], a, k) :: L₀) [] = k := by
    have := recAr_eq hnd (t := ([], a, k)) List.mem_cons_self
    simpa using this
  intro u _ i hmem
  obtain ⟨t, ht, e⟩ := mem_toFinset_map_fst.mp hmem
  rw [List.mem_cons] at ht
  rcases ht with rfl | ht
  · exact absurd e (by simp)
  · rcases w.closed t ht with ⟨j, hj, h⟩ | ⟨t', ht', j, hj, hlt, h⟩
    · obtain ⟨j', -, hj'k, hj', hpre⟩ := w.below t ht
      rw [h] at hpre
      have hjj := eq_of_gChild_prefix [] hj' hj hpre
      rw [h, gChild_of_lt _ hj, List.nil_append] at e
      have hu : u = [] := by
        have := congrArg List.length e
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        exact List.length_eq_zero_iff.mp (by omega)
      subst hu
      rw [List.nil_append, List.cons.injEq] at e
      have hi : (i : ℕ) = j := by rw [← e.1]
      rw [hi, hk0]
      omega
    · rw [h, gChild_of_lt _ hj] at e
      obtain ⟨hu, hi⟩ := List.append_inj' e rfl
      rw [List.cons.injEq] at hi
      have hi' : (i : ℕ) = j := by rw [← hi.1]
      rw [← hu, hi', recAr_eq hnd (List.mem_cons_of_mem _ ht')]
      exact hlt

/-! ### The projective identification from a product formula -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that two fields realise a list of records is measurable once the fibres of
the fields are. -/
lemma measurableSet_levent_of {lab ar : Ω → GWord N' → ℕ}
    (hlab : ∀ w a, MeasurableSet {ω | lab ω w = a})
    (har : ∀ w k, MeasurableSet {ω | ar ω w = k}) (L : List (Rec N')) :
    MeasurableSet {ω | Levent L (lab ω) (ar ω)} := by
  have hset : {ω | Levent L (lab ω) (ar ω)}
      = ⋂ t ∈ L, ({ω | lab ω t.1 = t.2.1} ∩ {ω | ar ω t.1 = t.2.2}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, Levent]
  rw [hset]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
    (hlab t.1 t.2.1).inter (har t.1 t.2.2)

/-- The encoded label field is measurable once the fibres of the fields are. -/
lemma measurable_encLab_of {lab ar : Ω → GWord N' → ℕ}
    (hlab : ∀ w a, MeasurableSet {ω | lab ω w = a})
    (har : ∀ w k, MeasurableSet {ω | ar ω w = k}) (exc : ℕ → Option (ℕ × ℕ)) (v0 n : ℕ) :
    Measurable fun ω => encLab exc (lab ω) (ar ω) v0 n := by
  refine measurable_to_countable' fun ℓ => ?_
  rcases hdec : decTop exc v0 n ℓ with _ | L
  · have hset : (fun ω => encLab exc (lab ω) (ar ω) v0 n) ⁻¹' {ℓ} = ∅ := by
      ext ω
      rw [Set.mem_preimage, Set.mem_singleton_iff, encLab_eq_iff, hdec]
      simp
    rw [hset]
    exact MeasurableSet.empty
  · have hset : (fun ω => encLab exc (lab ω) (ar ω) v0 n) ⁻¹' {ℓ}
        = {ω | Levent L (lab ω) (ar ω)} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, encLab_eq_iff, hdec,
        Option.some.injEq, exists_eq_left']
    rw [hset]
    exact measurableSet_levent_of hlab har L

/-- **The projective identification from a product formula, at one labelling**: if the
pairs of a label and an arity are i.i.d. with the product law `μ ⊗ ν` over every
prefix-closed probe respecting the prescribed arities, and `ν` is supported in the letter
range, then the mass of a labelling of `𝔹_n` under the encoded label field is its mass
under the composite process law.  The decoded records of a labelling contain a well-formed
sublist; when every record of the sublist has its arity in the letter range, the sublist
is the whole list and the product formula over its probe is the record mass, and
otherwise a record with an arity off the support of `ν` makes both sides vanish. -/
theorem encLab_apply_of_pattern (P : Measure Ω) {lab ar : Ω → GWord N' → ℕ} (μ ν : PMF ℕ)
    (hpat : ∀ F : Finset (GWord N'), (∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F) →
      ∀ a k : GWord N' → ℕ, (∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) →
        P (⋂ u ∈ F, ({ω | lab ω u = a u} ∩ {ω | ar ω u = k u})) = ∏ u ∈ F, μ (a u) * ν (k u))
    (hsupp : ∀ k, ν k ≠ 0 → 2 ≤ k ∧ k ≤ N') {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc)
    (v0 n : ℕ) (ℓ : FullLab (CState ℕ) n) :
    P {ω | encLab exc (lab ω) (ar ω) v0 n = ℓ} = cT exc μ ν v0 n ℓ := by
  rw [cT_eq_recMass]
  rcases hdec : decTop exc v0 n ℓ with _ | L
  · have hset : {ω | encLab exc (lab ω) (ar ω) v0 n = ℓ} = ∅ := by
      ext ω
      rw [Set.mem_setOf_eq, encLab_eq_iff, hdec]
      simp
    rw [hset, measure_empty]
    rfl
  · have hset : {ω | encLab exc (lab ω) (ar ω) v0 n = ℓ} = {ω | Levent L (lab ω) (ar ω)} := by
      ext ω
      simp only [Set.mem_setOf_eq, encLab_eq_iff, hdec, Option.some.injEq, exists_eq_left']
    rw [hset]
    obtain ⟨a, k, L₀, hr, rfl, hwf⟩ := decTop_some hexc v0 n ℓ hdec
    -- the product formula over the probe of a well-formed list
    have hprobe : ∀ L₁ : List (Rec N'), WFL [] 0 k L₁ →
        P {ω | Levent (([], a, k) :: L₁) (lab ω) (ar ω)}
          = ∏ u ∈ ((([], a, k) :: L₁).map Prod.fst).toFinset,
              μ (recLab (([], a, k) :: L₁) u) * ν (recAr (([], a, k) :: L₁) u) := by
      intro L₁ hw
      have hnd := nodup_of_wfl (a := a) hw
      have hset' : {ω | Levent (([], a, k) :: L₁) (lab ω) (ar ω)}
          = ⋂ u ∈ ((([], a, k) :: L₁).map Prod.fst).toFinset,
              ({ω | lab ω u = recLab (([], a, k) :: L₁) u}
                ∩ {ω | ar ω u = recAr (([], a, k) :: L₁) u}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
        exact levent_iff_probe hnd _ _
      rw [hset']
      exact hpat _ (prefixClosed_of_wfl hw) _ _ (compat_of_wfl hw)
    by_cases hk : 2 ≤ k ∧ k ≤ N'
    · obtain ⟨L₀', hsub, hw, hgood⟩ := hwf hk
      have hnd := nodup_of_wfl (a := a) hw
      have hev : ∀ ω, Levent (([], a, k) :: L₀) (lab ω) (ar ω) →
          Levent (([], a, k) :: L₀') (lab ω) (ar ω) := by
        intro ω hω t ht
        rw [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hω _ List.mem_cons_self
        · exact hω t (List.mem_cons_of_mem _ (hsub t ht))
      by_cases hall : ∀ t ∈ L₀', GoodRec N' t
      · have hL₀ : L₀' = L₀ := hgood hall
        subst hL₀
        rw [hprobe L₀' hw, optMass, recMass_eq_prod μ ν hnd]
      · simp only [not_forall] at hall
        obtain ⟨t, ht, hbad⟩ := hall
        have hν : ν t.2.2 = 0 := by
          by_contra h
          exact hbad (hsupp _ h)
        have hz : optMass μ ν (some (([], a, k) :: L₀)) = 0 := by
          simp only [optMass, recMass]
          apply List.prod_eq_zero
          rw [List.mem_map]
          exact ⟨t, List.mem_cons_of_mem _ (hsub t ht), by rw [hν, mul_zero]⟩
        rw [hz]
        refine measure_mono_null (t := {ω | Levent (([], a, k) :: L₀') (lab ω) (ar ω)})
          (fun ω hω => hev ω hω) ?_
        rw [hprobe L₀' hw]
        refine Finset.prod_eq_zero (i := t.1)
          (mem_toFinset_map_fst.mpr ⟨t, List.mem_cons_of_mem _ ht, rfl⟩) ?_
        rw [recAr_eq hnd (List.mem_cons_of_mem _ ht), hν, mul_zero]
    · have hν : ν k = 0 := by
        by_contra h
        exact hk (hsupp _ h)
      have hz : optMass μ ν (some (([], a, k) :: L₀)) = 0 := by
        simp only [optMass, recMass, List.map_cons, List.prod_cons]
        rw [hν, mul_zero, zero_mul]
      rw [hz]
      refine measure_mono_null (t := {ω | lab ω [] = a} ∩ {ω | ar ω [] = k})
        (fun ω hω => hω _ List.mem_cons_self) ?_
      have h := hpat {[]} (by simp) (fun _ => a) (fun _ => k) (by simp)
      simp only [Finset.set_biInter_singleton, Finset.prod_singleton] at h
      rw [h, hν, mul_zero]

/-- **The projective identification from a product formula**: the law of the encoded
label field at height `n` is the composite process law `cT` at height `n`. -/
theorem map_encLab_of_pattern (P : Measure Ω) {lab ar : Ω → GWord N' → ℕ}
    (hlab : ∀ w a, MeasurableSet {ω | lab ω w = a})
    (har : ∀ w k, MeasurableSet {ω | ar ω w = k}) (μ ν : PMF ℕ)
    (hpat : ∀ F : Finset (GWord N'), (∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F) →
      ∀ a k : GWord N' → ℕ, (∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) →
        P (⋂ u ∈ F, ({ω | lab ω u = a u} ∩ {ω | ar ω u = k u})) = ∏ u ∈ F, μ (a u) * ν (k u))
    (hsupp : ∀ k, ν k ≠ 0 → 2 ≤ k ∧ k ≤ N') {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc)
    (v0 n : ℕ) :
    P.map (fun ω => encLab exc (lab ω) (ar ω) v0 n) = (cT exc μ ν v0 n).toMeasure := by
  refine Measure.ext_of_singleton fun ℓ => ?_
  rw [Measure.map_apply (measurable_encLab_of hlab har exc v0 n) (measurableSet_singleton ℓ),
    PMF.toMeasure_apply_singleton _ ℓ (measurableSet_singleton ℓ)]
  have hset : (fun ω => encLab exc (lab ω) (ar ω) v0 n) ⁻¹' {ℓ}
      = {ω | encLab exc (lab ω) (ar ω) v0 n = ℓ} := by
    ext ω
    simp
  rw [hset]
  exact encLab_apply_of_pattern P μ ν hpat hsupp hexc v0 n ℓ

end Generic

/-! ### The reduced law and the class law as probability laws -/

variable {J N J' : ℕ}

lemma reducedWeight_nonneg (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (κ : ℕ) : 0 ≤ reducedWeight θ' κ := by
  rw [reducedWeight_def]
  exact div_nonneg (θ'.skeletonWeight_nonneg hq' κ) (by linarith)

/-- The reduced weights sum to one over the arities at least `2`. -/
lemma sum_reducedWeight (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') :
    ∑ κ ∈ Finset.range (J' + 1), (if 2 ≤ κ then reducedWeight θ' κ else 0) = 1 := by
  have hsum := θ'.sum_skeletonWeight hq'
  have hJ : J' + 1 = (J' - 1) + 1 + 1 := by omega
  rw [hJ, Finset.sum_range_succ', Finset.sum_range_succ'] at hsum ⊢
  rw [θ'.skeletonWeight_zero] at hsum
  have e1 : ∀ i ∈ Finset.range (J' - 1),
      (if 2 ≤ i + 1 + 1 then reducedWeight θ' (i + 1 + 1) else 0)
        = θ'.skeletonWeight (i + 1 + 1) / (1 - θ'.skeletonWeight 1) := fun i _ => by
    rw [if_pos (by omega), reducedWeight_def]
  have h1 : 0 < 1 - θ'.skeletonWeight 1 := by linarith
  rw [Finset.sum_congr rfl e1, if_neg (by norm_num), if_neg (by norm_num), add_zero, add_zero,
    ← Finset.sum_div, div_eq_one_iff_eq h1.ne']
  linarith

/-- **The reduced law `ν̃` as a probability law on `ℕ`**: the weight `ν̃_κ` at every arity
`κ ≥ 2`, which vanishes above `J'`. -/
noncomputable def reducedPMF (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') : PMF ℕ :=
  PMF.ofFinset (fun κ => if 2 ≤ κ then ENNReal.ofReal (reducedWeight θ' κ) else 0)
    (Finset.range (J' + 1))
    (by
      have h := sum_reducedWeight θ' hq' hs1' hJ2'
      have e : ∀ κ, (if 2 ≤ κ then ENNReal.ofReal (reducedWeight θ' κ) else 0)
          = ENNReal.ofReal (if 2 ≤ κ then reducedWeight θ' κ else 0) := fun κ => by
        split_ifs <;> simp
      simp_rw [e]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun κ _ => ?_), h, ENNReal.ofReal_one]
      split_ifs
      · exact reducedWeight_nonneg θ' hq' hs1' κ
      · exact le_rfl)
    (by
      intro κ hκ
      rw [Finset.mem_range, not_lt] at hκ
      split_ifs with h2
      · rw [reducedWeight_eq_zero_of_gt θ' (by omega), ENNReal.ofReal_zero]
      · rfl)

lemma reducedPMF_apply (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') (κ : ℕ) :
    reducedPMF θ' hq' hs1' hJ2' κ = if 2 ≤ κ then ENNReal.ofReal (reducedWeight θ' κ) else 0 :=
  PMF.ofFinset_apply _ _ κ

lemma reducedPMF_of_le (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') {κ : ℕ} (hκ : 2 ≤ κ) :
    reducedPMF θ' hq' hs1' hJ2' κ = ENNReal.ofReal (reducedWeight θ' κ) := by
  rw [reducedPMF_apply, if_pos hκ]

lemma reducedPMF_eq_zero (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') {κ : ℕ} (hκ : ¬ (2 ≤ κ ∧ κ ≤ J')) :
    reducedPMF θ' hq' hs1' hJ2' κ = 0 := by
  rw [reducedPMF_apply]
  split_ifs with h2
  · rw [reducedWeight_eq_zero_of_gt θ' (by omega), ENNReal.ofReal_zero]
  · rfl

/-- **The support of the reduced law** is `{2, …, J'}` (`thm:full-support`). -/
lemma reducedPMF_ne_zero_iff (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') (κ : ℕ) :
    reducedPMF θ' hq' hs1' hJ2' κ ≠ 0 ↔ 2 ≤ κ ∧ κ ≤ J' := by
  constructor
  · intro h
    by_contra hκ
    exact h (reducedPMF_eq_zero θ' hq' hs1' hJ2' hκ)
  · intro hκ
    rw [reducedPMF_of_le θ' hq' hs1' hJ2' hκ.1]
    exact (ENNReal.ofReal_pos.mpr (reducedWeight_pos θ' hq' hq0' hJ2' hθJ' hκ.1 hκ.2)).ne'

/-- The mass of a class is the class law. -/
lemma gClassMass_eq_gClassPMF (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) (D : ℝ) (a : ℕ) :
    gClassMass (N := N) θ D a = gClassPMF θ hJN hq hq0 hs1 D a := by
  rw [gClassMass_eq_tsum_ite, gClassPMF_eq_tsum]
  rfl

/-! ### Arities at compatible addresses -/

/-- An address is compatible with a sample when every letter on the way lies below the
arity of its parent. -/
def GCompat (c : GWord N' → ℕ) : GWord N' → Prop
  | [] => True
  | i :: u => (i : ℕ) < gArity c ∧ GCompat (gSplitBush c (i : ℕ)) u

/-- Compatibility in terms of the arity field: every letter of the address lies below the
arity at its parent. -/
lemma gCompat_iff : ∀ (w : GWord N') (c : GWord N' → ℕ), GCompat c w ↔
    ∀ (p : GWord N') (i : Fin N'), p ++ [i] <+: w → (i : ℕ) < gArityAt c p
  | [], c => by
      simp only [GCompat, true_iff]
      intro p i h
      rw [List.prefix_nil] at h
      exact absurd h (by simp)
  | i :: w, c => by
      simp only [GCompat]
      constructor
      · rintro ⟨h1, h2⟩ p i' hpi
        cases p with
        | nil =>
            rw [List.nil_append, List.cons_prefix_cons] at hpi
            rw [hpi.1, gArityAt_nil]
            exact h1
        | cons i'' p' =>
            rw [List.cons_append, List.cons_prefix_cons] at hpi
            rw [hpi.1, gArityAt_cons]
            exact (gCompat_iff w (gSplitBush c (i : ℕ))).mp h2 p' i' hpi.2
      · intro H
        refine ⟨?_, ?_⟩
        · have := H [] i (by simp)
          rwa [gArityAt_nil] at this
        · refine (gCompat_iff w (gSplitBush c (i : ℕ))).mpr fun p' i' hpi => ?_
          have := H (i :: p') i' (by rw [List.cons_append]; exact List.cons_prefix_cons.mpr ⟨rfl, hpi⟩)
          rwa [gArityAt_cons] at this

lemma measurableSet_gCompat : ∀ w : GWord N', MeasurableSet {c : GWord N' → ℕ | GCompat c w}
  | [] => by
      have : {c : GWord N' → ℕ | GCompat c []} = Set.univ := by
        ext c
        simp [GCompat]
      rw [this]
      exact MeasurableSet.univ
  | i :: w => by
      have : {c : GWord N' → ℕ | GCompat c (i :: w)}
          = {c : GWord N' → ℕ | gArity c ∈ {k : ℕ | (i : ℕ) < k}}
            ∩ (fun c : GWord N' → ℕ => gSplitBush c (i : ℕ)) ⁻¹' {d | GCompat d w} := by
        ext c
        simp [GCompat]
      rw [this]
      exact (fibreMeasurableG_gArity.preimage _).inter
        (measurable_gSplitBush (i : ℕ) (measurableSet_gCompat w))

/-- The arity at the root lies in the reduced support almost surely. -/
lemma survivalMeasure_gArity_bad_null (θ' : Offspring J') (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') :
    survivalMeasure (N := N') θ' {c : GWord N' → ℕ | ¬ (2 ≤ gArity c ∧ gArity c ≤ J')} = 0 := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  have h1 : survivalMeasure (N := N') θ' {c : GWord N' → ℕ | 2 ≤ gArity c}ᶜ = 0 :=
    (prob_compl_eq_zero_iff (fibreMeasurableG_gArity.preimage {k : ℕ | 2 ≤ k})).mpr
      (survivalMeasure_two_le_gArity θ' hJN' hq' hs1')
  have h2 : survivalMeasure (N := N') θ'
      (⋃ j : ℕ, {c : GWord N' → ℕ | gArity c = J' + 1 + j}) = 0 := by
    refine measure_iUnion_null fun j => ?_
    rw [survivalMeasure_gArity_eq θ' hJN' hq' hs1' (by omega),
      reducedWeight_eq_zero_of_gt θ' (by omega), ENNReal.ofReal_zero]
  refine measure_mono_null (fun c hc => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_setOf_eq] at hc
  by_cases h2' : 2 ≤ gArity c
  · right
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨gArity c - J' - 1, by omega⟩
  · left
    exact h2'

/-- **The arities at compatible addresses lie in the reduced support almost surely.** -/
theorem survivalMeasure_compat_bad_null (θ' : Offspring J') (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') :
    ∀ w : GWord N', survivalMeasure (N := N') θ'
      {c : GWord N' → ℕ | GCompat c w ∧ ¬ (2 ≤ gArityAt c w ∧ gArityAt c w ≤ J')} = 0 := by
  have hroot := survivalMeasure_gArity_bad_null θ' hJN' hq' hs1' hJ2'
  intro w
  induction w with
  | nil =>
      simpa [GCompat] using hroot
  | cons i w ih =>
      set S : Set (GWord N' → ℕ) :=
        {d | GCompat d w ∧ ¬ (2 ≤ gArityAt d w ∧ gArityAt d w ≤ J')} with hS
      have hSm : MeasurableSet S := (measurableSet_gCompat w).inter
        ((fibreMeasurableG_gArityAt w).preimage {k : ℕ | ¬ (2 ≤ k ∧ k ≤ J')})
      set A : ℕ → Set (GWord N' → ℕ) := fun m => if m = (i : ℕ) then S else Set.univ with hA
      have hAm : ∀ m, MeasurableSet (A m) := fun m => by
        simp only [hA]
        split_ifs
        · exact hSm
        · exact MeasurableSet.univ
      set B : ℕ → Set (GWord N' → ℕ) := fun κ =>
        if (i : ℕ) < κ then {c : GWord N' → ℕ | gArity c = κ}
          ∩ {c : GWord N' → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m} else ∅ with hB
      have hBnull : ∀ κ, survivalMeasure (N := N') θ' (B κ) = 0 := by
        intro κ
        simp only [hB]
        split_ifs with hiκ
        · by_cases hκ2 : 2 ≤ κ
          · rw [survivalMeasure_gArityPair θ' hJN' hq' hs1' hκ2 hAm,
              Finset.prod_eq_zero (Finset.mem_range.mpr hiκ) (by
                simp only [hA, if_pos rfl]
                exact ih), mul_zero]
          · refine measure_mono_null (fun c hc => ?_) hroot
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hc ⊢
            omega
        · exact measure_empty
      refine measure_mono_null (fun c hc => ?_) (measure_iUnion_null hBnull)
      simp only [Set.mem_setOf_eq, GCompat, gArityAt_cons] at hc
      obtain ⟨⟨hi, hcomp⟩, hbad⟩ := hc
      simp only [Set.mem_iUnion]
      refine ⟨gArity c, ?_⟩
      simp only [hB, if_pos hi, Set.mem_inter_iff, Set.mem_setOf_eq]
      refine ⟨by trivial, fun m _ => ?_⟩
      simp only [hA]
      split_ifs with hmi
      · subst hmi
        exact ⟨hcomp, hbad⟩
      · exact Set.mem_univ _

/-- The same on the labelled space. -/
lemma labelMeasure_compat_bad_null (θ' : Offspring J') (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') (w : GWord N') :
    labelMeasure θ' {ω : (GWord N' → ℕ) × (GWord N' → ℝ) |
      GCompat ω.1 w ∧ ¬ (2 ≤ gArityAt ω.1 w ∧ gArityAt ω.1 w ≤ J')} = 0 := by
  have hset : {ω : (GWord N' → ℕ) × (GWord N' → ℝ) |
        GCompat ω.1 w ∧ ¬ (2 ≤ gArityAt ω.1 w ∧ gArityAt ω.1 w ≤ J')}
      = {c : GWord N' → ℕ | GCompat c w ∧ ¬ (2 ≤ gArityAt c w ∧ gArityAt c w ≤ J')}
          ×ˢ (Set.univ : Set (GWord N' → ℝ)) := by
    ext ω
    simp
  rw [hset, labelMeasure, Measure.prod_prod,
    survivalMeasure_compat_bad_null θ' hJN' hq' hs1' hJ2' w, zero_mul]

/-! ### The projective identification -/

/-- **The encoded label field is measurable.** -/
lemma measurable_encLab (D : ℝ) {θ' : Offspring J'} (π : GCouplings θ')
    (exc : ℕ → Option (ℕ × ℕ)) (v0 n : ℕ) :
    Measurable fun ω : (GWord N' → ℕ) × (GWord N' → ℝ) =>
      encLab exc (gLab D π ω) (gArityAt ω.1) v0 n :=
  measurable_encLab_of (fun w a => measurableSet_gLab_fibre D π w a)
    (fun w k => measurable_fst (fibreMeasurableG_gArityAt w k)) exc v0 n

/-- **The product formula of `thm:hairy-general`, unconstrained**: over every prefix-closed
probe respecting the prescribed arities, the pairs of a label and an arity are i.i.d. with
the product law `μ_D ⊗ ν̃`, with no condition on the prescribed arities: a prescribed
arity off the reduced support makes both sides vanish, the event lying in the null set
of `labelMeasure_compat_bad_null`. -/
theorem labelMeasure_label_pattern' (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν))
    (F : Finset (GWord N')) (hpc : ∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F)
    (a k : GWord N' → ℕ) (hcomp : ∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) :
    labelMeasure θ'
        (⋂ u ∈ F, ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω u = a u}
          ∩ {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 u = k u}))
      = ∏ u ∈ F, gClassPMF θ hJN hq hq0 hs1 D (a u) * reducedPMF θ' hq' hs1' hJ2' (k u) := by
  by_cases hall : ∀ u ∈ F, 2 ≤ k u ∧ k u ≤ J'
  · rw [labelMeasure_label_pattern θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1' hJ2' hθJ' π hπ F hpc
      a k (fun u hu => (hall u hu).1) (fun u hu => (hall u hu).2) hcomp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [gClassMass_eq_gClassPMF, reducedPMF_of_le θ' hq' hs1' hJ2' (hall u hu).1]
  · simp only [not_forall] at hall
    obtain ⟨t, ht, hbad⟩ := hall
    rw [Finset.prod_eq_zero ht (by rw [reducedPMF_eq_zero θ' hq' hs1' hJ2' hbad, mul_zero])]
    refine measure_mono_null ?_ (labelMeasure_compat_bad_null θ' hJN' hq' hs1' hJ2' t)
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hω
    refine ⟨?_, ?_⟩
    · rw [gCompat_iff]
      intro p i hpi
      have hmem : p ++ [i] ∈ F := hpc t ht _ hpi
      have hp : p ∈ F := hpc _ hmem p (List.prefix_append _ _)
      rw [(hω p hp).2]
      exact hcomp p hp i hmem
    · rw [(hω t ht).2]
      exact hbad

/-- **The projective identification, at one labelling**: the mass of a labelling of
`𝔹_n` under the encoded label field is its mass under the composite process law with the
class law `μ_D` and the reduced law `ν̃` (`thm:hairy-general`, the identification with the
engine's process), by `encLab_apply_of_pattern` at the unconstrained product formula. -/
theorem labelMeasure_encLab_apply (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν))
    {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (v0 n : ℕ) (ℓ : FullLab (CState ℕ) n) :
    labelMeasure θ' {ω : (GWord N' → ℕ) × (GWord N' → ℝ) |
        encLab exc (gLab D π ω) (gArityAt ω.1) v0 n = ℓ}
      = cT exc (gClassPMF θ hJN hq hq0 hs1 D) (reducedPMF θ' hq' hs1' hJ2') v0 n ℓ :=
  encLab_apply_of_pattern (labelMeasure θ') (gClassPMF θ hJN hq hq0 hs1 D)
    (reducedPMF θ' hq' hs1' hJ2')
    (fun F hpc a k hcomp => labelMeasure_label_pattern' θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1'
      hJ2' hθJ' π hπ F hpc a k hcomp)
    (fun k hk => by
      have := (reducedPMF_ne_zero_iff θ' hq' hq0' hs1' hJ2' hθJ' k).mp hk
      exact ⟨this.1, this.2.trans hJN'⟩)
    hexc v0 n ℓ

/-- **The projective identification** (`thm:hairy-general`, the identification with the
engine's process): the law of the encoded label field at height `n` is the composite
process law `cT` with the class law `μ_D` and the reduced law `ν̃`. -/
theorem labelMeasure_map_encLab (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν))
    {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (v0 n : ℕ) :
    (labelMeasure θ').map (fun ω : (GWord N' → ℕ) × (GWord N' → ℝ) =>
        encLab exc (gLab D π ω) (gArityAt ω.1) v0 n)
      = (cT exc (gClassPMF θ hJN hq hq0 hs1 D) (reducedPMF θ' hq' hs1' hJ2') v0 n).toMeasure :=
  map_encLab_of_pattern (labelMeasure θ') (fun w a => measurableSet_gLab_fibre D π w a)
    (fun w k => measurable_fst (fibreMeasurableG_gArityAt w k))
    (gClassPMF θ hJN hq hq0 hs1 D) (reducedPMF θ' hq' hs1' hJ2')
    (fun F hpc a k hcomp => labelMeasure_label_pattern' θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1'
      hJ2' hθJ' π hπ F hpc a k hcomp)
    (fun k hk => by
      have := (reducedPMF_ne_zero_iff θ' hq' hq0' hs1' hJ2' hθJ' k).mp hk
      exact ⟨this.1, this.2.trans hJN'⟩)
    hexc v0 n

/-! ### The matching step of `thm:hairy-general` -/

/-- **The two potentials agree**: the relation-based potential of the engine at the
compatibility relation of a label graph is the graph potential `η_{G,5/2}` of
`thm:matching`, the summands off the support vanishing on both sides. -/
lemma etaG_compat_eq {V : Type} (μ : PMF V) (G : SimpleGraph V) :
    GraphMarkovMatching.etaG (5 / 2) (GraphMatching.compat G) μ = GraphMatching.etaG μ G := by
  rw [GraphMatching.etaG_eq_etaGA, GraphMatching.etaGA_eq_PhiA, GraphMarkovMatching.etaG,
    GraphMarkovMatching.PhiD, GraphMatching.PhiA]
  refine tsum_congr fun x => ?_
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · have hq : GraphMarkovMatching.Support.q μ (GraphMatching.compat G) x < 1 :=
      GraphMarkovMatching.Support.q_lt_one (GraphMatching.compat_refl G x) hx
    rw [GraphMarkovMatching.phiE_of_lt hq]
    rfl

/-- **The chart of `thm:hairy-cross`**: the exceptional arities `z ∈ {J+1, …, J'}` carry
the composite pair `(z + 1 - J, J)`. -/
def bushyExc (J J' : ℕ) (z : ℕ) : Option (ℕ × ℕ) :=
  if J + 1 ≤ z ∧ z ≤ J' then some (z + 1 - J, J) else none

lemma bushyExc_eq_none_iff (J J' z : ℕ) : bushyExc J J' z = none ↔ ¬ (J + 1 ≤ z ∧ z ≤ J') := by
  unfold bushyExc
  split_ifs with h
  · exact ⟨fun e => e.elim, fun e => absurd h e⟩
  · exact ⟨fun _ => h, fun _ => rfl⟩

lemma bushyExc_eq_some_iff (J J' z : ℕ) (p : ℕ × ℕ) :
    bushyExc J J' z = some p ↔ (J + 1 ≤ z ∧ z ≤ J') ∧ p = (z + 1 - J, J) := by
  unfold bushyExc
  split_ifs with h
  · rw [Option.some.injEq]
    exact ⟨fun e => ⟨h, e.symm⟩, fun e => e.2.symm⟩
  · exact ⟨fun e => e.elim, fun e => absurd e.1 h⟩

/-- The chart is compatible with the arities. -/
lemma excCompat_bushyExc {J J' : ℕ} (hJ2 : 2 ≤ J) : ExcCompat (bushyExc J J') := by
  intro z p hp
  rw [bushyExc_eq_some_iff] at hp
  obtain ⟨⟨h1, h2⟩, rfl⟩ := hp
  simp only
  omega

/-- The empty chart is compatible. -/
lemma excCompat_none : ExcCompat (fun _ => (none : Option (ℕ × ℕ))) :=
  fun _ p h => (Option.some_ne_none p h.symm).elim

/-- **The two-sample space of `thm:hairy-general`**: two independent labelled samples. -/
noncomputable def twoLabelMeasure (θ : Offspring J) (θ' : Offspring J') :
    Measure (((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ))) :=
  (labelMeasure (N' := N) θ).prod (labelMeasure (N' := N') θ')

lemma isProbabilityMeasure_twoLabelMeasure (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1) :
    IsProbabilityMeasure (twoLabelMeasure (N := N) (N' := N') θ θ') := by
  have _ := isProbabilityMeasure_labelMeasure (N' := N) θ hJN hq
  have _ := isProbabilityMeasure_labelMeasure (N' := N') θ' hJN' hq'
  exact inferInstanceAs (IsProbabilityMeasure
    ((labelMeasure (N' := N) θ).prod (labelMeasure (N' := N') θ')))

/-- **The two-sample law at height `n`**: the pair of encoded label fields of two
independent labelled samples, both labelled through the one class law of `θ`, is
distributed as two independent composite samples, the `hlaw` hypothesis of
`thm:composite-matching`. -/
theorem twoLabelMeasure_map_encLab (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π₁ : GCouplings θ)
    (hπ₁ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ κ),
      IsGShapeCoupling D (gCondPMF θ hJN hq hq0 hs1 hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π₁ κ hκ hν))
    (π₂ : GCouplings θ')
    (hπ₂ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π₂ κ hκ hν))
    {exc1 exc2 : ℕ → Option (ℕ × ℕ)} (hexc1 : ExcCompat exc1) (hexc2 : ExcCompat exc2)
    (v0 n : ℕ) :
    (twoLabelMeasure (N := N) (N' := N') θ θ').map (fun ω =>
        (encLab exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) v0 n,
          encLab exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) v0 n))
      = (prodPMF (cT exc1 (gClassPMF θ hJN hq hq0 hs1 D) (reducedPMF θ hq hs1 hJ2) v0 n)
          (cT exc2 (gClassPMF θ hJN hq hq0 hs1 D) (reducedPMF θ' hq' hs1' hJ2') v0 n)).toMeasure := by
  have hmeas : Measurable fun ω :
      ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) =>
        (encLab exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) v0 n,
          encLab exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) v0 n) :=
    ((measurable_encLab D π₁ exc1 v0 n).comp measurable_fst).prodMk
      ((measurable_encLab D π₂ exc2 v0 n).comp measurable_snd)
  have _ := isProbabilityMeasure_labelMeasure (N' := N) θ hJN hq
  have _ := isProbabilityMeasure_labelMeasure (N' := N') θ' hJN' hq'
  refine Measure.ext_of_singleton fun z => ?_
  obtain ⟨x, y⟩ := z
  rw [Measure.map_apply hmeas (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    GraphMarkovMatching.Support.prodPMF_apply]
  have hpre : (fun ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) =>
        (encLab exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) v0 n,
          encLab exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) v0 n)) ⁻¹' {(x, y)}
      = {ω₁ : (GWord N → ℕ) × (GWord N → ℝ) |
            encLab exc1 (gLab D π₁ ω₁) (gArityAt ω₁.1) v0 n = x}
          ×ˢ {ω₂ : (GWord N' → ℕ) × (GWord N' → ℝ) |
            encLab exc2 (gLab D π₂ ω₂) (gArityAt ω₂.1) v0 n = y} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_setOf_eq,
      Prod.mk.injEq]
  rw [hpre, twoLabelMeasure, Measure.prod_prod,
    labelMeasure_encLab_apply θ hJN hq hq0 hs1 θ hJN hq hq0 hs1 hJ2 hθJ π₁ hπ₁ hexc1 v0 n x,
    labelMeasure_encLab_apply θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1' hJ2' hθJ' π₂ hπ₂ hexc2
      v0 n y]

/-- **`thm:hairy-general`, the matching step**: for two bushy laws with offspring bounds
`J ≤ J' ≤ 2J - 1`, past a threshold `D₆` depending on the two laws alone, two independent
samples labelled through the one class law `μ_D` of `θ` admit one automorphism of `𝔹`
matching their encoded label fields to within one class of `G_D` at every vertex, with
probability at least `1 - K e^{-cD²}`; the constants `K` and `c` depend on the two laws
alone, `K` being the constant `K_{\vec ν}` of `thm:composite-matching` at the chart of
`thm:hairy-cross` and `c` the rate of `thm:cross-relabel`. -/
theorem exists_engine_match (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hθJ' : 0 < θ' J')
    (hJJ' : J ≤ J') (hJ'2 : J' ≤ 2 * J - 1) :
    ∃ (D₆ : ℕ) (K c : ℝ), 0 < c ∧ ∀ D : ℕ, D₆ ≤ D →
      ∀ (π₁ : GCouplings θ)
        (_ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ κ),
          IsGShapeCoupling (D : ℝ) (gCondPMF θ hJN hq hq0 hs1 hκ hν) (gMixPMF θ hJN hq hq0 hs1)
            (π₁ κ hκ hν))
        (π₂ : GCouplings θ')
        (_ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
          IsGShapeCoupling (D : ℝ) (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν)
            (gMixPMF θ hJN hq hq0 hs1) (π₂ κ hκ hν)),
        1 - ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) ≤
          twoLabelMeasure (N := N) (N' := N') θ θ'
            {ω | GraphMarkovMatching.InfMatch (cRel (GraphMatching.compat (gNetGraph D)))
              (fun n => encLab (fun _ => none) (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
              (fun n => encLab (bushyExc J J') (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)} := by
  have hJ2' : 2 ≤ J' := le_trans hJ2 hJJ'
  -- the instance data of `thm:hairy-cross`
  set ν1 := reducedPMF θ hq hs1 hJ2 with hν1
  set ν2 := reducedPMF θ' hq' hs1' hJ2' with hν2
  set exc1 : ℕ → Option (ℕ × ℕ) := fun _ => none with hexc1
  set exc2 := bushyExc J J' with hexc2
  set K1 := Finset.Icc 2 J with hK1
  set K2 := Finset.Icc 2 J' with hK2
  set E2 := (Finset.Icc (J + 1) J').image fun z => (z + 1 - J, J) with hE2
  have hsup1 : ∀ k, ν1 k ≠ 0 ↔ k ∈ K1 := fun k => by
    rw [hν1, reducedPMF_ne_zero_iff θ hq hq0 hs1 hJ2 hθJ, hK1, Finset.mem_Icc]
  have hsup2 : ∀ k, ν2 k ≠ 0 ↔ k ∈ K2 := fun k => by
    rw [hν2, reducedPMF_ne_zero_iff θ' hq' hq0' hs1' hJ2' hθJ', hK2, Finset.mem_Icc]
  have hnone1 : ∀ k p, exc1 k = some p → False := fun _ p h => Option.some_ne_none p h.symm
  have hexc2some : ∀ k p, exc2 k = some p → (J + 1 ≤ k ∧ k ≤ J') ∧ p = (k + 1 - J, J) :=
    fun k p h => (bushyExc_eq_some_iff J J' k p).mp h
  have hexc2none : ∀ k, exc2 k = none ↔ ¬ (J + 1 ≤ k ∧ k ≤ J') :=
    fun k => bushyExc_eq_none_iff J J' k
  have hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0 :=
    fun k p h => (hnone1 k p h).elim
  have hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0 := by
    intro k p h
    obtain ⟨⟨h1, h2⟩, rfl⟩ := hexc2some k p h
    simp only
    rw [hsup2, hsup2, hK2, Finset.mem_Icc, Finset.mem_Icc]
    omega
  -- the constants
  have hKne : GraphMarkovMatching.Composite.compKcFinalM exc1 exc2 ν1 ν2 K1 K2 J ≠ ⊤ :=
    GraphMarkovMatching.Composite.compKcFinalM_ne_top exc1 exc2 ν1 ν2 K1 K2 J hsup1 hdecl1
      hsup2 hdecl2
  have hεpos : 0 < GraphMarkovMatching.Composite.compEtaStarM exc1 exc2 ν1 ν2 K1 K2 J :=
    GraphMarkovMatching.Composite.compEtaStarM_pos exc1 exc2 ν1 ν2 K1 K2 J hsup1 hdecl1
      hsup2 hdecl2
  have hεne : GraphMarkovMatching.Composite.compEtaStarM exc1 exc2 ν1 ν2 K1 K2 J ≠ ⊤ :=
    GraphMarkovMatching.Composite.compEtaStarM_ne_top exc1 exc2 ν1 ν2 K1 K2 J
  -- the potential of the class law
  obtain ⟨c, hc, D₀, hD₀⟩ := exists_etaG_gNetGraph_le θ hJN hq hq0 hs1 h0 hθJ hJ2
  obtain ⟨D₁, hD₁⟩ := exists_etaG_gNetGraph_le_ofReal θ hJN hq hq0 hs1 h0 hθJ hJ2
    (r := (GraphMarkovMatching.Composite.compEtaStarM exc1 exc2 ν1 ν2 K1 K2 J).toReal)
    (ENNReal.toReal_pos hεpos.ne' hεne)
  refine ⟨max D₀ D₁, (GraphMarkovMatching.Composite.compKcFinalM exc1 exc2 ν1 ν2 K1 K2 J).toReal,
    c, hc, fun D hD π₁ hπ₁ π₂ hπ₂ => ?_⟩
  obtain ⟨heta_exp, -⟩ := hD₀ D (le_trans (le_max_left _ _) hD)
  obtain ⟨-, heta_r, hhalf⟩ := hD₁ D (le_trans (le_max_right _ _) hD)
  set μ := gClassPMF θ hJN hq hq0 hs1 D with hμ
  set Rv := GraphMatching.compat (gNetGraph D) with hRvdef
  have _ := isProbabilityMeasure_twoLabelMeasure θ hJN hq θ' hJN' hq'
  have hhalf' : (2 : ℝ≥0∞)⁻¹ ≤ μ 0 := by rwa [one_div] at hhalf
  have hμ0 : μ 0 ≠ 0 := (lt_of_lt_of_le (by norm_num) hhalf').ne'
  -- the projective sample pack
  have hmain := GraphMarkovMatching.Composite.composite_matching_bound_massfree Rv μ 0
    exc1 exc2 ν1 ν2 K1 K2 K1 ∅ E2 J (twoLabelMeasure (N := N) (N' := N') θ θ')
    (GraphMatching.compat_refl _) (GraphMatching.compat_symm _) hμ0 hhalf'
    (fun j hj => ⟨rfl, (hexc2none j).mpr (by omega)⟩)
    (fun k p h => (hnone1 k p h).elim)
    (fun k hk _ => by
      rw [hsup1, hK1, Finset.mem_Icc] at hk
      rw [hsup2, hK2, Finset.mem_Icc]
      omega)
    (fun k p h => by
      obtain ⟨⟨h1, h2⟩, rfl⟩ := hexc2some k p h
      simp only
      rw [hsup1, hsup1, hK1, Finset.mem_Icc, Finset.mem_Icc]
      omega)
    (fun k hk hn => by
      rw [hsup2, hK2, Finset.mem_Icc] at hk
      rw [hexc2none] at hn
      rw [hsup1, hK1, Finset.mem_Icc]
      omega)
    (fun k p h => (hnone1 k p h).elim)
    (fun k p h j hj => by
      obtain ⟨⟨h1, h2⟩, rfl⟩ := hexc2some k p h
      simp only at hj
      exact (hexc2none j).mpr (by omega))
    hdecl1 hdecl2 hsup1 hsup2
    (fun k => ⟨fun hk => ⟨(hsup1 k).mpr hk, rfl⟩, fun h => (hsup1 k).mp h.1⟩)
    ⟨2, by rw [hK1, Finset.mem_Icc]; omega⟩
    (fun p => ⟨fun hp => absurd hp (Finset.notMem_empty p),
      fun ⟨z, _, hz⟩ => (hnone1 z p hz).elim⟩)
    (fun p => by
      rw [hE2, Finset.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [Finset.mem_Icc] at hz
        refine ⟨z, ?_, (bushyExc_eq_some_iff J J' z _).mpr ⟨hz, rfl⟩⟩
        rw [hsup2, hK2, Finset.mem_Icc]
        omega
      · rintro ⟨z, -, hz⟩
        obtain ⟨hz', rfl⟩ := hexc2some z p hz
        exact ⟨z, Finset.mem_Icc.mpr hz', rfl⟩)
    (by
      rw [hRvdef, etaG_compat_eq]
      exact heta_r.trans (le_of_eq (ENNReal.ofReal_toReal hεne)))
    (fun n ω => encLab exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
    (fun n ω => encLab exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)
    (fun n ω => restrictLab_encLab exc1 _ _ 0 n)
    (fun n ω => restrictLab_encLab exc2 _ _ 0 n)
    (fun n => ((measurable_encLab D π₁ exc1 0 n).comp measurable_fst).prodMk
      ((measurable_encLab D π₂ exc2 0 n).comp measurable_snd))
    (fun n => twoLabelMeasure_map_encLab θ hJN hq hq0 hs1 hJ2 hθJ θ' hJN' hq' hq0' hs1' hJ2'
      hθJ' π₁ hπ₁ π₂ hπ₂ excCompat_none (excCompat_bushyExc hJ2) 0 n)
  refine le_trans ?_ hmain.2
  refine tsub_le_tsub_left ?_ 1
  rw [hRvdef, etaG_compat_eq, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hKne]
  gcongr

end ChainClasses
