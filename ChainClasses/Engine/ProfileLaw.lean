import ChainClasses.Engine.ProfileKernel
import ChainClasses.General.GeneralLabelField

/-! Identification of a bounded-profile encoding from the product law on finite
prefix-closed probes of the reduced skeleton. -/

namespace ChainClasses.Profile

open MeasureTheory
open GraphMarkovMatching GraphMarkovMatching.Support GraphMarkovMatching.Stopped
open scoped ENNReal Classical

variable {N' : ℕ}

/-- The numbered child address (unused indices have an arbitrary value). -/
def gChild (u : GWord N') (j : ℕ) : GWord N' :=
  if h : j < N' then u ++ [⟨j, h⟩] else u

lemma gChild_of_lt (u : GWord N') {j : ℕ} (h : j < N') : gChild u j = u ++ [⟨j, h⟩] :=
  dite_eq_left h

/-- The address and slot offset a child of the profile vertex `u` works at. -/
def childAddr (u : GWord N') : ChildK → GWord N' × ℕ
  | ChildK.internal o _ => (u, o)
  | ChildK.slot j => (gChild u j, 0)

/-- The state of a child of the profile vertex `u` read off the fields: an internal child
carries `v₀` with its auxiliary type, a slot carries the label and the arity of the skeleton
child it holds. -/
def childState (lab ar : GWord N' → ℕ) (v0 : ℕ) (u : GWord N') : ChildK → RawState ℕ
  | ChildK.internal _ t => (v0, t)
  | ChildK.slot j => (lab (gChild u j), RawType.ord (ar (gChild u j)))

/-- **The encoded label field below a profile vertex**: the labelling of `𝔹_n` below the
vertex of state `s` working at the address `u` and the slot offset `off`. -/
noncomputable def encSub (exc : Family) (lab ar : GWord N' → ℕ) (v0 : ℕ) :
    (n : ℕ) → GWord N' → ℕ → RawState ℕ → FullLab (RawState ℕ) n
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
noncomputable def encLab (exc : Family) (lab ar : GWord N' → ℕ) (v0 : ℕ)
    (n : ℕ) : FullLab (RawState ℕ) n :=
  encSub exc lab ar v0 n [] 0 (lab [], RawType.ord (ar []))

lemma encSub_zero (exc : Family) (lab ar : GWord N' → ℕ) (v0 : ℕ)
    (u : GWord N') (off : ℕ) (s : RawState ℕ) : encSub exc lab ar v0 0 u off s = leaf s := rfl

lemma encSub_succ (exc : Family) (lab ar : GWord N' → ℕ) (v0 n : ℕ)
    (u : GWord N') (off : ℕ) (s : RawState ℕ) :
    encSub exc lab ar v0 (n + 1) u off s =
      GraphMarkovMatching.branch s
        (encSub exc lab ar v0 n (childAddr u (stepKind exc off s).1).1
            (childAddr u (stepKind exc off s).1).2
            (childState lab ar v0 u (stepKind exc off s).1),
          encSub exc lab ar v0 n (childAddr u (stepKind exc off s).2).1
            (childAddr u (stepKind exc off s).2).2
            (childState lab ar v0 u (stepKind exc off s).2)) := rfl

lemma rootLab_encSub (exc : Family) (lab ar : GWord N' → ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : RawState ℕ),
      rootLab n (encSub exc lab ar v0 n u off s) = s
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl

lemma restrictLab_branch_succ {V : Type} (n : ℕ) (s : V)
    (p : FullLab V (n + 1) × FullLab V (n + 1)) :
    restrictLab (n + 1) (GraphMarkovMatching.branch s p) =
      GraphMarkovMatching.branch s (restrictLab n p.1, restrictLab n p.2) := rfl

/-- The encoded field is projective: the restriction of the height-`(n+1)` encoding is the
height-`n` encoding. -/
lemma restrictLab_encSub (exc : Family) (lab ar : GWord N' → ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : RawState ℕ),
      restrictLab n (encSub exc lab ar v0 (n + 1) u off s) = encSub exc lab ar v0 n u off s
  | 0, _, _, _ => rfl
  | n + 1, u, off, s => by
      rw [encSub_succ exc lab ar v0 (n + 1) u off s, restrictLab_branch_succ,
        encSub_succ exc lab ar v0 n u off s]
      simp only
      rw [restrictLab_encSub exc lab ar v0 n, restrictLab_encSub exc lab ar v0 n]

lemma restrictLab_encLab (exc : Family) (lab ar : GWord N' → ℕ) (v0 n : ℕ) :
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
  · rw [ite_eq_left hroot]
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
  · rw [ite_eq_right hroot]
    refine ENNReal.tsum_eq_zero.mpr fun p => ?_
    rw [ite_eq_right]
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

/-- The record a child of the profile vertex `u` prescribes, given the root state found
below it: an internal child must carry `v₀` with its auxiliary type and prescribes nothing, a
slot must carry an sampled arity and prescribes the label and the arity of the
skeleton child it holds. -/
def childRec (v0 : ℕ) (u : GWord N') : ChildK → RawState ℕ → Option (List (Rec N'))
  | ChildK.internal _ t, r => if r = (v0, t) then some [] else none
  | ChildK.slot j, (a, RawType.ord m) => some [(gChild u j, a, m)]
  | ChildK.slot _, (_, RawType.rem _) => none

/-- The mass a child contributes, given the root state found below it: an internal child
forces its state, a slot draws a fresh state. -/
noncomputable def childMass (μ ν : PMF ℕ) (v0 : ℕ) : ChildK → RawState ℕ → ℝ≥0∞
  | ChildK.internal _ t, r => if r = (v0, t) then 1 else 0
  | ChildK.slot _, r => freshRaw μ ν r

/-- **The decoder**: the records a labelling of `𝔹_n` prescribes below the profile vertex
of state `s` working at `u` and `off`, or `none` when the labelling is not an encoding. -/
noncomputable def dec (exc : Family) (v0 : ℕ) :
    (n : ℕ) → GWord N' → ℕ → RawState ℕ → FullLab (RawState ℕ) n → Option (List (Rec N'))
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
noncomputable def decChild (exc : Family) (v0 n : ℕ) (u : GWord N') (c : ChildK)
    (x : FullLab (RawState ℕ) n) : Option (List (Rec N')) :=
  (childRec v0 u c (rootLab n x)).bind fun M =>
    (dec exc v0 n (childAddr u c).1 (childAddr u c).2 (rootLab n x) x).map fun L => M ++ L

lemma dec_zero (exc : Family) (v0 : ℕ) (u : GWord N') (off : ℕ) (s : RawState ℕ)
    (ℓ : FullLab (RawState ℕ) 0) :
    dec exc v0 0 u off s ℓ = if ℓ = leaf s then some [] else none := rfl

lemma dec_succ (exc : Family) (v0 n : ℕ) (u : GWord N') (off : ℕ) (s : RawState ℕ)
    (ℓ : FullLab (RawState ℕ) (n + 1)) :
    dec exc v0 (n + 1) u off s ℓ =
      if rootLab (n + 1) ℓ = s then
        (decChild exc v0 n u (stepKind exc off s).1 (subL ℓ)).bind fun L₁ =>
          (decChild exc v0 n u (stepKind exc off s).2 (subR ℓ)).map fun L₂ => L₁ ++ L₂
      else none := rfl

/-- **The decoder at the root**: the root must carry an sampled arity, which with its
label is the first record. -/
noncomputable def decTop (exc : Family) (v0 n : ℕ) (ℓ : FullLab (RawState ℕ) n) :
    Option (List (Rec N')) :=
  match rootLab n ℓ with
  | (a, RawType.ord k) => (dec exc v0 n [] 0 (a, RawType.ord k) ℓ).map fun L => ([], a, k) :: L
  | (_, RawType.rem _) => none

/-! ### The local step -/

/-- A child's record is realised by the fields exactly when the state found below it is
the encoded state. -/
lemma childRec_iff (lab ar : GWord N' → ℕ) (v0 : ℕ) (u : GWord N') (c : ChildK)
    (r : RawState ℕ) :
    (∃ M, childRec v0 u c r = some M ∧ Levent M lab ar) ↔ r = childState lab ar v0 u c := by
  cases c with
  | internal o t =>
      simp only [childRec, childState]
      constructor
      · rintro ⟨M, hM, -⟩
        by_contra h
        rw [ite_eq_right h] at hM
        exact Option.some_ne_none M hM.symm
      · intro h
        exact ⟨[], by rw [ite_eq_left h], Levent_nil⟩
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
            simp only [Prod.mk.injEq, RawType.ord.injEq] at h
            refine ⟨_, rfl, ?_⟩
            intro t ht
            rw [List.mem_singleton] at ht
            subst ht
            exact ⟨h.1.symm, h.2.symm⟩
      | rem τ =>
          simp only [childRec, childState, Prod.mk.injEq, reduceCtorEq, and_false, iff_false,
            not_exists, not_and]
          intro M hM
          exact hM.elim

/-- A child's mass is the mass of its record. -/
lemma childMass_eq (μ ν : PMF ℕ) (v0 : ℕ) (u : GWord N') (c : ChildK) (r : RawState ℕ) :
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
          exact freshRaw_ord_apply μ ν a m
      | rem τ =>
          simp only [childMass, childRec, optMass]
          exact freshRaw_rem_apply μ ν a τ

lemma map_pair_left_apply {A : Type} (ρ : PMF A) (c r₁ r₂ : A) :
    (ρ.map fun f => (c, f)) (r₁, r₂) = if r₁ = c then ρ r₂ else 0 := by
  rw [PMF.map_apply]
  by_cases h : r₁ = c
  · subst h
    rw [ite_eq_left rfl]
    have hiff : ∀ f : A, ((r₁, r₂) = (r₁, f)) ↔ f = r₂ := by
      intro f
      simp only [Prod.mk.injEq, true_and]
      exact eq_comm
    simp_rw [hiff]
    rw [tsum_ite_eq]
  · rw [ite_eq_right h]
    refine ENNReal.tsum_eq_zero.mpr fun f => ?_
    rw [ite_eq_right]
    intro hf
    exact h (congrArg Prod.fst hf)

lemma pure_pair_apply {A : Type} (c₁ c₂ r₁ r₂ : A) :
    (PMF.pure (c₁, c₂)) (r₁, r₂) = (if r₁ = c₁ then 1 else 0) * (if r₂ = c₂ then 1 else 0) := by
  rw [PMF.pure_apply]
  by_cases h1 : r₁ = c₁ <;> by_cases h2 : r₂ = c₂ <;> simp [h1, h2]

lemma childLaw_apply (μ ν : PMF ℕ) (v0 : ℕ) (c : ChildK) (r : RawState ℕ) :
    childLaw μ ν v0 c r = childMass μ ν v0 c r := by
  cases c <;> simp only [childLaw, childMass, PMF.pure_apply]
  split_ifs <;> rfl

lemma childLaw_treeStep (μ ν : PMF ℕ) (v0 off : ℕ) (τ : MTree) :
    childLaw μ ν v0 (treeStep 0 τ).1 = childLaw μ ν v0 (treeStep off τ).1 ∧
    childLaw μ ν v0 (treeStep 0 τ).2 = childLaw μ ν v0 (treeStep off τ).2 := by
  cases τ with
  | leaf => exact ⟨rfl, rfl⟩
  | node l r | gnode l r =>
      cases l <;> cases r <;> exact ⟨rfl, rfl⟩

/-- The auxiliary transition is the product of its two child laws. -/
lemma rawKernel_apply_eq (exc : Family) (μ ν : PMF ℕ) (v0 off : ℕ) (s : RawState ℕ)
    (r₁ r₂ : RawState ℕ) :
    rawKernel exc μ ν v0 s (r₁, r₂) =
      childMass μ ν v0 (stepKind exc off s).1 r₁ *
        childMass μ ν v0 (stepKind exc off s).2 r₂ := by
  rw [rawKernel, prodPMF_apply]
  rcases s with ⟨v, k | τ⟩
  · obtain ⟨h1, h2⟩ := childLaw_treeStep μ ν v0 off (exc.tree k)
    simp only [stepKind]
    rw [h1, h2, childLaw_apply, childLaw_apply]
  · obtain ⟨h1, h2⟩ := childLaw_treeStep μ ν v0 off τ
    simp only [stepKind]
    rw [h1, h2, childLaw_apply, childLaw_apply]

/-! ### The decoder characterises the encoding -/

lemma exists_bind_map_append_iff (o₁ o₂ : Option (List (Rec N'))) (lab ar : GWord N' → ℕ) :
    (∃ L, (o₁.bind fun L₁ => o₂.map fun L₂ => L₁ ++ L₂) = some L ∧ Levent L lab ar) ↔
      (∃ L₁, o₁ = some L₁ ∧ Levent L₁ lab ar) ∧ ∃ L₂, o₂ = some L₂ ∧ Levent L₂ lab ar := by
  rcases o₁ with _ | L₁ <;> rcases o₂ with _ | L₂ <;> simp [Levent_append]

lemma optMass_bind_map_append (μ ν : PMF ℕ) (o₁ o₂ : Option (List (Rec N'))) :
    optMass μ ν (o₁.bind fun L₁ => o₂.map fun L₂ => L₁ ++ L₂) =
      optMass μ ν o₁ * optMass μ ν o₂ := by
  rcases o₁ with _ | L₁ <;> rcases o₂ with _ | L₂ <;> simp [optMass, recMass_append]

lemma optMass_decChild (exc : Family) (μ ν : PMF ℕ) (v0 n : ℕ) (u : GWord N')
    (c : ChildK) (x : FullLab (RawState ℕ) n) :
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
lemma decChild_iff (exc : Family) (lab ar : GWord N' → ℕ) (v0 n : ℕ)
    (ih : ∀ (u : GWord N') (off : ℕ) (s : RawState ℕ) (ℓ : FullLab (RawState ℕ) n),
      encSub exc lab ar v0 n u off s = ℓ ↔
        ∃ L, dec exc v0 n u off s ℓ = some L ∧ Levent L lab ar)
    (u : GWord N') (c : ChildK) (x : FullLab (RawState ℕ) n) :
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
a profile vertex exactly when it decodes to records the fields realise. -/
theorem encSub_eq_iff (exc : Family) (lab ar : GWord N' → ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : RawState ℕ) (ℓ : FullLab (RawState ℕ) n),
      encSub exc lab ar v0 n u off s = ℓ ↔
        ∃ L, dec exc v0 n u off s ℓ = some L ∧ Levent L lab ar := by
  intro n
  induction n with
  | zero =>
      intro u off s ℓ
      rw [encSub_zero, dec_zero]
      constructor
      · intro h
        exact ⟨[], by rw [ite_eq_left h.symm], Levent_nil⟩
      · rintro ⟨L, hL, -⟩
        by_contra h
        rw [ite_eq_right (Ne.symm h)] at hL
        exact Option.some_ne_none L hL.symm
  | succ n ih =>
      intro u off s ℓ
      rw [encSub_succ, dec_succ, branch_eq_iff]
      by_cases hroot : rootLab (n + 1) ℓ = s
      · rw [ite_eq_left hroot, exists_bind_map_append_iff, ← decChild_iff exc lab ar v0 n ih,
          ← decChild_iff exc lab ar v0 n ih]
        simp only [hroot, true_and]
      · rw [ite_eq_right hroot]
        simp only [hroot, false_and, false_iff, not_exists, not_and]
        intro L hL
        exact (Option.some_ne_none L hL.symm).elim

/-- **The encoded field at the root**: a labelling is the encoding exactly when its root
record and the records below are realised. -/
theorem encLab_eq_iff (exc : Family) (lab ar : GWord N' → ℕ) (v0 n : ℕ)
    (ℓ : FullLab (RawState ℕ) n) :
    encLab exc lab ar v0 n = ℓ ↔ ∃ L, decTop exc v0 n ℓ = some L ∧ Levent L lab ar := by
  rw [encLab]
  constructor
  · intro h
    have hroot : rootLab n ℓ = (lab [], RawType.ord (ar [])) := by
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
    | rem τ =>
        simp only [decTop, hr] at hL
        exact (Option.some_ne_none L hL.symm).elim

/-! ### The mass of a labelling -/

/-- **The tree law as a product of record masses**: the mass of a labelling below a
profile vertex is the product of the fresh masses of the records it decodes to. -/
theorem muM_eq_recMass (exc : Family) (μ ν : PMF ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : RawState ℕ) (ℓ : FullLab (RawState ℕ) n),
      muM (rawKernel exc μ ν v0) s n ℓ = optMass μ ν (dec exc v0 n u off s ℓ) := by
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
      · rw [ite_eq_left hroot, ite_eq_left hroot, optMass_bind_map_append, optMass_decChild,
          optMass_decChild, rawKernel_apply_eq exc μ ν v0 off, childMass_eq μ ν v0 u,
          childMass_eq μ ν v0 u, ih, ih]
        ring
      · rw [ite_eq_right hroot, ite_eq_right hroot]
        rfl

lemma decTop_ord (exc : Family) (v0 n : ℕ) (ℓ : FullLab (RawState ℕ) n) {a k : ℕ}
    (h : rootLab n ℓ = (a, RawType.ord k)) :
    decTop exc v0 n ℓ =
      (dec exc v0 n [] 0 (a, RawType.ord k) ℓ).map fun L => (([] : GWord N'), a, k) :: L := by
  simp only [decTop, h]

lemma decTop_rem (exc : Family) (v0 n : ℕ) (ℓ : FullLab (RawState ℕ) n)
    {a : ℕ} {τ : MTree} (h : rootLab n ℓ = (a, RawType.rem τ)) :
    decTop exc v0 n ℓ = (none : Option (List (Rec N'))) := by
  simp only [decTop, h]

lemma optMass_map_cons (μ ν : PMF ℕ) (t : Rec N') (o : Option (List (Rec N'))) :
    optMass μ ν (o.map fun L => t :: L) = μ t.2.1 * ν t.2.2 * optMass μ ν o := by
  rcases o with _ | L <;> simp [optMass, recMass]

/-- **The fresh law as a product of record masses**: the mass of a labelling under the
profile law is the product of the fresh masses of the records of its decoding
at the root. -/
theorem rawLaw_eq_recMass (exc : Family) (μ ν : PMF ℕ) (v0 n : ℕ)
    (ℓ : FullLab (RawState ℕ) n) :
    rawLaw exc μ ν v0 n ℓ = optMass μ ν (decTop exc v0 n ℓ : Option (List (Rec N'))) := by
  rw [rawLaw, PMF.bind_apply, tsum_eq_single (rootLab n ℓ)]
  · rcases hr : rootLab n ℓ with ⟨a, c⟩
    cases c with
    | ord k =>
        rw [decTop_ord exc v0 n ℓ hr, optMass_map_cons,
          freshRaw_ord_apply,
          muM_eq_recMass exc μ ν v0 n [] 0 (a, RawType.ord k) ℓ]
    | rem τ =>
        rw [decTop_rem exc v0 n ℓ hr, freshRaw_rem_apply,
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

/-- **A well-formed list of records** below the profile vertex `u` serving the slots
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
lemma wfl_decChild (exc : Family) (v0 n : ℕ)
    (ih : ∀ (u : GWord N') (off : ℕ) (s : RawState ℕ) (ℓ : FullLab (RawState ℕ) n)
      (L : List (Rec N')), dec exc v0 n u off s ℓ = some L → validS s →
      off + servedC s.2 ≤ N' → ∃ L' : List (Rec N'), (∀ t ∈ L', t ∈ L) ∧
        WFL u off (off + servedC s.2) L' ∧ ((∀ t ∈ L', GoodRec N' t) → L' = L))
    (u : GWord N') (c : ChildK) (x : FullLab (RawState ℕ) n) (Lc : List (Rec N'))
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
        rw [ite_eq_right h] at hM
        exact Option.some_ne_none M hM.symm
      rw [ite_eq_left hroot, Option.some.injEq] at hM
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
          · obtain ⟨L'', hsub, hw, hgood⟩ := ih (gChild u j) 0 (a, RawType.ord m) x L' hL'
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
      | rem τ =>
          simp only [childRec] at hM
          exact (Option.some_ne_none M hM.symm).elim

/-- **The decoded records are well formed**: below a valid state with its slots in the
letter range, the records of a labelling contain a well-formed sublist, the whole list when
the sublist has its arities in the letter range. -/
theorem wfl_dec (exc : Family) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : RawState ℕ) (ℓ : FullLab (RawState ℕ) n)
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
      obtain ⟨hst1, hst2, hsum, hv1, hv2⟩ := stepKind_spec exc v0 off hs
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
lemma decTop_some (exc : Family) (v0 n : ℕ)
    (ℓ : FullLab (RawState ℕ) n) {L : List (Rec N')} (hL : decTop exc v0 n ℓ = some L) :
    ∃ (a k : ℕ) (L₀ : List (Rec N')), rootLab n ℓ = (a, RawType.ord k) ∧
      L = ([], a, k) :: L₀ ∧ (2 ≤ k ∧ k ≤ N' → ∃ L₀' : List (Rec N'),
        (∀ t ∈ L₀', t ∈ L₀) ∧ WFL [] 0 k L₀' ∧ ((∀ t ∈ L₀', GoodRec N' t) → L₀' = L₀)) := by
  rcases hr : rootLab n ℓ with ⟨a, c⟩
  cases c with
  | ord k =>
      rw [decTop_ord exc v0 n ℓ hr] at hL
      obtain ⟨L₀, hL₀, rfl⟩ := Option.map_eq_some_iff.mp hL
      refine ⟨a, k, L₀, rfl, rfl, fun hk => ?_⟩
      have := wfl_dec exc v0 n [] 0 (a, RawType.ord k) ℓ L₀ hL₀ (by simpa [validS] using hk.1)
        (by simpa [servedC] using hk.2)
      simpa [servedC] using this
  | rem τ =>
      rw [decTop_rem exc v0 n ℓ hr] at hL
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
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, Levent]
  rw [hset]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
    (hlab t.1 t.2.1).inter (har t.1 t.2.2)

/-- The encoded label field is measurable once the fibres of the fields are. -/
lemma measurable_encLab_of {lab ar : Ω → GWord N' → ℕ}
    (hlab : ∀ w a, MeasurableSet {ω | lab ω w = a})
    (har : ∀ w k, MeasurableSet {ω | ar ω w = k}) (exc : Family) (v0 n : ℕ) :
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
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, encLab_eq_iff, hdec,
        Option.some.injEq, exists_eq_left']
    rw [hset]
    exact measurableSet_levent_of hlab har L

/-- **The projective identification from a product formula, at one labelling**: if the
pairs of a label and an arity are i.i.d. with the product law `μ ⊗ ν` over every
prefix-closed probe respecting the prescribed arities, and `ν` is supported in the letter
range, then the mass of a labelling of `𝔹_n` under the encoded label field is its mass
under the profile law.  The decoded records of a labelling contain a well-formed
sublist; when every record of the sublist has its arity in the letter range, the sublist
is the whole list and the product formula over its probe is the record mass, and
otherwise a record with an arity off the support of `ν` makes both sides vanish. -/
theorem encLab_apply_of_pattern (P : Measure Ω) {lab ar : Ω → GWord N' → ℕ} (μ ν : PMF ℕ)
    (hpat : ∀ F : Finset (GWord N'), (∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F) →
      ∀ a k : GWord N' → ℕ, (∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) →
        P (⋂ u ∈ F, ({ω | lab ω u = a u} ∩ {ω | ar ω u = k u})) = ∏ u ∈ F, μ (a u) * ν (k u))
    (hsupp : ∀ k, ν k ≠ 0 → 2 ≤ k ∧ k ≤ N') (exc : Family)
    (v0 n : ℕ) (ℓ : FullLab (RawState ℕ) n) :
    P {ω | encLab exc (lab ω) (ar ω) v0 n = ℓ} = rawLaw exc μ ν v0 n ℓ := by
  rw [rawLaw_eq_recMass]
  rcases hdec : decTop exc v0 n ℓ with _ | L
  · have hset : {ω | encLab exc (lab ω) (ar ω) v0 n = ℓ} = ∅ := by
      ext ω
      rw [Set.mem_ofPred_eq, encLab_eq_iff, hdec]
      simp
    rw [hset, measure_empty]
    rfl
  · have hset : {ω | encLab exc (lab ω) (ar ω) v0 n = ℓ} = {ω | Levent L (lab ω) (ar ω)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, encLab_eq_iff, hdec, Option.some.injEq, exists_eq_left']
    rw [hset]
    obtain ⟨a, k, L₀, hr, rfl, hwf⟩ := decTop_some exc v0 n ℓ hdec
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
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
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
label field at height `n` is the profile law `rawLaw` at height `n`. -/
theorem map_encLab_of_pattern (P : Measure Ω) {lab ar : Ω → GWord N' → ℕ}
    (hlab : ∀ w a, MeasurableSet {ω | lab ω w = a})
    (har : ∀ w k, MeasurableSet {ω | ar ω w = k}) (μ ν : PMF ℕ)
    (hpat : ∀ F : Finset (GWord N'), (∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F) →
      ∀ a k : GWord N' → ℕ, (∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) →
        P (⋂ u ∈ F, ({ω | lab ω u = a u} ∩ {ω | ar ω u = k u})) = ∏ u ∈ F, μ (a u) * ν (k u))
    (hsupp : ∀ k, ν k ≠ 0 → 2 ≤ k ∧ k ≤ N') (exc : Family)
    (v0 n : ℕ) :
    P.map (fun ω => encLab exc (lab ω) (ar ω) v0 n) = (rawLaw exc μ ν v0 n).toMeasure := by
  refine Measure.ext_of_singleton fun ℓ => ?_
  rw [Measure.map_apply (measurable_encLab_of hlab har exc v0 n) (measurableSet_singleton ℓ),
    PMF.toMeasure_apply_singleton _ ℓ (measurableSet_singleton ℓ)]
  have hset : (fun ω => encLab exc (lab ω) (ar ω) v0 n) ⁻¹' {ℓ}
      = {ω | encLab exc (lab ω) (ar ω) v0 n = ℓ} := by
    ext ω
    simp
  rw [hset]
  exact encLab_apply_of_pattern P μ ν hpat hsupp exc v0 n ℓ

end Generic


end ChainClasses.Profile
