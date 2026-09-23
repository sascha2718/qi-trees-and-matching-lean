import ChainClasses.Universality.CascadeEncoding
import ChainClasses.Engine.ProfileMatching
import ChainClasses.Universality.BAssembly
import ChainClasses.Universality.GeneralObstructions
import ChainClasses.General.GeneralShapeEta

/-! The ordered leaf slots and geometric encoding of finite full binary profiles.
This supplies the deterministic interface in `thm:profile-encoding`. -/

namespace ChainClasses.Profile

open MeasureTheory
open GraphMarkovMatching GraphMarkovMatching.Support GraphMarkovMatching.Stopped
open BranchingProcess (sample skeletonDegree bushAt)
open scoped ENNReal Classical

variable {N N' : ℕ}

def cChild (exc : Family) (off : ℕ) (t : RawType) (b : Bool) : ChildK :=
  bif b then (stepKind exc off (0, t)).2 else (stepKind exc off (0, t)).1

/-- The step geometry reads the type only. -/
lemma stepKind_eq_zero (exc : Family) (off : ℕ) (s : RawState ℕ) :
    stepKind exc off s = stepKind exc off (0, s.2) := by
  obtain ⟨v, t⟩ := s
  cases t <;> rfl

/-- The position reached by a descent through a cascade: an internal vertex with its
type and slot offset, or a slot together with the rest of the path. -/
inductive CPos where
  | inside (t : RawType) (off : ℕ) : CPos
  | atSlot (j : ℕ) (q : List Bool) : CPos

/-- **The descent through a cascade** along a binary word, from an internal vertex of
type `t` serving the slots from `off` on. -/
def walk (exc : Family) : RawType → ℕ → List Bool → CPos
  | t, off, [] => CPos.inside t off
  | t, off, b :: p =>
      match cChild exc off t b with
      | ChildK.internal o t' => walk exc t' o p
      | ChildK.slot j => CPos.atSlot j p

lemma walk_nil (exc : Family) (t : RawType) (off : ℕ) :
    walk exc t off [] = CPos.inside t off := rfl

lemma walk_cons_internal {exc : Family} {t : RawType} {off : ℕ} {b : Bool}
    {o : ℕ} {t' : RawType} (h : cChild exc off t b = ChildK.internal o t') (p : List Bool) :
    walk exc t off (b :: p) = walk exc t' o p := by
  simp only [walk, h]

lemma walk_cons_slot {exc : Family} {t : RawType} {off : ℕ} {b : Bool} {j : ℕ}
    (h : cChild exc off t b = ChildK.slot j) (p : List Bool) :
    walk exc t off (b :: p) = CPos.atSlot j p := by
  simp only [walk, h]

/-- The descent along a concatenation continues from the position the first word
reaches. -/
lemma walk_append (exc : Family) :
    ∀ (p q : List Bool) (t : RawType) (off : ℕ),
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
      | rem τ => simpa [servedK, servedC] using Nat.succ_le_of_lt (MTree.leaves_pos τ)

/-- The slot range of a child of a profile type: the left child serves the slots from
`off` to `off + servedK`, the right child the following ones. -/
lemma cChild_range (exc : Family) {t : RawType}
    (ht : validS (0, t)) (off : ℕ) (b : Bool) :
    off ≤ startK (cChild exc off t b) ∧
      startK (cChild exc off t b) + servedK (cChild exc off t b) ≤ off + servedC t ∧
      validK 0 (cChild exc off t b) ∧
      (b = false → startK (cChild exc off t b) = off) ∧
      (b = true → startK (cChild exc off t b) = off + servedK (stepKind exc off (0, t)).1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stepKind_spec exc 0 off ht
  have h3' : servedK (stepKind exc off (0, t)).1 + servedK (stepKind exc off (0, t)).2
      = servedC t := h3
  cases b
  · simp only [cChild, Bool.cond_false]
    exact ⟨h1.ge, by omega, h4, fun _ => h1, fun h => absurd h (by decide)⟩
  · simp only [cChild, Bool.cond_true]
    exact ⟨by omega, by omega, h5, fun h => absurd h (by decide), fun _ => h2⟩

/-- **The range of a slot reached by a descent**: a valid type serving the slots from
`off` on reaches slots in `[off, off + servedC t)` only. -/
lemma walk_atSlot_range (exc : Family) :
    ∀ (p : List Bool) {t : RawType}, validS (0, t) → ∀ {off j : ℕ} {q : List Bool},
      walk exc t off p = CPos.atSlot j q → off ≤ j ∧ j < off + servedC t
  | [], t, _, off, j, q, h => by simp [walk_nil] at h
  | b :: p, t, ht, off, j, q, h => by
      obtain ⟨hr1, hr2, hv, -, -⟩ := cChild_range exc ht off b
      rcases hc : cChild exc off t b with ⟨o, t'⟩ | j'
      · rw [walk_cons_internal hc] at h
        rw [hc] at hr1 hr2 hv
        simp only [startK, servedK] at hr1 hr2
        have hv' : validS (0, t') := hv
        have := walk_atSlot_range exc p hv' h
        omega
      · rw [walk_cons_slot hc, CPos.atSlot.injEq] at h
        rw [hc] at hr1 hr2
        simp only [startK, servedK] at hr1 hr2
        omega

/-- A descent reaching a slot lies in the slot range of its first child. -/
lemma walk_cons_atSlot_range (exc : Family) {t : RawType}
    (ht : validS (0, t)) {off : ℕ} {b : Bool} {p : List Bool} {j : ℕ} {q : List Bool}
    (h : walk exc t off (b :: p) = CPos.atSlot j q) :
    startK (cChild exc off t b) ≤ j ∧
      j < startK (cChild exc off t b) + servedK (cChild exc off t b) := by
  obtain ⟨-, -, hv, -, -⟩ := cChild_range exc ht off b
  rcases hc : cChild exc off t b with ⟨o, t'⟩ | j'
  · rw [walk_cons_internal hc] at h
    rw [hc] at hv
    have := walk_atSlot_range exc p hv h
    simpa [startK, servedK] using this
  · rw [walk_cons_slot hc, CPos.atSlot.injEq] at h
    simp only [startK, servedK]
    omega

/-- **The path to a slot is unique.** -/
lemma walk_atSlot_unique (exc : Family) :
    ∀ (p p' : List Bool) {t : RawType}, validS (0, t) → ∀ {off j : ℕ},
      walk exc t off p = CPos.atSlot j [] → walk exc t off p' = CPos.atSlot j [] → p = p'
  | [], _, t, _, off, j, h, _ => by simp [walk_nil] at h
  | _ :: _, [], t, _, off, j, _, h' => by simp [walk_nil] at h'
  | b :: p, b' :: p', t, ht, off, j, h, h' => by
      obtain ⟨-, -, hv, hl, hr⟩ := cChild_range exc ht off b
      obtain ⟨-, -, hv', hl', hr'⟩ := cChild_range exc ht off b'
      by_cases hb : b = b'
      · subst hb
        rcases hc : cChild exc off t b with ⟨o, t'⟩ | j'
        · rw [walk_cons_internal hc] at h h'
          rw [hc] at hv
          rw [walk_atSlot_unique exc p p' hv h h']
        · rw [walk_cons_slot hc, CPos.atSlot.injEq] at h h'
          rw [h.2, h'.2]
      · exfalso
        have h1 := walk_cons_atSlot_range exc ht h
        have h2 := walk_cons_atSlot_range exc ht h'
        obtain ⟨s1, s2, s3, s4, s5⟩ := stepKind_spec exc 0 off ht
        cases b <;> cases b' <;> simp at hb
        · have e1 := hl rfl
          have e2 := hr' rfl
          simp only [cChild, Bool.cond_false, Bool.cond_true] at h1 h2 e1 e2
          omega
        · have e1 := hr rfl
          have e2 := hl' rfl
          simp only [cChild, Bool.cond_false, Bool.cond_true] at h1 h2 e1 e2
          omega

/-- **The path to a slot**, with a fuel: descend into the child whose slot range
contains the slot. -/
def slotPathF (exc : Family) : ℕ → RawType → ℕ → ℕ → List Bool
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

lemma slotPathF_length_le (exc : Family) :
    ∀ (d : ℕ) (t : RawType) (off j : ℕ), (slotPathF exc d t off j).length ≤ d
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

lemma slotPathF_ne_nil (exc : Family) (d : ℕ) (t : RawType) (off j : ℕ) :
    slotPathF exc (d + 1) t off j ≠ [] := by
  simp only [slotPathF]
  split_ifs
  · rcases (stepKind exc off (0, t)).1 with ⟨o, t'⟩ | _ <;> simp
  · rcases (stepKind exc off (0, t)).2 with ⟨o, t'⟩ | _ <;> simp

/-- **The path to a slot reaches it**, once the fuel is at least the number of slots
served: every internal vertex serves strictly fewer slots than its parent. -/
lemma walk_slotPathF (exc : Family) :
    ∀ (d : ℕ) {t : RawType}, validS (0, t) → servedC t ≤ d → ∀ {off j : ℕ},
      off ≤ j → j < off + servedC t → walk exc t off (slotPathF exc d t off j) = CPos.atSlot j []
  | 0, t, ht, hd, off, j, h1, h2 => by
      exfalso
      cases t with
      | ord k => simp only [validS] at ht; simp only [servedC] at hd; omega
      | rem τ =>
          have hp := MTree.leaves_pos τ
          simp only [servedC] at hd
          omega
  | d + 1, t, ht, hd, off, j, h1, h2 => by
      obtain ⟨s1, s2, s3, s4, s5⟩ := stepKind_spec exc 0 off ht
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
          exact walk_slotPathF exc d e3 (by omega) (by omega) (by omega)
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
          exact walk_slotPathF exc d e3 (by omega) (by omega) (by omega)
        · rw [walk_cons_slot hcr]
          have e1 : startK (ChildK.slot j') = j' := rfl
          have e2 : servedK (ChildK.slot j') = 1 := rfl
          rw [e1] at s2 hj
          rw [e2] at s3
          congr 1
          omega

/-- A descent stays inside valid types serving no more slots than the root, within
the root's slot range. -/
lemma walk_inside_valid (exc : Family) :
    ∀ (p : List Bool) {t₀ : RawType}, validS (0, t₀) → ∀ {off : ℕ} {t : RawType} {o : ℕ},
      walk exc t₀ off p = CPos.inside t o →
        validS (0, t) ∧ off ≤ o ∧ o + servedC t ≤ off + servedC t₀
  | [], t₀, ht, off, t, o, h => by
      rw [walk_nil, CPos.inside.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ht, le_rfl, le_rfl⟩
  | b :: p, t₀, ht, off, t, o, h => by
      obtain ⟨hr1, hr2, hv, -, -⟩ := cChild_range exc ht off b
      rcases hc : cChild exc off t₀ b with ⟨o', t'⟩ | j'
      · rw [walk_cons_internal hc] at h
        rw [hc] at hr1 hr2 hv
        have e1 : startK (ChildK.internal o' t') = o' := rfl
        have e2 : servedK (ChildK.internal o' t') = servedC t' := rfl
        rw [e1] at hr1 hr2
        rw [e2] at hr2
        have hv' : validS (0, t') := hv
        obtain ⟨h1, h2, h3⟩ := walk_inside_valid exc p hv' h
        exact ⟨h1, by omega, by omega⟩
      · rw [walk_cons_slot hc] at h
        cases h

/-! ### The profile's encoding as a `CascadeEnc` -/

/-- **The slot word of the `j`-th child of `u`**: the path through the cascade of `u`
to its `j`-th slot. -/
def profileSlot (exc : Family) (L : ℕ) (ar : GWord N → ℕ) (u : GWord N)
    (j : ℕ) : List Bool :=
  slotPathF exc L (RawType.ord (ar u)) 0 j

/-- The encoding of a skeleton address below a prefix: one slot word per letter. -/
def profileEncAux (exc : Family) (L : ℕ) (ar : GWord N → ℕ) :
    GWord N → GWord N → List Bool
  | _, [] => []
  | p, i :: rest => profileSlot exc L ar p (i : ℕ) ++ profileEncAux exc L ar (p ++ [i]) rest

lemma profileEncAux_append (exc : Family) (L : ℕ) (ar : GWord N → ℕ) :
    ∀ (u v p : GWord N), profileEncAux exc L ar p (u ++ v)
      = profileEncAux exc L ar p u ++ profileEncAux exc L ar (p ++ u) v
  | [], v, p => by simp [profileEncAux]
  | i :: u, v, p => by
      simp only [List.cons_append, profileEncAux, List.append_assoc]
      rw [profileEncAux_append exc L ar u v (p ++ [i])]
      simp

/-- **The encoding of a skeleton address**: the concatenation of the slot words along
the address. -/
def profileEncWord (exc : Family) (L : ℕ) (ar : GWord N → ℕ) (u : GWord N) :
    List Bool :=
  profileEncAux exc L ar [] u

@[simp] lemma profileEncWord_nil (exc : Family) (L : ℕ) (ar : GWord N → ℕ) :
    profileEncWord exc L ar [] = [] := rfl

lemma profileEncWord_concat (exc : Family) (L : ℕ) (ar : GWord N → ℕ)
    (u : GWord N) (i : Fin N) :
    profileEncWord exc L ar (u ++ [i]) = profileEncWord exc L ar u ++ profileSlot exc L ar u (i : ℕ) := by
  rw [profileEncWord, profileEncWord, profileEncAux_append]
  simp [profileEncAux]

/-- The arity field admits the encoding: every nonzero arity lies in `{2, …, L}`. -/
def ArityBounded (L : ℕ) (ar : GWord N → ℕ) : Prop := ∀ u, ar u ≠ 0 → 2 ≤ ar u ∧ ar u ≤ L

/-- **The slot word reaches its slot.** -/
lemma walk_profileSlot (exc : Family) {L : ℕ}
    {ar : GWord N → ℕ} (har : ArityBounded L ar) {u : GWord N} {j : ℕ} (hj : j < ar u) :
    walk exc (RawType.ord (ar u)) 0 (profileSlot exc L ar u j) = CPos.atSlot j [] := by
  obtain ⟨h2, hL⟩ := har u (by omega)
  exact walk_slotPathF exc L (t := RawType.ord (ar u)) h2 hL (Nat.zero_le j) (by simpa [servedC])

/-- **The profile's encoding as a `CascadeEnc`** (`thm:hairy-general`): the slot of a
child is its path through the cascade, of length at most the bound on the arities. -/
def profileEnc (exc : Family) (L : ℕ) (ar : GWord N → ℕ) 
    (har : ArityBounded L ar) : CascadeEnc N L where
  k := ar
  enc := profileEncWord exc L ar
  slot := profileSlot exc L ar
  enc_nil := rfl
  enc_concat := profileEncWord_concat exc L ar
  slot_ne_nil := fun u i hi => by
    obtain ⟨h2, hL⟩ := har u (by omega)
    cases L with
    | zero => omega
    | succ L' => exact slotPathF_ne_nil exc L' _ 0 i
  slot_length_le := fun u i _ => slotPathF_length_le exc L _ 0 i
  slot_prefix := fun u i j hi hj hp => by
    have hi' := walk_profileSlot exc har hi
    have hj' := walk_profileSlot exc har hj
    obtain ⟨q, hq⟩ := hp
    rw [← hq, walk_append, hi'] at hj'
    simp only [List.nil_append, CPos.atSlot.injEq] at hj'
    exact hj'.1

@[simp] lemma profileEnc_k (exc : Family) (L : ℕ) (ar : GWord N → ℕ)
     (har : ArityBounded L ar) : (profileEnc exc L ar har).k = ar := rfl

@[simp] lemma profileEnc_enc (exc : Family) (L : ℕ) (ar : GWord N → ℕ)
     (har : ArityBounded L ar) :
    (profileEnc exc L ar har).enc = profileEncWord exc L ar := rfl

/-! ### Reading the encoded label field -/

/-- A full labelling of the profile read as a full labelling of `GraphMatching`; the two
types are the same recursion. -/
def labOfK {V : Type} : (n : ℕ) → FullLab V n → GraphMatching.FullLab V n
  | 0, x => x
  | n + 1, x => (x.1, labOfK n x.2.1, labOfK n x.2.2)

/-- **The label of a full labelling at a binary address**, junk beyond the depth. -/
def labelAt {V : Type} (n : ℕ) (X : FullLab V n) (w : List Bool) : V :=
  GraphMatching.coord n (labOfK n X) w

/-- **The encoded label field below a cascade vertex, read along a path**: the state at
the end of the descent from the vertex of state `s` working at `u` and `off`. -/
def encAt (exc : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) :
    GWord N → ℕ → RawState ℕ → List Bool → RawState ℕ
  | _, _, s, [] => s
  | u, off, s, b :: p =>
      encAt exc lab ar v0 (childAddr u (cChild exc off s.2 b)).1
        (childAddr u (cChild exc off s.2 b)).2 (childState lab ar v0 u (cChild exc off s.2 b)) p

lemma encAt_nil (exc : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) (u : GWord N)
    (off : ℕ) (s : RawState ℕ) : encAt exc lab ar v0 u off s [] = s := rfl

lemma encAt_cons (exc : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) (u : GWord N)
    (off : ℕ) (s : RawState ℕ) (b : Bool) (p : List Bool) :
    encAt exc lab ar v0 u off s (b :: p)
      = encAt exc lab ar v0 (childAddr u (cChild exc off s.2 b)).1
        (childAddr u (cChild exc off s.2 b)).2 (childState lab ar v0 u (cChild exc off s.2 b)) p :=
  rfl

/-- **Reading the encoding**: the label of the height-`n` encoding at an address of
length at most `n` is the state the descent reaches. -/
lemma labelAt_encSub (exc : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) :
    ∀ (n : ℕ) (p : List Bool), p.length ≤ n → ∀ (u : GWord N) (off : ℕ) (s : RawState ℕ),
      labelAt n (encSub exc lab ar v0 n u off s) p = encAt exc lab ar v0 u off s p
  | 0, [], _, u, off, s => rfl
  | 0, _ :: _, h, _, _, _ => by simp at h
  | _ + 1, [], _, u, off, s => rfl
  | n + 1, b :: p, h, u, off, s => by
      have hp : p.length ≤ n := by simpa using h
      rw [encAt_cons]
      cases b
      · have e : cChild exc off s.2 false = (stepKind exc off s).1 := by
          rw [cChild, Bool.cond_false, ← stepKind_eq_zero]
        rw [e]
        exact labelAt_encSub exc lab ar v0 n p hp _ _ _
      · have e : cChild exc off s.2 true = (stepKind exc off s).2 := by
          rw [cChild, Bool.cond_true, ← stepKind_eq_zero]
        rw [e]
        exact labelAt_encSub exc lab ar v0 n p hp _ _ _

/-- **The encoded label field on `𝔹`**: the descent from the root. -/
def encField (exc : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) (w : List Bool) :
    RawState ℕ :=
  encAt exc lab ar v0 [] 0 (lab [], RawType.ord (ar [])) w

lemma labelAt_encLab (exc : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) {n : ℕ}
    {w : List Bool} (hw : w.length ≤ n) :
    labelAt n (encLab exc lab ar v0 n) w = encField exc lab ar v0 w :=
  labelAt_encSub exc lab ar v0 n w hw [] 0 _

/-- A descent ending inside the cascade reads the state `(v₀, t)` of the internal vertex. -/
lemma encAt_of_walk_inside (exc : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) :
    ∀ (p : List Bool) (u : GWord N) (off : ℕ) (s : RawState ℕ) {t : RawType} {o : ℕ},
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
lemma encAt_of_walk_atSlot (exc : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) :
    ∀ (p : List Bool) (u : GWord N) (off : ℕ) (s : RawState ℕ) {j : ℕ} {q : List Bool},
      walk exc s.2 off p = CPos.atSlot j q →
        encAt exc lab ar v0 u off s p
          = encAt exc lab ar v0 (gChild u j) 0 (lab (gChild u j), RawType.ord (ar (gChild u j))) q
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
lemma encAt_nil_enc (exc : Family) {L : ℕ}
    (lab : GWord N → ℕ) {ar : GWord N → ℕ} (har : ArityBounded L ar) (v0 : ℕ) :
    ∀ (u : GWord N), u ∈ sample ar → ∀ (q : List Bool),
      encAt exc lab ar v0 [] 0 (lab [], RawType.ord (ar [])) (profileEncWord exc L ar u ++ q)
        = encAt exc lab ar v0 u 0 (lab u, RawType.ord (ar u)) q := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro _ q; simp
  | append_singleton u i ih =>
      intro hu q
      obtain ⟨hu', hi⟩ := BranchingProcess.mem_sample_append_singleton.mp hu
      rw [profileEncWord_concat, List.append_assoc, ih hu']
      have hw : walk exc (RawType.ord (ar u)) 0 (profileSlot exc L ar u (i : ℕ) ++ q)
          = CPos.atSlot (i : ℕ) q := by
        simp only [walk_append, walk_profileSlot exc har hi, List.nil_append]
      rw [encAt_of_walk_atSlot exc lab ar v0 _ u 0 _ hw, gChild_of_lt u i.2]

/-- **The label of a skeleton vertex sits at its encoding.** -/
lemma encField_enc (exc : Family) {L : ℕ}
    (lab : GWord N → ℕ) {ar : GWord N → ℕ} (har : ArityBounded L ar) (v0 : ℕ) {u : GWord N}
    (hu : u ∈ sample ar) :
    encField exc lab ar v0 (profileEncWord exc L ar u) = (lab u, RawType.ord (ar u)) := by
  have h := encAt_nil_enc exc lab har v0 u hu []
  rw [List.append_nil] at h
  exact h

/-- **Every binary word lies in the cascade of a skeleton vertex**: it is the encoding of
the vertex followed by a path ending inside the cascade. -/
lemma exists_enc_inside (exc : Family) {L : ℕ}
    {ar : GWord N → ℕ} (har : ArityBounded L ar) (hs : SkelBounded L ar)
    (harN : ∀ u, ar u ≤ N) (w : List Bool) :
    ∃ u, u ∈ sample ar ∧ ∃ p, w = profileEncWord exc L ar u ++ p ∧
      ∃ t o, walk exc (RawType.ord (ar u)) 0 p = CPos.inside t o := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨[], BranchingProcess.nil_mem_sample _, [], by simp, _, _, walk_nil _ _ _⟩
  | append_singleton w b ih =>
      obtain ⟨u, hu, p, rfl, t, o, hw⟩ := ih
      have hv : validS (0, RawType.ord (ar u)) := (hs u hu).1
      obtain ⟨hvt, -, -⟩ := walk_inside_valid exc p hv hw
      rcases hc : cChild exc o t b with ⟨o', t'⟩ | j
      · refine ⟨u, hu, p ++ [b], by rw [List.append_assoc], t', o', ?_⟩
        simp only [walk_append, hw, walk_cons_internal hc, walk_nil]
      · have hslot : walk exc (RawType.ord (ar u)) 0 (p ++ [b]) = CPos.atSlot j [] := by
          simp only [walk_append, hw, walk_cons_slot hc]
        have hj : j < ar u := by
          have := walk_atSlot_range exc (p ++ [b]) hv hslot
          change 0 ≤ j ∧ j < 0 + ar u at this
          omega
        have hjN : j < N := lt_of_lt_of_le hj (harN u)
        have huj : u ++ [⟨j, hjN⟩] ∈ sample ar :=
          BranchingProcess.mem_sample_append_singleton.mpr ⟨hu, hj⟩
        refine ⟨u ++ [⟨j, hjN⟩], huj, [], ?_, _, _, walk_nil _ _ _⟩
        rw [List.append_nil, List.append_assoc, profileEncWord_concat]
        congr 1
        exact walk_atSlot_unique exc _ _ hv hslot (walk_profileSlot exc har hj)

/-- **Off the encoded skeleton the label is `v₀`**: an internal cascade vertex carries
the state of the one-vertex shape. -/
lemma encField_of_not_image (exc : Family) {L : ℕ}
    (lab : GWord N → ℕ) {ar : GWord N → ℕ} (har : ArityBounded L ar) (hs : SkelBounded L ar)
    (harN : ∀ u, ar u ≤ N) (v0 : ℕ) {w : List Bool}
    (hw : ¬ ∃ u, u ∈ sample ar ∧ w = profileEncWord exc L ar u) :
    (encField exc lab ar v0 w).1 = v0 := by
  obtain ⟨u, hu, p, rfl, t, o, hwalk⟩ := exists_enc_inside exc har hs harN w
  rcases p with _ | ⟨b, p⟩
  · exact absurd ⟨u, hu, by simp⟩ hw
  · rw [encField, encAt_nil_enc exc lab har v0 u hu,
      encAt_of_walk_inside exc lab ar v0 (b :: p) u 0 _ hwalk (by simp)]

/-- **The prefix closure of the encoded skeleton is `𝔹`**: every binary word is a prefix
of the encoding of a skeleton vertex. -/
lemma profileEnc_inClosure (exc : Family) {L : ℕ}
    {ar : GWord N → ℕ} (har : ArityBounded L ar) (hs : SkelBounded L ar)
    (harN : ∀ u, ar u ≤ N) (w : List Bool) :
    (profileEnc exc L ar har).InClosure (bnat w) := by
  obtain ⟨u, hu, p, rfl, t, o, hwalk⟩ := exists_enc_inside exc har hs harN w
  have hv : validS (0, RawType.ord (ar u)) := (hs u hu).1
  obtain ⟨hvt, ho1, ho2⟩ := walk_inside_valid exc p hv hwalk
  have ht2 : 2 ≤ servedC t := by
    cases t with
    | ord k => simpa [validS, servedC] using hvt
    | rem τ =>
        change τ ≠ MTree.leaf at hvt
        cases τ with
        | leaf => exact (hvt rfl).elim
        | node l r | gnode l r =>
            have hl := MTree.leaves_pos l
            have hr := MTree.leaves_pos r
            simp only [servedC, MTree.leaves]
            omega
  change o + servedC t ≤ 0 + ar u at ho2
  have hL : ar u ≤ L := (hs u hu).2
  -- the slot `o` lies below the internal vertex
  have hpath := walk_slotPathF exc L hvt (by omega) (le_refl o) (by omega)
  have hslot : walk exc (RawType.ord (ar u)) 0 (p ++ slotPathF exc L t o o) = CPos.atSlot o [] := by
    simp only [walk_append, hwalk, hpath]
  have hj : o < ar u := by omega
  have hjN : o < N := lt_of_lt_of_le hj (harN u)
  have huj : u ++ [⟨o, hjN⟩] ∈ sample ar :=
    BranchingProcess.mem_sample_append_singleton.mpr ⟨hu, hj⟩
  refine ⟨u ++ [⟨o, hjN⟩], huj, ?_⟩
  rw [bnat_prefix_iff, profileEnc_enc, profileEncWord_concat]
  refine List.prefix_append_right_inj _ |>.mpr ?_
  refine ⟨slotPathF exc L t o o, ?_⟩
  exact walk_atSlot_unique exc _ _ hv hslot (walk_profileSlot exc har hj)


lemma labelAt_statesOf {V X : Type} : ∀ (n : ℕ) (x : FullLab (V × X) n) (w : List Bool),
    labelAt n (statesOf n x) w = (labelAt n x w).1
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | n + 1, x, false :: w => labelAt_statesOf n x.2.1 w
  | n + 1, x, true :: w => labelAt_statesOf n x.2.2 w

/-- Reading the state-only encoding agrees with the geometric label field. -/
lemma labelAt_encodedStates (C : Family) (lab ar : GWord N → ℕ) (v0 : ℕ) {n : ℕ}
    {w : List Bool} (hw : w.length ≤ n) :
    labelAt n (encodedStates C lab ar v0 n) w = (encField C lab ar v0 w).1 := by
  rw [encodedStates, labelAt_statesOf, labelAt_encLab C lab ar v0 hw]

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
  rw [bushAt, BranchingProcess.bushOf, dite_eq_right h']

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

/-- The skeleton arities of a bushy sample bounded by `L` give a bounded arity field. -/
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
lemma exists_partner_bFamily {L : ℕ} (exc : Family)
    {c : GWord N → ℕ} (hs : SkelBounded L (gArityAt c)) {D : ℝ} (hD : 1 ≤ D)
    {lab : GWord N → ℕ} {τ : GWord N → GShape}
    (hlab : ∀ u, u ∈ sample (gArityAt c) → lab u = gNetLab D (τ u))
    (hτ : ∀ u, u ∈ sample (gArityAt c) →
      MarkedQI (9 * D ^ 3) (gShapeSpace (gShapeAt c u)) (gShapeSpace (τ u)))
    (w : Word) :
    ∃ ρ : GShape, MarkedQI (9 * D ^ 3)
        (gShapeSpace ((profileEnc exc L (gArityAt c) (arityBounded_gArityAt hs)).bFamily
          (gShapeAt c) (bnat w)))
        (gShapeSpace ρ) ∧
      gNetLab D ρ = (encField exc lab (gArityAt c) 0 w).1 := by
  set E := profileEnc exc L (gArityAt c) (arityBounded_gArityAt hs) with hE
  have h9 : (1 : ℝ) ≤ 9 * D ^ 3 := by
    have := one_le_pow₀ (n := 3) hD
    nlinarith
  by_cases h : ∃ u, u ∈ sample (gArityAt c) ∧ w = profileEncWord exc L (gArityAt c) u
  · obtain ⟨u, hu, rfl⟩ := h
    refine ⟨τ u, ?_, ?_⟩
    · have hb : E.bFamily (gShapeAt c) (bnat (E.enc u)) = gShapeAt c u :=
        CascadeEnc.bFamily_enc (E := E) hu
      rw [hE, profileEnc_enc] at hb
      rw [hb]
      exact hτ u hu
    · rw [encField_enc exc lab (arityBounded_gArityAt hs) 0 hu, hlab u hu]
  · refine ⟨gOne, ?_, ?_⟩
    · have hb : E.bFamily (gShapeAt c) (bnat w) = gOne := by
        refine CascadeEnc.bFamily_of_not_isImage ?_
        rintro ⟨u, hu, hw⟩
        exact h ⟨u, hu, bnat_injective hw⟩
      rw [hb]
      exact markedQI_id h9 _
    · rw [gNetLab_gOne hD, encField_of_not_image exc lab (arityBounded_gArityAt hs) hs
        (gArityAt_le_alphabet c) 0 h]

/-- **The deterministic core of `thm:hairy-general`**: an alignment of the encoded label
fields of two bushy samples to within one class of `G_D`, the labels being the classes
of partners `9D³`-comparable to the shapes, gives a quasi-isometry of the two samples at
the constant `⌈216 L L'² (3·(3¹⁵D¹⁶)²)²⌉`. -/
theorem sample_qi_of_profile_match {L L' : ℕ} (exc exc' : Family) {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    (hc : IsGBushySample c) (hc' : IsGBushySample c')
    (hs : SkelBounded L (gArityAt c)) (hs' : SkelBounded L' (gArityAt c'))
    (hL : 1 ≤ L) (hL' : 1 ≤ L') {D : ℝ} (hD : 1 ≤ D)
    {lab : GWord N → ℕ} {lab' : GWord N' → ℕ} {τ : GWord N → GShape} {τ' : GWord N' → GShape}
    (hlab : ∀ u, u ∈ sample (gArityAt c) → lab u = gNetLab D (τ u))
    (hlab' : ∀ u, u ∈ sample (gArityAt c') → lab' u = gNetLab D (τ' u))
    (hτ : ∀ u, u ∈ sample (gArityAt c) →
      MarkedQI (9 * D ^ 3) (gShapeSpace (gShapeAt c u)) (gShapeSpace (τ u)))
    (hτ' : ∀ u, u ∈ sample (gArityAt c') →
      MarkedQI (9 * D ^ 3) (gShapeSpace (gShapeAt c' u)) (gShapeSpace (τ' u)))
    (hm : InfMatch (GraphMatching.compat (gNetGraph D))
      (fun n => encodedStates exc lab (gArityAt c) 0 n)
      (fun n => encodedStates exc' lab' (gArityAt c') 0 n)) :
    ∃ F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'},
      BranchingProcess.IsQIWith ⌈216 * L * L' ^ 2 * (3 * (14348907 * D ^ 16) ^ 2) ^ 2⌉₊
        (wordGraphN (· ∈ sample c)) (wordGraphN (· ∈ sample c')) F := by
  obtain ⟨π, hπ⟩ := exists_portrait_of_infMatchK _ hm
  set E := profileEnc exc L (gArityAt c) (arityBounded_gArityAt hs) with hE
  set E' := profileEnc exc' L' (gArityAt c') (arityBounded_gArityAt hs') with hE'
  have hC : (1 : ℝ) ≤ 14348907 * D ^ 16 := by
    have := one_le_pow₀ (n := 16) hD
    nlinarith
  have hK : (1 : ℝ) ≤ 3 * (14348907 * D ^ 16) ^ 2 := by nlinarith
  refine sample_qi_of_bShape_matching hc hc' E E' rfl rfl hL hL' hK π (fun w => ?_) (fun w => ?_)
  · exact ⟨fun _ => profileEnc_inClosure exc' _ hs' (gArityAt_le_alphabet c') _,
      fun _ => profileEnc_inClosure exc _ hs (gArityAt_le_alphabet c) _⟩
  · obtain ⟨ρ, hρ, hρl⟩ := exists_partner_bFamily exc hs hD hlab hτ w
    obtain ⟨ρ', hρ', hρl'⟩ := exists_partner_bFamily exc' hs' hD hlab' hτ' (autOf π w)
    have hrel := hπ w
    rw [labelAt_encodedStates _ _ _ _ le_rfl,
      labelAt_encodedStates _ _ _ _ (by rw [autOf_length])] at hrel
    have hcompat : gNetLab D ρ = gNetLab D ρ' ∨ (gNetGraph D).Adj (gNetLab D ρ) (gNetLab D ρ') := by
      rw [hρl, hρl']
      exact hrel
    rcases crossRelabel_qi_compat hD hρ hρ' hcompat with h | h
    · exact h.mono (by positivity) (by nlinarith)
    · exact markedQI_symm hC h


/-! ### The geometric bound in terms of profile height -/

/-- The remaining depth of an internal profile type. -/
def typeHeight (C : Family) : RawType → ℕ
  | .ord k => (C.tree k).height
  | .rem τ => τ.height

def childHeight (C : Family) : ChildK → ℕ
  | .internal _ t => typeHeight C t
  | .slot _ => 0

lemma childHeight_subtreeKind (C : Family) (off : ℕ) (τ : MTree) :
    childHeight C (subtreeKind off τ) = τ.height := by
  cases τ <;> rfl

lemma treeStep_child_height_lt (C : Family) (off : ℕ) {τ : MTree}
    (hne : τ ≠ MTree.leaf) (b : Bool) :
    childHeight C (bif b then (treeStep off τ).2 else (treeStep off τ).1) < τ.height := by
  cases τ with
  | leaf => exact (hne rfl).elim
  | node l r | gnode l r =>
      cases b <;> simp only [treeStep, Bool.cond_false, Bool.cond_true, childHeight_subtreeKind,
        MTree.height] <;> omega

lemma cChild_height_lt (C : Family) {t : RawType} (ht : validS (0, t))
    (off : ℕ) (b : Bool) : childHeight C (cChild C off t b) < typeHeight C t := by
  cases t with
  | ord k =>
      obtain ⟨l, r, h | h⟩ := C.root k
      · exact treeStep_child_height_lt C off (by rw [h]; simp) b
      · exact treeStep_child_height_lt C off (by rw [h]; simp) b
  | rem τ => exact treeStep_child_height_lt C off ht b

/-- Any path terminating at a leaf is no longer than the profile height. -/
lemma walk_atSlot_length_le (C : Family) :
    ∀ (p : List Bool) {t : RawType}, validS (0, t) → ∀ {off j : ℕ},
      walk C t off p = CPos.atSlot j [] → p.length ≤ typeHeight C t
  | [], t, _, off, j, h => by simp [walk] at h
  | b :: p, t, ht, off, j, h => by
      have hlt := cChild_height_lt C ht off b
      obtain ⟨-, -, hv, -, -⟩ := cChild_range C ht off b
      rcases hc : cChild C off t b with ⟨o, t'⟩ | k
      · rw [walk_cons_internal hc] at h
        rw [hc] at hv hlt
        have hp := walk_atSlot_length_le C p hv h
        change typeHeight C t' < typeHeight C t at hlt
        simp only [List.length_cons]
        omega
      · rw [walk_cons_slot hc, CPos.atSlot.injEq] at h
        rw [hc] at hlt
        simp only [childHeight] at hlt
        rw [h.2]
        simpa using Nat.succ_le_of_lt hlt

lemma profileSlot_height_le (C : Family) {A : ℕ} {ar : GWord N → ℕ}
    (har : ArityBounded A ar) {u : GWord N} {j : ℕ} (hj : j < ar u) :
    (profileSlot C A ar u j).length ≤ (C.tree (ar u)).height :=
  walk_atSlot_length_le C _ (t := RawType.ord (ar u))
    (har u (by omega)).1 (walk_profileSlot C har hj)

/-- The same encoding with its sharp geometric input: a bound on profile heights.
The arity bound is used only as fuel for computing the ordered leaf slots. -/
def profileEncHeight (C : Family) (A L : ℕ) (ar : GWord N → ℕ)
    (har : ArityBounded A ar) (hheight : ∀ u, ar u ≠ 0 → (C.tree (ar u)).height ≤ L) :
    CascadeEnc N L where
  k := ar
  enc := profileEncWord C A ar
  slot := profileSlot C A ar
  enc_nil := rfl
  enc_concat := profileEncWord_concat C A ar
  slot_ne_nil := (profileEnc C A ar har).slot_ne_nil
  slot_length_le := fun u i hi => (profileSlot_height_le C har hi).trans (hheight u (by omega))
  slot_prefix := (profileEnc C A ar har).slot_prefix

@[simp] lemma profileEncHeight_enc (C : Family) (A L : ℕ) (ar : GWord N → ℕ)
    (har : ArityBounded A ar) (hheight : ∀ u, ar u ≠ 0 → (C.tree (ar u)).height ≤ L) :
    (profileEncHeight C A L ar har hheight).enc = profileEncWord C A ar := rfl

lemma profileEncHeight_inClosure (C : Family) {A L : ℕ} {ar : GWord N → ℕ}
    (har : ArityBounded A ar) (hs : SkelBounded A ar)
    (hheight : ∀ u, ar u ≠ 0 → (C.tree (ar u)).height ≤ L)
    (harN : ∀ u, ar u ≤ N) (w : List Bool) :
    (profileEncHeight C A L ar har hheight).InClosure (bnat w) :=
  profileEnc_inClosure C har hs harN w

end ChainClasses.Profile
