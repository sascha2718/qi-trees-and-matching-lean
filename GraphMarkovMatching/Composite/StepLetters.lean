/-
The concrete screen-ledger input of the composite two-law programme, part one of six
(`arbitrary_offspring_matching.tex`, `thm:screen-rows`): the bounded tameness envelope and
the letter box `cLetterBox`, the debt index `cIdx` with its orientation dispatchers,
coordinates and gates, the boxing of raw data, the embedding of the three debt classes
into the ledger, orientation pruning and the height-0 rows, the successor letters, member
counters and target sets, and the common and priced target sets.  The matrices follow in
`StepMatrices`.
-/
import GraphMarkovMatching.Composite.Debt
import GraphMarkovMatching.Process.Factorize

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### The bounded tameness envelope and the letter box -/

/-- Bounded tameness: the reachability envelope `cTame` sharpened by the
marker-stage certificate: a reachable marker is either at stage `0` or
records `2 ^ (i + 1) ≤ a`, so its stage is bounded by the running
value. -/
def cTameB (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ) : Option CtrC → Prop
  | none => True
  | some (CtrC.ord j) => j ≤ N ∧ exc j = none
  | some (CtrC.mark a b i) => a ≤ N ∧ b ≤ N ∧ (i = 0 ∨ 2 ^ (i + 1) ≤ a)

/-- The components of a common bounded counter are boundedly tame. -/
lemma cTameB_comps_ord (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none) {k : ℕ} (hk : k ≤ N)
    (hexc : exc k = none) :
    cTameB exc N (cComp0 exc (CtrC.ord k))
      ∧ cTameB exc N (cComp1 exc (CtrC.ord k)) := by
  rw [cComp0_ord_none hexc, cComp1_ord_none hexc]
  rcases Nat.lt_or_ge k 3 with h2 | h3
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact ⟨trivial, trivial⟩
  · rcases Nat.lt_or_ge k 4 with h4 | h4
    · rw [if_neg (by omega), if_pos (by omega : k = 3),
        if_neg (by omega)]
      exact ⟨⟨by omega, hN 2 (by omega)⟩, trivial⟩
    · rw [if_pos h4, if_pos h4]
      exact ⟨⟨by omega, hN _ (by omega)⟩, ⟨by omega, hN _ (by omega)⟩⟩

/-- The components of a bounded marker are boundedly tame: the next
marker regenerates the stage certificate from the halving rule. -/
lemma cTameB_markComp (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none) {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (i : ℕ) :
    cTameB exc N (markComp0 a b i) ∧ cTameB exc N (markComp1 a b i) := by
  have hval : val a i ≤ a := Nat.div_le_self a (2 ^ i)
  rcases Nat.lt_or_ge (val a i) 3 with h2 | h3
  · rw [markComp0, if_neg (by omega), if_neg (by omega),
      markComp1, if_neg (by omega), if_neg (by omega)]
    exact ⟨⟨hb, hN b hb⟩, trivial⟩
  · rcases Nat.lt_or_ge (val a i) 4 with h4 | h4
    · have h3' : val a i = 3 := by omega
      rw [markComp0, if_neg (by omega), if_pos h3',
        markComp1, if_neg (by omega), if_pos h3']
      exact ⟨⟨by omega, hN 2 (by omega)⟩, ⟨hb, hN b hb⟩⟩
    · rw [markComp0, if_pos h4, markComp1, if_pos h4]
      have hstage : 2 ^ (i + 1 + 1) ≤ a := by
        have hdiv : 4 * 2 ^ i ≤ a := by
          have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos i)).mp h4
          omega
        have hpow : 2 ^ (i + 1 + 1) = 4 * 2 ^ i := by
          rw [pow_succ, pow_succ]
          ring
        omega
      exact ⟨⟨ha, hb, Or.inr hstage⟩, ⟨by omega, hN _ (by omega)⟩⟩

/-- One spawn step preserves bounded tameness. -/
lemma cTameB_of_cSpawn (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    {l m : Option CtrC} (hl : cTameB exc N l) (hsp : cSpawn exc ν l m) :
    cTameB exc N m := by
  cases l with
  | none =>
      obtain ⟨k, hk, hor⟩ := hsp
      rcases hexc : exc k with _ | p
      · have hcm := cTameB_comps_ord exc N hN (hch k hk hexc) hexc
        rcases hor with rfl | rfl
        · exact hcm.1
        · exact hcm.2
      · obtain ⟨h1, h2⟩ := hdeclB k p hexc
        have hcm := cTameB_markComp exc N hN h1 h2 0
        rcases hor with rfl | rfl
        · rw [cComp0_ord_some hexc]
          exact hcm.1
        · rw [cComp1_ord_some hexc]
          exact hcm.2
  | some c =>
      cases c with
      | ord j =>
          have hl' : j ≤ N ∧ exc j = none := hl
          have hcm := cTameB_comps_ord exc N hN hl'.1 hl'.2
          rcases hsp with rfl | rfl
          · exact hcm.1
          · exact hcm.2
      | mark a b i =>
          have hl' : a ≤ N ∧ b ≤ N ∧ (i = 0 ∨ 2 ^ (i + 1) ≤ a) := hl
          have hcm := cTameB_markComp exc N hN hl'.1 hl'.2.1 i
          rcases hsp with rfl | rfl
          · rw [cComp0_mark]
            exact hcm.1
          · rw [cComp1_mark]
            exact hcm.2

/-- Reachable letters are boundedly tame. -/
theorem cReach_cTameB (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N) :
    ∀ {n : ℕ} {l : Option CtrC}, cReach exc ν n l → cTameB exc N l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      have hl' : l = none := hl
      subst hl'
      trivial
  | succ n ih =>
      intro l hl
      obtain ⟨l', hl', hsp⟩ := hl
      exact cTameB_of_cSpawn exc ν N hN hch hdeclB (ih hl') hsp

/-- The letter box: the fresh letter, the common counters up to `N`, and
the markers with data and stage up to `N`.  Every boundedly tame letter
lies in the box. -/
def cLetterBox (N : ℕ) : Finset (Option CtrC) :=
  insert none
    (((Finset.range (N + 1)).image fun j => some (CtrC.ord j))
      ∪ ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)
            ×ˢ Finset.range (N + 1)).image
          fun t => some (CtrC.mark t.1 t.2.1 t.2.2)))

lemma none_mem_cLetterBox (N : ℕ) : none ∈ cLetterBox N :=
  Finset.mem_insert_self _ _

lemma ord_mem_cLetterBox {N j : ℕ} (hj : j ≤ N) :
    some (CtrC.ord j) ∈ cLetterBox N := by
  refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

lemma mark_mem_cLetterBox {N a b i : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (hi : i ≤ N) : some (CtrC.mark a b i) ∈ cLetterBox N := by
  refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
  refine Finset.mem_image.mpr ⟨(a, b, i), ?_, rfl⟩
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨by omega, by omega, by omega⟩

/-- **`eq:composite-cardinals`, the alphabet count**: the letter box has exactly
`n_A = (N+1)³ + N + 2` letters. -/
lemma cLetterBox_card (N : ℕ) :
    (cLetterBox N).card = (N + 1) ^ 3 + N + 2 := by
  have hord : Function.Injective fun j : ℕ => some (CtrC.ord j) := by
    intro a b h
    simpa using h
  have hmark : Function.Injective
      fun t : ℕ × ℕ × ℕ => some (CtrC.mark t.1 t.2.1 t.2.2) := by
    intro a b h
    simp only [Option.some.injEq, CtrC.mark.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hnone : (none : Option CtrC) ∉
      ((Finset.range (N + 1)).image fun j => some (CtrC.ord j))
      ∪ ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)
            ×ˢ Finset.range (N + 1)).image
          fun t => some (CtrC.mark t.1 t.2.1 t.2.2)) := by
    simp
  have hdisj : Disjoint
      ((Finset.range (N + 1)).image fun j => some (CtrC.ord j))
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)
            ×ˢ Finset.range (N + 1)).image
          fun t => some (CtrC.mark t.1 t.2.1 t.2.2)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨j, -, rfl⟩ := ha
    obtain ⟨t, -, ht⟩ := hb
    simp at ht
  rw [cLetterBox, Finset.card_insert_of_notMem hnone,
    Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hord,
    Finset.card_image_of_injective _ hmark]
  simp only [Finset.card_product, Finset.card_range]
  ring

/-- Boundedly tame letters lie in the box: the stage certificate forces
`i ≤ N` through `i + 1 < 2 ^ (i + 1)`. -/
lemma cTameB_mem_cLetterBox {exc : ℕ → Option (ℕ × ℕ)} {N : ℕ}
    {l : Option CtrC} (hl : cTameB exc N l) : l ∈ cLetterBox N := by
  cases l with
  | none => exact none_mem_cLetterBox N
  | some c =>
      cases c with
      | ord j => exact ord_mem_cLetterBox hl.1
      | mark a b i =>
          obtain ⟨ha, hb, hi⟩ := hl
          refine mark_mem_cLetterBox ha hb ?_
          rcases hi with rfl | hi
          · omega
          · have hlt : i + 1 < 2 ^ (i + 1) :=
              Nat.lt_pow_self (by omega)
            omega

/-- Reachable letters lie in the box. -/
theorem cReach_mem_cLetterBox (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)
    (N : ℕ) (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    {n : ℕ} {l : Option CtrC} (hl : cReach exc ν n l) :
    l ∈ cLetterBox N :=
  cTameB_mem_cLetterBox (cReach_cTameB exc ν N hN hch hdeclB hl)

/-! ### The debt index: orientation dispatchers, coordinates, gates -/

section Index

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ)

/-- The exceptional chart of an orientation: `false` reads side 1. -/
def cExcO : Bool → ℕ → Option (ℕ × ℕ)
  | false => exc1
  | true => exc2

/-- The offspring law of an orientation. -/
noncomputable def cNuO : Bool → PMF ℕ
  | false => ν1
  | true => ν2

/-- The support of an orientation. -/
def cKO : Bool → Finset ℕ
  | false => K1
  | true => K2

@[simp] lemma cExcO_false : cExcO exc1 exc2 false = exc1 := rfl
@[simp] lemma cExcO_true : cExcO exc1 exc2 true = exc2 := rfl
@[simp] lemma cNuO_false : cNuO ν1 ν2 false = ν1 := rfl
@[simp] lemma cNuO_true : cNuO ν1 ν2 true = ν2 := rfl
@[simp] lemma cKO_false : cKO K1 K2 false = K1 := rfl
@[simp] lemma cKO_true : cKO K1 K2 true = K2 := rfl

lemma cLetO_eq (o : Bool) (l : Option CtrC) (h : ℕ) :
    cLetO μ v0 exc1 exc2 ν1 ν2 o l h
      = cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 l h := by
  cases o <;> rfl

/-- The zero-list laws of a raw letter set. -/
noncomputable def cZLaws (o : Bool) (Z : Finset (Option CtrC)) (h : ℕ) :
    List (PMF (FullLab (CState V) h)) :=
  Z.toList.map fun l => cLetO μ v0 exc1 exc2 ν1 ν2 o l h

lemma mem_cZLaws {o : Bool} {Z : Finset (Option CtrC)} {h : ℕ}
    {ρ : PMF (FullLab (CState V) h)} :
    ρ ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 o Z h
      ↔ ∃ l ∈ Z, ρ = cLetO μ v0 exc1 exc2 ν1 ν2 o l h := by
  rw [cZLaws, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Finset.mem_toList.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Finset.mem_toList.mpr hl, rfl⟩

/-- The tilt weight of an optional tilt letter: `none` is the unit
normalization, `some l` the restricted inverse degree of the letter. -/
noncomputable def cTiltW (o : Bool) (t : Option (Option CtrC)) (h : ℕ) :
    FullLab (CState V) h → ℝ≥0∞ :=
  match t with
  | none => fun _ => 1
  | some l => WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 o l h)
      (fullSim (cRel Rv) h)

@[simp] lemma cTiltW_none (o : Bool) (h : ℕ) :
    cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 o none h = fun _ => 1 := rfl

@[simp] lemma cTiltW_some (o : Bool) (l : Option CtrC) (h : ℕ) :
    cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 o (some l) h
      = WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 o l h)
          (fullSim (cRel Rv) h) := rfl

/-- The raw coordinate interpretation: the letter screen of an
orientation, a source letter, a zero-list letter set, and an optional
tilt letter. -/
noncomputable def cInterp (h : ℕ) (o : Bool) (s : Option CtrC)
    (Z : Finset (Option CtrC)) (t : Option (Option CtrC)) : ℝ≥0∞ :=
  screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o s h) (fullSim (cRel Rv) h)
    (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z h)
    (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t h)

/-- The reachability gate of a raw coordinate: joint reachability of
all letters at a common level, and a nonempty zero list. -/
def cGateR (o : Bool) (n : ℕ) (s : Option CtrC) (Z : Finset (Option CtrC))
    (t : Option (Option CtrC)) : Prop :=
  cReachO exc1 exc2 ν1 ν2 o n s
    ∧ (∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l)
    ∧ (∀ l ∈ t, cReachO exc1 exc2 ν1 ν2 (!o) n l)
    ∧ Z.Nonempty

end Index

/-- The boxed letters. -/
abbrev cLB (N : ℕ) : Type := {l : Option CtrC // l ∈ cLetterBox N}

/-- The debt index: an orientation, a boxed source letter, a boxed
zero-list letter set, and an optional boxed tilt letter. -/
abbrev cIdx (N : ℕ) : Type :=
  Bool × cLB N × Finset (cLB N) × Option (cLB N)

/-- The raw source letter of a coordinate. -/
def cRawS {N : ℕ} (i : cIdx N) : Option CtrC := i.2.1.1

/-- The raw zero-list letter set of a coordinate. -/
def cRawZ {N : ℕ} (i : cIdx N) : Finset (Option CtrC) :=
  i.2.2.1.image Subtype.val

/-- The raw tilt letter of a coordinate. -/
def cRawT {N : ℕ} (i : cIdx N) : Option (Option CtrC) :=
  i.2.2.2.map Subtype.val

section Coord

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)

/-- The coordinate value at a height. -/
noncomputable def cVal (N h : ℕ) (i : cIdx N) : ℝ≥0∞ :=
  cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h i.1 (cRawS i) (cRawZ i) (cRawT i)

/-- The ledger vector: the coordinate value gated by joint reachability
at a common level, mirroring the debts of `Main`. -/
noncomputable def cE (N h : ℕ) (i : cIdx N) : ℝ≥0∞ :=
  ⨆ n : ℕ,
    ⨆ _ : cGateR exc1 exc2 ν1 ν2 i.1 n (cRawS i) (cRawZ i) (cRawT i),
      cVal α Rv μ v0 exc1 exc2 ν1 ν2 N h i

lemma cE_eq_zero_of_not_gate {N h : ℕ} {i : cIdx N}
    (hng : ¬ ∃ n, cGateR exc1 exc2 ν1 ν2 i.1 n (cRawS i) (cRawZ i)
      (cRawT i)) :
    cE α Rv μ v0 exc1 exc2 ν1 ν2 N h i = 0 := by
  refine le_antisymm ?_ zero_le
  exact iSup_le fun n => iSup_le fun hg => absurd ⟨n, hg⟩ hng

end Coord

/-! ### Boxing raw data -/

/-- The boxed lift of a raw letter set. -/
def cLiftB (N : ℕ) (s : Finset (Option CtrC)) : Finset (cLB N) :=
  (cLetterBox N).attach.filter fun x => x.1 ∈ s

lemma mem_cLiftB {N : ℕ} {s : Finset (Option CtrC)} {x : cLB N} :
    x ∈ cLiftB N s ↔ x.1 ∈ s := by
  rw [cLiftB, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_attach _ _, h⟩⟩

lemma cLiftB_image_val {N : ℕ} {s : Finset (Option CtrC)}
    (hs : ∀ l ∈ s, l ∈ cLetterBox N) :
    (cLiftB N s).image Subtype.val = s := by
  ext l
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_cLiftB.mp hx
  · intro hl
    exact ⟨⟨l, hs l hl⟩, mem_cLiftB.mpr hl, rfl⟩

lemma cLiftB_card_le {N : ℕ} (s : Finset (Option CtrC)) :
    (cLiftB N s).card ≤ s.card := by
  refine Finset.card_le_card_of_injOn Subtype.val
    (fun x hx => mem_cLiftB.mp hx) ?_
  exact Subtype.val_injective.injOn

/-- The coordinate of raw data: boxed source, lifted zero list, boxed
tilt. -/
def cMk (N : ℕ) (o : Bool) {s : Option CtrC} (hs : s ∈ cLetterBox N)
    (Z : Finset (Option CtrC)) {t : Option (Option CtrC)}
    (ht : ∀ l ∈ t, l ∈ cLetterBox N) : cIdx N :=
  (o, ⟨s, hs⟩, cLiftB N Z,
    t.pmap (fun l hl => (⟨l, hl⟩ : cLB N)) ht)

@[simp] lemma cMk_fst {N : ℕ} (o : Bool) {s : Option CtrC}
    (hs : s ∈ cLetterBox N) (Z : Finset (Option CtrC))
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N) :
    (cMk N o hs Z ht).1 = o := rfl

lemma cRawS_cMk {N : ℕ} (o : Bool) {s : Option CtrC}
    (hs : s ∈ cLetterBox N) (Z : Finset (Option CtrC))
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N) :
    cRawS (cMk N o hs Z ht) = s := rfl

lemma cRawZ_cMk {N : ℕ} (o : Bool) {s : Option CtrC}
    (hs : s ∈ cLetterBox N) {Z : Finset (Option CtrC)}
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N)
    (hZ : ∀ l ∈ Z, l ∈ cLetterBox N) :
    cRawZ (cMk N o hs Z ht) = Z :=
  cLiftB_image_val hZ

lemma cRawT_cMk {N : ℕ} (o : Bool) {s : Option CtrC}
    (hs : s ∈ cLetterBox N) (Z : Finset (Option CtrC))
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N) :
    cRawT (cMk N o hs Z ht) = t := by
  rw [cRawT]
  cases t <;> rfl

section GateVal

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)

/-- A gated raw coordinate with boxed data sits below its ledger
entry. -/
lemma cInterp_le_cE (N h : ℕ) (o : Bool) {s : Option CtrC}
    {Z : Finset (Option CtrC)} {t : Option (Option CtrC)}
    (hs : s ∈ cLetterBox N) (hZ : ∀ l ∈ Z, l ∈ cLetterBox N)
    (ht : ∀ l ∈ t, l ∈ cLetterBox N) {n : ℕ}
    (hg : cGateR exc1 exc2 ν1 ν2 o n s Z t) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s Z t
      ≤ cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hs Z ht) := by
  have hval : cVal α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hs Z ht)
      = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s Z t := by
    rw [cVal, cRawZ_cMk o hs ht hZ, cRawT_cMk, cRawS_cMk, cMk_fst]
  have hg' : cGateR exc1 exc2 ν1 ν2 (cMk N o hs Z ht).1 n
      (cRawS (cMk N o hs Z ht)) (cRawZ (cMk N o hs Z ht))
      (cRawT (cMk N o hs Z ht)) := by
    rw [cRawZ_cMk o hs ht hZ, cRawT_cMk, cRawS_cMk, cMk_fst]
    exact hg
  rw [cE]
  exact le_trans (le_of_eq hval.symm)
    (le_iSup_of_le n (le_iSup_of_le hg' le_rfl))

/-- A gated raw coordinate with boxed data sits below the ledger
supremum. -/
lemma cInterp_le_iSup_cE (N h : ℕ) (o : Bool) {s : Option CtrC}
    {Z : Finset (Option CtrC)} {t : Option (Option CtrC)}
    (hs : s ∈ cLetterBox N) (hZ : ∀ l ∈ Z, l ∈ cLetterBox N)
    (ht : ∀ l ∈ t, l ∈ cLetterBox N) {n : ℕ}
    (hg : cGateR exc1 exc2 ν1 ν2 o n s Z t) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s Z t
      ≤ ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j :=
  le_trans (cInterp_le_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o hs hZ ht hg)
    (le_iSup _ _)

end GateVal

lemma option_forall_mem_none {A : Type} {P : A → Prop} :
    ∀ l ∈ (none : Option A), P l := by
  simp

lemma option_forall_mem_some {A : Type} {P : A → Prop} {a : A}
    (ha : P a) : ∀ l ∈ some a, P l := by
  simpa using ha

/-! ### The debt classes embed into the ledger -/

section DebtLe

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)

/-- Reachable letters of either orientation lie in the box. -/
lemma cReachO_mem_cLetterBox
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hch1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 → exc1 k = none → k ≤ N)
    (hdeclB1 : ∀ k p, exc1 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hch2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 → exc2 k = none → k ≤ N)
    (hdeclB2 : ∀ k p, exc2 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (o : Bool) {n : ℕ} {l : Option CtrC}
    (hl : cReachO exc1 exc2 ν1 ν2 o n l) : l ∈ cLetterBox N := by
  cases o with
  | false =>
      exact cReach_mem_cLetterBox exc1 ν1 N (fun j hj => (hN j hj).1)
        hch1 hdeclB1 hl
  | true =>
      exact cReach_mem_cLetterBox exc2 ν2 N (fun j hj => (hN j hj).2)
        hch2 hdeclB2 hl

/-- The zero-mass debt coordinates are singleton unit coordinates. -/
private lemma zMass_eq_cInterp (h : ℕ) (o : Bool) (l1 l2 : Option CtrC) :
    zMass (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h)
        (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h) (fullSim (cRel Rv) h)
      = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 {l2} none := by
  rw [zMass_eq_screenE_unit, cInterp]
  refine screenE_congr_mem _ _ (fun ρ => ?_) _
  rw [mem_cZLaws, List.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨l2, Finset.mem_singleton_self _, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rw [Finset.mem_singleton.mp hl]

/-- The one-member screen debt coordinates are singleton tilted
coordinates. -/
private lemma scrOne_eq_cInterp (h : ℕ) (o : Bool)
    (l1 l2 l3 : Option CtrC) :
    screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h) (fullSim (cRel Rv) h)
        [cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h]
        (WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l3 h)
          (fullSim (cRel Rv) h))
      = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 {l2} (some l3) := by
  rw [cInterp]
  refine screenE_congr_mem _ _ (fun ρ => ?_) _
  rw [mem_cZLaws, List.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨l2, Finset.mem_singleton_self _, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rw [Finset.mem_singleton.mp hl]

/-- The two-member screen debt coordinates are pair tilted
coordinates. -/
private lemma scrTwo_eq_cInterp (h : ℕ) (o : Bool)
    (l1 l2 l2' l3 : Option CtrC) :
    screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h) (fullSim (cRel Rv) h)
        [cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h,
          cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2' h]
        (WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l3 h)
          (fullSim (cRel Rv) h))
      = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 {l2, l2'} (some l3) := by
  rw [cInterp]
  refine screenE_congr_mem _ _ (fun ρ => ?_) _
  rw [mem_cZLaws, List.mem_cons, List.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨l2, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨l2', Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact Or.inl rfl
    · rw [Finset.mem_singleton.mp hl]
      exact Or.inr rfl

/-- **The debt embeds into the ledger** (`debt_le` of
`ScreenLedgerInput`): the three debt classes of `Main` are gated
coordinates of the index. -/
theorem cDebt_le_iSup_cE
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hch1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 → exc1 k = none → k ≤ N)
    (hdeclB1 : ∀ k p, exc1 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hch2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 → exc2 k = none → k ≤ N)
    (hdeclB2 : ∀ k p, exc2 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (h : ℕ) :
    cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h
      ≤ ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j := by
  have hbox : ∀ (o : Bool) {n : ℕ} {l : Option CtrC},
      cReachO exc1 exc2 ν1 ν2 o n l → l ∈ cLetterBox N := by
    intro o n l hl
    exact cReachO_mem_cLetterBox exc1 exc2 ν1 ν2 N hN hch1 hdeclB1
      hch2 hdeclB2 o hl
  rw [cDebt]
  refine sup_le ?_ (sup_le ?_ ?_)
  · rw [cZeroDebt]
    refine iSup_le fun o => iSup_le fun n => iSup_le fun l1 =>
      iSup_le fun l2 => iSup_le fun r1 => iSup_le fun r2 => ?_
    rw [zMass_eq_cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 l2]
    refine cInterp_le_iSup_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o
      (hbox o r1)
      (fun l hl => by rw [Finset.mem_singleton.mp hl]; exact hbox (!o) r2)
      option_forall_mem_none
      (n := n) ⟨r1, ?_, option_forall_mem_none, Finset.singleton_nonempty _⟩
    intro l hl
    rw [Finset.mem_singleton.mp hl]
    exact r2
  · rw [cScrOneDebt]
    refine iSup_le fun o => iSup_le fun n => iSup_le fun l1 =>
      iSup_le fun l2 => iSup_le fun l3 => iSup_le fun r1 =>
        iSup_le fun r2 => iSup_le fun r3 => ?_
    rw [scrOne_eq_cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 l2 l3]
    refine cInterp_le_iSup_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o
      (hbox o r1)
      (fun l hl => by rw [Finset.mem_singleton.mp hl]; exact hbox (!o) r2)
      (option_forall_mem_some (hbox (!o) r3))
      (n := n) ⟨r1, ?_, option_forall_mem_some r3,
        Finset.singleton_nonempty _⟩
    intro l hl
    rw [Finset.mem_singleton.mp hl]
    exact r2
  · rw [cScrTwoDebt]
    refine iSup_le fun o => iSup_le fun n => iSup_le fun l1 =>
      iSup_le fun l2 => iSup_le fun l2' => iSup_le fun l3 =>
        iSup_le fun r1 => iSup_le fun r2 => iSup_le fun r2' =>
          iSup_le fun r3 => ?_
    rw [scrTwo_eq_cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 l2 l2' l3]
    have hZ : ∀ l ∈ ({l2, l2'} : Finset (Option CtrC)),
        cReachO exc1 exc2 ν1 ν2 (!o) n l := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact r2
      · rw [Finset.mem_singleton.mp hl]
        exact r2'
    refine cInterp_le_iSup_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o
      (hbox o r1) (fun l hl => hbox (!o) (hZ l hl))
      (option_forall_mem_some (hbox (!o) r3))
      (n := n) ⟨r1, hZ, option_forall_mem_some r3,
        Finset.insert_nonempty _ _⟩

end DebtLe

/-! ### Orientation pruning and the height-0 rows -/

section Base

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)

/-- The fresh-diagonal pruning in either orientation
(`thm:exact-pruning`): the fresh source of a side against a zero list
containing the opposite fresh law vanishes, for any normalization. -/
lemma cPruneO (o : Bool)
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (h : ℕ) (zs : List (PMF (FullLab (CState V) h)))
    (hmem : cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 h ∈ zs)
    (W : FullLab (CState V) h → ℝ≥0∞) :
    screenE (cT (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 h)
      (fullSim (cRel Rv) h) zs W = 0 := by
  cases o with
  | false =>
      exact screenE_cT_opposite_eq_zero Rv μ v0 exc1 exc2 ν1 ν2 N hRv hμ0
        hN hdeclN1 hcharged1 h zs hmem W
  | true =>
      exact screenE_cT_opposite_eq_zero Rv μ v0 exc2 exc1 ν2 ν1 N hRv hμ0
        (fun j hj => ⟨(hN j hj).2, (hN j hj).1⟩) hdeclN2 hcharged2
        h zs hmem W

/-- A fresh-diagonal raw coordinate vanishes at every height. -/
lemma cInterp_fdiag_eq_zero (o : Bool)
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (h : ℕ) {Z : Finset (Option CtrC)} (hfz : none ∈ Z)
    (t : Option (Option CtrC)) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o none Z t = 0 := by
  rw [cInterp, cLetO_eq, cLet_none]
  refine cPruneO Rv μ v0 exc1 exc2 ν1 ν2 N o hRv hμ0 hN hdeclN1
    hcharged1 hdeclN2 hcharged2 h _ ?_ _
  exact (mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
    ⟨none, hfz, by rw [cLetO_eq, cLet_none]⟩

/-- The good degree of a point law is the relation indicator. -/
private lemma rE_pure_ite {X : Type} (a : X) (R : X → X → Prop) (x : X) :
    rE (PMF.pure a) R x = if R x a then 1 else 0 := by
  rw [rE, tsum_congr fun y => show (if R x y then (PMF.pure a) y else 0)
      = (PMF.pure a) y * (if R x y then 1 else 0) from by
    by_cases hy : R x y
    · rw [if_pos hy, if_pos hy, mul_one]
    · rw [if_neg hy, if_neg hy, mul_zero], tsum_pure_mul]

/-- At height 0 a frozen tilt is at most one. -/
private lemma WresD_cZ_zero_le_one (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)
    (c3 : CtrC) (x : FullLab (CState V) 0) :
    WresD α (cZ exc μ ν v0 c3 0) (fullSim (cRel Rv) 0) x ≤ 1 := by
  by_cases h0 : rE (cZ exc μ ν v0 c3 0) (fullSim (cRel Rv) 0) x = 0
  · rw [WresD, if_pos h0]
    exact zero_le
  · rw [← rE_rpow_neg_eq_WresD _ _ _ h0]
    have h1 : rE (cZ exc μ ν v0 c3 0) (fullSim (cRel Rv) 0) x = 1 := by
      rw [show cZ exc μ ν v0 c3 0 = PMF.pure (leaf (v0, c3)) from rfl,
        rE_pure_ite] at h0 ⊢
      by_cases hx : fullSim (cRel Rv) 0 x (leaf (v0, c3))
      · rw [if_pos hx]
      · rw [if_neg hx] at h0
        exact absurd rfl h0
    rw [h1, ENNReal.one_rpow]

/-- **The height-0 rows** (`base` of `ScreenLedgerInput`,
`thm:zero-interface`): every ledger coordinate starts below
`2 * etaG` under `μ(v0) ≥ 1/2`. -/
theorem cE_base_le (hα : 1 ≤ α)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (i : cIdx N) :
    cE α Rv μ v0 exc1 exc2 ν1 ν2 N 0 i ≤ 2 * etaG α Rv μ := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hαpos : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα
  refine iSup_le fun n => iSup_le fun hg => ?_
  obtain ⟨hr1, hrZ, hrT, hZne⟩ := hg
  rw [cVal]
  rcases hsrc : cRawS i with _ | c1
  · -- fresh source
    by_cases hfz : none ∈ cRawZ i
    · rw [cInterp_fdiag_eq_zero α Rv μ v0 exc1 exc2 ν1 ν2 N i.1 hRv hμ0
        hN hdeclN1 hcharged1 hdeclN2 hcharged2 0 hfz]
      exact zero_le
    · obtain ⟨l0, hl0⟩ := hZne
      rcases hl0eq : l0 with _ | c2
      · exact absurd (hl0eq ▸ hl0) hfz
      · subst hl0eq
        have hmem : cZ (cExcO exc1 exc2 (!i.1)) μ (cNuO ν1 ν2 (!i.1)) v0
            c2 0 ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 (!i.1) (cRawZ i) 0 :=
          (mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
            ⟨some c2, hl0, by rw [cLetO_eq, cLet_some]⟩
        rw [cInterp, cLetO_eq, cLet_none]
        rcases htl : cRawT i with _ | l3
        · rw [cTiltW_none]
          exact cScr_base_cT_source_le Rv μ v0
            (cExcO exc1 exc2 i.1) (cExcO exc1 exc2 (!i.1))
            (cNuO ν1 ν2 i.1) (cNuO ν1 ν2 (!i.1)) c2 hmem
            (fun x => le_refl 1) (2 * etaG α Rv μ)
            (cFarMass_le_two_etaG α Rv μ v0 hα0 hsymm hhalf)
        · rcases l3 with _ | c3
          · rw [cTiltW_some, cLetO_eq, cLet_none]
            exact cScr_base_cT_source_tiltT_le α Rv μ v0
              (cExcO exc1 exc2 i.1) (cExcO exc1 exc2 (!i.1))
              (cNuO ν1 ν2 i.1) (cNuO ν1 ν2 (!i.1)) hαpos hsymm hhalf
              c2 hmem
          · rw [cTiltW_some, cLetO_eq, cLet_some]
            exact cScr_base_cT_source_le Rv μ v0
              (cExcO exc1 exc2 i.1) (cExcO exc1 exc2 (!i.1))
              (cNuO ν1 ν2 i.1) (cNuO ν1 ν2 (!i.1)) c2 hmem
              (WresD_cZ_zero_le_one α Rv μ v0
                (cExcO exc1 exc2 (!i.1)) (cNuO ν1 ν2 (!i.1)) c3)
              (2 * etaG α Rv μ)
              (cFarMass_le_two_etaG α Rv μ v0 hα0 hsymm hhalf)
  · -- frozen source: dead by reflexivity at the root
    obtain ⟨l0, hl0⟩ := hZne
    have hmem : (∃ c₂, cZ (cExcO exc1 exc2 (!i.1)) μ (cNuO ν1 ν2 (!i.1))
          v0 c₂ 0 ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 (!i.1) (cRawZ i) 0)
        ∨ cT (cExcO exc1 exc2 (!i.1)) μ (cNuO ν1 ν2 (!i.1)) v0 0
          ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 (!i.1) (cRawZ i) 0 := by
      rcases hl0eq : l0 with _ | c2
      · subst hl0eq
        exact Or.inr ((mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
          ⟨none, hl0, by rw [cLetO_eq, cLet_none]⟩)
      · subst hl0eq
        exact Or.inl ⟨c2, (mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
          ⟨some c2, hl0, by rw [cLetO_eq, cLet_some]⟩⟩
    rw [cInterp, cLetO_eq, cLet_some,
      cScr_base_cZ_source_eq_zero Rv μ v0
        (cExcO exc1 exc2 i.1) (cExcO exc1 exc2 (!i.1))
        (cNuO ν1 ν2 i.1) (cNuO ν1 ν2 (!i.1)) (hRv v0) hμ0 c1 hmem]
    exact zero_le

end Base

/-! ### Successor letters, member counters, and target sets -/

/-- The raw successor letters of a zero-list member on a target side:
the components of its cell, the fresh letter expanding to the
components of every charged cell. -/
def cSuccRaw (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ) :
    Option CtrC → Finset (Option CtrC)
  | some c => {cComp0 exc c, cComp1 exc c}
  | none => Kf.biUnion fun k =>
      {cComp0 exc (CtrC.ord k), cComp1 exc (CtrC.ord k)}

/-- The member counters of a zero-list letter set: frozen letters
contribute their counters, the fresh letter the whole support. -/
noncomputable def cMsL (Kf : Finset ℕ) (Z : Finset (Option CtrC)) :
    List CtrC :=
  Z.toList.flatMap fun l =>
    match l with
    | some c => [c]
    | none => Kf.toList.map CtrC.ord

lemma mem_cMsL {Kf : Finset ℕ} {Z : Finset (Option CtrC)} {c : CtrC} :
    c ∈ cMsL Kf Z
      ↔ some c ∈ Z ∨ (none ∈ Z ∧ ∃ k ∈ Kf, c = CtrC.ord k) := by
  rw [cMsL, List.mem_flatMap]
  constructor
  · rintro ⟨l, hl, hc⟩
    rcases l with _ | c'
    · refine Or.inr ⟨Finset.mem_toList.mp hl, ?_⟩
      obtain ⟨k, hk, hkc⟩ := List.mem_map.mp hc
      exact ⟨k, Finset.mem_toList.mp hk, hkc.symm⟩
    · rcases List.mem_singleton.mp hc with rfl
      exact Or.inl (Finset.mem_toList.mp hl)
  · rintro (hc | ⟨hz, k, hk, rfl⟩)
    · exact ⟨some c, Finset.mem_toList.mpr hc, List.mem_singleton_self _⟩
    · exact ⟨none, Finset.mem_toList.mpr hz,
        List.mem_map.mpr ⟨k, Finset.mem_toList.mpr hk, rfl⟩⟩

/-- The component letter list of the member counters. -/
noncomputable def cCompL (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (Z : Finset (Option CtrC)) : List (Option CtrC) :=
  (cMsL Kf Z).flatMap fun c => [cComp0 exc c, cComp1 exc c]

lemma mem_cCompL {exc : ℕ → Option (ℕ × ℕ)} {Kf : Finset ℕ}
    {Z : Finset (Option CtrC)} {l : Option CtrC} :
    l ∈ cCompL exc Kf Z
      ↔ ∃ c ∈ cMsL Kf Z, l = cComp0 exc c ∨ l = cComp1 exc c := by
  rw [cCompL, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hl⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨c, hc, Or.inl rfl⟩
    · rcases List.mem_singleton.mp hl with rfl
      exact ⟨c, hc, Or.inr rfl⟩
  · rintro ⟨c, hc, rfl | rfl⟩
    · exact ⟨c, hc, List.mem_cons_self ..⟩
    · exact ⟨c, hc, List.mem_cons.mpr
        (Or.inr (List.mem_singleton_self _))⟩

/-- The raw zero-list successor set. -/
def cZSuccR (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (Z : Finset (Option CtrC)) : Finset (Option CtrC) :=
  Z.biUnion (cSuccRaw exc Kf)

/-- The raw successor set collects exactly the components of the member
counters. -/
lemma mem_cZSuccR {exc : ℕ → Option (ℕ × ℕ)} {Kf : Finset ℕ}
    {Z : Finset (Option CtrC)} {l : Option CtrC} :
    l ∈ cZSuccR exc Kf Z
      ↔ ∃ c ∈ cMsL Kf Z, l = cComp0 exc c ∨ l = cComp1 exc c := by
  rw [cZSuccR, Finset.mem_biUnion]
  constructor
  · rintro ⟨lz, hlz, hl⟩
    rcases lz with _ | c'
    · rw [cSuccRaw, Finset.mem_biUnion] at hl
      obtain ⟨k, hk, hl⟩ := hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact ⟨CtrC.ord k, mem_cMsL.mpr (Or.inr ⟨hlz, k, hk, rfl⟩),
          Or.inl rfl⟩
      · rcases Finset.mem_singleton.mp hl with rfl
        exact ⟨CtrC.ord k, mem_cMsL.mpr (Or.inr ⟨hlz, k, hk, rfl⟩),
          Or.inr rfl⟩
    · rcases Finset.mem_insert.mp hl with rfl | hl
      · exact ⟨c', mem_cMsL.mpr (Or.inl hlz), Or.inl rfl⟩
      · rcases Finset.mem_singleton.mp hl with rfl
        exact ⟨c', mem_cMsL.mpr (Or.inl hlz), Or.inr rfl⟩
  · rintro ⟨c, hc, hor⟩
    rcases mem_cMsL.mp hc with hz | ⟨hz, k, hk, rfl⟩
    · refine ⟨some c, hz, ?_⟩
      rw [cSuccRaw]
      rcases hor with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · refine ⟨none, hz, ?_⟩
      rw [cSuccRaw, Finset.mem_biUnion]
      refine ⟨k, hk, ?_⟩
      rcases hor with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The length budget of a constant-length flat map. -/
private lemma length_flatMap_pair {A B : Type} (l : List A)
    (f g : A → B) :
    (l.flatMap fun a => [f a, g a]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega

lemma cMsL_length_le (Kf : Finset ℕ) (Z : Finset (Option CtrC)) :
    (cMsL Kf Z).length ≤ Z.card * max Kf.card 1 := by
  rw [cMsL, List.length_flatMap]
  calc (Z.toList.map fun l =>
        (match l with
          | some c => [c]
          | none => Kf.toList.map CtrC.ord).length).sum
      ≤ (Z.toList.map fun l =>
          (match l with
            | some c => [c]
            | none => Kf.toList.map CtrC.ord).length).length
          • max Kf.card 1 := by
        refine List.sum_le_card_nsmul _ _ fun x hx => ?_
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
        rcases l with _ | c
        · rw [List.length_map, Finset.length_toList]
          exact le_max_left _ _
        · exact le_max_right _ _
    _ = Z.card * max Kf.card 1 := by
        rw [List.length_map, Finset.length_toList, smul_eq_mul]

lemma cCompL_length_le (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (Z : Finset (Option CtrC)) :
    (cCompL exc Kf Z).length ≤ 2 * (Z.card * max Kf.card 1) := by
  rw [cCompL, length_flatMap_pair]
  exact Nat.mul_le_mul_left 2 (cMsL_length_le Kf Z)

/-! ### The common and priced target sets -/

/-- The common source moves: components of a frozen counter, components
of the charged common cells below the fresh letter. -/
def cSrcC (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ) :
    Option CtrC → Finset (Option CtrC)
  | some c => {cComp0 exc c, cComp1 exc c}
  | none => (Kf.filter fun k => exc k = none).biUnion fun k =>
      {cComp0 exc (CtrC.ord k), cComp1 exc (CtrC.ord k)}

/-- The exceptional-entrance source moves below the fresh letter. -/
def cSrcE (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ) :
    Option CtrC → Finset (Option CtrC)
  | some _ => ∅
  | none => (Kf.filter fun k => exc k ≠ none).biUnion fun k =>
      {cComp0 exc (CtrC.ord k), cComp1 exc (CtrC.ord k)}

/-- The common tilt moves: the unit stays, a frozen tilt descends to a
component; the fresh tilt has no common move. -/
def cTiltC (exc : ℕ → Option (ℕ × ℕ)) :
    Option (Option CtrC) → Finset (Option (Option CtrC))
  | none => {none}
  | some (some c3) => {some (cComp0 exc c3), some (cComp1 exc c3)}
  | some none => ∅

/-- The priced tilt moves: the fresh tilt renews to a component of a
charged cell. -/
def cTiltP (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ) :
    Option (Option CtrC) → Finset (Option (Option CtrC))
  | some none => Kf.biUnion fun k =>
      {some (cComp0 exc (CtrC.ord k)), some (cComp1 exc (CtrC.ord k))}
  | none => ∅
  | some (some _) => ∅

/-- The boxed lift of a set of optional tilt letters. -/
def cLiftO (N : ℕ) (s : Finset (Option (Option CtrC))) :
    Finset (Option (cLB N)) :=
  s.biUnion fun t =>
    match t with
    | none => {none}
    | some l => (cLiftB N {l}).image some

lemma pmap_mem_cLiftO {N : ℕ} {s : Finset (Option (Option CtrC))}
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N)
    (hts : t ∈ s) :
    t.pmap (fun l hl => (⟨l, hl⟩ : cLB N)) ht ∈ cLiftO N s := by
  rw [cLiftO, Finset.mem_biUnion]
  refine ⟨t, hts, ?_⟩
  cases t with
  | none => exact Finset.mem_singleton_self _
  | some l =>
      refine Finset.mem_image.mpr ⟨⟨l, ht l rfl⟩, ?_, rfl⟩
      exact mem_cLiftB.mpr (Finset.mem_singleton_self _)

lemma cLiftO_card_le (N : ℕ) (s : Finset (Option (Option CtrC))) :
    (cLiftO N s).card ≤ s.card := by
  refine le_trans (Finset.card_biUnion_le) ?_
  calc ∑ t ∈ s, (match t with
        | none => ({none} : Finset (Option (cLB N)))
        | some l => (cLiftB N {l}).image some).card
      ≤ ∑ _t ∈ s, 1 := by
        refine Finset.sum_le_sum fun t _ => ?_
        rcases t with _ | l
        · exact le_of_eq (Finset.card_singleton _)
        · exact le_trans Finset.card_image_le
            (le_trans (cLiftB_card_le _) (le_of_eq (Finset.card_singleton _)))
    _ = s.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- The support budget. -/
def cMx (K1 K2 : Finset ℕ) : ℕ := max (max K1.card K2.card) 1

lemma one_le_cMx (K1 K2 : Finset ℕ) : 1 ≤ cMx K1 K2 :=
  le_max_right _ _

lemma cKO_card_le_cMx (K1 K2 : Finset ℕ) (o : Bool) :
    (cKO K1 K2 o).card ≤ cMx K1 K2 := by
  cases o with
  | false => exact le_trans (le_max_left _ _) (le_max_left _ _)
  | true => exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- The singleton-screen length budget. -/
def cLz (N : ℕ) (K1 K2 : Finset ℕ) : ℕ :=
  2 * ((cLetterBox N).card * cMx K1 K2)

private lemma card_pair_le {A : Type} [DecidableEq A] (a b : A) :
    ({a, b} : Finset A).card ≤ 2 :=
  le_trans (Finset.card_insert_le _ _)
    (by rw [Finset.card_singleton])

private lemma biUnion_pair_card_le {A B : Type} [DecidableEq B]
    (s : Finset A) (f g : A → B) :
    (s.biUnion fun a => ({f a, g a} : Finset B)).card ≤ 2 * s.card := by
  refine le_trans (Finset.card_biUnion_le) ?_
  calc ∑ a ∈ s, ({f a, g a} : Finset B).card
      ≤ ∑ _a ∈ s, 2 := Finset.sum_le_sum fun a _ => card_pair_le _ _
    _ = 2 * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma cSrcC_card_le (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (s : Option CtrC) : (cSrcC exc Kf s).card ≤ 2 * max Kf.card 1 := by
  rcases s with _ | c
  · rw [cSrcC]
    refine le_trans (biUnion_pair_card_le _ _ _) ?_
    have := Finset.card_filter_le Kf fun k => exc k = none
    have hK : Kf.card ≤ max Kf.card 1 := le_max_left _ _
    omega
  · rw [cSrcC]
    have h2 : (2 : ℕ) ≤ 2 * max Kf.card 1 := by
      have : 1 ≤ max Kf.card 1 := le_max_right _ _
      omega
    exact le_trans (card_pair_le _ _) h2

lemma cSrcE_card_le (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (s : Option CtrC) : (cSrcE exc Kf s).card ≤ 2 * max Kf.card 1 := by
  rcases s with _ | c
  · rw [cSrcE]
    refine le_trans (biUnion_pair_card_le _ _ _) ?_
    have := Finset.card_filter_le Kf fun k => exc k ≠ none
    have hK : Kf.card ≤ max Kf.card 1 := le_max_left _ _
    omega
  · rw [cSrcE]
    simp

lemma cTiltC_card_le (exc : ℕ → Option (ℕ × ℕ))
    (t : Option (Option CtrC)) : (cTiltC exc t).card ≤ 2 := by
  rcases t with _ | (_ | c3)
  · rw [cTiltC]
    simp
  · rw [cTiltC]
    simp
  · rw [cTiltC]
    exact card_pair_le _ _

lemma cTiltP_card_le (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (t : Option (Option CtrC)) :
    (cTiltP exc Kf t).card ≤ 2 * max Kf.card 1 := by
  rcases t with _ | (_ | c3)
  · rw [cTiltP]
    simp
  · rw [cTiltP]
    refine le_trans (biUnion_pair_card_le _ _ _) ?_
    have hK : Kf.card ≤ max Kf.card 1 := le_max_left _ _
    omega
  · rw [cTiltP]
    simp


end Composite
end GraphMarkovMatching
