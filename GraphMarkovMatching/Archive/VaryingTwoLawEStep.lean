/-
The concrete screen-step assembly for the finite two-law ledger.

Every asymmetric Hall row has two kinds of successor screens.  Live
successors remain in the directed nilpotent block.  A successor which has
left the live alphabet is discharged into the ordinary two-law scalar.  The
lemmas below carry out this split before the six source/normalization rows are
assembled.

This module deliberately stops at the useful screen-row inequality.  The
former end-to-end scalar closure was deleted because its unweighted raw-
failure term contained `2 * M`; see `unweighted_twoLaw_closure_forces_zero`
in `Obstructions/Semigroup.lean`.
-/
import GraphMarkovMatching.Archive.VaryingTwoLawClosure
import GraphMarkovMatching.Closure.EStep
import GraphMarkovMatching.Archive.VaryingCrossERowForced
import GraphMarkovMatching.Archive.VaryingCrossERowFresh

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (νL νR : PMF ℕ) (v0 : V)

/-- A symmetric screen inhomogeneity.  `genG` contains the six Hall-row
outputs; `D * a` is the finite charge for formal diagonal successors diverted
back to the ordinary two-law envelope.  This is a screen-row bound, not a
closed two-law recurrence. -/
noncomputable def twoLawG (T RT FM FT D : ℝ≥0∞) (nA : ℕ)
    (a b : ℝ≥0∞) : ℝ≥0∞ :=
  genG α T RT FM FT nA a
      ((1 + ENNReal.ofReal α) * a + b) + D * a

lemma twoLawG_mono (T RT FM FT D : ℝ≥0∞) (nA : ℕ)
    {a a' b b' : ℝ≥0∞} (ha : a ≤ a') (hb : b ≤ b') :
    twoLawG α T RT FM FT D nA a b
      ≤ twoLawG α T RT FM FT D nA a' b' := by
  have hscreen : (1 + ENNReal.ofReal α) * a + b
      ≤ (1 + ENNReal.ofReal α) * a' + b' :=
    add_le_add (mul_le_mul_right ha _) hb
  exact add_le_add (genG_mono α T RT FM FT nA ha hscreen)
    (mul_le_mul' le_rfl ha)

/-- The ordinary return envelope used for pruned asymmetric screens. -/
noncomputable def twoLawScreenB (a b : ℝ≥0∞) : ℝ≥0∞ :=
  (1 + ENNReal.ofReal α) * a + b

/-- A common coefficient for the successor sum in all six screen rows. -/
noncomputable def twoLawScreenC (T RT : ℝ≥0∞) : ℝ≥0∞ :=
  4 + 4 * (RT * T)

/-! ### Absorbing the six row outputs -/

private lemma twoLawG_absorb_none
    {T RT FM FT D a e B Eplus MV : ℝ≥0∞} {nA nz : ℕ}
    (hB : B = (1 + ENNReal.ofReal α) * a + e)
    (hnA : nz ≤ nA) (hSucc : 2 * Eplus ≤ D * a + MV) :
    FM + (2 * Eplus + (nz * B) * (nz * B))
      ≤ twoLawG α T RT FM FT D nA a e + MV := by
  have hnAb : (nz : ℝ≥0∞) * B ≤ (nA : ℝ≥0∞) * B :=
    mul_le_mul' (Nat.cast_le.mpr hnA) le_rfl
  have hone : ∀ x : ℝ≥0∞, x ≤ (1 + RT * T) * x := fun x =>
    le_trans (le_of_eq (one_mul x).symm) (mul_le_mul' le_self_add le_rfl)
  have hquad : ((nz : ℝ≥0∞) * B) * ((nz : ℝ≥0∞) * B)
      ≤ (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
          + 2 * (((nA : ℝ≥0∞) * B) * ((nA : ℝ≥0∞) * B))) :=
    le_trans (mul_le_mul' hnAb hnAb)
      (le_trans (le_trans (le_of_eq (one_mul _).symm)
          (mul_le_mul' (by norm_num : (1 : ℝ≥0∞) ≤ 2) le_rfl))
        (le_trans le_add_self (hone _)))
  rw [twoLawG, genG, ← hB]
  calc
    FM + (2 * Eplus + (nz * B) * (nz * B))
        = (FM + (nz * B) * (nz * B)) + 2 * Eplus := by ring
    _ ≤ (FM + FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a))))
          + (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
            + 2 * ((nA * B) * (nA * B)))) + (D * a + MV) :=
      add_le_add (add_le_add le_self_add hquad) hSucc
    _ = (FM + FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a))))
          + (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
            + 2 * ((nA * B) * (nA * B))) + D * a) + MV := by ring

private lemma twoLawG_absorb_forced
    {T RT FM FT D a e B Eplus MV : ℝ≥0∞} {nA nz : ℕ}
    (hB : B = (1 + ENNReal.ofReal α) * a + e)
    (hnA : nz ≤ nA) (hSucc : 4 * Eplus ≤ D * a + MV) :
    4 * Eplus + 4 * (ENNReal.ofReal α * a * B)
        + 2 * ((nz * B) * (nz * B))
      ≤ twoLawG α T RT FM FT D nA a e + MV := by
  have hnAb : (nz : ℝ≥0∞) * B ≤ (nA : ℝ≥0∞) * B :=
    mul_le_mul' (Nat.cast_le.mpr hnA) le_rfl
  have hone : ∀ x : ℝ≥0∞, x ≤ (1 + RT * T) * x := fun x =>
    le_trans (le_of_eq (one_mul x).symm) (mul_le_mul' le_self_add le_rfl)
  have hcore : 4 * (ENNReal.ofReal α * a * B)
        + 2 * ((nz * B) * (nz * B))
      ≤ (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
        + 2 * ((nA * B) * (nA * B))) :=
    le_trans (add_le_add le_rfl (mul_le_mul' le_rfl
      (mul_le_mul' hnAb hnAb))) (hone _)
  rw [twoLawG, genG, ← hB]
  calc
    4 * Eplus + 4 * (ENNReal.ofReal α * a * B)
          + 2 * ((nz * B) * (nz * B))
        = (4 * (ENNReal.ofReal α * a * B)
          + 2 * ((nz * B) * (nz * B))) + 4 * Eplus := by ring
    _ ≤ (FM + FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a))))
          + (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
            + 2 * ((nA * B) * (nA * B)))) + (D * a + MV) :=
      add_le_add (le_trans hcore le_add_self) hSucc
    _ = (FM + FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a))))
          + (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
            + 2 * ((nA * B) * (nA * B))) + D * a) + MV := by ring

private lemma twoLawG_absorb_fresh
    {T RT FM FT D a e B Eplus MV : ℝ≥0∞} {nA nz : ℕ}
    (hB : B = (1 + ENNReal.ofReal α) * a + e)
    (hnA : nz ≤ nA)
    (hSucc : 4 * (RT * T) * Eplus ≤ D * a + MV) :
    FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
          * (1 + ENNReal.ofReal α * a))))
        + RT * T * (4 * Eplus + 4 * (ENNReal.ofReal α * a * B)
          + 2 * ((nz * B) * (nz * B)))
      ≤ twoLawG α T RT FM FT D nA a e + MV := by
  have hnAb : (nz : ℝ≥0∞) * B ≤ (nA : ℝ≥0∞) * B :=
    mul_le_mul' (Nat.cast_le.mpr hnA) le_rfl
  have hcore : RT * T * (4 * (ENNReal.ofReal α * a * B)
        + 2 * ((nz * B) * (nz * B)))
      ≤ (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
        + 2 * ((nA * B) * (nA * B))) :=
    le_trans (mul_le_mul' le_rfl (add_le_add le_rfl
      (mul_le_mul' le_rfl (mul_le_mul' hnAb hnAb))))
      (mul_le_mul' le_add_self le_rfl)
  rw [twoLawG, genG, ← hB]
  calc
    FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
          * (1 + ENNReal.ofReal α * a))))
        + RT * T * (4 * Eplus + 4 * (ENNReal.ofReal α * a * B)
          + 2 * ((nz * B) * (nz * B)))
        = (FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a))))
          + RT * T * (4 * (ENNReal.ofReal α * a * B)
            + 2 * ((nz * B) * (nz * B))))
          + 4 * (RT * T) * Eplus := by ring
    _ ≤ (FM + FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a))))
          + (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
            + 2 * ((nA * B) * (nA * B)))) + (D * a + MV) :=
      add_le_add (add_le_add le_add_self hcore) hSucc
    _ = (FM + FT * (T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a))))
          + (1 + RT * T) * (4 * (ENNReal.ofReal α * a * B)
            + 2 * ((nA * B) * (nA * B))) + D * a) + MV := by ring

/-- The Fk-free property is preserved by an asymmetric screen successor. -/
lemma crossScreenSucc_zf {SL SR : Finset ℕ} {sc sc' : GScreen}
    (hsc' : sc' ∈ crossScreenSucc SL SR sc) :
    ZFtgt sc'.cell ∧ (∀ t ∈ sc'.zlist, ZFtgt t)
      ∧ ∀ u, sc'.norm = some u → ZFtgt u := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hsc'
  obtain ⟨hcell, hnorm⟩ := Finset.mem_product.mp hp
  refine ⟨ZFtgt_of_mem_tgtSucc hcell, ?_, ?_⟩
  · intro t ht
    obtain ⟨w, hw, hwt⟩ := Finset.mem_biUnion.mp ht
    exact ZFtgt_of_mem_tgtSucc hwt
  · intro u hu
    cases hs : sc.norm with
    | none =>
        rw [hs] at hnorm
        simp only [normSucc, Finset.mem_singleton] at hnorm
        rw [hnorm] at hu
        exact absurd hu (by simp)
    | some w =>
        rw [hs] at hnorm
        simp only [normSucc] at hnorm
        obtain ⟨t, ht, htu⟩ := Finset.mem_image.mp hnorm
        rw [← htu] at hu
        obtain rfl := Option.some_inj.mp hu
        exact ZFtgt_of_mem_tgtSucc ht

/-- The live part of a directed successor sum is exactly represented by the
restricted cross matrix. -/
lemma crossReach_live_sum_le_mulVec
    {N : ℕ} {SL SR : Finset ℕ} {sc : GScreen}
    (hsc : sc ∈ crossScreenIndex N) (CW : ℝ≥0∞) (h : ℕ) :
    CW * (∑ sc' ∈ (crossScreenSucc SL SR sc).filter
        (fun sc' => sc' ∈ crossScreenIndex N),
      crossInterpScreen α Rv μ νL νR v0 h sc')
      ≤ mulVec (crossReachN N SL SR CW)
          (fun j => crossInterpScreen α Rv μ νL νR v0 h j.val) ⟨sc, hsc⟩ := by
  rw [Finset.mul_sum]
  rw [show mulVec (crossReachN N SL SR CW)
        (fun j => crossInterpScreen α Rv μ νL νR v0 h j.val) ⟨sc, hsc⟩
      = ∑ j : {sc // sc ∈ crossScreenIndex N},
          (if j.val ∈ crossScreenSucc SL SR sc then CW else 0)
            * crossInterpScreen α Rv μ νL νR v0 h j.val from rfl]
  rw [show (∑ j : {sc // sc ∈ crossScreenIndex N},
      (if j.val ∈ crossScreenSucc SL SR sc then CW else 0)
        * crossInterpScreen α Rv μ νL νR v0 h j.val)
      = ∑ j ∈ Finset.univ.filter
          (fun j : {sc // sc ∈ crossScreenIndex N} =>
            j.val ∈ crossScreenSucc SL SR sc),
          (if j.val ∈ crossScreenSucc SL SR sc then CW else 0)
            * crossInterpScreen α Rv μ νL νR v0 h j.val from ?_]
  · exact le_of_eq (Finset.sum_bij
      (fun sc' hsc' => (⟨sc', (Finset.mem_filter.mp hsc').2⟩ :
        {sc // sc ∈ crossScreenIndex N}))
      (fun sc' hsc' => by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hsc').1⟩)
      (fun a _ b _ hab => congrArg Subtype.val hab)
      (fun j hj => ⟨j.val, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hj).2, j.property⟩, Subtype.ext rfl⟩)
      (fun sc' hsc' => by
        rw [if_pos (Finset.mem_filter.mp hsc').1]))
  · refine (Finset.sum_filter_of_ne fun j _ hne => ?_).symm
    by_contra hj
    rw [if_neg hj, zero_mul] at hne
    exact hne rfl

/-- Block-matrix evaluation in the forward orientation. -/
lemma twoLawN_true_eq (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞)
    (h : ℕ) (i : {sc // sc ∈ crossScreenIndex N}) :
    mulVec (twoLawN N SL SR CW) (twoLawE α Rv μ νL νR v0 N h) (true, i)
      = mulVec (crossReachN N SL SR CW)
          (fun j => crossInterpScreen α Rv μ νL νR v0 h j.val) i := by
  simp [mulVec, twoLawN, twoLawE, biCrossScreen, Fintype.sum_prod_type]

/-- Block-matrix evaluation in the reverse orientation. -/
lemma twoLawN_false_eq (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞)
    (h : ℕ) (i : {sc // sc ∈ crossScreenIndex N}) :
    mulVec (twoLawN N SL SR CW) (twoLawE α Rv μ νL νR v0 N h) (false, i)
      = mulVec (crossReachN N SR SL CW)
          (fun j => crossInterpScreen α Rv μ νR νL v0 h j.val) i := by
  simp [mulVec, twoLawN, twoLawE, biCrossScreen, Fintype.sum_prod_type]

/-- A complete directed successor row: nonlive successors return to the
ordinary scalar and live successors are collected by `crossReachN`. -/
lemma crossSucc_core_le
    {N : ℕ} {SL SR : Finset ℕ} (hα : 1 ≤ α)
    (hN : 2 ≤ N) (hSL : ∀ k ∈ SL, k ≤ N)
    (hSR : ∀ k ∈ SR, k ≤ N) (hSRne : SR.Nonempty)
    {sc : GScreen} (hsc : sc ∈ crossScreenIndex N)
    (C CW D : ℝ≥0∞) (hC : C ≤ CW)
    (hD : (screenUniv N).card * (C * (1 + ENNReal.ofReal α)) ≤ D)
    (h : ℕ) :
    C * (∑ sc' ∈ crossScreenSucc SL SR sc,
        crossInterpScreen α Rv μ νL νR v0 h sc')
      ≤ D * twoLawPsi α Rv μ νL νR v0 N h
        + mulVec (crossReachN N SL SR CW)
            (fun j => crossInterpScreen α Rv μ νL νR v0 h j.val) ⟨sc, hsc⟩ := by
  let M := twoLawPsi α Rv μ νL νR v0 N h
  let O := (1 + ENNReal.ofReal α) * M
  have hcross : sc ∈ crossLiveScreens N := (Finset.mem_filter.mp hsc).1
  have hsrc := Finset.mem_filter.mp hcross
  have huniv : sc ∈ screenUniv N := hsrc.1
  have hzne : sc.zlist.Nonempty := hsrc.2.1
  have hpt : ∀ sc' ∈ crossScreenSucc SL SR sc,
      C * crossInterpScreen α Rv μ νL νR v0 h sc'
        ≤ (if sc' ∈ crossScreenIndex N then 0 else C * O)
          + (if sc' ∈ crossScreenIndex N then
              CW * crossInterpScreen α Rv μ νL νR v0 h sc' else 0) := by
    intro sc' hsucc
    by_cases hlive : sc' ∈ crossScreenIndex N
    · rw [if_pos hlive, if_pos hlive, zero_add]
      exact mul_le_mul' hC le_rfl
    · rw [if_neg hlive, if_neg hlive, add_zero]
      refine mul_le_mul_right ?_ C
      have huniv' : sc' ∈ screenUniv N :=
        crossScreenSucc_subset hN hSL hSR huniv hsucc
      have hne' : sc'.zlist.Nonempty := by
        rw [crossScreenSucc_zlist hsucc]
        exact zsucc_nonempty hSRne hzne
      have hord := biCrossScreen_le_ordinary α Rv μ νL νR v0 hα
        huniv' hne' (crossScreenSucc_zf hsucc) (lr := true) (h := h)
      simpa [biCrossScreen, O, M] using hord
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun sc' hsucc => hpt sc' hsucc) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · calc
      (∑ sc' ∈ crossScreenSucc SL SR sc,
          if sc' ∈ crossScreenIndex N then 0 else C * O)
          ≤ ∑ _sc' ∈ crossScreenSucc SL SR sc, C * O :=
            Finset.sum_le_sum fun sc' _ => by
              split_ifs
              · exact zero_le
              · exact le_rfl
      _ = (crossScreenSucc SL SR sc).card * (C * O) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (screenUniv N).card * (C * O) := by
            exact mul_le_mul' (Nat.cast_le.mpr (Finset.card_le_card
              (crossScreenSucc_subset hN hSL hSR huniv))) le_rfl
      _ = ((screenUniv N).card * (C * (1 + ENNReal.ofReal α))) * M := by
            simp only [O]
            ring
      _ ≤ D * M := mul_le_mul' hD le_rfl
      _ = D * twoLawPsi α Rv μ νL νR v0 N h := rfl
  · have hlive := crossReach_live_sum_le_mulVec α Rv μ νL νR v0
        (SL := SL) (SR := SR) hsc CW h
    refine le_trans ?_ hlive
    rw [Finset.mul_sum]
    exact le_of_eq (by rw [Finset.sum_filter])

/-- Forward-orientation successor diversion into the full two-law matrix. -/
lemma crossSucc_true_le
    {N : ℕ} {SL SR : Finset ℕ} (hα : 1 ≤ α)
    (hN : 2 ≤ N) (hSL : ∀ k ∈ SL, k ≤ N)
    (hSR : ∀ k ∈ SR, k ≤ N) (hSRne : SR.Nonempty)
    {sc : GScreen} (hsc : sc ∈ crossScreenIndex N)
    (C CW D : ℝ≥0∞) (hC : C ≤ CW)
    (hD : (screenUniv N).card * (C * (1 + ENNReal.ofReal α)) ≤ D)
    (h : ℕ) :
    C * (∑ sc' ∈ crossScreenSucc SL SR sc,
        crossInterpScreen α Rv μ νL νR v0 h sc')
      ≤ D * twoLawPsi α Rv μ νL νR v0 N h
        + mulVec (twoLawN N SL SR CW)
            (twoLawE α Rv μ νL νR v0 N h) (true, ⟨sc, hsc⟩) := by
  rw [twoLawN_true_eq α Rv μ νL νR v0 N SL SR CW h ⟨sc, hsc⟩]
  exact crossSucc_core_le α Rv μ νL νR v0 hα hN hSL hSR hSRne hsc
    C CW D hC hD h

/-- Reverse-orientation successor diversion into the full two-law matrix. -/
lemma crossSucc_false_le
    {N : ℕ} {SL SR : Finset ℕ} (hα : 1 ≤ α)
    (hN : 2 ≤ N) (hSL : ∀ k ∈ SL, k ≤ N)
    (hSR : ∀ k ∈ SR, k ≤ N) (hLne : SL.Nonempty)
    {sc : GScreen} (hsc : sc ∈ crossScreenIndex N)
    (C CW D : ℝ≥0∞) (hC : C ≤ CW)
    (hD : (screenUniv N).card * (C * (1 + ENNReal.ofReal α)) ≤ D)
    (h : ℕ) :
    C * (∑ sc' ∈ crossScreenSucc SR SL sc,
        crossInterpScreen α Rv μ νR νL v0 h sc')
      ≤ D * twoLawPsi α Rv μ νL νR v0 N h
        + mulVec (twoLawN N SL SR CW)
            (twoLawE α Rv μ νL νR v0 N h) (false, ⟨sc, hsc⟩) := by
  rw [twoLawN_false_eq α Rv μ νL νR v0 N SL SR CW h ⟨sc, hsc⟩]
  rw [← twoLawPsi_swap α Rv μ νL νR v0 N h]
  exact crossSucc_core_le α Rv μ νR νL v0 hα hN hSR hSL hLne hsc
    C CW D hC hD h

/-! ### Bounded sub-successor screens -/

/-- Any nonempty sub-successor screen is controlled by the ordinary return
envelope plus the live-screen supremum.  This is the form needed for the
singleton Hall charges. -/
lemma crossSubScreen_le
    {N : ℕ} {SL SR : Finset ℕ} (hα : 1 ≤ α)
    (hN : 2 ≤ N) (hSL : ∀ k ∈ SL, k ≤ N)
    (hSR : ∀ k ∈ SR, k ≤ N) {sc : GScreen}
    (hsc : sc ∈ crossScreenIndex N) {c' : Tgt} {z' : Finset Tgt}
    {u' : Option Tgt} (hc' : c' ∈ tgtSucc SL sc.cell)
    (hz' : z' ⊆ zsucc SR sc.zlist) (hzne : z'.Nonempty)
    (hu' : u' ∈ normSucc SR sc.norm) (h : ℕ) :
    crossInterpScreen α Rv μ νL νR v0 h ⟨c', z', u'⟩
      ≤ twoLawScreenB α (twoLawPsi α Rv μ νL νR v0 N h)
          (⨆ i, twoLawE α Rv μ νL νR v0 N h i) := by
  have hcross : sc ∈ crossLiveScreens N := (Finset.mem_filter.mp hsc).1
  have huniv : sc ∈ screenUniv N := (Finset.mem_filter.mp hcross).1
  have hdata := mem_screenUniv.mp huniv
  have hcN : c' ∈ tgtUniv N := tgtSucc_subset hN hSL hdata.1 hc'
  have hzN : z' ⊆ tgtUniv N :=
    fun t ht => zsucc_subset hN hSR hdata.2.1 (hz' ht)
  have huN : ∀ u, u' = some u → u ∈ tgtUniv N := by
    intro u hu
    cases hs : sc.norm with
    | none =>
        rw [hs] at hu'
        simp only [normSucc, Finset.mem_singleton] at hu'
        rw [hu'] at hu
        exact absurd hu (by simp)
    | some w =>
        have hwN : w ∈ tgtUniv N := hdata.2.2 w hs
        rw [hs] at hu'
        simp only [normSucc] at hu'
        obtain ⟨t, ht, htu⟩ := Finset.mem_image.mp hu'
        rw [← htu] at hu
        obtain rfl := Option.some_inj.mp hu
        exact tgtSucc_subset hN hSR hwN ht
  have hzf : ZFtgt c' ∧ (∀ t ∈ z', ZFtgt t)
      ∧ ∀ u, u' = some u → ZFtgt u := by
    refine ⟨ZFtgt_of_mem_tgtSucc hc', ?_, ?_⟩
    · intro t ht
      obtain ⟨w, hw, hwt⟩ := Finset.mem_biUnion.mp (hz' ht)
      exact ZFtgt_of_mem_tgtSucc hwt
    · intro u hu
      cases hs : sc.norm with
      | none =>
          rw [hs] at hu'
          simp only [normSucc, Finset.mem_singleton] at hu'
          rw [hu'] at hu
          exact absurd hu (by simp)
      | some w =>
          rw [hs] at hu'
          simp only [normSucc] at hu'
          obtain ⟨t, ht, htu⟩ := Finset.mem_image.mp hu'
          rw [← htu] at hu
          obtain rfl := Option.some_inj.mp hu
          exact ZFtgt_of_mem_tgtSucc ht
  have hledger := biCrossScreen_le_ledger α Rv μ νL νR v0 hα
    (mem_screenUniv.mpr ⟨hcN, hzN, huN⟩) hzne hzf
    (lr := true) (h := h) (sc := (⟨c', z', u'⟩ : GScreen))
  simpa [twoLawScreenB, biCrossScreen] using hledger

/-! ### The six forward screen rows -/

/-- All six asymmetric screen rows in the left-to-right orientation. -/
theorem twoLaw_E_step_true
    {N : ℕ} (hα : 1 ≤ α) (hrefl : ∀ v, Rv v v)
    (SL SR : Finset ℕ) (hN : 2 ≤ N)
    (hLbd : ∀ k ∈ SL, k ≤ N) (hRbd : ∀ k ∈ SR, k ≤ N)
    (hLne : SL.Nonempty) (hRne : SR.Nonempty)
    (hLsupp : ∀ k : ℕ, (νL k : ℝ≥0∞) ≠ 0 ↔ k ∈ SL)
    (hRsupp : ∀ k : ℕ, (νR k : ℝ≥0∞) ≠ 0 ↔ k ∈ SR)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0)
    (T RT FM FT CW D : ℝ≥0∞)
    (hT : (∑' j, if (νR j : ℝ≥0∞) = 0 then 0
        else (νR j : ℝ≥0∞) ^ (-α)) ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM)
    (hFT : (∑' v, if Rv v v0 then 0
        else (μ v : ℝ≥0∞) * WresD α μ Rv v) ≤ FT)
    (hCW : twoLawScreenC T RT ≤ CW)
    (hD : (screenUniv N).card
        * (twoLawScreenC T RT * (1 + ENNReal.ofReal α)) ≤ D)
    (h : ℕ) (i : {sc // sc ∈ crossScreenIndex N}) :
    twoLawE α Rv μ νL νR v0 N (h + 1) (true, i)
      ≤ twoLawG α T RT FM FT D (tgtUniv N).card
          (twoLawPsi α Rv μ νL νR v0 N h)
          (⨆ j, twoLawE α Rv μ νL νR v0 N h j)
        + mulVec (twoLawN N SL SR CW)
            (twoLawE α Rv μ νL νR v0 N h) (true, i) := by
  have _hLne := hLne
  obtain ⟨⟨c, z, u⟩, hsc⟩ := i
  let M := twoLawPsi α Rv μ νL νR v0 N h
  let E := ⨆ j, twoLawE α Rv μ νL νR v0 N h j
  let B := twoLawScreenB α M E
  let C := twoLawScreenC T RT
  let MV := mulVec (twoLawN N SL SR CW)
    (twoLawE α Rv μ νL νR v0 N h)
      (true, (⟨⟨c, z, u⟩, hsc⟩ : {sc // sc ∈ crossScreenIndex N}))
  change crossInterpScreen α Rv μ νL νR v0 (h + 1) ⟨c, z, u⟩
    ≤ twoLawG α T RT FM FT D (tgtUniv N).card M E + MV
  have hcross : (⟨c, z, u⟩ : GScreen) ∈ crossLiveScreens N :=
    (Finset.mem_filter.mp hsc).1
  have hsrc := Finset.mem_filter.mp hcross
  have huniv : (⟨c, z, u⟩ : GScreen) ∈ screenUniv N := hsrc.1
  have hz : z.Nonempty := hsrc.2.1
  have hzf := (Finset.mem_filter.mp hsc).2
  have hzfree : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m := by
    intro t ht m heq
    subst t
    exact hzf.2.1 (Tgt.Fk m) ht
  have hcard : (zsucc SR z).card ≤ (tgtUniv N).card :=
    Finset.card_le_card (zsucc_subset hN hRbd
      (mem_screenUniv.mp huniv).2.1)
  have hEd : ∀ sc' ∈ crossScreenSucc SL SR ⟨c, z, u⟩,
      crossInterpScreen α Rv μ νL νR v0 h sc' ≤ B := by
    intro sc' hsc'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hsc'
    obtain ⟨hcp, hup⟩ := Finset.mem_product.mp hp
    exact crossSubScreen_le α Rv μ νL νR v0 hα hN hLbd hRbd hsc
      hcp (Finset.Subset.refl _) (zsucc_nonempty hRne hz) hup h
  have hsuccC : C * (∑ sc' ∈ crossScreenSucc SL SR ⟨c, z, u⟩,
      crossInterpScreen α Rv μ νL νR v0 h sc') ≤ D * M + MV := by
    exact crossSucc_true_le α Rv μ νL νR v0 hα hN hLbd hRbd hRne hsc
      C CW D hCW hD h
  have h2C : (2 : ℝ≥0∞) ≤ C := by
    simp only [C, twoLawScreenC]
    exact le_trans (by norm_num) le_self_add
  have h4C : (4 : ℝ≥0∞) ≤ C := by
    simp only [C, twoLawScreenC]
    exact le_self_add
  have hRTC : 4 * (RT * T) ≤ C := by
    simp only [C, twoLawScreenC]
    exact le_add_self
  have hsucc2 : 2 * (∑ sc' ∈ crossScreenSucc SL SR ⟨c, z, u⟩,
      crossInterpScreen α Rv μ νL νR v0 h sc') ≤ D * M + MV :=
    le_trans (mul_le_mul' h2C le_rfl) hsuccC
  have hsucc4 : 4 * (∑ sc' ∈ crossScreenSucc SL SR ⟨c, z, u⟩,
      crossInterpScreen α Rv μ νL νR v0 h sc') ≤ D * M + MV :=
    le_trans (mul_le_mul' h4C le_rfl) hsuccC
  have hsuccRT : 4 * (RT * T)
      * (∑ sc' ∈ crossScreenSucc SL SR ⟨c, z, u⟩,
        crossInterpScreen α Rv μ νL νR v0 h sc') ≤ D * M + MV :=
    le_trans (mul_le_mul' hRTC le_rfl) hsuccC
  have hv0pos : rE μ Rv v0 ≠ 0 :=
    rE_v0_ne_zero Rv μ v0 (hrefl v0) hpos
  cases c with
  | Fk k => exact hzf.1.elim
  | Z k =>
      have hkN : k ≤ N := Z_mem_tgtUniv.mp (mem_screenUniv.mp huniv).1
      cases u with
      | none =>
          refine le_trans (crossERowZ_none α Rv μ νL νR v0 SL SR hRsupp
              (hrefl v0) hv0pos k z hzfree hz h B ?_)
            (le_trans le_add_self (twoLawG_absorb_none α
              (T := T) (RT := RT) (FM := FM) (FT := FT) (D := D)
              (a := M) (e := E) (B := B) (Eplus := ∑ sc' ∈
                crossScreenSucc SL SR ⟨Tgt.Z k, z, none⟩,
                crossInterpScreen α Rv μ νL νR v0 h sc')
              (MV := MV) (nA := (tgtUniv N).card) (nz := (zsucc SR z).card)
              rfl hcard hsucc2))
          intro t' ht' c' hc'
          have hs := crossSubScreen_le α Rv μ νL νR v0 hα hN hLbd hRbd hsc
            hc' (Finset.singleton_subset_iff.mpr ht')
            (Finset.singleton_nonempty t') (none_mem_normSucc SR) h
          simpa [crossInterpScreen, crossInterpNorm, B] using hs
      | some w =>
          cases w with
          | Fk m => exact (hzf.2.2 (Tgt.Fk m) rfl).elim
          | Z m =>
              have hmN : m ≤ N := Z_mem_tgtUniv.mp
                ((mem_screenUniv.mp huniv).2.2 (Tgt.Z m) rfl)
              refine le_trans (crossERowZ_forced α Rv μ νL νR v0 hα SL SR
                  hRsupp (hrefl v0) hv0pos k z hzfree hz m h M B ?_ ?_ hEd)
                (twoLawG_absorb_forced α
                  (T := T) (RT := RT) (FM := FM) (FT := FT) (D := D)
                  (a := M) (e := E) (B := B) (MV := MV)
                  rfl hcard hsucc4)
              · intro c' hc' w' hw'
                have hp : (c', w') ∈ crossOrdIndex N :=
                  Finset.mem_product.mpr
                    ⟨gpair_mem_crossTgtIndex hN hkN hc',
                      gpair_mem_crossTgtIndex hN hmN hw'⟩
                simpa [M, biCrossPhi, biCrossSource, biCrossTarget] using
                  (biCrossPhi_le_twoLawPsi α Rv μ νL νR v0
                    (h := h) (lr := true) hp)
              · intro t' ht' c' hc' w' hw'
                have hs := crossSubScreen_le α Rv μ νL νR v0 hα hN hLbd hRbd
                  hsc hc' (Finset.singleton_subset_iff.mpr ht')
                  (Finset.singleton_nonempty t') (some_mem_normSucc hw') h
                simpa [crossInterpScreen, crossInterpNorm, B] using hs
          | F =>
              refine le_trans (crossERowZ_fresh α Rv μ νL νR v0 hα SL SR
                  hRsupp (hrefl v0) hv0pos k z hzfree hz h M B T RT
                  (hRT v0 (hrefl v0)) hT ?_ ?_ hEd)
                (le_trans le_add_self (twoLawG_absorb_fresh α
                  (T := T) (RT := RT) (FM := FM) (FT := FT) (D := D)
                  (a := M) (e := E) (B := B) (MV := MV)
                  rfl hcard hsuccRT))
              · intro j hj c' hc' w' hw'
                have hp : (c', w') ∈ crossOrdIndex N :=
                  Finset.mem_product.mpr
                    ⟨gpair_mem_crossTgtIndex hN hkN hc',
                      gpair_mem_crossTgtIndex hN (hRbd j hj) hw'⟩
                simpa [M, biCrossPhi, biCrossSource, biCrossTarget] using
                  (biCrossPhi_le_twoLawPsi α Rv μ νL νR v0
                    (h := h) (lr := true) hp)
              · intro j hj t' ht' c' hc' w' hw'
                have hs := crossSubScreen_le α Rv μ νL νR v0 hα hN hLbd hRbd
                  hsc hc' (Finset.singleton_subset_iff.mpr ht')
                  (Finset.singleton_nonempty t')
                  (some_mem_normSucc (Finset.mem_biUnion.mpr ⟨j, hj, hw'⟩)) h
                simpa [crossInterpScreen, crossInterpNorm, B] using hs
  | F =>
      cases u with
      | none =>
          refine le_trans (crossERowF_none α Rv μ νL νR v0 SL SR hLsupp
              hRsupp hpos z hzfree h B FM hFM ?_)
            (twoLawG_absorb_none α
              (T := T) (RT := RT) (FM := FM) (FT := FT) (D := D)
              (a := M) (e := E) (B := B) (MV := MV)
              rfl hcard hsucc2)
          intro t' ht' k hk c' hc'
          have hs := crossSubScreen_le α Rv μ νL νR v0 hα hN hLbd hRbd hsc
            (Finset.mem_biUnion.mpr ⟨k, hk, hc'⟩)
            (Finset.singleton_subset_iff.mpr ht')
            (Finset.singleton_nonempty t') (none_mem_normSucc SR) h
          simpa [crossInterpScreen, crossInterpNorm, B] using hs
      | some w =>
          cases w with
          | Fk m => exact (hzf.2.2 (Tgt.Fk m) rfl).elim
          | Z m =>
              have hmN : m ≤ N := Z_mem_tgtUniv.mp
                ((mem_screenUniv.mp huniv).2.2 (Tgt.Z m) rfl)
              refine le_trans (crossERowF_forced α Rv μ νL νR v0 hα SL SR
                  hLsupp hRsupp hpos z hzfree m h M B ?_ ?_ hEd)
                (twoLawG_absorb_forced α
                  (T := T) (RT := RT) (FM := FM) (FT := FT) (D := D)
                  (a := M) (e := E) (B := B) (MV := MV)
                  rfl hcard hsucc4)
              · intro k hk c' hc' w' hw'
                have hp : (c', w') ∈ crossOrdIndex N :=
                  Finset.mem_product.mpr
                    ⟨gpair_mem_crossTgtIndex hN (hLbd k hk) hc',
                      gpair_mem_crossTgtIndex hN hmN hw'⟩
                simpa [M, biCrossPhi, biCrossSource, biCrossTarget] using
                  (biCrossPhi_le_twoLawPsi α Rv μ νL νR v0
                    (h := h) (lr := true) hp)
              · intro t' ht' k hk c' hc' w' hw'
                have hs := crossSubScreen_le α Rv μ νL νR v0 hα hN hLbd hRbd
                  hsc (Finset.mem_biUnion.mpr ⟨k, hk, hc'⟩)
                  (Finset.singleton_subset_iff.mpr ht')
                  (Finset.singleton_nonempty t') (some_mem_normSucc hw') h
                simpa [crossInterpScreen, crossInterpNorm, B] using hs
          | F =>
              refine le_trans (crossERowF_fresh α Rv μ νL νR v0 hα SL SR
                  hLsupp hRsupp hpos z hzfree h M B T RT FT hRT hT hFT
                  ?_ ?_ hEd)
                (twoLawG_absorb_fresh α
                  (T := T) (RT := RT) (FM := FM) (FT := FT) (D := D)
                  (a := M) (e := E) (B := B) (MV := MV)
                  rfl hcard hsuccRT)
              · intro k hk j hj c' hc' w' hw'
                have hp : (c', w') ∈ crossOrdIndex N :=
                  Finset.mem_product.mpr
                    ⟨gpair_mem_crossTgtIndex hN (hLbd k hk) hc',
                      gpair_mem_crossTgtIndex hN (hRbd j hj) hw'⟩
                simpa [M, biCrossPhi, biCrossSource, biCrossTarget] using
                  (biCrossPhi_le_twoLawPsi α Rv μ νL νR v0
                    (h := h) (lr := true) hp)
              · intro j hj t' ht' k hk c' hc' w' hw'
                have hs := crossSubScreen_le α Rv μ νL νR v0 hα hN hLbd hRbd
                  hsc (Finset.mem_biUnion.mpr ⟨k, hk, hc'⟩)
                  (Finset.singleton_subset_iff.mpr ht')
                  (Finset.singleton_nonempty t')
                  (some_mem_normSucc (Finset.mem_biUnion.mpr ⟨j, hj, hw'⟩)) h
                simpa [crossInterpScreen, crossInterpNorm, B] using hs

/-- The same six rows in the right-to-left orientation. -/
theorem twoLaw_E_step_false
    {N : ℕ} (hα : 1 ≤ α) (hrefl : ∀ v, Rv v v)
    (SL SR : Finset ℕ) (hN : 2 ≤ N)
    (hLbd : ∀ k ∈ SL, k ≤ N) (hRbd : ∀ k ∈ SR, k ≤ N)
    (hLne : SL.Nonempty) (hRne : SR.Nonempty)
    (hLsupp : ∀ k : ℕ, (νL k : ℝ≥0∞) ≠ 0 ↔ k ∈ SL)
    (hRsupp : ∀ k : ℕ, (νR k : ℝ≥0∞) ≠ 0 ↔ k ∈ SR)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0)
    (T RT FM FT CW D : ℝ≥0∞)
    (hT : (∑' j, if (νL j : ℝ≥0∞) = 0 then 0
        else (νL j : ℝ≥0∞) ^ (-α)) ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM)
    (hFT : (∑' v, if Rv v v0 then 0
        else (μ v : ℝ≥0∞) * WresD α μ Rv v) ≤ FT)
    (hCW : twoLawScreenC T RT ≤ CW)
    (hD : (screenUniv N).card
        * (twoLawScreenC T RT * (1 + ENNReal.ofReal α)) ≤ D)
    (h : ℕ) (i : {sc // sc ∈ crossScreenIndex N}) :
    twoLawE α Rv μ νL νR v0 N (h + 1) (false, i)
      ≤ twoLawG α T RT FM FT D (tgtUniv N).card
          (twoLawPsi α Rv μ νL νR v0 N h)
          (⨆ j, twoLawE α Rv μ νL νR v0 N h j)
        + mulVec (twoLawN N SL SR CW)
            (twoLawE α Rv μ νL νR v0 N h) (false, i) := by
  have hf := twoLaw_E_step_true α Rv μ νR νL v0 hα hrefl SR SL hN
    hRbd hLbd hRne hLne hRsupp hLsupp hpos T RT FM FT CW D hT hRT
    hFM hFT hCW hD h i
  rw [twoLawPsi_swap α Rv μ νL νR v0 N h,
    twoLawE_sup_swap α Rv μ νL νR v0 N h] at hf
  simpa [twoLawE, biCrossScreen, mulVec, twoLawN,
    Fintype.sum_prod_type] using hf

/-- **Complete two-law screen-step assembly.**  Both orientations and all
six source/normalization rows are now discharged by the concrete Hall rows;
there is no remaining abstract `hEstep` premise. -/
theorem twoLaw_E_step
    {N : ℕ} (hα : 1 ≤ α) (hrefl : ∀ v, Rv v v)
    (SL SR : Finset ℕ) (hN : 2 ≤ N)
    (hLbd : ∀ k ∈ SL, k ≤ N) (hRbd : ∀ k ∈ SR, k ≤ N)
    (hLne : SL.Nonempty) (hRne : SR.Nonempty)
    (hLsupp : ∀ k : ℕ, (νL k : ℝ≥0∞) ≠ 0 ↔ k ∈ SL)
    (hRsupp : ∀ k : ℕ, (νR k : ℝ≥0∞) ≠ 0 ↔ k ∈ SR)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0)
    (T RT FM FT CW D : ℝ≥0∞)
    (hTL : (∑' j, if (νL j : ℝ≥0∞) = 0 then 0
        else (νL j : ℝ≥0∞) ^ (-α)) ≤ T)
    (hTR : (∑' j, if (νR j : ℝ≥0∞) = 0 then 0
        else (νR j : ℝ≥0∞) ^ (-α)) ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM)
    (hFT : (∑' v, if Rv v v0 then 0
        else (μ v : ℝ≥0∞) * WresD α μ Rv v) ≤ FT)
    (hCW : twoLawScreenC T RT ≤ CW)
    (hD : (screenUniv N).card
        * (twoLawScreenC T RT * (1 + ENNReal.ofReal α)) ≤ D)
    (h : ℕ) (i : Bool × {sc // sc ∈ crossScreenIndex N}) :
    twoLawE α Rv μ νL νR v0 N (h + 1) i
      ≤ twoLawG α T RT FM FT D (tgtUniv N).card
          (twoLawPsi α Rv μ νL νR v0 N h)
          (⨆ j, twoLawE α Rv μ νL νR v0 N h j)
        + mulVec (twoLawN N SL SR CW)
            (twoLawE α Rv μ νL νR v0 N h) i := by
  rcases i with ⟨lr, i⟩
  cases lr
  · exact twoLaw_E_step_false α Rv μ νL νR v0 hα hrefl SL SR hN
      hLbd hRbd hLne hRne hLsupp hRsupp hpos T RT FM FT CW D hTL hRT
      hFM hFT hCW hD h i
  · exact twoLaw_E_step_true α Rv μ νL νR v0 hα hrefl SL SR hN
      hLbd hRbd hLne hRne hLsupp hRsupp hpos T RT FM FT CW D hTR hRT
      hFM hFT hCW hD h i

end GraphMarkovMatching
