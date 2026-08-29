/-
The finite bidirectional coordinate system for the two-law ledger.

The ordinary scalar contains both the restricted potential and raw directed
failure for every bounded formal pair and in both orientations.  This is the
minimal enlargement forced by asymmetric formal diagonals.  The screen vector
is likewise bidirectional.  The main pruning/diversion lemma below proves that
every bounded cross screen is either a live matrix coordinate, vanishes because
its normalization is in the right-law zero list, or returns to the ordinary
scalar.  Thus no same-law diagonal pruning is used.
-/
import GraphMarkovMatching.Archive.VaryingCrossClosure
import GraphMarkovMatching.Archive.VaryingCrossStep
import GraphMarkovMatching.Rows.Psi
import GraphMarkovMatching.Grammar.Index

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (νL νR : PMF ℕ) (v0 : V)

/-- The bounded forced/fresh alphabet.  `Fk` is an auxiliary mixture component,
not a state produced by the cascade grammar; retaining it in the running
supremum would introduce irrelevant rows which are not reachable from the
fresh/fresh seed. -/
noncomputable def crossTgtIndex (N : ℕ) : Finset Tgt :=
  (tgtUniv N).filter ZFtgt

/-- All bounded formal ordinary pairs in the reachable forced/fresh alphabet. -/
noncomputable def crossOrdIndex (N : ℕ) : Finset (Tgt × Tgt) :=
  crossTgtIndex N ×ˢ crossTgtIndex N

lemma F_mem_crossTgtIndex {N : ℕ} : Tgt.F ∈ crossTgtIndex N := by
  simp [crossTgtIndex, F_mem_tgtUniv, ZFtgt]

lemma Z_mem_crossTgtIndex {N j : ℕ} (hj : j ≤ N) :
    Tgt.Z j ∈ crossTgtIndex N := by
  simp [crossTgtIndex, Z_mem_tgtUniv, ZFtgt, hj]

lemma gpair_mem_crossTgtIndex {N k : ℕ} (hN : 2 ≤ N) (hk : k ≤ N)
    {t : Tgt} (ht : t ∈ gpair k) : t ∈ crossTgtIndex N := by
  exact Finset.mem_filter.mpr
    ⟨gpair_subset hN hk ht, ZFtgt_of_mem_gpair ht⟩

/-- Source interpretation in one of the two orientations. -/
noncomputable def biCrossSource (lr : Bool) (h : ℕ) (t : Tgt) :
    PMF (FullLab (V × ℕ) h) :=
  if lr then interpT μ νL v0 h t else interpT μ νR v0 h t

/-- Target interpretation in one of the two orientations. -/
noncomputable def biCrossTarget (lr : Bool) (h : ℕ) (t : Tgt) :
    PMF (FullLab (V × ℕ) h) :=
  if lr then interpT μ νR v0 h t else interpT μ νL v0 h t

/-- A directed restricted-potential coordinate. -/
noncomputable def biCrossPhi (lr : Bool) (h : ℕ) (p : Tgt × Tgt) : ℝ≥0∞ :=
  PhiDres α (biCrossSource μ νL νR v0 lr h p.1)
    (biCrossTarget μ νL νR v0 lr h p.2) (fullSim (labRel Rv) h)

/-- A directed raw-failure coordinate. -/
noncomputable def biCrossFailure (lr : Bool) (h : ℕ)
    (p : Tgt × Tgt) : ℝ≥0∞ :=
  failureD (biCrossSource μ νL νR v0 lr h p.1)
    (biCrossTarget μ νL νR v0 lr h p.2) (fullSim (labRel Rv) h)

/-- The full ordinary two-law scalar: both analytic coordinates, all bounded
formal pairs, and both directions. -/
noncomputable def twoLawPsi (N h : ℕ) : ℝ≥0∞ :=
  ⨆ lr : Bool, ⨆ p : {p // p ∈ crossOrdIndex N},
    max (biCrossPhi α Rv μ νL νR v0 lr h p.val)
      (biCrossFailure Rv μ νL νR v0 lr h p.val)

lemma biCrossPhi_le_twoLawPsi {N h : ℕ} {lr : Bool} {p : Tgt × Tgt}
    (hp : p ∈ crossOrdIndex N) :
    biCrossPhi α Rv μ νL νR v0 lr h p ≤
      twoLawPsi α Rv μ νL νR v0 N h := by
  exact le_trans (le_max_left _ _)
    (le_trans (le_iSup (fun p : {p // p ∈ crossOrdIndex N} =>
      max (biCrossPhi α Rv μ νL νR v0 lr h p.val)
        (biCrossFailure Rv μ νL νR v0 lr h p.val)) ⟨p, hp⟩)
      (le_iSup (fun lr : Bool => ⨆ p : {p // p ∈ crossOrdIndex N},
        max (biCrossPhi α Rv μ νL νR v0 lr h p.val)
          (biCrossFailure Rv μ νL νR v0 lr h p.val)) lr))

lemma biCrossFailure_le_twoLawPsi {N h : ℕ} {lr : Bool} {p : Tgt × Tgt}
    (hp : p ∈ crossOrdIndex N) :
    biCrossFailure Rv μ νL νR v0 lr h p ≤
      twoLawPsi α Rv μ νL νR v0 N h := by
  exact le_trans (le_max_right _ _)
    (le_trans (le_iSup (fun p : {p // p ∈ crossOrdIndex N} =>
      max (biCrossPhi α Rv μ νL νR v0 lr h p.val)
        (biCrossFailure Rv μ νL νR v0 lr h p.val)) ⟨p, hp⟩)
      (le_iSup (fun lr : Bool => ⨆ p : {p // p ∈ crossOrdIndex N},
        max (biCrossPhi α Rv μ νL νR v0 lr h p.val)
          (biCrossFailure Rv μ νL νR v0 lr h p.val)) lr))

/-- The principal left-to-right raw matching failure is one coordinate of
the retained ordinary envelope.  This lemma remains useful for any future
weighted closure, independently of how the envelope is propagated. -/
lemma twoLawFailure_le_Psi {N h : ℕ} :
    failureD (Tlaw μ νL v0 h) (Tlaw μ νR v0 h)
        (fullSim (labRel Rv) h)
      ≤ twoLawPsi α Rv μ νL νR v0 N h := by
  have hp : (Tgt.F, Tgt.F) ∈ crossOrdIndex N :=
    Finset.mem_product.mpr ⟨F_mem_crossTgtIndex, F_mem_crossTgtIndex⟩
  simpa [biCrossFailure, biCrossSource, biCrossTarget, interpT] using
    (biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
      (h := h) (lr := true) hp)

/-- Semantic cross screen in either orientation. -/
noncomputable def biCrossScreen (lr : Bool) (h : ℕ) (sc : GScreen) : ℝ≥0∞ :=
  if lr then crossInterpScreen α Rv μ νL νR v0 h sc
  else crossInterpScreen α Rv μ νR νL v0 h sc

/-- The reachable part of the live screen universe. -/
noncomputable def crossScreenIndex (N : ℕ) : Finset GScreen :=
  (crossLiveScreens N).filter fun sc =>
    ZFtgt sc.cell ∧ (∀ t ∈ sc.zlist, ZFtgt t)
      ∧ ∀ u, sc.norm = some u → ZFtgt u

/-- The live screen vector, indexed by orientation and the common bounded
reachable screen universe. -/
noncomputable def twoLawE (N h : ℕ) :
    Bool × {sc // sc ∈ crossScreenIndex N} → ℝ≥0∞ :=
  fun i => biCrossScreen α Rv μ νL νR v0 i.1 h i.2.val

/-- If the normalizing law occurs in the zero list then an inverse-normalized
screen is genuinely zero.  This remains valid cross-law because both the zero
list and normalization use the target law. -/
lemma screenE_WresD_eq_zero_of_mem {X : Type} (ρs ρnorm : PMF X)
    (R : X → X → Prop) (zs : List (PMF X)) (hmem : ρnorm ∈ zs) :
    screenE ρs R zs (WresD α ρnorm R) = 0 := by
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  rw [screenInd]
  by_cases hall : ∀ ρ ∈ zs, rE ρ R x = 0
  · simp [WresD, hall ρnorm hmem]
  · rw [if_neg hall, mul_zero, zero_mul]

/-- A live cross screen is below the corresponding vector supremum. -/
lemma biCrossScreen_live_le {N h : ℕ} {lr : Bool} {sc : GScreen}
    (hsc : sc ∈ crossScreenIndex N) :
    biCrossScreen α Rv μ νL νR v0 lr h sc
      ≤ ⨆ i, twoLawE α Rv μ νL νR v0 N h i := by
  exact le_iSup (fun i : Bool × {sc // sc ∈ crossScreenIndex N} =>
    twoLawE α Rv μ νL νR v0 N h i) (lr, ⟨sc, hsc⟩)

/-- Once directed failure is part of the ordinary ledger, every nonempty
cross screen is an ordinary inhomogeneous coordinate.  Choose any member of
the zero list.  Unit normalization is bounded by the corresponding failure;
inverse normalization is bounded by that failure plus the potential toward
the normalizing law.  No recursive screen coordinate is needed for this
estimate. -/
theorem biCrossScreen_le_ordinary (hα : 1 ≤ α) {N h : ℕ} {lr : Bool}
    {sc : GScreen} (huniv : sc ∈ screenUniv N) (hne : sc.zlist.Nonempty)
    (hzf : ZFtgt sc.cell ∧ (∀ t ∈ sc.zlist, ZFtgt t)
      ∧ ∀ u, sc.norm = some u → ZFtgt u) :
    biCrossScreen α Rv μ νL νR v0 lr h sc
      ≤ (1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h := by
  obtain ⟨t, ht⟩ := hne
  have hcellN : sc.cell ∈ tgtUniv N := (mem_screenUniv.mp huniv).1
  have htN : t ∈ tgtUniv N := (mem_screenUniv.mp huniv).2.1 ht
  have hcellI : sc.cell ∈ crossTgtIndex N :=
    Finset.mem_filter.mpr ⟨hcellN, hzf.1⟩
  have htI : t ∈ crossTgtIndex N :=
    Finset.mem_filter.mpr ⟨htN, hzf.2.1 t ht⟩
  cases hnorm : sc.norm with
  | none =>
      have hp : (sc.cell, t) ∈ crossOrdIndex N :=
        Finset.mem_product.mpr ⟨hcellI, htI⟩
      have hret : biCrossScreen α Rv μ νL νR v0 lr h sc ≤
          biCrossFailure Rv μ νL νR v0 lr h (sc.cell, t) := by
        cases lr
        · simpa [biCrossScreen, biCrossFailure, biCrossSource, biCrossTarget,
            crossInterpScreen, crossInterpNorm, hnorm] using
            (screenE_le_failureD_of_mem
              (interpT μ νR v0 h sc.cell) (interpT μ νL v0 h t)
              (fullSim (labRel Rv) h)
              ((sc.zlist.toList).map (interpT μ νL v0 h))
              (List.mem_map.mpr ⟨t, Finset.mem_toList.mpr ht, rfl⟩))
        · simpa [biCrossScreen, biCrossFailure, biCrossSource, biCrossTarget,
            crossInterpScreen, crossInterpNorm, hnorm] using
            (screenE_le_failureD_of_mem
              (interpT μ νL v0 h sc.cell) (interpT μ νR v0 h t)
              (fullSim (labRel Rv) h)
              ((sc.zlist.toList).map (interpT μ νR v0 h))
              (List.mem_map.mpr ⟨t, Finset.mem_toList.mpr ht, rfl⟩))
      refine le_trans hret (le_trans
        (biCrossFailure_le_twoLawPsi α Rv μ νL νR v0 hp) ?_)
      have hone : (1 : ℝ≥0∞) ≤ 1 + ENNReal.ofReal α := le_self_add
      calc
        twoLawPsi α Rv μ νL νR v0 N h
            = 1 * twoLawPsi α Rv μ νL νR v0 N h := (one_mul _).symm
        _ ≤ _ := by simpa [mul_comm] using
          (mul_le_mul_right hone (twoLawPsi α Rv μ νL νR v0 N h))
  | some u =>
      have huN : u ∈ tgtUniv N :=
        (mem_screenUniv.mp huniv).2.2 u hnorm
      have huI : u ∈ crossTgtIndex N :=
        Finset.mem_filter.mpr ⟨huN, hzf.2.2 u hnorm⟩
      have hpbad : (sc.cell, t) ∈ crossOrdIndex N :=
        Finset.mem_product.mpr ⟨hcellI, htI⟩
      have hpnorm : (sc.cell, u) ∈ crossOrdIndex N :=
        Finset.mem_product.mpr ⟨hcellI, huI⟩
      have hret : biCrossScreen α Rv μ νL νR v0 lr h sc ≤
          biCrossFailure Rv μ νL νR v0 lr h (sc.cell, t)
            + ENNReal.ofReal α *
              biCrossPhi α Rv μ νL νR v0 lr h (sc.cell, u) := by
        cases lr
        · refine le_trans ?_
            (crossDres_le_failureD_add_PhiDres α hα _ _ _ _)
          simpa [biCrossScreen, biCrossFailure, biCrossPhi, biCrossSource,
              biCrossTarget, crossInterpScreen, crossInterpNorm, hnorm] using
            (screenE_WresD_le_crossDres_of_mem α
              (interpT μ νR v0 h sc.cell) (interpT μ νL v0 h t)
              (interpT μ νL v0 h u) (fullSim (labRel Rv) h)
              ((sc.zlist.toList).map (interpT μ νL v0 h))
              (List.mem_map.mpr ⟨t, Finset.mem_toList.mpr ht, rfl⟩))
        · refine le_trans ?_
            (crossDres_le_failureD_add_PhiDres α hα _ _ _ _)
          simpa [biCrossScreen, biCrossFailure, biCrossPhi, biCrossSource,
              biCrossTarget, crossInterpScreen, crossInterpNorm, hnorm] using
            (screenE_WresD_le_crossDres_of_mem α
              (interpT μ νL v0 h sc.cell) (interpT μ νR v0 h t)
              (interpT μ νR v0 h u) (fullSim (labRel Rv) h)
              ((sc.zlist.toList).map (interpT μ νR v0 h))
              (List.mem_map.mpr ⟨t, Finset.mem_toList.mpr ht, rfl⟩))
      refine le_trans hret ?_
      have hf := biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
        (h := h) (lr := lr) hpbad
      have hp := biCrossPhi_le_twoLawPsi α Rv μ νL νR v0
        (h := h) (lr := lr) hpnorm
      calc
        biCrossFailure Rv μ νL νR v0 lr h (sc.cell, t)
              + ENNReal.ofReal α * biCrossPhi α Rv μ νL νR v0 lr h (sc.cell, u)
            ≤ twoLawPsi α Rv μ νL νR v0 N h
              + ENNReal.ofReal α * twoLawPsi α Rv μ νL νR v0 N h :=
                add_le_add hf (mul_le_mul_right hp _)
        _ = (1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h := by ring

/-- Uniform direct discharge of the whole bidirectional live screen vector. -/
lemma twoLawE_sup_le_ordinary (hα : 1 ≤ α) {N h : ℕ} :
    (⨆ i, twoLawE α Rv μ νL νR v0 N h i)
      ≤ (1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h := by
  refine iSup_le fun i => ?_
  have hi := (Finset.mem_filter.mp
    (Finset.mem_filter.mp i.2.property).1).2
  exact biCrossScreen_le_ordinary α Rv μ νL νR v0 hα
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp i.2.property).1).1 hi.1
    (Finset.mem_filter.mp i.2.property).2

/-- **Complete asymmetric pruning/diversion dichotomy.**  Every bounded
nonempty screen is controlled by the ordinary scalar plus the live-screen
supremum.  A cell diagonal returns to raw failure (and, for an inverse
normalization, to raw failure plus restricted potential); a target-law
normalization diagonal vanishes; all remaining screens are live coordinates.
-/
theorem biCrossScreen_le_ledger (hα : 1 ≤ α) {N h : ℕ} {lr : Bool}
    {sc : GScreen} (huniv : sc ∈ screenUniv N) (hne : sc.zlist.Nonempty)
    (hzf : ZFtgt sc.cell ∧ (∀ t ∈ sc.zlist, ZFtgt t)
      ∧ ∀ u, sc.norm = some u → ZFtgt u) :
    biCrossScreen α Rv μ νL νR v0 lr h sc
      ≤ (1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h
        + ⨆ i, twoLawE α Rv μ νL νR v0 N h i := by
  have hcellN : sc.cell ∈ tgtUniv N := (mem_screenUniv.mp huniv).1
  have hnormN : ∀ u, sc.norm = some u → u ∈ tgtUniv N :=
    (mem_screenUniv.mp huniv).2.2
  have hcellI : sc.cell ∈ crossTgtIndex N :=
    Finset.mem_filter.mpr ⟨hcellN, hzf.1⟩
  by_cases hcell : sc.cell ∈ sc.zlist
  · cases hnorm : sc.norm with
    | none =>
        have hp : (sc.cell, sc.cell) ∈ crossOrdIndex N :=
          Finset.mem_product.mpr ⟨hcellI, hcellI⟩
        have hret : biCrossScreen α Rv μ νL νR v0 lr h sc ≤
            biCrossFailure Rv μ νL νR v0 lr h (sc.cell, sc.cell) := by
          cases lr
          · simpa [biCrossScreen, biCrossFailure, biCrossSource, biCrossTarget]
              using crossInterpScreen_cell_mem_none_le α Rv μ νR νL v0
                hcell hnorm
          · simpa [biCrossScreen, biCrossFailure, biCrossSource, biCrossTarget]
              using crossInterpScreen_cell_mem_none_le α Rv μ νL νR v0
                hcell hnorm
        refine le_trans hret (le_trans
          (biCrossFailure_le_twoLawPsi α Rv μ νL νR v0 hp) ?_)
        calc
          twoLawPsi α Rv μ νL νR v0 N h
              ≤ (1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h := by
                have hone : (1 : ℝ≥0∞) ≤ 1 + ENNReal.ofReal α := le_self_add
                calc
                  _ = 1 * twoLawPsi α Rv μ νL νR v0 N h := (one_mul _).symm
                  _ ≤ _ := by
                    simpa [mul_comm] using
                      (mul_le_mul_right hone (twoLawPsi α Rv μ νL νR v0 N h))
          _ ≤ _ := le_add_right le_rfl
    | some u =>
        have huN : u ∈ tgtUniv N := hnormN u hnorm
        have huI : u ∈ crossTgtIndex N :=
          Finset.mem_filter.mpr ⟨huN, hzf.2.2 u hnorm⟩
        have hpbad : (sc.cell, sc.cell) ∈ crossOrdIndex N :=
          Finset.mem_product.mpr ⟨hcellI, hcellI⟩
        have hpnorm : (sc.cell, u) ∈ crossOrdIndex N :=
          Finset.mem_product.mpr ⟨hcellI, huI⟩
        have hret : biCrossScreen α Rv μ νL νR v0 lr h sc ≤
            biCrossFailure Rv μ νL νR v0 lr h (sc.cell, sc.cell)
              + ENNReal.ofReal α *
                biCrossPhi α Rv μ νL νR v0 lr h (sc.cell, u) := by
          cases lr
          · refine le_trans
              (crossInterpScreen_cell_mem_some_le α Rv μ νR νL v0 hcell hnorm)
              (crossDres_le_failureD_add_PhiDres α hα _ _ _ _)
          · refine le_trans
              (crossInterpScreen_cell_mem_some_le α Rv μ νL νR v0 hcell hnorm)
              (crossDres_le_failureD_add_PhiDres α hα _ _ _ _)
        refine le_trans hret ?_
        have hf := biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
          (h := h) (lr := lr) hpbad
        have hp := biCrossPhi_le_twoLawPsi α Rv μ νL νR v0
          (h := h) (lr := lr) hpnorm
        calc
          biCrossFailure Rv μ νL νR v0 lr h (sc.cell, sc.cell)
                + ENNReal.ofReal α * biCrossPhi α Rv μ νL νR v0 lr h (sc.cell, u)
              ≤ twoLawPsi α Rv μ νL νR v0 N h
                + ENNReal.ofReal α * twoLawPsi α Rv μ νL νR v0 N h :=
                  add_le_add hf (mul_le_mul_right hp _)
          _ = (1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h := by ring
          _ ≤ _ := le_add_right le_rfl
  · by_cases hnormdead : ∃ u, sc.norm = some u ∧ u ∈ sc.zlist
    · obtain ⟨u, hu, humem⟩ := hnormdead
      have hz : biCrossScreen α Rv μ νL νR v0 lr h sc = 0 := by
        cases lr
        · simpa [biCrossScreen, crossInterpScreen, crossInterpNorm, hu] using
            screenE_WresD_eq_zero_of_mem α
              (interpT μ νR v0 h sc.cell) (interpT μ νL v0 h u)
              (fullSim (labRel Rv) h)
              ((sc.zlist.toList).map (interpT μ νL v0 h))
              (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr humem, rfl⟩)
        · simpa [biCrossScreen, crossInterpScreen, crossInterpNorm, hu] using
            screenE_WresD_eq_zero_of_mem α
              (interpT μ νL v0 h sc.cell) (interpT μ νR v0 h u)
              (fullSim (labRel Rv) h)
              ((sc.zlist.toList).map (interpT μ νR v0 h))
              (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr humem, rfl⟩)
      rw [hz]
      exact zero_le
    · have hlive : sc ∈ crossScreenIndex N := by
        rw [crossScreenIndex, Finset.mem_filter]
        refine ⟨?_, hzf⟩
        rw [crossLiveScreens, Finset.mem_filter]
        refine ⟨huniv, hne, hcell, ?_⟩
        intro u hu humem
        exact hnormdead ⟨u, hu, humem⟩
      exact le_trans (biCrossScreen_live_le α Rv μ νL νR v0 hlive)
        le_add_self

/-! ### The assembled product cell -/

lemma gcomp_mem_tgtUniv {N k : ℕ} (hN : 2 ≤ N) (hk : k ≤ N) (e : Bool) :
    (if e then gcomp0 k else gcomp1 k) ∈ tgtUniv N := by
  split
  · exact gpair_subset hN hk (gcomp_mem_gpair k).1
  · exact gpair_subset hN hk (gcomp_mem_gpair k).2

lemma gcomp_mem_crossTgtIndex_bool {N k : ℕ} (hN : 2 ≤ N)
    (hk : k ≤ N) (e : Bool) :
    (if e then gcomp0 k else gcomp1 k) ∈ crossTgtIndex N := by
  split
  · exact gpair_mem_crossTgtIndex hN hk (gcomp_mem_gpair k).1
  · exact gpair_mem_crossTgtIndex hN hk (gcomp_mem_gpair k).2

/-- The zero-interface mass is bounded by raw directed failure. -/
lemma zMass_le_failureD {X : Type} (ρs ρt : PMF X) (R : X → X → Prop) :
    zMass ρs ρt R ≤ failureD ρs ρt R := by
  rw [zMass, failureD]
  refine ENNReal.tsum_le_tsum fun x => ?_
  exact mul_le_mul_right (deadInd_le_qE ρt R x) _

/-- **Assembled asymmetric square-cell row.**  Every component potential,
reverse zero interface, and resolved singleton screen is discharged from the
bidirectional running ledger.  This is the central Hall product row for a
left-law counter cell against a right-law counter cell. -/
theorem crossSquare_le_cellCB {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    {N k j h : ℕ} (hN : 2 ≤ N) (hk : k ≤ N) (hj : j ≤ N) :
    PhiDres α (Xi μ νL v0 k h) (Xi μ νR v0 j h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ cellCB α δ L K
          (twoLawPsi α Rv μ νL νR v0 N h)
          (twoLawPsi α Rv μ νL νR v0 N h)
          ((1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h
            + ⨆ i, twoLawE α Rv μ νL νR v0 N h i) := by
  let M := twoLawPsi α Rv μ νL νR v0 N h
  let E := (1 + ENNReal.ofReal α) * M
    + ⨆ i, twoLawE α Rv μ νL νR v0 N h i
  have hcompL : ∀ e : Bool,
      (if e then gcomp0 k else gcomp1 k) ∈ crossTgtIndex N :=
    fun e => gcomp_mem_crossTgtIndex_bool hN hk e
  have hcompR : ∀ e : Bool,
      (if e then gcomp0 j else gcomp1 j) ∈ crossTgtIndex N :=
    fun e => gcomp_mem_crossTgtIndex_bool hN hj e
  have hphiLR : ∀ e f : Bool,
      PhiDres α
          (interpT μ νL v0 h (if e then gcomp0 k else gcomp1 k))
          (interpT μ νR v0 h (if f then gcomp0 j else gcomp1 j))
          (fullSim (labRel Rv) h) ≤ M := by
    intro e f
    have hp : ((if e then gcomp0 k else gcomp1 k),
        (if f then gcomp0 j else gcomp1 j)) ∈ crossOrdIndex N :=
      Finset.mem_product.mpr ⟨hcompL e, hcompR f⟩
    simpa [M, biCrossPhi, biCrossSource, biCrossTarget] using
      (biCrossPhi_le_twoLawPsi α Rv μ νL νR v0 (h := h) (lr := true) hp)
  have hphiRL : ∀ e f : Bool,
      PhiDres α
          (interpT μ νR v0 h (if f then gcomp0 j else gcomp1 j))
          (interpT μ νL v0 h (if e then gcomp0 k else gcomp1 k))
          (fullSim (labRel Rv) h) ≤ M := by
    intro e f
    have hp : ((if f then gcomp0 j else gcomp1 j),
        (if e then gcomp0 k else gcomp1 k)) ∈ crossOrdIndex N :=
      Finset.mem_product.mpr ⟨hcompR f, hcompL e⟩
    simpa [M, biCrossPhi, biCrossSource, biCrossTarget] using
      (biCrossPhi_le_twoLawPsi α Rv μ νL νR v0 (h := h) (lr := false) hp)
  have hz : ∀ e f : Bool,
      zMass
          (interpT μ νR v0 h (if f then gcomp0 j else gcomp1 j))
          (interpT μ νL v0 h (if e then gcomp0 k else gcomp1 k))
          (fullSim (labRel Rv) h) ≤ M := by
    intro e f
    have hp : ((if f then gcomp0 j else gcomp1 j),
        (if e then gcomp0 k else gcomp1 k)) ∈ crossOrdIndex N :=
      Finset.mem_product.mpr ⟨hcompR f, hcompL e⟩
    refine le_trans (zMass_le_failureD _ _ _) ?_
    simpa [M, biCrossFailure, biCrossSource, biCrossTarget] using
      (biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
        (h := h) (lr := false) hp)
  have hscr : ∀ e f g : Bool,
      screenE
          (interpT μ νL v0 h (if e then gcomp0 k else gcomp1 k))
          (fullSim (labRel Rv) h)
          [interpT μ νR v0 h (if f then gcomp0 j else gcomp1 j)]
          (WresD α (interpT μ νR v0 h
            (if g then gcomp0 j else gcomp1 j))
            (fullSim (labRel Rv) h)) ≤ E := by
    intro e f g
    let sc : GScreen := ⟨(if e then gcomp0 k else gcomp1 k),
      {(if f then gcomp0 j else gcomp1 j)},
      some (if g then gcomp0 j else gcomp1 j)⟩
    have hsc : sc ∈ screenUniv N := by
      refine mem_screenUniv.mpr ⟨(Finset.mem_filter.mp (hcompL e)).1,
        Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp (hcompR f)).1, ?_⟩
      intro u hu
      have hu' : u = (if g then gcomp0 j else gcomp1 j) :=
        Option.some_inj.mp hu.symm
      rw [hu']
      exact (Finset.mem_filter.mp (hcompR g)).1
    have hne : sc.zlist.Nonempty := Finset.singleton_nonempty _
    simpa [E, M, sc, biCrossScreen, crossInterpScreen, crossInterpNorm] using
      (biCrossScreen_le_ledger α Rv μ νL νR v0 hα hsc hne
        ⟨(Finset.mem_filter.mp (hcompL e)).2,
          (fun t ht => by
            have ht' : t = (if f then gcomp0 j else gcomp1 j) :=
              Finset.mem_singleton.mp ht
            rw [ht']
            exact (Finset.mem_filter.mp (hcompR f)).2),
          (fun u hu => by
            have hu' : u = (if g then gcomp0 j else gcomp1 j) :=
              Option.some_inj.mp hu.symm
            simpa [hu'] using (Finset.mem_filter.mp (hcompR g)).2)⟩
        (lr := true) (h := h))
  rw [Xi_eq_prod μ νL v0 k h, Xi_eq_prod μ νR v0 j h]
  refine le_trans (PhiDres_square_le hα hδ hL0 hL hK0 hK
    (interpT μ νL v0 h (gcomp0 k)) (interpT μ νL v0 h (gcomp1 k))
    (interpT μ νR v0 h (gcomp0 j)) (interpT μ νR v0 h (gcomp1 j))
    (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (fun a b hab => hsymm a.1 b.1 hab) h) M M
    (hphiLR true true) (hphiLR true false)
    (hphiLR false true) (hphiLR false false)
    (hphiRL true true) (hphiRL false true)
    (hphiRL true false) (hphiRL false false)
    (hz true true) (hz false true) (hz true false) (hz false false)) ?_
  rw [cellCB]
  refine add_le_add le_rfl ?_
  refine le_trans (mul_le_mul_left
    (add_le_add (add_le_add (add_le_add
      (hscr true true false) (hscr true false true))
      (hscr false true false)) (hscr false false true))
    (1 + ENNReal.ofReal α * M)) ?_
  exact le_of_eq (by ring)

/-- The forced-forced ordinary row, now with all component hypotheses
discharged by the bidirectional ledger. -/
theorem biCrossPhi_ZZ_le_cellCB {δ L K : ℝ} (hα : 1 ≤ α)
    (hδ : 0 < δ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : Rv v0 v0) (hsymm : ∀ a b, Rv a b → Rv b a)
    {N k j h : ℕ} (hN : 2 ≤ N) (hk : k ≤ N) (hj : j ≤ N) :
    biCrossPhi α Rv μ νL νR v0 true (h + 1) (Tgt.Z k, Tgt.Z j)
      ≤ cellCB α δ L K
          (twoLawPsi α Rv μ νL νR v0 N h)
          (twoLawPsi α Rv μ νL νR v0 N h)
          ((1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h
            + ⨆ i, twoLawE α Rv μ νL νR v0 N h i) := by
  change PhiDres α (Zlaw μ νL v0 k (h + 1))
    (Zlaw μ νR v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) ≤ _
  rw [PhiDres_Zlaw_Zlaw_cross_succ α Rv μ νL νR v0 hrefl k j h]
  exact crossSquare_le_cellCB α Rv μ νL νR v0 hα hδ hL0 hL hK0 hK
    hsymm hN hk hj

lemma twoLawPsi_swap (N h : ℕ) :
    twoLawPsi α Rv μ νR νL v0 N h = twoLawPsi α Rv μ νL νR v0 N h := by
  apply le_antisymm
  · refine iSup_le fun lr => iSup_le fun p => ?_
    cases lr
    · simpa [twoLawPsi, biCrossPhi, biCrossFailure, biCrossSource, biCrossTarget] using
        (le_iSup (fun lr : Bool => ⨆ p : {p // p ∈ crossOrdIndex N},
          max (biCrossPhi α Rv μ νL νR v0 lr h p.val)
            (biCrossFailure Rv μ νL νR v0 lr h p.val)) true |> fun hsup =>
          le_trans (le_iSup (fun q : {p // p ∈ crossOrdIndex N} =>
            max (biCrossPhi α Rv μ νL νR v0 true h q.val)
              (biCrossFailure Rv μ νL νR v0 true h q.val)) p) hsup)
    · simpa [twoLawPsi, biCrossPhi, biCrossFailure, biCrossSource, biCrossTarget] using
        (le_iSup (fun lr : Bool => ⨆ p : {p // p ∈ crossOrdIndex N},
          max (biCrossPhi α Rv μ νL νR v0 lr h p.val)
            (biCrossFailure Rv μ νL νR v0 lr h p.val)) false |> fun hsup =>
          le_trans (le_iSup (fun q : {p // p ∈ crossOrdIndex N} =>
            max (biCrossPhi α Rv μ νL νR v0 false h q.val)
              (biCrossFailure Rv μ νL νR v0 false h q.val)) p) hsup)
  · refine iSup_le fun lr => iSup_le fun p => ?_
    cases lr
    · simpa [twoLawPsi, biCrossPhi, biCrossFailure, biCrossSource, biCrossTarget] using
        (le_iSup (fun lr : Bool => ⨆ p : {p // p ∈ crossOrdIndex N},
          max (biCrossPhi α Rv μ νR νL v0 lr h p.val)
            (biCrossFailure Rv μ νR νL v0 lr h p.val)) true |> fun hsup =>
          le_trans (le_iSup (fun q : {p // p ∈ crossOrdIndex N} =>
            max (biCrossPhi α Rv μ νR νL v0 true h q.val)
              (biCrossFailure Rv μ νR νL v0 true h q.val)) p) hsup)
    · simpa [twoLawPsi, biCrossPhi, biCrossFailure, biCrossSource, biCrossTarget] using
        (le_iSup (fun lr : Bool => ⨆ p : {p // p ∈ crossOrdIndex N},
          max (biCrossPhi α Rv μ νR νL v0 lr h p.val)
            (biCrossFailure Rv μ νR νL v0 lr h p.val)) false |> fun hsup =>
          le_trans (le_iSup (fun q : {p // p ∈ crossOrdIndex N} =>
            max (biCrossPhi α Rv μ νR νL v0 false h q.val)
              (biCrossFailure Rv μ νR νL v0 false h q.val)) p) hsup)

lemma twoLawE_sup_swap (N h : ℕ) :
    (⨆ i, twoLawE α Rv μ νR νL v0 N h i) =
      ⨆ i, twoLawE α Rv μ νL νR v0 N h i := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    obtain ⟨lr, sc⟩ := i
    cases lr
    · simpa [twoLawE, biCrossScreen] using
        (le_iSup (fun i => twoLawE α Rv μ νL νR v0 N h i) (true, sc))
    · simpa [twoLawE, biCrossScreen] using
        (le_iSup (fun i => twoLawE α Rv μ νL νR v0 N h i) (false, sc))
  · refine iSup_le fun i => ?_
    obtain ⟨lr, sc⟩ := i
    cases lr
    · simpa [twoLawE, biCrossScreen] using
        (le_iSup (fun i => twoLawE α Rv μ νR νL v0 N h i) (true, sc))
    · simpa [twoLawE, biCrossScreen] using
        (le_iSup (fun i => twoLawE α Rv μ νR νL v0 N h i) (false, sc))

/-- The same forced-forced row in the reverse orientation. -/
theorem biCrossPhi_ZZ_rev_le_cellCB {δ L K : ℝ} (hα : 1 ≤ α)
    (hδ : 0 < δ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : Rv v0 v0) (hsymm : ∀ a b, Rv a b → Rv b a)
    {N k j h : ℕ} (hN : 2 ≤ N) (hk : k ≤ N) (hj : j ≤ N) :
    biCrossPhi α Rv μ νL νR v0 false (h + 1) (Tgt.Z k, Tgt.Z j)
      ≤ cellCB α δ L K
          (twoLawPsi α Rv μ νL νR v0 N h)
          (twoLawPsi α Rv μ νL νR v0 N h)
          ((1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h
            + ⨆ i, twoLawE α Rv μ νL νR v0 N h i) := by
  change PhiDres α (Zlaw μ νR v0 k (h + 1))
    (Zlaw μ νL v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) ≤ _
  rw [PhiDres_Zlaw_Zlaw_cross_succ α Rv μ νR νL v0 hrefl k j h]
  rw [← twoLawPsi_swap α Rv μ νL νR v0 N h,
    ← twoLawE_sup_swap α Rv μ νL νR v0 N h]
  exact crossSquare_le_cellCB α Rv μ νR νL v0 hα hδ hL0 hL hK0 hK
    hsymm hN hk hj

/-! ### Raw-failure product and forced rows -/

/-- A fixed straight pairing gives the raw-failure product row. -/
lemma failureD_square_le_straight {X : Type} (ρa ρb ρc ρd : PMF X)
    (R : X → X → Prop) :
    failureD (prodPMF ρa ρb) (prodPMF ρc ρd) (SquareRel R)
      ≤ failureD ρa ρc R + failureD ρb ρd R := by
  rw [failureD]
  calc
    (∑' p : X × X, prodPMF ρa ρb p *
        qE (prodPMF ρc ρd) (SquareRel R) p)
      ≤ ∑' p : X × X, ((ρa p.1 * qE ρc R p.1) * ρb p.2
          + ρa p.1 * (ρb p.2 * qE ρd R p.2)) := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        rw [prodPMF_apply]
        have hq := qE_square_le_straight_sum ρc ρd R p.1 p.2
        calc
          ρa p.1 * ρb p.2 * qE (prodPMF ρc ρd) (SquareRel R) p
              ≤ ρa p.1 * ρb p.2 * (qE ρc R p.1 + qE ρd R p.2) :=
                mul_le_mul_right hq _
          _ = _ := by ring
    _ = failureD ρa ρc R + failureD ρb ρd R := by
      rw [ENNReal.tsum_add,
        tsum_prod_split (fun x => ρa x * qE ρc R x) (fun x => ρb x),
        tsum_prod_split (fun x => ρa x) (fun x => ρb x * qE ρd R x),
        PMF.tsum_coe, PMF.tsum_coe, mul_one, one_mul, failureD, failureD]

/-- Exact raw-failure transfer through two fixed roots. -/
lemma failureD_muM_muM_cross_succ (v w : V) (k j h : ℕ) :
    failureD (muM (varyK μ νL v0) (v, k) (h + 1))
        (muM (varyK μ νR v0) (w, j) (h + 1))
        (fullSim (labRel Rv) (h + 1))
      = if Rv v w then
          failureD (Xi μ νL v0 k h) (Xi μ νR v0 j h)
            (SquareRel (fullSim (labRel Rv) h))
        else 1 := by
  rw [muM_varyK_succ μ νL v0 v k h,
    muM_varyK_succ μ νR v0 w j h, failureD, tsum_map_mul]
  by_cases hvw : Rv v w
  · rw [if_pos hvw, failureD]
    exact tsum_congr fun xp => by
      rw [qE_map_branch_law,
        if_pos (show labRel Rv (v, k) (w, j) from hvw)]
  · rw [if_neg hvw]
    calc
      (∑' xp, Xi μ νL v0 k h xp *
          qE ((Xi μ νR v0 j h).map (branch (w, j)))
            (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp))
          = ∑' xp, Xi μ νL v0 k h xp * 1 := by
              refine tsum_congr fun xp => ?_
              rw [qE_map_branch_law,
                if_neg (show ¬ labRel Rv (v, k) (w, j) from hvw)]
      _ = 1 := by rw [tsum_congr fun xp => mul_one _, PMF.tsum_coe]

/-- Every bounded counter-cell failure is at most two ordinary ledger units. -/
lemma failureD_Xi_cross_le {N k j h : ℕ} (hN : 2 ≤ N)
    (hk : k ≤ N) (hj : j ≤ N) :
    failureD (Xi μ νL v0 k h) (Xi μ νR v0 j h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ 2 * twoLawPsi α Rv μ νL νR v0 N h := by
  rw [Xi_eq_prod μ νL v0 k h, Xi_eq_prod μ νR v0 j h]
  refine le_trans (failureD_square_le_straight _ _ _ _ _) ?_
  have hp0 : (gcomp0 k, gcomp0 j) ∈ crossOrdIndex N :=
    Finset.mem_product.mpr
      ⟨(show gcomp0 k ∈ crossTgtIndex N from
          gpair_mem_crossTgtIndex hN hk (gcomp_mem_gpair k).1),
        (show gcomp0 j ∈ crossTgtIndex N from
          gpair_mem_crossTgtIndex hN hj (gcomp_mem_gpair j).1)⟩
  have hp1 : (gcomp1 k, gcomp1 j) ∈ crossOrdIndex N :=
    Finset.mem_product.mpr
      ⟨(show gcomp1 k ∈ crossTgtIndex N from
          gpair_mem_crossTgtIndex hN hk (gcomp_mem_gpair k).2),
        (show gcomp1 j ∈ crossTgtIndex N from
          gpair_mem_crossTgtIndex hN hj (gcomp_mem_gpair j).2)⟩
  have h0 := biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
    (h := h) (lr := true) hp0
  have h1 := biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
    (h := h) (lr := true) hp1
  refine le_trans (add_le_add ?_ ?_) (le_of_eq (by ring))
  · simpa [biCrossFailure, biCrossSource, biCrossTarget] using h0
  · simpa [biCrossFailure, biCrossSource, biCrossTarget] using h1

lemma failureD_bind_left {A X : Type} (w : PMF A) (f : A → PMF X)
    (ρt : PMF X) (R : X → X → Prop) :
    failureD (w.bind f) ρt R = ∑' a, w a * failureD (f a) ρt R := by
  rw [failureD, tsum_bind_mul]
  exact tsum_congr fun a => by rw [failureD]

lemma failureD_bind_right {A X : Type} (ρs : PMF X) (w : PMF A)
    (f : A → PMF X) (R : X → X → Prop) :
    failureD ρs (w.bind f) R = ∑' a, w a * failureD ρs (f a) R := by
  rw [failureD]
  calc
    (∑' x, ρs x * qE (w.bind f) R x)
        = ∑' x, ∑' a, w a * (ρs x * qE (f a) R x) := by
            refine tsum_congr fun x => ?_
            rw [qE_bind, ← ENNReal.tsum_mul_left]
            exact tsum_congr fun a => by ring
    _ = ∑' a, ∑' x, w a * (ρs x * qE (f a) R x) := ENNReal.tsum_comm
    _ = ∑' a, w a * failureD ρs (f a) R := by
          refine tsum_congr fun a => ?_
          rw [failureD, ENNReal.tsum_mul_left]

/-- Root-incompatibility budgets for the three rows containing a fresh law. -/
noncomputable def rootFailZF : ℝ≥0∞ :=
  ∑' s : V × ℕ, freshQ μ νR s * (if Rv v0 s.1 then 0 else 1)

noncomputable def rootFailFZ : ℝ≥0∞ :=
  ∑' s : V × ℕ, freshQ μ νL s * (if Rv s.1 v0 then 0 else 1)

noncomputable def rootFailFF : ℝ≥0∞ :=
  ∑' s : V × ℕ, freshQ μ νL s *
    ∑' t : V × ℕ, freshQ μ νR t * (if Rv s.1 t.1 then 0 else 1)

lemma rootFailZF_eq : rootFailZF Rv μ νR v0 = qE μ Rv v0 := by
  rw [rootFailZF, ENNReal.tsum_prod', qE_eq_tsum_mul]
  refine tsum_congr fun v => ?_
  calc
    (∑' k, freshQ μ νR (v, k) * (if Rv v0 v then 0 else 1))
        = ∑' k, νR k * (μ v * (if Rv v0 v then 0 else 1)) := by
            refine tsum_congr fun k => ?_
            rw [show freshQ μ νR (v, k) = μ v * νR k from prodPMF_apply μ νR _]
            ring
    _ = μ v * (if Rv v0 v then 0 else 1) := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = μ v * badInd Rv v0 v := by
          by_cases hv : Rv v0 v <;> simp [badInd, hv]

lemma rootFailFZ_eq (hsymm : ∀ a b, Rv a b → Rv b a) :
    rootFailFZ Rv μ νL v0 = qE μ Rv v0 := by
  rw [rootFailFZ, ENNReal.tsum_prod', qE_eq_tsum_mul]
  refine tsum_congr fun v => ?_
  calc
    (∑' k, freshQ μ νL (v, k) * (if Rv v v0 then 0 else 1))
        = ∑' k, νL k * (μ v * (if Rv v v0 then 0 else 1)) := by
            refine tsum_congr fun k => ?_
            rw [show freshQ μ νL (v, k) = μ v * νL k from prodPMF_apply μ νL _]
            ring
    _ = μ v * (if Rv v v0 then 0 else 1) := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = μ v * badInd Rv v0 v := by
          by_cases hv : Rv v v0
          · rw [if_pos hv]
            simp [badInd, hsymm v v0 hv]
          · rw [if_neg hv]
            have hv' : ¬ Rv v0 v := fun h => hv (hsymm v0 v h)
            simp [badInd, hv']

lemma rootFailFF_eq : rootFailFF Rv μ νL νR = failureD μ μ Rv := by
  rw [rootFailFF, ENNReal.tsum_prod']
  calc
    (∑' v, ∑' k, freshQ μ νL (v, k) *
        ∑' t : V × ℕ, freshQ μ νR t * (if Rv v t.1 then 0 else 1))
        = ∑' v, ∑' k, νL k * (μ v *
            ∑' w, ∑' j, freshQ μ νR (w, j) *
              (if Rv v w then 0 else 1)) := by
            refine tsum_congr fun v => tsum_congr fun k => ?_
            rw [ENNReal.tsum_prod',
              show freshQ μ νL (v, k) = μ v * νL k from prodPMF_apply μ νL _]
            ring
    _ = ∑' v, μ v * ∑' w, μ w * (if Rv v w then 0 else 1) := by
          refine tsum_congr fun v => ?_
          have hinner : (∑' w, ∑' j, freshQ μ νR (w, j) *
                (if Rv v w then 0 else 1))
              = ∑' w, μ w * (if Rv v w then 0 else 1) := by
            refine tsum_congr fun w => ?_
            calc
              (∑' j, freshQ μ νR (w, j) * (if Rv v w then 0 else 1))
                  = ∑' j, νR j * (μ w * (if Rv v w then 0 else 1)) := by
                      refine tsum_congr fun j => ?_
                      rw [show freshQ μ νR (w, j) = μ w * νR j from
                        prodPMF_apply μ νR _]
                      ring
              _ = μ w * (if Rv v w then 0 else 1) := by
                    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          rw [hinner]
          calc
            (∑' k, νL k * (μ v * ∑' w, μ w * (if Rv v w then 0 else 1)))
                = (∑' k, νL k) *
                    (μ v * ∑' w, μ w * (if Rv v w then 0 else 1)) :=
                      ENNReal.tsum_mul_right
            _ = μ v * ∑' w, μ w * (if Rv v w then 0 else 1) := by
                  rw [PMF.tsum_coe, one_mul]
    _ = failureD μ μ Rv := by
          rw [failureD]
          refine tsum_congr fun v => ?_
          rw [qE_eq_tsum_mul]
          congr 1

lemma rootFailZF_le_rootPotential (hα : 1 ≤ α) :
    rootFailZF Rv μ νR v0 ≤ phiE α (q μ Rv v0) := by
  rw [rootFailZF_eq]
  rw [show qE μ Rv v0 = ENNReal.ofReal (q μ Rv v0) from
    (ENNReal.ofReal_toReal qE_ne_top).symm]
  exact ofReal_le_phiE (le_trans zero_le_one hα) q_nonneg q_le_one

lemma rootFailFZ_le_rootPotential (hα : 1 ≤ α)
    (hsymm : ∀ a b, Rv a b → Rv b a) :
    rootFailFZ Rv μ νL v0 ≤ phiE α (q μ Rv v0) := by
  rw [rootFailFZ_eq Rv μ νL v0 hsymm]
  rw [show qE μ Rv v0 = ENNReal.ofReal (q μ Rv v0) from
    (ENNReal.ofReal_toReal qE_ne_top).symm]
  exact ofReal_le_phiE (le_trans zero_le_one hα) q_nonneg q_le_one

lemma rootFailFF_le_eta (hα : 1 ≤ α) :
    rootFailFF Rv μ νL νR ≤ etaG α Rv μ := by
  rw [rootFailFF_eq, failureD, etaG]
  exact tsum_qE_le_PhiD (le_trans zero_le_one hα) μ μ Rv

/-- Forced source, fresh target raw-failure row. -/
theorem biCrossFailure_ZF_le {N k h : ℕ} (hN : 2 ≤ N) (hk : k ≤ N)
    (hRbd : ∀ j, (νR j : ℝ≥0∞) ≠ 0 → j ≤ N) :
    biCrossFailure Rv μ νL νR v0 true (h + 1) (Tgt.Z k, Tgt.F)
      ≤ rootFailZF Rv μ νR v0
        + 2 * twoLawPsi α Rv μ νL νR v0 N h := by
  change failureD (Zlaw μ νL v0 k (h + 1)) (Tlaw μ νR v0 (h + 1))
    (fullSim (labRel Rv) (h + 1)) ≤ _
  rw [show Tlaw μ νR v0 (h + 1) = (freshQ μ νR).bind
      (fun s => muM (varyK μ νR v0) s (h + 1)) from rfl,
    failureD_bind_right]
  calc
    (∑' s, freshQ μ νR s * failureD (Zlaw μ νL v0 k (h + 1))
        (muM (varyK μ νR v0) s (h + 1))
        (fullSim (labRel Rv) (h + 1)))
      ≤ ∑' s, freshQ μ νR s *
          ((if Rv v0 s.1 then 0 else 1)
            + 2 * twoLawPsi α Rv μ νL νR v0 N h) := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        obtain ⟨w, j⟩ := s
        by_cases hj0 : (νR j : ℝ≥0∞) = 0
        · rw [show freshQ μ νR (w, j) = μ w * νR j from prodPMF_apply μ νR _,
            hj0, mul_zero, zero_mul, zero_mul]
        rw [show Zlaw μ νL v0 k (h + 1) =
          muM (varyK μ νL v0) (v0, k) (h + 1) from rfl,
          failureD_muM_muM_cross_succ Rv μ νL νR v0]
        by_cases hw : Rv v0 w
        · rw [if_pos hw, if_pos hw, zero_add]
          exact mul_le_mul_right (failureD_Xi_cross_le α Rv μ νL νR v0 hN hk
            (hRbd j hj0)) _
        · rw [if_neg hw, if_neg hw]
          exact mul_le_mul_right le_self_add _
    _ = rootFailZF Rv μ νR v0
          + 2 * twoLawPsi α Rv μ νL νR v0 N h := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          rootFailZF]

/-- Fresh source, forced target raw-failure row. -/
theorem biCrossFailure_FZ_le {N j h : ℕ} (hN : 2 ≤ N) (hj : j ≤ N)
    (hLbd : ∀ k, (νL k : ℝ≥0∞) ≠ 0 → k ≤ N) :
    biCrossFailure Rv μ νL νR v0 true (h + 1) (Tgt.F, Tgt.Z j)
      ≤ rootFailFZ Rv μ νL v0
        + 2 * twoLawPsi α Rv μ νL νR v0 N h := by
  change failureD (Tlaw μ νL v0 (h + 1)) (Zlaw μ νR v0 j (h + 1))
    (fullSim (labRel Rv) (h + 1)) ≤ _
  rw [show Tlaw μ νL v0 (h + 1) = (freshQ μ νL).bind
      (fun s => muM (varyK μ νL v0) s (h + 1)) from rfl,
    failureD_bind_left]
  calc
    (∑' s, freshQ μ νL s * failureD
        (muM (varyK μ νL v0) s (h + 1)) (Zlaw μ νR v0 j (h + 1))
        (fullSim (labRel Rv) (h + 1)))
      ≤ ∑' s, freshQ μ νL s *
          ((if Rv s.1 v0 then 0 else 1)
            + 2 * twoLawPsi α Rv μ νL νR v0 N h) := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        obtain ⟨v, k⟩ := s
        by_cases hk0 : (νL k : ℝ≥0∞) = 0
        · rw [show freshQ μ νL (v, k) = μ v * νL k from prodPMF_apply μ νL _,
            hk0, mul_zero, zero_mul, zero_mul]
        rw [show Zlaw μ νR v0 j (h + 1) =
          muM (varyK μ νR v0) (v0, j) (h + 1) from rfl,
          failureD_muM_muM_cross_succ Rv μ νL νR v0]
        by_cases hv : Rv v v0
        · rw [if_pos hv, if_pos hv, zero_add]
          exact mul_le_mul_right (failureD_Xi_cross_le α Rv μ νL νR v0 hN
            (hLbd k hk0) hj) _
        · rw [if_neg hv, if_neg hv]
          exact mul_le_mul_right le_self_add _
    _ = rootFailFZ Rv μ νL v0
          + 2 * twoLawPsi α Rv μ νL νR v0 N h := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          rootFailFZ]

/-- Fresh/fresh raw-failure row. -/
theorem biCrossFailure_FF_le {N h : ℕ} (hN : 2 ≤ N)
    (hLbd : ∀ k, (νL k : ℝ≥0∞) ≠ 0 → k ≤ N)
    (hRbd : ∀ j, (νR j : ℝ≥0∞) ≠ 0 → j ≤ N) :
    biCrossFailure Rv μ νL νR v0 true (h + 1) (Tgt.F, Tgt.F)
      ≤ rootFailFF Rv μ νL νR
        + 2 * twoLawPsi α Rv μ νL νR v0 N h := by
  change failureD (Tlaw μ νL v0 (h + 1)) (Tlaw μ νR v0 (h + 1))
    (fullSim (labRel Rv) (h + 1)) ≤ _
  rw [show Tlaw μ νL v0 (h + 1) = (freshQ μ νL).bind
      (fun s => muM (varyK μ νL v0) s (h + 1)) from rfl,
    show Tlaw μ νR v0 (h + 1) = (freshQ μ νR).bind
      (fun s => muM (varyK μ νR v0) s (h + 1)) from rfl,
    failureD_bind_bind]
  calc
    (∑' s, freshQ μ νL s * ∑' t, freshQ μ νR t * failureD
        (muM (varyK μ νL v0) s (h + 1))
        (muM (varyK μ νR v0) t (h + 1))
        (fullSim (labRel Rv) (h + 1)))
      ≤ ∑' s, freshQ μ νL s * ∑' t, freshQ μ νR t *
          ((if Rv s.1 t.1 then 0 else 1)
            + 2 * twoLawPsi α Rv μ νL νR v0 N h) := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        obtain ⟨v, k⟩ := s
        by_cases hk0 : (νL k : ℝ≥0∞) = 0
        · rw [show freshQ μ νL (v, k) = μ v * νL k from prodPMF_apply μ νL _,
            hk0, mul_zero, zero_mul, zero_mul]
        refine mul_le_mul_right ?_ _
        refine ENNReal.tsum_le_tsum fun t => ?_
        obtain ⟨w, j⟩ := t
        by_cases hj0 : (νR j : ℝ≥0∞) = 0
        · rw [show freshQ μ νR (w, j) = μ w * νR j from prodPMF_apply μ νR _,
            hj0, mul_zero, zero_mul, zero_mul]
        rw [failureD_muM_muM_cross_succ Rv μ νL νR v0]
        by_cases hvw : Rv v w
        · rw [if_pos hvw, if_pos hvw, zero_add]
          exact mul_le_mul_right (failureD_Xi_cross_le α Rv μ νL νR v0 hN
            (hLbd k hk0) (hRbd j hj0)) _
        · rw [if_neg hvw, if_neg hvw]
          exact mul_le_mul_right le_self_add _
    _ = rootFailFF Rv μ νL νR
          + 2 * twoLawPsi α Rv μ νL νR v0 N h := by
        rw [rootFailFF]
        simp_rw [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          PMF.tsum_coe, one_mul]
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Exact forced/forced root transfer for raw failure. -/
lemma failureD_Zlaw_Zlaw_cross_succ (hrefl : Rv v0 v0) (k j h : ℕ) :
    failureD (Zlaw μ νL v0 k (h + 1)) (Zlaw μ νR v0 j (h + 1))
        (fullSim (labRel Rv) (h + 1))
      = failureD (Xi μ νL v0 k h) (Xi μ νR v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) := by
  rw [show Zlaw μ νL v0 k (h + 1) =
      (Xi μ νL v0 k h).map (branch (v0, k)) from
        muM_varyK_succ μ νL v0 v0 k h,
    show Zlaw μ νR v0 j (h + 1) =
      (Xi μ νR v0 j h).map (branch (v0, j)) from
        muM_varyK_succ μ νR v0 v0 j h,
    failureD, tsum_map_mul, failureD]
  refine tsum_congr fun xp => ?_
  rw [qE_map_branch_law,
    if_pos (show labRel Rv (v0, k) (v0, j) from hrefl)]

/-- The assembled forced/forced raw-failure row in the forward direction. -/
theorem biCrossFailure_ZZ_le {N k j h : ℕ} (hN : 2 ≤ N)
    (hk : k ≤ N) (hj : j ≤ N) (hrefl : Rv v0 v0) :
    biCrossFailure Rv μ νL νR v0 true (h + 1) (Tgt.Z k, Tgt.Z j)
      ≤ 2 * twoLawPsi α Rv μ νL νR v0 N h := by
  change failureD (Zlaw μ νL v0 k (h + 1)) (Zlaw μ νR v0 j (h + 1))
    (fullSim (labRel Rv) (h + 1)) ≤ _
  rw [failureD_Zlaw_Zlaw_cross_succ Rv μ νL νR v0 hrefl k j h,
    Xi_eq_prod μ νL v0 k h, Xi_eq_prod μ νR v0 j h]
  refine le_trans (failureD_square_le_straight _ _ _ _ _) ?_
  have h0 : failureD (interpT μ νL v0 h (gcomp0 k))
      (interpT μ νR v0 h (gcomp0 j)) (fullSim (labRel Rv) h)
      ≤ twoLawPsi α Rv μ νL νR v0 N h := by
    have hp : (gcomp0 k, gcomp0 j) ∈ crossOrdIndex N :=
      Finset.mem_product.mpr
        ⟨gpair_mem_crossTgtIndex hN hk (gcomp_mem_gpair k).1,
          gpair_mem_crossTgtIndex hN hj (gcomp_mem_gpair j).1⟩
    simpa [biCrossFailure, biCrossSource, biCrossTarget] using
      (biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
        (h := h) (lr := true) hp)
  have h1 : failureD (interpT μ νL v0 h (gcomp1 k))
      (interpT μ νR v0 h (gcomp1 j)) (fullSim (labRel Rv) h)
      ≤ twoLawPsi α Rv μ νL νR v0 N h := by
    have hp : (gcomp1 k, gcomp1 j) ∈ crossOrdIndex N :=
      Finset.mem_product.mpr
        ⟨gpair_mem_crossTgtIndex hN hk (gcomp_mem_gpair k).2,
          gpair_mem_crossTgtIndex hN hj (gcomp_mem_gpair j).2⟩
    simpa [biCrossFailure, biCrossSource, biCrossTarget] using
      (biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
        (h := h) (lr := true) hp)
  exact le_trans (add_le_add h0 h1) (le_of_eq (by ring))

/-! ### The asymmetric fresh-target one-sided term -/

/-- A pointwise countable tilt bound can be integrated through a screen. -/
lemma screenE_tsum_tilt_le {X A : Type} (ρs : PMF X)
    (R : X → X → Prop) (zs : List (PMF X)) (g : X → ℝ≥0∞)
    (c : A → ℝ≥0∞) (f : A → X → ℝ≥0∞)
    (hg : ∀ x, g x ≤ ∑' a, c a * f a x) :
    screenE ρs R zs g ≤ ∑' a, c a * screenE ρs R zs (f a) := by
  rw [screenE]
  calc
    (∑' x, ρs x * screenInd R zs x * g x)
      ≤ ∑' x, ρs x * screenInd R zs x * (∑' a, c a * f a x) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hg x) _
    _ = ∑' x, ∑' a, c a * (ρs x * screenInd R zs x * f a x) := by
      refine tsum_congr fun x => ?_
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun a => by ring
    _ = ∑' a, ∑' x, c a * (ρs x * screenInd R zs x * f a x) :=
      ENNReal.tsum_comm
    _ = ∑' a, c a * screenE ρs R zs (f a) := by
      refine tsum_congr fun a => ?_
      rw [screenE, ENNReal.tsum_mul_left]

/-- Union expansion for the target-component dead event, with an arbitrary
source law. -/
lemma component_dead_exists_le {X : Type} (ρs : PMF X) (w : PMF ℕ)
    (f : ℕ → PMF X) (R : X → X → Prop) (W : X → ℝ≥0∞) :
    (∑' x, ρs x * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
      * W x))
      ≤ ∑' j, ∑' x, ρs x *
        ((if w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0) * W x) := by
  have hpt : ∀ x, ρs x *
      ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0) * W x)
      ≤ ∑' j, ρs x *
        ((if w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0) * W x) := by
    intro x
    by_cases hex : ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0
    · obtain ⟨j, hj⟩ := hex
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum j)
      rw [if_pos ⟨j, hj⟩, if_pos hj]
    · rw [if_neg hex, zero_mul, mul_zero]
      exact zero_le
  exact le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ENNReal.tsum_comm)

/-- The one-sided term in the cross fresh-target split is a concrete sum of
mixed product coordinates.  This is the asymmetric replacement for the
same-law diagonal-reserve charge. -/
theorem crossOneSided_le_crossDres (hα : 1 ≤ α) (k h : ℕ) :
    (∑' xp, Xi μ νL v0 k h xp *
      ((if ∃ j, νR j ≠ 0 ∧ rE (Xi μ νR v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
        * WresD α (XiBar μ νR v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp))
      ≤ ∑' j, if (νR j : ℝ≥0∞) = 0 then 0 else
        ∑' i, (if (νR i : ℝ≥0∞) = 0 then 0 else (νR i : ℝ≥0∞) ^ (-α))
          * crossDres α (Xi μ νL v0 k h) (Xi μ νR v0 j h)
              (Xi μ νR v0 i h) (SquareRel (fullSim (labRel Rv) h)) := by
  let R2 := SquareRel (fullSim (labRel Rv) h)
  refine le_trans (component_dead_exists_le (Xi μ νL v0 k h) νR
    (fun j => Xi μ νR v0 j h) R2
    (WresD α (XiBar μ νR v0 h) R2)) ?_
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases hj : (νR j : ℝ≥0∞) = 0
  · rw [if_pos hj]
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun xp => ?_)
    rw [if_neg (fun hbad => hbad.1 hj), zero_mul, mul_zero]
  · rw [if_neg hj]
    have heq : (∑' xp, Xi μ νL v0 k h xp *
          ((if νR j ≠ 0 ∧ rE (Xi μ νR v0 j h) R2 xp = 0 then 1 else 0)
            * WresD α (XiBar μ νR v0 h) R2 xp))
        = screenE (Xi μ νL v0 k h) R2 [Xi μ νR v0 j h]
            (WresD α (XiBar μ νR v0 h) R2) := by
      rw [screenE_singleton]
      refine tsum_congr fun xp => ?_
      by_cases hd : rE (Xi μ νR v0 j h) R2 xp = 0
      · rw [if_pos ⟨hj, hd⟩, if_pos hd]
      · rw [if_neg (fun hc => hd hc.2), if_neg hd]
    rw [heq]
    refine le_trans (screenE_tsum_tilt_le (Xi μ νL v0 k h) R2
      [Xi μ νR v0 j h] (WresD α (XiBar μ νR v0 h) R2)
      (fun i => if (νR i : ℝ≥0∞) = 0 then 0 else (νR i : ℝ≥0∞) ^ (-α))
      (fun i => WresD α (Xi μ νR v0 i h) R2)
      (by simpa [R2] using
        (WresD_XiBar_le_sum α Rv μ νR v0 (le_trans zero_le_one hα) h))) ?_
    refine ENNReal.tsum_le_tsum fun i => mul_le_mul_right ?_ _
    exact screenE_WresD_le_crossDres_of_mem α _ _ _ _ _
      (List.mem_singleton_self _)

/-- A mixed product coordinate between concrete counter cells is controlled
entirely by the two ordinary child families. -/
theorem crossDres_Xi_le (hα : 1 ≤ α) {N k j i h : ℕ}
    (hN : 2 ≤ N) (hk : k ≤ N) (hj : j ≤ N) (hi : i ≤ N) :
    crossDres α (Xi μ νL v0 k h) (Xi μ νR v0 j h) (Xi μ νR v0 i h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ 4 * ((1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h)
          * (1 + ENNReal.ofReal α * twoLawPsi α Rv μ νL νR v0 N h) := by
  let M := twoLawPsi α Rv μ νL νR v0 N h
  have hL : ∀ e : Bool,
      (if e then gcomp0 k else gcomp1 k) ∈ crossTgtIndex N :=
    fun e => gcomp_mem_crossTgtIndex_bool hN hk e
  have hB : ∀ e : Bool,
      (if e then gcomp0 j else gcomp1 j) ∈ crossTgtIndex N :=
    fun e => gcomp_mem_crossTgtIndex_bool hN hj e
  have hT : ∀ e : Bool,
      (if e then gcomp0 i else gcomp1 i) ∈ crossTgtIndex N :=
    fun e => gcomp_mem_crossTgtIndex_bool hN hi e
  have hmix : ∀ e f g : Bool,
      crossDres α
          (interpT μ νL v0 h (if e then gcomp0 k else gcomp1 k))
          (interpT μ νR v0 h (if f then gcomp0 j else gcomp1 j))
          (interpT μ νR v0 h (if g then gcomp0 i else gcomp1 i))
          (fullSim (labRel Rv) h) ≤ (1 + ENNReal.ofReal α) * M := by
    intro e f g
    have hpf : ((if e then gcomp0 k else gcomp1 k),
        (if f then gcomp0 j else gcomp1 j)) ∈ crossOrdIndex N :=
      Finset.mem_product.mpr ⟨hL e, hB f⟩
    have hpg : ((if e then gcomp0 k else gcomp1 k),
        (if g then gcomp0 i else gcomp1 i)) ∈ crossOrdIndex N :=
      Finset.mem_product.mpr ⟨hL e, hT g⟩
    refine le_trans (crossDres_le_failureD_add_PhiDres α hα _ _ _ _) ?_
    have hf := biCrossFailure_le_twoLawPsi α Rv μ νL νR v0
      (h := h) (lr := true) hpf
    have hp := biCrossPhi_le_twoLawPsi α Rv μ νL νR v0
      (h := h) (lr := true) hpg
    calc
      failureD
            (interpT μ νL v0 h (if e then gcomp0 k else gcomp1 k))
            (interpT μ νR v0 h (if f then gcomp0 j else gcomp1 j))
            (fullSim (labRel Rv) h)
          + ENNReal.ofReal α * PhiDres α
            (interpT μ νL v0 h (if e then gcomp0 k else gcomp1 k))
            (interpT μ νR v0 h (if g then gcomp0 i else gcomp1 i))
            (fullSim (labRel Rv) h)
        ≤ M + ENNReal.ofReal α * M := by
          simpa [M, biCrossFailure, biCrossPhi, biCrossSource, biCrossTarget] using
            (add_le_add hf (mul_le_mul_right hp (ENNReal.ofReal α)))
      _ = (1 + ENNReal.ofReal α) * M := by ring
  have hphi : ∀ e g : Bool,
      PhiDres α
          (interpT μ νL v0 h (if e then gcomp0 k else gcomp1 k))
          (interpT μ νR v0 h (if g then gcomp0 i else gcomp1 i))
          (fullSim (labRel Rv) h) ≤ M := by
    intro e g
    have hp : ((if e then gcomp0 k else gcomp1 k),
        (if g then gcomp0 i else gcomp1 i)) ∈ crossOrdIndex N :=
      Finset.mem_product.mpr ⟨hL e, hT g⟩
    simpa [M, biCrossPhi, biCrossSource, biCrossTarget] using
      (biCrossPhi_le_twoLawPsi α Rv μ νL νR v0
        (h := h) (lr := true) hp)
  rw [Xi_eq_prod μ νL v0 k h, Xi_eq_prod μ νR v0 j h,
    Xi_eq_prod μ νR v0 i h]
  refine le_trans (crossDres_square_le α hα _ _ _ _ _ _ _) ?_
  refine le_trans (add_le_add (add_le_add (add_le_add
    (mul_le_mul' (hmix true true true)
      (add_le_add le_rfl (mul_le_mul_right (hphi false false) _)))
    (mul_le_mul' (hmix true true false)
      (add_le_add le_rfl (mul_le_mul_right (hphi false true) _))))
    (mul_le_mul'
      (add_le_add le_rfl (mul_le_mul_right (hphi true true) _))
      (hmix false false false)))
    (mul_le_mul'
      (add_le_add le_rfl (mul_le_mul_right (hphi true false) _))
      (hmix false false true))) ?_
  exact le_of_eq (by ring)

/-- Finite-support collapse of the asymmetric one-sided term. -/
theorem crossOneSided_le_ledger (hα : 1 ≤ α) (SR : Finset ℕ)
    (hRsupp : ∀ n : ℕ, (νR n : ℝ≥0∞) ≠ 0 ↔ n ∈ SR)
    (hRbd : ∀ n ∈ SR, n ≤ N)
    (hT : (∑' i, if (νR i : ℝ≥0∞) = 0 then 0
      else (νR i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hN : 2 ≤ N) {k h : ℕ} (hk : k ≤ N) :
    (∑' xp, Xi μ νL v0 k h xp *
      ((if ∃ j, νR j ≠ 0 ∧ rE (Xi μ νR v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
        * WresD α (XiBar μ νR v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp))
      ≤ SR.card * (Tν *
        (4 * ((1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h)
          * (1 + ENNReal.ofReal α * twoLawPsi α Rv μ νL νR v0 N h))) := by
  let C := 4 * ((1 + ENNReal.ofReal α) * twoLawPsi α Rv μ νL νR v0 N h)
    * (1 + ENNReal.ofReal α * twoLawPsi α Rv μ νL νR v0 N h)
  refine le_trans (crossOneSided_le_crossDres α Rv μ νL νR v0 hα k h) ?_
  have hout : ∀ j ∉ SR, (if (νR j : ℝ≥0∞) = 0 then 0 else
      ∑' i, (if (νR i : ℝ≥0∞) = 0 then 0 else (νR i : ℝ≥0∞) ^ (-α))
        * crossDres α (Xi μ νL v0 k h) (Xi μ νR v0 j h)
          (Xi μ νR v0 i h) (SquareRel (fullSim (labRel Rv) h))) = 0 := by
    intro j hj
    have hz : (νR j : ℝ≥0∞) = 0 := by
      by_contra hn
      exact hj ((hRsupp j).mp hn)
    rw [if_pos hz]
  rw [tsum_eq_sum hout]
  have hinner : ∀ j ∈ SR, (if (νR j : ℝ≥0∞) = 0 then 0 else
      ∑' i, (if (νR i : ℝ≥0∞) = 0 then 0 else (νR i : ℝ≥0∞) ^ (-α))
        * crossDres α (Xi μ νL v0 k h) (Xi μ νR v0 j h)
          (Xi μ νR v0 i h) (SquareRel (fullSim (labRel Rv) h))) ≤ Tν * C := by
    intro j hj
    rw [if_neg ((hRsupp j).mpr hj)]
    calc
      (∑' i, (if (νR i : ℝ≥0∞) = 0 then 0 else (νR i : ℝ≥0∞) ^ (-α))
          * crossDres α (Xi μ νL v0 k h) (Xi μ νR v0 j h)
            (Xi μ νR v0 i h) (SquareRel (fullSim (labRel Rv) h)))
        ≤ ∑' i, (if (νR i : ℝ≥0∞) = 0 then 0 else (νR i : ℝ≥0∞) ^ (-α))
            * C := ENNReal.tsum_le_tsum fun i => by
              by_cases hi0 : (νR i : ℝ≥0∞) = 0
              · rw [if_pos hi0, zero_mul, zero_mul]
              · rw [if_neg hi0]
                exact mul_le_mul_right
                  (crossDres_Xi_le α Rv μ νL νR v0 hα hN hk (hRbd j hj)
                    (hRbd i ((hRsupp i).mp hi0))) _
      _ = (∑' i, if (νR i : ℝ≥0∞) = 0 then 0
          else (νR i : ℝ≥0∞) ^ (-α)) * C := ENNReal.tsum_mul_right
      _ ≤ Tν * C := by simpa [mul_comm] using (mul_le_mul_right hT C)
  calc
    (∑ j ∈ SR, if (νR j : ℝ≥0∞) = 0 then 0 else
        ∑' i, (if (νR i : ℝ≥0∞) = 0 then 0 else (νR i : ℝ≥0∞) ^ (-α))
          * crossDres α (Xi μ νL v0 k h) (Xi μ νR v0 j h)
            (Xi μ νR v0 i h) (SquareRel (fullSim (labRel Rv) h)))
      ≤ ∑ _j ∈ SR, Tν * C := Finset.sum_le_sum hinner
    _ = SR.card * (Tν * C) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Uniform cross-law counter-cell bound at one height. -/
noncomputable def crossCellB (α δ L K : ℝ) (M E : ℝ≥0∞) : ℝ≥0∞ :=
  cellCB α δ L K M M ((1 + ENNReal.ofReal α) * M + E)

/-- The additional fresh-target one-sided charge. -/
noncomputable def crossOneB (α : ℝ) (Tν M : ℝ≥0∞) (nR : ℕ) : ℝ≥0∞ :=
  nR * (Tν * (4 * ((1 + ENNReal.ofReal α) * M)
    * (1 + ENNReal.ofReal α * M)))

/-- The full counter-to-fresh child bound. -/
noncomputable def crossMixB (α δ L K : ℝ) (Tν M E : ℝ≥0∞)
    (nR : ℕ) : ℝ≥0∞ :=
  crossCellB α δ L K M E + crossOneB α Tν M nR

/-- The fresh-target child row with every component and one-sided output
discharged by the finite two-law ledger. -/
theorem crossXi_XiBar_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (SR : Finset ℕ) (hRsupp : ∀ n : ℕ, (νR n : ℝ≥0∞) ≠ 0 ↔ n ∈ SR)
    (hRbd : ∀ n ∈ SR, n ≤ N)
    (hT : (∑' i, if (νR i : ℝ≥0∞) = 0 then 0
      else (νR i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hN : 2 ≤ N) {k h : ℕ} (hk : k ≤ N) :
    PhiDres α (Xi μ νL v0 k h) (XiBar μ νR v0 h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ crossMixB α δ L K Tν (twoLawPsi α Rv μ νL νR v0 N h)
          (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SR.card := by
  let M := twoLawPsi α Rv μ νL νR v0 N h
  let E := ⨆ i, twoLawE α Rv μ νL νR v0 N h i
  let CB := crossCellB α δ L K M E
  have havg : (∑' j, νR j * PhiDres α (Xi μ νL v0 k h)
      (Xi μ νR v0 j h) (SquareRel (fullSim (labRel Rv) h))) ≤ CB := by
    calc
      (∑' j, νR j * PhiDres α (Xi μ νL v0 k h)
          (Xi μ νR v0 j h) (SquareRel (fullSim (labRel Rv) h)))
        ≤ ∑' j, νR j * CB := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          by_cases hj0 : (νR j : ℝ≥0∞) = 0
          · rw [hj0, zero_mul, zero_mul]
          · exact mul_le_mul_right
              (crossSquare_le_cellCB α Rv μ νL νR v0 hα hδ hL0 hL hK0 hK
                hsymm hN hk (hRbd j ((hRsupp j).mp hj0))) _
      _ = CB := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  refine le_trans
    (PhiDres_rho_XiBar_le α Rv μ νR v0 h (Xi μ νL v0 k h) hα)
    (add_le_add havg ?_)
  simpa [crossMixB, crossOneB, CB, M, E] using
    (crossOneSided_le_ledger α Rv μ νL νR v0 hα SR hRsupp hRbd hT hN hk)

/-- Forced source, fresh target: fully assembled forward ordinary row. -/
theorem biCrossPhi_ZF_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (SR : Finset ℕ) (hRsupp : ∀ n : ℕ, (νR n : ℝ≥0∞) ≠ 0 ↔ n ∈ SR)
    (hRbd : ∀ n ∈ SR, n ≤ N)
    (hT : (∑' i, if (νR i : ℝ≥0∞) = 0 then 0
      else (νR i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hN : 2 ≤ N) {k h : ℕ} (hk : k ≤ N) :
    biCrossPhi α Rv μ νL νR v0 true (h + 1) (Tgt.Z k, Tgt.F)
      ≤ phiE α (q μ Rv v0)
        + crossMixB α δ L K Tν (twoLawPsi α Rv μ νL νR v0 N h)
            (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SR.card
        + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v0) *
          crossMixB α δ L K Tν (twoLawPsi α Rv μ νL νR v0 N h)
            (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SR.card) := by
  change PhiDres α (Zlaw μ νL v0 k (h + 1)) (Tlaw μ νR v0 (h + 1))
    (fullSim (labRel Rv) (h + 1)) ≤ _
  refine le_trans
    (PhiDres_Zlaw_Tlaw_cross_succ α Rv μ νL νR v0 hα k h) ?_
  have hm := crossXi_XiBar_le α Rv μ νL νR v0 hα hδ hL0 hL hK0 hK
    hsymm SR hRsupp hRbd hT hN (k := k) (h := h) hk
  exact add_le_add (add_le_add le_rfl hm)
    (mul_le_mul_right (mul_le_mul_right hm _) _)

/-- Fresh source, forced target: fully assembled forward ordinary row. -/
theorem biCrossPhi_FZ_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (SL : Finset ℕ) (hLsupp : ∀ n : ℕ, (νL n : ℝ≥0∞) ≠ 0 ↔ n ∈ SL)
    (hLbd : ∀ n ∈ SL, n ≤ N) (hN : 2 ≤ N) {j h : ℕ} (hj : j ≤ N) :
    biCrossPhi α Rv μ νL νR v0 true (h + 1) (Tgt.F, Tgt.Z j)
      ≤ crossCellB α δ L K (twoLawPsi α Rv μ νL νR v0 N h)
          (⨆ i, twoLawE α Rv μ νL νR v0 N h i) := by
  change PhiDres α (Tlaw μ νL v0 (h + 1)) (Zlaw μ νR v0 j (h + 1))
    (fullSim (labRel Rv) (h + 1)) ≤ _
  refine le_trans (PhiDres_Tlaw_Zlaw_cross_succ α Rv μ νL νR v0 j h) ?_
  let CB := crossCellB α δ L K (twoLawPsi α Rv μ νL νR v0 N h)
    (⨆ i, twoLawE α Rv μ νL νR v0 N h i)
  calc
    (∑' k, νL k * PhiDres α (Xi μ νL v0 k h) (Xi μ νR v0 j h)
        (SquareRel (fullSim (labRel Rv) h)))
      ≤ ∑' k, νL k * CB := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk0 : (νL k : ℝ≥0∞) = 0
        · rw [hk0, zero_mul, zero_mul]
        · exact mul_le_mul_right
            (crossSquare_le_cellCB α Rv μ νL νR v0 hα hδ hL0 hL hK0 hK
              hsymm hN (hLbd k ((hLsupp k).mp hk0)) hj) _
    _ = CB := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Fresh/fresh: fully assembled forward ordinary row. -/
theorem biCrossPhi_FF_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (SL SR : Finset ℕ)
    (hLsupp : ∀ n : ℕ, (νL n : ℝ≥0∞) ≠ 0 ↔ n ∈ SL)
    (hRsupp : ∀ n : ℕ, (νR n : ℝ≥0∞) ≠ 0 ↔ n ∈ SR)
    (hLbd : ∀ n ∈ SL, n ≤ N) (hRbd : ∀ n ∈ SR, n ≤ N)
    (hT : (∑' i, if (νR i : ℝ≥0∞) = 0 then 0
      else (νR i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hN : 2 ≤ N) {h : ℕ} :
    biCrossPhi α Rv μ νL νR v0 true (h + 1) (Tgt.F, Tgt.F)
      ≤ etaG α Rv μ
        + crossMixB α δ L K Tν (twoLawPsi α Rv μ νL νR v0 N h)
            (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SR.card
        + ENNReal.ofReal (2 * α) * (etaG α Rv μ *
          crossMixB α δ L K Tν (twoLawPsi α Rv μ νL νR v0 N h)
            (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SR.card) := by
  change PhiDres α (Tlaw μ νL v0 (h + 1)) (Tlaw μ νR v0 (h + 1))
    (fullSim (labRel Rv) (h + 1)) ≤ _
  refine le_trans (PhiDres_Tlaw_Tlaw_cross_succ α Rv μ νL νR v0 hα h) ?_
  let B := crossMixB α δ L K Tν (twoLawPsi α Rv μ νL νR v0 N h)
    (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SR.card
  have havg : (∑' k, νL k * PhiDres α (Xi μ νL v0 k h)
      (XiBar μ νR v0 h) (SquareRel (fullSim (labRel Rv) h))) ≤ B := by
    calc
      _ ≤ ∑' k, νL k * B := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk0 : (νL k : ℝ≥0∞) = 0
        · rw [hk0, zero_mul, zero_mul]
        · exact mul_le_mul_right
            (crossXi_XiBar_le α Rv μ νL νR v0 hα hδ hL0 hL hK0 hK
              hsymm SR hRsupp hRbd hT hN (k := k) (h := h)
                (hLbd k ((hLsupp k).mp hk0))) _
      _ = B := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  exact add_le_add (add_le_add le_rfl havg)
    (mul_le_mul_right (mul_le_mul_right havg _) _)

/-! ### Bidirectional restricted-potential row assembly -/

noncomputable def twoLawTheta : ℝ≥0∞ :=
  etaG α Rv μ + phiE α (q μ Rv v0)

noncomputable def twoLawMixSum (δ L K : ℝ) (TL TR M E : ℝ≥0∞)
    (nL nR : ℕ) : ℝ≥0∞ :=
  crossMixB α δ L K TR M E nR + crossMixB α δ L K TL M E nL

/-- A symmetric common upper bound for every directed potential row. -/
noncomputable def twoLawPhiB (δ L K : ℝ) (TL TR M E : ℝ≥0∞)
    (nL nR : ℕ) : ℝ≥0∞ :=
  twoLawTheta α Rv μ v0 + twoLawMixSum α δ L K TL TR M E nL nR
    + ENNReal.ofReal (2 * α) *
      (twoLawTheta α Rv μ v0 * twoLawMixSum α δ L K TL TR M E nL nR)

lemma row_potential_le_twoLawPhiB {δ L K : ℝ} {TL TR M E x B : ℝ≥0∞}
    {nL nR : ℕ}
    (hx : x ≤ twoLawTheta α Rv μ v0)
    (hB : B ≤ twoLawMixSum α δ L K TL TR M E nL nR) :
    x + B + ENNReal.ofReal (2 * α) * (x * B)
      ≤ twoLawPhiB α Rv μ v0 δ L K TL TR M E nL nR := by
  exact add_le_add (add_le_add hx hB)
    (mul_le_mul_right (mul_le_mul' hx hB) _)

private lemma crossCellB_le_mixSum_right {δ L K : ℝ} {TL TR M E : ℝ≥0∞}
    {nL nR : ℕ} :
    crossCellB α δ L K M E
      ≤ twoLawMixSum α δ L K TL TR M E nL nR := by
  calc
    crossCellB α δ L K M E
        ≤ crossMixB α δ L K TR M E nR := le_add_right le_rfl
    _ ≤ twoLawMixSum α δ L K TL TR M E nL nR := le_add_right le_rfl

private lemma crossCellB_le_mixSum_left {δ L K : ℝ} {TL TR M E : ℝ≥0∞}
    {nL nR : ℕ} :
    crossCellB α δ L K M E
      ≤ twoLawMixSum α δ L K TL TR M E nL nR := by
  calc
    crossCellB α δ L K M E
        ≤ crossMixB α δ L K TL M E nL := le_add_right le_rfl
    _ ≤ twoLawMixSum α δ L K TL TR M E nL nR := le_add_left le_rfl

private lemma mix_right_le_mixSum {δ L K : ℝ} {TL TR M E : ℝ≥0∞}
    {nL nR : ℕ} :
    crossMixB α δ L K TR M E nR
      ≤ twoLawMixSum α δ L K TL TR M E nL nR := le_add_right le_rfl

private lemma mix_left_le_mixSum {δ L K : ℝ} {TL TR M E : ℝ≥0∞}
    {nL nR : ℕ} :
    crossMixB α δ L K TL M E nL
      ≤ twoLawMixSum α δ L K TL TR M E nL nR := le_add_left le_rfl

/-- Every forward-orientation potential coordinate has the common symmetric
row bound. -/
theorem biCrossPhi_forward_step_le {δ L K : ℝ}
    (hα : 1 ≤ α) (hδ : 0 < δ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : Rv v0 v0) (hsymm : ∀ a b, Rv a b → Rv b a)
    (SL SR : Finset ℕ)
    (hLsupp : ∀ n : ℕ, (νL n : ℝ≥0∞) ≠ 0 ↔ n ∈ SL)
    (hRsupp : ∀ n : ℕ, (νR n : ℝ≥0∞) ≠ 0 ↔ n ∈ SR)
    (hLbd : ∀ n ∈ SL, n ≤ N) (hRbd : ∀ n ∈ SR, n ≤ N)
    (hTL : (∑' i, if (νL i : ℝ≥0∞) = 0 then 0
      else (νL i : ℝ≥0∞) ^ (-α)) ≤ TL)
    (hTR : (∑' i, if (νR i : ℝ≥0∞) = 0 then 0
      else (νR i : ℝ≥0∞) ^ (-α)) ≤ TR)
    (hN : 2 ≤ N) {h : ℕ} {p : Tgt × Tgt} (hp : p ∈ crossOrdIndex N) :
    biCrossPhi α Rv μ νL νR v0 true (h + 1) p
      ≤ twoLawPhiB α Rv μ v0 δ L K TL TR
        (twoLawPsi α Rv μ νL νR v0 N h)
        (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SL.card SR.card := by
  have _hTL := hTL
  let M := twoLawPsi α Rv μ νL νR v0 N h
  let E := ⨆ i, twoLawE α Rv μ νL νR v0 N h i
  have hp' := Finset.mem_product.mp hp
  have h1N := (Finset.mem_filter.mp hp'.1).1
  have h2N := (Finset.mem_filter.mp hp'.2).1
  have h1zf := (Finset.mem_filter.mp hp'.1).2
  have h2zf := (Finset.mem_filter.mp hp'.2).2
  rcases p with ⟨s, t⟩
  cases s with
  | Fk k => exact h1zf.elim
  | Z k =>
      have hk : k ≤ N := Z_mem_tgtUniv.mp h1N
      cases t with
      | Fk j => exact h2zf.elim
      | Z j =>
          have hj : j ≤ N := Z_mem_tgtUniv.mp h2N
          refine le_trans (biCrossPhi_ZZ_le_cellCB α Rv μ νL νR v0 hα hδ hL0
            hL hK0 hK hrefl hsymm hN hk hj) ?_
          refine le_trans (crossCellB_le_mixSum_right α
            (TL := TL) (TR := TR) (M := M) (E := E)
            (nL := SL.card) (nR := SR.card)) ?_
          exact le_trans (le_add_left le_rfl) (le_add_right le_rfl)
      | F =>
          refine le_trans (biCrossPhi_ZF_le α Rv μ νL νR v0 hα hδ hL0 hL hK0
            hK hsymm SR hRsupp hRbd hTR hN hk) ?_
          exact row_potential_le_twoLawPhiB α Rv μ v0
            (le_add_left le_rfl) (mix_right_le_mixSum α)
  | F =>
      cases t with
      | Fk j => exact h2zf.elim
      | Z j =>
          have hj : j ≤ N := Z_mem_tgtUniv.mp h2N
          refine le_trans (biCrossPhi_FZ_le α Rv μ νL νR v0 hα hδ hL0 hL hK0
            hK hsymm SL hLsupp hLbd hN hj) ?_
          refine le_trans (crossCellB_le_mixSum_right α
            (TL := TL) (TR := TR) (M := M) (E := E)
            (nL := SL.card) (nR := SR.card)) ?_
          exact le_trans (le_add_left le_rfl) (le_add_right le_rfl)
      | F =>
          refine le_trans (biCrossPhi_FF_le α Rv μ νL νR v0 hα hδ hL0 hL hK0
            hK hsymm SL SR hLsupp hRsupp hLbd hRbd hTR hN) ?_
          exact row_potential_le_twoLawPhiB α Rv μ v0
            (le_add_right le_rfl) (mix_right_le_mixSum α)

lemma twoLawPhiB_swap (δ L K : ℝ) (TL TR M E : ℝ≥0∞) (nL nR : ℕ) :
    twoLawPhiB α Rv μ v0 δ L K TR TL M E nR nL =
      twoLawPhiB α Rv μ v0 δ L K TL TR M E nL nR := by
  simp only [twoLawPhiB, twoLawMixSum]
  rw [add_comm (crossMixB α δ L K TL M E nL)]

/-- The potential row in either orientation. -/
theorem biCrossPhi_step_le {δ L K : ℝ}
    (hα : 1 ≤ α) (hδ : 0 < δ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : Rv v0 v0) (hsymm : ∀ a b, Rv a b → Rv b a)
    (SL SR : Finset ℕ)
    (hLsupp : ∀ n : ℕ, (νL n : ℝ≥0∞) ≠ 0 ↔ n ∈ SL)
    (hRsupp : ∀ n : ℕ, (νR n : ℝ≥0∞) ≠ 0 ↔ n ∈ SR)
    (hLbd : ∀ n ∈ SL, n ≤ N) (hRbd : ∀ n ∈ SR, n ≤ N)
    (hTL : (∑' i, if (νL i : ℝ≥0∞) = 0 then 0
      else (νL i : ℝ≥0∞) ^ (-α)) ≤ TL)
    (hTR : (∑' i, if (νR i : ℝ≥0∞) = 0 then 0
      else (νR i : ℝ≥0∞) ^ (-α)) ≤ TR)
    (hN : 2 ≤ N) {lr : Bool} {h : ℕ} {p : Tgt × Tgt}
    (hp : p ∈ crossOrdIndex N) :
    biCrossPhi α Rv μ νL νR v0 lr (h + 1) p
      ≤ twoLawPhiB α Rv μ v0 δ L K TL TR
        (twoLawPsi α Rv μ νL νR v0 N h)
        (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SL.card SR.card := by
  cases lr
  · change biCrossPhi α Rv μ νR νL v0 true (h + 1) p ≤ _
    have hs := biCrossPhi_forward_step_le α Rv μ νR νL v0 hα hδ hL0 hL
      hK0 hK hrefl hsymm SR SL hRsupp hLsupp hRbd hLbd hTR hTL hN
        (h := h) hp
    rw [twoLawPsi_swap α Rv μ νL νR v0 N h,
      twoLawE_sup_swap α Rv μ νL νR v0 N h] at hs
    rw [← twoLawPhiB_swap α Rv μ v0 δ L K TL TR
      (twoLawPsi α Rv μ νL νR v0 N h)
      (⨆ i, twoLawE α Rv μ νL νR v0 N h i) SL.card SR.card]
    exact hs
  · exact biCrossPhi_forward_step_le α Rv μ νL νR v0 hα hδ hL0 hL hK0
      hK hrefl hsymm SL SR hLsupp hRsupp hLbd hRbd hTL hTR hN hp

/-!
The potential row above is retained.  Do **not** combine it with the raw
failure product bound by adding a `2 * M` term to the same scalar invariant:
that discarded construction has no finite positive fixed budget.  The formal
no-go lemma is `unweighted_twoLaw_closure_forces_zero` in
`Obstructions/Semigroup.lean`.  A future two-law proof must propagate
structural zero mass in a separate weighted exceptional-debt coordinate.
-/

lemma crossCellB_mono {δ L K : ℝ} {M M' E E' : ℝ≥0∞}
    (hM : M ≤ M') (hE : E ≤ E') :
    crossCellB α δ L K M E ≤ crossCellB α δ L K M' E' := by
  exact cellCB_mono α δ L K hM hM
    (add_le_add (mul_le_mul_right hM _) hE)

lemma crossOneB_mono {T M M' : ℝ≥0∞} {n : ℕ} (hM : M ≤ M') :
    crossOneB α T M n ≤ crossOneB α T M' n := by
  unfold crossOneB
  gcongr

lemma crossMixB_mono {δ L K : ℝ} {T M M' E E' : ℝ≥0∞} {n : ℕ}
    (hM : M ≤ M') (hE : E ≤ E') :
    crossMixB α δ L K T M E n ≤ crossMixB α δ L K T M' E' n := by
  exact add_le_add (crossCellB_mono α hM hE) (crossOneB_mono α hM)

end GraphMarkovMatching
