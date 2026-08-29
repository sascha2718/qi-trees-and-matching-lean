/-
Finite-coordinate envelopes for assembling the literal 11/13 semantic rows.

This file does not assert the one-step recurrence.  It proves the bookkeeping
bridge needed by that recurrence: every formal potential is below one finite
ordinary supremum, every live screen is below the live-ledger supremum, and
every nonlive successor screen with a nonempty zero list is absorbed by the
ordinary supremum.  The last statement uses the already-proved fixed-law
support theorem; it is not a formal-grammar shortcut.
-/
import GraphMarkovMatching.Archive.VaryingGraftedERowCore
import GraphMarkovMatching.Archive.VaryingGraftedEstimate

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (νL νR : PMF ℕ) (v0 : V)

/-- Finite ordinary-potential envelope in both orientations. -/
noncomputable def graftPsi (h : ℕ) : ℝ≥0∞ :=
  ⨆ lr : Bool, ⨆ p : GraftTgt × GraftTgt,
    graftBiPhi α Rv μ νL νR v0 lr h p

/-- The literal value of one live screen-ledger coordinate. -/
noncomputable def graftE (h : ℕ) (i : GraftLedgerIndex) : ℝ≥0∞ :=
  graftBiScreen α Rv μ νL νR v0 i.1 h i.2.val

/-- Supremum of the finite live screen ledger. -/
noncomputable def graftESup (h : ℕ) : ℝ≥0∞ :=
  ⨆ i : GraftLedgerIndex, graftE α Rv μ νL νR v0 h i

lemma graftBiPhi_le_graftPsi (lr : Bool) (h : ℕ)
    (p : GraftTgt × GraftTgt) :
    graftBiPhi α Rv μ νL νR v0 lr h p ≤
      graftPsi α Rv μ νL νR v0 h := by
  exact le_iSup_of_le lr (le_iSup_of_le p le_rfl)

lemma graftLiveScreen_le_graftESup (lr : Bool) (h : ℕ)
    (sc : GraftScreen) (hlive : sc ∈ graftLiveScreens) :
    graftBiScreen α Rv μ νL νR v0 lr h sc ≤
      graftESup α Rv μ νL νR v0 h := by
  let i : GraftLedgerIndex := (lr, ⟨sc, hlive⟩)
  exact le_iSup_of_le i le_rfl

private lemma graftNorm_mem_screen_zero (lr : Bool) (h : ℕ)
    (sc : GraftScreen) {u : GraftTgt}
    (hnorm : sc.norm = some u) (hu : u ∈ sc.zlist) :
    graftBiScreen α Rv μ νL νR v0 lr h sc = 0 := by
  rw [graftBiScreen, hnorm, graftBiNorm]
  apply screenE_tilt_mem
  exact List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩

/-- A formal screen which is excluded from the live finite block is absorbed
by the ordinary potential envelope, provided its zero list is nonempty.

There are only two exclusion mechanisms.  If the normalization target lies
in the zero list, the restricted inverse tilt vanishes exactly.  Otherwise
the source cell lies in the zero list; the unit part is paid by the proved
fixed-law diagonal support theorem, and `screenE_WresD_le` pays the remaining
normalization by one additional ordinary potential. -/
theorem graftNonliveScreen_le_graftPsi (hα : 1 ≤ α)
    {ζ : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (sc : GraftScreen)
    (hz : sc.zlist.Nonempty) (hnlive : sc ∉ graftLiveScreens) :
    graftBiScreen α Rv μ νL νR v0 lr h sc ≤
      graftPsi α Rv μ νL νR v0 h +
        ENNReal.ofReal α * graftPsi α Rv μ νL νR v0 h := by
  have hbad : sc.cell ∈ sc.zlist ∨
      ∃ u, sc.norm = some u ∧ u ∈ sc.zlist := by
    by_contra h
    push Not at h
    apply hnlive
    rw [graftLiveScreens, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hz, ?_, ?_⟩
    · exact h.1
    · intro u hu
      exact h.2 u hu
  rcases hbad with hcell | ⟨u, hnorm, hu⟩
  · cases hnorm0 : sc.norm with
    | none =>
        have hdiag := graftBiScreen_cell_mem_none_le_phi_of_law
          (Rv := Rv) (μ := μ) (νL := νL) (νR := νR) (v0 := v0)
          α (le_trans zero_le_one hα) hrefl hLaw hp11 hp13
          (lr := lr) (h := h) (sc := sc) hcell hnorm0
        exact hdiag.trans (le_trans
          (graftBiPhi_le_graftPsi α Rv μ νL νR v0 lr h
            (sc.cell, sc.cell)) le_self_add)
    | some u =>
        by_cases hu : u ∈ sc.zlist
        · rw [graftNorm_mem_screen_zero α Rv μ νL νR v0 lr h sc hnorm0 hu]
          exact zero_le
        · let sc0 : GraftScreen := ⟨sc.cell, sc.zlist, none⟩
          have hunit : graftBiScreen α Rv μ νL νR v0 lr h sc0 ≤
              graftBiPhi α Rv μ νL νR v0 lr h (sc.cell, sc.cell) := by
            apply graftBiScreen_cell_mem_none_le_phi_of_law
              (Rv := Rv) (μ := μ) (νL := νL) (νR := νR) (v0 := v0)
              α (le_trans zero_le_one hα) hrefl hLaw hp11 hp13
              (sc := sc0)
            · simpa [sc0] using hcell
            · rfl
          have htilt := screenE_WresD_le hα
            (graftBiSource μ νL νR v0 lr h sc.cell)
            (graftBiTarget μ νL νR v0 lr h u)
            (fullSim (graftLabRel Rv) h)
            (sc.zlist.toList.map (graftBiTarget μ νL νR v0 lr h))
          rw [graftBiScreen, hnorm0, graftBiNorm] at ⊢
          calc
            screenE (graftBiSource μ νL νR v0 lr h sc.cell)
                (fullSim (graftLabRel Rv) h)
                (sc.zlist.toList.map (graftBiTarget μ νL νR v0 lr h))
                (WresD α (graftBiTarget μ νL νR v0 lr h u)
                  (fullSim (graftLabRel Rv) h)) ≤
              screenE (graftBiSource μ νL νR v0 lr h sc.cell)
                  (fullSim (graftLabRel Rv) h)
                  (sc.zlist.toList.map (graftBiTarget μ νL νR v0 lr h))
                  (fun _ => 1) +
                ENNReal.ofReal α *
                  PhiDres α (graftBiSource μ νL νR v0 lr h sc.cell)
                    (graftBiTarget μ νL νR v0 lr h u)
                    (fullSim (graftLabRel Rv) h) := htilt
            _ ≤ graftBiPhi α Rv μ νL νR v0 lr h (sc.cell, sc.cell) +
                ENNReal.ofReal α *
                  graftBiPhi α Rv μ νL νR v0 lr h (sc.cell, u) := by
              exact add_le_add hunit (mul_le_mul_right le_rfl _)
            _ ≤ graftPsi α Rv μ νL νR v0 h +
                ENNReal.ofReal α * graftPsi α Rv μ νL νR v0 h :=
              add_le_add
                (graftBiPhi_le_graftPsi α Rv μ νL νR v0 lr h
                  (sc.cell, sc.cell))
                (mul_le_mul_right
                  (graftBiPhi_le_graftPsi α Rv μ νL νR v0 lr h
                    (sc.cell, u)) _)
  · rw [graftNorm_mem_screen_zero α Rv μ νL νR v0 lr h sc hnorm hu]
    exact zero_le

/-- Uniform classification of every successor screen with nonempty zero
list: it is either a live ledger coordinate or an ordinary-potential charge. -/
theorem graftScreen_le_live_add_ordinary (hα : 1 ≤ α)
    {ζ : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (sc : GraftScreen) (hz : sc.zlist.Nonempty) :
    graftBiScreen α Rv μ νL νR v0 lr h sc ≤
      graftESup α Rv μ νL νR v0 h +
        (graftPsi α Rv μ νL νR v0 h +
          ENNReal.ofReal α * graftPsi α Rv μ νL νR v0 h) := by
  by_cases hlive : sc ∈ graftLiveScreens
  · exact (graftLiveScreen_le_graftESup α Rv μ νL νR v0 lr h sc hlive).trans
      le_self_add
  · exact (graftNonliveScreen_le_graftPsi α Rv μ νL νR v0 hα hrefl
      hLaw hp11 hp13 lr h sc hz hlive).trans le_add_self

end GraphMarkovMatching
