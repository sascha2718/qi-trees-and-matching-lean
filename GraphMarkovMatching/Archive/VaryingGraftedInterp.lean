/-
Semantic interpretation of the finite grafted target grammar.

Every symbol in `VaryingGraftedGrammar` is interpreted by a literal law of
`graftK`.  The theorem `graftChildren_forced_eq_prod` checks all six frozen
and marker cases against the actual kernel; it is the bridge which prevents
the formal screen grammar from drifting away from the tagged process.
-/
import GraphMarkovMatching.Archive.VaryingGraftedGrammar
import GraphMarkovMatching.Archive.VaryingGraftedRows
import GraphMarkovMatching.Tail.QuenchedRows
import GraphMarkovMatching.Archive.VaryingCrossInterp

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (νL νR : PMF ℕ) (v0 : V)

def graftTgtCounter : GraftTgt → Option GraftCounter
  | .F => none
  | .Z2 => some (.ordinary 2)
  | .Z3 => some (.ordinary 3)
  | .Z4 => some (.ordinary 4)
  | .Z5 => some (.ordinary 5)
  | .M3 => some .force3Five
  | .M5 => some .force5Five

/-- Literal interpretation on one side of the tagged process. -/
noncomputable def graftInterp (left : Bool) (ν : PMF ℕ) (h : ℕ) :
    GraftTgt → PMF (FullLab (GraftState V) h)
  | .F => graftTlaw left μ ν v0 h
  | t => match graftTgtCounter t with
    | none => graftTlaw left μ ν v0 h
    | some c => graftZlaw left μ ν v0 c h

/-- Literal child-pair law of a grammar target. -/
noncomputable def graftChildren (left : Bool) (ν : PMF ℕ) (h : ℕ) :
    GraftTgt → PMF (FullLab (GraftState V) h × FullLab (GraftState V) h)
  | .F => graftXiBar left μ ν v0 h
  | t => match graftTgtCounter t with
    | none => graftXiBar left μ ν v0 h
    | some c => graftXi left μ ν v0 c h

@[simp] lemma graftInterp_F (left : Bool) (ν : PMF ℕ) (h : ℕ) :
    graftInterp μ v0 left ν h .F = graftTlaw left μ ν v0 h := rfl

@[simp] lemma graftChildren_F (left : Bool) (ν : PMF ℕ) (h : ℕ) :
    graftChildren μ v0 left ν h .F = graftXiBar left μ ν v0 h := rfl

/-- Every frozen interpretation has the exact root/children decomposition
of the literal tagged kernel. -/
lemma graftInterp_forced_succ (left : Bool) (ν : PMF ℕ) (h : ℕ)
    {t : GraftTgt} {c : GraftCounter} (ht : graftTgtCounter t = some c) :
    graftInterp μ v0 left ν (h + 1) t =
      (graftChildren μ v0 left ν h t).map (branch (v0, c)) := by
  cases t <;> simp_all [graftTgtCounter, graftInterp, graftChildren,
    graftZlaw_succ]

/-- The exact product identity for every deterministic recursive target. -/
theorem graftChildren_forced_eq_prod (left : Bool) (ν : PMF ℕ) (h : ℕ)
    {t a b : GraftTgt} (ht : graftForcedPair t = some (a, b)) :
    graftChildren μ v0 left ν h t =
      prodPMF (graftInterp μ v0 left ν h a)
        (graftInterp μ v0 left ν h b) := by
  cases t with
  | F => simp [graftForcedPair] at ht
  | Z2 =>
      simp only [graftForcedPair, Option.some.injEq, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩
      simpa [graftChildren, graftTgtCounter, graftInterp] using
        (graftXi_ordinary_of_le_two left μ ν v0 (show 2 ≤ 2 by omega) h)
  | Z3 =>
      simp only [graftForcedPair, Option.some.injEq, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩
      simpa [graftChildren, graftTgtCounter, graftInterp] using
        (graftXi_ordinary_three left μ ν v0 h)
  | Z4 =>
      simp only [graftForcedPair, Option.some.injEq, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩
      simpa [graftChildren, graftTgtCounter, graftInterp] using
        (graftXi_ordinary_four left μ ν v0 h)
  | Z5 =>
      simp only [graftForcedPair, Option.some.injEq, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩
      simpa [graftChildren, graftTgtCounter, graftInterp] using
        (graftXi_ordinary_five left μ ν v0 h)
  | M3 =>
      simp only [graftForcedPair, Option.some.injEq, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩
      simpa [graftChildren, graftTgtCounter, graftInterp] using
        (graftXi_force3Five left μ ν v0 h)
  | M5 =>
      simp only [graftForcedPair, Option.some.injEq, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩
      simpa [graftChildren, graftTgtCounter, graftInterp] using
        (graftXi_force5Five left μ ν v0 h)

/-- The common fresh components are exactly the four displayed product
targets. -/
def graftCommonPair : Fin 4 → GraftTgt × GraftTgt
  | ⟨0, _⟩ => (.Z2, .F)
  | ⟨1, _⟩ => (.Z2, .Z3)
  | ⟨2, _⟩ => (.Z3, .Z4)
  | ⟨3, _⟩ => (.Z4, .Z5)

def graftCommonArity : Fin 4 → ℕ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 7
  | ⟨3, _⟩ => 9

/- The preceding proof used side-specific names for arities 7 and 9.  The
kernel is in fact balanced at both arities on either side; expose that fact
once for later semantic rows. -/
lemma graftK_ordinary_seven (left : Bool) (ν : PMF ℕ) (v : V) :
    graftK left μ ν v0 (v, .ordinary 7) =
      PMF.pure ((v0, .ordinary 3), (v0, .ordinary 4)) := by
  cases left
  · exact graftK_right_seven μ ν v0 v
  · norm_num [graftK]

lemma graftK_ordinary_nine (left : Bool) (ν : PMF ℕ) (v : V) :
    graftK left μ ν v0 (v, .ordinary 9) =
      PMF.pure ((v0, .ordinary 4), (v0, .ordinary 5)) := by
  cases left
  · norm_num [graftK]
  · exact graftK_left_nine μ ν v0 v

lemma graftXi_ordinary_seven (left : Bool) (ν : PMF ℕ) (h : ℕ) :
    graftXi left μ ν v0 (.ordinary 7) h =
      prodPMF (graftInterp μ v0 left ν h .Z3)
        (graftInterp μ v0 left ν h .Z4) := by
  exact pairMix_pure_pattern _ _ _ _ _
    (graftK_ordinary_seven μ v0 left ν v0)

lemma graftXi_ordinary_nine (left : Bool) (ν : PMF ℕ) (h : ℕ) :
    graftXi left μ ν v0 (.ordinary 9) h =
      prodPMF (graftInterp μ v0 left ν h .Z4)
        (graftInterp μ v0 left ν h .Z5) := by
  exact pairMix_pure_pattern _ _ _ _ _
    (graftK_ordinary_nine μ v0 left ν v0)

lemma graftXi_common_eq_prod (left : Bool) (ν : PMF ℕ) (h : ℕ)
    (i : Fin 4) :
    graftXi left μ ν v0 (.ordinary (graftCommonArity i)) h =
      prodPMF
        (graftInterp μ v0 left ν h (graftCommonPair i).1)
        (graftInterp μ v0 left ν h (graftCommonPair i).2) := by
  fin_cases i
  · simpa [graftCommonArity, graftCommonPair, graftInterp, graftTgtCounter]
      using graftXi_ordinary_three left μ ν v0 h
  · simpa [graftCommonArity, graftCommonPair, graftInterp, graftTgtCounter]
      using graftXi_ordinary_five left μ ν v0 h
  · simpa [graftCommonArity, graftCommonPair] using
      graftXi_ordinary_seven μ v0 left ν h
  · simpa [graftCommonArity, graftCommonPair] using
      graftXi_ordinary_nine μ v0 left ν h

/-! ### Directed semantic coordinates -/

noncomputable def graftBiSource (lr : Bool) (h : ℕ) (t : GraftTgt) :
    PMF (FullLab (GraftState V) h) :=
  if lr then graftInterp μ v0 true νL h t
  else graftInterp μ v0 false νR h t

noncomputable def graftBiTarget (lr : Bool) (h : ℕ) (t : GraftTgt) :
    PMF (FullLab (GraftState V) h) :=
  if lr then graftInterp μ v0 false νR h t
  else graftInterp μ v0 true νL h t

noncomputable def graftBiPhi (lr : Bool) (h : ℕ)
    (p : GraftTgt × GraftTgt) : ℝ≥0∞ :=
  PhiDres α (graftBiSource μ νL νR v0 lr h p.1)
    (graftBiTarget μ νL νR v0 lr h p.2)
    (fullSim (graftLabRel Rv) h)

noncomputable def graftBiZMass (lr : Bool) (h : ℕ)
    (p : GraftTgt × GraftTgt) : ℝ≥0∞ :=
  zMass (graftBiSource μ νL νR v0 lr h p.1)
    (graftBiTarget μ νL νR v0 lr h p.2)
    (fullSim (graftLabRel Rv) h)

noncomputable def graftBiFailure (lr : Bool) (h : ℕ)
    (p : GraftTgt × GraftTgt) : ℝ≥0∞ :=
  failureD (graftBiSource μ νL νR v0 lr h p.1)
    (graftBiTarget μ νL νR v0 lr h p.2)
    (fullSim (graftLabRel Rv) h)

/-- The corrected ordinary/debt split for every literal tagged target pair. -/
lemma graftBiFailure_le_phi_add_zMass (hα0 : 0 ≤ α) (lr : Bool)
    (h : ℕ) (p : GraftTgt × GraftTgt) :
    graftBiFailure Rv μ νL νR v0 lr h p ≤
      graftBiPhi α Rv μ νL νR v0 lr h p +
        graftBiZMass Rv μ νL νR v0 lr h p := by
  exact failureD_le_PhiDres_add_zMass α hα0 _ _ _

noncomputable def graftBiNorm (lr : Bool) (h : ℕ) :
    Option GraftTgt → (FullLab (GraftState V) h → ℝ≥0∞)
  | none => fun _ => 1
  | some u => WresD α (graftBiTarget μ νL νR v0 lr h u)
      (fullSim (graftLabRel Rv) h)

noncomputable def graftBiScreen (lr : Bool) (h : ℕ)
    (sc : GraftScreen) : ℝ≥0∞ :=
  screenE (graftBiSource μ νL νR v0 lr h sc.cell)
    (fullSim (graftLabRel Rv) h)
    (sc.zlist.toList.map (graftBiTarget μ νL νR v0 lr h))
    (graftBiNorm α Rv μ νL νR v0 lr h sc.norm)

/-- A formal diagonal no longer gets called zero.  It is bounded by the
ordinary restricted potential plus its explicitly retained zero interface. -/
lemma graftBiScreen_cell_mem_none_le (hα0 : 0 ≤ α) {lr : Bool} {h : ℕ}
    {sc : GraftScreen} (hcell : sc.cell ∈ sc.zlist)
    (hnorm : sc.norm = none) :
    graftBiScreen α Rv μ νL νR v0 lr h sc ≤
      graftBiPhi α Rv μ νL νR v0 lr h (sc.cell, sc.cell) +
        graftBiZMass Rv μ νL νR v0 lr h (sc.cell, sc.cell) := by
  rw [graftBiScreen, hnorm, graftBiNorm]
  refine (screenE_le_failureD_of_mem _ _ _ _ ?_).trans
    (graftBiFailure_le_phi_add_zMass α Rv μ νL νR v0 hα0 lr h
      (sc.cell, sc.cell))
  exact List.mem_map.mpr
    ⟨sc.cell, Finset.mem_toList.mpr hcell, rfl⟩

end GraphMarkovMatching
