/-
Semantic interpretation of the asymmetric two-law screen grammar.

For one offspring law, a formal diagonal screen vanishes by reflexivity.
For two different laws this is false: the same formal target is interpreted
with the left law in the source cell and with the right law in the zero list.
The correct replacement is a return to an ordinary two-law coordinate.

This file carries out that replacement.  Reading the generic diagonal-screen
estimates of `Tail/Hybrid.lean` at the cross-law interpretation, a
unit-normalized formal diagonal is bounded by directed failure and an
inverse-normalized one by the mixed `crossDres` coordinate.  Thus the acyclic
live block from `VaryingCrossGrammar` may omit formal diagonals only when
these quantities are inserted into its inhomogeneous row; no semantic zero is
asserted.
-/
import GraphMarkovMatching.Archive.VaryingCrossGrammar
import GraphMarkovMatching.Tail.Hybrid

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (νL νR : PMF ℕ) (v0 : V)

/-- Left/right interpretation of a formal target. -/
noncomputable def crossInterpT (left : Bool) (h : ℕ) (t : Tgt) :
    PMF (FullLab (V × ℕ) h) :=
  if left then interpT μ νL v0 h t else interpT μ νR v0 h t

/-- The right-law inverse normalization of a formal target. -/
noncomputable def crossInterpNorm (h : ℕ) :
    Option Tgt → (FullLab (V × ℕ) h → ℝ≥0∞)
  | none => fun _ => 1
  | some u => WresD α (interpT μ νR v0 h u) (fullSim (labRel Rv) h)

/-- Semantic value of a cross-law screen: its cell is a left-law context,
while its zero list and normalization are right-law contexts. -/
noncomputable def crossInterpScreen (h : ℕ) (sc : GScreen) : ℝ≥0∞ :=
  screenE (interpT μ νL v0 h sc.cell) (fullSim (labRel Rv) h)
    ((sc.zlist.toList).map (interpT μ νR v0 h))
    (crossInterpNorm α Rv μ νR v0 h sc.norm)

/-- A unit-normalized formal diagonal is bounded by the corresponding
ordinary directed two-law failure coordinate. -/
lemma crossInterpScreen_cell_mem_none_le {h : ℕ} {sc : GScreen}
    (hcell : sc.cell ∈ sc.zlist) (hnorm : sc.norm = none) :
    crossInterpScreen α Rv μ νL νR v0 h sc
      ≤ failureD (interpT μ νL v0 h sc.cell)
          (interpT μ νR v0 h sc.cell) (fullSim (labRel Rv) h) := by
  rw [crossInterpScreen, hnorm]
  exact screenE_le_failureD_of_mem _ _ _ _
    (List.mem_map.mpr ⟨sc.cell, Finset.mem_toList.mpr hcell, rfl⟩)

/-- An inverse-normalized formal diagonal is bounded by `crossDres`; when
the bad and normalizing targets agree this specializes to `PhiDres` through
`crossDres_self`. -/
lemma crossInterpScreen_cell_mem_some_le {h : ℕ} {sc : GScreen} {u : Tgt}
    (hcell : sc.cell ∈ sc.zlist) (hnorm : sc.norm = some u) :
    crossInterpScreen α Rv μ νL νR v0 h sc
      ≤ crossDres α (interpT μ νL v0 h sc.cell)
          (interpT μ νR v0 h sc.cell) (interpT μ νR v0 h u)
          (fullSim (labRel Rv) h) := by
  rw [crossInterpScreen, hnorm]
  exact screenE_WresD_le_crossDres_of_mem α _ _ _ _ _
    (List.mem_map.mpr ⟨sc.cell, Finset.mem_toList.mpr hcell, rfl⟩)

end GraphMarkovMatching
