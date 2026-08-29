/-
The interpretation of the formal screen grammar
(`arbitrary_offspring_matching.tex`, the bridge between the grammar of
`sec:rows`/`thm:nilpotence` and the ledger quantities): formal
targets denote the context laws at a height, formal screens denote
normalized screens, and the two pruning lemmas transfer: a formal
screen whose zero list contains its own cell, or its own
normalization, interprets to zero.  This is the semantic content of
liveness for the accessible screen graph: the `Anchored` acyclicity
(`Grammar/Accessible.lean`) concludes `cell ∈ zlist` along any would-be
cycle, and the interpretation of such a screen vanishes, so the
corresponding `N`-coordinate carries no mass.

* `interpT`: `Z j ↦ Zlaw j`, `F ↦ Tlaw`, `Fk k ↦ Flaw k`;
* `interpScreen`: formal screens as normalized screen values (the
  `none` normalization is the unit tilt of the zero masses);
* `screenE_tilt_mem`: tilt pruning for a member of a general zero
  list;
* `interpScreen_prune` / `interpScreen_tilt_prune`: self-pruned
  formal screens interpret to zero (`thm:pruning`,
  `thm:tilt-pruning`).
-/
import GraphMarkovMatching.Grammar.Accessible
import GraphMarkovMatching.Process.ScreenBridges
import GraphMarkovMatching.Process.Cells

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (ν : PMF ℕ) (v0 : V)

/-- The interpretation of formal targets: the context laws at a
height. -/
noncomputable def interpT (h : ℕ) : Tgt → PMF (FullLab (V × ℕ) h)
  | Tgt.Z j => Zlaw μ ν v0 j h
  | Tgt.F => Tlaw μ ν v0 h
  | Tgt.Fk k => Flaw μ ν v0 k h

/-- The interpretation of formal normalizations: the restricted
inverse degree, or the unit tilt of the zero masses. -/
noncomputable def interpNorm (h : ℕ) :
    Option Tgt → (FullLab (V × ℕ) h → ℝ≥0∞)
  | none => fun _ => 1
  | some u => WresD α (interpT μ ν v0 h u) (fullSim (labRel Rv) h)

/-- The interpretation of formal screens: normalized screen values. -/
noncomputable def interpScreen (h : ℕ) (sc : GScreen) : ℝ≥0∞ :=
  screenE (interpT μ ν v0 h sc.cell) (fullSim (labRel Rv) h)
    ((sc.zlist.toList).map (interpT μ ν v0 h))
    (interpNorm α Rv μ ν v0 h sc.norm)

/-- Tilt pruning for general zero lists: a screen whose zero list
contains its tilt law vanishes. -/
lemma screenE_tilt_mem {X : Type} (α : ℝ) (ρs : PMF X)
    (R : X → X → Prop) (zs : List (PMF X)) (ρ : PMF X) (hρ : ρ ∈ zs) :
    screenE ρs R zs (WresD α ρ R) = 0 := by
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : rE ρ R x = 0
  · rw [WresD, if_pos hx, mul_zero]
  · rw [show screenInd R zs x = 0 from by
      rw [screenInd, if_neg (fun hall => hx (hall ρ hρ))],
      mul_zero, zero_mul]

/-- **Diagonal pruning transfers**: a formal screen whose zero list
contains its own cell interprets to zero. -/
lemma interpScreen_prune {h : ℕ} {sc : GScreen} (hRv : ∀ v, Rv v v)
    (hmem : sc.cell ∈ sc.zlist) :
    interpScreen α Rv μ ν v0 h sc = 0 :=
  screenE_self_mem (interpT μ ν v0 h sc.cell) (fullSim (labRel Rv) h)
    ((sc.zlist.toList).map (interpT μ ν v0 h))
    (interpNorm α Rv μ ν v0 h sc.norm)
    (List.mem_map.mpr ⟨sc.cell, Finset.mem_toList.mpr hmem, rfl⟩)
    (fullSim_refl (labRel Rv) (fun s => hRv s.1) h)

/-- **Tilt pruning transfers**: a formal screen whose zero list
contains its normalization interprets to zero. -/
lemma interpScreen_tilt_prune {h : ℕ} {sc : GScreen} {u : Tgt}
    (hu : sc.norm = some u) (hmem : u ∈ sc.zlist) :
    interpScreen α Rv μ ν v0 h sc = 0 := by
  rw [interpScreen, hu]
  exact screenE_tilt_mem α _ _ _ _
    (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hmem, rfl⟩)

end GraphMarkovMatching
