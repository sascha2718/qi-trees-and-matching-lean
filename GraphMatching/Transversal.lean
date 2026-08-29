/-
`thm:transversal` of `graph_matching_selfcontained.tex`: the `2 × 2` transversal.

This is the combinatorial core isolated by the paper before the proof of
`thm:contraction`. It is finite, so both statements below are decided by `decide`
after reverting the array.

Indices are `Bool` rather than `Fin 2`: in the application (proof of
`thm:contraction`) the array is `cell (i,j) good ↔ x i R Y j`, indexed by the two
`x`'s and the two `Y`'s, and `Bool` keeps the case split cheap for `decide`.
-/
import Mathlib.Tactic

namespace GraphMatching

/-- **`thm:transversal`** (`2 × 2` transversal). Mark each cell of a `2 × 2` array
good (`true`) or bad (`false`). If no row and no column is entirely bad, then
the array has a good transversal: a good main diagonal or a good
antidiagonal. -/
theorem transversal (g : Bool → Bool → Bool)
    (hrow : ∀ i, g i false = true ∨ g i true = true)
    (hcol : ∀ j, g false j = true ∨ g true j = true) :
    (g false false = true ∧ g true true = true) ∨
    (g false true = true ∧ g true false = true) := by
  revert hrow hcol
  revert g
  decide

/-- The contrapositive of `transversal`, in the form the proof of `thm:contraction`
actually uses: absence of a good transversal forces a bad row or a bad
column. This is what feeds the union bound `eq:Q-union`, `q^□ ≤ q₀² + q₁² + 2c`. -/
theorem bad_row_or_bad_col (g : Bool → Bool → Bool)
    (h : ¬((g false false = true ∧ g true true = true) ∨
           (g false true = true ∧ g true false = true))) :
    (∃ i, g i false = false ∧ g i true = false) ∨
    (∃ j, g false j = false ∧ g true j = false) := by
  revert h
  revert g
  decide

end GraphMatching
