/-
The verified structural and weight reduction for the four-point common core
`{3,5,7,9}` with exceptional counters `11` and `13`.

If the common weights have total mass `1 - ε` and `ε ≤ 1/2`, a maximal
common atom has mass at least `1/8`.  Indexing the four possible heavy
arities by `r_i = 2i+3`, with `m_i=i+1`, gives the exact shifted identity

  m_i * (13 - 1) = m_i * (11 - 1) + (r_i - 1).

Thus a block of at most four exceptional `13` offsets is balanced by the
same number of exceptional `11` offsets and one occurrence of the selected
common arity.  The exceptional factors `ε^m` stay on both sides, while the
selected common factor is uniformly at least `1/8`.  All possible selected
arities, and both exceptional arities, have two consecutive fresh-return
depths.

This module deliberately stops at that finite structural/weight reduction.
It does not assert the cross-law matching theorem: the weighted Hall
ordinary/screen rows and their scalar closure are still to be instantiated.
-/
import GraphMarkovMatching.Grammar.Depths
import GraphMarkovMatching.Potential.ZeroInterface

namespace GraphMarkovMatching

open scoped ENNReal Classical BigOperators

lemma rareCore_toFresh_five : toFresh 5 = {2, 3} := by
  rw [toFresh_of_ge (by omega)]
  norm_num
  rw [toFresh_three, toFresh_le_two (by omega)]
  decide

end GraphMarkovMatching
