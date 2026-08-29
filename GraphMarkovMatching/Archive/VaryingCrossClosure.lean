/-
Closure of the finite asymmetric screen block.

The non-power-of-two right exception makes the live cross-screen matrix
nilpotent.  Formal diagonals are not semantic zeros for two different laws;
`VaryingCrossInterp` bounds them by ordinary/mixed inhomogeneous coordinates.
Once those diverted terms are included in the row function `g`, the usual
finite screened invariant closes with no killed-kernel or small exceptional-
mass hypothesis.
-/
import GraphMarkovMatching.Archive.VaryingCrossInterp
import GraphMarkovMatching.Closure.Geometric

namespace GraphMarkovMatching

open scoped ENNReal Classical

/-- Crude uniform row bound for the finite cross-screen support matrix. -/
lemma crossN_row_sum_le (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞)
    (i : {sc // sc ∈ crossLiveScreens N}) :
    ∑ j, crossN N SL SR CW i j ≤ CW * (crossLiveScreens N).card := by
  calc
    ∑ j, crossN N SL SR CW i j
        ≤ ∑ _j : {sc // sc ∈ crossLiveScreens N}, CW := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hj : j.val ∈ crossScreenSucc SL SR i.val
          · exact le_of_eq (by rw [crossN, if_pos hj])
          · rw [crossN, if_neg hj]
            exact zero_le
    _ = Fintype.card {sc // sc ∈ crossLiveScreens N} * CW := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = CW * (crossLiveScreens N).card := by
          rw [Fintype.card_coe, mul_comm]

/-- **Finite two-law screen closure.**  Suppose the ordinary error `Ψ` and
the live cross-screen vector `E` obey monotone rows after every formal
diagonal has been diverted using `crossInterpScreen_cell_mem_none_le` or
`crossInterpScreen_cell_mem_some_le`.  A non-power-of-two atom in the right
support then supplies nilpotence internally and the invariant closes.

This theorem is the exact cross-law analogue of `screened_uniform_bound_mono`:
there is no remaining matrix or renewal-kernel hypothesis. -/
theorem cross_screened_uniform_bound
    {N : ℕ} {SL SR : Finset ℕ} {b : ℕ}
    (hb : b ∈ SR) (hb2 : 2 ≤ b) (hbpow : ¬ IsPowerOfTwo b)
    (CW Kc η u Ξ : ℝ≥0∞)
    (Ψ : ℕ → ℝ≥0∞)
    (E : ℕ → {sc // sc ∈ crossLiveScreens N} → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' c c', a ≤ a' → c ≤ c' → f a c ≤ f a' c')
    (hg : ∀ a a' c c', a ≤ a' → c ≤ c' → g a c ≤ g a' c')
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (⨆ j, E h j)
        + mulVec (crossN N SL SR CW) (E h) i)
    (hΞ : (∑ j ∈ Finset.range
        (Fintype.card {sc // sc ∈ crossLiveScreens N} + 1),
        (CW * (crossLiveScreens N).card) ^ j) * u ≤ Ξ)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η := by
  let r := Fintype.card {sc // sc ∈ crossLiveScreens N} + 1
  refine screened_uniform_bound_mono (ι := {sc // sc ∈ crossLiveScreens N})
    (N := crossN N SL SR CW) (r := r) (by simp [r])
    Ψ E f g hf hg Kc η u Ξ ?_ ?_ hΨ0 hE0 hΨstep hEstep hu hclose
  · exact crossN_nilpotent_of_nonpower_right hb hb2 hbpow CW
      (fun _ => u)
  · intro i
    exact le_trans
      (nilSum_le_geom (crossN_row_sum_le N SL SR CW) r u i)
      (by simpa [r] using hΞ)

end GraphMarkovMatching
