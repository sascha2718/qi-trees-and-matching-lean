/-
The mixture split (`arbitrary_offspring_matching.tex` `eq:split`): if the
good degree factorises exactly, `1 - q = (1-e)(1-q̃)`, then

    φ_α(q) ≤ φ_α(e) + φ_α(q̃) + 2α φ_α(e) φ_α(q̃).

This is the algebra of the product lemma with no independence input: the
factorisation comes from conditioning (mismatch first, the rest given no
mismatch). The pointwise heart `phi_prod_le` is imported unchanged from the
`Support` support layer; this file wraps it in the safe `phiE` convention, where the
endpoint cases `e = 1` or `q̃ = 1` are trivially `⊤`-absorbed.
-/
import GraphMarkovMatching.Potential.Jensen
import GraphMarkovMatching.Support.Product

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- **The mixture split in the safe convention**: for `e, q̃ ∈ [0,1]`,

    `phiE α (e + (1-e) q̃) ≤ phiE α e + phiE α q̃ + 2α · phiE α e · phiE α q̃`. -/
lemma phiE_split {α e qt : ℝ} (hα : 1 ≤ α)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hq0 : 0 ≤ qt) (hq1 : qt ≤ 1) :
    phiE α (e + (1 - e) * qt)
      ≤ phiE α e + phiE α qt
        + ENNReal.ofReal (2 * α) * (phiE α e * phiE α qt) := by
  rcases lt_or_eq_of_le he1 with he1' | he1'
  · rcases lt_or_eq_of_le hq1 with hq1' | hq1'
    · -- both strictly below 1: the real product algebra
      have hq : e + (1 - e) * qt = 1 - (1 - e) * (1 - qt) := by ring
      have hqlt : e + (1 - e) * qt < 1 := by nlinarith
      have hkey := phi_prod_le (q₁ := e) (q₂ := qt) hα he0 he1' hq0 hq1'
      rw [phiE_of_lt hqlt, phiE_of_lt he1', phiE_of_lt hq1']
      calc ENNReal.ofReal (phi α (e + (1 - e) * qt))
          = ENNReal.ofReal (phi α (1 - (1 - e) * (1 - qt))) := by rw [hq]
        _ ≤ ENNReal.ofReal (phi α e + phi α qt + 2 * α * (phi α e * phi α qt)) :=
            ENNReal.ofReal_le_ofReal hkey
        _ = ENNReal.ofReal (phi α e) + ENNReal.ofReal (phi α qt)
              + ENNReal.ofReal (2 * α) * (ENNReal.ofReal (phi α e) * ENNReal.ofReal (phi α qt)) :=
            ofReal_expand (by positivity) (phi_nonneg he0 he1') (phi_nonneg hq0 hq1')
    · -- q̃ = 1: right side contains `⊤`
      have h : phiE α qt = ⊤ := by rw [hq1']; exact phiE_one α
      rw [h]
      exact le_trans le_top (by simp)
  · -- e = 1: right side contains `⊤`
    have h : phiE α e = ⊤ := by rw [he1']; exact phiE_one α
    rw [h]
    exact le_trans le_top (by simp)

end GraphMarkovMatching
