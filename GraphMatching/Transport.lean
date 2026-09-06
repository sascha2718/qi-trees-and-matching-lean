/-
Isomorphism invariance of the potential `Φ`. `sec:reduction` of
`graph_matching_selfcontained.tex` identifies

    (X_{h+1}, μ_{h+1}, ≈^leaf_{h+1})  ≅  (X_h², μ_h², (≈^leaf_h)^□)

by a canonical bijection, and then applies the contraction `thm:contraction` to the
identified object. This file makes that identification rigorous: `Φ` depends
only on `(X, μ, R)` up to a measure-preserving relation isomorphism.

Given `e : X ≃ Y`, transport `(μ, R)` on `X` to `(μ', R')` on `Y` by
`μ' y = μ (e.symm y)` and `R' a b = R (e.symm a) (e.symm b)`. Then every derived
quantity (`rE`, `qE`, `q`, `Φ`) transports, and reflexivity/symmetry are
preserved. The proofs are all a single `tsum` reindexing by `Equiv.tsum_eq`.
-/
import GraphMatching.Potential

namespace GraphMatching

open scoped ENNReal Classical

variable {X Y : Type*}

/-! ### Transport of the data -/

/-- The pushforward PMF along a bijection: `(transportPMF e μ) y = μ (e.symm y)`. -/
noncomputable def transportPMF (e : X ≃ Y) (μ : PMF X) : PMF Y :=
  ⟨fun y => μ (e.symm y), by
    have h : ∑' y, μ (e.symm y) = 1 := by rw [Equiv.tsum_eq e.symm μ]; exact μ.tsum_coe
    rw [← h]; exact ENNReal.summable.hasSum⟩

@[simp] lemma transportPMF_apply (e : X ≃ Y) (μ : PMF X) (y : Y) :
    transportPMF e μ y = μ (e.symm y) := rfl

/-- The transported relation, `R' a b = R (e.symm a) (e.symm b)`. -/
def transportRel (e : X ≃ Y) (R : X → X → Prop) : Y → Y → Prop :=
  fun a b => R (e.symm a) (e.symm b)

/-! ### Transport of the degrees and the potential -/

lemma qE_transport (e : X ≃ Y) (μ : PMF X) (R : X → X → Prop) (y : Y) :
    qE (transportPMF e μ) (transportRel e R) y = qE μ R (e.symm y) := by
  rw [qE, qE, ← Equiv.tsum_eq e]
  refine tsum_congr fun x => ?_
  simp only [transportRel, transportPMF_apply, Equiv.symm_apply_apply]

lemma q_transport (e : X ≃ Y) (μ : PMF X) (R : X → X → Prop) (y : Y) :
    q (transportPMF e μ) (transportRel e R) y = q μ R (e.symm y) := by
  rw [q, q, qE_transport]

/-- **Isomorphism invariance of `Φ`**: transporting `(μ, R)` along any bijection
`e : X ≃ Y` leaves the potential unchanged. -/
theorem Phi_transport (e : X ≃ Y) (μ : PMF X) (R : X → X → Prop) :
    Phi (transportPMF e μ) (transportRel e R) = Phi μ R := by
  rw [Phi, Phi, ← Equiv.tsum_eq e]
  refine tsum_congr fun x => ?_
  rw [transportPMF_apply, Equiv.symm_apply_apply, q_transport, Equiv.symm_apply_apply]

end GraphMatching
