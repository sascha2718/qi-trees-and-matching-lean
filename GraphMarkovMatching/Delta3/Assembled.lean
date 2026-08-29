/-
The assembled `ν = δ₃` uniform failure bound
(`arbitrary_offspring_matching.tex`, `thm:main-matching` at pure ternary law,
recursion closed): the closure keystone `delta3_failure_uniform`
instantiated at the concrete monotone step functions `delta3F` and
`delta3G`, with the two assembled step bounds and the joint
monotonicity discharged.  What remains open are the ledger constants
(`hδ`, `hL`, `hK`), the closure inequalities at the bounds
(`hu`, `hclose`), and the root budgets — exactly the inputs of the
numeric corollary.
-/
import GraphMarkovMatching.Delta3.PsiStep
import GraphMarkovMatching.Delta3.EStep

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- **The assembled `δ₃` uniform failure bound**: with the concrete
step functions `delta3F`/`delta3G` in place, the matching failure is at
most `Kc·η` at every height from the ledger constants, the two closure
inequalities, and the root budgets alone. -/
theorem delta3_failure_uniform_assembled {δ L K : ℝ} (hα : 1 ≤ α)
    (hδ : 0 < δ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0) (Kc η u Ξ : ℝ≥0∞)
    (hΞ : u * (2 + 2 * delta3Tilt α Rv μ) ≤ Ξ)
    (hKη1 : etaG α Rv μ ≤ Kc * η)
    (hKη2 : phiE α (q μ Rv v0) ≤ Kc * η)
    (hu0 : 2 * etaG α Rv μ ≤ u)
    (hu : delta3G α Rv μ v0 δ L K (Kc * η) Ξ ≤ u)
    (hclose : delta3F α Rv μ v0 δ L K (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, (∑' x, Tlaw μ (PMF.pure 3) v0 h x
        * qE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) x)
      ≤ Kc * η :=
  delta3_failure_uniform α Rv μ v0 hα hRv hsymm hhalf
    (delta3F α Rv μ v0 δ L K) (delta3G α Rv μ v0 δ L K)
    (fun _ _ _ _ ha hb => delta3F_mono α Rv μ v0 δ L K ha hb)
    (fun _ _ _ _ ha hb => delta3G_mono α Rv μ v0 δ L K ha hb)
    (fun h => delta3_Psi_step_assembled α Rv μ v0 hα hδ hL0 hL hK0 hK
      hsymm hRv h)
    (fun h i => delta3_E_step_assembled α Rv μ v0 hα hδ hL0 hL hK0 hK
      hsymm hRv hhalf h i)
    Kc η u Ξ hΞ hKη1 hKη2 hu0 hu hclose

end GraphMarkovMatching
