/-
Root and child laws of a finite common-core profile presentation.
-/
import GraphMarkovMatching.Stopped.Presentation
import GraphMarkovMatching.Stopped.Projection

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Model
open scoped ENNReal Classical

variable {V : Type}

namespace Presentation

variable (P : Presentation) (R : V → V → Prop) (zero : V) (μ : PMF V)

/-- The law of a forced type is the tree law started from the typed state `(t, 0)`. -/
lemma rho_forced_eq {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live) (n : ℕ) :
    (P.toModel R zero μ).rho ⟨(σ, some τ), h⟩ n
      = muM (P.toModel R zero μ).kernel (⟨(σ, some τ), h⟩, zero) n := by
  rw [Model.rho, Model.rootT, P.rootLaw_forced', PMF.pure_map, PMF.pure_bind]

/-- The law of a forced type, through the coercion of its raw type. -/
lemma rho_forced_eq' {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live) (n : ℕ) :
    (P.toModel R zero μ).rho (P.toLive (σ, some τ)) n
      = muM (P.toModel R zero μ).kernel (P.toLive (σ, some τ), zero) n := by
  rw [P.toLive_of_mem h]
  exact P.rho_forced_eq R zero μ h n

/-- The law of a fresh type is the `μ`-mixture of the tree laws started from the typed
states `(t, v)`. -/
lemma rho_fresh_eq (σ : Bool) (n : ℕ) :
    (P.toModel R zero μ).rho (P.freshL σ) n
      = μ.bind fun v => muM (P.toModel R zero μ).kernel (P.freshL σ, v) n := by
  rw [Model.rho, Model.rootT, PMF.bind_map, Model.rootLaw_fresh _ rfl]
  rfl

/-- The child-pair mixture of a forced type is the product of the laws of its child
types. -/
lemma childMix_forced {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live) (n : ℕ) :
    (P.toModel R zero μ).childMix ⟨(σ, some τ), h⟩ n
      = prodPMF ((P.toModel R zero μ).rho (P.toLive (rootPair σ τ).1) n)
          ((P.toModel R zero μ).rho (P.toLive (rootPair σ τ).2) n) := by
  rw [Model.childMix]
  show (P.kernelL _).bind _ = _
  rw [P.kernelL_forced, PMF.pure_bind]

/-- The child-pair mixture of a forced type, through the coercion of its raw type. -/
lemma childMix_forced' {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live) (n : ℕ) :
    (P.toModel R zero μ).childMix (P.toLive (σ, some τ)) n
      = prodPMF ((P.toModel R zero μ).rho (P.toLive (rootPair σ τ).1) n)
          ((P.toModel R zero μ).rho (P.toLive (rootPair σ τ).2) n) := by
  rw [P.toLive_of_mem h]
  exact P.childMix_forced R zero μ h n

/-- The child-pair mixture of a fresh type is the arity mixture of the products of the laws
of the child types of the profiles. -/
lemma childMix_fresh (σ : Bool) (n : ℕ) :
    (P.toModel R zero μ).childMix (P.freshL σ) n
      = (P.ν σ).bind fun k =>
          prodPMF ((P.toModel R zero μ).rho (P.toLive (rootPair σ (P.C σ k)).1) n)
            ((P.toModel R zero μ).rho (P.toLive (rootPair σ (P.C σ k)).2) n) := by
  rw [Model.childMix]
  show (P.kernelL _).bind _ = _
  rw [Presentation.kernelL, PMF.bind_map]
  show (P.rawKernel (σ, none)).bind _ = _
  rw [P.rawKernel_fresh, PMF.bind_map]
  rfl

end Presentation

end GraphMarkovMatching.Stopped
