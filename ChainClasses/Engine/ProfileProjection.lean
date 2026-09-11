import ChainClasses.Engine.ProfileLaw
import GraphMarkovMatching.Stopped.PresentationLaws

/-! Forgetting the auxiliary arity information identifies the profile encoding with the
state law of the common-profile Markov model. -/

namespace ChainClasses.Profile

open GraphMarkovMatching GraphMarkovMatching.Support GraphMarkovMatching.Stopped
open scoped ENNReal Classical

variable (P : Presentation) (C : Family) (σ : Bool) (R : ℕ → ℕ → Prop) (v0 : ℕ) (μ : PMF ℕ)

local notation "M" => P.toModel R v0 μ
local notation "Q" => rawKernel C μ (P.ν σ) v0

def ForcedClaim (h : ℕ) : Prop :=
  ∀ τ, (σ, some τ) ∈ P.live → ∀ v,
    (muM Q (v, RawType.rem τ) h).map (statesOf h) =
      (muM (M).kernel (P.toLive (σ, some τ), v) h).map (statesOf' h)

def FreshClaim (h : ℕ) : Prop :=
  ∀ v, ((P.ν σ).bind fun k => (muM Q (v, RawType.ord k) h).map (statesOf h)) =
    (muM (M).kernel (P.freshL σ, v) h).map (statesOf' h)

lemma rawLaw_map_of_fresh (h : ℕ) (hF : FreshClaim P C σ R v0 μ h) :
    (rawLaw C μ (P.ν σ) v0 h).map (statesOf h) =
      ((M).rho (P.freshL σ) h).map (statesOf' h) := by
  rw [rawLaw, freshRaw, PMF.bind_map, prodPMF_bind_eq, PMF.map_bind,
    P.rho_fresh_eq R v0 μ, PMF.map_bind]
  refine congrArg _ (funext fun v => ?_)
  rw [PMF.map_bind]
  exact hF v

lemma subtreeLaw_map (h : ℕ) (hZ : ForcedClaim P C σ R v0 μ h)
    (hF : FreshClaim P C σ R v0 μ h) (off : ℕ) (τ : MTree)
    (hτ : typeOf σ τ ∈ P.live) :
    ((childLaw μ (P.ν σ) v0 (subtreeKind off τ)).bind fun s => muM Q s h).map
        (statesOf h) = ((M).rho (P.toLive (typeOf σ τ)) h).map (statesOf' h) := by
  cases τ with
  | leaf =>
      simp only [subtreeKind, childLaw, Presentation.typeOf_leaf, P.toLive_of_mem (P.fresh_mem_live σ)]
      exact rawLaw_map_of_fresh P C σ R v0 μ h hF
  | node l r | gnode l r =>
      simp only [subtreeKind, childLaw, PMF.pure_bind, typeOf] at hτ ⊢
      rw [hZ _ hτ v0, P.rho_forced_eq' R v0 μ hτ]

lemma rawPairMix (s : RawState ℕ) (h : ℕ) :
    pairMix Q s h =
      prodPMF ((childLaw μ (P.ν σ) v0 (stepKind C 0 s).1).bind fun s => muM Q s h)
        ((childLaw μ (P.ν σ) v0 (stepKind C 0 s).2).bind fun s => muM Q s h) := by
  rw [pairMix, rawKernel]
  exact prodPMF_bind_prodPMF _ _ (fun s => muM Q s h) (fun s => muM Q s h)

lemma treePair_map (h : ℕ) (hZ : ForcedClaim P C σ R v0 μ h)
    (hF : FreshClaim P C σ R v0 μ h) (τ : MTree) (hne : τ ≠ MTree.leaf)
    (h1 : (rootPair σ τ).1 ∈ P.live) (h2 : (rootPair σ τ).2 ∈ P.live) :
    (prodPMF
      ((childLaw μ (P.ν σ) v0 (treeStep 0 τ).1).bind fun s => muM Q s h)
      ((childLaw μ (P.ν σ) v0 (treeStep 0 τ).2).bind fun s => muM Q s h)).map
        (Prod.map (statesOf h) (statesOf h)) =
      (prodPMF ((M).rho (P.toLive (rootPair σ τ).1) h)
        ((M).rho (P.toLive (rootPair σ τ).2) h)).map
          (Prod.map (statesOf' h) (statesOf' h)) := by
  cases τ with
  | leaf => exact (hne rfl).elim
  | node l r | gnode l r =>
      simp only [rootPair, treeStep] at h1 h2 ⊢
      rw [prodPMF_map_prod, prodPMF_map_prod,
        subtreeLaw_map P C σ R v0 μ h hZ hF 0 l h1,
        subtreeLaw_map P C σ R v0 μ h hZ hF _ r h2]

lemma forced_succ (h : ℕ) (hZ : ForcedClaim P C σ R v0 μ h)
    (hF : FreshClaim P C σ R v0 μ h) : ForcedClaim P C σ R v0 μ (h + 1) := by
  intro τ hτ v
  have hne : τ ≠ MTree.leaf := by
    obtain ⟨_, _, _, _, hne⟩ := (P.mem_live_some_iff σ τ).mp hτ
    exact hne
  obtain ⟨h1, h2⟩ := P.rootPair_mem_live_of_mem hτ
  have hp := treePair_map P C σ R v0 μ h hZ hF τ hne h1 h2
  rw [muM_succ, muM_succ, Model.pairMix_kernel,
    P.childMix_forced' R v0 μ hτ, rawPairMix]
  simp only [stepKind]
  rw [PMF.map_comp, PMF.map_comp]
  change (prodPMF _ _).map (fun xy => GraphMarkovMatching.branch v (statesOf h xy.1, statesOf h xy.2)) =
    (prodPMF _ _).map (fun xy => GraphMarkovMatching.branch v (statesOf' h xy.1, statesOf' h xy.2))
  have := congrArg (fun p => p.map (GraphMarkovMatching.branch v)) hp
  simpa only [PMF.map_comp, Function.comp_def, Prod.map] using this

lemma fresh_succ (hC : ∀ k, k ∈ P.supp σ → C.tree k = P.C σ k)
    (h : ℕ) (hZ : ForcedClaim P C σ R v0 μ h)
    (hF : FreshClaim P C σ R v0 μ h) : FreshClaim P C σ R v0 μ (h + 1) := by
  intro v
  rw [muM_succ, Model.pairMix_kernel, P.childMix_fresh R v0 μ,
    PMF.map_bind, PMF.map_bind]
  apply bind_congr_of_ne_zero
  intro k hk
  have hk' := (P.mem_supp σ k).mp hk
  have heq := hC k hk'
  have hne : P.C σ k ≠ MTree.leaf := by
    obtain ⟨l, r, h⟩ := P.C_gnode σ k hk'
    simp [h]
  obtain ⟨h1, h2⟩ := P.rootPair_mem_live hk' (MTree.mem_subtrees_self _)
  have hp := treePair_map P C σ R v0 μ h hZ hF (P.C σ k) hne h1 h2
  rw [muM_succ, rawPairMix]
  simp only [stepKind, heq]
  rw [PMF.map_comp, PMF.map_comp]
  change (prodPMF _ _).map (fun xy => GraphMarkovMatching.branch v (statesOf h xy.1, statesOf h xy.2)) =
    (prodPMF _ _).map (fun xy => GraphMarkovMatching.branch v (statesOf' h xy.1, statesOf' h xy.2))
  have := congrArg (fun p => p.map (GraphMarkovMatching.branch v)) hp
  simpa only [PMF.map_comp, Function.comp_def, Prod.map] using this

/-- At every finite height, the encoded state law is exactly the presentation law. -/
theorem rawLaw_states (hC : ∀ k, k ∈ P.supp σ → C.tree k = P.C σ k) (h : ℕ) :
    (rawLaw C μ (P.ν σ) v0 h).map (statesOf h) =
      ((M).rho (P.freshL σ) h).map (statesOf' h) := by
  have both : ∀ n, ForcedClaim P C σ R v0 μ n ∧ FreshClaim P C σ R v0 μ n := by
    intro n
    induction n with
    | zero =>
        constructor
        · intro τ _ v
          rw [muM_zero, muM_zero, PMF.pure_map, PMF.pure_map]
          rfl
        · intro v
          simp only [muM_zero, PMF.pure_map]
          exact PMF.bind_const (P.ν σ) (PMF.pure (leaf v))
    | succ n ih =>
        exact ⟨forced_succ P C σ R v0 μ n ih.1 ih.2,
          fresh_succ P C σ R v0 μ hC n ih.1 ih.2⟩
  exact rawLaw_map_of_fresh P C σ R v0 μ h (both h).2

end ChainClasses.Profile
