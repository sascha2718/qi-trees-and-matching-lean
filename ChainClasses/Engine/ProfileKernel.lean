import GraphMarkovMatching.Stopped.Presentation
import Mathlib.Logic.Encodable.Basic

/-! Binary profiles with their sampled arities retained for the finite law calculation.
The arity is auxiliary information; the matching model forgets it at fresh vertices. -/

namespace ChainClasses.Profile

open GraphMarkovMatching GraphMarkovMatching.Support GraphMarkovMatching.Stopped
open scoped ENNReal Classical

/-- A binary profile for every arity. Values below two are unused. -/
structure Family where
  tree : ℕ → MTree
  leaves : ∀ k, 2 ≤ k → (tree k).leaves = k
  root : ∀ k, ∃ l r, tree k = MTree.node l r ∨ tree k = MTree.gnode l r

/-- Auxiliary types retain an arity at a sampled vertex and a remaining profile at an
inserted vertex. -/
inductive RawType where
  | ord (k : ℕ)
  | rem (τ : MTree)
  deriving DecidableEq

abbrev RawState (V : Type) := V × RawType

private def treeCode : MTree → ℕ
  | .leaf => 0
  | .node l r => 2 * Nat.pair (treeCode l) (treeCode r) + 1
  | .gnode l r => 2 * Nat.pair (treeCode l) (treeCode r) + 2

private lemma treeCode_injective : Function.Injective treeCode := by
  intro t
  induction t with
  | leaf => intro u h; cases u <;> simp_all [treeCode]
  | node l r hl hr =>
      intro u h
      cases u with
      | leaf => simp [treeCode] at h
      | node l' r' =>
          simp only [treeCode] at h
          have e : Nat.pair (treeCode l) (treeCode r) = Nat.pair (treeCode l') (treeCode r') := by omega
          have e' := Nat.pair_eq_pair.mp e
          exact congrArg₂ MTree.node (hl e'.1) (hr e'.2)
      | gnode l' r' => simp only [treeCode] at h; omega
  | gnode l r hl hr =>
      intro u h
      cases u with
      | leaf => simp [treeCode] at h
      | node l' r' => simp only [treeCode] at h; omega
      | gnode l' r' =>
          simp only [treeCode] at h
          have e : Nat.pair (treeCode l) (treeCode r) = Nat.pair (treeCode l') (treeCode r') := by omega
          have e' := Nat.pair_eq_pair.mp e
          exact congrArg₂ MTree.gnode (hl e'.1) (hr e'.2)

instance : Countable MTree := treeCode_injective.countable

instance : Countable RawType := by
  let f : RawType → ℕ ⊕ MTree := fun t => match t with | .ord k => .inl k | .rem τ => .inr τ
  have hf : Function.Injective f := by intro t u h; cases t <;> cases u <;> simp_all [f]
  exact hf.countable

instance : MeasurableSpace RawType := ⊤
instance : MeasurableSingletonClass RawType := ⟨fun _ => trivial⟩

noncomputable def freshRaw {V : Type} (μ : PMF V) (ν : PMF ℕ) : PMF (RawState V) :=
  (prodPMF μ ν).map fun s => (s.1, RawType.ord s.2)

@[simp] theorem freshRaw_ord_apply {V : Type} (μ : PMF V) (ν : PMF ℕ) (v : V) (k : ℕ) :
    freshRaw μ ν (v, RawType.ord k) = μ v * ν k := by
  rw [freshRaw, PMF.map_apply]
  have heq : ∀ a : V × ℕ, ((v, RawType.ord k) = (a.1, RawType.ord a.2)) ↔ a = (v, k) := by
    intro a; rcases a with ⟨w, j⟩
    simp only [Prod.mk.injEq, RawType.ord.injEq]
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  simp_rw [heq]
  rw [tsum_ite_eq]
  exact prodPMF_apply μ ν (v, k)

@[simp] theorem freshRaw_rem_apply {V : Type} (μ : PMF V) (ν : PMF ℕ) (v : V) (τ : MTree) :
    freshRaw μ ν (v, RawType.rem τ) = 0 := by
  rw [freshRaw, PMF.map_apply]
  exact ENNReal.tsum_eq_zero.mpr fun s => if_neg (by intro h; cases congrArg Prod.snd h)

inductive ChildK where
  | internal (off : ℕ) (t : RawType)
  | slot (j : ℕ)

def subtreeKind (off : ℕ) : MTree → ChildK
  | .leaf => .slot off
  | τ => .internal off (.rem τ)

def treeStep (off : ℕ) : MTree → ChildK × ChildK
  | .leaf => (.slot off, .slot (off + 1))
  | .node l r => (subtreeKind off l, subtreeKind (off + l.leaves) r)
  | .gnode l r => (subtreeKind off l, subtreeKind (off + l.leaves) r)

def stepKind (C : Family) (off : ℕ) : RawState ℕ → ChildK × ChildK
  | (_, .ord k) => treeStep off (C.tree k)
  | (_, .rem τ) => treeStep off τ

def servedC : RawType → ℕ
  | .ord k => k
  | .rem τ => τ.leaves

def validS : RawState ℕ → Prop
  | (_, .ord k) => 2 ≤ k
  | (_, .rem τ) => τ ≠ MTree.leaf

def servedK : ChildK → ℕ
  | .internal _ t => servedC t
  | .slot _ => 1

def startK : ChildK → ℕ
  | .internal off _ => off
  | .slot j => j

def validK (v0 : ℕ) : ChildK → Prop
  | .internal _ t => validS (v0, t)
  | .slot _ => True

lemma subtreeKind_spec (v0 off : ℕ) (τ : MTree) :
    startK (subtreeKind off τ) = off ∧ servedK (subtreeKind off τ) = τ.leaves ∧
      validK v0 (subtreeKind off τ) := by
  cases τ <;> simp [subtreeKind, startK, servedK, servedC, validK, validS, MTree.leaves]

lemma treeStep_spec (v0 off : ℕ) {τ : MTree} (hτ : τ ≠ MTree.leaf) :
    startK (treeStep off τ).1 = off ∧
    startK (treeStep off τ).2 = off + servedK (treeStep off τ).1 ∧
    servedK (treeStep off τ).1 + servedK (treeStep off τ).2 = τ.leaves ∧
    validK v0 (treeStep off τ).1 ∧ validK v0 (treeStep off τ).2 := by
  cases τ with
  | leaf => exact (hτ rfl).elim
  | node l r | gnode l r =>
      obtain ⟨hl1, hl2, hl3⟩ := subtreeKind_spec v0 off l
      obtain ⟨hr1, hr2, hr3⟩ := subtreeKind_spec v0 (off + l.leaves) r
      simp only [treeStep, MTree.leaves]
      exact ⟨hl1, by rw [hl2, hr1], by rw [hl2, hr2], hl3, hr3⟩

lemma stepKind_spec (C : Family) (v0 off : ℕ) {s : RawState ℕ} (hs : validS s) :
    startK (stepKind C off s).1 = off ∧
    startK (stepKind C off s).2 = off + servedK (stepKind C off s).1 ∧
    servedK (stepKind C off s).1 + servedK (stepKind C off s).2 = servedC s.2 ∧
    validK v0 (stepKind C off s).1 ∧ validK v0 (stepKind C off s).2 := by
  rcases s with ⟨v, k | τ⟩
  · have hne : C.tree k ≠ MTree.leaf := by
      obtain ⟨l, r, h | h⟩ := C.root k <;> simp [h]
    simpa only [stepKind, servedC, C.leaves k hs] using treeStep_spec v0 off hne
  · exact treeStep_spec v0 off hs

noncomputable def childLaw (μ ν : PMF ℕ) (v0 : ℕ) : ChildK → PMF (RawState ℕ)
  | .internal _ t => PMF.pure (v0, t)
  | .slot _ => freshRaw μ ν

noncomputable def rawKernel (C : Family) (μ ν : PMF ℕ) (v0 : ℕ) (s : RawState ℕ) :
    PMF (RawState ℕ × RawState ℕ) :=
  prodPMF (childLaw μ ν v0 (stepKind C 0 s).1) (childLaw μ ν v0 (stepKind C 0 s).2)

noncomputable def rawLaw (C : Family) (μ ν : PMF ℕ) (v0 n : ℕ) : PMF (FullLab (RawState ℕ) n) :=
  (freshRaw μ ν).bind fun s => muM (rawKernel C μ ν v0) s n

end ChainClasses.Profile
