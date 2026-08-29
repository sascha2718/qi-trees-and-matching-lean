/-
The matching relation over the full automorphism group
(`arbitrary_offspring_matching.tex` `eq:matching-event`): `fullSim R₀ n` is
matchability of two labellings of `𝔹_n` by some rooted automorphism. The
group is `AutK 1` of the `Support` support layer: at `k = 1` every
vertex carries a swap bit, which is the full group, and the recursion

    fullSim (n+1) = R₀ ⊗ (fullSim n)^(2)

is the `k = 1` swap-phase recursion. This file restates the recursion through
the typed wrappers `leaf`/`branch` (pointwise, as an `Iff`), and proves that
matching forces root compatibility, the fact behind the kernel-mismatch layer.
-/
import GraphMarkovMatching.Process.Basic

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {S : Type u}

/-- Matchability over the full automorphism group of `𝔹_n`. -/
def fullSim (R₀ : S → S → Prop) (n : ℕ) : FullLab S n → FullLab S n → Prop :=
  fullSimK R₀ 1 0 n

/-- Height `0` through the wrappers: two leaves match iff their states are
compatible. -/
lemma fullSim_leaf (R₀ : S → S → Prop) (s t : S) :
    fullSim R₀ 0 (leaf s) (leaf t) ↔ R₀ s t := by
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨(), h⟩

/-- The recursion through the wrappers: attached samples match iff the roots
are compatible and the subtree pairs match under the symmetrised square. -/
lemma fullSim_branch (R₀ : S → S → Prop) (n : ℕ) (s t : S)
    (p r : FullLab S n × FullLab S n) :
    fullSim R₀ (n + 1) (branch s p) (branch t r)
      ↔ R₀ s t ∧ SquareRel (fullSim R₀ n) p r := by
  constructor
  · rintro ⟨⟨b, π₀, π₁⟩, hroot, h₀, h₁⟩
    refine ⟨hroot, ?_⟩
    cases b
    · exact Or.inl ⟨⟨π₀, h₀⟩, π₁, h₁⟩
    · exact Or.inr ⟨⟨π₀, h₀⟩, π₁, h₁⟩
  · rintro ⟨hroot, (⟨⟨π₀, h₀⟩, π₁, h₁⟩ | ⟨⟨π₀, h₀⟩, π₁, h₁⟩)⟩
    · exact ⟨(false, π₀, π₁), hroot, h₀, h₁⟩
    · exact ⟨(true, π₀, π₁), hroot, h₀, h₁⟩

/-- Matching forces root compatibility. This is the mechanism that converts
kernel-pattern mismatch into certain matching failure. -/
lemma fullSim_root (R₀ : S → S → Prop) :
    ∀ (n : ℕ) (x y : FullLab S n),
      fullSim R₀ n x y → R₀ (rootLab n x) (rootLab n y) := by
  intro n
  cases n with
  | zero => rintro x y ⟨_, h⟩; exact h
  | succ n =>
      rintro x y ⟨π, h⟩
      exact h.1

/-- The squared form: a matched pair of subtree pairs has `R₀`-square-related
root patterns. -/
lemma squareRel_root (R₀ : S → S → Prop) (n : ℕ)
    (p r : FullLab S n × FullLab S n) :
    SquareRel (fullSim R₀ n) p r
      → SquareRel R₀ (rootLab n p.1, rootLab n p.2) (rootLab n r.1, rootLab n r.2) := by
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · exact Or.inl ⟨fullSim_root R₀ n _ _ h₁, fullSim_root R₀ n _ _ h₂⟩
  · exact Or.inr ⟨fullSim_root R₀ n _ _ h₁, fullSim_root R₀ n _ _ h₂⟩

/-- Reflexivity propagates (identity automorphism). -/
lemma fullSim_refl (R₀ : S → S → Prop) (h : ∀ v, R₀ v v) (n : ℕ)
    (x : FullLab S n) : fullSim R₀ n x x :=
  fullSimK_refl R₀ h 1 n 0 x

/-- Symmetry propagates. -/
lemma fullSim_symm (R₀ : S → S → Prop) (h : ∀ a b, R₀ a b → R₀ b a) (n : ℕ)
    (x y : FullLab S n) : fullSim R₀ n x y → fullSim R₀ n y x :=
  fullSimK_symm R₀ h 1 n 0 x y

end GraphMarkovMatching
