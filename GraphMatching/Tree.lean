/-
`sec:reduction` of `graph_matching_selfcontained.tex`: the tree layer for leaf
labellings. Following design decision D4, `Aut(𝔹_h)` is **defined** as the swap
group (the iterated wreath product `Aut(𝔹_{h+1}) = Aut(𝔹_h) ≀ Bool`): an
automorphism fixes the root, either preserves or swaps the two principal
subtrees, and acts by independent automorphisms inside them. This is exactly the
recursive characterisation the paper uses; `AutBridge.lean` identifies the swap
group with the root-fixing graph automorphisms of the tree's adjacency
structure, closing the bridge D4 left open.

With this definition the leaf recursion `eq:leaf-rec`,

    x ≈^leaf_{h+1} y  ↔  (x₀ ≈^leaf_h y₀ ∧ x₁ ≈^leaf_h y₁) ∨ (x₀ ≈^leaf_h y₁ ∧ x₁ ≈^leaf_h y₀),

is proved (`leafSim_succ`): it is `SquareRel (≈^leaf_h)`. The measure recursion
`μ_{h+1} = μ_h ⊗ μ_h` is definitional. Reflexivity and symmetry propagate.
-/
import GraphMatching.Square

namespace GraphMatching

open scoped ENNReal Classical

universe u
variable {V : Type u}

/-! ### The tree, its leaf labellings, and its automorphism group -/

/-- Leaf labellings of `𝔹_h`, split by principal subtrees:
`Leaf V 0 = V`, `Leaf V (h+1) = Leaf V h × Leaf V h`. -/
def Leaf (V : Type u) : ℕ → Type u
  | 0 => V
  | h + 1 => Leaf V h × Leaf V h

/-- `Aut(𝔹_h)` as the swap group: `Aut 0 = Unit`,
`Aut (h+1) = Bool × Aut h × Aut h` (a swap bit and the two subtree
automorphisms). -/
def Aut : ℕ → Type
  | 0 => Unit
  | h + 1 => Bool × Aut h × Aut h

/-- `matchesA R₀ h π x y`: the leaf labelling `x` matches `y` under the
automorphism `π`, i.e. `x(ℓ) R₀ y(π ℓ)` at every leaf `ℓ`. At `h+1`, `π`'s swap
bit sends `x`'s left subtree to `y`'s right (`bif π.1`) or left subtree. -/
def matchesA (R₀ : V → V → Prop) : (h : ℕ) → Aut h → Leaf V h → Leaf V h → Prop
  | 0, _, x, y => R₀ x y
  | h + 1, π, x, y =>
      matchesA R₀ h π.2.1 x.1 (bif π.1 then y.2 else y.1)
        ∧ matchesA R₀ h π.2.2 x.2 (bif π.1 then y.1 else y.2)

/-- The leaf relation `x ≈^leaf_h y`: some automorphism of `𝔹_h` matches `x` to `y`. -/
def leafSim (R₀ : V → V → Prop) (h : ℕ) (x y : Leaf V h) : Prop :=
  ∃ π : Aut h, matchesA R₀ h π x y

/-- At height 0 the tree is a single vertex, so `≈^leaf_0 = R₀`. -/
lemma leafSim_zero (R₀ : V → V → Prop) : leafSim R₀ 0 = R₀ := by
  funext x y
  simp only [leafSim, matchesA]
  exact propext ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨(), hh⟩⟩

/-- **`eq:leaf-rec`**, the leaf recursion: `≈^leaf_{h+1} = (≈^leaf_h)^□`. This is where the
swap-group structure of `Aut(𝔹_{h+1})` is used. -/
lemma leafSim_succ (R₀ : V → V → Prop) (h : ℕ) :
    leafSim R₀ (h + 1) = SquareRel (leafSim R₀ h) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨b, π₀, π₁⟩, hm⟩
    simp only [matchesA] at hm
    cases b
    · exact Or.inl ⟨⟨π₀, hm.1⟩, π₁, hm.2⟩
    · exact Or.inr ⟨⟨π₀, hm.1⟩, π₁, hm.2⟩
  · rintro (⟨⟨π₀, h₀⟩, π₁, h₁⟩ | ⟨⟨π₀, h₀⟩, π₁, h₁⟩)
    · exact ⟨(false, π₀, π₁), h₀, h₁⟩
    · exact ⟨(true, π₀, π₁), h₀, h₁⟩

/-! ### Reflexivity and symmetry propagate -/

lemma leafSim_refl (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v) :
    ∀ (h : ℕ) (x : Leaf V h), leafSim R₀ h x x := by
  intro h
  induction h with
  | zero => intro x; exact ⟨(), hrefl x⟩
  | succ h ih => intro x; rw [leafSim_succ]; exact SquareRel_refl ih x

lemma leafSim_symm (R₀ : V → V → Prop) (hsymm : ∀ a b, R₀ a b → R₀ b a) :
    ∀ (h : ℕ) (x y : Leaf V h), leafSim R₀ h x y → leafSim R₀ h y x := by
  intro h
  induction h with
  | zero => intro x y; exact fun ⟨_, hh⟩ => ⟨(), hsymm _ _ hh⟩
  | succ h ih => intro x y; rw [leafSim_succ]; exact SquareRel_symm ih x y

/-! ### The leaf product measure -/

/-- The leaf product measure: `μ_0 = μ`, `μ_{h+1} = μ_h ⊗ μ_h`. Since
`Leaf V (h+1) = Leaf V h × Leaf V h` this is `prodPMF` at each step. -/
noncomputable def leafMu (μ : PMF V) : (h : ℕ) → PMF (Leaf V h)
  | 0 => μ
  | h + 1 => prodPMF (leafMu μ h) (leafMu μ h)

@[simp] lemma leafMu_succ (μ : PMF V) (h : ℕ) :
    leafMu μ (h + 1) = prodPMF (leafMu μ h) (leafMu μ h) := rfl

/-! ### Full labellings

A full labelling carries a value at every vertex: `FullLab V 0 = V`,
`FullLab V (h+1) = V × (FullLab V h × FullLab V h)` (root label, then the two
subtree labellings). A matching must agree (via `R₀`) at every vertex, so the
recursion `eq:full-rec` carries a root conjunct `R₀ a a'` on top of the swap action:
`≈_{h+1} = R₀ ⊗ (≈_h)^□`. -/

/-- Full labellings of `𝔹_h`. -/
def FullLab (V : Type u) : ℕ → Type u
  | 0 => V
  | h + 1 => V × (FullLab V h × FullLab V h)

/-- `x` matches `y` under `π` at every vertex: the root labels are `R₀`-related,
and the two subtrees match under the swap action. -/
def fullMatchesA (R₀ : V → V → Prop) : (h : ℕ) → Aut h → FullLab V h → FullLab V h → Prop
  | 0, _, x, y => R₀ x y
  | h + 1, π, x, y =>
      R₀ x.1 y.1
        ∧ fullMatchesA R₀ h π.2.1 x.2.1 (bif π.1 then y.2.2 else y.2.1)
        ∧ fullMatchesA R₀ h π.2.2 x.2.2 (bif π.1 then y.2.1 else y.2.2)

/-- The full relation `x ≈_h y`: some automorphism matches every vertex. -/
def fullSim (R₀ : V → V → Prop) (h : ℕ) (x y : FullLab V h) : Prop :=
  ∃ π : Aut h, fullMatchesA R₀ h π x y

lemma fullSim_zero (R₀ : V → V → Prop) : fullSim R₀ 0 = R₀ := by
  funext x y
  simp only [fullSim, fullMatchesA]
  exact propext ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨(), hh⟩⟩

/-- **`eq:full-rec`**, the full recursion: `≈_{h+1} = R₀ ⊗ (≈_h)^□`. -/
lemma fullSim_succ (R₀ : V → V → Prop) (h : ℕ) :
    fullSim R₀ (h + 1) = ProdRel R₀ (SquareRel (fullSim R₀ h)) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨b, π₀, π₁⟩, hroot, hm⟩
    refine ⟨hroot, ?_⟩
    cases b
    · exact Or.inl ⟨⟨π₀, hm.1⟩, π₁, hm.2⟩
    · exact Or.inr ⟨⟨π₀, hm.1⟩, π₁, hm.2⟩
  · rintro ⟨hroot, (⟨⟨π₀, h₀⟩, π₁, h₁⟩ | ⟨⟨π₀, h₀⟩, π₁, h₁⟩)⟩
    · exact ⟨(false, π₀, π₁), hroot, h₀, h₁⟩
    · exact ⟨(true, π₀, π₁), hroot, h₀, h₁⟩

lemma fullSim_refl (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v) :
    ∀ (h : ℕ) (x : FullLab V h), fullSim R₀ h x x := by
  intro h
  induction h with
  | zero => intro x; exact ⟨(), hrefl x⟩
  | succ h ih => intro x; rw [fullSim_succ]; exact ProdRel_refl hrefl (SquareRel_refl ih) x

lemma fullSim_symm (R₀ : V → V → Prop) (hsymm : ∀ a b, R₀ a b → R₀ b a) :
    ∀ (h : ℕ) (x y : FullLab V h), fullSim R₀ h x y → fullSim R₀ h y x := by
  intro h
  induction h with
  | zero => intro x y; exact fun ⟨_, hh⟩ => ⟨(), hsymm _ _ hh⟩
  | succ h ih => intro x y; rw [fullSim_succ]; exact ProdRel_symm hsymm (SquareRel_symm ih) x y

/-- The full product measure: `μ_0 = μ`, `μ_{h+1} = μ ⊗ (μ_h ⊗ μ_h)`. -/
noncomputable def fullMu (μ : PMF V) : (h : ℕ) → PMF (FullLab V h)
  | 0 => μ
  | h + 1 => prodPMF μ (prodPMF (fullMu μ h) (fullMu μ h))

@[simp] lemma fullMu_succ (μ : PMF V) (h : ℕ) :
    fullMu μ (h + 1) = prodPMF μ (prodPMF (fullMu μ h) (fullMu μ h)) := rfl

end GraphMatching
