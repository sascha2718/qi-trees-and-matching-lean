/-
The `G_k` tree layer: full labellings of `𝔹_n`, the restricted automorphism
group, and the phase recursions.

Indexing convention: `m` is the *swap distance* of the root, the number of
levels down to the next admissible swap level. `m = 0` means the root itself
carries a swap (phase `j = k-1`); its children restart at distance
`k-1`. For `m+1` the root has no swap and the children are at distance `m`.
The matching theorems root the tree at distance `k-1` (levels `≡ k-1 (mod k)`
are admissible, so the root at level `0` is `k-1` levels above the first).
At `k = 1` every vertex has `m = 0` and the group is the full automorphism
group, the case the Markov layer consumes.

Phase-dependent labels: the label law at a vertex of swap distance `m` is
`ν m`, for a given family `ν : ℕ → PMF V` (the applications use `ν` constant
on `{0,…,k-1}`-classes; only the values `m ≤ k-1` ever occur).

The recursions proved here:

    ≈(m,0)    = R₀
    ≈(0,n+1)  = R₀ ⊗ (≈(k-1,n))^(2)     (swap phase: symmetrised square)
    ≈(m+1,n+1)= R₀ ⊗ (≈(m,n) ⊗ ≈(m,n))  (product phase: no choice)

together with reflexivity/symmetry propagation and the product-measure
recursions, all definitional or by the `SquareRel`/`ProdRel` lemmas.
-/
import GraphMarkovMatching.Support.Square

namespace GraphMarkovMatching.Support

open scoped ENNReal Classical

universe u
variable {V : Type u}

/-! ### Full labellings -/

/-- Full labellings of `𝔹_n`: a label at every vertex.
`FullLab V 0 = V`, `FullLab V (n+1) = V × (FullLab V n × FullLab V n)`. -/
def FullLab (V : Type u) : ℕ → Type u
  | 0 => V
  | n + 1 => V × (FullLab V n × FullLab V n)

/-! ### The restricted automorphism group -/

/-- `AutK k m n`: the relative restricted automorphism group of `𝔹_n` when the
root is at swap distance `m`. A swap bit is available exactly at distance-`0`
vertices; children of a distance-`0` vertex are at distance `k-1`, children of
a distance-`(m+1)` vertex at distance `m`. At `k = 1` this is the full
automorphism group `Aut(𝔹_n)`, the case the Markov layer consumes. -/
def AutK (k : ℕ) : ℕ → ℕ → Type
  | _, 0 => Unit
  | 0, n + 1 => Bool × AutK k (k - 1) n × AutK k (k - 1) n
  | m + 1, n + 1 => AutK k m n × AutK k m n

example : AutK 2 0 1 = (Bool × AutK 2 1 0 × AutK 2 1 0) := rfl
example : AutK 2 1 1 = (AutK 2 0 0 × AutK 2 0 0) := rfl

/-- `AutK` is finite at every level (needed for the König step). -/
instance autK_finite (k : ℕ) : ∀ m n, Finite (AutK k m n)
  | _, 0 => by unfold AutK; infer_instance
  | 0, n + 1 => by
      have := autK_finite k (k - 1) n
      unfold AutK; infer_instance
  | m + 1, n + 1 => by
      have := autK_finite k m n
      unfold AutK; infer_instance

/-- `AutK` is nonempty at every level (the identity). -/
instance autK_nonempty (k : ℕ) : ∀ m n, Nonempty (AutK k m n)
  | _, 0 => ⟨()⟩
  | 0, n + 1 => by
      have h := autK_nonempty k (k - 1) n
      exact ⟨(false, h.some, h.some)⟩
  | m + 1, n + 1 => by
      have h := autK_nonempty k m n
      exact ⟨(h.some, h.some)⟩

/-! ### Matching under a restricted automorphism -/

/-- `fullMatchesK R₀ k m n π x y`: the labelling `x` matches `y` at every
vertex under `π ∈ AutK k m n`. At a swap vertex the bit `π.1` decides whether
the subtrees cross; at a product vertex they may not. -/
def fullMatchesK (R₀ : V → V → Prop) (k : ℕ) :
    (m : ℕ) → (n : ℕ) → AutK k m n → FullLab V n → FullLab V n → Prop
  | _, 0, _, x, y => R₀ x y
  | 0, n + 1, π, x, y =>
      R₀ x.1 y.1
        ∧ fullMatchesK R₀ k (k - 1) n π.2.1 x.2.1 (bif π.1 then y.2.2 else y.2.1)
        ∧ fullMatchesK R₀ k (k - 1) n π.2.2 x.2.2 (bif π.1 then y.2.1 else y.2.2)
  | m + 1, n + 1, π, x, y =>
      R₀ x.1 y.1
        ∧ fullMatchesK R₀ k m n π.1 x.2.1 y.2.1
        ∧ fullMatchesK R₀ k m n π.2 x.2.2 y.2.2

/-- The matching relation `≈(m,n)`: some `π ∈ AutK k m n` matches everything. -/
def fullSimK (R₀ : V → V → Prop) (k m n : ℕ) (x y : FullLab V n) : Prop :=
  ∃ π : AutK k m n, fullMatchesK R₀ k m n π x y

/-- **The swap-phase recursion**: `≈(0,n+1) = R₀ ⊗ (≈(k-1,n))^(2)`. -/
lemma fullSimK_succ_swap (R₀ : V → V → Prop) (k n : ℕ) :
    fullSimK R₀ k 0 (n + 1)
      = ProdRel R₀ (SquareRel (fullSimK R₀ k (k - 1) n)) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨b, π₀, π₁⟩, hroot, h⟩
    refine ⟨hroot, ?_⟩
    cases b
    · exact Or.inl ⟨⟨π₀, h.1⟩, π₁, h.2⟩
    · exact Or.inr ⟨⟨π₀, h.1⟩, π₁, h.2⟩
  · rintro ⟨hroot, (⟨⟨π₀, h₀⟩, π₁, h₁⟩ | ⟨⟨π₀, h₀⟩, π₁, h₁⟩)⟩
    · exact ⟨(false, π₀, π₁), hroot, h₀, h₁⟩
    · exact ⟨(true, π₀, π₁), hroot, h₀, h₁⟩

/-- **The product-phase recursion**: `≈(m+1,n+1) = R₀ ⊗ (≈(m,n) ⊗ ≈(m,n))`. -/
lemma fullSimK_succ_prod (R₀ : V → V → Prop) (k m n : ℕ) :
    fullSimK R₀ k (m + 1) (n + 1)
      = ProdRel R₀ (ProdRel (fullSimK R₀ k m n) (fullSimK R₀ k m n)) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨π₀, π₁⟩, hroot, h₀, h₁⟩
    exact ⟨hroot, ⟨π₀, h₀⟩, π₁, h₁⟩
  · rintro ⟨hroot, ⟨π₀, h₀⟩, π₁, h₁⟩
    exact ⟨(π₀, π₁), hroot, h₀, h₁⟩

/-! ### Reflexivity and symmetry propagate -/

lemma fullSimK_refl (R₀ : V → V → Prop) (h : ∀ v, R₀ v v) (k : ℕ) :
    ∀ (n m : ℕ) (x : FullLab V n), fullSimK R₀ k m n x x := by
  intro n
  induction n with
  | zero => intro m x; exact ⟨(), h x⟩
  | succ n ih =>
      intro m x
      match m with
      | 0 =>
          rw [fullSimK_succ_swap]
          exact ProdRel_refl h (SquareRel_refl (ih (k - 1))) x
      | m + 1 =>
          rw [fullSimK_succ_prod]
          exact ProdRel_refl h (ProdRel_refl (ih m) (ih m)) x

lemma fullSimK_symm (R₀ : V → V → Prop) (h : ∀ a b, R₀ a b → R₀ b a) (k : ℕ) :
    ∀ (n m : ℕ) (x y : FullLab V n), fullSimK R₀ k m n x y → fullSimK R₀ k m n y x := by
  intro n
  induction n with
  | zero => intro m x y; exact fun ⟨_, hh⟩ => ⟨(), h _ _ hh⟩
  | succ n ih =>
      intro m x y
      match m with
      | 0 =>
          rw [fullSimK_succ_swap]
          exact ProdRel_symm h (SquareRel_symm (ih (k - 1))) x y
      | m + 1 =>
          rw [fullSimK_succ_prod]
          exact ProdRel_symm h (ProdRel_symm (ih m) (ih m)) x y

end GraphMarkovMatching.Support
