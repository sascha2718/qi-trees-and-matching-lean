module

public import Mathlib

@[expose] public section

/-!
# The quasi-isometry classes of Galton–Watson trees

Thirteen statements from J. S. Athreya and S. Troscheit,
*The quasi-isometry classes of Galton–Watson trees*, arXiv:2609.23882v2.
Theorem, equation and condition numbers refer to that version.

Vertices are words over `Fin N`, with `0, …, N-1` representing the paper's children
`1, …, N`; the binary tree uses `Fin 2`. Label laws are `PMF`s; event probabilities lie in
`ℝ≥0∞`. Distances are `SimpleGraph.dist`, the graph metric on the connected graphs used here.
-/

namespace Challenge

open scoped ENNReal Classical
open MeasureTheory

/-! ## Matching labels on the binary tree -/

/-- The joint law of independent draws from `μ` and `ν`. -/
noncomputable def prodPMF {X Y : Type*} (μ : PMF X) (ν : PMF Y) : PMF (X × Y) :=
  μ.bind fun x => ν.map fun y => (x, y)

section Potential
variable {X : Type*}

/-- The compatible mass `b(x) = μ{y : x R y}`. -/
noncomputable def rE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then μ y else 0

/-- The incompatible mass `q(x) = μ{y : ¬ x R y} = 1 - b(x)`. -/
noncomputable def qE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then 0 else μ y

/-- The incompatible mass `q(x)` as a real number in `[0, 1]`. -/
noncomputable def q (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ := (qE μ R x).toReal

/-- The weight `φ_α(t) = t / (1 - t)^α`, used for `0 ≤ t < 1`. -/
noncomputable def phi (α t : ℝ) : ℝ := t / (1 - t) ^ α

/-- The weight `φ_α(t)` with values in `ℝ≥0∞`, taken to be `∞` for `t ≥ 1`. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤

/-- The one-site potential `η_α(μ)` of (5.1), infinite if `b(x) = 0` at a label of positive mass. -/
noncomputable def potential (α : ℝ) (μ : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * phiE α (q μ R x)

end Potential

/-- Labellings of every vertex of the binary tree of height `n`. -/
def FullLab (S : Type*) : ℕ → Type _
  | 0 => S
  | n + 1 => S × (FullLab S n × FullLab S n)

section Iid
variable {V : Type*}

/-- Labellings of the `2^h` leaves of the binary tree of height `h`. -/
def Leaf (V : Type*) : ℕ → Type _
  | 0 => V
  | h + 1 => Leaf V h × Leaf V h

/-- Rooted automorphisms `Aut(𝔹_h)`, encoded by a swap bit and two subtree automorphisms. -/
def Aut : ℕ → Type
  | 0 => Unit
  | h + 1 => Bool × Aut h × Aut h

/-- The automorphism `π` matches every leaf of `x` to an `R₀`-compatible leaf of `y`. -/
def matchesA (R₀ : V → V → Prop) : (h : ℕ) → Aut h → Leaf V h → Leaf V h → Prop
  | 0, _, x, y => R₀ x y
  | h + 1, π, x, y =>
      matchesA R₀ h π.2.1 x.1 (bif π.1 then y.2 else y.1)
        ∧ matchesA R₀ h π.2.2 x.2 (bif π.1 then y.1 else y.2)

/-- Two leaf labellings are matched by some automorphism of the tree. -/
def leafSim (R₀ : V → V → Prop) (h : ℕ) (x y : Leaf V h) : Prop :=
  ∃ π : Aut h, matchesA R₀ h π x y

/-- The automorphism `π` matches every vertex of `x` to an `R₀`-compatible vertex of `y`. -/
def fullMatchesA (R₀ : V → V → Prop) : (h : ℕ) → Aut h → FullLab V h → FullLab V h → Prop
  | 0, _, x, y => R₀ x y
  | h + 1, π, x, y =>
      R₀ x.1 y.1
        ∧ fullMatchesA R₀ h π.2.1 x.2.1 (bif π.1 then y.2.2 else y.2.1)
        ∧ fullMatchesA R₀ h π.2.2 x.2.2 (bif π.1 then y.2.1 else y.2.2)

/-- Two full labellings are matched at every vertex by some automorphism. -/
def fullSim (R₀ : V → V → Prop) (h : ℕ) (x y : FullLab V h) : Prop :=
  ∃ π : Aut h, fullMatchesA R₀ h π x y

/-- The law of a leaf labelling of height `h` whose leaf labels are i.i.d. with law `μ`. -/
noncomputable def leafMu (μ : PMF V) : (h : ℕ) → PMF (Leaf V h)
  | 0 => μ
  | h + 1 => prodPMF (leafMu μ h) (leafMu μ h)

/-- The law of a full labelling of height `h` whose labels are i.i.d. with law `μ`. -/
noncomputable def fullMu (μ : PMF V) : (h : ℕ) → PMF (FullLab V h)
  | 0 => μ
  | h + 1 => prodPMF μ (prodPMF (fullMu μ h) (fullMu μ h))

/-- Labels in `G` are compatible when equal or adjacent. -/
def compat (G : SimpleGraph V) (v w : V) : Prop := v = w ∨ G.Adj v w

/-- Restriction from height `h + 1` to height `h`. -/
def restrictLab : (h : ℕ) → FullLab V (h + 1) → FullLab V h
  | 0, x => x.1
  | h + 1, x => (x.1, restrictLab h x.2.1, restrictLab h x.2.2)

/-- The label at a word, used for words of length at most the height. -/
def coord : (h : ℕ) → FullLab V h → List (Fin 2) → V
  | 0, x, _ => x
  | _ + 1, x, [] => x.1
  | h + 1, x, c :: t => coord h (if c = 0 then x.2.1 else x.2.2) t

/-- Adjacency in the infinite rooted binary tree: one word extends the other by one letter. -/
def treeAdj (s t : List (Fin 2)) : Prop := (∃ c, t = s ++ [c]) ∨ (∃ c, s = t ++ [c])

/-- A root-fixing automorphism of the infinite binary tree. -/
def IsTreeAut (g : List (Fin 2) ≃ List (Fin 2)) : Prop :=
  g [] = [] ∧ ∀ s t, treeAdj s t ↔ treeAdj (g s) (g t)

/-- The product σ-algebra on full labellings. -/
instance instMeasurableFullLab {V : Type*} [MeasurableSpace V] :
    (h : ℕ) → MeasurableSpace (FullLab V h)
  | 0 => ‹MeasurableSpace V›
  | h + 1 =>
      let inst := instMeasurableFullLab (V := V) h
      @Prod.instMeasurableSpace V (FullLab V h × FullLab V h) _
        (@Prod.instMeasurableSpace (FullLab V h) (FullLab V h) inst inst)

end Iid

/-- Independent consistent labellings with finite-height laws `μ`, `ν`, matched at every
vertex by one root-fixing automorphism with probability at least `p`. -/
def InfiniteMatching {V : Type u} [MeasurableSpace V] (R : V → V → Prop)
    (μ ν : (h : ℕ) → PMF (FullLab V h)) (p : ℝ≥0∞) : Prop :=
  ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (X Y : (h : ℕ) → Ω → FullLab V h),
    (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
    (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
    (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
    (∀ h, P.map (fun ω => (X h ω, Y h ω)) = (prodPMF (μ h) (ν h)).toMeasure) ∧
    p ≤ P {ω | ∃ g : List (Fin 2) ≃ List (Fin 2), IsTreeAut g ∧
      ∀ s : List (Fin 2), R (coord (g s).length (X (g s).length ω) (g s))
        (coord s.length (Y s.length ω) s)}

/-! ## Galton–Watson trees and quasi-isometry -/

/-- The parent–child graph on `T`, joining words to their one-letter extensions in `T`. -/
def wordGraph {A : Type*} (T : List A → Prop) : SimpleGraph {w // T w} :=
  SimpleGraph.fromRel fun u v => ∃ a, v.1 = u.1 ++ [a]

section Classification

/-- An offspring law supported on `{0, …, J}`; positive mass at `J` is not required. -/
structure Offspring (J : ℕ) where
  /-- The law of the number of children. -/
  pmf : PMF ℕ
  /-- No mass above `J`. -/
  vanishing : ∀ j, J < j → pmf j = 0

/-- An offspring law applied to `j` is the real probability `θ(j)` of `j` children. -/
instance {J : ℕ} : CoeFun (Offspring J) (fun _ => ℕ → ℝ) :=
  ⟨fun theta j => (theta.pmf j).toReal⟩

namespace Offspring

/-- The mean offspring number `∑_j j θ(j)`. -/
noncomputable def mean {J : ℕ} (theta : Offspring J) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), (j : ℝ) * theta j

/-- Supercriticality: the mean offspring number exceeds `1`. -/
def IsSupercritical {J : ℕ} (theta : Offspring J) : Prop := 1 < theta.mean

end Offspring

/-- Vertex addresses of the `N`-ary tree, as words over `Fin N`. -/
abbrev GWWord (N : ℕ) : Type := List (Fin N)

/-- The tree cut out by offspring counts `c`: each letter is below the count at its prefix. -/
def inGWSample {N : ℕ} (c : GWWord N → ℕ) (v : GWWord N) : Prop :=
  ∀ i, (h : i < v.length) → ((v.get ⟨i, h⟩ : Fin N) : ℕ) < c (v.take i)

/-- Survival: the sample tree is infinite, equivalently of infinite diameter. -/
def gwSurvives {N : ℕ} (c : GWWord N → ℕ) : Prop :=
  {v | inGWSample c v}.Infinite

/-- Independent offspring counts with law `θ` on the `N`-ary tree. For `J ≤ N`,
`inGWSample` gives a Galton–Watson tree with offspring law `θ`. -/
noncomputable def gwField {J N : ℕ} (theta : Offspring J) : Measure (GWWord N → ℕ) :=
  Measure.infinitePi (fun _ : GWWord N => theta.pmf.toMeasure)

/-- The root `[]` of the tree cut out by `c`, as a vertex of that tree. -/
def gwRoot {N : ℕ} (c : GWWord N → ℕ) : {w : GWWord N // inGWSample c w} :=
  ⟨[], fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A `D`-quasi-isometry for the graph metrics, with `D`-dense image. -/
structure GraphQIWith {V V' : Type*} (D : ℕ) (G : SimpleGraph V)
    (G' : SimpleGraph V') (f : V → V') : Prop where
  upper : ∀ x y, G'.dist (f x) (f y) ≤ D * G.dist x y + D
  lower : ∀ x y, G.dist x y ≤ D * G'.dist (f x) (f y) + D * D
  dense : ∀ y', ∃ x, G'.dist (f x) y' ≤ D

/-- Two graphs are quasi-isometric: some map is a `D`-quasi-isometry for some `D`. -/
def GraphQuasiIsometric {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ (D : ℕ) (f : V → V'), GraphQIWith D G G' f

/-- Two graphs are quasi-isometric by a map sending a chosen vertex to a chosen vertex. -/
def GraphQuasiIsometricRooted {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')
    (r : V) (r' : V') : Prop :=
  ∃ (D : ℕ) (f : V → V'), GraphQIWith D G G' f ∧ f r = r'

/-- A `D`-quasi-isometric embedding: the metric inequalities without coarse density. -/
structure GraphQIEmbWith {V V' : Type*} (D : ℕ) (G : SimpleGraph V)
    (G' : SimpleGraph V') (f : V → V') : Prop where
  upper : ∀ x y, G'.dist (f x) (f y) ≤ D * G.dist x y + D
  lower : ∀ x y, G.dist x y ≤ D * G'.dist (f x) (f y) + D * D

/-- Existence of a quasi-isometric embedding from `G` into `G'`. -/
def GraphQIEmbeddable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ (D : ℕ) (f : V → V'), GraphQIEmbWith D G G' f

/-- The shifted support `{k - 1 : 2 ≤ k ≤ J, θ(k) ≠ 0}`. The additive monoid it generates is
the branching semigroup `Λ_θ` that indexes the chain classes. -/
noncomputable def shiftSupp {J : ℕ} (theta : Offspring J) : Finset ℕ :=
  ((Finset.range (J + 1)).filter fun k => 2 ≤ k ∧ theta k ≠ 0).image fun k => k - 1

/-- The same infinite class of Theorem 1.2: ray (R), full tree (F), chain `(C_Λ)` with
the same branching semigroup, or bushy (B), in the order below. -/
def SameInfiniteClass {J J' : ℕ} (theta : Offspring J) (theta' : Offspring J') : Prop :=
  (theta 1 = 1 ∧ theta' 1 = 1) ∨
  (theta 0 = 0 ∧ theta 1 = 0 ∧ theta' 0 = 0 ∧ theta' 1 = 0) ∨
  ((theta 0 = 0 ∧ 0 < theta 1 ∧ theta 1 < 1) ∧ (theta' 0 = 0 ∧ 0 < theta' 1 ∧ theta' 1 < 1) ∧
    AddSubmonoid.closure (shiftSupp theta : Set ℕ) =
      AddSubmonoid.closure (shiftSupp theta' : Set ℕ)) ∨
  (0 < theta 0 ∧ 0 < theta' 0)

end Classification

/-! ## The two-value family -/

section TwoValue

/-- Vertices of the binary tree, as words over `Fin 2`. -/
abbrev Word : Type := List (Fin 2)

/-- The sample tree of the offspring field `χ`: the root, one child `v·1` always,
and a second child `v·2` exactly when `χ v = true`. -/
inductive InTree (χ : Word → Bool) : Word → Prop
  | root : InTree χ []
  | one {v : Word} : InTree χ v → InTree χ (v ++ [0])
  | two {v : Word} : InTree χ v → χ v = true → InTree χ (v ++ [1])

/-- Independent Bernoulli labels; `InTree` gives offspring law `θ(2) = t`, `θ(1) = 1 - t`. -/
noncomputable def bernoulliField {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : Measure (Word → Bool) :=
  Measure.infinitePi (fun _ : Word =>
    ProbabilityTheory.bernoulliMeasure true false ⟨t, ht, ht1⟩)

end TwoValue

/-! ## Markov labels -/

namespace Markov

/-- A Markov model of Section 6 with states `V`, types `I`, compatibility `R`, prescribed
state `zero`, fresh law `μ`, fresh types `I_μ`, and child-type pair laws `π t = P_t`. -/
structure Model (V I : Type) where
  R : V → V → Prop
  zero : V
  μ : PMF V
  fresh : I → Prop
  π : I → PMF (I × I)

namespace Model

variable {V I : Type} (M : Model V I)

/-- State compatibility is reflexive and symmetric. -/
structure IsCompat (M : Model V I) : Prop where
  refl : ∀ v, M.R v v
  symm : ∀ v w, M.R v w → M.R w v

/-- The state law at type `t`: `μ` if fresh, the point mass at `zero` otherwise. -/
noncomputable def rootLaw (t : I) : PMF V :=
  if M.fresh t then M.μ else PMF.pure M.zero

/-- The state labelling law at height `h` from type `t`: draw the root state and child types
independently, then independent subtrees conditional on their types. -/
noncomputable def rho : I → (h : ℕ) → PMF (FullLab V h)
  | t, 0 => M.rootLaw t
  | t, h + 1 => (M.rootLaw t).bind fun v =>
      ((M.π t).bind fun j => prodPMF (rho j.1 h) (rho j.2 h)).map fun p => (v, p)

/-- The failure probability `P(M_h(s,t)^c)` for independent state labellings from `s` and `t`. -/
noncomputable def failProb (s t : I) (h : ℕ) : ℝ≥0∞ :=
  ∑' x, M.rho s h x * qE (M.rho t h) (fullSim M.R h) x

/-- The incompatibility mass of the prescribed state: `δ = 1 - b(0) = μ{v : ¬ R 0 v}`. -/
noncomputable def delta : ℝ≥0∞ := qE M.μ M.R M.zero

/-- The one-site defect `ζ_α = max(η_α, φ_α(δ))` of (6.1), infinite when `b(0) = 0`. -/
noncomputable def zeta (α : ℝ) : ℝ≥0∞ :=
  max (potential α M.μ M.R) (phiE α M.delta.toReal)

/-- The cyclic type classes of the finite-type alternative in Theorem 6.1. -/
structure Phase (M : Model V I) (g : ℕ) where
  /-- The class of each type. -/
  θ : I → ZMod g
  /-- Fresh types lie in class `0`. -/
  fresh_zero : ∀ t, M.fresh t → θ t = 0
  /-- Possible child types lie in the next class. -/
  child : ∀ t j, M.π t j ≠ 0 → θ j.1 = θ t + 1 ∧ θ j.2 = θ t + 1

/-- The number of types in class `i`. -/
noncomputable def Phase.count {M : Model V I} [Fintype I] {g : ℕ} (Θ : Phase M g)
    (i : ZMod g) : ℕ :=
  (Finset.univ.filter fun t => Θ.θ t = i).card

/-- `t'` is a possible child type of `t`: it occurs in a transition of positive probability. -/
def child (t t' : I) : Prop := ∃ j, M.π t j ≠ 0 ∧ (t' = j.1 ∨ t' = j.2)

/-- The types at depth `n` of possible type paths from `t`. -/
def reach (t : I) : ℕ → Set I
  | 0 => {t}
  | n + 1 => {u | ∃ s ∈ reach t n, M.child s u}

/-- Condition (M2), bounded returns: whenever `s` and `t` lie in the same class, every possible
type path from `s` visits a fresh type at some depth `n ≤ H` at which a possible type path from
`t` also visits a fresh type. -/
def CommonReturns {g : ℕ} (Θ : Phase M g) (H : ℕ) : Prop :=
  ∀ s t, Θ.θ s = Θ.θ t → ∀ p : ℕ → I, p 0 = s →
    (∀ i < H, M.child (p i) (p (i + 1))) →
    ∃ n ≤ H, M.fresh (p n) ∧ ∃ u ∈ M.reach t n, M.fresh u

/-- Condition (M1), positive matching: for fresh types `s` and `t` and every height `h`, each
state labelling of positive probability from `s` is matched with positive probability by an
independent labelling from `t`. -/
def FreshPositive : Prop :=
  ∀ (h : ℕ) (s t : I) (x : FullLab V h), M.fresh s → M.fresh t → M.rho s h x ≠ 0 →
    rE (M.rho t h) (fullSim M.R h) x ≠ 0

/-- The transition sum `∑_{j ∈ supp P_t} P_t(j)^(-α)` over the full transition support. -/
noncomputable def inverseSum [Fintype I] (α : ℝ) (t : I) : ℝ≥0∞ :=
  ∑ j ∈ Finset.univ.filter (fun j => M.π t j ≠ 0), (M.π t j) ^ (-α)

end Model

/-- The contraction coefficient `λ_α` of (6.2); `λ_α < 1` holds for `α ≥ 4/3`. -/
noncomputable def lambda (α : ℝ) : ℝ :=
  2 * sInf ((fun β : ℝ =>
    sSup ((fun q : ℝ => q / (1 + q) ^ α + β * (1 - q) ^ α) '' Set.Icc 0 1) +
      α ^ α / (α + 1) ^ (α + 1) * (1 - β) ^ (α + 1)) '' Set.Icc 0 1)

end Markov

/-! ## The i.i.d. matching theorem -/

/-- Theorem 5.1(1), the leaf bound (5.2). The sum is the matching failure probability
for two independent i.i.d. leaf labellings. -/
theorem audit_graph_leaf_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (h0 : potential (5 / 2) μ (compat G) ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * potential (5 / 2) μ (compat G) := sorry

/-- Theorem 5.1(2), the full bound (5.3): matching failure for independent i.i.d. labellings
of every vertex, uniformly in the height. -/
theorem audit_graph_full_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (hη : potential (5 / 2) μ (compat G) ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim (compat G) h) x
      ≤ 16 * potential (5 / 2) μ (compat G) := sorry

/-- Theorem 5.1(2) at infinite height: with probability at least `1 - 16 η_{5/2}(μ)`,
one root-fixing automorphism matches two independent i.i.d. labellings at every vertex. -/
theorem audit_exists_infinite_tree_matching_graphAut {V : Type u} (μ : PMF V)
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hη : potential (5 / 2) μ R₀ ≤ 1 / 10000) :
    InfiniteMatching R₀ (fullMu μ) (fullMu μ) (1 - 16 * potential (5 / 2) μ R₀) := sorry

/-! ## The finite class and the complete classification -/

/-- The finite class of Theorem 1.2: a connected graph of bounded diameter is quasi-isometric
to a point. -/
theorem audit_bounded_graph_qi_point {V : Type u} (G : SimpleGraph V) (hconn : G.Connected)
    (hbdd : ∃ D : ℕ, ∀ x y, G.dist x y ≤ D) :
    GraphQuasiIsometric G (⊥ : SimpleGraph Unit) := sorry

/-- Extinction for the finite class of Theorem 1.2: mean at most one implies almost-sure
finiteness, except for the deterministic one-child law. -/
theorem audit_extinction_of_not_supercritical {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hmean : ¬ theta.IsSupercritical) (h1 : theta 1 ≠ 1) :
    ∀ᵐ c ∂(gwField (N := N) theta), ¬ gwSurvives c := sorry

/-- Theorem 1.2, including the finite class, under independent unconditioned laws.
Almost surely, quasi-isometry is equivalent to the stated class agreement, and a
root-preserving map then exists. Conditioning is expressed through the survival events. -/
theorem audit_full_classification_ae_iff {J J' N N' : ℕ}
    (theta : Offspring J) (hJN : J ≤ N) (theta' : Offspring J') (hJN' : J' ≤ N') :
    ∀ᵐ omega ∂((gwField (N := N) theta).prod (gwField (N := N') theta')),
      (GraphQuasiIsometricRooted (wordGraph (inGWSample omega.1)) (wordGraph (inGWSample omega.2))
          (gwRoot omega.1) (gwRoot omega.2) ↔
        (¬ gwSurvives omega.1 ∧ ¬ gwSurvives omega.2) ∨
        (gwSurvives omega.1 ∧ gwSurvives omega.2 ∧ SameInfiniteClass theta theta')) ∧
      (GraphQuasiIsometric (wordGraph (inGWSample omega.1)) (wordGraph (inGWSample omega.2)) →
        (¬ gwSurvives omega.1 ∧ ¬ gwSurvives omega.2) ∨
        (gwSurvives omega.1 ∧ gwSurvives omega.2 ∧ SameInfiniteClass theta theta')) := sorry

/-! ## Mutual embeddability -/

/-- Theorem 1.3: almost surely on survival, a supercritical sample and the binary tree
admit quasi-isometric embeddings into one another. -/
theorem audit_mutual_embeddability {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hsup : theta.IsSupercritical) :
    ∀ᵐ c ∂(gwField (N := N) theta), gwSurvives c →
      GraphQIEmbeddable (wordGraph (inGWSample c)) (wordGraph (fun _ : GWWord 2 => True)) ∧
      GraphQIEmbeddable (wordGraph (fun _ : GWWord 2 => True)) (wordGraph (inGWSample c)) := sorry

/-! ## Universality in the two-value family -/

/-- Theorem 1.4: two independent trees of the two-value law almost surely admit a
root-preserving quasi-isometry, including at `t = 0, 1`. -/
theorem audit_twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((bernoulliField ht0 ht1).prod (bernoulliField ht0 ht1))
      {ω | ¬ GraphQuasiIsometricRooted (wordGraph (InTree ω.1)) (wordGraph (InTree ω.2))
        ⟨[], InTree.root⟩ ⟨[], InTree.root⟩} = 0 := sorry

/-- Theorem 1.4, the rate (1.1). For `D ≥ 3`, the bound is
`256 θ(1)^(D(D - 5/2))` with `θ(1) = 1 - t`, so `C = 256`. -/
theorem audit_twovalue_rate_tree {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ((bernoulliField ht0.le ht1.le).prod (bernoulliField ht0.le ht1.le))
          {ω | ¬ ∃ f : {w // InTree ω.1 w} → {w // InTree ω.2 w},
            GraphQIWith (D ^ 2 + 3) (wordGraph (InTree ω.1)) (wordGraph (InTree ω.2)) f ∧
              f ⟨[], InTree.root⟩ = ⟨[], InTree.root⟩}
        ≤ ENNReal.ofReal (256 * Real.sqrt ((1 - t) ^ (D * (2 * D - 5)))) := sorry

/-! ## The Markov matching theorem -/

/-- Theorem 6.1, finite-type alternative: matching failure is at most `K ζ_α` within each
cyclic class, uniformly in height. The constants depend only on `α, H, T, B`. -/
theorem audit_markov_matching_finite {α : ℝ} (hα : 1 ≤ α) (hlam : Markov.lambda α < 1)
    (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Markov.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Markov.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      (∀ t, M.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t → ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := sorry

/-- Theorem 6.1, zero-compatible alternative (`δ = 0`): the bound holds for all types and
heights, with constants depending only on `α` and no finiteness or return hypothesis. -/
theorem audit_markov_matching_zero {α : ℝ} (hα : 1 ≤ α) (hlam : Markov.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Markov.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := sorry

/-- Theorem 6.1, finite-type alternative at infinite height: with probability at least
`1 - K ζ_α`, one root-fixing automorphism matches independent processes of same-class types. -/
theorem audit_markov_matching_finite_infinite {α : ℝ} (hα : 1 ≤ α)
    (hlam : Markov.lambda α < 1) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V]
      (M : Markov.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Markov.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      (∀ t, M.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t →
      InfiniteMatching M.R (M.rho s) (M.rho t) (1 - ENNReal.ofReal Kc * M.zeta α) := sorry

/-- Theorem 6.1, zero-compatible alternative at infinite height: the same conclusion for
any two types, with countable state and type sets and constants depending only on `α`. -/
theorem audit_markov_matching_zero_infinite {α : ℝ} (hα : 1 ≤ α)
    (hlam : Markov.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V] [Countable I] (M : Markov.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t,
      InfiniteMatching M.R (M.rho s) (M.rho t) (1 - ENNReal.ofReal Kc * M.zeta α) := sorry

end Challenge
