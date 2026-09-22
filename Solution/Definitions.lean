import Mathlib

/-!
# The challenge vocabulary

This file repeats the definitions of `Challenge.lean`, with the same names, types, values and
docstrings, so that the solution does not import the challenge. Comparator checks that the
definitions used by the thirteen theorems agree between the two modules. Theorem, equation and
condition numbers refer to version 1 of arXiv:2609.23882.
-/

namespace Challenge

open scoped ENNReal Classical
open MeasureTheory

/-! ## Matching labels on the binary tree -/

/-- The product law of `μ` and `ν`: the joint law of independent draws from `μ` and `ν`. -/
noncomputable def prodPMF {X Y : Type*} (μ : PMF X) (ν : PMF Y) : PMF (X × Y) :=
  μ.bind fun x => ν.map fun y => (x, y)

section Potential
variable {X : Type*}

/-- The compatible mass `b(x) = μ{y : x R y}` of a label `x`: the probability that a label
drawn from `μ` is compatible with `x`. -/
noncomputable def rE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then μ y else 0

/-- The incompatible mass `q(x) = μ{y : ¬ x R y} = 1 - b(x)`: the probability that a label
drawn from `μ` is not compatible with `x`. -/
noncomputable def qE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then 0 else μ y

/-- The incompatible mass `q(x)` as a real number in `[0, 1]`. -/
noncomputable def q (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ := (qE μ R x).toReal

/-- The weight `φ_α(t) = t / (1 - t)^α`, used for `0 ≤ t < 1`. -/
noncomputable def phi (α t : ℝ) : ℝ := t / (1 - t) ^ α

/-- The weight `φ_α(t)` with values in `ℝ≥0∞`, taken to be `∞` for `t ≥ 1`. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤

/-- The one-site potential `η_α(μ) = ∑_x μ(x) φ_α(q(x))` of equation (5.1), for the
compatibility relation `R`. It is infinite when some label of positive mass has compatible
mass `b(x) = 0`. -/
noncomputable def potential (α : ℝ) (μ : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * phiE α (q μ R x)

end Potential

/-- Full labellings of the binary tree of height `n`, with a label in `S` at every vertex:
a single label at height `0`, and otherwise the root label together with the labellings of
the two subtrees of height `n - 1`. -/
def FullLab (S : Type*) : ℕ → Type _
  | 0 => S
  | n + 1 => S × (FullLab S n × FullLab S n)

section Iid
variable {V : Type*}

/-- Leaf labellings of the binary tree of height `h`, with a label in `V` at each of the `2^h`
leaves: a single label at height `0`, and otherwise the leaf labellings of the two subtrees. -/
def Leaf (V : Type*) : ℕ → Type _
  | 0 => V
  | h + 1 => Leaf V h × Leaf V h

/-- The rooted automorphisms `Aut(𝔹_h)` of the binary tree of height `h`, encoded recursively:
a bit recording whether the two subtrees of the root are exchanged, and automorphisms of the
two subtrees. -/
def Aut : ℕ → Type
  | 0 => Unit
  | h + 1 => Bool × Aut h × Aut h

/-- `matchesA R₀ h π x y`: the automorphism `π` carries every leaf of `x` to an
`R₀`-compatible leaf of `y`. -/
def matchesA (R₀ : V → V → Prop) : (h : ℕ) → Aut h → Leaf V h → Leaf V h → Prop
  | 0, _, x, y => R₀ x y
  | h + 1, π, x, y =>
      matchesA R₀ h π.2.1 x.1 (bif π.1 then y.2 else y.1)
        ∧ matchesA R₀ h π.2.2 x.2 (bif π.1 then y.1 else y.2)

/-- Two leaf labellings are matched by some automorphism of the tree. -/
def leafSim (R₀ : V → V → Prop) (h : ℕ) (x y : Leaf V h) : Prop :=
  ∃ π : Aut h, matchesA R₀ h π x y

/-- `fullMatchesA R₀ h π x y`: the automorphism `π` carries every vertex of `x` to an
`R₀`-compatible vertex of `y`. -/
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

/-- Compatibility of labels in a label graph `G`: equal or adjacent, that is,
`d_G(v, w) ≤ 1`. -/
def compat (G : SimpleGraph V) (v w : V) : Prop := v = w ∨ G.Adj v w

/-- The restriction of a full labelling of height `h + 1` to the vertices of depth at most
`h`. -/
def restrictLab : (h : ℕ) → FullLab V (h + 1) → FullLab V h
  | 0, x => x.1
  | h + 1, x => (x.1, restrictLab h x.2.1, restrictLab h x.2.2)

/-- The label of `x` at the vertex addressed by a word, where `false` selects the first child
and `true` the second. It is used for words of length at most the height. -/
def coord : (h : ℕ) → FullLab V h → List Bool → V
  | 0, x, _ => x
  | _ + 1, x, [] => x.1
  | h + 1, x, false :: t => coord h x.2.1 t
  | h + 1, x, true :: t => coord h x.2.2 t

/-- Adjacency in the infinite rooted binary tree: one word extends the other by one letter. -/
def treeAdj (s t : List Bool) : Prop := (∃ c, t = s ++ [c]) ∨ (∃ c, s = t ++ [c])

/-- `g` is a root-fixing automorphism of the infinite binary tree: a bijection of the words
that fixes the root `[]` and preserves adjacency in both directions. -/
def IsTreeAut (g : List Bool ≃ List Bool) : Prop :=
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

/-! ## Galton–Watson trees and quasi-isometry -/

/-- The parent–child graph on a set `T` of words: each word in `T` is joined to its one-letter
extensions in `T`. For the prefix-closed sets used below, this is the rooted tree with vertex
set `T` and root `[]`. -/
def wordGraph {A : Type*} (T : List A → Prop) : SimpleGraph {w // T w} :=
  SimpleGraph.fromRel fun u v => ∃ a, v.1 = u.1 ++ [a]

section Classification

/-- An offspring distribution `θ` with support in `{0, …, J}`. The bound `J` need not be
attained: positive mass at `J` is not required. -/
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

/-- Membership in the tree cut out by an offspring-count field `c`, which assigns a number of
children to every word: `v` belongs to the tree when each letter of `v` is less than the value
of `c` at the prefix preceding it. The tree is prefix-closed and contains the root `[]`. -/
def inGWSample {N : ℕ} (c : GWWord N → ℕ) (v : GWWord N) : Prop :=
  ∀ i, (h : i < v.length) → ((v.get ⟨i, h⟩ : Fin N) : ℕ) < c (v.take i)

/-- Survival: the tree cut out by the offspring-count field `c` is infinite. Since every vertex
has at most `N` children, this is equivalent to infinite diameter. -/
def gwSurvives {N : ℕ} (c : GWWord N → ℕ) : Prop :=
  {v | inGWSample c v}.Infinite

/-- The law of the offspring field: independent offspring counts with law `θ` at all words of
the `N`-ary tree. For `J ≤ N`, the tree cut out by a sample is a Galton–Watson tree with
offspring distribution `θ`. -/
noncomputable def gwField {J N : ℕ} (theta : Offspring J) : Measure (GWWord N → ℕ) :=
  Measure.infinitePi (fun _ : GWWord N => theta.pmf.toMeasure)

/-- The root `[]` of the tree cut out by `c`, as a vertex of that tree. -/
def gwRoot {N : ℕ} (c : GWWord N → ℕ) : {w : GWWord N // inGWSample c w} :=
  ⟨[], fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- `GraphQIWith D G G' f`: `f` is a `D`-quasi-isometry from `G` to `G'` for the graph metrics
`d`, `d'`, that is, `d'(f x, f y) ≤ D d(x, y) + D` and `d(x, y) ≤ D d'(f x, f y) + D²` for all
`x`, `y`, and every vertex of `G'` lies within distance `D` of the image. -/
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

/-- `GraphQIEmbWith D G G' f`: `f` is a `D`-quasi-isometric embedding of `G` into `G'`, the
two metric inequalities of a `D`-quasi-isometry without coarse density. -/
structure GraphQIEmbWith {V V' : Type*} (D : ℕ) (G : SimpleGraph V)
    (G' : SimpleGraph V') (f : V → V') : Prop where
  upper : ∀ x y, G'.dist (f x) (f y) ≤ D * G.dist x y + D
  lower : ∀ x y, G.dist x y ≤ D * G'.dist (f x) (f y) + D * D

/-- `G` embeds quasi-isometrically into `G'`: some map is a `D`-quasi-isometric embedding
for some `D`. -/
def GraphQIEmbeddable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ (D : ℕ) (f : V → V'), GraphQIEmbWith D G G' f

/-- The shifted support `{k - 1 : 2 ≤ k ≤ J, θ(k) ≠ 0}`. The additive monoid it generates is
the branching semigroup `Λ_θ` that indexes the chain classes. -/
noncomputable def shiftSupp {J : ℕ} (theta : Offspring J) : Finset ℕ :=
  ((Finset.range (J + 1)).filter fun k => 2 ≤ k ∧ theta k ≠ 0).image fun k => k - 1

/-- Two laws lie in the same infinite class of Theorem 1.2: both in the ray class (R),
`θ(1) = 1`; both in the full tree class (F), `θ(0) = θ(1) = 0`; both in chain classes,
`θ(0) = 0 < θ(1) < 1`, with the same branching semigroup; or both in the bushy class (B),
`θ(0) > 0`. -/
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

/-- Vertices of the binary tree, as words over `Bool`. -/
abbrev Word : Type := List Bool

/-- The sample tree of the offspring field `χ`: the root, one child `v·1` always,
and a second child `v·2` exactly when `χ v = true`. -/
inductive InTree (χ : Word → Bool) : Word → Prop
  | root : InTree χ []
  | one {v : Word} : InTree χ v → InTree χ (v ++ [false])
  | two {v : Word} : InTree χ v → χ v = true → InTree χ (v ++ [true])

/-- The i.i.d. field recording at each vertex whether it has two children (`true`, with
probability `t`) or one child (`false`). With `InTree`, a sample gives the Galton–Watson tree
with `θ(2) = t` and `θ(1) = 1 - t`. -/
noncomputable def bernoulliField {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : Measure (Word → Bool) :=
  Measure.infinitePi (fun _ : Word =>
    ProbabilityTheory.bernoulliMeasure true false ⟨t, ht, ht1⟩)

end TwoValue

/-! ## Markov labels -/

namespace Stopped

/-- A Markov label model of Section 6 with states `V` and types `I`. `R` is the compatibility
relation on states, `zero` the prescribed state `0`, `μ` the law of fresh states, `fresh` the
set `I_μ` of types that draw a fresh state, and `π t` the law `P_t` of the pair of child types
of a vertex of type `t`. -/
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

/-- The law of the state at a vertex of type `t`: `μ` for a fresh type, and the point mass at
`zero` otherwise. -/
noncomputable def rootLaw (t : I) : PMF V :=
  if M.fresh t then M.μ else PMF.pure M.zero

/-- The law of the state labelling of height `h` started at type `t`. The root state has law
`rootLaw t`; independently, the two child types are drawn from `π t`, and given them the two
subtrees are independent with the laws for their types. The labelling records states only,
not types. -/
noncomputable def rho : I → (h : ℕ) → PMF (FullLab V h)
  | t, 0 => M.rootLaw t
  | t, h + 1 => (M.rootLaw t).bind fun v =>
      ((M.π t).bind fun j => prodPMF (rho j.1 h) (rho j.2 h)).map fun p => (v, p)

/-- The failure probability `P(M_h(s,t)^c)`: the probability that two independent state
labellings of height `h`, started at types `s` and `t`, admit no automorphism matching the
states at every vertex. -/
noncomputable def failProb (s t : I) (h : ℕ) : ℝ≥0∞ :=
  ∑' x, M.rho s h x * qE (M.rho t h) (fullSim M.R h) x

/-- `δ = 1 - b(0) = μ{v : ¬ R 0 v}`: the probability that a fresh state is incompatible with
the prescribed state. -/
noncomputable def delta : ℝ≥0∞ := qE M.μ M.R M.zero

/-- The one-site defect `ζ_α = max(η_α, φ_α(δ))` of equation (6.1), where
`φ_α(δ) = (1 - b(0))/b(0)^α`. It is infinite when `b(0) = 0`. -/
noncomputable def zeta (α : ℝ) : ℝ≥0∞ :=
  max (potential α M.μ M.R) (phiE α M.delta.toReal)

/-- A partition of the types into `g` cyclic classes, indexed by `ZMod g`, as in the
finite-type hypotheses of Theorem 6.1: fresh types lie in class `0`, and both child types of a
transition of positive probability lie in the class following that of the parent. -/
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

/-- The transition sum `∑_{j ∈ supp P_t} P_t(j)^(-α)` over the support of the child-type law of
`t`. Bounds on these sums control the constants of the finite-type alternative. -/
noncomputable def inverseSum [Fintype I] (α : ℝ) (t : I) : ℝ≥0∞ :=
  ∑ j ∈ Finset.univ.filter (fun j => M.π t j ≠ 0), (M.π t j) ^ (-α)

end Model

/-- The contraction coefficient of equation (6.2),
`λ_α = 2 min_{0 ≤ β ≤ 1} (max_{0 ≤ q ≤ 1} (q/(1+q)^α + β(1-q)^α) + α^α (1-β)^(α+1)/(α+1)^(α+1))`.
The matching theorems assume `λ_α < 1`, which holds for `α ≥ 4/3`: the library proves
`λ_{4/3} < 499/500` (`GraphMarkovMatching.Stopped.lambda_fourThirds_lt`) and that `λ` is
strictly decreasing on `[1, ∞)` (`GraphMarkovMatching.Stopped.lambda_strictAntiOn`). -/
noncomputable def lambda (α : ℝ) : ℝ :=
  2 * sInf ((fun β : ℝ =>
    sSup ((fun q : ℝ => q / (1 + q) ^ α + β * (1 - q) ^ α) '' Set.Icc 0 1) +
      α ^ α / (α + 1) ^ (α + 1) * (1 - β) ^ (α + 1)) '' Set.Icc 0 1)

end Stopped

end Challenge
