import Mathlib

/-!
# The quasi-isometry classes of Galton–Watson trees: audited statements

This file states the thirteen headline theorems of J. S. Athreya and S. Troscheit,
*The quasi-isometry classes of Galton–Watson trees*, arXiv:2609.23882. Theorem, equation and
condition numbers below refer to version 1 of that paper. Every theorem here has the proof
`sorry`. `Solution.lean` proves declarations of the same names and types from the project
libraries, and Comparator checks that they agree and that the proofs use only `propext`,
`Classical.choice` and `Quot.sound`. The vocabulary below depends on Mathlib alone.

* Matching (Theorem 5.1). Two independent labellings of the binary tree, each with i.i.d.
  labels of law `μ`, are matched by a tree automorphism with high probability when the
  one-site potential `η_{5/2}(μ)` is small: `audit_graph_leaf_matching_bound`,
  `audit_graph_full_matching_bound` and `audit_exists_infinite_tree_matching_graphAut`.
* Classification (Theorem 1.2). Two independent Galton–Watson trees with finitely supported
  offspring laws almost surely admit a quasi-isometry exactly when both are finite, or both are
  infinite with laws in the same infinite class, and in that case they admit a root-preserving
  one: `audit_full_classification_ae_iff`, with the finite-class inputs
  `audit_bounded_graph_qi_point` and `audit_extinction_of_not_supercritical`.
* Mutual embeddability (Theorem 1.3): `audit_mutual_embeddability`.
* Universality in the two-value family (Theorem 1.4, with the rate (1.1)):
  `audit_twovalue_ae_tree_family` and `audit_twovalue_rate_tree`.
* Markov matching (Theorem 6.1), in its finite-type and zero-compatible alternatives, each at
  finite and at infinite height: `audit_markov_matching_finite`, `audit_markov_matching_zero`,
  `audit_markov_matching_finite_infinite` and `audit_markov_matching_zero_infinite`.

Conventions. Vertices of the binary tree are words in `List Bool`, whose letters `false` and
`true` stand for the paper's children `1` and `2`. Vertices of the `N`-ary tree are words over
`Fin N`, whose letters `0, …, N-1` stand for the paper's `1, …, N`. Laws of labels are `PMF`s,
and probabilities of events take values in `ℝ≥0∞`. Distances are Mathlib's graph distance
`SimpleGraph.dist`, which is the graph metric on the connected graphs used here.
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

/-! ## The i.i.d. matching theorem -/

/-- Theorem 5.1(1), the leaf bound (5.2). Let `μ` be a law on the vertex set of a graph `G`,
and call two labels compatible when they are equal or adjacent. If `η_{5/2}(μ) ≤ 1/256`, then
two independent leaf labellings of the binary tree of height `h`, each with i.i.d. labels of
law `μ`, admit no automorphism carrying every leaf to a leaf with a compatible label with
probability at most `(253/256)^h η_{5/2}(μ)`. The left side is this probability, written as
the expected mass of second labellings that the first labelling fails to match. -/
theorem audit_graph_leaf_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (h0 : potential (5 / 2) μ (compat G) ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * potential (5 / 2) μ (compat G) := sorry

/-- Theorem 5.1(2), the full bound (5.3) at finite height. In the setting of the leaf bound,
with every vertex labelled, `η_{5/2}(μ) ≤ 10⁻⁴` implies that two independent labellings of the
binary tree of height `h` admit no automorphism matching every vertex with probability at most
`16 η_{5/2}(μ)`, uniformly in `h`. -/
theorem audit_graph_full_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (hη : potential (5 / 2) μ (compat G) ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim (compat G) h) x
      ≤ 16 * potential (5 / 2) μ (compat G) := sorry

/-- Theorem 5.1(2) at infinite height. Let `R₀` be a reflexive symmetric compatibility
relation on a countable label set, which is compatibility in the graph joining distinct related
labels, and let `η_{5/2}(μ) ≤ 10⁻⁴`. There is a probability space carrying two sequences of
full labellings `X h`, `Y h` of all heights, each restricting to the previous one, such that
`(X h, Y h)` has the law of two independent labellings of height `h` with i.i.d. labels of law
`μ`. With probability at least `1 - 16 η_{5/2}(μ)`, there is one root-fixing automorphism `g`
of the infinite binary tree such that, at every vertex `s`, the label of `X` at `g s` is
compatible with the label of `Y` at `s`. -/
theorem audit_exists_infinite_tree_matching_graphAut {V : Type u} (μ : PMF V)
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hη : potential (5 / 2) μ R₀ ≤ 1 / 10000) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : (h : ℕ) → Ω → FullLab V h),
      (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
      (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
      (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
      (∀ h, P.map (fun ω => (X h ω, Y h ω))
        = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) ∧
      1 - 16 * potential (5 / 2) μ R₀ ≤ P {ω | ∃ g : List Bool ≃ List Bool, IsTreeAut g ∧
        ∀ s : List Bool, R₀ (coord (g s).length (X (g s).length ω) (g s))
          (coord s.length (Y s.length ω) s)} := sorry

/-! ## The finite class and the complete classification -/

/-- The finite class of Theorem 1.2, geometric input: a connected graph of bounded diameter is
quasi-isometric to the one-vertex graph. In particular, all finite trees are quasi-isometric to
one another. -/
theorem audit_bounded_graph_qi_point {V : Type u} (G : SimpleGraph V) (hconn : G.Connected)
    (hbdd : ∃ D : ℕ, ∀ x y, G.dist x y ≤ D) :
    GraphQuasiIsometric G (⊥ : SimpleGraph Unit) := sorry

/-- The finite class of Theorem 1.2, probabilistic input: an offspring distribution with mean
at most one, other than the deterministic single child `θ(1) = 1`, gives an almost surely
finite Galton–Watson tree. Hence only the laws admitted in Theorem 1.2 survive with positive
probability. -/
theorem audit_extinction_of_not_supercritical {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hmean : ¬ theta.IsSupercritical) (h1 : theta 1 ≠ 1) :
    ∀ᵐ c ∂(gwField (N := N) theta), ¬ gwSurvives c := sorry

/-- Theorem 1.2, including the finite class, over the unconditioned laws. Let `θ` and `θ'` be
finitely supported offspring distributions and consider the trees cut out by independent
offspring fields. Almost surely, a root-preserving quasi-isometry between the two trees exists
exactly when both trees are finite, or both are infinite and `SameInfiniteClass θ θ'` holds;
and any quasi-isometry, root-preserving or not, forces the same alternative. The paper
conditions both trees on infinite diameter; here that conditioning is expressed through the
survival events, and the laws are unrestricted. -/
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

/-- Theorem 1.3, mutual embeddability: a Galton–Watson tree with a finitely supported
supercritical offspring distribution, conditioned on infinite diameter, almost surely admits a
quasi-isometric embedding into the binary tree and receives one from it. The binary tree is
the parent–child graph of all words over a two-letter alphabet, and the conditioning is
expressed by quantifying over the surviving samples of the unconditioned law. -/
theorem audit_mutual_embeddability {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hsup : theta.IsSupercritical) :
    ∀ᵐ c ∂(gwField (N := N) theta), gwSurvives c →
      GraphQIEmbeddable (wordGraph (inGWSample c)) (wordGraph (fun _ : GWWord 2 => True)) ∧
      GraphQIEmbeddable (wordGraph (fun _ : GWWord 2 => True)) (wordGraph (inGWSample c)) := sorry

/-! ## Universality in the two-value family -/

/-- Theorem 1.4, almost-sure part. Let every vertex independently have two children with
probability `t` and one child otherwise. For every `t ∈ [0, 1]`, two independent such trees
almost surely admit a root-preserving quasi-isometry. -/
theorem audit_twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((bernoulliField ht0 ht1).prod (bernoulliField ht0 ht1))
      {ω | ¬ GraphQuasiIsometricRooted (wordGraph (InTree ω.1)) (wordGraph (InTree ω.2))
        ⟨[], InTree.root⟩ ⟨[], InTree.root⟩} = 0 := sorry

/-- Theorem 1.4, the rate (1.1). For `0 < t < 1` there is `D₀` such that, for every `D ≥ D₀`,
the probability that two independent trees of the two-value family admit no root-preserving
`(D² + 3)`-quasi-isometry is at most `256 √((1 - t)^(D(2D - 5)))`. For `D ≥ 3` this equals
`256 θ(1)^(D(D - 5/2))` with `θ(1) = 1 - t`, so the constant `C` of (1.1) is `256`. -/
theorem audit_twovalue_rate_tree {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ((bernoulliField ht0.le ht1.le).prod (bernoulliField ht0.le ht1.le))
          {ω | ¬ ∃ f : {w // InTree ω.1 w} → {w // InTree ω.2 w},
            GraphQIWith (D ^ 2 + 3) (wordGraph (InTree ω.1)) (wordGraph (InTree ω.2)) f ∧
              f ⟨[], InTree.root⟩ = ⟨[], InTree.root⟩}
        ≤ ENNReal.ofReal (256 * Real.sqrt ((1 - t) ^ (D * (2 * D - 5)))) := sorry

/-! ## The stopped Markov matching theorem -/

/-- Theorem 6.1, finite-type alternative at finite height. Fix `α ≥ 1` with `λ_α < 1` and
bounds `H`, `T ≥ 1` and `B ≥ 1`. There are constants `K` and `ε > 0`, depending only on
`α, H, T, B`, with the following property. Take any model with finitely many types and
reflexive symmetric compatibility, with a partition into cyclic classes of at most `T` types
each, transition sums `∑_{j ∈ supp P_t} P_t(j)^(-α) ≤ B`, conditions (M1) and (M2) with return
bound `H`, and `ζ_α ≤ ε`. Then two independent processes started at types of the same class
fail to match with probability at most `K ζ_α`, at every height. -/
theorem audit_markov_matching_finite {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1)
    (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Stopped.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Stopped.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      (∀ t, M.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t → ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := sorry

/-- Theorem 6.1, zero-compatible alternative at finite height. Fix `α ≥ 1` with `λ_α < 1`.
There are constants `K` and `ε > 0`, depending only on `α`, such that for every model with
reflexive symmetric compatibility, `δ = 0` (that is, `b(0) = 1`) and `ζ_α ≤ ε`, two independent
processes started at any two types fail to match with probability at most `K ζ_α`, at every
height. No finiteness, class or return hypothesis is imposed on the types. -/
theorem audit_markov_matching_zero {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Stopped.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := sorry

/-- Theorem 6.1, finite-type alternative at infinite height. Under the hypotheses of
`audit_markov_matching_finite`, with a countable state set, let `s` and `t` be types of the
same class. There is a probability space carrying two sequences of state labellings `X n`,
`Y n` of all heights, each restricting to the previous one, such that `(X n, Y n)` has the law
of two independent labellings of height `n` started at `s` and `t`. With probability at least
`1 - K ζ_α`, one root-fixing automorphism of the infinite binary tree matches their states at
every vertex. -/
theorem audit_markov_matching_finite_infinite {α : ℝ} (hα : 1 ≤ α)
    (hlam : Stopped.lambda α < 1) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V]
      (M : Stopped.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Stopped.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      (∀ t, M.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t →
      ∃ (Omega : Type) (_ : MeasurableSpace Omega) (P : Measure Omega)
        (_ : IsProbabilityMeasure P) (X Y : (n : ℕ) → Omega → FullLab V n),
        (∀ n omega, restrictLab n (X (n + 1) omega) = X n omega) ∧
        (∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega) ∧
        (∀ n, Measurable (fun omega => (X n omega, Y n omega))) ∧
        (∀ n, P.map (fun omega => (X n omega, Y n omega))
          = (prodPMF (M.rho s n) (M.rho t n)).toMeasure) ∧
        1 - ENNReal.ofReal Kc * M.zeta α
          ≤ P {omega | ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧
            ∀ w : List Bool, M.R
              (coord (aut w).length (X (aut w).length omega) (aut w))
              (coord w.length (Y w.length omega) w)} := sorry

/-- Theorem 6.1, zero-compatible alternative at infinite height. Under the hypotheses of
`audit_markov_matching_zero`, with countable state and type sets, the conclusion of
`audit_markov_matching_finite_infinite` holds for any two types `s` and `t`. -/
theorem audit_markov_matching_zero_infinite {α : ℝ} (hα : 1 ≤ α)
    (hlam : Stopped.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V] [Countable I] (M : Stopped.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t,
      ∃ (Omega : Type) (_ : MeasurableSpace Omega) (P : Measure Omega)
        (_ : IsProbabilityMeasure P) (X Y : (n : ℕ) → Omega → FullLab V n),
        (∀ n omega, restrictLab n (X (n + 1) omega) = X n omega) ∧
        (∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega) ∧
        (∀ n, Measurable (fun omega => (X n omega, Y n omega))) ∧
        (∀ n, P.map (fun omega => (X n omega, Y n omega))
          = (prodPMF (M.rho s n) (M.rho t n)).toMeasure) ∧
        1 - ENNReal.ofReal Kc * M.zeta α
          ≤ P {omega | ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧
            ∀ w : List Bool, M.R
              (coord (aut w).length (X (aut w).length omega) (aut w))
              (coord w.length (Y w.length omega) w)} := sorry

end Challenge
