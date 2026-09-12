/-
Headline statements for binary-tree matching and the quasi-isometry classification of
Galton--Watson trees. The statement vocabulary below depends only on Mathlib.
-/
import Mathlib

namespace Challenge

open scoped ENNReal Classical
open MeasureTheory

/-! ## Matching labels on the binary tree -/

/-- The product of two laws. -/
noncomputable def prodPMF {X Y : Type*} (μ : PMF X) (ν : PMF Y) : PMF (X × Y) :=
  μ.bind fun x => ν.map fun y => (x, y)

section Potential
variable {X : Type*}

/-- The good degree `r(x) = μ{y : x R y}`. -/
noncomputable def rE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then μ y else 0

/-- The bad degree `q(x) = μ{y : ¬ x R y}`. -/
noncomputable def qE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then 0 else μ y

/-- The bad degree as a real number, `q(x) = μ{y : ¬ x R y}`. -/
noncomputable def q (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ := (qE μ R x).toReal

/-- The weight `φ_α t = t / (1-t)^α`. -/
noncomputable def phi (α t : ℝ) : ℝ := t / (1 - t) ^ α

/-- The weight in `ℝ≥0∞`, infinite for `t ≥ 1`. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤

/-- The one-site potential `η_α = ∑ μ(x) φ_α(q(x))`. -/
noncomputable def potential (α : ℝ) (μ : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * phiE α (q μ R x)

end Potential

/-- Full labellings of the binary tree of height `n`. -/
def FullLab (S : Type*) : ℕ → Type _
  | 0 => S
  | n + 1 => S × (FullLab S n × FullLab S n)

section Iid
variable {V : Type*}

/-- Leaf labellings of the binary tree of height `h`. -/
def Leaf (V : Type*) : ℕ → Type _
  | 0 => V
  | h + 1 => Leaf V h × Leaf V h

/-- `Aut(𝔹_h)` as the swap group: a swap bit and the two subtree automorphisms. -/
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

/-- The i.i.d. leaf law. -/
noncomputable def leafMu (μ : PMF V) : (h : ℕ) → PMF (Leaf V h)
  | 0 => μ
  | h + 1 => prodPMF (leafMu μ h) (leafMu μ h)

/-- The i.i.d. full law. -/
noncomputable def fullMu (μ : PMF V) : (h : ℕ) → PMF (FullLab V h)
  | 0 => μ
  | h + 1 => prodPMF μ (prodPMF (fullMu μ h) (fullMu μ h))

/-- Compatibility in a label graph: `d_G(v,w) ≤ 1`. -/
def compat (G : SimpleGraph V) (v w : V) : Prop := v = w ∨ G.Adj v w

/-- Restriction of a height-`h+1` labelling to height `h`. -/
def restrictLab : (h : ℕ) → FullLab V (h + 1) → FullLab V h
  | 0, x => x.1
  | h + 1, x => (x.1, restrictLab h x.2.1, restrictLab h x.2.2)

/-- The label at the vertex addressed by a word. -/
def coord : (h : ℕ) → FullLab V h → List Bool → V
  | 0, x, _ => x
  | _ + 1, x, [] => x.1
  | h + 1, x, false :: t => coord h x.2.1 t
  | h + 1, x, true :: t => coord h x.2.2 t

/-- Adjacency in the infinite rooted binary tree, on words. -/
def treeAdj (s t : List Bool) : Prop := (∃ c, t = s ++ [c]) ∨ (∃ c, s = t ++ [c])

/-- A root-fixing automorphism of the infinite binary tree. -/
def IsTreeAut (g : List Bool ≃ List Bool) : Prop :=
  g [] = [] ∧ ∀ s t, treeAdj s t ↔ treeAdj (g s) (g t)

/-- Full labellings carry the product measurable structure. -/
instance instMeasurableFullLab {V : Type*} [MeasurableSpace V] :
    (h : ℕ) → MeasurableSpace (FullLab V h)
  | 0 => ‹MeasurableSpace V›
  | h + 1 =>
      let inst := instMeasurableFullLab (V := V) h
      @Prod.instMeasurableSpace V (FullLab V h × FullLab V h) _
        (@Prod.instMeasurableSpace (FullLab V h) (FullLab V h) inst inst)

end Iid

/-! ## Galton--Watson trees and quasi-isometry -/

/-- The parent–child graph of a set of words. -/
def wordGraph {A : Type*} (T : List A → Prop) : SimpleGraph {w // T w} :=
  SimpleGraph.fromRel fun u v => ∃ a, v.1 = u.1 ++ [a]

section Classification

/-- A finitely supported offspring distribution. -/
structure Offspring (J : ℕ) where
  pmf : PMF ℕ
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

/-- Membership in the tree cut out by an offspring-count field. -/
def inGWSample {N : ℕ} (c : GWWord N → ℕ) (v : GWWord N) : Prop :=
  ∀ i, (h : i < v.length) → ((v.get ⟨i, h⟩ : Fin N) : ℕ) < c (v.take i)

/-- Survival: the sample tree cut out by the offspring-count field `c` is infinite. -/
def gwSurvives {N : ℕ} (c : GWWord N → ℕ) : Prop :=
  {v | inGWSample c v}.Infinite

/-- The law of the i.i.d. offspring field. -/
noncomputable def gwField {J N : ℕ} (theta : Offspring J) : Measure (GWWord N → ℕ) :=
  Measure.infinitePi (fun _ : GWWord N => theta.pmf.toMeasure)

/-- The root of a sample, as a vertex of its tree. -/
def gwRoot {N : ℕ} (c : GWWord N → ℕ) : {w : GWWord N // inGWSample c w} :=
  ⟨[], fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- `GraphQIWith D G G' f`: `f` is a `D`-quasi-isometry from `G` to `G'` for connected graphs
with their graph metrics, with `D`-dense image. -/
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

/-- The shifted positive support generating the chain-regime invariant. -/
noncomputable def shiftSupp {J : ℕ} (theta : Offspring J) : Finset ℕ :=
  ((Finset.range (J + 1)).filter fun k => 2 ≤ k ∧ theta k ≠ 0).image fun k => k - 1

/-- Two laws lie in the same infinite class: both ray, both full tree, both chain with the
same branching semigroup, or both bushy. -/
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

/-- The i.i.d. field recording whether each vertex has two children (rather than one). -/
noncomputable def bernoulliField {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : Measure (Word → Bool) :=
  Measure.infinitePi (fun _ : Word =>
    ProbabilityTheory.bernoulliMeasure true false ⟨t, ht, ht1⟩)

end TwoValue

/-! ## Markov labels -/

namespace Stopped

/-- Types specify the child-type law and whether the state is drawn from `μ` or is `zero`. -/
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

/-- The state at a vertex of type `t`. -/
noncomputable def rootLaw (t : I) : PMF V :=
  if M.fresh t then M.μ else PMF.pure M.zero

/-- The state labelling law, with independent root state and child-type transition. -/
noncomputable def rho : I → (h : ℕ) → PMF (FullLab V h)
  | t, 0 => M.rootLaw t
  | t, h + 1 => (M.rootLaw t).bind fun v =>
      ((M.π t).bind fun j => prodPMF (rho j.1 h) (rho j.2 h)).map fun p => (v, p)

/-- Probability that two independent height-`h` processes cannot be matched. -/
noncomputable def failProb (s t : I) (h : ℕ) : ℝ≥0∞ :=
  ∑' x, M.rho s h x * qE (M.rho t h) (fullSim M.R h) x

/-- Incompatibility with the prescribed state, `δ = 1 − b(0)`. -/
noncomputable def delta : ℝ≥0∞ := qE M.μ M.R M.zero

/-- The defect `ζ_α = max{η_α, φ_α(δ)}`, infinite when `b(0)=0`. -/
noncomputable def zeta (α : ℝ) : ℝ≥0∞ :=
  max (potential α M.μ M.R) (phiE α M.delta.toReal)

/-- The cyclic classes: fresh types have class zero, and children have the next class. -/
structure Phase (M : Model V I) (g : ℕ) where
  θ : I → ZMod g
  fresh_zero : ∀ t, M.fresh t → θ t = 0
  child : ∀ t j, M.π t j ≠ 0 → θ j.1 = θ t + 1 ∧ θ j.2 = θ t + 1

/-- The number of types in a class. -/
noncomputable def Phase.count {M : Model V I} [Fintype I] {g : ℕ} (Θ : Phase M g)
    (i : ZMod g) : ℕ :=
  (Finset.univ.filter fun t => Θ.θ t = i).card

/-- A child type produced by a transition of positive probability. -/
def child (t t' : I) : Prop := ∃ j, M.π t j ≠ 0 ∧ (t' = j.1 ∨ t' = j.2)

/-- Types reachable from `t` after `n` transitions. -/
def reach (t : I) : ℕ → Set I
  | 0 => {t}
  | n + 1 => {u | ∃ s ∈ reach t n, M.child s u}

/-- Every possible source path has a fresh visit within `H` steps at which a possible
same-class target path also has a fresh visit (`it:markov-returns`). -/
def CommonReturns {g : ℕ} (Θ : Phase M g) (H : ℕ) : Prop :=
  ∀ s t, Θ.θ s = Θ.θ t → ∀ p : ℕ → I, p 0 = s →
    (∀ i < H, M.child (p i) (p (i + 1))) →
    ∃ n ≤ H, M.fresh (p n) ∧ ∃ u ∈ M.reach t n, M.fresh u

/-- Every positive-probability fresh labelling has positive matching degree against each
fresh type (`it:markov-positivity`). -/
def FreshPositive : Prop :=
  ∀ (h : ℕ) (s t : I) (x : FullLab V h), M.fresh s → M.fresh t → M.rho s h x ≠ 0 →
    rE (M.rho t h) (fullSim M.R h) x ≠ 0

/-- The full-support transition sum in the quantitative Markov theorem. -/
noncomputable def inverseSum [Fintype I] (α : ℝ) (t : I) : ℝ≥0∞ :=
  ∑ j ∈ Finset.univ.filter (fun j => M.π t j ≠ 0), (M.π t j) ^ (-α)

end Model

/-- The contraction coefficient `λ_α` of `eq:markov-exponent`. -/
noncomputable def lambda (α : ℝ) : ℝ :=
  2 * sInf ((fun β : ℝ =>
    sSup ((fun q : ℝ => q / (1 + q) ^ α + β * (1 - q) ^ α) '' Set.Icc 0 1) +
      α ^ α / (α + 1) ^ (α + 1) * (1 - β) ^ (α + 1)) '' Set.Icc 0 1)

end Stopped

end Challenge
