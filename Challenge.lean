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

/-! ## The i.i.d. matching theorem -/

/-- `thm:matching`(1): the leaf bound. -/
theorem audit_graph_leaf_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (h0 : potential (5 / 2) μ (compat G) ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * potential (5 / 2) μ (compat G) := sorry

/-- `thm:matching`(2): the full bound. -/
theorem audit_graph_full_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (hη : potential (5 / 2) μ (compat G) ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim (compat G) h) x
      ≤ 16 * potential (5 / 2) μ (compat G) := sorry

/-- `thm:matching`, the infinite tree: the matching automorphism as a root-fixing
automorphism of the infinite binary tree. -/
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

/-- Bounded connected graphs form one quasi-isometry class: each is quasi-isometric to a
single vertex. -/
theorem audit_bounded_graph_qi_point {V : Type u} (G : SimpleGraph V) (hconn : G.Connected)
    (hbdd : ∃ D : ℕ, ∀ x y, G.dist x y ≤ D) :
    GraphQuasiIsometric G (⊥ : SimpleGraph Unit) := sorry

/-- A law with mean at most one dies out almost surely, unless it is the deterministic
single child `θ_1 = 1`. -/
theorem audit_extinction_of_not_supercritical {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hmean : ¬ theta.IsSupercritical) (h1 : theta 1 ≠ 1) :
    ∀ᵐ c ∂(gwField (N := N) theta), ¬ gwSurvives c := sorry

/-- `thm:trichotomy` in full: for two independent Galton--Watson trees with finitely supported
offspring laws, almost surely a root-preserving quasi-isometry exists exactly when both are
finite, or both are infinite and the two laws lie in the same infinite class, and otherwise no
quasi-isometry exists at all. -/
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

/-- `thm:embedding-hierarchy`: a Galton--Watson tree with a finitely supported supercritical
offspring law, conditioned on infinite diameter, almost surely admits quasi-isometric
embeddings into the binary tree and from it. The binary tree is the parent--child graph of
all words over a two-letter alphabet, and the conditioning is expressed by quantifying over
the surviving samples of the unconditioned law. -/
theorem audit_mutual_embeddability {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hsup : theta.IsSupercritical) :
    ∀ᵐ c ∂(gwField (N := N) theta), gwSurvives c →
      GraphQIEmbeddable (wordGraph (inGWSample c)) (wordGraph (fun _ : GWWord 2 => True)) ∧
      GraphQIEmbeddable (wordGraph (fun _ : GWWord 2 => True)) (wordGraph (inGWSample c)) := sorry

/-! ## Universality in the two-value family -/

/-- `thm:twovalue`: two independent Galton--Watson trees whose offspring law is
supported on `{1,2}` almost surely admit a root-preserving quasi-isometry. -/
theorem audit_twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((bernoulliField ht0 ht1).prod (bernoulliField ht0 ht1))
      {ω | ¬ GraphQuasiIsometricRooted (wordGraph (InTree ω.1)) (wordGraph (InTree ω.2))
        ⟨[], InTree.root⟩ ⟨[], InTree.root⟩} = 0 := sorry

/-- The quantitative half of `thm:twovalue`: above a threshold, failure of a root-preserving
`(D²+3)`-quasi-isometry has probability at most the explicit rate. -/
theorem audit_twovalue_rate_tree {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ((bernoulliField ht0.le ht1.le).prod (bernoulliField ht0.le ht1.le))
          {ω | ¬ ∃ f : {w // InTree ω.1 w} → {w // InTree ω.2 w},
            GraphQIWith (D ^ 2 + 3) (wordGraph (InTree ω.1)) (wordGraph (InTree ω.2)) f ∧
              f ⟨[], InTree.root⟩ = ⟨[], InTree.root⟩}
        ≤ ENNReal.ofReal (256 * Real.sqrt ((1 - t) ^ (D * (2 * D - 5)))) := sorry

/-! ## The stopped Markov matching theorem -/

/-- `thm:markov-matching`, finite alternative: under the exponent condition `λ_α < 1`,
there are constants `K`, `ε > 0` depending only on `α, H, T, B` such that every finite
model with type classes of size at most `T`, full-support transition inverse sums at most
`B`, fresh positivity and common returns within `H`, and one-site defect `ζ_α ≤ ε`, has
every same-class pair failing to match at every height with probability at most `K ζ_α`. -/
theorem audit_markov_matching_finite {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1)
    (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Stopped.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Stopped.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      (∀ t, M.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t → ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := sorry

/-- `thm:markov-matching`, zero-compatible alternative: under the exponent condition
`λ_α < 1`, there are constants `K`, `ε > 0` depending only on `α` such that every model
with `δ = 0` and `ζ_α ≤ ε` has every pair of types failing to match at every height with
probability at most `K ζ_α`. -/
theorem audit_markov_matching_zero {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Stopped.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := sorry

/-- `thm:markov-matching`, finite alternative at infinite height: two independent
consistent processes of same-class types admit one root-fixing infinite-tree
automorphism matching their states at every vertex with probability at least
`1 - K ζ_α`. -/
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

/-- `thm:markov-matching`, zero-compatible alternative at infinite height: two independent
consistent processes of any two types admit one root-fixing infinite-tree automorphism
matching their states at every vertex with probability at least `1 - K ζ_α`. -/
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
