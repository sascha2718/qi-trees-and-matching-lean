/-
Comparator solution file: the headline theorems of `Challenge.lean`, proved.

This file repeats the challenge's definitions verbatim, so that the declarations
its statements use carry the same names and the same bodies as the challenge's,
and then discharges each theorem from the libraries. Comparator compares the two
exported environments declaration by declaration; the challenge is never imported.
-/
import GraphMarkovMatching.Stopped.Main
import GraphMatching.Graph
import GraphMatching.Kolmogorov
import GraphMatching.AutBridge
import ChainClasses.Classification
import ChainClasses.TwoValue

universe u

namespace Challenge

open scoped ENNReal Classical
open MeasureTheory

/-! ## Shared notions -/

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

noncomputable def q (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ := (qE μ R x).toReal

/-- The weight `φ_α t = t / (1-t)^α`. -/
noncomputable def phi (α t : ℝ) : ℝ := t / (1 - t) ^ α

/-- The weight in `ℝ≥0∞`, infinite for `t ≥ 1`. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤

/-- The directed potential `Φ_α(μ → ν; R) = ∑_x μ(x) φ_α(q_ν(x))`. -/
noncomputable def PhiD (α : ℝ) (μ ν : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * phiE α (q ν R x)

end Potential

/-! ## The tree-indexed process -/

section Process
variable {S : Type*}

/-- Full labellings of the binary tree of height `n`. -/
def FullLab (S : Type*) : ℕ → Type _
  | 0 => S
  | n + 1 => S × (FullLab S n × FullLab S n)

def leaf (s : S) : FullLab S 0 := s

def branch {n : ℕ} (s : S) (p : FullLab S n × FullLab S n) : FullLab S (n + 1) := (s, p.1, p.2)

/-- The law of the height-`n` sample rooted at `s`, for the kernel `P`. -/
noncomputable def muM (P : S → PMF (S × S)) : S → (n : ℕ) → PMF (FullLab S n)
  | s, 0 => PMF.pure (leaf s)
  | s, n + 1 => ((P s).bind fun στ => prodPMF (muM P στ.1 n) (muM P στ.2 n)).map (branch s)

/-- `AutK k m n`: the restricted automorphism group of the height-`n` tree when the
root sits at swap distance `m`; a swap bit is available exactly at distance `0`. -/
def AutK (k : ℕ) : ℕ → ℕ → Type
  | _, 0 => Unit
  | 0, n + 1 => Bool × AutK k (k - 1) n × AutK k (k - 1) n
  | m + 1, n + 1 => AutK k m n × AutK k m n

def fullMatchesK (R₀ : S → S → Prop) (k : ℕ) :
    (m : ℕ) → (n : ℕ) → AutK k m n → FullLab S n → FullLab S n → Prop
  | _, 0, _, x, y => R₀ x y
  | 0, n + 1, π, x, y =>
      R₀ x.1 y.1
        ∧ fullMatchesK R₀ k (k - 1) n π.2.1 x.2.1 (bif π.1 then y.2.2 else y.2.1)
        ∧ fullMatchesK R₀ k (k - 1) n π.2.2 x.2.2 (bif π.1 then y.2.1 else y.2.2)
  | m + 1, n + 1, π, x, y =>
      R₀ x.1 y.1
        ∧ fullMatchesK R₀ k m n π.1 x.2.1 y.2.1
        ∧ fullMatchesK R₀ k m n π.2 x.2.2 y.2.2

def fullSimK (R₀ : S → S → Prop) (k m n : ℕ) (x y : FullLab S n) : Prop :=
  ∃ π : AutK k m n, fullMatchesK R₀ k m n π x y

/-- Matching of two height-`n` labellings by an automorphism of the tree. -/
def fullSim (R₀ : S → S → Prop) (n : ℕ) : FullLab S n → FullLab S n → Prop :=
  fullSimK R₀ 1 0 n

end Process

/-! ## The i.i.d. label field on the binary tree -/

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

def matchesA (R₀ : V → V → Prop) : (h : ℕ) → Aut h → Leaf V h → Leaf V h → Prop
  | 0, _, x, y => R₀ x y
  | h + 1, π, x, y =>
      matchesA R₀ h π.2.1 x.1 (bif π.1 then y.2 else y.1)
        ∧ matchesA R₀ h π.2.2 x.2 (bif π.1 then y.1 else y.2)

/-- Two leaf labellings are matched by some automorphism of the tree. -/
def leafSim (R₀ : V → V → Prop) (h : ℕ) (x y : Leaf V h) : Prop :=
  ∃ π : Aut h, matchesA R₀ h π x y

def fullMatchesA (R₀ : V → V → Prop) : (h : ℕ) → Aut h → FullLab V h → FullLab V h → Prop
  | 0, _, x, y => R₀ x y
  | h + 1, π, x, y =>
      R₀ x.1 y.1
        ∧ fullMatchesA R₀ h π.2.1 x.2.1 (bif π.1 then y.2.2 else y.2.1)
        ∧ fullMatchesA R₀ h π.2.2 x.2.2 (bif π.1 then y.2.1 else y.2.2)

/-- Two full labellings are matched at every vertex by some automorphism. -/
def fullSimIid (R₀ : V → V → Prop) (h : ℕ) (x y : FullLab V h) : Prop :=
  ∃ π : Aut h, fullMatchesA R₀ h π x y

/-- The i.i.d. leaf law. -/
noncomputable def leafMu (μ : PMF V) : (h : ℕ) → PMF (Leaf V h)
  | 0 => μ
  | h + 1 => prodPMF (leafMu μ h) (leafMu μ h)

/-- The i.i.d. full law. -/
noncomputable def fullMu (μ : PMF V) : (h : ℕ) → PMF (FullLab V h)
  | 0 => μ
  | h + 1 => prodPMF μ (prodPMF (fullMu μ h) (fullMu μ h))

/-- The one-site potential `Φ(R,μ) = 𝔼 φ_{5/2}(q(X))`. -/
noncomputable def PhiIid (μ : PMF V) (R : V → V → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * ENNReal.ofReal (phi (5 / 2) (q μ R x))

/-- Compatibility in a label graph: `d_G(v,w) ≤ 1`. -/
def compat (G : SimpleGraph V) (v w : V) : Prop := v = w ∨ G.Adj v w

/-- The compatible mass `b(v) = μ(B_G(v,1))`. -/
noncomputable def gdeg (μ : PMF V) (G : SimpleGraph V) (v : V) : ℝ :=
  (rE μ (compat G) v).toReal

/-- The graph potential `η_{G,5/2}(μ) = ∑_v μ(v) (1-b(v))/b(v)^{5/2}`. -/
noncomputable def etaGraph (μ : PMF V) (G : SimpleGraph V) : ℝ≥0∞ :=
  ∑' v, μ v * ENNReal.ofReal ((1 - gdeg μ G v) / gdeg μ G v ^ (5 / 2 : ℝ))

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

/-! ## Conditioned Galton--Watson trees and their coarse classes -/

section Classification

/-- A finitely supported offspring distribution. -/
structure Offspring (J : ℕ) where
  pmf : PMF ℕ
  vanishing : ∀ j, J < j → pmf j = 0

instance {J : ℕ} : CoeFun (Offspring J) (fun _ => ℕ → ℝ) :=
  ⟨fun theta j => (theta.pmf j).toReal⟩

namespace Offspring

noncomputable def mean {J : ℕ} (theta : Offspring J) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), (j : ℝ) * theta j

def IsSupercritical {J : ℕ} (theta : Offspring J) : Prop := 1 < theta.mean

end Offspring

abbrev GWWord (N : ℕ) : Type := List (Fin N)

/-- Membership in the tree cut out by an offspring-count field. -/
def inGWSample {N : ℕ} (c : GWWord N → ℕ) (v : GWWord N) : Prop :=
  ∀ i, (h : i < v.length) → ((v.get ⟨i, h⟩ : Fin N) : ℕ) < c (v.take i)

def gwSurvives {N : ℕ} (c : GWWord N → ℕ) : Prop :=
  {v | inGWSample c v}.Infinite

/-- The i.i.d. offspring field and its law conditioned on an infinite sample. -/
noncomputable def gwField {J N : ℕ} (theta : Offspring J) : Measure (GWWord N → ℕ) :=
  Measure.infinitePi (fun _ : GWWord N => theta.pmf.toMeasure)

def wedgeN {N : ℕ} : GWWord N → GWWord N → GWWord N
  | [], _ => []
  | _, [] => []
  | a :: v, b :: w => if a = b then a :: wedgeN v w else []

def treeDistN {N : ℕ} (v w : GWWord N) : ℕ :=
  v.length + w.length - 2 * (wedgeN v w).length

/-- The root of a sample, as a vertex of its tree. -/
def gwRoot {N : ℕ} (c : GWWord N → ℕ) : {w : GWWord N // inGWSample c w} :=
  ⟨[], fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The parent--child graph of a Galton--Watson sample. -/
def gwTreeGraph {N : ℕ} (c : GWWord N → ℕ) :
    SimpleGraph {w : GWWord N // inGWSample c w} :=
  SimpleGraph.fromRel fun u v => treeDistN u.1 v.1 = 1

structure GraphQIWith {V V' : Type*} (D : ℕ) (G : SimpleGraph V)
    (G' : SimpleGraph V') (f : V → V') : Prop where
  upper : ∀ x y, G'.dist (f x) (f y) ≤ D * G.dist x y + D
  lower : ∀ x y, G.dist x y ≤ D * G'.dist (f x) (f y) + D * D
  dense : ∀ y', ∃ x, G'.dist (f x) y' ≤ D

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

/-! ## Bridge for the conditioned classification block -/

def offspringToLib {J : ℕ} (theta : Offspring J) : BranchingProcess.Offspring J where
  mass := fun j => (theta.pmf j).toReal
  nonneg := fun j => ENNReal.toReal_nonneg
  vanishing := by
    intro j hj
    simp [theta.vanishing j hj]
  total := by
    have hzero : ∀ j ∉ Finset.range (J + 1), theta.pmf j = 0 := by
      intro j hj
      exact theta.vanishing j (by simpa using hj)
    have hsum : ∑ j ∈ Finset.range (J + 1), theta.pmf j = 1 := by
      calc
        ∑ j ∈ Finset.range (J + 1), theta.pmf j = ∑' j, theta.pmf j :=
          (tsum_eq_sum hzero).symm
        _ = 1 := theta.pmf.tsum_coe
    calc
      ∑ j ∈ Finset.range (J + 1), (theta.pmf j).toReal =
          ENNReal.toReal (∑ j ∈ Finset.range (J + 1), theta.pmf j) :=
        (ENNReal.toReal_sum (fun j _ => theta.pmf.apply_ne_top j)).symm
      _ = 1 := by rw [hsum]; simp

@[simp] lemma offspringToLib_apply {J : ℕ} (theta : Offspring J) (j : ℕ) :
    offspringToLib theta j = theta j := rfl

lemma offspringSupercritical_iff {J : ℕ} (theta : Offspring J) :
    theta.IsSupercritical ↔ (offspringToLib theta).IsSupercritical := Iff.rfl

lemma offspringPMF_eq {J : ℕ} (theta : Offspring J) :
    (offspringToLib theta).toPMF = theta.pmf := by
  ext j
  exact ENNReal.ofReal_toReal (theta.pmf.apply_ne_top j)

lemma offspringLaw_eq {J : ℕ} (theta : Offspring J) :
    theta.pmf.toMeasure = (offspringToLib theta).law := by
  rw [BranchingProcess.Offspring.law, offspringPMF_eq]

lemma gwField_eq {J N : ℕ} (theta : Offspring J) :
    gwField (N := N) theta = BranchingProcess.sampleMeasure (N := N) (offspringToLib theta) := by
  simp only [gwField, BranchingProcess.sampleMeasure, BranchingProcess.fieldMeasure,
    offspringLaw_eq]

lemma inGWSample_iff {N : ℕ} (c : GWWord N → ℕ) (w : GWWord N) :
    inGWSample c w ↔ w ∈ BranchingProcess.sample c := Iff.rfl

lemma gwSurvives_iff {N : ℕ} (c : GWWord N → ℕ) :
    gwSurvives c ↔ BranchingProcess.Survives c := Iff.rfl

lemma wedgeN_eq {N : ℕ} : ∀ v w : GWWord N,
    wedgeN v w = BranchingProcess.wedge v w
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: v, b :: w => by
      simp only [wedgeN, BranchingProcess.wedge, wedgeN_eq v w]

lemma treeDistN_eq {N : ℕ} (v w : GWWord N) :
    treeDistN v w = BranchingProcess.treeDist v w := by
  simp [treeDistN, BranchingProcess.treeDist, wedgeN_eq]

lemma gwTreeGraph_eq {N : ℕ} (c : GWWord N → ℕ) :
    gwTreeGraph c = ChainClasses.wordGraphN (fun w => w ∈ BranchingProcess.sample c) := by
  ext u v
  change u ≠ v ∧ (treeDistN u.1 v.1 = 1 ∨ treeDistN v.1 u.1 = 1) ↔
    BranchingProcess.treeDist u.1 v.1 = 1
  rw [treeDistN_eq, treeDistN_eq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rwa [BranchingProcess.treeDist_comm] at h
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro huv
    subst v
    rw [BranchingProcess.treeDist_self] at h
    omega

lemma graphQIWith_iff {V V' : Type*} (D : ℕ) (G : SimpleGraph V)
    (G' : SimpleGraph V') (f : V → V') :
    GraphQIWith D G G' f ↔ BranchingProcess.IsQIWith D G G' f := by
  constructor <;> rintro ⟨hup, hlo, hden⟩ <;> exact ⟨hup, hlo, hden⟩

lemma graphQuasiIsometric_iff {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V') :
    GraphQuasiIsometric G G' ↔ BranchingProcess.QuasiIsometric G G' := by
  constructor
  · rintro ⟨D, f, hf⟩
    exact ⟨D, f, (graphQIWith_iff D G G' f).1 hf⟩
  · rintro ⟨D, f, hf⟩
    exact ⟨D, f, (graphQIWith_iff D G G' f).2 hf⟩

lemma shiftSupp_eq {J : ℕ} (theta : Offspring J) :
    shiftSupp theta = ChainClasses.shiftSupp (offspringToLib theta) := rfl

/-! ## The two-value family -/

section TwoValue

/-- Vertices of the binary tree, as words over `Bool`. -/
abbrev Word : Type := List Bool

/-- The common prefix of two words. -/
def wedge : Word → Word → Word
  | [], _ => []
  | _, [] => []
  | a :: x, b :: y => if a = b then a :: wedge x y else []

/-- The tree distance: `|x| + |y| - 2|x ∧ y|`. -/
def treeDist (x y : Word) : ℕ := x.length + y.length - 2 * (wedge x y).length

/-- The sample tree of the offspring field `χ`: the root, one child `v·1` always,
and a second child `v·2` exactly when `χ v = true`. -/
inductive InTree (χ : Word → Bool) : Word → Prop
  | root : InTree χ []
  | one {v : Word} : InTree χ v → InTree χ (v ++ [false])
  | two {v : Word} : InTree χ v → χ v = true → InTree χ (v ++ [true])

/-- A `K`-quasi-isometry between two subtrees. -/
structure IsQIWith (K : ℕ) (T T' : Word → Prop) (f : Word → Word) : Prop where
  maps : ∀ x, T x → T' (f x)
  upper : ∀ x y, T x → T y → treeDist (f x) (f y) ≤ K * treeDist x y + K
  lower : ∀ x y, T x → T y → treeDist x y ≤ K * treeDist (f x) (f y) + K * K
  dense : ∀ y', T' y' → ∃ x, T x ∧ treeDist (f x) y' ≤ K

/-- The Bernoulli law on `Bool` with success probability `t`. -/
noncomputable def bernoulliLaw {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false ⟨t, ht, ht1⟩

/-- The i.i.d. Bernoulli field indexed by the vertices of the tree. -/
noncomputable def bernoulliField {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : Measure (Word → Bool) :=
  Measure.infinitePi (fun _ : Word => bernoulliLaw ht ht1)

/-- The square-root form of the quantitative two-value error rate. -/
noncomputable def qBound (a : ℝ) (D : ℕ) : ℝ :=
  Real.sqrt (a ^ (D * (2 * D - 5)))

end TwoValue

/-! ## Bridge to the library -/

/-- The challenge's product law is the library's. -/
lemma prodPMF_eq {X Y : Type*} (μ : PMF X) (ν : PMF Y) :
    prodPMF μ ν = GraphMarkovMatching.Support.prodPMF μ ν := by
  ext p
  show (μ.bind fun x => ν.map fun y => (x, y)) p = μ p.1 * ν p.2
  rw [PMF.bind_apply, tsum_eq_single p.1]
  · rw [PMF.map_apply, tsum_eq_single p.2]
    · simp
    · intro b hb
      exact if_neg (by simp [Prod.ext_iff, Ne.symm hb])
  · intro a ha
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ ?_
    refine (tsum_congr fun y => ?_).trans tsum_zero
    exact if_neg (by simp [Prod.ext_iff]; intro h; exact absurd h.symm ha)


/-- The challenge's labelling type is the library's, coordinatewise. -/
def toLib (S : Type u) : (n : ℕ) → FullLab S n ≃ GraphMarkovMatching.Support.FullLab S n
  | 0 => Equiv.refl S
  | n + 1 => Equiv.prodCongr (Equiv.refl S) (Equiv.prodCongr (toLib S n) (toLib S n))

/-- The challenge's automorphism group is the library's. -/
def autToLib (k : ℕ) : (m n : ℕ) → AutK k m n ≃ GraphMarkovMatching.Support.AutK k m n
  | _, 0 => Equiv.refl Unit
  | 0, n + 1 => Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.prodCongr (autToLib k (k - 1) n) (autToLib k (k - 1) n))
  | m + 1, n + 1 => Equiv.prodCongr (autToLib k m n) (autToLib k m n)

@[simp] lemma toLib_succ_apply (S : Type u) (n : ℕ) (a : S) (l r : FullLab S n) :
    toLib S (n + 1) (a, l, r) = (a, toLib S n l, toLib S n r) := rfl

@[simp] lemma toLib_succ_symm_apply (S : Type u) (n : ℕ) (a : S)
    (l r : GraphMarkovMatching.Support.FullLab S n) :
    (toLib S (n + 1)).symm (a, l, r) =
      (a, (toLib S n).symm l, (toLib S n).symm r) := rfl

@[simp] lemma autToLib_zero_succ_apply (k n : ℕ) (b : Bool) (l r : AutK k (k - 1) n) :
    autToLib k 0 (n + 1) (b, l, r) = (b, autToLib k (k - 1) n l, autToLib k (k - 1) n r) := rfl

@[simp] lemma autToLib_succ_succ_apply (k m n : ℕ) (l r : AutK k m n) :
    autToLib k (m + 1) (n + 1) (l, r) = (autToLib k m n l, autToLib k m n r) := rfl

open GraphMarkovMatching in
/-- Matching under an automorphism transports along the two equivalences. -/
lemma fullMatchesK_iff {S : Type u} (R : S → S → Prop) (k : ℕ) :
    ∀ (m n : ℕ) (π : AutK k m n) (x y : FullLab S n),
      fullMatchesK R k m n π x y ↔
        Support.fullMatchesK R k m n (autToLib k m n π) (toLib S n x) (toLib S n y)
  | _, 0, _, _, _ => Iff.rfl
  | 0, n + 1, π, x, y => by
      obtain ⟨b, πl, πr⟩ := π
      obtain ⟨xr, xl, xrr⟩ := x
      obtain ⟨yr, yl, yrr⟩ := y
      cases b <;>
        simp [fullMatchesK, Support.fullMatchesK, fullMatchesK_iff R k (k - 1) n]
  | m + 1, n + 1, π, x, y => by
      obtain ⟨πl, πr⟩ := π
      obtain ⟨xr, xl, xrr⟩ := x
      obtain ⟨yr, yl, yrr⟩ := y
      simp [fullMatchesK, Support.fullMatchesK, fullMatchesK_iff R k m n]

/-- The challenge's matching relation is the library's, along `toLib`. -/
lemma fullSim_iff {S : Type u} (R : S → S → Prop) (n : ℕ) (x y : FullLab S n) :
    fullSim R n x y ↔ GraphMarkovMatching.fullSim R n (toLib S n x) (toLib S n y) := by
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨autToLib 1 0 n π, (fullMatchesK_iff R 1 0 n π x y).1 hπ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨(autToLib 1 0 n).symm σ, ?_⟩
    rw [fullMatchesK_iff R 1 0 n]
    simpa using hσ


/-- Mapping a product law coordinatewise. -/
lemma map_prodPMF {X Y X' Y' : Type*} (μ : PMF X) (ν : PMF Y) (f : X → X') (g : Y → Y') :
    (prodPMF μ ν).map (Prod.map f g) = prodPMF (μ.map f) (ν.map g) := by
  simp [prodPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

/-- The challenge's process law is the library's, along `toLib`. -/
lemma muM_eq {S : Type u} (P : S → PMF (S × S)) (s : S) :
    ∀ n, (muM P s n).map (toLib S n) = GraphMarkovMatching.muM P s n
  | 0 => by
      simp only [muM, GraphMarkovMatching.muM, PMF.pure_map]
      rfl
  | n + 1 => by
      have hl : ∀ t : S, (muM P t n).map (toLib S n) = GraphMarkovMatching.muM P t n :=
        fun t => muM_eq P t n
      simp only [muM, GraphMarkovMatching.muM, PMF.map_bind, PMF.map_comp, Function.comp_def]
      congr 1
      funext στ
      rw [show (fun p : FullLab S n × FullLab S n => toLib S (n + 1) (branch s p))
            = (fun p => GraphMarkovMatching.branch s p) ∘ Prod.map (toLib S n) (toLib S n) from rfl,
        ← PMF.map_comp, map_prodPMF, hl στ.1, hl στ.2, prodPMF_eq]

/-- Restriction of labellings commutes with the Markov-library transport. -/
lemma restrictLab_toLib_process {S : Type u} :
    ∀ (n : ℕ) (x : FullLab S (n + 1)),
      toLib S n (restrictLab n x) =
        GraphMarkovMatching.Support.restrictLab n (toLib S (n + 1) x)
  | 0, _ => rfl
  | n + 1, x => by
      obtain ⟨a, l, r⟩ := x
      simp [restrictLab, GraphMarkovMatching.Support.restrictLab,
        restrictLab_toLib_process n]

/-- The transport of Markov full labellings and its inverse are measurable. -/
lemma measurable_toLib_process {S : Type u} [MeasurableSpace S] :
    ∀ n, Measurable (toLib S n)
  | 0 => measurable_id
  | n + 1 => by
      have h := measurable_toLib_process (S := S) n
      exact (measurable_fst.prodMk
        (((h.comp measurable_fst).comp measurable_snd).prodMk
          ((h.comp measurable_snd).comp measurable_snd)))

lemma measurable_toLib_process_symm {S : Type u} [MeasurableSpace S] :
    ∀ n, Measurable (toLib S n).symm
  | 0 => measurable_id
  | n + 1 => by
      have h := measurable_toLib_process_symm (S := S) n
      exact (measurable_fst.prodMk
        (((h.comp measurable_fst).comp measurable_snd).prodMk
          ((h.comp measurable_snd).comp measurable_snd)))

/-! ### The full-group Markov tower as a graph automorphism -/

def supportFullToGraph (S : Type u) :
    (n : ℕ) → GraphMarkovMatching.Support.FullLab S n ≃ GraphMatching.FullLab S n
  | 0 => Equiv.refl S
  | n + 1 => Equiv.prodCongr (Equiv.refl S)
      (Equiv.prodCongr (supportFullToGraph S n) (supportFullToGraph S n))

def supportAutToGraph :
    (n : ℕ) → GraphMarkovMatching.Support.AutK 1 0 n ≃ GraphMatching.Aut n
  | 0 => Equiv.refl Unit
  | n + 1 => Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.prodCongr (supportAutToGraph n) (supportAutToGraph n))

@[simp] lemma supportFullToGraph_succ_apply (S : Type u) (n : ℕ) (a : S)
    (l r : GraphMarkovMatching.Support.FullLab S n) :
    supportFullToGraph S (n + 1) (a, l, r) =
      (a, supportFullToGraph S n l, supportFullToGraph S n r) := rfl

@[simp] lemma supportAutToGraph_succ_apply (n : ℕ) (b : Bool)
    (l r : GraphMarkovMatching.Support.AutK 1 0 n) :
    supportAutToGraph (n + 1) (b, l, r) =
      (b, supportAutToGraph n l, supportAutToGraph n r) := rfl

lemma supportRestrictLab_toGraph {S : Type u} :
    ∀ (n : ℕ) (x : GraphMarkovMatching.Support.FullLab S (n + 1)),
      supportFullToGraph S n (GraphMarkovMatching.Support.restrictLab n x) =
        GraphMatching.restrictLab n (supportFullToGraph S (n + 1) x)
  | 0, _ => rfl
  | n + 1, x => by
      obtain ⟨a, l, r⟩ := x
      simp only [GraphMarkovMatching.Support.restrictLab,
        supportFullToGraph_succ_apply, GraphMatching.restrictLab]
      rw [supportRestrictLab_toGraph n, supportRestrictLab_toGraph n]

lemma supportRestrictAut_toGraph :
    ∀ (n : ℕ) (π : GraphMarkovMatching.Support.AutK 1 0 (n + 1)),
      supportAutToGraph n (GraphMarkovMatching.Support.restrictAutK 1 0 n π) =
        GraphMatching.restrictAut n (supportAutToGraph (n + 1) π)
  | 0, _ => rfl
  | n + 1, π => by
      obtain ⟨b, l, r⟩ := π
      simp only [GraphMarkovMatching.Support.restrictAutK,
        supportAutToGraph_succ_apply, GraphMatching.restrictAut]
      rw [supportRestrictAut_toGraph n, supportRestrictAut_toGraph n]

lemma supportMatches_toGraph {S : Type u} (R : S → S → Prop) :
    ∀ (n : ℕ) (π : GraphMarkovMatching.Support.AutK 1 0 n)
      (x y : GraphMarkovMatching.Support.FullLab S n),
      GraphMarkovMatching.Support.fullMatchesK R 1 0 n π x y ↔
        GraphMatching.fullMatchesA R n (supportAutToGraph n π)
          (supportFullToGraph S n x) (supportFullToGraph S n y)
  | 0, _, _, _ => Iff.rfl
  | n + 1, π, x, y => by
      obtain ⟨b, πl, πr⟩ := π
      change GraphMarkovMatching.Support.AutK 1 0 n at πl πr
      obtain ⟨xa, xl, xr⟩ := x
      obtain ⟨ya, yl, yr⟩ := y
      cases b <;>
        simp only [GraphMarkovMatching.Support.fullMatchesK,
          supportAutToGraph_succ_apply, supportFullToGraph_succ_apply,
          GraphMatching.fullMatchesA, supportMatches_toGraph R n] <;> simp

lemma supportInfMatch_toGraph {S : Type u} (R : S → S → Prop)
    (X Y : (n : ℕ) → GraphMarkovMatching.Support.FullLab S n)
    (h : GraphMarkovMatching.InfMatch R X Y) :
    GraphMatching.InfMatch R (fun n => supportFullToGraph S n (X n))
      (fun n => supportFullToGraph S n (Y n)) := by
  obtain ⟨σ, hcompat, hmatch⟩ := h
  refine ⟨fun n => supportAutToGraph n (σ n), fun n => ?_, fun n => ?_⟩
  · rw [← supportRestrictAut_toGraph, hcompat]
  · exact (supportMatches_toGraph R n (σ n) (X n) (Y n)).1 (hmatch n)

lemma coord_supportToGraph {S : Type u} :
    ∀ (n : ℕ) (x : GraphMarkovMatching.Support.FullLab S n) (w : List Bool),
      coord n ((toLib S n).symm x) w =
        GraphMatching.coord n (supportFullToGraph S n x) w
  | 0, _, _ => rfl
  | n + 1, x, [] => rfl
  | n + 1, x, false :: w => by
      obtain ⟨a, l, r⟩ := x
      simpa only [toLib_succ_symm_apply, coord, supportFullToGraph_succ_apply,
        GraphMatching.coord] using
        coord_supportToGraph n l w
  | n + 1, x, true :: w => by
      obtain ⟨a, l, r⟩ := x
      simpa only [toLib_succ_symm_apply, coord, supportFullToGraph_succ_apply,
        GraphMatching.coord] using
        coord_supportToGraph n r w

/-! ## Bridge for the i.i.d. block -/

/-- The challenge's leaf type is the library's. -/
def leafToLib (S : Type u) : (n : ℕ) → Leaf S n ≃ GraphMatching.Leaf S n
  | 0 => Equiv.refl S
  | n + 1 => Equiv.prodCongr (leafToLib S n) (leafToLib S n)

/-- The challenge's full-labelling type is the i.i.d. library's. -/
def fullToLib (S : Type u) : (n : ℕ) → FullLab S n ≃ GraphMatching.FullLab S n
  | 0 => Equiv.refl S
  | n + 1 => Equiv.prodCongr (Equiv.refl S) (Equiv.prodCongr (fullToLib S n) (fullToLib S n))

/-- The challenge's swap group is the library's. -/
def autToLibIid : (n : ℕ) → Aut n ≃ GraphMatching.Aut n
  | 0 => Equiv.refl Unit
  | n + 1 => Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.prodCongr (autToLibIid n) (autToLibIid n))

@[simp] lemma leafToLib_succ_apply (S : Type u) (n : ℕ) (l r : Leaf S n) :
    leafToLib S (n + 1) (l, r) = (leafToLib S n l, leafToLib S n r) := rfl

@[simp] lemma fullToLib_succ_apply (S : Type u) (n : ℕ) (a : S) (l r : FullLab S n) :
    fullToLib S (n + 1) (a, l, r) = (a, fullToLib S n l, fullToLib S n r) := rfl

@[simp] lemma autToLibIid_succ_apply (n : ℕ) (b : Bool) (l r : Aut n) :
    autToLibIid (n + 1) (b, l, r) = (b, autToLibIid n l, autToLibIid n r) := rfl

lemma matchesA_iff {S : Type u} (R : S → S → Prop) :
    ∀ (n : ℕ) (π : Aut n) (x y : Leaf S n),
      matchesA R n π x y ↔
        GraphMatching.matchesA R n (autToLibIid n π) (leafToLib S n x) (leafToLib S n y)
  | 0, _, _, _ => Iff.rfl
  | n + 1, π, x, y => by
      obtain ⟨b, πl, πr⟩ := π
      obtain ⟨xl, xr⟩ := x
      obtain ⟨yl, yr⟩ := y
      cases b <;> simp [matchesA, GraphMatching.matchesA, matchesA_iff R n]

lemma fullMatchesA_iff {S : Type u} (R : S → S → Prop) :
    ∀ (n : ℕ) (π : Aut n) (x y : FullLab S n),
      fullMatchesA R n π x y ↔
        GraphMatching.fullMatchesA R n (autToLibIid n π) (fullToLib S n x) (fullToLib S n y)
  | 0, _, _, _ => Iff.rfl
  | n + 1, π, x, y => by
      obtain ⟨b, πl, πr⟩ := π
      obtain ⟨xa, xl, xr⟩ := x
      obtain ⟨ya, yl, yr⟩ := y
      cases b <;> simp [fullMatchesA, GraphMatching.fullMatchesA, fullMatchesA_iff R n]

lemma leafSim_iff {S : Type u} (R : S → S → Prop) (n : ℕ) (x y : Leaf S n) :
    leafSim R n x y ↔ GraphMatching.leafSim R n (leafToLib S n x) (leafToLib S n y) := by
  constructor
  · rintro ⟨π, hπ⟩; exact ⟨autToLibIid n π, (matchesA_iff R n π x y).1 hπ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨(autToLibIid n).symm σ, ?_⟩
    rw [matchesA_iff R n]; simpa using hσ

lemma fullSimIid_iff {S : Type u} (R : S → S → Prop) (n : ℕ) (x y : FullLab S n) :
    fullSimIid R n x y ↔ GraphMatching.fullSim R n (fullToLib S n x) (fullToLib S n y) := by
  constructor
  · rintro ⟨π, hπ⟩; exact ⟨autToLibIid n π, (fullMatchesA_iff R n π x y).1 hπ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨(autToLibIid n).symm σ, ?_⟩
    rw [fullMatchesA_iff R n]; simpa using hσ

lemma prodPMF_eq_iid {X Y : Type*} (μ : PMF X) (ν : PMF Y) :
    prodPMF μ ν = GraphMatching.prodPMF μ ν := by
  ext p
  show (μ.bind fun x => ν.map fun y => (x, y)) p = μ p.1 * ν p.2
  rw [PMF.bind_apply, tsum_eq_single p.1]
  · rw [PMF.map_apply, tsum_eq_single p.2]
    · simp
    · intro b hb
      exact if_neg (by simp [Prod.ext_iff, Ne.symm hb])
  · intro a ha
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ ?_
    refine (tsum_congr fun y => ?_).trans tsum_zero
    exact if_neg (by simp [Prod.ext_iff]; intro h; exact absurd h.symm ha)

lemma leafMu_eq {V : Type u} (μ : PMF V) :
    ∀ n, (leafMu μ n).map (leafToLib V n) = GraphMatching.leafMu μ n
  | 0 => by
      show μ.map id = μ
      exact PMF.map_id μ
  | n + 1 => by
      have hl : (leafMu μ n).map (leafToLib V n) = GraphMatching.leafMu μ n := leafMu_eq μ n
      show (prodPMF (leafMu μ n) (leafMu μ n)).map (Prod.map (leafToLib V n) (leafToLib V n))
        = GraphMatching.prodPMF (GraphMatching.leafMu μ n) (GraphMatching.leafMu μ n)
      rw [map_prodPMF, hl, prodPMF_eq_iid]

lemma fullMu_eq {V : Type u} (μ : PMF V) :
    ∀ n, (fullMu μ n).map (fullToLib V n) = GraphMatching.fullMu μ n
  | 0 => by
      show μ.map id = μ
      exact PMF.map_id μ
  | n + 1 => by
      have hl : (fullMu μ n).map (fullToLib V n) = GraphMatching.fullMu μ n := fullMu_eq μ n
      show (prodPMF μ (prodPMF (fullMu μ n) (fullMu μ n))).map
            (Prod.map id (Prod.map (fullToLib V n) (fullToLib V n)))
        = GraphMatching.prodPMF μ
            (GraphMatching.prodPMF (GraphMatching.fullMu μ n) (GraphMatching.fullMu μ n))
      rw [map_prodPMF, map_prodPMF, hl, PMF.map_id, prodPMF_eq_iid, prodPMF_eq_iid]

/-- Transporting a law along an equivalence, pointwise. -/
lemma map_equiv_apply {α β : Type*} (e : α ≃ β) (p : PMF α) (x : α) :
    p x = (p.map e) (e x) := by
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro b hb
    exact if_neg fun hh => hb (e.injective hh.symm)

lemma etaGraph_eq : @etaGraph = @GraphMatching.etaG := rfl
lemma PhiIid_eq : @PhiIid = @GraphMatching.Phi := rfl
lemma compat_eq : @compat = @GraphMatching.compat := rfl

/-- The transport of full labellings is measurable. -/
lemma measurable_fullToLib {V : Type u} [MeasurableSpace V] :
    ∀ n, Measurable (fullToLib V n)
  | 0 => measurable_id
  | n + 1 => by
      have h := measurable_fullToLib (V := V) n
      exact (measurable_fst.prodMk
        (((h.comp measurable_fst).comp measurable_snd).prodMk
          ((h.comp measurable_snd).comp measurable_snd)))

lemma measurable_fullToLib_symm {V : Type u} [MeasurableSpace V] :
    ∀ n, Measurable (fullToLib V n).symm
  | 0 => measurable_id
  | n + 1 => by
      have h := measurable_fullToLib_symm (V := V) n
      exact (measurable_fst.prodMk
        (((h.comp measurable_fst).comp measurable_snd).prodMk
          ((h.comp measurable_snd).comp measurable_snd)))

/-- Restriction commutes with the transport. -/
lemma restrictLab_toLib {V : Type u} :
    ∀ (n : ℕ) (x : FullLab V (n + 1)),
      fullToLib V n (restrictLab n x) = GraphMatching.restrictLab n (fullToLib V (n + 1) x)
  | 0, _ => rfl
  | n + 1, x => by
      obtain ⟨a, l, r⟩ := x
      simp [restrictLab, GraphMatching.restrictLab, restrictLab_toLib n]

/-- The coordinate map commutes with the transport. -/
lemma coord_toLib {V : Type u} :
    ∀ (n : ℕ) (x : FullLab V n) (w : List Bool),
      coord n x w = GraphMatching.coord n (fullToLib V n x) w
  | 0, _, _ => rfl
  | n + 1, x, [] => rfl
  | n + 1, x, false :: t => by
      obtain ⟨a, l, r⟩ := x
      simpa [coord, GraphMatching.coord] using coord_toLib n l t
  | n + 1, x, true :: t => by
      obtain ⟨a, l, r⟩ := x
      simpa [coord, GraphMatching.coord] using coord_toLib n r t

/-! ## The i.i.d. matching theorem -/

/-- `thm:matching`(1): the leaf bound. -/
theorem audit_graph_leaf_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (h0 : etaGraph μ G ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * etaGraph μ G := by
  rw [etaGraph_eq] at h0 ⊢
  refine le_of_eq_of_le ?_ (GraphMatching.graph_leaf_matching_bound μ G h0 h)
  rw [← (leafToLib V h).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [map_equiv_apply (leafToLib V h) (leafMu μ h) x, leafMu_eq]
  congr 1
  rw [qE, GraphMatching.qE, ← (leafToLib V h).tsum_eq]
  refine tsum_congr fun y => ?_
  rw [map_equiv_apply (leafToLib V h) (leafMu μ h) y, leafMu_eq, leafSim_iff]
  rfl

/-- `thm:matching`(2): the full bound. -/
theorem audit_graph_full_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (hη : etaGraph μ G ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSimIid (compat G) h) x
      ≤ 16 * etaGraph μ G := by
  rw [etaGraph_eq] at hη ⊢
  refine le_of_eq_of_le ?_ (GraphMatching.graph_full_matching_bound μ G hη h)
  rw [← (fullToLib V h).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [map_equiv_apply (fullToLib V h) (fullMu μ h) x, fullMu_eq]
  congr 1
  rw [qE, GraphMatching.qE, ← (fullToLib V h).tsum_eq]
  refine tsum_congr fun y => ?_
  rw [map_equiv_apply (fullToLib V h) (fullMu μ h) y, fullMu_eq, fullSimIid_iff]
  rfl

/-- `thm:matching`, the infinite tree: the matching automorphism as a root-fixing
automorphism of the infinite binary tree. -/
theorem audit_exists_infinite_tree_matching_graphAut {V : Type u} (μ : PMF V)
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hη : PhiIid μ R₀ ≤ 1 / 10000) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : (h : ℕ) → Ω → FullLab V h),
      (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
      (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
      (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
      (∀ h, P.map (fun ω => (X h ω, Y h ω))
        = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) ∧
      1 - 16 * PhiIid μ R₀ ≤ P {ω | ∃ g : List Bool ≃ List Bool, IsTreeAut g ∧
        ∀ s : List Bool, R₀ (coord (g s).length (X (g s).length ω) (g s))
          (coord s.length (Y s.length ω) s)} := by
  rw [PhiIid_eq] at hη ⊢
  obtain ⟨Ω, mΩ, P, hP, X, Y, hX, hY, hmeas, hlaw, hmatch⟩ :=
    GraphMatching.exists_infinite_tree_matching_graphAut μ R₀ hrefl hsymm hη
  refine ⟨Ω, mΩ, P, hP, fun h ω => (fullToLib V h).symm (X h ω),
    fun h ω => (fullToLib V h).symm (Y h ω), ?_, ?_, ?_, ?_, ?_⟩
  · intro h ω
    refine (fullToLib V h).injective ?_
    rw [restrictLab_toLib, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hX]
  · intro h ω
    refine (fullToLib V h).injective ?_
    rw [restrictLab_toLib, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hY]
  · intro h
    exact ((measurable_fullToLib_symm h).comp measurable_fst).prodMk
      ((measurable_fullToLib_symm h).comp measurable_snd) |>.comp (hmeas h)
  · intro h
    have hmm : Measurable (Prod.map (fullToLib V h).symm (fullToLib V h).symm) :=
      ((measurable_fullToLib_symm h).comp measurable_fst).prodMk
        ((measurable_fullToLib_symm h).comp measurable_snd)
    have : (fun ω => ((fullToLib V h).symm (X h ω), (fullToLib V h).symm (Y h ω)))
        = (Prod.map (fullToLib V h).symm (fullToLib V h).symm) ∘ fun ω => (X h ω, Y h ω) := rfl
    rw [this, ← Measure.map_map hmm (hmeas h), hlaw, PMF.toMeasure_map _ _ hmm,
      ← prodPMF_eq_iid, map_prodPMF, ← fullMu_eq, PMF.map_comp, Equiv.symm_comp_self,
      PMF.map_id]
  · refine le_trans hmatch (measure_mono ?_)
    rintro ω ⟨g, hroot, hg⟩
    refine ⟨g.toEquiv, ⟨hroot, fun s t => ?_⟩, fun s => ?_⟩
    · exact ⟨fun h => (g.map_adj_iff).2 h, fun h => (g.map_adj_iff).1 h⟩
    · simpa [coord_toLib, Equiv.apply_symm_apply] using hg s

/-! ## The finite class and the complete classification -/

lemma sameInfiniteClass_iff {J J' : ℕ} (theta : Offspring J) (theta' : Offspring J') :
    SameInfiniteClass theta theta' ↔
      ChainClasses.SameInfiniteClass (offspringToLib theta) (offspringToLib theta') :=
  Iff.rfl

/-- Bounded connected graphs form one quasi-isometry class: each is quasi-isometric to a
single vertex. -/
theorem audit_bounded_graph_qi_point {V : Type u} (G : SimpleGraph V) (hconn : G.Connected)
    (hbdd : ∃ D : ℕ, ∀ x y, G.dist x y ≤ D) :
    GraphQuasiIsometric G (⊥ : SimpleGraph Unit) := by
  haveI : Nonempty V := hconn.nonempty
  exact (graphQuasiIsometric_iff G _).2 (BranchingProcess.quasiIsometric_unit_of_bounded hbdd)

/-- A law with mean at most one dies out almost surely, unless it is the deterministic
single child `θ_1 = 1`. -/
theorem audit_extinction_of_not_supercritical {J N : ℕ} (theta : Offspring J) (hJN : J ≤ N)
    (hmean : ¬ theta.IsSupercritical) (h1 : theta 1 ≠ 1) :
    ∀ᵐ c ∂(gwField (N := N) theta), ¬ gwSurvives c := by
  rw [gwField_eq]
  have hmean' : (offspringToLib theta).mean ≤ 1 :=
    not_lt.1 fun h => hmean ((offspringSupercritical_iff theta).2 h)
  filter_upwards [BranchingProcess.ae_not_survives_of_mean_le_one (offspringToLib theta) hJN
    hmean' h1] with c hc
  exact hc

/-- `thm:trichotomy` in full: for two independent Galton--Watson trees with finitely supported
offspring laws, almost surely a root-preserving quasi-isometry exists exactly when both are
finite, or both are infinite and the two laws lie in the same infinite class, and otherwise no
quasi-isometry exists at all. -/
theorem audit_full_classification_ae_iff {J J' N N' : ℕ}
    (theta : Offspring J) (hJN : J ≤ N) (theta' : Offspring J') (hJN' : J' ≤ N') :
    ∀ᵐ omega ∂((gwField (N := N) theta).prod (gwField (N := N') theta')),
      (GraphQuasiIsometricRooted (gwTreeGraph omega.1) (gwTreeGraph omega.2)
          (gwRoot omega.1) (gwRoot omega.2) ↔
        (¬ gwSurvives omega.1 ∧ ¬ gwSurvives omega.2) ∨
        (gwSurvives omega.1 ∧ gwSurvives omega.2 ∧ SameInfiniteClass theta theta')) ∧
      (GraphQuasiIsometric (gwTreeGraph omega.1) (gwTreeGraph omega.2) →
        (¬ gwSurvives omega.1 ∧ ¬ gwSurvives omega.2) ∨
        (gwSurvives omega.1 ∧ gwSurvives omega.2 ∧ SameInfiniteClass theta theta')) := by
  rw [gwField_eq, gwField_eq]
  filter_upwards [ChainClasses.full_classification_rooted_ae_iff (offspringToLib theta) hJN
    (offspringToLib theta') hJN'] with omega homega
  simp only [gwTreeGraph_eq, graphQuasiIsometric_iff, gwSurvives_iff, sameInfiniteClass_iff,
    GraphQuasiIsometricRooted, graphQIWith_iff]
  exact homega

/-! ## Bridge for the two-value block -/

lemma wedge_eq : ∀ x y : Word, wedge x y = ChainClasses.wedge x y
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: x, b :: y => by
      simp only [wedge, ChainClasses.wedge, wedge_eq x y]

lemma treeDist_eq (x y : Word) : treeDist x y = ChainClasses.treeDist x y := by
  simp [treeDist, ChainClasses.treeDist, wedge_eq]

lemma inTree_iff (χ : Word → Bool) (v : Word) : InTree χ v ↔ ChainClasses.InTree χ v := by
  constructor
  · intro h; induction h with
    | root => exact .root
    | one _ ih => exact .one ih
    | two _ hχ ih => exact .two ih hχ
  · intro h; induction h with
    | root => exact .root
    | one _ ih => exact .one ih
    | two _ hχ ih => exact .two ih hχ

lemma isQIWith_iff (K : ℕ) (T T' : Word → Prop) (f : Word → Word) :
    IsQIWith K T T' f ↔ ChainClasses.IsQIWith K T T' f := by
  constructor
  · rintro ⟨m, u, l, d⟩
    exact ⟨m, by simpa [treeDist_eq] using u, by simpa [treeDist_eq] using l,
      by simpa [treeDist_eq] using d⟩
  · rintro ⟨m, u, l, d⟩
    exact ⟨m, by simpa [treeDist_eq] using u, by simpa [treeDist_eq] using l,
      by simpa [treeDist_eq] using d⟩

lemma inTree_eq (χ : Word → Bool) : InTree χ = ChainClasses.InTree χ := by
  funext v; exact propext (inTree_iff χ v)

lemma isQIWith_eq : @IsQIWith = @ChainClasses.IsQIWith := by
  funext K T T' f; exact propext (isQIWith_iff K T T' f)

lemma bernoulliField_eq {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    bernoulliField ht ht1 = BranchingProcess.bernoulliField (ι := Word) ht ht1 := rfl

lemma qBound_eq : @qBound = @ChainClasses.qBound := rfl

/-! ## Universality in the two-value family -/

/-- `thm:twovalue`: two independent Galton--Watson trees whose offspring law is
supported on `{1,2}` almost surely admit a root-preserving quasi-isometry. -/
theorem audit_twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((bernoulliField ht0 ht1).prod (bernoulliField ht0 ht1))
      {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
        IsQIWith K (InTree ω.1) (InTree ω.2) f ∧ f [] = []} = 0 := by
  rw [bernoulliField_eq]
  refine Eq.trans ?_ (ChainClasses.twovalue_ae_tree_family ht0 ht1)
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, inTree_eq, isQIWith_eq]

/-- The quantitative half of `thm:twovalue`: above a threshold, failure of a root-preserving
`(D²+3)`-quasi-isometry has probability at most the explicit rate. -/
theorem audit_twovalue_rate_tree {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ((bernoulliField ht0.le ht1.le).prod (bernoulliField ht0.le ht1.le))
          {ω | ¬ ∃ f : Word → Word,
            IsQIWith (D ^ 2 + 3) (InTree ω.1) (InTree ω.2) f ∧ f [] = []}
        ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  rw [bernoulliField_eq, qBound_eq]
  simpa only [ChainClasses.twoSampleMeasure, ChainClasses.chainMeasure, inTree_eq,
    isQIWith_eq] using ChainClasses.exists_twovalue_rate_tree ht0 ht1

/-! ## The stopped Markov matching theorem: the model -/

section StoppedPotential
variable {X : Type*}

/-- The symmetrised square `R^□`: straight or crossed compatibility of pairs. -/
def SquareRel (R : X → X → Prop) : X × X → X × X → Prop :=
  fun x y => (R x.1 y.1 ∧ R x.2 y.2) ∨ (R x.1 y.2 ∧ R x.2 y.1)

/-- The directed mismatch mass `∑_x ρ_s(x) q_{ρ_t}(x)` between two laws. -/
noncomputable def failureD (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * qE ρt R x

end StoppedPotential

namespace Stopped

/-- A Markov label model (`sec:markov-proof`): states with a compatibility relation and a
distinguished state `0`, the label law `μ`, the fresh types (the set `I_μ`) and a child-type
kernel. -/
structure Model (V I : Type) where
  /-- compatibility of states, `v ∼ w` -/
  R : V → V → Prop
  /-- the distinguished state `0` -/
  zero : V
  /-- the label law `μ` of the fresh types -/
  μ : PMF V
  /-- the fresh types, the set `I_μ` whose labels are drawn from `μ` -/
  fresh : I → Prop
  /-- the kernel on ordered child-type pairs -/
  π : I → PMF (I × I)

namespace Model

variable {V I : Type} (M : Model V I)

/-- Reflexivity and symmetry of the compatibility relation. -/
structure IsCompat (M : Model V I) : Prop where
  refl : ∀ v, M.R v v
  symm : ∀ v w, M.R v w → M.R w v

/-- The state-only relation on typed states. -/
def srel : I × V → I × V → Prop := fun a b => M.R a.2 b.2

/-- The root state law of a type: `μ` at a fresh type, the point mass at `0` otherwise. -/
noncomputable def rootLaw (t : I) : PMF V :=
  if M.fresh t then M.μ else PMF.pure M.zero

/-- The typed root law. -/
noncomputable def rootT (t : I) : PMF (I × V) :=
  (M.rootLaw t).map fun v => (t, v)

/-- The child kernel on typed states: draw the child-type pair from `π`, then independent
root states. -/
noncomputable def kernel : I × V → PMF ((I × V) × (I × V)) := fun s =>
  (M.π s.1).bind fun j => prodPMF (M.rootT j.1) (M.rootT j.2)

/-- The height-`h` law `ρ_{t,h}` of the labelling of type `t`, as a typed labelling. -/
noncomputable def rho (t : I) (h : ℕ) : PMF (FullLab (I × V) h) :=
  (M.rootT t).bind fun s => muM M.kernel s h

/-- The child-pair mixture of type `t` at height `h`: the law of the two subtrees below a
vertex of type `t`. -/
noncomputable def childMix (t : I) (h : ℕ) :
    PMF (FullLab (I × V) h × FullLab (I × V) h) :=
  (M.π t).bind fun j => prodPMF (M.rho j.1 h) (M.rho j.2 h)

/-- Matching at height `h`: state compatibility at every vertex under some rooted
automorphism, `x ≈_h y`. -/
abbrev sim (h : ℕ) : FullLab (I × V) h → FullLab (I × V) h → Prop :=
  fullSim M.srel h

/-- The matching degree `r_{t,h}(x) = ρ_{t,h}{y : x ≈_h y}`. -/
noncomputable def deg (t : I) (h : ℕ) (x : FullLab (I × V) h) : ℝ≥0∞ :=
  rE (M.rho t h) (M.sim h) x

/-- The realised states `V_μ = supp μ ∪ {0}`. -/
def Vmu : Set V := {v | M.μ v ≠ 0} ∪ {M.zero}

/-- All states of a typed labelling lie in `A`. -/
def StatesIn (A : Set V) : (h : ℕ) → FullLab (I × V) h → Prop
  | 0, x => x.2 ∈ A
  | _ + 1, x => x.1.2 ∈ A ∧ StatesIn A _ x.2.1 ∧ StatesIn A _ x.2.2

/-- The graph potential `η_{G,α}(μ) = ∑_v μ(v) φ_α(1 - b(v))` (`eq:root-defect`). -/
noncomputable def eta (α : ℝ) : ℝ≥0∞ := PhiD α M.μ M.μ M.R

/-- The incompatible root mass `δ = 1 - b(0) = μ{v : v ≁ 0}` (`eq:root-defect`). -/
noncomputable def delta : ℝ≥0∞ := qE M.μ M.R M.zero

/-- The forced-state term `e_0 = φ_α(δ)`, infinite when `b(0) = 0` (`eq:root-defect`). -/
noncomputable def e0 (α : ℝ) : ℝ≥0∞ := phiE α (q M.μ M.R M.zero)

/-- The one-site defect `ζ_α = max{η_α, φ_α(δ)}` (`eq:root-defect`). -/
noncomputable def zeta (α : ℝ) : ℝ≥0∞ := max (M.eta α) (M.e0 α)

/-- The failure probability `P(M_h(s,t)^c) = ∑_x ρ_{s,h}(x) q_{ρ_{t,h}}(x)`
(`sec:completion`). -/
noncomputable def failProb (s t : I) (h : ℕ) : ℝ≥0∞ :=
  failureD (M.rho s h) (M.rho t h) (M.sim h)

/-- The class index (`sec:finite-hypotheses`), here called the phase: fresh types have phase
zero and every child in a charged transition has phase one greater than its parent. -/
structure Phase (M : Model V I) (g : ℕ) where
  θ : I → ZMod g
  fresh_zero : ∀ t, M.fresh t → θ t = 0
  child : ∀ t j, M.π t j ≠ 0 → θ j.1 = θ t + 1 ∧ θ j.2 = θ t + 1

/-- The number of types of phase `i` (`eq:transition-budget`). -/
noncomputable def Phase.count {M : Model V I} [Fintype I] {g : ℕ} (Θ : Phase M g)
    (i : ZMod g) : ℕ :=
  (Finset.univ.filter fun t => Θ.θ t = i).card

/-- A possible child: some charged transition produces it. -/
def child (t t' : I) : Prop := ∃ j, M.π t j ≠ 0 ∧ (t' = j.1 ∨ t' = j.2)

/-- The possible children of a set of types. -/
def children (D : Set I) : Set I := {t' | ∃ t ∈ D, M.child t t'}

/-- The types reachable from `D` by possible paths of length `n`. -/
def reach (D : Set I) : ℕ → Set I
  | 0 => D
  | n + 1 => children M (reach D n)

/-- A possible type path of length `n`: successive possible children. -/
def IsPath (p : ℕ → I) (n : ℕ) : Prop := ∀ i < n, M.child (p i) (p (i + 1))

/-- The stopping predicate (`sec:finite-hypotheses`): every possible source path of
length `n` from `s` passes, at some depth `k ≤ n`, a fresh type at which some type reachable
from `D` in `k` steps is fresh. -/
def Stops (s : I) (D : Set I) (n : ℕ) : Prop :=
  ∀ p : ℕ → I, p 0 = s → M.IsPath p n → ∃ k ≤ n, M.fresh (p k) ∧ ∃ f ∈ M.reach D k, M.fresh f

/-- Common returns, condition `it:markov-returns`: from any two types of the same class, every
possible source path reaches a fresh type at a depth at most `H` at which some possible
target path is fresh as well. -/
def CommonReturns {g : ℕ} (Θ : Phase M g) (H : ℕ) : Prop :=
  ∀ s t, Θ.θ s = Θ.θ t → M.Stops s {t} H

/-- Positivity, condition `it:markov-positivity`: every charged realisation of a fresh type
has positive degree against every fresh type. -/
def FreshPositive : Prop :=
  ∀ (h : ℕ) (f f' : I) (x : FullLab (I × V) h),
    M.fresh f → M.fresh f' → M.rho f h x ≠ 0 → M.deg f' h x ≠ 0

/-- A transition selection (`eq:transition-budget`): for every target type a nonempty
finite set of charged child pairs such that, for every source child pair with states in
`V_μ`, positive degree against the full child-pair mixture implies positive degree against
some selected component. -/
structure Selection (M : Model V I) where
  J : I → Finset (I × I)
  nonempty : ∀ t, (J t).Nonempty
  charged : ∀ t, ∀ j ∈ J t, M.π t j ≠ 0
  positive : ∀ (t : I) (h : ℕ) (p : FullLab (I × V) h × FullLab (I × V) h),
    StatesIn M.Vmu h p.1 → StatesIn M.Vmu h p.2 →
    rE (M.childMix t h) (SquareRel (M.sim h)) p ≠ 0 →
    ∃ j ∈ J t, rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) p ≠ 0

/-- The inverse-probability sum `∑_{j ∈ J_t} π_t(j)^{-α}` of a type
(`eq:transition-budget`). -/
noncomputable def Selection.inverseSum {M : Model V I} (Sel : Selection M) (α : ℝ) (t : I) :
    ℝ≥0∞ :=
  ∑ j ∈ Sel.J t, (M.π t j) ^ (-α)

end Model

/-- The summand of `L_α(β)` at `q` (`eq:mean-constants`). -/
noncomputable def Lsummand (α β q : ℝ) : ℝ := q / (1 + q) ^ α + β * (1 - q) ^ α

/-- `L_α(β) = max_{0 ≤ q ≤ 1} (q/(1+q)^α + β(1-q)^α)` (`eq:mean-constants`). -/
noncomputable def Lfun (α β : ℝ) : ℝ := sSup (Lsummand α β '' Set.Icc 0 1)

/-- `K_α(β) = α^α/(α+1)^{α+1} (1-β)^{α+1}` (`eq:mean-constants`). -/
noncomputable def Kfun (α β : ℝ) : ℝ := α ^ α / (α + 1) ^ (α + 1) * (1 - β) ^ (α + 1)

/-- `λ_α = 2 min_{0 ≤ β ≤ 1} (L_α(β) + K_α(β))` (`eq:mean-constants`). -/
noncomputable def lambda (α : ℝ) : ℝ :=
  2 * sInf ((fun β => Lfun α β + Kfun α β) '' Set.Icc 0 1)

end Stopped

/-! ## Bridge for the stopped Markov block -/

namespace Stopped

/-- The scalar functions of `eq:mean-constants` are literally the library's. -/
lemma Lsummand_eq : @Lsummand = @GraphMarkovMatching.Stopped.Lsummand := rfl
lemma Lfun_eq : @Lfun = @GraphMarkovMatching.Stopped.Lfun := rfl
lemma Kfun_eq : @Kfun = @GraphMarkovMatching.Stopped.Kfun := rfl
lemma lambda_eq : @lambda = @GraphMarkovMatching.Stopped.lambda := rfl

/-- The pair transport of labellings. -/
def pairToLib (S : Type u) (h : ℕ) :
    FullLab S h × FullLab S h ≃
      GraphMarkovMatching.Support.FullLab S h × GraphMarkovMatching.Support.FullLab S h :=
  (toLib S h).prodCongr (toLib S h)

/-- Transporting the good degree along an equivalence. -/
lemma rE_map_equiv {X Y : Type*} (e : X ≃ Y) (μ : PMF X) (R : X → X → Prop)
    (R' : Y → Y → Prop) (hR : ∀ x y, R x y ↔ R' (e x) (e y)) (x : X) :
    rE μ R x = GraphMarkovMatching.Support.rE (μ.map e) R' (e x) := by
  rw [rE, GraphMarkovMatching.Support.rE, ← e.tsum_eq]
  refine tsum_congr fun y => ?_
  rw [← map_equiv_apply e μ y]
  by_cases h : R x y
  · rw [if_pos h, if_pos ((hR x y).1 h)]
  · rw [if_neg h, if_neg fun h' => h ((hR x y).2 h')]

/-- Transporting the bad degree along an equivalence. -/
lemma qE_map_equiv {X Y : Type*} (e : X ≃ Y) (μ : PMF X) (R : X → X → Prop)
    (R' : Y → Y → Prop) (hR : ∀ x y, R x y ↔ R' (e x) (e y)) (x : X) :
    qE μ R x = GraphMarkovMatching.Support.qE (μ.map e) R' (e x) := by
  rw [qE, GraphMarkovMatching.Support.qE, ← e.tsum_eq]
  refine tsum_congr fun y => ?_
  rw [← map_equiv_apply e μ y]
  by_cases h : R x y
  · rw [if_pos h, if_pos ((hR x y).1 h)]
  · rw [if_neg h, if_neg fun h' => h ((hR x y).2 h')]

namespace Model

variable {V I : Type} (M : Model V I)

/-- The challenge's model as the library's model, field by field. -/
def lib : GraphMarkovMatching.Stopped.Model V I := ⟨M.R, M.zero, M.μ, M.fresh, M.π⟩

/-- Compatibility of the relation is the same on both sides. -/
lemma isCompat_iff : M.IsCompat ↔ M.lib.IsCompat :=
  ⟨fun h => ⟨h.refl, h.symm⟩, fun h => ⟨h.refl, h.symm⟩⟩

/-- The state-only relation is literally the library's. -/
lemma srel_eq : M.srel = M.lib.srel := rfl

/-- The typed root law is literally the library's. -/
lemma rootT_eq (t : I) : M.rootT t = M.lib.rootT t := rfl

/-- The challenge's child kernel is the library's. -/
lemma kernel_eq : M.kernel = M.lib.kernel := by
  funext s
  show (M.π s.1).bind (fun j => prodPMF (M.rootT j.1) (M.rootT j.2))
    = (M.π s.1).bind fun j =>
        GraphMarkovMatching.Support.prodPMF (M.rootT j.1) (M.rootT j.2)
  simp only [prodPMF_eq]

/-- The challenge's height-`h` law is the library's, along `toLib`. -/
lemma rho_eq (t : I) (h : ℕ) : (M.rho t h).map (toLib (I × V) h) = M.lib.rho t h := by
  simp only [rho, GraphMarkovMatching.Stopped.Model.rho, PMF.map_bind]
  rw [← kernel_eq, ← rootT_eq]
  congr 1
  funext s
  exact muM_eq M.kernel s h

/-- The pointwise form. -/
lemma rho_apply (t : I) (h : ℕ) (x : FullLab (I × V) h) :
    M.rho t h x = M.lib.rho t h (toLib (I × V) h x) := by
  rw [← rho_eq]
  exact map_equiv_apply _ _ _

/-- The challenge's matching relation is the library's, along `toLib`. -/
lemma sim_iff (h : ℕ) (x y : FullLab (I × V) h) :
    M.sim h x y ↔ M.lib.sim h (toLib (I × V) h x) (toLib (I × V) h y) :=
  fullSim_iff M.srel h x y

/-- The challenge's matching degree is the library's, along `toLib`. -/
lemma deg_eq (t : I) (h : ℕ) (x : FullLab (I × V) h) :
    M.deg t h x = M.lib.deg t h (toLib (I × V) h x) := by
  rw [deg, GraphMarkovMatching.Stopped.Model.deg, ← rho_eq]
  exact rE_map_equiv _ _ _ _ (M.sim_iff h) x

/-- The challenge's failure probability is the library's. -/
lemma failProb_eq (s t : I) (h : ℕ) : M.failProb s t h = M.lib.failProb s t h := by
  rw [failProb, failureD, GraphMarkovMatching.Stopped.Model.failProb,
    GraphMarkovMatching.failureD, ← (toLib (I × V) h).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [rho_apply, qE_map_equiv (toLib (I × V) h) (M.rho t h) (M.sim h) (M.lib.sim h)
    (M.sim_iff h) x, rho_eq]

/-- The one-site defect `ζ_α` is literally the library's (`eq:root-defect`). -/
lemma zeta_eq (α : ℝ) : M.zeta α = M.lib.zeta α := rfl

/-- The incompatible root mass `δ` is literally the library's (`eq:root-defect`). -/
lemma delta_eq : M.delta = M.lib.delta := rfl

/-- The challenge's phase map as the library's. -/
def Phase.lib {M : Model V I} {g : ℕ} (Θ : Phase M g) :
    GraphMarkovMatching.Stopped.Model.Phase M.lib g :=
  ⟨Θ.θ, Θ.fresh_zero, Θ.child⟩

/-- The class sizes agree (`eq:transition-budget`). -/
lemma Phase.count_eq {M : Model V I} [Fintype I] {g : ℕ} (Θ : Phase M g) (i : ZMod g) :
    Θ.count i = Θ.lib.count i := rfl

/-- The reachable sets agree. -/
lemma reach_eq (D : Set I) : ∀ n, M.reach D n = M.lib.reach D n
  | 0 => rfl
  | n + 1 => by
      show M.children (M.reach D n) = M.lib.children (M.lib.reach D n)
      rw [reach_eq D n]
      rfl

/-- The stopping predicate agrees. -/
lemma stops_iff (s : I) (D : Set I) (n : ℕ) : M.Stops s D n ↔ M.lib.Stops s D n := by
  simp only [Stops, GraphMarkovMatching.Stopped.Model.Stops, reach_eq]
  exact Iff.rfl

/-- Common returns agree. -/
lemma commonReturns_iff {g : ℕ} (Θ : Phase M g) (H : ℕ) :
    M.CommonReturns Θ H ↔ M.lib.CommonReturns Θ.lib H :=
  forall_congr' fun s => forall_congr' fun t => imp_congr Iff.rfl (M.stops_iff s {t} H)

/-- Fresh positivity agrees. -/
lemma freshPositive_iff : M.FreshPositive ↔ M.lib.FreshPositive := by
  constructor
  · intro hFP h f f' x hf hf' hx
    have hx' : M.rho f h ((toLib (I × V) h).symm x) ≠ 0 := by
      rw [rho_apply, Equiv.apply_symm_apply]
      exact hx
    have := hFP h f f' ((toLib (I × V) h).symm x) hf hf' hx'
    rw [deg_eq, Equiv.apply_symm_apply] at this
    exact this
  · intro hFP h f f' x hf hf' hx
    rw [deg_eq]
    refine hFP h f f' _ hf hf' ?_
    rw [← rho_apply]
    exact hx

/-- The states of a labelling lie in `A` on either side of the transport. -/
lemma statesIn_iff (A : Set V) : ∀ (h : ℕ) (x : FullLab (I × V) h),
    StatesIn A h x ↔ GraphMarkovMatching.Stopped.Model.StatesIn A h (toLib (I × V) h x)
  | 0, _ => Iff.rfl
  | h + 1, x => by
      obtain ⟨a, l, r⟩ := x
      simp only [StatesIn, GraphMarkovMatching.Stopped.Model.StatesIn, toLib_succ_apply,
        statesIn_iff A h l, statesIn_iff A h r]

/-- The realised states are literally the library's. -/
lemma vmu_eq : M.Vmu = M.lib.Vmu := rfl

/-- The symmetrised square of the matching relation transports along the pair map. -/
lemma squareRel_iff (h : ℕ) (p r : FullLab (I × V) h × FullLab (I × V) h) :
    SquareRel (M.sim h) p r
      ↔ GraphMarkovMatching.Support.SquareRel (M.lib.sim h) (pairToLib (I × V) h p)
          (pairToLib (I × V) h r) := by
  simp only [SquareRel, GraphMarkovMatching.Support.SquareRel, pairToLib,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, M.sim_iff h]

/-- The child-pair mixture transports along the pair map. -/
lemma childMix_eq (t : I) (h : ℕ) :
    (M.childMix t h).map (pairToLib (I × V) h) = M.lib.childMix t h := by
  simp only [childMix, GraphMarkovMatching.Stopped.Model.childMix, PMF.map_bind]
  congr 1
  funext j
  rw [pairToLib, Equiv.prodCongr_apply, map_prodPMF, rho_eq, rho_eq, prodPMF_eq]

/-- A product of two level laws transports along the pair map. -/
lemma prodPMF_rho_eq (j : I × I) (h : ℕ) :
    (prodPMF (M.rho j.1 h) (M.rho j.2 h)).map (pairToLib (I × V) h)
      = GraphMarkovMatching.Support.prodPMF (M.lib.rho j.1 h) (M.lib.rho j.2 h) := by
  rw [pairToLib, Equiv.prodCongr_apply, map_prodPMF, rho_eq, rho_eq, prodPMF_eq]

/-- The child-pair degree transports along the pair map. -/
lemma rE_childMix_eq (t : I) (h : ℕ) (p : FullLab (I × V) h × FullLab (I × V) h) :
    rE (M.childMix t h) (SquareRel (M.sim h)) p
      = GraphMarkovMatching.Support.rE (M.lib.childMix t h)
          (GraphMarkovMatching.Support.SquareRel (M.lib.sim h)) (pairToLib (I × V) h p) := by
  rw [← childMix_eq]
  exact rE_map_equiv _ _ _ _ (M.squareRel_iff h) p

/-- The component pair degree transports along the pair map. -/
lemma rE_prodPMF_rho_eq (j : I × I) (h : ℕ) (p : FullLab (I × V) h × FullLab (I × V) h) :
    rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) p
      = GraphMarkovMatching.Support.rE
          (GraphMarkovMatching.Support.prodPMF (M.lib.rho j.1 h) (M.lib.rho j.2 h))
          (GraphMarkovMatching.Support.SquareRel (M.lib.sim h)) (pairToLib (I × V) h p) := by
  rw [← prodPMF_rho_eq]
  exact rE_map_equiv _ _ _ _ (M.squareRel_iff h) p

/-- The challenge's transition selection as the library's. -/
def Selection.lib {M : Model V I} (Sel : Selection M) :
    GraphMarkovMatching.Stopped.Model.Selection M.lib where
  J := Sel.J
  nonempty := Sel.nonempty
  charged := Sel.charged
  positive := fun t h p hp1 hp2 hr => by
    have e1 : toLib (I × V) h ((pairToLib (I × V) h).symm p).1 = p.1 :=
      Equiv.apply_symm_apply _ _
    have e2 : toLib (I × V) h ((pairToLib (I × V) h).symm p).2 = p.2 :=
      Equiv.apply_symm_apply _ _
    obtain ⟨j, hj, hj'⟩ := Sel.positive t h ((pairToLib (I × V) h).symm p)
      ((statesIn_iff _ _ _).2 (by rw [e1]; exact hp1))
      ((statesIn_iff _ _ _).2 (by rw [e2]; exact hp2))
      (by rw [rE_childMix_eq, Equiv.apply_symm_apply]; exact hr)
    refine ⟨j, hj, ?_⟩
    rw [rE_prodPMF_rho_eq, Equiv.apply_symm_apply] at hj'
    exact hj'

/-- The inverse-probability sums agree (`eq:transition-budget`). -/
lemma Selection.inverseSum_eq {M : Model V I} (Sel : Selection M) (α : ℝ) (t : I) :
    Sel.inverseSum α t = Sel.lib.inverseSum α t := rfl

end Model

end Stopped

/-! ## The stopped Markov matching theorem -/

/-- `thm:markov-matching`, finite alternative: under the exponent condition `λ_α < 1`,
there are constants `K`, `ε > 0` depending only on `α, H, T, B` such that every finite
model with type classes of size at most `T`, transition selections with inverse sums at most
`B`, fresh positivity and common returns within `H`, and one-site defect `ζ_α ≤ ε`, has
every same-class pair failing to match at every height with probability at most `K ζ_α`. -/
theorem audit_markov_matching_finite {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1)
    (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Stopped.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Stopped.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      ∀ (Sel : Stopped.Model.Selection M), (∀ t, Sel.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t → ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := by
  obtain ⟨Kc, ε, hε, hbound⟩ :=
    GraphMarkovMatching.Stopped.markov_matching_of_lambda hα hlam H T hT B hB
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I _ M hc g Θ hTc Sel hBs hFP hCR hζ s t hst h
  rw [Stopped.Model.failProb_eq, Stopped.Model.zeta_eq]
  exact hbound M.lib ((M.isCompat_iff).1 hc) Θ.lib hTc Sel.lib hBs
    ((M.freshPositive_iff).1 hFP) ((M.commonReturns_iff Θ H).1 hCR) hζ s t hst h

/-- `thm:markov-matching`, zero-compatible alternative: under the exponent condition
`λ_α < 1`, there are constants `K`, `ε > 0` depending only on `α` such that every model
with `δ = 0` and `ζ_α ≤ ε` has every pair of types failing to match at every height with
probability at most `K ζ_α`. -/
theorem audit_markov_matching_zero {α : ℝ} (hα : 1 ≤ α) (hlam : Stopped.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Stopped.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α := by
  obtain ⟨Kc, ε, hε, hbound⟩ := GraphMarkovMatching.Stopped.markov_matching_zero_of_lambda hα hlam
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I M hc hδ hζ s t h
  rw [Stopped.Model.failProb_eq, Stopped.Model.zeta_eq]
  exact hbound M.lib ((M.isCompat_iff).1 hc) hδ hζ s t h

/-- `thm:markov-matching`, finite alternative at infinite height: two independent
consistent processes of same-class types admit one root-fixing infinite-tree
automorphism matching their states at every vertex with probability at least
`1 - K ζ_α`. -/
theorem audit_markov_matching_finite_infinite {α : ℝ} (hα : 1 ≤ α)
    (hlam : Stopped.lambda α < 1) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V] [MeasurableSpace I] [MeasurableSingletonClass I]
      (M : Stopped.Model V I), M.IsCompat →
      ∀ {g : ℕ} (Θ : Stopped.Model.Phase M g), (∀ i, Θ.count i ≤ T) →
      ∀ (Sel : Stopped.Model.Selection M), (∀ t, Sel.inverseSum α t ≤ ENNReal.ofReal B) →
      M.FreshPositive → M.CommonReturns Θ H → M.zeta α ≤ ENNReal.ofReal ε →
      ∀ s t, Θ.θ s = Θ.θ t →
      ∃ (Omega : Type) (_ : MeasurableSpace Omega) (P : Measure Omega)
        (_ : IsProbabilityMeasure P) (X Y : (n : ℕ) → Omega → FullLab (I × V) n),
        (∀ n omega, restrictLab n (X (n + 1) omega) = X n omega) ∧
        (∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega) ∧
        (∀ n, Measurable (fun omega => (X n omega, Y n omega))) ∧
        (∀ n, P.map (fun omega => (X n omega, Y n omega))
          = (prodPMF (M.rho s n) (M.rho t n)).toMeasure) ∧
        1 - ENNReal.ofReal Kc * M.zeta α
          ≤ P {omega | ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧
            ∀ w : List Bool, M.srel
              (coord (aut w).length (X (aut w).length omega) (aut w))
              (coord w.length (Y w.length omega) w)} := by
  obtain ⟨Kc, ε, hε, hbound⟩ :=
    GraphMarkovMatching.Stopped.markov_matching_of_lambda hα hlam H T hT B hB
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I _ _ _ _ _ _ M hc g Θ hTc Sel hBs hFP hCR hζ s t hst
  have hfail : ∀ h, M.lib.failProb s t h ≤ ENNReal.ofReal Kc * M.lib.zeta α :=
    hbound M.lib ((M.isCompat_iff).1 hc) Θ.lib hTc Sel.lib hBs
      ((M.freshPositive_iff).1 hFP) ((M.commonReturns_iff Θ H).1 hCR) hζ s t hst
  let Omega :=
    ((Π n, GraphMarkovMatching.Support.FullLab (I × V) n) ×
      (Π n, GraphMarkovMatching.Support.FullLab (I × V) n))
  let P : Measure Omega := M.lib.trajPair s t
  let X : (n : ℕ) → Omega → FullLab (I × V) n := fun n omega =>
    (toLib (I × V) n).symm (GraphMarkovMatching.Support.consLab n omega.1)
  let Y : (n : ℕ) → Omega → FullLab (I × V) n := fun n omega =>
    (toLib (I × V) n).symm (GraphMarkovMatching.Support.consLab n omega.2)
  refine ⟨Omega, inferInstance, P, inferInstance, X, Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro n omega
    apply (toLib (I × V) n).injective
    rw [restrictLab_toLib_process, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact GraphMarkovMatching.Support.restrictLab_consLab n omega.1
  · intro n omega
    apply (toLib (I × V) n).injective
    rw [restrictLab_toLib_process, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact GraphMarkovMatching.Support.restrictLab_consLab n omega.2
  · intro n
    exact ((measurable_toLib_process_symm n).comp measurable_fst).prodMk
      ((measurable_toLib_process_symm n).comp measurable_snd) |>.comp
        (GraphMarkovMatching.Support.measurable_consLab_pair n)
  · intro n
    have hmm : Measurable
        (Prod.map (toLib (I × V) n).symm (toLib (I × V) n).symm) :=
      ((measurable_toLib_process_symm n).comp measurable_fst).prodMk
        ((measurable_toLib_process_symm n).comp measurable_snd)
    have hfun : (fun omega : Omega => (X n omega, Y n omega)) =
        (Prod.map (toLib (I × V) n).symm (toLib (I × V) n).symm) ∘
          (fun omega => (GraphMarkovMatching.Support.consLab n omega.1,
            GraphMarkovMatching.Support.consLab n omega.2)) := rfl
    have hlawlib : P.map
        (fun omega => (GraphMarkovMatching.Support.consLab n omega.1,
          GraphMarkovMatching.Support.consLab n omega.2)) =
        (GraphMarkovMatching.Support.prodPMF (M.lib.rho s n) (M.lib.rho t n)).toMeasure :=
      GraphMarkovMatching.Support.trajPairLab_map_consLab _ _ _ _ n
    rw [hfun, ← Measure.map_map hmm
      (GraphMarkovMatching.Support.measurable_consLab_pair n), hlawlib,
      PMF.toMeasure_map _ _ hmm, ← prodPMF_eq, map_prodPMF, ← M.rho_eq s n, ← M.rho_eq t n,
      PMF.map_comp, PMF.map_comp, Equiv.symm_comp_self, PMF.map_id, PMF.map_id]
  · have hge := M.lib.trajPair_infMatch_ge s t hfail
    refine le_trans hge (measure_mono ?_)
    intro omega homega
    change GraphMarkovMatching.InfMatch M.lib.srel
      (fun n => GraphMarkovMatching.Support.consLab n omega.1)
      (fun n => GraphMarkovMatching.Support.consLab n omega.2) at homega
    have hmatch := supportInfMatch_toGraph M.lib.srel
      (fun n => GraphMarkovMatching.Support.consLab n omega.1)
      (fun n => GraphMarkovMatching.Support.consLab n omega.2) homega
    have hXgraph : ∀ n, GraphMatching.restrictLab n
        (supportFullToGraph (I × V) (n + 1)
          (GraphMarkovMatching.Support.consLab (n + 1) omega.1)) =
        supportFullToGraph (I × V) n (GraphMarkovMatching.Support.consLab n omega.1) := by
      intro n
      rw [← supportRestrictLab_toGraph,
        GraphMarkovMatching.Support.restrictLab_consLab]
    have hYgraph : ∀ n, GraphMatching.restrictLab n
        (supportFullToGraph (I × V) (n + 1)
          (GraphMarkovMatching.Support.consLab (n + 1) omega.2)) =
        supportFullToGraph (I × V) n (GraphMarkovMatching.Support.consLab n omega.2) := by
      intro n
      rw [← supportRestrictLab_toGraph,
        GraphMarkovMatching.Support.restrictLab_consLab]
    obtain ⟨aut, hroot, haut⟩ := (GraphMatching.infMatch_iff_graphAut M.lib.srel
      (fun n => supportFullToGraph (I × V) n
        (GraphMarkovMatching.Support.consLab n omega.1))
      (fun n => supportFullToGraph (I × V) n
        (GraphMarkovMatching.Support.consLab n omega.2)) hXgraph hYgraph).1 hmatch
    change ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧ ∀ w : List Bool, M.srel
      (coord (aut w).length (X (aut w).length omega) (aut w))
      (coord w.length (Y w.length omega) w)
    refine ⟨aut.toEquiv, ⟨hroot, fun s t => ?_⟩, fun w => ?_⟩
    · exact ⟨fun h => (aut.map_adj_iff).2 h, fun h => (aut.map_adj_iff).1 h⟩
    · simpa [X, Y, Stopped.Model.srel, GraphMarkovMatching.Stopped.Model.srel,
        Stopped.Model.lib, coord_supportToGraph] using haut w

/-- `thm:markov-matching`, zero-compatible alternative at infinite height: two independent
consistent processes of any two types admit one root-fixing infinite-tree automorphism
matching their states at every vertex with probability at least `1 - K ζ_α`. -/
theorem audit_markov_matching_zero_infinite {α : ℝ} (hα : 1 ≤ α)
    (hlam : Stopped.lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V] [Countable I] [MeasurableSpace I]
      [MeasurableSingletonClass I] (M : Stopped.Model V I), M.IsCompat → M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t,
      ∃ (Omega : Type) (_ : MeasurableSpace Omega) (P : Measure Omega)
        (_ : IsProbabilityMeasure P) (X Y : (n : ℕ) → Omega → FullLab (I × V) n),
        (∀ n omega, restrictLab n (X (n + 1) omega) = X n omega) ∧
        (∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega) ∧
        (∀ n, Measurable (fun omega => (X n omega, Y n omega))) ∧
        (∀ n, P.map (fun omega => (X n omega, Y n omega))
          = (prodPMF (M.rho s n) (M.rho t n)).toMeasure) ∧
        1 - ENNReal.ofReal Kc * M.zeta α
          ≤ P {omega | ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧
            ∀ w : List Bool, M.srel
              (coord (aut w).length (X (aut w).length omega) (aut w))
              (coord w.length (Y w.length omega) w)} := by
  obtain ⟨Kc, ε, hε, hbound⟩ := GraphMarkovMatching.Stopped.markov_matching_zero_of_lambda hα hlam
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I _ _ _ _ _ _ M hc hδ hζ s t
  have hfail : ∀ h, M.lib.failProb s t h ≤ ENNReal.ofReal Kc * M.lib.zeta α :=
    hbound M.lib ((M.isCompat_iff).1 hc) hδ hζ s t
  let Omega :=
    ((Π n, GraphMarkovMatching.Support.FullLab (I × V) n) ×
      (Π n, GraphMarkovMatching.Support.FullLab (I × V) n))
  let P : Measure Omega := M.lib.trajPair s t
  let X : (n : ℕ) → Omega → FullLab (I × V) n := fun n omega =>
    (toLib (I × V) n).symm (GraphMarkovMatching.Support.consLab n omega.1)
  let Y : (n : ℕ) → Omega → FullLab (I × V) n := fun n omega =>
    (toLib (I × V) n).symm (GraphMarkovMatching.Support.consLab n omega.2)
  refine ⟨Omega, inferInstance, P, inferInstance, X, Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro n omega
    apply (toLib (I × V) n).injective
    rw [restrictLab_toLib_process, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact GraphMarkovMatching.Support.restrictLab_consLab n omega.1
  · intro n omega
    apply (toLib (I × V) n).injective
    rw [restrictLab_toLib_process, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact GraphMarkovMatching.Support.restrictLab_consLab n omega.2
  · intro n
    exact ((measurable_toLib_process_symm n).comp measurable_fst).prodMk
      ((measurable_toLib_process_symm n).comp measurable_snd) |>.comp
        (GraphMarkovMatching.Support.measurable_consLab_pair n)
  · intro n
    have hmm : Measurable
        (Prod.map (toLib (I × V) n).symm (toLib (I × V) n).symm) :=
      ((measurable_toLib_process_symm n).comp measurable_fst).prodMk
        ((measurable_toLib_process_symm n).comp measurable_snd)
    have hfun : (fun omega : Omega => (X n omega, Y n omega)) =
        (Prod.map (toLib (I × V) n).symm (toLib (I × V) n).symm) ∘
          (fun omega => (GraphMarkovMatching.Support.consLab n omega.1,
            GraphMarkovMatching.Support.consLab n omega.2)) := rfl
    have hlawlib : P.map
        (fun omega => (GraphMarkovMatching.Support.consLab n omega.1,
          GraphMarkovMatching.Support.consLab n omega.2)) =
        (GraphMarkovMatching.Support.prodPMF (M.lib.rho s n) (M.lib.rho t n)).toMeasure :=
      GraphMarkovMatching.Support.trajPairLab_map_consLab _ _ _ _ n
    rw [hfun, ← Measure.map_map hmm
      (GraphMarkovMatching.Support.measurable_consLab_pair n), hlawlib,
      PMF.toMeasure_map _ _ hmm, ← prodPMF_eq, map_prodPMF, ← M.rho_eq s n, ← M.rho_eq t n,
      PMF.map_comp, PMF.map_comp, Equiv.symm_comp_self, PMF.map_id, PMF.map_id]
  · have hge := M.lib.trajPair_infMatch_ge s t hfail
    refine le_trans hge (measure_mono ?_)
    intro omega homega
    change GraphMarkovMatching.InfMatch M.lib.srel
      (fun n => GraphMarkovMatching.Support.consLab n omega.1)
      (fun n => GraphMarkovMatching.Support.consLab n omega.2) at homega
    have hmatch := supportInfMatch_toGraph M.lib.srel
      (fun n => GraphMarkovMatching.Support.consLab n omega.1)
      (fun n => GraphMarkovMatching.Support.consLab n omega.2) homega
    have hXgraph : ∀ n, GraphMatching.restrictLab n
        (supportFullToGraph (I × V) (n + 1)
          (GraphMarkovMatching.Support.consLab (n + 1) omega.1)) =
        supportFullToGraph (I × V) n (GraphMarkovMatching.Support.consLab n omega.1) := by
      intro n
      rw [← supportRestrictLab_toGraph,
        GraphMarkovMatching.Support.restrictLab_consLab]
    have hYgraph : ∀ n, GraphMatching.restrictLab n
        (supportFullToGraph (I × V) (n + 1)
          (GraphMarkovMatching.Support.consLab (n + 1) omega.2)) =
        supportFullToGraph (I × V) n (GraphMarkovMatching.Support.consLab n omega.2) := by
      intro n
      rw [← supportRestrictLab_toGraph,
        GraphMarkovMatching.Support.restrictLab_consLab]
    obtain ⟨aut, hroot, haut⟩ := (GraphMatching.infMatch_iff_graphAut M.lib.srel
      (fun n => supportFullToGraph (I × V) n
        (GraphMarkovMatching.Support.consLab n omega.1))
      (fun n => supportFullToGraph (I × V) n
        (GraphMarkovMatching.Support.consLab n omega.2)) hXgraph hYgraph).1 hmatch
    change ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧ ∀ w : List Bool, M.srel
      (coord (aut w).length (X (aut w).length omega) (aut w))
      (coord w.length (Y w.length omega) w)
    refine ⟨aut.toEquiv, ⟨hroot, fun s t => ?_⟩, fun w => ?_⟩
    · exact ⟨fun h => (aut.map_adj_iff).2 h, fun h => (aut.map_adj_iff).1 h⟩
    · simpa [X, Y, Stopped.Model.srel, GraphMarkovMatching.Stopped.Model.srel,
        Stopped.Model.lib, coord_supportToGraph] using haut w

end Challenge
