/-
Comparator challenge file: the headline theorems, restated with `sorry` in place
of their proofs.
Checked by ST on 1 Sep 19:40 CEST
Everything these statements mention is defined below, over Mathlib alone. No
module of the four libraries is imported: the trust boundary of the audit is this
file together with its import closure, and the libraries are what the audit is
about. The material preceding the headline theorems is definitional scaffolding
only; no auxiliary result is proved here. `Solution.lean` is the untrusted side
and may import the libraries freely.

Run from `lean/` with
`lake env <comparator binary> comparator-config.json`
(see `comparator-config.json` for the audited names).
-/
import Mathlib

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

/-- The weight in `ℝ≥0∞`, infinite off `[0,1)`. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤

/-- The directed potential `Φ_α(μ → ν; R) = ∑_x μ(x) φ_α(q_ν(x))`. -/
noncomputable def PhiD (α : ℝ) (μ ν : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * phiE α (q ν R x)

end Potential

/-- The label-graph potential `η_α = Φ_α(μ → μ; R)`. -/
noncomputable def etaG {V : Type*} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) : ℝ≥0∞ :=
  PhiD α μ μ Rv

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

section VaryingCounter
variable {V : Type} (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- Two labels are compatible when their states are. -/
def labRel {V : Type*} (Rv : V → V → Prop) : V × ℕ → V × ℕ → Prop := fun s t => Rv s.1 t.1

/-- The fresh law `Q = μ ⊗ ν`. -/
noncomputable def freshQ : PMF (V × ℕ) := prodPMF μ ν

/-- The varying-counter kernel: a counter of at least `4` halves, a counter of `3`
forces one child and frees the other, and a smaller counter refreshes both. -/
noncomputable def varyK : V × ℕ → PMF ((V × ℕ) × (V × ℕ)) := fun s =>
  if 4 ≤ s.2 then PMF.pure ((v0, s.2 / 2), (v0, s.2 - s.2 / 2))
  else if s.2 = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
  else prodPMF (freshQ μ ν) (freshQ μ ν)

/-- The height-`h` law of the process rooted at a fresh sample. -/
noncomputable def Tlaw (h : ℕ) : PMF (FullLab (V × ℕ) h) :=
  (freshQ μ ν).bind fun s => muM (varyK μ ν v0) s h

end VaryingCounter

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

noncomputable def conditionedGW {J N : ℕ} (theta : Offspring J) :
    Measure (GWWord N → ℕ) :=
  ProbabilityTheory.cond (gwField (N := N) theta) {c | gwSurvives c}

def wedgeN {N : ℕ} : GWWord N → GWWord N → GWWord N
  | [], _ => []
  | _, [] => []
  | a :: v, b :: w => if a = b then a :: wedgeN v w else []

def treeDistN {N : ℕ} (v w : GWWord N) : ℕ :=
  v.length + w.length - 2 * (wedgeN v w).length

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

/-- The shifted positive support generating the chain-regime invariant. -/
noncomputable def shiftSupp {J : ℕ} (theta : Offspring J) : Finset ℕ :=
  ((Finset.range (J + 1)).filter fun k => 2 ≤ k ∧ theta k ≠ 0).image fun k => k - 1

end Classification

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

/-! ## The constants -/

noncomputable def genCW (T : ℝ≥0∞) : ℝ≥0∞ := 32 * T + 4

noncomputable def genGeomC (cN : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ :=
  ((cN : ℝ≥0∞) + 1) * (genCW T * cN) ^ cN

noncomputable def genUC (T : ℝ≥0∞) : ℝ≥0∞ := 16 * T + 4

noncomputable def genXiC (cN : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ := genGeomC cN T * genUC T

noncomputable def genKcC (cN cS : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ :=
  120 + (72 + 48 * (T * cS)) * genXiC cN T

noncomputable def genSmallC (cN cS nA : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ :=
  4 + 3 * genKcC cN cS T
    + (1 + 8 * T) * (12 * (genKcC cN cS T * genXiC cN T)
        + 2 * (((nA : ℝ≥0∞) * genXiC cN T) * ((nA : ℝ≥0∞) * genXiC cN T)))
    + (160 * (genKcC cN cS T * genKcC cN cS T)
        + 4 * ((T * cS) * (genXiC cN T * genXiC cN T)))
    + 85 * (genKcC cN cS T + 12 * genXiC cN T
        + 8 * ((T * cS) * genXiC cN T) + 1)

/-! ## The general matching theorem -/

/-- `thm:main-matching`: for a tree-indexed Markov label field whose counter law is
supported in `{0,…,N}`, the probability that no automorphism matches two independent
samples is at most `genKcC · η`, uniformly in the height. -/
theorem audit_main_matching_failure_le {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (heta : etaG (5 / 2) Rv μ
      ≤ (genSmallC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card
          (2 * N + 3) T)⁻¹) :
    genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
        * etaG (5 / 2) Rv μ ≤ 3⁻¹
      ∧ ∀ h, (∑' x, Tlaw μ ν v0 h x
          * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x)
        ≤ genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
            * etaG (5 / 2) Rv μ := sorry

/-- `thm:main-matching`, the infinite conclusion: two independent consistent
processes admit one root-fixing infinite-tree automorphism with the stated probability. -/
theorem audit_main_matching_infinite {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (heta : etaG (5 / 2) Rv μ
      ≤ (genSmallC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card
          (2 * N + 3) T)⁻¹) :
    ∃ (Omega : Type) (_ : MeasurableSpace Omega) (P : Measure Omega)
      (_ : IsProbabilityMeasure P)
      (X Y : (n : ℕ) → Omega → FullLab (V × ℕ) n),
      (∀ n omega, restrictLab n (X (n + 1) omega) = X n omega) ∧
      (∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega) ∧
      (∀ n, Measurable (fun omega => (X n omega, Y n omega))) ∧
      (∀ n, P.map (fun omega => (X n omega, Y n omega))
        = (prodPMF (Tlaw μ ν v0 n) (Tlaw μ ν v0 n)).toMeasure) ∧
      1 - genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
          * etaG (5 / 2) Rv μ
        ≤ P {omega | ∃ g : List Bool ≃ List Bool, IsTreeAut g ∧
          ∀ s : List Bool, labRel Rv
            (coord (g s).length (X (g s).length omega) (g s))
            (coord s.length (Y s.length omega) s)} := sorry

/-! ## The i.i.d. matching theorem -/

/-- `thm:matching`(1): the leaf bound. -/
theorem audit_graph_leaf_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (h0 : etaGraph μ G ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * etaGraph μ G := sorry

/-- `thm:matching`(2): the full bound. -/
theorem audit_graph_full_matching_bound {V : Type u} (μ : PMF V) (G : SimpleGraph V)
    (hη : etaGraph μ G ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSimIid (compat G) h) x
      ≤ 16 * etaGraph μ G := sorry

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
          (coord s.length (Y s.length ω) s)} := sorry

/-! ## Complete conditioned-infinite classification -/

/-- `thm:trichotomy`, on the part claimed as machine-checked: two conditioned
infinite finite-support Galton--Watson trees are quasi-isometric almost surely
exactly in classes (R), (F), the same `(C_Lambda)`, or (B). -/
theorem audit_offspring_classification_ae_iff {J J' N N' : ℕ}
    (theta : Offspring J) (hJN : J ≤ N)
    (hvalid : theta.IsSupercritical ∨ theta 1 = 1)
    (htop : theta 1 = 1 ∨ (2 ≤ J ∧ 0 < theta J))
    (theta' : Offspring J') (hJN' : J' ≤ N')
    (hvalid' : theta'.IsSupercritical ∨ theta' 1 = 1)
    (htop' : theta' 1 = 1 ∨ (2 ≤ J' ∧ 0 < theta' J')) :
    ∀ᵐ omega ∂((conditionedGW (N := N) theta).prod (conditionedGW (N := N') theta')),
      GraphQuasiIsometric (gwTreeGraph omega.1) (gwTreeGraph omega.2) ↔
        (theta 1 = 1 ∧ theta' 1 = 1) ∨
        (theta 0 = 0 ∧ theta 1 = 0 ∧ theta' 0 = 0 ∧ theta' 1 = 0) ∨
        ((theta 0 = 0 ∧ 0 < theta 1 ∧ theta 1 < 1) ∧
          (theta' 0 = 0 ∧ 0 < theta' 1 ∧ theta' 1 < 1) ∧
          AddSubmonoid.closure (shiftSupp theta : Set ℕ) =
            AddSubmonoid.closure (shiftSupp theta' : Set ℕ)) ∨
        (0 < theta 0 ∧ 0 < theta' 0) := sorry

/-! ## Universality in the two-value family -/

/-- `thm:twovalue`: two independent Galton--Watson trees whose offspring law is
supported on `{1,2}` are almost surely quasi-isometric. -/
theorem audit_twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((bernoulliField ht0 ht1).prod (bernoulliField ht0 ht1))
      {ω | ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K (InTree ω.1) (InTree ω.2) f} = 0 := sorry

/-- The quantitative half of `thm:twovalue`: above a threshold, failure of a
`(D²+3)`-quasi-isometry has probability at most the explicit rate. -/
theorem audit_twovalue_rate_tree {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ((bernoulliField ht0.le ht1.le).prod (bernoulliField ht0.le ht1.le))
          {ω | ¬ ∃ f : Word → Word,
            IsQIWith (D ^ 2 + 3) (InTree ω.1) (InTree ω.2) f}
        ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := sorry

end Challenge
