/-
Comparator solution file: the headline theorems of `Challenge.lean`, proved.

This file repeats the challenge's definitions verbatim, so that the declarations
its statements use carry the same names and the same bodies as the challenge's,
and then discharges each theorem from the libraries. Comparator compares the two
exported environments declaration by declaration; the challenge is never imported.
-/
import GraphMarkovMatching.Closure.Numeric
import GraphMatching.Graph
import GraphMatching.Kolmogorov
import GraphMatching.AutBridge
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

instance instIsProbabilityBernoulliLaw {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (bernoulliLaw ht ht1) :=
  inferInstanceAs
    (IsProbabilityMeasure (ProbabilityTheory.bernoulliMeasure true false ⟨t, ht, ht1⟩))

/-- The i.i.d. Bernoulli field indexed by the vertices of the tree. -/
noncomputable def bernoulliField {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : Measure (Word → Bool) :=
  Measure.infinitePi (fun _ : Word => bernoulliLaw ht ht1)

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

/-- The challenge's varying-counter kernel is the library's. -/
lemma varyK_eq {V : Type} (μ : PMF V) (ν : PMF ℕ) (v0 : V) :
    varyK μ ν v0 = GraphMarkovMatching.varyK μ ν v0 := by
  funext s
  simp only [varyK, GraphMarkovMatching.varyK,
    show freshQ μ ν = GraphMarkovMatching.freshQ μ ν from prodPMF_eq μ ν, prodPMF_eq]

/-- The challenge's fresh-rooted law is the library's, along `toLib`. -/
lemma Tlaw_eq {V : Type} (μ : PMF V) (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    (Tlaw μ ν v0 h).map (toLib (V × ℕ) h) = GraphMarkovMatching.Tlaw μ ν v0 h := by
  simp only [Tlaw, GraphMarkovMatching.Tlaw, PMF.map_bind]
  rw [show freshQ μ ν = GraphMarkovMatching.freshQ μ ν from prodPMF_eq μ ν]
  congr 1
  funext s
  rw [muM_eq, varyK_eq]

/-- The pointwise form: the equivalence carries the mass across. -/
lemma Tlaw_apply {V : Type} (μ : PMF V) (ν : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (V × ℕ) h) :
    Tlaw μ ν v0 h x = GraphMarkovMatching.Tlaw μ ν v0 h (toLib (V × ℕ) h x) := by
  conv_rhs => rw [← Tlaw_eq μ ν v0 h]
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro b hb
    exact if_neg fun hh => hb ((toLib (V × ℕ) h).injective hh.symm)

/-- The potential and the constants are literally the library's. -/
lemma etaG_eq : @etaG = @GraphMarkovMatching.etaG := rfl
lemma genKcC_eq : @genKcC = @GraphMarkovMatching.genKcC := rfl
lemma genSmallC_eq : @genSmallC = @GraphMarkovMatching.genSmallC := rfl

/-! ## The general matching theorem -/

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
            * etaG (5 / 2) Rv μ := by
  rw [etaG_eq, genSmallC_eq] at heta
  rw [etaG_eq, genKcC_eq]
  obtain ⟨h1, h2⟩ := GraphMarkovMatching.main_matching_failure_le (Rv := Rv) (μ := μ) (v0 := v0)
    ν N S hrefl hsymm hhalf hN hS hSne hSsupp T hT heta
  refine ⟨h1, fun h => ?_⟩
  refine le_of_eq_of_le ?_ (h2 h)
  rw [← (toLib (V × ℕ) h).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [Tlaw_apply μ ν v0 h x]
  congr 1
  rw [qE, GraphMarkovMatching.Support.qE, ← (toLib (V × ℕ) h).tsum_eq]
  refine tsum_congr fun y => ?_
  rw [Tlaw_apply μ ν v0 h y, fullSim_iff]
  rfl



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

/-! ## Universality in the two-value family -/

/-- `thm:twovalue`: two independent Galton--Watson trees whose offspring law is
supported on `{1,2}` are almost surely quasi-isometric. -/
theorem audit_twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((bernoulliField ht0 ht1).prod (bernoulliField ht0 ht1))
      {ω | ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K (InTree ω.1) (InTree ω.2) f} = 0 := by
  rw [bernoulliField_eq]
  refine Eq.trans ?_ (ChainClasses.twovalue_ae_tree_family ht0 ht1)
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, inTree_eq, isQIWith_eq]

end Challenge
