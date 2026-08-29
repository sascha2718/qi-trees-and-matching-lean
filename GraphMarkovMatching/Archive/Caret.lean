/-
The Galton--Watson caret layer: the caret-state Markov label system
encoding a finitely supported offspring law with `θ₀ = 0` on the complete
binary tree.

* States: caret tops `mkTop m ℓ` carrying the arity `m` and the quantised
  chain level `ℓ`, and interior comb positions `mkComb m j`.
* The compatibility relation sees only the level: `|lev s - lev t| ≤ 1`,
  blind to the caret structure; this is what evades the frozen-ray
  obstruction.
* The kernel: a continuing state emits its continuation and one fresh top in
  uniform random order (the random turn); a terminal state emits two fresh
  tops. The fresh-top law is `â ⊗ p` for an arity law `â` and a level law
  `p`, both arbitrary PMFs on `ℕ` here; the application takes `p` to be the
  quantised geometric law of base `θ₁`.

Certified here: the system's structural properties, the reduction of the
root budget `η_ι` to the pure level law (the arity integrates out), and the
instantiated matching theorems at every finite height and on the infinite
tree, with the kernel budgets `ε`, `β` as hypotheses. WARNING: those budget
hypotheses are unsatisfiable for the intended level laws: see
`CaretObstruction.lean` (`caret_etaD_eq_top`), which refutes this encoding
as stated.  The caret system is superseded by the varying-offspring process
(`Varying`; `arbitrary_offspring_matching.tex` `sec:statement`), which runs the
change-of-measure route instead of per-state budgets.
-/
import GraphMarkovMatching.Archive.MarkovInfinite
import Mathlib.Probability.Distributions.Uniform

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

/-! ### The caret state space -/

/-- Caret states: tops `(m, ℓ)` (arity, level) or interior combs `(m, j)`. -/
def CaretState : Type := (ℕ × ℕ) ⊕ (ℕ × ℕ)

/-- A caret top of arity `m` and quantised chain level `ℓ`. -/
def mkTop (m ℓ : ℕ) : CaretState := Sum.inl (m, ℓ)

/-- An interior comb position `j` of an `m`-caret. -/
def mkComb (m j : ℕ) : CaretState := Sum.inr (m, j)

instance : Countable CaretState := by
  unfold CaretState
  infer_instance

instance : MeasurableSpace CaretState := ⊤

instance : MeasurableSingletonClass CaretState := ⟨fun _ => trivial⟩

/-- The level of a state: the quantised chain level at tops, `0` inside
carets. -/
def lev : CaretState → ℕ
  | Sum.inl (_, ℓ) => ℓ
  | Sum.inr _ => 0

@[simp] lemma lev_mkTop (m ℓ : ℕ) : lev (mkTop m ℓ) = ℓ := rfl

@[simp] lemma lev_mkComb (m j : ℕ) : lev (mkComb m j) = 0 := rfl

/-! ### The level relation -/

/-- Nearest-neighbour compatibility of levels. -/
def levRel (a b : ℕ) : Prop := a ≤ b + 1 ∧ b ≤ a + 1

/-- The caret compatibility relation: levels within one, blind to structure. -/
def caretRel (s t : CaretState) : Prop := levRel (lev s) (lev t)

lemma caretRel_refl (s : CaretState) : caretRel s s :=
  ⟨Nat.le_succ _, Nat.le_succ _⟩

lemma caretRel_symm (s t : CaretState) (h : caretRel s t) : caretRel t s :=
  ⟨h.2, h.1⟩

/-! ### The kernel -/

/-- The fresh-top law: arity `â`, level `p`, independently. -/
noncomputable def freshTop (arity p : PMF ℕ) : PMF CaretState :=
  arity.bind fun m => p.map fun ℓ => mkTop m ℓ

/-- The caret continuation: `top (m, ·)` continues into `comb (m, 2)` when
`m ≥ 3`; `comb (m, j)` continues into `comb (m, j+1)` while `j + 1 < m`;
terminal states have no continuation. -/
def contOf : CaretState → Option CaretState
  | Sum.inl (m, _) => if 3 ≤ m then some (mkComb m 2) else none
  | Sum.inr (m, j) => if j + 2 ≤ m then some (mkComb m (j + 1)) else none

/-- The caret kernel: a continuing state emits its continuation and a fresh
top in uniform random order; a terminal state emits two fresh tops. -/
noncomputable def caretKernel (arity p : PMF ℕ) (s : CaretState) :
    PMF (CaretState × CaretState) :=
  match contOf s with
  | some c => (PMF.uniformOfFintype Bool).bind fun b =>
      (freshTop arity p).map fun f => bif b then (c, f) else (f, c)
  | none => prodPMF (freshTop arity p) (freshTop arity p)

/-! ### The root budget reduces to the level law -/

/-- The bad degree of any state against the fresh-top law depends only on
its level: the arity integrates out. -/
lemma qE_freshTop (arity p : PMF ℕ) (s : CaretState) :
    qE (freshTop arity p) caretRel s = qE p (fun a b => levRel a b) (lev s) := by
  rw [freshTop, qE_bind]
  calc (∑' m, arity m * qE (p.map fun ℓ => mkTop m ℓ) caretRel s)
      = ∑' m, arity m * qE p (fun a b => levRel a b) (lev s) := by
        refine tsum_congr fun m => ?_
        congr 1
        rw [qE_map, qE_eq_tsum_mul]
        exact tsum_congr fun ℓ => rfl
    _ = qE p (fun a b => levRel a b) (lev s) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **The root budget in level form**: the mean fresh-vs-fresh mismatch is a
functional of the level law alone,

    `η_ι = ∑' ℓ, p ℓ · q_p(ℓ)` (nearest-neighbour bad degree on levels). -/
lemma etaRoot_caret_eq (arity p : PMF ℕ) :
    ∑' s, freshTop arity p s * qE (freshTop arity p) caretRel s
      = ∑' ℓ, p ℓ * qE p (fun a b => levRel a b) ℓ := by
  calc (∑' s, freshTop arity p s * qE (freshTop arity p) caretRel s)
      = ∑' s, freshTop arity p s * qE p (fun a b => levRel a b) (lev s) :=
        tsum_congr fun s => by rw [qE_freshTop]
    _ = ∑' m, arity m * ∑' ℓ, p ℓ * qE p (fun a b => levRel a b) ℓ := by
        rw [freshTop, tsum_bind_mul]
        refine tsum_congr fun m => ?_
        congr 1
        rw [tsum_map_mul]
        exact tsum_congr fun ℓ => by rw [lev_mkTop]
    _ = ∑' ℓ, p ℓ * qE p (fun a b => levRel a b) ℓ := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### The instantiated matching theorems -/

/-- **The caret matching bound at every finite height**: for the caret
system with arity law `â` and level law `p`, given the kernel budgets and
the closure inequality, two independent root-mixture samples fail to match
with probability at most the level-law root budget plus the ceiling. -/
theorem caretMatching_failure_le {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (arity p : PMF ℕ) (ε β B : ℝ≥0∞)
    (hEta : ∀ s t, caretRel s t → etaD α (caretKernel arity p) caretRel s t ≤ ε)
    (hBeta : ∀ s t, caretRel s t → betaD (caretKernel arity p) caretRel s t ≤ β)
    (hclose : ε
        + ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
          + β * (B + B + ENNReal.ofReal (2 * α) * (B * B)))
        + ENNReal.ofReal (2 * α) * (ε
            * ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
              + (B + B + ENNReal.ofReal (2 * α) * (B * B)))) ≤ B)
    (n : ℕ) :
    ∑' x, ((freshTop arity p).bind fun s => muM (caretKernel arity p) s n) x
        * qE ((freshTop arity p).bind fun t => muM (caretKernel arity p) t n)
            (fullSim caretRel n) x
      ≤ (∑' ℓ, p ℓ * qE p (fun a b => levRel a b) ℓ) + B := by
  rw [← etaRoot_caret_eq arity p]
  exact markovMatching_failure_le_closed (caretKernel arity p) caretRel hα hδ hL0 hL
    hK0 hK caretRel_symm ε β B hEta hBeta hclose (freshTop arity p) n

/-- **The caret matching theorem on the infinite tree**: with the same
budgets, two independent infinite caret labellings (through compatible
measurable level projections) admit a single automorphism of the infinite
binary tree matching every vertex with probability at least
`1 - (η_ι + B)`, the root budget in level form. -/
theorem caretMatching_infinite {Ω : Type} [MeasurableSpace Ω] (Pm : Measure Ω)
    [IsProbabilityMeasure Pm]
    {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (arity p : PMF ℕ) (ε β B : ℝ≥0∞)
    (hEta : ∀ s t, caretRel s t → etaD α (caretKernel arity p) caretRel s t ≤ ε)
    (hBeta : ∀ s t, caretRel s t → betaD (caretKernel arity p) caretRel s t ≤ β)
    (hclose : ε
        + ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
          + β * (B + B + ENNReal.ofReal (2 * α) * (B * B)))
        + ENNReal.ofReal (2 * α) * (ε
            * ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
              + (B + B + ENNReal.ofReal (2 * α) * (B * B)))) ≤ B)
    (X Y : (n : ℕ) → Ω → FullLab CaretState n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Pm.map (fun ω => (X n ω, Y n ω))
        = (prodPMF ((freshTop arity p).bind fun s => muM (caretKernel arity p) s n)
            ((freshTop arity p).bind fun s => muM (caretKernel arity p) s n)).toMeasure) :
    1 - ((∑' ℓ, p ℓ * qE p (fun a b => levRel a b) ℓ) + B)
      ≤ Pm {ω | InfMatch caretRel (fun n => X n ω) (fun n => Y n ω)} := by
  rw [← etaRoot_caret_eq arity p]
  exact markovMatching_infinite Pm (caretKernel arity p) caretRel hα hδ hL0 hL hK0 hK
    caretRel_symm ε β B hEta hBeta hclose (freshTop arity p) X Y hX hY hpair hlaw

end GraphMarkovMatching
