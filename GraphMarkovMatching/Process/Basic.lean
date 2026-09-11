/-
Abstract Markov label systems: a state space `S` with a child kernel `P : S → PMF (S × S)`, the height-`n` tree law `muM`
started from a frozen root state, and the pair mixture `pairMix` that the
recursion consumes.

Design notes:

* Labellings reuse `FullLab` from the `Support` support layer; the state at a
  vertex is
  its label, so the root state of a sample is `rootLab`.
* `FullLab S 0` and `FullLab S (n+1)` unfold definitionally to `S` and to a
  product, and elaboration happily mixes the unfolded and folded types, which
  then defeats `rw`'s syntactic matching. All constructions therefore go
  through the explicitly typed wrappers `leaf` and `branch`, keeping every
  term uniformly at the `FullLab` type.
* `muM P s (n+1)` is *defined* as the pushforward of `pairMix P s n` under
  `branch s`, so the measure recursion is definitional.
* The change-of-variable helpers `tsum_bind_mul` / `tsum_map_mul` are the
  only measure-theoretic moves the potential layer needs: everything is a
  `tsum` in `ℝ≥0∞` and is unconditionally covered by Fubini's theorem as in
  the support layer.
-/
import GraphMarkovMatching.Support.Tree
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {S : Type u}

/-! ### Change of variables for `tsum` against `bind` and `map` -/

/-- Expectation of `F` under a bound PMF, as an iterated `tsum`. -/
lemma tsum_bind_mul {A B : Type u} (w : PMF A) (f : A → PMF B) (F : B → ℝ≥0∞) :
    ∑' b, (w.bind f) b * F b = ∑' a, w a * ∑' b, f a b * F b := by
  calc ∑' b, (w.bind f) b * F b
      = ∑' b, ∑' a, w a * f a b * F b := by
        refine tsum_congr fun b => ?_
        rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' b, w a * f a b * F b := ENNReal.tsum_comm
    _ = ∑' a, w a * ∑' b, f a b * F b := by
        refine tsum_congr fun a => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun b => by ring

/-- Expectation of `F` under a pushforward PMF: `𝔼_{μ.map g}[F] = 𝔼_μ[F ∘ g]`. -/
lemma tsum_map_mul {A B : Type u} (μ : PMF A) (g : A → B) (F : B → ℝ≥0∞) :
    ∑' b, (μ.map g) b * F b = ∑' a, μ a * F (g a) := by
  calc ∑' b, (μ.map g) b * F b
      = ∑' b, ∑' a, (if b = g a then μ a else 0) * F b := by
        refine tsum_congr fun b => ?_
        rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' b, (if b = g a then μ a else 0) * F b := ENNReal.tsum_comm
    _ = ∑' a, μ a * F (g a) := by
        refine tsum_congr fun a => ?_
        rw [show (∑' b, (if b = g a then μ a else 0) * F b)
            = ∑' b, if b = g a then μ a * F b else 0 from
          tsum_congr fun b => by by_cases h : b = g a <;> simp [h]]
        exact tsum_ite_eq (g a) fun b => μ a * F b

/-! ### Typed wrappers for `FullLab` -/

/-- A height-`0` labelling is a single state, at the `FullLab` type. -/
def leaf (s : S) : FullLab S 0 := s

/-- Attach a root state to a pair of subtrees, at the `FullLab` type. -/
def branch {n : ℕ} (s : S) (p : FullLab S n × FullLab S n) : FullLab S (n + 1) :=
  (s, p.1, p.2)

/-- The root label of a full labelling. -/
def rootLab : (n : ℕ) → FullLab S n → S
  | 0, x => x
  | _ + 1, x => x.1

@[simp] lemma rootLab_leaf (s : S) : rootLab 0 (leaf s) = s := rfl

@[simp] lemma rootLab_branch {n : ℕ} (s : S) (p : FullLab S n × FullLab S n) :
    rootLab (n + 1) (branch s p) = s := rfl

/-! ### The tree law of a Markov label system -/

variable (P : S → PMF (S × S))

/-- The height-`n` tree law started from root state `s`: the root carries the
label `s`, the children pattern is drawn from `P s`, and the two subtrees are
conditionally independent copies started from the pattern states. -/
noncomputable def muM : S → (n : ℕ) → PMF (FullLab S n)
  | s, 0 => PMF.pure (leaf s)
  | s, n + 1 =>
      ((P s).bind fun στ => prodPMF (muM στ.1 n) (muM στ.2 n)).map (branch s)

/-- The pair mixture at `s`: the joint law of the two subtrees of an
`s`-rooted sample, i.e. the kernel mixture of subtree product laws. -/
noncomputable def pairMix (s : S) (n : ℕ) : PMF (FullLab S n × FullLab S n) :=
  (P s).bind fun στ => prodPMF (muM P στ.1 n) (muM P στ.2 n)

@[simp] lemma muM_zero (s : S) : muM P s 0 = PMF.pure (leaf s) := rfl

/-- The measure recursion, definitionally: an `(n+1)`-sample is a pair-mixture
sample with the root state attached. -/
lemma muM_succ (s : S) (n : ℕ) :
    muM P s (n + 1) = (pairMix P s n).map (branch s) := rfl

/-- Samples carry their root state: `rootLab = s` wherever `muM P s n` charges. -/
lemma rootLab_of_ne_zero : ∀ (n : ℕ) (s : S) (x : FullLab S n),
    muM P s n x ≠ 0 → rootLab n x = s := by
  intro n
  cases n with
  | zero =>
      intro s x hx
      rw [muM_zero, PMF.pure_apply] at hx
      by_cases h : x = leaf s
      · rw [h, rootLab_leaf]
      · simp [h] at hx
  | succ n =>
      intro s x hx
      rw [muM_succ, PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hx
      push Not at hx
      obtain ⟨p, hp⟩ := hx
      by_cases h : x = branch s p
      · rw [h, rootLab_branch]
      · simp [h] at hp

/-- Contrapositive form: a labelling whose root is not `s` has `muM`-mass zero. -/
lemma muM_eq_zero_of_rootLab_ne {n : ℕ} {s : S} {x : FullLab S n}
    (h : rootLab n x ≠ s) : muM P s n x = 0 := by
  by_contra hc
  exact h (rootLab_of_ne_zero P n s x hc)

end GraphMarkovMatching
