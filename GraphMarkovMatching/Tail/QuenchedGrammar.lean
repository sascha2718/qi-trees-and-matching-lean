/-
The mixture-free target grammar over a quenched counter environment.

Every target carries the finite counter environment below its root.  A
forced target has root state `v0` and an explicit counter; a fresh target
has a `μ`-root state and reads its counter from the environment.  Both have
exactly two component successors.  In particular, no successor is the
aggregate law `Tlaw` and no child-pair target is `XiBar`.
-/
import GraphMarkovMatching.Tail.Quenched
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

/-- Root mode of a quenched target. -/
inductive QMode
  | Z (k : ℕ)
  | F
  deriving DecidableEq

/-- A quenched target at height `h`: a root mode together with the complete
counter environment below it. -/
structure QTgt (h : ℕ) where
  mode : QMode
  env : FullLab ℕ h

/-- The actual counter at the root of a quenched target. -/
def QTgt.counter {h : ℕ} (t : QTgt h) : ℕ :=
  match t.mode with
  | QMode.Z k => k
  | QMode.F => envRoot h t.env

/-- Interpretation of a quenched target as a tree law. -/
noncomputable def qInterp (μ : PMF V) (v0 : V) {h : ℕ} (t : QTgt h) :
    PMF (FullLab (V × ℕ) h) :=
  match t.mode with
  | QMode.Z k => quenchedMuM μ v0 (v0, k) h t.env
  | QMode.F => quenchedFresh μ v0 h t.env

/-- Left child target. -/
def qchild0 {h : ℕ} (t : QTgt (h + 1)) : QTgt h :=
  let k := t.counter
  let e0 := envLeft t.env
  if 4 ≤ k then ⟨QMode.Z (k / 2), e0⟩
  else if k = 3 then ⟨QMode.Z 2, e0⟩
  else ⟨QMode.F, e0⟩

/-- Right child target. -/
def qchild1 {h : ℕ} (t : QTgt (h + 1)) : QTgt h :=
  let k := t.counter
  let e1 := envRight t.env
  if 4 ≤ k then ⟨QMode.Z (k - k / 2), e1⟩
  else ⟨QMode.F, e1⟩

/-- Product law of the two quenched child targets. -/
noncomputable def qChildren (μ : PMF V) (v0 : V) {h : ℕ}
    (t : QTgt (h + 1)) : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h) :=
  prodPMF (qInterp μ v0 (qchild0 t)) (qInterp μ v0 (qchild1 t))

@[simp] lemma QTgt.counter_Z {h : ℕ} (k : ℕ) (e : FullLab ℕ h) :
    (QTgt.mk (QMode.Z k) e).counter = k := rfl

@[simp] lemma QTgt.counter_F {h : ℕ} (e : FullLab ℕ h) :
    (QTgt.mk QMode.F e).counter = envRoot h e := rfl

@[simp] lemma qInterp_Z (μ : PMF V) (v0 : V) {h : ℕ} (k : ℕ)
    (e : FullLab ℕ h) :
    qInterp μ v0 ⟨QMode.Z k, e⟩ = quenchedMuM μ v0 (v0, k) h e := rfl

@[simp] lemma qInterp_F (μ : PMF V) (v0 : V) {h : ℕ}
    (e : FullLab ℕ h) :
    qInterp μ v0 ⟨QMode.F, e⟩ = quenchedFresh μ v0 h e := rfl

/-! ### Exact component child identities -/

/-- A forced quenched target is its component child product with its fixed
root attached. -/
lemma qInterp_Z_succ (μ : PMF V) (v0 : V) {h : ℕ} (k : ℕ)
    (e : FullLab ℕ (h + 1)) :
    qInterp μ v0 (⟨QMode.Z k, e⟩ : QTgt (h + 1))
      = (qChildren μ v0 (⟨QMode.Z k, e⟩ : QTgt (h + 1))).map
          (branch (v0, k)) := by
  rw [qInterp_Z, quenchedMuM_succ]
  simp only [qChildren, qchild0, qchild1, QTgt.counter_Z]
  by_cases h4 : 4 ≤ k
  · simp only [h4, if_pos, qInterp_Z]
  · by_cases h3 : k = 3
    · subst k
      simp only [show ¬ 4 ≤ 3 by omega, if_false, if_true, qInterp_Z, qInterp_F,
        quenchedFresh]
    · simp only [h4, h3, if_false, qInterp_F, quenchedFresh]

/-- A fresh quenched target samples only its root state; below the root its
law is the same component child product. -/
lemma qInterp_F_succ (μ : PMF V) (v0 : V) {h : ℕ}
    (e : FullLab ℕ (h + 1)) :
    qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1))
      = μ.bind fun v =>
          (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1))).map
            (branch (v, envRoot (h + 1) e)) := by
  rw [qInterp_F, quenchedFresh]
  congr 1
  funext v
  rw [quenchedMuM_succ]
  simp only [qChildren, qchild0, qchild1, QTgt.counter_F]
  by_cases h4 : 4 ≤ envRoot (h + 1) e
  · simp only [h4, if_pos, qInterp_Z]
  · by_cases h3 : envRoot (h + 1) e = 3
    · rw [h3]
      simp only [show ¬ 4 ≤ 3 by omega, if_false, if_true, qInterp_Z, qInterp_F,
        quenchedFresh]
    · simp only [h4, h3, if_false, qInterp_F, quenchedFresh]

/-- The quenched child target is always a product of two component laws;
there is no aggregate `XiBar` target. -/
lemma qChildren_eq_prod (μ : PMF V) (v0 : V) {h : ℕ}
    (t : QTgt (h + 1)) :
    qChildren μ v0 t
      = prodPMF (qInterp μ v0 (qchild0 t)) (qInterp μ v0 (qchild1 t)) := rfl

end GraphMarkovMatching
