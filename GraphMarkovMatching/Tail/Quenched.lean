/-
Quenched counter environments for the unbounded-offspring argument.

The fresh law contains a new `ν`-mixture every time a cascade returns to a
fresh vertex.  Resolving an inverse degree against that mixture introduces
inverse atoms and is unusable for an infinite support.  The definitions in
this file instead pre-sample an independent counter at every vertex of the
finite binary tree.  Conditional on this environment all fresh counters are
components, never mixtures; averaging over environments is postponed until
after the screened estimates have been applied.

`counterEnvLaw` is the iid `ν`-law on counter-labelled full binary trees and
`quenchedMuM` is the varying process conditional on such a tree.  The main
structural theorem below says that averaging the quenched law recovers the
original Markov law exactly.
-/
import GraphMarkovMatching.Process.Cells
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

/-- The iid counter environment on a full binary tree of height `h`. -/
noncomputable def counterEnvLaw (ν : PMF ℕ) : (h : ℕ) → PMF (FullLab ℕ h)
  | 0 => ν.map leaf
  | h + 1 =>
      ν.bind fun k =>
        (prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).map (branch k)

@[simp] lemma counterEnvLaw_zero (ν : PMF ℕ) :
    counterEnvLaw ν 0 = ν.map leaf := rfl

lemma counterEnvLaw_succ (ν : PMF ℕ) (h : ℕ) :
    counterEnvLaw ν (h + 1)
      = ν.bind fun k =>
          (prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).map (branch k) := rfl

/-- The counter stored at the root of an environment. -/
def envRoot (h : ℕ) (e : FullLab ℕ h) : ℕ := rootLab h e

/-- The left sub-environment of a positive-height environment. -/
def envLeft {h : ℕ} (e : FullLab ℕ (h + 1)) : FullLab ℕ h := e.2.1

/-- The right sub-environment of a positive-height environment. -/
def envRight {h : ℕ} (e : FullLab ℕ (h + 1)) : FullLab ℕ h := e.2.2

@[simp] lemma envRoot_branch {h : ℕ} (k : ℕ)
    (ep : FullLab ℕ h × FullLab ℕ h) :
    envRoot (h + 1) (branch k ep) = k := rfl

@[simp] lemma envLeft_branch {h : ℕ} (k : ℕ)
    (ep : FullLab ℕ h × FullLab ℕ h) :
    envLeft (branch k ep) = ep.1 := rfl

@[simp] lemma envRight_branch {h : ℕ} (k : ℕ)
    (ep : FullLab ℕ h × FullLab ℕ h) :
    envRight (branch k ep) = ep.2 := rfl

variable (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- The varying process conditional on a complete counter environment.

The environment counter at the current vertex is ignored because the
started label already contains its counter.  When a child is fresh, its
counter is read from the root of the corresponding child environment.
-/
noncomputable def quenchedMuM :
    (s : V × ℕ) → (h : ℕ) → FullLab ℕ h → PMF (FullLab (V × ℕ) h)
  | s, 0, _ => PMF.pure (leaf s)
  | s, h + 1, e =>
      let e0 := envLeft e
      let e1 := envRight e
      let Lfresh := μ.bind fun v =>
        quenchedMuM (v, envRoot h e0) h e0
      let Rfresh := μ.bind fun v =>
        quenchedMuM (v, envRoot h e1) h e1
      let children :=
        if 4 ≤ s.2 then
          prodPMF
            (quenchedMuM (v0, s.2 / 2) h e0)
            (quenchedMuM (v0, s.2 - s.2 / 2) h e1)
        else if s.2 = 3 then
          prodPMF (quenchedMuM (v0, 2) h e0) Rfresh
        else
          prodPMF Lfresh Rfresh
      children.map (branch s)

/-- A fresh quenched tree: only the root state is sampled; the root counter
comes from the environment. -/
noncomputable def quenchedFresh (h : ℕ) (e : FullLab ℕ h) :
    PMF (FullLab (V × ℕ) h) :=
  μ.bind fun v => quenchedMuM μ v0 (v, envRoot h e) h e

@[simp] lemma quenchedMuM_zero (s : V × ℕ) (e : FullLab ℕ 0) :
    quenchedMuM μ v0 s 0 e = PMF.pure (leaf s) := rfl

lemma quenchedMuM_succ (s : V × ℕ) (h : ℕ) (e : FullLab ℕ (h + 1)) :
    quenchedMuM μ v0 s (h + 1) e
      = (let e0 := envLeft e
         let e1 := envRight e
         let Lfresh := μ.bind fun v =>
           quenchedMuM μ v0 (v, envRoot h e0) h e0
         let Rfresh := μ.bind fun v =>
           quenchedMuM μ v0 (v, envRoot h e1) h e1
         let children :=
           if 4 ≤ s.2 then
             prodPMF
               (quenchedMuM μ v0 (v0, s.2 / 2) h e0)
               (quenchedMuM μ v0 (v0, s.2 - s.2 / 2) h e1)
           else if s.2 = 3 then
             prodPMF (quenchedMuM μ v0 (v0, 2) h e0) Rfresh
           else
             prodPMF Lfresh Rfresh
         children.map (branch s)) := rfl

/-! ### Environment averaging -/

/-- Averaging a function which ignores the root counter of an environment
reduces to the product law of its two sub-environments. -/
lemma counterEnvLaw_succ_bind_ignore_root {D : Type} (h : ℕ)
    (F : FullLab ℕ h → FullLab ℕ h → PMF D) :
    (counterEnvLaw ν (h + 1)).bind
        (fun e => F (envLeft e) (envRight e))
      = (prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).bind
          (fun ep => F ep.1 ep.2) := by
  rw [counterEnvLaw_succ, PMF.bind_bind]
  calc
    (ν.bind fun k =>
        ((prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).map (branch k)).bind
          (fun e => F (envLeft e) (envRight e)))
        = ν.bind fun _ =>
            (prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).bind
              (fun ep => F ep.1 ep.2) := by
            congr 1
            funext k
            rw [PMF.bind_map]
            rfl
    _ = (prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).bind
          (fun ep => F ep.1 ep.2) := PMF.bind_const _ _

/-- The root counter and the two child environments can be exposed as
independent variables. -/
lemma counterEnvLaw_succ_bind_root {D : Type} (h : ℕ)
    (F : ℕ → FullLab ℕ h → FullLab ℕ h → PMF D) :
    (counterEnvLaw ν (h + 1)).bind
        (fun e => F (envRoot (h + 1) e) (envLeft e) (envRight e))
      = ν.bind fun k =>
          (prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).bind
            (fun ep => F k ep.1 ep.2) := by
  rw [counterEnvLaw_succ, PMF.bind_bind]
  congr 1
  funext k
  rw [PMF.bind_map]
  rfl

/-- Averaging a quenched fresh tree over its environment gives the original
fresh law.  This statement is proved simultaneously with the started-law
identity below. -/
theorem counterEnv_bind_quenched (h : ℕ) :
    (∀ s : V × ℕ,
      (counterEnvLaw ν h).bind (quenchedMuM μ v0 s h)
        = muM (varyK μ ν v0) s h)
    ∧ (counterEnvLaw ν h).bind (quenchedFresh μ v0 h)
        = Tlaw (V := V) μ ν v0 h := by
  induction h with
  | zero =>
      constructor
      · intro s
        apply PMF.ext
        intro x
        rw [PMF.bind_apply, muM_zero]
        calc
          (∑' e, counterEnvLaw ν 0 e * quenchedMuM μ v0 s 0 e x)
              = ∑' e, counterEnvLaw ν 0 e * (PMF.pure (leaf s)) x := by
                  refine tsum_congr fun e => ?_
                  rw [quenchedMuM_zero]
          _ = (PMF.pure (leaf s)) x := by
                  rw [ENNReal.tsum_mul_right, (counterEnvLaw ν 0).tsum_coe,
                    one_mul]
      · apply PMF.ext
        intro x
        rw [PMF.bind_apply, Tlaw, PMF.bind_apply]
        simp only [quenchedFresh, PMF.bind_apply, quenchedMuM_zero, muM_zero]
        rw [counterEnvLaw_zero]
        -- Both sides are the independent `(μ,ν)` mixture of root labels.
        calc
          (∑' e, (ν.map leaf) e * ∑' v, μ v * (PMF.pure (leaf (v, envRoot 0 e))) x)
              = ∑' k, ν k * ∑' v, μ v * (PMF.pure (leaf (v, k))) x := by
                  rw [tsum_map_mul]
                  rfl
          _ = ∑' s : V × ℕ, freshQ μ ν s * (PMF.pure (leaf s)) x := by
                  calc
                    (∑' k, ν k * ∑' v, μ v * (PMF.pure (leaf (v, k))) x)
                        = ∑' k, ∑' v,
                            ν k * (μ v * (PMF.pure (leaf (v, k))) x) := by
                              refine tsum_congr fun k => ?_
                              rw [ENNReal.tsum_mul_left]
                    _ = ∑' v, ∑' k,
                          ν k * (μ v * (PMF.pure (leaf (v, k))) x) :=
                            ENNReal.tsum_comm
                    _ = ∑' s : V × ℕ,
                          ν s.2 * (μ s.1 * (PMF.pure (leaf s)) x) :=
                            by
                              simpa using
                                (ENNReal.tsum_prod'
                                  (f := fun s : V × ℕ =>
                                    ν s.2 * (μ s.1 * (PMF.pure (leaf s)) x))).symm
                    _ = ∑' s : V × ℕ,
                          freshQ μ ν s * (PMF.pure (leaf s)) x := by
                            refine tsum_congr fun s => ?_
                            simp only [freshQ, prodPMF_apply]
                            ring
  | succ h ih =>
      obtain ⟨ihM, ihF⟩ := ih
      have hMsucc : ∀ s : V × ℕ,
          (counterEnvLaw ν (h + 1)).bind (quenchedMuM μ v0 s (h + 1))
            = muM (varyK μ ν v0) s (h + 1) := by
        rintro ⟨sv, sk⟩
        -- The environment root is unused.  After removing it, independence
        -- of the two sub-environments and the induction hypotheses recover
        -- exactly the three cases of `varyK`.
        let F : FullLab ℕ h → FullLab ℕ h → PMF (FullLab (V × ℕ) (h + 1)) :=
          fun e0 e1 =>
            let Lfresh := quenchedFresh μ v0 h e0
            let Rfresh := quenchedFresh μ v0 h e1
            let children :=
              if 4 ≤ sk then
                prodPMF
                  (quenchedMuM μ v0 (v0, sk / 2) h e0)
                  (quenchedMuM μ v0 (v0, sk - sk / 2) h e1)
              else if sk = 3 then
                prodPMF (quenchedMuM μ v0 (v0, 2) h e0) Rfresh
              else
                prodPMF Lfresh Rfresh
            children.map (branch (sv, sk))
        have hq : quenchedMuM μ v0 (sv, sk) (h + 1)
            = fun e => F (envLeft e) (envRight e) := by
          funext e
          rw [quenchedMuM_succ]
          simp only [F, quenchedFresh]
        rw [hq, counterEnvLaw_succ_bind_ignore_root ν h F]
        rw [muM_varyK_succ]
        -- The remaining calculation is the componentwise bind/product
        -- exchange, split according to the deterministic cascade rule.
        simp only [F]
        by_cases h4 : 4 ≤ sk
        · simp only [h4, if_pos]
          rw [← PMF.map_bind, prodPMF_bind_prodPMF,
            ihM (v0, sk / 2), ihM (v0, sk - sk / 2),
            Xi_of_four_le μ ν v0 h4 h]
          rfl
        · by_cases h3 : sk = 3
          · simp only [h3, if_pos]
            subst sk
            simp only [show ¬4 ≤ 3 by omega, if_false]
            rw [← PMF.map_bind, prodPMF_bind_prodPMF,
              ihM (v0, 2), ihF, Xi_three μ ν v0 h]
            rfl
          · have h2 : sk ≤ 2 := by omega
            simp only [h4, h3, if_false]
            rw [← PMF.map_bind, prodPMF_bind_prodPMF, ihF,
              Xi_of_le_two μ ν v0 h2 h]
      constructor
      · exact hMsucc
      · rw [Tlaw_eq_bind_Flaw]
        -- Root counter and root state are already exposed by the environment
        -- and `quenchedFresh`; the started-law half just proved finishes.
        let G : ℕ → FullLab ℕ h → FullLab ℕ h →
            PMF (FullLab (V × ℕ) (h + 1)) :=
          fun k e0 e1 => μ.bind fun v =>
            quenchedMuM μ v0 (v, k) (h + 1) (branch k (e0, e1))
        have hfresh : quenchedFresh μ v0 (h + 1)
            = fun e => G (envRoot (h + 1) e) (envLeft e) (envRight e) := by
          funext e
          simp only [quenchedFresh, G]
          congr 1
        rw [hfresh, counterEnvLaw_succ_bind_root ν h G]
        congr 1
        funext k
        rw [PMF.bind_comm]
        simp only [Flaw]
        congr 1
        funext v
        have hpair :
            (prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).bind
                (fun ep => quenchedMuM μ v0 (v, k) (h + 1)
                  (branch k ep))
              = muM (varyK μ ν v0) (v, k) (h + 1) := by
          calc
            (prodPMF (counterEnvLaw ν h) (counterEnvLaw ν h)).bind
                (fun ep => quenchedMuM μ v0 (v, k) (h + 1) (branch k ep))
                = (counterEnvLaw ν (h + 1)).bind
                    (fun e => quenchedMuM μ v0 (v, k) (h + 1)
                      (branch k (envLeft e, envRight e))) :=
                  (counterEnvLaw_succ_bind_ignore_root ν h
                    (fun e0 e1 => quenchedMuM μ v0 (v, k) (h + 1)
                      (branch k (e0, e1)))).symm
            _ = (counterEnvLaw ν (h + 1)).bind
                    (quenchedMuM μ v0 (v, k) (h + 1)) := by
                  congr 1
            _ = muM (varyK μ ν v0) (v, k) (h + 1) := hMsucc (v, k)
        exact hpair

/-! ### Annealed failure as a quenched average -/

/-- Mismatch mass is bilinear under mixtures of the source and target
laws.  Unlike `PhiD`, this identity has no convexity or inverse-degree
factor. -/
lemma failureD_bind_bind {A B X : Type} (wa : PMF A) (wb : PMF B)
    (fa : A → PMF X) (fb : B → PMF X) (R : X → X → Prop) :
    failureD (wa.bind fa) (wb.bind fb) R
      = ∑' a, wa a * ∑' b, wb b * failureD (fa a) (fb b) R := by
  rw [failureD, tsum_bind_mul]
  refine tsum_congr fun a => ?_
  congr 1
  calc
    (∑' x, fa a x * qE (wb.bind fb) R x)
        = ∑' x, fa a x * ∑' b, wb b * qE (fb b) R x := by
            refine tsum_congr fun x => ?_
            rw [qE_bind]
    _ = ∑' x, ∑' b, wb b * (fa a x * qE (fb b) R x) := by
            refine tsum_congr fun x => ?_
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun b => by ring
    _ = ∑' b, ∑' x, wb b * (fa a x * qE (fb b) R x) :=
          ENNReal.tsum_comm
    _ = ∑' b, wb b * ∑' x, fa a x * qE (fb b) R x := by
          refine tsum_congr fun b => ?_
          rw [ENNReal.tsum_mul_left]

/-- The matching failure of two fresh process trees is exactly the iid
environment average of the mismatch between the two quenched laws. -/
theorem failureD_Tlaw_eq_quenched (Rv : V → V → Prop) (h : ℕ) :
    failureD (Tlaw μ ν v0 h) (Tlaw μ ν v0 h)
        (fullSim (labRel Rv) h)
      = ∑' e0, counterEnvLaw ν h e0 * ∑' e1, counterEnvLaw ν h e1
          * failureD (quenchedFresh μ v0 h e0) (quenchedFresh μ v0 h e1)
              (fullSim (labRel Rv) h) := by
  obtain ⟨_, hfresh⟩ := counterEnv_bind_quenched μ ν v0 h
  rw [← hfresh]
  exact failureD_bind_bind (counterEnvLaw ν h) (counterEnvLaw ν h)
    (quenchedFresh μ v0 h) (quenchedFresh μ v0 h)
    (fullSim (labRel Rv) h)

end GraphMarkovMatching
