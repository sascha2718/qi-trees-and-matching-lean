/-
The cell layer of the arbitrary-support proof
(`arbitrary_offspring_matching.tex` §3, plan item (1) begun): the fresh
counter cells `Flaw k` of the varying-offspring process, the mixture
identity `Tlaw = ν.bind Flaw`, and the degree identities of Lemma
`thm:fresh-mixture` instantiated at the process laws:

* `freshQ_bind_eq`: binding a fresh `Q = μ ⊗ ν` sample is the `ν`-mixture
  of the `μ`-mixtures at a fixed counter;
* `Tlaw_eq_bind_Flaw`: the fresh law is the `ν`-mixture of its cells;
* `rE_Tlaw_eq_tsum`: `r_{·|F} = ∑_k ν_k r_{·|F_k}` (`eq:fresh-mixture`);
* `rE_Tlaw_eq_zero_iff`: a fresh zero forces a zero toward every charged
  component (the zero direction of `thm:fresh-mixture`);
* `mul_rE_Flaw_le_rE_Tlaw`: the first-positive-component minorization
  (`thm:mixture-tilt`, before the `ν_*` normalization).
-/
import GraphMarkovMatching.Process.Kernel
import GraphMarkovMatching.Process.Screens

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-! ### The one-step decomposition in good-degree form (`thm:one-step`) -/

section OneStep

variable {S : Type u}

/-- **The one-step decomposition** (`eq:decomp-forced` in good-degree
form): against a branch point, the good degree toward a height-`(h+1)`
tree law is the root-compatibility indicator times the child-pair good
degree under straight-or-crossed matching. -/
lemma rE_succ_branch (P : S → PMF (S × S)) (R₀ : S → S → Prop)
    (s t : S) (n : ℕ) (xp : FullLab S n × FullLab S n) :
    rE (muM P t (n + 1)) (fullSim R₀ (n + 1)) (branch s xp)
      = if R₀ s t then rE (pairMix P t n) (SquareRel (fullSim R₀ n)) xp
        else 0 := by
  by_cases hst : R₀ s t
  · rw [if_pos hst, muM_succ, rE_map, rE_eq_tsum_mul]
    refine tsum_congr fun yp => ?_
    congr 1
    rw [goodInd, goodInd]
    by_cases h : SquareRel (fullSim R₀ n) xp yp
    · rw [if_pos ((fullSim_branch R₀ n s t xp yp).mpr ⟨hst, h⟩), if_pos h]
    · rw [if_neg (fun hc => h ((fullSim_branch R₀ n s t xp yp).mp hc).2),
        if_neg h]
  · rw [if_neg hst, muM_succ, rE_map]
    refine ENNReal.tsum_eq_zero.mpr fun yp => ?_
    rw [goodInd,
      if_neg (fun hc => hst ((fullSim_branch R₀ n s t xp yp).mp hc).1),
      mul_zero]

end OneStep

variable {V : Type} (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- The fresh cell law `F_k`: a fresh sample with the counter exposed and
equal to `k`; the root label stays a `μ`-sample. -/
noncomputable def Flaw (k h : ℕ) : PMF (FullLab (V × ℕ) h) :=
  μ.bind fun v => muM (varyK μ ν v0) (v, k) h

/-- Binding a fresh `Q = μ ⊗ ν` sample is the `ν`-mixture of `μ`-mixtures
at a fixed counter. -/
lemma freshQ_bind_eq {D : Type} (f : V × ℕ → PMF D) (x : D) :
    (freshQ μ ν).bind f x = (ν.bind fun k => μ.bind fun v => f (v, k)) x := by
  rw [PMF.bind_apply, PMF.bind_apply]
  calc ∑' s : V × ℕ, freshQ μ ν s * f s x
      = ∑' v, ∑' k, freshQ μ ν (v, k) * f (v, k) x := ENNReal.tsum_prod'
    _ = ∑' k, ∑' v, ν k * (μ v * f (v, k) x) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun k => tsum_congr fun v => by
          simp only [freshQ, prodPMF_apply]
          ring
    _ = ∑' k, ν k * (μ.bind fun v => f (v, k)) x := by
        refine tsum_congr fun k => ?_
        rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]

/-- The fresh law is the `ν`-mixture of its counter cells. -/
lemma Tlaw_eq_bind_Flaw (h : ℕ) :
    Tlaw μ ν v0 h = ν.bind fun k => Flaw μ ν v0 k h := by
  ext x
  exact freshQ_bind_eq μ ν (fun s => muM (varyK μ ν v0) s h) x

/-- `r_{·|F} = ∑_k ν_k r_{·|F_k}` at the process laws
(`eq:fresh-mixture`). -/
lemma rE_Tlaw_eq_tsum (h : ℕ)
    (R : FullLab (V × ℕ) h → FullLab (V × ℕ) h → Prop)
    (z : FullLab (V × ℕ) h) :
    rE (Tlaw μ ν v0 h) R z = ∑' k, ν k * rE (Flaw μ ν v0 k h) R z := by
  rw [Tlaw_eq_bind_Flaw, rE_bind]

/-- A zero degree toward the fresh law forces a zero degree toward every
component the offspring law charges (the zero direction of
`thm:fresh-mixture`). -/
lemma rE_Tlaw_eq_zero_iff (h : ℕ)
    (R : FullLab (V × ℕ) h → FullLab (V × ℕ) h → Prop)
    (z : FullLab (V × ℕ) h) :
    rE (Tlaw μ ν v0 h) R z = 0 ↔
      ∀ k, ν k = 0 ∨ rE (Flaw μ ν v0 k h) R z = 0 := by
  rw [Tlaw_eq_bind_Flaw, rE_bind_eq_zero_iff]

/-- The first-positive-component minorization (`thm:mixture-tilt`): one
charged cell already bounds the fresh degree from below. -/
lemma mul_rE_Flaw_le_rE_Tlaw (h : ℕ)
    (R : FullLab (V × ℕ) h → FullLab (V × ℕ) h → Prop)
    (z : FullLab (V × ℕ) h) (k : ℕ) :
    ν k * rE (Flaw μ ν v0 k h) R z ≤ rE (Tlaw μ ν v0 h) R z := by
  rw [Tlaw_eq_bind_Flaw]
  exact mul_rE_le_rE_bind ν _ R z k

/-! ### The forced and fresh decompositions at the process laws -/

variable (Rv : V → V → Prop)

/-- **The forced decomposition** (`eq:decomp-forced`): the good degree
toward a forced target law is the root indicator times the pair degree
against the cascade mixture. -/
lemma rE_Zlaw_succ_branch (v : V) (k j h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = if Rv v v0 then
          rE (Xi μ ν v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp
        else 0 :=
  rE_succ_branch (varyK μ ν v0) (labRel Rv) (v, k) (v0, j) h xp

/-- The bad-degree form of the forced decomposition at a compatible root. -/
lemma qE_Zlaw_succ_branch {v : V} (hv : Rv v v0) (k j h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    qE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = qE (Xi μ ν v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp :=
  qE_succ_branch (varyK μ ν v0) (labRel Rv)
    (show labRel Rv (v, k) (v0, j) from hv) h xp

/-- **The fresh decomposition** (`eq:decomp-fresh` in good-degree form):
`r_{·|F} = b(x_r) · ∑_ℓ ν_ℓ R_{g(ℓ)}`; the root factor and the cascade
mixture separate exactly because `Q = μ ⊗ ν`. -/
lemma rE_Tlaw_succ_branch (v : V) (k h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = rE μ Rv v
        * rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp := by
  rw [show Tlaw μ ν v0 (h + 1)
      = (freshQ μ ν).bind fun s => muM (varyK μ ν v0) s (h + 1) from rfl,
    rE_bind]
  calc ∑' s : V × ℕ, freshQ μ ν s
        * rE (muM (varyK μ ν v0) s (h + 1)) (fullSim (labRel Rv) (h + 1))
            (branch (v, k) xp)
      = ∑' s : V × ℕ, (if Rv v s.1 then μ s.1 else 0)
          * (ν s.2 * rE (Xi μ ν v0 s.2 h)
              (SquareRel (fullSim (labRel Rv) h)) xp) := by
        refine tsum_congr fun s => ?_
        obtain ⟨w, l⟩ := s
        rw [rE_succ_branch (varyK μ ν v0) (labRel Rv) (v, k) (w, l) h xp,
          pairMix_varyK]
        by_cases hw : Rv v w
        · rw [if_pos (show labRel Rv (v, k) (w, l) from hw), if_pos hw]
          simp only [freshQ, prodPMF_apply]
          ring
        · rw [if_neg (show ¬ labRel Rv (v, k) (w, l) from hw), if_neg hw,
            mul_zero, zero_mul]
    _ = (∑' w, if Rv v w then μ w else 0)
        * ∑' l, ν l * rE (Xi μ ν v0 l h)
            (SquareRel (fullSim (labRel Rv) h)) xp :=
      tsum_prod_split (fun w => if Rv v w then μ w else 0)
        (fun l => ν l * rE (Xi μ ν v0 l h)
          (SquareRel (fullSim (labRel Rv) h)) xp)
    _ = rE μ Rv v
        * rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp := by
      have h2 : rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp
          = ∑' l, ν l * rE (Xi μ ν v0 l h)
              (SquareRel (fullSim (labRel Rv) h)) xp :=
        rE_bind ν (fun l => Xi μ ν v0 l h) _ xp
      rw [h2]
      rfl

end GraphMarkovMatching
