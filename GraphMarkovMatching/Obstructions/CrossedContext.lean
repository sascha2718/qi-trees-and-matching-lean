/-
The crossed-context obstruction for the varying-offspring process,
`thm:obstruction` of `arbitrary_offspring_matching.tex`
(`crossed_context_potential_top` below is its certificate): the
refutation that dictated the screened design.

The obstruction:

* `crossed_context_potential_top`: for the pure-ternary law (`ν` supported
  on `{3}`) and any label `vf` charged by `μ` and incompatible with the
  forced label, the crossed context potential `Φ(Z₂ → T)` is infinite: the
  frozen counter-`2` context whose two fresh children are both rooted at
  `vf` meets, in every sample of `T` and under both pairings, a forced
  `(v0, 2)` root.  Consequently the arbitrary-`ν` block recursion cannot
  factor through unconditioned cross-type context potentials; the crossed
  gain must be quantified conditionally (the screened design of
  `arbitrary_offspring_matching.tex`, certified in the general-ν layer).
  This is the varying-offspring analogue of the caret obstruction of the
  retired per-state route.
-/
import GraphMarkovMatching.Process.Contraction

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### Helpers -/

lemma ne_zero_of_le {a b : ℝ≥0∞} (hb : b ≠ 0) (hba : b ≤ a) : a ≠ 0 :=
  fun ha => hb (le_antisymm (ha ▸ hba) zero_le)

lemma map_apply_ge {A B : Type*} (p : PMF A) (f : A → B) (a : A) :
    p a ≤ (p.map f) (f a) := by
  rw [PMF.map_apply]
  calc p a = if f a = f a then p a else 0 := by rw [if_pos rfl]
    _ ≤ ∑' a', if f a = f a' then p a' else 0 := ENNReal.le_tsum a

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- Every started tree law is a component of the fresh law. -/
lemma mul_muM_le_Tlaw (t : V × ℕ) (h : ℕ) (x : FullLab (V × ℕ) h) :
    freshQ μ ν t * muM (varyK μ ν v0) t h x ≤ Tlaw μ ν v0 h x := by
  rw [Tlaw, PMF.bind_apply]
  exact ENNReal.le_tsum t

/-! ### The crossed-context obstruction -/

variable (vf : V)

/-- The canonical witness pair: `(farPair h).1` is a fresh-law tree rooted at
the far label `vf`, `(farPair h).2` a counter-`2` context tree, for the
pure-ternary law. -/
def farPair : (h : ℕ) → FullLab (V × ℕ) h × FullLab (V × ℕ) h
  | 0 => (leaf (vf, 3), leaf (v0, 2))
  | h + 1 =>
      (branch (vf, 3) ((farPair h).2, (farPair h).1),
        branch (v0, 2) ((farPair h).1, (farPair h).1))

/-- The far fresh tree. -/
def farT (h : ℕ) : FullLab (V × ℕ) h := (farPair v0 vf h).1

/-- The counter-`2` context tree. -/
def zT (h : ℕ) : FullLab (V × ℕ) h := (farPair v0 vf h).2

@[simp] lemma rootLab_farT (h : ℕ) : rootLab h (farT v0 vf h) = (vf, 3) := by
  cases h <;> rfl

/-- The witness trees are charged by their context laws, and the far tree by
the fresh law. -/
lemma farT_pos (hμf : μ vf ≠ 0) (hν3 : ν 3 ≠ 0) :
    ∀ h, muM (varyK μ ν v0) (vf, 3) h (farT v0 vf h) ≠ 0
      ∧ muM (varyK μ ν v0) (v0, 2) h (zT v0 vf h) ≠ 0
      ∧ Tlaw μ ν v0 h (farT v0 vf h) ≠ 0 := by
  intro h
  induction h with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [show farT v0 vf 0 = leaf (vf, 3) from rfl, muM_zero]
        simp [PMF.pure_apply]
      · rw [show zT v0 vf 0 = leaf (v0, 2) from rfl, muM_zero]
        simp [PMF.pure_apply]
      · refine ne_zero_of_le ?_ (mul_muM_le_Tlaw μ ν v0 (vf, 3) 0 (farT v0 vf 0))
        refine mul_ne_zero (show freshQ μ ν (vf, 3) ≠ 0 from mul_ne_zero hμf hν3) ?_
        rw [show farT v0 vf 0 = leaf (vf, 3) from rfl, muM_zero]
        simp [PMF.pure_apply]
  | succ h ih =>
      obtain ⟨ihf, ihz, ihT⟩ := ih
      have hXi3 : Xi μ ν v0 3 h (zT v0 vf h, farT v0 vf h) ≠ 0 := by
        rw [Xi_three μ ν v0 h, prodPMF_apply]
        exact mul_ne_zero ihz ihT
      have hXi2 : Xi μ ν v0 2 h (farT v0 vf h, farT v0 vf h) ≠ 0 := by
        rw [Xi_of_le_two μ ν v0 (le_refl 2) h, prodPMF_apply]
        exact mul_ne_zero ihT ihT
      have hf' : muM (varyK μ ν v0) (vf, 3) (h + 1) (farT v0 vf (h + 1)) ≠ 0 := by
        refine ne_zero_of_le hXi3 ?_
        rw [muM_varyK_succ μ ν v0 vf 3 h,
          show farT v0 vf (h + 1)
            = branch (vf, 3) (zT v0 vf h, farT v0 vf h) from rfl]
        exact map_apply_ge _ _ _
      have hz' : muM (varyK μ ν v0) (v0, 2) (h + 1) (zT v0 vf (h + 1)) ≠ 0 := by
        refine ne_zero_of_le hXi2 ?_
        rw [muM_varyK_succ μ ν v0 v0 2 h,
          show zT v0 vf (h + 1)
            = branch (v0, 2) (farT v0 vf h, farT v0 vf h) from rfl]
        exact map_apply_ge _ _ _
      refine ⟨hf', hz', ?_⟩
      refine ne_zero_of_le ?_
        (mul_muM_le_Tlaw μ ν v0 (vf, 3) (h + 1) (farT v0 vf (h + 1)))
      exact mul_ne_zero (show freshQ μ ν (vf, 3) ≠ 0 from mul_ne_zero hμf hν3) hf'

/-- For the pure-ternary law, every charged sample of the fresh law at height
`h + 1` is a counter-`3` root whose left subtree is a counter-`2` context. -/
lemma Tlaw_succ_support (hν3 : ∀ k, ν k ≠ 0 → k = 3) {h : ℕ}
    {y : FullLab (V × ℕ) (h + 1)} (hy : Tlaw μ ν v0 (h + 1) y ≠ 0) :
    ∃ (w : V) (yp : FullLab (V × ℕ) h × FullLab (V × ℕ) h),
      y = branch (w, 3) yp ∧ rootLab h yp.1 = (v0, 2) := by
  rw [Tlaw, PMF.bind_apply, Ne, ENNReal.tsum_eq_zero] at hy
  push Not at hy
  obtain ⟨t, ht⟩ := hy
  obtain ⟨hQ, hm⟩ := mul_ne_zero_iff.mp ht
  obtain ⟨w, k⟩ := t
  have hk : k = 3 := hν3 k (mul_ne_zero_iff.mp
    (show μ w * ν k ≠ 0 from hQ)).2
  subst hk
  rw [muM_varyK_succ μ ν v0 w 3 h, PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hm
  push Not at hm
  obtain ⟨yp, hyp⟩ := hm
  have hcase : y = branch (w, 3) yp := by
    by_contra hne
    rw [if_neg hne] at hyp
    exact hyp rfl
  have hXi : Xi μ ν v0 3 h yp ≠ 0 := by
    rw [if_pos hcase] at hyp
    exact hyp
  rw [Xi_three μ ν v0 h, prodPMF_apply] at hXi
  obtain ⟨hz, -⟩ := mul_ne_zero_iff.mp hXi
  exact ⟨w, yp, hcase, rootLab_of_ne_zero (varyK μ ν v0) h (v0, 2) yp.1 hz⟩

/-- **Certain crossed mismatch**: the frozen counter-`2` context whose fresh
children are both far-rooted fails against every charged fresh sample: under
both pairings a far root meets a forced `(v0, 2)` root. -/
lemma qE_crossed_eq_one (hν3 : ∀ k, ν k ≠ 0 → k = 3) (hfar : ¬ Rv vf v0)
    (h : ℕ) :
    qE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
      (branch (v0, 2) (farT v0 vf h, farT v0 vf h)) = 1 := by
  have hr : rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
      (branch (v0, 2) (farT v0 vf h, farT v0 vf h)) = 0 := by
    rw [rE]
    refine ENNReal.tsum_eq_zero.mpr fun y => ?_
    by_cases hy : fullSim (labRel Rv) (h + 1)
        (branch (v0, 2) (farT v0 vf h, farT v0 vf h)) y
    · rw [if_pos hy]
      by_contra hne
      obtain ⟨w, yp, rfl, hroot1⟩ := Tlaw_succ_support μ ν v0 hν3 hne
      obtain ⟨-, hsq⟩ := (fullSim_branch (labRel Rv) h (v0, 2) (w, 3) _ yp).mp hy
      have h1 : fullSim (labRel Rv) h (farT v0 vf h) yp.1 := by
        rcases hsq with ⟨h1, -⟩ | ⟨-, h1⟩ <;> exact h1
      have hlab := fullSim_root (labRel Rv) h _ _ h1
      rw [rootLab_farT, hroot1] at hlab
      exact hfar hlab
    · rw [if_neg hy]
  have h1 := rE_add_qE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
    (branch (v0, 2) (farT v0 vf h, farT v0 vf h))
  rw [hr, zero_add] at h1
  exact h1

/-- **The crossed-context obstruction**: for the pure-ternary offspring law
and any far label charged by `μ`, the crossed context potential
`Φ_α(Z₂ → T)` is infinite at every height.  The arbitrary-`ν` block
recursion therefore cannot factor through unconditioned cross-type context
potentials. -/
theorem crossed_context_potential_top (hν3 : ∀ k, ν k ≠ 0 → k = 3)
    (hμf : μ vf ≠ 0) (hν3' : ν 3 ≠ 0) (hfar : ¬ Rv vf v0) (h : ℕ) :
    PhiD α (Zlaw μ ν v0 2 (h + 1)) (Tlaw μ ν v0 (h + 1))
      (fullSim (labRel Rv) (h + 1)) = ⊤ := by
  obtain ⟨-, -, hT⟩ := farT_pos μ ν v0 vf hμf hν3' h
  set x := branch (v0, 2) (farT v0 vf h, farT v0 vf h) with hx
  have hmass : Zlaw μ ν v0 2 (h + 1) x ≠ 0 := by
    have h1 : Xi μ ν v0 2 h (farT v0 vf h, farT v0 vf h) ≠ 0 := by
      rw [Xi_of_le_two μ ν v0 (le_refl 2) h, prodPMF_apply]
      exact mul_ne_zero hT hT
    refine ne_zero_of_le h1 ?_
    rw [show Zlaw μ ν v0 2 (h + 1) = (Xi μ ν v0 2 h).map (branch (v0, 2)) from rfl,
      hx]
    exact map_apply_ge _ _ _
  have hq1 : q (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 1 := by
    rw [q, hx, qE_crossed_eq_one Rv μ ν v0 vf hν3 hfar h, ENNReal.toReal_one]
  have hle : Zlaw μ ν v0 2 (h + 1) x
      * phiE α (q (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) x)
      ≤ PhiD α (Zlaw μ ν v0 2 (h + 1)) (Tlaw μ ν v0 (h + 1))
          (fullSim (labRel Rv) (h + 1)) := by
    rw [PhiD]
    exact ENNReal.le_tsum x
  rw [hq1, phiE_one, ENNReal.mul_top hmass] at hle
  exact top_le_iff.mp hle

end GraphMarkovMatching
