/-
The one-level extension kernel of the Markov tree law, the mathematical core
of the Kolmogorov existence construction behind the K\H{o}nig passage
(`thm:konig` in `arbitrary_offspring_matching.tex`; the trajectory
assembly itself is not formalised, see the module notes below).

`extK P n x` extends a height-`n` labelling `x` by one level: at every
depth-`n` leaf, a fresh children pattern is drawn from the kernel at the
leaf's state, independently across leaves. The two key properties:

* `muM_bind_extK` (consistency): extending a height-`n` sample gives a
  height-`(n+1)` sample, `(muM P s n).bind (extK P n) = muM P s (n+1)`;
* `restrictLab_of_extK_ne_zero` (support): every extension restricts back to
  its base, so the trajectory measure built from `extK` by Ionescu-Tulcea
  concentrates on compatible sequences.

Together with `muM_map_restrictLab` these discharge the mathematical inputs
of the trajectory construction; the remaining assembly (Mathlib's
`trajMeasure` over the levels, the compatible-sequence correction, and the
marginal identification) is measure plumbing.
-/
import GraphMarkovMatching.Closure.Measure

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {S : Type u}

/-! ### PMF product-bind algebra -/

/-- The product PMF, monadically. -/
lemma prodPMF_eq_bind {A B : Type u} (p : PMF A) (q : PMF B) :
    prodPMF p q = p.bind fun a => q.map fun b => (a, b) := by
  apply PMF.ext
  intro z
  rw [prodPMF_apply, PMF.bind_apply]
  calc p z.1 * q z.2
      = ∑' a, p a * (if z.1 = a then q z.2 else 0) := by
        refine Eq.symm (Eq.trans (tsum_congr fun a => ?_)
          (tsum_ite_eq z.1 (fun a => p a * q z.2)))
        by_cases h : z.1 = a
        · rw [if_pos h, if_pos (show a = z.1 from h.symm)]
        · rw [if_neg h, mul_zero, if_neg (show ¬ a = z.1 from fun hc => h hc.symm)]
    _ = ∑' a, p a * (q.map fun b => (a, b)) z := by
        refine tsum_congr fun a => ?_
        congr 1
        rw [PMF.map_apply]
        by_cases h : z.1 = a
        · rw [if_pos h]
          refine Eq.symm (Eq.trans (tsum_congr fun b => ?_) (tsum_ite_eq z.2 q))
          by_cases hb : z = (a, b)
          · rw [if_pos hb, if_pos (show b = z.2 from by rw [hb])]
          · rw [if_neg hb, if_neg (show ¬ b = z.2 from fun hc => hb (Prod.ext h hc.symm))]
        · rw [if_neg h]
          refine (ENNReal.tsum_eq_zero.mpr fun b => ?_).symm
          rw [if_neg (show ¬ z = (a, b) from fun hc => h (congrArg Prod.fst hc))]

/-- The two coordinates of a product sample can be extended independently:
the bind-Fubini identity behind the extension kernel. -/
lemma prodPMF_bind_ext {A B C D E : Type u} (μ : PMF A) (ν : PMF B)
    (f : A → PMF C) (g : B → PMF D) (h : C → D → E) :
    (prodPMF μ ν).bind (fun z => (f z.1).bind fun c => (g z.2).map fun d => h c d)
      = (prodPMF (μ.bind f) (ν.bind g)).map fun w => h w.1 w.2 := by
  have hL : (prodPMF μ ν).bind (fun z => (f z.1).bind fun c => (g z.2).map fun d => h c d)
      = μ.bind fun a => (f a).bind fun c => ν.bind fun b => (g b).map fun d => h c d := by
    rw [prodPMF_eq_bind, PMF.bind_bind]
    refine congrArg _ (funext fun a => ?_)
    rw [PMF.bind_map]
    exact PMF.bind_comm ν (f a) (fun b c => (g b).map fun d => h c d)
  have hR : (prodPMF (μ.bind f) (ν.bind g)).map (fun w => h w.1 w.2)
      = μ.bind fun a => (f a).bind fun c => ν.bind fun b => (g b).map fun d => h c d := by
    rw [prodPMF_eq_bind, PMF.map_bind, PMF.bind_bind]
    refine congrArg _ (funext fun a => ?_)
    refine congrArg _ (funext fun c => ?_)
    rw [PMF.map_comp, PMF.map_bind]
    rfl
  rw [hL, hR]

/-! ### The extension kernel -/

variable (P : S → PMF (S × S))

/-- Extend a height-`n` labelling by one level: fresh children patterns at
every depth-`n` leaf, independently. -/
noncomputable def extK : (n : ℕ) → FullLab S n → PMF (FullLab S (n + 1))
  | 0, x => (P (rootLab 0 x)).map fun στ => branch (rootLab 0 x) (leaf στ.1, leaf στ.2)
  | n + 1, x =>
      (extK n x.2.1).bind fun y₀ => (extK n x.2.2).map fun y₁ => branch x.1 (y₀, y₁)

/-- **Consistency**: extending a height-`n` sample yields a height-`(n+1)`
sample. -/
lemma muM_bind_extK (s : S) : ∀ n, (muM P s n).bind (extK P n) = muM P s (n + 1) := by
  intro n
  induction n generalizing s with
  | zero =>
      rw [muM_zero, PMF.pure_bind]
      show (P s).map (fun στ => branch s (leaf στ.1, leaf στ.2)) = muM P s 1
      rw [muM_succ, pairMix]
      rw [show ((P s).bind fun στ => prodPMF (muM P στ.1 0) (muM P στ.2 0))
          = (P s).map fun στ => ((leaf στ.1, leaf στ.2) : FullLab S 0 × FullLab S 0) from by
        rw [← PMF.bind_pure_comp]
        refine congrArg _ (funext fun στ => ?_)
        rw [muM_zero, muM_zero, prodPMF_eq_bind, PMF.pure_bind, ← PMF.bind_pure_comp,
          PMF.pure_bind]
        rfl]
      rw [PMF.map_comp]
      rfl
  | succ n ih =>
      rw [show muM P s (n + 1) = (pairMix P s n).map (branch s) from rfl,
        PMF.bind_map,
        show muM P s (n + 1 + 1) = (pairMix P s (n + 1)).map (branch s) from rfl,
        pairMix, pairMix, PMF.bind_bind, PMF.map_bind]
      refine congrArg _ (funext fun στ => ?_)
      rw [← ih στ.1, ← ih στ.2,
        ← prodPMF_bind_ext (muM P στ.1 n) (muM P στ.2 n) (extK P n) (extK P n)
          (fun y₀ y₁ => branch s (y₀, y₁))]
      rfl

/-- The root-mixture form of consistency. -/
lemma mix_bind_extK (ι : PMF S) (n : ℕ) :
    ((ι.bind fun s => muM P s n).bind (extK P n))
      = ι.bind fun s => muM P s (n + 1) := by
  rw [PMF.bind_bind]
  exact congrArg _ (funext fun s => muM_bind_extK P s n)

/-- **Support**: every extension restricts back to its base. This is what
concentrates the trajectory measure on compatible sequences. -/
lemma restrictLab_of_extK_ne_zero :
    ∀ (n : ℕ) (x : FullLab S n) (y : FullLab S (n + 1)),
      extK P n x y ≠ 0 → restrictLab n y = x := by
  intro n
  induction n with
  | zero =>
      intro x y hy
      rw [show extK P 0 x = (P (rootLab 0 x)).map
          (fun στ => branch (rootLab 0 x) (leaf στ.1, leaf στ.2)) from rfl,
        PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hy
      push Not at hy
      obtain ⟨στ, hστ⟩ := hy
      by_cases h : y = branch (rootLab 0 x) (leaf στ.1, leaf στ.2)
      · rw [h]
        rfl
      · rw [if_neg h] at hστ
        exact absurd rfl hστ
  | succ n ih =>
      intro x y hy
      rw [show extK P (n + 1) x
          = (extK P n x.2.1).bind (fun y₀ => (extK P n x.2.2).map fun y₁ => branch x.1 (y₀, y₁))
          from rfl,
        PMF.bind_apply, Ne, ENNReal.tsum_eq_zero] at hy
      push Not at hy
      obtain ⟨y₀, hy₀⟩ := hy
      obtain ⟨h₀, h₁⟩ := mul_ne_zero_iff.mp hy₀
      rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at h₁
      push Not at h₁
      obtain ⟨y₁, hy₁⟩ := h₁
      by_cases h : y = branch x.1 (y₀, y₁)
      · rw [if_pos h] at hy₁
        rw [h]
        show (x.1, restrictLab n y₀, restrictLab n y₁) = x
        rw [ih x.2.1 y₀ h₀, ih x.2.2 y₁ hy₁]
        rfl
      · rw [if_neg h] at hy₁
        exact absurd rfl hy₁

end GraphMarkovMatching
