/-
Composite counter kernels and their elementary child-law identities.
The state matching relation forgets the counters.
-/
import GraphMarkovMatching.Models.Counter

namespace GraphMarkovMatching.Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

def val (a i : ℕ) : ℕ := a / 2 ^ i

@[simp] lemma val_zero (a : ℕ) : val a 0 = a := by simp [val]

lemma val_succ (a i : ℕ) : val a (i + 1) = val a i / 2 := by
  simp [val, pow_succ, Nat.div_div_eq_div_mul]

/-- Tagged counters: ordinary counters and the pair-indexed markers of the
composite charts.  Fresh vertices only sample ordinary counters. -/
inductive CtrC where
  | ord (k : ℕ) : CtrC
  | mark (a b i : ℕ) : CtrC
deriving DecidableEq

/-- Tagged states: a graph state and a tagged counter. -/
abbrev CState (V : Type) := V × CtrC

variable {V : Type}

/-- The fresh law: the original fresh law with the counter embedded as an
ordinary tagged counter.  Markers are never sampled freshly. -/
noncomputable def freshC (μ : PMF V) (ν : PMF ℕ) : PMF (CState V) :=
  (freshQ μ ν).map fun s => (s.1, CtrC.ord s.2)

@[simp] theorem freshC_ord_apply (μ : PMF V) (ν : PMF ℕ) (v : V) (k : ℕ) :
    freshC μ ν (v, CtrC.ord k) = μ v * ν k := by
  rw [freshC, PMF.map_apply]
  have heq : ∀ a : V × ℕ,
      ((v, CtrC.ord k) = (a.1, CtrC.ord a.2)) ↔ a = (v, k) := by
    intro a
    rcases a with ⟨w, j⟩
    constructor
    · intro h
      simp only [Prod.mk.injEq, CtrC.ord.injEq] at h ⊢
      exact ⟨h.1.symm, h.2.symm⟩
    · intro h
      simp only [Prod.mk.injEq, CtrC.ord.injEq] at h ⊢
      exact ⟨h.1.symm, h.2.symm⟩
  simp_rw [heq]
  rw [tsum_ite_eq]
  exact prodPMF_apply μ ν (v, k)

@[simp] theorem freshC_mark_apply (μ : PMF V) (ν : PMF ℕ) (v : V)
    (a b i : ℕ) : freshC μ ν (v, CtrC.mark a b i) = 0 := by
  rw [freshC, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro s
  rw [if_neg]
  intro h
  exact CtrC.noConfusion (congrArg Prod.snd h)

/-- The marker step of the pair `(a, b)` at stage `i`
(`sec:composite-process`, rules (ii) at `i = 0` and (iii) at
`i ≥ 1`). -/
noncomputable def markK (μ : PMF V) (ν : PMF ℕ) (v0 : V) (a b i : ℕ) :
    PMF (CState V × CState V) :=
  if val a i ≤ 2 then (freshC μ ν).map fun f => ((v0, CtrC.ord b), f)
  else if val a i = 3 then PMF.pure ((v0, CtrC.ord 2), (v0, CtrC.ord b))
  else PMF.pure ((v0, CtrC.mark a b (i + 1)),
    (v0, CtrC.ord (val a i - val a i / 2)))

lemma markK_le_two {μ : PMF V} {ν : PMF ℕ} {v0 : V} {a b i : ℕ}
    (h : val a i ≤ 2) :
    markK μ ν v0 a b i = (freshC μ ν).map fun f => ((v0, CtrC.ord b), f) := by
  rw [markK, if_pos h]

lemma markK_three {μ : PMF V} {ν : PMF ℕ} {v0 : V} {a b i : ℕ}
    (h : val a i = 3) :
    markK μ ν v0 a b i =
      PMF.pure ((v0, CtrC.ord 2), (v0, CtrC.ord b)) := by
  rw [markK, if_neg (by omega), if_pos h]

lemma markK_of_ge {μ : PMF V} {ν : PMF ℕ} {v0 : V} {a b i : ℕ}
    (h : 4 ≤ val a i) :
    markK μ ν v0 a b i =
      PMF.pure ((v0, CtrC.mark a b (i + 1)),
        (v0, CtrC.ord (val a i - val a i / 2))) := by
  rw [markK, if_neg (by omega), if_neg (by omega)]

/-- The composite kernel of a side with exceptional data `exc`
(`sec:composite-process`). -/
noncomputable def compK (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) : CState V → PMF (CState V × CState V)
  | (_, CtrC.mark a b i) => markK μ ν v0 a b i
  | (_, CtrC.ord k) =>
      match exc k with
      | some p => markK μ ν v0 p.1 p.2 0
      | none =>
          if 4 ≤ k then
            PMF.pure ((v0, CtrC.ord (k / 2)), (v0, CtrC.ord (k - k / 2)))
          else if k = 3 then
            (freshC μ ν).map fun f => ((v0, CtrC.ord 2), f)
          else prodPMF (freshC μ ν) (freshC μ ν)

variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

@[simp] lemma compK_mark (v : V) (a b i : ℕ) :
    compK exc μ ν v0 (v, CtrC.mark a b i) = markK μ ν v0 a b i := rfl

lemma compK_ord_exc {z : ℕ} {p : ℕ × ℕ} (hz : exc z = some p) (v : V) :
    compK exc μ ν v0 (v, CtrC.ord z) = markK μ ν v0 p.1 p.2 0 := by
  simp only [compK, hz]

lemma compK_ord_none_of_ge {k : ℕ} (hk : exc k = none) (h4 : 4 ≤ k) (v : V) :
    compK exc μ ν v0 (v, CtrC.ord k) =
      PMF.pure ((v0, CtrC.ord (k / 2)), (v0, CtrC.ord (k - k / 2))) := by
  simp only [compK, hk, if_pos h4]

lemma compK_ord_none_three {k : ℕ} (hk : exc k = none) (h3 : k = 3) (v : V) :
    compK exc μ ν v0 (v, CtrC.ord k) =
      (freshC μ ν).map fun f => ((v0, CtrC.ord 2), f) := by
  subst h3
  simp only [compK, hk]
  norm_num

lemma compK_ord_none_le_two {k : ℕ} (hk : exc k = none) (h2 : k ≤ 2) (v : V) :
    compK exc μ ν v0 (v, CtrC.ord k) =
      prodPMF (freshC μ ν) (freshC μ ν) := by
  simp only [compK, hk, if_neg (by omega : ¬ 4 ≤ k),
    if_neg (by omega : ¬ k = 3)]

/-- The fresh subtree law of the side. -/
noncomputable def cT (h : ℕ) : PMF (FullLab (CState V) h) :=
  (freshC μ ν).bind fun s => muM (compK exc μ ν v0) s h

/-- The frozen subtree law below the label `(v0, c)`. -/
noncomputable def cZ (c : CtrC) (h : ℕ) : PMF (FullLab (CState V) h) :=
  muM (compK exc μ ν v0) (v0, c) h

/-- The child-pair law below a root with tagged counter `c`. -/
noncomputable def cXi (c : CtrC) (h : ℕ) :
    PMF (FullLab (CState V) h × FullLab (CState V) h) :=
  pairMix (compK exc μ ν v0) (v0, c) h

/-- The fresh cell mixture. -/
noncomputable def cXiBar (h : ℕ) :
    PMF (FullLab (CState V) h × FullLab (CState V) h) :=
  ν.bind fun k => cXi exc μ ν v0 (CtrC.ord k) h

lemma cZ_succ (c : CtrC) (h : ℕ) :
    cZ exc μ ν v0 c (h + 1) = (cXi exc μ ν v0 c h).map (branch (v0, c)) := rfl

/-- The cell law does not depend on the root state, so the exceptional cell
is the stage-zero marker cell of its pair. -/
lemma cXi_ord_exc {z : ℕ} {p : ℕ × ℕ} (hz : exc z = some p) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.ord z) h = cXi exc μ ν v0 (CtrC.mark p.1 p.2 0) h := by
  rw [cXi, cXi, pairMix, pairMix, compK_ord_exc exc μ ν v0 hz, compK_mark]

/-! ### Cell shapes -/

lemma pairMix_pure_pattern {S : Type} (P : S → PMF (S × S))
    (s a b : S) (h : ℕ) (hs : P s = PMF.pure (a, b)) :
    pairMix P s h = prodPMF (muM P a h) (muM P b h) := by
  rw [pairMix, hs]
  simp

/-- A bind in the second coordinate of a product factors out. -/
lemma bind_prodPMF_right {A X Y : Type} (ρ : PMF A) (p : PMF X)
    (τ : A → PMF Y) :
    (ρ.bind fun f => prodPMF p (τ f)) = prodPMF p (ρ.bind τ) := by
  apply PMF.ext
  intro z
  rw [PMF.bind_apply, prodPMF_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun f => ?_
  rw [prodPMF_apply]
  ring

/-- A product kernel mixes into a product of mixtures. -/
lemma prodPMF_bind_pair {A B X Y : Type} (q : PMF A) (r : PMF B)
    (F : A → PMF X) (G : B → PMF Y) :
    ((prodPMF q r).bind fun c => prodPMF (F c.1) (G c.2)) =
      prodPMF (q.bind F) (r.bind G) := by
  apply PMF.ext
  intro z
  rw [PMF.bind_apply, prodPMF_apply, PMF.bind_apply, PMF.bind_apply,
    ENNReal.tsum_prod']
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  simp only [prodPMF_apply]
  ring

/-- The cell of a kernel that freezes the left child and refreshes the
right child. -/
lemma pairMix_map_pattern {S : Type} (P : S → PMF (S × S)) (ρ : PMF S)
    (s c₀ : S) (h : ℕ) (hs : P s = ρ.map fun f => (c₀, f)) :
    pairMix P s h =
      prodPMF (muM P c₀ h) (ρ.bind fun f => muM P f h) := by
  rw [pairMix, hs, PMF.bind_map]
  have hcomp : ((fun στ : S × S => prodPMF (muM P στ.1 h) (muM P στ.2 h)) ∘
      fun f => (c₀, f)) = fun f => prodPMF (muM P c₀ h) (muM P f h) := rfl
  rw [hcomp]
  exact bind_prodPMF_right ρ (muM P c₀ h) fun f => muM P f h

/-- The cell of a kernel that refreshes both children. -/
lemma pairMix_prod_pattern {S : Type} (P : S → PMF (S × S)) (ρ : PMF S)
    (s : S) (h : ℕ) (hs : P s = prodPMF ρ ρ) :
    pairMix P s h =
      prodPMF (ρ.bind fun f => muM P f h) (ρ.bind fun f => muM P f h) := by
  rw [pairMix, hs]
  exact prodPMF_bind_pair ρ ρ (fun s => muM P s h) (fun s => muM P s h)

lemma cXi_mark_of_ge {a b i : ℕ} (hval : 4 ≤ val a i) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.mark a b i) h =
      prodPMF (cZ exc μ ν v0 (CtrC.mark a b (i + 1)) h)
        (cZ exc μ ν v0 (CtrC.ord (val a i - val a i / 2)) h) :=
  pairMix_pure_pattern _ _ _ _ _ (by rw [compK_mark, markK_of_ge hval])

lemma cXi_mark_three {a b i : ℕ} (hval : val a i = 3) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.mark a b i) h =
      prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
        (cZ exc μ ν v0 (CtrC.ord b) h) :=
  pairMix_pure_pattern _ _ _ _ _ (by rw [compK_mark, markK_three hval])

lemma cXi_mark_le_two {a b i : ℕ} (hval : val a i ≤ 2) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.mark a b i) h =
      prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h) :=
  pairMix_map_pattern _ _ _ _ _ (by rw [compK_mark, markK_le_two hval])

lemma cXi_ord_none_of_ge {k : ℕ} (hk : exc k = none) (h4 : 4 ≤ k) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.ord k) h =
      prodPMF (cZ exc μ ν v0 (CtrC.ord (k / 2)) h)
        (cZ exc μ ν v0 (CtrC.ord (k - k / 2)) h) :=
  pairMix_pure_pattern _ _ _ _ _ (compK_ord_none_of_ge exc μ ν v0 hk h4 v0)

lemma cXi_ord_none_three {k : ℕ} (hk : exc k = none) (h3 : k = 3) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.ord k) h =
      prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h) (cT exc μ ν v0 h) :=
  pairMix_map_pattern _ _ _ _ _ (compK_ord_none_three exc μ ν v0 hk h3 v0)

lemma cXi_ord_none_le_two {k : ℕ} (hk : exc k = none) (h2 : k ≤ 2) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.ord k) h =
      prodPMF (cT exc μ ν v0 h) (cT exc μ ν v0 h) :=
  pairMix_prod_pattern _ _ _ _ (compK_ord_none_le_two exc μ ν v0 hk h2 v0)

def cRel (Rv : V → V → Prop) : CState V → CState V → Prop :=
  fun s t => Rv s.1 t.1

end GraphMarkovMatching.Composite
