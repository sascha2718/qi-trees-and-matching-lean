/-
Support witnesses and exact pruning across the two composite laws
(`arbitrary_offspring_matching.tex`, `sec:composite`,
`thm:support-equality` and `thm:exact-pruning`), and the degree half of
the weighted mixture tilt (`thm:mixture-tilt-composite`).

The two sides share the graph law `μ` and the distinguished state `v0`
and differ in the offspring law and the declared composite pairs.  The
mirror map sends a left label to the right label heading the arrangement
that realizes the same state pattern: common counters to themselves,
an exceptional counter to the first member of its pair, and a marker at
stage `i` to the plain running value.  The witness theorem produces, for
every charged left sample, a charged right sample whose states are
compatible, by the reflexivity of the state relation; the exact pruning
theorem turns this into the vanishing of every screen whose dead
indicator includes the opposite fresh law.  This is the liveness input
of the acyclicity theorem `no_live_common_cycle`.

* `cRel`: labels compare through their graph states only;
* `mirrorC`, `Safe`: the mirror map and the reachability invariant;
* `exists_sim_of_muM_ne_zero`, `exists_sim_of_cT_ne_zero`
  (`thm:support-equality`): the support witness, per component and for
  the fresh laws;
* `simDeg`, `dead_screen_eq_zero`, `fresh_dead_screen_eq_zero`
  (`thm:exact-pruning`): a screen whose dead indicator includes the
  namesake of its cell is exactly zero;
* `mul_simDeg_le_simDeg`: degrees are monotone under component
  minorization, the degree half of `thm:mixture-tilt-composite`.
-/
import GraphMarkovMatching.Composite.Kernel
import GraphMarkovMatching.Process.Sim

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

/-- Labels compare through their graph states only; counters and markers
are proof bookkeeping. -/
def cRel (Rv : V → V → Prop) : CState V → CState V → Prop :=
  fun s t => Rv s.1 t.1

/-! ### Positivity helpers -/

lemma exists_ne_zero_of_tsum_ne_zero {X : Type} {f : X → ℝ≥0∞}
    (h : (∑' x, f x) ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hall
  exact h (ENNReal.tsum_eq_zero.mpr fun x =>
    not_not.mp (not_exists.mp hall x))

lemma exists_of_map_ne_zero {A B : Type} {ρ : PMF A} {g : A → B} {y : B}
    (h : (ρ.map g) y ≠ 0) : ∃ a, ρ a ≠ 0 ∧ y = g a := by
  rw [PMF.map_apply] at h
  obtain ⟨a, ha⟩ := exists_ne_zero_of_tsum_ne_zero h
  by_cases hy : y = g a
  · rw [if_pos hy] at ha
    exact ⟨a, ha, hy⟩
  · rw [if_neg hy] at ha
    exact absurd rfl ha

lemma map_ne_zero_of_apply {A B : Type} (ρ : PMF A) (g : A → B) {a : A}
    (h : ρ a ≠ 0) : (ρ.map g) (g a) ≠ 0 := by
  rw [PMF.map_apply]
  intro hz
  have := ENNReal.tsum_eq_zero.mp hz a
  rw [if_pos rfl] at this
  exact h this

lemma exists_of_bind_ne_zero {A X : Type} {w : PMF A} {f : A → PMF X}
    {x : X} (h : (w.bind f) x ≠ 0) : ∃ a, w a ≠ 0 ∧ f a x ≠ 0 := by
  rw [PMF.bind_apply] at h
  obtain ⟨a, ha⟩ := exists_ne_zero_of_tsum_ne_zero h
  exact ⟨a, (mul_ne_zero_iff.mp ha).1, (mul_ne_zero_iff.mp ha).2⟩

lemma bind_ne_zero_of_apply {A X : Type} (w : PMF A) (f : A → PMF X)
    {a : A} {x : X} (hw : w a ≠ 0) (hf : f a x ≠ 0) :
    (w.bind f) x ≠ 0 := by
  intro hz
  rw [PMF.bind_apply] at hz
  exact mul_ne_zero hw hf (ENNReal.tsum_eq_zero.mp hz a)

lemma eq_of_pure_ne_zero {X : Type} {a x : X} (h : (PMF.pure a) x ≠ 0) :
    x = a := by
  rw [PMF.pure_apply] at h
  by_contra hxa
  rw [if_neg hxa] at h
  exact absurd rfl h

lemma pure_apply_self_ne_zero {X : Type} (a : X) : (PMF.pure a) a ≠ 0 := by
  rw [PMF.pure_apply, if_pos rfl]
  exact one_ne_zero

/-- Structure of a charged branch sample: the children pattern and both
subtrees are charged. -/
lemma exists_of_muM_succ_ne_zero {S : Type} {P : S → PMF (S × S)} {s : S}
    {h : ℕ} {x : FullLab S (h + 1)} (hx : muM P s (h + 1) x ≠ 0) :
    ∃ c : S × S, ∃ x₁ x₂ : FullLab S h,
      x = branch s (x₁, x₂) ∧ P s c ≠ 0 ∧
        muM P c.1 h x₁ ≠ 0 ∧ muM P c.2 h x₂ ≠ 0 := by
  rw [muM_succ] at hx
  obtain ⟨p, hp, hxp⟩ := exists_of_map_ne_zero hx
  rw [pairMix, PMF.bind_apply] at hp
  obtain ⟨c, hc⟩ := exists_ne_zero_of_tsum_ne_zero hp
  have h1 := (mul_ne_zero_iff.mp hc).1
  have h2 := (mul_ne_zero_iff.mp hc).2
  rw [prodPMF_apply] at h2
  exact ⟨c, p.1, p.2, by rw [hxp], h1,
    (mul_ne_zero_iff.mp h2).1, (mul_ne_zero_iff.mp h2).2⟩

/-- Charged children patterns and subtrees produce a charged branch. -/
lemma muM_succ_ne_zero_of {S : Type} {P : S → PMF (S × S)} {s : S} {h : ℕ}
    {c : S × S} {y₁ y₂ : FullLab S h} (hc : P s c ≠ 0)
    (h₁ : muM P c.1 h y₁ ≠ 0) (h₂ : muM P c.2 h y₂ ≠ 0) :
    muM P s (h + 1) (branch s (y₁, y₂)) ≠ 0 := by
  rw [muM_succ]
  refine map_ne_zero_of_apply _ (branch s) ?_
  refine bind_ne_zero_of_apply _ _ hc ?_
  rw [prodPMF_apply]
  exact mul_ne_zero h₁ h₂

lemma exists_of_freshC_ne_zero {μ : PMF V} {ν : PMF ℕ} {f : CState V}
    (hf : freshC μ ν f ≠ 0) :
    ∃ u m, f = (u, CtrC.ord m) ∧ μ u ≠ 0 ∧ ν m ≠ 0 := by
  rcases f with ⟨u, c⟩
  cases c with
  | ord m =>
      rw [freshC_ord_apply] at hf
      exact ⟨u, m, rfl, (mul_ne_zero_iff.mp hf).1, (mul_ne_zero_iff.mp hf).2⟩
  | mark a b i =>
      rw [freshC_mark_apply] at hf
      exact absurd rfl hf

lemma freshC_ord_ne_zero {μ : PMF V} {ν : PMF ℕ} {u : V} {m : ℕ}
    (hu : μ u ≠ 0) (hm : ν m ≠ 0) : freshC μ ν (u, CtrC.ord m) ≠ 0 := by
  rw [freshC_ord_apply]
  exact mul_ne_zero hu hm

/-! ### The mirror map and the reachability invariant -/

/-- The mirror of a left label: common counters map to themselves, an
exceptional counter to the head of its declared pair, and a marker at
stage `i` to the plain running value. -/
def mirrorC (exc1 : ℕ → Option (ℕ × ℕ)) : CState V → CState V
  | (v, CtrC.ord k) =>
      match exc1 k with
      | some p => (v, CtrC.ord p.1)
      | none => (v, CtrC.ord k)
  | (v, CtrC.mark a _ i) => (v, CtrC.ord (val a i))

lemma mirrorC_ord_none {exc1 : ℕ → Option (ℕ × ℕ)} {k : ℕ}
    (hk : exc1 k = none) (v : V) :
    mirrorC exc1 (v, CtrC.ord k) = (v, CtrC.ord k) := by
  simp [mirrorC, hk]

lemma mirrorC_ord_some {exc1 : ℕ → Option (ℕ × ℕ)} {k : ℕ} {p : ℕ × ℕ}
    (hk : exc1 k = some p) (v : V) :
    mirrorC exc1 (v, CtrC.ord k) = (v, CtrC.ord p.1) := by
  simp [mirrorC, hk]

lemma mirrorC_mark (exc1 : ℕ → Option (ℕ × ℕ)) (v : V) (a b i : ℕ) :
    mirrorC exc1 (v, CtrC.mark a b i) = (v, CtrC.ord (val a i)) := rfl

lemma mirrorC_fst (exc1 : ℕ → Option (ℕ × ℕ)) (s : CState V) :
    (mirrorC exc1 s).1 = s.1 := by
  rcases s with ⟨v, c⟩
  cases c with
  | ord k =>
      rcases hk : exc1 k with _ | p
      · rw [mirrorC_ord_none hk]
      · rw [mirrorC_ord_some hk]
  | mark a b i => rfl

/-- The reachability invariant of the left process: ordinary counters are
common or declared, and markers carry bounded data with a charged
opposite port weight. -/
def Safe (exc1 : ℕ → Option (ℕ × ℕ)) (ν2 : PMF ℕ) (N : ℕ) :
    CState V → Prop
  | (_, CtrC.ord k) => k ≤ N ∨ ∃ p, exc1 k = some p
  | (_, CtrC.mark a b _) => a ≤ N ∧ b ≤ N ∧ ν2 b ≠ 0

variable (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)

/-- A charged fresh left draw is safe, and its mirror is a charged fresh
right draw. -/
lemma safe_of_fresh
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    {f : CState V} (hf : freshC μ ν1 f ≠ 0) :
    Safe exc1 ν2 N f ∧ freshC μ ν2 (mirrorC exc1 f) ≠ 0 := by
  obtain ⟨u, m, rfl, hu, hm⟩ := exists_of_freshC_ne_zero hf
  rcases hem : exc1 m with _ | p
  · obtain ⟨hmN, hm2⟩ := hcharged m hm hem
    rw [mirrorC_ord_none hem]
    exact ⟨Or.inl hmN, freshC_ord_ne_zero hu hm2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hpair m p hem
    rw [mirrorC_ord_some hem]
    exact ⟨Or.inr ⟨p, hem⟩, freshC_ord_ne_zero hu h3⟩

/-- **The support witness** (`thm:support-equality`): every charged left
sample below a safe root has a charged right sample below the mirrored
root with vertexwise compatible states. -/
theorem exists_sim_of_muM_ne_zero
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0) :
    ∀ (h : ℕ) (s : CState V), Safe exc1 ν2 N s →
      ∀ x, muM (compK exc1 μ ν1 v0) s h x ≠ 0 →
        ∃ y, muM (compK exc2 μ ν2 v0) (mirrorC exc1 s) h y ≠ 0 ∧
          fullSim (cRel Rv) h x y := by
  intro h
  induction h with
  | zero =>
      intro s _ x hx
      have hxs : x = leaf s := eq_of_pure_ne_zero hx
      refine ⟨leaf (mirrorC exc1 s), pure_apply_self_ne_zero _, ?_⟩
      rw [hxs, fullSim_leaf]
      show Rv (leaf s).1 (mirrorC exc1 s).1
      rw [mirrorC_fst]
      exact hRv _
  | succ h ih =>
      intro s hs x hx
      obtain ⟨c, x₁, x₂, rfl, hc, hx₁, hx₂⟩ := exists_of_muM_succ_ne_zero hx
      rcases s with ⟨v, ctr⟩
      cases ctr with
      | ord k =>
          rcases hexc : exc1 k with _ | p
          · -- a common counter, balanced on both sides
            have hkN : k ≤ N := by
              rcases hs with hk | ⟨p', hp'⟩
              · exact hk
              · rw [hexc] at hp'
                exact absurd hp' (by simp)
            have hk2 : exc2 k = none := (hN k hkN).2
            rw [mirrorC_ord_none hexc]
            rcases Nat.lt_or_ge k 3 with hklt | hkge
            · -- both children fresh
              rw [compK_ord_none_le_two exc1 μ ν1 v0 hexc (by omega)] at hc
              rw [prodPMF_apply] at hc
              obtain ⟨hf₁, hf₂⟩ := mul_ne_zero_iff.mp hc
              obtain ⟨hs₁, hm₁⟩ := safe_of_fresh μ exc1 ν1 ν2 N hpair hcharged hf₁
              obtain ⟨hs₂, hm₂⟩ := safe_of_fresh μ exc1 ν1 ν2 N hpair hcharged hf₂
              obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1 hs₁ x₁ hx₁
              obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2 hs₂ x₂ hx₂
              refine ⟨branch (v, CtrC.ord k) (y₁, y₂), ?_, ?_⟩
              · refine muM_succ_ne_zero_of
                  (c := (mirrorC exc1 c.1, mirrorC exc1 c.2)) ?_ hy₁ hy₂
                rw [compK_ord_none_le_two exc2 μ ν2 v0 hk2 (by omega),
                  prodPMF_apply]
                exact mul_ne_zero hm₁ hm₂
              · rw [fullSim_branch]
                exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩
            · rcases Nat.lt_or_ge k 4 with hklt4 | hkge4
              · -- counter three: one forced child, one fresh child
                have hk3 : k = 3 := by omega
                subst hk3
                rw [compK_ord_none_three exc1 μ ν1 v0 hexc rfl] at hc
                obtain ⟨f, hf, hcf⟩ := exists_of_map_ne_zero hc
                have hc1 : c.1 = (v0, CtrC.ord 2) := by rw [hcf]
                have hc2 : c.2 = f := by rw [hcf]
                have h2N : (2 : ℕ) ≤ N := by omega
                have h2none := hN 2 h2N
                obtain ⟨hsf, hmf⟩ := safe_of_fresh μ exc1 ν1 ν2 N hpair hcharged hf
                obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1 (by rw [hc1]; exact Or.inl h2N) x₁ hx₁
                obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2 (by rw [hc2]; exact hsf) x₂ hx₂
                rw [hc1, mirrorC_ord_none h2none.1] at hy₁
                rw [hc2] at hy₂
                refine ⟨branch (v, CtrC.ord 3) (y₁, y₂), ?_, ?_⟩
                · refine muM_succ_ne_zero_of
                    (c := ((v0, CtrC.ord 2), mirrorC exc1 f)) ?_ hy₁ hy₂
                  rw [compK_ord_none_three exc2 μ ν2 v0 hk2 rfl]
                  exact map_ne_zero_of_apply _ _ hmf
                · rw [fullSim_branch]
                  exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩
              · -- a large counter: deterministic halving on both sides
                rw [compK_ord_none_of_ge exc1 μ ν1 v0 hexc hkge4] at hc
                have hcc := eq_of_pure_ne_zero hc
                have hc1 : c.1 = (v0, CtrC.ord (k / 2)) := by rw [hcc]
                have hc2 : c.2 = (v0, CtrC.ord (k - k / 2)) := by rw [hcc]
                have hhalf := hN (k / 2) (by omega)
                have hrest := hN (k - k / 2) (by omega)
                obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1 (by rw [hc1]; exact Or.inl (by omega)) x₁ hx₁
                obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2 (by rw [hc2]; exact Or.inl (by omega)) x₂ hx₂
                rw [hc1, mirrorC_ord_none hhalf.1] at hy₁
                rw [hc2, mirrorC_ord_none hrest.1] at hy₂
                refine ⟨branch (v, CtrC.ord k) (y₁, y₂), ?_, ?_⟩
                · refine muM_succ_ne_zero_of
                    (c := ((v0, CtrC.ord (k / 2)), (v0, CtrC.ord (k - k / 2)))) ?_ hy₁ hy₂
                  rw [compK_ord_none_of_ge exc2 μ ν2 v0 hk2 hkge4]
                  exact pure_apply_self_ne_zero _
                · rw [fullSim_branch]
                  exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩
          · -- an exceptional counter: the chart against its arrangement
            obtain ⟨haN, hbN, ha2, hb2⟩ := hpair k p hexc
            have hexc2a : exc2 p.1 = none := (hN p.1 haN).2
            rw [mirrorC_ord_some hexc]
            rw [compK_ord_exc exc1 μ ν1 v0 hexc] at hc
            rcases Nat.lt_or_ge p.1 3 with halt | hage
            · -- pair head at most two: port left, fresh right
              rw [markK_le_two (by rw [val_zero]; omega)] at hc
              obtain ⟨f, hf, hcf⟩ := exists_of_map_ne_zero hc
              have hc1 : c.1 = (v0, CtrC.ord p.2) := by rw [hcf]
              have hc2 : c.2 = f := by rw [hcf]
              have hbnone := hN p.2 hbN
              obtain ⟨hsf, hmf⟩ := safe_of_fresh μ exc1 ν1 ν2 N hpair hcharged hf
              obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1 (by rw [hc1]; exact Or.inl hbN) x₁ hx₁
              obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2 (by rw [hc2]; exact hsf) x₂ hx₂
              rw [hc1, mirrorC_ord_none hbnone.1] at hy₁
              rw [hc2] at hy₂
              refine ⟨branch (v, CtrC.ord p.1) (y₁, y₂), ?_, ?_⟩
              · refine muM_succ_ne_zero_of
                  (c := ((v0, CtrC.ord p.2), mirrorC exc1 f)) ?_ hy₁ hy₂
                rw [compK_ord_none_le_two exc2 μ ν2 v0 hexc2a (by omega),
                  prodPMF_apply]
                exact mul_ne_zero (freshC_ord_ne_zero hμ0 hb2) hmf
              · rw [fullSim_branch]
                exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩
            · rcases Nat.lt_or_ge p.1 4 with halt4 | hage4
              · -- pair head three: forced left, port right
                have ha3 : p.1 = 3 := by omega
                rw [markK_three (by rw [val_zero]; omega)] at hc
                have hcc := eq_of_pure_ne_zero hc
                have hc1 : c.1 = (v0, CtrC.ord 2) := by rw [hcc]
                have hc2 : c.2 = (v0, CtrC.ord p.2) := by rw [hcc]
                have h2N : (2 : ℕ) ≤ N := by omega
                have h2none := hN 2 h2N
                have hbnone := hN p.2 hbN
                obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1 (by rw [hc1]; exact Or.inl h2N) x₁ hx₁
                obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2 (by rw [hc2]; exact Or.inl hbN) x₂ hx₂
                rw [hc1, mirrorC_ord_none h2none.1] at hy₁
                rw [hc2, mirrorC_ord_none hbnone.1] at hy₂
                refine ⟨branch (v, CtrC.ord p.1) (y₁, y₂), ?_, ?_⟩
                · refine muM_succ_ne_zero_of
                    (c := ((v0, CtrC.ord 2), (v0, CtrC.ord p.2))) ?_ hy₁ hy₂
                  rw [compK_ord_none_three exc2 μ ν2 v0 hexc2a ha3]
                  exact map_ne_zero_of_apply _ _ (freshC_ord_ne_zero hμ0 hb2)
                · rw [fullSim_branch]
                  exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩
              · -- pair head at least four: marker left, halving right
                rw [markK_of_ge (by rw [val_zero]; omega)] at hc
                have hcc := eq_of_pure_ne_zero hc
                have hc1 : c.1 = (v0, CtrC.mark p.1 p.2 1) := by
                  rw [hcc]
                have hc2 : c.2 = (v0, CtrC.ord (val p.1 0 - val p.1 0 / 2)) := by
                  rw [hcc]
                have hrest := hN (p.1 - p.1 / 2) (by omega)
                obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1
                  (by rw [hc1]; exact ⟨haN, hbN, hb2⟩) x₁ hx₁
                obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2
                  (by rw [hc2, val_zero]; exact Or.inl (by omega)) x₂ hx₂
                rw [hc1, mirrorC_mark] at hy₁
                rw [hc2, val_zero, mirrorC_ord_none hrest.1] at hy₂
                have hval1 : val p.1 1 = p.1 / 2 := by
                  rw [val_succ, val_zero]
                rw [hval1] at hy₁
                refine ⟨branch (v, CtrC.ord p.1) (y₁, y₂), ?_, ?_⟩
                · refine muM_succ_ne_zero_of
                    (c := ((v0, CtrC.ord (p.1 / 2)),
                      (v0, CtrC.ord (p.1 - p.1 / 2)))) ?_ hy₁ hy₂
                  rw [compK_ord_none_of_ge exc2 μ ν2 v0 hexc2a hage4]
                  exact pure_apply_self_ne_zero _
                · rw [fullSim_branch]
                  exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩
      | mark a b i =>
          obtain ⟨haN, hbN, hb2⟩ := hs
          have hvala : val a i ≤ a := Nat.div_le_self a (2 ^ i)
          have hvnone := hN (val a i) (le_trans hvala haN)
          rw [mirrorC_mark]
          rw [compK_mark] at hc
          rcases Nat.lt_or_ge (val a i) 3 with hvlt | hvge
          · -- running value at most two: port left, fresh right
            rw [markK_le_two (by omega)] at hc
            obtain ⟨f, hf, hcf⟩ := exists_of_map_ne_zero hc
            have hc1 : c.1 = (v0, CtrC.ord b) := by rw [hcf]
            have hc2 : c.2 = f := by rw [hcf]
            have hbnone := hN b hbN
            obtain ⟨hsf, hmf⟩ := safe_of_fresh μ exc1 ν1 ν2 N hpair hcharged hf
            obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1 (by rw [hc1]; exact Or.inl hbN) x₁ hx₁
            obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2 (by rw [hc2]; exact hsf) x₂ hx₂
            rw [hc1, mirrorC_ord_none hbnone.1] at hy₁
            rw [hc2] at hy₂
            refine ⟨branch (v, CtrC.ord (val a i)) (y₁, y₂), ?_, ?_⟩
            · refine muM_succ_ne_zero_of
                (c := ((v0, CtrC.ord b), mirrorC exc1 f)) ?_ hy₁ hy₂
              rw [compK_ord_none_le_two exc2 μ ν2 v0 hvnone.2 (by omega),
                prodPMF_apply]
              exact mul_ne_zero (freshC_ord_ne_zero hμ0 hb2) hmf
            · rw [fullSim_branch]
              exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩
          · rcases Nat.lt_or_ge (val a i) 4 with hvlt4 | hvge4
            · -- running value three: forced left, port right
              have hv3 : val a i = 3 := by omega
              rw [markK_three hv3] at hc
              have hcc := eq_of_pure_ne_zero hc
              have hc1 : c.1 = (v0, CtrC.ord 2) := by rw [hcc]
              have hc2 : c.2 = (v0, CtrC.ord b) := by rw [hcc]
              have h2N : (2 : ℕ) ≤ N := by omega
              have h2none := hN 2 h2N
              have hbnone := hN b hbN
              obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1 (by rw [hc1]; exact Or.inl h2N) x₁ hx₁
              obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2 (by rw [hc2]; exact Or.inl hbN) x₂ hx₂
              rw [hc1, mirrorC_ord_none h2none.1] at hy₁
              rw [hc2, mirrorC_ord_none hbnone.1] at hy₂
              refine ⟨branch (v, CtrC.ord (val a i)) (y₁, y₂), ?_, ?_⟩
              · refine muM_succ_ne_zero_of
                  (c := ((v0, CtrC.ord 2), (v0, CtrC.ord b))) ?_ hy₁ hy₂
                rw [compK_ord_none_three exc2 μ ν2 v0 hvnone.2 hv3]
                exact map_ne_zero_of_apply _ _ (freshC_ord_ne_zero hμ0 hb2)
              · rw [fullSim_branch]
                exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩
            · -- running value at least four: the marker advances
              rw [markK_of_ge hvge4] at hc
              have hcc := eq_of_pure_ne_zero hc
              have hc1 : c.1 = (v0, CtrC.mark a b (i + 1)) := by rw [hcc]
              have hc2 : c.2 = (v0, CtrC.ord (val a i - val a i / 2)) := by rw [hcc]
              have hrest := hN (val a i - val a i / 2)
                (le_trans (by omega) haN)
              obtain ⟨y₁, hy₁, hsim₁⟩ := ih c.1
                (by rw [hc1]; exact ⟨haN, hbN, hb2⟩) x₁ hx₁
              obtain ⟨y₂, hy₂, hsim₂⟩ := ih c.2
                (by rw [hc2]; exact Or.inl (le_trans (by omega) haN)) x₂ hx₂
              rw [hc1, mirrorC_mark] at hy₁
              rw [hc2, mirrorC_ord_none hrest.1] at hy₂
              rw [val_succ] at hy₁
              refine ⟨branch (v, CtrC.ord (val a i)) (y₁, y₂), ?_, ?_⟩
              · refine muM_succ_ne_zero_of
                  (c := ((v0, CtrC.ord (val a i / 2)),
                    (v0, CtrC.ord (val a i - val a i / 2)))) ?_ hy₁ hy₂
                rw [compK_ord_none_of_ge exc2 μ ν2 v0 hvnone.2 hvge4]
                exact pure_apply_self_ne_zero _
              · rw [fullSim_branch]
                exact ⟨hRv v, Or.inl ⟨hsim₁, hsim₂⟩⟩

/-- The support witness for the fresh laws (`thm:support-equality`). -/
theorem exists_sim_of_cT_ne_zero
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (h : ℕ) (x : FullLab (CState V) h)
    (hx : cT exc1 μ ν1 v0 h x ≠ 0) :
    ∃ y, cT exc2 μ ν2 v0 h y ≠ 0 ∧ fullSim (cRel Rv) h x y := by
  obtain ⟨f, hf, hxf⟩ := exists_of_bind_ne_zero hx
  obtain ⟨hsafe, hf2⟩ :=
    safe_of_fresh μ exc1 ν1 ν2 N hpair hcharged hf
  obtain ⟨y, hy, hsim⟩ := exists_sim_of_muM_ne_zero Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged h f hsafe x hxf
  exact ⟨y, bind_ne_zero_of_apply _ _ hf2 hy, hsim⟩

/-! ### Exact pruning (`thm:exact-pruning`) -/

/-- The compatible mass of a point against a law, through a relation. -/
noncomputable def simDeg {X : Type} (ρ : PMF X) (Rel : X → X → Prop)
    (x : X) : ℝ≥0∞ :=
  ∑' y, if Rel x y then ρ y else 0

lemma simDeg_ne_zero {X : Type} {ρ : PMF X} {Rel : X → X → Prop}
    {x y : X} (hxy : Rel x y) (hy : ρ y ≠ 0) : simDeg ρ Rel x ≠ 0 := by
  intro h0
  have hterm := ENNReal.tsum_eq_zero.mp h0 y
  rw [if_pos hxy] at hterm
  exact hy hterm

/-- **Exact pruning** (`thm:exact-pruning`): a weighted dead sum vanishes
as soon as every charged source point has a compatible charged target
point and the weight vanishes wherever the target degree is positive. -/
theorem dead_screen_eq_zero {X : Type} (ρs ρt : PMF X)
    (Rel : X → X → Prop)
    (hwit : ∀ x, ρs x ≠ 0 → ∃ y, Rel x y ∧ ρt y ≠ 0) (D : X → ℝ≥0∞)
    (hD : ∀ x, simDeg ρt Rel x ≠ 0 → D x = 0) :
    (∑' x, ρs x * D x) = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : ρs x = 0
  · rw [hx, zero_mul]
  · obtain ⟨y, hxy, hy⟩ := hwit x hx
    rw [hD x (simDeg_ne_zero hxy hy), mul_zero]

/-- The fresh diagonal screen is exactly zero: any weight that vanishes
where the degree against the opposite fresh law is positive integrates to
zero against the fresh law of this side.  This discharges the liveness
input of `no_live_common_cycle` for the fresh diagonal. -/
theorem fresh_dead_screen_eq_zero
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (h : ℕ) (D : FullLab (CState V) h → ℝ≥0∞)
    (hD : ∀ x, simDeg (cT exc2 μ ν2 v0 h) (fullSim (cRel Rv) h) x ≠ 0 →
      D x = 0) :
    (∑' x, cT exc1 μ ν1 v0 h x * D x) = 0 := by
  refine dead_screen_eq_zero _ (cT exc2 μ ν2 v0 h) (fullSim (cRel Rv) h)
    (fun x hx => ?_) D hD
  obtain ⟨y, hy, hsim⟩ := exists_sim_of_cT_ne_zero Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged h x hx
  exact ⟨y, hsim, hy⟩

/-! ### Degrees under minorization: the priced-tilt input -/

lemma mul_simDeg_le_simDeg {X : Type} (c : ℝ≥0∞) {ρ ρ' : PMF X}
    (Rel : X → X → Prop) (hle : ∀ y, c * ρ y ≤ ρ' y) (x : X) :
    c * simDeg ρ Rel x ≤ simDeg ρ' Rel x := by
  rw [simDeg, simDeg, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases hxy : Rel x y
  · rw [if_pos hxy, if_pos hxy]
    exact hle y
  · rw [if_neg hxy, if_neg hxy, mul_zero]

end Composite
end GraphMarkovMatching
