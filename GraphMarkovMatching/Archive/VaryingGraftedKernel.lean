import GraphMarkovMatching.Archive.VaryingGraftedHallClose

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- Counter states for the modified encoding.  Fresh vertices only sample
`ordinary k`.  The two marker states record the deterministic provenance
needed to force a 5-pattern into the distinguished leaf. -/
inductive GraftCounter where
  | ordinary : ℕ → GraftCounter
  | force3Five : GraftCounter
  | force5Five : GraftCounter
deriving DecidableEq, Countable

abbrev GraftState (V : Type) := V × GraftCounter

/-- The fresh law embeds the original offspring counter as an ordinary tagged
counter.  Marker states are never sampled freshly. -/
noncomputable def graftFreshQ {V : Type} (μ : PMF V) (ν : PMF ℕ) :
    PMF (GraftState V) :=
  (freshQ μ ν).map fun s => (s.1, GraftCounter.ordinary s.2)

@[simp] theorem graftFreshQ_ordinary_apply {V : Type} (μ : PMF V)
    (ν : PMF ℕ) (v : V) (k : ℕ) :
    graftFreshQ μ ν (v, GraftCounter.ordinary k) = μ v * ν k := by
  change ((freshQ μ ν).map
      (fun s => (s.1, GraftCounter.ordinary s.2)) : PMF (V × GraftCounter))
    (v, GraftCounter.ordinary k) = μ v * ν k
  rw [PMF.map_apply]
  have heq : ∀ a : V × ℕ,
      ((v, GraftCounter.ordinary k) =
          (a.1, GraftCounter.ordinary a.2)) ↔ a = (v, k) := by
    intro a
    rcases a with ⟨w, j⟩
    constructor
    · intro h
      simp only [Prod.mk.injEq, GraftCounter.ordinary.injEq] at h ⊢
      exact ⟨h.1.symm, h.2.symm⟩
    · intro h
      simp only [Prod.mk.injEq, GraftCounter.ordinary.injEq] at h ⊢
      exact ⟨h.1.symm, h.2.symm⟩
  simp_rw [heq]
  rw [tsum_ite_eq]
  exact prodPMF_apply μ ν (v, k)

@[simp] theorem graftFreshQ_force3Five_apply {V : Type} (μ : PMF V)
    (ν : PMF ℕ) (v : V) :
    graftFreshQ μ ν (v, GraftCounter.force3Five) = 0 := by
  rw [graftFreshQ, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro a
  rw [if_neg]
  intro h
  exact GraftCounter.noConfusion (congrArg Prod.snd h)

@[simp] theorem graftFreshQ_force5Five_apply {V : Type} (μ : PMF V)
    (ν : PMF ℕ) (v : V) :
    graftFreshQ μ ν (v, GraftCounter.force5Five) = 0 := by
  rw [graftFreshQ, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro a
  rw [if_neg]
  intro h
  exact GraftCounter.noConfusion (congrArg Prod.snd h)

/-- The tagged binary kernel.  `left = true` installs the grafted 11 pattern;
`left = false` installs the grafted 13 pattern.  Away from those exceptional
states and the two provenance markers this is the original balanced kernel. -/
noncomputable def graftK {V : Type} (left : Bool) (μ : PMF V) (ν : PMF ℕ)
    (v0 : V) : GraftState V → PMF (GraftState V × GraftState V)
  | (_, GraftCounter.force3Five) =>
      PMF.pure ((v0, GraftCounter.ordinary 2),
        (v0, GraftCounter.ordinary 5))
  | (_, GraftCounter.force5Five) =>
      PMF.pure ((v0, GraftCounter.ordinary 2),
        (v0, GraftCounter.force3Five))
  | (_, GraftCounter.ordinary k) =>
      if left = true ∧ k = 11 then
        PMF.pure ((v0, GraftCounter.force3Five),
          (v0, GraftCounter.ordinary 4))
      else if left = false ∧ k = 13 then
        PMF.pure ((v0, GraftCounter.ordinary 4),
          (v0, GraftCounter.force5Five))
      else if 4 ≤ k then
        PMF.pure ((v0, GraftCounter.ordinary (k / 2)),
          (v0, GraftCounter.ordinary (k - k / 2)))
      else if k = 3 then
        (graftFreshQ μ ν).map fun f =>
          ((v0, GraftCounter.ordinary 2), f)
      else
        prodPMF (graftFreshQ μ ν) (graftFreshQ μ ν)

def graftLabRel {V : Type} (Rv : V → V → Prop) :
    GraftState V → GraftState V → Prop := fun s t => Rv s.1 t.1

noncomputable def graftTlaw {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (h : ℕ) : PMF (FullLab (GraftState V) h) :=
  (graftFreshQ μ ν).bind fun s => muM (graftK left μ ν v0) s h

noncomputable def graftZlaw {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (c : GraftCounter) (h : ℕ) :
    PMF (FullLab (GraftState V) h) :=
  muM (graftK left μ ν v0) (v0, c) h

noncomputable def graftXi {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (c : GraftCounter) (h : ℕ) :
    PMF (FullLab (GraftState V) h × FullLab (GraftState V) h) :=
  pairMix (graftK left μ ν v0) (v0, c) h

noncomputable def graftXiBar {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    PMF (FullLab (GraftState V) h × FullLab (GraftState V) h) :=
  ν.bind fun k => graftXi left μ ν v0 (GraftCounter.ordinary k) h

@[simp] theorem graftK_left_eleven {V : Type} (μ : PMF V) (ν : PMF ℕ)
    (v0 v : V) :
    graftK true μ ν v0 (v, GraftCounter.ordinary 11) =
      PMF.pure ((v0, GraftCounter.force3Five),
        (v0, GraftCounter.ordinary 4)) := by
  simp [graftK]

@[simp] theorem graftK_right_thirteen {V : Type} (μ : PMF V) (ν : PMF ℕ)
    (v0 v : V) :
    graftK false μ ν v0 (v, GraftCounter.ordinary 13) =
      PMF.pure ((v0, GraftCounter.ordinary 4),
        (v0, GraftCounter.force5Five)) := by
  simp [graftK]

@[simp] theorem graftK_force3Five {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 v : V) :
    graftK left μ ν v0 (v, GraftCounter.force3Five) =
      PMF.pure ((v0, GraftCounter.ordinary 2),
        (v0, GraftCounter.ordinary 5)) := rfl

@[simp] theorem graftK_force5Five {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 v : V) :
    graftK left μ ν v0 (v, GraftCounter.force5Five) =
      PMF.pure ((v0, GraftCounter.ordinary 2),
        (v0, GraftCounter.force3Five)) := rfl

theorem graftK_right_seven {V : Type} (μ : PMF V) (ν : PMF ℕ)
    (v0 v : V) :
    graftK false μ ν v0 (v, GraftCounter.ordinary 7) =
      PMF.pure ((v0, GraftCounter.ordinary 3),
        (v0, GraftCounter.ordinary 4)) := by
  norm_num [graftK]

theorem graftK_left_nine {V : Type} (μ : PMF V) (ν : PMF ℕ)
    (v0 v : V) :
    graftK true μ ν v0 (v, GraftCounter.ordinary 9) =
      PMF.pure ((v0, GraftCounter.ordinary 4),
        (v0, GraftCounter.ordinary 5)) := by
  norm_num [graftK]

theorem graftK_ordinary_three {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 v : V) :
    graftK left μ ν v0 (v, GraftCounter.ordinary 3) =
      (graftFreshQ μ ν).map fun f =>
        ((v0, GraftCounter.ordinary 2), f) := by
  cases left <;> simp [graftK]

theorem graftK_ordinary_five {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 v : V) :
    graftK left μ ν v0 (v, GraftCounter.ordinary 5) =
      PMF.pure ((v0, GraftCounter.ordinary 2),
        (v0, GraftCounter.ordinary 3)) := by
  cases left <;> norm_num [graftK]

theorem graftK_ordinary_four {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 v : V) :
    graftK left μ ν v0 (v, GraftCounter.ordinary 4) =
      PMF.pure ((v0, GraftCounter.ordinary 2),
        (v0, GraftCounter.ordinary 2)) := by
  cases left <;> simp [graftK]

theorem graftK_ordinary_of_le_two {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 v : V) {k : ℕ} (hk : k ≤ 2) :
    graftK left μ ν v0 (v, GraftCounter.ordinary k) =
      prodPMF (graftFreshQ μ ν) (graftFreshQ μ ν) := by
  cases left
  · rw [graftK, if_neg (by simp), if_neg (by simp; omega),
      if_neg (by omega), if_neg (by omega)]
  · rw [graftK, if_neg (by simp; omega), if_neg (by simp),
      if_neg (by omega), if_neg (by omega)]

lemma pairMix_pure_pattern {S : Type} (P : S → PMF (S × S))
    (s a b : S) (h : ℕ) (hs : P s = PMF.pure (a, b)) :
    pairMix P s h = prodPMF (muM P a h) (muM P b h) := by
  rw [pairMix, hs]
  simp

theorem graftXi_left_eleven {V : Type} (μ : PMF V) (ν : PMF ℕ)
    (v0 : V) (h : ℕ) :
    graftXi true μ ν v0 (GraftCounter.ordinary 11) h =
      prodPMF (graftZlaw true μ ν v0 GraftCounter.force3Five h)
        (graftZlaw true μ ν v0 (GraftCounter.ordinary 4) h) := by
  exact pairMix_pure_pattern _ _ _ _ _ (graftK_left_eleven μ ν v0 v0)

theorem graftXi_right_seven {V : Type} (μ : PMF V) (ν : PMF ℕ)
    (v0 : V) (h : ℕ) :
    graftXi false μ ν v0 (GraftCounter.ordinary 7) h =
      prodPMF (graftZlaw false μ ν v0 (GraftCounter.ordinary 3) h)
        (graftZlaw false μ ν v0 (GraftCounter.ordinary 4) h) := by
  exact pairMix_pure_pattern _ _ _ _ _ (graftK_right_seven μ ν v0 v0)

theorem graftXi_right_thirteen {V : Type} (μ : PMF V) (ν : PMF ℕ)
    (v0 : V) (h : ℕ) :
    graftXi false μ ν v0 (GraftCounter.ordinary 13) h =
      prodPMF (graftZlaw false μ ν v0 (GraftCounter.ordinary 4) h)
        (graftZlaw false μ ν v0 GraftCounter.force5Five h) := by
  exact pairMix_pure_pattern _ _ _ _ _ (graftK_right_thirteen μ ν v0 v0)

theorem graftXi_left_nine {V : Type} (μ : PMF V) (ν : PMF ℕ)
    (v0 : V) (h : ℕ) :
    graftXi true μ ν v0 (GraftCounter.ordinary 9) h =
      prodPMF (graftZlaw true μ ν v0 (GraftCounter.ordinary 4) h)
        (graftZlaw true μ ν v0 (GraftCounter.ordinary 5) h) := by
  exact pairMix_pure_pattern _ _ _ _ _ (graftK_left_nine μ ν v0 v0)

theorem graftXi_force3Five {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    graftXi left μ ν v0 GraftCounter.force3Five h =
      prodPMF (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h)
        (graftZlaw left μ ν v0 (GraftCounter.ordinary 5) h) := by
  exact pairMix_pure_pattern _ _ _ _ _ (graftK_force3Five left μ ν v0 v0)

theorem graftXi_force5Five {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    graftXi left μ ν v0 GraftCounter.force5Five h =
      prodPMF (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h)
        (graftZlaw left μ ν v0 GraftCounter.force3Five h) := by
  exact pairMix_pure_pattern _ _ _ _ _ (graftK_force5Five left μ ν v0 v0)

/-! ### Exact ordinary and selected-component laws -/

theorem graftXi_ordinary_three {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    graftXi left μ ν v0 (GraftCounter.ordinary 3) h =
      prodPMF
        (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h)
        (graftTlaw left μ ν v0 h) := by
  rw [graftXi, pairMix, graftK_ordinary_three, PMF.bind_map]
  rw [show ((fun στ : GraftState V × GraftState V =>
        prodPMF (muM (graftK left μ ν v0) στ.1 h)
          (muM (graftK left μ ν v0) στ.2 h))
      ∘ fun f => ((v0, GraftCounter.ordinary 2), f)) =
        fun f => prodPMF
          (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h)
          (muM (graftK left μ ν v0) f h) from rfl]
  exact bind_prodPMF_const_left _ _ _

theorem graftXi_ordinary_five {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    graftXi left μ ν v0 (GraftCounter.ordinary 5) h =
      prodPMF
        (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h)
        (graftZlaw left μ ν v0 (GraftCounter.ordinary 3) h) := by
  exact pairMix_pure_pattern _ _ _ _ _
    (graftK_ordinary_five left μ ν v0 v0)

theorem graftXi_ordinary_four {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    graftXi left μ ν v0 (GraftCounter.ordinary 4) h =
      prodPMF
        (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h)
        (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h) := by
  exact pairMix_pure_pattern _ _ _ _ _
    (graftK_ordinary_four left μ ν v0 v0)

theorem graftXi_ordinary_of_le_two {V : Type} (left : Bool) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) {k : ℕ} (hk : k ≤ 2) (h : ℕ) :
    graftXi left μ ν v0 (GraftCounter.ordinary k) h =
      prodPMF (graftTlaw left μ ν v0 h) (graftTlaw left μ ν v0 h) := by
  rw [graftXi, pairMix, graftK_ordinary_of_le_two left μ ν v0 v0 hk]
  exact prodPMF_bind_prodPMF (graftFreshQ μ ν) (graftFreshQ μ ν)
    (fun s => muM (graftK left μ ν v0) s h)
    (fun s => muM (graftK left μ ν v0) s h)

lemma graftZlaw_succ {V : Type} (left : Bool) (μ : PMF V) (ν : PMF ℕ)
    (v0 : V) (c : GraftCounter) (h : ℕ) :
    graftZlaw left μ ν v0 c (h + 1) =
      (graftXi left μ ν v0 c h).map
        (branch (v0, c)) := rfl

/-- Every ordinary frozen context is a literal component of the fresh tagged
law.  The coefficient is exactly `μ(v0)ν(k)`; marker states are deliberately
excluded because their fresh mass is zero. -/
theorem graftFreshQ_mul_graftZlaw_le_graftTlaw {V : Type} (left : Bool)
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) (k h : ℕ)
    (x : FullLab (GraftState V) h) :
    graftFreshQ μ ν (v0, GraftCounter.ordinary k) *
        graftZlaw left μ ν v0 (GraftCounter.ordinary k) h x
      ≤ graftTlaw left μ ν v0 h x := by
  rw [graftTlaw, PMF.bind_apply]
  exact ENNReal.le_tsum (v0, GraftCounter.ordinary k)

/-- Pointwise component minorization for an arbitrary PMF mixture. -/
lemma pmf_component_le_bind {A X : Type} (w : PMF A) (f : A → PMF X)
    (a : A) (x : X) : w a * f a x ≤ (w.bind f) x := by
  rw [PMF.bind_apply]
  exact ENNReal.le_tsum a

/-- The selected `5` child inside an ordinary counter `3`.  This is the
literal process-law component used by the grafted `11` replacement, before
the root counter tag is attached. -/
noncomputable def graftThreeFiveChildComponent {V : Type} (left : Bool)
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    PMF (FullLab (GraftState V) h × FullLab (GraftState V) h) :=
  prodPMF
    (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h)
    (graftZlaw left μ ν v0 (GraftCounter.ordinary 5) h)

theorem graftThreeFiveChildComponent_le_Xi_three {V : Type}
    (left : Bool) (μ : PMF V) (ν : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    graftFreshQ μ ν (v0, GraftCounter.ordinary 5) *
        graftThreeFiveChildComponent left μ ν v0 h x
      ≤ graftXi left μ ν v0 (GraftCounter.ordinary 3) h x := by
  rw [graftXi_ordinary_three]
  rw [graftThreeFiveChildComponent, prodPMF_apply, prodPMF_apply]
  calc
    graftFreshQ μ ν (v0, GraftCounter.ordinary 5) *
          (graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h x.1 *
            graftZlaw left μ ν v0 (GraftCounter.ordinary 5) h x.2)
        = graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h x.1 *
            (graftFreshQ μ ν (v0, GraftCounter.ordinary 5) *
              graftZlaw left μ ν v0 (GraftCounter.ordinary 5) h x.2) := by ring
    _ ≤ graftZlaw left μ ν v0 (GraftCounter.ordinary 2) h x.1 *
          graftTlaw left μ ν v0 h x.2 :=
      mul_le_mul_right
        (graftFreshQ_mul_graftZlaw_le_graftTlaw left μ ν v0 5 h x.2) _

lemma mul_map_le_map {A X : Type} (p : ℝ≥0∞) (ρ σ : PMF A) (f : A → X)
    (hρ : ∀ x, p * ρ x ≤ σ x) (y : X) :
    p * (ρ.map f) y ≤ (σ.map f) y := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun x => by
    by_cases hx : y = f x
    · rw [if_pos hx, if_pos hx]
      exact hρ x
    · simp [hx]

lemma mul_prodPMF_le_prodPMF_left {A B : Type} (p : ℝ≥0∞)
    (ρ ρ' : PMF A) (τ : PMF B) (hρ : ∀ x, p * ρ x ≤ ρ' x)
    (z : A × B) :
    p * prodPMF ρ τ z ≤ prodPMF ρ' τ z := by
  rw [prodPMF_apply, prodPMF_apply]
  calc
    p * (ρ z.1 * τ z.2) = (p * ρ z.1) * τ z.2 := by ring
    _ ≤ ρ' z.1 * τ z.2 := by
      simpa [mul_comm, mul_left_comm] using
        (mul_le_mul_right (hρ z.1) (τ z.2))

lemma mul_prodPMF_le_prodPMF_right {A B : Type} (p : ℝ≥0∞)
    (ρ : PMF A) (τ τ' : PMF B) (hτ : ∀ y, p * τ y ≤ τ' y)
    (z : A × B) :
    p * prodPMF ρ τ z ≤ prodPMF ρ τ' z := by
  rw [prodPMF_apply, prodPMF_apply]
  calc
    p * (ρ z.1 * τ z.2) = ρ z.1 * (p * τ z.2) := by ring
    _ ≤ ρ z.1 * τ' z.2 := mul_le_mul_right (hτ z.2) _

/-- The complete selected subtree under an ordinary counter `3`: its root is
the ordinary `3` state, and its fresh child has been fixed to ordinary `5`. -/
noncomputable def graftThreeFiveTreeComponent {V : Type} (left : Bool)
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    PMF (FullLab (GraftState V) (h + 1)) :=
  (graftThreeFiveChildComponent left μ ν v0 h).map
    (branch (v0, GraftCounter.ordinary 3))

theorem graftThreeFiveTreeComponent_le_Zthree {V : Type}
    (left : Bool) (μ : PMF V) (ν : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) (h + 1)) :
    graftFreshQ μ ν (v0, GraftCounter.ordinary 5) *
        graftThreeFiveTreeComponent left μ ν v0 h x
      ≤ graftZlaw left μ ν v0 (GraftCounter.ordinary 3) (h + 1) x := by
  rw [graftZlaw_succ]
  exact mul_map_le_map _ _ _ _
    (graftThreeFiveChildComponent_le_Xi_three left μ ν v0 h) x

/-- The selected right-law `7`--then--`5` pair component, at the child-pair
level consumed below a fresh root. -/
noncomputable def graftElevenReplacementComponent {V : Type}
    (μ : PMF V) (νR : PMF ℕ) (v0 : V) (h : ℕ) :
    PMF (FullLab (GraftState V) (h + 1) ×
      FullLab (GraftState V) (h + 1)) :=
  prodPMF (graftThreeFiveTreeComponent false μ νR v0 h)
    (graftZlaw false μ νR v0 (GraftCounter.ordinary 4) (h + 1))

theorem graftElevenReplacementComponent_le_Xi_seven {V : Type}
    (μ : PMF V) (νR : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) (h + 1) ×
      FullLab (GraftState V) (h + 1)) :
    graftFreshQ μ νR (v0, GraftCounter.ordinary 5) *
        graftElevenReplacementComponent μ νR v0 h x
      ≤ graftXi false μ νR v0 (GraftCounter.ordinary 7) (h + 1) x := by
  rw [graftXi_right_seven]
  exact mul_prodPMF_le_prodPMF_left _ _ _ _
    (graftThreeFiveTreeComponent_le_Zthree false μ νR v0 h) x

/-- The exceptional replacement is a literal component of the actual right
fresh child-pair mixture, with the exact two-stage mass
`νR(7) μ(v0) νR(5)`. -/
theorem graftElevenReplacementComponent_le_XiBar {V : Type}
    (μ : PMF V) (νR : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) (h + 1) ×
      FullLab (GraftState V) (h + 1)) :
    ((νR 7 : ℝ≥0∞) * graftFreshQ μ νR
        (v0, GraftCounter.ordinary 5)) *
        graftElevenReplacementComponent μ νR v0 h x
      ≤ graftXiBar false μ νR v0 (h + 1) x := by
  rw [graftXiBar, PMF.bind_apply]
  calc
    ((νR 7 : ℝ≥0∞) * graftFreshQ μ νR
          (v0, GraftCounter.ordinary 5)) *
          graftElevenReplacementComponent μ νR v0 h x
        = (νR 7 : ℝ≥0∞) *
            (graftFreshQ μ νR (v0, GraftCounter.ordinary 5) *
              graftElevenReplacementComponent μ νR v0 h x) := by ring
    _ ≤ (νR 7 : ℝ≥0∞) *
          graftXi false μ νR v0 (GraftCounter.ordinary 7) (h + 1) x :=
      mul_le_mul_right
        (graftElevenReplacementComponent_le_Xi_seven μ νR v0 h x) _
    _ ≤ ∑' k, νR k *
          graftXi false μ νR v0 (GraftCounter.ordinary k) (h + 1) x :=
      ENNReal.le_tsum 7

/-- The selected subtree under a left-law ordinary `5`, where the internal
ordinary `3` has itself selected an ordinary `5` fresh child. -/
noncomputable def graftFiveFiveTreeComponent {V : Type} (μ : PMF V)
    (νL : PMF ℕ) (v0 : V) (h : ℕ) :
    PMF (FullLab (GraftState V) (h + 2)) :=
  (prodPMF
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) (h + 1))
      (graftThreeFiveTreeComponent true μ νL v0 h)).map
    (branch (v0, GraftCounter.ordinary 5))

theorem graftFiveFiveTreeComponent_le_Zfive {V : Type} (μ : PMF V)
    (νL : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) (h + 2)) :
    graftFreshQ μ νL (v0, GraftCounter.ordinary 5) *
        graftFiveFiveTreeComponent μ νL v0 h x
      ≤ graftZlaw true μ νL v0 (GraftCounter.ordinary 5) (h + 2) x := by
  change graftFreshQ μ νL (v0, GraftCounter.ordinary 5) *
      graftFiveFiveTreeComponent μ νL v0 h x ≤
    graftZlaw true μ νL v0 (GraftCounter.ordinary 5) ((h + 1) + 1) x
  rw [graftZlaw_succ, graftXi_ordinary_five]
  apply mul_map_le_map
  intro z
  exact mul_prodPMF_le_prodPMF_right _ _ _ _
    (graftThreeFiveTreeComponent_le_Zthree true μ νL v0 h) z

/-- The selected left-law `9`--then--`5` pair component used to replace the
right exceptional counter `13`. -/
noncomputable def graftThirteenReplacementComponent {V : Type}
    (μ : PMF V) (νL : PMF ℕ) (v0 : V) (h : ℕ) :
    PMF (FullLab (GraftState V) (h + 2) ×
      FullLab (GraftState V) (h + 2)) :=
  prodPMF
    (graftZlaw true μ νL v0 (GraftCounter.ordinary 4) (h + 2))
    (graftFiveFiveTreeComponent μ νL v0 h)

theorem graftThirteenReplacementComponent_le_Xi_nine {V : Type}
    (μ : PMF V) (νL : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) (h + 2) ×
      FullLab (GraftState V) (h + 2)) :
    graftFreshQ μ νL (v0, GraftCounter.ordinary 5) *
        graftThirteenReplacementComponent μ νL v0 h x
      ≤ graftXi true μ νL v0 (GraftCounter.ordinary 9) (h + 2) x := by
  rw [graftXi_left_nine]
  exact mul_prodPMF_le_prodPMF_right _ _ _ _
    (graftFiveFiveTreeComponent_le_Zfive μ νL v0 h) x

/-- The reverse replacement is a component of the actual left fresh
child-pair mixture with exact mass `νL(9) μ(v0) νL(5)`. -/
theorem graftThirteenReplacementComponent_le_XiBar {V : Type}
    (μ : PMF V) (νL : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) (h + 2) ×
      FullLab (GraftState V) (h + 2)) :
    ((νL 9 : ℝ≥0∞) * graftFreshQ μ νL
        (v0, GraftCounter.ordinary 5)) *
        graftThirteenReplacementComponent μ νL v0 h x
      ≤ graftXiBar true μ νL v0 (h + 2) x := by
  rw [graftXiBar, PMF.bind_apply]
  calc
    ((νL 9 : ℝ≥0∞) * graftFreshQ μ νL
          (v0, GraftCounter.ordinary 5)) *
          graftThirteenReplacementComponent μ νL v0 h x
        = (νL 9 : ℝ≥0∞) *
            (graftFreshQ μ νL (v0, GraftCounter.ordinary 5) *
              graftThirteenReplacementComponent μ νL v0 h x) := by ring
    _ ≤ (νL 9 : ℝ≥0∞) *
          graftXi true μ νL v0 (GraftCounter.ordinary 9) (h + 2) x :=
      mul_le_mul_right
        (graftThirteenReplacementComponent_le_Xi_nine μ νL v0 h x) _
    _ ≤ ∑' k, νL k *
          graftXi true μ νL v0 (GraftCounter.ordinary k) (h + 2) x :=
      ENNReal.le_tsum 9

end GraphMarkovMatching
