/-
Actual tagged-process Hall rows for the grafted 11/13 example.

Unlike the earlier abstract macro interface, the target in this file is the
literal child-pair mixture of `graftK`.  The selected `7`--then--`5` and
`9`--then--`5` laws were constructed in `VaryingGraftedKernel`, where their
pointwise mixture minorizations were proved with their exact cylinder masses.
-/
import GraphMarkovMatching.Archive.VaryingGraftedKernel
import GraphMarkovMatching.Tail.Hybrid
import GraphMarkovMatching.Archive.TwoCeiling

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

lemma mul_rE_le_of_pmf_minorization {X : Type} (p : ℝ≥0∞)
    (ρrep ρt : PMF X) (R : X → X → Prop)
    (hmin : ∀ y, p * ρrep y ≤ ρt y) (x : X) :
    p * rE ρrep R x ≤ rE ρt R x := by
  rw [rE, rE, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun y => by
    by_cases hxy : R x y
    · rw [if_pos hxy, if_pos hxy]
      exact hmin y
    · simp [hxy]

lemma elevenTaggedMass_eq {V : Type} (μ : PMF V) (νR : PMF ℕ) (v0 : V) :
    (νR 7 : ℝ≥0∞) *
        graftFreshQ μ νR (v0, GraftCounter.ordinary 5) =
      replacementMass (νR 7) (μ v0) (νR 5) := by
  simp [replacementMass]
  ring

lemma thirteenTaggedMass_eq {V : Type} (μ : PMF V) (νL : PMF ℕ) (v0 : V) :
    (νL 9 : ℝ≥0∞) *
        graftFreshQ μ νL (v0, GraftCounter.ordinary 5) =
      replacementMass (νL 9) (μ v0) (νL 5) := by
  simp [replacementMass]
  ring

theorem elevenTagged_rE_minorization {V : Type} (Rv : V → V → Prop)
    (μ : PMF V) (νR : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) (h + 1) ×
      FullLab (GraftState V) (h + 1)) :
    replacementMass (νR 7) (μ v0) (νR 5) *
        rE (graftElevenReplacementComponent μ νR v0 h)
          (SquareRel (fullSim (graftLabRel Rv) (h + 1))) x
      ≤ rE (graftXiBar false μ νR v0 (h + 1))
          (SquareRel (fullSim (graftLabRel Rv) (h + 1))) x := by
  rw [← elevenTaggedMass_eq]
  exact mul_rE_le_of_pmf_minorization _ _ _ _
    (graftElevenReplacementComponent_le_XiBar μ νR v0 h) x

theorem thirteenTagged_rE_minorization {V : Type} (Rv : V → V → Prop)
    (μ : PMF V) (νL : PMF ℕ) (v0 : V) (h : ℕ)
    (x : FullLab (GraftState V) (h + 2) ×
      FullLab (GraftState V) (h + 2)) :
    replacementMass (νL 9) (μ v0) (νL 5) *
        rE (graftThirteenReplacementComponent μ νL v0 h)
          (SquareRel (fullSim (graftLabRel Rv) (h + 2))) x
      ≤ rE (graftXiBar true μ νL v0 (h + 2))
          (SquareRel (fullSim (graftLabRel Rv) (h + 2))) x := by
  rw [← thirteenTaggedMass_eq]
  exact mul_rE_le_of_pmf_minorization _ _ _ _
    (graftThirteenReplacementComponent_le_XiBar μ νL v0 h) x

/-! ### Recursive ceilings for the selected replacement components -/

noncomputable def graftPairBound (α : ℝ) (a b : ℝ≥0∞) : ℝ≥0∞ :=
  a + b + ENNReal.ofReal (2 * α) * (a * b)

noncomputable def graftDoubleBound (α : ℝ) (M : ℝ≥0∞) : ℝ≥0∞ :=
  graftPairBound α M M

lemma graftPairBound_ne_top {α : ℝ} {a b : ℝ≥0∞}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) : graftPairBound α a b ≠ ⊤ := by
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.add_ne_top.2 ⟨ha, hb⟩,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ha hb)⟩

lemma graftDoubleBound_ne_top {α : ℝ} {M : ℝ≥0∞} (hM : M ≠ ⊤) :
    graftDoubleBound α M ≠ ⊤ := by
  exact graftPairBound_ne_top hM hM

lemma PhiD_map_branch_eq {S : Type} {h : ℕ} (α : ℝ)
    (ρs ρt : PMF (FullLab S h × FullLab S h))
    (R₀ : S → S → Prop) (s t : S) (hst : R₀ s t) :
    PhiD α (ρs.map (branch s)) (ρt.map (branch t))
        (fullSim R₀ (h + 1)) =
      PhiD α ρs ρt (SquareRel (fullSim R₀ h)) := by
  rw [PhiD_map_left, PhiD]
  exact tsum_congr fun xp => by
    rw [q, q, qE_map_branch_law, if_pos hst]

theorem PhiD_graftMarker3_to_threeFive_le {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0) (h : ℕ) (M : ℝ≥0∞)
    (h2 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h5 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M) :
    PhiD α
        (graftZlaw true μ νL v0 GraftCounter.force3Five (h + 1))
        (graftThreeFiveTreeComponent false μ νR v0 h)
        (fullSim (graftLabRel Rv) (h + 1))
      ≤ graftDoubleBound α M := by
  rw [graftZlaw_succ, graftThreeFiveTreeComponent,
    PhiD_map_branch_eq α _ _ (graftLabRel Rv)
      (v0, GraftCounter.force3Five)
      (v0, GraftCounter.ordinary 3) (by simpa [graftLabRel] using hrefl),
    graftXi_force3Five, graftThreeFiveChildComponent]
  exact (PhiD_square_straight_le hα _ _ _ _ _).trans (by
    simp only [graftDoubleBound, graftPairBound]
    gcongr)

theorem PhiD_graftZfour_cross_le {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop)
    (leftSource leftTarget : Bool) (μ : PMF V) (νs νt : PMF ℕ)
    (v0 : V) (hrefl : Rv v0 v0) (h : ℕ) (M : ℝ≥0∞)
    (h2 : PhiD α
      (graftZlaw leftSource μ νs v0 (GraftCounter.ordinary 2) h)
      (graftZlaw leftTarget μ νt v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M) :
    PhiD α
        (graftZlaw leftSource μ νs v0 (GraftCounter.ordinary 4) (h + 1))
        (graftZlaw leftTarget μ νt v0 (GraftCounter.ordinary 4) (h + 1))
        (fullSim (graftLabRel Rv) (h + 1))
      ≤ graftDoubleBound α M := by
  rw [graftZlaw_succ, graftZlaw_succ,
    PhiD_map_branch_eq α _ _ (graftLabRel Rv)
      (v0, GraftCounter.ordinary 4)
      (v0, GraftCounter.ordinary 4) (by simpa [graftLabRel] using hrefl),
    graftXi_ordinary_four, graftXi_ordinary_four]
  exact (PhiD_square_straight_le hα _ _ _ _ _).trans (by
    simp only [graftDoubleBound, graftPairBound]
    gcongr)

/-- The actual `11` source component versus its selected right replacement
has a two-level product ceiling depending only on the lower ordinary
`2→2` and `5→5` cross coordinates. -/
theorem PhiD_elevenReplacement_le {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0) (h : ℕ) (M : ℝ≥0∞)
    (h2 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h5 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M) :
    PhiD α
      (graftXi true μ νL v0 (GraftCounter.ordinary 11) (h + 1))
      (graftElevenReplacementComponent μ νR v0 h)
      (SquareRel (fullSim (graftLabRel Rv) (h + 1))) ≤
        graftDoubleBound α (graftDoubleBound α M) := by
  rw [graftXi_left_eleven, graftElevenReplacementComponent]
  refine (PhiD_square_straight_le hα _ _ _ _ _).trans ?_
  have hm := PhiD_graftMarker3_to_threeFive_le hα Rv μ νL νR v0 hrefl h M h2 h5
  have h4 := PhiD_graftZfour_cross_le hα Rv true false μ νL νR
    v0 hrefl h M h2
  have hm' : PhiD α
      (graftZlaw true μ νL v0 GraftCounter.force3Five (h + 1))
      (graftThreeFiveTreeComponent false μ νR v0 h)
      (fullSim (graftLabRel Rv) (h + 1)) ≤
        M + M + ENNReal.ofReal (2 * α) * (M * M) := by
    simpa [graftDoubleBound, graftPairBound] using hm
  have h4' : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 4) (h + 1))
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 4) (h + 1))
      (fullSim (graftLabRel Rv) (h + 1)) ≤
        M + M + ENNReal.ofReal (2 * α) * (M * M) := by
    simpa [graftDoubleBound, graftPairBound] using h4
  simp only [graftDoubleBound, graftPairBound]
  gcongr

theorem PhiD_graftZtwo_succ_cross_le {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop)
    (leftSource leftTarget : Bool) (μ : PMF V) (νs νt : PMF ℕ)
    (v0 : V) (hrefl : Rv v0 v0) (h : ℕ) (M : ℝ≥0∞)
    (hF : PhiD α (graftTlaw leftSource μ νs v0 h)
      (graftTlaw leftTarget μ νt v0 h)
      (fullSim (graftLabRel Rv) h) ≤ M) :
    PhiD α
        (graftZlaw leftSource μ νs v0 (GraftCounter.ordinary 2) (h + 1))
        (graftZlaw leftTarget μ νt v0 (GraftCounter.ordinary 2) (h + 1))
        (fullSim (graftLabRel Rv) (h + 1))
      ≤ graftDoubleBound α M := by
  rw [graftZlaw_succ, graftZlaw_succ,
    PhiD_map_branch_eq α _ _ (graftLabRel Rv)
      (v0, GraftCounter.ordinary 2)
      (v0, GraftCounter.ordinary 2) (by simpa [graftLabRel] using hrefl),
    graftXi_ordinary_of_le_two leftSource μ νs v0 (by omega) h,
    graftXi_ordinary_of_le_two leftTarget μ νt v0 (by omega) h]
  exact (PhiD_square_straight_le hα _ _ _ _ _).trans (by
    simp only [graftDoubleBound, graftPairBound]
    gcongr)

theorem PhiD_graftMarker3_reverse_to_threeFive_le {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νR νL : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0) (h : ℕ) (M : ℝ≥0∞)
    (h2 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h5 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M) :
    PhiD α
        (graftZlaw false μ νR v0 GraftCounter.force3Five (h + 1))
        (graftThreeFiveTreeComponent true μ νL v0 h)
        (fullSim (graftLabRel Rv) (h + 1))
      ≤ graftDoubleBound α M := by
  rw [graftZlaw_succ, graftThreeFiveTreeComponent,
    PhiD_map_branch_eq α _ _ (graftLabRel Rv)
      (v0, GraftCounter.force3Five)
      (v0, GraftCounter.ordinary 3) (by simpa [graftLabRel] using hrefl),
    graftXi_force3Five, graftThreeFiveChildComponent]
  exact (PhiD_square_straight_le hα _ _ _ _ _).trans (by
    simp only [graftDoubleBound, graftPairBound]
    gcongr)

theorem PhiD_graftMarker5_to_fiveFive_le {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νR νL : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0) (h : ℕ) (M : ℝ≥0∞)
    (hF : PhiD α (graftTlaw false μ νR v0 h)
      (graftTlaw true μ νL v0 h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h2 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h5 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M) :
    PhiD α
        (graftZlaw false μ νR v0 GraftCounter.force5Five (h + 2))
        (graftFiveFiveTreeComponent μ νL v0 h)
        (fullSim (graftLabRel Rv) (h + 2))
      ≤ graftDoubleBound α (graftDoubleBound α M) := by
  change PhiD α
      (graftZlaw false μ νR v0 GraftCounter.force5Five ((h + 1) + 1))
      (graftFiveFiveTreeComponent μ νL v0 h)
      (fullSim (graftLabRel Rv) ((h + 1) + 1)) ≤ _
  rw [graftZlaw_succ, graftFiveFiveTreeComponent,
    PhiD_map_branch_eq α _ _ (graftLabRel Rv)
      (v0, GraftCounter.force5Five)
      (v0, GraftCounter.ordinary 5) (by simpa [graftLabRel] using hrefl),
    graftXi_force5Five]
  refine (PhiD_square_straight_le hα _ _ _ _ _).trans ?_
  have h2s := PhiD_graftZtwo_succ_cross_le hα Rv false true μ νR νL
    v0 hrefl h M hF
  have hm := PhiD_graftMarker3_reverse_to_threeFive_le hα Rv μ νR νL
    v0 hrefl h M h2 h5
  have h2s' : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) (h + 1))
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) (h + 1))
      (fullSim (graftLabRel Rv) (h + 1)) ≤
        M + M + ENNReal.ofReal (2 * α) * (M * M) := by
    simpa [graftDoubleBound, graftPairBound] using h2s
  have hm' : PhiD α
      (graftZlaw false μ νR v0 GraftCounter.force3Five (h + 1))
      (graftThreeFiveTreeComponent true μ νL v0 h)
      (fullSim (graftLabRel Rv) (h + 1)) ≤
        M + M + ENNReal.ofReal (2 * α) * (M * M) := by
    simpa [graftDoubleBound, graftPairBound] using hm
  simp only [graftDoubleBound, graftPairBound]
  gcongr

/-- The actual reverse exceptional component has a three-level product
ceiling.  Besides the lower forced coordinates it needs the ordinary
fresh-to-fresh reverse coordinate at the same lower height. -/
theorem PhiD_thirteenReplacement_le {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0) (h : ℕ) (M : ℝ≥0∞)
    (hF : PhiD α (graftTlaw false μ νR v0 h)
      (graftTlaw true μ νL v0 h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h2 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h5 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M) :
    PhiD α
      (graftXi false μ νR v0 (GraftCounter.ordinary 13) (h + 2))
      (graftThirteenReplacementComponent μ νL v0 h)
      (SquareRel (fullSim (graftLabRel Rv) (h + 2))) ≤
        graftDoubleBound α
          (graftDoubleBound α (graftDoubleBound α M)) := by
  rw [graftXi_right_thirteen, graftThirteenReplacementComponent]
  refine (PhiD_square_straight_le hα _ _ _ _ _).trans ?_
  have h2s := PhiD_graftZtwo_succ_cross_le hα Rv false true μ νR νL
    v0 hrefl h M hF
  have h4 := PhiD_graftZfour_cross_le hα Rv false true μ νR νL
    v0 hrefl (h + 1) (graftDoubleBound α M) h2s
  have hm := PhiD_graftMarker5_to_fiveFive_le hα Rv μ νR νL v0 hrefl
    h M hF h2 h5
  have h4' : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 4) (h + 2))
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 4) (h + 2))
      (fullSim (graftLabRel Rv) (h + 2)) ≤
        graftDoubleBound α (graftDoubleBound α M) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h4
  simp only [graftDoubleBound, graftPairBound] at hm ⊢
  have h4'' := h4'
  simp only [graftDoubleBound, graftPairBound] at h4''
  gcongr

/-- Complete left-exceptional tagged Hall row.  The only recursive input is
the finite directed-potential ceiling `M` between the actual source 11
component and the actual selected right replacement component.  That ceiling
simultaneously proves support positivity, so no support premise remains. -/
theorem rare_elevenTagged_PhiDres_le {V : Type} {α : ℝ} (hα : 1 ≤ α)
    (Rv : V → V → Prop) (μ : PMF V) (νL νR : PMF ℕ) (v0 : V)
    (h : ℕ) (M : ℝ≥0∞) {ζ c : ℝ≥0∞}
    (hMtop : M ≠ ⊤)
    (hM : PhiD α
      (graftXi true μ νL v0 (GraftCounter.ordinary 11) (h + 1))
      (graftElevenReplacementComponent μ νR v0 h)
      (SquareRel (fullSim (graftLabRel Rv) (h + 1))) ≤ M)
    (hp : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hsmall : ζ ≤ c * (replacementMass (νR 7) (μ v0) (νR 5)) ^ α) :
    ζ * PhiDres α
        (graftXi true μ νL v0 (GraftCounter.ordinary 11) (h + 1))
        (graftXiBar false μ νR v0 (h + 1))
        (SquareRel (fullSim (graftLabRel Rv) (h + 1)))
      ≤ c * (1 + ENNReal.ofReal α * M) := by
  let R := SquareRel (fullSim (graftLabRel Rv) (h + 1))
  let ρs := graftXi true μ νL v0 (GraftCounter.ordinary 11) (h + 1)
  let ρrep := graftElevenReplacementComponent μ νR v0 h
  let ρt := graftXiBar false μ νR v0 (h + 1)
  have hfin : PhiD α ρs ρrep R ≠ ⊤ :=
    ne_top_of_le_ne_top hMtop hM
  have hsupp : ∀ x, ρs x ≠ 0 → rE ρrep R x ≠ 0 :=
    fun _ hx => rE_ne_zero_of_PhiD_ne_top hfin hx
  have hpT : replacementMass (νR 7) (μ v0) (νR 5) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (PMF.apply_ne_top νR 7)
        (PMF.apply_ne_top μ v0))
      (PMF.apply_ne_top νR 5)
  have hrow := rare_mul_PhiDres_le_of_replacement_component hα
    ρs ρrep ρt R hp hpT hsmall hsupp
    (elevenTagged_rE_minorization Rv μ νR v0 h)
  refine hrow.trans ?_
  gcongr
  exact (PhiDres_le_PhiD α ρs ρrep R).trans hM

/-- Complete reverse exceptional tagged Hall row. -/
theorem rare_thirteenTagged_PhiDres_le {V : Type} {α : ℝ} (hα : 1 ≤ α)
    (Rv : V → V → Prop) (μ : PMF V) (νL νR : PMF ℕ) (v0 : V)
    (h : ℕ) (M : ℝ≥0∞) {ζ c : ℝ≥0∞}
    (hMtop : M ≠ ⊤)
    (hM : PhiD α
      (graftXi false μ νR v0 (GraftCounter.ordinary 13) (h + 2))
      (graftThirteenReplacementComponent μ νL v0 h)
      (SquareRel (fullSim (graftLabRel Rv) (h + 2))) ≤ M)
    (hp : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (hsmall : ζ ≤ c * (replacementMass (νL 9) (μ v0) (νL 5)) ^ α) :
    ζ * PhiDres α
        (graftXi false μ νR v0 (GraftCounter.ordinary 13) (h + 2))
        (graftXiBar true μ νL v0 (h + 2))
        (SquareRel (fullSim (graftLabRel Rv) (h + 2)))
      ≤ c * (1 + ENNReal.ofReal α * M) := by
  let R := SquareRel (fullSim (graftLabRel Rv) (h + 2))
  let ρs := graftXi false μ νR v0 (GraftCounter.ordinary 13) (h + 2)
  let ρrep := graftThirteenReplacementComponent μ νL v0 h
  let ρt := graftXiBar true μ νL v0 (h + 2)
  have hfin : PhiD α ρs ρrep R ≠ ⊤ :=
    ne_top_of_le_ne_top hMtop hM
  have hsupp : ∀ x, ρs x ≠ 0 → rE ρrep R x ≠ 0 :=
    fun _ hx => rE_ne_zero_of_PhiD_ne_top hfin hx
  have hpT : replacementMass (νL 9) (μ v0) (νL 5) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (PMF.apply_ne_top νL 9)
        (PMF.apply_ne_top μ v0))
      (PMF.apply_ne_top νL 5)
  have hrow := rare_mul_PhiDres_le_of_replacement_component hα
    ρs ρrep ρt R hp hpT hsmall hsupp
    (thirteenTagged_rE_minorization Rv μ νL v0 h)
  refine hrow.trans ?_
  gcongr
  exact (PhiDres_le_PhiD α ρs ρrep R).trans hM

/-! ### Exceptional rows discharged from ordinary lower coordinates -/

theorem rare_elevenTagged_PhiDres_le_of_lower {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0)
    (h : ℕ) (M : ℝ≥0∞) {ζ c : ℝ≥0∞}
    (hMtop : M ≠ ⊤)
    (h2 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h5 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hp : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hsmall : ζ ≤ c * (replacementMass (νR 7) (μ v0) (νR 5)) ^ α) :
    ζ * PhiDres α
        (graftXi true μ νL v0 (GraftCounter.ordinary 11) (h + 1))
        (graftXiBar false μ νR v0 (h + 1))
        (SquareRel (fullSim (graftLabRel Rv) (h + 1)))
      ≤ c * (1 + ENNReal.ofReal α *
        graftDoubleBound α (graftDoubleBound α M)) := by
  exact rare_elevenTagged_PhiDres_le hα Rv μ νL νR v0 h
    (graftDoubleBound α (graftDoubleBound α M))
    (graftDoubleBound_ne_top (graftDoubleBound_ne_top hMtop))
    (PhiD_elevenReplacement_le hα Rv μ νL νR v0 hrefl h M h2 h5)
    hp hsmall

theorem rare_thirteenTagged_PhiDres_le_of_lower {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0)
    (h : ℕ) (M : ℝ≥0∞) {ζ c : ℝ≥0∞}
    (hMtop : M ≠ ⊤)
    (hF : PhiD α (graftTlaw false μ νR v0 h)
      (graftTlaw true μ νL v0 h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h2 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (h5 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hp : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (hsmall : ζ ≤ c * (replacementMass (νL 9) (μ v0) (νL 5)) ^ α) :
    ζ * PhiDres α
        (graftXi false μ νR v0 (GraftCounter.ordinary 13) (h + 2))
        (graftXiBar true μ νL v0 (h + 2))
        (SquareRel (fullSim (graftLabRel Rv) (h + 2)))
      ≤ c * (1 + ENNReal.ofReal α *
        graftDoubleBound α
          (graftDoubleBound α (graftDoubleBound α M))) := by
  exact rare_thirteenTagged_PhiDres_le hα Rv μ νL νR v0 h
    (graftDoubleBound α
      (graftDoubleBound α (graftDoubleBound α M)))
    (graftDoubleBound_ne_top
      (graftDoubleBound_ne_top (graftDoubleBound_ne_top hMtop)))
    (PhiD_thirteenReplacement_le hα Rv μ νL νR v0 hrefl h M hF h2 h5)
    hp hsmall

/-- The two exceptional orientations assembled in one literal tagged-process
statement.  A single smallness condition using the smaller replacement
cylinder pays both rows. -/
theorem rare_eleven_thirteenTagged_rows_of_lower {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0)
    (h : ℕ) (M : ℝ≥0∞) {ζ c : ℝ≥0∞}
    (hMtop : M ≠ ⊤)
    (hL2R2 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hL2R5 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hR2LF : PhiD α (graftTlaw false μ νR v0 h)
      (graftTlaw true μ νL v0 h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hR2L2 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hR2L5 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (hsmall : ζ ≤ c * min
      ((replacementMass (νR 7) (μ v0) (νR 5)) ^ α)
      ((replacementMass (νL 9) (μ v0) (νL 5)) ^ α)) :
    (ζ * PhiDres α
        (graftXi true μ νL v0 (GraftCounter.ordinary 11) (h + 1))
        (graftXiBar false μ νR v0 (h + 1))
        (SquareRel (fullSim (graftLabRel Rv) (h + 1)))
      ≤ c * (1 + ENNReal.ofReal α *
        graftDoubleBound α (graftDoubleBound α M))) ∧
    (ζ * PhiDres α
        (graftXi false μ νR v0 (GraftCounter.ordinary 13) (h + 2))
        (graftXiBar true μ νL v0 (h + 2))
        (SquareRel (fullSim (graftLabRel Rv) (h + 2)))
      ≤ c * (1 + ENNReal.ofReal α *
        graftDoubleBound α
          (graftDoubleBound α (graftDoubleBound α M)))) := by
  have hs11 : ζ ≤ c *
      (replacementMass (νR 7) (μ v0) (νR 5)) ^ α :=
    hsmall.trans (mul_le_mul_right
      (min_le_left
        ((replacementMass (νR 7) (μ v0) (νR 5)) ^ α)
        ((replacementMass (νL 9) (μ v0) (νL 5)) ^ α)) c)
  have hs13 : ζ ≤ c *
      (replacementMass (νL 9) (μ v0) (νL 5)) ^ α :=
    hsmall.trans (mul_le_mul_right
      (min_le_right
        ((replacementMass (νR 7) (μ v0) (νR 5)) ^ α)
        ((replacementMass (νL 9) (μ v0) (νL 5)) ^ α)) c)
  exact ⟨
    rare_elevenTagged_PhiDres_le_of_lower hα Rv μ νL νR v0 hrefl h M
      hMtop hL2R2 hL2R5 hp11 hs11,
    rare_thirteenTagged_PhiDres_le_of_lower hα Rv μ νL νR v0 hrefl h M
      hMtop hR2LF hR2L2 hR2L5 hp13 hs13⟩

/-! ### Exact law-level bookkeeping for the fixed example -/

/-- The four arities on which the two laws agree. -/
def elevenThirteenCommonCore : Finset ℕ := {3, 5, 7, 9}

/-- The precise offspring-law hypothesis for the fixed example.  The laws
agree pointwise on `{3,5,7,9}`, the left exceptional mass is `zeta` at 11,
the right exceptional mass is `zeta` at 13, and there is no other support. -/
def IsElevenThirteenLawPair (nuL nuR : PMF ℕ) (zeta : ℝ≥0∞) : Prop :=
  nuL 11 = zeta ∧
  nuR 13 = zeta ∧
  (∀ k ∈ elevenThirteenCommonCore, nuL k = nuR k) ∧
  (∀ k, (nuL k : ℝ≥0∞) ≠ 0 →
    k ∈ insert 11 elevenThirteenCommonCore) ∧
  (∀ k, (nuR k : ℝ≥0∞) ≠ 0 →
    k ∈ insert 13 elevenThirteenCommonCore)

lemma IsElevenThirteenLawPair.common_five {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta) : nuL 5 = nuR 5 := by
  exact hLaw.2.2.1 5 (by simp [elevenThirteenCommonCore])

lemma IsElevenThirteenLawPair.common_seven {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta) : nuL 7 = nuR 7 := by
  exact hLaw.2.2.1 7 (by simp [elevenThirteenCommonCore])

lemma IsElevenThirteenLawPair.common_nine {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta) : nuL 9 = nuR 9 := by
  exact hLaw.2.2.1 9 (by simp [elevenThirteenCommonCore])

/-- The combined exceptional rows stated with the actual source masses of
the fixed offspring laws.  This is the law-level version of
`rare_eleven_thirteenTagged_rows_of_lower`; `zeta` is no longer an unrelated
coefficient. -/
theorem rare_eleven_thirteenExample_rows_of_lower {V : Type} {α : ℝ}
    (hα : 1 ≤ α) (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (hrefl : Rv v0 v0)
    (h : ℕ) (M : ℝ≥0∞) {ζ c : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hMtop : M ≠ ⊤)
    (hL2R2 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hL2R5 : PhiD α
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hR2LF : PhiD α (graftTlaw false μ νR v0 h)
      (graftTlaw true μ νL v0 h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hR2L2 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 2) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 2) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hR2L5 : PhiD α
      (graftZlaw false μ νR v0 (GraftCounter.ordinary 5) h)
      (graftZlaw true μ νL v0 (GraftCounter.ordinary 5) h)
      (fullSim (graftLabRel Rv) h) ≤ M)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (hsmall : ζ ≤ c * min
      ((replacementMass (νR 7) (μ v0) (νR 5)) ^ α)
      ((replacementMass (νL 9) (μ v0) (νL 5)) ^ α)) :
    ((νL 11 : ℝ≥0∞) * PhiDres α
        (graftXi true μ νL v0 (GraftCounter.ordinary 11) (h + 1))
        (graftXiBar false μ νR v0 (h + 1))
        (SquareRel (fullSim (graftLabRel Rv) (h + 1)))
      ≤ c * (1 + ENNReal.ofReal α *
        graftDoubleBound α (graftDoubleBound α M))) ∧
    ((νR 13 : ℝ≥0∞) * PhiDres α
        (graftXi false μ νR v0 (GraftCounter.ordinary 13) (h + 2))
        (graftXiBar true μ νL v0 (h + 2))
        (SquareRel (fullSim (graftLabRel Rv) (h + 2)))
      ≤ c * (1 + ENNReal.ofReal α *
        graftDoubleBound α
          (graftDoubleBound α (graftDoubleBound α M)))) := by
  rw [hLaw.1, hLaw.2.1]
  exact rare_eleven_thirteenTagged_rows_of_lower hα Rv μ νL νR v0 hrefl
    h M hMtop hL2R2 hL2R5 hR2LF hR2L2 hR2L5 hp11 hp13 hsmall

end GraphMarkovMatching
