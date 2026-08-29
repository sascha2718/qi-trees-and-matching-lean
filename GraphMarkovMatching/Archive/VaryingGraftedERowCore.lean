/-
Semantic descent for the literal seven-symbol grafted grammar.

This file supplies the part of the one-step Hall row which cannot be
replaced by a matrix calculation: a target zero event at height `h+1`
forces the corresponding finite family of child-pair zero events at height
`h`.  For the fresh target we deliberately use only the four common
components.  Thus the result is an implication (which is what an upper Hall
bound needs), rather than the false equivalence which would discard the
exceptional 11/13 component.
-/
import GraphMarkovMatching.Archive.VaryingGraftedSupport
import GraphMarkovMatching.Process.Factorize

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {V : Type} (Rv : V → V → Prop) (μ : PMF V)
  (νL νR : PMF ℕ) (v0 : V)

/-! ### Exact five-component fresh support -/

/-- The side-specific exceptional offspring arity. -/
def graftRareArity : Bool → ℕ
  | true => 11
  | false => 13

/-- The two grammar children of the exceptional offspring component. -/
def graftRarePair : Bool → GraftTgt × GraftTgt
  | true => (.M3, .Z4)
  | false => (.Z4, .M5)

/-- The child pair attached to each of the five possible charged arities of
the fixed law on one side.  Values outside the fixed support are irrelevant. -/
def graftSupportedPair (left : Bool) (k : ℕ) : GraftTgt × GraftTgt :=
  if k = 3 then (.Z2, .F)
  else if k = 5 then (.Z2, .Z3)
  else if k = 7 then (.Z3, .Z4)
  else if k = 9 then (.Z4, .Z5)
  else graftRarePair left

/-- Every charged component allowed by the fixed 11/13 support is literally
the product law described by `graftSupportedPair`.  This is an equality of
the actual tagged laws, not merely a support or frontier calculation. -/
lemma graftXi_eq_prod_of_fixed_support (left : Bool) (ν : PMF ℕ) (h k : ℕ)
    (hk : k ∈ insert (graftRareArity left) elevenThirteenCommonCore) :
    graftXi left μ ν v0 (.ordinary k) h =
      prodPMF
        (graftInterp μ v0 left ν h (graftSupportedPair left k).1)
        (graftInterp μ v0 left ν h (graftSupportedPair left k).2) := by
  cases left with
  | false =>
      simp only [graftRareArity, elevenThirteenCommonCore,
        Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · simpa [graftSupportedPair, graftRarePair, graftInterp,
          graftTgtCounter] using graftXi_right_thirteen μ ν v0 h
      · simpa [graftSupportedPair, graftInterp, graftTgtCounter] using
          graftXi_ordinary_three false μ ν v0 h
      · simpa [graftSupportedPair, graftInterp, graftTgtCounter] using
          graftXi_ordinary_five false μ ν v0 h
      · simpa [graftSupportedPair] using
          graftXi_ordinary_seven μ v0 false ν h
      · simpa [graftSupportedPair] using
          graftXi_ordinary_nine μ v0 false ν h
  | true =>
      simp only [graftRareArity, elevenThirteenCommonCore,
        Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · simpa [graftSupportedPair, graftRarePair, graftInterp,
          graftTgtCounter] using graftXi_left_eleven μ ν v0 h
      · simpa [graftSupportedPair, graftInterp, graftTgtCounter] using
          graftXi_ordinary_three true μ ν v0 h
      · simpa [graftSupportedPair, graftInterp, graftTgtCounter] using
          graftXi_ordinary_five true μ ν v0 h
      · simpa [graftSupportedPair] using
          graftXi_ordinary_seven μ v0 true ν h
      · simpa [graftSupportedPair] using
          graftXi_ordinary_nine μ v0 true ν h

/-! ### Finite member-pair list -/

/-- The symbolic product components used to descend one target symbol. -/
def graftPairSymbols : GraftTgt → List (GraftTgt × GraftTgt)
  | .F =>
      [(.Z2, .F), (.Z2, .Z3), (.Z3, .Z4), (.Z4, .Z5)]
  | .Z2 => [(.F, .F)]
  | .Z3 => [(.Z2, .F)]
  | .Z4 => [(.Z2, .Z2)]
  | .Z5 => [(.Z2, .Z3)]
  | .M3 => [(.Z2, .Z5)]
  | .M5 => [(.Z2, .M3)]

/-- The four fresh pairs above are exactly the arity 3,5,7,9 child pairs.
In particular, the list excludes the rare 11/13 pair. -/
lemma graftPairSymbols_common (i : Fin 4) :
    graftCommonPair i ∈ graftPairSymbols .F := by
  fin_cases i <;> simp [graftCommonPair, graftPairSymbols]

lemma graftPairSymbols_mem {t : GraftTgt} {p : GraftTgt × GraftTgt}
    (hp : p ∈ graftPairSymbols t) :
    p.1 ∈ graftCommonSucc t ∧ p.2 ∈ graftCommonSucc t := by
  cases t <;>
    simp [graftPairSymbols, graftCommonSucc, graftCommonFreshSucc,
      graftForcedPair] at hp ⊢ <;>
    rcases hp with rfl | rfl | rfl | rfl <;> simp

lemma graftPairSymbols_cov {t u : GraftTgt} (hu : u ∈ graftCommonSucc t) :
    ∃ p ∈ graftPairSymbols t, u = p.1 ∨ u = p.2 := by
  cases t <;> cases u <;>
    simp_all [graftPairSymbols, graftCommonSucc, graftCommonFreshSucc,
      graftForcedPair]

/-- Interpretation of the symbolic member pairs as literal process laws.
A forced symbol contributes its unique child pair.  The fresh symbol
contributes the four common offspring components 3,5,7,9 and does not
pretend that the rare component has disappeared. -/
noncomputable def graftMemPairsOf (left : Bool) (ν : PMF ℕ) (h : ℕ)
    (t : GraftTgt) : List
      (PMF (FullLab (GraftState V) h) × PMF (FullLab (GraftState V) h)) :=
  (graftPairSymbols t).map fun p =>
    (graftInterp μ v0 left ν h p.1, graftInterp μ v0 left ν h p.2)

noncomputable def graftMemPairs (left : Bool) (ν : PMF ℕ) (h : ℕ)
    (z : Finset GraftTgt) : List
      (PMF (FullLab (GraftState V) h) × PMF (FullLab (GraftState V) h)) :=
  z.toList.flatMap (graftMemPairsOf μ v0 left ν h)

/-- Each coordinate of a selected member pair belongs to the interpreted
common successor list. -/
lemma graftMemPairs_mem (left : Bool) (ν : PMF ℕ) (h : ℕ)
    (z : Finset GraftTgt) :
    ∀ p ∈ graftMemPairs μ v0 left ν h z,
      p.1 ∈ (graftZSuccCommon z).toList.map (graftInterp μ v0 left ν h) ∧
      p.2 ∈ (graftZSuccCommon z).toList.map (graftInterp μ v0 left ν h) := by
  intro p hp
  obtain ⟨t, htz, hpt⟩ := List.mem_flatMap.mp hp
  obtain ⟨q, hqt, rfl⟩ := List.mem_map.mp hpt
  have htz' : t ∈ z := Finset.mem_toList.mp htz
  have hmem : ∀ u ∈ graftCommonSucc t,
      graftInterp μ v0 left ν h u ∈
        (graftZSuccCommon z).toList.map (graftInterp μ v0 left ν h) := by
    intro u hu
    exact List.mem_map.mpr ⟨u, Finset.mem_toList.mpr
      (Finset.mem_biUnion.mpr ⟨t, htz', hu⟩), rfl⟩
  exact ⟨hmem q.1 (graftPairSymbols_mem hqt).1,
    hmem q.2 (graftPairSymbols_mem hqt).2⟩

/-- Conversely, every interpreted common successor occurs in at least one
selected member pair.  This is the coverage premise of `hallFactorize`. -/
lemma graftMemPairs_cov (left : Bool) (ν : PMF ℕ) (h : ℕ)
    (z : Finset GraftTgt) :
    ∀ ρ ∈ (graftZSuccCommon z).toList.map (graftInterp μ v0 left ν h),
      ∃ p ∈ graftMemPairs μ v0 left ν h z, ρ = p.1 ∨ ρ = p.2 := by
  intro ρ hρ
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hρ
  obtain ⟨t, htz, hut⟩ :=
    Finset.mem_biUnion.mp (Finset.mem_toList.mp hu)
  have hflat : ∀ p ∈ graftMemPairsOf μ v0 left ν h t,
      p ∈ graftMemPairs μ v0 left ν h z := by
    intro p hp
    exact List.mem_flatMap.mpr ⟨t, Finset.mem_toList.mpr htz, hp⟩
  obtain ⟨q, hqt, huq⟩ := graftPairSymbols_cov hut
  let p := (graftInterp μ v0 left ν h q.1, graftInterp μ v0 left ν h q.2)
  refine ⟨p, hflat p ?_, ?_⟩
  · exact List.mem_map.mpr ⟨q, hqt, rfl⟩
  · rcases huq with huq | huq
    · exact Or.inl (congrArg (graftInterp μ v0 left ν h) huq)
    · exact Or.inr (congrArg (graftInterp μ v0 left ν h) huq)

/-! ### Literal root descent -/

lemma graftK_fst_irrel (left : Bool) (ν : PMF ℕ) (v w : V)
    (c : GraftCounter) :
    graftK left μ ν v0 (v, c) = graftK left μ ν v0 (w, c) := by
  cases c <;> simp [graftK]

lemma graftPairMix_ordinary (left : Bool) (ν : PMF ℕ) (v : V)
    (k h : ℕ) :
    pairMix (graftK left μ ν v0) (v, .ordinary k) h =
      graftXi left μ ν v0 (.ordinary k) h := by
  rw [graftXi, pairMix, pairMix, graftK_fst_irrel μ v0 left ν v v0]

lemma graftFreshQ_bind_eq {D : Type} (f : GraftState V → PMF D)
    (ν : PMF ℕ) :
    (graftFreshQ μ ν).bind f =
      ν.bind fun k => μ.bind fun v => f (v, .ordinary k) := by
  ext x
  rw [graftFreshQ, PMF.bind_map]
  exact freshQ_bind_eq μ ν (fun s => f (s.1, .ordinary s.2)) x

lemma graftTlaw_eq_bind (left : Bool) (ν : PMF ℕ) (h : ℕ) :
    graftTlaw left μ ν v0 h =
      ν.bind fun k => μ.bind fun v =>
        muM (graftK left μ ν v0) (v, .ordinary k) h := by
  rw [graftTlaw]
  exact graftFreshQ_bind_eq μ _ ν

/-- Exact source-mixture decomposition of a fresh grafted screen. -/
lemma graftFreshScreen_split (left : Bool) (ν : PMF ℕ) (h : ℕ)
    (R : FullLab (GraftState V) h → FullLab (GraftState V) h → Prop)
    (zs : List (PMF (FullLab (GraftState V) h)))
    (g : FullLab (GraftState V) h → ℝ≥0∞) :
    screenE (graftTlaw left μ ν v0 h) R zs g =
      ∑' k, (ν k : ℝ≥0∞) * ∑' v, (μ v : ℝ≥0∞) *
        screenE (muM (graftK left μ ν v0) (v, .ordinary k) h)
          R zs g := by
  rw [graftTlaw_eq_bind μ v0 left ν]
  rw [screenE_bind_left]
  refine tsum_congr fun k => ?_
  rw [screenE_bind_left]

/-- A fresh component at successor height, written at the child-pair level.
The child law is independent of the sampled root label `v`; the root label
is retained only in the attached branch. -/
lemma graftComponentScreen_branch (left : Bool) (ν : PMF ℕ)
    (v : V) (k h : ℕ)
    (R : FullLab (GraftState V) (h + 1) →
      FullLab (GraftState V) (h + 1) → Prop)
    (zs : List (PMF (FullLab (GraftState V) (h + 1))))
    (g : FullLab (GraftState V) (h + 1) → ℝ≥0∞) :
    screenE (muM (graftK left μ ν v0) (v, .ordinary k) (h + 1))
        R zs g =
      ∑' xp, graftXi left μ ν v0 (.ordinary k) h xp *
        (screenInd R zs (branch (v, .ordinary k) xp) *
          g (branch (v, .ordinary k) xp)) := by
  rw [screenE, muM_succ,
    graftPairMix_ordinary μ v0 left ν v k h]
  simpa only [mul_assoc] using
    (tsum_map_mul (graftXi left μ ν v0 (.ordinary k) h)
      (branch (v, .ordinary k))
      (fun x => screenInd R zs x * g x))

/-- Exact fresh-root good-degree factorization for the tagged kernel. -/
lemma rE_graftTlaw_succ_branch (left : Bool) (ν : PMF ℕ) (v : V)
    (c : GraftCounter) (h : ℕ)
    (xp : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    rE (graftTlaw left μ ν v0 (h + 1))
        (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp) =
      rE μ Rv v *
        rE (graftXiBar left μ ν v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
  rw [graftTlaw_eq_bind μ v0 left ν, rE_bind]
  have hcomponent : ∀ k,
      rE (μ.bind fun w =>
          muM (graftK left μ ν v0) (w, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp) =
        rE μ Rv v *
          rE (graftXi left μ ν v0 (.ordinary k) h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
    intro k
    rw [rE_bind]
    calc
      (∑' w, μ w *
          rE (muM (graftK left μ ν v0) (w, .ordinary k) (h + 1))
            (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp)) =
          ∑' w, (if Rv v w then μ w else 0) *
            rE (graftXi left μ ν v0 (.ordinary k) h)
              (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
        refine tsum_congr fun w => ?_
        rw [rE_succ_branch (graftK left μ ν v0) (graftLabRel Rv)
          (v, c) (w, .ordinary k) h xp,
          graftPairMix_ordinary μ v0 left ν w]
        by_cases hvw : Rv v w <;> simp [graftLabRel, hvw]
      _ = (∑' w, if Rv v w then μ w else 0) *
          rE (graftXi left μ ν v0 (.ordinary k) h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
        rw [ENNReal.tsum_mul_right]
      _ = rE μ Rv v *
          rE (graftXi left μ ν v0 (.ordinary k) h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp := rfl
  simp_rw [hcomponent]
  calc
    (∑' a, ν a * (rE μ Rv v *
        rE (graftXi left μ ν v0 (.ordinary a) h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp)) =
      ∑' a, rE μ Rv v * (ν a *
        rE (graftXi left μ ν v0 (.ordinary a) h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
        refine tsum_congr fun a => ?_
        ring
    _ = rE μ Rv v * ∑' a, ν a *
        rE (graftXi left μ ν v0 (.ordinary a) h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
      rw [ENNReal.tsum_mul_left]
    _ = rE μ Rv v *
        rE (graftXiBar left μ ν v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
      rw [graftXiBar, rE_bind]

/-- Restricted inverse normalization passes exactly through a compatible
deterministic tagged root. -/
lemma WresD_graftInterp_forced_succ_branch (α : ℝ) (left : Bool)
    (ν : PMF ℕ) (v : V) (cs : GraftCounter) (h : ℕ)
    {t : GraftTgt} {ct : GraftCounter}
    (ht : graftTgtCounter t = some ct)
    (xp : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    WresD α (graftInterp μ v0 left ν (h + 1) t)
        (fullSim (graftLabRel Rv) (h + 1)) (branch (v, cs) xp) =
      if Rv v v0 then
        WresD α (graftChildren μ v0 left ν h t)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp
      else 0 := by
  rw [graftInterp_forced_succ μ v0 left ν h ht,
    WresD_map_branch_law]
  by_cases hv : Rv v v0 <;> simp [graftLabRel, hv]

/-- Fresh tagged normalization factors into the root inverse degree and the
child-mixture inverse degree. -/
lemma WresD_graftTlaw_succ_branch (α : ℝ) (left : Bool) (ν : PMF ℕ)
    (v : V) (hvpos : rE μ Rv v ≠ 0) (cs : GraftCounter) (h : ℕ)
    (xp : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    WresD α (graftTlaw left μ ν v0 (h + 1))
        (fullSim (graftLabRel Rv) (h + 1)) (branch (v, cs) xp) =
      (rE μ Rv v) ^ (-α) *
        WresD α (graftXiBar left μ ν v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
  have hroot := rE_graftTlaw_succ_branch Rv μ v0 left ν v cs h xp
  by_cases hbar : rE (graftXiBar left μ ν v0 h)
      (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
  · have hz : rE (graftTlaw left μ ν v0 (h + 1))
        (fullSim (graftLabRel Rv) (h + 1)) (branch (v, cs) xp) = 0 := by
      rw [hroot, hbar, mul_zero]
    rw [WresD, if_pos hz, WresD, if_pos hbar, mul_zero]
  · have hbr : rE (graftTlaw left μ ν v0 (h + 1))
        (fullSim (graftLabRel Rv) (h + 1)) (branch (v, cs) xp) ≠ 0 := by
      rw [hroot]
      exact mul_ne_zero hvpos hbar
    rw [← rE_rpow_neg_eq_WresD (graftTlaw left μ ν v0 (h + 1))
        (fullSim (graftLabRel Rv) (h + 1)) (branch (v, cs) xp) hbr,
      ← rE_rpow_neg_eq_WresD (graftXiBar left μ ν v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) xp hbar,
      hroot, ENNReal.mul_rpow_of_ne_zero hvpos hbar (-α)]

/-- Pointwise mixture-tilt conversion for the literal tagged child mixture.
The fresh inverse degree is bounded by the sum of the inverse degrees of its
charged offspring components, with the exact factors `ν(k)⁻ᵅ`. -/
lemma WresD_graftXiBar_le_sum (α : ℝ) (hα0 : 0 ≤ α)
    (left : Bool) (ν : PMF ℕ) (h : ℕ)
    (xp : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    WresD α (graftXiBar left μ ν v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) xp ≤
      ∑' k, (if (ν k : ℝ≥0∞) = 0 then 0 else
        (ν k : ℝ≥0∞) ^ (-α) *
          WresD α (graftXi left μ ν v0 (.ordinary k) h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
  by_cases hbar : rE (graftXiBar left μ ν v0 h)
      (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
  · rw [WresD, if_pos hbar]
    exact zero_le
  · have hnall : ¬ ∀ k, (ν k : ℝ≥0∞) = 0 ∨
        rE (graftXi left μ ν v0 (.ordinary k) h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0 := by
      intro hall
      apply hbar
      rw [graftXiBar]
      exact (rE_bind_eq_zero_iff ν
        (fun k => graftXi left μ ν v0 (.ordinary k) h)
        (SquareRel (fullSim (graftLabRel Rv) h)) xp).mpr hall
    push Not at hnall
    obtain ⟨k, hν, hXi⟩ := hnall
    have hmin : (ν k : ℝ≥0∞) *
        rE (graftXi left μ ν v0 (.ordinary k) h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp ≤
        rE (graftXiBar left μ ν v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
      rw [graftXiBar]
      exact mul_rE_le_rE_bind ν
        (fun j => graftXi left μ ν v0 (.ordinary j) h)
        (SquareRel (fullSim (graftLabRel Rv) h)) xp k
    have hstep : WresD α (graftXiBar left μ ν v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp ≤
        (ν k : ℝ≥0∞) ^ (-α) *
          WresD α (graftXi left μ ν v0 (.ordinary k) h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
      rw [← rE_rpow_neg_eq_WresD (graftXiBar left μ ν v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp hbar,
        ← rE_rpow_neg_eq_WresD
          (graftXi left μ ν v0 (.ordinary k) h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp hXi,
        ← ENNReal.mul_rpow_of_ne_zero hν hXi (-α)]
      exact rpow_neg_antitone hα0 hmin
    refine hstep.trans ?_
    refine (le_of_eq ?_).trans (ENNReal.le_tsum k)
    rw [if_neg hν]

/-- A dead target at a compatible root forces all selected common child
pairs to be dead.  Fresh targets require positivity only of the four common
weights; no condition is imposed on the exceptional weight. -/
lemma graftTarget_dead_implies_pair_dead (left : Bool) (ν : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (ν (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    {v : V} (hv0 : Rv v v0) (hvpos : rE μ Rv v ≠ 0)
    (c : GraftCounter) (h : ℕ) (t : GraftTgt)
    (xp : FullLab (GraftState V) h × FullLab (GraftState V) h)
    (hdead : rE (graftInterp μ v0 left ν (h + 1) t)
      (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp) = 0) :
    ∀ p ∈ graftMemPairsOf μ v0 left ν h t,
      rE (prodPMF p.1 p.2)
        (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0 := by
  have hv0' : graftLabRel Rv (v, c) (v0, c) := hv0
  cases t with
  | F =>
      have hroot := rE_graftTlaw_succ_branch Rv μ v0 left ν v c h xp
      rw [graftInterp_F] at hdead
      rw [hroot] at hdead
      have hbar : rE (graftXiBar left μ ν v0 h)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0 :=
        (mul_eq_zero.mp hdead).resolve_left hvpos
      have hall := (rE_bind_eq_zero_iff ν
        (fun k => graftXi left μ ν v0 (.ordinary k) h)
        (SquareRel (fullSim (graftLabRel Rv) h)) xp).mp hbar
      have hi : ∀ i : Fin 4,
          rE (prodPMF
              (graftInterp μ v0 left ν h (graftCommonPair i).1)
              (graftInterp μ v0 left ν h (graftCommonPair i).2))
            (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0 := by
        intro i
        have hxi := (hall (graftCommonArity i)).resolve_left (hcommon i)
        rw [graftXi_common_eq_prod μ v0 left ν h i] at hxi
        exact hxi
      intro p hp
      simp only [graftMemPairsOf, graftPairSymbols, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · simpa [graftCommonPair] using hi (0 : Fin 4)
      · simpa [graftCommonPair] using hi (1 : Fin 4)
      · simpa [graftCommonPair] using hi (2 : Fin 4)
      · simpa [graftCommonPair] using hi (3 : Fin 4)
  | Z2 =>
      rw [graftInterp_forced_succ μ v0 left ν h (t := .Z2) (c := .ordinary 2) rfl,
        rE_map_branch_law, if_pos (by simpa [graftLabRel] using hv0)] at hdead
      rw [graftChildren_forced_eq_prod μ v0 left ν h
        (t := .Z2) (a := .F) (b := .F) rfl] at hdead
      simpa [graftMemPairsOf, graftPairSymbols] using hdead
  | Z3 =>
      rw [graftInterp_forced_succ μ v0 left ν h (t := .Z3) (c := .ordinary 3) rfl,
        rE_map_branch_law, if_pos (by simpa [graftLabRel] using hv0)] at hdead
      rw [graftChildren_forced_eq_prod μ v0 left ν h
        (t := .Z3) (a := .Z2) (b := .F) rfl] at hdead
      simpa [graftMemPairsOf, graftPairSymbols] using hdead
  | Z4 =>
      rw [graftInterp_forced_succ μ v0 left ν h (t := .Z4) (c := .ordinary 4) rfl,
        rE_map_branch_law, if_pos (by simpa [graftLabRel] using hv0)] at hdead
      rw [graftChildren_forced_eq_prod μ v0 left ν h
        (t := .Z4) (a := .Z2) (b := .Z2) rfl] at hdead
      simpa [graftMemPairsOf, graftPairSymbols] using hdead
  | Z5 =>
      rw [graftInterp_forced_succ μ v0 left ν h (t := .Z5) (c := .ordinary 5) rfl,
        rE_map_branch_law, if_pos (by simpa [graftLabRel] using hv0)] at hdead
      rw [graftChildren_forced_eq_prod μ v0 left ν h
        (t := .Z5) (a := .Z2) (b := .Z3) rfl] at hdead
      simpa [graftMemPairsOf, graftPairSymbols] using hdead
  | M3 =>
      rw [graftInterp_forced_succ μ v0 left ν h (t := .M3) (c := .force3Five) rfl,
        rE_map_branch_law, if_pos (by simpa [graftLabRel] using hv0)] at hdead
      rw [graftChildren_forced_eq_prod μ v0 left ν h
        (t := .M3) (a := .Z2) (b := .Z5) rfl] at hdead
      simpa [graftMemPairsOf, graftPairSymbols] using hdead
  | M5 =>
      rw [graftInterp_forced_succ μ v0 left ν h (t := .M5) (c := .force5Five) rfl,
        rE_map_branch_law, if_pos (by simpa [graftLabRel] using hv0)] at hdead
      rw [graftChildren_forced_eq_prod μ v0 left ν h
        (t := .M5) (a := .Z2) (b := .M3) rfl] at hdead
      simpa [graftMemPairsOf, graftPairSymbols] using hdead

/-- Zero descent for an entire finite target list. -/
theorem graftMemInd_branch (left : Bool) (ν : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (ν (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    {v : V} (hv0 : Rv v v0) (hvpos : rE μ Rv v ≠ 0)
    (c : GraftCounter) (h : ℕ) (z : Finset GraftTgt)
    (xp : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    (∀ ρ ∈ z.toList.map (graftInterp μ v0 left ν (h + 1)),
        rE ρ (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp) = 0) →
      ∀ p ∈ graftMemPairs μ v0 left ν h z,
        rE (prodPMF p.1 p.2)
          (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0 := by
  intro hall p hp
  obtain ⟨t, htz, hpt⟩ := List.mem_flatMap.mp hp
  exact graftTarget_dead_implies_pair_dead Rv μ v0 left ν hcommon hv0 hvpos
    c h t xp (hall _ (List.mem_map.mpr ⟨t, htz, rfl⟩)) p hpt

/-! ### The first actual semantic Hall row -/

/-- Root-compatible form of the screen-indicator descent.  This is the form
used for a sampled fresh source root. -/
private lemma graftScreenInd_le_memberInd_near (leftTarget : Bool)
    (νt : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    {v : V} (hv0 : Rv v v0) (hvpos : rE μ Rv v ≠ 0)
    (c : GraftCounter) (h : ℕ) (z : Finset GraftTgt)
    (xp : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    screenInd (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (branch (v, c) xp) ≤
      if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
          rE (prodPMF p.1 p.2)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
        then 1 else 0 := by
  rw [screenInd]
  by_cases hzdead : ∀ ρ ∈
      z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)),
      rE ρ (fullSim (graftLabRel Rv) (h + 1)) (branch (v, c) xp) = 0
  · rw [if_pos hzdead, if_pos]
    exact graftMemInd_branch Rv μ v0 leftTarget νt hcommon hv0 hvpos
      c h z xp hzdead
  · rw [if_neg hzdead]
    exact zero_le

private lemma graftScreenInd_le_memberInd (leftTarget : Bool) (νt : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl0 : Rv v0 v0) (hμ0 : (μ v0 : ℝ≥0∞) ≠ 0)
    (c : GraftCounter) (h : ℕ) (z : Finset GraftTgt)
    (xp : FullLab (GraftState V) h × FullLab (GraftState V) h) :
    screenInd (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (branch (v0, c) xp) ≤
      if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
          rE (prodPMF p.1 p.2)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
        then 1 else 0 := by
  have hvpos : rE μ Rv v0 ≠ 0 := by
    intro hr
    exact hμ0 (le_antisymm (hr ▸ le_rE_of_refl hrefl0) zero_le)
  exact graftScreenInd_le_memberInd_near Rv μ v0 leftTarget νt hcommon
    hrefl0 hvpos c h z xp

/-- Integrate a pointwise countable bound after a change of variables through
a mapped source law.  Only values on the image of the map are required. -/
private lemma screenE_map_tsum_tilt_le {A X I : Type} (ρ : PMF A)
    (m : A → X) (R : X → X → Prop) (zs : List (PMF X))
    (g : X → ℝ≥0∞) (c : I → ℝ≥0∞) (f : I → X → ℝ≥0∞)
    (hg : ∀ a, g (m a) ≤ ∑' i, c i * f i (m a)) :
    screenE (ρ.map m) R zs g ≤
      ∑' i, c i * screenE (ρ.map m) R zs (f i) := by
  rw [screenE]
  have hmapg :
      (∑' x, (ρ.map m) x * screenInd R zs x * g x) =
        ∑' a, ρ a * (screenInd R zs (m a) * g (m a)) := by
    simpa only [mul_assoc] using
      (tsum_map_mul ρ m (fun x => screenInd R zs x * g x))
  rw [hmapg]
  calc
    (∑' a, ρ a * (screenInd R zs (m a) * g (m a))) ≤
        ∑' a, ρ a *
          (screenInd R zs (m a) * (∑' i, c i * f i (m a))) := by
      refine ENNReal.tsum_le_tsum fun a => ?_
      exact mul_le_mul_right (mul_le_mul_right (hg a) _) _
    _ = ∑' a, ∑' i,
          c i * (ρ a * (screenInd R zs (m a) * f i (m a))) := by
      refine tsum_congr fun a => ?_
      calc
        ρ a * (screenInd R zs (m a) * ∑' i, c i * f i (m a)) =
            (ρ a * screenInd R zs (m a)) * ∑' i, c i * f i (m a) := by
          ring
        _ = ∑' i, (ρ a * screenInd R zs (m a)) *
              (c i * f i (m a)) := ENNReal.tsum_mul_left.symm
        _ = ∑' i, c i *
              (ρ a * (screenInd R zs (m a) * f i (m a))) := by
          refine tsum_congr fun i => by ring
    _ = ∑' i, ∑' a,
          c i * (ρ a * (screenInd R zs (m a) * f i (m a))) :=
      ENNReal.tsum_comm
    _ = ∑' i, c i * screenE (ρ.map m) R zs (f i) := by
      refine tsum_congr fun i => ?_
      rw [screenE, ENNReal.tsum_mul_left]
      congr 1
      simpa only [mul_assoc] using
        (tsum_map_mul ρ m (fun x => screenInd R zs x * f i x)).symm

/-- **Forced-source, unit-normalization Hall row for the literal grafted
laws.**  This theorem starts from the actual height-`h+1` interpreted laws,
uses `graftMemInd_branch`, and ends at the exact common successor screens.
It is therefore the semantic row which the earlier abstract matrix estimate
did not itself provide. -/
theorem graftForcedScreen_none_le_hall
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl0 : Rv v0 v0) (hμ0 : (μ v0 : ℝ≥0∞) ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) {t a b : GraftTgt}
    {c : GraftCounter} (htc : graftTgtCounter t = some c)
    (htp : graftForcedPair t = some (a, b)) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) t)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (fun _ => (1 : ℝ≥0∞)) ≤
      screenE (graftInterp μ v0 leftSource νs h a)
          (fullSim (graftLabRel Rv) h)
          ((graftZSuccCommon z).toList.map
            (graftInterp μ v0 leftTarget νt h)) (fun _ => 1)
        + screenE (graftInterp μ v0 leftSource νs h b)
          (fullSim (graftLabRel Rv) h)
          ((graftZSuccCommon z).toList.map
            (graftInterp μ v0 leftTarget νt h)) (fun _ => 1)
        + (((graftZSuccCommon z).toList.map
              (graftInterp μ v0 leftTarget νt h)).map fun ρ =>
              screenE (graftInterp μ v0 leftSource νs h a)
                (fullSim (graftLabRel Rv) h) [ρ] (fun _ => 1)).sum
          * (((graftZSuccCommon z).toList.map
              (graftInterp μ v0 leftTarget νt h)).map fun ρ =>
              screenE (graftInterp μ v0 leftSource νs h b)
                (fullSim (graftLabRel Rv) h) [ρ] (fun _ => 1)).sum := by
  rw [graftInterp_forced_succ μ v0 leftSource νs h htc,
    graftChildren_forced_eq_prod μ v0 leftSource νs h htp]
  rw [screenE]
  calc
    (∑' x, ((prodPMF (graftInterp μ v0 leftSource νs h a)
        (graftInterp μ v0 leftSource νs h b)).map
          (branch (v0, c))) x *
        screenInd (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) x * 1) =
      ∑' xp, prodPMF (graftInterp μ v0 leftSource νs h a)
          (graftInterp μ v0 leftSource νs h b) xp *
        screenInd (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (branch (v0, c) xp) * 1 := by
        simpa only [mul_assoc] using
          (tsum_map_mul
            (prodPMF (graftInterp μ v0 leftSource νs h a)
              (graftInterp μ v0 leftSource νs h b))
            (branch (v0, c))
            (fun x => screenInd (fullSim (graftLabRel Rv) (h + 1))
              (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) x * 1))
    _ ≤ ∑' xp, prodPMF (graftInterp μ v0 leftSource νs h a)
          (graftInterp μ v0 leftSource νs h b) xp *
        ((if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
              rE (prodPMF p.1 p.2)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
            then (1 : ℝ≥0∞) else 0) * (1 * 1)) := by
      refine ENNReal.tsum_le_tsum fun xp => ?_
      simpa only [mul_one] using mul_le_mul_right
        (graftScreenInd_le_memberInd Rv μ v0 leftTarget νt hcommon
          hrefl0 hμ0 c h z xp)
        (prodPMF (graftInterp μ v0 leftSource νs h a)
          (graftInterp μ v0 leftSource νs h b) xp)
    _ ≤ _ := by
      have hhall := hallFactorize
        (graftInterp μ v0 leftSource νs h a)
        (graftInterp μ v0 leftSource νs h b)
        (fullSim (graftLabRel Rv) h)
        (graftMemPairs μ v0 leftTarget νt h z)
        ((graftZSuccCommon z).toList.map
          (graftInterp μ v0 leftTarget νt h))
        (graftMemPairs_mem μ v0 leftTarget νt h z)
        (graftMemPairs_cov μ v0 leftTarget νt h z)
        (fun _ => (1 : ℝ≥0∞)) (fun _ => (1 : ℝ≥0∞))
      simpa only [mul_one,
        (graftInterp μ v0 leftSource νs h a).tsum_coe,
        (graftInterp μ v0 leftSource νs h b).tsum_coe,
        one_mul] using hhall

/-- The exact right side produced by one application of the multi-member
Hall factorization. -/
noncomputable def graftHallRHS (leftSource leftTarget : Bool)
    (νs νt : PMF ℕ) (h : ℕ) (z : Finset GraftTgt) (a b : GraftTgt)
    (G₀ G₁ : FullLab (GraftState V) h → ℝ≥0∞) : ℝ≥0∞ :=
  screenE (graftInterp μ v0 leftSource νs h a)
      (fullSim (graftLabRel Rv) h)
      ((graftZSuccCommon z).toList.map
        (graftInterp μ v0 leftTarget νt h)) G₀
    * (∑' x, graftInterp μ v0 leftSource νs h b x * G₁ x)
  + (∑' x, graftInterp μ v0 leftSource νs h a x * G₀ x)
    * screenE (graftInterp μ v0 leftSource νs h b)
      (fullSim (graftLabRel Rv) h)
      ((graftZSuccCommon z).toList.map
        (graftInterp μ v0 leftTarget νt h)) G₁
  + (((graftZSuccCommon z).toList.map
        (graftInterp μ v0 leftTarget νt h)).map fun ρ =>
        screenE (graftInterp μ v0 leftSource νs h a)
          (fullSim (graftLabRel Rv) h) [ρ] G₀).sum
    * (((graftZSuccCommon z).toList.map
        (graftInterp μ v0 leftTarget νt h)).map fun ρ =>
        screenE (graftInterp μ v0 leftSource νs h b)
          (fullSim (graftLabRel Rv) h) [ρ] G₁).sum

private lemma graftListSum_le_length_mul (xs : List ℝ≥0∞) (E : ℝ≥0∞)
    (hxs : ∀ x ∈ xs, x ≤ E) : xs.sum ≤ (xs.length : ℝ≥0∞) * E := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ E := hxs x (by simp)
      have htail : ∀ y ∈ xs, y ≤ E := by
        intro y hy
        exact hxs y (by simp [hy])
      calc
        (x :: xs).sum = x + xs.sum := by simp
        _ ≤ E + (xs.length : ℝ≥0∞) * E := add_le_add hx (ih htail)
        _ = ((x :: xs).length : ℝ≥0∞) * E := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Quantitative envelope of one literal Hall factorization output.  If the
two full-list screens are at most `E`, the two inverse moments are at most
`L`, and every singleton screen in the successor list is at most `E`, then
the Hall output has exactly the familiar two linear terms plus the squared
finite-list term. -/
theorem graftHallRHS_le_uniform (leftSource leftTarget : Bool)
    (νs νt : PMF ℕ) (h : ℕ) (z : Finset GraftTgt) (a b : GraftTgt)
    (G₀ G₁ : FullLab (GraftState V) h → ℝ≥0∞) (L E : ℝ≥0∞)
    (hScr0 : screenE (graftInterp μ v0 leftSource νs h a)
      (fullSim (graftLabRel Rv) h)
      ((graftZSuccCommon z).toList.map
        (graftInterp μ v0 leftTarget νt h)) G₀ ≤ E)
    (hScr1 : screenE (graftInterp μ v0 leftSource νs h b)
      (fullSim (graftLabRel Rv) h)
      ((graftZSuccCommon z).toList.map
        (graftInterp μ v0 leftTarget νt h)) G₁ ≤ E)
    (hMom0 : (∑' x, graftInterp μ v0 leftSource νs h a x * G₀ x) ≤ L)
    (hMom1 : (∑' x, graftInterp μ v0 leftSource νs h b x * G₁ x) ≤ L)
    (hSing0 : ∀ u ∈ graftZSuccCommon z,
      screenE (graftInterp μ v0 leftSource νs h a)
        (fullSim (graftLabRel Rv) h)
        [graftInterp μ v0 leftTarget νt h u] G₀ ≤ E)
    (hSing1 : ∀ u ∈ graftZSuccCommon z,
      screenE (graftInterp μ v0 leftSource νs h b)
        (fullSim (graftLabRel Rv) h)
        [graftInterp μ v0 leftTarget νt h u] G₁ ≤ E) :
    graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b G₀ G₁ ≤
      E * L + L * E +
        (((graftZSuccCommon z).card : ℝ≥0∞) * E) *
          (((graftZSuccCommon z).card : ℝ≥0∞) * E) := by
  let us := (graftZSuccCommon z).toList
  let ρs := us.map (graftInterp μ v0 leftTarget νt h)
  have hsum0 :
      (ρs.map fun ρ => screenE (graftInterp μ v0 leftSource νs h a)
        (fullSim (graftLabRel Rv) h) [ρ] G₀).sum ≤
        ((graftZSuccCommon z).card : ℝ≥0∞) * E := by
    refine (graftListSum_le_length_mul _ E ?_).trans_eq ?_
    · intro x hx
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hρ
      exact hSing0 u (Finset.mem_toList.mp hu)
    · simp [ρs, us]
  have hsum1 :
      (ρs.map fun ρ => screenE (graftInterp μ v0 leftSource νs h b)
        (fullSim (graftLabRel Rv) h) [ρ] G₁).sum ≤
        ((graftZSuccCommon z).card : ℝ≥0∞) * E := by
    refine (graftListSum_le_length_mul _ E ?_).trans_eq ?_
    · intro x hx
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hρ
      exact hSing1 u (Finset.mem_toList.mp hu)
    · simp [ρs, us]
  dsimp [graftHallRHS]
  exact add_le_add (add_le_add (mul_le_mul' hScr0 hMom1)
    (mul_le_mul' hMom0 hScr1)) (mul_le_mul' hsum0 hsum1)

/-- The exact root-and-component inverse price in a fresh normalization. -/
noncomputable def graftFreshTiltCoeff (α : ℝ) (ν : PMF ℕ) (k : ℕ) : ℝ≥0∞ :=
  if (ν k : ℝ≥0∞) = 0 then 0
  else (rE μ Rv v0) ^ (-α) * (ν k : ℝ≥0∞) ^ (-α)

/-- Root-dependent version of the fresh normalization price, used before
integrating a sampled fresh source label. -/
noncomputable def graftRootFreshTiltCoeff (α : ℝ) (ν : PMF ℕ)
    (v : V) (k : ℕ) : ℝ≥0∞ :=
  if (ν k : ℝ≥0∞) = 0 then 0
  else (rE μ Rv v) ^ (-α) * (ν k : ℝ≥0∞) ^ (-α)

/-- Straight plus crossed child inverse tilts, lifted to a successor-height
tree.  The root coordinate is deliberately ignored. -/
noncomputable def graftPairTiltLift (α : ℝ) (left : Bool) (ν : PMF ℕ)
    (h k : ℕ) (x : FullLab (GraftState V) (h + 1)) : ℝ≥0∞ :=
  let p := graftSupportedPair left k
  let W₀ := WresD α (graftInterp μ v0 left ν h p.1)
    (fullSim (graftLabRel Rv) h)
  let W₁ := WresD α (graftInterp μ v0 left ν h p.2)
    (fullSim (graftLabRel Rv) h)
  W₀ x.2.1 * W₁ x.2.2 + W₁ x.2.1 * W₀ x.2.2

/-- The two Hall-factorization outputs attached to one charged fresh
normalization component. -/
noncomputable def graftFreshHallTerm (α : ℝ)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (h : ℕ) (z : Finset GraftTgt) (a b : GraftTgt) (k : ℕ) : ℝ≥0∞ :=
  let p := graftSupportedPair leftTarget k
  let W₀ := WresD α (graftInterp μ v0 leftTarget νt h p.1)
    (fullSim (graftLabRel Rv) h)
  let W₁ := WresD α (graftInterp μ v0 leftTarget νt h p.2)
    (fullSim (graftLabRel Rv) h)
  graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b W₀ W₁ +
    graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b W₁ W₀

/-- Hall output for one fresh-source arity against a deterministic target
normalization with child pair `(d,e)`. -/
noncomputable def graftSourceForcedHallTerm (α : ℝ)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (h : ℕ) (z : Finset GraftTgt) (k : ℕ) (d e : GraftTgt) : ℝ≥0∞ :=
  let p := graftSupportedPair leftSource k
  let W₀ := WresD α (graftInterp μ v0 leftTarget νt h d)
    (fullSim (graftLabRel Rv) h)
  let W₁ := WresD α (graftInterp μ v0 leftTarget νt h e)
    (fullSim (graftLabRel Rv) h)
  graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z p.1 p.2 W₀ W₁ +
    graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z p.1 p.2 W₁ W₀

/-- General forced-source Hall workhorse.  Any normalization whose value at
the branch point is bounded by a product `G₀⊗G₁` is routed through the
literal common successor screens with exactly `graftHallRHS`. -/
theorem graftForcedScreen_le_hall_of_norm
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl0 : Rv v0 v0) (hμ0 : (μ v0 : ℝ≥0∞) ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) {t a b : GraftTgt}
    {c : GraftCounter} (htc : graftTgtCounter t = some c)
    (htp : graftForcedPair t = some (a, b))
    (g : FullLab (GraftState V) (h + 1) → ℝ≥0∞)
    (G₀ G₁ : FullLab (GraftState V) h → ℝ≥0∞)
    (hnorm : ∀ xp, g (branch (v0, c) xp) ≤ G₀ xp.1 * G₁ xp.2) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) t)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) g ≤
      graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b G₀ G₁ := by
  rw [graftInterp_forced_succ μ v0 leftSource νs h htc,
    graftChildren_forced_eq_prod μ v0 leftSource νs h htp,
    screenE]
  calc
    (∑' x, ((prodPMF (graftInterp μ v0 leftSource νs h a)
        (graftInterp μ v0 leftSource νs h b)).map
          (branch (v0, c))) x *
        screenInd (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) x * g x) =
      ∑' xp, prodPMF (graftInterp μ v0 leftSource νs h a)
          (graftInterp μ v0 leftSource νs h b) xp *
        screenInd (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (branch (v0, c) xp) * g (branch (v0, c) xp) := by
        simpa only [mul_assoc] using
          (tsum_map_mul
            (prodPMF (graftInterp μ v0 leftSource νs h a)
              (graftInterp μ v0 leftSource νs h b))
            (branch (v0, c))
            (fun x => screenInd (fullSim (graftLabRel Rv) (h + 1))
              (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) x * g x))
    _ ≤ ∑' xp, prodPMF (graftInterp μ v0 leftSource νs h a)
          (graftInterp μ v0 leftSource νs h b) xp *
        ((if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
              rE (prodPMF p.1 p.2)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
            then (1 : ℝ≥0∞) else 0) * (G₀ xp.1 * G₁ xp.2)) := by
      refine ENNReal.tsum_le_tsum fun xp => ?_
      simpa only [mul_assoc] using
        (mul_le_mul_right
          (mul_le_mul'
            (graftScreenInd_le_memberInd Rv μ v0 leftTarget νt hcommon
              hrefl0 hμ0 c h z xp) (hnorm xp))
          (prodPMF (graftInterp μ v0 leftSource νs h a)
            (graftInterp μ v0 leftSource νs h b) xp))
    _ ≤ _ := by
      exact hallFactorize
        (graftInterp μ v0 leftSource νs h a)
        (graftInterp μ v0 leftSource νs h b)
        (fullSim (graftLabRel Rv) h)
        (graftMemPairs μ v0 leftTarget νt h z)
        ((graftZSuccCommon z).toList.map
          (graftInterp μ v0 leftTarget νt h))
        (graftMemPairs_mem μ v0 leftTarget νt h z)
        (graftMemPairs_cov μ v0 leftTarget νt h z) G₀ G₁

/-- Two-product version of the forced Hall workhorse.  This is the exact
shape produced by the straight/crossed inverse-degree split. -/
theorem graftForcedScreen_le_two_hall_of_norm
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl0 : Rv v0 v0) (hμ0 : (μ v0 : ℝ≥0∞) ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) {t a b : GraftTgt}
    {c : GraftCounter} (htc : graftTgtCounter t = some c)
    (htp : graftForcedPair t = some (a, b))
    (g : FullLab (GraftState V) (h + 1) → ℝ≥0∞)
    (G₀ G₁ H₀ H₁ : FullLab (GraftState V) h → ℝ≥0∞)
    (hnorm : ∀ xp, g (branch (v0, c) xp) ≤
      G₀ xp.1 * G₁ xp.2 + H₀ xp.1 * H₁ xp.2) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) t)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) g ≤
      graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b G₀ G₁ +
      graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b H₀ H₁ := by
  rw [graftInterp_forced_succ μ v0 leftSource νs h htc,
    graftChildren_forced_eq_prod μ v0 leftSource νs h htp,
    screenE]
  let ρa := graftInterp μ v0 leftSource νs h a
  let ρb := graftInterp μ v0 leftSource νs h b
  let I : FullLab (GraftState V) h × FullLab (GraftState V) h → ℝ≥0∞ :=
    fun xp => if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
      rE (prodPMF p.1 p.2) (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
      then 1 else 0
  have hmap :
      (∑' x, ((prodPMF ρa ρb).map (branch (v0, c))) x *
          screenInd (fullSim (graftLabRel Rv) (h + 1))
            (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) x * g x) =
        ∑' xp, prodPMF ρa ρb xp *
          screenInd (fullSim (graftLabRel Rv) (h + 1))
            (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
            (branch (v0, c) xp) * g (branch (v0, c) xp) := by
    simpa only [mul_assoc] using
      (tsum_map_mul (prodPMF ρa ρb) (branch (v0, c))
        (fun x => screenInd (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) x * g x))
  rw [hmap]
  calc
    (∑' xp, prodPMF ρa ρb xp *
        screenInd (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (branch (v0, c) xp) * g (branch (v0, c) xp)) ≤
      ∑' xp, (prodPMF ρa ρb xp * (I xp * (G₀ xp.1 * G₁ xp.2)) +
        prodPMF ρa ρb xp * (I xp * (H₀ xp.1 * H₁ xp.2))) := by
      refine ENNReal.tsum_le_tsum fun xp => ?_
      have hi := graftScreenInd_le_memberInd Rv μ v0 leftTarget νt
        hcommon hrefl0 hμ0 c h z xp
      dsimp [I]
      calc
        prodPMF ρa ρb xp *
              screenInd (fullSim (graftLabRel Rv) (h + 1))
                (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
                (branch (v0, c) xp) * g (branch (v0, c) xp)
            = prodPMF ρa ρb xp *
                (screenInd (fullSim (graftLabRel Rv) (h + 1))
                  (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
                  (branch (v0, c) xp) * g (branch (v0, c) xp)) := by ring
        _ ≤ prodPMF ρa ρb xp *
              ((if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
                  rE (prodPMF p.1 p.2)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
                then 1 else 0) *
                (G₀ xp.1 * G₁ xp.2 + H₀ xp.1 * H₁ xp.2)) := by
              gcongr
              exact hnorm xp
        _ = prodPMF ρa ρb xp *
              ((if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
                  rE (prodPMF p.1 p.2)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
                then 1 else 0) * (G₀ xp.1 * G₁ xp.2)) +
            prodPMF ρa ρb xp *
              ((if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
                  rE (prodPMF p.1 p.2)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
                then 1 else 0) * (H₀ xp.1 * H₁ xp.2)) := by ring
    _ = (∑' xp, prodPMF ρa ρb xp * (I xp * (G₀ xp.1 * G₁ xp.2))) +
        (∑' xp, prodPMF ρa ρb xp * (I xp * (H₀ xp.1 * H₁ xp.2))) := by
      rw [ENNReal.tsum_add]
    _ ≤ graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b G₀ G₁ +
        graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b H₀ H₁ := by
      apply add_le_add
      · exact hallFactorize ρa ρb (fullSim (graftLabRel Rv) h)
          (graftMemPairs μ v0 leftTarget νt h z)
          ((graftZSuccCommon z).toList.map
            (graftInterp μ v0 leftTarget νt h))
          (graftMemPairs_mem μ v0 leftTarget νt h z)
          (graftMemPairs_cov μ v0 leftTarget νt h z) G₀ G₁
      · exact hallFactorize ρa ρb (fullSim (graftLabRel Rv) h)
          (graftMemPairs μ v0 leftTarget νt h z)
          ((graftZSuccCommon z).toList.map
            (graftInterp μ v0 leftTarget νt h))
          (graftMemPairs_mem μ v0 leftTarget νt h z)
          (graftMemPairs_cov μ v0 leftTarget νt h z) H₀ H₁

/-- Literal forced-source row with a forced target normalization.  The
normalization is converted to its product child law and split into the
straight and crossed survivor orders, each of which is discharged by the
two-product Hall workhorse above. -/
theorem graftForcedScreen_some_forced_le_hall (α : ℝ) (hα0 : 0 ≤ α)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl0 : Rv v0 v0) (hμ0 : (μ v0 : ℝ≥0∞) ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) {t a b u d e : GraftTgt}
    {ct cu : GraftCounter} (htc : graftTgtCounter t = some ct)
    (htp : graftForcedPair t = some (a, b))
    (huc : graftTgtCounter u = some cu)
    (hup : graftForcedPair u = some (d, e)) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) t)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (WresD α (graftInterp μ v0 leftTarget νt (h + 1) u)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b
        (WresD α (graftInterp μ v0 leftTarget νt h d)
          (fullSim (graftLabRel Rv) h))
        (WresD α (graftInterp μ v0 leftTarget νt h e)
          (fullSim (graftLabRel Rv) h))
      + graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z a b
        (WresD α (graftInterp μ v0 leftTarget νt h e)
          (fullSim (graftLabRel Rv) h))
        (WresD α (graftInterp μ v0 leftTarget νt h d)
          (fullSim (graftLabRel Rv) h)) := by
  apply graftForcedScreen_le_two_hall_of_norm Rv μ v0 leftSource leftTarget
    νs νt hcommon hrefl0 hμ0 h z htc htp
  intro xp
  rw [WresD_graftInterp_forced_succ_branch Rv μ v0 α leftTarget νt
      v0 ct h huc xp,
    if_pos hrefl0,
    graftChildren_forced_eq_prod μ v0 leftTarget νt h hup]
  exact WresD_square_le_sum hα0 _ _ _ xp

/-- **Forced source with a fresh target normalization.**  Under the exact
five-arity support of the fixed law, the literal successor-height screen is
bounded by the countable sum of the straight/crossed Hall terms of the five
charged components.  Terms outside support vanish through
`graftFreshTiltCoeff`; no inverse price is assigned to a zero-mass atom. -/
theorem graftForcedScreen_some_fresh_le_hall (α : ℝ) (hα0 : 0 ≤ α)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hsupp : ∀ k, (νt k : ℝ≥0∞) ≠ 0 →
      k ∈ insert (graftRareArity leftTarget) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl0 : Rv v0 v0) (hμ0 : (μ v0 : ℝ≥0∞) ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) {t a b : GraftTgt}
    {c : GraftCounter} (htc : graftTgtCounter t = some c)
    (htp : graftForcedPair t = some (a, b)) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) t)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      ∑' k, graftFreshTiltCoeff Rv μ v0 α νt k *
        graftFreshHallTerm Rv μ v0 α leftSource leftTarget νs νt
          h z a b k := by
  have hvpos : rE μ Rv v0 ≠ 0 := by
    intro hr
    exact hμ0 (le_antisymm (hr ▸ le_rE_of_refl hrefl0) zero_le)
  let ρa := graftInterp μ v0 leftSource νs h a
  let ρb := graftInterp μ v0 leftSource νs h b
  let R₁ := fullSim (graftLabRel Rv) (h + 1)
  let zs := z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))
  let g := WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F) R₁
  let coeff := graftFreshTiltCoeff Rv μ v0 α νt
  let tilt := graftPairTiltLift Rv μ v0 α leftTarget νt h
  have hpoint : ∀ xp : FullLab (GraftState V) h × FullLab (GraftState V) h,
      g (branch (v0, c) xp) ≤ ∑' k, coeff k * tilt k (branch (v0, c) xp) := by
    intro xp
    rw [show g (branch (v0, c) xp) =
        WresD α (graftTlaw leftTarget μ νt v0 (h + 1)) R₁
          (branch (v0, c) xp) from rfl,
      WresD_graftTlaw_succ_branch Rv μ v0 α leftTarget νt v0 hvpos c h xp]
    calc
      (rE μ Rv v0) ^ (-α) *
          WresD α (graftXiBar leftTarget μ νt v0 h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp ≤
        (rE μ Rv v0) ^ (-α) *
          (∑' k, if (νt k : ℝ≥0∞) = 0 then 0 else
            (νt k : ℝ≥0∞) ^ (-α) *
              WresD α (graftXi leftTarget μ νt v0 (.ordinary k) h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
          exact mul_le_mul_right
            (WresD_graftXiBar_le_sum Rv μ v0 α hα0 leftTarget νt h xp) _
      _ = ∑' k, (rE μ Rv v0) ^ (-α) *
          (if (νt k : ℝ≥0∞) = 0 then 0 else
            (νt k : ℝ≥0∞) ^ (-α) *
              WresD α (graftXi leftTarget μ νt v0 (.ordinary k) h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp) :=
        ENNReal.tsum_mul_left.symm
      _ ≤ ∑' k, coeff k * tilt k (branch (v0, c) xp) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk0 : (νt k : ℝ≥0∞) = 0
        · simp [hk0, coeff, graftFreshTiltCoeff]
        · rw [if_neg hk0]
          have hk := hsupp k hk0
          let p := graftSupportedPair leftTarget k
          have hsquare := WresD_square_le_sum hα0
            (graftInterp μ v0 leftTarget νt h p.1)
            (graftInterp μ v0 leftTarget νt h p.2)
            (fullSim (graftLabRel Rv) h) xp
          rw [← graftXi_eq_prod_of_fixed_support μ v0 leftTarget νt h k hk]
            at hsquare
          calc
            (rE μ Rv v0) ^ (-α) *
                ((νt k : ℝ≥0∞) ^ (-α) *
                  WresD α (graftXi leftTarget μ νt v0 (.ordinary k) h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp) ≤
              ((rE μ Rv v0) ^ (-α) * (νt k : ℝ≥0∞) ^ (-α)) *
                (WresD α (graftInterp μ v0 leftTarget νt h p.1)
                    (fullSim (graftLabRel Rv) h) xp.1 *
                  WresD α (graftInterp μ v0 leftTarget νt h p.2)
                    (fullSim (graftLabRel Rv) h) xp.2 +
                 WresD α (graftInterp μ v0 leftTarget νt h p.2)
                    (fullSim (graftLabRel Rv) h) xp.1 *
                  WresD α (graftInterp μ v0 leftTarget νt h p.1)
                    (fullSim (graftLabRel Rv) h) xp.2) := by
                simpa only [mul_assoc] using
                  mul_le_mul_right hsquare
                    ((rE μ Rv v0) ^ (-α) * (νt k : ℝ≥0∞) ^ (-α))
            _ = coeff k * tilt k (branch (v0, c) xp) := by
              simp [coeff, graftFreshTiltCoeff, hk0, tilt,
                graftPairTiltLift, p, branch]
  rw [graftInterp_forced_succ μ v0 leftSource νs h htc,
    graftChildren_forced_eq_prod μ v0 leftSource νs h htp]
  refine le_trans
    (screenE_map_tsum_tilt_le (prodPMF ρa ρb) (branch (v0, c)) R₁ zs
      g coeff tilt hpoint) ?_
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk0 : (νt k : ℝ≥0∞) = 0
  · simp [coeff, graftFreshTiltCoeff, hk0]
  · refine mul_le_mul_right ?_ (coeff k)
    have hrow := graftForcedScreen_le_two_hall_of_norm Rv μ v0
      leftSource leftTarget νs νt hcommon hrefl0 hμ0 h z htc htp
      (tilt k)
      (WresD α (graftInterp μ v0 leftTarget νt h
          (graftSupportedPair leftTarget k).1) (fullSim (graftLabRel Rv) h))
      (WresD α (graftInterp μ v0 leftTarget νt h
          (graftSupportedPair leftTarget k).2) (fullSim (graftLabRel Rv) h))
      (WresD α (graftInterp μ v0 leftTarget νt h
          (graftSupportedPair leftTarget k).2) (fullSim (graftLabRel Rv) h))
      (WresD α (graftInterp μ v0 leftTarget νt h
          (graftSupportedPair leftTarget k).1) (fullSim (graftLabRel Rv) h))
      (by intro xp; simp [tilt, graftPairTiltLift, branch])
    rw [graftInterp_forced_succ μ v0 leftSource νs h htc,
      graftChildren_forced_eq_prod μ v0 leftSource νs h htp] at hrow
    simpa [ρa, ρb, R₁, zs, graftFreshHallTerm] using hrow

/-- **One sampled fresh-source component at a compatible root.**  For every
charged arity of the fixed law, the actual per-root Markov law has the exact
product source used by the Hall factorization.  A two-product normalization
therefore produces the same straight/crossed Hall outputs as a forced source
cell.  This is the near-root component row; integrating it over `μ` and
charging incompatible roots are separate quantitative steps. -/
theorem graftComponentScreen_le_two_hall_of_norm
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    {v : V} (hv0 : Rv v v0) (hvpos : rE μ Rv v ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) (k : ℕ)
    (hksupp : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore)
    (g : FullLab (GraftState V) (h + 1) → ℝ≥0∞)
    (G₀ G₁ H₀ H₁ : FullLab (GraftState V) h → ℝ≥0∞)
    (hnorm : ∀ xp, g (branch (v, .ordinary k) xp) ≤
      G₀ xp.1 * G₁ xp.2 + H₀ xp.1 * H₁ xp.2) :
    screenE
        (muM (graftK leftSource μ νs v0) (v, .ordinary k) (h + 1))
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))) g ≤
      graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z
          (graftSupportedPair leftSource k).1
          (graftSupportedPair leftSource k).2 G₀ G₁ +
        graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z
          (graftSupportedPair leftSource k).1
          (graftSupportedPair leftSource k).2 H₀ H₁ := by
  rw [graftComponentScreen_branch μ v0 leftSource νs v k h,
    graftXi_eq_prod_of_fixed_support μ v0 leftSource νs h k hksupp]
  let ρa := graftInterp μ v0 leftSource νs h
    (graftSupportedPair leftSource k).1
  let ρb := graftInterp μ v0 leftSource νs h
    (graftSupportedPair leftSource k).2
  let I : FullLab (GraftState V) h × FullLab (GraftState V) h → ℝ≥0∞ :=
    fun xp => if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
      rE (prodPMF p.1 p.2) (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
      then 1 else 0
  calc
    (∑' xp, prodPMF ρa ρb xp *
        (screenInd (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (branch (v, .ordinary k) xp) *
            g (branch (v, .ordinary k) xp))) ≤
      ∑' xp, (prodPMF ρa ρb xp * (I xp * (G₀ xp.1 * G₁ xp.2)) +
        prodPMF ρa ρb xp * (I xp * (H₀ xp.1 * H₁ xp.2))) := by
      refine ENNReal.tsum_le_tsum fun xp => ?_
      have hi := graftScreenInd_le_memberInd_near Rv μ v0 leftTarget νt
        hcommon hv0 hvpos (.ordinary k) h z xp
      dsimp [I]
      calc
        prodPMF ρa ρb xp *
            (screenInd (fullSim (graftLabRel Rv) (h + 1))
              (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
              (branch (v, .ordinary k) xp) *
                g (branch (v, .ordinary k) xp)) ≤
          prodPMF ρa ρb xp *
            ((if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
              then 1 else 0) *
                (G₀ xp.1 * G₁ xp.2 + H₀ xp.1 * H₁ xp.2)) := by
            gcongr
            exact hnorm xp
        _ = prodPMF ρa ρb xp *
              ((if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
                  rE (prodPMF p.1 p.2)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
                then 1 else 0) * (G₀ xp.1 * G₁ xp.2)) +
            prodPMF ρa ρb xp *
              ((if ∀ p ∈ graftMemPairs μ v0 leftTarget νt h z,
                  rE (prodPMF p.1 p.2)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp = 0
                then 1 else 0) * (H₀ xp.1 * H₁ xp.2)) := by ring
    _ = (∑' xp, prodPMF ρa ρb xp * (I xp * (G₀ xp.1 * G₁ xp.2))) +
        (∑' xp, prodPMF ρa ρb xp * (I xp * (H₀ xp.1 * H₁ xp.2))) := by
      rw [ENNReal.tsum_add]
    _ ≤ graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z
          (graftSupportedPair leftSource k).1
          (graftSupportedPair leftSource k).2 G₀ G₁ +
        graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z
          (graftSupportedPair leftSource k).1
          (graftSupportedPair leftSource k).2 H₀ H₁ := by
      apply add_le_add
      · exact hallFactorize ρa ρb (fullSim (graftLabRel Rv) h)
          (graftMemPairs μ v0 leftTarget νt h z)
          ((graftZSuccCommon z).toList.map
            (graftInterp μ v0 leftTarget νt h))
          (graftMemPairs_mem μ v0 leftTarget νt h z)
          (graftMemPairs_cov μ v0 leftTarget νt h z) G₀ G₁
      · exact hallFactorize ρa ρb (fullSim (graftLabRel Rv) h)
          (graftMemPairs μ v0 leftTarget νt h z)
          ((graftZSuccCommon z).toList.map
            (graftInterp μ v0 leftTarget νt h))
          (graftMemPairs_mem μ v0 leftTarget νt h z)
          (graftMemPairs_cov μ v0 leftTarget νt h z) H₀ H₁

/-- Near-root fresh-source component with a fresh target normalization.  The
target mixture is expanded into its five charged product components, while
the sampled source arity remains fixed. -/
theorem graftComponentScreen_some_fresh_le_hall (α : ℝ) (hα0 : 0 ≤ α)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (htsupp : ∀ j, (νt j : ℝ≥0∞) ≠ 0 →
      j ∈ insert (graftRareArity leftTarget) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    {v : V} (hv0 : Rv v v0) (hvpos : rE μ Rv v ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) (k : ℕ)
    (hksupp : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore) :
    screenE
        (muM (graftK leftSource μ νs v0) (v, .ordinary k) (h + 1))
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      ∑' j, graftRootFreshTiltCoeff Rv μ α νt v j *
        graftFreshHallTerm Rv μ v0 α leftSource leftTarget νs νt h z
          (graftSupportedPair leftSource k).1
          (graftSupportedPair leftSource k).2 j := by
  let ρa := graftInterp μ v0 leftSource νs h
    (graftSupportedPair leftSource k).1
  let ρb := graftInterp μ v0 leftSource νs h
    (graftSupportedPair leftSource k).2
  let R₁ := fullSim (graftLabRel Rv) (h + 1)
  let zs := z.toList.map (graftInterp μ v0 leftTarget νt (h + 1))
  let g := WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F) R₁
  let coeff := graftRootFreshTiltCoeff Rv μ α νt v
  let tilt := graftPairTiltLift Rv μ v0 α leftTarget νt h
  have hpoint : ∀ xp : FullLab (GraftState V) h × FullLab (GraftState V) h,
      g (branch (v, .ordinary k) xp) ≤
        ∑' j, coeff j * tilt j (branch (v, .ordinary k) xp) := by
    intro xp
    rw [show g (branch (v, .ordinary k) xp) =
        WresD α (graftTlaw leftTarget μ νt v0 (h + 1)) R₁
          (branch (v, .ordinary k) xp) from rfl,
      WresD_graftTlaw_succ_branch Rv μ v0 α leftTarget νt v hvpos
        (.ordinary k) h xp]
    calc
      (rE μ Rv v) ^ (-α) *
          WresD α (graftXiBar leftTarget μ νt v0 h)
            (SquareRel (fullSim (graftLabRel Rv) h)) xp ≤
        (rE μ Rv v) ^ (-α) *
          (∑' j, if (νt j : ℝ≥0∞) = 0 then 0 else
            (νt j : ℝ≥0∞) ^ (-α) *
              WresD α (graftXi leftTarget μ νt v0 (.ordinary j) h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
          exact mul_le_mul_right
            (WresD_graftXiBar_le_sum Rv μ v0 α hα0 leftTarget νt h xp) _
      _ = ∑' j, (rE μ Rv v) ^ (-α) *
          (if (νt j : ℝ≥0∞) = 0 then 0 else
            (νt j : ℝ≥0∞) ^ (-α) *
              WresD α (graftXi leftTarget μ νt v0 (.ordinary j) h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp) :=
        ENNReal.tsum_mul_left.symm
      _ ≤ ∑' j, coeff j * tilt j (branch (v, .ordinary k) xp) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases hj0 : (νt j : ℝ≥0∞) = 0
        · simp [hj0, coeff, graftRootFreshTiltCoeff]
        · rw [if_neg hj0]
          have hj := htsupp j hj0
          let p := graftSupportedPair leftTarget j
          have hsquare := WresD_square_le_sum hα0
            (graftInterp μ v0 leftTarget νt h p.1)
            (graftInterp μ v0 leftTarget νt h p.2)
            (fullSim (graftLabRel Rv) h) xp
          rw [← graftXi_eq_prod_of_fixed_support μ v0 leftTarget νt h j hj]
            at hsquare
          calc
            (rE μ Rv v) ^ (-α) *
                ((νt j : ℝ≥0∞) ^ (-α) *
                  WresD α (graftXi leftTarget μ νt v0 (.ordinary j) h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp) ≤
              ((rE μ Rv v) ^ (-α) * (νt j : ℝ≥0∞) ^ (-α)) *
                (WresD α (graftInterp μ v0 leftTarget νt h p.1)
                    (fullSim (graftLabRel Rv) h) xp.1 *
                  WresD α (graftInterp μ v0 leftTarget νt h p.2)
                    (fullSim (graftLabRel Rv) h) xp.2 +
                 WresD α (graftInterp μ v0 leftTarget νt h p.2)
                    (fullSim (graftLabRel Rv) h) xp.1 *
                  WresD α (graftInterp μ v0 leftTarget νt h p.1)
                    (fullSim (graftLabRel Rv) h) xp.2) := by
                simpa only [mul_assoc] using
                  mul_le_mul_right hsquare
                    ((rE μ Rv v) ^ (-α) * (νt j : ℝ≥0∞) ^ (-α))
            _ = coeff j * tilt j (branch (v, .ordinary k) xp) := by
              simp [coeff, graftRootFreshTiltCoeff, hj0, tilt,
                graftPairTiltLift, p, branch]
  rw [muM_succ, graftPairMix_ordinary μ v0 leftSource νs v k h,
    graftXi_eq_prod_of_fixed_support μ v0 leftSource νs h k hksupp]
  refine le_trans
    (screenE_map_tsum_tilt_le (prodPMF ρa ρb)
      (branch (v, .ordinary k)) R₁ zs g coeff tilt hpoint) ?_
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases hj0 : (νt j : ℝ≥0∞) = 0
  · simp [coeff, graftRootFreshTiltCoeff, hj0]
  · refine mul_le_mul_right ?_ (coeff j)
    have hrow := graftComponentScreen_le_two_hall_of_norm Rv μ v0
      leftSource leftTarget νs νt hcommon hv0 hvpos h z k hksupp
      (tilt j)
      (WresD α (graftInterp μ v0 leftTarget νt h
          (graftSupportedPair leftTarget j).1) (fullSim (graftLabRel Rv) h))
      (WresD α (graftInterp μ v0 leftTarget νt h
          (graftSupportedPair leftTarget j).2) (fullSim (graftLabRel Rv) h))
      (WresD α (graftInterp μ v0 leftTarget νt h
          (graftSupportedPair leftTarget j).2) (fullSim (graftLabRel Rv) h))
      (WresD α (graftInterp μ v0 leftTarget νt h
          (graftSupportedPair leftTarget j).1) (fullSim (graftLabRel Rv) h))
      (by intro xp; simp [tilt, graftPairTiltLift, branch])
    rw [muM_succ, graftPairMix_ordinary μ v0 leftSource νs v k h,
      graftXi_eq_prod_of_fixed_support μ v0 leftSource νs h k hksupp] at hrow
    simpa [ρa, ρb, R₁, zs, graftFreshHallTerm] using hrow

private lemma graftScreenInd_le_one {X : Type} (R : X → X → Prop)
    (zs : List (PMF X)) (x : X) : screenInd R zs x ≤ 1 := by
  rw [screenInd]
  split_ifs <;> simp

private lemma graftScreenE_one_le_one {X : Type} (ρ : PMF X)
    (R : X → X → Prop) (zs : List (PMF X)) :
    screenE ρ R zs (fun _ => 1) ≤ 1 := by
  rw [screenE]
  calc
    (∑' x, ρ x * screenInd R zs x * 1) ≤ ∑' x, ρ x := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      simpa using mul_le_mul_right (graftScreenInd_le_one R zs x) (ρ x)
    _ = 1 := ρ.tsum_coe

/-- Unit-normalization specialization of the near-root component row. -/
theorem graftComponentScreen_none_le_hall
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    {v : V} (hv0 : Rv v v0) (hvpos : rE μ Rv v ≠ 0)
    (h : ℕ) (z : Finset GraftTgt) (k : ℕ)
    (hksupp : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore) :
    screenE
        (muM (graftK leftSource μ νs v0) (v, .ordinary k) (h + 1))
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (fun _ => 1) ≤
      graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z
        (graftSupportedPair leftSource k).1
        (graftSupportedPair leftSource k).2 (fun _ => 1) (fun _ => 1) := by
  have hrow := graftComponentScreen_le_two_hall_of_norm Rv μ v0
    leftSource leftTarget νs νt hcommon hv0 hvpos h z k hksupp
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0)
    (by intro xp; simp)
  simpa [graftHallRHS, screenE] using hrow

/-- **Fresh source with unit normalization, including the root error.**
The actual fresh law is split over `(k,v)`.  Compatible charged roots use the
component Hall row; incompatible roots contribute at most the one-site bad
mass `qE μ Rv v0`.  The exceptional source arity keeps its literal law mass
inside the displayed sum. -/
theorem graftFreshScreen_none_le_qE_add_hall
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hsupp : ∀ k, (νs k : ℝ≥0∞) ≠ 0 →
      k ∈ insert (graftRareArity leftSource) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ v w, Rv v w → Rv w v)
    (h : ℕ) (z : Finset GraftTgt) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) .F)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (fun _ => 1) ≤
      qE μ Rv v0 +
        ∑' k, (νs k : ℝ≥0∞) *
          graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z
            (graftSupportedPair leftSource k).1
            (graftSupportedPair leftSource k).2
            (fun _ => 1) (fun _ => 1) := by
  rw [graftInterp_F,
    graftFreshScreen_split μ v0 leftSource νs (h + 1)]
  let B : ℕ → ℝ≥0∞ := fun k =>
    graftHallRHS Rv μ v0 leftSource leftTarget νs νt h z
      (graftSupportedPair leftSource k).1
      (graftSupportedPair leftSource k).2 (fun _ => 1) (fun _ => 1)
  have hinner : ∀ k, (νs k : ℝ≥0∞) ≠ 0 →
      (∑' v, (μ v : ℝ≥0∞) *
        screenE (muM (graftK leftSource μ νs v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (fun _ => 1)) ≤ B k + qE μ Rv v0 := by
    intro k hk
    have hksupp := hsupp k hk
    calc
      (∑' v, (μ v : ℝ≥0∞) *
          screenE (muM (graftK leftSource μ νs v0)
              (v, .ordinary k) (h + 1))
            (fullSim (graftLabRel Rv) (h + 1))
            (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
            (fun _ => 1)) ≤
        ∑' v, ((μ v : ℝ≥0∞) * B k +
          if Rv v0 v then 0 else (μ v : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hμv : (μ v : ℝ≥0∞) = 0
        · simp [hμv]
        · by_cases hv : Rv v v0
          · have hvpos : rE μ Rv v ≠ 0 := by
              intro hr
              exact hμv (le_antisymm (hr ▸ le_rE_of_refl (hrefl v)) zero_le)
            rw [if_pos (hsymm v v0 hv), add_zero]
            exact mul_le_mul_right
              (graftComponentScreen_none_le_hall Rv μ v0
                leftSource leftTarget νs νt hcommon hv hvpos h z k hksupp) _
          · rw [if_neg (fun hv' => hv (hsymm v0 v hv'))]
            calc
              (μ v : ℝ≥0∞) *
                  screenE (muM (graftK leftSource μ νs v0)
                      (v, .ordinary k) (h + 1))
                    (fullSim (graftLabRel Rv) (h + 1))
                    (z.toList.map
                      (graftInterp μ v0 leftTarget νt (h + 1)))
                    (fun _ => 1) ≤ (μ v : ℝ≥0∞) * 1 :=
                mul_le_mul_right
                  (graftScreenE_one_le_one _ _ _) _
              _ ≤ (μ v : ℝ≥0∞) * B k + (μ v : ℝ≥0∞) := by
                simp
      _ = B k + qE μ Rv v0 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe,
          one_mul, qE]
  calc
    (∑' k, (νs k : ℝ≥0∞) * ∑' v, (μ v : ℝ≥0∞) *
        screenE (muM (graftK leftSource μ νs v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (fun _ => 1)) ≤
      ∑' k, (νs k : ℝ≥0∞) * (B k + qE μ Rv v0) := by
      refine ENNReal.tsum_le_tsum fun k => ?_
      by_cases hk : (νs k : ℝ≥0∞) = 0
      · simp [hk]
      · exact mul_le_mul_right (hinner k hk) _
    _ = (∑' k, (νs k : ℝ≥0∞) * B k) + qE μ Rv v0 := by
      calc
        (∑' k, (νs k : ℝ≥0∞) * (B k + qE μ Rv v0)) =
            ∑' k, ((νs k : ℝ≥0∞) * B k +
              (νs k : ℝ≥0∞) * qE μ Rv v0) := by
          refine tsum_congr fun k => by ring
        _ = (∑' k, (νs k : ℝ≥0∞) * B k) +
            ∑' k, (νs k : ℝ≥0∞) * qE μ Rv v0 := ENNReal.tsum_add
        _ = (∑' k, (νs k : ℝ≥0∞) * B k) + qE μ Rv v0 := by
          rw [ENNReal.tsum_mul_right, νs.tsum_coe, one_mul]
    _ = qE μ Rv v0 + ∑' k, (νs k : ℝ≥0∞) * B k := add_comm _ _

/-- **Fresh source with a deterministic target normalization.**  A source
root incompatible with `v0` contributes exactly zero because the target
normalization itself vanishes there.  Compatible roots produce the two Hall
orders of the target child pair, and integration leaves the literal source
weights `νs(k)` in front of the component rows. -/
theorem graftFreshScreen_some_forced_le_hall (α : ℝ) (hα0 : 0 ≤ α)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hsupp : ∀ k, (νs k : ℝ≥0∞) ≠ 0 →
      k ∈ insert (graftRareArity leftSource) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl : ∀ v, Rv v v)
    (h : ℕ) (z : Finset GraftTgt) {u d e : GraftTgt}
    {cu : GraftCounter} (huc : graftTgtCounter u = some cu)
    (hup : graftForcedPair u = some (d, e)) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) .F)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (WresD α (graftInterp μ v0 leftTarget νt (h + 1) u)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      ∑' k, (νs k : ℝ≥0∞) *
        graftSourceForcedHallTerm Rv μ v0 α leftSource leftTarget νs νt
          h z k d e := by
  rw [graftInterp_F,
    graftFreshScreen_split μ v0 leftSource νs (h + 1)]
  let B : ℕ → ℝ≥0∞ := fun k =>
    graftSourceForcedHallTerm Rv μ v0 α leftSource leftTarget νs νt
      h z k d e
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : (νs k : ℝ≥0∞) = 0
  · simp [hk]
  · refine mul_le_mul_right ?_ _
    have hksupp := hsupp k hk
    calc
      (∑' v, (μ v : ℝ≥0∞) *
          screenE (muM (graftK leftSource μ νs v0)
              (v, .ordinary k) (h + 1))
            (fullSim (graftLabRel Rv) (h + 1))
            (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
            (WresD α (graftInterp μ v0 leftTarget νt (h + 1) u)
              (fullSim (graftLabRel Rv) (h + 1)))) ≤
        ∑' v, (μ v : ℝ≥0∞) * B k := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hμv : (μ v : ℝ≥0∞) = 0
        · simp [hμv]
        · by_cases hv : Rv v v0
          · have hvpos : rE μ Rv v ≠ 0 := by
              intro hr
              exact hμv (le_antisymm (hr ▸ le_rE_of_refl (hrefl v)) zero_le)
            refine mul_le_mul_right ?_ _
            have hrow := graftComponentScreen_le_two_hall_of_norm Rv μ v0
              leftSource leftTarget νs νt hcommon hv hvpos h z k hksupp
              (WresD α (graftInterp μ v0 leftTarget νt (h + 1) u)
                (fullSim (graftLabRel Rv) (h + 1)))
              (WresD α (graftInterp μ v0 leftTarget νt h d)
                (fullSim (graftLabRel Rv) h))
              (WresD α (graftInterp μ v0 leftTarget νt h e)
                (fullSim (graftLabRel Rv) h))
              (WresD α (graftInterp μ v0 leftTarget νt h e)
                (fullSim (graftLabRel Rv) h))
              (WresD α (graftInterp μ v0 leftTarget νt h d)
                (fullSim (graftLabRel Rv) h))
              (by
                intro xp
                rw [WresD_graftInterp_forced_succ_branch Rv μ v0 α
                    leftTarget νt v (.ordinary k) h huc xp,
                  if_pos hv,
                  graftChildren_forced_eq_prod μ v0 leftTarget νt h hup]
                exact WresD_square_le_sum hα0 _ _ _ xp)
            simpa [B, graftSourceForcedHallTerm] using hrow
          · have hzero :
                screenE (muM (graftK leftSource μ νs v0)
                    (v, .ordinary k) (h + 1))
                  (fullSim (graftLabRel Rv) (h + 1))
                  (z.toList.map
                    (graftInterp μ v0 leftTarget νt (h + 1)))
                  (WresD α (graftInterp μ v0 leftTarget νt (h + 1) u)
                    (fullSim (graftLabRel Rv) (h + 1))) = 0 := by
              rw [graftComponentScreen_branch μ v0 leftSource νs v k h]
              apply ENNReal.tsum_eq_zero.mpr
              intro xp
              rw [WresD_graftInterp_forced_succ_branch Rv μ v0 α
                  leftTarget νt v (.ordinary k) h huc xp,
                if_neg hv]
              simp
            rw [hzero, mul_zero]
            exact zero_le
      _ = B k := by
        rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- **Fresh source with fresh target normalization, with the far-root term
kept explicit.**  `RT` controls the full sampled-root inverse moment and
`FT` its incompatible-root part.  `M` controls the child component-to-mixture
restricted potentials.  The conclusion separates the far analytic charge
from the literal two-law Hall sum; no absorption into the finite matrix is
asserted here. -/
theorem graftFreshScreen_some_fresh_le_far_add_hall
    (α : ℝ) (hα : 1 ≤ α)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hssupp : ∀ k, (νs k : ℝ≥0∞) ≠ 0 →
      k ∈ insert (graftRareArity leftSource) elevenThirteenCommonCore)
    (htsupp : ∀ j, (νt j : ℝ≥0∞) ≠ 0 →
      j ∈ insert (graftRareArity leftTarget) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl : ∀ v, Rv v v)
    (h : ℕ) (z : Finset GraftTgt) (RT FT M : ℝ≥0∞)
    (hRT : (∑' v, (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α)) ≤ RT)
    (hFT : (∑' v, if Rv v v0 then 0 else
      (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α)) ≤ FT)
    (hMom : ∀ k, (νs k : ℝ≥0∞) ≠ 0 →
      PhiDres α (graftXi leftSource μ νs v0 (.ordinary k) h)
        (graftXiBar leftTarget μ νt v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) ≤ M) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) .F)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      FT * (1 + ENNReal.ofReal α * M) +
        RT * ∑' k, (νs k : ℝ≥0∞) * ∑' j,
          (if (νt j : ℝ≥0∞) = 0 then 0
            else (νt j : ℝ≥0∞) ^ (-α)) *
          graftFreshHallTerm Rv μ v0 α leftSource leftTarget νs νt h z
            (graftSupportedPair leftSource k).1
            (graftSupportedPair leftSource k).2 j := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hα
  rw [graftInterp_F,
    graftFreshScreen_split μ v0 leftSource νs (h + 1)]
  let T : ℕ → ℝ≥0∞ := fun j =>
    if (νt j : ℝ≥0∞) = 0 then 0 else (νt j : ℝ≥0∞) ^ (-α)
  let B : ℕ → ℕ → ℝ≥0∞ := fun k j =>
    graftFreshHallTerm Rv μ v0 α leftSource leftTarget νs νt h z
      (graftSupportedPair leftSource k).1
      (graftSupportedPair leftSource k).2 j
  let H : ℕ → ℝ≥0∞ := fun k => ∑' j, T j * B k j
  let C : ℝ≥0∞ := 1 + ENNReal.ofReal α * M
  have hinner : ∀ k, (νs k : ℝ≥0∞) ≠ 0 →
      (∑' v, (μ v : ℝ≥0∞) *
        screenE (muM (graftK leftSource μ νs v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
            (fullSim (graftLabRel Rv) (h + 1)))) ≤
        RT * H k + FT * C := by
    intro k hk
    have hksupp := hssupp k hk
    have hnear : ∀ v, Rv v v0 → (μ v : ℝ≥0∞) ≠ 0 →
        screenE (muM (graftK leftSource μ νs v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
            (fullSim (graftLabRel Rv) (h + 1))) ≤
          (rE μ Rv v) ^ (-α) * H k := by
      intro v hv hμv
      have hvpos : rE μ Rv v ≠ 0 := by
        intro hr
        exact hμv (le_antisymm (hr ▸ le_rE_of_refl (hrefl v)) zero_le)
      calc
        screenE (muM (graftK leftSource μ νs v0)
              (v, .ordinary k) (h + 1))
            (fullSim (graftLabRel Rv) (h + 1))
            (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
            (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
              (fullSim (graftLabRel Rv) (h + 1))) ≤
          ∑' j, graftRootFreshTiltCoeff Rv μ α νt v j * B k j := by
            simpa [B] using
              (graftComponentScreen_some_fresh_le_hall Rv μ v0 α hα0
                leftSource leftTarget νs νt htsupp hcommon hv hvpos h z k hksupp)
        _ = ∑' j, (rE μ Rv v) ^ (-α) * (T j * B k j) := by
          refine tsum_congr fun j => ?_
          by_cases hj : (νt j : ℝ≥0∞) = 0
          · simp [graftRootFreshTiltCoeff, T, hj]
          · simp [graftRootFreshTiltCoeff, T, hj]
            ring
        _ = (rE μ Rv v) ^ (-α) * H k := by
          rw [ENNReal.tsum_mul_left]
    have hfar : ∀ v, ¬ Rv v v0 → (μ v : ℝ≥0∞) ≠ 0 →
        screenE (muM (graftK leftSource μ νs v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
            (fullSim (graftLabRel Rv) (h + 1))) ≤
          (rE μ Rv v) ^ (-α) * C := by
      intro v _hv hμv
      have hvpos : rE μ Rv v ≠ 0 := by
        intro hr
        exact hμv (le_antisymm (hr ▸ le_rE_of_refl (hrefl v)) zero_le)
      rw [graftComponentScreen_branch μ v0 leftSource νs v k h]
      calc
        (∑' xp, graftXi leftSource μ νs v0 (.ordinary k) h xp *
            (screenInd (fullSim (graftLabRel Rv) (h + 1))
              (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
              (branch (v, .ordinary k) xp) *
              WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
                (fullSim (graftLabRel Rv) (h + 1))
                (branch (v, .ordinary k) xp))) ≤
          ∑' xp, graftXi leftSource μ νs v0 (.ordinary k) h xp *
            ((rE μ Rv v) ^ (-α) *
              WresD α (graftXiBar leftTarget μ νt v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
            refine ENNReal.tsum_le_tsum fun xp => ?_
            rw [graftInterp_F,
              WresD_graftTlaw_succ_branch Rv μ v0 α leftTarget νt v
                hvpos (.ordinary k) h xp]
            have hi := graftScreenInd_le_one
              (fullSim (graftLabRel Rv) (h + 1))
              (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
              (branch (v, .ordinary k) xp)
            calc
              graftXi leftSource μ νs v0 (.ordinary k) h xp *
                  (screenInd (fullSim (graftLabRel Rv) (h + 1))
                    (z.toList.map
                      (graftInterp μ v0 leftTarget νt (h + 1)))
                    (branch (v, .ordinary k) xp) *
                    ((rE μ Rv v) ^ (-α) *
                      WresD α (graftXiBar leftTarget μ νt v0 h)
                        (SquareRel (fullSim (graftLabRel Rv) h)) xp)) ≤
                graftXi leftSource μ νs v0 (.ordinary k) h xp *
                  (1 * ((rE μ Rv v) ^ (-α) *
                      WresD α (graftXiBar leftTarget μ νt v0 h)
                        (SquareRel (fullSim (graftLabRel Rv) h)) xp)) := by
                have hinner := mul_le_mul_right hi
                  ((rE μ Rv v) ^ (-α) *
                    WresD α (graftXiBar leftTarget μ νt v0 h)
                      (SquareRel (fullSim (graftLabRel Rv) h)) xp)
                have houter := mul_le_mul_right hinner
                  (graftXi leftSource μ νs v0 (.ordinary k) h xp)
                simpa [mul_comm, mul_left_comm, mul_assoc] using houter
              _ = graftXi leftSource μ νs v0 (.ordinary k) h xp *
                  ((rE μ Rv v) ^ (-α) *
                    WresD α (graftXiBar leftTarget μ νt v0 h)
                      (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
                rw [one_mul]
        _ = (rE μ Rv v) ^ (-α) *
            ∑' xp, graftXi leftSource μ νs v0 (.ordinary k) h xp *
              WresD α (graftXiBar leftTarget μ νt v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h)) xp := by
          calc
            (∑' xp, graftXi leftSource μ νs v0 (.ordinary k) h xp *
                ((rE μ Rv v) ^ (-α) *
                  WresD α (graftXiBar leftTarget μ νt v0 h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp)) =
              ∑' xp, (rE μ Rv v) ^ (-α) *
                (graftXi leftSource μ νs v0 (.ordinary k) h xp *
                  WresD α (graftXiBar leftTarget μ νt v0 h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp) := by
                refine tsum_congr fun xp => by ring
            _ = (rE μ Rv v) ^ (-α) *
                ∑' xp, graftXi leftSource μ νs v0 (.ordinary k) h xp *
                  WresD α (graftXiBar leftTarget μ νt v0 h)
                    (SquareRel (fullSim (graftLabRel Rv) h)) xp :=
              ENNReal.tsum_mul_left
        _ ≤ (rE μ Rv v) ^ (-α) *
            (1 + ENNReal.ofReal α *
              PhiDres α (graftXi leftSource μ νs v0 (.ordinary k) h)
                (graftXiBar leftTarget μ νt v0 h)
                (SquareRel (fullSim (graftLabRel Rv) h))) := by
          exact mul_le_mul_right
            (tsum_WresD_le hα
              (graftXi leftSource μ νs v0 (.ordinary k) h)
              (graftXiBar leftTarget μ νt v0 h)
              (SquareRel (fullSim (graftLabRel Rv) h))) _
        _ ≤ (rE μ Rv v) ^ (-α) * C := by
          exact mul_le_mul_right
            (add_le_add le_rfl (mul_le_mul_right (hMom k hk) _)) _
    calc
      (∑' v, (μ v : ℝ≥0∞) *
          screenE (muM (graftK leftSource μ νs v0)
              (v, .ordinary k) (h + 1))
            (fullSim (graftLabRel Rv) (h + 1))
            (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
            (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
              (fullSim (graftLabRel Rv) (h + 1)))) ≤
        ∑' v, ((μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α) * H k +
          (if Rv v v0 then 0 else
            (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α) * C)) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hμv : (μ v : ℝ≥0∞) = 0
        · simp [hμv]
        · by_cases hv : Rv v v0
          · rw [if_pos hv, add_zero]
            simpa only [mul_assoc] using mul_le_mul_right (hnear v hv hμv) _
          · rw [if_neg hv]
            calc
              (μ v : ℝ≥0∞) *
                  screenE (muM (graftK leftSource μ νs v0)
                      (v, .ordinary k) (h + 1))
                    (fullSim (graftLabRel Rv) (h + 1))
                    (z.toList.map
                      (graftInterp μ v0 leftTarget νt (h + 1)))
                    (WresD α
                      (graftInterp μ v0 leftTarget νt (h + 1) .F)
                      (fullSim (graftLabRel Rv) (h + 1))) ≤
                (μ v : ℝ≥0∞) * ((rE μ Rv v) ^ (-α) * C) :=
                  mul_le_mul_right (hfar v hv hμv) _
              _ ≤ (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α) * H k +
                  (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α) * C := by
                simpa only [mul_assoc] using le_add_left
                  (le_refl ((μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α) * C))
      _ = (∑' v, (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α)) * H k +
          (∑' v, if Rv v v0 then 0 else
            (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α)) * C := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        congr 1
        calc
          (∑' v, if Rv v v0 then 0 else
              (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α) * C) =
            ∑' v, (if Rv v v0 then 0 else
              (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α)) * C := by
                refine tsum_congr fun v => ?_
                by_cases hv : Rv v v0 <;> simp [hv]
          _ = (∑' v, if Rv v v0 then 0 else
              (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α)) * C :=
            ENNReal.tsum_mul_right
      _ ≤ RT * H k + FT * C := by
        apply add_le_add
        · simpa [mul_comm] using mul_le_mul_right hRT (H k)
        · simpa [mul_comm] using mul_le_mul_right hFT C
  calc
    (∑' k, (νs k : ℝ≥0∞) * ∑' v, (μ v : ℝ≥0∞) *
        screenE (muM (graftK leftSource μ νs v0)
            (v, .ordinary k) (h + 1))
          (fullSim (graftLabRel Rv) (h + 1))
          (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
          (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
            (fullSim (graftLabRel Rv) (h + 1)))) ≤
      ∑' k, (νs k : ℝ≥0∞) * (RT * H k + FT * C) := by
      refine ENNReal.tsum_le_tsum fun k => ?_
      by_cases hk : (νs k : ℝ≥0∞) = 0
      · simp [hk]
      · exact mul_le_mul_right (hinner k hk) _
    _ = FT * C + RT * ∑' k, (νs k : ℝ≥0∞) * H k := by
      calc
        (∑' k, (νs k : ℝ≥0∞) * (RT * H k + FT * C)) =
            (∑' k, (νs k : ℝ≥0∞) * (RT * H k)) +
              ∑' k, (νs k : ℝ≥0∞) * (FT * C) := by
          rw [← ENNReal.tsum_add]
          refine tsum_congr fun k => by ring
        _ = RT * (∑' k, (νs k : ℝ≥0∞) * H k) + FT * C := by
          calc
            (∑' k, (νs k : ℝ≥0∞) * (RT * H k)) +
                ∑' k, (νs k : ℝ≥0∞) * (FT * C) =
              (∑' k, RT * ((νs k : ℝ≥0∞) * H k)) +
                ∑' k, (νs k : ℝ≥0∞) * (FT * C) := by
                  congr 1
                  refine tsum_congr fun k => by ring
            _ = RT * (∑' k, (νs k : ℝ≥0∞) * H k) +
                ∑' k, (νs k : ℝ≥0∞) * (FT * C) := by
              rw [ENNReal.tsum_mul_left]
            _ = RT * (∑' k, (νs k : ℝ≥0∞) * H k) + FT * C := by
              rw [ENNReal.tsum_mul_right, νs.tsum_coe, one_mul]
        _ = FT * C + RT * ∑' k, (νs k : ℝ≥0∞) * H k := by ring
    _ = FT * (1 + ENNReal.ofReal α * M) +
        RT * ∑' k, (νs k : ℝ≥0∞) * ∑' j,
          (if (νt j : ℝ≥0∞) = 0 then 0
            else (νt j : ℝ≥0∞) ^ (-α)) * B k j := by
      rfl

/-- Standard graph-potential specialization of the preceding fresh/fresh
row.  Under `μ(v0) ≥ 1/2`, reflexivity and symmetry, the full root inverse
moment is at most `2^α + 2η` and its incompatible part is at most `2η`, where
`η = etaG α Rv μ`. -/
theorem graftFreshScreen_some_fresh_le_eta_add_hall
    (α : ℝ) (hα : 1 ≤ α)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hssupp : ∀ k, (νs k : ℝ≥0∞) ≠ 0 →
      k ∈ insert (graftRareArity leftSource) elevenThirteenCommonCore)
    (htsupp : ∀ j, (νt j : ℝ≥0∞) ≠ 0 →
      j ∈ insert (graftRareArity leftTarget) elevenThirteenCommonCore)
    (hcommon : ∀ i : Fin 4, (νt (graftCommonArity i) : ℝ≥0∞) ≠ 0)
    (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ v w, Rv v w → Rv w v)
    (hhalf : 2⁻¹ ≤ (μ v0 : ℝ≥0∞))
    (h : ℕ) (z : Finset GraftTgt) (M : ℝ≥0∞)
    (hMom : ∀ k, (νs k : ℝ≥0∞) ≠ 0 →
      PhiDres α (graftXi leftSource μ νs v0 (.ordinary k) h)
        (graftXiBar leftTarget μ νt v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) ≤ M) :
    screenE (graftInterp μ v0 leftSource νs (h + 1) .F)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp μ v0 leftTarget νt (h + 1)))
        (WresD α (graftInterp μ v0 leftTarget νt (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      (2 * etaG α Rv μ) * (1 + ENNReal.ofReal α * M) +
        ((2 : ℝ≥0∞) ^ α + 2 * etaG α Rv μ) *
          ∑' k, (νs k : ℝ≥0∞) * ∑' j,
            (if (νt j : ℝ≥0∞) = 0 then 0
              else (νt j : ℝ≥0∞) ^ (-α)) *
            graftFreshHallTerm Rv μ v0 α leftSource leftTarget νs νt h z
              (graftSupportedPair leftSource k).1
              (graftSupportedPair leftSource k).2 j := by
  apply graftFreshScreen_some_fresh_le_far_add_hall Rv μ v0 α hα
    leftSource leftTarget νs νt hssupp htsupp hcommon hrefl h z
    ((2 : ℝ≥0∞) ^ α + 2 * etaG α Rv μ) (2 * etaG α Rv μ) M
  · exact tilt_le_pow_add α Rv μ v0 (by linarith) hsymm hhalf
  · calc
      (∑' v, if Rv v v0 then 0 else
          (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α)) =
        ∑' v, if Rv v0 v then 0 else
          (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α) := by
            refine tsum_congr fun v => ?_
            have hviff : Rv v v0 ↔ Rv v0 v :=
              ⟨hsymm v v0, hsymm v0 v⟩
            by_cases hv : Rv v v0
            · rw [if_pos hv, if_pos (hviff.mp hv)]
            · rw [if_neg hv, if_neg (fun hc => hv (hviff.mpr hc))]
      _ ≤ 2 * etaG α Rv μ :=
        far_tilt_le α Rv μ v0 (by linarith) hsymm hhalf
  · exact hMom

end GraphMarkovMatching
