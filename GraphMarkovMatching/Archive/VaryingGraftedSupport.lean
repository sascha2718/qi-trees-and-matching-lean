/-
Support-level tools for the grafted two-law ledger.

The restricted potential must be accompanied by a genuine zero-interface
argument.  This file uses the concrete witness formulation: every charged
source atom has a related charged target atom.  The formulation composes
under mixtures, maps and product cells and immediately kills `zMass`.
-/
import GraphMarkovMatching.Archive.VaryingGraftedInterp
import GraphMarkovMatching.Process.MatchingSupport

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### Semantic consequences for the grafted diagonal -/

variable {V : Type} (Rv : V → V → Prop) (μ : PMF V)
  (νL νR : PMF ℕ) (v0 : V)

lemma graftFreshQ_ne_zero_cases (ν : PMF ℕ) {s : GraftState V}
    (hs : graftFreshQ μ ν s ≠ 0) :
    ∃ v k, s = (v, GraftCounter.ordinary k) ∧
      (μ v : ℝ≥0∞) ≠ 0 ∧ (ν k : ℝ≥0∞) ≠ 0 := by
  rcases s with ⟨v, c⟩
  cases c with
  | ordinary k =>
      refine ⟨v, k, rfl, ?_⟩
      rw [graftFreshQ_ordinary_apply] at hs
      exact mul_ne_zero_iff.mp hs
  | force3Five => simp at hs
  | force5Five => simp at hs

/-- A frozen target at height zero only records its root state; counters are
ignored by `graftLabRel`. -/
lemma graft_forced_zero_support (hrefl : ∀ v, Rv v v)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    {s t : GraftTgt} {cs ct : GraftCounter}
    (hs : graftTgtCounter s = some cs)
    (ht : graftTgtCounter t = some ct) :
    HasMatchingSupport
      (graftInterp μ v0 leftSource νs 0 s)
      (graftInterp μ v0 leftTarget νt 0 t)
      (fullSim (graftLabRel Rv) 0) := by
  have his : graftInterp μ v0 leftSource νs 0 s =
      graftZlaw leftSource μ νs v0 cs 0 := by
    cases s <;> simp_all [graftInterp, graftTgtCounter]
  have hit : graftInterp μ v0 leftTarget νt 0 t =
      graftZlaw leftTarget μ νt v0 ct 0 := by
    cases t <;> simp_all [graftInterp, graftTgtCounter]
  rw [his, hit]
  change HasMatchingSupport (PMF.pure (leaf (v0, cs)))
    (PMF.pure (leaf (v0, ct))) _
  apply matchingSupport_pure
  exact (fullSim_leaf (graftLabRel Rv) _ _).mpr (hrefl v0)

/-- A common offspring component has identical formal children on the two
sides, so diagonal child support gives support of the whole component. -/
lemma graft_commonXi_support (hrefl : ∀ v, Rv v v)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ) (h : ℕ)
    (hdiag : ∀ t : GraftTgt,
      HasMatchingSupport
        (graftInterp μ v0 leftSource νs h t)
        (graftInterp μ v0 leftTarget νt h t)
        (fullSim (graftLabRel Rv) h)) (i : Fin 4) :
    HasMatchingSupport
      (graftXi leftSource μ νs v0 (.ordinary (graftCommonArity i)) h)
      (graftXi leftTarget μ νt v0 (.ordinary (graftCommonArity i)) h)
      (SquareRel (fullSim (graftLabRel Rv) h)) := by
  have _hrefl := hrefl
  rw [graftXi_common_eq_prod μ v0 leftSource νs h i,
    graftXi_common_eq_prod μ v0 leftTarget νt h i]
  exact matchingSupport_prod_square (hdiag (graftCommonPair i).1)
    (hdiag (graftCommonPair i).2)

/-- Height-zero support for a common rooted component with the same root
label and counter. -/
lemma graft_common_muM_zero_support (hrefl : ∀ v, Rv v v)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ) (v : V) (k : ℕ) :
    HasMatchingSupport
      (muM (graftK leftSource μ νs v0) (v, GraftCounter.ordinary k) 0)
      (muM (graftK leftTarget μ νt v0) (v, GraftCounter.ordinary k) 0)
      (fullSim (graftLabRel Rv) 0) := by
  change HasMatchingSupport (PMF.pure (leaf (v, GraftCounter.ordinary k)))
    (PMF.pure (leaf (v, GraftCounter.ordinary k))) _
  apply matchingSupport_pure
  exact (fullSim_leaf (graftLabRel Rv) _ _).mpr (hrefl v)

/-- Successor-height support for one common rooted component. -/
lemma graft_common_muM_succ_support (hrefl : ∀ v, Rv v v)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ) (v : V)
    (h : ℕ) (i : Fin 4)
    (hdiag : ∀ t : GraftTgt,
      HasMatchingSupport
        (graftInterp μ v0 leftSource νs h t)
        (graftInterp μ v0 leftTarget νt h t)
        (fullSim (graftLabRel Rv) h)) :
    HasMatchingSupport
      (muM (graftK leftSource μ νs v0)
        (v, GraftCounter.ordinary (graftCommonArity i)) (h + 1))
      (muM (graftK leftTarget μ νt v0)
        (v, GraftCounter.ordinary (graftCommonArity i)) (h + 1))
      (fullSim (graftLabRel Rv) (h + 1)) := by
  change HasMatchingSupport
    ((graftXi leftSource μ νs v0 (.ordinary (graftCommonArity i)) h).map
      (branch (v, GraftCounter.ordinary (graftCommonArity i))))
    ((graftXi leftTarget μ νt v0 (.ordinary (graftCommonArity i)) h).map
      (branch (v, GraftCounter.ordinary (graftCommonArity i)))) _
  exact matchingSupport_branch (hrefl v)
    (graft_commonXi_support Rv μ v0 hrefl leftSource leftTarget νs νt h
      hdiag i)

/-- Every deterministic grammar symbol preserves diagonal support for one
successor step. -/
lemma graft_forced_diag_succ_support (hrefl : ∀ v, Rv v v)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ) (h : ℕ)
    (hdiag : ∀ t : GraftTgt,
      HasMatchingSupport
        (graftInterp μ v0 leftSource νs h t)
        (graftInterp μ v0 leftTarget νt h t)
        (fullSim (graftLabRel Rv) h))
    {t a b : GraftTgt} (ht : graftForcedPair t = some (a, b)) :
    HasMatchingSupport
      (graftInterp μ v0 leftSource νs (h + 1) t)
      (graftInterp μ v0 leftTarget νt (h + 1) t)
      (fullSim (graftLabRel Rv) (h + 1)) := by
  have hcounter : ∃ c, graftTgtCounter t = some c := by
    cases t <;> simp_all [graftForcedPair, graftTgtCounter]
  obtain ⟨c, hc⟩ := hcounter
  rw [graftInterp_forced_succ μ v0 leftSource νs h hc,
    graftInterp_forced_succ μ v0 leftTarget νt h hc,
    graftChildren_forced_eq_prod μ v0 leftSource νs h ht,
    graftChildren_forced_eq_prod μ v0 leftTarget νt h ht]
  exact matchingSupport_branch (hrefl v0)
    (matchingSupport_prod_square (hdiag a) (hdiag b))

/-- At a positive height, the left exceptional component is supported by
the ordinary right counter-7 component once `M3` is supported by `Z3`. -/
lemma graft_eleven_to_seven_succ_support (hrefl : ∀ v, Rv v v)
    (v : V) (h : ℕ)
    (hM3 : HasMatchingSupport
      (graftInterp μ v0 true νL h .M3)
      (graftInterp μ v0 false νR h .Z3)
      (fullSim (graftLabRel Rv) h))
    (h4 : HasMatchingSupport
      (graftInterp μ v0 true νL h .Z4)
      (graftInterp μ v0 false νR h .Z4)
      (fullSim (graftLabRel Rv) h)) :
    HasMatchingSupport
      (muM (graftK true μ νL v0) (v, GraftCounter.ordinary 11) (h + 1))
      (muM (graftK false μ νR v0) (v, GraftCounter.ordinary 7) (h + 1))
      (fullSim (graftLabRel Rv) (h + 1)) := by
  change HasMatchingSupport
    ((graftXi true μ νL v0 (.ordinary 11) h).map
      (branch (v, GraftCounter.ordinary 11)))
    ((graftXi false μ νR v0 (.ordinary 7) h).map
      (branch (v, GraftCounter.ordinary 7))) _
  rw [graftXi_left_eleven, graftXi_right_seven]
  exact matchingSupport_branch (hrefl v)
    (matchingSupport_prod_square hM3 h4)

/-- Symmetrically, the right exceptional component is supported by the
ordinary left counter-9 component once `M5` is supported by `Z5`. -/
lemma graft_thirteen_to_nine_succ_support (hrefl : ∀ v, Rv v v)
    (v : V) (h : ℕ)
    (h4 : HasMatchingSupport
      (graftInterp μ v0 false νR h .Z4)
      (graftInterp μ v0 true νL h .Z4)
      (fullSim (graftLabRel Rv) h))
    (hM5 : HasMatchingSupport
      (graftInterp μ v0 false νR h .M5)
      (graftInterp μ v0 true νL h .Z5)
      (fullSim (graftLabRel Rv) h)) :
    HasMatchingSupport
      (muM (graftK false μ νR v0) (v, GraftCounter.ordinary 13) (h + 1))
      (muM (graftK true μ νL v0) (v, GraftCounter.ordinary 9) (h + 1))
      (fullSim (graftLabRel Rv) (h + 1)) := by
  change HasMatchingSupport
    ((graftXi false μ νR v0 (.ordinary 13) h).map
      (branch (v, GraftCounter.ordinary 13)))
    ((graftXi true μ νL v0 (.ordinary 9) h).map
      (branch (v, GraftCounter.ordinary 9))) _
  rw [graftXi_right_thirteen, graftXi_left_nine]
  exact matchingSupport_branch (hrefl v)
    (matchingSupport_prod_square h4 hM5)

/-- Fresh left atoms have fresh related atoms on the right: common atoms use
the same counter, while the sole exceptional atom `11` uses counter `7`. -/
lemma graftFresh_LR_support (hrefl : ∀ v, Rv v v) {ζ : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hR7 : (νR 7 : ℝ≥0∞) ≠ 0) :
    HasMatchingSupport (graftFreshQ μ νL) (graftFreshQ μ νR)
      (graftLabRel Rv) := by
  intro s hs
  obtain ⟨v, k, rfl, hμv, hνk⟩ := graftFreshQ_ne_zero_cases μ νL hs
  have hk := hLaw.2.2.2.1 k hνk
  rcases Finset.mem_insert.mp hk with hk11 | hkcore
  · subst k
    refine ⟨(v, GraftCounter.ordinary 7), ?_, hrefl v⟩
    simpa using mul_ne_zero hμv hR7
  · have heq : νL k = νR k := hLaw.2.2.1 k hkcore
    refine ⟨(v, GraftCounter.ordinary k), ?_, hrefl v⟩
    rw [graftFreshQ_ordinary_apply, ← heq]
    exact mul_ne_zero hμv hνk

/-- Fresh right atoms have fresh related atoms on the left: common atoms use
the same counter, while the sole exceptional atom `13` uses counter `9`. -/
lemma graftFresh_RL_support (hrefl : ∀ v, Rv v v) {ζ : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hL9 : (νL 9 : ℝ≥0∞) ≠ 0) :
    HasMatchingSupport (graftFreshQ μ νR) (graftFreshQ μ νL)
      (graftLabRel Rv) := by
  intro s hs
  obtain ⟨v, k, rfl, hμv, hνk⟩ := graftFreshQ_ne_zero_cases μ νR hs
  have hk := hLaw.2.2.2.2 k hνk
  rcases Finset.mem_insert.mp hk with hk13 | hkcore
  · subst k
    refine ⟨(v, GraftCounter.ordinary 9), ?_, hrefl v⟩
    simpa using mul_ne_zero hμv hL9
  · have heq : νL k = νR k := hLaw.2.2.1 k hkcore
    refine ⟨(v, GraftCounter.ordinary k), ?_, hrefl v⟩
    rw [graftFreshQ_ordinary_apply, heq]
    exact mul_ne_zero hμv hνk

/-- At height zero, support of the fresh state laws lifts to support of the
fresh rooted tree laws. -/
lemma graftTlaw_zero_support_of_fresh
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hfresh : HasMatchingSupport (graftFreshQ μ νs) (graftFreshQ μ νt)
      (graftLabRel Rv)) :
    HasMatchingSupport (graftTlaw leftSource μ νs v0 0)
      (graftTlaw leftTarget μ νt v0 0)
      (fullSim (graftLabRel Rv) 0) := by
  rw [graftTlaw, graftTlaw]
  apply matchingSupport_bind
  intro s hs
  obtain ⟨t, ht, hst⟩ := hfresh s hs
  refine ⟨t, ht, ?_⟩
  change HasMatchingSupport (PMF.pure (leaf s)) (PMF.pure (leaf t)) _
  exact matchingSupport_pure ((fullSim_leaf (graftLabRel Rv) s t).mpr hst)

lemma graftInterp_diag_zero_support (hrefl : ∀ v, Rv v v)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ)
    (hfresh : HasMatchingSupport (graftFreshQ μ νs) (graftFreshQ μ νt)
      (graftLabRel Rv)) :
    ∀ t : GraftTgt, HasMatchingSupport
      (graftInterp μ v0 leftSource νs 0 t)
      (graftInterp μ v0 leftTarget νt 0 t)
      (fullSim (graftLabRel Rv) 0) := by
  intro t
  cases t with
  | F =>
      exact graftTlaw_zero_support_of_fresh Rv μ v0 leftSource leftTarget
        νs νt hfresh
  | Z2 =>
      exact graft_forced_zero_support Rv μ v0 hrefl leftSource leftTarget
        νs νt (s := .Z2) (t := .Z2) rfl rfl
  | Z3 =>
      exact graft_forced_zero_support Rv μ v0 hrefl leftSource leftTarget
        νs νt (s := .Z3) (t := .Z3) rfl rfl
  | Z4 =>
      exact graft_forced_zero_support Rv μ v0 hrefl leftSource leftTarget
        νs νt (s := .Z4) (t := .Z4) rfl rfl
  | Z5 =>
      exact graft_forced_zero_support Rv μ v0 hrefl leftSource leftTarget
        νs νt (s := .Z5) (t := .Z5) rfl rfl
  | M3 =>
      exact graft_forced_zero_support Rv μ v0 hrefl leftSource leftTarget
        νs νt (s := .M3) (t := .M3) rfl rfl
  | M5 =>
      exact graft_forced_zero_support Rv μ v0 hrefl leftSource leftTarget
        νs νt (s := .M5) (t := .M5) rfl rfl

lemma elevenThirteenCommonCore_exists_index {k : ℕ}
    (hk : k ∈ elevenThirteenCommonCore) :
    ∃ i : Fin 4, k = graftCommonArity i := by
  simp [elevenThirteenCommonCore] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The complete fresh left law has right support at the next height.  This
is where the exceptional `11` atom is routed to the positive `7` component;
all common atoms are routed to the same arity. -/
lemma graftF_LR_succ_support (hrefl : ∀ v, Rv v v) {ζ : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hR7 : (νR 7 : ℝ≥0∞) ≠ 0) (h : ℕ)
    (hdiag : ∀ t : GraftTgt,
      HasMatchingSupport
        (graftInterp μ v0 true νL h t)
        (graftInterp μ v0 false νR h t)
        (fullSim (graftLabRel Rv) h))
    (hM3 : HasMatchingSupport
      (graftInterp μ v0 true νL h .M3)
      (graftInterp μ v0 false νR h .Z3)
      (fullSim (graftLabRel Rv) h)) :
    HasMatchingSupport (graftTlaw true μ νL v0 (h + 1))
      (graftTlaw false μ νR v0 (h + 1))
      (fullSim (graftLabRel Rv) (h + 1)) := by
  rw [graftTlaw, graftTlaw]
  apply matchingSupport_bind
  intro s hs
  obtain ⟨v, k, rfl, hμv, hνk⟩ := graftFreshQ_ne_zero_cases μ νL hs
  have hk := hLaw.2.2.2.1 k hνk
  rcases Finset.mem_insert.mp hk with hk11 | hkcore
  · subst k
    refine ⟨(v, GraftCounter.ordinary 7), ?_, ?_⟩
    · simpa using mul_ne_zero hμv hR7
    · exact graft_eleven_to_seven_succ_support Rv μ νL νR v0 hrefl v h
        hM3 (hdiag .Z4)
  · obtain ⟨i, rfl⟩ := elevenThirteenCommonCore_exists_index hkcore
    have heq : νL (graftCommonArity i) = νR (graftCommonArity i) :=
      hLaw.2.2.1 _ hkcore
    refine ⟨(v, GraftCounter.ordinary (graftCommonArity i)), ?_, ?_⟩
    · rw [graftFreshQ_ordinary_apply, ← heq]
      exact mul_ne_zero hμv hνk
    · exact graft_common_muM_succ_support Rv μ v0 hrefl true false νL νR
        v h i hdiag

/-- The symmetric fresh-law support step routes the exceptional `13` atom
to the positive left counter-9 component. -/
lemma graftF_RL_succ_support (hrefl : ∀ v, Rv v v) {ζ : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hL9 : (νL 9 : ℝ≥0∞) ≠ 0) (h : ℕ)
    (hdiag : ∀ t : GraftTgt,
      HasMatchingSupport
        (graftInterp μ v0 false νR h t)
        (graftInterp μ v0 true νL h t)
        (fullSim (graftLabRel Rv) h))
    (hM5 : HasMatchingSupport
      (graftInterp μ v0 false νR h .M5)
      (graftInterp μ v0 true νL h .Z5)
      (fullSim (graftLabRel Rv) h)) :
    HasMatchingSupport (graftTlaw false μ νR v0 (h + 1))
      (graftTlaw true μ νL v0 (h + 1))
      (fullSim (graftLabRel Rv) (h + 1)) := by
  rw [graftTlaw, graftTlaw]
  apply matchingSupport_bind
  intro s hs
  obtain ⟨v, k, rfl, hμv, hνk⟩ := graftFreshQ_ne_zero_cases μ νR hs
  have hk := hLaw.2.2.2.2 k hνk
  rcases Finset.mem_insert.mp hk with hk13 | hkcore
  · subst k
    refine ⟨(v, GraftCounter.ordinary 9), ?_, ?_⟩
    · simpa using mul_ne_zero hμv hL9
    · exact graft_thirteen_to_nine_succ_support Rv μ νL νR v0 hrefl v h
        (hdiag .Z4) hM5
  · obtain ⟨i, rfl⟩ := elevenThirteenCommonCore_exists_index hkcore
    have heq : νL (graftCommonArity i) = νR (graftCommonArity i) :=
      hLaw.2.2.1 _ hkcore
    refine ⟨(v, GraftCounter.ordinary (graftCommonArity i)), ?_, ?_⟩
    · rw [graftFreshQ_ordinary_apply, heq]
      exact mul_ne_zero hμv hνk
    · exact graft_common_muM_succ_support Rv μ v0 hrefl false true νR νL
        v h i hdiag

/-- The marker `M3` is supported by the selected counter-3 component whose
fresh child is fixed to counter 5. -/
lemma graft_M3_to_Z3_succ_support (hrefl : ∀ v, Rv v v)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ) (h : ℕ)
    (hp5 : graftFreshQ μ νt (v0, .ordinary 5) ≠ 0)
    (h2 : HasMatchingSupport
      (graftInterp μ v0 leftSource νs h .Z2)
      (graftInterp μ v0 leftTarget νt h .Z2)
      (fullSim (graftLabRel Rv) h))
    (h5 : HasMatchingSupport
      (graftInterp μ v0 leftSource νs h .Z5)
      (graftInterp μ v0 leftTarget νt h .Z5)
      (fullSim (graftLabRel Rv) h)) :
    HasMatchingSupport
      (graftInterp μ v0 leftSource νs (h + 1) .M3)
      (graftInterp μ v0 leftTarget νt (h + 1) .Z3)
      (fullSim (graftLabRel Rv) (h + 1)) := by
  have h5F : HasMatchingSupport
      (graftInterp μ v0 leftSource νs h .Z5)
      (graftInterp μ v0 leftTarget νt h .F)
      (fullSim (graftLabRel Rv) h) := by
    apply matchingSupport_mono_target hp5
      (graftFreshQ_mul_graftZlaw_le_graftTlaw leftTarget μ νt v0 5 h)
      h5
  rw [show graftInterp μ v0 leftSource νs (h + 1) .M3 =
      (prodPMF (graftInterp μ v0 leftSource νs h .Z2)
        (graftInterp μ v0 leftSource νs h .Z5)).map
          (branch (v0, .force3Five)) by
        rw [graftInterp_forced_succ μ v0 leftSource νs h
          (show graftTgtCounter .M3 = some .force3Five by rfl),
          graftChildren_forced_eq_prod μ v0 leftSource νs h
            (show graftForcedPair .M3 = some (.Z2, .Z5) by rfl)],
    show graftInterp μ v0 leftTarget νt (h + 1) .Z3 =
      (prodPMF (graftInterp μ v0 leftTarget νt h .Z2)
        (graftInterp μ v0 leftTarget νt h .F)).map
          (branch (v0, .ordinary 3)) by
        rw [graftInterp_forced_succ μ v0 leftTarget νt h
          (show graftTgtCounter .Z3 = some (.ordinary 3) by rfl),
          graftChildren_forced_eq_prod μ v0 leftTarget νt h
            (show graftForcedPair .Z3 = some (.Z2, .F) by rfl)]]
  exact matchingSupport_branch (hrefl v0)
    (matchingSupport_prod_square h2 h5F)

/-- The second marker then matches the ordinary counter-5 target. -/
lemma graft_M5_to_Z5_succ_support (hrefl : ∀ v, Rv v v)
    (leftSource leftTarget : Bool) (νs νt : PMF ℕ) (h : ℕ)
    (h2 : HasMatchingSupport
      (graftInterp μ v0 leftSource νs h .Z2)
      (graftInterp μ v0 leftTarget νt h .Z2)
      (fullSim (graftLabRel Rv) h))
    (hM3 : HasMatchingSupport
      (graftInterp μ v0 leftSource νs h .M3)
      (graftInterp μ v0 leftTarget νt h .Z3)
      (fullSim (graftLabRel Rv) h)) :
    HasMatchingSupport
      (graftInterp μ v0 leftSource νs (h + 1) .M5)
      (graftInterp μ v0 leftTarget νt (h + 1) .Z5)
      (fullSim (graftLabRel Rv) (h + 1)) := by
  rw [show graftInterp μ v0 leftSource νs (h + 1) .M5 =
      (prodPMF (graftInterp μ v0 leftSource νs h .Z2)
        (graftInterp μ v0 leftSource νs h .M3)).map
          (branch (v0, .force5Five)) by
        rw [graftInterp_forced_succ μ v0 leftSource νs h
          (show graftTgtCounter .M5 = some .force5Five by rfl),
          graftChildren_forced_eq_prod μ v0 leftSource νs h
            (show graftForcedPair .M5 = some (.Z2, .M3) by rfl)],
    show graftInterp μ v0 leftTarget νt (h + 1) .Z5 =
      (prodPMF (graftInterp μ v0 leftTarget νt h .Z2)
        (graftInterp μ v0 leftTarget νt h .Z3)).map
          (branch (v0, .ordinary 5)) by
        rw [graftInterp_forced_succ μ v0 leftTarget νt h
          (show graftTgtCounter .Z5 = some (.ordinary 5) by rfl),
          graftChildren_forced_eq_prod μ v0 leftTarget νt h
            (show graftForcedPair .Z5 = some (.Z2, .Z3) by rfl)]]
  exact matchingSupport_branch (hrefl v0)
    (matchingSupport_prod_square h2 hM3)

/-- The three support statements which close under one recursive step:
formal diagonals in both directions and the two marker-to-ordinary
replacements used by the exceptional components. -/
def GraftSupportAt (h : ℕ) : Prop :=
  (∀ lr t, HasMatchingSupport
    (graftBiSource μ νL νR v0 lr h t)
    (graftBiTarget μ νL νR v0 lr h t)
    (fullSim (graftLabRel Rv) h)) ∧
  (∀ lr, HasMatchingSupport
    (graftBiSource μ νL νR v0 lr h .M3)
    (graftBiTarget μ νL νR v0 lr h .Z3)
    (fullSim (graftLabRel Rv) h)) ∧
  (∀ lr, HasMatchingSupport
    (graftBiSource μ νL νR v0 lr h .M5)
    (graftBiTarget μ νL νR v0 lr h .Z5)
    (fullSim (graftLabRel Rv) h))

/-- Full semantic support for the fixed 11/13 grafted grammar.  The two
nonzero replacement masses give exactly the target atoms needed by the
recursive marker constructions. -/
theorem graftSupportAt_all { ζ : ℝ≥0∞ }
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0) :
    ∀ h, GraftSupportAt Rv μ νL νR v0 h := by
  have hp11' : (νR 7 : ℝ≥0∞) * μ v0 * νR 5 ≠ 0 := by
    simpa [replacementMass] using hp11
  have hp13' : (νL 9 : ℝ≥0∞) * μ v0 * νL 5 ≠ 0 := by
    simpa [replacementMass] using hp13
  have hR7mu : (νR 7 : ℝ≥0∞) * μ v0 ≠ 0 :=
    (mul_ne_zero_iff.mp hp11').1
  have hL9mu : (νL 9 : ℝ≥0∞) * μ v0 ≠ 0 :=
    (mul_ne_zero_iff.mp hp13').1
  have hR7 : (νR 7 : ℝ≥0∞) ≠ 0 := (mul_ne_zero_iff.mp hR7mu).1
  have hL9 : (νL 9 : ℝ≥0∞) ≠ 0 := (mul_ne_zero_iff.mp hL9mu).1
  have hμ0 : (μ v0 : ℝ≥0∞) ≠ 0 := (mul_ne_zero_iff.mp hR7mu).2
  have hR5 : (νR 5 : ℝ≥0∞) ≠ 0 := (mul_ne_zero_iff.mp hp11').2
  have hL5 : (νL 5 : ℝ≥0∞) ≠ 0 := (mul_ne_zero_iff.mp hp13').2
  have hpR5 : graftFreshQ μ νR (v0, GraftCounter.ordinary 5) ≠ 0 := by
    simpa using mul_ne_zero hμ0 hR5
  have hpL5 : graftFreshQ μ νL (v0, GraftCounter.ordinary 5) ≠ 0 := by
    simpa using mul_ne_zero hμ0 hL5
  intro h
  induction h with
  | zero =>
      rw [GraftSupportAt]
      refine ⟨?_, ?_, ?_⟩
      · intro lr
        cases lr with
        | false =>
            simpa [graftBiSource, graftBiTarget] using
              (graftInterp_diag_zero_support Rv μ v0 hrefl false true νR νL
                (graftFresh_RL_support Rv μ νL νR hrefl hLaw hL9))
        | true =>
            simpa [graftBiSource, graftBiTarget] using
              (graftInterp_diag_zero_support Rv μ v0 hrefl true false νL νR
                (graftFresh_LR_support Rv μ νL νR hrefl hLaw hR7))
      · intro lr
        cases lr with
        | false =>
            simpa [graftBiSource, graftBiTarget] using
              (graft_forced_zero_support Rv μ v0 hrefl false true νR νL
                (s := .M3) (t := .Z3) rfl rfl)
        | true =>
            simpa [graftBiSource, graftBiTarget] using
              (graft_forced_zero_support Rv μ v0 hrefl true false νL νR
                (s := .M3) (t := .Z3) rfl rfl)
      · intro lr
        cases lr with
        | false =>
            simpa [graftBiSource, graftBiTarget] using
              (graft_forced_zero_support Rv μ v0 hrefl false true νR νL
                (s := .M5) (t := .Z5) rfl rfl)
        | true =>
            simpa [graftBiSource, graftBiTarget] using
              (graft_forced_zero_support Rv μ v0 hrefl true false νL νR
                (s := .M5) (t := .Z5) rfl rfl)
  | succ h ih =>
      rw [GraftSupportAt] at ih ⊢
      rcases ih with ⟨hdiag, hM3, hM5⟩
      have hdiagLR : ∀ t, HasMatchingSupport
          (graftInterp μ v0 true νL h t)
          (graftInterp μ v0 false νR h t)
          (fullSim (graftLabRel Rv) h) := by
        intro t
        simpa [graftBiSource, graftBiTarget] using hdiag true t
      have hdiagRL : ∀ t, HasMatchingSupport
          (graftInterp μ v0 false νR h t)
          (graftInterp μ v0 true νL h t)
          (fullSim (graftLabRel Rv) h) := by
        intro t
        simpa [graftBiSource, graftBiTarget] using hdiag false t
      have hM3LR : HasMatchingSupport
          (graftInterp μ v0 true νL h .M3)
          (graftInterp μ v0 false νR h .Z3)
          (fullSim (graftLabRel Rv) h) := by
        simpa [graftBiSource, graftBiTarget] using hM3 true
      have hM3RL : HasMatchingSupport
          (graftInterp μ v0 false νR h .M3)
          (graftInterp μ v0 true νL h .Z3)
          (fullSim (graftLabRel Rv) h) := by
        simpa [graftBiSource, graftBiTarget] using hM3 false
      have hM5LR : HasMatchingSupport
          (graftInterp μ v0 true νL h .M5)
          (graftInterp μ v0 false νR h .Z5)
          (fullSim (graftLabRel Rv) h) := by
        simpa [graftBiSource, graftBiTarget] using hM5 true
      have hM5RL : HasMatchingSupport
          (graftInterp μ v0 false νR h .M5)
          (graftInterp μ v0 true νL h .Z5)
          (fullSim (graftLabRel Rv) h) := by
        simpa [graftBiSource, graftBiTarget] using hM5 false
      refine ⟨?_, ?_, ?_⟩
      · intro lr t
        cases lr with
        | false =>
            cases t with
            | F =>
                simpa [graftBiSource, graftBiTarget, graftInterp] using
                  (graftF_RL_succ_support Rv μ νL νR v0 hrefl hLaw hL9 h
                    hdiagRL hM5RL)
            | Z2 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl false true νR νL h
                    hdiagRL (show graftForcedPair .Z2 = some (.F, .F) by rfl))
            | Z3 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl false true νR νL h
                    hdiagRL (show graftForcedPair .Z3 = some (.Z2, .F) by rfl))
            | Z4 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl false true νR νL h
                    hdiagRL (show graftForcedPair .Z4 = some (.Z2, .Z2) by rfl))
            | Z5 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl false true νR νL h
                    hdiagRL (show graftForcedPair .Z5 = some (.Z2, .Z3) by rfl))
            | M3 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl false true νR νL h
                    hdiagRL (show graftForcedPair .M3 = some (.Z2, .Z5) by rfl))
            | M5 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl false true νR νL h
                    hdiagRL (show graftForcedPair .M5 = some (.Z2, .M3) by rfl))
        | true =>
            cases t with
            | F =>
                simpa [graftBiSource, graftBiTarget, graftInterp] using
                  (graftF_LR_succ_support Rv μ νL νR v0 hrefl hLaw hR7 h
                    hdiagLR hM3LR)
            | Z2 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl true false νL νR h
                    hdiagLR (show graftForcedPair .Z2 = some (.F, .F) by rfl))
            | Z3 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl true false νL νR h
                    hdiagLR (show graftForcedPair .Z3 = some (.Z2, .F) by rfl))
            | Z4 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl true false νL νR h
                    hdiagLR (show graftForcedPair .Z4 = some (.Z2, .Z2) by rfl))
            | Z5 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl true false νL νR h
                    hdiagLR (show graftForcedPair .Z5 = some (.Z2, .Z3) by rfl))
            | M3 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl true false νL νR h
                    hdiagLR (show graftForcedPair .M3 = some (.Z2, .Z5) by rfl))
            | M5 =>
                simpa [graftBiSource, graftBiTarget] using
                  (graft_forced_diag_succ_support Rv μ v0 hrefl true false νL νR h
                    hdiagLR (show graftForcedPair .M5 = some (.Z2, .M3) by rfl))
      · intro lr
        cases lr with
        | false =>
            simpa [graftBiSource, graftBiTarget] using
              (graft_M3_to_Z3_succ_support Rv μ v0 hrefl false true νR νL h hpL5
                (hdiagRL .Z2) (hdiagRL .Z5))
        | true =>
            simpa [graftBiSource, graftBiTarget] using
              (graft_M3_to_Z3_succ_support Rv μ v0 hrefl true false νL νR h hpR5
                (hdiagLR .Z2) (hdiagLR .Z5))
      · intro lr
        cases lr with
        | false =>
            simpa [graftBiSource, graftBiTarget] using
              (graft_M5_to_Z5_succ_support Rv μ v0 hrefl false true νR νL h
                (hdiagRL .Z2) hM3RL)
        | true =>
            simpa [graftBiSource, graftBiTarget] using
              (graft_M5_to_Z5_succ_support Rv μ v0 hrefl true false νL νR h
                (hdiagLR .Z2) hM3LR)

/-- A support witness for a formal diagonal kills exactly the structural
zero-interface coordinate used by the corrected ledger. -/
theorem graftBiZMass_eq_zero_of_matching (lr : Bool) (h : ℕ)
    (t : GraftTgt)
    (hsupp : HasMatchingSupport
      (graftBiSource μ νL νR v0 lr h t)
      (graftBiTarget μ νL νR v0 lr h t)
      (fullSim (graftLabRel Rv) h)) :
    graftBiZMass Rv μ νL νR v0 lr h (t, t) = 0 :=
  hsupp.zMass_eq_zero

/-- The zero-interface term on every formal diagonal vanishes under the
actual fixed-example hypotheses; no additional support premise is exposed
to downstream ledger estimates. -/
theorem graftBiZMass_eq_zero { ζ : ℝ≥0∞ }
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (t : GraftTgt) :
    graftBiZMass Rv μ νL νR v0 lr h (t, t) = 0 := by
  apply graftBiZMass_eq_zero_of_matching Rv μ νL νR v0 lr h t
  exact (graftSupportAt_all Rv μ νL νR v0 hrefl hLaw hp11 hp13 h).1 lr t

/-- On every semantic diagonal, raw directed failure is controlled by the
restricted potential alone.  The additional zero-interface term in the
general inequality has been proved to vanish. -/
theorem graftBiFailure_diag_le_phi (α : ℝ) (hα0 : 0 ≤ α) { ζ : ℝ≥0∞ }
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (lr : Bool) (h : ℕ) (t : GraftTgt) :
    graftBiFailure Rv μ νL νR v0 lr h (t, t) ≤
      graftBiPhi α Rv μ νL νR v0 lr h (t, t) := by
  have hrow := graftBiFailure_le_phi_add_zMass α Rv μ νL νR v0
    hα0 lr h (t, t)
  rw [graftBiZMass_eq_zero Rv μ νL νR v0 hrefl hLaw hp11 hp13 lr h t,
    add_zero] at hrow
  exact hrow

/-- Root-law form of the preceding estimate. -/
theorem graftFailure_le_PhiDres_of_law (α : ℝ) (hα0 : 0 ≤ α)
    { ζ : ℝ≥0∞ }
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    (h : ℕ) :
    failureD (graftTlaw true μ νL v0 h) (graftTlaw false μ νR v0 h)
        (fullSim (graftLabRel Rv) h) ≤
      PhiDres α (graftTlaw true μ νL v0 h) (graftTlaw false μ νR v0 h)
        (fullSim (graftLabRel Rv) h) := by
  simpa [graftBiFailure, graftBiPhi, graftBiSource, graftBiTarget,
    graftInterp] using
    (graftBiFailure_diag_le_phi (Rv := Rv) (μ := μ) (νL := νL)
      (νR := νR) (v0 := v0) α hα0 hrefl hLaw hp11 hp13 true h .F)

/-- With the support witness supplied, a formal diagonal screen is paid by
the restricted potential alone. -/
theorem graftBiScreen_cell_mem_none_le_phi (α : ℝ) (hα0 : 0 ≤ α)
    {lr : Bool} {h : ℕ} {sc : GraftScreen}
    (hcell : sc.cell ∈ sc.zlist) (hnorm : sc.norm = none)
    (hsupp : HasMatchingSupport
      (graftBiSource μ νL νR v0 lr h sc.cell)
      (graftBiTarget μ νL νR v0 lr h sc.cell)
      (fullSim (graftLabRel Rv) h)) :
    graftBiScreen α Rv μ νL νR v0 lr h sc ≤
      graftBiPhi α Rv μ νL νR v0 lr h (sc.cell, sc.cell) := by
  have hrow := graftBiScreen_cell_mem_none_le α Rv μ νL νR v0 hα0
    (lr := lr) (h := h) (sc := sc) hcell hnorm
  rw [graftBiZMass_eq_zero_of_matching Rv μ νL νR v0 lr h sc.cell hsupp,
    add_zero] at hrow
  exact hrow

/-- Closed diagonal-screen estimate for the fixed 11/13 example. -/
theorem graftBiScreen_cell_mem_none_le_phi_of_law (α : ℝ) (hα0 : 0 ≤ α)
    { ζ : ℝ≥0∞ }
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair νL νR ζ)
    (hp11 : replacementMass (νR 7) (μ v0) (νR 5) ≠ 0)
    (hp13 : replacementMass (νL 9) (μ v0) (νL 5) ≠ 0)
    {lr : Bool} {h : ℕ} {sc : GraftScreen}
    (hcell : sc.cell ∈ sc.zlist) (hnorm : sc.norm = none) :
    graftBiScreen α Rv μ νL νR v0 lr h sc ≤
      graftBiPhi α Rv μ νL νR v0 lr h (sc.cell, sc.cell) := by
  apply graftBiScreen_cell_mem_none_le_phi (Rv := Rv) (μ := μ)
    (νL := νL) (νR := νR) (v0 := v0) α hα0 hcell hnorm
  exact (graftSupportAt_all Rv μ νL νR v0 hrefl hLaw hp11 hp13 h).1 lr sc.cell

end GraphMarkovMatching
