import GraphMatching.AutBridge
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The exact full-labelling probability recursion and its scalar failure criterion:
`thm:full-probability-recursion` and `thm:iid-scalar-failure` in `prelims.tex`.
-/

namespace GraphMatching

open scoped ENNReal Classical Topology
open MeasureTheory Filter

variable {V X Y : Type*}

private noncomputable def avg (μ : PMF X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, μ x * f x

private lemma avg_mono (μ : PMF X) {f g : X → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    avg μ f ≤ avg μ g := ENNReal.tsum_le_tsum fun x => mul_le_mul_right (h x) _

private lemma avg_const (μ : PMF X) (c : ℝ≥0∞) : avg μ (fun _ => c) = c := by
  simp [avg, ENNReal.tsum_mul_right, μ.tsum_coe]

private lemma avg_le_one (μ : PMF X) {f : X → ℝ≥0∞} (h : ∀ x, f x ≤ 1) :
    avg μ f ≤ 1 := (avg_mono μ h).trans_eq (avg_const μ 1)

private lemma avg_add (μ : PMF X) (f g : X → ℝ≥0∞) :
    avg μ (fun x => f x + g x) = avg μ f + avg μ g := by
  simp only [avg, mul_add, ENNReal.tsum_add]

private lemma avg_mul_const (μ : PMF X) (f : X → ℝ≥0∞) (c : ℝ≥0∞) :
    avg μ (fun x => f x * c) = avg μ f * c := by
  simp only [avg, ← mul_assoc, ENNReal.tsum_mul_right]

private lemma avg_prod (μ : PMF X) (ν : PMF Y) (f : X → ℝ≥0∞) (g : Y → ℝ≥0∞) :
    avg (prodPMF μ ν) (fun p => f p.1 * g p.2) = avg μ f * avg ν g := by
  unfold avg
  simp only [prodPMF_apply]
  convert tsum_prod_split (fun x => μ x * f x) (fun y => ν y * g y) using 1
  congr 1
  funext p
  ring

private lemma avg_sq_ge (μ : PMF X) (f : X → ℝ≥0∞) (hf : ∀ x, f x ≤ 1) :
    avg μ f ^ 2 ≤ avg μ (fun x => f x ^ 2) := by
  have hpoint (p : X × X) : (f p.1 * f p.2) * 2 ≤ f p.1 ^ 2 + f p.2 ^ 2 := by
    have h0 : f p.1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hf p.1)
    have h1 : f p.2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hf p.2)
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (ENNReal.pow_ne_top h0) (ENNReal.pow_ne_top h1)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow]
    nlinarith [sq_nonneg ((f p.1).toReal - (f p.2).toReal)]
  have h := avg_mono (prodPMF μ μ) hpoint
  rw [avg_mul_const, avg_prod, avg_add] at h
  have hleft : avg (prodPMF μ μ) (fun p => f p.1 ^ 2) = avg μ (fun x => f x ^ 2) := by
    simpa [avg_const] using avg_prod μ μ (fun x => f x ^ 2) (fun _ => 1)
  have hright : avg (prodPMF μ μ) (fun p => f p.2 ^ 2) = avg μ (fun x => f x ^ 2) := by
    simpa [avg_const] using avg_prod μ μ (fun _ => 1) (fun x => f x ^ 2)
  rw [hleft, hright, ← pow_two, ← mul_two] at h
  exact (ENNReal.mul_le_mul_iff_left (by norm_num) (by norm_num)).mp h

/-- Probability that two independent labels are related. -/
noncomputable def matchingProb (μ : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * rE μ R x

lemma matchingProb_le_one (μ : PMF X) (R : X → X → Prop) : matchingProb μ R ≤ 1 :=
  avg_le_one μ fun _ => rE_le_one

lemma matchingProb_ne_top (μ : PMF X) (R : X → X → Prop) : matchingProb μ R ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (matchingProb_le_one μ R)

private lemma matchingProb_prod (μ : PMF X) (ν : PMF Y)
    (R : X → X → Prop) (S : Y → Y → Prop) :
    matchingProb (prodPMF μ ν) (ProdRel R S) = matchingProb μ R * matchingProb ν S := by
  simp only [matchingProb, rE_prodPMF]
  exact avg_prod μ ν (rE μ R) (rE ν S)

/-- The mutual acceptance moment `E[a(X₁,X₂)^k]`. -/
noncomputable def overlapMoment (μ : PMF X) (R : X → X → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' p : X × X, μ p.1 * μ p.2 * aOverlap μ R p.1 p.2 ^ k

lemma overlapMoment_le_one (μ : PMF X) (R : X → X → Prop) (k : ℕ) :
    overlapMoment μ R k ≤ 1 := by
  apply avg_le_one (prodPMF μ μ)
  intro p
  exact pow_le_one₀ zero_le ((aOverlap_le_rE_left μ R p.1 p.2).trans rE_le_one)

private lemma matchingProb_square (μ : PMF X) (R : X → X → Prop) :
    matchingProb (prodPMF μ μ) (SquareRel R) + overlapMoment μ R 2 =
      2 * matchingProb μ R ^ 2 := by
  have h := congrArg (avg (prodPMF μ μ))
    (funext fun p : X × X => rE_square_add_aOverlap_sq μ R p.1 p.2)
  rw [avg_add] at h
  have hr : avg (prodPMF μ μ) (fun p => 2 * (rE μ R p.1 * rE μ R p.2)) =
      2 * matchingProb μ R ^ 2 := by
    simp_rw [mul_comm (2 : ℝ≥0∞), avg_mul_const, avg_prod]
    simp only [avg, matchingProb, pow_two]
  exact h.trans hr

/-- The probability `u_h` of matching two independent full height-`h` labellings. -/
noncomputable def fullMatchingProb (μ : PMF V) (R : V → V → Prop) (h : ℕ) : ℝ≥0∞ :=
  matchingProb (fullMu μ h) (fullSim R h)

/-- The additive form of the recursion avoids truncated subtraction in `ℝ≥0∞`. -/
private lemma full_probability_recursion_add (μ : PMF V) (R : V → V → Prop) :
    fullMatchingProb μ R 0 = matchingProb μ R ∧
    ∀ h, fullMatchingProb μ R (h + 1) +
        matchingProb μ R * overlapMoment (fullMu μ h) (fullSim R h) 2 =
      matchingProb μ R * (2 * fullMatchingProb μ R h ^ 2) := by
  constructor
  · change matchingProb μ (fullSim R 0) = matchingProb μ R
    rw [fullSim_zero]
  · intro h
    change matchingProb (prodPMF μ (prodPMF (fullMu μ h) (fullMu μ h)))
      (fullSim R (h + 1)) + _ = _
    rw [fullSim_succ, matchingProb_prod, ← mul_add,
      matchingProb_square]
    rfl

/-- `thm:full-probability-recursion`: the initial value and exact recursion for `u_h`. -/
theorem full_probability_recursion (μ : PMF V) (R : V → V → Prop) :
    (fullMatchingProb μ R 0).toReal = (matchingProb μ R).toReal ∧
    ∀ h, (fullMatchingProb μ R (h + 1)).toReal =
      (matchingProb μ R).toReal * (2 * (fullMatchingProb μ R h).toReal ^ 2 -
        (overlapMoment (fullMu μ h) (fullSim R h) 2).toReal) := by
  refine ⟨congrArg ENNReal.toReal (full_probability_recursion_add μ R).1, fun h => ?_⟩
  have hp : matchingProb μ R ≠ ⊤ := matchingProb_ne_top _ _
  have hu : fullMatchingProb μ R (h + 1) ≠ ⊤ := matchingProb_ne_top _ _
  have ha : overlapMoment (fullMu μ h) (fullSim R h) 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (overlapMoment_le_one _ _ _)
  have hh := congrArg ENNReal.toReal ((full_probability_recursion_add μ R).2 h)
  rw [ENNReal.toReal_add hu (ENNReal.mul_ne_top hp ha)] at hh
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hh
  nlinarith

private lemma overlapMoment_one (μ : PMF X) (R : X → X → Prop)
    (hsymm : ∀ x y, R x y → R y x) :
    overlapMoment μ R 1 = avg μ (fun x => rE μ R x ^ 2) := by
  unfold overlapMoment aOverlap
  simp_rw [pow_one, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  unfold avg
  refine tsum_congr fun y => ?_
  have hsym (x) : R x y ↔ R y x := ⟨hsymm x y, hsymm y x⟩
  simp_rw [hsym]
  calc
    (∑' p : X × X, μ p.1 * μ p.2 * (if R y p.1 ∧ R y p.2 then μ y else 0)) =
        (∑' p : X × X, (if R y p.1 then μ p.1 else 0) *
          (if R y p.2 then μ p.2 else 0)) * μ y := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun p => ?_
      by_cases h0 : R y p.1 <;> by_cases h1 : R y p.2 <;> simp [h0, h1]
    _ = μ y * rE μ R y ^ 2 := by
      rw [tsum_prod_split (fun x => if R y x then μ x else 0)
        (fun x => if R y x then μ x else 0)]
      simp only [rE, pow_two]
      ring

/-- The two mutual acceptance moment bounds in `thm:iid-scalar-failure`. -/
theorem acceptance_moment_bounds (μ : PMF X) (R : X → X → Prop)
    (hsymm : ∀ x y, R x y → R y x) :
    matchingProb μ R ^ 2 ≤ overlapMoment μ R 1 ∧
    matchingProb μ R ^ 4 ≤ overlapMoment μ R 2 := by
  have hfirst : matchingProb μ R ^ 2 ≤ overlapMoment μ R 1 := by
    rw [overlapMoment_one μ R hsymm]
    exact avg_sq_ge μ (rE μ R) fun _ => rE_le_one
  refine ⟨hfirst, ?_⟩
  have hsecond := avg_sq_ge (prodPMF μ μ) (fun p => aOverlap μ R p.1 p.2)
    (fun p => (aOverlap_le_rE_left μ R p.1 p.2).trans rE_le_one)
  change (∑' p : X × X, μ p.1 * μ p.2 * aOverlap μ R p.1 p.2) ^ 2 ≤
    overlapMoment μ R 2 at hsecond
  have hpow : matchingProb μ R ^ 4 ≤ overlapMoment μ R 1 ^ 2 := by
    calc
      matchingProb μ R ^ 4 = (matchingProb μ R ^ 2) ^ 2 := by ring
      _ ≤ overlapMoment μ R 1 ^ 2 := by gcongr
  exact hpow.trans (by simpa only [overlapMoment, pow_one] using hsecond)

private lemma cubic_bound {t : ℝ} (ht : 0 ≤ t) :
    t * (2 - t ^ 2) ≤ 4 * Real.sqrt 6 / 9 := by
  have hs : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 6 ^ 3 = 6 * Real.sqrt 6 := by
    calc
      Real.sqrt 6 ^ 3 = Real.sqrt 6 ^ 2 * Real.sqrt 6 := by ring
      _ = 6 * Real.sqrt 6 := by rw [hs2]
  have hp := mul_nonneg (sq_nonneg (t - Real.sqrt 6 / 3))
    (show 0 ≤ t + 2 * Real.sqrt 6 / 3 by positivity)
  nlinarith [mul_nonneg ht hs]

/-- The scalar polynomial and linear bounds in `thm:iid-scalar-failure`. -/
theorem iid_scalar_bounds (μ : PMF V) (R : V → V → Prop)
    (hsymm : ∀ x y, R x y → R y x) (h : ℕ) :
    (fullMatchingProb μ R (h + 1)).toReal ≤
      (matchingProb μ R).toReal * (fullMatchingProb μ R h).toReal ^ 2 *
        (2 - (fullMatchingProb μ R h).toReal ^ 2) ∧
    (matchingProb μ R).toReal * (fullMatchingProb μ R h).toReal ^ 2 *
        (2 - (fullMatchingProb μ R h).toReal ^ 2) ≤
      (4 * Real.sqrt 6 / 9) * (matchingProb μ R).toReal *
        (fullMatchingProb μ R h).toReal := by
  have hu (k) : fullMatchingProb μ R k ≠ ⊤ := matchingProb_ne_top _ _
  have hp : matchingProb μ R ≠ ⊤ := matchingProb_ne_top _ _
  have ha : overlapMoment (fullMu μ h) (fullSim R h) 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (overlapMoment_le_one _ _ _)
  have hrec := congrArg ENNReal.toReal ((full_probability_recursion_add μ R).2 h)
  rw [ENNReal.toReal_add (hu _) (ENNReal.mul_ne_top hp ha)] at hrec
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hrec
  have hmoment := ENNReal.toReal_mono ha
    (acceptance_moment_bounds (fullMu μ h) (fullSim R h) (fullSim_symm R hsymm h)).2
  simp only [ENNReal.toReal_pow] at hmoment
  change (fullMatchingProb μ R h).toReal ^ 4 ≤ _ at hmoment
  constructor
  · have hm := mul_le_mul_of_nonneg_left hmoment (ENNReal.toReal_nonneg (a := matchingProb μ R))
    nlinarith
  · have hc := mul_le_mul_of_nonneg_left (cubic_bound
      (ENNReal.toReal_nonneg (a := fullMatchingProb μ R h)))
      (mul_nonneg (ENNReal.toReal_nonneg (a := matchingProb μ R))
        (ENNReal.toReal_nonneg (a := fullMatchingProb μ R h)))
    nlinarith

/-- Explicit geometric bound for the full-labelling matching probability. -/
theorem fullMatchingProb_le_geometric (μ : PMF V) (R : V → V → Prop)
    (hsymm : ∀ x y, R x y → R y x) (h : ℕ) :
    (fullMatchingProb μ R h).toReal ≤
      ((4 * Real.sqrt 6 / 9) * (matchingProb μ R).toReal) ^ h *
        (matchingProb μ R).toReal := by
  induction h with
  | zero => rw [pow_zero, one_mul, (full_probability_recursion μ R).1]
  | succ h ih =>
    have hstep := (iid_scalar_bounds μ R hsymm h).1.trans (iid_scalar_bounds μ R hsymm h).2
    have hc : 0 ≤ (4 * Real.sqrt 6 / 9) * (matchingProb μ R).toReal := by positivity
    calc
      (fullMatchingProb μ R (h + 1)).toReal ≤
          ((4 * Real.sqrt 6 / 9) * (matchingProb μ R).toReal) *
            (fullMatchingProb μ R h).toReal := hstep
      _ ≤ ((4 * Real.sqrt 6 / 9) * (matchingProb μ R).toReal) *
          (((4 * Real.sqrt 6 / 9) * (matchingProb μ R).toReal) ^ h *
            (matchingProb μ R).toReal) := mul_le_mul_of_nonneg_left ih hc
      _ = _ := by rw [pow_succ]; ring

/-- Below the threshold `3√6/8`, full-labelling matching probabilities tend to zero. -/
theorem fullMatchingProb_tendsto_zero (μ : PMF V) (R : V → V → Prop)
    (hsymm : ∀ x y, R x y → R y x)
    (hp : (matchingProb μ R).toReal < 3 * Real.sqrt 6 / 8) :
    Tendsto (fullMatchingProb μ R) atTop (𝓝 0) := by
  have hs : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 ≤ (4 * Real.sqrt 6 / 9) * (matchingProb μ R).toReal := by positivity
  have hc1 : (4 * Real.sqrt 6 / 9) * (matchingProb μ R).toReal < 1 := by
    have hh := mul_lt_mul_of_pos_left hp (show 0 < 4 * Real.sqrt 6 / 9 by positivity)
    nlinarith
  have ht : Tendsto (fun h => (fullMatchingProb μ R h).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fullMatchingProb_le_geometric μ R hsymm)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const
      (matchingProb μ R).toReal
  exact (ENNReal.tendsto_toReal_zero_iff (fun _ => matchingProb_ne_top _ _)).mp ht

lemma prodPMF_toMeasure_rel [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    (μ : PMF X) (R : X → X → Prop) :
    (prodPMF μ μ).toMeasure {p : X × X | R p.1 p.2} = matchingProb μ R := by
  rw [(prodPMF μ μ).toMeasure_apply ((Set.to_countable _).measurableSet), ENNReal.tsum_prod']
  unfold matchingProb
  refine tsum_congr fun x => ?_
  rw [rE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  by_cases h : R x y <;> simp [h]

/-- The infinite failure conclusion of `thm:iid-scalar-failure`, for any pair of consistent
labellings with the independent i.i.d. finite-dimensional laws. -/
theorem iid_scalar_failure_of_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : PMF V) (R : V → V → Prop) (hsymm : ∀ x y, R x y → R y x)
    (hp : (matchingProb μ R).toReal < 3 * Real.sqrt 6 / 8)
    (X Y : (h : ℕ) → Ω → FullLab V h)
    (hX : ∀ h ω, restrictLab h (X (h + 1) ω) = X h ω)
    (hY : ∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω)
    (hpair : ∀ h, Measurable (fun ω => (X h ω, Y h ω)))
    (hlaw : ∀ h, P.map (fun ω => (X h ω, Y h ω)) =
      (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) :
    P {ω | ∃ g : treeGraphInf ≃g treeGraphInf, g [] = [] ∧
      ∀ s : List Bool, R (coord (g s).length (X (g s).length ω) (g s))
        (coord s.length (Y s.length ω) s)} = 0 := by
  apply le_antisymm ?_ bot_le
  apply ge_of_tendsto' (fullMatchingProb_tendsto_zero μ R hsymm hp)
  intro h
  have hfinite : P {ω | fullSim R h (X h ω) (Y h ω)} = fullMatchingProb μ R h := by
    rw [show {ω | fullSim R h (X h ω) (Y h ω)} =
      (fun ω => (X h ω, Y h ω)) ⁻¹' {p | fullSim R h p.1 p.2} from rfl,
      ← Measure.map_apply (hpair h) ((Set.to_countable _).measurableSet), hlaw h,
      prodPMF_toMeasure_rel]
    rfl
  rw [← hfinite]
  apply measure_mono
  intro ω hω
  have hi := (infMatch_iff_graphAut R (fun h => X h ω) (fun h => Y h ω)
    (fun h => hX h ω) (fun h => hY h ω)).mpr hω
  exact ⟨hi.choose h, hi.choose_spec.2 h⟩

private lemma coord_readLab_at_depth (f : List Bool → V) (s : List Bool) :
    coord s.length (readLab f s.length) s = f s := by
  induction s generalizing f with
  | nil => rfl
  | cons b s ih =>
    cases b
    · exact ih (fun t => f (false :: t))
    · exact ih (fun t => f (true :: t))

/-- Two independent i.i.d. labellings of the infinite binary tree almost surely admit no
matching root-fixing graph automorphism when `p_c < 3√6/8` (`thm:iid-scalar-failure`). -/
theorem iid_scalar_failure [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : PMF V) (R : V → V → Prop) (hsymm : ∀ x y, R x y → R y x)
    (hp : (matchingProb μ R).toReal < 3 * Real.sqrt 6 / 8) :
    ((Measure.infinitePi (fun _ : List Bool => μ.toMeasure)).prod
      (Measure.infinitePi (fun _ : List Bool => μ.toMeasure)))
      {ω : (List Bool → V) × (List Bool → V) |
        ∃ g : treeGraphInf ≃g treeGraphInf, g [] = [] ∧
          ∀ s : List Bool, R (ω.1 (g s)) (ω.2 s)} = 0 := by
  have hlaw : ∀ h, ((Measure.infinitePi (fun _ : List Bool => μ.toMeasure)).prod
      (Measure.infinitePi (fun _ : List Bool => μ.toMeasure))).map
        (fun ω : (List Bool → V) × (List Bool → V) => (readLab ω.1 h, readLab ω.2 h)) =
      (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure := by
    intro h
    rw [show (fun ω : (List Bool → V) × (List Bool → V) => (readLab ω.1 h, readLab ω.2 h)) =
      Prod.map (fun f => readLab f h) (fun f => readLab f h) from rfl,
      ← Measure.map_prod_map _ _ (measurable_readLab h) (measurable_readLab h),
      map_readLab, toMeasure_prodPMF]
  have hh := iid_scalar_failure_of_law _ μ R hsymm hp
    (fun h (ω : (List Bool → V) × (List Bool → V)) => readLab ω.1 h)
    (fun h (ω : (List Bool → V) × (List Bool → V)) => readLab ω.2 h)
    (fun h ω => restrictLab_readLab h ω.1) (fun h ω => restrictLab_readLab h ω.2)
    (fun h => ((measurable_readLab h).comp measurable_fst).prodMk
      ((measurable_readLab h).comp measurable_snd)) hlaw
  simpa only [coord_readLab_at_depth] using hh

end GraphMatching
