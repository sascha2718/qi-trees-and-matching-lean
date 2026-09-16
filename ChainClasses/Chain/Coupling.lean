import ChainClasses.Chain.Quantise
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
`sec:chain-coupling` of `matching_classes_simple.tex`: `thm:chain-coupling`,
the chain classes coupled across two laws.

* `cgamma`: the exponent ratio `γ = log θ₁ / log θ₁'`, with `cgamma_pos` and
  `rpow_cgamma` (`θ₁ = (θ₁')^γ`).
* `tQ` and `threshold`: the crossing points `t_k = 1 + γ(D^k - 1)` and
  `eq:threshold`; `DQ` is the cut point `D_k' = ⌊t_k⌋`, with `DQ_zero`,
  `DQ_lt_succ` and `succ_le_DQ`; `atom` is `eq:atom`.
* `betaQ`: the split fraction `β_k`, with `betaQ_nonneg`, `betaQ_lt_one` and
  `betaQ_zero`.
* `ellQ`: the class map `ℓ'`.  Clause (i) of `thm:chain-coupling` is
  `ellQ_interior` and `ellQ_endpoint` together with the sandwich
  `ellQ_sandwich_lower`, `ellQ_sandwich_upper`; `ellQ_mono_left` is the
  monotonicity in the length.
* Clause (iii) is `DQ_ratio`.
* Clause (ii) is `coupling_law`: `geomPMF` packages the second law
  `ℙ(λ' = n) = (θ₁')^{n-1}(1 - θ₁')`, the uniform variable `U` enters as
  `volume.restrict (Set.Ico 0 1)`, `coupling_sum` is the scalar computation
  of the proof, and `coupling_law` is the identity `ℙ(ℓ'(λ', U) = k) = p^{(D)}_k`.

Throughout, `a` is the paper's `θ₁` and `b` its `θ₁'`.
-/

namespace ChainClasses

open scoped ENNReal
open MeasureTheory

/-! ### The exponent ratio and the cut points -/

variable {a b : ℝ} {D : ℕ}

/-- The exponent ratio `γ = log θ₁ / log θ₁'` of `thm:chain-coupling`. -/
noncomputable def cgamma (a b : ℝ) : ℝ := Real.log a / Real.log b

lemma cgamma_pos (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) : 0 < cgamma a b :=
  div_pos_iff.mpr (Or.inr ⟨Real.log_neg ha ha1, Real.log_neg hb hb1⟩)

/-- The defining property of the ratio: `θ₁ = (θ₁')^γ`. -/
lemma rpow_cgamma (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) : b ^ cgamma a b = a := by
  unfold cgamma
  rw [Real.log_div_log]
  exact Real.rpow_logb hb hb1.ne ha

/-- The crossing points `t_k = 1 + γ(D^k - 1)` of the proof of
`thm:chain-coupling`: the tail of the second law reaches at `t_k` the value
the tail of the first law reaches at `D^k`. -/
noncomputable def tQ (a b : ℝ) (D k : ℕ) : ℝ := 1 + cgamma a b * ((D : ℝ) ^ k - 1)

lemma tQ_zero (a b : ℝ) (D : ℕ) : tQ a b D 0 = 1 := by simp [tQ]

lemma one_le_tQ (hγ : 0 < cgamma a b) (hD : 2 ≤ D) (k : ℕ) : 1 ≤ tQ a b D k := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  have h1 : (1 : ℝ) ≤ (D : ℝ) ^ k := one_le_pow₀ hD1
  have h2 : 0 ≤ cgamma a b * ((D : ℝ) ^ k - 1) := mul_nonneg hγ.le (by linarith)
  simp only [tQ]
  linarith

/-- The cut points `D_k' = ⌊t_k⌋` of `thm:chain-coupling`. -/
noncomputable def DQ (a b : ℝ) (D k : ℕ) : ℕ := ⌊tQ a b D k⌋₊

lemma DQ_zero (a b : ℝ) (D : ℕ) : DQ a b D 0 = 1 := by
  simp [DQ, tQ_zero]

lemma one_le_DQ (hγ : 0 < cgamma a b) (hD : 2 ≤ D) (k : ℕ) : 1 ≤ DQ a b D k :=
  Nat.le_floor (by exact_mod_cast one_le_tQ hγ hD k)

lemma DQ_le_tQ (hγ : 0 < cgamma a b) (hD : 2 ≤ D) (k : ℕ) :
    (DQ a b D k : ℝ) ≤ tQ a b D k :=
  Nat.floor_le (le_trans zero_le_one (one_le_tQ hγ hD k))

lemma tQ_lt_DQ_add_one (a b : ℝ) (D k : ℕ) : tQ a b D k < (DQ a b D k : ℝ) + 1 :=
  Nat.lt_floor_add_one _

/-- The cut points step by at least one: `t_{k+1} - t_k = γ D^k (D-1) ≥ 1`. -/
lemma DQ_lt_succ (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) : DQ a b D k < DQ a b D (k + 1) := by
  have hγ := cgamma_pos ha ha1 hb hb1
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  have hDk : (1 : ℝ) ≤ (D : ℝ) ^ k := one_le_pow₀ hD1
  have hstep : tQ a b D k + 1 ≤ tQ a b D (k + 1) := by
    have h2 : 1 * 1 ≤ cgamma a b * ((D : ℝ) - 1) * (D : ℝ) ^ k :=
      mul_le_mul hgD hDk zero_le_one (le_trans zero_le_one hgD)
    have h3 : cgamma a b * ((D : ℝ) ^ (k + 1) - 1) - cgamma a b * ((D : ℝ) ^ k - 1)
        = cgamma a b * ((D : ℝ) - 1) * (D : ℝ) ^ k := by
      rw [pow_succ]
      ring
    simp only [tQ]
    linarith
  have h0 : 0 ≤ tQ a b D k := le_trans zero_le_one (one_le_tQ hγ hD k)
  have h4 : DQ a b D k + 1 ≤ DQ a b D (k + 1) := by
    calc DQ a b D k + 1 = ⌊tQ a b D k + 1⌋₊ := (Nat.floor_add_one h0).symm
      _ ≤ ⌊tQ a b D (k + 1)⌋₊ := Nat.floor_mono hstep
      _ = DQ a b D (k + 1) := rfl
  omega

lemma DQ_strictMono (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) : StrictMono (DQ a b D) :=
  strictMono_nat_of_lt_succ (DQ_lt_succ ha ha1 hb hb1 hD hgD)

/-- The cut points grow strictly from `D_0' = 1`, so `k + 1 ≤ D_k'`. -/
lemma succ_le_DQ (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) : k + 1 ≤ DQ a b D k := by
  induction k with
  | zero =>
    have := DQ_zero a b D
    omega
  | succ k ih =>
    have := DQ_lt_succ ha ha1 hb hb1 hD hgD k
    omega

/-- `eq:threshold`: `θ₁^{D^k-1} = (θ₁')^{t_k-1}`, through `θ₁ = (θ₁')^γ`. -/
lemma threshold (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D) (k : ℕ) :
    tailB a D k = b ^ (tQ a b D k - 1) := by
  have h1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  have hcast : ((D ^ k - 1 : ℕ) : ℝ) = (D : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have key : (b ^ cgamma a b) ^ (D ^ k - 1) = b ^ (tQ a b D k - 1) := by
    rw [← Real.rpow_natCast (b ^ cgamma a b) (D ^ k - 1), ← Real.rpow_mul hb.le, hcast]
    congr 1
    simp only [tQ]
    ring
  calc tailB a D k = a ^ (D ^ k - 1) := rfl
    _ = (b ^ cgamma a b) ^ (D ^ k - 1) := by rw [rpow_cgamma ha hb hb1]
    _ = b ^ (tQ a b D k - 1) := key

/-- `eq:atom`: the threshold `θ₁^{D^k-1}` falls inside the atom of the second
law at `D_k'`. -/
lemma atom (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D) (k : ℕ) :
    b ^ DQ a b D k < tailB a D k ∧ tailB a D k ≤ b ^ (DQ a b D k - 1) := by
  have hγ := cgamma_pos ha ha1 hb hb1
  have hDQ1 := one_le_DQ hγ hD k
  have hfl := DQ_le_tQ hγ hD k
  have hfu := tQ_lt_DQ_add_one a b D k
  constructor
  · rw [threshold ha hb hb1 hD k, ← Real.rpow_natCast b (DQ a b D k),
      Real.rpow_lt_rpow_left_iff_of_base_lt_one hb hb1]
    linarith
  · rw [threshold ha hb hb1 hD k, ← Real.rpow_natCast b (DQ a b D k - 1),
      Real.rpow_le_rpow_left_iff_of_base_lt_one hb hb1, Nat.cast_sub hDQ1]
    push_cast
    linarith

/-! ### The split fraction -/

/-- The split fraction `β_k` of `thm:chain-coupling`: the part of the atom of
the second law at `D_k'` lying above the threshold. -/
noncomputable def betaQ (a b : ℝ) (D k : ℕ) : ℝ :=
  (b ^ (DQ a b D k - 1) - tailB a D k) / (b ^ (DQ a b D k - 1) - b ^ DQ a b D k)

lemma betaQ_den_pos (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (k : ℕ) : 0 < b ^ (DQ a b D k - 1) - b ^ DQ a b D k := by
  have h1 := one_le_DQ (cgamma_pos ha ha1 hb hb1) hD k
  exact sub_pos.mpr (pow_lt_pow_right_of_lt_one₀ hb hb1 (by omega))

lemma betaQ_nonneg (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (k : ℕ) : 0 ≤ betaQ a b D k :=
  div_nonneg (sub_nonneg.mpr (atom ha ha1 hb hb1 hD k).2)
    (betaQ_den_pos ha ha1 hb hb1 hD k).le

lemma betaQ_lt_one (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (k : ℕ) : betaQ a b D k < 1 := by
  unfold betaQ
  rw [div_lt_one (betaQ_den_pos ha ha1 hb hb1 hD k)]
  have := (atom ha ha1 hb hb1 hD k).1
  linarith

lemma betaQ_zero (a b : ℝ) (D : ℕ) : betaQ a b D 0 = 0 := by
  simp [betaQ, DQ_zero, tailB_zero]

lemma betaQ_mul_den (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (k : ℕ) :
    betaQ a b D k * (b ^ (DQ a b D k - 1) - b ^ DQ a b D k)
      = b ^ (DQ a b D k - 1) - tailB a D k :=
  div_mul_cancel₀ _ (betaQ_den_pos ha ha1 hb hb1 hD k).ne'

/-! ### The class map and clause (i) -/

/-- The class map `ℓ'` of `thm:chain-coupling`: the greatest `k` whose cut
point the length `n` has passed, the tie at `n = D_k'` broken by `u` against
`β_k`. -/
noncomputable def ellQ (a b : ℝ) (D : ℕ) (n : ℕ) (u : ℝ) : ℕ :=
  Nat.findGreatest (fun k => DQ a b D k < n ∨ (DQ a b D k = n ∧ betaQ a b D k ≤ u)) n

/-- The padding value `n = 0` is sent to class `0`. -/
lemma ellQ_zero (a b : ℝ) (D : ℕ) (u : ℝ) : ellQ a b D 0 u = 0 := rfl

/-- The defining predicate of `ellQ` holds at `k = 0`. -/
lemma ellQ_pred_zero {n : ℕ} {u : ℝ} (hn : 1 ≤ n) (hu : 0 ≤ u) :
    DQ a b D 0 < n ∨ (DQ a b D 0 = n ∧ betaQ a b D 0 ≤ u) := by
  rw [DQ_zero, betaQ_zero]
  rcases Nat.lt_or_ge 1 n with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by omega, hu⟩

/-- `ℓ'` is nondecreasing in the length. -/
lemma ellQ_mono_left {n n' : ℕ} (h : n ≤ n') (u : ℝ) :
    ellQ a b D n u ≤ ellQ a b D n' u := by
  unfold ellQ
  refine Nat.findGreatest_mono (fun j hj => ?_) h
  rcases hj with hlt | ⟨heq, hu⟩
  · exact Or.inl (lt_of_lt_of_le hlt h)
  · rcases h.eq_or_lt with rfl | hlt'
    · exact Or.inr ⟨heq, hu⟩
    · exact Or.inl (by omega)

/-- For a fixed length the class map is nondecreasing in `u`. -/
lemma ellQ_mono_u (a b : ℝ) (D n : ℕ) : Monotone (fun u : ℝ => ellQ a b D n u) := by
  intro u v huv
  show ellQ a b D n u ≤ ellQ a b D n v
  unfold ellQ
  exact Nat.findGreatest_mono (fun j hj => hj.imp id fun h => ⟨h.1, h.2.trans huv⟩) le_rfl

/-- Clause (i), interior: strictly between cut points the class is forced. -/
lemma ellQ_interior (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) {k n : ℕ} (u : ℝ)
    (h1 : DQ a b D k < n) (h2 : n < DQ a b D (k + 1)) : ellQ a b D n u = k := by
  have hmono := DQ_strictMono ha ha1 hb hb1 hD hgD
  have hk1 := succ_le_DQ ha ha1 hb hb1 hD hgD k
  unfold ellQ
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => Or.inl h1, ?_⟩
  rintro j hkj hjn hP
  have hDj : DQ a b D (k + 1) ≤ DQ a b D j := hmono.monotone (by omega)
  rcases hP with hlt | ⟨heq, -⟩ <;> omega

/-- Clause (i), endpoint: at the cut point `n = D_{k+1}'` the variable `u`
splits the class between `k` and `k + 1` at `β_{k+1}`. -/
lemma ellQ_endpoint (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) {k n : ℕ} (u : ℝ)
    (hn : DQ a b D (k + 1) = n) :
    (u < betaQ a b D (k + 1) → ellQ a b D n u = k) ∧
    (betaQ a b D (k + 1) ≤ u → ellQ a b D n u = k + 1) := by
  have hmono := DQ_strictMono ha ha1 hb hb1 hD hgD
  have hk2 := succ_le_DQ ha ha1 hb hb1 hD hgD (k + 1)
  have hkk : DQ a b D k < DQ a b D (k + 1) := hmono (by omega)
  constructor
  · intro hu
    unfold ellQ
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, fun _ => Or.inl (by omega), ?_⟩
    rintro j hkj hjn hP
    rcases (by omega : k + 1 ≤ j).eq_or_lt with rfl | hj2
    · rcases hP with hlt | ⟨-, hu'⟩
      · omega
      · exact absurd hu' (not_le.mpr hu)
    · have hDj : DQ a b D (k + 1) < DQ a b D j := hmono hj2
      rcases hP with hlt | ⟨heq, -⟩ <;> omega
  · intro hu
    unfold ellQ
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, fun _ => Or.inr ⟨hn, hu⟩, ?_⟩
    rintro j hk1j hjn hP
    have hDj : DQ a b D (k + 1) < DQ a b D j := hmono hk1j
    rcases hP with hlt | ⟨heq, -⟩ <;> omega

/-- The left endpoint of class `0`: length `1` always lies in class `0`. -/
lemma ellQ_one (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (u : ℝ) : ellQ a b D 1 u = 0 := by
  have h2 := succ_le_DQ ha ha1 hb hb1 hD hgD 1
  unfold ellQ
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun h => absurd rfl h, ?_⟩
  rintro j h0j hj1 hP
  have hj : j = 1 := by omega
  subst hj
  rcases hP with hlt | ⟨heq, -⟩ <;> omega

/-- Clause (i), lower inclusion: the open interval between consecutive cut
points lies inside the class. -/
lemma ellQ_sandwich_lower (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) {k n : ℕ} (u : ℝ)
    (h1 : DQ a b D k < n) (h2 : n < DQ a b D (k + 1)) : 1 ≤ n ∧ ellQ a b D n u = k := by
  have := one_le_DQ (cgamma_pos ha ha1 hb hb1) hD k
  exact ⟨by omega, ellQ_interior ha ha1 hb hb1 hD hgD u h1 h2⟩

/-- Clause (i), upper inclusion: the class lies inside the closed interval
between consecutive cut points. -/
lemma ellQ_sandwich_upper (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) {k n : ℕ} {u : ℝ} (hn : 1 ≤ n)
    (h : ellQ a b D n u = k) : DQ a b D k ≤ n ∧ n ≤ DQ a b D (k + 1) := by
  have hk2 := succ_le_DQ ha ha1 hb hb1 hD hgD (k + 1)
  constructor
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have := DQ_zero a b D
      omega
    · unfold ellQ at h
      have hP := Nat.findGreatest_of_ne_zero h (by omega)
      rcases hP with h' | ⟨h', -⟩ <;> omega
  · by_contra hcon
    have hlt : DQ a b D (k + 1) < n := by omega
    have hge : k + 1 ≤ ellQ a b D n u := by
      unfold ellQ
      exact Nat.le_findGreatest (by omega) (Or.inl hlt)
    omega

/-- Every length `n ≥ 1` lies between consecutive cut points. -/
lemma DQ_exists_class (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ j, DQ a b D j ≤ n ∧ n < DQ a b D (j + 1) := by
  have h0 : DQ a b D 0 ≤ n := by
    have := DQ_zero a b D
    omega
  refine ⟨Nat.findGreatest (fun i => DQ a b D i ≤ n) n,
    Nat.findGreatest_spec (P := fun i => DQ a b D i ≤ n) (Nat.zero_le n) h0, ?_⟩
  by_contra hcon
  have hle : DQ a b D (Nat.findGreatest (fun i => DQ a b D i ≤ n) n + 1) ≤ n := by omega
  have hj1n : Nat.findGreatest (fun i => DQ a b D i ≤ n) n + 1 ≤ n := by
    have := succ_le_DQ ha ha1 hb hb1 hD hgD
      (Nat.findGreatest (fun i => DQ a b D i ≤ n) n + 1)
    omega
  have := Nat.le_findGreatest (P := fun i => DQ a b D i ≤ n) hj1n hle
  omega

/-! ### Clause (iii) -/

/-- Clause (iii) of `thm:chain-coupling`: the cut points track the powers
`D^k` within the fixed factors `min(1, γ/2)` and `max(1, γ)`. -/
theorem DQ_ratio (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (k : ℕ) :
    min 1 (cgamma a b / 2) * (D : ℝ) ^ k ≤ (DQ a b D k : ℝ) ∧
    (DQ a b D k : ℝ) ≤ max 1 (cgamma a b) * (D : ℝ) ^ k := by
  have hγ := cgamma_pos ha ha1 hb hb1
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  have hDk1 : (1 : ℝ) ≤ (D : ℝ) ^ k := one_le_pow₀ hD1
  have hfl := DQ_le_tQ hγ hD k
  have hfu := tQ_lt_DQ_add_one a b D k
  simp only [tQ] at hfl hfu
  constructor
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [DQ_zero]
      simp only [pow_zero, mul_one, Nat.cast_one]
      exact min_le_left _ _
    · have hDk2 : (2 : ℝ) ≤ (D : ℝ) ^ k := by
        calc (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
          _ ≤ (D : ℝ) ^ k := le_self_pow₀ hD1 (by omega)
      have h1 : min 1 (cgamma a b / 2) * (D : ℝ) ^ k ≤ cgamma a b / 2 * (D : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
      have h2 : 0 ≤ cgamma a b * ((D : ℝ) ^ k - 2) := mul_nonneg hγ.le (by linarith)
      nlinarith [h1, h2, hfu]
  · have hmax1 : (1 : ℝ) ≤ max 1 (cgamma a b) := le_max_left _ _
    have h1 : cgamma a b * ((D : ℝ) ^ k - 1) ≤ max 1 (cgamma a b) * ((D : ℝ) ^ k - 1) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    nlinarith [hfl, h1, hmax1]

/-! ### The second law -/

/-- The mass `ℙ(λ' = n) = (θ₁')^{n-1}(1 - θ₁')` of the second chain law,
padded with `0` at `n = 0`. -/
noncomputable def gmass (b : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else b ^ (n - 1) * (1 - b)

lemma gmass_nonneg (hb : 0 ≤ b) (hb1 : b ≤ 1) (n : ℕ) : 0 ≤ gmass b n := by
  unfold gmass
  split
  · exact le_refl 0
  · exact mul_nonneg (pow_nonneg hb _) (by linarith)

lemma gmass_succ (b : ℝ) (n : ℕ) : gmass b (n + 1) = b ^ n * (1 - b) := by
  simp [gmass]

lemma gmass_summable (hb : 0 ≤ b) (hb1 : b < 1) : Summable (gmass b) := by
  have h1 : Summable (fun n : ℕ => b ^ n * (1 - b)) :=
    (summable_geometric_of_lt_one hb hb1).mul_right _
  exact (summable_nat_add_iff 1).mp (h1.congr fun n => (gmass_succ b n).symm)

/-- The second law has total mass one. -/
lemma gmass_tsum (hb : 0 ≤ b) (hb1 : b < 1) : ∑' n, gmass b n = 1 := by
  have h1 : Summable (fun n : ℕ => b ^ n * (1 - b)) :=
    (summable_geometric_of_lt_one hb hb1).mul_right _
  have h2 : Summable (fun n : ℕ => gmass b (n + 1)) :=
    h1.congr fun n => (gmass_succ b n).symm
  rw [tsum_eq_zero_add' h2, show gmass b 0 = 0 from rfl, zero_add]
  calc ∑' n : ℕ, gmass b (n + 1) = ∑' n : ℕ, b ^ n * (1 - b) :=
        tsum_congr fun n => gmass_succ b n
    _ = (∑' n : ℕ, b ^ n) * (1 - b) := tsum_mul_right
    _ = (1 - b)⁻¹ * (1 - b) := by rw [tsum_geometric_of_lt_one hb hb1]
    _ = 1 := inv_mul_cancel₀ (by linarith : (0 : ℝ) < 1 - b).ne'

/-- The second law has total mass one, in `ℝ≥0∞`. -/
lemma gmass_tsum_ennreal (hb : 0 ≤ b) (hb1 : b < 1) :
    ∑' n, ENNReal.ofReal (gmass b n) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (gmass_nonneg hb hb1.le) (gmass_summable hb hb1),
    gmass_tsum hb hb1, ENNReal.ofReal_one]

/-- The second chain law `ℙ(λ' = n) = (θ₁')^{n-1}(1 - θ₁')` as a `PMF ℕ`. -/
noncomputable def geomPMF (hb : 0 < b) (hb1 : b < 1) : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (gmass b n), by
    have h := ENNReal.summable.hasSum (f := fun n => ENNReal.ofReal (gmass b n))
    rwa [gmass_tsum_ennreal hb.le hb1] at h⟩

lemma geomPMF_apply (hb : 0 < b) (hb1 : b < 1) (n : ℕ) :
    geomPMF hb hb1 n = ENNReal.ofReal (gmass b n) := rfl

/-! ### Clause (ii): the law of the coupled class -/

/-- The `u`-measure of the fibre of `ℓ'` over the length `n` inside class `k`:
full weight strictly between the cut points, the split fractions at the two
endpoints. -/
noncomputable def uWeight (a b : ℝ) (D k n : ℕ) : ℝ :=
  if n = DQ a b D k then 1 - betaQ a b D k
  else if n = DQ a b D (k + 1) then betaQ a b D (k + 1)
  else if DQ a b D k < n ∧ n < DQ a b D (k + 1) then 1 else 0

lemma uWeight_nonneg (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (k n : ℕ) : 0 ≤ uWeight a b D k n := by
  unfold uWeight
  split
  · have := betaQ_lt_one ha ha1 hb hb1 hD k
    linarith
  · split
    · exact betaQ_nonneg ha ha1 hb hb1 hD (k + 1)
    · split
      · exact zero_le_one
      · exact le_refl 0

/-- The telescoping geometric block:
`∑_{A ≤ n < B} b^{n-1}(1-b) = b^{A-1} - b^{B-1}`. -/
lemma geom_block_sum (b : ℝ) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ico A B, b ^ (n - 1) * (1 - b) = b ^ (A - 1) - b ^ (B - 1) := by
  set f : ℕ → ℝ := fun j => b ^ (A + j - 1) with hf
  have hcong : ∑ n ∈ Finset.Ico A B, b ^ (n - 1) * (1 - b)
      = ∑ i ∈ Finset.range (B - A), (f i - f (i + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hstep : b ^ (A + i) = b ^ (A + i - 1) * b := by
      rw [← pow_succ]
      congr 1
      omega
    have hidx : A + (i + 1) - 1 = A + i := by omega
    simp only [hf, hidx]
    rw [hstep]
    ring
  rw [hcong, Finset.sum_range_sub']
  simp only [hf]
  have h1 : A + 0 - 1 = A - 1 := by omega
  have h2 : A + (B - A) - 1 = B - 1 := by omega
  rw [h1, h2]

/-- The scalar computation behind clause (ii): summing the second law over
class `k`, with the endpoint atoms weighted by `1 - β_k` and `β_{k+1}`, gives
exactly `p^{(D)}_k`. -/
lemma coupling_sum (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) :
    ∑ n ∈ Finset.Ico (DQ a b D k) (DQ a b D (k + 1) + 1), uWeight a b D k n * gmass b n
      = qF a D k := by
  have hγ := cgamma_pos ha ha1 hb hb1
  have hm1 := one_le_DQ hγ hD k
  have hM1 := one_le_DQ hγ hD (k + 1)
  have hmM := DQ_lt_succ ha ha1 hb hb1 hD hgD k
  rw [Finset.sum_Ico_succ_top (show DQ a b D k ≤ DQ a b D (k + 1) by omega),
    Finset.sum_eq_sum_Ico_succ_bot hmM]
  have hint : ∑ n ∈ Finset.Ico (DQ a b D k + 1) (DQ a b D (k + 1)),
      uWeight a b D k n * gmass b n
      = ∑ n ∈ Finset.Ico (DQ a b D k + 1) (DQ a b D (k + 1)), b ^ (n - 1) * (1 - b) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ico] at hn
    have e1 : ¬n = DQ a b D k := by omega
    have e2 : ¬n = DQ a b D (k + 1) := by omega
    have e3 : DQ a b D k < n ∧ n < DQ a b D (k + 1) := by omega
    have e4 : ¬n = 0 := by omega
    unfold uWeight gmass
    rw [if_neg e1, if_neg e2, if_pos e3, if_neg e4, one_mul]
  have hend1 : uWeight a b D k (DQ a b D k) * gmass b (DQ a b D k)
      = (1 - betaQ a b D k) * (b ^ (DQ a b D k - 1) * (1 - b)) := by
    have e5 : ¬DQ a b D k = 0 := by omega
    unfold uWeight gmass
    rw [if_pos rfl, if_neg e5]
  have hend2 : uWeight a b D k (DQ a b D (k + 1)) * gmass b (DQ a b D (k + 1))
      = betaQ a b D (k + 1) * (b ^ (DQ a b D (k + 1) - 1) * (1 - b)) := by
    have e6 : ¬DQ a b D (k + 1) = DQ a b D k := by omega
    have e7 : ¬DQ a b D (k + 1) = 0 := by omega
    unfold uWeight gmass
    rw [if_neg e6, if_pos rfl, if_neg e7]
  rw [hint, hend1, hend2,
    geom_block_sum b (A := DQ a b D k + 1) (B := DQ a b D (k + 1)) (by omega) (by omega)]
  have hgm : b ^ (DQ a b D k - 1) * (1 - b) = b ^ (DQ a b D k - 1) - b ^ DQ a b D k := by
    have hs : b ^ DQ a b D k = b ^ (DQ a b D k - 1) * b := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hs]
    ring
  have hgM : b ^ (DQ a b D (k + 1) - 1) * (1 - b)
      = b ^ (DQ a b D (k + 1) - 1) - b ^ DQ a b D (k + 1) := by
    have hs : b ^ DQ a b D (k + 1) = b ^ (DQ a b D (k + 1) - 1) * b := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hs]
    ring
  have hβm := betaQ_mul_den ha ha1 hb hb1 hD k
  have hβM := betaQ_mul_den ha ha1 hb hb1 hD (k + 1)
  rw [hgm, hgM]
  simp only [Nat.add_sub_cancel, qF]
  linear_combination hβM - hβm

/-- The `u`-fibres of the class map are measurable: the map is monotone in
`u`, so each fibre is order connected. -/
lemma ellQ_section_measurable (a b : ℝ) (D n k : ℕ) :
    MeasurableSet {u : ℝ | ellQ a b D n u = k} := by
  have hmono := ellQ_mono_u a b D n
  have hconn : Set.OrdConnected {u : ℝ | ellQ a b D n u = k} := by
    refine Set.ordConnected_iff.mpr fun x hx y hy _ => fun z hz => ?_
    have h1 : ellQ a b D n x ≤ ellQ a b D n z := hmono hz.1
    have h2 : ellQ a b D n z ≤ ellQ a b D n y := hmono hz.2
    have hx' : ellQ a b D n x = k := hx
    have hy' : ellQ a b D n y = k := hy
    show ellQ a b D n z = k
    omega
  exact hconn.measurableSet

/-- The measure of the `u`-fibre of class `k` over the length `n` under the
uniform law on `[0,1)` is exactly `uWeight`. -/
lemma ellQ_section_volume (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    volume.restrict (Set.Ico (0 : ℝ) 1) {u : ℝ | ellQ a b D n u = k}
      = ENNReal.ofReal (uWeight a b D k n) := by
  have hmono := DQ_strictMono ha ha1 hb hb1 hD hgD
  obtain ⟨j, hj1, hj2⟩ := DQ_exists_class ha ha1 hb hb1 hD hgD hn
  rcases hj1.eq_or_lt with heq | hlt
  · -- `n` is the cut point `D_j'`
    rcases j with _ | i
    · -- `j = 0`: the length is `1` and always lies in class `0`
      have hD0 := DQ_zero a b D
      have hn1 : n = 1 := by omega
      subst hn1
      have hall : ∀ u : ℝ, ellQ a b D 1 u = 0 := ellQ_one ha ha1 hb hb1 hD hgD
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have hset : {u : ℝ | ellQ a b D 1 u = 0} = Set.univ := by
          ext u
          simp [hall u]
        rw [hset, Measure.restrict_apply_univ, Real.volume_Ico]
        unfold uWeight
        rw [if_pos (by omega : (1 : ℕ) = DQ a b D 0), betaQ_zero]
      · have hset : {u : ℝ | ellQ a b D 1 u = k} = ∅ := by
          ext u
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hall u]
          omega
        rw [hset, measure_empty]
        have h1 := succ_le_DQ ha ha1 hb hb1 hD hgD k
        have h2 := succ_le_DQ ha ha1 hb hb1 hD hgD (k + 1)
        have e1 : ¬(1 : ℕ) = DQ a b D k := by omega
        have e2 : ¬(1 : ℕ) = DQ a b D (k + 1) := by omega
        have e3 : ¬(DQ a b D k < 1 ∧ 1 < DQ a b D (k + 1)) := by omega
        unfold uWeight
        rw [if_neg e1, if_neg e2, if_neg e3, ENNReal.ofReal_zero]
    · -- `j = i + 1`: the split endpoint between classes `i` and `i + 1`
      have hβ0 := betaQ_nonneg ha ha1 hb hb1 hD (i + 1)
      have hβ1 := betaQ_lt_one ha ha1 hb hb1 hD (i + 1)
      have hii : DQ a b D i < DQ a b D (i + 1) := hmono (by omega)
      by_cases hk1 : k = i + 1
      · subst hk1
        have hset : {u : ℝ | ellQ a b D n u = i + 1} = Set.Ici (betaQ a b D (i + 1)) := by
          ext u
          simp only [Set.mem_setOf_eq, Set.mem_Ici]
          constructor
          · intro h
            by_contra hcon
            have := (ellQ_endpoint ha ha1 hb hb1 hD hgD u heq).1 (not_le.mp hcon)
            omega
          · exact fun h => (ellQ_endpoint ha ha1 hb hb1 hD hgD u heq).2 h
        rw [hset, Measure.restrict_apply measurableSet_Ici]
        have hins : Set.Ici (betaQ a b D (i + 1)) ∩ Set.Ico (0 : ℝ) 1
            = Set.Ico (betaQ a b D (i + 1)) 1 := by
          ext u
          simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ico]
          constructor
          · rintro ⟨h1, -, h3⟩
            exact ⟨h1, h3⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, le_trans hβ0 h1, h2⟩
        rw [hins, Real.volume_Ico]
        unfold uWeight
        rw [if_pos heq.symm]
      · by_cases hk2 : k = i
        · subst hk2
          have hset : {u : ℝ | ellQ a b D n u = k} = Set.Iio (betaQ a b D (k + 1)) := by
            ext u
            simp only [Set.mem_setOf_eq, Set.mem_Iio]
            constructor
            · intro h
              by_contra hcon
              have := (ellQ_endpoint ha ha1 hb hb1 hD hgD u heq).2 (not_lt.mp hcon)
              omega
            · exact fun h => (ellQ_endpoint ha ha1 hb hb1 hD hgD u heq).1 h
          rw [hset, Measure.restrict_apply measurableSet_Iio]
          have hins : Set.Iio (betaQ a b D (k + 1)) ∩ Set.Ico (0 : ℝ) 1
              = Set.Ico 0 (betaQ a b D (k + 1)) := by
            ext u
            simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
            constructor
            · rintro ⟨h1, h2, -⟩
              exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h2, h1, lt_trans h2 hβ1⟩
          rw [hins, Real.volume_Ico, sub_zero]
          have e1 : ¬n = DQ a b D k := by omega
          unfold uWeight
          rw [if_neg e1, if_pos heq.symm]
        · have hset : {u : ℝ | ellQ a b D n u = k} = ∅ := by
            ext u
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            intro h
            by_cases hu : betaQ a b D (i + 1) ≤ u
            · have := (ellQ_endpoint ha ha1 hb hb1 hD hgD u heq).2 hu
              omega
            · have := (ellQ_endpoint ha ha1 hb hb1 hD hgD u heq).1 (not_le.mp hu)
              omega
          rw [hset, measure_empty]
          have e1 : ¬n = DQ a b D k := by
            intro hcon
            have := hmono.injective (heq.trans hcon)
            omega
          have e2 : ¬n = DQ a b D (k + 1) := by
            intro hcon
            have := hmono.injective (heq.trans hcon)
            omega
          have e3 : ¬(DQ a b D k < n ∧ n < DQ a b D (k + 1)) := by
            rintro ⟨hc1, hc2⟩
            rw [← heq] at hc1 hc2
            have h1' := hmono.lt_iff_lt.mp hc1
            have h2' := hmono.lt_iff_lt.mp hc2
            omega
          unfold uWeight
          rw [if_neg e1, if_neg e2, if_neg e3, ENNReal.ofReal_zero]
  · -- `n` lies strictly between cut points: the class is forced
    have hall : ∀ u : ℝ, ellQ a b D n u = j :=
      fun u => ellQ_interior ha ha1 hb hb1 hD hgD u hlt hj2
    by_cases hjk : j = k
    · subst hjk
      have hset : {u : ℝ | ellQ a b D n u = j} = Set.univ := by
        ext u
        simp [hall u]
      rw [hset, Measure.restrict_apply_univ, Real.volume_Ico]
      have e1 : ¬n = DQ a b D j := by omega
      have e2 : ¬n = DQ a b D (j + 1) := by omega
      unfold uWeight
      rw [if_neg e1, if_neg e2, if_pos ⟨hlt, hj2⟩]
      norm_num
    · have hset : {u : ℝ | ellQ a b D n u = k} = ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hall u]
        omega
      rw [hset, measure_empty]
      have e1 : ¬n = DQ a b D k := by
        intro hcon
        rw [hcon] at hlt hj2
        have h1' := hmono.lt_iff_lt.mp hlt
        have h2' := hmono.lt_iff_lt.mp hj2
        omega
      have e2 : ¬n = DQ a b D (k + 1) := by
        intro hcon
        rw [hcon] at hlt hj2
        have h1' := hmono.lt_iff_lt.mp hlt
        have h2' := hmono.lt_iff_lt.mp hj2
        omega
      have e3 : ¬(DQ a b D k < n ∧ n < DQ a b D (k + 1)) := by
        rintro ⟨hc1, hc2⟩
        have h1' := hmono.lt_iff_lt.mp (lt_trans hc1 hj2)
        have h2' := hmono.lt_iff_lt.mp (lt_trans hlt hc2)
        omega
      unfold uWeight
      rw [if_neg e1, if_neg e2, if_neg e3, ENNReal.ofReal_zero]

/-- Clause (ii) of **`thm:chain-coupling`**: under the product of the second
law and the uniform variable `U` on `[0,1)`, the coupled class has the law `p^{(D)}`
of `thm:quantised-law`, `ℙ(ℓ'(λ', U) = k) = p^{(D)}_k`. -/
theorem coupling_law (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) :
    ((geomPMF hb hb1).toMeasure.prod (volume.restrict (Set.Ico (0 : ℝ) 1)))
      {p : ℕ × ℝ | ellQ a b D p.1 p.2 = k} = ENNReal.ofReal (qF a D k) := by
  have hS : MeasurableSet {p : ℕ × ℝ | ellQ a b D p.1 p.2 = k} := by
    have hset : {p : ℕ × ℝ | ellQ a b D p.1 p.2 = k}
        = ⋃ n : ℕ, ({n} : Set ℕ) ×ˢ {u : ℝ | ellQ a b D n u = k} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro h
        exact ⟨p.1, rfl, h⟩
      · rintro ⟨n, h1, h2⟩
        rw [h1]
        exact h2
    rw [hset]
    exact MeasurableSet.iUnion fun n =>
      (measurableSet_singleton n).prod (ellQ_section_measurable a b D n k)
  rw [Measure.prod_apply hS]
  have hpre : ∀ n : ℕ, (Prod.mk n ⁻¹' {p : ℕ × ℝ | ellQ a b D p.1 p.2 = k})
      = {u : ℝ | ellQ a b D n u = k} := fun n => rfl
  simp only [hpre]
  rw [lintegral_countable']
  have hterm : ∀ n : ℕ,
      volume.restrict (Set.Ico (0 : ℝ) 1) {u : ℝ | ellQ a b D n u = k}
        * (geomPMF hb hb1).toMeasure {n}
      = ENNReal.ofReal (uWeight a b D k n * gmass b n) := by
    intro n
    rw [PMF.toMeasure_apply_singleton (geomPMF hb hb1) n (measurableSet_singleton n),
      geomPMF_apply]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [show gmass b 0 = 0 from rfl]
      simp
    · rw [ellQ_section_volume ha ha1 hb hb1 hD hgD k hn,
        ← ENNReal.ofReal_mul (uWeight_nonneg ha ha1 hb hb1 hD k n)]
  calc ∑' n : ℕ, volume.restrict (Set.Ico (0 : ℝ) 1) {u : ℝ | ellQ a b D n u = k}
        * (geomPMF hb hb1).toMeasure {n}
      = ∑' n : ℕ, ENNReal.ofReal (uWeight a b D k n * gmass b n) := tsum_congr hterm
    _ = ∑ n ∈ Finset.Ico (DQ a b D k) (DQ a b D (k + 1) + 1),
          ENNReal.ofReal (uWeight a b D k n * gmass b n) := by
        refine tsum_eq_sum fun n hn => ?_
        rw [Finset.mem_Ico] at hn
        have hDQ := DQ_lt_succ ha ha1 hb hb1 hD hgD k
        have e1 : ¬n = DQ a b D k := by omega
        have e2 : ¬n = DQ a b D (k + 1) := by omega
        have e3 : ¬(DQ a b D k < n ∧ n < DQ a b D (k + 1)) := by omega
        have hz : uWeight a b D k n = 0 := by
          unfold uWeight
          rw [if_neg e1, if_neg e2, if_neg e3]
        rw [hz, zero_mul, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∑ n ∈ Finset.Ico (DQ a b D k) (DQ a b D (k + 1) + 1),
          uWeight a b D k n * gmass b n) :=
        (ENNReal.ofReal_sum_of_nonneg fun n _ =>
          mul_nonneg (uWeight_nonneg ha ha1 hb hb1 hD k n)
            (gmass_nonneg hb.le hb1.le n)).symm
    _ = ENNReal.ofReal (qF a D k) := by
        rw [coupling_sum ha ha1 hb hb1 hD hgD k]

end ChainClasses
