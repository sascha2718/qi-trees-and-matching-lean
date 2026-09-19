/-
The two limitations of `arbitrary_offspring_matching.tex` (`sec:contraction-lower-bound`,
`sec:extension-limits`):

* `pathRel`, `muEps`, `iidModel`, `eta_muEps`, `failProb_ge`, `ratio_ge`, `liminf_ratio`:
  the iid process on the path graph `0 – 1 – 2` with law `μ_ε`, whose failure probability is
  at least `2(3/4-ε)ε` at every height because every matching matches the roots, so that the
  ratio to `η_α(μ_ε)` stays above every `c < 2/(1+4^α)` for small `ε`;
* `sixRel`, `rhoS`, `tauS`, `degrees_pos`, `PhiDres_rho_tau_eq`, `PhiDres_tau_rho_eq`,
  `PhiDres_square_eq`, `tendsto_ratio`: the six-point comparison `(ρ_s, ρ_s; τ_s, τ_s)` whose
  pair potential is of first order in the maximal directed potential;
* `Tlin`, `linear_coeff_ge`, `Tlin_one`, `Tlin_strictAntiOn`, `Tlin_fourThirds_lt`,
  `exists_Tlin_root`: every uniform bound `P^□ ≤ λ M + C M²` over the four-law comparisons
  on six points without zero degrees has `λ ≥ T_α = 2^{1-α} + 2 K_α (1 - 2^{-α})^{α+1}`,
  with `T_1 = 9/8`, `T_{4/3} < 1`, `T` strictly decreasing on `[1,∞)` and a unique root in
  `(1, 4/3)`.

The laws on finite types are handled through their real weight vectors
(`qE_eq_ofReal_sum`, `PhiDres_eq_ofReal_sum`, `PhiD_eq_ofReal_sum`).
-/
import GraphMarkovMatching.Stopped.Paths
import GraphMarkovMatching.Stopped.Scalar

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### Laws on finite types through real weights -/

section FiniteLaws

variable {X : Type} [Fintype X]

/-- The law on a finite inhabited type with the real weights `w`, when these are
nonnegative and sum to one; the point mass at the default element otherwise. -/
noncomputable def pmfOfWeights [Inhabited X] (w : X → ℝ) : PMF X :=
  if h : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 then
    PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h.1 i), h.2, ENNReal.ofReal_one])
  else PMF.pure default

lemma pmfOfWeights_apply [Inhabited X] {w : X → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (i : X) : pmfOfWeights w i = ENNReal.ofReal (w i) := by
  rw [pmfOfWeights, dif_pos ⟨hw, hs⟩, PMF.ofFintype_apply]

/-- The bad degree of a law with real weights is the weight of the incompatible points. -/
lemma qE_eq_ofReal_sum (μ : PMF X) (w : X → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hμ : ∀ y, μ y = ENNReal.ofReal (w y)) (R : X → X → Prop) (x : X) :
    qE μ R x = ENNReal.ofReal (∑ y, if R x y then 0 else w y) := by
  rw [qE, tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg (fun y _ => by split_ifs <;> [exact le_rfl; exact hw y])]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp [hμ]

/-- The good degree of a law with real weights is the weight of the compatible points. -/
lemma rE_eq_ofReal_sum (μ : PMF X) (w : X → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hμ : ∀ y, μ y = ENNReal.ofReal (w y)) (R : X → X → Prop) (x : X) :
    rE μ R x = ENNReal.ofReal (∑ y, if R x y then w y else 0) := by
  rw [rE, tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg (fun y _ => by split_ifs <;> [exact hw y; exact le_rfl])]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp [hμ]

/-- The real bad degree of a law with real weights. -/
lemma q_eq_sum (μ : PMF X) (w : X → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hμ : ∀ y, μ y = ENNReal.ofReal (w y)) (R : X → X → Prop) (x : X) :
    q μ R x = ∑ y, if R x y then 0 else w y := by
  rw [q, qE_eq_ofReal_sum μ w hw hμ, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg fun y _ => by split_ifs <;> [exact le_rfl; exact hw y]

/-- A bad degree below one is a positive good degree. -/
lemma rE_ne_zero_of_q_lt_one {Y : Type} {μ : PMF Y} {R : Y → Y → Prop} {x : Y}
    (h : q μ R x < 1) : rE μ R x ≠ 0 := by
  intro h0
  have h1 := rE_add_qE μ R x
  rw [h0, zero_add] at h1
  rw [q, h1, ENNReal.toReal_one] at h
  exact lt_irrefl _ h

/-- The restricted potential of two laws with real weights, when every charged source point
has positive degree: the real sum of `φ_α` at the real bad degrees. -/
lemma PhiDres_eq_ofReal_sum (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (ws wt : X → ℝ)
    (hws : ∀ x, 0 ≤ ws x) (hwt : ∀ y, 0 ≤ wt y) (hρs : ∀ x, ρs x = ENNReal.ofReal (ws x))
    (hρt : ∀ y, ρt y = ENNReal.ofReal (wt y)) (hpos : ∀ x, ρs x ≠ 0 → rE ρt R x ≠ 0) :
    PhiDres α ρs ρt R
      = ENNReal.ofReal (∑ x, ws x * phi α (∑ y, if R x y then 0 else wt y)) := by
  have hq : ∀ x, q ρt R x = ∑ y, if R x y then 0 else wt y :=
    fun x => q_eq_sum ρt wt hwt hρt R x
  have hnn : ∀ x, 0 ≤ ws x * phi α (∑ y, if R x y then 0 else wt y) := by
    intro x
    by_cases hx : ρs x = 0
    · have hw0 : ws x = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.mp (by rw [← hρs x]; exact hx)) (hws x)
      rw [hw0, zero_mul]
    · have hq1 := q_lt_one_of_rE_ne_zero (hpos x hx)
      rw [hq x] at hq1
      exact mul_nonneg (hws x) (phi_nonneg (by rw [← hq x]; exact q_nonneg) hq1)
  rw [PhiDres, tsum_fintype, ENNReal.ofReal_sum_of_nonneg (fun x _ => hnn x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : ρs x = 0
  · have hw0 : ws x = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp (by rw [← hρs x]; exact hx)) (hws x)
    rw [hx, hw0, zero_mul, zero_mul, ENNReal.ofReal_zero]
  · have hr := hpos x hx
    rw [if_neg hr, phiE_of_lt (q_lt_one_of_rE_ne_zero hr), hρs x,
      ← ENNReal.ofReal_mul (hws x), hq x]

/-- The directed potential of two laws with real weights, when every charged source point
has positive degree. -/
lemma PhiD_eq_ofReal_sum (α : ℝ) (μ ν : PMF X) (R : X → X → Prop) (ws wt : X → ℝ)
    (hws : ∀ x, 0 ≤ ws x) (hwt : ∀ y, 0 ≤ wt y) (hμ : ∀ x, μ x = ENNReal.ofReal (ws x))
    (hν : ∀ y, ν y = ENNReal.ofReal (wt y)) (hpos : ∀ x, μ x ≠ 0 → rE ν R x ≠ 0) :
    PhiD α μ ν R
      = ENNReal.ofReal (∑ x, ws x * phi α (∑ y, if R x y then 0 else wt y)) := by
  rw [← PhiDres_eq_ofReal_sum α μ ν R ws wt hws hwt hμ hν hpos, PhiD, PhiDres]
  refine tsum_congr fun x => ?_
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [if_neg (hpos x hx)]

end FiniteLaws

/-! ### Every matching matches the roots -/

namespace Model

variable {V I : Type} (M : Model V I)

/-- The root marginal of `ρ_{t,h}` is the typed root law. -/
lemma tsum_rho_mul_rootLab (t : I) (h : ℕ) (F : I × V → ℝ≥0∞) :
    ∑' x, M.rho t h x * F (rootLab h x) = ∑' s, M.rootT t s * F s := by
  rw [rho, tsum_bind_mul]
  refine tsum_congr fun s => ?_
  congr 1
  calc ∑' x, muM M.kernel s h x * F (rootLab h x)
      = ∑' x, muM M.kernel s h x * F s := by
        refine tsum_congr fun x => ?_
        by_cases hx : muM M.kernel s h x = 0
        · rw [hx, zero_mul, zero_mul]
        · rw [rootLab_of_ne_zero M.kernel h s x hx]
    _ = F s := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The bad degree against `ρ_{t,h}` is at least the bad root degree against the root law
of `t`, since matching forces root compatibility (`sec:extension-limits`). -/
lemma qE_rootLaw_le_qE_rho (t : I) (h : ℕ) (x : FullLab (I × V) h) :
    qE (M.rootLaw t) M.R (rootLab h x).2 ≤ qE (M.rho t h) (M.sim h) x := by
  calc qE (M.rootLaw t) M.R (rootLab h x).2
      = ∑' v, M.rootLaw t v * (if M.R (rootLab h x).2 v then 0 else 1) := by
        rw [qE]
        exact tsum_congr fun v => by split_ifs <;> simp
    _ = ∑' s, M.rootT t s * (if M.R (rootLab h x).2 s.2 then 0 else 1) := by
        rw [rootT, tsum_map_mul]
    _ = ∑' y, M.rho t h y * (if M.R (rootLab h x).2 (rootLab h y).2 then 0 else 1) :=
        (M.tsum_rho_mul_rootLab t h fun s => if M.R (rootLab h x).2 s.2 then 0 else 1).symm
    _ ≤ ∑' y, if M.sim h x y then 0 else M.rho t h y := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hR : M.R (rootLab h x).2 (rootLab h y).2
        · rw [if_pos hR, mul_zero]
          exact zero_le
        · have hs : ¬ M.sim h x y := fun hs => hR (fullSim_root M.srel h x y hs)
          rw [if_neg hR, if_neg hs, mul_one]
    _ = qE (M.rho t h) (M.sim h) x := rfl

/-- **Every matching matches the roots**: the failure probability at every height is at
least the mass of the incompatible root pairs (`sec:extension-limits`). -/
lemma tsum_rootLaw_mul_qE_le_failProb (s t : I) (h : ℕ) :
    ∑' v, M.rootLaw s v * qE (M.rootLaw t) M.R v ≤ M.failProb s t h := by
  calc ∑' v, M.rootLaw s v * qE (M.rootLaw t) M.R v
      = ∑' s', M.rootT s s' * qE (M.rootLaw t) M.R s'.2 := by rw [rootT, tsum_map_mul]
    _ = ∑' x, M.rho s h x * qE (M.rootLaw t) M.R (rootLab h x).2 :=
        (M.tsum_rho_mul_rootLab s h fun s' => qE (M.rootLaw t) M.R s'.2).symm
    _ ≤ ∑' x, M.rho s h x * qE (M.rho t h) (M.sim h) x := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        gcongr
        exact M.qE_rootLaw_le_qE_rho t h x
    _ = M.failProb s t h := rfl

end Model

/-! ### The order of the failure probability (`sec:extension-limits`) -/

/-- The path graph `0 – 1 – 2` on `Fin 3`, reflexive and symmetric. -/
def pathRel : Fin 3 → Fin 3 → Prop := fun v w => v = w ∨ v.val + 1 = w.val ∨ w.val + 1 = v.val

lemma pathRel_refl (v : Fin 3) : pathRel v v := Or.inl rfl

/-- The real weights of `μ_ε`. -/
noncomputable def muEpsW (ε : ℝ) : Fin 3 → ℝ := ![3 / 4 - ε, 1 / 4, ε]

/-- The law `μ_ε = (3/4 - ε) δ₀ + 1/4 δ₁ + ε δ₂` for `0 < ε ≤ 1/4`. -/
noncomputable def muEps (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) : PMF (Fin 3) :=
  PMF.ofFintype (fun v => ENNReal.ofReal (muEpsW ε v)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg, Fin.sum_univ_three]
    · simp only [muEpsW, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [show (3 / 4 - ε) + 1 / 4 + ε = (1 : ℝ) by ring, ENNReal.ofReal_one]
    · intro v _
      fin_cases v <;> simp [muEpsW] <;> linarith)

lemma muEps_apply (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) (v : Fin 3) :
    muEps ε h0 h1 v = ENNReal.ofReal (muEpsW ε v) := by
  rw [muEps, PMF.ofFintype_apply]

lemma muEpsW_nonneg {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) (v : Fin 3) : 0 ≤ muEpsW ε v := by
  fin_cases v <;> simp [muEpsW] <;> linarith

/-- The iid process on the path graph with law `μ_ε`: one type, fresh, with the trivial
kernel. -/
noncomputable def iidModel (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) : Model (Fin 3) Unit where
  R := pathRel
  zero := 0
  μ := muEps ε h0 h1
  fresh := fun _ => True
  π := fun _ => PMF.pure ((), ())

/-- `η_α(μ_ε) = (3/4 - ε) ε ((1-ε)^{-α} + (1/4+ε)^{-α})` (`sec:extension-limits`). -/
theorem eta_muEps (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) :
    (iidModel ε h0 h1).eta α
      = ENNReal.ofReal ((3 / 4 - ε) * ε * ((1 - ε) ^ (-α) + (1 / 4 + ε) ^ (-α))) := by
  have _ := hα
  have hpos : ∀ x, muEps ε h0 h1 x ≠ 0 → rE (muEps ε h0 h1) pathRel x ≠ 0 := by
    intro x hx h
    have := le_rE_of_refl (μ := muEps ε h0 h1) (pathRel_refl x)
    rw [h, nonpos_iff_eq_zero] at this
    exact hx this
  rw [Model.eta]
  show PhiD α (muEps ε h0 h1) (muEps ε h0 h1) pathRel = _
  rw [PhiD_eq_ofReal_sum α _ _ pathRel (muEpsW ε) (muEpsW ε) (muEpsW_nonneg h0 h1)
    (muEpsW_nonneg h0 h1) (muEps_apply ε h0 h1) (muEps_apply ε h0 h1) hpos]
  congr 1
  have e1 : (1 : ℝ) - (3 / 4 - ε) = 1 / 4 + ε := by ring
  simp [Fin.sum_univ_three, pathRel, muEpsW, phi, e1]
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
  ring

/-- The two incompatible ordered root pairs `(0,2)` and `(2,0)` have combined mass
`2(3/4-ε)ε`, and every matching matches the roots (`sec:extension-limits`). -/
theorem failProb_ge (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) (h : ℕ) :
    ENNReal.ofReal (2 * (3 / 4 - ε) * ε) ≤ (iidModel ε h0 h1).failProb () () h := by
  refine le_trans (le_of_eq ?_) ((iidModel ε h0 h1).tsum_rootLaw_mul_qE_le_failProb () () h)
  have hroot : (iidModel ε h0 h1).rootLaw () = muEps ε h0 h1 :=
    Model.rootLaw_fresh _ trivial
  rw [hroot]
  show ENNReal.ofReal (2 * (3 / 4 - ε) * ε)
    = ∑' v, muEps ε h0 h1 v * qE (muEps ε h0 h1) pathRel v
  rw [tsum_fintype]
  simp_rw [qE_eq_ofReal_sum (muEps ε h0 h1) (muEpsW ε) (muEpsW_nonneg h0 h1)
    (muEps_apply ε h0 h1) pathRel, muEps_apply]
  have hnn : ∀ v : Fin 3, 0 ≤ muEpsW ε v * ∑ y, if pathRel v y then 0 else muEpsW ε y :=
    fun v => mul_nonneg (muEpsW_nonneg h0 h1 v)
      (Finset.sum_nonneg fun y _ => by split_ifs <;> [exact le_rfl; exact muEpsW_nonneg h0 h1 y])
  simp_rw [← ENNReal.ofReal_mul (muEpsW_nonneg h0 h1 _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => hnn v)]
  congr 1
  simp [Fin.sum_univ_three, pathRel, muEpsW]
  ring

/-- The ratio bound at every `ε`: `2/((1-ε)^{-α} + (1/4+ε)^{-α}) · η_α(μ_ε) ≤ P(no matching)`
at every height. -/
theorem ratio_ge (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) (h : ℕ) :
    ENNReal.ofReal (2 / ((1 - ε) ^ (-α) + (1 / 4 + ε) ^ (-α))) * (iidModel ε h0 h1).eta α
      ≤ (iidModel ε h0 h1).failProb () () h := by
  rw [eta_muEps α hα ε h0 h1]
  have hA : 0 < (1 - ε) ^ (-α) + (1 / 4 + ε) ^ (-α) :=
    add_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _)
  set A := (1 - ε) ^ (-α) + (1 / 4 + ε) ^ (-α) with hAdef
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine le_trans (le_of_eq ?_) (failProb_ge ε h0 h1 h)
  congr 1
  rw [show 2 / A * ((3 / 4 - ε) * ε * A) = 2 * (3 / 4 - ε) * ε * (A / A) by ring,
    div_self hA.ne', mul_one]

/-- **The linear order is sharp** (`sec:extension-limits`): for every `c < 2/(1+4^α)` there is
`ε₀ > 0` such that `c η_α(μ_ε) ≤ P(no matching)` at every height for all `0 < ε ≤ ε₀`. -/
theorem liminf_ratio (α : ℝ) (hα : 0 ≤ α) {c : ℝ} (hc : c < 2 / (1 + 4 ^ α)) :
    ∃ ε₀ > 0, ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1 / 4), ε ≤ ε₀ → ∀ h,
      ENNReal.ofReal c * (iidModel ε h0 h1).eta α ≤ (iidModel ε h0 h1).failProb () () h := by
  set f : ℝ → ℝ := fun ε => 2 / ((1 - ε) ^ (-α) + (1 / 4 + ε) ^ (-α)) with hf
  have hf0 : f 0 = 2 / (1 + 4 ^ α) := by
    simp only [hf, sub_zero, add_zero, Real.one_rpow]
    rw [Real.rpow_neg (by norm_num), show (1 / 4 : ℝ) = 4⁻¹ by norm_num,
      Real.inv_rpow (by norm_num), inv_inv]
  have hcont : ContinuousAt f 0 := by
    have h1 : ContinuousAt (fun ε : ℝ => (1 - ε) ^ (-α)) 0 :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))
    have h2 : ContinuousAt (fun ε : ℝ => (1 / 4 + ε) ^ (-α)) 0 :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
    refine continuousAt_const.div (h1.add h2) ?_
    simp only [sub_zero, add_zero, Real.one_rpow]
    positivity
  have hev : ∀ᶠ ε in nhds (0 : ℝ), c < f ε := by
    rw [← hf0] at hc
    exact hcont.tendsto.eventually_const_lt hc
  obtain ⟨δ, hδ, hδc⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ / 2, by positivity, fun ε h0 h1 hε h => ?_⟩
  have hcf : c < f ε := hδc (by rw [Real.dist_eq, sub_zero, abs_of_pos h0]; linarith)
  calc ENNReal.ofReal c * (iidModel ε h0 h1).eta α
      ≤ ENNReal.ofReal (f ε) * (iidModel ε h0 h1).eta α := by
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcf.le) zero_le
    _ ≤ (iidModel ε h0 h1).failProb () () h := ratio_ge α hα ε h0 h1 h


/-! ### The six-point comparison (`sec:contraction-lower-bound`) -/

/-- The six-point relation on `a b c d e f = 0 … 5`: every pair compatible except `{a,d}`
and `{b,e}`. -/
def sixRel : Fin 6 → Fin 6 → Prop := fun v w =>
  ¬ ((v = 0 ∧ w = 3) ∨ (v = 3 ∧ w = 0) ∨ (v = 1 ∧ w = 4) ∨ (v = 4 ∧ w = 1))

lemma sixRel_refl (v : Fin 6) : sixRel v v := by
  fin_cases v <;> simp [sixRel]

lemma sixRel_symm (v w : Fin 6) (h : sixRel v w) : sixRel w v := by
  unfold sixRel at *
  tauto

/-- `φ_α(0) = 0`. -/
@[simp] lemma phi_zero (α : ℝ) : phi α 0 = 0 := by simp [phi]

/-- `x = (1-t)/(1-rt)` with `r = (1-q)^α` and `t = (1-p)^α`. -/
noncomputable def xCoef (α p q : ℝ) : ℝ :=
  (1 - (1 - p) ^ α) / (1 - (1 - q) ^ α * (1 - p) ^ α)

/-- `y = (1-r)/(1-rt)`. -/
noncomputable def yCoef (α p q : ℝ) : ℝ :=
  (1 - (1 - q) ^ α) / (1 - (1 - q) ^ α * (1 - p) ^ α)

/-- `u_s = s x / φ_α(q)`. -/
noncomputable def uS (α p q s : ℝ) : ℝ := s * xCoef α p q / phi α q

/-- `v_s = s y / φ_α(p)`. -/
noncomputable def vS (α p q s : ℝ) : ℝ := s * yCoef α p q / phi α p

/-- The weights of `ρ_s = u_s δ_a + p δ_b + (1-p-u_s) δ_c`. -/
noncomputable def rhoW (α p q s : ℝ) : Fin 6 → ℝ :=
  ![uS α p q s, p, 1 - p - uS α p q s, 0, 0, 0]

/-- The weights of `τ_s = q δ_d + v_s δ_e + (1-q-v_s) δ_f`. -/
noncomputable def tauW (α p q s : ℝ) : Fin 6 → ℝ :=
  ![0, 0, 0, q, vS α p q s, 1 - q - vS α p q s]

/-- The source law `ρ_s` (the point mass at `a` outside the admissible range). -/
noncomputable def rhoS (α p q s : ℝ) : PMF (Fin 6) := pmfOfWeights (rhoW α p q s)

/-- The target law `τ_s` (the point mass at `a` outside the admissible range). -/
noncomputable def tauS (α p q s : ℝ) : PMF (Fin 6) := pmfOfWeights (tauW α p q s)

/-- The range `s ≥ 0`, `u_s ≤ 1 - p`, `v_s ≤ 1 - q` on which `ρ_s` and `τ_s` are the laws
of the note ("sufficiently small `s`"). -/
def Admissible (α p q s : ℝ) : Prop := 0 ≤ s ∧ uS α p q s ≤ 1 - p ∧ vS α p q s ≤ 1 - q

/-- `P(ρ_s, τ_s) = u_s φ(q) + p φ(v_s)`. -/
noncomputable def potST (α p q s : ℝ) : ℝ := uS α p q s * phi α q + p * phi α (vS α p q s)

/-- `P(τ_s, ρ_s) = q φ(u_s) + v_s φ(p)`. -/
noncomputable def potTS (α p q s : ℝ) : ℝ := q * phi α (uS α p q s) + vS α p q s * phi α p

/-- The pair potential `P(ρ_s × ρ_s, τ_s × τ_s; R^□)`, the display of
`sec:contraction-lower-bound`. -/
noncomputable def potSq (α p q s : ℝ) : ℝ :=
  uS α p q s ^ 2 * phi α (2 * q - q ^ 2)
    + 2 * uS α p q s * p * phi α (q ^ 2 + vS α p q s ^ 2)
    + 2 * uS α p q s * (1 - p - uS α p q s) * phi α (q ^ 2)
    + p ^ 2 * phi α (2 * vS α p q s - vS α p q s ^ 2)
    + 2 * p * (1 - p - uS α p q s) * phi α (vS α p q s ^ 2)

lemma rhoW_sum (α p q s : ℝ) : ∑ i, rhoW α p q s i = 1 := by
  simp [Fin.sum_univ_six, rhoW]
  ring

lemma tauW_sum (α p q s : ℝ) : ∑ i, tauW α p q s i = 1 := by
  simp [Fin.sum_univ_six, tauW]

section SixPoint

variable {α p q : ℝ} (hα : 0 < α) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
include hα hp0 hp1 hq0 hq1

lemma rt_lt_one : (1 - q) ^ α * (1 - p) ^ α < 1 :=
  mul_lt_one_of_nonneg_of_lt_one_left (Real.rpow_nonneg (by linarith) α)
    (Real.rpow_lt_one (by linarith) (by linarith) hα)
    (Real.rpow_le_one (by linarith) (by linarith) hα.le)

lemma xCoef_pos : 0 < xCoef α p q := by
  unfold xCoef
  have := rt_lt_one hα hp0 hp1 hq0 hq1
  have := Real.rpow_lt_one (by linarith : (0 : ℝ) ≤ 1 - p) (by linarith) hα
  exact div_pos (by linarith) (by linarith)

lemma yCoef_pos : 0 < yCoef α p q := by
  unfold yCoef
  have := rt_lt_one hα hp0 hp1 hq0 hq1
  have := Real.rpow_lt_one (by linarith : (0 : ℝ) ≤ 1 - q) (by linarith) hα
  exact div_pos (by linarith) (by linarith)

/-- `x + t y = 1`. -/
lemma xCoef_add : xCoef α p q + (1 - p) ^ α * yCoef α p q = 1 := by
  have h := rt_lt_one hα hp0 hp1 hq0 hq1
  have hne : 1 - (1 - q) ^ α * (1 - p) ^ α ≠ 0 := by linarith
  unfold xCoef yCoef
  rw [mul_div_assoc', ← add_div, div_eq_one_iff_eq hne]
  ring

/-- `r x + y = 1`. -/
lemma yCoef_add : (1 - q) ^ α * xCoef α p q + yCoef α p q = 1 := by
  have h := rt_lt_one hα hp0 hp1 hq0 hq1
  have hne : 1 - (1 - q) ^ α * (1 - p) ^ α ≠ 0 := by linarith
  unfold xCoef yCoef
  rw [mul_div_assoc', ← add_div, div_eq_one_iff_eq hne]
  ring

lemma uS_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ uS α p q s :=
  div_nonneg (mul_nonneg hs (xCoef_pos hα hp0 hp1 hq0 hq1).le) (phi_nonneg hq0.le hq1)

lemma vS_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ vS α p q s :=
  div_nonneg (mul_nonneg hs (yCoef_pos hα hp0 hp1 hq0 hq1).le) (phi_nonneg hp0.le hp1)

lemma rhoW_nonneg {s : ℝ} (hs : Admissible α p q s) (i : Fin 6) : 0 ≤ rhoW α p q s i := by
  have hu := uS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hu1 := hs.2.1
  fin_cases i <;> simp [rhoW] <;> linarith

lemma tauW_nonneg {s : ℝ} (hs : Admissible α p q s) (i : Fin 6) : 0 ≤ tauW α p q s i := by
  have hv := vS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hv1 := hs.2.2
  fin_cases i <;> simp [tauW] <;> linarith

lemma rhoS_apply {s : ℝ} (hs : Admissible α p q s) (i : Fin 6) :
    rhoS α p q s i = ENNReal.ofReal (rhoW α p q s i) :=
  pmfOfWeights_apply (rhoW_nonneg hα hp0 hp1 hq0 hq1 hs) (rhoW_sum α p q s) i

lemma tauS_apply {s : ℝ} (hs : Admissible α p q s) (i : Fin 6) :
    tauS α p q s i = ENNReal.ofReal (tauW α p q s i) :=
  pmfOfWeights_apply (tauW_nonneg hα hp0 hp1 hq0 hq1 hs) (tauW_sum α p q s) i

/-- **All degrees between the supports are positive**: in fact every point of `Fin 6` has
positive degree against both laws (`sec:contraction-lower-bound`). -/
theorem degrees_pos {s : ℝ} (hs : Admissible α p q s) :
    (∀ x, rE (tauS α p q s) sixRel x ≠ 0) ∧ (∀ y, rE (rhoS α p q s) sixRel y ≠ 0) := by
  have hu := uS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hv := vS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hu1 := hs.2.1
  have hv1 := hs.2.2
  constructor
  · intro x
    apply rE_ne_zero_of_q_lt_one
    rw [q_eq_sum _ (tauW α p q s) (tauW_nonneg hα hp0 hp1 hq0 hq1 hs)
      (tauS_apply hα hp0 hp1 hq0 hq1 hs)]
    fin_cases x <;> simp [sixRel, tauW] <;> linarith
  · intro y
    apply rE_ne_zero_of_q_lt_one
    rw [q_eq_sum _ (rhoW α p q s) (rhoW_nonneg hα hp0 hp1 hq0 hq1 hs)
      (rhoS_apply hα hp0 hp1 hq0 hq1 hs)]
    fin_cases y <;> simp [sixRel, rhoW] <;> linarith

/-- `P(ρ_s, τ_s) = u_s φ(q) + p φ(v_s)` (`sec:contraction-lower-bound`). -/
theorem PhiDres_rho_tau_eq {s : ℝ} (hs : Admissible α p q s) :
    PhiDres α (rhoS α p q s) (tauS α p q s) sixRel = ENNReal.ofReal (potST α p q s) := by
  rw [PhiDres_eq_ofReal_sum α _ _ sixRel (rhoW α p q s) (tauW α p q s)
    (rhoW_nonneg hα hp0 hp1 hq0 hq1 hs) (tauW_nonneg hα hp0 hp1 hq0 hq1 hs)
    (rhoS_apply hα hp0 hp1 hq0 hq1 hs) (tauS_apply hα hp0 hp1 hq0 hq1 hs)
    (fun x _ => (degrees_pos hα hp0 hp1 hq0 hq1 hs).1 x)]
  congr 1
  simp [Fin.sum_univ_six, sixRel, rhoW, tauW, potST]

/-- `P(τ_s, ρ_s) = q φ(u_s) + v_s φ(p)` (`sec:contraction-lower-bound`). -/
theorem PhiDres_tau_rho_eq {s : ℝ} (hs : Admissible α p q s) :
    PhiDres α (tauS α p q s) (rhoS α p q s) sixRel = ENNReal.ofReal (potTS α p q s) := by
  rw [PhiDres_eq_ofReal_sum α _ _ sixRel (tauW α p q s) (rhoW α p q s)
    (tauW_nonneg hα hp0 hp1 hq0 hq1 hs) (rhoW_nonneg hα hp0 hp1 hq0 hq1 hs)
    (tauS_apply hα hp0 hp1 hq0 hq1 hs) (rhoS_apply hα hp0 hp1 hq0 hq1 hs)
    (fun x _ => (degrees_pos hα hp0 hp1 hq0 hq1 hs).2 x)]
  congr 1
  simp [Fin.sum_univ_six, sixRel, rhoW, tauW, potTS]

/-- **The pair potential**, the exact expansion of `sec:contraction-lower-bound`. -/
theorem PhiDres_square_eq {s : ℝ} (hs : Admissible α p q s) :
    PhiDres α (prodPMF (rhoS α p q s) (rhoS α p q s)) (prodPMF (tauS α p q s) (tauS α p q s))
        (SquareRel sixRel)
      = ENNReal.ofReal (potSq α p q s) := by
  have hdeg := degrees_pos hα hp0 hp1 hq0 hq1 hs
  have hws : ∀ x : Fin 6 × Fin 6, 0 ≤ rhoW α p q s x.1 * rhoW α p q s x.2 := fun x =>
    mul_nonneg (rhoW_nonneg hα hp0 hp1 hq0 hq1 hs _) (rhoW_nonneg hα hp0 hp1 hq0 hq1 hs _)
  have hwt : ∀ y : Fin 6 × Fin 6, 0 ≤ tauW α p q s y.1 * tauW α p q s y.2 := fun y =>
    mul_nonneg (tauW_nonneg hα hp0 hp1 hq0 hq1 hs _) (tauW_nonneg hα hp0 hp1 hq0 hq1 hs _)
  have hρ : ∀ x : Fin 6 × Fin 6, prodPMF (rhoS α p q s) (rhoS α p q s) x
      = ENNReal.ofReal (rhoW α p q s x.1 * rhoW α p q s x.2) := by
    intro x
    rw [prodPMF_apply, rhoS_apply hα hp0 hp1 hq0 hq1 hs, rhoS_apply hα hp0 hp1 hq0 hq1 hs,
      ENNReal.ofReal_mul (rhoW_nonneg hα hp0 hp1 hq0 hq1 hs _)]
  have hτ : ∀ y : Fin 6 × Fin 6, prodPMF (tauS α p q s) (tauS α p q s) y
      = ENNReal.ofReal (tauW α p q s y.1 * tauW α p q s y.2) := by
    intro y
    rw [prodPMF_apply, tauS_apply hα hp0 hp1 hq0 hq1 hs, tauS_apply hα hp0 hp1 hq0 hq1 hs,
      ENNReal.ofReal_mul (tauW_nonneg hα hp0 hp1 hq0 hq1 hs _)]
  have hpos : ∀ x : Fin 6 × Fin 6, prodPMF (rhoS α p q s) (rhoS α p q s) x ≠ 0 →
      rE (prodPMF (tauS α p q s) (tauS α p q s)) (SquareRel sixRel) x ≠ 0 := by
    rintro ⟨x₁, x₂⟩ _ h0
    have hle := straight_le_rE_square (tauS α p q s) (tauS α p q s) sixRel x₁ x₂
    rw [h0, nonpos_iff_eq_zero] at hle
    exact mul_ne_zero (hdeg.1 x₁) (hdeg.1 x₂) hle
  rw [PhiDres_eq_ofReal_sum α _ _ _ _ _ hws hwt hρ hτ hpos]
  congr 1
  simp [Fintype.sum_prod_type, Fin.sum_univ_six, SquareRel, sixRel, rhoW, tauW, potSq]
  ring_nf

end SixPoint


/-! ### The limit `s ↓ 0` (`sec:contraction-lower-bound`) -/

/-- The slope `a = x/φ_α(q)` of `u_s = s a`. -/
noncomputable def aSlope (α p q : ℝ) : ℝ := xCoef α p q / phi α q

/-- The slope `b = y/φ_α(p)` of `v_s = s b`. -/
noncomputable def bSlope (α p q : ℝ) : ℝ := yCoef α p q / phi α p

lemma uS_eq (α p q s : ℝ) : uS α p q s = s * aSlope α p q := by
  rw [uS, aSlope, mul_div_assoc]

lemma vS_eq (α p q s : ℝ) : vS α p q s = s * bSlope α p q := by
  rw [vS, bSlope, mul_div_assoc]

/-- `P(ρ_s, τ_s)/s`, continued to `s = 0`. -/
noncomputable def Afun (α p q s : ℝ) : ℝ :=
  aSlope α p q * phi α q + p * (bSlope α p q / (1 - s * bSlope α p q) ^ α)

/-- `P(τ_s, ρ_s)/s`, continued to `s = 0`. -/
noncomputable def Bfun (α p q s : ℝ) : ℝ :=
  q * (aSlope α p q / (1 - s * aSlope α p q) ^ α) + bSlope α p q * phi α p

/-- The pair potential divided by `s`, continued to `s = 0`. -/
noncomputable def Nfun (α p q s : ℝ) : ℝ :=
  s * aSlope α p q ^ 2 * phi α (2 * q - q ^ 2)
    + 2 * aSlope α p q * p * phi α (q ^ 2 + (s * bSlope α p q) ^ 2)
    + 2 * aSlope α p q * (1 - p - s * aSlope α p q) * phi α (q ^ 2)
    + p ^ 2 * ((2 * bSlope α p q - s * bSlope α p q ^ 2)
        / (1 - (2 * (s * bSlope α p q) - (s * bSlope α p q) ^ 2)) ^ α)
    + 2 * p * (1 - p - s * aSlope α p q)
        * (s * bSlope α p q ^ 2 / (1 - (s * bSlope α p q) ^ 2) ^ α)

lemma potST_eq (α p q s : ℝ) : potST α p q s = s * Afun α p q s := by
  rw [potST, Afun, uS_eq, vS_eq]
  simp only [phi]
  ring

lemma potTS_eq (α p q s : ℝ) : potTS α p q s = s * Bfun α p q s := by
  rw [potTS, Bfun, uS_eq, vS_eq]
  simp only [phi]
  ring

lemma potSq_eq (α p q s : ℝ) : potSq α p q s = s * Nfun α p q s := by
  rw [potSq, Nfun, uS_eq, vS_eq]
  simp only [phi]
  ring

/-- `s ↦ f(s)/(1 - g(s))^α` is continuous where `g < 1`. -/
private lemma continuousAt_div_rpow {α : ℝ} {f g : ℝ → ℝ} {s₀ : ℝ} (hf : ContinuousAt f s₀)
    (hg : ContinuousAt g s₀) (h : g s₀ < 1) :
    ContinuousAt (fun s => f s / (1 - g s) ^ α) s₀ := by
  have h1 : (0 : ℝ) < 1 - g s₀ := by linarith
  refine hf.div ((continuousAt_const.sub hg).rpow_const (Or.inl h1.ne')) ?_
  exact (Real.rpow_pos_of_pos h1 α).ne'

section Limit

variable {α p q : ℝ} (hα : 0 < α) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
include hα hp0 hp1 hq0 hq1

lemma aSlope_pos : 0 < aSlope α p q :=
  div_pos (xCoef_pos hα hp0 hp1 hq0 hq1) (div_pos hq0 (rpow_denom_pos α hq1))

lemma bSlope_pos : 0 < bSlope α p q :=
  div_pos (yCoef_pos hα hp0 hp1 hq0 hq1) (div_pos hp0 (rpow_denom_pos α hp1))

lemma aSlope_mul_phi : aSlope α p q * phi α q = xCoef α p q := by
  have _ := hα
  have _ := hp0
  have _ := hp1
  have hφ : phi α q ≠ 0 := (div_pos hq0 (rpow_denom_pos α hq1)).ne'
  rw [aSlope, div_mul_cancel₀ _ hφ]

lemma bSlope_mul_phi : bSlope α p q * phi α p = yCoef α p q := by
  have _ := hα
  have _ := hq0
  have _ := hq1
  have hφ : phi α p ≠ 0 := (div_pos hp0 (rpow_denom_pos α hp1)).ne'
  rw [bSlope, div_mul_cancel₀ _ hφ]

/-- `p b = (1-p)^α y`, since `p/φ_α(p) = (1-p)^α`. -/
lemma mul_bSlope : p * bSlope α p q = (1 - p) ^ α * yCoef α p q := by
  have _ := hα
  have _ := hq0
  have _ := hq1
  have h := (rpow_denom_pos α hp1).ne'
  rw [bSlope, phi]
  field_simp

/-- `q a = (1-q)^α x`. -/
lemma mul_aSlope : q * aSlope α p q = (1 - q) ^ α * xCoef α p q := by
  have _ := hα
  have _ := hp0
  have _ := hp1
  have h := (rpow_denom_pos α hq1).ne'
  rw [aSlope, phi]
  field_simp

/-- `a φ_α(q²) = q/(1+q)^α · x`. -/
lemma aSlope_mul_phi_sq : aSlope α p q * phi α (q ^ 2) = q / (1 + q) ^ α * xCoef α p q := by
  rw [phi_sq_eq hq0.le hq1, ← mul_assoc, aSlope_mul_phi hα hp0 hp1 hq0 hq1]
  ring

lemma Afun_zero : Afun α p q 0 = 1 := by
  rw [Afun, zero_mul, sub_zero, Real.one_rpow, div_one, aSlope_mul_phi hα hp0 hp1 hq0 hq1,
    mul_bSlope hα hp0 hp1 hq0 hq1]
  exact xCoef_add hα hp0 hp1 hq0 hq1

lemma Bfun_zero : Bfun α p q 0 = 1 := by
  rw [Bfun, zero_mul, sub_zero, Real.one_rpow, div_one, mul_aSlope hα hp0 hp1 hq0 hq1,
    bSlope_mul_phi hα hp0 hp1 hq0 hq1]
  exact yCoef_add hα hp0 hp1 hq0 hq1

/-- The limit value `2q/(1+q)^α x + 2p(1-p)^α y`. -/
lemma Nfun_zero :
    Nfun α p q 0 = 2 * q / (1 + q) ^ α * xCoef α p q + 2 * p * (1 - p) ^ α * yCoef α p q := by
  have e : Nfun α p q 0 = 2 * (aSlope α p q * phi α (q ^ 2)) + 2 * p * (p * bSlope α p q) := by
    simp [Nfun]
    ring
  rw [e, aSlope_mul_phi_sq hα hp0 hp1 hq0 hq1, mul_bSlope hα hp0 hp1 hq0 hq1]
  ring

lemma continuousAt_Afun : ContinuousAt (Afun α p q) 0 := by
  have _ := hα
  have _ := hp0
  have _ := hp1
  have _ := hq0
  have _ := hq1
  refine continuousAt_const.add (continuousAt_const.mul ?_)
  exact continuousAt_div_rpow continuousAt_const (continuousAt_id.mul continuousAt_const)
    (by simp)

lemma continuousAt_Bfun : ContinuousAt (Bfun α p q) 0 := by
  have _ := hα
  have _ := hp0
  have _ := hp1
  have _ := hq0
  have _ := hq1
  refine (continuousAt_const.mul ?_).add continuousAt_const
  exact continuousAt_div_rpow continuousAt_const (continuousAt_id.mul continuousAt_const)
    (by simp)

lemma continuousAt_Nfun : ContinuousAt (Nfun α p q) 0 := by
  have _ := hα
  have _ := hp0
  have _ := hp1
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hcs : ∀ c : ℝ, ContinuousAt (fun s : ℝ => s * c) 0 :=
    fun c => continuousAt_id.mul continuousAt_const
  refine ((((continuousAt_id.mul continuousAt_const).mul continuousAt_const).add
    (continuousAt_const.mul ?_)).add (((continuousAt_const.mul
    (continuousAt_const.sub (hcs _))).mul continuousAt_const))).add
    (continuousAt_const.mul ?_) |>.add ((continuousAt_const.mul
    (continuousAt_const.sub (hcs _))).mul ?_)
  · -- `φ_α(q² + (s b)²)`
    have hg : ContinuousAt (fun s : ℝ => q ^ 2 + (s * bSlope α p q) ^ 2) 0 :=
      continuousAt_const.add ((hcs _).pow 2)
    exact continuousAt_div_rpow hg hg
      (by simp only [zero_mul, zero_pow two_ne_zero, add_zero]; exact hq2)
  · -- `(2b - s b²)/(1 - (2 s b - (s b)²))^α`
    exact continuousAt_div_rpow (continuousAt_const.sub (hcs _))
      ((continuousAt_const.mul (hcs _)).sub ((hcs _).pow 2)) (by simp)
  · -- `s b²/(1 - (s b)²)^α`
    exact continuousAt_div_rpow (hcs _) ((hcs _).pow 2) (by simp)

/-- The admissible range is eventually reached as `s ↓ 0`. -/
lemma admissible_eventually : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), Admissible α p q s := by
  have hu : Filter.Tendsto (uS α p q) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have : ContinuousAt (uS α p q) 0 := by
      have e : uS α p q = fun s => s * aSlope α p q := funext (uS_eq α p q)
      rw [e]
      exact continuousAt_id.mul continuousAt_const
    have h0 : uS α p q 0 = 0 := by rw [uS_eq, zero_mul]
    have h := this.tendsto
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hv : Filter.Tendsto (vS α p q) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have : ContinuousAt (vS α p q) 0 := by
      have e : vS α p q = fun s => s * bSlope α p q := funext (vS_eq α p q)
      rw [e]
      exact continuousAt_id.mul continuousAt_const
    have h0 : vS α p q 0 = 0 := by rw [vS_eq, zero_mul]
    have h := this.tendsto
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have _ := hα
  have _ := hp0
  have _ := hq0
  filter_upwards [self_mem_nhdsWithin, hu.eventually_lt_const (by linarith : (0 : ℝ) < 1 - p),
    hv.eventually_lt_const (by linarith : (0 : ℝ) < 1 - q)] with s hs hus hvs
  exact ⟨le_of_lt hs, hus.le, hvs.le⟩

lemma potST_nonneg {s : ℝ} (hs : Admissible α p q s) : 0 ≤ potST α p q s := by
  have hv := vS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hv1 : vS α p q s < 1 := by linarith [hs.2.2]
  exact add_nonneg (mul_nonneg (uS_nonneg hα hp0 hp1 hq0 hq1 hs.1) (phi_nonneg hq0.le hq1))
    (mul_nonneg hp0.le (phi_nonneg hv hv1))

lemma potST_pos {s : ℝ} (hs : Admissible α p q s) (hs0 : 0 < s) : 0 < potST α p q s := by
  have hv := vS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hv1 : vS α p q s < 1 := by linarith [hs.2.2]
  have hu : 0 < uS α p q s := by
    rw [uS_eq]
    exact mul_pos hs0 (aSlope_pos hα hp0 hp1 hq0 hq1)
  exact add_pos_of_pos_of_nonneg (mul_pos hu (div_pos hq0 (rpow_denom_pos α hq1)))
    (mul_nonneg hp0.le (phi_nonneg hv hv1))

lemma potSq_nonneg {s : ℝ} (hs : Admissible α p q s) : 0 ≤ potSq α p q s := by
  have hu := uS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hv := vS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hu1 := hs.2.1
  have hv1 := hs.2.2
  have h1 : 0 ≤ phi α (2 * q - q ^ 2) := phi_nonneg (by nlinarith) (by nlinarith)
  have h2 : 0 ≤ phi α (q ^ 2 + vS α p q s ^ 2) := phi_nonneg (by positivity) (by nlinarith)
  have h3 : 0 ≤ phi α (q ^ 2) := phi_nonneg (by positivity) (by nlinarith)
  have h4 : 0 ≤ phi α (2 * vS α p q s - vS α p q s ^ 2) :=
    phi_nonneg (by nlinarith) (by nlinarith)
  have h5 : 0 ≤ phi α (vS α p q s ^ 2) := phi_nonneg (by positivity) (by nlinarith)
  unfold potSq
  have : 0 ≤ 1 - p - uS α p q s := by linarith
  positivity

lemma potSq_pos {s : ℝ} (hs : Admissible α p q s) (hs0 : 0 < s) : 0 < potSq α p q s := by
  have hu := uS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hv := vS_nonneg hα hp0 hp1 hq0 hq1 hs.1
  have hu1 := hs.2.1
  have hv1 := hs.2.2
  have hu0 : 0 < uS α p q s := by
    rw [uS_eq]
    exact mul_pos hs0 (aSlope_pos hα hp0 hp1 hq0 hq1)
  have h1 : 0 ≤ phi α (2 * q - q ^ 2) := phi_nonneg (by nlinarith) (by nlinarith)
  have h2 : 0 < phi α (q ^ 2 + vS α p q s ^ 2) :=
    div_pos (by positivity) (rpow_denom_pos α (by nlinarith))
  have h3 : 0 ≤ phi α (q ^ 2) := phi_nonneg (by positivity) (by nlinarith)
  have h4 : 0 ≤ phi α (2 * vS α p q s - vS α p q s ^ 2) :=
    phi_nonneg (by nlinarith) (by nlinarith)
  have h5 : 0 ≤ phi α (vS α p q s ^ 2) := phi_nonneg (by positivity) (by nlinarith)
  unfold potSq
  have : 0 ≤ 1 - p - uS α p q s := by linarith
  positivity

/-- **The limit of the ratio**, in real form: the pair potential over the maximal directed
potential tends to `2q/(1+q)^α x + 2p(1-p)^α y` as `s ↓ 0`. -/
lemma tendsto_ratio_real :
    Filter.Tendsto (fun s => potSq α p q s / max (potST α p q s) (potTS α p q s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (2 * q / (1 + q) ^ α * xCoef α p q + 2 * p * (1 - p) ^ α * yCoef α p q)) := by
  have hcont : ContinuousAt (fun s => Nfun α p q s / max (Afun α p q s) (Bfun α p q s)) 0 := by
    refine (continuousAt_Nfun hα hp0 hp1 hq0 hq1).div
      ((continuousAt_Afun hα hp0 hp1 hq0 hq1).max (continuousAt_Bfun hα hp0 hp1 hq0 hq1)) ?_
    show max (Afun α p q 0) (Bfun α p q 0) ≠ 0
    rw [Afun_zero hα hp0 hp1 hq0 hq1, Bfun_zero hα hp0 hp1 hq0 hq1]
    norm_num
  have hval : Nfun α p q 0 / max (Afun α p q 0) (Bfun α p q 0)
      = 2 * q / (1 + q) ^ α * xCoef α p q + 2 * p * (1 - p) ^ α * yCoef α p q := by
    rw [Afun_zero hα hp0 hp1 hq0 hq1, Bfun_zero hα hp0 hp1 hq0 hq1, Nfun_zero hα hp0 hp1 hq0 hq1]
    simp
  have h1 := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rw [hval] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (0 : ℝ) < s := hs
  rw [potSq_eq, potST_eq, potTS_eq, ← mul_max_of_nonneg _ _ hs0.le,
    mul_div_mul_left _ _ hs0.ne']

/-- **The limit of the ratio** (`sec:contraction-lower-bound`): for the comparison
`(ρ_s, ρ_s; τ_s, τ_s)` the eight directed potentials take the two values `P(ρ_s,τ_s)` and
`P(τ_s,ρ_s)`, and the pair potential divided by their maximum tends to
`2q/(1+q)^α x + 2p(1-p)^α y` as `s ↓ 0`. -/
theorem tendsto_ratio :
    Filter.Tendsto (fun s =>
        (PhiDres α (prodPMF (rhoS α p q s) (rhoS α p q s))
          (prodPMF (tauS α p q s) (tauS α p q s)) (SquareRel sixRel)).toReal
        / (max (PhiDres α (rhoS α p q s) (tauS α p q s) sixRel)
            (PhiDres α (tauS α p q s) (rhoS α p q s) sixRel)).toReal)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (2 * q / (1 + q) ^ α * xCoef α p q + 2 * p * (1 - p) ^ α * yCoef α p q)) := by
  refine (tendsto_ratio_real hα hp0 hp1 hq0 hq1).congr' ?_
  filter_upwards [admissible_eventually hα hp0 hp1 hq0 hq1] with s hs
  rw [PhiDres_square_eq hα hp0 hp1 hq0 hq1 hs, PhiDres_rho_tau_eq hα hp0 hp1 hq0 hq1 hs,
    PhiDres_tau_rho_eq hα hp0 hp1 hq0 hq1 hs, ← ENNReal.ofReal_max,
    ENNReal.toReal_ofReal (potSq_nonneg hα hp0 hp1 hq0 hq1 hs),
    ENNReal.toReal_ofReal (le_max_of_le_left (potST_nonneg hα hp0 hp1 hq0 hq1 hs))]

end Limit

/-! ### The lower bound for the linear coefficient -/

/-- A four-law comparison without zero degrees (`sec:contraction-lower-bound`): every charged
source point has positive degree against both target laws, and every charged target point has
positive degree against both source laws. -/
def NoZeroDeg {X : Type} (R : X → X → Prop) (ρ₁ ρ₂ τ₁ τ₂ : PMF X) : Prop :=
  (∀ x, ρ₁ x ≠ 0 → rE τ₁ R x ≠ 0 ∧ rE τ₂ R x ≠ 0)
    ∧ (∀ x, ρ₂ x ≠ 0 → rE τ₁ R x ≠ 0 ∧ rE τ₂ R x ≠ 0)
    ∧ (∀ y, τ₁ y ≠ 0 → rE ρ₁ R y ≠ 0 ∧ rE ρ₂ R y ≠ 0)
    ∧ (∀ y, τ₂ y ≠ 0 → rE ρ₁ R y ≠ 0 ∧ rE ρ₂ R y ≠ 0)

/-- The eight directed potentials `P(ρ_i,τ_j)`, `P(τ_j,ρ_i)` of a four-law comparison are at
most `M`. -/
def EightLe {X : Type} (α : ℝ) (R : X → X → Prop) (ρ₁ ρ₂ τ₁ τ₂ : PMF X) (M : ℝ) : Prop :=
  PhiDres α ρ₁ τ₁ R ≤ ENNReal.ofReal M ∧ PhiDres α ρ₁ τ₂ R ≤ ENNReal.ofReal M
    ∧ PhiDres α ρ₂ τ₁ R ≤ ENNReal.ofReal M ∧ PhiDres α ρ₂ τ₂ R ≤ ENNReal.ofReal M
    ∧ PhiDres α τ₁ ρ₁ R ≤ ENNReal.ofReal M ∧ PhiDres α τ₁ ρ₂ R ≤ ENNReal.ofReal M
    ∧ PhiDres α τ₂ ρ₁ R ≤ ENNReal.ofReal M ∧ PhiDres α τ₂ ρ₂ R ≤ ENNReal.ofReal M

/-- `T_α = 2^{1-α} + 2 K_α (1 - 2^{-α})^{α+1}` (`sec:contraction-lower-bound`). -/
noncomputable def Tlin (α : ℝ) : ℝ :=
  2 ^ (1 - α) + 2 * Kfun α 0 * (1 - 2 ^ (-α)) ^ (α + 1)

/-- `T_α = 2 (β + K_α(β))` at `β = 2^{-α}`. -/
lemma Tlin_eq (α : ℝ) : Tlin α = 2 * 2 ^ (-α) + 2 * Kfun α (2 ^ (-α)) := by
  unfold Tlin Kfun
  rw [sub_zero, Real.one_rpow, mul_one, Real.rpow_sub two_pos, Real.rpow_one,
    Real.rpow_neg two_pos.le]
  ring

/-- `K_α(β) > 0` for `α > 0` and `β < 1`. -/
lemma Kfun_pos {α β : ℝ} (hα : 0 < α) (hβ : β < 1) : 0 < Kfun α β := by
  unfold Kfun
  exact mul_pos (div_pos (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (by linarith) _))
    (Real.rpow_pos_of_pos (by linarith) _)

section LinearCoefficient

variable {α : ℝ} (hα : 0 < α) {lam C : ℝ}
  (hbound : ∀ ρ₁ ρ₂ τ₁ τ₂ : PMF (Fin 6), NoZeroDeg sixRel ρ₁ ρ₂ τ₁ τ₂ →
    ∀ M : ℝ, EightLe α sixRel ρ₁ ρ₂ τ₁ τ₂ M →
      PhiDres α (prodPMF ρ₁ ρ₂) (prodPMF τ₁ τ₂) (SquareRel sixRel)
        ≤ ENNReal.ofReal (lam * M + C * M ^ 2))
include hα hbound

/-- The comparison `(ρ_s, ρ_s; τ_s, τ_s)` has no zero degrees. -/
lemma noZeroDeg_six {p q s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hs : Admissible α p q s) :
    NoZeroDeg sixRel (rhoS α p q s) (rhoS α p q s) (tauS α p q s) (tauS α p q s) := by
  have _ := hbound
  have h := degrees_pos hα hp0 hp1 hq0 hq1 hs
  exact ⟨fun x _ => ⟨h.1 x, h.1 x⟩, fun x _ => ⟨h.1 x, h.1 x⟩, fun y _ => ⟨h.2 y, h.2 y⟩,
    fun y _ => ⟨h.2 y, h.2 y⟩⟩

/-- The eight potentials of `(ρ_s, ρ_s; τ_s, τ_s)` are at most `max{P(ρ_s,τ_s), P(τ_s,ρ_s)}`. -/
lemma eightLe_six {p q s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hs : Admissible α p q s) :
    EightLe α sixRel (rhoS α p q s) (rhoS α p q s) (tauS α p q s) (tauS α p q s)
      (max (potST α p q s) (potTS α p q s)) := by
  have _ := hbound
  unfold EightLe
  rw [PhiDres_rho_tau_eq hα hp0 hp1 hq0 hq1 hs, PhiDres_tau_rho_eq hα hp0 hp1 hq0 hq1 hs]
  have h1 : ENNReal.ofReal (potST α p q s) ≤ ENNReal.ofReal (max (potST α p q s) (potTS α p q s)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have h2 : ENNReal.ofReal (potTS α p q s) ≤ ENNReal.ofReal (max (potST α p q s) (potTS α p q s)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  exact ⟨h1, h1, h1, h1, h2, h2, h2, h2⟩

/-- Under the uniform bound, the ratio at an admissible `s > 0` is at most `λ + C M_s`. -/
lemma ratio_le_of_bound {p q s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hs : Admissible α p q s) (hs0 : 0 < s) :
    potSq α p q s / max (potST α p q s) (potTS α p q s)
      ≤ lam + C * max (potST α p q s) (potTS α p q s) := by
  set Ms := max (potST α p q s) (potTS α p q s) with hMs
  have hM : 0 < Ms := lt_max_of_lt_left (potST_pos hα hp0 hp1 hq0 hq1 hs hs0)
  have h := hbound _ _ _ _ (noZeroDeg_six hα hbound hp0 hp1 hq0 hq1 hs) Ms
    (eightLe_six hα hbound hp0 hp1 hq0 hq1 hs)
  rw [PhiDres_square_eq hα hp0 hp1 hq0 hq1 hs] at h
  rcases ENNReal.ofReal_le_ofReal_iff'.mp h with h | h
  · rw [div_le_iff₀ hM]
    linarith [show (lam + C * Ms) * Ms = lam * Ms + C * Ms ^ 2 by ring]
  · exact absurd h (not_le.mpr (potSq_pos hα hp0 hp1 hq0 hq1 hs hs0))

/-- The limit ratio at fixed `p, q` is at most `λ`. -/
lemma limit_le_lam {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * q / (1 + q) ^ α * xCoef α p q + 2 * p * (1 - p) ^ α * yCoef α p q ≤ lam := by
  have hMs : Filter.Tendsto (fun s => max (potST α p q s) (potTS α p q s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hA : Filter.Tendsto (potST α p q) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have e : potST α p q = fun s => s * Afun α p q s := funext (potST_eq α p q)
      have hc : ContinuousAt (fun s => s * Afun α p q s) 0 :=
        continuousAt_id.mul (continuousAt_Afun hα hp0 hp1 hq0 hq1)
      have h0 : (0 : ℝ) * Afun α p q 0 = 0 := zero_mul _
      have h := hc.tendsto
      rw [h0] at h
      rw [e]
      exact h.mono_left nhdsWithin_le_nhds
    have hB : Filter.Tendsto (potTS α p q) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have e : potTS α p q = fun s => s * Bfun α p q s := funext (potTS_eq α p q)
      have hc : ContinuousAt (fun s => s * Bfun α p q s) 0 :=
        continuousAt_id.mul (continuousAt_Bfun hα hp0 hp1 hq0 hq1)
      have h0 : (0 : ℝ) * Bfun α p q 0 = 0 := zero_mul _
      have h := hc.tendsto
      rw [h0] at h
      rw [e]
      exact h.mono_left nhdsWithin_le_nhds
    simpa using hA.max hB
  have hR : Filter.Tendsto (fun s => lam + C * max (potST α p q s) (potTS α p q s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds lam) := by
    simpa using tendsto_const_nhds.add (hMs.const_mul C)
  refine le_of_tendsto_of_tendsto (tendsto_ratio_real hα hp0 hp1 hq0 hq1) hR ?_
  filter_upwards [admissible_eventually hα hp0 hp1 hq0 hq1, self_mem_nhdsWithin] with s hs hs0
  exact ratio_le_of_bound hα hbound hp0 hp1 hq0 hq1 hs hs0

/-- Letting `q ↑ 1`: `λ ≥ 2^{1-α}(1 - (1-p)^α) + 2p(1-p)^α` for every `p ∈ (0,1)`. -/
lemma lam_ge_of_p {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 ^ (1 - α) * (1 - (1 - p) ^ α) + 2 * p * (1 - p) ^ α ≤ lam := by
  set G : ℝ → ℝ := fun q =>
    2 * q / (1 + q) ^ α * xCoef α p q + 2 * p * (1 - p) ^ α * yCoef α p q with hG
  have hr : ContinuousAt (fun q : ℝ => (1 - q) ^ α) 1 :=
    (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr hα.le)
  have hr1 : (1 - (1 : ℝ)) ^ α = 0 := by rw [sub_self, Real.zero_rpow hα.ne']
  have hden : ContinuousAt (fun q : ℝ => 1 - (1 - q) ^ α * (1 - p) ^ α) 1 :=
    continuousAt_const.sub (hr.mul continuousAt_const)
  have hden1 : (fun q : ℝ => 1 - (1 - q) ^ α * (1 - p) ^ α) 1 ≠ 0 := by
    simp only [hr1, zero_mul, sub_zero]
    exact one_ne_zero
  have hx : ContinuousAt (xCoef α p) 1 := by
    have e : xCoef α p = fun q => (1 - (1 - p) ^ α) / (1 - (1 - q) ^ α * (1 - p) ^ α) := rfl
    rw [e]
    exact continuousAt_const.div hden hden1
  have hy : ContinuousAt (yCoef α p) 1 := by
    have e : yCoef α p = fun q => (1 - (1 - q) ^ α) / (1 - (1 - q) ^ α * (1 - p) ^ α) := rfl
    rw [e]
    exact (continuousAt_const.sub hr).div hden hden1
  have hfrac : ContinuousAt (fun q : ℝ => 2 * q / (1 + q) ^ α) 1 := by
    refine (continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))) ?_
    exact (Real.rpow_pos_of_pos (by norm_num) α).ne'
  have hGc : ContinuousAt G 1 := (hfrac.mul hx).add (continuousAt_const.mul hy)
  have hG1 : G 1 = 2 ^ (1 - α) * (1 - (1 - p) ^ α) + 2 * p * (1 - p) ^ α := by
    simp only [hG, xCoef, yCoef, hr1, zero_mul, sub_zero, div_one, mul_one]
    rw [Real.rpow_sub two_pos, Real.rpow_one, show (1 : ℝ) + 1 = 2 by norm_num]
  have hlim : Filter.Tendsto G (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (2 ^ (1 - α) * (1 - (1 - p) ^ α) + 2 * p * (1 - p) ^ α)) := by
    rw [← hG1]
    exact hGc.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with q hq
  exact limit_le_lam hα hbound hp0 hp1 hq.1 hq.2

end LinearCoefficient

/-- **The lower bound for the linear coefficient** (`sec:contraction-lower-bound`): if
`P^□ ≤ λ M + C M²` holds for every four-law comparison on `Fin 6` without zero degrees, with
`M` a bound for the eight directed potentials, then `λ ≥ T_α`. -/
theorem linear_coeff_ge (α : ℝ) (hα : 1 ≤ α) (lam C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ ρ₁ ρ₂ τ₁ τ₂ : PMF (Fin 6), NoZeroDeg sixRel ρ₁ ρ₂ τ₁ τ₂ →
      ∀ M : ℝ, EightLe α sixRel ρ₁ ρ₂ τ₁ τ₂ M →
        PhiDres α (prodPMF ρ₁ ρ₂) (prodPMF τ₁ τ₂) (SquareRel sixRel)
          ≤ ENNReal.ofReal (lam * M + C * M ^ 2)) :
    Tlin α ≤ lam := by
  have _ := hC
  have hα0 : 0 < α := by linarith
  set β : ℝ := 2 ^ (-α) with hβ
  have hβ0 : 0 < β := Real.rpow_pos_of_pos two_pos _
  have hβ1 : β < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hK : 0 < Kfun α β := Kfun_pos hα0 hβ1
  obtain ⟨q₀, hq0, hq1, hq⟩ := Kfun_attained hα hβ0.le hβ1.le
  have hq0' : 0 < q₀ := by
    rcases eq_or_lt_of_le hq0 with h | h
    · exfalso
      rw [← h, zero_sub, sub_zero, Real.one_rpow, mul_one] at hq
      linarith
    · exact h
  have hq1' : q₀ < 1 := by
    rcases eq_or_lt_of_le hq1 with h | h
    · exfalso
      rw [h, sub_self, Real.zero_rpow hα0.ne', mul_zero] at hq
      linarith
    · exact h
  have h := lam_ge_of_p hα0 hbound hq0' hq1'
  have h2 : (2 : ℝ) ^ (1 - α) = 2 * β := by
    rw [hβ, Real.rpow_sub two_pos, Real.rpow_one, Real.rpow_neg two_pos.le, div_eq_mul_inv]
  rw [Tlin_eq, ← hβ, ← hq]
  rw [h2] at h
  linarith [h]

/-! ### The function `T_α` (`sec:contraction-lower-bound`) -/

/-- The summand `2·2^{-α} + 2(p - 2^{-α})(1-p)^α = 2^{1-α} + (2p - 2^{1-α})(1-p)^α` of
`sec:contraction-lower-bound`, whose maximum over `p ∈ [0,1]` is `T_α`. -/
noncomputable def Tsummand (α p : ℝ) : ℝ :=
  2 * 2 ^ (-α) + 2 * (p - 2 ^ (-α)) * (1 - p) ^ α

lemma two_rpow_neg_pos (α : ℝ) : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos two_pos _

lemma two_rpow_neg_lt_one {α : ℝ} (hα : 0 < α) : (2 : ℝ) ^ (-α) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)

/-- Every summand is at most `T_α` (`Kfun_bound` at `β = 2^{-α}`). -/
lemma Tsummand_le_Tlin {α p : ℝ} (hα : 1 ≤ α) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Tsummand α p ≤ Tlin α := by
  rw [Tlin_eq, Tsummand]
  have h := Kfun_bound (β := 2 ^ (-α)) hα (two_rpow_neg_pos α).le
    (two_rpow_neg_lt_one (by linarith)).le hp0 hp1
  linarith

/-- `T_α` is attained by a summand (`Kfun_attained` at `β = 2^{-α}`). -/
lemma exists_Tsummand_eq {α : ℝ} (hα : 1 ≤ α) :
    ∃ p, 0 ≤ p ∧ p ≤ 1 ∧ Tsummand α p = Tlin α := by
  obtain ⟨p, hp0, hp1, hp⟩ := Kfun_attained (β := 2 ^ (-α)) hα (two_rpow_neg_pos α).le
    (two_rpow_neg_lt_one (by linarith)).le
  refine ⟨p, hp0, hp1, ?_⟩
  rw [Tlin_eq, Tsummand, ← hp]
  ring

/-- `T_1 = 9/8` (`sec:contraction-lower-bound`). -/
theorem Tlin_one : Tlin 1 = 9 / 8 := by
  unfold Tlin Kfun
  rw [sub_self, Real.rpow_zero, Real.one_rpow, sub_zero, Real.one_rpow, Real.rpow_neg_one,
    show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two, Real.rpow_two]
  norm_num

/-- **`T_α` is strictly decreasing on `[1, ∞)`** (`sec:contraction-lower-bound`): at the
maximising `p` of `T_{α'}`, the summand is at most `2·2^{-α} < T_α` when `p ≤ 2^{-α}`, and
otherwise below its value at `α`, since `2^{-α}` and `(1-p)^α` both decrease in `α`. -/
theorem Tlin_strictAntiOn : StrictAntiOn Tlin (Set.Ici 1) := by
  intro α hα α' hα' hlt
  rw [Set.mem_Ici] at hα hα'
  obtain ⟨p, hp0, hp1, hp⟩ := exists_Tsummand_eq (by linarith : 1 ≤ α')
  rw [← hp]
  have hβ0 : 0 < (2 : ℝ) ^ (-α) := two_rpow_neg_pos α
  have hβ1 : (2 : ℝ) ^ (-α) < 1 := two_rpow_neg_lt_one (by linarith)
  have hββ' : (2 : ℝ) ^ (-α') < 2 ^ (-α) :=
    Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
  have hK : 0 < Kfun α (2 ^ (-α)) := Kfun_pos (by linarith) hβ1
  have ht' : (1 - p) ^ α' ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  have ht0' : 0 ≤ (1 - p) ^ α' := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt p (2 ^ (-α)) with hpβ | hpβ
  · have hle : Tsummand α' p ≤ 2 * 2 ^ (-α) := by
      rw [Tsummand]
      rcases le_or_gt ((2 : ℝ) ^ (-α')) p with h | h
      · nlinarith [mul_le_mul_of_nonneg_left ht' (by linarith : 0 ≤ p - 2 ^ (-α'))]
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : p - 2 ^ (-α') ≤ 0) ht0']
    rw [Tlin_eq]
    linarith
  · have hp0' : 0 < p := hβ0.trans hpβ
    have htt' : (1 - p) ^ α' ≤ (1 - p) ^ α :=
      Real.rpow_le_rpow_of_exponent_ge' (by linarith) (by linarith) (by linarith) hlt.le
    have ht'1 : (1 - p) ^ α' < 1 := Real.rpow_lt_one (by linarith) (by linarith) (by linarith)
    calc Tsummand α' p < Tsummand α p := by
          unfold Tsummand
          nlinarith [mul_pos (sub_pos.2 hββ') (sub_pos.2 ht'1),
            mul_nonneg (sub_pos.2 hpβ).le (sub_nonneg.2 htt')]
      _ ≤ Tlin α := Tsummand_le_Tlin hα hp0 hp1

/-- `T` is continuous at every positive exponent. -/
lemma continuousAt_Tlin {α : ℝ} (hα : 0 < α) : ContinuousAt Tlin α := by
  have h2 : ContinuousAt (fun a : ℝ => (2 : ℝ) ^ (-a)) α :=
    continuousAt_const.rpow continuousAt_id.neg (Or.inl two_ne_zero)
  have hβ1 : (2 : ℝ) ^ (-α) < 1 := two_rpow_neg_lt_one hα
  have hK : ContinuousAt (fun a : ℝ => Kfun a 0) α := by
    unfold Kfun
    refine ((continuousAt_id.rpow continuousAt_id (Or.inl hα.ne')).div
      ((continuousAt_id.add continuousAt_const).rpow (continuousAt_id.add continuousAt_const)
        (Or.inl (by show α + 1 ≠ 0; linarith))) ?_).mul
      (continuousAt_const.rpow (continuousAt_id.add continuousAt_const) (Or.inl (by norm_num)))
    exact (Real.rpow_pos_of_pos (by show 0 < α + 1; linarith) _).ne'
  unfold Tlin
  refine (continuousAt_const.rpow (continuousAt_const.sub continuousAt_id)
    (Or.inl two_ne_zero)).add ((continuousAt_const.mul hK).mul ?_)
  exact (continuousAt_const.sub h2).rpow (continuousAt_id.add continuousAt_const)
    (Or.inr (by show 0 < α + 1; linarith))

/-- `(x^r)^3 = x^n` for `x ≥ 0` and `3 r = n`: rational surrogates of cube roots are
compared by cubing. -/
private lemma rpow_cube_eq {x r : ℝ} (hx : 0 ≤ x) {n : ℕ} (hr : r * 3 = n) :
    (x ^ r) ^ 3 = x ^ n := by
  rw [← Real.rpow_natCast (x ^ r) 3, ← Real.rpow_mul hx,
    show r * ((3 : ℕ) : ℝ) = (n : ℝ) by push_cast; linarith, Real.rpow_natCast]

/-- `39/100 ≤ 2^{-4/3} ≤ 2/5` (cubed: `16 ≤ (100/39)³` and `(5/2)³ ≤ 16`). -/
private lemma two_rpow_neg_fourThirds_bounds :
    39 / 100 ≤ (2 : ℝ) ^ (-(4 / 3 : ℝ)) ∧ (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 2 / 5 := by
  have hpos : 0 < (2 : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos two_pos _
  rw [Real.rpow_neg two_pos.le, le_inv_comm₀ (by norm_num) hpos, inv_le_comm₀ hpos (by norm_num),
    ← pow_le_pow_iff_left₀ hpos.le (by norm_num) (by norm_num : (3 : ℕ) ≠ 0),
    ← pow_le_pow_iff_left₀ (by norm_num) hpos.le (by norm_num : (3 : ℕ) ≠ 0),
    rpow_cube_eq (by norm_num) (n := 4) (by norm_num)]
  norm_num

/-- `K_{4/3}(0) ≤ 10/49` (cubed: `(4/3)⁴ ≤ (10/49)³ (7/3)⁷`). -/
private lemma Kfun_fourThirds_zero_le : Kfun (4 / 3) 0 ≤ 10 / 49 := by
  unfold Kfun
  rw [show (4 / 3 : ℝ) + 1 = 7 / 3 by norm_num, sub_zero, Real.one_rpow, mul_one]
  have hA : 0 ≤ (4 / 3 : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hB : 0 < (7 / 3 : ℝ) ^ (7 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [div_le_iff₀ hB, ← pow_le_pow_iff_left₀ hA (by positivity) (by norm_num : (3 : ℕ) ≠ 0),
    mul_pow, rpow_cube_eq (by norm_num) (n := 4) (by norm_num),
    rpow_cube_eq (by norm_num) (n := 7) (by norm_num)]
  norm_num

/-- `(1 - 2^{-4/3})^{7/3} ≤ 8/25` (cubed: `(61/100)⁷ ≤ (8/25)³`). -/
private lemma one_sub_two_rpow_fourThirds_le :
    (1 - (2 : ℝ) ^ (-(4 / 3 : ℝ))) ^ (4 / 3 + 1 : ℝ) ≤ 8 / 25 := by
  obtain ⟨h1, h2⟩ := two_rpow_neg_fourThirds_bounds
  calc (1 - (2 : ℝ) ^ (-(4 / 3 : ℝ))) ^ (4 / 3 + 1 : ℝ)
      ≤ (61 / 100 : ℝ) ^ (4 / 3 + 1 : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    _ ≤ 8 / 25 := by
        rw [show (4 / 3 + 1 : ℝ) = 7 / 3 by norm_num,
          ← pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
            (by norm_num : (3 : ℕ) ≠ 0), rpow_cube_eq (by norm_num) (n := 7) (by norm_num)]
        norm_num

/-- `K_α(β) = K_α(0) (1-β)^{α+1}`. -/
private lemma Kfun_eq_mul (α β : ℝ) : Kfun α β = Kfun α 0 * (1 - β) ^ (α + 1) := by
  unfold Kfun
  simp

/-- `T_{4/3} < 1` (`sec:contraction-lower-bound`): `T_{4/3} ≤ 4/5 + 2 (10/49)(8/25) < 1`. -/
theorem Tlin_fourThirds_lt : Tlin (4 / 3) < 1 := by
  obtain ⟨-, h2⟩ := two_rpow_neg_fourThirds_bounds
  have hK := Kfun_fourThirds_zero_le
  have hP := one_sub_two_rpow_fourThirds_le
  have hP0 : 0 ≤ (1 - (2 : ℝ) ^ (-(4 / 3 : ℝ))) ^ (4 / 3 + 1 : ℝ) :=
    Real.rpow_nonneg (by linarith [two_rpow_neg_lt_one (by norm_num : (0 : ℝ) < 4 / 3)]) _
  have hprod := mul_le_mul hK hP hP0 (by norm_num)
  rw [Tlin_eq, Kfun_eq_mul]
  linarith

/-- **The root of `T`** (`sec:contraction-lower-bound`): `T_α = 1` at exactly one exponent
`α₀ ∈ (1, 4/3)`, by the intermediate value theorem between `T_1 = 9/8` and `T_{4/3} < 1`
and the strict monotonicity. -/
theorem exists_Tlin_root : ∃! α₀, 1 < α₀ ∧ α₀ < 4 / 3 ∧ Tlin α₀ = 1 := by
  have hcont : ContinuousOn Tlin (Set.Icc 1 (4 / 3)) := fun a ha =>
    (continuousAt_Tlin (by linarith [ha.1])).continuousWithinAt
  have hmem : (1 : ℝ) ∈ Set.Ioo (Tlin (4 / 3)) (Tlin 1) :=
    ⟨Tlin_fourThirds_lt, by rw [Tlin_one]; norm_num⟩
  obtain ⟨α₀, hα₀, hT⟩ := intermediate_value_Ioo' (by norm_num : (1 : ℝ) ≤ 4 / 3) hcont hmem
  refine ⟨α₀, ⟨hα₀.1, hα₀.2, hT⟩, ?_⟩
  rintro α₁ ⟨h1, -, hT1⟩
  exact Tlin_strictAntiOn.injOn (Set.mem_Ici.2 h1.le) (Set.mem_Ici.2 hα₀.1.le) (hT1.trans hT.symm)

end GraphMarkovMatching.Stopped
