/-
The per-`ν` numeric closure of the general matching theorem
(`arbitrary_offspring_matching.tex` `sec:numeric`: `thm:ledger-constants`,
`def:constants`, `thm:numeric`, `rem:delta3`, feeding `thm:main-matching`):
at `α = 5/2`, `δ = 1/8`, `L = 1/4`, `K = 4/27`, the closure
inequalities of `varying_failure_uniform` are discharged with explicit
levels built from the charged tilt sum `T`, the support size, an
accessible-index cardinality bound `cN`, and an alphabet bound `nA`,
whenever the label budget satisfies `genSmallC · η ≤ 1`.

* `rootTilt_le` / `genFarMass_le` / `genFarTilt_le`: the ledger
  constants: the ball inverse degree is at most `8`, the far masses
  are at most `2η`;
* `geom_sum_le_geomC`: the nilpotence window is bounded by the closed
  geometric bound `(cN+1)·(CW·cN)^{cN}`;
* `genCW`, `genUC`, `genXiC`, `genKcC`, `genSmallC`: the explicit
  constants;
* `varying_failure_le`: **the general matching theorem with explicit
  constants**: the failure at every height is at most `genKcC · η`
  once `genSmallC · η ≤ 1`;
* `varying_matching_le`: the infinite-tree packaging;
* `delta3_failure_le_of_general`: `ν = δ₃` re-derived as an instance.
-/
import GraphMarkovMatching.Closure.Main
import GraphMarkovMatching.Delta3.NumericClose

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-! ### The ledger constants -/

/-- The root tilt bound (`thm:ledger-constants`, `R_T = 8`): on the
ball of `v0` the inverse degree is
at most `2^{5/2} ≤ 8`. -/
lemma rootTilt_le (hhalf : 2⁻¹ ≤ μ v0) :
    ∀ v, Rv v v0 → (rE μ Rv v) ^ (-(5 / 2 : ℝ)) ≤ 8 := by
  intro v hv
  have hr : 2⁻¹ ≤ rE μ Rv v := by
    rw [rE]
    refine le_trans hhalf (le_trans (le_of_eq ?_) (ENNReal.le_tsum v0))
    rw [if_pos hv]
  calc (rE μ Rv v) ^ (-(5 / 2 : ℝ))
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ (-(5 / 2 : ℝ)) :=
        rpow_neg_antitone (by norm_num) hr
    _ = (2 : ℝ≥0∞) ^ ((5 : ℝ) / 2) := by
        rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
    _ ≤ 8 := ennreal_two_rpow_five_half_le_eight

/-- The far mass (`thm:ledger-constants`, `F_M = 2η`) seen from the
root condition of the screen step is at
most `2η`. -/
lemma genFarMass_le {α : ℝ} (hα : 0 ≤ α)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0) :
    (∑' v, if Rv v v0 then 0 else μ v) ≤ 2 * etaG α Rv μ := by
  have hswap : (∑' v, if Rv v v0 then 0 else μ v) = qE μ Rv v0 := by
    rw [qE]
    refine tsum_congr fun v => ?_
    by_cases hv : Rv v v0
    · rw [if_pos hv, if_pos (hsymm _ _ hv)]
    · rw [if_neg hv, if_neg (fun hc => hv (hsymm _ _ hc))]
  rw [hswap]
  exact qE_zero_le α Rv μ v0 hα hhalf

/-- The tilted far mass of the screen step is at most `2η`
(`thm:ledger-constants`, `F_T = 2η`). -/
lemma genFarTilt_le {α : ℝ} (hα : 0 < α)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0) :
    (∑' v, if Rv v v0 then 0 else μ v * WresD α μ Rv v)
      ≤ 2 * etaG α Rv μ := by
  refine le_trans (ENNReal.tsum_le_tsum fun v => ?_)
    (far_tilt_le α Rv μ v0 hα hsymm hhalf)
  by_cases hv : Rv v v0
  · rw [if_pos hv, if_pos (hsymm _ _ hv)]
  · rw [if_neg hv, if_neg (fun hc => hv (hsymm _ _ hc))]
    refine mul_le_mul_right ?_ _
    by_cases h0 : rE μ Rv v = 0
    · rw [WresD, if_pos h0]
      exact zero_le
    · exact le_of_eq (rE_rpow_neg_eq_WresD μ Rv v h0).symm

/-! ### The geometric bound -/

/-- The geometric sum over the nilpotence window at exact index
cardinality `c`. -/
lemma geom_sum_card_le (c : ℕ) {CW : ℝ≥0∞} (hCW : 1 ≤ CW) :
    ∑ j ∈ Finset.range (c + 1), (CW * c) ^ j
      ≤ ((c : ℝ≥0∞) + 1) * (CW * c) ^ c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · have hbase : (1 : ℝ≥0∞) ≤ CW * c := by
      calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ CW * c := mul_le_mul' hCW (by exact_mod_cast hc)
    calc ∑ j ∈ Finset.range (c + 1), (CW * c) ^ j
        ≤ ∑ _j ∈ Finset.range (c + 1), (CW * c) ^ c :=
          Finset.sum_le_sum fun j hj =>
            pow_le_pow_right' hbase
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = ((c : ℝ≥0∞) + 1) * (CW * c) ^ c := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            Nat.cast_add, Nat.cast_one]

/-- The geometric sum over the nilpotence window, estimated at any upper
bound of the index cardinality. -/
lemma geom_sum_le_geomC {c cN : ℕ} (hc : c ≤ cN) {CW : ℝ≥0∞}
    (hCW : 1 ≤ CW) :
    ∑ j ∈ Finset.range (c + 1), (CW * c) ^ j
      ≤ ((cN : ℝ≥0∞) + 1) * (CW * cN) ^ cN := by
  have hbase : (CW * (c : ℝ≥0∞)) ≤ CW * cN :=
    mul_le_mul_right (Nat.cast_le.mpr hc) CW
  calc ∑ j ∈ Finset.range (c + 1), (CW * c) ^ j
      ≤ ∑ j ∈ Finset.range (c + 1), (CW * cN) ^ j :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left' hbase j
    _ ≤ ∑ j ∈ Finset.range (cN + 1), (CW * cN) ^ j :=
        Finset.sum_le_sum_of_subset
          (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr
            (lt_of_lt_of_le hx (Nat.succ_le_succ hc)))
    _ ≤ ((cN : ℝ≥0∞) + 1) * (CW * cN) ^ cN := geom_sum_card_le cN hCW

/-! ### The explicit constants -/

/-- The matrix entry bound `CW = 32T + 4`: it dominates `4` and the
root-tilt term `4·(8·T)`. -/
noncomputable def genCW (T : ℝ≥0∞) : ℝ≥0∞ := 32 * T + 4

/-- The geometric bound of the nilpotence window at index
cardinality bound `cN`. -/
noncomputable def genGeomC (cN : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ :=
  ((cN : ℝ≥0∞) + 1) * (genCW T * cN) ^ cN

/-- The screen bound coefficient: the screen bound is `genUC · η`. -/
noncomputable def genUC (T : ℝ≥0∞) : ℝ≥0∞ := 16 * T + 4

/-- The invariant bound coefficient: the invariant bound is
`genXiC · η`. -/
noncomputable def genXiC (cN : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ :=
  genGeomC cN T * genUC T

/-- The ordinary bound coefficient: the failure bound is
`genKcC · η`. -/
noncomputable def genKcC (cN cS : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ :=
  120 + (72 + 48 * (T * cS)) * genXiC cN T

/-- The smallness threshold (`def:constants`; its five summands are
the absorption budgets of `thm:numeric`): the closure inequalities
hold once
`genSmallC · η ≤ 1`. -/
noncomputable def genSmallC (cN cS nA : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ :=
  4 + 3 * genKcC cN cS T
    + (1 + 8 * T) * (12 * (genKcC cN cS T * genXiC cN T)
        + 2 * (((nA : ℝ≥0∞) * genXiC cN T) * ((nA : ℝ≥0∞) * genXiC cN T)))
    + (160 * (genKcC cN cS T * genKcC cN cS T)
        + 4 * ((T * cS) * (genXiC cN T * genXiC cN T)))
    + 85 * (genKcC cN cS T + 12 * genXiC cN T
        + 8 * ((T * cS) * genXiC cN T) + 1)

section SmallAccess

variable (cN cS nA : ℕ) (T : ℝ≥0∞)

lemma four_le_genSmallC : (4 : ℝ≥0∞) ≤ genSmallC cN cS nA T := by
  rw [genSmallC]
  exact le_trans le_self_add
    (le_trans le_self_add (le_trans le_self_add le_self_add))

lemma lin_le_genSmallC : 3 * genKcC cN cS T ≤ genSmallC cN cS nA T := by
  rw [genSmallC]
  exact le_trans le_add_self
    (le_trans le_self_add (le_trans le_self_add le_self_add))

lemma screen_le_genSmallC :
    (1 + 8 * T) * (12 * (genKcC cN cS T * genXiC cN T)
        + 2 * (((nA : ℝ≥0∞) * genXiC cN T) * ((nA : ℝ≥0∞) * genXiC cN T)))
      ≤ genSmallC cN cS nA T := by
  rw [genSmallC]
  exact le_trans le_add_self (le_trans le_self_add le_self_add)

lemma cell_le_genSmallC :
    160 * (genKcC cN cS T * genKcC cN cS T)
        + 4 * ((T * cS) * (genXiC cN T * genXiC cN T))
      ≤ genSmallC cN cS nA T := by
  rw [genSmallC]
  exact le_trans le_add_self le_self_add

lemma cross_le_genSmallC :
    85 * (genKcC cN cS T + 12 * genXiC cN T
        + 8 * ((T * cS) * genXiC cN T) + 1)
      ≤ genSmallC cN cS nA T := by
  rw [genSmallC]
  exact le_add_self

end SmallAccess

/-- **The final inequality of `eq:main-bound`**: the smallness budget contains the
summand `3 · genKcC`, so below the threshold the failure barrier is at most `1/3`. -/
lemma genKcC_le_third (cN cS nA : ℕ) (T η : ℝ≥0∞)
    (hsmall : genSmallC cN cS nA T * η ≤ 1) :
    genKcC cN cS T * η ≤ 3⁻¹ := by
  have h3 : genKcC cN cS T * η * 3 ≤ 1 := by
    calc genKcC cN cS T * η * 3 = (3 * genKcC cN cS T) * η := by ring
      _ ≤ genSmallC cN cS nA T * η := by
          refine mul_le_mul_left ?_ η
          rw [genSmallC]
          exact ((le_add_self.trans le_self_add).trans le_self_add).trans le_self_add
      _ ≤ 1 := hsmall
  exact ENNReal.le_inv_iff_mul_le.mpr h3

/-! ### The general matching theorem with explicit constants -/

/-- **The general matching theorem with explicit constants**
(`thm:numeric`, proving `thm:main-matching` at finite heights)
(`thm:main-matching`, numeric closure): for an arbitrary offspring law charged
exactly on a support `S ⊆ {0,…,N}` with `2 ≤ N`, a countable label
graph with reflexive symmetric relation whose root label carries at
least half the mass, a charged tilt sum at most `T`, an accessible
index of cardinality at most `cN`, and a target alphabet of
cardinality at most `nA`, if the label budget satisfies
`genSmallC · η ≤ 1` then the matching failure at every height is at
most `genKcC · η`. -/
theorem varying_failure_le (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T * etaG (5 / 2) Rv μ ≤ 1) :
    ∀ h, (∑' x, Tlaw μ ν v0 h x
        * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x)
      ≤ genKcC cN S.card T * etaG (5 / 2) Rv μ := by
  set η := etaG (5 / 2 : ℝ) Rv μ with hηdef
  -- linear and quadratic absorption from the smallness hypothesis
  have hlin : ∀ x : ℝ≥0∞, x ≤ genSmallC cN S.card nA T → x * η ≤ 1 :=
    fun x hx => le_trans (mul_le_mul_left hx η) hsmall
  have hquad : ∀ x : ℝ≥0∞, x ≤ genSmallC cN S.card nA T
      → x * (η * η) ≤ η := by
    intro x hx
    calc x * (η * η) = (x * η) * η := by ring
      _ ≤ 1 * η := mul_le_mul_left (hlin x hx) η
      _ = η := one_mul η
  -- the `ofReal` atoms
  have hof3 : ENNReal.ofReal ((5 : ℝ) / 2) ≤ 3 := by
    rw [show ((3 : ℝ≥0∞)) = ENNReal.ofReal (3 : ℝ) from by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hof5 : ENNReal.ofReal (2 * ((5 : ℝ) / 2)) ≤ 5 := by
    rw [show ((5 : ℝ≥0∞)) = ENNReal.ofReal (5 : ℝ) from by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hof8 : ENNReal.ofReal ((2 : ℝ) ^ ((5 : ℝ) / 2)) ≤ 8 := by
    rw [show ((8 : ℝ≥0∞)) = ENNReal.ofReal (8 : ℝ) from by simp]
    exact ENNReal.ofReal_le_ofReal two_rpow_five_half_le_eight
  have hofsum : ENNReal.ofReal (5 / 6) + ENNReal.ofReal (1 / 6) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      show (5 / 6 + 1 / 6 : ℝ) = 1 from by norm_num, ENNReal.ofReal_one]
  have f6 : ENNReal.ofReal (1 / 6) * 6 = 1 := by
    rw [show ((6 : ℝ≥0∞)) = ENNReal.ofReal (6 : ℝ) from by simp,
      ← ENNReal.ofReal_mul (by norm_num),
      show ((1 : ℝ) / 6 * 6) = 1 from by norm_num, ENNReal.ofReal_one]
  -- the root budgets
  have hq2 : qE μ Rv v0 ≤ 2 * η :=
    qE_zero_le (5 / 2) Rv μ v0 (by norm_num) hhalf
  have h4η : (4 : ℝ≥0∞) * η ≤ 1 := hlin 4 (four_le_genSmallC cN S.card nA T)
  have hqhalf : qE μ Rv v0 ≤ 2⁻¹ := by
    refine le_trans hq2 (ENNReal.le_inv_iff_mul_le.mpr ?_)
    calc (2 : ℝ≥0∞) * η * 2 = 4 * η := by ring
      _ ≤ 1 := h4η
  have hphi : phiE (5 / 2) (q μ Rv v0) ≤ 16 * η := by
    calc phiE (5 / 2) (q μ Rv v0)
        ≤ ENNReal.ofReal (2 ^ ((5 : ℝ) / 2)) * qE μ Rv v0 :=
          phiE_le_of_qE_le_half (by norm_num) μ Rv v0 hqhalf
      _ ≤ 8 * (2 * η) := mul_le_mul' hof8 hq2
      _ = 16 * η := by ring
  have hroot : η + phiE (5 / 2) (q μ Rv v0) ≤ 17 * η := by
    calc η + phiE (5 / 2) (q μ Rv v0) ≤ η + 16 * η :=
        add_le_add le_rfl hphi
      _ = 17 * η := by ring
  -- the running ordinary bound is tame
  have hαa : ENNReal.ofReal ((5 : ℝ) / 2) * (genKcC cN S.card T * η)
      ≤ 1 := by
    calc ENNReal.ofReal ((5 : ℝ) / 2) * (genKcC cN S.card T * η)
        ≤ 3 * (genKcC cN S.card T * η) := mul_le_mul_left hof3 _
      _ = (3 * genKcC cN S.card T) * η := by ring
      _ ≤ 1 := hlin _ (lin_le_genSmallC cN S.card nA T)
  have hone2 : 1 + ENNReal.ofReal ((5 : ℝ) / 2)
      * (genKcC cN S.card T * η) ≤ 2 := by
    calc 1 + ENNReal.ofReal ((5 : ℝ) / 2) * (genKcC cN S.card T * η)
        ≤ 1 + 1 := add_le_add le_rfl hαa
      _ = 2 := one_add_one_eq_two
  -- the ledger constants
  have hRT8 : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-(5 / 2 : ℝ)) ≤ 8 :=
    rootTilt_le Rv μ v0 hhalf
  have hFM2 : (∑' v, if Rv v v0 then 0 else μ v) ≤ 2 * η :=
    genFarMass_le Rv μ v0 (α := 5 / 2) (by norm_num) hsymm hhalf
  have hFT2 : (∑' v, if Rv v v0 then 0 else μ v * WresD (5 / 2) μ Rv v)
      ≤ 2 * η :=
    genFarTilt_le Rv μ v0 (α := 5 / 2) (by norm_num) hsymm hhalf
  have hCW1 : (1 : ℝ≥0∞) ≤ genCW T := by
    rw [genCW]
    exact le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 4) le_add_self
  have hCW4 : (4 : ℝ≥0∞) ≤ genCW T := by
    rw [genCW]
    exact le_add_self
  have hCWRT : 4 * ((8 : ℝ≥0∞) * T) ≤ genCW T := by
    rw [genCW]
    calc (4 : ℝ≥0∞) * (8 * T) = 32 * T := by ring
      _ ≤ 32 * T + 4 := le_self_add
  -- the invariant bound
  have hXi : (∑ j ∈ Finset.range
        (Fintype.card {sc // sc ∈ scrIndex N S} + 1),
        (genCW T * (scrIndex N S).card) ^ j) * (genUC T * η)
      ≤ genXiC cN T * η := by
    have hcard : Fintype.card {sc // sc ∈ scrIndex N S}
        = (scrIndex N S).card := Fintype.card_coe _
    rw [hcard]
    calc (∑ j ∈ Finset.range ((scrIndex N S).card + 1),
          (genCW T * (scrIndex N S).card) ^ j) * (genUC T * η)
        ≤ (((cN : ℝ≥0∞) + 1) * (genCW T * cN) ^ cN) * (genUC T * η) :=
          mul_le_mul_left (geom_sum_le_geomC hcN hCW1) _
      _ = genXiC cN T * η := by rw [genXiC, genGeomC]; ring
  -- the level bounds
  have hb1 : η + phiE (5 / 2) (q μ Rv v0) ≤ genKcC cN S.card T * η := by
    refine le_trans hroot (mul_le_mul_left ?_ η)
    rw [genKcC]
    exact le_trans (by norm_num : (17 : ℝ≥0∞) ≤ 120) le_self_add
  have hb2 : baseScreenBound (5 / 2) Rv μ ≤ genUC T * η := by
    rw [baseScreenBound, ← hηdef, genUC]
    exact mul_le_mul_left le_add_self η
  -- the screen closure inequality
  have hu : genG (5 / 2) T 8 (2 * η) (2 * η) (tgtUniv N).card
      (genKcC cN S.card T * η) (genXiC cN T * η) ≤ genUC T * η := by
    rw [genG]
    have hg2 : (2 * η) * (T * (2 * ((1 + ENNReal.ofReal (5 / 2)
          * (genKcC cN S.card T * η)) * (1 + ENNReal.ofReal (5 / 2)
          * (genKcC cN S.card T * η))))) ≤ 16 * T * η := by
      calc (2 * η) * (T * (2 * ((1 + ENNReal.ofReal (5 / 2)
            * (genKcC cN S.card T * η)) * (1 + ENNReal.ofReal (5 / 2)
            * (genKcC cN S.card T * η)))))
          ≤ (2 * η) * (T * (2 * (2 * 2))) :=
            mul_le_mul_right (mul_le_mul_right
              (mul_le_mul_right (mul_le_mul' hone2 hone2) 2) T) _
        _ = 16 * T * η := by ring
    have hg3 : (1 + 8 * T) * (4 * (ENNReal.ofReal (5 / 2)
          * (genKcC cN S.card T * η) * (genXiC cN T * η))
        + 2 * ((((tgtUniv N).card : ℝ≥0∞) * (genXiC cN T * η))
            * (((tgtUniv N).card : ℝ≥0∞) * (genXiC cN T * η))))
        ≤ η := by
      have h31 : ENNReal.ofReal (5 / 2) * (genKcC cN S.card T * η)
          * (genXiC cN T * η)
          ≤ 3 * (genKcC cN S.card T * η) * (genXiC cN T * η) :=
        mul_le_mul_left (mul_le_mul_left hof3 _) _
      have h32 : ((tgtUniv N).card : ℝ≥0∞) * (genXiC cN T * η)
          ≤ (nA : ℝ≥0∞) * (genXiC cN T * η) :=
        mul_le_mul_left (Nat.cast_le.mpr hnA) _
      calc (1 + 8 * T) * (4 * (ENNReal.ofReal (5 / 2)
            * (genKcC cN S.card T * η) * (genXiC cN T * η))
          + 2 * ((((tgtUniv N).card : ℝ≥0∞) * (genXiC cN T * η))
              * (((tgtUniv N).card : ℝ≥0∞) * (genXiC cN T * η))))
          ≤ (1 + 8 * T) * (4 * (3 * (genKcC cN S.card T * η)
              * (genXiC cN T * η))
            + 2 * (((nA : ℝ≥0∞) * (genXiC cN T * η))
                * ((nA : ℝ≥0∞) * (genXiC cN T * η)))) :=
            mul_le_mul_right (add_le_add (mul_le_mul_right h31 4)
              (mul_le_mul_right (mul_le_mul' h32 h32) 2)) _
        _ = ((1 + 8 * T) * (12 * (genKcC cN S.card T * genXiC cN T)
              + 2 * (((nA : ℝ≥0∞) * genXiC cN T)
                  * ((nA : ℝ≥0∞) * genXiC cN T)))) * (η * η) := by ring
        _ ≤ η := hquad _ (screen_le_genSmallC cN S.card nA T)
    have hfinal : 2 * η + 16 * T * η + η ≤ genUC T * η := by
      calc 2 * η + 16 * T * η + η = (16 * T + 3) * η := by ring
        _ ≤ (16 * T + 4) * η :=
            mul_le_mul_left (add_le_add le_rfl (by norm_num)) η
        _ = genUC T * η := by rw [genUC]
    exact le_trans (add_le_add (add_le_add le_rfl hg2) hg3) hfinal
  -- the ordinary closure inequality
  have hclose : genF (5 / 2) (1 / 8) (1 / 4) (4 / 27)
      (η + phiE (5 / 2) (q μ Rv v0)) T S.card
      (genKcC cN S.card T * η) (genXiC cN T * η)
      ≤ genKcC cN S.card T * η := by
    have hD : cellCB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
          (genKcC cN S.card T * η) (genXiC cN T * η) (genXiC cN T * η)
        + oneSidedBound (5 / 2) T S.card (genKcC cN S.card T * η)
            (genXiC cN T * η)
        ≤ ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η) + η
          + (11 * genXiC cN T
              + 8 * ((T * S.card) * genXiC cN T)) * η := by
      rw [cellCB, oneSidedBound]
      have hq1 : ENNReal.ofReal (2 * (1 / 4) + 2 * (1 + (1 : ℝ) / 8)
            * (4 / 27)) * (genKcC cN S.card T * η)
          ≤ ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (by norm_num)) _
      have hB160 : ENNReal.ofReal (2 * (1 / 4) * chordConst ((5 : ℝ) / 2)
            + 20 + 2 * (1 + ((1 : ℝ) / 8)⁻¹) * ((5 : ℝ) / 2) ^ 2)
          ≤ 160 := by
        rw [show ((160 : ℝ≥0∞)) = ENNReal.ofReal (160 : ℝ) from by simp]
        exact ENNReal.ofReal_le_ofReal
          (by linarith [chordConst_five_half_le])
      have hq2' : ENNReal.ofReal (2 * (1 / 4) * chordConst ((5 : ℝ) / 2)
            + 20 + 2 * (1 + ((1 : ℝ) / 8)⁻¹) * ((5 : ℝ) / 2) ^ 2)
            * (genKcC cN S.card T * η) ^ 2
          ≤ (160 * (genKcC cN S.card T * genKcC cN S.card T))
              * (η * η) := by
        calc ENNReal.ofReal (2 * (1 / 4) * chordConst ((5 : ℝ) / 2)
              + 20 + 2 * (1 + ((1 : ℝ) / 8)⁻¹) * ((5 : ℝ) / 2) ^ 2)
              * (genKcC cN S.card T * η) ^ 2
            ≤ 160 * (genKcC cN S.card T * η) ^ 2 :=
              mul_le_mul_left hB160 _
          _ = (160 * (genKcC cN S.card T * genKcC cN S.card T))
              * (η * η) := by ring
      have hof94 : ENNReal.ofReal (2 * (1 + (1 : ℝ) / 8)) ≤ 3 := by
        rw [show ((3 : ℝ≥0∞)) = ENNReal.ofReal (3 : ℝ) from by simp]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      have hq3 : ENNReal.ofReal (2 * (1 + (1 : ℝ) / 8))
            * (genXiC cN T * η) ≤ 3 * (genXiC cN T * η) :=
        mul_le_mul_left hof94 _
      have hq4 : 4 * (genXiC cN T * η) * (1 + ENNReal.ofReal (5 / 2)
            * (genKcC cN S.card T * η)) ≤ 8 * (genXiC cN T * η) := by
        calc 4 * (genXiC cN T * η) * (1 + ENNReal.ofReal (5 / 2)
              * (genKcC cN S.card T * η))
            ≤ 4 * (genXiC cN T * η) * 2 := mul_le_mul_right hone2 _
          _ = 8 * (genXiC cN T * η) := by ring
      have hos : T * ((S.card : ℝ≥0∞) * (4 * (genXiC cN T * η)
            * (1 + ENNReal.ofReal (5 / 2) * (genKcC cN S.card T * η))
            + 4 * ((genXiC cN T * η) * (genXiC cN T * η))))
          ≤ 8 * ((T * S.card) * genXiC cN T) * η
            + (4 * ((T * S.card) * (genXiC cN T * genXiC cN T)))
                * (η * η) := by
        calc T * ((S.card : ℝ≥0∞) * (4 * (genXiC cN T * η)
              * (1 + ENNReal.ofReal (5 / 2) * (genKcC cN S.card T * η))
              + 4 * ((genXiC cN T * η) * (genXiC cN T * η))))
            ≤ T * ((S.card : ℝ≥0∞) * (8 * (genXiC cN T * η)
              + 4 * ((genXiC cN T * η) * (genXiC cN T * η)))) :=
              mul_le_mul_right (mul_le_mul_right
                (add_le_add hq4 le_rfl) _) _
          _ = 8 * ((T * S.card) * genXiC cN T) * η
              + (4 * ((T * S.card) * (genXiC cN T * genXiC cN T)))
                  * (η * η) := by ring
      calc ENNReal.ofReal (2 * (1 / 4) + 2 * (1 + (1 : ℝ) / 8)
            * (4 / 27)) * (genKcC cN S.card T * η)
          + ENNReal.ofReal (2 * (1 / 4) * chordConst ((5 : ℝ) / 2)
              + 20 + 2 * (1 + ((1 : ℝ) / 8)⁻¹) * ((5 : ℝ) / 2) ^ 2)
              * (genKcC cN S.card T * η) ^ 2
          + ENNReal.ofReal (2 * (1 + (1 : ℝ) / 8)) * (genXiC cN T * η)
          + 4 * (genXiC cN T * η) * (1 + ENNReal.ofReal (5 / 2)
              * (genKcC cN S.card T * η))
          + T * ((S.card : ℝ≥0∞) * (4 * (genXiC cN T * η)
              * (1 + ENNReal.ofReal (5 / 2) * (genKcC cN S.card T * η))
              + 4 * ((genXiC cN T * η) * (genXiC cN T * η))))
          ≤ ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η)
            + (160 * (genKcC cN S.card T * genKcC cN S.card T))
                * (η * η)
            + 3 * (genXiC cN T * η) + 8 * (genXiC cN T * η)
            + (8 * ((T * S.card) * genXiC cN T) * η
              + (4 * ((T * S.card) * (genXiC cN T * genXiC cN T)))
                  * (η * η)) :=
            add_le_add (add_le_add (add_le_add
              (add_le_add hq1 hq2') hq3) hq4) hos
        _ = ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η)
            + (160 * (genKcC cN S.card T * genKcC cN S.card T)
              + 4 * ((T * S.card) * (genXiC cN T * genXiC cN T)))
                * (η * η)
            + (11 * genXiC cN T
                + 8 * ((T * S.card) * genXiC cN T)) * η := by ring
        _ ≤ ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η) + η
            + (11 * genXiC cN T
                + 8 * ((T * S.card) * genXiC cN T)) * η :=
            add_le_add (add_le_add le_rfl
              (hquad _ (cell_le_genSmallC cN S.card nA T))) le_rfl
    have hDcrude : cellCB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
          (genKcC cN S.card T * η) (genXiC cN T * η) (genXiC cN T * η)
        + oneSidedBound (5 / 2) T S.card (genKcC cN S.card T * η)
            (genXiC cN T * η)
        ≤ (genKcC cN S.card T + 12 * genXiC cN T
            + 8 * ((T * S.card) * genXiC cN T) + 1) * η := by
      refine le_trans hD ?_
      have h56 : ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η)
          ≤ genKcC cN S.card T * η := by
        calc ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η)
            ≤ 1 * (genKcC cN S.card T * η) :=
              mul_le_mul_left (ENNReal.ofReal_le_one.mpr (by norm_num)) _
          _ = genKcC cN S.card T * η := one_mul _
      calc ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η) + η
            + (11 * genXiC cN T
                + 8 * ((T * S.card) * genXiC cN T)) * η
          ≤ genKcC cN S.card T * η + η
            + (11 * genXiC cN T
                + 8 * ((T * S.card) * genXiC cN T)) * η :=
            add_le_add (add_le_add h56 le_rfl) le_rfl
        _ = (genKcC cN S.card T + 11 * genXiC cN T
            + 8 * ((T * S.card) * genXiC cN T) + 1) * η := by ring
        _ ≤ (genKcC cN S.card T + 12 * genXiC cN T
            + 8 * ((T * S.card) * genXiC cN T) + 1) * η := by
            refine mul_le_mul_left (add_le_add (add_le_add
              (add_le_add le_rfl ?_) le_rfl) le_rfl) η
            exact mul_le_mul_left (by norm_num) _
    have hcross : ENNReal.ofReal (2 * (5 / 2))
        * ((η + phiE (5 / 2) (q μ Rv v0))
          * (cellCB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
              (genKcC cN S.card T * η) (genXiC cN T * η)
              (genXiC cN T * η)
            + oneSidedBound (5 / 2) T S.card (genKcC cN S.card T * η)
                (genXiC cN T * η)))
        ≤ η := by
      calc ENNReal.ofReal (2 * (5 / 2))
          * ((η + phiE (5 / 2) (q μ Rv v0))
            * (cellCB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
                (genKcC cN S.card T * η) (genXiC cN T * η)
                (genXiC cN T * η)
              + oneSidedBound (5 / 2) T S.card
                  (genKcC cN S.card T * η) (genXiC cN T * η)))
          ≤ 5 * ((17 * η) * ((genKcC cN S.card T + 12 * genXiC cN T
              + 8 * ((T * S.card) * genXiC cN T) + 1) * η)) :=
            mul_le_mul' hof5 (mul_le_mul' hroot hDcrude)
        _ = (85 * (genKcC cN S.card T + 12 * genXiC cN T
            + 8 * ((T * S.card) * genXiC cN T) + 1)) * (η * η) := by
            ring
        _ ≤ η := hquad _ (cross_le_genSmallC cN S.card nA T)
    have h6 : (19 : ℝ≥0∞) + 11 * genXiC cN T
        + 8 * ((T * S.card) * genXiC cN T)
        ≤ ENNReal.ofReal (1 / 6) * genKcC cN S.card T := by
      have h66 : (6 : ℝ≥0∞) * (19 + 11 * genXiC cN T
          + 8 * ((T * S.card) * genXiC cN T)) ≤ genKcC cN S.card T := by
        rw [genKcC]
        calc (6 : ℝ≥0∞) * (19 + 11 * genXiC cN T
              + 8 * ((T * S.card) * genXiC cN T))
            = 114 + (66 + 48 * (T * S.card)) * genXiC cN T := by ring
          _ ≤ 120 + (72 + 48 * (T * S.card)) * genXiC cN T :=
              add_le_add (by norm_num) (mul_le_mul_left
                (add_le_add (by norm_num) le_rfl) _)
      calc (19 : ℝ≥0∞) + 11 * genXiC cN T
            + 8 * ((T * S.card) * genXiC cN T)
          = (ENNReal.ofReal (1 / 6) * 6) * (19 + 11 * genXiC cN T
              + 8 * ((T * S.card) * genXiC cN T)) := by
            rw [f6, one_mul]
        _ = ENNReal.ofReal (1 / 6) * (6 * (19 + 11 * genXiC cN T
              + 8 * ((T * S.card) * genXiC cN T))) := by
            rw [mul_assoc]
        _ ≤ ENNReal.ofReal (1 / 6) * genKcC cN S.card T :=
            mul_le_mul_right h66 _
    have hfinal : 17 * η + (ENNReal.ofReal (5 / 6)
          * (genKcC cN S.card T * η) + η
          + (11 * genXiC cN T + 8 * ((T * S.card) * genXiC cN T)) * η)
          + η
        ≤ genKcC cN S.card T * η := by
      calc 17 * η + (ENNReal.ofReal (5 / 6)
            * (genKcC cN S.card T * η) + η
            + (11 * genXiC cN T
                + 8 * ((T * S.card) * genXiC cN T)) * η) + η
          = ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η)
            + (19 + 11 * genXiC cN T
                + 8 * ((T * S.card) * genXiC cN T)) * η := by ring
        _ ≤ ENNReal.ofReal (5 / 6) * (genKcC cN S.card T * η)
            + ENNReal.ofReal (1 / 6) * (genKcC cN S.card T * η) := by
            refine add_le_add le_rfl ?_
            calc (19 + 11 * genXiC cN T
                  + 8 * ((T * S.card) * genXiC cN T)) * η
                ≤ (ENNReal.ofReal (1 / 6) * genKcC cN S.card T) * η :=
                  mul_le_mul_left h6 η
              _ = ENNReal.ofReal (1 / 6) * (genKcC cN S.card T * η) :=
                  mul_assoc _ _ _
        _ = (ENNReal.ofReal (5 / 6) + ENNReal.ofReal (1 / 6))
            * (genKcC cN S.card T * η) := (add_mul _ _ _).symm
        _ = 1 * (genKcC cN S.card T * η) := by rw [hofsum]
        _ = genKcC cN S.card T * η := one_mul _
    rw [genF]
    exact le_trans (add_le_add (add_le_add hroot hD) hcross) hfinal
  intro h
  exact varying_failure_uniform (5 / 2) Rv μ ν v0 N S
    (δ := 1 / 8) (L := 1 / 4) (K := 4 / 27)
    (by norm_num) (by norm_num) (by norm_num) quarter_L_bound
    (by norm_num) fourTwentySeventh_K_bound
    hrefl hsymm hhalf hN hS hSne hSsupp
    T 8 (2 * η) (2 * η) (genCW T)
    hT hRT8 hFM2 hFT2 hCW4 hCWRT
    (genKcC cN S.card T) (genUC T * η) (genXiC cN T * η)
    hb1 hb2 hXi hu hclose h

/-- **The general matching theorem on the infinite tree with explicit
constants**: under the numeric hypotheses, two independent infinite
varying-offspring labellings admit a single automorphism of the
infinite binary tree matching every vertex with probability at least
`1 - genKcC · η`. -/
theorem varying_matching_le {Ω : Type*} [MeasurableSpace Ω]
    (Pm : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure Pm]
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T * etaG (5 / 2) Rv μ ≤ 1)
    (X Y : (n : ℕ) → Ω → FullLab (V × ℕ) n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Pm.map (fun ω => (X n ω, Y n ω))
        = (prodPMF (Tlaw μ ν v0 n) (Tlaw μ ν v0 n)).toMeasure) :
    1 - genKcC cN S.card T * etaG (5 / 2) Rv μ
      ≤ Pm {ω | InfMatch (labRel Rv)
          (fun n => X n ω) (fun n => Y n ω)} :=
  varyingMatching_infinite Rv μ ν v0 Pm
    (genKcC cN S.card T * etaG (5 / 2) Rv μ)
    (varying_failure_le Rv μ v0 ν N S hrefl hsymm hhalf hN hS hSne
      hSsupp T hT cN nA hcN hnA hsmall)
    X Y hX hY hpair hlaw

/-- **The general matching theorem on the infinite tree, with the trajectory space
constructed** (`thm:main-matching`, `eq:main-bound-infinite`): under the numeric
hypotheses, on the product of the two trajectory measures the consistent level processes
realise the two independent infinite labellings, and a single automorphism of the
infinite binary tree matches every vertex with probability at least `1 - genKcC · η`.
No probability space is assumed. -/
theorem varying_matching_le_traj
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T * etaG (5 / 2) Rv μ ≤ 1) :
    1 - genKcC cN S.card T * etaG (5 / 2) Rv μ
      ≤ TlawPair μ ν v0 {ω | InfMatch (labRel Rv)
          (fun n => consLab n ω.1) (fun n => consLab n ω.2)} :=
  varyingMatching_infinite_traj Rv μ ν v0
    (genKcC cN S.card T * etaG (5 / 2) Rv μ)
    (varying_failure_le Rv μ v0 ν N S hrefl hsymm hhalf hN hS hSne
      hSsupp T hT cN nA hcN hnA hsmall)

/-! ### Cardinality bounds for instantiation -/

/-- The bounded alphabet has at most `2N + 3` letters. -/
lemma tgtUniv_card_le (N : ℕ) : (tgtUniv N).card ≤ 2 * N + 3 := by
  rw [tgtUniv]
  refine le_trans (Finset.card_insert_le _ _) ?_
  have h := Finset.card_union_le
    ((Finset.range (N + 1)).image Tgt.Z)
    ((Finset.range (N + 1)).image Tgt.Fk)
  have h1 := Finset.card_image_le
    (s := Finset.range (N + 1)) (f := Tgt.Z)
  have h2 := Finset.card_image_le
    (s := Finset.range (N + 1)) (f := Tgt.Fk)
  rw [Finset.card_range] at h1 h2
  omega

/-- The bounded screen family has at most `(2N+3) · (2^{2N+3} · (2N+4))`
members. -/
lemma screenUniv_card_le (N : ℕ) :
    (screenUniv N).card ≤ (2 * N + 3) * (2 ^ (2 * N + 3) * (2 * N + 4)) := by
  rw [screenUniv]
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_powerset]
  have htgt := tgtUniv_card_le N
  have hnorm : (insert none ((tgtUniv N).image some)).card ≤ 2 * N + 4 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have := Finset.card_image_le (s := tgtUniv N) (f := some)
    omega
  have hpow : 2 ^ (tgtUniv N).card ≤ 2 ^ (2 * N + 3) :=
    Nat.pow_le_pow_right (by norm_num) htgt
  exact Nat.mul_le_mul htgt (Nat.mul_le_mul hpow hnorm)

/-- The accessible index is inside the bounded screen family. -/
lemma scrIndex_card_le (N : ℕ) (S : Finset ℕ) :
    (scrIndex N S).card ≤ (screenUniv N).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- **The one-law matching theorem at the constants of the paper**
(`thm:main-matching`, `eq:card-constants`, `eq:K-eps`): the numeric closure at
`c_N = (2N+3)·2^{2N+3}·(2N+4)` and `n_A = 2N+3`, with the threshold in the form
`η ≤ ε_ν`: the `1/3` barrier holds, giving `eq:main-bound`, and the mismatch at
every height is at most `K_ν · η`, uniformly in the height. -/
theorem main_matching_failure_le (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (heta : etaG (5 / 2) Rv μ
      ≤ (genSmallC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card
          (2 * N + 3) T)⁻¹) :
    genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
        * etaG (5 / 2) Rv μ ≤ 3⁻¹
      ∧ ∀ h, (∑' x, Tlaw μ ν v0 h x
          * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x)
        ≤ genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
            * etaG (5 / 2) Rv μ := by
  have hsmall : genSmallC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card
      (2 * N + 3) T * etaG (5 / 2) Rv μ ≤ 1 :=
    le_trans (mul_le_mul_right heta _) (ENNReal.mul_inv_le_one _)
  have hcN : (scrIndex N S).card ≤ (2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4) :=
    le_trans (le_trans (scrIndex_card_le N S) (screenUniv_card_le N))
      (le_of_eq (mul_assoc _ _ _).symm)
  exact ⟨genKcC_le_third _ S.card (2 * N + 3) T _ hsmall,
    varying_failure_le Rv μ v0 ν N S hrefl hsymm hhalf hN hS hSne hSsupp T hT
      _ _ hcN (tgtUniv_card_le N) hsmall⟩

/-- **The one-law matching theorem at the constants of the paper, on the constructed
trajectory space** (`thm:main-matching`, `eq:main-bound-infinite` at
`eq:card-constants` and `eq:K-eps`). -/
theorem main_matching_le_traj
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (heta : etaG (5 / 2) Rv μ
      ≤ (genSmallC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card
          (2 * N + 3) T)⁻¹) :
    1 - genKcC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card T
        * etaG (5 / 2) Rv μ
      ≤ TlawPair μ ν v0 {ω | InfMatch (labRel Rv)
          (fun n => consLab n ω.1) (fun n => consLab n ω.2)} := by
  have hsmall : genSmallC ((2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4)) S.card
      (2 * N + 3) T * etaG (5 / 2) Rv μ ≤ 1 :=
    le_trans (mul_le_mul_right heta _) (ENNReal.mul_inv_le_one _)
  have hcN : (scrIndex N S).card ≤ (2 * N + 3) * 2 ^ (2 * N + 3) * (2 * N + 4) :=
    le_trans (le_trans (scrIndex_card_le N S) (screenUniv_card_le N))
      (le_of_eq (mul_assoc _ _ _).symm)
  exact varying_matching_le_traj Rv μ v0 ν N S hrefl hsymm hhalf hN hS hSne hSsupp
    T hT _ _ hcN (tgtUniv_card_le N) hsmall

/-! ### The pure ternary law as an instance -/

/-- `ν = δ₃` re-derived as an instance of the general numeric closure
(`rem:delta3`)
at `N = 3`, `S = {3}`, `T = 1`, `cN = 46080`, `nA = 9` (the constants
are far larger than in the separate pipeline `delta3_failure_le`; the
point is the instantiation). -/
theorem delta3_failure_le_of_general (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0)
    (hsmall : genSmallC 46080 1 9 1 * etaG (5 / 2) Rv μ ≤ 1) :
    ∀ h, (∑' x, Tlaw μ (PMF.pure 3) v0 h x
        * qE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) x)
      ≤ genKcC 46080 1 1 * etaG (5 / 2) Rv μ := by
  have hcard : ({3} : Finset ℕ).card = 1 := Finset.card_singleton 3
  have hSsupp : ∀ i : ℕ, ((PMF.pure 3 : PMF ℕ) i : ℝ≥0∞) ≠ 0
      ↔ i ∈ ({3} : Finset ℕ) := by
    intro i
    by_cases hi : i = 3
    · subst hi
      simp [PMF.pure_apply]
    · simp [PMF.pure_apply, hi]
  have hT : (∑' i, if ((PMF.pure 3 : PMF ℕ) i : ℝ≥0∞) = 0 then 0
      else ((PMF.pure 3 : PMF ℕ) i : ℝ≥0∞) ^ (-(5 / 2 : ℝ)))
      ≤ (1 : ℝ≥0∞) := by
    have hpt : ∀ i : ℕ, (if ((PMF.pure 3 : PMF ℕ) i : ℝ≥0∞) = 0 then 0
        else ((PMF.pure 3 : PMF ℕ) i : ℝ≥0∞) ^ (-(5 / 2 : ℝ)))
        = if i = 3 then 1 else 0 := by
      intro i
      by_cases hi : i = 3
      · subst hi
        rw [if_pos rfl]
        rw [if_neg (by simp [PMF.pure_apply])]
        simp [PMF.pure_apply, ENNReal.one_rpow]
      · rw [if_neg hi, if_pos (by simp [PMF.pure_apply, hi])]
    rw [tsum_congr hpt]
    rw [tsum_ite_eq]
  have hcN : (scrIndex 3 ({3} : Finset ℕ)).card ≤ 46080 := by
    refine le_trans (scrIndex_card_le 3 {3}) ?_
    refine le_trans (screenUniv_card_le 3) ?_
    norm_num
  have hnA : (tgtUniv 3).card ≤ 9 := le_trans (tgtUniv_card_le 3) (by norm_num)
  have h := varying_failure_le Rv μ v0 (PMF.pure 3) 3 {3}
    hrefl hsymm hhalf (by norm_num)
    (fun k hk => by rw [Finset.mem_singleton] at hk; omega)
    ⟨3, Finset.mem_singleton_self 3⟩ hSsupp 1 hT 46080 9 hcN hnA
    (by rw [hcard] at *; exact hsmall)
  rw [hcard] at h
  exact h

end GraphMarkovMatching
