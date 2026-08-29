/-
The numeric closure of the composite two-law programme at `α = 5/2`
(`arbitrary_offspring_matching.tex`, `thm:composite-matching` with the
explicit constants `eq:composite-cardinals`, `eq:composite-tilt`, and
`eq:composite-K-eps`).

Every scalar witness fed to `composite_failure_le_final` /
`composite_matching_le_final` is replaced by a μ-free quantity built
from the instance data `(exc1, exc2, ν1, ν2, K1, K2, N)` alone, using
only the root-mass floor `2⁻¹ ≤ μ v0`:

* `compTiltBound`: the explicit finite tilt sum dominating the
  composite charged tilt sum `cTiltSum`, with summands `(ν k)^{-5/2}`
  for common counters and `(2⁻¹ (ν p₁ ν p₂))^{-5/2}` for declared
  exceptional counters (from `compFloor ≥ ν p₁ · (2⁻¹ · ν p₂)`);
* `compT`, `compEM`: the two-sided tilt and exceptional-mass budgets;
  the root-tilt budget is the certified constant `RT = 8`
  (`rootTilt_le`);
* `compC`, `compCu`, `compX`: the common row weight
  `16·cMx + 128·cMx²·T` (the nilpotent block carries the uniform
  tilt-renewal weight at `RT = 8`, as the one-law row constant
  `C_W = 32T + 4` does; `thm:geom`), the screen-closure weight
  `16 T + 3`, and the geometric debt multiplier `cX` at these values;
* `compKcFinal`: the μ-free ordinary barrier, an upper bound for the
  running `cKc` obtained from `cRootA ≤ 3` and
  `(1 - cLamS)⁻¹ ≤ 6` at the certified calculus pack
  `δ = 1/8`, `L = 1/4`, `K = 4/27` (`quarter_L_bound`,
  `fourTwentySeventh_K_bound`, `cLamS = 5/6 < 1`);
* `compEtaStar`: the μ-free threshold, the minimum of a lower bound
  for the absorption threshold `cEtaStar`, the screen-closure
  threshold `compHuCOf⁻¹`, and the half-barrier entry
  `(2 · compKcFinal)⁻¹`;
* `compChi`: the priced entrance weight
  `(2 · (2 · compC)^(cRank N))⁻¹`, the reciprocal of the smallness
  denominator, so `cSmallness` holds outright and the affordability
  budget becomes exactly the domination hypothesis `hdom`, the composite
  form of the entrance-price smallness:

      cMpBudget · (2 · (2 · compC)^(cRank N)) ≤ compC.

The headline theorems `composite_failure_bound` and
`composite_matching_bound` instantiate the conditional theorems of
`Step` at these witnesses: their hypotheses are the structural
instance pack, `hdom`, and the threshold `heta`; all constants in the
conclusions are μ-free and existence-level.

Non-vacuity: since the rare budget is proportional to the exceptional
mass (`cMpBudget = compEM · compC` at the instance data), `hdom` holds
whenever `compEM` is at most the strictly positive threshold
`compDomThreshold` (`hdom_of_compEM_le`, `compDomThreshold_pos`); the
no-exception instance (`composite_failure_bound_no_exceptions`)
discharges the whole structural pack and `hdom` for the empty
exceptional charts, so the hypothesis pack of the headline theorems is
satisfiable.
-/
import GraphMarkovMatching.Composite.Step
import GraphMarkovMatching.Closure.Numeric

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### ENNReal helpers -/

private lemma mul_le_one_of_le_inv {c η : ℝ≥0∞} (h : η ≤ c⁻¹) :
    c * η ≤ 1 :=
  le_trans (mul_le_mul_right h c) (ENNReal.mul_inv_le_one c)

private lemma ofReal_five_half_le_three :
    ENNReal.ofReal ((5 : ℝ) / 2) ≤ 3 := by
  rw [show ((3 : ℝ≥0∞)) = ENNReal.ofReal (3 : ℝ) from by simp]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

private lemma ofReal_two_mul_five_half_le_five :
    ENNReal.ofReal (2 * ((5 : ℝ) / 2)) ≤ 5 := by
  rw [show ((5 : ℝ≥0∞)) = ENNReal.ofReal (5 : ℝ) from by simp]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-! ### The μ-free tilt bound of one side -/

section TiltBound

variable (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)

/-- The μ-free floor of an arity: its own weight for a common arity,
the half-weighted product `2⁻¹ (ν p₁ ν p₂)` for a declared exceptional
arity.  Under `2⁻¹ ≤ μ v0` it minorizes the composite floor. -/
noncomputable def compTiltFloor (k : ℕ) : ℝ≥0∞ :=
  match exc k with
  | none => ν k
  | some p => 2⁻¹ * (ν p.1 * ν p.2)

lemma compTiltFloor_none {k : ℕ} (hk : exc k = none) :
    compTiltFloor exc ν k = ν k := by
  simp [compTiltFloor, hk]

lemma compTiltFloor_some {k : ℕ} {p : ℕ × ℕ} (hk : exc k = some p) :
    compTiltFloor exc ν k = 2⁻¹ * (ν p.1 * ν p.2) := by
  simp [compTiltFloor, hk]

lemma compTiltFloor_le_one (k : ℕ) : compTiltFloor exc ν k ≤ 1 := by
  rcases hexc : exc k with _ | p
  · rw [compTiltFloor_none exc ν hexc]
    exact pmf_apply_le_one ν k
  · rw [compTiltFloor_some exc ν hexc]
    exact mul_le_one' (by norm_num)
      (mul_le_one' (pmf_apply_le_one ν _) (pmf_apply_le_one ν _))

lemma compTiltFloor_ne_zero
    (hdecl : ∀ k p, exc k = some p → ν p.1 ≠ 0 ∧ ν p.2 ≠ 0)
    {k : ℕ} (hν : ν k ≠ 0) : compTiltFloor exc ν k ≠ 0 := by
  rcases hexc : exc k with _ | p
  · rw [compTiltFloor_none exc ν hexc]
    exact hν
  · rw [compTiltFloor_some exc ν hexc]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero (hdecl k p hexc).1 (hdecl k p hexc).2)

/-- The μ-free floor minorizes the composite floor under the root-mass
floor `2⁻¹ ≤ μ v0`. -/
lemma compTiltFloor_le_compFloor (μ : PMF V) (v0 : V)
    (hhalf : 2⁻¹ ≤ μ v0) (k : ℕ) :
    compTiltFloor exc ν k ≤ compFloor exc μ ν v0 k := by
  rcases hexc : exc k with _ | p
  · rw [compTiltFloor_none exc ν hexc, compFloor_none exc μ ν v0 hexc]
  · rw [compTiltFloor_some exc ν hexc, compFloor_some exc μ ν v0 hexc]
    calc 2⁻¹ * (ν p.1 * ν p.2) = ν p.1 * (2⁻¹ * ν p.2) := by ring
      _ ≤ ν p.1 * (μ v0 * ν p.2) :=
          mul_le_mul_right (mul_le_mul_left hhalf _) _

/-- **The μ-free tilt bound of one side**: the explicit finite sum of
inverse `5/2`-powers of the μ-free floors over the support. -/
noncomputable def compTiltBound (Kf : Finset ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Kf, compTiltFloor exc ν k ^ (-(5 / 2 : ℝ))

/-- The composite charged tilt sum is dominated by the μ-free tilt
bound whenever the root label carries at least half the mass. -/
lemma cTiltSum_le_compTiltBound (μ : PMF V) (v0 : V) {Kf : Finset ℕ}
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ Kf) (hhalf : 2⁻¹ ≤ μ v0) :
    cTiltSum (5 / 2) exc μ ν v0 ≤ compTiltBound exc ν Kf := by
  rw [cTiltSum_eq_sum (5 / 2) exc μ ν v0 (fun k hk => (hsup k).mp hk),
    compTiltBound]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hν : ν k = 0
  · rw [if_pos hν]
    exact zero_le
  · rw [if_neg hν]
    exact rpow_neg_antitone (by norm_num)
      (compTiltFloor_le_compFloor exc ν μ v0 hhalf k)

/-- The μ-free tilt bound is finite under chargedness of the declared
pairs. -/
lemma compTiltBound_ne_top {Kf : Finset ℕ}
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ Kf)
    (hdecl : ∀ k p, exc k = some p → ν p.1 ≠ 0 ∧ ν p.2 ≠ 0) :
    compTiltBound exc ν Kf ≠ ⊤ := by
  rw [compTiltBound]
  refine ENNReal.sum_ne_top.mpr fun k hk => ?_
  have hfl0 : compTiltFloor exc ν k ≠ 0 :=
    compTiltFloor_ne_zero exc ν hdecl ((hsup k).mpr hk)
  have hflt : compTiltFloor exc ν k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (compTiltFloor_le_one exc ν k)
  rw [ENNReal.rpow_neg, Ne, ENNReal.inv_eq_top, ENNReal.rpow_eq_zero_iff]
  rintro (⟨h0, _⟩ | ⟨ht, _⟩)
  · exact hfl0 h0
  · exact hflt ht

/-- On a nonempty support the μ-free tilt bound is at least one. -/
lemma one_le_compTiltBound {Kf : Finset ℕ} (hne : Kf.Nonempty) :
    1 ≤ compTiltBound exc ν Kf := by
  obtain ⟨k, hk⟩ := hne
  rw [compTiltBound]
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => zero_le) hk)
  calc (1 : ℝ≥0∞) = 1 ^ (-(5 / 2 : ℝ)) := (ENNReal.one_rpow _).symm
    _ ≤ compTiltFloor exc ν k ^ (-(5 / 2 : ℝ)) :=
        rpow_neg_antitone (by norm_num) (compTiltFloor_le_one exc ν k)

end TiltBound

/-! ### The scalar comparison layer at `δ = 1/8`, `L = 1/4`,
`K = 4/27` -/

/-- The linear four-law constant at the certified pack is `5/6`,
strictly below one. -/
lemma compLamS_lt_one : cLamS (1 / 8) (1 / 4) (4 / 27) < 1 := by
  rw [cLamS]
  exact delta3_A_lt_one

lemma compLamS_le_one : cLamS (1 / 8) (1 / 4) (4 / 27) ≤ 1 :=
  le_of_lt compLamS_lt_one

/-- The root multiplier is at most `3` under the root-mass floor. -/
lemma cRootA_le_three (μ : PMF V) (v0 : V) (hhalf : 2⁻¹ ≤ μ v0) :
    cRootA μ v0 ≤ 3 := by
  rw [cRootA]
  have hinv : (μ v0)⁻¹ ≤ 2 := by
    have h := ENNReal.inv_le_inv' hhalf
    rwa [inv_inv] at h
  calc 1 + (μ v0)⁻¹ ≤ 1 + 2 := add_le_add le_rfl hinv
    _ = 3 := by norm_num

/-- The subcriticality denominator is at most `6` at the certified
pack: `(1 - 5/6)⁻¹ = 6`. -/
lemma invLamS_le_six : (1 - cLamS (1 / 8) (1 / 4) (4 / 27))⁻¹ ≤ 6 := by
  have hLam : cLamS (1 / 8) (1 / 4) (4 / 27)
      = ENNReal.ofReal (5 / 6) := by
    rw [cLamS, delta3_A_le]
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (5 / 6)
      = ENNReal.ofReal (1 / 6) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    norm_num
  have h16 : ENNReal.ofReal (1 / 6 : ℝ) = (6 : ℝ≥0∞)⁻¹ := by
    rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [hLam, hsub, h16, inv_inv]

/-- The μ-free ordinary barrier at budgets `(T, κ, X)`:
`(3 + B₁ + 1) · 6`, the barrier `cKc` with the root multiplier and the
subcriticality denominator replaced by their μ-free bounds. -/
noncomputable def compKcOf (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  (3 + cLinB (1 / 8) T κ X + 1) * 6

/-- The running barrier is dominated by the μ-free barrier. -/
lemma cKc_le_compKcOf (μ : PMF V) (v0 : V) (hhalf : 2⁻¹ ≤ μ v0)
    (T κ X : ℝ≥0∞) :
    cKc (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X ≤ compKcOf T κ X := by
  rw [cKc, compKcOf]
  exact mul_le_mul'
    (add_le_add (add_le_add (cRootA_le_three μ v0 hhalf) le_rfl) le_rfl)
    invLamS_le_six

lemma compKcOf_ne_top {T κ X : ℝ≥0∞} (hT : T ≠ ⊤) (hκ : κ ≠ ⊤)
    (hX : X ≠ ⊤) : compKcOf T κ X ≠ ⊤ := by
  rw [compKcOf]
  exact ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofNat_ne_top, cLinB_ne_top (1 / 8) hT hκ hX⟩,
        ENNReal.one_ne_top⟩)
    ENNReal.ofNat_ne_top

/-- The μ-free quadratic coefficient: `cB2` with `cQuadC ≤ 160`,
`4 · ofReal (5/2) ≤ 12`, and the barrier replaced by `compKcOf`. -/
noncomputable def compB2Of (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  160 * (compKcOf T κ X * compKcOf T κ X)
    + 12 * X * compKcOf T κ X * (1 + T * κ)
    + 4 * T * κ * (X * X)

lemma cB2_le_compB2Of (μ : PMF V) (v0 : V) (hhalf : 2⁻¹ ≤ μ v0)
    (T κ X : ℝ≥0∞) :
    cB2 (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X
      ≤ compB2Of T κ X := by
  have hKc := cKc_le_compKcOf μ v0 hhalf T κ X
  rw [cB2, compB2Of]
  refine add_le_add (add_le_add ?_ ?_) le_rfl
  · refine mul_le_mul' ?_ (mul_le_mul' hKc hKc)
    rw [cQuadC, show ((160 : ℝ≥0∞)) = ENNReal.ofReal (160 : ℝ) from by
      simp]
    exact ENNReal.ofReal_le_ofReal (by linarith [chordConst_five_half_le])
  · refine mul_le_mul_left (mul_le_mul' ?_ hKc) _
    refine mul_le_mul_left ?_ X
    calc (4 : ℝ≥0∞) * ENNReal.ofReal ((5 : ℝ) / 2) ≤ 4 * 3 :=
          mul_le_mul_right ofReal_five_half_le_three 4
      _ = 12 := by norm_num

lemma compB2Of_ne_top {T κ X : ℝ≥0∞} (hT : T ≠ ⊤) (hκ : κ ≠ ⊤)
    (hX : X ≠ ⊤) : compB2Of T κ X ≠ ⊤ := by
  have hKc := compKcOf_ne_top hT hκ hX
  rw [compB2Of]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.mul_ne_top hKc hKc)
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hX) hKc)
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hT hκ⟩)
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT) hκ)
      (ENNReal.mul_ne_top hX hX)

/-- The μ-free first absorbed coefficient. -/
noncomputable def compC2Of (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  compB2Of T κ X + 15 * (compKcOf T κ X + cLinB (1 / 8) T κ X)

lemma cC2_le_compC2Of (μ : PMF V) (v0 : V) (hhalf : 2⁻¹ ≤ μ v0)
    (T κ X : ℝ≥0∞) :
    cC2 (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X
      ≤ compC2Of T κ X := by
  have hKc := cKc_le_compKcOf μ v0 hhalf T κ X
  rw [cC2, compC2Of]
  refine add_le_add (cB2_le_compB2Of μ v0 hhalf T κ X) ?_
  calc ENNReal.ofReal (2 * ((5 : ℝ) / 2)) * cRootA μ v0
        * (cLamS (1 / 8) (1 / 4) (4 / 27)
            * cKc (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X
          + cLinB (1 / 8) T κ X)
      ≤ (5 * 3) * (1 * compKcOf T κ X + cLinB (1 / 8) T κ X) :=
        mul_le_mul'
          (mul_le_mul' ofReal_two_mul_five_half_le_five
            (cRootA_le_three μ v0 hhalf))
          (add_le_add (mul_le_mul' compLamS_le_one hKc) le_rfl)
    _ = 15 * (compKcOf T κ X + cLinB (1 / 8) T κ X) := by
        rw [one_mul]
        norm_num

lemma compC2Of_ne_top {T κ X : ℝ≥0∞} (hT : T ≠ ⊤) (hκ : κ ≠ ⊤)
    (hX : X ≠ ⊤) : compC2Of T κ X ≠ ⊤ := by
  rw [compC2Of]
  exact ENNReal.add_ne_top.mpr
    ⟨compB2Of_ne_top hT hκ hX,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.add_ne_top.mpr
          ⟨compKcOf_ne_top hT hκ hX, cLinB_ne_top (1 / 8) hT hκ hX⟩)⟩

/-- The μ-free second absorbed coefficient. -/
noncomputable def compC3Of (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  15 * compB2Of T κ X

lemma cC3_le_compC3Of (μ : PMF V) (v0 : V) (hhalf : 2⁻¹ ≤ μ v0)
    (T κ X : ℝ≥0∞) :
    cC3 (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X
      ≤ compC3Of T κ X := by
  rw [cC3, compC3Of]
  calc ENNReal.ofReal (2 * ((5 : ℝ) / 2)) * cRootA μ v0
        * cB2 (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X
      ≤ (5 * 3) * compB2Of T κ X :=
        mul_le_mul'
          (mul_le_mul' ofReal_two_mul_five_half_le_five
            (cRootA_le_three μ v0 hhalf))
          (cB2_le_compB2Of μ v0 hhalf T κ X)
    _ = 15 * compB2Of T κ X := by norm_num

lemma compC3Of_ne_top {T κ X : ℝ≥0∞} (hT : T ≠ ⊤) (hκ : κ ≠ ⊤)
    (hX : X ≠ ⊤) : compC3Of T κ X ≠ ⊤ := by
  rw [compC3Of]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (compB2Of_ne_top hT hκ hX)

/-- The μ-free absorption entry of the threshold dominates the running
threshold `cEtaStar` from below. -/
lemma compEtaOf_le_cEtaStar (μ : PMF V) (v0 : V) (hhalf : 2⁻¹ ≤ μ v0)
    (T κ X : ℝ≥0∞) :
    (compC2Of T κ X + compC3Of T κ X + 1)⁻¹
      ≤ cEtaStar (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X := by
  rw [cEtaStar]
  exact ENNReal.inv_le_inv'
    (add_le_add
      (add_le_add (cC2_le_compC2Of μ v0 hhalf T κ X)
        (cC3_le_compC3Of μ v0 hhalf T κ X))
      le_rfl)

/-! ### The screen-closure constant and the `hu` discharge -/

/-- The μ-free screen-closure constant at budgets `(T, κ, X)` and
singleton-length budget `Lz`: `3 Kc' + (1 + 8T)(24 Kc' X + 4 (Lz X)²)`;
once `compHuCOf · η ≤ 1`, the inhomogeneity `cG` closes at the weight
`16 T + 3`. -/
noncomputable def compHuCOf (T κ X : ℝ≥0∞) (Lz : ℕ) : ℝ≥0∞ :=
  3 * compKcOf T κ X
    + (1 + 8 * T) * (24 * (compKcOf T κ X * X)
        + 4 * (((Lz : ℝ≥0∞) * X) * ((Lz : ℝ≥0∞) * X)))

lemma compHuCOf_ne_top {T κ X : ℝ≥0∞} (hT : T ≠ ⊤) (hκ : κ ≠ ⊤)
    (hX : X ≠ ⊤) (Lz : ℕ) : compHuCOf T κ X Lz ≠ ⊤ := by
  have hKc := compKcOf_ne_top hT hκ hX
  rw [compHuCOf]
  refine ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hKc, ?_⟩
  refine ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT⟩)
    (ENNReal.add_ne_top.mpr ⟨?_, ?_⟩)
  · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.mul_ne_top hKc hX)
  · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hX)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hX))

/-- **The screen-closure discharge**: at root-tilt budget `RT = 8` and
below the screen-closure threshold, the inhomogeneity `cG` at the
invariant box is at most `(16 T + 3) · η`. -/
lemma cG_le_of_compHuCOf (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (hhalf : 2⁻¹ ≤ μ v0) (T κ X : ℝ≥0∞) (Lz : ℕ)
    (hsmall : compHuCOf T κ X Lz * etaG (5 / 2) Rv μ ≤ 1) :
    cG (5 / 2) Rv μ T 8 Lz
        (cKc (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X * etaG (5 / 2) Rv μ)
        (X * etaG (5 / 2) Rv μ)
      ≤ (16 * T + 3) * etaG (5 / 2) Rv μ := by
  set η := etaG (5 / 2) Rv μ with hη
  set KF := compKcOf T κ X with hKF
  set Kc := cKc (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X with hKc'
  have hKc : Kc ≤ KF := cKc_le_compKcOf μ v0 hhalf T κ X
  have h3KF : 3 * KF * η ≤ 1 := by
    refine le_trans (mul_le_mul_left ?_ η) hsmall
    rw [compHuCOf, ← hKF]
    exact le_self_add
  have hαa : ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η) ≤ 1 := by
    calc ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η)
        ≤ 3 * (KF * η) :=
          mul_le_mul' ofReal_five_half_le_three (mul_le_mul_left hKc η)
      _ = 3 * KF * η := by ring
      _ ≤ 1 := h3KF
  have hone2 : 1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η) ≤ 2 := by
    calc 1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η) ≤ 1 + 1 :=
        add_le_add le_rfl hαa
      _ = 2 := one_add_one_eq_two
  have hsq8 : 2 * ((1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η))
      * (1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η))) ≤ 8 := by
    calc 2 * ((1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η))
          * (1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η)))
        ≤ 2 * (2 * 2) := mul_le_mul_right (mul_le_mul' hone2 hone2) 2
      _ = 8 := by norm_num
  rw [cG]
  have hfirst : 2 * η
      * (1 + T * (2 * ((1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η))
          * (1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η)))))
      ≤ 2 * η + 16 * T * η := by
    calc 2 * η
        * (1 + T * (2 * ((1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η))
            * (1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η)))))
        ≤ 2 * η * (1 + T * 8) :=
          mul_le_mul_right
            (add_le_add le_rfl (mul_le_mul_right hsq8 T)) _
      _ = 2 * η + 16 * T * η := by ring
  have hsecond : (1 + 8 * T)
      * (8 * (ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η) * (X * η))
        + 4 * (((Lz : ℝ≥0∞) * (X * η)) * ((Lz : ℝ≥0∞) * (X * η))))
      ≤ η := by
    calc (1 + 8 * T)
        * (8 * (ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η) * (X * η))
          + 4 * (((Lz : ℝ≥0∞) * (X * η)) * ((Lz : ℝ≥0∞) * (X * η))))
        ≤ (1 + 8 * T) * (8 * (3 * (KF * η) * (X * η))
          + 4 * (((Lz : ℝ≥0∞) * (X * η)) * ((Lz : ℝ≥0∞) * (X * η)))) :=
          mul_le_mul_right
            (add_le_add
              (mul_le_mul_right
                (mul_le_mul_left
                  (mul_le_mul' ofReal_five_half_le_three
                    (mul_le_mul_left hKc η)) (X * η)) 8)
              le_rfl) _
      _ = ((1 + 8 * T) * (24 * (KF * X)
            + 4 * (((Lz : ℝ≥0∞) * X) * ((Lz : ℝ≥0∞) * X)))) * (η * η) := by
          ring
      _ ≤ compHuCOf T κ X Lz * (η * η) := by
          refine mul_le_mul_left ?_ (η * η)
          rw [compHuCOf, ← hKF]
          exact le_add_self
      _ = (compHuCOf T κ X Lz * η) * η := by ring
      _ ≤ 1 * η := mul_le_mul_left hsmall η
      _ = η := one_mul η
  calc 2 * η
      * (1 + T * (2 * ((1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η))
          * (1 + ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η)))))
      + (1 + 8 * T)
        * (8 * (ENNReal.ofReal ((5 : ℝ) / 2) * (Kc * η) * (X * η))
          + 4 * (((Lz : ℝ≥0∞) * (X * η)) * ((Lz : ℝ≥0∞) * (X * η))))
      ≤ (2 * η + 16 * T * η) + η := add_le_add hfirst hsecond
    _ = (16 * T + 3) * η := by ring

/-! ### The μ-free instance constants -/

/-- The two-sided μ-free tilt budget `T`. -/
noncomputable def compT (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) : ℝ≥0∞ :=
  max (compTiltBound exc1 ν1 K1) (compTiltBound exc2 ν2 K2)

/-- The two-sided exceptional-mass budget `eM`. -/
noncomputable def compEM (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) : ℝ≥0∞ :=
  max (cExcMass exc1 ν1) (cExcMass exc2 ν2)

/-- The common row weight `C = 16·cMx + 128·cMx²·T`: the common row
budget `cNcBudget` at the root-tilt budget `RT = 8`, carrying the
tilt-renewal weight inside the nilpotent block as the one-law row
constant `C_W = 32T + 4` does. -/
noncomputable def compC (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) : ℝ≥0∞ :=
  cNcBudget (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)

/-- The screen-closure weight `cu = 16 T + 3`. -/
noncomputable def compCu (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) : ℝ≥0∞ :=
  16 * compT exc1 exc2 ν1 ν2 K1 K2 + 3

/-- The μ-free Green debt multiplier `X = cX C (cRank N) cu`. -/
noncomputable def compX (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  cX (compC exc1 exc2 ν1 ν2 K1 K2) (cRank N)
    (compCu exc1 exc2 ν1 ν2 K1 K2)

/-- **The μ-free ordinary barrier of the composite theorem**:
`compKcOf` at the instance budgets; the failure constant of
`composite_failure_bound`. -/
noncomputable def compKcFinal (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  compKcOf (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
    (compX exc1 exc2 ν1 ν2 K1 K2 N)

/-- **The μ-free threshold of the composite theorem**: the minimum of
the absorption entry, the screen-closure entry, and the half-barrier
entry. -/
noncomputable def compEtaStar (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  min ((compC2Of (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
        (compX exc1 exc2 ν1 ν2 K1 K2 N)
      + compC3Of (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
          (compX exc1 exc2 ν1 ν2 K1 K2 N) + 1)⁻¹)
    (min ((compHuCOf (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
          (compX exc1 exc2 ν1 ν2 K1 K2 N) (cLz N K1 K2))⁻¹)
      ((2 * compKcFinal exc1 exc2 ν1 ν2 K1 K2 N)⁻¹))

/-- The priced entrance weight `χ0 = (2·(2·C)^(cRank N))⁻¹`: the
reciprocal of the smallness denominator, making `cSmallness` automatic
and turning the affordability budget into the single domination
hypothesis `hdom`. -/
noncomputable def compChi (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)⁻¹

/-- **The domination threshold**: the domination hypothesis `hdom`
holds whenever the two-sided exceptional mass is at most this bound
(`hdom_of_compEM_le`); it coincides with the priced entrance weight
`compChi`. -/
noncomputable def compDomThreshold (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  compChi exc1 exc2 ν1 ν2 K1 K2 N

/-! ### Finiteness and positivity of the instance constants -/

section Instance

variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

lemma compT_ne_top
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compT exc1 exc2 ν1 ν2 K1 K2 ≠ ⊤ := by
  rw [compT]
  exact (max_lt_iff.mpr
    ⟨lt_top_iff_ne_top.mpr (compTiltBound_ne_top exc1 ν1 hsup1 hdecl1),
      lt_top_iff_ne_top.mpr
        (compTiltBound_ne_top exc2 ν2 hsup2 hdecl2)⟩).ne

lemma one_le_compT (hne : K1.Nonempty) :
    1 ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
  rw [compT]
  exact le_trans (one_le_compTiltBound exc1 ν1 hne) (le_max_left _ _)

lemma compEM_le_one : compEM exc1 exc2 ν1 ν2 ≤ 1 := by
  rw [compEM]
  exact max_le (cExcMass_le_one exc1 ν1) (cExcMass_le_one exc2 ν2)

lemma one_le_compC : 1 ≤ compC exc1 exc2 ν1 ν2 K1 K2 := by
  have hmx1 : (1 : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) := by
    exact_mod_cast one_le_cMx K1 K2
  rw [compC, cNcBudget]
  refine le_trans ?_ le_self_add
  calc (1 : ℝ≥0∞) ≤ 16 := by norm_num
    _ = 16 * 1 := (mul_one _).symm
    _ ≤ 16 * (cMx K1 K2 : ℝ≥0∞) := mul_le_mul_right hmx1 16

lemma compC_ne_zero : compC exc1 exc2 ν1 ν2 K1 K2 ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one
    (one_le_compC exc1 exc2 ν1 ν2 K1 K2)).ne'

lemma compC_ne_top
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compC exc1 exc2 ν1 ν2 K1 K2 ≠ ⊤ := by
  have hT := compT_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2
    hdecl2
  rw [compC, cNcBudget]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top _)
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.natCast_ne_top _)))
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT)

lemma compCu_ne_top
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compCu exc1 exc2 ν1 ν2 K1 K2 ≠ ⊤ := by
  rw [compCu]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (compT_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2),
      ENNReal.ofNat_ne_top⟩

lemma compX_ne_top
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compX exc1 exc2 ν1 ν2 K1 K2 N ≠ ⊤ := by
  rw [compX, cX, graftGreenMultiplier, graftGreenRemainder]
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ?_)
    (compCu_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2)
  refine ENNReal.sum_ne_top.mpr fun j _ => ENNReal.pow_ne_top ?_
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (compC_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2)

/-- **Finiteness of the failure constant.** -/
theorem compKcFinal_ne_top
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compKcFinal exc1 exc2 ν1 ν2 K1 K2 N ≠ ⊤ := by
  rw [compKcFinal]
  exact compKcOf_ne_top
    (compT_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2)
    (ENNReal.natCast_ne_top _)
    (compX_ne_top exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1 hsup2 hdecl2)

/-- **Positivity of the threshold**: under chargedness of the declared
pairs all three entries of the minimum are positive. -/
theorem compEtaStar_pos
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    0 < compEtaStar exc1 exc2 ν1 ν2 K1 K2 N := by
  have hT := compT_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2
  have hκ : (cMx K1 K2 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hX := compX_ne_top exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1 hsup2
    hdecl2
  rw [compEtaStar]
  refine lt_min_iff.mpr ⟨?_, lt_min_iff.mpr ⟨?_, ?_⟩⟩
  · rw [ENNReal.inv_pos]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨compC2Of_ne_top hT hκ hX, compC3Of_ne_top hT hκ hX⟩,
        ENNReal.one_ne_top⟩
  · rw [ENNReal.inv_pos]
    exact compHuCOf_ne_top hT hκ hX _
  · rw [ENNReal.inv_pos]
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top ?_
    exact compKcFinal_ne_top exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1
      hsup2 hdecl2

/-- The threshold is nonzero (the form used by the headline
hypotheses). -/
theorem compEtaStar_ne_zero
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compEtaStar exc1 exc2 ν1 ν2 K1 K2 N ≠ 0 :=
  (compEtaStar_pos exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1 hsup2
    hdecl2).ne'

/-- The threshold is finite: the absorption entry is at most one. -/
theorem compEtaStar_ne_top :
    compEtaStar exc1 exc2 ν1 ν2 K1 K2 N ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [compEtaStar]
  exact le_trans (min_le_left _ _) (ENNReal.inv_le_one.mpr le_add_self)

end Instance

/-! ### The priced entrance weight and the domination hypothesis -/

section Chi

variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

lemma compChi_ne_zero
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compChi exc1 exc2 ν1 ν2 K1 K2 N ≠ 0 := by
  rw [compChi, Ne, ENNReal.inv_eq_zero]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (compC_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2)))

/-- **Positivity of the domination threshold** under chargedness of
the declared pairs: the domination hypothesis of the headline theorems
is satisfiable throughout a strictly positive range of exceptional
masses. -/
theorem compDomThreshold_pos
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    0 < compDomThreshold exc1 exc2 ν1 ν2 K1 K2 N :=
  pos_iff_ne_zero.mpr
    (compChi_ne_zero exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1 hsup2 hdecl2)

lemma compChi_le_one : compChi exc1 exc2 ν1 ν2 K1 K2 N ≤ 1 := by
  rw [compChi]
  refine ENNReal.inv_le_one.mpr ?_
  calc (1 : ℝ≥0∞) ≤ 2 := one_le_two
    _ = 2 * 1 := (mul_one _).symm
    _ ≤ 2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N := by
        refine mul_le_mul_right ?_ 2
        calc (1 : ℝ≥0∞) = 1 ^ cRank N := (one_pow _).symm
          _ ≤ (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N := by
              refine pow_le_pow_left' ?_ _
              calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
                _ ≤ 2 * compC exc1 exc2 ν1 ν2 K1 K2 :=
                    mul_le_mul' one_le_two
                      (one_le_compC exc1 exc2 ν1 ν2 K1 K2)

/-- **The smallness discharge**: at the reciprocal entrance weight both
halves of `cSmallness` hold outright. -/
lemma compChi_smallness :
    cSmallness (compChi exc1 exc2 ν1 ν2 K1 K2 N)
      (compC exc1 exc2 ν1 ν2 K1 K2) (cRank N) := by
  refine ⟨compChi_le_one exc1 exc2 ν1 ν2 K1 K2 N, ?_⟩
  rw [compChi, ENNReal.mul_inv (Or.inl (by norm_num))
    (Or.inl ENNReal.ofNat_ne_top), mul_assoc]
  refine le_trans (mul_le_mul_right ?_ 2⁻¹) (le_of_eq (mul_one _))
  exact le_trans (le_of_eq (mul_comm _ _)) (ENNReal.mul_inv_le_one _)

/-- **The affordability discharge**: under the domination hypothesis
the raw priced budget is affordable at the entrance weight. -/
lemma compChi_afford
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hdom : cMpBudget (compEM exc1 exc2 ν1 ν2)
          (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
        * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
        ≤ compC exc1 exc2 ν1 ν2 K1 K2) :
    cMpBudget (compEM exc1 exc2 ν1 ν2)
        (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      ≤ compChi exc1 exc2 ν1 ν2 K1 K2 N
        * compC exc1 exc2 ν1 ν2 K1 K2 := by
  have hD0 : (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
      ≠ 0 := by
    refine mul_ne_zero (by norm_num) (pow_ne_zero _ ?_)
    exact mul_ne_zero (by norm_num)
      (compC_ne_zero exc1 exc2 ν1 ν2 K1 K2)
  have hDt : (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
      ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (compC_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2
          hdecl2)))
  calc cMpBudget (compEM exc1 exc2 ν1 ν2)
        (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      = cMpBudget (compEM exc1 exc2 ν1 ν2)
          (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
        * ((2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
          * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hD0 hDt, mul_one]
    _ = cMpBudget (compEM exc1 exc2 ν1 ν2)
          (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
        * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
        * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)⁻¹ :=
        (mul_assoc _ _ _).symm
    _ ≤ compC exc1 exc2 ν1 ν2 K1 K2
        * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)⁻¹ :=
        mul_le_mul_left hdom _
    _ = compChi exc1 exc2 ν1 ν2 K1 K2 N
        * compC exc1 exc2 ν1 ν2 K1 K2 := by
        rw [compChi, mul_comm]

/-- The raw priced budget at the instance data is exactly the
two-sided exceptional mass times the common row weight. -/
lemma compMpBudget_eq :
    cMpBudget (compEM exc1 exc2 ν1 ν2)
        (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      = compEM exc1 exc2 ν1 ν2 * compC exc1 exc2 ν1 ν2 K1 K2 := by
  rw [cMpBudget, compC, cNcBudget]
  ring

/-- **Non-vacuity of the domination hypothesis**: `hdom` holds
whenever the two-sided exceptional mass is at most the strictly
positive threshold `compDomThreshold`. -/
theorem hdom_of_compEM_le
    (hEM : compEM exc1 exc2 ν1 ν2
      ≤ compDomThreshold exc1 exc2 ν1 ν2 K1 K2 N) :
    cMpBudget (compEM exc1 exc2 ν1 ν2)
        (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
      ≤ compC exc1 exc2 ν1 ν2 K1 K2 := by
  rw [compDomThreshold, compChi] at hEM
  rw [compMpBudget_eq exc1 exc2 ν1 ν2 K1 K2]
  calc compEM exc1 exc2 ν1 ν2 * compC exc1 exc2 ν1 ν2 K1 K2
        * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
      ≤ (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)⁻¹
          * compC exc1 exc2 ν1 ν2 K1 K2
          * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N) :=
        mul_le_mul_left (mul_le_mul_left hEM _) _
    _ = compC exc1 exc2 ν1 ν2 K1 K2
        * ((2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
          * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)⁻¹) := by
        ring
    _ ≤ compC exc1 exc2 ν1 ν2 K1 K2 * 1 :=
        mul_le_mul_right (ENNReal.mul_inv_le_one _) _
    _ = compC exc1 exc2 ν1 ν2 K1 K2 := mul_one _

end Chi

/-! ### The headline theorems -/

section Headline

variable (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)

/-- **The composite two-law mismatch bound with μ-free constants**, an
intermediate form of `thm:composite-matching` still carrying a
domination hypothesis: under the structural instance pack, the root-mass
floor `2⁻¹ ≤ μ v0`, the domination hypothesis `hdom` (the entrance-price
smallness in composite form), and the graph potential below the μ-free
threshold `compEtaStar`, the mismatch at every height is at most
`compKcFinal · η`.  All constants are built from
`(exc1, exc2, ν1, ν2, K1, K2, N)` alone.  The mass-free form below,
which is what `thm:composite-matching` states, drops `hdom`. -/
theorem composite_failure_bound
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (hdom : cMpBudget (compEM exc1 exc2 ν1 ν2)
          (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
        * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
        ≤ compC exc1 exc2 ν1 ν2 K1 K2)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStar exc1 exc2 ν1 ν2 K1 K2 N) :
    ∀ h, failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
        (fullSim (cRel Rv) h)
      ≤ compKcFinal exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ := by
  have hT1 : cTiltSum (5 / 2) exc1 μ ν1 v0
      ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compT]
    exact le_trans (cTiltSum_le_compTiltBound exc1 ν1 μ v0 hsup1 hhalf)
      (le_max_left _ _)
  have hT2 : cTiltSum (5 / 2) exc2 μ ν2 v0
      ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compT]
    exact le_trans (cTiltSum_le_compTiltBound exc2 ν2 μ v0 hsup2 hhalf)
      (le_max_right _ _)
  have heM1 : cExcMass exc1 ν1 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_left _ _
  have heM2 : cExcMass exc2 ν2 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_right _ _
  have hκ1 : (K1.card : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) :=
    Nat.cast_le.mpr (le_trans (le_max_left _ _) (le_max_left _ _))
  have hκ2 : (K2.card : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) :=
    Nat.cast_le.mpr (le_trans (le_max_right _ _) (le_max_left _ _))
  have hchi0 := compChi_ne_zero exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1
    hsup2 hdecl2
  have hC : cNcBudget (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      ≤ compC exc1 exc2 ν1 ν2 K1 K2 := le_of_eq (by rw [compC])
  have hafford := compChi_afford exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1
    hsup2 hdecl2 hdom
  have hcu : 2 ≤ compCu exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compCu]
    exact le_trans (by norm_num : (2 : ℝ≥0∞) ≤ 3) le_add_self
  have hsmall := compChi_smallness exc1 exc2 ν1 ν2 K1 K2 N
  have hetaHu : compHuCOf (compT exc1 exc2 ν1 ν2 K1 K2)
      (cMx K1 K2 : ℝ≥0∞) (compX exc1 exc2 ν1 ν2 K1 K2 N)
      (cLz N K1 K2) * etaG (5 / 2) Rv μ ≤ 1 := by
    refine mul_le_one_of_le_inv (le_trans heta ?_)
    rw [compEtaStar]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hu := cG_le_of_compHuCOf Rv μ v0 hhalf
    (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
    (compX exc1 exc2 ν1 ν2 K1 K2 N) (cLz N K1 K2) hetaHu
  have hetaStar : etaG (5 / 2) Rv μ
      ≤ cEtaStar (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0
          (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
          (compX exc1 exc2 ν1 ν2 K1 K2 N) := by
    refine le_trans heta (le_trans ?_
      (compEtaOf_le_cEtaStar μ v0 hhalf _ _ _))
    rw [compEtaStar]
    exact min_le_left _ _
  have hmain := composite_failure_le_final (5 / 2 : ℝ) Rv μ v0
    exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
    (δ := 1 / 8) (L := 1 / 4) (K := 4 / 27)
    (by norm_num) (by norm_num) (by norm_num) quarter_L_bound
    (by norm_num) fourTwentySeventh_K_bound
    hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
    hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2
    (compT exc1 exc2 ν1 ν2 K1 K2) 8 (compEM exc1 exc2 ν1 ν2)
    (cMx K1 K2 : ℝ≥0∞)
    hT1 hT2 (rootTilt_le Rv μ v0 hhalf) heM1 heM2 hκ1 hκ2
    compLamS_lt_one
    (compChi exc1 exc2 ν1 ν2 K1 K2 N)
    (compC exc1 exc2 ν1 ν2 K1 K2)
    (compCu exc1 exc2 ν1 ν2 K1 K2)
    hchi0 hC hafford hcu hsmall hu hetaStar
  intro h
  refine le_trans (hmain h) (mul_le_mul_left ?_ _)
  rw [compKcFinal]
  exact cKc_le_compKcOf μ v0 hhalf _ _ _

/-- **The composite two-law matching theorem with μ-free constants**, an
intermediate form of `thm:composite-matching` still carrying the
domination hypothesis: under the same instance pack and the projective
sample pack, the defect `compKcFinal · η` is at most `2⁻¹`, and one
binary-tree automorphism matches the two infinite composite samples
with probability at least `1 - compKcFinal · η`. -/
theorem composite_matching_bound {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega)
    [IsProbabilityMeasure Pm]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (hdom : cMpBudget (compEM exc1 exc2 ν1 ν2)
          (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
        * (2 * (2 * compC exc1 exc2 ν1 ν2 K1 K2) ^ cRank N)
        ≤ compC exc1 exc2 ν1 ν2 K1 K2)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStar exc1 exc2 ν1 ν2 K1 K2 N)
    (Xs Ys : (n : ℕ) → Omega → FullLab (CState V) n)
    (hXs : ∀ n omega, restrictLab n (Xs (n + 1) omega) = Xs n omega)
    (hYs : ∀ n omega, restrictLab n (Ys (n + 1) omega) = Ys n omega)
    (hpairM : ∀ n, Measurable (fun omega => (Xs n omega, Ys n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (Xs n omega, Ys n omega)) =
      (prodPMF (cT exc1 μ ν1 v0 n) (cT exc2 μ ν2 v0 n)).toMeasure) :
    compKcFinal exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinal exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ
        ≤ Pm {omega | InfMatch (cRel Rv)
            (fun n => Xs n omega) (fun n => Ys n omega)} := by
  have hT1 : cTiltSum (5 / 2) exc1 μ ν1 v0
      ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compT]
    exact le_trans (cTiltSum_le_compTiltBound exc1 ν1 μ v0 hsup1 hhalf)
      (le_max_left _ _)
  have hT2 : cTiltSum (5 / 2) exc2 μ ν2 v0
      ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compT]
    exact le_trans (cTiltSum_le_compTiltBound exc2 ν2 μ v0 hsup2 hhalf)
      (le_max_right _ _)
  have heM1 : cExcMass exc1 ν1 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_left _ _
  have heM2 : cExcMass exc2 ν2 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_right _ _
  have hκ1 : (K1.card : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) :=
    Nat.cast_le.mpr (le_trans (le_max_left _ _) (le_max_left _ _))
  have hκ2 : (K2.card : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) :=
    Nat.cast_le.mpr (le_trans (le_max_right _ _) (le_max_left _ _))
  have hchi0 := compChi_ne_zero exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1
    hsup2 hdecl2
  have hC : cNcBudget (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      ≤ compC exc1 exc2 ν1 ν2 K1 K2 := le_of_eq (by rw [compC])
  have hafford := compChi_afford exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1
    hsup2 hdecl2 hdom
  have hcu : 2 ≤ compCu exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compCu]
    exact le_trans (by norm_num : (2 : ℝ≥0∞) ≤ 3) le_add_self
  have hsmall := compChi_smallness exc1 exc2 ν1 ν2 K1 K2 N
  have hetaHu : compHuCOf (compT exc1 exc2 ν1 ν2 K1 K2)
      (cMx K1 K2 : ℝ≥0∞) (compX exc1 exc2 ν1 ν2 K1 K2 N)
      (cLz N K1 K2) * etaG (5 / 2) Rv μ ≤ 1 := by
    refine mul_le_one_of_le_inv (le_trans heta ?_)
    rw [compEtaStar]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hu := cG_le_of_compHuCOf Rv μ v0 hhalf
    (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
    (compX exc1 exc2 ν1 ν2 K1 K2 N) (cLz N K1 K2) hetaHu
  have hetaStar : etaG (5 / 2) Rv μ
      ≤ cEtaStar (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0
          (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
          (compX exc1 exc2 ν1 ν2 K1 K2 N) := by
    refine le_trans heta (le_trans ?_
      (compEtaOf_le_cEtaStar μ v0 hhalf _ _ _))
    rw [compEtaStar]
    exact min_le_left _ _
  have hKcle : cKc (1 / 8) (1 / 4) (4 / 27) μ v0
      (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
      (compX exc1 exc2 ν1 ν2 K1 K2 N)
      ≤ compKcFinal exc1 exc2 ν1 ν2 K1 K2 N := by
    rw [compKcFinal]
    exact cKc_le_compKcOf μ v0 hhalf _ _ _
  constructor
  · -- the half-barrier clause
    have h2 : etaG (5 / 2) Rv μ
        ≤ (2 * compKcFinal exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ := by
      refine le_trans heta ?_
      rw [compEtaStar]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    calc compKcFinal exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ
        ≤ compKcFinal exc1 exc2 ν1 ν2 K1 K2 N
          * (2 * compKcFinal exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ :=
          mul_le_mul_right h2 _
      _ ≤ 2⁻¹ := by
          rw [ENNReal.le_inv_iff_mul_le]
          calc compKcFinal exc1 exc2 ν1 ν2 K1 K2 N
              * (2 * compKcFinal exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ * 2
              = 2 * compKcFinal exc1 exc2 ν1 ν2 K1 K2 N
                * (2 * compKcFinal exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ := by
                ring
            _ ≤ 1 := ENNReal.mul_inv_le_one _
  · -- the matching probability
    have hmain := composite_matching_le_final (5 / 2 : ℝ) Rv μ v0
      exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N Pm
      (δ := 1 / 8) (L := 1 / 4) (K := 4 / 27)
      (by norm_num) (by norm_num) (by norm_num) quarter_L_bound
      (by norm_num) fourTwentySeventh_K_bound
      hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
      hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2
      (compT exc1 exc2 ν1 ν2 K1 K2) 8 (compEM exc1 exc2 ν1 ν2)
      (cMx K1 K2 : ℝ≥0∞)
      hT1 hT2 (rootTilt_le Rv μ v0 hhalf) heM1 heM2 hκ1 hκ2
      compLamS_lt_one
      (compChi exc1 exc2 ν1 ν2 K1 K2 N)
      (compC exc1 exc2 ν1 ν2 K1 K2)
      (compCu exc1 exc2 ν1 ν2 K1 K2)
      hchi0 hC hafford hcu hsmall hu hetaStar
      Xs Ys hXs hYs hpairM hlaw
    refine le_trans ?_ hmain
    exact tsub_le_tsub_left (mul_le_mul_left hKcle _) 1

/-! ### The no-exception witness -/

/-- The retained exceptional mass of the empty chart vanishes. -/
lemma cExcMass_none (ν : PMF ℕ) :
    cExcMass (fun _ => none) ν = 0 := by
  rw [cExcMass]
  refine (tsum_congr fun z => ?_).trans tsum_zero
  exact if_pos rfl

/-- The two-sided exceptional mass of the no-exception instance
vanishes. -/
lemma compEM_no_exceptions (ν1 ν2 : PMF ℕ) :
    compEM (fun _ => none) (fun _ => none) ν1 ν2 = 0 := by
  rw [compEM, cExcMass_none, cExcMass_none]
  exact max_self 0

/-- **Non-vacuity witness: the no-exception instance**
(`thm:composite-matching` at empty exceptional charts).  For a single
offspring law `ν` with support `K` and the empty charts, every
structural hypothesis of `composite_failure_bound` holds with
`S = K1 = K2 = K`, `E1 = E2 = ∅`, `N = K.sup id`, and the domination
hypothesis holds outright (`hdom_of_compEM_le` at exceptional mass
zero): the hypothesis pack of the headline theorems is proved
satisfiable. -/
theorem composite_failure_bound_no_exceptions
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (ν : PMF ℕ) (K : Finset ℕ)
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ K)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStar (fun _ => none) (fun _ => none) ν ν K K
          (K.sup id)) :
    ∀ h, failureD (cT (fun _ => none) μ ν v0 h)
        (cT (fun _ => none) μ ν v0 h) (fullSim (cRel Rv) h)
      ≤ compKcFinal (fun _ => none) (fun _ => none) ν ν K K (K.sup id)
        * etaG (5 / 2) Rv μ := by
  have hKne : K.Nonempty := by
    obtain ⟨k, hk⟩ : ∃ k, (ν k : ℝ≥0∞) ≠ 0 := by
      by_contra hall
      push Not at hall
      have h1 := ν.tsum_coe
      rw [tsum_congr fun k => hall k, tsum_zero] at h1
      exact one_ne_zero h1.symm
    exact ⟨k, (hsup k).mp hk⟩
  have hnone : ∀ (k : ℕ) (p : ℕ × ℕ),
      (fun _ => (none : Option (ℕ × ℕ))) k = some p → False :=
    fun _ p hp => Option.some_ne_none p
      (show some p = (none : Option (ℕ × ℕ)) from hp.symm)
  have hEg : ∀ p : ℕ × ℕ, p ∈ (∅ : Finset (ℕ × ℕ))
      ↔ ∃ z, (ν z : ℝ≥0∞) ≠ 0
        ∧ (fun _ => (none : Option (ℕ × ℕ))) z = some p := by
    intro p
    constructor
    · intro hp
      exact absurd hp (Finset.notMem_empty p)
    · rintro ⟨z, -, hz⟩
      exact (hnone z p hz).elim
  have hdom := hdom_of_compEM_le (fun _ => none) (fun _ => none) ν ν
    K K (K.sup id)
    (le_trans (le_of_eq (compEM_no_exceptions ν ν)) zero_le)
  exact composite_failure_bound Rv μ v0 (fun _ => none)
    (fun _ => none) ν ν K K K ∅ ∅ (K.sup id) hRv hsymm hμ0 hhalf
    (fun j _ => ⟨rfl, rfl⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k hk _ => ⟨Finset.le_sup (f := id) ((hsup k).mp hk), hk⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k hk _ => ⟨Finset.le_sup (f := id) ((hsup k).mp hk), hk⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    hsup hsup
    (fun k => ⟨fun hk => ⟨(hsup k).mpr hk, rfl⟩,
      fun hh => (hsup k).mp hh.1⟩)
    hKne hEg hEg hdom heta

end Headline

/-! ### The merged μ-free constants -/

/-- The merged row budget `2·C`: with the rare rows folded into the
nilpotent block at raw weight, the common and the exceptional rows
together occupy at most `(1 + eM)·C ≤ 2·C` (`compMpBudget_eq`,
`compEM_le_one`). -/
noncomputable def compCM (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) : ℝ≥0∞ :=
  2 * compC exc1 exc2 ν1 ν2 K1 K2

/-- The merged Green debt multiplier `X = cX (2C) (cRank N) cu`. -/
noncomputable def compXM (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  cX (compCM exc1 exc2 ν1 ν2 K1 K2) (cRank N)
    (compCu exc1 exc2 ν1 ν2 K1 K2)

/-- **The merged μ-free ordinary barrier**: `compKcOf` at the merged
row budget; the failure constant of
`composite_failure_bound_massfree`. -/
noncomputable def compKcFinalM (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  compKcOf (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
    (compXM exc1 exc2 ν1 ν2 K1 K2 N)

/-- **The merged μ-free threshold**: the minimum of the absorption
entry, the screen-closure entry, and the half-barrier entry, all at
the merged Green debt multiplier. -/
noncomputable def compEtaStarM (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  min ((compC2Of (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
        (compXM exc1 exc2 ν1 ν2 K1 K2 N)
      + compC3Of (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
          (compXM exc1 exc2 ν1 ν2 K1 K2 N) + 1)⁻¹)
    (min ((compHuCOf (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
          (compXM exc1 exc2 ν1 ν2 K1 K2 N) (cLz N K1 K2))⁻¹)
      ((2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹))

/-! ### `eq:composite-K-eps` in closed form -/

/-- The linear debt coefficient at `δ = 1/8` in closed form:
`B₁ = (25/4 + 4Tκ)·X`. -/
lemma cLinB_eq (T κ X : ℝ≥0∞) :
    cLinB (1 / 8) T κ X = (25 / 4 + 4 * T * κ) * X := by
  have h94 : ENNReal.ofReal (2 * (1 + 1 / 8)) = 9 / 4 := by
    rw [show (2 : ℝ) * (1 + 1 / 8) = 9 / 4 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have h164 : (4 : ℝ≥0∞) = 16 / 4 := by
    rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
    norm_num
  have h25 : (9 : ℝ≥0∞) / 4 + 4 = 25 / 4 := by
    nth_rewrite 2 [h164]
    rw [ENNReal.div_add_div_same]
    norm_num
  rw [cLinB, h94, h25]

/-- **`C_W` of `eq:composite-K-eps`**: the merged row budget in closed form,
`C_W = 32m + 256m²T` at `m = cMx`. -/
lemma compCM_eq (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ) :
    compCM exc1 exc2 ν1 ν2 K1 K2
      = 32 * (cMx K1 K2 : ℝ≥0∞)
        + 256 * (cMx K1 K2 : ℝ≥0∞) ^ 2 * compT exc1 exc2 ν1 ν2 K1 K2 := by
  rw [compCM, compC, cNcBudget]
  ring

/-- **`Ξ` of `eq:composite-K-eps`**: the merged Green debt multiplier in closed form,
`Ξ = 2(16T + 3)·∑_{j<r}(2C_W)^j` at `r = cRank N`. -/
lemma compXM_eq (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ) (N : ℕ) :
    compXM exc1 exc2 ν1 ν2 K1 K2 N
      = 2 * (16 * compT exc1 exc2 ν1 ν2 K1 K2 + 3)
        * ∑ j : Fin (cRank N), (2 * compCM exc1 exc2 ν1 ν2 K1 K2) ^ (j : ℕ) := by
  rw [compXM, cX, graftGreenMultiplier, graftGreenRemainder, compCu]
  ring

/-- **`K` of `eq:composite-K-eps`**: the merged ordinary barrier in closed form,
`K = 6(4 + (25/4 + 4Tm)Ξ)`. -/
lemma compKcFinalM_eq (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ) (N : ℕ) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N
      = 6 * (4 + (25 / 4 + 4 * compT exc1 exc2 ν1 ν2 K1 K2 * (cMx K1 K2 : ℝ≥0∞))
          * compXM exc1 exc2 ν1 ν2 K1 K2 N) := by
  rw [compKcFinalM, compKcOf, cLinB_eq]
  ring

/-- **`B` of `eq:composite-K-eps`**: the μ-free quadratic coefficient in closed form,
`B = 160K² + 12KΞ(1 + Tκ) + 4Tκ·Ξ²`. -/
lemma compB2Of_eq (T κ X : ℝ≥0∞) :
    compB2Of T κ X
      = 160 * compKcOf T κ X ^ 2
        + 12 * compKcOf T κ X * X * (1 + T * κ) + 4 * T * κ * X ^ 2 := by
  rw [compB2Of]
  ring

/-- **`A` of `eq:composite-K-eps`**: the absorption entry in closed form,
`A = 16B + 15(K + (25/4 + 4Tκ)Ξ) + 1`. -/
lemma compAM_eq (T κ X : ℝ≥0∞) :
    compC2Of T κ X + compC3Of T κ X + 1
      = 16 * compB2Of T κ X
        + 15 * (compKcOf T κ X + (25 / 4 + 4 * T * κ) * X) + 1 := by
  rw [compC2Of, compC3Of, cLinB_eq]
  ring

/-- **`H` of `eq:composite-K-eps`**: the screen-closure entry in closed form,
`H = 3K + (1 + 8T)(24KΞ + 16(n_A·m·Ξ)²)` at the singleton-length budget
`Lz = 2·n_A·m`. -/
lemma compHuCOf_eq (T κ X : ℝ≥0∞) (nA m : ℕ) :
    compHuCOf T κ X (2 * (nA * m))
      = 3 * compKcOf T κ X
        + (1 + 8 * T) * (24 * (compKcOf T κ X * X)
            + 16 * ((nA : ℝ≥0∞) * (m : ℝ≥0∞) * X) ^ 2) := by
  rw [compHuCOf]
  push_cast
  ring

/-- **`ε` of `eq:composite-K-eps`**: the merged threshold is the inverse of the maximum
of the absorption entry, the screen-closure entry, and twice the barrier,
`ε⁻¹ = max {A, H, 2K}`. -/
lemma compEtaStarM_eq (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ) (N : ℕ) :
    compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N
      = (max (compC2Of (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
            (compXM exc1 exc2 ν1 ν2 K1 K2 N)
          + compC3Of (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
              (compXM exc1 exc2 ν1 ν2 K1 K2 N) + 1)
        (max (compHuCOf (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
            (compXM exc1 exc2 ν1 ν2 K1 K2 N) (cLz N K1 K2))
          (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)))⁻¹ := by
  have hminmax : ∀ a b : ℝ≥0∞, min a⁻¹ b⁻¹ = (max a b)⁻¹ := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right h, min_eq_right (ENNReal.inv_le_inv.mpr h)]
    · rw [max_eq_left h, min_eq_left (ENNReal.inv_le_inv.mpr h)]
  rw [compEtaStarM, hminmax, hminmax]

/-! ### Finiteness and positivity of the merged constants -/

section MergedInstance

variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

lemma compCM_ne_top
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compCM exc1 exc2 ν1 ν2 K1 K2 ≠ ⊤ := by
  rw [compCM]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (compC_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2)

lemma compXM_ne_top
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compXM exc1 exc2 ν1 ν2 K1 K2 N ≠ ⊤ := by
  rw [compXM, cX, graftGreenMultiplier, graftGreenRemainder]
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ?_)
    (compCu_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2)
  refine ENNReal.sum_ne_top.mpr fun j _ => ENNReal.pow_ne_top ?_
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (compCM_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2)

/-- **Finiteness of the merged failure constant.** -/
theorem compKcFinalM_ne_top
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N ≠ ⊤ := by
  rw [compKcFinalM]
  exact compKcOf_ne_top
    (compT_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2)
    (ENNReal.natCast_ne_top _)
    (compXM_ne_top exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1 hsup2 hdecl2)

/-- **Positivity of the merged threshold**: under chargedness of the
declared pairs all three entries of the minimum are positive. -/
theorem compEtaStarM_pos
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    0 < compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N := by
  have hT := compT_ne_top exc1 exc2 ν1 ν2 K1 K2 hsup1 hdecl1 hsup2 hdecl2
  have hκ : (cMx K1 K2 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hX := compXM_ne_top exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1 hsup2
    hdecl2
  rw [compEtaStarM]
  refine lt_min_iff.mpr ⟨?_, lt_min_iff.mpr ⟨?_, ?_⟩⟩
  · rw [ENNReal.inv_pos]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨compC2Of_ne_top hT hκ hX, compC3Of_ne_top hT hκ hX⟩,
        ENNReal.one_ne_top⟩
  · rw [ENNReal.inv_pos]
    exact compHuCOf_ne_top hT hκ hX _
  · rw [ENNReal.inv_pos]
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top ?_
    exact compKcFinalM_ne_top exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1
      hsup2 hdecl2

/-- The merged threshold is nonzero (the form used by the headline
hypotheses). -/
theorem compEtaStarM_ne_zero
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0) :
    compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N ≠ 0 :=
  (compEtaStarM_pos exc1 exc2 ν1 ν2 K1 K2 N hsup1 hdecl1 hsup2
    hdecl2).ne'

/-- The merged threshold is finite: the absorption entry is at most
one. -/
theorem compEtaStarM_ne_top :
    compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [compEtaStarM]
  exact le_trans (min_le_left _ _) (ENNReal.inv_le_one.mpr le_add_self)

/-! ### The merged constants at an arbitrary tilt budget -/

/-- The screen-closure weight `cu = 16T + 3` at an arbitrary tilt budget. -/
noncomputable def compCuT (T : ℝ≥0∞) : ℝ≥0∞ := 16 * T + 3

/-- The merged row budget `2 · cNcBudget (8T)` at an arbitrary tilt budget. -/
noncomputable def compCMT (T : ℝ≥0∞) (K1 K2 : Finset ℕ) : ℝ≥0∞ :=
  2 * cNcBudget (8 * T) (cMx K1 K2)

/-- The merged Green debt multiplier at an arbitrary tilt budget. -/
noncomputable def compXMT (T : ℝ≥0∞) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  cX (compCMT T K1 K2) (cRank N) (compCuT T)

/-- **The merged μ-free ordinary barrier at an arbitrary tilt budget**:
`K_ν⃗` of `eq:composite-K-eps` as a function of any `T`. -/
noncomputable def compKcFinalMT (T : ℝ≥0∞) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  compKcOf T (cMx K1 K2 : ℝ≥0∞) (compXMT T K1 K2 N)

/-- **The merged μ-free threshold at an arbitrary tilt budget**:
`ε_ν⃗` of `eq:composite-K-eps` as a function of any `T`. -/
noncomputable def compEtaStarMT (T : ℝ≥0∞) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  min ((compC2Of T (cMx K1 K2 : ℝ≥0∞) (compXMT T K1 K2 N)
      + compC3Of T (cMx K1 K2 : ℝ≥0∞) (compXMT T K1 K2 N) + 1)⁻¹)
    (min ((compHuCOf T (cMx K1 K2 : ℝ≥0∞) (compXMT T K1 K2 N) (cLz N K1 K2))⁻¹)
      ((2 * compKcFinalMT T K1 K2 N)⁻¹))

lemma compCMT_ne_top {T : ℝ≥0∞} (hT : T ≠ ⊤) (K1 K2 : Finset ℕ) :
    compCMT T K1 K2 ≠ ⊤ := by
  rw [compCMT, cNcBudget]
  refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.add_ne_top.mpr ⟨?_, ?_⟩)
  · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _)
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.natCast_ne_top _)))
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT)

lemma compCuT_ne_top {T : ℝ≥0∞} (hT : T ≠ ⊤) : compCuT T ≠ ⊤ := by
  rw [compCuT]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT, ENNReal.ofNat_ne_top⟩

lemma compXMT_ne_top {T : ℝ≥0∞} (hT : T ≠ ⊤) (K1 K2 : Finset ℕ) (N : ℕ) :
    compXMT T K1 K2 N ≠ ⊤ := by
  rw [compXMT, cX, graftGreenMultiplier, graftGreenRemainder]
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ?_)
    (compCuT_ne_top hT)
  refine ENNReal.sum_ne_top.mpr fun j _ => ENNReal.pow_ne_top ?_
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (compCMT_ne_top hT K1 K2)

theorem compKcFinalMT_ne_top {T : ℝ≥0∞} (hT : T ≠ ⊤)
    (K1 K2 : Finset ℕ) (N : ℕ) : compKcFinalMT T K1 K2 N ≠ ⊤ := by
  rw [compKcFinalMT]
  exact compKcOf_ne_top hT (ENNReal.natCast_ne_top _)
    (compXMT_ne_top hT K1 K2 N)

/-- **Positivity of the threshold at an arbitrary finite tilt budget**:
`ε_ν⃗(T) > 0` whenever `T ≠ ⊤`. -/
theorem compEtaStarMT_pos {T : ℝ≥0∞} (hT : T ≠ ⊤)
    (K1 K2 : Finset ℕ) (N : ℕ) : 0 < compEtaStarMT T K1 K2 N := by
  have hκ : (cMx K1 K2 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hX := compXMT_ne_top hT K1 K2 N
  rw [compEtaStarMT]
  refine lt_min_iff.mpr ⟨?_, lt_min_iff.mpr ⟨?_, ?_⟩⟩
  · rw [ENNReal.inv_pos]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨compC2Of_ne_top hT hκ hX, compC3Of_ne_top hT hκ hX⟩,
        ENNReal.one_ne_top⟩
  · rw [ENNReal.inv_pos]
    exact compHuCOf_ne_top hT hκ hX _
  · rw [ENNReal.inv_pos]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (compKcFinalMT_ne_top hT K1 K2 N)

/-- Every merged constant is monotone in the tilt budget: the debt multiplier. -/
lemma compXMT_mono {T T' : ℝ≥0∞} (h : T ≤ T') (K1 K2 : Finset ℕ) (N : ℕ) :
    compXMT T K1 K2 N ≤ compXMT T' K1 K2 N := by
  rw [compXMT, compXMT, cX, cX, graftGreenMultiplier, graftGreenMultiplier,
    graftGreenRemainder, graftGreenRemainder, compCMT, compCMT, compCuT, compCuT,
    cNcBudget, cNcBudget]
  gcongr

/-- The linear debt coefficient is monotone in the tilt budget and the multiplier. -/
lemma cLinB_mono {T T' X X' : ℝ≥0∞} (κ : ℝ≥0∞) (hT : T ≤ T') (hX : X ≤ X') :
    cLinB (1 / 8) T κ X ≤ cLinB (1 / 8) T' κ X' := by
  rw [cLinB_eq, cLinB_eq]
  gcongr

/-- The ordinary barrier is monotone in the tilt budget and the multiplier. -/
lemma compKcOf_mono {T T' X X' : ℝ≥0∞} (κ : ℝ≥0∞) (hT : T ≤ T') (hX : X ≤ X') :
    compKcOf T κ X ≤ compKcOf T' κ X' := by
  rw [compKcOf, compKcOf]
  gcongr
  exact cLinB_mono κ hT hX

/-- The quadratic debt coefficient is monotone in the tilt budget and the multiplier. -/
lemma compB2Of_mono {T T' X X' : ℝ≥0∞} (κ : ℝ≥0∞) (hT : T ≤ T') (hX : X ≤ X') :
    compB2Of T κ X ≤ compB2Of T' κ X' := by
  rw [compB2Of, compB2Of]
  gcongr <;> exact compKcOf_mono κ hT hX

/-- The first absorbed coefficient is monotone in the tilt budget and the multiplier. -/
lemma compC2Of_mono {T T' X X' : ℝ≥0∞} (κ : ℝ≥0∞) (hT : T ≤ T') (hX : X ≤ X') :
    compC2Of T κ X ≤ compC2Of T' κ X' := by
  rw [compC2Of, compC2Of]
  gcongr <;> first
    | exact compB2Of_mono κ hT hX
    | exact compKcOf_mono κ hT hX
    | exact cLinB_mono κ hT hX

/-- The second absorbed coefficient is monotone in the tilt budget and the multiplier. -/
lemma compC3Of_mono {T T' X X' : ℝ≥0∞} (κ : ℝ≥0∞) (hT : T ≤ T') (hX : X ≤ X') :
    compC3Of T κ X ≤ compC3Of T' κ X' := by
  rw [compC3Of, compC3Of]
  gcongr
  exact compB2Of_mono κ hT hX

/-- The screen-closure constant is monotone in the tilt budget and the multiplier. -/
lemma compHuCOf_mono {T T' X X' : ℝ≥0∞} (κ : ℝ≥0∞) (Lz : ℕ) (hT : T ≤ T') (hX : X ≤ X') :
    compHuCOf T κ X Lz ≤ compHuCOf T' κ X' Lz := by
  rw [compHuCOf, compHuCOf]
  gcongr <;> exact compKcOf_mono κ hT hX

end MergedInstance

/-! ### The mass-free headline theorems -/

/-- Half barrier from the reciprocal entry: `η ≤ (2K)⁻¹` gives `K·η ≤ 2⁻¹`. -/
lemma mul_le_half_of_le_inv {K η : ℝ≥0∞} (h : η ≤ (2 * K)⁻¹) : K * η ≤ 2⁻¹ := by
  calc K * η ≤ K * (2 * K)⁻¹ := mul_le_mul_right h _
    _ ≤ 2⁻¹ := by
        rw [ENNReal.le_inv_iff_mul_le]
        calc K * (2 * K)⁻¹ * 2 = 2 * K * (2 * K)⁻¹ := by ring
          _ ≤ 1 := ENNReal.mul_inv_le_one _

section MassFree

variable (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)

/-- **The half barrier of `eq:composite-bound`**: below the merged threshold the
failure constant times the potential is at most `2⁻¹`, from the third entry of
the minimum. -/
lemma compKcFinalM_mul_le_half {η : ℝ≥0∞}
    (heta : η ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * η ≤ 2⁻¹ := by
  have h2 : η ≤ (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ := by
    refine le_trans heta ?_
    rw [compEtaStarM]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  calc compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * η
      ≤ compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N
        * (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ :=
        mul_le_mul_right h2 _
    _ ≤ 2⁻¹ := by
        rw [ENNReal.le_inv_iff_mul_le]
        calc compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N
            * (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ * 2
            = 2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N
              * (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ := by ring
          _ ≤ 1 := ENNReal.mul_inv_le_one _

/-- **The composite two-law mismatch bound, mass-free form**
(`thm:composite-matching`, merged rows): under the structural instance
pack, the root-mass floor `2⁻¹ ≤ μ v0`, and the graph potential below
the merged μ-free threshold `compEtaStarM`, the mismatch at every
height is at most `compKcFinalM · η`.  No hypothesis constrains the
exceptional masses: the rare rows ride inside the merged row budget
`compCM = 2·compC` (`compMpBudget_eq`, `compEM_le_one`), so the bound
holds for every admissible pair of laws.  All constants are built
from `(exc1, exc2, ν1, ν2, K1, K2, N)` alone. -/
theorem composite_failure_bound_massfree
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N) :
    ∀ h, failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
        (fullSim (cRel Rv) h)
      ≤ compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ := by
  have hT1 : cTiltSum (5 / 2) exc1 μ ν1 v0
      ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compT]
    exact le_trans (cTiltSum_le_compTiltBound exc1 ν1 μ v0 hsup1 hhalf)
      (le_max_left _ _)
  have hT2 : cTiltSum (5 / 2) exc2 μ ν2 v0
      ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compT]
    exact le_trans (cTiltSum_le_compTiltBound exc2 ν2 μ v0 hsup2 hhalf)
      (le_max_right _ _)
  have heM1 : cExcMass exc1 ν1 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_left _ _
  have heM2 : cExcMass exc2 ν2 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_right _ _
  have hκ1 : (K1.card : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) :=
    Nat.cast_le.mpr (le_trans (le_max_left _ _) (le_max_left _ _))
  have hκ2 : (K2.card : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) :=
    Nat.cast_le.mpr (le_trans (le_max_right _ _) (le_max_left _ _))
  have hC : cNcBudget (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      + cMpBudget (compEM exc1 exc2 ν1 ν2)
          (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      ≤ compCM exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compMpBudget_eq exc1 exc2 ν1 ν2 K1 K2, compCM, two_mul]
    refine add_le_add (le_of_eq (by rw [compC])) ?_
    calc compEM exc1 exc2 ν1 ν2 * compC exc1 exc2 ν1 ν2 K1 K2
        ≤ 1 * compC exc1 exc2 ν1 ν2 K1 K2 :=
          mul_le_mul_left (compEM_le_one exc1 exc2 ν1 ν2) _
      _ = compC exc1 exc2 ν1 ν2 K1 K2 := one_mul _
  have hcu : 2 ≤ compCu exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compCu]
    exact le_trans (by norm_num : (2 : ℝ≥0∞) ≤ 3) le_add_self
  have hetaHu : compHuCOf (compT exc1 exc2 ν1 ν2 K1 K2)
      (cMx K1 K2 : ℝ≥0∞) (compXM exc1 exc2 ν1 ν2 K1 K2 N)
      (cLz N K1 K2) * etaG (5 / 2) Rv μ ≤ 1 := by
    refine mul_le_one_of_le_inv (le_trans heta ?_)
    rw [compEtaStarM]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hu := cG_le_of_compHuCOf Rv μ v0 hhalf
    (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
    (compXM exc1 exc2 ν1 ν2 K1 K2 N) (cLz N K1 K2) hetaHu
  have hetaStar : etaG (5 / 2) Rv μ
      ≤ cEtaStar (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0
          (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
          (compXM exc1 exc2 ν1 ν2 K1 K2 N) := by
    refine le_trans heta (le_trans ?_
      (compEtaOf_le_cEtaStar μ v0 hhalf _ _ _))
    rw [compEtaStarM]
    exact min_le_left _ _
  have hmain := composite_failure_le_merged (5 / 2 : ℝ) Rv μ v0
    exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
    (δ := 1 / 8) (L := 1 / 4) (K := 4 / 27)
    (by norm_num) (by norm_num) (by norm_num) quarter_L_bound
    (by norm_num) fourTwentySeventh_K_bound
    hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
    hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2
    (compT exc1 exc2 ν1 ν2 K1 K2) 8 (compEM exc1 exc2 ν1 ν2)
    (cMx K1 K2 : ℝ≥0∞)
    hT1 hT2 (rootTilt_le Rv μ v0 hhalf) heM1 heM2 hκ1 hκ2
    compLamS_lt_one
    (compCM exc1 exc2 ν1 ν2 K1 K2)
    (compCu exc1 exc2 ν1 ν2 K1 K2)
    hC hcu hu hetaStar
  intro h
  refine le_trans (hmain h) (mul_le_mul_left ?_ _)
  rw [compKcFinalM]
  exact cKc_le_compKcOf μ v0 hhalf _ _ _

/-- **The composite two-law matching theorem, mass-free form**
(`thm:composite-matching`, with the explicit constants
`eq:composite-K-eps`): under the same instance pack and the projective
sample pack, the defect `compKcFinalM · η` is at most `2⁻¹`, and one
binary-tree automorphism matches the two infinite composite samples
with probability at least `1 - compKcFinalM · η`; no hypothesis
constrains the exceptional masses. -/
theorem composite_matching_bound_massfree {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega)
    [IsProbabilityMeasure Pm]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N)
    (Xs Ys : (n : ℕ) → Omega → FullLab (CState V) n)
    (hXs : ∀ n omega, restrictLab n (Xs (n + 1) omega) = Xs n omega)
    (hYs : ∀ n omega, restrictLab n (Ys (n + 1) omega) = Ys n omega)
    (hpairM : ∀ n, Measurable (fun omega => (Xs n omega, Ys n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (Xs n omega, Ys n omega)) =
      (prodPMF (cT exc1 μ ν1 v0 n) (cT exc2 μ ν2 v0 n)).toMeasure) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ
        ≤ Pm {omega | InfMatch (cRel Rv)
            (fun n => Xs n omega) (fun n => Ys n omega)} := by
  have hT1 : cTiltSum (5 / 2) exc1 μ ν1 v0
      ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compT]
    exact le_trans (cTiltSum_le_compTiltBound exc1 ν1 μ v0 hsup1 hhalf)
      (le_max_left _ _)
  have hT2 : cTiltSum (5 / 2) exc2 μ ν2 v0
      ≤ compT exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compT]
    exact le_trans (cTiltSum_le_compTiltBound exc2 ν2 μ v0 hsup2 hhalf)
      (le_max_right _ _)
  have heM1 : cExcMass exc1 ν1 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_left _ _
  have heM2 : cExcMass exc2 ν2 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_right _ _
  have hκ1 : (K1.card : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) :=
    Nat.cast_le.mpr (le_trans (le_max_left _ _) (le_max_left _ _))
  have hκ2 : (K2.card : ℝ≥0∞) ≤ (cMx K1 K2 : ℝ≥0∞) :=
    Nat.cast_le.mpr (le_trans (le_max_right _ _) (le_max_left _ _))
  have hC : cNcBudget (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      + cMpBudget (compEM exc1 exc2 ν1 ν2)
          (8 * compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2)
      ≤ compCM exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compMpBudget_eq exc1 exc2 ν1 ν2 K1 K2, compCM, two_mul]
    refine add_le_add (le_of_eq (by rw [compC])) ?_
    calc compEM exc1 exc2 ν1 ν2 * compC exc1 exc2 ν1 ν2 K1 K2
        ≤ 1 * compC exc1 exc2 ν1 ν2 K1 K2 :=
          mul_le_mul_left (compEM_le_one exc1 exc2 ν1 ν2) _
      _ = compC exc1 exc2 ν1 ν2 K1 K2 := one_mul _
  have hcu : 2 ≤ compCu exc1 exc2 ν1 ν2 K1 K2 := by
    rw [compCu]
    exact le_trans (by norm_num : (2 : ℝ≥0∞) ≤ 3) le_add_self
  have hetaHu : compHuCOf (compT exc1 exc2 ν1 ν2 K1 K2)
      (cMx K1 K2 : ℝ≥0∞) (compXM exc1 exc2 ν1 ν2 K1 K2 N)
      (cLz N K1 K2) * etaG (5 / 2) Rv μ ≤ 1 := by
    refine mul_le_one_of_le_inv (le_trans heta ?_)
    rw [compEtaStarM]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hu := cG_le_of_compHuCOf Rv μ v0 hhalf
    (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
    (compXM exc1 exc2 ν1 ν2 K1 K2 N) (cLz N K1 K2) hetaHu
  have hetaStar : etaG (5 / 2) Rv μ
      ≤ cEtaStar (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0
          (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
          (compXM exc1 exc2 ν1 ν2 K1 K2 N) := by
    refine le_trans heta (le_trans ?_
      (compEtaOf_le_cEtaStar μ v0 hhalf _ _ _))
    rw [compEtaStarM]
    exact min_le_left _ _
  have hKcle : cKc (1 / 8) (1 / 4) (4 / 27) μ v0
      (compT exc1 exc2 ν1 ν2 K1 K2) (cMx K1 K2 : ℝ≥0∞)
      (compXM exc1 exc2 ν1 ν2 K1 K2 N)
      ≤ compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N := by
    rw [compKcFinalM]
    exact cKc_le_compKcOf μ v0 hhalf _ _ _
  constructor
  · -- the half-barrier clause
    have h2 : etaG (5 / 2) Rv μ
        ≤ (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ := by
      refine le_trans heta ?_
      rw [compEtaStarM]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    calc compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ
        ≤ compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N
          * (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ :=
          mul_le_mul_right h2 _
      _ ≤ 2⁻¹ := by
          rw [ENNReal.le_inv_iff_mul_le]
          calc compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N
              * (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ * 2
              = 2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N
                * (2 * compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N)⁻¹ := by
                ring
            _ ≤ 1 := ENNReal.mul_inv_le_one _
  · -- the matching probability
    have hmain := composite_matching_le_merged (5 / 2 : ℝ) Rv μ v0
      exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N Pm
      (δ := 1 / 8) (L := 1 / 4) (K := 4 / 27)
      (by norm_num) (by norm_num) (by norm_num) quarter_L_bound
      (by norm_num) fourTwentySeventh_K_bound
      hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
      hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2
      (compT exc1 exc2 ν1 ν2 K1 K2) 8 (compEM exc1 exc2 ν1 ν2)
      (cMx K1 K2 : ℝ≥0∞)
      hT1 hT2 (rootTilt_le Rv μ v0 hhalf) heM1 heM2 hκ1 hκ2
      compLamS_lt_one
      (compCM exc1 exc2 ν1 ν2 K1 K2)
      (compCu exc1 exc2 ν1 ν2 K1 K2)
      hC hcu hu hetaStar
      Xs Ys hXs hYs hpairM hlaw
    refine le_trans ?_ hmain
    exact tsub_le_tsub_left (mul_le_mul_left hKcle _) 1

/-- At any tilt budget dominating both μ-free tilt sums, the pinned merged barrier
is dominated by the budgeted one. -/
lemma compKcFinalM_le_MT {T : ℝ≥0∞}
    (hT1 : compTiltBound exc1 ν1 K1 ≤ T)
    (hT2 : compTiltBound exc2 ν2 K2 ≤ T) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N ≤ compKcFinalMT T K1 K2 N := by
  have hT : compT exc1 exc2 ν1 ν2 K1 K2 ≤ T := max_le hT1 hT2
  have hXM : compXM exc1 exc2 ν1 ν2 K1 K2 N ≤ compXMT T K1 K2 N := by
    have h1 : compXM exc1 exc2 ν1 ν2 K1 K2 N
        = compXMT (compT exc1 exc2 ν1 ν2 K1 K2) K1 K2 N := rfl
    rw [h1]
    exact compXMT_mono hT K1 K2 N
  rw [compKcFinalM, compKcFinalMT]
  exact compKcOf_mono _ hT hXM

/-- At any tilt budget dominating both μ-free tilt sums, the budgeted threshold is
dominated by the pinned merged one. -/
lemma compEtaStarMT_le_M {T : ℝ≥0∞}
    (hT1 : compTiltBound exc1 ν1 K1 ≤ T)
    (hT2 : compTiltBound exc2 ν2 K2 ≤ T) :
    compEtaStarMT T K1 K2 N ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N := by
  have hT : compT exc1 exc2 ν1 ν2 K1 K2 ≤ T := max_le hT1 hT2
  have hXM : compXM exc1 exc2 ν1 ν2 K1 K2 N ≤ compXMT T K1 K2 N := by
    have h1 : compXM exc1 exc2 ν1 ν2 K1 K2 N
        = compXMT (compT exc1 exc2 ν1 ν2 K1 K2) K1 K2 N := rfl
    rw [h1]
    exact compXMT_mono hT K1 K2 N
  have hKc := compKcFinalM_le_MT exc1 exc2 ν1 ν2 K1 K2 N hT1 hT2
  rw [compEtaStarMT, compEtaStarM]
  refine min_le_min (ENNReal.inv_le_inv.mpr ?_)
    (min_le_min (ENNReal.inv_le_inv.mpr ?_) (ENNReal.inv_le_inv.mpr ?_))
  · exact add_le_add (add_le_add (compC2Of_mono _ hT hXM)
      (compC3Of_mono _ hT hXM)) le_rfl
  · exact compHuCOf_mono _ _ hT hXM
  · exact mul_le_mul_right hKc 2

/-- **The composite two-law mismatch bound, mass-free form, at an arbitrary tilt
budget** (`thm:composite-matching`, `eq:composite-tilt`, `eq:composite-bound`): for
any `T` bounding the two μ-free tilt sums, with the constants of
`eq:composite-K-eps` built from `T`, the half barrier holds and the mismatch at
every height is at most `compKcFinalMT T · η`, uniformly in the height. -/
theorem composite_failure_bound_massfree_T (T : ℝ≥0∞)
    (hT1 : compTiltBound exc1 ν1 K1 ≤ T)
    (hT2 : compTiltBound exc2 ν2 K2 ≤ T)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ ≤ compEtaStarMT T K1 K2 N) :
    compKcFinalMT T K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ ∀ h, failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
          (fullSim (cRel Rv) h)
        ≤ compKcFinalMT T K1 K2 N * etaG (5 / 2) Rv μ := by
  have hKle := compKcFinalM_le_MT exc1 exc2 ν1 ν2 K1 K2 N hT1 hT2
  have heta' : etaG (5 / 2) Rv μ ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N :=
    le_trans heta (compEtaStarMT_le_M exc1 exc2 ν1 ν2 K1 K2 N hT1 hT2)
  refine ⟨mul_le_half_of_le_inv (le_trans heta ?_), fun h => le_trans
    (composite_failure_bound_massfree Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
      hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2 hpair1 hpair2
      hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 heta' h)
    (mul_le_mul_left hKle _)⟩
  rw [compEtaStarMT]
  exact le_trans (min_le_right _ _) (min_le_right _ _)

/-! ### The mass-free no-exception instance -/

/-- **The composite two-law matching theorem, mass-free form, with the trajectory space
constructed** (`thm:composite-matching`, `eq:composite-bound-infinite`): under the
instance pack alone, on the product of the two trajectory measures the consistent level
processes realise the two independent infinite composite samples, the defect
`compKcFinalM · η` is at most `2⁻¹`, and one binary-tree automorphism matches them with
probability at least `1 - compKcFinalM · η`.  No probability space is assumed. -/
theorem composite_matching_bound_massfree_traj
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N) :
    compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalM exc1 exc2 ν1 ν2 K1 K2 N * etaG (5 / 2) Rv μ
        ≤ cTPair μ v0 exc1 exc2 ν1 ν2 {omega | InfMatch (cRel Rv)
            (fun n => consLab n omega.1) (fun n => consLab n omega.2)} :=
  composite_matching_bound_massfree Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
    (cTPair μ v0 exc1 exc2 ν1 ν2) hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1
    hdeclN2 hcharged2 hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 heta
    (fun n omega => consLab n omega.1) (fun n omega => consLab n omega.2)
    (fun n omega => restrictLab_consLab n omega.1)
    (fun n omega => restrictLab_consLab n omega.2)
    (fun n => measurable_consLab_pair n)
    (fun n => trajPairLab_map_consLab _ _ _ _ n)

/-- **The composite two-law matching theorem at an arbitrary tilt budget, with the
trajectory space constructed** (`thm:composite-matching`, `eq:composite-tilt`,
`eq:composite-bound-infinite`): for any `T` bounding the two μ-free tilt sums, on
the product of the two trajectory measures one binary-tree automorphism matches
the two infinite samples with probability at least `1 - compKcFinalMT T · η`. -/
theorem composite_matching_bound_massfree_traj_T
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (T : ℝ≥0∞)
    (hT1 : compTiltBound exc1 ν1 K1 ≤ T)
    (hT2 : compTiltBound exc2 ν2 K2 ≤ T)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (heta : etaG (5 / 2) Rv μ ≤ compEtaStarMT T K1 K2 N) :
    compKcFinalMT T K1 K2 N * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalMT T K1 K2 N * etaG (5 / 2) Rv μ
        ≤ cTPair μ v0 exc1 exc2 ν1 ν2 {omega | InfMatch (cRel Rv)
            (fun n => consLab n omega.1) (fun n => consLab n omega.2)} := by
  have hKle := compKcFinalM_le_MT exc1 exc2 ν1 ν2 K1 K2 N hT1 hT2
  have heta' : etaG (5 / 2) Rv μ ≤ compEtaStarM exc1 exc2 ν1 ν2 K1 K2 N :=
    le_trans heta (compEtaStarMT_le_M exc1 exc2 ν1 ν2 K1 K2 N hT1 hT2)
  obtain ⟨-, hmain⟩ := composite_matching_bound_massfree_traj Rv μ v0
    exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1
    hdeclN2 hcharged2 hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 heta'
  refine ⟨mul_le_half_of_le_inv (le_trans heta ?_),
    le_trans (tsub_le_tsub_left (mul_le_mul_left hKle _) 1) hmain⟩
  rw [compEtaStarMT]
  exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- **Non-vacuity witness: the no-exception instance, mass-free
form** (`thm:composite-matching` at empty exceptional charts, the
one-law specialisation quoted in `thm:main-matching`).  For a
single offspring law `ν` with support `K` and the empty charts, every
structural hypothesis of `composite_failure_bound_massfree` holds with
`S = K1 = K2 = K`, `E1 = E2 = ∅`, `N = K.sup id`.  The merged row
budget carries the rare rows, so nothing constrains the exceptional
mass and the pack reduces to the reflexive symmetric relation, the
root-mass floor `2⁻¹ ≤ μ v0`, and the threshold `heta`. -/
theorem composite_failure_bound_massfree_no_exceptions
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (ν : PMF ℕ) (K : Finset ℕ)
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ K)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM (fun _ => none) (fun _ => none) ν ν K K
          (K.sup id)) :
    ∀ h, failureD (cT (fun _ => none) μ ν v0 h)
        (cT (fun _ => none) μ ν v0 h) (fullSim (cRel Rv) h)
      ≤ compKcFinalM (fun _ => none) (fun _ => none) ν ν K K
          (K.sup id) * etaG (5 / 2) Rv μ := by
  have hKne : K.Nonempty := by
    obtain ⟨k, hk⟩ : ∃ k, (ν k : ℝ≥0∞) ≠ 0 := by
      by_contra hall
      push Not at hall
      have h1 := ν.tsum_coe
      rw [tsum_congr fun k => hall k, tsum_zero] at h1
      exact one_ne_zero h1.symm
    exact ⟨k, (hsup k).mp hk⟩
  have hnone : ∀ (k : ℕ) (p : ℕ × ℕ),
      (fun _ => (none : Option (ℕ × ℕ))) k = some p → False :=
    fun _ p hp => Option.some_ne_none p
      (show some p = (none : Option (ℕ × ℕ)) from hp.symm)
  have hEg : ∀ p : ℕ × ℕ, p ∈ (∅ : Finset (ℕ × ℕ))
      ↔ ∃ z, (ν z : ℝ≥0∞) ≠ 0
        ∧ (fun _ => (none : Option (ℕ × ℕ))) z = some p := by
    intro p
    constructor
    · intro hp
      exact absurd hp (Finset.notMem_empty p)
    · rintro ⟨z, -, hz⟩
      exact (hnone z p hz).elim
  exact composite_failure_bound_massfree Rv μ v0 (fun _ => none)
    (fun _ => none) ν ν K K K ∅ ∅ (K.sup id) hRv hsymm hμ0 hhalf
    (fun j _ => ⟨rfl, rfl⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k hk _ => ⟨Finset.le_sup (f := id) ((hsup k).mp hk), hk⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k hk _ => ⟨Finset.le_sup (f := id) ((hsup k).mp hk), hk⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    hsup hsup
    (fun k => ⟨fun hk => ⟨(hsup k).mpr hk, rfl⟩,
      fun hh => (hsup k).mp hh.1⟩)
    hKne hEg hEg heta

/-- **The mass-free matching theorem at the no-exception instance**
(`thm:composite-matching` at empty exceptional charts, the one-law
specialisation quoted in `thm:main-matching`, `eq:K-eps`).  For a
single offspring law `ν` with support `K`, the
empty charts, and the projective sample pack, the defect
`compKcFinalM · η` is at most `2⁻¹` and one binary-tree automorphism
matches the two infinite samples with probability at least
`1 - compKcFinalM · η`. -/
theorem composite_matching_bound_massfree_no_exceptions
    {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega)
    [IsProbabilityMeasure Pm]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (ν : PMF ℕ) (K : Finset ℕ)
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ K)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM (fun _ => none) (fun _ => none) ν ν K K
          (K.sup id))
    (Xs Ys : (n : ℕ) → Omega → FullLab (CState V) n)
    (hXs : ∀ n omega, restrictLab n (Xs (n + 1) omega) = Xs n omega)
    (hYs : ∀ n omega, restrictLab n (Ys (n + 1) omega) = Ys n omega)
    (hpairM : ∀ n, Measurable (fun omega => (Xs n omega, Ys n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (Xs n omega, Ys n omega)) =
      (prodPMF (cT (fun _ => none) μ ν v0 n)
        (cT (fun _ => none) μ ν v0 n)).toMeasure) :
    compKcFinalM (fun _ => none) (fun _ => none) ν ν K K (K.sup id)
        * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalM (fun _ => none) (fun _ => none) ν ν K K
            (K.sup id) * etaG (5 / 2) Rv μ
        ≤ Pm {omega | InfMatch (cRel Rv)
            (fun n => Xs n omega) (fun n => Ys n omega)} := by
  have hKne : K.Nonempty := by
    obtain ⟨k, hk⟩ : ∃ k, (ν k : ℝ≥0∞) ≠ 0 := by
      by_contra hall
      push Not at hall
      have h1 := ν.tsum_coe
      rw [tsum_congr fun k => hall k, tsum_zero] at h1
      exact one_ne_zero h1.symm
    exact ⟨k, (hsup k).mp hk⟩
  have hnone : ∀ (k : ℕ) (p : ℕ × ℕ),
      (fun _ => (none : Option (ℕ × ℕ))) k = some p → False :=
    fun _ p hp => Option.some_ne_none p
      (show some p = (none : Option (ℕ × ℕ)) from hp.symm)
  have hEg : ∀ p : ℕ × ℕ, p ∈ (∅ : Finset (ℕ × ℕ))
      ↔ ∃ z, (ν z : ℝ≥0∞) ≠ 0
        ∧ (fun _ => (none : Option (ℕ × ℕ))) z = some p := by
    intro p
    constructor
    · intro hp
      exact absurd hp (Finset.notMem_empty p)
    · rintro ⟨z, -, hz⟩
      exact (hnone z p hz).elim
  exact composite_matching_bound_massfree Rv μ v0 (fun _ => none)
    (fun _ => none) ν ν K K K ∅ ∅ (K.sup id) Pm hRv hsymm hμ0 hhalf
    (fun j _ => ⟨rfl, rfl⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k hk _ => ⟨Finset.le_sup (f := id) ((hsup k).mp hk), hk⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k hk _ => ⟨Finset.le_sup (f := id) ((hsup k).mp hk), hk⟩)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    (fun k p hp => (hnone k p hp).elim)
    hsup hsup
    (fun k => ⟨fun hk => ⟨(hsup k).mpr hk, rfl⟩,
      fun hh => (hsup k).mp hh.1⟩)
    hKne hEg hEg heta Xs Ys hXs hYs hpairM hlaw

/-- **The mass-free matching theorem at the no-exception instance, with the trajectory
space constructed** (`thm:main-matching` as a special case of `thm:composite-matching`,
`eq:main-bound-infinite`): for a single offspring law `ν` with support `K` and the empty
charts, on the product of the two trajectory measures the defect `compKcFinalM · η` is at
most `2⁻¹` and one binary-tree automorphism matches the two infinite samples with
probability at least `1 - compKcFinalM · η`.  No probability space is assumed. -/
theorem composite_matching_bound_massfree_no_exceptions_traj
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (ν : PMF ℕ) (K : Finset ℕ)
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ K)
    (heta : etaG (5 / 2) Rv μ
      ≤ compEtaStarM (fun _ => none) (fun _ => none) ν ν K K
          (K.sup id)) :
    compKcFinalM (fun _ => none) (fun _ => none) ν ν K K (K.sup id)
        * etaG (5 / 2) Rv μ ≤ 2⁻¹
      ∧ 1 - compKcFinalM (fun _ => none) (fun _ => none) ν ν K K
            (K.sup id) * etaG (5 / 2) Rv μ
        ≤ cTPair μ v0 (fun _ => none) (fun _ => none) ν ν {omega | InfMatch (cRel Rv)
            (fun n => consLab n omega.1) (fun n => consLab n omega.2)} :=
  composite_matching_bound_massfree_no_exceptions Rv μ v0
    (cTPair μ v0 (fun _ => none) (fun _ => none) ν ν) hRv hsymm hμ0 hhalf ν K hsup heta
    (fun n omega => consLab n omega.1) (fun n omega => consLab n omega.2)
    (fun n omega => restrictLab_consLab n omega.1)
    (fun n omega => restrictLab_consLab n omega.2)
    (fun n => measurable_consLab_pair n)
    (fun n => trajPairLab_map_consLab _ _ _ _ n)

end MassFree

end Composite
end GraphMarkovMatching
