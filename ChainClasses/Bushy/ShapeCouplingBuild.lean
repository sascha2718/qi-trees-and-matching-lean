import ChainClasses.Scalar.ShapeCoupling
import ChainClasses.Bushy.ShapeCouplingCross

/-!
`sec:shape-coupling` of `gw_classes_simple.tex`: the cascade of `thm:shape-coupling`, the
coupling it builds at the two shape laws, and `thm:hairy` across two laws over it.

The shrinking of `thm:shape-shrink` (`it:shape-shrink`) is defined on the tail shapes
only, so the cascade is carried by a partial map: `IsCascadeOn dom shrink M` asks for the
fibre decomposition and the capacity bound `eq:capacity` over the fibres
`{ρ // dom ρ ∧ shrink ρ = σ}` of the restriction, while the levels are indexed by the whole
type, a target of the shrinking lying outside the domain as often as not.  The scalar
content of the alternating series is `IsHalvingLevels`, the nonnegativity and the halving
alone, which is what the sandwich `½M₀ ≤ out ≤ M₀` needs; `IsCascade.toHalvingLevels` reads
the total interface of `ShapeCoupling.lean` in it.

The coupling is supported on the cascade pairs `(σ, shrink σ)` and on pairs of two shapes
outside the domain, with no exceptional set: a source atom spends `out`, a target atom
receives `in`, and `out + in` is its full mass, so the leftovers of the two sides sit on the
small shapes and have equal total mass, which their normalised product closes off.  At the
shape laws the domain is the tail `D² < |σ|`, where the two small shapes of a closure pair
are `9D³`-comparable through the one-vertex shape, and a cascade pair is comparable at `D`
forward and `3D²` back, both below `9D³`.

* `IsHalvingLevels`, `IsCascadeOn`: **the cascade over a partial shrinking**, with
  `IsCascadeOn.halving` propagating `eq:capacity` to every level, `half_le_outFrom` and
  `outFrom_le` the sandwich, `cascadeInOn_eq` the identity `in = M₀ - out`,
  `cascadeOut_add_cascadeInOn` the marginal clause.
* `cascMassE`, `isCascadeOn_cascMass`: **the levels of a partial shrinking**, the mass of
  the iterated fibre defined by the recursion `M_{k+1} = ∑_{fibre} M_k`, finite by the
  halving.
* `cascPair`, `leftover`, `cascCoupling`, `exists_coupling_of_out`: **the coupling read off
  the cascade**, its two marginals and its support.
* `sideDom`, `sideShrink`, `sideMass`, `sideOut`, `exists_coupling_of_capacity`: **the
  two-sided cascade**, the shrinking alternating between the two laws, and the coupling of
  two laws obeying `eq:capacity`.
* `shrinkShape`, `capacity_of_mass_bounds`, `exists_capacity_shapePMF`: **`eq:capacity` at
  the two shape laws**, the fibre of a target being confined above the size
  `max(D², s|τ|/64)`, where the tail bound of
  `thm:shape-mass` (`it:shape-mass-tail`) for the source law and the point bound
  `thm:shape-mass` (`it:shape-mass-point`) for the target law meet.
* `markedQI_shrinkShape_pair`, `exists_isShapeCoupling_of_capacity`,
  `exists_isShapeCoupling`: **`thm:shape-coupling`**, the coupling of the two shape laws
  supported on `9D³`-comparable pairs, at every `D` past a largeness condition on the two
  laws, with the shrinking taken at `s = ⌊√(D/2592)⌋`.
* `hairy_ae_shape_tree_cross_large`, `hairy_ae_shape_tree_two_law`: **`thm:hairy` across two
  laws**, the assembly reading the coupling at the scale it chooses, and the almost sure
  statement with no hypothesis left.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory GraphMatching
open BranchingProcess (sample survivalMeasure Offspring)
open scoped ENNReal Classical

/-! ### The scalar content of the cascade -/

variable {T : Type*} {dom : T → Prop} {shrink : T → T} {M : T → ℕ → ℝ}

/-- **The scalar content of the cascade**: nonnegative levels that halve.  This is all the
alternating series `out(σ) = ∑_k (-1)^k M_k(σ)` needs; where the levels come from, a total
or a partial shrinking, does not enter. -/
structure IsHalvingLevels (M : T → ℕ → ℝ) : Prop where
  /-- The levels are nonnegative. -/
  nonneg : ∀ σ k, 0 ≤ M σ k
  /-- Each level is at most half of the one before it. -/
  halving : ∀ σ k, M σ (k + 1) ≤ M σ k / 2

/-- **The cascade at a partial shrinking**: the iterated-fibre masses of a map defined on
`dom`, with the fibre decomposition over `{ρ // dom ρ ∧ shrink ρ = σ}` and the capacity
bound `eq:capacity` at the first level.  The levels are indexed by the whole type: a target
of the shrinking need not lie in its domain. -/
structure IsCascadeOn (dom : T → Prop) (shrink : T → T) (M : T → ℕ → ℝ) : Prop where
  /-- The levels are nonnegative. -/
  nonneg : ∀ σ k, 0 ≤ M σ k
  /-- The fibre decomposition of the levels. -/
  fibre : ∀ σ k, HasSum (fun ρ : {ρ : T // dom ρ ∧ shrink ρ = σ} ↦ M ρ.1 k) (M σ (k + 1))
  /-- **`eq:capacity`**: the fibre of a point carries at most half of its mass. -/
  capacity : ∀ σ, M σ 1 ≤ M σ 0 / 2

/-- **`eq:capacity` propagates to every level**: the fibre decomposition carries the
capacity bound up the cascade. -/
lemma IsCascadeOn.halving (h : IsCascadeOn dom shrink M) : ∀ (k : ℕ) (σ : T),
    M σ (k + 1) ≤ M σ k / 2 := by
  intro k
  induction k with
  | zero => exact h.capacity
  | succ n ih =>
      intro σ
      have h1 : HasSum (fun ρ : {ρ : T // dom ρ ∧ shrink ρ = σ} ↦ M ρ.1 (n + 1))
          (M σ (n + 1 + 1)) := h.fibre σ (n + 1)
      have h2 : HasSum (fun ρ : {ρ : T // dom ρ ∧ shrink ρ = σ} ↦ M ρ.1 n / 2)
          (M σ (n + 1) / 2) := HasSum.div_const (h.fibre σ n) 2
      refine hasSum_le ?_ h1 h2
      intro ρ
      exact ih ρ.1

/-- The cascade at a partial shrinking carries the scalar content. -/
lemma IsCascadeOn.toHalvingLevels (h : IsCascadeOn dom shrink M) : IsHalvingLevels M :=
  ⟨h.nonneg, fun σ k ↦ h.halving k σ⟩

/-- The cascade at a total shrinking of `ShapeCoupling.lean` carries the same scalar
content. -/
lemma IsCascade.toHalvingLevels {shrink : T → T} (h : IsCascade shrink M) :
    IsHalvingLevels M := ⟨h.nonneg, fun σ k ↦ h.halving k σ⟩

/-! ### The alternating series over the levels -/

namespace IsHalvingLevels

variable (h : IsHalvingLevels M)
include h

/-- Geometric decay along the levels: `M σ (k+m) ≤ M σ m (1/2)^k`. -/
lemma le_shift (σ : T) (m : ℕ) : ∀ k, M σ (k + m) ≤ M σ m * (1 / 2 : ℝ) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      have hrw : n + 1 + m = n + m + 1 := by omega
      rw [hrw]
      have h1 : M σ (n + m + 1) ≤ M σ (n + m) / 2 := h.halving _ _
      have h2 : M σ m * (1 / 2 : ℝ) ^ (n + 1) = M σ m * (1 / 2 : ℝ) ^ n / 2 := by
        rw [pow_succ]; ring
      rw [h2]
      linarith

lemma summable_shift (σ : T) (m : ℕ) : Summable fun k ↦ M σ (k + m) := by
  refine Summable.of_nonneg_of_le (fun k ↦ h.nonneg _ _) (h.le_shift σ m) ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

lemma summable_row (σ : T) : Summable fun k ↦ M σ k := by
  simpa using h.summable_shift σ 0

lemma tsum_shift_le (σ : T) (m : ℕ) : ∑' k, M σ (k + m) ≤ 2 * M σ m := by
  refine (Summable.tsum_le_tsum (h.le_shift σ m) (h.summable_shift σ m)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)).trans ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num
  linarith [h.nonneg σ m]

lemma summable_outFrom (σ : T) (m : ℕ) : Summable fun k ↦ (-1 : ℝ) ^ k * M σ (k + m) := by
  have habs : (fun k ↦ ‖(-1 : ℝ) ^ k * M σ (k + m)‖) = fun k ↦ M σ (k + m) := by
    funext k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_of_nonneg (h.nonneg _ _)]
  refine Summable.of_norm ?_
  rw [habs]
  exact h.summable_shift σ m

/-- Peeling the first term: `outFrom m = M σ m - outFrom (m+1)`. -/
lemma outFrom_rec (σ : T) (m : ℕ) : outFrom M σ m = M σ m - outFrom M σ (m + 1) := by
  rw [outFrom, (h.summable_outFrom σ m).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Nat.zero_add]
  have htail : ∑' k, (-1 : ℝ) ^ (k + 1) * M σ (k + 1 + m) = -outFrom M σ (m + 1) := by
    rw [outFrom, ← tsum_neg]
    refine tsum_congr fun k ↦ ?_
    have hidx : k + 1 + m = k + (m + 1) := by omega
    rw [hidx, pow_succ]
    ring
  rw [htail]
  ring

lemma abs_outFrom_le (σ : T) (m : ℕ) : |outFrom M σ m| ≤ 2 * M σ m := by
  have habs : (fun k ↦ ‖(-1 : ℝ) ^ k * M σ (k + m)‖) = fun k ↦ M σ (k + m) := by
    funext k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_of_nonneg (h.nonneg _ _)]
  have hsum : Summable fun k ↦ ‖(-1 : ℝ) ^ k * M σ (k + m)‖ := by
    rw [habs]; exact h.summable_shift σ m
  have h1 := norm_tsum_le_tsum_norm hsum
  rw [habs] at h1
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (h.tsum_shift_le σ m)

/-- The cascade mass is nonnegative. -/
lemma outFrom_nonneg (σ : T) (m : ℕ) : 0 ≤ outFrom M σ m := by
  have h1 := h.outFrom_rec σ m
  have h3 : outFrom M σ (m + 1) ≤ 2 * M σ (m + 1) :=
    (le_abs_self _).trans (h.abs_outFrom_le σ (m + 1))
  have h4 : M σ (m + 1) ≤ M σ m / 2 := h.halving _ _
  linarith

/-- **`½M₀ ≤ out`**: the alternating series loses at most the first correction, which the
capacity bound caps at half. -/
lemma half_le_outFrom (σ : T) (m : ℕ) : M σ m / 2 ≤ outFrom M σ m := by
  have h1 := h.outFrom_rec σ m
  have h2 : outFrom M σ (m + 1) ≤ M σ (m + 1) := by
    have h3 := h.outFrom_rec σ (m + 1)
    have h4 := h.outFrom_nonneg σ (m + 2)
    linarith
  have h5 : M σ (m + 1) ≤ M σ m / 2 := h.halving _ _
  linarith

/-- **`out ≤ M₀`**: the cascade never spends more than the atom carries. -/
lemma outFrom_le (σ : T) (m : ℕ) : outFrom M σ m ≤ M σ m := by
  have h1 := h.outFrom_rec σ m
  have h2 := h.outFrom_nonneg σ (m + 1)
  linarith

lemma cascadeOut_nonneg (σ : T) : 0 ≤ cascadeOut M σ := h.outFrom_nonneg σ 0

lemma half_le_cascadeOut (σ : T) : M σ 0 / 2 ≤ cascadeOut M σ := h.half_le_outFrom σ 0

lemma cascadeOut_le (σ : T) : cascadeOut M σ ≤ M σ 0 := h.outFrom_le σ 0

end IsHalvingLevels

/-! ### The mass the cascade spends at a target -/

/-- **The cascade mass `in(σ)`** spent at `σ` as a target of the partial shrinking. -/
noncomputable def cascadeInOn (dom : T → Prop) (shrink : T → T) (M : T → ℕ → ℝ) (σ : T) : ℝ :=
  ∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, cascadeOut M ρ.1

namespace IsCascadeOn

variable (h : IsCascadeOn dom shrink M)
include h

/-- The cascade masses of a fibre are summable, being dominated by the first level. -/
lemma summable_fibre_cascadeOut (σ : T) :
    Summable fun ρ : {ρ : T // dom ρ ∧ shrink ρ = σ} ↦ cascadeOut M ρ.1 := by
  refine Summable.of_nonneg_of_le (fun ρ ↦ h.toHalvingLevels.cascadeOut_nonneg ρ.1)
    (fun ρ ↦ h.toHalvingLevels.cascadeOut_le ρ.1) (h.fibre σ 0).summable

lemma cascadeInOn_nonneg (σ : T) : 0 ≤ cascadeInOn dom shrink M σ :=
  tsum_nonneg fun ρ ↦ h.toHalvingLevels.cascadeOut_nonneg ρ.1

/-- **`in = M₀ - out`**: summing the alternating series over the fibre shifts it by one
level. -/
theorem cascadeInOn_eq (σ : T) : cascadeInOn dom shrink M σ = M σ 0 - cascadeOut M σ := by
  set F : {ρ : T // dom ρ ∧ shrink ρ = σ} → ℕ → ℝ := fun ρ k ↦ (-1 : ℝ) ^ k * M ρ.1 k with hF
  have habs : ∀ (ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}) (k : ℕ), |F ρ k| = M ρ.1 k := by
    intro ρ k
    rw [hF]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (h.nonneg _ _)
  have hrow : ∀ ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, Summable fun k ↦ |F ρ k| := by
    intro ρ
    simp only [habs]
    exact h.toHalvingLevels.summable_row ρ.1
  have hcol : Summable fun ρ : {ρ : T // dom ρ ∧ shrink ρ = σ} ↦ ∑' k, |F ρ k| := by
    refine Summable.of_nonneg_of_le (fun ρ ↦ tsum_nonneg fun k ↦ abs_nonneg _)
      (fun ρ ↦ ?_) (((h.fibre σ 0).summable).mul_left 2)
    simp only [habs]
    simpa using h.toHalvingLevels.tsum_shift_le ρ.1 0
  have hsummable : Summable (Function.uncurry F) := by
    refine Summable.of_abs ?_
    refine (summable_prod_of_nonneg (fun p ↦ abs_nonneg _)).mpr ⟨fun ρ ↦ hrow ρ, hcol⟩
  have hswap : ∑' (k : ℕ) (ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}), F ρ k
      = ∑' (ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}) (k : ℕ), F ρ k := hsummable.tsum_comm
  have hinner : ∀ k : ℕ, ∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, F ρ k
      = (-1 : ℝ) ^ k * M σ (k + 1) := by
    intro k
    rw [hF]
    simp only
    rw [tsum_mul_left, (h.fibre σ k).tsum_eq]
  have hleft : ∑' (k : ℕ) (ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}), F ρ k = outFrom M σ 1 := by
    rw [outFrom]
    exact tsum_congr hinner
  have hright : ∑' (ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}) (k : ℕ), F ρ k
      = cascadeInOn dom shrink M σ := by
    rw [cascadeInOn]
    refine tsum_congr fun ρ ↦ ?_
    rw [cascadeOut, outFrom]
    exact tsum_congr fun k ↦ by simp only [hF, Nat.add_zero]
  rw [← hright, ← hswap, hleft]
  have := h.toHalvingLevels.outFrom_rec σ 0
  rw [cascadeOut]
  linarith

/-- **A source atom spends its full mass**: `out(σ) + in(σ) = M₀(σ)`. -/
theorem cascadeOut_add_cascadeInOn (σ : T) :
    cascadeOut M σ + cascadeInOn dom shrink M σ = M σ 0 := by
  rw [h.cascadeInOn_eq σ]; ring

end IsCascadeOn

/-! ### The levels of a partial shrinking -/

/-- **The mass of the iterated fibre**: `cascMassE dom shrink m₀ k σ` is the mass of
`shrink^{-k}(σ)`, defined by the fibre recursion `M_{k+1}(σ) = ∑_{ρ ∈ shrink^{-1}(σ)}M_k(ρ)`
over the fibres of the restriction of `shrink` to `dom`. -/
noncomputable def cascMassE (dom : T → Prop) (shrink : T → T) (m0 : T → ℝ≥0∞) :
    ℕ → T → ℝ≥0∞
  | 0 => m0
  | (k + 1) => fun σ ↦ ∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, cascMassE dom shrink m0 k ρ.1

@[simp] lemma cascMassE_zero (dom : T → Prop) (shrink : T → T) (m0 : T → ℝ≥0∞) :
    cascMassE dom shrink m0 0 = m0 := rfl

lemma cascMassE_succ (dom : T → Prop) (shrink : T → T) (m0 : T → ℝ≥0∞) (k : ℕ) (σ : T) :
    cascMassE dom shrink m0 (k + 1) σ
      = ∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, cascMassE dom shrink m0 k ρ.1 := rfl

variable {m0 : T → ℝ≥0∞}

/-- **`eq:capacity` at every level**, in the extended reals: the capacity bound at the
first level propagates along the fibre recursion. -/
lemma cascMassE_halving
    (hcap : ∀ σ : T, (∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, m0 ρ.1) ≤ m0 σ / 2) :
    ∀ (k : ℕ) (σ : T), cascMassE dom shrink m0 (k + 1) σ
      ≤ cascMassE dom shrink m0 k σ / 2 := by
  intro k
  induction k with
  | zero => exact hcap
  | succ n ih =>
      intro σ
      rw [cascMassE_succ, cascMassE_succ (k := n)]
      calc ∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, cascMassE dom shrink m0 (n + 1) ρ.1
          ≤ ∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, cascMassE dom shrink m0 n ρ.1 / 2 :=
            ENNReal.tsum_le_tsum fun ρ ↦ ih ρ.1
        _ = (∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, cascMassE dom shrink m0 n ρ.1) / 2 := by
            simp only [div_eq_mul_inv]
            exact ENNReal.tsum_mul_right

/-- The levels decrease, so they stay below the mass they start from. -/
lemma cascMassE_le
    (hcap : ∀ σ : T, (∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, m0 ρ.1) ≤ m0 σ / 2) :
    ∀ (k : ℕ) (σ : T), cascMassE dom shrink m0 k σ ≤ m0 σ := by
  intro k
  induction k with
  | zero => intro σ; exact le_rfl
  | succ n ih =>
      intro σ
      refine le_trans (cascMassE_halving hcap n σ) (le_trans ?_ (ih σ))
      exact ENNReal.half_le_self

lemma cascMassE_ne_top (hfin : ∀ σ : T, m0 σ ≠ ⊤)
    (hcap : ∀ σ : T, (∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, m0 ρ.1) ≤ m0 σ / 2)
    (k : ℕ) (σ : T) : cascMassE dom shrink m0 k σ ≠ ⊤ :=
  ne_top_of_le_ne_top (hfin σ) (cascMassE_le hcap k σ)

/-- **The cascade at a partial shrinking**: the iterated-fibre masses of a shrinking map
defined on `dom`, read as real numbers, form a cascade once the masses are finite and the
capacity bound `eq:capacity` holds at the first level. -/
theorem isCascadeOn_cascMass (hfin : ∀ σ : T, m0 σ ≠ ⊤)
    (hcap : ∀ σ : T, (∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, m0 ρ.1) ≤ m0 σ / 2) :
    IsCascadeOn dom shrink (fun σ k ↦ (cascMassE dom shrink m0 k σ).toReal) where
  nonneg := fun _ _ ↦ ENNReal.toReal_nonneg
  fibre := by
    intro σ k
    have hne : (∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ}, cascMassE dom shrink m0 k ρ.1) ≠ ⊤ :=
      (cascMassE_succ dom shrink m0 k σ) ▸ cascMassE_ne_top hfin hcap (k + 1) σ
    have hsum := ENNReal.hasSum_toReal hne
    have heq : ∑' ρ : {ρ : T // dom ρ ∧ shrink ρ = σ},
        (cascMassE dom shrink m0 k ρ.1).toReal
          = (cascMassE dom shrink m0 (k + 1) σ).toReal := by
      rw [cascMassE_succ]
      exact (ENNReal.tsum_toReal_eq
        fun ρ : {ρ : T // dom ρ ∧ shrink ρ = σ} ↦ cascMassE_ne_top hfin hcap k ρ.1).symm
    rwa [heq] at hsum
  capacity := by
    intro σ
    have h := cascMassE_halving hcap 0 σ
    have hle := ENNReal.toReal_mono
      (by simpa using ENNReal.div_ne_top (cascMassE_ne_top hfin hcap 0 σ) two_ne_zero) h
    rwa [ENNReal.toReal_div] at hle

/-! ### The coupling read off the cascade -/

/-- **The cascade pairs**: the pair `(σ, shrink σ)` of a source in the domain carries the
mass `out(σ)`, on either side. -/
noncomputable def cascPair (dm : Shape → Prop) (sh : Shape → Shape) (out₁ out₂ : Shape → ℝ≥0∞)
    (p : Shape × Shape) : ℝ≥0∞ :=
  (if dm p.1 ∧ sh p.1 = p.2 then out₁ p.1 else 0)
    + (if dm p.2 ∧ sh p.2 = p.1 then out₂ p.2 else 0)

/-- **The leftover of a side**: what the cascade does not spend, carried by the atoms
outside the domain. -/
noncomputable def leftover (dm : Shape → Prop) (out : Shape → ℝ≥0∞) (a : Shape) : ℝ≥0∞ :=
  if dm a then 0 else out a

/-- The total leftover of a side. -/
noncomputable def leftoverTot (dm : Shape → Prop) (out : Shape → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a : Shape, leftover dm out a

/-- **The coupling of the cascade**: the cascade pairs together with the normalised product
of the two leftovers, the closure pairs. -/
noncomputable def cascCoupling (dm : Shape → Prop) (sh : Shape → Shape)
    (out₁ out₂ : Shape → ℝ≥0∞) (p : Shape × Shape) : ℝ≥0∞ :=
  cascPair dm sh out₁ out₂ p
    + leftover dm out₁ p.1 * leftover dm out₂ p.2 / leftoverTot dm out₁

section Coupling

variable {dm : Shape → Prop} {sh : Shape → Shape} {out₁ out₂ : Shape → ℝ≥0∞}

/-- A sum over the fibre of the shrinking written as a sum over all shapes. -/
lemma tsum_fibre_eq (f : Shape → ℝ≥0∞) (a : Shape) :
    ∑' b : Shape, (if dm b ∧ sh b = a then f b else 0)
      = ∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, f τ.1 := by
  refine Eq.trans ?_ (tsum_subtype {τ : Shape | dm τ ∧ sh τ = a} f).symm
  refine tsum_congr fun b ↦ ?_
  by_cases hb : dm b ∧ sh b = a
  · rw [if_pos hb, Set.indicator_of_mem (show b ∈ {τ : Shape | dm τ ∧ sh τ = a} from hb) f]
  · rw [if_neg hb, Set.indicator_of_notMem (show b ∉ {τ : Shape | dm τ ∧ sh τ = a} from hb) f]

/-- The mass a source atom sends out, summed over the fibre it is the source of. -/
lemma tsum_cascPair_fst (a : Shape) :
    ∑' b : Shape, cascPair dm sh out₁ out₂ (a, b)
      = (if dm a then out₁ a else 0) + ∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, out₂ τ.1 := by
  simp only [cascPair]
  rw [ENNReal.tsum_add, ← tsum_fibre_eq out₂ a]
  congr 1
  by_cases ha : dm a
  · rw [if_pos ha]
    refine (tsum_eq_single (sh a) fun b hb ↦ ?_).trans ?_
    · exact if_neg fun h ↦ hb h.2.symm
    · exact if_pos ⟨ha, rfl⟩
  · rw [if_neg ha]
    exact (tsum_congr fun b ↦ if_neg fun h ↦ ha h.1).trans tsum_zero

/-- The mirror statement on the second component. -/
lemma tsum_cascPair_snd (b : Shape) :
    ∑' a : Shape, cascPair dm sh out₁ out₂ (a, b)
      = (if dm b then out₂ b else 0) + ∑' τ : {τ : Shape // dm τ ∧ sh τ = b}, out₁ τ.1 := by
  simp only [cascPair]
  rw [ENNReal.tsum_add, ← tsum_fibre_eq out₁ b, add_comm]
  congr 1
  by_cases hb : dm b
  · rw [if_pos hb]
    refine (tsum_eq_single (sh b) fun a ha ↦ ?_).trans ?_
    · exact if_neg fun h ↦ ha h.2.symm
    · exact if_pos ⟨hb, rfl⟩
  · rw [if_neg hb]
    exact (tsum_congr fun a ↦ if_neg fun h ↦ hb h.1).trans tsum_zero

/-- The mass a side carries splits into the part the cascade spends and the leftover. -/
lemma tsum_split_leftover (out : Shape → ℝ≥0∞) :
    ∑' a : Shape, out a
      = (∑' a : Shape, (if dm a then out a else 0)) + leftoverTot dm out := by
  rw [leftoverTot]
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun a ↦ ?_
  rw [leftover]
  by_cases ha : dm a <;> simp [ha]

/-- The mass the cascade spends at the targets of one side is the mass its sources send
out on the other. -/
lemma tsum_tsum_fibre (f : Shape → ℝ≥0∞) :
    ∑' a : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, f τ.1)
      = ∑' b : Shape, (if dm b then f b else 0) := by
  have hswap : ∑' (a : Shape) (b : Shape), (if dm b ∧ sh b = a then f b else 0)
      = ∑' (b : Shape) (a : Shape), (if dm b ∧ sh b = a then f b else 0) := ENNReal.tsum_comm
  calc ∑' a : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, f τ.1)
      = ∑' (a : Shape) (b : Shape), (if dm b ∧ sh b = a then f b else 0) :=
        (tsum_congr fun a ↦ tsum_fibre_eq f a).symm
    _ = ∑' (b : Shape) (a : Shape), (if dm b ∧ sh b = a then f b else 0) := hswap
    _ = ∑' b : Shape, (if dm b then f b else 0) := by
        refine tsum_congr fun b ↦ ?_
        by_cases hb : dm b
        · rw [if_pos hb]
          refine (tsum_eq_single (sh b) fun a ha ↦ ?_).trans ?_
          · exact if_neg fun h ↦ ha h.2.symm
          · exact if_pos ⟨hb, rfl⟩
        · rw [if_neg hb]
          exact (tsum_congr fun a ↦ if_neg fun h ↦ hb h.1).trans tsum_zero

/-- **The coupling read off the cascade**: with the two cascade masses satisfying
`out + in = mass` on either side, the cascade pairs and the normalised product of the two
leftovers form a coupling of the two laws.  It charges only the pairs `(σ, shrink σ)` of a
source in the domain and the pairs of two atoms outside it, and the pair of a source
carries at least the mass the source sends out. -/
theorem exists_coupling_of_out (q₁ q₂ : PMF Shape)
    (hout₁ : ∀ a : Shape, out₁ a + (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, out₂ τ.1) = q₁ a)
    (hout₂ : ∀ b : Shape, out₂ b + (∑' τ : {τ : Shape // dm τ ∧ sh τ = b}, out₁ τ.1) = q₂ b) :
    ∃ π : PMF (Shape × Shape), (∀ a : Shape, margFst π a = q₁ a) ∧
      (∀ b : Shape, margSnd π b = q₂ b) ∧
      (∀ p : Shape × Shape, π p ≠ 0 →
        (dm p.1 ∧ sh p.1 = p.2) ∨ (dm p.2 ∧ sh p.2 = p.1) ∨ (¬ dm p.1 ∧ ¬ dm p.2)) ∧
      (∀ a : Shape, dm a → out₁ a ≤ π (a, sh a)) ∧
      (∀ b : Shape, dm b → out₂ b ≤ π (sh b, b)) := by
  -- the mass each side spends as a source inside the domain
  have htot₁ : (∑' a : Shape, (if dm a then out₁ a else 0)) + leftoverTot dm out₁
      + (∑' b : Shape, (if dm b then out₂ b else 0)) = 1 := by
    rw [← tsum_split_leftover out₁, ← tsum_tsum_fibre out₂, ← ENNReal.tsum_add]
    rw [← q₁.tsum_coe]
    exact tsum_congr hout₁
  have htot₂ : (∑' b : Shape, (if dm b then out₂ b else 0)) + leftoverTot dm out₂
      + (∑' a : Shape, (if dm a then out₁ a else 0)) = 1 := by
    rw [← tsum_split_leftover out₂, ← tsum_tsum_fibre out₁, ← ENNReal.tsum_add]
    rw [← q₂.tsum_coe]
    exact tsum_congr hout₂
  have hSfin : (∑' a : Shape, (if dm a then out₁ a else 0))
      + (∑' b : Shape, (if dm b then out₂ b else 0)) ≠ ⊤ := by
    intro h
    rw [show (∑' a : Shape, (if dm a then out₁ a else 0)) + leftoverTot dm out₁
        + (∑' b : Shape, (if dm b then out₂ b else 0))
        = ((∑' a : Shape, (if dm a then out₁ a else 0))
          + (∑' b : Shape, (if dm b then out₂ b else 0))) + leftoverTot dm out₁ by ring_nf,
      h, top_add] at htot₁
    exact ENNReal.top_ne_one htot₁
  -- the two leftovers have the same total mass
  have hLeq : leftoverTot dm out₁ = leftoverTot dm out₂ := by
    refine (ENNReal.add_left_inj hSfin).mp ?_
    calc leftoverTot dm out₁ + ((∑' a : Shape, (if dm a then out₁ a else 0))
          + (∑' b : Shape, (if dm b then out₂ b else 0)))
        = (∑' a : Shape, (if dm a then out₁ a else 0)) + leftoverTot dm out₁
          + (∑' b : Shape, (if dm b then out₂ b else 0)) := by ring_nf
      _ = 1 := htot₁
      _ = (∑' b : Shape, (if dm b then out₂ b else 0)) + leftoverTot dm out₂
          + (∑' a : Shape, (if dm a then out₁ a else 0)) := htot₂.symm
      _ = leftoverTot dm out₂ + ((∑' a : Shape, (if dm a then out₁ a else 0))
          + (∑' b : Shape, (if dm b then out₂ b else 0))) := by ring_nf
  have hLfin : leftoverTot dm out₁ ≠ ⊤ := by
    intro h
    rw [show (∑' a : Shape, (if dm a then out₁ a else 0)) + leftoverTot dm out₁
        + (∑' b : Shape, (if dm b then out₂ b else 0))
        = leftoverTot dm out₁ + ((∑' a : Shape, (if dm a then out₁ a else 0))
          + (∑' b : Shape, (if dm b then out₂ b else 0))) by ring_nf,
      h, top_add] at htot₁
    exact ENNReal.top_ne_one htot₁
  -- the closure pairs above an atom carry the leftover of that atom
  have hclos₁ : ∀ a : Shape,
      (∑' b : Shape, leftover dm out₁ a * leftover dm out₂ b / leftoverTot dm out₁)
        = leftover dm out₁ a := by
    intro a
    have hstep : (∑' b : Shape, leftover dm out₁ a * leftover dm out₂ b / leftoverTot dm out₁)
        = leftover dm out₁ a * leftoverTot dm out₂ / leftoverTot dm out₁ := by
      simp only [div_eq_mul_inv, mul_assoc]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      rfl
    rw [hstep, ← hLeq]
    by_cases hL : leftoverTot dm out₁ = 0
    · have hz : leftover dm out₁ a = 0 := by
        rw [leftoverTot] at hL
        exact ENNReal.tsum_eq_zero.mp hL a
      rw [hz, zero_mul, ENNReal.zero_div]
    · rw [mul_div_assoc, ENNReal.div_self hL hLfin, mul_one]
  have hclos₂ : ∀ b : Shape,
      (∑' a : Shape, leftover dm out₁ a * leftover dm out₂ b / leftoverTot dm out₁)
        = leftover dm out₂ b := by
    intro b
    have hstep : (∑' a : Shape, leftover dm out₁ a * leftover dm out₂ b / leftoverTot dm out₁)
        = leftoverTot dm out₁ * leftover dm out₂ b / leftoverTot dm out₁ := by
      simp only [div_eq_mul_inv, mul_assoc]
      rw [ENNReal.tsum_mul_right]
      rfl
    rw [hstep]
    by_cases hL : leftoverTot dm out₁ = 0
    · have hz : leftover dm out₂ b = 0 := by
        rw [hLeq, leftoverTot] at hL
        exact ENNReal.tsum_eq_zero.mp hL b
      rw [hz, mul_zero, ENNReal.zero_div]
    · rw [mul_comm, mul_div_assoc, ENNReal.div_self hL hLfin, mul_one]
  -- the two marginals
  have hmarg₁ : ∀ a : Shape, ∑' b : Shape, cascCoupling dm sh out₁ out₂ (a, b) = q₁ a := by
    intro a
    simp only [cascCoupling]
    rw [ENNReal.tsum_add, tsum_cascPair_fst, hclos₁ a, ← hout₁ a, leftover]
    by_cases ha : dm a
    · rw [if_pos ha, if_pos ha, add_zero]
    · rw [if_neg ha, if_neg ha, zero_add, add_comm]
  have hmarg₂ : ∀ b : Shape, ∑' a : Shape, cascCoupling dm sh out₁ out₂ (a, b) = q₂ b := by
    intro b
    simp only [cascCoupling]
    rw [ENNReal.tsum_add, tsum_cascPair_snd, hclos₂ b, ← hout₂ b, leftover]
    by_cases hb : dm b
    · rw [if_pos hb, if_pos hb, add_zero]
    · rw [if_neg hb, if_neg hb, zero_add, add_comm]
  have htotal : ∑' p : Shape × Shape, cascCoupling dm sh out₁ out₂ p = 1 := by
    rw [ENNReal.tsum_prod', ← q₁.tsum_coe]
    exact tsum_congr hmarg₁
  refine ⟨⟨cascCoupling dm sh out₁ out₂, htotal ▸ ENNReal.summable.hasSum⟩, fun a ↦ ?_,
    fun b ↦ ?_, fun p hp ↦ ?_, fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · rw [margFst]
    exact hmarg₁ a
  · rw [margSnd]
    exact hmarg₂ b
  · by_cases h1 : dm p.1 ∧ sh p.1 = p.2
    · exact Or.inl h1
    by_cases h2 : dm p.2 ∧ sh p.2 = p.1
    · exact Or.inr (Or.inl h2)
    have hcp : cascPair dm sh out₁ out₂ p = 0 := by
      rw [cascPair, if_neg h1, if_neg h2, add_zero]
    have hlft : leftover dm out₁ p.1 * leftover dm out₂ p.2 / leftoverTot dm out₁ ≠ 0 := by
      intro h0
      exact hp (show cascCoupling dm sh out₁ out₂ p = 0 by rw [cascCoupling, hcp, h0, zero_add])
    refine Or.inr (Or.inr ⟨fun hd ↦ hlft ?_, fun hd ↦ hlft ?_⟩)
    · rw [show leftover dm out₁ p.1 = 0 by rw [leftover, if_pos hd], zero_mul,
        ENNReal.zero_div]
    · rw [show leftover dm out₂ p.2 = 0 by rw [leftover, if_pos hd], mul_zero,
        ENNReal.zero_div]
  · calc out₁ a = (if dm a ∧ sh a = sh a then out₁ a else 0) := (if_pos ⟨ha, rfl⟩).symm
      _ ≤ cascPair dm sh out₁ out₂ (a, sh a) := le_self_add
      _ ≤ cascCoupling dm sh out₁ out₂ (a, sh a) := le_self_add
  · calc out₂ b = (if dm b ∧ sh b = sh b then out₂ b else 0) := (if_pos ⟨hb, rfl⟩).symm
      _ ≤ cascPair dm sh out₁ out₂ (sh b, b) := le_add_self
      _ ≤ cascCoupling dm sh out₁ out₂ (sh b, b) := le_self_add

/-- The two-sided domain: the shrinking is defined on the atoms in `dm`, on either side. -/
def sideDom (dm : Shape → Prop) (p : Bool × Shape) : Prop := dm p.2

/-- The two-sided shrinking: it carries an atom of one side to an atom of the other. -/
def sideShrink (sh : Shape → Shape) (p : Bool × Shape) : Bool × Shape := (!p.1, sh p.2)

/-- The two-sided mass: the first law on one side, the second on the other. -/
noncomputable def sideMass (q₁ q₂ : PMF Shape) (p : Bool × Shape) : ℝ≥0∞ :=
  if p.1 then q₂ p.2 else q₁ p.2

lemma sideMass_ne_top (q₁ q₂ : PMF Shape) (p : Bool × Shape) : sideMass q₁ q₂ p ≠ ⊤ := by
  rw [sideMass]
  by_cases hp : p.1 = true
  · rw [if_pos hp]; exact PMF.apply_ne_top _ _
  · rw [if_neg hp]; exact PMF.apply_ne_top _ _

@[simp] lemma sideMass_false (q₁ q₂ : PMF Shape) (a : Shape) :
    sideMass q₁ q₂ (false, a) = q₁ a := by
  rw [sideMass]; simp

@[simp] lemma sideMass_true (q₁ q₂ : PMF Shape) (a : Shape) :
    sideMass q₁ q₂ (true, a) = q₂ a := by
  rw [sideMass]; simp

/-- A point of a fibre of the two-sided shrinking sits on the other side. -/
lemma fst_of_mem_sideFibre {sh : Shape → Shape} {i : Bool} {a : Shape}
    {ρ : Bool × Shape} (h : sideShrink sh ρ = (i, a)) : ρ.1 = !i := by
  have h1 : (!ρ.1) = i := congrArg Prod.fst h
  cases hb : ρ.1 <;> cases hi : i <;> simp_all

/-- The fibre of the two-sided shrinking over an atom of one side is the fibre of the
shrinking read on the other side. -/
def sideFibreEquiv (dm : Shape → Prop) (sh : Shape → Shape) (i : Bool) (a : Shape) :
    {τ : Shape // dm τ ∧ sh τ = a}
      ≃ {ρ : Bool × Shape // sideDom dm ρ ∧ sideShrink sh ρ = (i, a)} where
  toFun τ := ⟨(!i, τ.1), τ.2.1, by rw [sideShrink, Bool.not_not, τ.2.2]⟩
  invFun ρ := ⟨ρ.1.2, ρ.2.1, (congrArg Prod.snd ρ.2.2 : sh ρ.1.2 = a)⟩
  left_inv _ := rfl
  right_inv ρ := by
    refine Subtype.ext (Prod.ext_iff.mpr ⟨?_, rfl⟩)
    exact (fst_of_mem_sideFibre ρ.2.2).symm

/-- A sum over the fibre of the two-sided shrinking, read on the other side. -/
lemma tsum_sideFibre (dm : Shape → Prop) (sh : Shape → Shape) (i : Bool) (a : Shape)
    (f : Bool × Shape → ℝ≥0∞) :
    (∑' ρ : {ρ : Bool × Shape // sideDom dm ρ ∧ sideShrink sh ρ = (i, a)}, f ρ.1)
      = ∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, f (!i, τ.1) := by
  refine ((sideFibreEquiv dm sh i a).tsum_eq fun ρ ↦ f ρ.1).symm.trans (tsum_congr fun τ ↦ ?_)
  rfl

/-- **`eq:capacity` on the two sides**: the capacity bound for the two laws is the capacity
bound of the two-sided cascade. -/
lemma capacity_sideMass {q₁ q₂ : PMF Shape} {dm : Shape → Prop} {sh : Shape → Shape}
    (hcap₁ : ∀ a : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = b}, q₁ τ.1) ≤ q₂ b / 2)
    (p : Bool × Shape) :
    (∑' ρ : {ρ : Bool × Shape // sideDom dm ρ ∧ sideShrink sh ρ = p}, sideMass q₁ q₂ ρ.1)
      ≤ sideMass q₁ q₂ p / 2 := by
  obtain ⟨i, a⟩ := p
  rw [tsum_sideFibre dm sh i a (sideMass q₁ q₂)]
  cases i with
  | false =>
      simp only [Bool.not_false, sideMass_true, sideMass_false]
      exact hcap₁ a
  | true =>
      simp only [Bool.not_true, sideMass_true, sideMass_false]
      exact hcap₂ a

/-- The levels of the two-sided cascade. -/
noncomputable def sideLevels (q₁ q₂ : PMF Shape) (dm : Shape → Prop) (sh : Shape → Shape) :
    Bool × Shape → ℕ → ℝ :=
  fun σ k ↦ (cascMassE (sideDom dm) (sideShrink sh) (sideMass q₁ q₂) k σ).toReal

/-- **The mass a side sends out**, the alternating cascade sum at an atom of one side. -/
noncomputable def sideOut (q₁ q₂ : PMF Shape) (dm : Shape → Prop) (sh : Shape → Shape)
    (i : Bool) (a : Shape) : ℝ≥0∞ :=
  ENNReal.ofReal (cascadeOut (sideLevels q₁ q₂ dm sh) (i, a))

/-- **A source atom spends its full mass**, in the form the coupling reads: what an atom
sends out and what the atoms of the other side send into it exhaust its mass. -/
theorem sideOut_add_tsum_sideOut {q₁ q₂ : PMF Shape} {dm : Shape → Prop} {sh : Shape → Shape}
    (hcap₁ : ∀ a : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = b}, q₁ τ.1) ≤ q₂ b / 2)
    (i : Bool) (a : Shape) :
    sideOut q₁ q₂ dm sh i a
        + (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, sideOut q₁ q₂ dm sh (!i) τ.1)
      = sideMass q₁ q₂ (i, a) := by
  have hcasc : IsCascadeOn (sideDom dm) (sideShrink sh) (sideLevels q₁ q₂ dm sh) :=
    isCascadeOn_cascMass (sideMass_ne_top q₁ q₂) (capacity_sideMass hcap₁ hcap₂)
  have hsum := hcasc.cascadeOut_add_cascadeInOn (i, a)
  have hin : ENNReal.ofReal
      (cascadeInOn (sideDom dm) (sideShrink sh) (sideLevels q₁ q₂ dm sh) (i, a))
        = ∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, sideOut q₁ q₂ dm sh (!i) τ.1 := by
    rw [cascadeInOn]
    rw [ENNReal.ofReal_tsum_of_nonneg
      (f := fun ρ : {ρ : Bool × Shape // sideDom dm ρ ∧ sideShrink sh ρ = (i, a)} ↦
        cascadeOut (sideLevels q₁ q₂ dm sh) ρ.1)
      (fun ρ ↦ hcasc.toHalvingLevels.cascadeOut_nonneg ρ.1)
      (hcasc.summable_fibre_cascadeOut (i, a))]
    exact tsum_sideFibre dm sh i a
      (fun ρ ↦ ENNReal.ofReal (cascadeOut (sideLevels q₁ q₂ dm sh) ρ))
  have hzero : sideLevels q₁ q₂ dm sh (i, a) 0 = (sideMass q₁ q₂ (i, a)).toReal := by
    simp only [sideLevels, cascMassE_zero]
  rw [sideOut, ← hin, ← ENNReal.ofReal_add (hcasc.toHalvingLevels.cascadeOut_nonneg (i, a))
    (hcasc.cascadeInOn_nonneg (i, a)), hsum, hzero]
  exact ENNReal.ofReal_toReal (sideMass_ne_top q₁ q₂ (i, a))

/-- **`½M₀ ≤ out` in the form the coupling reads**: what an atom sends out is at least half
its mass. -/
lemma half_le_sideOut {q₁ q₂ : PMF Shape} {dm : Shape → Prop} {sh : Shape → Shape}
    (hcap₁ : ∀ a : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = b}, q₁ τ.1) ≤ q₂ b / 2)
    (i : Bool) (a : Shape) :
    sideMass q₁ q₂ (i, a) / 2 ≤ sideOut q₁ q₂ dm sh i a := by
  have hcasc : IsCascadeOn (sideDom dm) (sideShrink sh) (sideLevels q₁ q₂ dm sh) :=
    isCascadeOn_cascMass (sideMass_ne_top q₁ q₂) (capacity_sideMass hcap₁ hcap₂)
  have hhalf := hcasc.toHalvingLevels.half_le_cascadeOut (i, a)
  have hzero : sideLevels q₁ q₂ dm sh (i, a) 0 = (sideMass q₁ q₂ (i, a)).toReal := by
    simp only [sideLevels, cascMassE_zero]
  rw [hzero] at hhalf
  calc sideMass q₁ q₂ (i, a) / 2
      = ENNReal.ofReal ((sideMass q₁ q₂ (i, a)).toReal / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num),
          ENNReal.ofReal_toReal (sideMass_ne_top q₁ q₂ (i, a))]
        norm_num
    _ ≤ ENNReal.ofReal (cascadeOut (sideLevels q₁ q₂ dm sh) (i, a)) :=
        ENNReal.ofReal_le_ofReal hhalf
    _ = sideOut q₁ q₂ dm sh i a := rfl

/-- **The coupling of two laws with a capacity bound**: the cascade over the two-sided
shrinking, and the coupling read off it.  The two hypotheses are `eq:capacity` for the two
laws, the fibre of a target carrying at most half of its mass.  The pair of a source in
the domain carries at least half the mass of the source, the floor `½M₀ ≤ out` of the
cascade. -/
theorem exists_coupling_of_capacity (q₁ q₂ : PMF Shape) (dm : Shape → Prop) (sh : Shape → Shape)
    (hcap₁ : ∀ a : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : Shape, (∑' τ : {τ : Shape // dm τ ∧ sh τ = b}, q₁ τ.1) ≤ q₂ b / 2) :
    ∃ π : PMF (Shape × Shape), (∀ a : Shape, margFst π a = q₁ a) ∧
      (∀ b : Shape, margSnd π b = q₂ b) ∧
      (∀ p : Shape × Shape, π p ≠ 0 →
        (dm p.1 ∧ sh p.1 = p.2) ∨ (dm p.2 ∧ sh p.2 = p.1) ∨ (¬ dm p.1 ∧ ¬ dm p.2)) ∧
      (∀ a : Shape, dm a → q₁ a / 2 ≤ π (a, sh a)) ∧
      (∀ b : Shape, dm b → q₂ b / 2 ≤ π (sh b, b)) := by
  have hout₁ : ∀ a : Shape, sideOut q₁ q₂ dm sh false a
      + (∑' τ : {τ : Shape // dm τ ∧ sh τ = a}, sideOut q₁ q₂ dm sh true τ.1) = q₁ a := by
    intro a
    have h := sideOut_add_tsum_sideOut hcap₁ hcap₂ false a
    rw [sideMass_false] at h
    simp only [Bool.not_false] at h
    exact h
  have hout₂ : ∀ b : Shape, sideOut q₁ q₂ dm sh true b
      + (∑' τ : {τ : Shape // dm τ ∧ sh τ = b}, sideOut q₁ q₂ dm sh false τ.1) = q₂ b := by
    intro b
    have h := sideOut_add_tsum_sideOut hcap₁ hcap₂ true b
    rw [sideMass_true] at h
    simp only [Bool.not_true] at h
    exact h
  obtain ⟨π, hm₁, hm₂, hsupp, hfl₁, hfl₂⟩ :=
    exists_coupling_of_out (dm := dm) (sh := sh) (out₁ := sideOut q₁ q₂ dm sh false)
      (out₂ := sideOut q₁ q₂ dm sh true) q₁ q₂ hout₁ hout₂
  refine ⟨π, hm₁, hm₂, hsupp, fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · refine le_trans ?_ (hfl₁ a ha)
    have h := half_le_sideOut hcap₁ hcap₂ false a
    rwa [sideMass_false] at h
  · refine le_trans ?_ (hfl₂ b hb)
    have h := half_le_sideOut hcap₁ hcap₂ true b
    rwa [sideMass_true] at h

end Coupling

/-! ### The shrinking as a map -/

/-- **The shrinking of `thm:shape-shrink` (`it:shape-shrink`) as a map**: a choice of
the shape in the support that the shrinking at scale `s` produces. -/
noncomputable def shrinkShape (s : ℕ) (σ : Shape) : Shape :=
  if h : 1 ≤ s then (markedQI_shape_shrink h σ).choose else σ

lemma supported_shrinkShape {s : ℕ} (hs : 1 ≤ s) (σ : Shape) :
    Shape.Supported (shrinkShape s σ) := by
  rw [shrinkShape, dif_pos hs]
  exact (markedQI_shape_shrink hs σ).choose_spec.1

lemma size_shrinkShape_le {s : ℕ} (hs : 1 ≤ s) (σ : Shape) :
    (shrinkShape s σ).size ≤ 16 * (σ.size / s + 1) := by
  rw [shrinkShape, dif_pos hs]
  exact (markedQI_shape_shrink hs σ).choose_spec.2.1

lemma markedQI_shrinkShape {s : ℕ} (hs : 1 ≤ s) (σ : Shape) :
    MarkedQI (2592 * (s : ℝ) ^ 2) (shapeSpace σ) (shapeSpace (shrinkShape s σ)) := by
  rw [shrinkShape, dif_pos hs]
  exact (markedQI_shape_shrink hs σ).choose_spec.2.2

/-! ### `eq:capacity` at the shape laws -/

/-- **`eq:capacity`**: the fibre of a target under the shrinking carries at most half of its
mass.  The fibre sits above the size `max(D², s|τ|/64)`, where the tail bound of
`thm:shape-mass` (`it:shape-mass-tail`) for the source law and the point bound
`thm:shape-mass` (`it:shape-mass-point`) for the target law meet, at the two
largeness conditions `hsmall` and `hlarge`. -/
theorem capacity_of_mass_bounds {q₁ q₂ : PMF Shape} {p c : ℝ} {n₀ s N : ℕ}
    (hs : 1 ≤ s) (hp0 : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c)
    (hpoint : ∀ a : Shape, Shape.Supported a → ENNReal.ofReal (p ^ a.size) ≤ q₁ a)
    (htail : ∀ m : ℕ, n₀ ≤ m →
      (∑' y : Shape, if y.size ≤ m then 0 else q₂ y) ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))))
    (hn₀ : n₀ ≤ N)
    (hsmall : Real.log 2 + 64 * Real.log p⁻¹ ≤ c * (N : ℝ))
    (hlarge : Real.log 2 / 64 + Real.log p⁻¹ ≤ c * (s : ℝ) / 64)
    (a : Shape) :
    (∑' τ : {τ : Shape // N < τ.size ∧ shrinkShape s τ = a}, q₂ τ.1) ≤ q₁ a / 2 := by
  by_cases ha : Shape.Supported a
  swap
  · have hempty : IsEmpty {τ : Shape // N < τ.size ∧ shrinkShape s τ = a} :=
      ⟨fun τ ↦ ha (τ.2.2 ▸ supported_shrinkShape hs τ.1)⟩
    rw [tsum_empty]
    exact zero_le
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hlogp : 0 ≤ Real.log p⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hp0, hp1⟩)
  -- the size threshold of the fibre
  set k : ℕ := a.size with hk
  set j : ℕ := (k - 16) / 16 with hj
  set m : ℕ := max N (s * j - 1) with hm
  have hmN : N ≤ m := le_max_left _ _
  have hmc : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmN
  -- every shape of the fibre is larger than the threshold
  have hfibsize : ∀ τ : Shape, N < τ.size → shrinkShape s τ = a → m < τ.size := by
    intro τ hτ hsh
    have hsize : k ≤ 16 * (τ.size / s + 1) := by
      rw [hk, ← hsh]
      exact size_shrinkShape_le hs τ
    have hdiv : j ≤ τ.size / s := by
      have h1 : k - 16 ≤ 16 * (τ.size / s) := by omega
      have h2 : (k - 16) / 16 ≤ (16 * (τ.size / s)) / 16 := Nat.div_le_div_right h1
      rwa [Nat.mul_div_cancel_left _ (by norm_num : 0 < 16)] at h2
    have hsj : s * j ≤ τ.size :=
      le_trans (Nat.mul_le_mul_left s hdiv)
        (by rw [mul_comm]; exact Nat.div_mul_le_self τ.size s)
    exact max_lt hτ (by omega)
  -- the fibre mass is at most the tail mass above the threshold
  have hfibmass : (∑' τ : {τ : Shape // N < τ.size ∧ shrinkShape s τ = a}, q₂ τ.1)
      ≤ ∑' y : Shape, (if y.size ≤ m then 0 else q₂ y) := by
    refine le_trans (le_of_eq (tsum_subtype {τ : Shape | N < τ.size ∧ shrinkShape s τ = a} _))
      (ENNReal.tsum_le_tsum fun y ↦ ?_)
    by_cases hy : N < y.size ∧ shrinkShape s y = a
    · rw [Set.indicator_of_mem (show y ∈ {τ : Shape | N < τ.size ∧ shrinkShape s τ = a} from hy),
        if_neg (by have := hfibsize y hy.1 hy.2; omega)]
    · rw [Set.indicator_of_notMem
        (show y ∉ {τ : Shape | N < τ.size ∧ shrinkShape s τ = a} from hy)]
      exact zero_le
  -- the scalar comparison of the two bounds
  have hpk : p ^ k = Real.exp (-(Real.log p⁻¹ * (k : ℝ))) := pow_eq_exp_neg_log_inv hp0 k
  have hreal : Real.exp (-c * (m : ℝ)) ≤ p ^ k / 2 := by
    by_cases hkl : (k : ℝ) ≤ 64
    · refine capacity_small (cs := Real.log p⁻¹) (x := (k : ℝ))
        (mfib := Real.exp (-c * (m : ℝ))) (mtau := p ^ k) (y := c * (m : ℝ))
        hlogp hkl (le_of_eq hpk.symm) (le_of_eq (by rw [neg_mul])) ?_
      nlinarith [mul_le_mul_of_nonneg_left hmc hc.le]
    · replace hkl : (64 : ℝ) < (k : ℝ) := not_le.mp hkl
      have h16 : (16 : ℝ) * (j : ℝ) > (k : ℝ) - 32 := by
        have hmod := Nat.div_add_mod (k - 16) 16
        have hlt := Nat.mod_lt (k - 16) (by norm_num : 0 < 16)
        have hk64 : 64 < k := by exact_mod_cast hkl
        have : k - 16 < 16 * j + 16 := by omega
        have hcast : ((k : ℝ) - 16) < 16 * (j : ℝ) + 16 := by
          have h1 : ((k - 16 : ℕ) : ℝ) = (k : ℝ) - 16 := by
            have : 16 ≤ k := by omega
            rw [Nat.cast_sub this]
            norm_num
          have h2 : ((k - 16 : ℕ) : ℝ) < ((16 * j + 16 : ℕ) : ℝ) := by exact_mod_cast this
          rw [h1] at h2
          push_cast at h2
          linarith
        linarith
      have hj1 : 1 ≤ j := by
        have hk64 : 64 < k := by exact_mod_cast hkl
        have : 16 ≤ k - 16 := by omega
        exact Nat.one_le_div_iff (by norm_num) |>.mpr (by omega)
      have hmj : ((s * j - 1 : ℕ) : ℝ) = (s : ℝ) * (j : ℝ) - 1 := by
        have hsj1 : 1 ≤ s * j := Nat.one_le_iff_ne_zero.mpr (by positivity)
        rw [Nat.cast_sub hsj1]
        norm_num
      have hmge : (s : ℝ) * (j : ℝ) - 1 ≤ (m : ℝ) := by
        have : ((s * j - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast le_max_right N (s * j - 1)
        linarith [hmj ▸ this]
      have hkey : (s : ℝ) * (k : ℝ) / 64 ≤ (m : ℝ) := by nlinarith
      refine capacity_large (cs := Real.log p⁻¹) (r := c * (s : ℝ) / 64) (x := (k : ℝ))
        (mfib := Real.exp (-c * (m : ℝ))) (mtau := p ^ k) hkl (le_of_eq hpk.symm) ?_ hlarge
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_le_mul_of_nonneg_left hkey hc.le]
  -- the two bounds meet
  refine le_trans (le_trans hfibmass (htail m (le_trans hn₀ hmN))) ?_
  calc ENNReal.ofReal (Real.exp (-c * (m : ℝ)))
      ≤ ENNReal.ofReal (p ^ k / 2) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (p ^ k) / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
    _ ≤ q₁ a / 2 := by gcongr; exact hpoint a ha

/-- The point bound `thm:shape-mass` (`it:shape-mass-point`) at a constant common to
two laws. -/
lemma ofReal_pow_le_shapePMF (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ shapeWeight θ) (a : Shape)
    (ha : Shape.Supported a) : ENNReal.ofReal (p ^ a.size) ≤ shapePMF θ hq hq0 h2 a := by
  refine le_trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hp0.le hp a.size)) ?_
  exact (ofReal_pow_size_le_shapeMass_of_supported θ hq hq0 h2 ha).trans
    (shapeMass_le_shapePMF θ hq hq0 h2 ha)

/-- **`eq:capacity` at the two shape laws**: past a common threshold on the shrinking scale
and on the size cut, the fibre of a target under the shrinking carries at most half of its
mass, in both directions. -/
theorem exists_capacity_shapePMF (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ s N : ℕ, A ≤ s → A ≤ N →
      (∀ a : Shape,
          (∑' τ : {τ : Shape // N < τ.size ∧ shrinkShape s τ = a}, shapePMF θ' hq' hq0' h2' τ.1)
            ≤ shapePMF θ hq hq0 h2 a / 2) ∧
      (∀ b : Shape,
          (∑' τ : {τ : Shape // N < τ.size ∧ shrinkShape s τ = b}, shapePMF θ hq hq0 h2 τ.1)
            ≤ shapePMF θ' hq' hq0' h2' b / 2) := by
  obtain ⟨c₁, hc₁, n₁, htail₁⟩ := exists_fix_size_tail θ hq hq0 h2
  obtain ⟨c₂, hc₂, n₂, htail₂⟩ := exists_fix_size_tail θ' hq' hq0' h2'
  set c : ℝ := min c₁ c₂ with hcdef
  have hc : 0 < c := lt_min hc₁ hc₂
  set p : ℝ := min (shapeWeight θ) (shapeWeight θ') with hpdef
  have hp0 : 0 < p := lt_min (shapeWeight_pos θ hq hq0 h2) (shapeWeight_pos θ' hq' hq0' h2')
  have hp1 : p ≤ 1 := le_trans (min_le_left _ _) (shapeWeight_le_one θ)
  have hlogp : 0 ≤ Real.log p⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hp0, hp1⟩)
  set X : ℝ := Real.log 2 + 64 * Real.log p⁻¹ with hXdef
  have hX0 : 0 ≤ X := by
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨max (max 1 (max n₁ n₂)) ⌈X / c⌉₊, le_trans (le_max_left 1 _) (le_max_left _ _),
    fun s N hsA hNA ↦ ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_trans (le_max_left 1 _) (le_max_left _ _)) hsA
  have hXs : X ≤ c * (s : ℝ) := by
    have h1 : X / c ≤ (s : ℝ) := by
      refine le_trans (Nat.le_ceil (X / c)) ?_
      exact_mod_cast le_trans (le_max_right (max 1 (max n₁ n₂)) ⌈X / c⌉₊) hsA
    rw [div_le_iff₀ hc] at h1
    linarith
  have hXN : X ≤ c * (N : ℝ) := by
    have h1 : X / c ≤ (N : ℝ) := by
      refine le_trans (Nat.le_ceil (X / c)) ?_
      exact_mod_cast le_trans (le_max_right (max 1 (max n₁ n₂)) ⌈X / c⌉₊) hNA
    rw [div_le_iff₀ hc] at h1
    linarith
  have hsmall : Real.log 2 + 64 * Real.log p⁻¹ ≤ c * (N : ℝ) := hXN
  have hlarge : Real.log 2 / 64 + Real.log p⁻¹ ≤ c * (s : ℝ) / 64 := by
    rw [hXdef] at hXs
    linarith
  -- the tail bounds at the common rate
  have htailE : ∀ (ϑ : Offspring 2) (hϑ : ϑ.extinction < 1) (hϑ0 : 0 < ϑ.extinction)
      (h2ϑ : 0 < ϑ 2) {cϑ : ℝ} {nϑ : ℕ}, 0 < cϑ → c ≤ cϑ →
      (∀ m : ℕ, nϑ ≤ m → ∑' k : ℕ, fixSizeMass ϑ (k + m) ≤ Real.exp (-cϑ * (m : ℝ))) →
      ∀ m : ℕ, nϑ ≤ m →
        (∑' y : Shape, if y.size ≤ m then 0 else shapePMF ϑ hϑ hϑ0 h2ϑ y)
          ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))) := by
    intro ϑ hϑ hϑ0 h2ϑ cϑ nϑ hcϑ hle htail m hm
    refine le_trans (tsum_shapePMF_large_le ϑ hϑ hϑ0 h2ϑ hcϑ htail hm) ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hn₁ : n₁ ≤ N := le_trans (le_trans (le_trans (le_max_left n₁ n₂) (le_max_right 1 _))
    (le_max_left _ _)) hNA
  have hn₂ : n₂ ≤ N := le_trans (le_trans (le_trans (le_max_right n₁ n₂) (le_max_right 1 _))
    (le_max_left _ _)) hNA
  constructor
  · refine capacity_of_mass_bounds hs1 hp0 hp1 hc
      (fun a ha ↦ ofReal_pow_le_shapePMF θ hq hq0 h2 hp0 (min_le_left _ _) a ha)
      (fun m hm ↦ htailE θ' hq' hq0' h2' hc₂ (min_le_right _ _) htail₂ m hm) hn₂ hsmall hlarge
  · refine capacity_of_mass_bounds hs1 hp0 hp1 hc
      (fun a ha ↦ ofReal_pow_le_shapePMF θ' hq' hq0' h2' hp0 (min_le_right _ _) a ha)
      (fun m hm ↦ htailE θ hq hq0 h2 hc₁ (min_le_left _ _) htail₁ m hm) hn₁ hsmall hlarge

/-! ### `thm:shape-coupling` -/

/-- **A cascade pair is comparable**: a shape and its shrinking are `9D³`-comparable both
ways, the shrinking being `D`-marked and its quasi-inverse `3D²`-marked. -/
lemma markedQI_shrinkShape_pair {D s : ℕ} (hD : 1 ≤ D) (hs : 1 ≤ s)
    (hsD : 2592 * (s : ℝ) ^ 2 ≤ (D : ℝ)) (σ : Shape) :
    MarkedQI (9 * (D : ℝ) ^ 3) (shapeSpace σ) (shapeSpace (shrinkShape s σ)) ∧
      MarkedQI (9 * (D : ℝ) ^ 3) (shapeSpace (shrinkShape s σ)) (shapeSpace σ) := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hfwd : MarkedQI (D : ℝ) (shapeSpace σ) (shapeSpace (shrinkShape s σ)) :=
    (markedQI_shrinkShape hs σ).mono (by positivity) hsD
  have hback := markedQI_symm hDR hfwd
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := le_trans zero_le_one hDR
  have hsq : (1 : ℝ) ≤ (D : ℝ) ^ 2 := one_le_pow₀ hDR
  have hcube : (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 3 := by nlinarith
  refine ⟨hfwd.mono hD0 (by nlinarith), hback.mono (by nlinarith) (by nlinarith)⟩

/-- **The cascade data of the coupling**, in the form the potential estimate of
`thm:shape-coupling` (`it:shape-coupling-eta`) consumes: a charged pair is the
cascade pair of a tail source on either side or a pair of two small shapes, and the
cascade pair of a tail source carries at least half the mass of its source. -/
structure IsCascadePairing (N : ℕ) (sh : Shape → Shape) (q₁ q₂ : PMF Shape)
    (π : PMF (Shape × Shape)) : Prop where
  /-- A charged pair is a cascade pair or a pair of two small shapes. -/
  supp : ∀ p : Shape × Shape, π p ≠ 0 →
    (N < p.1.size ∧ sh p.1 = p.2) ∨ (N < p.2.size ∧ sh p.2 = p.1) ∨
      (p.1.size ≤ N ∧ p.2.size ≤ N)
  /-- The cascade pair of a tail source of the first law carries half its mass. -/
  floor₁ : ∀ a : Shape, N < a.size → q₁ a / 2 ≤ π (a, sh a)
  /-- The cascade pair of a tail source of the second law carries half its mass. -/
  floor₂ : ∀ b : Shape, N < b.size → q₂ b / 2 ≤ π (sh b, b)

/-- **`thm:shape-coupling`, the coupling**: at a shrinking scale where the capacity bound
holds, the cascade coupling of two laws is supported on `9D³`-comparable pairs, the small
shapes being pairwise comparable and a cascade pair comparable through the shrinking, and
it carries the cascade data. -/
theorem exists_isShapeCoupling_of_capacity {D s : ℕ} (hD : 1 ≤ D) (hs : 1 ≤ s)
    (hsD : 2592 * (s : ℝ) ^ 2 ≤ (D : ℝ)) {q₁ q₂ : PMF Shape}
    (hcap₁ : ∀ a : Shape,
      (∑' τ : {τ : Shape // D ^ 2 < τ.size ∧ shrinkShape s τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : Shape,
      (∑' τ : {τ : Shape // D ^ 2 < τ.size ∧ shrinkShape s τ = b}, q₁ τ.1) ≤ q₂ b / 2) :
    ∃ π : PMF (Shape × Shape), IsShapeCoupling (D : ℝ) q₁ q₂ π ∧
      IsCascadePairing (D ^ 2) (shrinkShape s) q₁ q₂ π := by
  obtain ⟨π, hm₁, hm₂, hsupp, hfl₁, hfl₂⟩ := exists_coupling_of_capacity q₁ q₂
    (fun σ ↦ D ^ 2 < σ.size) (shrinkShape s) hcap₁ hcap₂
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hsize : ∀ a : Shape, ¬ (D ^ 2 < a.size) → (a.size : ℝ) ≤ (D : ℝ) * (D : ℝ) := by
    intro a ha
    have h : a.size ≤ D ^ 2 := by omega
    have h' : (a.size : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    calc (a.size : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := h'
      _ = (D : ℝ) * (D : ℝ) := by push_cast; ring
  refine ⟨π, ⟨hm₁, hm₂, fun p hp ↦ ?_, fun p hp ↦ ?_⟩, ⟨fun p hp ↦ ?_, hfl₁, hfl₂⟩⟩
  · rcases hsupp p hp with ⟨_, hsh⟩ | ⟨_, hsh⟩ | ⟨h1, h2⟩
    · rw [← hsh]
      exact (markedQI_shrinkShape_pair hD hs hsD p.1).1
    · rw [← hsh]
      exact (markedQI_shrinkShape_pair hD hs hsD p.2).2
    · exact markedQI_small_pair hDR (hsize p.1 h1) (hsize p.2 h2)
  · rcases hsupp p hp with ⟨_, hsh⟩ | ⟨_, hsh⟩ | ⟨h1, h2⟩
    · rw [← hsh]
      exact (markedQI_shrinkShape_pair hD hs hsD p.1).2
    · rw [← hsh]
      exact (markedQI_shrinkShape_pair hD hs hsD p.2).1
    · exact markedQI_small_pair hDR (hsize p.2 h2) (hsize p.1 h1)
  · rcases hsupp p hp with ⟨h1, hsh⟩ | ⟨h2, hsh⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, hsh⟩
    · exact Or.inr (Or.inl ⟨h2, hsh⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- **`thm:shape-coupling`**: the two shape laws admit a coupling supported on
`9D³`-comparable pairs at every scale past a largeness condition on the two laws, the
shrinking being taken at `s = ⌊√(D/2592)⌋`. -/
theorem exists_isShapeCoupling (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) :
    ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → ∃ π : PMF (Shape × Shape),
      IsShapeCoupling (D : ℝ) (shapePMF θ hq hq0 h2) (shapePMF θ' hq' hq0' h2') π := by
  obtain ⟨A, hA1, hA⟩ := exists_capacity_shapePMF θ θ' hq hq0 h2 hq' hq0' h2'
  refine ⟨max 30 (2592 * (A * A) + A), fun D hD ↦ ?_⟩
  have hD30 : 30 ≤ D := le_trans (le_max_left _ _) hD
  have hDA : 2592 * (A * A) + A ≤ D := le_trans (le_max_right _ _) hD
  have hD1 : 1 ≤ D := by omega
  -- the shrinking scale
  have hsqrt : A * A ≤ D / 2592 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hsA : A ≤ Nat.sqrt (D / 2592) := by
    have h := Nat.sqrt_le_sqrt hsqrt
    rwa [Nat.sqrt_eq] at h
  have hs1 : 1 ≤ Nat.sqrt (D / 2592) := le_trans hA1 hsA
  have hsD : 2592 * ((Nat.sqrt (D / 2592) : ℕ) : ℝ) ^ 2 ≤ (D : ℝ) := by
    have h1 : 2592 * (Nat.sqrt (D / 2592) ^ 2) ≤ D := by
      calc 2592 * (Nat.sqrt (D / 2592) ^ 2) ≤ 2592 * (D / 2592) :=
            Nat.mul_le_mul_left _ (Nat.sqrt_le' _)
        _ = D / 2592 * 2592 := by ring
        _ ≤ D := Nat.div_mul_le_self _ _
    have h2 : ((2592 * (Nat.sqrt (D / 2592) ^ 2) : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hND : A ≤ D ^ 2 := by nlinarith [hDA, hA1]
  obtain ⟨hcap₁, hcap₂⟩ := hA (Nat.sqrt (D / 2592)) (D ^ 2) hsA hND
  obtain ⟨π, hπ, -⟩ := exists_isShapeCoupling_of_capacity hD1 hs1 hsD hcap₁ hcap₂
  exact ⟨π, hπ⟩

/-! ### `thm:hairy` across two laws -/

/-- **`thm:hairy` across two laws, over the couplings at large scales**: the scale at which
the coupling is taken is chosen along with the scale of `def:shape-net`, so a coupling past
a threshold is all the assembly asks for. -/
theorem hairy_ae_shape_tree_cross_large (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2)
    (hcoup : ∃ D₂ : ℕ, ∀ D : ℕ, D₂ ≤ D → ∃ π : PMF (Shape × Shape),
      IsShapeCoupling (D : ℝ) (shapePMF θ hq hq0 h2) (shapePMF θ' hq' hq0' h2') π) :
    twoHairyMeasure θ θ'
      {ω | ¬ ∃ (L : ℝ) (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}),
        IsSampleQI L F} = 0 := by
  obtain ⟨D₂, hcoup⟩ := hcoup
  refine hairy_ae_tree θ θ' fun ε hε ↦ ?_
  obtain ⟨D₀, hD₀⟩ := exists_etaG_shapeNet_small θ hq hq0 h2
  by_cases htop : ε = ⊤
  · exact ⟨0, htop ▸ le_top⟩
  · have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    obtain ⟨D₁, hD₁⟩ :=
      exists_etaG_shapeNet_le_ofReal θ hq hq0 h2 (r := ε.toReal / 16) (by positivity)
    set D : ℕ := max (max 30 D₀) (max D₁ D₂) with hDdef
    have h30 : 30 ≤ D := le_trans (le_max_left 30 D₀) (le_max_left _ _)
    have hDD₀ : D₀ ≤ D := le_trans (le_max_right 30 D₀) (le_max_left _ _)
    have hDD₁ : D₁ ≤ D := le_trans (le_max_left D₁ D₂) (le_max_right _ _)
    have hDD₂ : D₂ ≤ D := le_trans (le_max_right D₁ D₂) (le_max_right _ _)
    obtain ⟨π, hπ⟩ := hcoup D hDD₂
    obtain ⟨hDR, hle⟩ := hD₁ D hDD₁
    have h16 : (16 : ℝ≥0∞) * ENNReal.ofReal (ε.toReal / 16) = ε := by
      have hofn : ENNReal.ofReal (16 : ℝ) = (16 : ℝ≥0∞) := by simp
      rw [← hofn, ← ENNReal.ofReal_mul (by norm_num),
        show (16 : ℝ) * (ε.toReal / 16) = ε.toReal by ring]
      exact ENNReal.ofReal_toReal htop
    refine ⟨8 * 19683 ^ 2 * (D : ℝ) ^ 14, le_trans
      (hairy_rate_shape_tree_cross θ θ' hq hq0 h2 hq' hq0' h2' h30 hπ (hD₀ D hDD₀)) ?_⟩
    calc (16 : ℝ≥0∞) * etaG (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ))
        ≤ 16 * ENNReal.ofReal (ε.toReal / 16) := by gcongr
      _ = ε := h16

/-- **`thm:hairy` across two laws**: two independent samples of two supercritical offspring
laws on `{0,1,2}` with `θ₀,θ₀'>0` are almost surely quasi-isometric, with no hypothesis
left: the coupling of `thm:shape-coupling` is built by the cascade over the shrinking. -/
theorem hairy_ae_shape_tree_two_law (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) :
    twoHairyMeasure θ θ'
      {ω | ¬ ∃ (L : ℝ) (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}),
        IsSampleQI L F} = 0 :=
  hairy_ae_shape_tree_cross_large θ θ' hq hq0 h2 hq' hq0' h2'
    (exists_isShapeCoupling θ θ' hq hq0 h2 hq' hq0' h2')

end ChainClasses
