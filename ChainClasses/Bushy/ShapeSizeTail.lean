import ChainClasses.Bushy.ShapeMassBush
import ChainClasses.Shape.ShapeShrink

/-!
`sec:shape-harris` of `matching_classes_simple.tex`:
**`thm:shape-mass` (`it:shape-mass-tail`)** at the shape law itself.

`ShapeMassBush` carries the tail of a single bush.  The shape law is a product over the
decorations, so the size moment factorises: a shape is a finite tuple of decorations, the
mass of a shape is one factor per decoration and the split weight at the end, and the size
is the neck length plus the sizes of the decorations.  Summing over the tuples turns the
moment into a geometric series in the neck length whose ratio is the decoration moment
`A(s) = s(θ₁ + 2θ₀ 𝔼 s^{|T|})`.  At `s = 1` that ratio is the skeleton mean
`θ̃₁ = θ₁ + 2θ₀ < 1`, and the progeny equation of `BranchingProcess.Progeny` bounds the bush
moment by the fixed point `y`, so `y = 1 + ε` with `ε` small against `(1 - θ̃₁)/θ₀` keeps the
ratio below one at an `s > 1` written out.  A finite moment above one is then the input
`chernoff_tail` takes, and `shape_mass_tail` absorbs the moment constant past a threshold.

* `shapeSigmaEquiv`, `tsum_shape_prod`: **the shapes as tuples of decorations**, and the
  sum of a product of decoration weights over the shapes as a geometric series.
* `decWeight`, `decMoment`, `shapeMass_mul_pow`, `tsum_shapeMass_mul_pow`: **the size
  moment of the shape law**, summed to `θ̃₂ s (1 - A(s))⁻¹`.
* `tsum_option_ennreal`, `tsum_pow_size_bushTri`, `decMoment_eq`, `decMoment_le`: **the
  decoration moment**, the bare decoration split off and the bushes read against the size
  moment of a bush.
* `tsum_shapeMass_mul_pow_lt_top`: **the size moment is finite** at a fixed point of the
  progeny equation keeping the ratio below one.
* `gen_conjugate_eq`, `skeleton_mean_lt_one`, `exists_shape_size_moment`: **the conjugate
  law written out**, its weights being `(θ₂, θ₁, θ₀)`, and the choice of `s > 1`.
* `shapeStatMassE`, `shapeStatMass`, `tsum_pow_shapeStatMassE`,
  `summable_shapeStatMass_mgf`: **the law of a size statistic of the shape** and its
  moment as the real series `chernoff_tail` consumes.
* `shapeSizeMass`, `exists_shape_stat_tail`, `exists_shape_size_tail`:
  **`thm:shape-mass` (`it:shape-mass-tail`)**, the exponential tail of the size of
  a shape.
* `fixSizeMass`, `exists_fix_size_tail`: the same for the support fix of
  `thm:shape-shrink` (`it:shape-fix`), whose size at most doubles, so the rate
  halves.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (sample Survives survivalMeasure bushMeasure Offspring)
open scoped ENNReal

/-! ### Shapes as tuples of decorations -/

/-- A shape is a neck length together with that many decorations. -/
def shapeSigmaEquiv : Shape ≃ Σ n : ℕ, Fin n → Option Tri where
  toFun σ := ⟨σ.necks, σ.dec⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Summing a product of decoration weights over the shapes**: a shape is a finite
tuple of decorations, so the sum factorises into a geometric series in the length. -/
lemma tsum_shape_prod (G : Option Tri → ℝ≥0∞) :
    ∑' σ : Shape, ∏ i, G (σ.dec i) = ∑' n : ℕ, (∑' d : Option Tri, G d) ^ n := by
  have h1 : ∑' σ : Shape, ∏ i, G (σ.dec i)
      = ∑' p : Σ n : ℕ, Fin n → Option Tri, ∏ i, G (p.2 i) :=
    (Equiv.tsum_eq shapeSigmaEquiv.symm fun σ : Shape ↦ ∏ i, G (σ.dec i)).symm
  rw [h1, ENNReal.tsum_sigma']
  refine tsum_congr fun n ↦ ?_
  rw [tsum_pi_fin n fun _ a ↦ G a, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The size moment of the shape law -/

variable (θ : Offspring 2)

/-- The weight of a decoration in the size moment: its mass against a power of `s` for
its own vertices and for the neck vertex carrying it. -/
noncomputable def decWeight (s : ℝ≥0∞) (d : Option Tri) : ℝ≥0∞ :=
  decMass θ d * s ^ (Tri.optSize d + 1)

/-- **The size moment of one decoration**, the ratio of the geometric series the size
moment of a shape sums to. -/
noncomputable def decMoment (s : ℝ≥0∞) : ℝ≥0∞ := ∑' d : Option Tri, decWeight θ s d

/-- The mass of a shape against a power of its size, one factor per neck vertex and the
split weight at the end. -/
lemma shapeMass_mul_pow (s : ℝ≥0∞) (σ : Shape) :
    shapeMass θ σ * s ^ σ.size
      = ENNReal.ofReal (θ.skeletonWeight 2) * s * ∏ i, decWeight θ s (σ.dec i) := by
  have hprod : (σ.decs.map (decMass θ)).prod = ∏ i, decMass θ (σ.dec i) := by
    rw [Shape.decs, List.map_ofFn, List.prod_ofFn]
    rfl
  have hsum : (σ.decs.map Tri.optSize).sum = ∑ i, Tri.optSize (σ.dec i) := by
    rw [Shape.decs, List.map_ofFn, List.sum_ofFn]
    rfl
  have hsize : σ.size = (∑ i, (Tri.optSize (σ.dec i) + 1)) + 1 := by
    rw [Shape.size_eq', Shape.neckLen, hsum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  have hpow : ∏ i, s ^ (Tri.optSize (σ.dec i) + 1)
      = s ^ (∑ i, (Tri.optSize (σ.dec i) + 1)) := Finset.prod_pow_eq_pow_sum _ _ _
  simp only [decWeight, Finset.prod_mul_distrib, hpow]
  rw [shapeMass, hprod, hsize, pow_succ]
  generalize (∑ i, (Tri.optSize (σ.dec i) + 1)) = S
  ring

/-- **The size moment of the shape law**: the moment is a geometric series in the neck
length with the decoration moment as its ratio. -/
theorem tsum_shapeMass_mul_pow (s : ℝ≥0∞) :
    ∑' σ : Shape, shapeMass θ σ * s ^ σ.size
      = ENNReal.ofReal (θ.skeletonWeight 2) * s * (1 - decMoment θ s)⁻¹ := by
  simp only [shapeMass_mul_pow θ s]
  rw [ENNReal.tsum_mul_left, tsum_shape_prod, ENNReal.tsum_geometric]
  rfl

/-! ### The decoration moment against the bush law -/

/-- Summing over the decorations splits off the bare one. -/
lemma tsum_option_ennreal {α : Type} (G : Option α → ℝ≥0∞) :
    ∑' d : Option α, G d = G none + ∑' t : α, G (some t) := by
  have he : ∑' d : Option α, G d
      = ∑' x : α ⊕ Unit, G ((Equiv.optionEquivSumPUnit.{0, 0} α).symm x) :=
    (Equiv.tsum_eq (Equiv.optionEquivSumPUnit.{0, 0} α).symm G).symm
  rw [he, Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
  congr 1
  exact tsum_eq_single () fun b hb ↦ absurd (Subsingleton.elim b ()) hb

/-- **The size moment of a bush read over the trees**: the fibres of the bush partition
the sample space, and on almost every field the bush has as many vertices as the
sample. -/
lemma tsum_pow_size_bushTri (s : ℝ≥0∞) :
    ∑' t : Tri, s ^ t.size * bushMeasure (N := 2) θ {d : Amb → ℕ | bushTri d = t}
      = ∫⁻ d, s ^ ((sample d : Set Amb).ncard) ∂(bushMeasure (N := 2) θ) := by
  have hmeas : ∀ t : Tri, AEMeasurable
      (fun d : Amb → ℕ ↦ Set.indicator {d : Amb → ℕ | bushTri d = t}
        (fun _ ↦ s ^ t.size) d) (bushMeasure (N := 2) θ) :=
    fun t ↦ (measurable_const.indicator (measurableSet_bushTri_eq t)).aemeasurable
  have hpt : ∀ d : Amb → ℕ,
      ∑' t : Tri, Set.indicator {d : Amb → ℕ | bushTri d = t} (fun _ ↦ s ^ t.size) d
        = s ^ ((bushTri d).size) := by
    intro d
    refine (tsum_eq_single (bushTri d) fun t ht ↦ ?_).trans ?_
    · have hnot : d ∉ {d' : Amb → ℕ | bushTri d' = t} := fun h ↦ ht (h : bushTri d = t).symm
      exact Set.indicator_of_notMem hnot _
    · have hmem : d ∈ {d' : Amb → ℕ | bushTri d' = bushTri d} := rfl
      exact Set.indicator_of_mem hmem _
  have hae : ∫⁻ d, s ^ ((bushTri d).size) ∂(bushMeasure (N := 2) θ)
      = ∫⁻ d, s ^ ((sample d : Set Amb).ncard) ∂(bushMeasure (N := 2) θ) := by
    refine lintegral_congr_ae ?_
    have h1 : ∀ᵐ c ∂(bushMeasure (N := 2) θ), ∀ v, c v ≤ 2 :=
      ae_iff.mpr (bushMeasure_offspring_le θ)
    have h2 : ∀ᵐ c ∂(bushMeasure (N := 2) θ), ¬ Survives c := by
      rw [ae_iff]
      have hset : {c : Amb → ℕ | ¬ ¬ Survives c} = {c : Amb → ℕ | Survives c} := by
        ext c
        simp
      rw [hset]
      exact bushMeasure_survives θ
    filter_upwards [h1, h2] with c hc1 hc2
    rw [size_bushTri hc1 hc2]
  calc ∑' t : Tri, s ^ t.size * bushMeasure (N := 2) θ {d : Amb → ℕ | bushTri d = t}
      = ∑' t : Tri, ∫⁻ d, Set.indicator {d : Amb → ℕ | bushTri d = t}
          (fun _ ↦ s ^ t.size) d ∂(bushMeasure (N := 2) θ) :=
        tsum_congr fun t ↦ (lintegral_indicator_const (measurableSet_bushTri_eq t) _).symm
    _ = ∫⁻ d, ∑' t : Tri, Set.indicator {d : Amb → ℕ | bushTri d = t}
          (fun _ ↦ s ^ t.size) d ∂(bushMeasure (N := 2) θ) := (lintegral_tsum hmeas).symm
    _ = ∫⁻ d, s ^ ((bushTri d).size) ∂(bushMeasure (N := 2) θ) := lintegral_congr hpt
    _ = ∫⁻ d, s ^ ((sample d : Set Amb).ncard) ∂(bushMeasure (N := 2) θ) := hae

/-- **The decoration moment**: `θ₁` for the bare decoration and the decoration weight
against the size moment of a bush for the others, each carrying one power of `s` for the
neck vertex. -/
lemma decMoment_eq (s : ℝ≥0∞) :
    decMoment θ s = ENNReal.ofReal (θ 1) * s
      + ENNReal.ofReal (θ 2 * 2 * θ.extinction) * s
        * ∫⁻ d, s ^ ((sample d : Set Amb).ncard) ∂(bushMeasure (N := 2) θ) := by
  rw [decMoment, tsum_option_ennreal]
  congr 1
  · rw [decWeight, decMass, Tri.optSize_none, pow_one]
  · rw [← tsum_pow_size_bushTri θ s, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun t ↦ ?_
    rw [decWeight, decMass, Tri.optSize_some, pow_succ]
    ring

/-- **The decoration moment at a fixed point of the progeny equation**: the bush moment is
bounded by the fixed point `y`, so the ratio of the geometric series is at most
`s(θ₁ + 2θ₀y)`. -/
lemma decMoment_le (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) {s y : ℝ}
    (hs : 1 ≤ s) (hy : 1 ≤ y) (hfix : s * Offspring.gen (θ.conjugate hq0) y = y) :
    decMoment θ (ENNReal.ofReal s) ≤ ENNReal.ofReal (s * (θ 1 + 2 * θ 0 * y)) := by
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hy0 : (0 : ℝ) ≤ y := le_trans zero_le_one hy
  have h0 : (0 : ℝ) ≤ θ 0 := θ.nonneg 0
  have h1 : (0 : ℝ) ≤ θ 1 := θ.nonneg 1
  have hI : ∫⁻ d, ENNReal.ofReal s ^ ((sample d : Set Amb).ncard)
      ∂(bushMeasure (N := 2) θ) ≤ ENNReal.ofReal y :=
    BranchingProcess.lintegral_pow_ncard_bushMeasure_le (N := 2) θ le_rfl hq0 hs hy hfix
  rw [decMoment_eq θ (ENNReal.ofReal s), decoration_weight_eq θ hq]
  calc ENNReal.ofReal (θ 1) * ENNReal.ofReal s
        + ENNReal.ofReal (2 * θ 0) * ENNReal.ofReal s
          * ∫⁻ d, ENNReal.ofReal s ^ ((sample d : Set Amb).ncard) ∂(bushMeasure (N := 2) θ)
      ≤ ENNReal.ofReal (θ 1) * ENNReal.ofReal s
        + ENNReal.ofReal (2 * θ 0) * ENNReal.ofReal s * ENNReal.ofReal y := by gcongr
    _ = ENNReal.ofReal (s * (θ 1 + 2 * θ 0 * y)) := by
        rw [← ENNReal.ofReal_mul h1,
          ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) h0),
          ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) h0) hs0),
          ← ENNReal.ofReal_add (mul_nonneg h1 hs0)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h0) hs0) hy0)]
        congr 1
        ring

/-! ### The size moment is finite above one -/

/-- **The size moment of the shape law is finite** once the geometric series converges:
the ratio is bounded by `s(θ₁ + 2θ₀y)`, and below one that is a finite sum. -/
theorem tsum_shapeMass_mul_pow_lt_top (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    {s y : ℝ} (hs : 1 ≤ s) (hy : 1 ≤ y)
    (hfix : s * Offspring.gen (θ.conjugate hq0) y = y)
    (hlt : s * (θ 1 + 2 * θ 0 * y) < 1) :
    ∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal s ^ σ.size < ⊤ := by
  have hA : decMoment θ (ENNReal.ofReal s) < 1 :=
    lt_of_le_of_lt (decMoment_le θ hq hq0 hs hy hfix) (ENNReal.ofReal_lt_one.mpr hlt)
  rw [tsum_shapeMass_mul_pow]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ?_
  exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hA)

/-! ### The conjugate law written out -/

/-- **The generating function of the conjugate law** of a law on `{0,1,2}`: the weights
are `(θ₂, θ₁, θ₀)`, since `θ₂q = θ₀`. -/
lemma gen_conjugate_eq (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (y : ℝ) :
    Offspring.gen (θ.conjugate hq0) y = θ 2 + θ 1 * y + θ 0 * y ^ 2 := by
  have hq0' : θ.extinction ≠ 0 := hq0.ne'
  have hkey := mul_extinction_eq θ hq
  rw [gen_eq_of_two]
  simp only [Offspring.conjugate_apply, Offspring.conjugateWeight]
  have e0 : θ 0 * θ.extinction ^ 0 / θ.extinction = θ 2 := by
    rw [pow_zero, mul_one, ← hkey, mul_div_assoc, div_self hq0', mul_one]
  have e1 : θ 1 * θ.extinction ^ 1 / θ.extinction = θ 1 := by
    rw [pow_one, mul_div_assoc, div_self hq0', mul_one]
  have e2 : θ 2 * θ.extinction ^ 2 / θ.extinction = θ 0 := by
    rw [pow_two, ← mul_assoc, hkey, mul_div_assoc, div_self hq0', mul_one]
  rw [e0, e1, e2]

/-- **The skeleton is subcritical**: the mean `θ̃₁ = θ₁ + 2θ₀` of the conjugate law is
below one, because `θ₀ = θ₂q < θ₂`. -/
lemma skeleton_mean_lt_one (hq : θ.extinction < 1) (h2 : 0 < θ 2) :
    θ 1 + 2 * θ 0 < 1 := by
  have hkey := mul_extinction_eq θ hq
  have htot := total_of_two θ
  have hlt : θ 0 < θ 2 := by
    rw [← hkey]
    nlinarith
  linarith

/-- **The size of a shape has an exponential moment**: at `y = 1 + ε` the progeny equation
is solved by `s` the ratio of `y` to the generating function of the conjugate law, and `ε`
small against `(1 - θ̃₁)/θ₀` keeps the ratio of the geometric series below one. -/
theorem exists_shape_size_moment (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) :
    ∃ s : ℝ, 1 < s ∧ ∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal s ^ σ.size < ⊤ := by
  have hkey := mul_extinction_eq θ hq
  have htot := total_of_two θ
  have h0 : 0 < θ 0 := by
    rw [← hkey]
    exact mul_pos h2 hq0
  have hm : θ 1 + 2 * θ 0 < 1 := skeleton_mean_lt_one θ hq h2
  obtain ⟨ε, hε0, hε1, hεb⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ θ 0 * ε ≤ (1 - (θ 1 + 2 * θ 0)) / 6 := by
    refine ⟨min 1 ((1 - (θ 1 + 2 * θ 0)) / (6 * θ 0)), lt_min zero_lt_one (by positivity),
      min_le_left _ _, ?_⟩
    have hle : min 1 ((1 - (θ 1 + 2 * θ 0)) / (6 * θ 0))
        ≤ (1 - (θ 1 + 2 * θ 0)) / (6 * θ 0) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at hle
    linarith
  have hsq : θ 0 * ε ^ 2 ≤ θ 0 * ε := by
    have h := mul_le_mul_of_nonneg_left hε1 (mul_nonneg h0.le hε0.le)
    calc θ 0 * ε ^ 2 = θ 0 * ε * ε := by ring
      _ ≤ θ 0 * ε * 1 := h
      _ = θ 0 * ε := by ring
  have hsmall : θ 1 + 2 * θ 0 + 2 * (θ 0 * ε) + θ 0 * ε ^ 2 < 1 := by linarith
  have hgpos : (0 : ℝ) < 1 + ε * (θ 1 + 2 * θ 0) + θ 0 * ε ^ 2 := by nlinarith [θ.nonneg 1]
  have hgen : Offspring.gen (θ.conjugate hq0) (1 + ε)
      = 1 + ε * (θ 1 + 2 * θ 0) + θ 0 * ε ^ 2 := by
    rw [gen_conjugate_eq θ hq hq0]
    linear_combination htot
  have hylt : 1 + ε * (θ 1 + 2 * θ 0) + θ 0 * ε ^ 2 < 1 + ε := by nlinarith
  refine ⟨(1 + ε) / (1 + ε * (θ 1 + 2 * θ 0) + θ 0 * ε ^ 2), (one_lt_div hgpos).mpr hylt, ?_⟩
  refine tsum_shapeMass_mul_pow_lt_top θ hq hq0 ((one_lt_div hgpos).mpr hylt).le
    (by linarith : (1 : ℝ) ≤ 1 + ε) ?_ ?_
  · rw [hgen]
    exact div_mul_cancel₀ _ hgpos.ne'
  · rw [div_mul_eq_mul_div, div_lt_one hgpos]
    nlinarith

/-! ### The law of a size statistic of the shape -/

/-- The law of a statistic of the shape under the shape law. -/
noncomputable def shapeStatMassE (f : Shape → ℕ) (n : ℕ) : ℝ≥0∞ :=
  ∑' σ : Shape, if f σ = n then shapeMass θ σ else 0

/-- The law of a statistic of the shape as a real weight, the form `chernoff_tail`
consumes. -/
noncomputable def shapeStatMass (f : Shape → ℕ) (n : ℕ) : ℝ := (shapeStatMassE θ f n).toReal

lemma shapeStatMass_nonneg (f : Shape → ℕ) (n : ℕ) : 0 ≤ shapeStatMass θ f n :=
  ENNReal.toReal_nonneg

/-- **The size moment read off the law of the statistic**: the moment is the sum over the
possible values. -/
lemma tsum_pow_shapeStatMassE (f : Shape → ℕ) (s : ℝ≥0∞) :
    ∑' n : ℕ, s ^ n * shapeStatMassE θ f n = ∑' σ : Shape, shapeMass θ σ * s ^ f σ := by
  have hterm : ∀ (n : ℕ) (σ : Shape),
      s ^ n * (if f σ = n then shapeMass θ σ else 0)
        = if f σ = n then shapeMass θ σ * s ^ n else 0 := by
    intro n σ
    by_cases h : f σ = n <;> simp [h, mul_comm]
  calc ∑' n : ℕ, s ^ n * shapeStatMassE θ f n
      = ∑' (n : ℕ) (σ : Shape), (if f σ = n then shapeMass θ σ * s ^ n else 0) := by
        refine tsum_congr fun n ↦ ?_
        rw [shapeStatMassE, ← ENNReal.tsum_mul_left]
        exact tsum_congr (hterm n)
    _ = ∑' (σ : Shape) (n : ℕ), (if f σ = n then shapeMass θ σ * s ^ n else 0) :=
        ENNReal.tsum_comm
    _ = ∑' σ : Shape, shapeMass θ σ * s ^ f σ := by
        refine tsum_congr fun σ ↦ ?_
        refine (tsum_eq_single (f σ) fun n hn ↦ if_neg fun h ↦ hn h.symm).trans ?_
        rw [if_pos rfl]

/-- **The size moment in the form `chernoff_tail` consumes**: a finite moment is a
summable real series over the possible values of the statistic, and its sum is the
moment. -/
theorem summable_shapeStatMass_mgf (f : Shape → ℕ) {t : ℝ}
    (hmom : ∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal (Real.exp t) ^ f σ ≠ ⊤) :
    Summable (fun n : ℕ ↦ Real.exp (t * (n : ℝ)) * shapeStatMass θ f n) ∧
      ∑' n : ℕ, Real.exp (t * (n : ℝ)) * shapeStatMass θ f n
        = (∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal (Real.exp t) ^ f σ).toReal := by
  set G : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (Real.exp t) ^ n * shapeStatMassE θ f n with hG
  have hsum : ∑' n, G n = ∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal (Real.exp t) ^ f σ :=
    tsum_pow_shapeStatMassE θ f _
  have htop : ∑' n, G n ≠ ⊤ := by rw [hsum]; exact hmom
  have hne : ∀ n, G n ≠ ⊤ := fun n ↦ ne_top_of_le_ne_top htop (ENNReal.le_tsum n)
  have htoReal : ∀ n : ℕ, (G n).toReal = Real.exp (t * (n : ℝ)) * shapeStatMass θ f n := by
    intro n
    rw [hG]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (Real.exp_pos t).le, exp_mul_nat]
    rfl
  have hsummable : Summable fun n : ℕ ↦ (G n).toReal := ENNReal.summable_toReal htop
  refine ⟨hsummable.congr htoReal, ?_⟩
  rw [← hsum, ENNReal.tsum_toReal_eq hne]
  exact tsum_congr fun n ↦ (htoReal n).symm

/-- **`thm:shape-mass` (`it:shape-mass-tail`) for a statistic of the shape**: a
finite moment above one gives an exponential tail, `shape_mass_tail` absorbing the moment
constant past a threshold. -/
theorem exists_shape_stat_tail (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (f : Shape → ℕ) {s : ℝ} (hs : 1 < s)
    (hmom : ∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal s ^ f σ < ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      ∑' k : ℕ, shapeStatMass θ f (k + N) ≤ Real.exp (-c * (N : ℝ)) := by
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs
  have hone : (1 : ℝ≥0∞) ≤ ∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal s ^ f σ := by
    have hpow : ∀ σ : Shape, (1 : ℝ≥0∞) ≤ ENNReal.ofReal s ^ f σ := by
      intro σ
      refine one_le_pow₀ ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hs.le
    calc (1 : ℝ≥0∞) = ∑' σ : Shape, shapeMass θ σ := (tsum_shapeMass θ hq hq0 h2).symm
      _ ≤ ∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal s ^ f σ := by
          refine ENNReal.tsum_le_tsum fun σ ↦ ?_
          nth_rewrite 1 [← mul_one (shapeMass θ σ)]
          exact mul_le_mul' le_rfl (hpow σ)
  set t : ℝ := Real.log s with ht_def
  have hexp : Real.exp t = s := Real.exp_log hs0
  have ht : 0 < t := Real.log_pos hs
  rw [← hexp] at hmom hone
  set M : ℝ := (∑' σ : Shape, shapeMass θ σ * ENNReal.ofReal (Real.exp t) ^ f σ).toReal
    with hM_def
  have hM1 : (1 : ℝ) ≤ M := by
    have h := ENNReal.toReal_mono hmom.ne hone
    rwa [ENNReal.toReal_one] at h
  obtain ⟨hsummable, hsumeq⟩ := summable_shapeStatMass_mgf θ f hmom.ne
  refine ⟨t / 2, by linarith, ⌈2 * Real.log M / t⌉₊, fun N hN ↦ ?_⟩
  have hNge : 2 * Real.log M / t ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNt : 2 * Real.log M ≤ t * (N : ℝ) := by
    rw [div_le_iff₀ ht] at hNge
    linarith
  have hMle : ∑' n : ℕ, Real.exp (t * (n : ℝ)) * shapeStatMass θ f n ≤ M := le_of_eq hsumeq
  exact shape_mass_tail ht hM1 (shapeStatMass_nonneg θ f) hsummable hMle hNt

/-! ### The tail of the size of a shape -/

/-- **The law of the size of a shape**, the mass of the shapes of a given size. -/
noncomputable def shapeSizeMass (n : ℕ) : ℝ := shapeStatMass θ Shape.size n

/-- **`thm:shape-mass` (`it:shape-mass-tail`)**: the size of a shape has an
exponential tail. -/
theorem exists_shape_size_tail (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      ∑' k : ℕ, shapeSizeMass θ (k + N) ≤ Real.exp (-c * (N : ℝ)) := by
  obtain ⟨s, hs, hmom⟩ := exists_shape_size_moment θ hq hq0 h2
  exact exists_shape_stat_tail θ hq hq0 h2 Shape.size hs hmom

/-! ### The tail of the size of the support fix -/

/-- **The law of the size of the support fix of a shape**, the label
`thm:shape-coupling` reads. -/
noncomputable def fixSizeMass (n : ℕ) : ℝ := shapeStatMass θ (fun σ ↦ σ.fix.size) n

/-- **`thm:shape-mass` (`it:shape-mass-tail`) for the support fix**: the fix at
most doubles the size, so its size has an exponential tail at half the rate. -/
theorem exists_fix_size_tail (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      ∑' k : ℕ, fixSizeMass θ (k + N) ≤ Real.exp (-c * (N : ℝ)) := by
  obtain ⟨s, hs, hmom⟩ := exists_shape_size_moment θ hq hq0 h2
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs
  have hr : 1 < Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hs
  have hsq : ENNReal.ofReal (Real.sqrt s) ^ 2 = ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg s), Real.sq_sqrt hs0.le]
  have hmom' : ∑' σ : Shape,
      shapeMass θ σ * ENNReal.ofReal (Real.sqrt s) ^ σ.fix.size < ⊤ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun σ ↦ ?_) hmom
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt s) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le
    have hle : ENNReal.ofReal (Real.sqrt s) ^ σ.fix.size ≤ ENNReal.ofReal s ^ σ.size := by
      calc ENNReal.ofReal (Real.sqrt s) ^ σ.fix.size
          ≤ ENNReal.ofReal (Real.sqrt s) ^ (2 * σ.size) :=
            pow_le_pow_right' hone (size_fix_le σ)
        _ = ENNReal.ofReal s ^ σ.size := by rw [pow_mul, hsq]
    exact mul_le_mul' le_rfl hle
  exact exists_shape_stat_tail θ hq hq0 h2 (fun σ ↦ σ.fix.size) hr hmom'

end ChainClasses

