/-
`sec:gw-trees` of `prelims.tex`: the offspring layer of a Galton-Watson
branching process.  An offspring law with support in `{0,…,J}`, bundled with
its mean and its generating function, and the extinction probability read off
as the least fixed point of the generating function in `[0,1]`.

* `Offspring`: the law `θ = (θ_0,…,θ_J)`, nonnegative, vanishing above `J` and
  summing to one, with `mass_le_one`.
* `mean`, the mean offspring number `m = ∑_j j θ_j`, and the three regimes
  `IsSubcritical`, `IsCritical`, `IsSupercritical` that `thm:trichotomy`
  separates.
* `gen`, the generating function `f(s) = ∑_j θ_j s^j`, with `gen_one`,
  `gen_zero`, `gen_nonneg`, `gen_le_one`, `continuous_gen` and `gen_mono`;
  `genDeriv` with `hasDerivAt_gen` and `genDeriv_one` (`f'(1) = m`).
* `genSlope`, the difference quotient `(1-f(s))/(1-s)` in its polynomial form
  `one_sub_gen`, with `genSlope_one` (`= m`): the mean read off the generating
  function without differentiating.
* `extinction`, the extinction probability `q = inf {s ∈ [0,1] : f(s) = s}`:
  `extinction_mem` (the infimum is itself a fixed point), `extinction_nonneg`,
  `extinction_le_one`, `extinction_le_of_fixed` (minimality),
  `extinction_eq_zero_iff` (`q = 0` exactly at `θ_0 = 0`) and `extinction_pos`.
* `extinction_lt_one_of_supercritical`: a supercritical law survives with
  positive probability, the hypothesis carried by every offspring law of
  `thm:trichotomy`.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone

namespace BranchingProcess

/-- An offspring distribution with support in `{0,…,J}`: the masses
`θ_0,…,θ_J` of the number of children of a vertex. -/
structure Offspring (J : ℕ) where
  /-- The mass function `j ↦ θ_j`. -/
  mass : ℕ → ℝ
  /-- Masses are nonnegative. -/
  nonneg : ∀ j, 0 ≤ mass j
  /-- The support lies in `{0,…,J}`. -/
  vanishing : ∀ j, J < j → mass j = 0
  /-- The masses sum to one. -/
  total : ∑ j ∈ Finset.range (J + 1), mass j = 1

/-- An offspring law acts as its mass function, so `θ j` is the mass of `j`. -/
instance {J : ℕ} : CoeFun (Offspring J) (fun _ => ℕ → ℝ) := ⟨Offspring.mass⟩

namespace Offspring

variable {J : ℕ} (θ : Offspring J)

/-! ### The law -/

/-- Every mass is at most one. -/
lemma mass_le_one (j : ℕ) : θ j ≤ 1 := by
  rcases le_or_gt j J with hj | hj
  · have hle : θ j ≤ ∑ i ∈ Finset.range (J + 1), θ i :=
      Finset.single_le_sum (f := fun i => θ i) (fun i _ => θ.nonneg i)
        (Finset.mem_range.mpr (by omega))
    rw [θ.total] at hle
    exact hle
  · rw [θ.vanishing j hj]
    norm_num

/-! ### The mean and the three regimes -/

/-- The mean offspring number `m = ∑_j j θ_j`. -/
noncomputable def mean : ℝ := ∑ j ∈ Finset.range (J + 1), (j : ℝ) * θ j

/-- A law is subcritical when its mean is below one. -/
def IsSubcritical : Prop := mean θ < 1

/-- A law is critical when its mean is one. -/
def IsCritical : Prop := mean θ = 1

/-- A law is supercritical when its mean exceeds one. -/
def IsSupercritical : Prop := 1 < mean θ

/-! ### The generating function -/

/-- The generating function `f(s) = ∑_{j=0}^{J} θ_j s^j`. -/
noncomputable def gen (s : ℝ) : ℝ := ∑ j ∈ Finset.range (J + 1), θ j * s ^ j

/-- `f(1) = 1`: the masses sum to one. -/
@[simp] lemma gen_one : gen θ 1 = 1 := by
  simp only [gen, one_pow, mul_one]
  exact θ.total

/-- `f(0) = θ_0`: only the constant term survives. -/
@[simp] lemma gen_zero : gen θ 0 = θ 0 := by
  rw [gen, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos J))]
  · rw [pow_zero, mul_one]
  · intro j _ hj
    rw [zero_pow hj, mul_zero]

/-- `f` is nonnegative on the nonnegative half-line. -/
lemma gen_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ gen θ s :=
  Finset.sum_nonneg fun j _ => mul_nonneg (θ.nonneg j) (pow_nonneg hs j)

/-- `f` maps `[0,1]` into `[0,1]`; this is the upper half. -/
lemma gen_le_one {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : gen θ s ≤ 1 := by
  calc gen θ s ≤ ∑ j ∈ Finset.range (J + 1), θ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc θ j * s ^ j ≤ θ j * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ hs.1 hs.2) (θ.nonneg j)
          _ = θ j := mul_one _
    _ = 1 := θ.total

/-- `f` is a polynomial, hence continuous. -/
lemma continuous_gen : Continuous (gen θ) := by
  unfold gen
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow j)

/-- `f` is monotone on the nonnegative half-line, so in particular on `[0,1]`. -/
lemma gen_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : gen θ s ≤ gen θ t :=
  Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst j) (θ.nonneg j)

/-- The derivative `f'(s) = ∑_{j=1}^{J} j θ_j s^{j-1}`; the `j = 0` term
vanishes through the cast. -/
noncomputable def genDeriv (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), (j : ℝ) * θ j * s ^ (j - 1)

/-- `genDeriv` is the derivative of the generating function. -/
lemma hasDerivAt_gen (s : ℝ) : HasDerivAt (gen θ) (genDeriv θ s) s := by
  have h : ∀ j ∈ Finset.range (J + 1),
      HasDerivAt (fun x : ℝ => θ j * x ^ j) ((j : ℝ) * θ j * s ^ (j - 1)) s := by
    intro j _
    have hp := HasDerivAt.const_mul (θ j) (hasDerivAt_pow j s)
    have he : (j : ℝ) * θ j * s ^ (j - 1) = θ j * ((j : ℝ) * s ^ (j - 1)) := by ring
    rw [he]
    exact hp
  exact HasDerivAt.fun_sum (A := fun (j : ℕ) (x : ℝ) => θ j * x ^ j)
    (A' := fun j => (j : ℝ) * θ j * s ^ (j - 1)) h

/-- `f'(1) = m`: the derivative at one is the mean. -/
lemma genDeriv_one : genDeriv θ 1 = mean θ := by
  simp only [genDeriv, mean, one_pow, mul_one]

/-! ### The difference quotient at one -/

/-- The polynomial `g(s) = ∑_j θ_j (1 + s + ⋯ + s^{j-1})`, the difference
quotient `(1-f(s))/(1-s)` cleared of its denominator. -/
noncomputable def genSlope (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), θ j * ∑ i ∈ Finset.range j, s ^ i

/-- `1 - f(s) = (1-s) g(s)`, the geometric sum taken termwise. -/
lemma one_sub_gen (s : ℝ) : 1 - gen θ s = (1 - s) * genSlope θ s := by
  have hexp : (1 - s) * genSlope θ s
      = ∑ j ∈ Finset.range (J + 1), (θ j - θ j * s ^ j) := by
    rw [genSlope, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc (1 - s) * (θ j * ∑ i ∈ Finset.range j, s ^ i)
        = θ j * ((1 - s) * ∑ i ∈ Finset.range j, s ^ i) := by ring
      _ = θ j * (1 - s ^ j) := by rw [mul_neg_geom_sum]
      _ = θ j - θ j * s ^ j := by ring
  have hsum : ∑ j ∈ Finset.range (J + 1), (θ j - θ j * s ^ j) = 1 - gen θ s := by
    simp only [gen, Finset.sum_sub_distrib, θ.total]
  rw [hexp, hsum]

/-- `g(1) = m`: the difference quotient at one is the mean. -/
lemma genSlope_one : genSlope θ 1 = mean θ := by
  rw [genSlope, mean]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ∑ i ∈ Finset.range j, (1 : ℝ) ^ i = (j : ℝ) := by simp
  rw [hj, mul_comm]

/-- `g` is a polynomial, hence continuous. -/
lemma continuous_genSlope : Continuous (genSlope θ) := by
  unfold genSlope
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_pow i)

/-! ### The extinction probability -/

/-- The fixed points of the generating function in `[0,1]`. -/
def fixedSet : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ gen θ s = s}

/-- **The extinction probability** `q = inf {s ∈ [0,1] : f(s) = s}`, the least
fixed point of the generating function in `[0,1]`. -/
noncomputable def extinction : ℝ := sInf θ.fixedSet

/-- `1` is a fixed point, so the set is nonempty. -/
lemma one_mem_fixedSet : (1 : ℝ) ∈ θ.fixedSet := ⟨⟨zero_le_one, le_rfl⟩, θ.gen_one⟩

/-- The set of fixed points in `[0,1]` is nonempty. -/
lemma fixedSet_nonempty : θ.fixedSet.Nonempty := ⟨1, θ.one_mem_fixedSet⟩

/-- The set of fixed points in `[0,1]` is bounded below by `0`. -/
lemma bddBelow_fixedSet : BddBelow θ.fixedSet := ⟨0, fun _ hs => hs.1.1⟩

/-- The set of fixed points in `[0,1]` is closed, `f` being continuous. -/
lemma isClosed_fixedSet : IsClosed θ.fixedSet := by
  have hinter : θ.fixedSet = Set.Icc (0 : ℝ) 1 ∩ {s | gen θ s = s} := rfl
  rw [hinter]
  exact isClosed_Icc.inter (isClosed_eq θ.continuous_gen continuous_id)

/-- **The infimum is itself a fixed point**: `q ∈ [0,1]` and `f(q) = q`. -/
theorem extinction_mem :
    θ.extinction ∈ Set.Icc (0 : ℝ) 1 ∧ gen θ θ.extinction = θ.extinction :=
  θ.isClosed_fixedSet.csInf_mem θ.fixedSet_nonempty θ.bddBelow_fixedSet

/-- The extinction probability is nonnegative. -/
lemma extinction_nonneg : 0 ≤ θ.extinction := θ.extinction_mem.1.1

/-- The extinction probability is at most one. -/
lemma extinction_le_one : θ.extinction ≤ 1 := θ.extinction_mem.1.2

/-- `f(q) = q`. -/
lemma gen_extinction : gen θ θ.extinction = θ.extinction := θ.extinction_mem.2

/-- **Minimality**: the extinction probability is below every fixed point of
`f` in `[0,1]`. -/
theorem extinction_le_of_fixed {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hfix : gen θ s = s) : θ.extinction ≤ s :=
  csInf_le θ.bddBelow_fixedSet ⟨hs, hfix⟩

/-- **Extinction is impossible exactly when childless vertices are**:
`q = 0` if and only if `θ_0 = 0`. -/
theorem extinction_eq_zero_iff : θ.extinction = 0 ↔ θ 0 = 0 := by
  constructor
  · intro h
    have hfix := θ.extinction_mem.2
    rw [h, θ.gen_zero] at hfix
    exact hfix
  · intro h
    refine le_antisymm ?_ θ.extinction_nonneg
    exact θ.extinction_le_of_fixed ⟨le_rfl, zero_le_one⟩ (by rw [θ.gen_zero, h])

/-- Positive mass at zero forces a positive extinction probability. -/
theorem extinction_pos (h : 0 < θ 0) : 0 < θ.extinction :=
  lt_of_le_of_ne θ.extinction_nonneg fun hc =>
    h.ne' (θ.extinction_eq_zero_iff.mp hc.symm)

/-- **The classical criterion**: a supercritical law survives with positive
probability, `q < 1`.  The mean exceeds one, so the difference quotient `g` of
`one_sub_gen` exceeds one at some `s < 1`, whence `f(s) < s`; since
`f(0) = θ_0 ≥ 0`, the intermediate value theorem returns a fixed point in
`[0,s]`, and minimality pushes `q` below it. -/
theorem extinction_lt_one_of_supercritical (h : θ.IsSupercritical) :
    θ.extinction < 1 := by
  have hmean : 1 < mean θ := h
  have hopen : IsOpen {s : ℝ | 1 < genSlope θ s} :=
    isOpen_lt continuous_const θ.continuous_genSlope
  have hone : (1 : ℝ) ∈ {s : ℝ | 1 < genSlope θ s} := by
    show 1 < genSlope θ 1
    rw [θ.genSlope_one]
    exact hmean
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
  set s : ℝ := max (1 - ε / 2) (1 / 2) with hs_def
  have hs_ge : 1 - ε / 2 ≤ s := le_max_left _ _
  have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num) (le_max_right (1 - ε / 2) (1 / 2))
  have hs_lt : s < 1 := max_lt (by linarith) (by norm_num)
  have hs_ball : s ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith
  have hslope : 1 < genSlope θ s := hball hs_ball
  have hfs : gen θ s < s := by
    have hquot := θ.one_sub_gen s
    have hgt : (1 - s) * 1 < (1 - s) * genSlope θ s :=
      mul_lt_mul_of_pos_left hslope (by linarith)
    rw [mul_one] at hgt
    linarith
  have hcont : ContinuousOn (fun x => gen θ x - x) (Set.Icc 0 s) :=
    (θ.continuous_gen.sub continuous_id).continuousOn
  have hzero : (0 : ℝ) ∈ Set.Icc ((fun x => gen θ x - x) s) ((fun x => gen θ x - x) 0) := by
    refine ⟨by simpa using hfs.le, ?_⟩
    simp only [sub_zero, θ.gen_zero]
    exact θ.nonneg 0
  obtain ⟨c, hc_mem, hc⟩ := intermediate_value_Icc' hs_pos.le hcont hzero
  have hcfix : gen θ c = c := by
    have := hc
    simp only [sub_eq_zero] at this
    exact this
  have hle : θ.extinction ≤ c :=
    θ.extinction_le_of_fixed ⟨hc_mem.1, le_trans hc_mem.2 hs_lt.le⟩ hcfix
  linarith [hc_mem.2]

/-! ### The subcritical and critical criterion -/

/-- The difference quotient `g` is monotone on `[0,∞)`: each geometric sum is. -/
lemma genSlope_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    genSlope θ s ≤ genSlope θ t := by
  unfold genSlope
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (θ.nonneg j)
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hs hst i

/-- With positive mass at some `j ≥ 2`, `g` is strictly increasing on `[0,∞)`. -/
lemma genSlope_lt_of_lt {j : ℕ} (hj : 2 ≤ j) (hθ : 0 < θ j) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) : genSlope θ s < genSlope θ t := by
  have hjJ : j ∈ Finset.range (J + 1) := by
    rw [Finset.mem_range]
    by_contra hc
    exact hθ.ne' (θ.vanishing j (by omega))
  unfold genSlope
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, hjJ, ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hs hst.le i) (θ.nonneg i)
  · refine mul_lt_mul_of_pos_left ?_ hθ
    refine Finset.sum_lt_sum (fun i _ => pow_le_pow_left₀ hs hst.le i) ⟨1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · simpa using hst

/-- Without mass above one, `g` is the constant `θ_1`. -/
lemma genSlope_eq_of_forall_zero (h : ∀ j, 2 ≤ j → θ j = 0) (s : ℝ) :
    genSlope θ s = θ 1 := by
  unfold genSlope
  rw [Finset.sum_eq_single 1]
  · simp
  · intro j _ hj1
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      · simp
      · exact absurd rfl hj1
    · rw [h j hj, zero_mul]
  · intro h1
    rw [Finset.mem_range] at h1
    rw [θ.vanishing 1 (by omega), zero_mul]

/-- **The classical criterion, second half**: a law with mean at most one dies out, `q = 1`,
unless it is the deterministic single child `θ_1 = 1`.  At a fixed point `s < 1` the
difference quotient equals one; it is below the mean when some `θ_j > 0` with `j ≥ 2`, and
equals `θ_1` otherwise. -/
theorem extinction_eq_one_of_mean_le_one (h : mean θ ≤ 1) (h1 : θ 1 ≠ 1) :
    θ.extinction = 1 := by
  refine le_antisymm θ.extinction_le_one ?_
  by_contra hlt
  push Not at hlt
  have hq0 : 0 ≤ θ.extinction := θ.extinction_nonneg
  have hfix : gen θ θ.extinction = θ.extinction := θ.gen_extinction
  -- At the fixed point `q < 1` the difference quotient equals one.
  have hslope : genSlope θ θ.extinction = 1 := by
    have hquot := θ.one_sub_gen θ.extinction
    rw [hfix] at hquot
    have hne : (1 - θ.extinction) ≠ 0 := sub_ne_zero.mpr hlt.ne'
    have hmul : (1 - θ.extinction) * genSlope θ θ.extinction = (1 - θ.extinction) * 1 := by
      rw [mul_one, ← hquot]
    exact mul_left_cancel₀ hne hmul
  by_cases hex : ∃ j, 2 ≤ j ∧ θ j ≠ 0
  · -- Some mass above one: `g` is strictly increasing, so `g(q) < g(1) = m ≤ 1`.
    obtain ⟨j, hj, hjne⟩ := hex
    have hpos : 0 < θ j := lt_of_le_of_ne (θ.nonneg j) (Ne.symm hjne)
    have hlt' : genSlope θ θ.extinction < genSlope θ 1 := θ.genSlope_lt_of_lt hj hpos hq0 hlt
    rw [θ.genSlope_one, hslope] at hlt'
    linarith
  · -- No mass above one: `g` is the constant `θ_1`, which would have to be one.
    push Not at hex
    have hconst := θ.genSlope_eq_of_forall_zero hex θ.extinction
    rw [hslope] at hconst
    exact h1 hconst.symm

end Offspring

end BranchingProcess
