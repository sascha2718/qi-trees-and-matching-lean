/-
Directed potentials (`arbitrary_offspring_matching.tex` `sec:four-law`).
Two changes against the `Phi` of the support layer:

* **Directed**: the row law `μ` and the column law `ν` are different PMFs;
  the bad degree of a row point is measured against the column law. The
  support layer's `Phi α μ R` is the diagonal case `ν = μ`.
* **Safe at `q = 1`**: without reflexivity-on-support there is no guarantee
  that bad degrees stay below one, and `Real.rpow`'s junk value `0 ^ (-α) = 0`
  would silently zero out exactly the points that must contribute the most. The
  `ℝ≥0∞`-valued weight `phiE` is `⊤` at `q ≥ 1`, so finite potentials really
  do force `q < 1` wherever the row law charges, and the failure bound
  `𝔼 q ≤ Φ` holds unconditionally.

The `badInd` normal form `q_ν(z) = ∑' y, ν y · 𝟙[z ⋡ y]` makes the bad degree
linear in the column law, which is how the kernel mixture enters the step.
-/
import GraphMarkovMatching.Process.Sim
import GraphMarkovMatching.Support.Potential

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

/-! ### The safe weight `phiE` -/

/-- The `ℝ≥0∞`-valued potential weight: `φ_α` below `1`, `⊤` from `1` on. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤

lemma phiE_of_lt {α t : ℝ} (h : t < 1) : phiE α t = ENNReal.ofReal (phi α t) :=
  if_pos h

@[simp] lemma phiE_one (α : ℝ) : phiE α 1 = ⊤ := if_neg (lt_irrefl 1)

@[simp] lemma phiE_zero (α : ℝ) : phiE α 0 = 0 := by
  rw [phiE_of_lt one_pos, phi, ENNReal.ofReal_eq_zero]
  simp

/-- `φ_α` is monotone on `[0,1)` (numerator grows, denominator shrinks). -/
lemma phi_mono {α t t' : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ t) (htt : t ≤ t') (h1 : t' < 1) :
    phi α t ≤ phi α t' := by
  have hd' : (0 : ℝ) < (1 - t') ^ α := rpow_denom_pos α h1
  have hbase : (0 : ℝ) ≤ 1 - t' := by linarith
  have hmono : (1 - t') ^ α ≤ (1 - t) ^ α :=
    Real.rpow_le_rpow hbase (by linarith) hα
  exact div_le_div₀ (by linarith) htt hd' hmono

/-- `phiE` is monotone on `[0,1]` (and trivially beyond, where it is `⊤`). -/
lemma phiE_mono {α t t' : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ t) (htt : t ≤ t') :
    phiE α t ≤ phiE α t' := by
  by_cases h1' : t' < 1
  · rw [phiE_of_lt (lt_of_le_of_lt htt h1'), phiE_of_lt h1']
    exact ENNReal.ofReal_le_ofReal (phi_mono hα h0 htt h1')
  · have h : phiE α t' = ⊤ := if_neg h1'
    rw [h]
    exact le_top

/-- `t ≤ φ_α t` in the safe form: the failure-probability step. -/
lemma ofReal_le_phiE {α t : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ENNReal.ofReal t ≤ phiE α t := by
  rcases lt_or_eq_of_le h1 with h | h
  · rw [phiE_of_lt h]
    exact ENNReal.ofReal_le_ofReal (le_phi hα h0 h)
  · rw [h, phiE_one]
    exact le_top

/-! ### The bad-degree normal form -/

/-- The bad indicator `𝟙[¬ R z y]` as an `ℝ≥0∞` weight. -/
noncomputable def badInd (R : X → X → Prop) (z y : X) : ℝ≥0∞ :=
  if R z y then 0 else 1

/-- `q_ν(z) = 𝔼_ν 𝟙[z ⋡ ·]`: the bad degree in the linear normal form. -/
lemma qE_eq_tsum_mul (ν : PMF X) (R : X → X → Prop) (z : X) :
    qE ν R z = ∑' y, ν y * badInd R z y := by
  rw [qE]
  exact tsum_congr fun y => by by_cases h : R z y <;> simp [badInd, h]

/-- The bad degree is linear in the column law: mixture form. -/
lemma qE_bind {A : Type u} (w : PMF A) (f : A → PMF X) (R : X → X → Prop) (z : X) :
    qE (w.bind f) R z = ∑' a, w a * qE (f a) R z := by
  rw [qE_eq_tsum_mul, tsum_bind_mul]
  exact tsum_congr fun a => by rw [qE_eq_tsum_mul]

/-- The bad degree under a pushforward column law. -/
lemma qE_map {A : Type u} (μ : PMF A) (g : A → X) (R : X → X → Prop) (z : X) :
    qE (μ.map g) R z = ∑' a, μ a * badInd R z (g a) := by
  rw [qE_eq_tsum_mul, tsum_map_mul]

/-! ### The directed potential -/

/-- The directed potential `Φ_α(μ → ν; R) = 𝔼_{x∼μ} φ_α(q_ν(x))`, in the safe
`phiE` convention. -/
noncomputable def PhiD (α : ℝ) (μ ν : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * phiE α (q ν R x)

/-- Rows decompose linearly: the potential of a row mixture. -/
lemma PhiD_bind_left {A : Type u} (α : ℝ) (w : PMF A) (f : A → PMF X)
    (ν : PMF X) (R : X → X → Prop) :
    PhiD α (w.bind f) ν R = ∑' a, w a * PhiD α (f a) ν R := by
  rw [PhiD, tsum_bind_mul]
  exact tsum_congr fun a => by rw [PhiD]

/-- Rows transport along a pushforward. -/
lemma PhiD_map_left {A : Type u} (α : ℝ) (μ : PMF A) (g : A → X)
    (ν : PMF X) (R : X → X → Prop) :
    PhiD α (μ.map g) ν R = ∑' a, μ a * phiE α (q ν R (g a)) := by
  rw [PhiD, tsum_map_mul]

/-- **The failure bound**: the mean bad degree is at most the potential,
`𝔼_{x∼μ} q_ν(x) ≤ Φ_α(μ → ν)`. Unconditional in the safe convention. -/
lemma tsum_qE_le_PhiD {α : ℝ} (hα : 0 ≤ α) (μ ν : PMF X) (R : X → X → Prop) :
    ∑' x, μ x * qE ν R x ≤ PhiD α μ ν R := by
  rw [PhiD]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have hq : qE ν R x = ENNReal.ofReal (q ν R x) := by
    rw [q, ENNReal.ofReal_toReal qE_ne_top]
  rw [hq]
  exact mul_le_mul_right (ofReal_le_phiE hα q_nonneg q_le_one) _

end GraphMarkovMatching
