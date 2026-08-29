/-
`thm:relabel` and `thm:cross-relabel` of `matching_classes_general.tex`: the cascade
coupling at general shapes.

The cascade of `ShapeCouplingBuild` is a construction on an abstract countable type:
nothing in the coupling read off the alternating series mentions the shapes.  This file
restates it over an arbitrary type, so that the couplings of the conditional laws
`μ_κ` with the mixture `μ` are one instantiation away, and packages what
`thm:relabel` consumes: `IsGShapeCoupling`, the coupling supported on
`9D³`-comparable pairs of the marked spaces of `GeneralShapeMetric`, produced by
`exists_gShapeCoupling_of_capacity₂` from a capacity bound together with the
comparability of the cascade pairs and of the small pairs.  The two laws may have
different supports, so the cascade runs on two shrinkings: `sh₁₂` carries the atoms of
the second law into the support of the first, `sh₂₁` those of the first into the
support of the second, and the capacity bound `eq:capacity` asks of each fibre at most
half of the mass of its target.  The one-shrinking statements are the case
`sh₁₂ = sh₂₁`.  The capacity bound itself is `capacity_of_mass_boundsT_const`, the two
regimes of `eq:capacity` at an abstract size, support and shrinking with the shrinking
constant `C` of `|sh τ| ≤ C(|τ|/s + 1)`, fed by the point bound of `GeneralShapeMass`
and an exponential tail; the threshold between the regimes is `4C`, and the two
largeness conditions read `log 2 + 4C log p⁻¹ ≤ c Ncut` and
`log 2/(4C) + log p⁻¹ ≤ cs/(4C)`.

* `margFstT`, `margSndT`, `le_margFstT`, `le_margSndT`: the marginals of a law on pairs,
  each bounding the pairs it sums.
* `cascPairT₂`, `leftoverT`, `cascCouplingT₂`, `exists_couplingT_of_out₂`: **the
  coupling read off the cascade**, at an arbitrary type and two shrinkings;
  `cascPairT`, `cascCouplingT`, `exists_couplingT_of_out` the case of one shrinking.
* `sideDomT`, `sideMapT`, `sideShrinkT₂`, `sideMassT`, `sideOutT₂`,
  `exists_couplingT_of_capacity₂`: **the two-sided cascade** at two shrinkings and the
  coupling of two laws obeying `eq:capacity`; `sideShrinkT`, `sideOutT`,
  `exists_couplingT_of_capacity` the case of one shrinking.
* `capacity_small_const`, `capacity_large_const`, `capacity_of_mass_boundsT_const`:
  **`eq:capacity`** from a point bound and an exponential tail, at an abstract size,
  support and shrinking with the shrinking constant `C`; `capacity_of_mass_boundsT` the
  case `C = 16`.
* `IsGShapeCoupling`, `exists_gShapeCoupling_of_capacity₂`: **the coupling of
  `thm:relabel`**, supported on `9D³`-comparable pairs of general shapes, at two
  shrinkings; `exists_gShapeCoupling_of_capacity` the case of one shrinking, and
  `exists_gShapeCoupling_of_capacity₂'` the variant asking the comparabilities of the
  charged shapes only.
-/
import ChainClasses.GeneralShapeMass
import ChainClasses.GeneralShapeMetric
import ChainClasses.ShapeCouplingBuild

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical

/-! ### The marginals of a law on pairs -/

variable {T : Type*}

/-- The first marginal of a law on pairs. -/
noncomputable def margFstT (π : PMF (T × T)) (a : T) : ℝ≥0∞ := ∑' b : T, π (a, b)

/-- The second marginal of a law on pairs. -/
noncomputable def margSndT (π : PMF (T × T)) (b : T) : ℝ≥0∞ := ∑' a : T, π (a, b)

/-- A pair carries at most the first marginal of its first component. -/
lemma le_margFstT (π : PMF (T × T)) (a b : T) : π (a, b) ≤ margFstT π a :=
  ENNReal.le_tsum b

/-- A pair carries at most the second marginal of its second component. -/
lemma le_margSndT (π : PMF (T × T)) (a b : T) : π (a, b) ≤ margSndT π b :=
  ENNReal.le_tsum a

/-! ### The coupling read off the cascade, at an arbitrary type -/

/-- The cascade pairs at two shrinkings: a source `σ` of the first side in the domain
charges the pair `(σ, sh₂₁ σ)` with `out₁(σ)`, a source of the second side the pair
`(sh₁₂ σ, σ)` with `out₂(σ)`. -/
noncomputable def cascPairT₂ (dm : T → Prop) (sh₁₂ sh₂₁ : T → T) (out₁ out₂ : T → ℝ≥0∞)
    (p : T × T) : ℝ≥0∞ :=
  (if dm p.1 ∧ sh₂₁ p.1 = p.2 then out₁ p.1 else 0)
    + (if dm p.2 ∧ sh₁₂ p.2 = p.1 then out₂ p.2 else 0)

/-- The cascade pairs at one shrinking: the pair `(σ, sh σ)` of a source in the domain
carries the mass `out(σ)`, on either side. -/
noncomputable def cascPairT (dm : T → Prop) (sh : T → T) (out₁ out₂ : T → ℝ≥0∞)
    (p : T × T) : ℝ≥0∞ :=
  cascPairT₂ dm sh sh out₁ out₂ p

/-- The leftover of a side: what the cascade does not spend, carried by the atoms
outside the domain. -/
noncomputable def leftoverT (dm : T → Prop) (out : T → ℝ≥0∞) (a : T) : ℝ≥0∞ :=
  if dm a then 0 else out a

/-- The total leftover of a side. -/
noncomputable def leftoverTotT (dm : T → Prop) (out : T → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a : T, leftoverT dm out a

/-- The coupling of the cascade at two shrinkings: the cascade pairs together with the
normalised product of the two leftovers. -/
noncomputable def cascCouplingT₂ (dm : T → Prop) (sh₁₂ sh₂₁ : T → T)
    (out₁ out₂ : T → ℝ≥0∞) (p : T × T) : ℝ≥0∞ :=
  cascPairT₂ dm sh₁₂ sh₂₁ out₁ out₂ p
    + leftoverT dm out₁ p.1 * leftoverT dm out₂ p.2 / leftoverTotT dm out₁

/-- The coupling of the cascade at one shrinking. -/
noncomputable def cascCouplingT (dm : T → Prop) (sh : T → T)
    (out₁ out₂ : T → ℝ≥0∞) (p : T × T) : ℝ≥0∞ :=
  cascCouplingT₂ dm sh sh out₁ out₂ p

section Coupling

variable {dm : T → Prop} {sh sh₁₂ sh₂₁ : T → T} {out₁ out₂ : T → ℝ≥0∞}

/-- A sum over the fibre of the shrinking written as a sum over the whole type. -/
lemma tsum_fibreT_eq (f : T → ℝ≥0∞) (a : T) :
    ∑' b : T, (if dm b ∧ sh b = a then f b else 0)
      = ∑' τ : {τ : T // dm τ ∧ sh τ = a}, f τ.1 := by
  refine Eq.trans ?_ (tsum_subtype {τ : T | dm τ ∧ sh τ = a} f).symm
  refine tsum_congr fun b ↦ ?_
  by_cases hb : dm b ∧ sh b = a
  · rw [if_pos hb, Set.indicator_of_mem (show b ∈ {τ : T | dm τ ∧ sh τ = a} from hb) f]
  · rw [if_neg hb, Set.indicator_of_notMem (show b ∉ {τ : T | dm τ ∧ sh τ = a} from hb) f]

/-- The mass a source atom of the first side sends out, summed over the fibre of `sh₁₂`
it is the target of. -/
lemma tsum_cascPairT₂_fst (a : T) :
    ∑' b : T, cascPairT₂ dm sh₁₂ sh₂₁ out₁ out₂ (a, b)
      = (if dm a then out₁ a else 0) + ∑' τ : {τ : T // dm τ ∧ sh₁₂ τ = a}, out₂ τ.1 := by
  simp only [cascPairT₂]
  rw [ENNReal.tsum_add, ← tsum_fibreT_eq (sh := sh₁₂) out₂ a]
  congr 1
  by_cases ha : dm a
  · rw [if_pos ha]
    refine (tsum_eq_single (sh₂₁ a) fun b hb ↦ ?_).trans ?_
    · exact if_neg fun h ↦ hb h.2.symm
    · exact if_pos ⟨ha, rfl⟩
  · rw [if_neg ha]
    exact (tsum_congr fun b ↦ if_neg fun h ↦ ha h.1).trans tsum_zero

/-- The mirror statement on the second component. -/
lemma tsum_cascPairT₂_snd (b : T) :
    ∑' a : T, cascPairT₂ dm sh₁₂ sh₂₁ out₁ out₂ (a, b)
      = (if dm b then out₂ b else 0) + ∑' τ : {τ : T // dm τ ∧ sh₂₁ τ = b}, out₁ τ.1 := by
  simp only [cascPairT₂]
  rw [ENNReal.tsum_add, ← tsum_fibreT_eq (sh := sh₂₁) out₁ b, add_comm]
  congr 1
  by_cases hb : dm b
  · rw [if_pos hb]
    refine (tsum_eq_single (sh₁₂ b) fun a ha ↦ ?_).trans ?_
    · exact if_neg fun h ↦ ha h.2.symm
    · exact if_pos ⟨hb, rfl⟩
  · rw [if_neg hb]
    exact (tsum_congr fun a ↦ if_neg fun h ↦ hb h.1).trans tsum_zero

/-- The mass a source atom sends out, summed over the fibre it is the source of. -/
lemma tsum_cascPairT_fst (a : T) :
    ∑' b : T, cascPairT dm sh out₁ out₂ (a, b)
      = (if dm a then out₁ a else 0) + ∑' τ : {τ : T // dm τ ∧ sh τ = a}, out₂ τ.1 :=
  tsum_cascPairT₂_fst a

/-- The mirror statement on the second component. -/
lemma tsum_cascPairT_snd (b : T) :
    ∑' a : T, cascPairT dm sh out₁ out₂ (a, b)
      = (if dm b then out₂ b else 0) + ∑' τ : {τ : T // dm τ ∧ sh τ = b}, out₁ τ.1 :=
  tsum_cascPairT₂_snd b

/-- The mass a side carries splits into the part the cascade spends and the leftover. -/
lemma tsum_split_leftoverT (out : T → ℝ≥0∞) :
    ∑' a : T, out a
      = (∑' a : T, (if dm a then out a else 0)) + leftoverTotT dm out := by
  rw [leftoverTotT, ← ENNReal.tsum_add]
  refine tsum_congr fun a ↦ ?_
  rw [leftoverT]
  by_cases ha : dm a <;> simp [ha]

/-- The mass the cascade spends at the targets of one side is the mass its sources send
out on the other. -/
lemma tsum_tsum_fibreT (f : T → ℝ≥0∞) :
    ∑' a : T, (∑' τ : {τ : T // dm τ ∧ sh τ = a}, f τ.1)
      = ∑' b : T, (if dm b then f b else 0) := by
  have hswap : ∑' (a : T) (b : T), (if dm b ∧ sh b = a then f b else 0)
      = ∑' (b : T) (a : T), (if dm b ∧ sh b = a then f b else 0) := ENNReal.tsum_comm
  calc ∑' a : T, (∑' τ : {τ : T // dm τ ∧ sh τ = a}, f τ.1)
      = ∑' (a : T) (b : T), (if dm b ∧ sh b = a then f b else 0) :=
        (tsum_congr fun a ↦ tsum_fibreT_eq f a).symm
    _ = ∑' (b : T) (a : T), (if dm b ∧ sh b = a then f b else 0) := hswap
    _ = ∑' b : T, (if dm b then f b else 0) := by
        refine tsum_congr fun b ↦ ?_
        by_cases hb : dm b
        · rw [if_pos hb]
          refine (tsum_eq_single (sh b) fun a ha ↦ ?_).trans ?_
          · exact if_neg fun h ↦ ha h.2.symm
          · exact if_pos ⟨hb, rfl⟩
        · rw [if_neg hb]
          exact (tsum_congr fun a ↦ if_neg fun h ↦ hb h.1).trans tsum_zero

/-- **The coupling read off the cascade at two shrinkings**: with the two cascade masses
satisfying `out + in = mass` on either side, the cascade pairs and the normalised product
of the two leftovers form a coupling of the two laws.  It charges only the pairs
`(σ, sh₂₁ σ)` and `(sh₁₂ σ, σ)` of a source in the domain and the pairs of two atoms
outside it. -/
theorem exists_couplingT_of_out₂ (q₁ q₂ : PMF T)
    (hout₁ : ∀ a : T, out₁ a + (∑' τ : {τ : T // dm τ ∧ sh₁₂ τ = a}, out₂ τ.1) = q₁ a)
    (hout₂ : ∀ b : T, out₂ b + (∑' τ : {τ : T // dm τ ∧ sh₂₁ τ = b}, out₁ τ.1) = q₂ b) :
    ∃ π : PMF (T × T), (∀ a : T, margFstT π a = q₁ a) ∧
      (∀ b : T, margSndT π b = q₂ b) ∧
      ∀ p : T × T, π p ≠ 0 →
        (dm p.1 ∧ sh₂₁ p.1 = p.2) ∨ (dm p.2 ∧ sh₁₂ p.2 = p.1) ∨ (¬ dm p.1 ∧ ¬ dm p.2) := by
  have htot₁ : (∑' a : T, (if dm a then out₁ a else 0)) + leftoverTotT dm out₁
      + (∑' b : T, (if dm b then out₂ b else 0)) = 1 := by
    rw [← tsum_split_leftoverT out₁, ← tsum_tsum_fibreT (sh := sh₁₂) out₂, ← ENNReal.tsum_add,
      ← q₁.tsum_coe]
    exact tsum_congr hout₁
  have htot₂ : (∑' b : T, (if dm b then out₂ b else 0)) + leftoverTotT dm out₂
      + (∑' a : T, (if dm a then out₁ a else 0)) = 1 := by
    rw [← tsum_split_leftoverT out₂, ← tsum_tsum_fibreT (sh := sh₂₁) out₁, ← ENNReal.tsum_add,
      ← q₂.tsum_coe]
    exact tsum_congr hout₂
  have hSfin : (∑' a : T, (if dm a then out₁ a else 0))
      + (∑' b : T, (if dm b then out₂ b else 0)) ≠ ⊤ := by
    intro h
    rw [show (∑' a : T, (if dm a then out₁ a else 0)) + leftoverTotT dm out₁
        + (∑' b : T, (if dm b then out₂ b else 0))
        = ((∑' a : T, (if dm a then out₁ a else 0))
          + (∑' b : T, (if dm b then out₂ b else 0))) + leftoverTotT dm out₁ by ring_nf,
      h, top_add] at htot₁
    exact ENNReal.top_ne_one htot₁
  have hLeq : leftoverTotT dm out₁ = leftoverTotT dm out₂ := by
    refine (ENNReal.add_left_inj hSfin).mp ?_
    calc leftoverTotT dm out₁ + ((∑' a : T, (if dm a then out₁ a else 0))
          + (∑' b : T, (if dm b then out₂ b else 0)))
        = (∑' a : T, (if dm a then out₁ a else 0)) + leftoverTotT dm out₁
          + (∑' b : T, (if dm b then out₂ b else 0)) := by ring_nf
      _ = 1 := htot₁
      _ = (∑' b : T, (if dm b then out₂ b else 0)) + leftoverTotT dm out₂
          + (∑' a : T, (if dm a then out₁ a else 0)) := htot₂.symm
      _ = leftoverTotT dm out₂ + ((∑' a : T, (if dm a then out₁ a else 0))
          + (∑' b : T, (if dm b then out₂ b else 0))) := by ring_nf
  have hLfin : leftoverTotT dm out₁ ≠ ⊤ := by
    intro h
    rw [show (∑' a : T, (if dm a then out₁ a else 0)) + leftoverTotT dm out₁
        + (∑' b : T, (if dm b then out₂ b else 0))
        = leftoverTotT dm out₁ + ((∑' a : T, (if dm a then out₁ a else 0))
          + (∑' b : T, (if dm b then out₂ b else 0))) by ring_nf,
      h, top_add] at htot₁
    exact ENNReal.top_ne_one htot₁
  have hclos₁ : ∀ a : T,
      (∑' b : T, leftoverT dm out₁ a * leftoverT dm out₂ b / leftoverTotT dm out₁)
        = leftoverT dm out₁ a := by
    intro a
    have hstep : (∑' b : T, leftoverT dm out₁ a * leftoverT dm out₂ b / leftoverTotT dm out₁)
        = leftoverT dm out₁ a * leftoverTotT dm out₂ / leftoverTotT dm out₁ := by
      simp only [div_eq_mul_inv, mul_assoc]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      rfl
    rw [hstep, ← hLeq]
    by_cases hL : leftoverTotT dm out₁ = 0
    · have hz : leftoverT dm out₁ a = 0 := by
        rw [leftoverTotT] at hL
        exact ENNReal.tsum_eq_zero.mp hL a
      rw [hz, zero_mul, ENNReal.zero_div]
    · rw [mul_div_assoc, ENNReal.div_self hL hLfin, mul_one]
  have hclos₂ : ∀ b : T,
      (∑' a : T, leftoverT dm out₁ a * leftoverT dm out₂ b / leftoverTotT dm out₁)
        = leftoverT dm out₂ b := by
    intro b
    have hstep : (∑' a : T, leftoverT dm out₁ a * leftoverT dm out₂ b / leftoverTotT dm out₁)
        = leftoverTotT dm out₁ * leftoverT dm out₂ b / leftoverTotT dm out₁ := by
      simp only [div_eq_mul_inv, mul_assoc]
      rw [ENNReal.tsum_mul_right]
      rfl
    rw [hstep]
    by_cases hL : leftoverTotT dm out₁ = 0
    · have hz : leftoverT dm out₂ b = 0 := by
        rw [hLeq, leftoverTotT] at hL
        exact ENNReal.tsum_eq_zero.mp hL b
      rw [hz, mul_zero, ENNReal.zero_div]
    · rw [mul_comm, mul_div_assoc, ENNReal.div_self hL hLfin, mul_one]
  have hmarg₁ : ∀ a : T, ∑' b : T, cascCouplingT₂ dm sh₁₂ sh₂₁ out₁ out₂ (a, b) = q₁ a := by
    intro a
    simp only [cascCouplingT₂]
    rw [ENNReal.tsum_add, tsum_cascPairT₂_fst, hclos₁ a, ← hout₁ a, leftoverT]
    by_cases ha : dm a
    · rw [if_pos ha, if_pos ha, add_zero]
    · rw [if_neg ha, if_neg ha, zero_add, add_comm]
  have hmarg₂ : ∀ b : T, ∑' a : T, cascCouplingT₂ dm sh₁₂ sh₂₁ out₁ out₂ (a, b) = q₂ b := by
    intro b
    simp only [cascCouplingT₂]
    rw [ENNReal.tsum_add, tsum_cascPairT₂_snd, hclos₂ b, ← hout₂ b, leftoverT]
    by_cases hb : dm b
    · rw [if_pos hb, if_pos hb, add_zero]
    · rw [if_neg hb, if_neg hb, zero_add, add_comm]
  have htotal : ∑' p : T × T, cascCouplingT₂ dm sh₁₂ sh₂₁ out₁ out₂ p = 1 := by
    rw [ENNReal.tsum_prod', ← q₁.tsum_coe]
    exact tsum_congr hmarg₁
  refine ⟨⟨cascCouplingT₂ dm sh₁₂ sh₂₁ out₁ out₂, htotal ▸ ENNReal.summable.hasSum⟩, fun a ↦ ?_,
    fun b ↦ ?_, fun p hp ↦ ?_⟩
  · rw [margFstT]
    exact hmarg₁ a
  · rw [margSndT]
    exact hmarg₂ b
  · by_cases h1 : dm p.1 ∧ sh₂₁ p.1 = p.2
    · exact Or.inl h1
    by_cases h2 : dm p.2 ∧ sh₁₂ p.2 = p.1
    · exact Or.inr (Or.inl h2)
    have hcp : cascPairT₂ dm sh₁₂ sh₂₁ out₁ out₂ p = 0 := by
      rw [cascPairT₂, if_neg h1, if_neg h2, add_zero]
    have hlft : leftoverT dm out₁ p.1 * leftoverT dm out₂ p.2 / leftoverTotT dm out₁ ≠ 0 := by
      intro h0
      exact hp (show cascCouplingT₂ dm sh₁₂ sh₂₁ out₁ out₂ p = 0 by
        rw [cascCouplingT₂, hcp, h0, zero_add])
    refine Or.inr (Or.inr ⟨fun hd ↦ hlft ?_, fun hd ↦ hlft ?_⟩)
    · rw [show leftoverT dm out₁ p.1 = 0 by rw [leftoverT, if_pos hd], zero_mul,
        ENNReal.zero_div]
    · rw [show leftoverT dm out₂ p.2 = 0 by rw [leftoverT, if_pos hd], mul_zero,
        ENNReal.zero_div]

/-- **The coupling read off the cascade** at one shrinking: it charges only the pairs
`(σ, sh σ)` of a source in the domain and the pairs of two atoms outside it. -/
theorem exists_couplingT_of_out (q₁ q₂ : PMF T)
    (hout₁ : ∀ a : T, out₁ a + (∑' τ : {τ : T // dm τ ∧ sh τ = a}, out₂ τ.1) = q₁ a)
    (hout₂ : ∀ b : T, out₂ b + (∑' τ : {τ : T // dm τ ∧ sh τ = b}, out₁ τ.1) = q₂ b) :
    ∃ π : PMF (T × T), (∀ a : T, margFstT π a = q₁ a) ∧
      (∀ b : T, margSndT π b = q₂ b) ∧
      ∀ p : T × T, π p ≠ 0 →
        (dm p.1 ∧ sh p.1 = p.2) ∨ (dm p.2 ∧ sh p.2 = p.1) ∨ (¬ dm p.1 ∧ ¬ dm p.2) :=
  exists_couplingT_of_out₂ (sh₁₂ := sh) (sh₂₁ := sh) q₁ q₂ hout₁ hout₂

/-! ### The two-sided cascade -/

/-- The two-sided domain. -/
def sideDomT (dm : T → Prop) (p : Bool × T) : Prop := dm p.2

/-- The shrinking applied on a side: `sh₁₂` on the second side (`true`), carrying its
atoms to the first, and `sh₂₁` on the first side (`false`), carrying its atoms to the
second. -/
def sideMapT (sh₁₂ sh₂₁ : T → T) : Bool → T → T
  | true => sh₁₂
  | false => sh₂₁

@[simp] lemma sideMapT_true (sh₁₂ sh₂₁ : T → T) : sideMapT sh₁₂ sh₂₁ true = sh₁₂ := rfl

@[simp] lemma sideMapT_false (sh₁₂ sh₂₁ : T → T) : sideMapT sh₁₂ sh₂₁ false = sh₂₁ := rfl

/-- The two-sided shrinking at two maps: it carries an atom of one side to an atom of the
other, by the map of the side it starts from. -/
def sideShrinkT₂ (sh₁₂ sh₂₁ : T → T) (p : Bool × T) : Bool × T :=
  (!p.1, sideMapT sh₁₂ sh₂₁ p.1 p.2)

/-- The two-sided shrinking at one map: it carries an atom of one side to an atom of the
other. -/
def sideShrinkT (sh : T → T) (p : Bool × T) : Bool × T := (!p.1, sh p.2)

lemma sideShrinkT_eq (sh : T → T) : sideShrinkT sh = sideShrinkT₂ sh sh := by
  funext p
  obtain ⟨i, a⟩ := p
  cases i <;> rfl

/-- The two-sided mass: the first law on one side, the second on the other. -/
noncomputable def sideMassT (q₁ q₂ : PMF T) (p : Bool × T) : ℝ≥0∞ :=
  if p.1 then q₂ p.2 else q₁ p.2

lemma sideMassT_ne_top (q₁ q₂ : PMF T) (p : Bool × T) : sideMassT q₁ q₂ p ≠ ⊤ := by
  rw [sideMassT]
  by_cases hp : p.1 = true
  · rw [if_pos hp]; exact PMF.apply_ne_top _ _
  · rw [if_neg hp]; exact PMF.apply_ne_top _ _

@[simp] lemma sideMassT_false (q₁ q₂ : PMF T) (a : T) :
    sideMassT q₁ q₂ (false, a) = q₁ a := by
  rw [sideMassT]; simp

@[simp] lemma sideMassT_true (q₁ q₂ : PMF T) (a : T) :
    sideMassT q₁ q₂ (true, a) = q₂ a := by
  rw [sideMassT]; simp

/-- A point of a fibre of the two-sided shrinking sits on the other side. -/
lemma fst_of_mem_sideFibreT₂ {sh₁₂ sh₂₁ : T → T} {i : Bool} {a : T}
    {ρ : Bool × T} (h : sideShrinkT₂ sh₁₂ sh₂₁ ρ = (i, a)) : ρ.1 = !i := by
  have h1 : (!ρ.1) = i := congrArg Prod.fst h
  cases hb : ρ.1 <;> cases hi : i <;> simp_all

/-- A point of a fibre of the two-sided shrinking at one map sits on the other side. -/
lemma fst_of_mem_sideFibreT {sh : T → T} {i : Bool} {a : T}
    {ρ : Bool × T} (h : sideShrinkT sh ρ = (i, a)) : ρ.1 = !i :=
  fst_of_mem_sideFibreT₂ (by rwa [sideShrinkT_eq] at h)

/-- The fibre of the two-sided shrinking over an atom of one side is the fibre, read on
the other side, of the map of that side. -/
def sideFibreEquivT₂ (dm : T → Prop) (sh₁₂ sh₂₁ : T → T) (i : Bool) (a : T) :
    {τ : T // dm τ ∧ sideMapT sh₁₂ sh₂₁ (!i) τ = a}
      ≃ {ρ : Bool × T // sideDomT dm ρ ∧ sideShrinkT₂ sh₁₂ sh₂₁ ρ = (i, a)} where
  toFun τ := ⟨(!i, τ.1), τ.2.1, by rw [sideShrinkT₂, Bool.not_not, τ.2.2]⟩
  invFun ρ := ⟨ρ.1.2, ρ.2.1, by
    have h1 : sideMapT sh₁₂ sh₂₁ ρ.1.1 ρ.1.2 = a := congrArg Prod.snd ρ.2.2
    rwa [fst_of_mem_sideFibreT₂ ρ.2.2] at h1⟩
  left_inv _ := rfl
  right_inv ρ := by
    refine Subtype.ext (Prod.ext_iff.mpr ⟨?_, rfl⟩)
    exact (fst_of_mem_sideFibreT₂ ρ.2.2).symm

/-- A sum over the fibre of the two-sided shrinking, read on the other side. -/
lemma tsum_sideFibreT₂ (dm : T → Prop) (sh₁₂ sh₂₁ : T → T) (i : Bool) (a : T)
    (f : Bool × T → ℝ≥0∞) :
    (∑' ρ : {ρ : Bool × T // sideDomT dm ρ ∧ sideShrinkT₂ sh₁₂ sh₂₁ ρ = (i, a)}, f ρ.1)
      = ∑' τ : {τ : T // dm τ ∧ sideMapT sh₁₂ sh₂₁ (!i) τ = a}, f (!i, τ.1) := by
  refine ((sideFibreEquivT₂ dm sh₁₂ sh₂₁ i a).tsum_eq fun ρ ↦ f ρ.1).symm.trans
    (tsum_congr fun τ ↦ ?_)
  rfl

/-- The fibre of the two-sided shrinking at one map over an atom of one side is the
fibre of the shrinking read on the other side. -/
def sideFibreEquivT (dm : T → Prop) (sh : T → T) (i : Bool) (a : T) :
    {τ : T // dm τ ∧ sh τ = a}
      ≃ {ρ : Bool × T // sideDomT dm ρ ∧ sideShrinkT sh ρ = (i, a)} where
  toFun τ := ⟨(!i, τ.1), τ.2.1, by rw [sideShrinkT, Bool.not_not, τ.2.2]⟩
  invFun ρ := ⟨ρ.1.2, ρ.2.1, (congrArg Prod.snd ρ.2.2 : sh ρ.1.2 = a)⟩
  left_inv _ := rfl
  right_inv ρ := by
    refine Subtype.ext (Prod.ext_iff.mpr ⟨?_, rfl⟩)
    exact (fst_of_mem_sideFibreT ρ.2.2).symm

/-- A sum over the fibre of the two-sided shrinking at one map, read on the other
side. -/
lemma tsum_sideFibreT (dm : T → Prop) (sh : T → T) (i : Bool) (a : T)
    (f : Bool × T → ℝ≥0∞) :
    (∑' ρ : {ρ : Bool × T // sideDomT dm ρ ∧ sideShrinkT sh ρ = (i, a)}, f ρ.1)
      = ∑' τ : {τ : T // dm τ ∧ sh τ = a}, f (!i, τ.1) := by
  refine ((sideFibreEquivT dm sh i a).tsum_eq fun ρ ↦ f ρ.1).symm.trans
    (tsum_congr fun τ ↦ ?_)
  rfl

/-- **`eq:capacity` on the two sides**, at two shrinkings. -/
lemma capacity_sideMassT₂ {q₁ q₂ : PMF T} {dm : T → Prop} {sh₁₂ sh₂₁ : T → T}
    (hcap₁ : ∀ a : T, (∑' τ : {τ : T // dm τ ∧ sh₁₂ τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : T, (∑' τ : {τ : T // dm τ ∧ sh₂₁ τ = b}, q₁ τ.1) ≤ q₂ b / 2)
    (p : Bool × T) :
    (∑' ρ : {ρ : Bool × T // sideDomT dm ρ ∧ sideShrinkT₂ sh₁₂ sh₂₁ ρ = p},
        sideMassT q₁ q₂ ρ.1)
      ≤ sideMassT q₁ q₂ p / 2 := by
  obtain ⟨i, a⟩ := p
  rw [tsum_sideFibreT₂ dm sh₁₂ sh₂₁ i a (sideMassT q₁ q₂)]
  cases i with
  | false =>
      simp only [Bool.not_false, sideMassT_true, sideMassT_false]
      exact hcap₁ a
  | true =>
      simp only [Bool.not_true, sideMassT_true, sideMassT_false]
      exact hcap₂ a

/-- **`eq:capacity` on the two sides.** -/
lemma capacity_sideMassT {q₁ q₂ : PMF T} {dm : T → Prop} {sh : T → T}
    (hcap₁ : ∀ a : T, (∑' τ : {τ : T // dm τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : T, (∑' τ : {τ : T // dm τ ∧ sh τ = b}, q₁ τ.1) ≤ q₂ b / 2)
    (p : Bool × T) :
    (∑' ρ : {ρ : Bool × T // sideDomT dm ρ ∧ sideShrinkT sh ρ = p}, sideMassT q₁ q₂ ρ.1)
      ≤ sideMassT q₁ q₂ p / 2 := by
  rw [sideShrinkT_eq]
  exact capacity_sideMassT₂ hcap₁ hcap₂ p

/-- The levels of the two-sided cascade at two shrinkings. -/
noncomputable def sideLevelsT₂ (q₁ q₂ : PMF T) (dm : T → Prop) (sh₁₂ sh₂₁ : T → T) :
    Bool × T → ℕ → ℝ :=
  fun σ k ↦
    (cascMassE (sideDomT dm) (sideShrinkT₂ sh₁₂ sh₂₁) (sideMassT q₁ q₂) k σ).toReal

/-- The mass a side sends out, at two shrinkings. -/
noncomputable def sideOutT₂ (q₁ q₂ : PMF T) (dm : T → Prop) (sh₁₂ sh₂₁ : T → T)
    (i : Bool) (a : T) : ℝ≥0∞ :=
  ENNReal.ofReal (cascadeOut (sideLevelsT₂ q₁ q₂ dm sh₁₂ sh₂₁) (i, a))

/-- The levels of the two-sided cascade. -/
noncomputable def sideLevelsT (q₁ q₂ : PMF T) (dm : T → Prop) (sh : T → T) :
    Bool × T → ℕ → ℝ :=
  fun σ k ↦ (cascMassE (sideDomT dm) (sideShrinkT sh) (sideMassT q₁ q₂) k σ).toReal

/-- The mass a side sends out. -/
noncomputable def sideOutT (q₁ q₂ : PMF T) (dm : T → Prop) (sh : T → T)
    (i : Bool) (a : T) : ℝ≥0∞ :=
  ENNReal.ofReal (cascadeOut (sideLevelsT q₁ q₂ dm sh) (i, a))

lemma sideLevelsT_eq (q₁ q₂ : PMF T) (dm : T → Prop) (sh : T → T) :
    sideLevelsT q₁ q₂ dm sh = sideLevelsT₂ q₁ q₂ dm sh sh := by
  delta sideLevelsT sideLevelsT₂
  rw [sideShrinkT_eq]

lemma sideOutT_eq (q₁ q₂ : PMF T) (dm : T → Prop) (sh : T → T) :
    sideOutT q₁ q₂ dm sh = sideOutT₂ q₁ q₂ dm sh sh := by
  funext i a
  rw [sideOutT, sideOutT₂, sideLevelsT_eq]

/-- **A source atom spends its full mass**, at two shrinkings: what it sends out and
what the fibre of the map of the other side sends in add up to its mass. -/
theorem sideOutT₂_add_tsum_sideOutT₂ {q₁ q₂ : PMF T} {dm : T → Prop} {sh₁₂ sh₂₁ : T → T}
    (hcap₁ : ∀ a : T, (∑' τ : {τ : T // dm τ ∧ sh₁₂ τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : T, (∑' τ : {τ : T // dm τ ∧ sh₂₁ τ = b}, q₁ τ.1) ≤ q₂ b / 2)
    (i : Bool) (a : T) :
    sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ i a
        + (∑' τ : {τ : T // dm τ ∧ sideMapT sh₁₂ sh₂₁ (!i) τ = a},
            sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ (!i) τ.1)
      = sideMassT q₁ q₂ (i, a) := by
  have hcasc : IsCascadeOn (sideDomT dm) (sideShrinkT₂ sh₁₂ sh₂₁)
      (sideLevelsT₂ q₁ q₂ dm sh₁₂ sh₂₁) :=
    isCascadeOn_cascMass (sideMassT_ne_top q₁ q₂) (capacity_sideMassT₂ hcap₁ hcap₂)
  have hsum := hcasc.cascadeOut_add_cascadeInOn (i, a)
  have hin : ENNReal.ofReal
      (cascadeInOn (sideDomT dm) (sideShrinkT₂ sh₁₂ sh₂₁)
        (sideLevelsT₂ q₁ q₂ dm sh₁₂ sh₂₁) (i, a))
        = ∑' τ : {τ : T // dm τ ∧ sideMapT sh₁₂ sh₂₁ (!i) τ = a},
            sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ (!i) τ.1 := by
    rw [cascadeInOn]
    rw [ENNReal.ofReal_tsum_of_nonneg
      (f := fun ρ : {ρ : Bool × T // sideDomT dm ρ ∧ sideShrinkT₂ sh₁₂ sh₂₁ ρ = (i, a)} ↦
        cascadeOut (sideLevelsT₂ q₁ q₂ dm sh₁₂ sh₂₁) ρ.1)
      (fun ρ ↦ hcasc.toHalvingLevels.cascadeOut_nonneg ρ.1)
      (hcasc.summable_fibre_cascadeOut (i, a))]
    exact tsum_sideFibreT₂ dm sh₁₂ sh₂₁ i a
      (fun ρ ↦ ENNReal.ofReal (cascadeOut (sideLevelsT₂ q₁ q₂ dm sh₁₂ sh₂₁) ρ))
  have hzero : sideLevelsT₂ q₁ q₂ dm sh₁₂ sh₂₁ (i, a) 0
      = (sideMassT q₁ q₂ (i, a)).toReal := by
    simp only [sideLevelsT₂, cascMassE_zero]
  rw [sideOutT₂, ← hin, ← ENNReal.ofReal_add (hcasc.toHalvingLevels.cascadeOut_nonneg (i, a))
    (hcasc.cascadeInOn_nonneg (i, a)), hsum, hzero]
  exact ENNReal.ofReal_toReal (sideMassT_ne_top q₁ q₂ (i, a))

/-- **A source atom spends its full mass**, in the form the coupling reads. -/
theorem sideOutT_add_tsum_sideOutT {q₁ q₂ : PMF T} {dm : T → Prop} {sh : T → T}
    (hcap₁ : ∀ a : T, (∑' τ : {τ : T // dm τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : T, (∑' τ : {τ : T // dm τ ∧ sh τ = b}, q₁ τ.1) ≤ q₂ b / 2)
    (i : Bool) (a : T) :
    sideOutT q₁ q₂ dm sh i a
        + (∑' τ : {τ : T // dm τ ∧ sh τ = a}, sideOutT q₁ q₂ dm sh (!i) τ.1)
      = sideMassT q₁ q₂ (i, a) := by
  rw [sideOutT_eq]
  cases i
  · exact sideOutT₂_add_tsum_sideOutT₂ hcap₁ hcap₂ false a
  · exact sideOutT₂_add_tsum_sideOutT₂ hcap₁ hcap₂ true a

/-- **The coupling of two laws with a capacity bound at two shrinkings**, at an arbitrary
type: `sh₁₂` carries the atoms of the second law into the support of the first, `sh₂₁`
those of the first into the support of the second, each fibre carrying at most half of
the mass of its target. -/
theorem exists_couplingT_of_capacity₂ (q₁ q₂ : PMF T) (dm : T → Prop) (sh₁₂ sh₂₁ : T → T)
    (hcap₁ : ∀ a : T, (∑' τ : {τ : T // dm τ ∧ sh₁₂ τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : T, (∑' τ : {τ : T // dm τ ∧ sh₂₁ τ = b}, q₁ τ.1) ≤ q₂ b / 2) :
    ∃ π : PMF (T × T), (∀ a : T, margFstT π a = q₁ a) ∧
      (∀ b : T, margSndT π b = q₂ b) ∧
      ∀ p : T × T, π p ≠ 0 →
        (dm p.1 ∧ sh₂₁ p.1 = p.2) ∨ (dm p.2 ∧ sh₁₂ p.2 = p.1) ∨ (¬ dm p.1 ∧ ¬ dm p.2) := by
  have hout₁ : ∀ a : T, sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ false a
      + (∑' τ : {τ : T // dm τ ∧ sh₁₂ τ = a}, sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ true τ.1)
      = q₁ a := by
    intro a
    have h := sideOutT₂_add_tsum_sideOutT₂ hcap₁ hcap₂ false a
    rw [sideMassT_false] at h
    exact h
  have hout₂ : ∀ b : T, sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ true b
      + (∑' τ : {τ : T // dm τ ∧ sh₂₁ τ = b}, sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ false τ.1)
      = q₂ b := by
    intro b
    have h := sideOutT₂_add_tsum_sideOutT₂ hcap₁ hcap₂ true b
    rw [sideMassT_true] at h
    exact h
  exact exists_couplingT_of_out₂ (dm := dm) (sh₁₂ := sh₁₂) (sh₂₁ := sh₂₁)
    (out₁ := sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ false) (out₂ := sideOutT₂ q₁ q₂ dm sh₁₂ sh₂₁ true)
    q₁ q₂ hout₁ hout₂

/-- **The coupling of two laws with a capacity bound**, at an arbitrary type. -/
theorem exists_couplingT_of_capacity (q₁ q₂ : PMF T) (dm : T → Prop) (sh : T → T)
    (hcap₁ : ∀ a : T, (∑' τ : {τ : T // dm τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : T, (∑' τ : {τ : T // dm τ ∧ sh τ = b}, q₁ τ.1) ≤ q₂ b / 2) :
    ∃ π : PMF (T × T), (∀ a : T, margFstT π a = q₁ a) ∧
      (∀ b : T, margSndT π b = q₂ b) ∧
      ∀ p : T × T, π p ≠ 0 →
        (dm p.1 ∧ sh p.1 = p.2) ∨ (dm p.2 ∧ sh p.2 = p.1) ∨ (¬ dm p.1 ∧ ¬ dm p.2) :=
  exists_couplingT_of_capacity₂ q₁ q₂ dm sh sh hcap₁ hcap₂

end Coupling

/-! ### `eq:capacity` from the mass bounds, at an abstract size -/

/-- **`eq:capacity`, small targets, at a threshold `K`.** For `|τ| ≤ K` the fibre sits
above the cut, so its mass is at most `e^{-y}`, which the largeness condition
`log 2 + K c⋆ ≤ y` turns into half of the point mass `e^{-c⋆|τ|}` of `τ`. -/
lemma capacity_small_const {cs x mfib mtau y K : ℝ} (hcs : 0 ≤ cs) (hx : x ≤ K)
    (htau : Real.exp (-(cs * x)) ≤ mtau) (hfib : mfib ≤ Real.exp (-y))
    (hy : Real.log 2 + K * cs ≤ y) : mfib ≤ mtau / 2 := by
  have h1 : Real.exp (-y) ≤ Real.exp (-(Real.log 2 + K * cs)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(Real.log 2 + K * cs)) = Real.exp (-(K * cs)) / 2 := by
    rw [show -(Real.log 2 + K * cs) = -(K * cs) + -Real.log 2 by ring, Real.exp_add,
      show -Real.log 2 = Real.log (2 : ℝ)⁻¹ by rw [Real.log_inv],
      Real.exp_log (by norm_num)]
    ring
  have h3 : Real.exp (-(K * cs)) ≤ Real.exp (-(cs * x)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hx hcs])
  rw [h2] at h1
  linarith

/-- **`eq:capacity`, large targets, at a threshold `K`.** For `|τ| > K` the fibre mass is
at most `e^{-r|τ|}`, which the largeness condition `log 2/K + c⋆ ≤ r` turns into half of
`e^{-c⋆|τ|}`. -/
lemma capacity_large_const {cs r x mfib mtau K : ℝ} (hK : 0 < K) (hx : K < x)
    (htau : Real.exp (-(cs * x)) ≤ mtau) (hfib : mfib ≤ Real.exp (-(r * x)))
    (hr : Real.log 2 / K + cs ≤ r) : mfib ≤ mtau / 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hgap : Real.log 2 ≤ (r - cs) * x := by
    have h1 : Real.log 2 / K ≤ r - cs := by linarith
    have h2 : Real.log 2 ≤ (r - cs) * K := by rwa [div_le_iff₀ hK] at h1
    have h3 : (r - cs) * K ≤ (r - cs) * x :=
      mul_le_mul_of_nonneg_left hx.le (by linarith [div_pos hlog2 hK])
    linarith
  have h1 : Real.exp (-(r * x)) ≤ Real.exp (-(cs * x)) / 2 := by
    have h2 : Real.exp (-(r * x)) * 2 ≤ Real.exp (-(cs * x)) := by
      have hstep : Real.exp (-(r * x)) * Real.exp (Real.log 2) ≤ Real.exp (-(cs * x)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at hstep
    linarith
  linarith

/-- **`eq:capacity` at an abstract size, support and shrinking, at the shrinking
constant `C`**: with `|sh τ| ≤ C(|τ|/s + 1)`, the fibre of a target `a` sits above the
size `max(Ncut, s|a|/(4C))`, where an exponential tail for the source law and a point
bound for the target law meet, at the two largeness conditions `hsmall` and `hlarge`:
`log 2 + 4C log p⁻¹ ≤ c Ncut` and `log 2/(4C) + log p⁻¹ ≤ cs/(4C)`. -/
theorem capacity_of_mass_boundsT_const {q₁ q₂ : T → ℝ≥0∞} {size : T → ℕ}
    {Supp : T → Prop} {sh : T → T} {p c : ℝ} {C n₀ s Ncut : ℕ}
    (hC : 1 ≤ C) (hs : 1 ≤ s) (hp0 : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c)
    (hsupp : ∀ τ : T, Supp (sh τ))
    (hshsize : ∀ τ : T, size (sh τ) ≤ C * (size τ / s + 1))
    (hpoint : ∀ a : T, Supp a → ENNReal.ofReal (p ^ size a) ≤ q₁ a)
    (htail : ∀ m : ℕ, n₀ ≤ m →
      (∑' y : T, if size y ≤ m then 0 else q₂ y) ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))))
    (hn₀ : n₀ ≤ Ncut)
    (hsmall : Real.log 2 + 4 * (C : ℝ) * Real.log p⁻¹ ≤ c * (Ncut : ℝ))
    (hlarge : Real.log 2 / (4 * (C : ℝ)) + Real.log p⁻¹ ≤ c * (s : ℝ) / (4 * (C : ℝ)))
    (a : T) :
    (∑' τ : {τ : T // Ncut < size τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2 := by
  by_cases ha : Supp a
  swap
  · have hempty : IsEmpty {τ : T // Ncut < size τ ∧ sh τ = a} :=
      ⟨fun τ ↦ ha (τ.2.2 ▸ hsupp τ.1)⟩
    rw [tsum_empty]
    exact bot_le
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hC0 : 0 < C := hC
  have hC1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hC0r : (0 : ℝ) < (C : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log p⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hp0, hp1⟩)
  set k : ℕ := size a with hk
  set j : ℕ := (k - C) / C with hj
  set m : ℕ := max Ncut (s * j - 1) with hm
  have hmN : Ncut ≤ m := le_max_left _ _
  have hmc : (Ncut : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmN
  have hfibsize : ∀ τ : T, Ncut < size τ → sh τ = a → m < size τ := by
    intro τ hτ hsh
    have hsize : k ≤ C * (size τ / s) + C := by
      rw [hk, ← hsh]
      have := hshsize τ
      rwa [mul_add, mul_one] at this
    have hdiv : j ≤ size τ / s := by
      have h1 : k - C ≤ C * (size τ / s) := Nat.sub_le_of_le_add hsize
      have h2 : (k - C) / C ≤ (C * (size τ / s)) / C := Nat.div_le_div_right h1
      rwa [Nat.mul_div_cancel_left _ hC0] at h2
    have hsj : s * j ≤ size τ :=
      le_trans (Nat.mul_le_mul_left s hdiv)
        (by rw [mul_comm]; exact Nat.div_mul_le_self (size τ) s)
    exact max_lt hτ (by omega)
  have hfibmass : (∑' τ : {τ : T // Ncut < size τ ∧ sh τ = a}, q₂ τ.1)
      ≤ ∑' y : T, (if size y ≤ m then 0 else q₂ y) := by
    refine le_trans (le_of_eq (tsum_subtype {τ : T | Ncut < size τ ∧ sh τ = a} _))
      (ENNReal.tsum_le_tsum fun y ↦ ?_)
    by_cases hy : Ncut < size y ∧ sh y = a
    · rw [Set.indicator_of_mem (show y ∈ {τ : T | Ncut < size τ ∧ sh τ = a} from hy),
        if_neg (by have := hfibsize y hy.1 hy.2; omega)]
    · rw [Set.indicator_of_notMem
        (show y ∉ {τ : T | Ncut < size τ ∧ sh τ = a} from hy)]
      exact bot_le
  have hpk : p ^ k = Real.exp (-(Real.log p⁻¹ * (k : ℝ))) := pow_eq_exp_neg_log_inv hp0 k
  have hreal : Real.exp (-c * (m : ℝ)) ≤ p ^ k / 2 := by
    by_cases hkl : (k : ℝ) ≤ 4 * (C : ℝ)
    · refine capacity_small_const (cs := Real.log p⁻¹) (x := (k : ℝ)) (K := 4 * (C : ℝ))
        (mfib := Real.exp (-c * (m : ℝ))) (mtau := p ^ k) (y := c * (m : ℝ))
        hlogp hkl (le_of_eq hpk.symm) (le_of_eq (by rw [neg_mul])) ?_
      linarith [mul_le_mul_of_nonneg_left hmc hc.le]
    · replace hkl : 4 * (C : ℝ) < (k : ℝ) := not_le.mp hkl
      have hk4 : 4 * C < k := by exact_mod_cast hkl
      have hCj : (C : ℝ) * (j : ℝ) > (k : ℝ) - 2 * (C : ℝ) := by
        have hlt : k - C < C * j + C := by
          have := Nat.lt_mul_div_succ (k - C) hC0
          rwa [mul_add, mul_one] at this
        have hcast : ((k : ℝ) - (C : ℝ)) < (C : ℝ) * (j : ℝ) + (C : ℝ) := by
          have h1 : ((k - C : ℕ) : ℝ) = (k : ℝ) - (C : ℝ) := by
            rw [Nat.cast_sub (by omega)]
          have h2 : ((k - C : ℕ) : ℝ) < ((C * j + C : ℕ) : ℝ) := by exact_mod_cast hlt
          rw [h1] at h2
          push_cast at h2
          linarith
        linarith
      have hj1 : 1 ≤ j := (Nat.one_le_div_iff hC0).mpr (by omega)
      have hmj : ((s * j - 1 : ℕ) : ℝ) = (s : ℝ) * (j : ℝ) - 1 := by
        have hsj1 : 1 ≤ s * j := Nat.one_le_iff_ne_zero.mpr (by positivity)
        rw [Nat.cast_sub hsj1]
        norm_num
      have hmge : (s : ℝ) * (j : ℝ) - 1 ≤ (m : ℝ) := by
        have hle : ((s * j - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast le_max_right Ncut (s * j - 1)
        rw [hmj] at hle
        linarith
      have hkey : (s : ℝ) * (k : ℝ) / (4 * (C : ℝ)) ≤ (m : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : (s : ℝ) * ((k : ℝ) - 2 * (C : ℝ)) < (s : ℝ) * ((C : ℝ) * (j : ℝ)) :=
          mul_lt_mul_of_pos_left hCj hs0
        have h2 : 4 * (C : ℝ) * ((s : ℝ) * (j : ℝ) - 1) ≤ 4 * (C : ℝ) * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hmge (by positivity)
        have h3 : (s : ℝ) * (4 * (C : ℝ)) < (s : ℝ) * (k : ℝ) :=
          mul_lt_mul_of_pos_left hkl hs0
        have h4 : (C : ℝ) ≤ (s : ℝ) * (C : ℝ) := le_mul_of_one_le_left hC0r.le hs1
        nlinarith
      refine capacity_large_const (cs := Real.log p⁻¹) (r := c * (s : ℝ) / (4 * (C : ℝ)))
        (x := (k : ℝ)) (K := 4 * (C : ℝ)) (mfib := Real.exp (-c * (m : ℝ))) (mtau := p ^ k)
        (by positivity) hkl (le_of_eq hpk.symm) ?_ hlarge
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left hkey hc.le
      rw [show c * (s : ℝ) / (4 * (C : ℝ)) * (k : ℝ)
        = c * ((s : ℝ) * (k : ℝ) / (4 * (C : ℝ))) by ring]
      linarith
  refine le_trans (le_trans hfibmass (htail m (le_trans hn₀ hmN))) ?_
  calc ENNReal.ofReal (Real.exp (-c * (m : ℝ)))
      ≤ ENNReal.ofReal (p ^ k / 2) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (p ^ k) / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
    _ ≤ q₁ a / 2 := by gcongr; exact hpoint a ha

/-- **`eq:capacity` at an abstract size, support and shrinking**: the case `C = 16` of
`capacity_of_mass_boundsT_const`, the fibre of a target sitting above the size
`max(Ncut, s|τ|/64)`, at the two largeness conditions `hsmall` and `hlarge`. -/
theorem capacity_of_mass_boundsT {q₁ q₂ : T → ℝ≥0∞} {size : T → ℕ}
    {Supp : T → Prop} {sh : T → T} {p c : ℝ} {n₀ s Ncut : ℕ}
    (hs : 1 ≤ s) (hp0 : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c)
    (hsupp : ∀ τ : T, Supp (sh τ))
    (hshsize : ∀ τ : T, size (sh τ) ≤ 16 * (size τ / s + 1))
    (hpoint : ∀ a : T, Supp a → ENNReal.ofReal (p ^ size a) ≤ q₁ a)
    (htail : ∀ m : ℕ, n₀ ≤ m →
      (∑' y : T, if size y ≤ m then 0 else q₂ y) ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))))
    (hn₀ : n₀ ≤ Ncut)
    (hsmall : Real.log 2 + 64 * Real.log p⁻¹ ≤ c * (Ncut : ℝ))
    (hlarge : Real.log 2 / 64 + Real.log p⁻¹ ≤ c * (s : ℝ) / 64)
    (a : T) :
    (∑' τ : {τ : T // Ncut < size τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2 := by
  have h64 : (4 * ((16 : ℕ) : ℝ)) = 64 := by norm_num
  refine capacity_of_mass_boundsT_const (C := 16) (by norm_num) hs hp0 hp1 hc hsupp hshsize
    hpoint htail hn₀ ?_ ?_ a
  · rw [h64]; exact hsmall
  · rw [h64]; exact hlarge

/-! ### The coupling of `thm:relabel` -/

/-- **The coupling of `thm:relabel` at general shapes**: a law on pairs whose marginals
are the two laws and which charges only `9D³`-comparable pairs of the marked
realisations. -/
structure IsGShapeCoupling (Dq : ℝ) (q₁ q₂ : PMF GShape) (π : PMF (GShape × GShape)) :
    Prop where
  /-- The first marginal. -/
  marg₁ : ∀ a : GShape, margFstT π a = q₁ a
  /-- The second marginal. -/
  marg₂ : ∀ b : GShape, margSndT π b = q₂ b
  /-- A charged pair is comparable. -/
  qi : ∀ p : GShape × GShape, π p ≠ 0 →
    MarkedQI (9 * Dq ^ 3) (gShapeSpace p.1) (gShapeSpace p.2)
  /-- A charged pair is comparable the other way. -/
  qi' : ∀ p : GShape × GShape, π p ≠ 0 →
    MarkedQI (9 * Dq ^ 3) (gShapeSpace p.2) (gShapeSpace p.1)

/-- **The coupling of two general shape laws with a capacity bound at two shrinkings**:
the cascade coupling is supported on the cascade pairs and the small pairs, so the
comparability of those two kinds of pairs makes it an `IsGShapeCoupling`.  The
comparabilities enter as hypotheses: the cascade pairs `(σ, sh₂₁ σ)` and `(sh₁₂ σ, σ)`
through the two shrinkings of the general shapes, the small pairs through the collapse,
all at `9D³`. -/
theorem exists_gShapeCoupling_of_capacity₂ {Dq : ℝ} {q₁ q₂ : PMF GShape}
    (dm : GShape → Prop) (sh₁₂ sh₂₁ : GShape → GShape)
    (hpair₁ : ∀ σ : GShape, dm σ →
      MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace (sh₂₁ σ))
        ∧ MarkedQI (9 * Dq ^ 3) (gShapeSpace (sh₂₁ σ)) (gShapeSpace σ))
    (hpair₂ : ∀ σ : GShape, dm σ →
      MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace (sh₁₂ σ))
        ∧ MarkedQI (9 * Dq ^ 3) (gShapeSpace (sh₁₂ σ)) (gShapeSpace σ))
    (hsmall : ∀ σ τ : GShape, ¬ dm σ → ¬ dm τ →
      MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace τ))
    (hcap₁ : ∀ a : GShape,
      (∑' τ : {τ : GShape // dm τ ∧ sh₁₂ τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : GShape,
      (∑' τ : {τ : GShape // dm τ ∧ sh₂₁ τ = b}, q₁ τ.1) ≤ q₂ b / 2) :
    ∃ π : PMF (GShape × GShape), IsGShapeCoupling Dq q₁ q₂ π := by
  obtain ⟨π, hm₁, hm₂, hsupp⟩ :=
    exists_couplingT_of_capacity₂ q₁ q₂ dm sh₁₂ sh₂₁ hcap₁ hcap₂
  refine ⟨π, hm₁, hm₂, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rcases hsupp p hp with ⟨hd, hsh⟩ | ⟨hd, hsh⟩ | ⟨h1, h2⟩
    · rw [← hsh]
      exact (hpair₁ p.1 hd).1
    · rw [← hsh]
      exact (hpair₂ p.2 hd).2
    · exact hsmall p.1 p.2 h1 h2
  · rcases hsupp p hp with ⟨hd, hsh⟩ | ⟨hd, hsh⟩ | ⟨h1, h2⟩
    · rw [← hsh]
      exact (hpair₁ p.1 hd).2
    · rw [← hsh]
      exact (hpair₂ p.2 hd).1
    · exact hsmall p.2 p.1 h2 h1

/-- **The coupling of two general shape laws with a capacity bound**: the case of one
shrinking serving both sides, the cascade pairs entering through it and the small pairs
through the collapse, both at `9D³`. -/
theorem exists_gShapeCoupling_of_capacity {Dq : ℝ} {q₁ q₂ : PMF GShape}
    (dm : GShape → Prop) (sh : GShape → GShape)
    (hpair : ∀ σ : GShape, dm σ →
      MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace (sh σ))
        ∧ MarkedQI (9 * Dq ^ 3) (gShapeSpace (sh σ)) (gShapeSpace σ))
    (hsmall : ∀ σ τ : GShape, ¬ dm σ → ¬ dm τ →
      MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace τ))
    (hcap₁ : ∀ a : GShape,
      (∑' τ : {τ : GShape // dm τ ∧ sh τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : GShape,
      (∑' τ : {τ : GShape // dm τ ∧ sh τ = b}, q₁ τ.1) ≤ q₂ b / 2) :
    ∃ π : PMF (GShape × GShape), IsGShapeCoupling Dq q₁ q₂ π :=
  exists_gShapeCoupling_of_capacity₂ dm sh sh hpair hpair hsmall hcap₁ hcap₂

/-- **The coupling of two general shape laws with a capacity bound at two shrinkings,
the comparabilities asked of the charged shapes only**: a charged pair of the cascade
coupling has both components charged by their laws, each pair being bounded by its two
marginals, so the comparability of the cascade pairs and of the small pairs is needed at
the shapes of positive mass alone. -/
theorem exists_gShapeCoupling_of_capacity₂' {Dq : ℝ} {q₁ q₂ : PMF GShape}
    (dm : GShape → Prop) (sh₁₂ sh₂₁ : GShape → GShape)
    (hpair₁ : ∀ σ : GShape, dm σ → q₁ σ ≠ 0 →
      MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace (sh₂₁ σ))
        ∧ MarkedQI (9 * Dq ^ 3) (gShapeSpace (sh₂₁ σ)) (gShapeSpace σ))
    (hpair₂ : ∀ σ : GShape, dm σ → q₂ σ ≠ 0 →
      MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace (sh₁₂ σ))
        ∧ MarkedQI (9 * Dq ^ 3) (gShapeSpace (sh₁₂ σ)) (gShapeSpace σ))
    (hsmall : ∀ σ τ : GShape, ¬ dm σ → ¬ dm τ → q₁ σ ≠ 0 → q₂ τ ≠ 0 →
      MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace τ)
        ∧ MarkedQI (9 * Dq ^ 3) (gShapeSpace τ) (gShapeSpace σ))
    (hcap₁ : ∀ a : GShape,
      (∑' τ : {τ : GShape // dm τ ∧ sh₁₂ τ = a}, q₂ τ.1) ≤ q₁ a / 2)
    (hcap₂ : ∀ b : GShape,
      (∑' τ : {τ : GShape // dm τ ∧ sh₂₁ τ = b}, q₁ τ.1) ≤ q₂ b / 2) :
    ∃ π : PMF (GShape × GShape), IsGShapeCoupling Dq q₁ q₂ π := by
  obtain ⟨π, hm₁, hm₂, hsupp⟩ :=
    exists_couplingT_of_capacity₂ q₁ q₂ dm sh₁₂ sh₂₁ hcap₁ hcap₂
  have hq₁ : ∀ p : GShape × GShape, π p ≠ 0 → q₁ p.1 ≠ 0 := by
    intro p hp h0
    refine hp (le_antisymm ?_ bot_le)
    rw [← h0, ← hm₁ p.1]
    exact le_margFstT π p.1 p.2
  have hq₂ : ∀ p : GShape × GShape, π p ≠ 0 → q₂ p.2 ≠ 0 := by
    intro p hp h0
    refine hp (le_antisymm ?_ bot_le)
    rw [← h0, ← hm₂ p.2]
    exact le_margSndT π p.1 p.2
  refine ⟨π, hm₁, hm₂, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rcases hsupp p hp with ⟨hd, hsh⟩ | ⟨hd, hsh⟩ | ⟨h1, h2⟩
    · rw [← hsh]
      exact (hpair₁ p.1 hd (hq₁ p hp)).1
    · rw [← hsh]
      exact (hpair₂ p.2 hd (hq₂ p hp)).2
    · exact (hsmall p.1 p.2 h1 h2 (hq₁ p hp) (hq₂ p hp)).1
  · rcases hsupp p hp with ⟨hd, hsh⟩ | ⟨hd, hsh⟩ | ⟨h1, h2⟩
    · rw [← hsh]
      exact (hpair₁ p.1 hd (hq₁ p hp)).2
    · rw [← hsh]
      exact (hpair₂ p.2 hd (hq₂ p hp)).1
    · exact (hsmall p.1 p.2 h1 h2 (hq₁ p hp) (hq₂ p hp)).2

end ChainClasses
