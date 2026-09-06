import ChainClasses.Bushy.ShapeCouplingBuild

/-!
`sec:shape-coupling` and `sec:hairy-universality` of `gw_classes_simple.tex` at the
constants of the paper.  The label graph of `thm:shape-coupling` joins two charged pairs
when all four cross comparisons hold at the edge scale `27D⁴` of `def:shape-net`, matched
labels give a `972D⁴`-marked quasi-isometry, and `eq:hairy-rate` across two laws holds at
the scale `8·972²D⁸`.

The potential estimate is the split of `thm:shape-coupling` (`it:shape-coupling-eta`)
over the cascade coupling.  The shrinking is taken at the scale `s` with `3(2592s²)² ≤ D`,
so a cascade pair is `D`-comparable in both directions: the shrinking is `2592s²`-marked and
its quasi-inverse `3(2592s²)²`-marked.  Every closure pair and every cascade pair with a
small target then sees the whole closure block at the edge scale, the worst cross comparison
composing a small collapse with the shrinking to `3·9D³·D = 27D⁴`, and contributes through
the block mass `1-2e^{-cD²}`.  A cascade pair with a tail target `τ` is adjacent to the
outgoing pair of `τ`, whose mass the cascade floor bounds by `½μ(τ) ≥ ½p^{|τ|}`, and the
tail sums geometrically.

* `pairScale`, `pairScale_le`, `le_pairScale`: **the shrinking scale of the coupling**, the
  fourth root at which the quasi-inverse of the shrinking is `D`-marked.
* `pairNetS`: **the label graph `𝖰` of `thm:shape-coupling`**, distinct charged pairs
  linked when the four cross comparisons hold at `27D⁴`.
* `markedQI_of_compat_pairLabS`:
  **`thm:shape-coupling` (`it:shape-coupling-qi`)**, matched labels give a
  `972D⁴`-marked quasi-isometry.
* `markedQI_shrinkShape_both`, `markedQI_tail_small`, `compat_pairNetS_of_marked`,
  `compat_pairNetS_of_small`: the comparisons behind the adjacencies of the estimate.
* `single_le_gdeg`, `tsum_pair_large_le`, `tsum_pair_fibre_size_le`: the mass of a ball
  atom, of the tail pairs, and of a size fibre of the pairs.
* `exists_isShapeCoupling_etaS`:
  **`thm:shape-coupling` (`it:shape-coupling-eta`)**, the coupling with
  `η_{𝖰,5/2}(q) ≤ e^{-c₃D²}` over the edge scale `27D⁴`.
* `hairy_rate_two_law`: **`eq:hairy-rate` across two laws**, the failure probability of the
  `8·972²D⁸`-quasi-isometry bounded by `16η_{𝖰,5/2}(q) ≤ 16e^{-c₃D²}`.
-/

namespace ChainClasses

open MeasureTheory GraphMatching
open BranchingProcess (sample Offspring)
open scoped ENNReal Classical

/-! ### The shrinking scale of the coupling -/

/-- **The shrinking scale of the coupling**: the largest integer `s` with
`3(2592s²)² ≤ D`, so that the quasi-inverse of the shrinking at scale `s` is `D`-marked. -/
def pairScale (D : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (D / 20155392))

lemma pairScale_le (D : ℕ) : 20155392 * pairScale D ^ 4 ≤ D := by
  have h1 : pairScale D ^ 2 ≤ Nat.sqrt (D / 20155392) := Nat.sqrt_le' _
  have h2 : (pairScale D ^ 2) ^ 2 ≤ D / 20155392 :=
    le_trans (Nat.pow_le_pow_left h1 2) (Nat.sqrt_le' _)
  calc 20155392 * pairScale D ^ 4 = 20155392 * (pairScale D ^ 2) ^ 2 := by ring
    _ ≤ 20155392 * (D / 20155392) := Nat.mul_le_mul_left _ h2
    _ ≤ D := by
        rw [mul_comm]
        exact Nat.div_mul_le_self D 20155392

lemma le_pairScale {m D : ℕ} (h : 20155392 * m ^ 4 ≤ D) : m ≤ pairScale D := by
  have h1 : m ^ 4 ≤ D / 20155392 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have h2 : m ^ 2 ≤ Nat.sqrt (D / 20155392) := by
    have h3 : m ^ 2 * m ^ 2 ≤ D / 20155392 := by
      calc m ^ 2 * m ^ 2 = m ^ 4 := by ring
        _ ≤ D / 20155392 := h1
    have h4 := Nat.sqrt_le_sqrt h3
    rwa [Nat.sqrt_eq] at h4
  refine Nat.le_sqrt.mpr ?_
  calc m * m = m ^ 2 := by ring
    _ ≤ Nat.sqrt (D / 20155392) := h2

/-! ### The label graph at the edge scale of `def:shape-net` -/

/-- **The label graph `𝖰` of `thm:shape-coupling`**: distinct pairs the coupling charges
are linked when all four cross comparisons between their components hold at the edge scale
`27D⁴` of `def:shape-net`.  A pair the coupling does not charge, which no label ever takes,
is linked to everything, so that it carries no weight in `eq:etaG`. -/
def pairNetS (π : PMF (Shape × Shape)) (Dq : ℝ) : SimpleGraph (Shape × Shape) where
  Adj p p' := p ≠ p' ∧ (π p = 0 ∨ π p' = 0 ∨
    (MarkedQI (27 * Dq ^ 4) (shapeSpace p.1) (shapeSpace p'.2) ∧
      MarkedQI (27 * Dq ^ 4) (shapeSpace p'.2) (shapeSpace p.1) ∧
      MarkedQI (27 * Dq ^ 4) (shapeSpace p'.1) (shapeSpace p.2) ∧
      MarkedQI (27 * Dq ^ 4) (shapeSpace p.2) (shapeSpace p'.1)))
  symm := by
    refine ⟨fun p p' h => ⟨h.1.symm, ?_⟩⟩
    rcases h.2 with h0 | h0 | ⟨h1, h2, h3, h4⟩
    · exact Or.inr (Or.inl h0)
    · exact Or.inl h0
    · exact Or.inr (Or.inr ⟨h3, h4, h1, h2⟩)
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A pair the coupling does not charge is compatible with everything, so its ball carries
the whole mass. -/
lemma gdeg_pairNetS_of_zero (π : PMF (Shape × Shape)) (Dq : ℝ) {v : Shape × Shape}
    (hv : π v = 0) : gdeg π (pairNetS π Dq) v = 1 := by
  have h : rE π (compat (pairNetS π Dq)) v = 1 := by
    rw [rE]
    calc ∑' y : Shape × Shape, (if compat (pairNetS π Dq) v y then π y else 0)
        = ∑' y : Shape × Shape, π y := by
          refine tsum_congr fun y => if_pos ?_
          by_cases hy : y = v
          · exact Or.inl hy.symm
          · exact Or.inr ⟨fun h => hy h.symm, Or.inl hv⟩
      _ = 1 := π.tsum_coe
  rw [gdeg, h, ENNReal.toReal_one]

/-- Four cross comparisons at the edge scale make two pairs compatible. -/
lemma compat_pairNetS_of_marked {π : PMF (Shape × Shape)} {Dq : ℝ} {p p' : Shape × Shape}
    (h1 : MarkedQI (27 * Dq ^ 4) (shapeSpace p.1) (shapeSpace p'.2))
    (h2 : MarkedQI (27 * Dq ^ 4) (shapeSpace p'.2) (shapeSpace p.1))
    (h3 : MarkedQI (27 * Dq ^ 4) (shapeSpace p'.1) (shapeSpace p.2))
    (h4 : MarkedQI (27 * Dq ^ 4) (shapeSpace p.2) (shapeSpace p'.1)) :
    compat (pairNetS π Dq) p p' := by
  by_cases h : p = p'
  · exact Or.inl h
  · exact Or.inr ⟨h, Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)⟩

/-- The comparability scale of a charged pair lies below the edge scale. -/
lemma coupScale_le_netScale {Dq : ℝ} (hD : 1 ≤ Dq) : 9 * Dq ^ 3 ≤ 27 * Dq ^ 4 := by
  have h3 : (1 : ℝ) ≤ Dq ^ 3 := one_le_pow₀ hD
  nlinarith [pow_le_pow_right₀ hD (show 3 ≤ 4 by norm_num)]

/-- **The small block**: two pairs of small shapes are compatible, all four cross
comparisons being collapses at scale `9D³`. -/
lemma compat_pairNetS_of_small {π : PMF (Shape × Shape)} {Dq : ℝ} (hD : 1 ≤ Dq)
    {p p' : Shape × Shape} (h11 : ((p.1.size : ℝ)) ≤ Dq * Dq)
    (h12 : ((p.2.size : ℝ)) ≤ Dq * Dq) (h21 : ((p'.1.size : ℝ)) ≤ Dq * Dq)
    (h22 : ((p'.2.size : ℝ)) ≤ Dq * Dq) :
    compat (pairNetS π Dq) p p' := by
  have h0 : (0 : ℝ) ≤ 9 * Dq ^ 3 := by positivity
  have hle := coupScale_le_netScale hD
  exact compat_pairNetS_of_marked
    ((markedQI_small_pair hD h11 h22).mono h0 hle)
    ((markedQI_small_pair hD h22 h11).mono h0 hle)
    ((markedQI_small_pair hD h21 h12).mono h0 hle)
    ((markedQI_small_pair hD h12 h21).mono h0 hle)

/-! ### `thm:shape-coupling` (`it:shape-coupling-qi`) at the edge scale -/

/-- **The cross comparison of the label graph**: two charged pairs at graph distance at
most one have the first component of the one comparable to the second component of the
other at the edge scale. -/
theorem markedQI_of_compat_pairNetS {Dq : ℝ} (hD : 1 ≤ Dq) {q₁ q₂ : PMF Shape}
    {π : PMF (Shape × Shape)} (hπ : IsShapeCoupling Dq q₁ q₂ π) {p p' : Shape × Shape}
    (hp : π p ≠ 0) (hp' : π p' ≠ 0) (h : compat (pairNetS π Dq) p p') :
    MarkedQI (27 * Dq ^ 4) (shapeSpace p.1) (shapeSpace p'.2) := by
  rcases h with heq | hadj
  · rw [← heq]
    exact (hπ.qi p hp).mono (by positivity) (coupScale_le_netScale hD)
  · rcases hadj.2 with h0 | h0 | ⟨h1, _, _, _⟩
    · exact absurd h0 hp
    · exact absurd h0 hp'
    · exact h1

/-- **`thm:shape-coupling` (`it:shape-coupling-qi`)**: matched labels give
comparable shapes at the scale `972D⁴`.  A shape is comparable to its fix, the fixes are
the components of two pairs the coupling charges at graph distance at most one, and the
chain composes to at most `972D⁴`. -/
theorem markedQI_of_compat_pairLabS {Dq : ℝ} (hD : 1 ≤ Dq) (θ θ' : Offspring 2)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2)
    (hq' : θ'.extinction < 1) (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2)
    {q₁ q₂ : PMF Shape} {π : PMF (Shape × Shape)} (hπ : IsShapeCoupling Dq q₁ q₂ π)
    (hm : ∀ a : Shape, margFst π a = shapePMF θ hq hq0 h2 a)
    (hm' : ∀ b : Shape, margSnd π b = shapePMF θ' hq' hq0' h2' b)
    (τ τ' : Shape) (u u' : ℝ)
    (h : compat (pairNetS π Dq) (pairLab π τ u) (pairLab' π τ' u')) :
    MarkedQI (972 * Dq ^ 4) (shapeSpace τ) (shapeSpace τ') := by
  have hp : π (pairLab π τ u) ≠ 0 := pairLab_ne_zero θ hq hq0 h2 π hm τ u
  have hp' : π (pairLab' π τ' u') ≠ 0 := pairLab'_ne_zero θ' hq' hq0' h2' π hm' τ' u'
  have hmid : MarkedQI (27 * Dq ^ 4) (shapeSpace τ.fix) (shapeSpace τ'.fix) :=
    markedQI_of_compat_pairNetS hD hπ hp hp' h
  have hlamb : (1 : ℝ) ≤ 27 * Dq ^ 4 := one_le_netScale hD
  have hfix : MarkedQI 1 (shapeSpace τ) (shapeSpace τ.fix) := markedQI_shape_fix τ
  have hfix' : MarkedQI 3 (shapeSpace τ'.fix) (shapeSpace τ') := by
    have hs := markedQI_symm (le_refl (1 : ℝ)) (markedQI_shape_fix τ')
    norm_num at hs
    exact hs
  have h12 := markedQI_comp (le_refl (1 : ℝ)) hlamb hfix hmid
  have hall := markedQI_comp (by nlinarith) (by norm_num) h12 hfix'
  have h4 : (1 : ℝ) ≤ Dq ^ 4 := one_le_pow₀ hD
  refine hall.mono (by positivity) ?_
  nlinarith

/-! ### The shrinking is `D`-comparable in both directions -/

/-- **The two-sided shrink comparison**: at a scale `s` with `3(2592s²)² ≤ D`, a shape and
its shrinking are `D`-comparable in both directions, the shrinking being `2592s²`-marked
and its quasi-inverse `3(2592s²)²`-marked. -/
lemma markedQI_shrinkShape_both {s D : ℕ} (hs : 1 ≤ s)
    (hsD4 : 3 * (2592 * (s : ℝ) ^ 2) ^ 2 ≤ (D : ℝ)) (σ : Shape) :
    MarkedQI (D : ℝ) (shapeSpace σ) (shapeSpace (shrinkShape s σ)) ∧
      MarkedQI (D : ℝ) (shapeSpace (shrinkShape s σ)) (shapeSpace σ) := by
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have ha : (1 : ℝ) ≤ 2592 * (s : ℝ) ^ 2 := by nlinarith
  have hsD : 2592 * (s : ℝ) ^ 2 ≤ (D : ℝ) := by nlinarith
  have hfwd := markedQI_shrinkShape hs σ
  exact ⟨hfwd.mono (by positivity) hsD,
    (markedQI_symm ha hfwd).mono (by positivity) hsD4⟩

/-- **The tail-to-small comparison**: a tail source whose shrinking is small is comparable
to every small shape at the edge scale, in both directions, through its shrinking. -/
lemma markedQI_tail_small {s D : ℕ} (hs : 1 ≤ s) (hD : 1 ≤ D)
    (hsD4 : 3 * (2592 * (s : ℝ) ^ 2) ^ 2 ≤ (D : ℝ)) (σ y : Shape)
    (hτ : (((shrinkShape s σ).size : ℝ)) ≤ (D : ℝ) * (D : ℝ))
    (hy : ((y.size : ℝ)) ≤ (D : ℝ) * (D : ℝ)) :
    MarkedQI (27 * (D : ℝ) ^ 4) (shapeSpace σ) (shapeSpace y) ∧
      MarkedQI (27 * (D : ℝ) ^ 4) (shapeSpace y) (shapeSpace σ) := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have h9 : (1 : ℝ) ≤ 9 * (D : ℝ) ^ 3 := one_le_coupScale hDR
  obtain ⟨hfwd, hback⟩ := markedQI_shrinkShape_both hs hsD4 σ
  constructor
  · have h := markedQI_comp hDR h9 hfwd (markedQI_small_pair hDR hτ hy)
    rwa [show 3 * (D : ℝ) * (9 * (D : ℝ) ^ 3) = 27 * (D : ℝ) ^ 4 by ring] at h
  · have h := markedQI_comp h9 hDR (markedQI_small_pair hDR hy hτ) hback
    rwa [show 3 * (9 * (D : ℝ) ^ 3) * (D : ℝ) = 27 * (D : ℝ) ^ 4 by ring] at h

/-! ### The mass of a ball atom and of the tail pairs -/

/-- The ball of a vertex weighs at least any one compatible atom. -/
lemma single_le_gdeg {V : Type*} (μ : PMF V) (G : SimpleGraph V) {v y : V}
    (h : compat G v y) : (μ y).toReal ≤ gdeg μ G v := by
  have hle : μ y ≤ rE μ (compat G) v := by
    rw [rE]
    calc (μ y : ℝ≥0∞) = (if compat G v y then μ y else 0) := (if_pos h).symm
      _ ≤ ∑' z, (if compat G v z then μ z else 0) := ENNReal.le_tsum y
  exact ENNReal.toReal_mono (rE_ne_top (μ := μ) (R := compat G) (x := v)) hle

/-- **The tail pairs**: the mass of the pairs with a component above a size threshold is at
most the two marginal tails. -/
lemma tsum_pair_large_le (π : PMF (Shape × Shape)) (N : ℕ) :
    (∑' p : Shape × Shape, if max p.1.size p.2.size ≤ N then 0 else π p)
      ≤ (∑' a : Shape, if a.size ≤ N then 0 else margFst π a)
        + (∑' b : Shape, if b.size ≤ N then 0 else margSnd π b) := by
  have hpt : ∀ p : Shape × Shape, (if max p.1.size p.2.size ≤ N then 0 else π p)
      ≤ (if p.1.size ≤ N then 0 else π p) + (if p.2.size ≤ N then 0 else π p) := by
    intro p
    by_cases h : max p.1.size p.2.size ≤ N
    · rw [if_pos h]
      exact zero_le
    · rw [if_neg h]
      by_cases h1 : p.1.size ≤ N
      · have h2 : ¬ p.2.size ≤ N := fun hb => h (max_le h1 hb)
        rw [if_pos h1, if_neg h2]
        exact le_add_self
      · rw [if_neg h1]
        exact le_self_add
  calc (∑' p : Shape × Shape, if max p.1.size p.2.size ≤ N then 0 else π p)
      ≤ ∑' p : Shape × Shape,
          ((if p.1.size ≤ N then 0 else π p) + (if p.2.size ≤ N then 0 else π p)) :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' p : Shape × Shape, if p.1.size ≤ N then 0 else π p)
        + (∑' p : Shape × Shape, if p.2.size ≤ N then 0 else π p) := ENNReal.tsum_add
    _ = (∑' a : Shape, if a.size ≤ N then 0 else margFst π a)
        + (∑' b : Shape, if b.size ≤ N then 0 else margSnd π b) := by
        congr 1
        · rw [ENNReal.tsum_prod']
          refine tsum_congr fun a => ?_
          by_cases h : a.size ≤ N
          · simp [h]
          · simp only [h, if_false]
            rfl
        · rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
          refine tsum_congr fun b => ?_
          by_cases h : b.size ≤ N
          · simp [h]
          · simp only [h, if_false]
            rfl

/-- **A size fibre of the pairs**: the mass of the pairs whose larger component has size
`n` is at most the two marginal masses at size `n`. -/
lemma tsum_pair_fibre_size_le (π : PMF (Shape × Shape)) (n : ℕ) :
    (∑' v : {v : Shape × Shape // max v.1.size v.2.size = n}, π (v : Shape × Shape))
      ≤ (∑' a : {a : Shape // a.size = n}, margFst π (a : Shape))
        + (∑' b : {b : Shape // b.size = n}, margSnd π (b : Shape)) := by
  have hsub : (∑' v : {v : Shape × Shape // max v.1.size v.2.size = n}, π (v : Shape × Shape))
      = ∑' v : Shape × Shape, (if max v.1.size v.2.size = n then π v else 0) := by
    refine (tsum_subtype {v : Shape × Shape | max v.1.size v.2.size = n} π).trans
      (tsum_congr fun v => ?_)
    by_cases hv : max v.1.size v.2.size = n
    · rw [Set.indicator_of_mem (show v ∈ {v : Shape × Shape | max v.1.size v.2.size = n}
        from hv) π, if_pos hv]
    · rw [Set.indicator_of_notMem (show v ∉ {v : Shape × Shape | max v.1.size v.2.size = n}
        from hv) π, if_neg hv]
  have hsubA : (∑' a : {a : Shape // a.size = n}, margFst π (a : Shape))
      = ∑' a : Shape, (if a.size = n then margFst π a else 0) := by
    refine (tsum_subtype {a : Shape | a.size = n} (margFst π)).trans
      (tsum_congr fun a => ?_)
    by_cases ha : a.size = n
    · rw [Set.indicator_of_mem (show a ∈ {a : Shape | a.size = n} from ha), if_pos ha]
    · rw [Set.indicator_of_notMem (show a ∉ {a : Shape | a.size = n} from ha), if_neg ha]
  have hsubB : (∑' b : {b : Shape // b.size = n}, margSnd π (b : Shape))
      = ∑' b : Shape, (if b.size = n then margSnd π b else 0) := by
    refine (tsum_subtype {b : Shape | b.size = n} (margSnd π)).trans
      (tsum_congr fun b => ?_)
    by_cases hb : b.size = n
    · rw [Set.indicator_of_mem (show b ∈ {b : Shape | b.size = n} from hb), if_pos hb]
    · rw [Set.indicator_of_notMem (show b ∉ {b : Shape | b.size = n} from hb), if_neg hb]
  rw [hsub, hsubA, hsubB]
  have hpt : ∀ v : Shape × Shape, (if max v.1.size v.2.size = n then π v else 0)
      ≤ (if v.1.size = n then π v else 0) + (if v.2.size = n then π v else 0) := by
    intro v
    by_cases hv : max v.1.size v.2.size = n
    · rw [if_pos hv]
      rcases max_choice v.1.size v.2.size with h | h
      · rw [if_pos (h.symm.trans hv)]
        exact le_self_add
      · rw [if_pos (h.symm.trans hv)]
        exact le_add_self
    · rw [if_neg hv]
      exact zero_le
  calc ∑' v : Shape × Shape, (if max v.1.size v.2.size = n then π v else 0)
      ≤ ∑' v : Shape × Shape,
          ((if v.1.size = n then π v else 0) + (if v.2.size = n then π v else 0)) :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' v : Shape × Shape, if v.1.size = n then π v else 0)
        + (∑' v : Shape × Shape, if v.2.size = n then π v else 0) := ENNReal.tsum_add
    _ = (∑' a : Shape, if a.size = n then margFst π a else 0)
        + (∑' b : Shape, if b.size = n then margSnd π b else 0) := by
        congr 1
        · rw [ENNReal.tsum_prod']
          refine tsum_congr fun a => ?_
          by_cases h : a.size = n
          · simp only [h, if_true]
            rfl
          · simp [h]
        · rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
          refine tsum_congr fun b => ?_
          by_cases h : b.size = n
          · simp only [h, if_true]
            rfl
          · simp [h]

/-- `e^{-x} ≤ ½` past `x ≥ 1`. -/
lemma exp_neg_le_half {x : ℝ} (hx : 1 ≤ x) : Real.exp (-x) ≤ 1 / 2 := by
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hmono : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-1)]

/-- Two exponential tails at twice a rate sum below the tail at the rate itself. -/
lemma exp_two_tails_le {cA cB c X : ℝ} (hA : 2 * c ≤ cA) (hB : 2 * c ≤ cB)
    (hX : 1 ≤ c * X) (hX0 : 0 ≤ X) :
    Real.exp (-(cA * X)) + Real.exp (-(cB * X)) ≤ Real.exp (-(c * X)) := by
  have h2e : (2 : ℝ) ≤ Real.exp (c * X) :=
    le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_le_exp.mpr hX)
  have hsplit : Real.exp (-(2 * c * X)) = Real.exp (-(c * X)) * Real.exp (-(c * X)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul : Real.exp (c * X) * Real.exp (-(c * X)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hAle : Real.exp (-(cA * X)) ≤ Real.exp (-(2 * c * X)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hA hX0])
  have hBle : Real.exp (-(cB * X)) ≤ Real.exp (-(2 * c * X)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hB hX0])
  have hstep : 2 * Real.exp (-(2 * c * X)) ≤ Real.exp (-(c * X)) := by
    rw [hsplit]
    calc 2 * (Real.exp (-(c * X)) * Real.exp (-(c * X)))
        ≤ Real.exp (c * X) * (Real.exp (-(c * X)) * Real.exp (-(c * X))) :=
          mul_le_mul_of_nonneg_right h2e (by positivity)
      _ = Real.exp (c * X) * Real.exp (-(c * X)) * Real.exp (-(c * X)) := by ring
      _ = Real.exp (-(c * X)) := by rw [hmul, one_mul]
  linarith

/-- The scale of `def:shape-net` absorbs the base scale. -/
lemma le_netScale_self {Dq : ℝ} (hD : 1 ≤ Dq) : Dq ≤ 27 * Dq ^ 4 := by
  have h := pow_le_pow_right₀ hD (show 1 ≤ 4 by norm_num)
  rw [pow_one] at h
  nlinarith [pow_nonneg (le_trans zero_le_one hD) 4]

/-! ### `thm:shape-coupling` (`it:shape-coupling-eta`) -/

set_option maxHeartbeats 1000000 in
/-- **`thm:shape-coupling` (`it:shape-coupling-eta`)**: past a threshold, the two
shape laws admit a coupling whose law on pairs has potential at most `e^{-c₃D²}` over the
label graph at the edge scale `27D⁴`.  The closure block and the cascade pairs with small
targets contribute through the block mass, and the cascade pairs with tail targets through
the floor `out ≥ ½M₀` at the target, summed geometrically. -/
theorem exists_isShapeCoupling_etaS (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D →
      Real.exp (-(c₃ * (D : ℝ) ^ 2)) ≤ 1 / 10000 ∧ ∃ π : PMF (Shape × Shape),
      IsShapeCoupling (D : ℝ) (shapePMF θ hq hq0 h2) (shapePMF θ' hq' hq0' h2') π ∧
      etaG π (pairNetS π (D : ℝ)) ≤ ENNReal.ofReal (Real.exp (-(c₃ * (D : ℝ) ^ 2))) := by
  classical
  obtain ⟨cA, hcA, nA, htailA⟩ := exists_fix_size_tail θ hq hq0 h2
  obtain ⟨cB, hcB, nB, htailB⟩ := exists_fix_size_tail θ' hq' hq0' h2'
  obtain ⟨A, hA1, hA⟩ := exists_capacity_shapePMF θ θ' hq hq0 h2 hq' hq0' h2'
  set cm : ℝ := min cA cB with hcmdef
  have hcm : 0 < cm := lt_min hcA hcB
  set c : ℝ := cm / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set p : ℝ := min (shapeWeight θ) (shapeWeight θ') with hpdef
  have hp0 : 0 < p := lt_min (shapeWeight_pos θ hq hq0 h2) (shapeWeight_pos θ' hq' hq0' h2')
  have hp1 : p ≤ 1 := le_trans (min_le_left _ _) (shapeWeight_le_one θ)
  set L : ℝ := Real.log p⁻¹ with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hp0, hp1⟩)
  set C₂ : ℝ := 6 * Real.exp (40 * L) * (1 - Real.exp (-(c / 2)))⁻¹ with hC₂def
  have hpos2 : (0 : ℝ) < 1 - Real.exp (-(c / 2)) := by
    linarith [exp_neg_half_lt_one hc]
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂def]
    positivity
  obtain ⟨D₂, hD₂⟩ := shape_eta_final (c := c) (C₂ := C₂) hc hC₂0
  set M : ℕ := max A (⌈80 * L / c⌉₊ + 1) with hMdef
  refine ⟨c / 4, by linarith, 20155392 * M ^ 4 + 58 + nA + nB + ⌈1 / c⌉₊ + ⌈40000 / c⌉₊ + D₂,
    fun D hD ↦ ?_⟩
  -- the components of the threshold
  have hPD : 20155392 * M ^ 4 ≤ D :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (Nat.le_add_right _ 58)
      (Nat.le_add_right _ nA)) (Nat.le_add_right _ nB)) (Nat.le_add_right _ ⌈1 / c⌉₊))
      (Nat.le_add_right _ ⌈40000 / c⌉₊)) (Nat.le_add_right _ D₂)) hD
  have h58 : 58 ≤ D :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (Nat.le_add_left 58 _)
      (Nat.le_add_right _ nA)) (Nat.le_add_right _ nB)) (Nat.le_add_right _ ⌈1 / c⌉₊))
      (Nat.le_add_right _ ⌈40000 / c⌉₊)) (Nat.le_add_right _ D₂)) hD
  have hnAD : nA ≤ D :=
    le_trans (le_trans (le_trans (le_trans (le_trans (Nat.le_add_left nA _)
      (Nat.le_add_right _ nB)) (Nat.le_add_right _ ⌈1 / c⌉₊))
      (Nat.le_add_right _ ⌈40000 / c⌉₊)) (Nat.le_add_right _ D₂)) hD
  have hnBD : nB ≤ D :=
    le_trans (le_trans (le_trans (le_trans (Nat.le_add_left nB _)
      (Nat.le_add_right _ ⌈1 / c⌉₊)) (Nat.le_add_right _ ⌈40000 / c⌉₊))
      (Nat.le_add_right _ D₂)) hD
  have hceilD : ⌈1 / c⌉₊ ≤ D :=
    le_trans (le_trans (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ ⌈40000 / c⌉₊))
      (Nat.le_add_right _ D₂)) hD
  have hceil4D : ⌈40000 / c⌉₊ ≤ D :=
    le_trans (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ D₂)) hD
  have hDD₂ : D₂ ≤ D := le_trans (Nat.le_add_left _ _) hD
  -- the scale of the shrinking
  set s : ℕ := pairScale D with hsdef
  have hMs : M ≤ s := le_pairScale hPD
  have hM1 : 1 ≤ M := le_trans (by omega) (le_max_right A (⌈80 * L / c⌉₊ + 1))
  have hs1 : 1 ≤ s := le_trans hM1 hMs
  have hsA : A ≤ s := le_trans (le_max_left _ _) hMs
  have hs80 : ⌈80 * L / c⌉₊ + 1 ≤ s := le_trans (le_max_right _ _) hMs
  have hD1 : 1 ≤ D := by omega
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hsR0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
  have hsD4 : 3 * (2592 * (s : ℝ) ^ 2) ^ 2 ≤ (D : ℝ) := by
    have h1 : ((20155392 * s ^ 4 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast pairScale_le D
    push_cast at h1
    calc 3 * (2592 * (s : ℝ) ^ 2) ^ 2 = 20155392 * (s : ℝ) ^ 4 := by ring
      _ ≤ (D : ℝ) := h1
  have hsD2 : 2592 * (s : ℝ) ^ 2 ≤ (D : ℝ) := by
    have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    have ha1 : (1 : ℝ) ≤ 2592 * (s : ℝ) ^ 2 := by nlinarith
    have key : ∀ a : ℝ, 1 ≤ a → a ≤ 3 * a ^ 2 := by
      intro a ha
      nlinarith
    exact le_trans (key _ ha1) hsD4
  -- the coupling with the cascade data
  have hND : A ≤ D ^ 2 := by
    have h1 : A ≤ M := le_max_left _ _
    have h2 : M ≤ M ^ 4 := Nat.le_self_pow (by norm_num) M
    have h3 : M ^ 4 ≤ 20155392 * M ^ 4 := Nat.le_mul_of_pos_left _ (by norm_num)
    have h4 : D ≤ D ^ 2 := Nat.le_self_pow (by norm_num) D
    omega
  obtain ⟨hcap₁, hcap₂⟩ := hA s (D ^ 2) hsA hND
  obtain ⟨π, hπ, hcasc⟩ := exists_isShapeCoupling_of_capacity hD1 hs1 hsD2 hcap₁ hcap₂
  have hsmall4 : Real.exp (-(c / 4 * (D : ℝ) ^ 2)) ≤ 1 / 10000 := by
    have hceil : (40000 / c : ℝ) ≤ (D : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil4D)
    have hy : 10000 ≤ c / 4 * (D : ℝ) ^ 2 := by
      rw [div_le_iff₀ hc] at hceil
      nlinarith
    have hkey := mul_exp_neg_le_one (c / 4 * (D : ℝ) ^ 2)
    have h10 : 10000 * Real.exp (-(c / 4 * (D : ℝ) ^ 2)) ≤ 1 := by
      nlinarith [Real.exp_pos (-(c / 4 * (D : ℝ) ^ 2))]
    linarith
  refine ⟨hsmall4, π, hπ, ?_⟩
  set G : SimpleGraph (Shape × Shape) := pairNetS π (D : ℝ) with hGdef
  set sz : Shape × Shape → ℕ := fun v ↦ max v.1.size v.2.size with hszdef
  -- the two rates
  have hcD : 1 ≤ c * (D : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) / c ≤ (D : ℝ) :=
      (Nat.le_ceil (1 / c)).trans (by exact_mod_cast hceilD)
    rw [div_le_iff₀ hc] at h1
    nlinarith
  have hcA2 : 2 * c ≤ cA := by
    have h : cm ≤ cA := by
      rw [hcmdef]
      exact min_le_left _ _
    rw [hcdef]
    linarith
  have hcB2 : 2 * c ≤ cB := by
    have h : cm ≤ cB := by
      rw [hcmdef]
      exact min_le_right _ _
    rw [hcdef]
    linarith
  have hkey2 : ∀ X : ℝ, 1 ≤ c * X → 0 ≤ X →
      Real.exp (-(cA * X)) + Real.exp (-(cB * X)) ≤ Real.exp (-(c * X)) :=
    fun X hX hX0 => exp_two_tails_le hcA2 hcB2 hX hX0
  have hcastD2 : ((D ^ 2 : ℕ) : ℝ) = (D : ℝ) ^ 2 := by push_cast; ring
  -- the halving condition
  have hhalf : Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ 1 / 2 := exp_neg_le_half hcD
  -- the mass above the block
  have hDsq : D ≤ D ^ 2 := Nat.le_self_pow (by norm_num) D
  have hnA2 : nA ≤ D ^ 2 := le_trans hnAD hDsq
  have hnB2 : nB ≤ D ^ 2 := le_trans hnBD hDsq
  have hlarge : (∑' y : Shape × Shape, if sz y ≤ D ^ 2 then 0 else π y)
      ≤ ENNReal.ofReal (Real.exp (-(c * ((D : ℝ) ^ 2)))) := by
    refine (tsum_pair_large_le π (D ^ 2)).trans ?_
    have hAt : (∑' a : Shape, if a.size ≤ D ^ 2 then 0 else margFst π a)
        ≤ ENNReal.ofReal (Real.exp (-cA * ((D ^ 2 : ℕ) : ℝ))) := by
      refine le_trans (le_of_eq (tsum_congr fun a ↦ ?_))
        (tsum_shapePMF_large_le θ hq hq0 h2 hcA htailA hnA2)
      rw [hπ.marg₁ a]
    have hBt : (∑' b : Shape, if b.size ≤ D ^ 2 then 0 else margSnd π b)
        ≤ ENNReal.ofReal (Real.exp (-cB * ((D ^ 2 : ℕ) : ℝ))) := by
      refine le_trans (le_of_eq (tsum_congr fun b ↦ ?_))
        (tsum_shapePMF_large_le θ' hq' hq0' h2' hcB htailB hnB2)
      rw [hπ.marg₂ b]
    refine (add_le_add hAt hBt).trans ?_
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hkey2 ((D : ℝ) ^ 2) hcD (by positivity)
    rw [hcastD2]
    calc Real.exp (-cA * ((D : ℝ) ^ 2)) + Real.exp (-cB * ((D : ℝ) ^ 2))
        = Real.exp (-(cA * ((D : ℝ) ^ 2))) + Real.exp (-(cB * ((D : ℝ) ^ 2))) := by
          rw [neg_mul, neg_mul]
      _ ≤ Real.exp (-(c * ((D : ℝ) ^ 2))) := h
  -- the small block
  have hcast : ∀ w : Shape × Shape, sz w ≤ D ^ 2 →
      ((w.1.size : ℝ) ≤ (D : ℝ) * (D : ℝ) ∧ (w.2.size : ℝ) ≤ (D : ℝ) * (D : ℝ)) := by
    intro w hw
    have h1 : w.1.size ≤ D ^ 2 := le_trans (le_max_left _ _) hw
    have h2 : w.2.size ≤ D ^ 2 := le_trans (le_max_right _ _) hw
    constructor
    · calc (w.1.size : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (D : ℝ) * (D : ℝ) := by push_cast; ring
    · calc (w.2.size : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := by exact_mod_cast h2
        _ = (D : ℝ) * (D : ℝ) := by push_cast; ring
  have hsmall : ∀ v : Shape × Shape, sz v ≤ D ^ 2 →
      1 - Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ gdeg π G v := by
    intro v hv
    refine one_sub_le_gdeg_of_small π G sz (D ^ 2) v (fun y hy ↦ ?_) (Real.exp_pos _).le
      hlarge
    obtain ⟨hv1, hv2⟩ := hcast v hv
    obtain ⟨hy1, hy2⟩ := hcast y hy
    exact compat_pairNetS_of_small hDR hv1 hv2 hy1 hy2
  -- the mass of the sizes above the block
  have hfix0A : ∀ n : ℕ, 0 ≤ fixSizeMass θ n := fun n ↦ shapeStatMass_nonneg θ _ n
  have hfix0B : ∀ n : ℕ, 0 ≤ fixSizeMass θ' n := fun n ↦ shapeStatMass_nonneg θ' _ n
  have hfixsumA : Summable (fixSizeMass θ) :=
    summable_shapeStatMass θ hq hq0 h2 fun σ ↦ σ.fix.size
  have hfixsumB : Summable (fixSizeMass θ') :=
    summable_shapeStatMass θ' hq' hq0' h2' fun σ ↦ σ.fix.size
  set g : ℕ → ℝ := fun n ↦ if n ≤ D ^ 2 then 0 else fixSizeMass θ n + fixSizeMass θ' n
    with hgdef
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    rw [hgdef]
    by_cases hn : n ≤ D ^ 2 <;> simp [hn, add_nonneg (hfix0A n) (hfix0B n)]
  have hgvan : ∀ n ≤ D ^ 2, g n = 0 := by
    intro n hn
    rw [hgdef]
    simp [hn]
  have hfixleA : ∀ n : ℕ, nA ≤ n → fixSizeMass θ n ≤ Real.exp (-cA * (n : ℝ)) := by
    intro n hn
    have hshiftsum : Summable fun k : ℕ ↦ fixSizeMass θ (k + n) :=
      (summable_nat_add_iff n).mpr hfixsumA
    have hle : fixSizeMass θ n ≤ ∑' k : ℕ, fixSizeMass θ (k + n) := by
      have h := hshiftsum.le_tsum 0 fun j _ ↦ hfix0A _
      simpa using h
    exact hle.trans (htailA n hn)
  have hfixleB : ∀ n : ℕ, nB ≤ n → fixSizeMass θ' n ≤ Real.exp (-cB * (n : ℝ)) := by
    intro n hn
    have hshiftsum : Summable fun k : ℕ ↦ fixSizeMass θ' (k + n) :=
      (summable_nat_add_iff n).mpr hfixsumB
    have hle : fixSizeMass θ' n ≤ ∑' k : ℕ, fixSizeMass θ' (k + n) := by
      have h := hshiftsum.le_tsum 0 fun j _ ↦ hfix0B _
      simpa using h
    exact hle.trans (htailB n hn)
  have hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))) := by
    intro n
    by_cases hn : n ≤ D ^ 2
    · rw [hgvan n hn]
      exact (Real.exp_pos _).le
    · have hgn : g n = fixSizeMass θ n + fixSizeMass θ' n := by rw [hgdef]; simp [hn]
      have hcn : 1 ≤ c * (n : ℝ) := by
        have h1 : ((D ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : D ^ 2 ≤ n)
        rw [hcastD2] at h1
        nlinarith
      have h := hkey2 (n : ℝ) hcn (Nat.cast_nonneg n)
      have hAn := hfixleA n (by omega)
      have hBn := hfixleB n (by omega)
      rw [hgn]
      have hArw : Real.exp (-cA * (n : ℝ)) = Real.exp (-(cA * (n : ℝ))) := by rw [neg_mul]
      have hBrw : Real.exp (-cB * (n : ℝ)) = Real.exp (-(cB * (n : ℝ))) := by rw [neg_mul]
      rw [hArw] at hAn
      rw [hBrw] at hBn
      linarith
  have hmass : ∀ n, D ^ 2 < n →
      (∑' v : {v : Shape × Shape // sz v = n}, π (v : Shape × Shape))
        ≤ ENNReal.ofReal (g n) := by
    intro n hn
    have hgn : g n = fixSizeMass θ n + fixSizeMass θ' n := by
      have hn' : ¬ n ≤ D ^ 2 := by omega
      rw [hgdef]
      simp [hn']
    refine (tsum_pair_fibre_size_le π n).trans ?_
    have hAeq : (∑' a : {a : Shape // a.size = n}, margFst π (a : Shape))
        = ENNReal.ofReal (fixSizeMass θ n) := by
      have h1 : (∑' a : {a : Shape // a.size = n}, margFst π (a : Shape))
          = ∑' a : {a : Shape // a.size = n}, shapePMF θ hq hq0 h2 (a : Shape) :=
        tsum_congr fun a ↦ hπ.marg₁ _
      rw [h1, tsum_fibre_size_shapePMF θ hq hq0 h2 n]
      exact (ofReal_shapeStatMass θ hq hq0 h2 (fun σ ↦ σ.fix.size) n).symm
    have hBeq : (∑' b : {b : Shape // b.size = n}, margSnd π (b : Shape))
        = ENNReal.ofReal (fixSizeMass θ' n) := by
      have h1 : (∑' b : {b : Shape // b.size = n}, margSnd π (b : Shape))
          = ∑' b : {b : Shape // b.size = n}, shapePMF θ' hq' hq0' h2' (b : Shape) :=
        tsum_congr fun b ↦ hπ.marg₂ _
      rw [h1, tsum_fibre_size_shapePMF θ' hq' hq0' h2' n]
      exact (ofReal_shapeStatMass θ' hq' hq0' h2' (fun σ ↦ σ.fix.size) n).symm
    rw [hAeq, hBeq, hgn, ENNReal.ofReal_add (hfix0A n) (hfix0B n)]
  -- the domination of the ball masses in the tail
  set bb : ℕ → ℝ := fun n ↦ p ^ (16 * (n / s + 1)) / 2 with hbbdef
  have hbb0 : ∀ n, 0 < bb n := by
    intro n
    rw [hbbdef]
    positivity
  have hbbhalf : ∀ n, bb n ≤ 1 / 2 := by
    intro n
    rw [hbbdef]
    have h := pow_le_one₀ hp0.le hp1 (n := 16 * (n / s + 1))
    linarith
  have hbb1 : ∀ n, bb n ≤ 1 := fun n ↦ le_trans (hbbhalf n) (by norm_num)
  have hball : ∀ v : Shape × Shape, D ^ 2 < sz v → bb (sz v) ≤ gdeg π G v := by
    intro v hv
    by_cases hv0 : π v = 0
    · rw [hGdef, gdeg_pairNetS_of_zero π (D : ℝ) hv0]
      exact hbb1 _
    have hEhalf : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(c * ((D : ℝ) ^ 2))) := by linarith
    rcases hcasc.supp v hv0 with ⟨h1, hsh⟩ | ⟨h1, hsh⟩ | ⟨h1, h2s⟩
    · -- a cascade pair of a source of the first law
      by_cases hτ : v.2.size ≤ D ^ 2
      · -- small target: the ball contains the block
        have hτR : ((v.2.size : ℝ)) ≤ (D : ℝ) * (D : ℝ) := by
          calc ((v.2.size : ℝ)) ≤ ((D ^ 2 : ℕ) : ℝ) := by exact_mod_cast hτ
            _ = (D : ℝ) * (D : ℝ) := by push_cast; ring
        have hgd : 1 - Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ gdeg π G v := by
          refine one_sub_le_gdeg_of_small π G sz (D ^ 2) v (fun y hy ↦ ?_)
            (Real.exp_pos _).le hlarge
          obtain ⟨hy1, hy2⟩ := hcast y hy
          obtain ⟨hts1, hts2⟩ := markedQI_tail_small hs1 hD1 hsD4 v.1 y.2
            (by rw [hsh]; exact hτR) hy2
          have h0 : (0 : ℝ) ≤ 9 * (D : ℝ) ^ 3 := by positivity
          have hle := coupScale_le_netScale hDR
          exact compat_pairNetS_of_marked hts1 hts2
            ((markedQI_small_pair hDR hy1 hτR).mono h0 hle)
            ((markedQI_small_pair hDR hτR hy1).mono h0 hle)
        linarith [hbbhalf (sz v)]
      · -- tail target: the ball contains the outgoing pair of the target
        have hτtail : D ^ 2 < v.2.size := by omega
        have hfloor := hcasc.floor₂ v.2 hτtail
        obtain ⟨hf1, hb1⟩ := markedQI_shrinkShape_both hs1 hsD4 v.1
        obtain ⟨hf2, hb2⟩ := markedQI_shrinkShape_both hs1 hsD4 v.2
        rw [hsh] at hf1 hb1
        have hDle : (D : ℝ) ≤ 27 * (D : ℝ) ^ 4 := le_netScale_self hDR
        have hD0 : (0 : ℝ) ≤ (D : ℝ) := by linarith
        have hcompat : compat G v (shrinkShape s v.2, v.2) :=
          compat_pairNetS_of_marked (hf1.mono hD0 hDle) (hb1.mono hD0 hDle)
            (hb2.mono hD0 hDle) (hf2.mono hD0 hDle)
        refine le_trans ?_ (single_le_gdeg π G hcompat)
        have hsupp2 : Shape.Supported v.2 := hsh ▸ supported_shrinkShape hs1 v.1
        have hpoint : ENNReal.ofReal (p ^ v.2.size) ≤ shapePMF θ' hq' hq0' h2' v.2 :=
          ofReal_pow_le_shapePMF θ' hq' hq0' h2' hp0 (min_le_right _ _) v.2 hsupp2
        have hexp : v.2.size ≤ 16 * (sz v / s + 1) := by
          have hsz : v.1.size ≤ sz v := le_max_left _ _
          have h := size_shrinkShape_le hs1 v.1
          rw [hsh] at h
          have hdiv : v.1.size / s ≤ sz v / s := Nat.div_le_div_right hsz
          omega
        have hne : π (shrinkShape s v.2, v.2) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (π.coe_le_one _)
        calc bb (sz v) = p ^ (16 * (sz v / s + 1)) / 2 := by
              rw [hbbdef]
          _ ≤ p ^ v.2.size / 2 := by
              have := pow_le_pow_of_le_one hp0.le hp1 hexp
              linarith
          _ ≤ (shapePMF θ' hq' hq0' h2' v.2).toReal / 2 := by
              have h := ENNReal.toReal_mono
                (ne_top_of_le_ne_top ENNReal.one_ne_top
                  ((shapePMF θ' hq' hq0' h2').coe_le_one v.2)) hpoint
              rw [ENNReal.toReal_ofReal (by positivity)] at h
              linarith
          _ = (shapePMF θ' hq' hq0' h2' v.2 / 2).toReal := by
              rw [ENNReal.toReal_div]
              norm_num
          _ ≤ (π (shrinkShape s v.2, v.2)).toReal := ENNReal.toReal_mono hne hfloor
    · -- a cascade pair of a source of the second law
      by_cases hτ : v.1.size ≤ D ^ 2
      · have hτR : ((v.1.size : ℝ)) ≤ (D : ℝ) * (D : ℝ) := by
          calc ((v.1.size : ℝ)) ≤ ((D ^ 2 : ℕ) : ℝ) := by exact_mod_cast hτ
            _ = (D : ℝ) * (D : ℝ) := by push_cast; ring
        have hgd : 1 - Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ gdeg π G v := by
          refine one_sub_le_gdeg_of_small π G sz (D ^ 2) v (fun y hy ↦ ?_)
            (Real.exp_pos _).le hlarge
          obtain ⟨hy1, hy2⟩ := hcast y hy
          obtain ⟨hts1, hts2⟩ := markedQI_tail_small hs1 hD1 hsD4 v.2 y.1
            (by rw [hsh]; exact hτR) hy1
          have h0 : (0 : ℝ) ≤ 9 * (D : ℝ) ^ 3 := by positivity
          have hle := coupScale_le_netScale hDR
          exact compat_pairNetS_of_marked
            ((markedQI_small_pair hDR hτR hy2).mono h0 hle)
            ((markedQI_small_pair hDR hy2 hτR).mono h0 hle) hts2 hts1
        linarith [hbbhalf (sz v)]
      · have hτtail : D ^ 2 < v.1.size := by omega
        have hfloor := hcasc.floor₁ v.1 hτtail
        obtain ⟨hf1, hb1⟩ := markedQI_shrinkShape_both hs1 hsD4 v.1
        obtain ⟨hf2, hb2⟩ := markedQI_shrinkShape_both hs1 hsD4 v.2
        rw [hsh] at hf2 hb2
        have hDle : (D : ℝ) ≤ 27 * (D : ℝ) ^ 4 := le_netScale_self hDR
        have hD0 : (0 : ℝ) ≤ (D : ℝ) := by linarith
        have hcompat : compat G v (v.1, shrinkShape s v.1) :=
          compat_pairNetS_of_marked (hf1.mono hD0 hDle) (hb1.mono hD0 hDle)
            (hb2.mono hD0 hDle) (hf2.mono hD0 hDle)
        refine le_trans ?_ (single_le_gdeg π G hcompat)
        have hsupp1 : Shape.Supported v.1 := hsh ▸ supported_shrinkShape hs1 v.2
        have hpoint : ENNReal.ofReal (p ^ v.1.size) ≤ shapePMF θ hq hq0 h2 v.1 :=
          ofReal_pow_le_shapePMF θ hq hq0 h2 hp0 (min_le_left _ _) v.1 hsupp1
        have hexp : v.1.size ≤ 16 * (sz v / s + 1) := by
          have hsz : v.2.size ≤ sz v := le_max_right _ _
          have h := size_shrinkShape_le hs1 v.2
          rw [hsh] at h
          have hdiv : v.2.size / s ≤ sz v / s := Nat.div_le_div_right hsz
          omega
        have hne : π (v.1, shrinkShape s v.1) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (π.coe_le_one _)
        calc bb (sz v) = p ^ (16 * (sz v / s + 1)) / 2 := by
              rw [hbbdef]
          _ ≤ p ^ v.1.size / 2 := by
              have := pow_le_pow_of_le_one hp0.le hp1 hexp
              linarith
          _ ≤ (shapePMF θ hq hq0 h2 v.1).toReal / 2 := by
              have h := ENNReal.toReal_mono
                (ne_top_of_le_ne_top ENNReal.one_ne_top
                  ((shapePMF θ hq hq0 h2).coe_le_one v.1)) hpoint
              rw [ENNReal.toReal_ofReal (by positivity)] at h
              linarith
          _ = (shapePMF θ hq hq0 h2 v.1 / 2).toReal := by
              rw [ENNReal.toReal_div]
              norm_num
          _ ≤ (π (v.1, shrinkShape s v.1)).toReal := ENNReal.toReal_mono hne hfloor
    · -- a closure pair has no size above the block
      exfalso
      have : sz v ≤ D ^ 2 := max_le h1 h2s
      omega
  -- the weight of the tail masses
  set γ : ℝ := 40 * L / (s : ℝ) with hγdef
  have hsc : 80 * L / c ≤ (s : ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    have h1 : (⌈80 * L / c⌉₊ : ℕ) ≤ s := by omega
    exact_mod_cast h1
  have hγ : γ ≤ c / 2 := by
    rw [hγdef, div_le_div_iff₀ hsR0 (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ hc] at hsc
    nlinarith
  have hwle : ∀ n : ℕ, wgt (bb n) ≤ 6 * Real.exp (40 * L) * Real.exp (γ * (n : ℝ)) := by
    intro n
    have hb : Real.exp (-(L * ((16 * (n / s + 1) : ℕ) : ℝ))) / 2 ≤ bb n := by
      have hbbn : bb n = p ^ (16 * (n / s + 1)) / 2 := by rw [hbbdef]
      rw [hbbn, pow_eq_exp_neg_log_inv hp0, hLdef]
    refine (wgt_le_of_half_exp hb).trans ?_
    have hcastm : ((16 * (n / s + 1) : ℕ) : ℝ) = 16 * (((n / s : ℕ) : ℝ) + 1) := by
      push_cast
      ring
    have hdiv : ((n / s : ℕ) : ℝ) ≤ (n : ℝ) / (s : ℝ) := Nat.cast_div_le
    have hexp : 5 / 2 * (L * ((16 * (n / s + 1) : ℕ) : ℝ)) ≤ γ * (n : ℝ) + 40 * L := by
      rw [hcastm, hγdef]
      have h1 : 40 * L * ((n / s : ℕ) : ℝ) ≤ 40 * L * ((n : ℝ) / (s : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (by linarith)
      have h2 : 40 * L * ((n : ℝ) / (s : ℝ)) = 40 * L / (s : ℝ) * (n : ℝ) := by ring
      nlinarith
    calc 6 * Real.exp (5 / 2 * (L * ((16 * (n / s + 1) : ℕ) : ℝ)))
        ≤ 6 * Real.exp (γ * (n : ℝ) + 40 * L) := by
          have := Real.exp_le_exp.mpr hexp
          linarith
      _ = 6 * Real.exp (40 * L) * Real.exp (γ * (n : ℝ)) := by
          rw [Real.exp_add]
          ring
  have hgterm : ∀ n : ℕ, g n * wgt (bb n)
      ≤ 6 * Real.exp (40 * L) * (g n * Real.exp (γ * (n : ℝ))) := by
    intro n
    calc g n * wgt (bb n) ≤ g n * (6 * Real.exp (40 * L) * Real.exp (γ * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left (hwle n) (hg0 n)
      _ = 6 * Real.exp (40 * L) * (g n * Real.exp (γ * (n : ℝ))) := by ring
  have hmaj : Summable fun n : ℕ ↦
      6 * Real.exp (40 * L) * (g n * Real.exp (γ * (n : ℝ))) :=
    (summable_eta_tail hc hg0 hgle hγ).mul_left _
  have hsum : Summable fun n : ℕ ↦ g n * wgt (bb n) :=
    Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (hg0 n) (wgt_nonneg (hbb0 n) (hbb1 n))) hgterm hmaj
  -- the assembled bound
  have hmain := etaG_le_size π G sz (D ^ 2) (Real.exp_pos _).le hhalf hsmall hbb0 hbb1
    hg0 hmass hball hsum
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have htailsum : ∑' n : ℕ, g n * wgt (bb n)
      ≤ C₂ * Real.exp (-(c / 2) * ((D : ℝ) ^ 2)) := by
    have h1 := Summable.tsum_le_tsum hgterm hsum hmaj
    rw [tsum_mul_left] at h1
    have h2 := eta_tail_sum (N := D ^ 2) hc hg0 hgle hgvan hγ
    rw [hcastD2] at h2
    refine h1.trans ?_
    calc 6 * Real.exp (40 * L) * ∑' n : ℕ, g n * Real.exp (γ * (n : ℝ))
        ≤ 6 * Real.exp (40 * L)
            * ((1 - Real.exp (-(c / 2)))⁻¹ * Real.exp (-(c / 2) * ((D : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C₂ * Real.exp (-(c / 2) * ((D : ℝ) ^ 2)) := by rw [hC₂def]; ring
  have hfin := hD₂ D hDD₂
  have hrw : Real.exp (-(c / 4) * ((D : ℝ) ^ 2)) = Real.exp (-(c / 4 * (D : ℝ) ^ 2)) := by
    rw [neg_mul]
  rw [hrw] at hfin
  linarith

/-! ### `eq:hairy-rate` across two laws -/

/-- **`eq:hairy-rate` across two laws** (`thm:hairy`): past a threshold, the two sampled
trees admit an `8·972²D⁸`-quasi-isometry outside an event of probability at most
`16η_{𝖰,5/2}(q) ≤ 16e^{-c₃D²}`, over the coupling of `thm:shape-coupling` and the label
graph at the edge scale `27D⁴`. -/
theorem hairy_rate_two_law (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → ∃ π : PMF (Shape × Shape),
      IsShapeCoupling (D : ℝ) (shapePMF θ hq hq0 h2) (shapePMF θ' hq' hq0' h2') π ∧
      twoHairyMeasure θ θ'
          {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
            IsSampleQI (8 * 972 ^ 2 * (D : ℝ) ^ 8) F}
        ≤ 16 * etaG π (pairNetS π (D : ℝ)) ∧
      etaG π (pairNetS π (D : ℝ)) ≤ ENNReal.ofReal (Real.exp (-(c₃ * (D : ℝ) ^ 2))) := by
  obtain ⟨c₃, hc₃, D₀, hD₀⟩ := exists_isShapeCoupling_etaS θ θ' hq hq0 h2 hq' hq0' h2'
  refine ⟨c₃, hc₃, D₀ + 1, fun D hD ↦ ?_⟩
  have hDD₀ : D₀ ≤ D := by omega
  have hD1 : 1 ≤ D := by omega
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  obtain ⟨hexp, π, hπ, hη⟩ := hD₀ D hDD₀
  have hη4 : etaG π (pairNetS π (D : ℝ)) ≤ 1 / 10000 := by
    refine hη.trans ((ENNReal.ofReal_le_ofReal hexp).trans (le_of_eq ?_))
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  have hmain := hairy_rate_tree_scale θ θ' hq hq' h2 h2' π (pairNetS π (D : ℝ)) hD1
    (measurableSet_pairLab_fibre π) (measurableSet_pairLab'_fibre π)
    (hairyMeasure_pairLab_prod θ hq hq0 h2 π hπ.marg₁)
    (hairyMeasure_pairLab'_prod θ' hq' hq0' h2' π hπ.marg₂)
    (markedQI_of_compat_pairLabS hDR θ θ' hq hq0 h2 hq' hq0' h2' hπ hπ.marg₁ hπ.marg₂)
    hη4
  exact ⟨π, hπ, hmain, hη⟩

end ChainClasses
