import ChainClasses.Bushy.ShapeEtaBlock
import ChainClasses.Bushy.ShapeSizeTail
import ChainClasses.Bushy.ShapeCouplingSelf
import ChainClasses.Shape.Binarise

/-!
`sec:shape-eta` and `sec:hairy-universality` of `gw_classes_simple.tex`: the potential
bound `thm:shape-eta` at the label law of `thm:shape-coupling` for one law, and
`thm:hairy` over it with no hypothesis left.

`ShapeEtaBlock` carries the summation of `eq:potential` over an arbitrary vertex type
with an arbitrary size, `ShapeSizeTail` the tail of
`thm:shape-mass` (`it:shape-mass-tail`), `ShapeShrink` the collapse of a shape of
small diameter and `Binarise` the shrinking of
`thm:shape-shrink` (`it:shape-shrink`).  What is left is the geometry that turns
those into the three inputs `etaG_shape_le` consumes, at the vertex type `Shape` with the
size `Shape.size`.

* `shapePMF_eq_tsum`, `shapeMass_le_shapePMF`, `tsum_fibre_size_shapePMF`: **the label law
  read off the shape law**, the pushforward along the fix of
  `thm:shape-shrink` (`it:shape-fix`), which only adds mass and carries the size
  fibres onto the law of `fixSizeMass`.
* `Tri.count_ne_one_of_full`, `bushPointBound_full`,
  `ofReal_pow_size_le_shapeMass_supported`: **`thm:shape-mass` (`it:shape-mass-point`)
  in the support**, where no neck vertex is bare and no bush vertex has one child, so the
  weight `θ₁` never enters and the bound holds without assuming `θ₁ > 0`.
* `shapeWeight`: the constant `p` of the point bound, the least of `θ₀`, `θ₂` and the
  split weight `θ̃₂`.
* `markedQI_small_pair`, `compat_shapeNet_of_small`: **the collapse**, small shapes being
  `9D³`-comparable both ways through the one-vertex shape, hence linked in `def:shape-net`,
  the edge scale `27D⁴` leaving room.
* `exists_supported_compat_shapeNet`, `pow_le_gdeg_shapeNet`: **`eq:shape-domination`**, a
  shape being `3D²`-comparable to a shape of size `16(n/s+1)` in the support, whose
  quasi-inverse is `27D⁴`-marked and whose mass the point bound bounds below.
* `one_sub_le_gdeg_of_small`, `tsum_shapePMF_large_le`: the mass of the block and the mass
  above a size threshold, from the exponential tail.
* `exists_etaG_shapeNet_le`: **`eq:shape-eta`**, with `exists_etaG_shapeNet_le_ofReal` and
  `exists_etaG_shapeNet_small` the potential condition of `thm:matching`.
* `hairy_rate_shape_tree`, `hairy_ae_shape_tree`: **`thm:hairy` for one law**, with the
  potential hypothesis discharged.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory GraphMatching
open BranchingProcess (sample Survives survivalMeasure bushMeasure Offspring)
open scoped ENNReal Classical

/-! ### The label law read off the shape law -/

/-- **The label law of `thm:shape-coupling` for one law**: the shape law pushed forward
along the fix, the uniform variable not entering. -/
lemma shapePMF_eq_tsum (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (x : Shape) :
    shapePMF θ hq hq0 h2 x = ∑' τ : Shape, if τ.fix = x then shapeMass θ τ else 0 := by
  have hval : shapePMF θ hq hq0 h2 x = labMass θ shapeLabel x := rfl
  rw [hval, labMass]
  refine tsum_congr fun τ ↦ ?_
  by_cases h : τ.fix = x
  · have hset : {u : ℝ | shapeLabel τ u = x} = Set.univ := by
      ext u
      simp [h]
    rw [hset, measure_univ, mul_one, if_pos h]
  · have hset : {u : ℝ | shapeLabel τ u = x} = (∅ : Set ℝ) := by
      ext u
      simp [h]
    rw [hset, measure_empty, mul_zero, if_neg h]

/-- The fix is the identity on the support, so the pushforward only adds mass there. -/
lemma shapeMass_le_shapePMF (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {σ : Shape} (hσ : Shape.Supported σ) :
    shapeMass θ σ ≤ shapePMF θ hq hq0 h2 σ := by
  rw [shapePMF_eq_tsum θ hq hq0 h2]
  have hterm : (if σ.fix = σ then shapeMass θ σ else 0) = shapeMass θ σ :=
    if_pos (fix_eq_self hσ)
  calc shapeMass θ σ = if σ.fix = σ then shapeMass θ σ else 0 := hterm.symm
    _ ≤ ∑' τ : Shape, if τ.fix = σ then shapeMass θ τ else 0 := ENNReal.le_tsum σ

/-- **The size fibres of the label law**: the labels of a given size carry the mass of the
shapes whose fix has that size, which is the law `fixSizeMass`. -/
lemma tsum_fibre_size_shapePMF (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (n : ℕ) :
    ∑' v : {v : Shape // v.size = n}, shapePMF θ hq hq0 h2 (v : Shape)
      = shapeStatMassE θ (fun σ ↦ σ.fix.size) n := by
  calc ∑' v : {v : Shape // v.size = n}, shapePMF θ hq hq0 h2 (v : Shape)
      = ∑' (v : {v : Shape // v.size = n}) (τ : Shape),
          (if τ.fix = (v : Shape) then shapeMass θ τ else 0) :=
        tsum_congr fun v ↦ shapePMF_eq_tsum θ hq hq0 h2 _
    _ = ∑' (τ : Shape) (v : {v : Shape // v.size = n}),
          (if τ.fix = (v : Shape) then shapeMass θ τ else 0) := ENNReal.tsum_comm
    _ = ∑' τ : Shape, (if τ.fix.size = n then shapeMass θ τ else 0) := by
        refine tsum_congr fun τ ↦ ?_
        by_cases hτ : τ.fix.size = n
        · rw [if_pos hτ]
          refine (tsum_eq_single ⟨τ.fix, hτ⟩ fun v hv ↦ ?_).trans (if_pos rfl)
          exact if_neg fun h ↦ hv (Subtype.ext h.symm)
        · rw [if_neg hτ]
          refine (tsum_congr fun v ↦ if_neg fun h ↦ hτ ?_).trans tsum_zero
          rw [h]
          exact v.2
    _ = shapeStatMassE θ (fun σ ↦ σ.fix.size) n := rfl

/-! ### The law of a size statistic as a real weight -/

lemma tsum_shapeStatMassE (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (f : Shape → ℕ) :
    ∑' n : ℕ, shapeStatMassE θ f n = 1 := by
  have h := tsum_pow_shapeStatMassE θ f 1
  simp only [one_pow, one_mul, mul_one] at h
  rw [h]
  exact tsum_shapeMass θ hq hq0 h2

lemma shapeStatMassE_ne_top (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (f : Shape → ℕ) (n : ℕ) :
    shapeStatMassE θ f n ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← tsum_shapeStatMassE θ hq hq0 h2 f]
  exact ENNReal.le_tsum n

lemma ofReal_shapeStatMass (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (f : Shape → ℕ) (n : ℕ) :
    ENNReal.ofReal (shapeStatMass θ f n) = shapeStatMassE θ f n :=
  ENNReal.ofReal_toReal (shapeStatMassE_ne_top θ hq hq0 h2 f n)

lemma summable_shapeStatMass (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (f : Shape → ℕ) :
    Summable (shapeStatMass θ f) := by
  refine ENNReal.summable_toReal ?_
  rw [tsum_shapeStatMassE θ hq hq0 h2 f]
  exact ENNReal.one_ne_top

/-! ### The point mass in the support -/

/-- A tree in the support has no vertex with exactly one child, read on the field that
cuts it out. -/
lemma Tri.count_ne_one_of_full : ∀ {t : Tri}, t.Full → ∀ v : Amb, t.count v ≠ 1 := by
  intro t
  induction t with
  | leaf => intro _ v; simp
  | one t ih => intro h; exact absurd h id
  | two l r ihl ihr =>
      intro h v
      cases v with
      | nil => simp
      | cons i w =>
          rw [Tri.count_two_cons]
          split
          · exact ihl h.1 w
          · exact ihr h.2 w

/-- **`thm:shape-mass` (`it:shape-mass-point`), the bush input in the support**: a
bush with no vertex of exactly one child has mass at least `p^n`, `p` a lower bound for
`θ₀` and `θ₂` alone, the weight `θ₁` never being read. -/
theorem bushPointBound_full (θ : Offspring 2) {p : ℝ} (hp0 : 0 ≤ p) (h0 : p ≤ θ 0)
    (h2 : p ≤ θ 2) {t : Tri} (ht : t.Full) :
    ENNReal.ofReal (p ^ t.size) ≤ bushMeasure (N := 2) θ {d : Amb → ℕ | bushTri d = t} := by
  have hnull := bushMeasure_offspring_le θ
  have hfin := t.finite_sample_count
  have hmass : ∀ v ∈ sample t.count, p ≤ θ (t.count v) := by
    intro v _
    have hle := t.count_le_two v
    have hne := Tri.count_ne_one_of_full ht v
    have hcases : t.count v = 0 ∨ t.count v = 2 := by omega
    rcases hcases with h | h <;> rw [h] <;> assumption
  have hbase := BranchingProcess.ofReal_pow_le_bushMeasure_sample_eq (N := 2) θ hfin hmass
  have hsub : {c : Amb → ℕ | (sample c : Set Amb) = (sample t.count : Set Amb)}
      \ {c : Amb → ℕ | ¬ ∀ v, c v ≤ 2} ⊆ {d : Amb → ℕ | bushTri d = t} := by
    rintro c ⟨hc, hc2⟩
    have hd : ∀ v, c v ≤ 2 := not_not.mp hc2
    have hcfin : ¬ Survives c := by
      rw [Survives, hc]
      exact Set.not_infinite.mpr hfin
    refine Tri.ext_isAddr _ _ fun a ↦ ?_
    have hmem := Set.ext_iff.mp hc (letters a)
    simp only [SetLike.mem_coe] at hmem
    rw [isAddr_bushTri hd hcfin a, hmem, Tri.mem_sample_count, bits_letters]
  calc ENNReal.ofReal (p ^ t.size)
      = ENNReal.ofReal p ^ t.size := ENNReal.ofReal_pow hp0 _
    _ = ENNReal.ofReal p ^ (sample t.count : Set Amb).ncard := by rw [t.ncard_sample_count]
    _ ≤ bushMeasure (N := 2) θ
          {c : Amb → ℕ | (sample c : Set Amb) = (sample t.count : Set Amb)} := hbase
    _ = bushMeasure (N := 2) θ
          ({c : Amb → ℕ | (sample c : Set Amb) = (sample t.count : Set Amb)}
            \ {c : Amb → ℕ | ¬ ∀ v, c v ≤ 2}) := (measure_sdiff_null hnull).symm
    _ ≤ bushMeasure (N := 2) θ {d : Amb → ℕ | bushTri d = t} := measure_mono hsub

section Point

variable {θ : Offspring 2} {p : ℝ}

/-- A decoration in the support contributes one power of `p` per vertex of its bush and one for
the neck vertex carrying it. -/
lemma ofReal_pow_le_decMass_full (hp0 : 0 < p) (h0 : p ≤ θ 0) (h2 : p ≤ θ 2)
    (hd : p ≤ θ 2 * 2 * θ.extinction) {o : Option Tri} (ho : Tri.optFull o) :
    ENNReal.ofReal (p ^ (Tri.optSize o + 1)) ≤ decMass θ o := by
  cases o with
  | none => exact absurd ho id
  | some t =>
      have hsplit : p ^ (Tri.optSize (some t) + 1) = p * p ^ t.size := by
        rw [Tri.optSize_some, pow_succ]
        ring
      rw [decMass, hsplit, ENNReal.ofReal_mul hp0.le]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hd) (bushPointBound_full θ hp0.le h0 h2 ho)

lemma ofReal_pow_le_prod_decMass_full (hp0 : 0 < p) (h0 : p ≤ θ 0) (h2 : p ≤ θ 2)
    (hd : p ≤ θ 2 * 2 * θ.extinction) :
    ∀ l : List (Option Tri), (∀ b ∈ l, Tri.optFull b) →
      ENNReal.ofReal (p ^ ((l.map Tri.optSize).sum + l.length))
        ≤ (l.map (decMass θ)).prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons o l ih =>
      intro hl
      have hexp : ((o :: l).map Tri.optSize).sum + (o :: l).length
          = (Tri.optSize o + 1) + ((l.map Tri.optSize).sum + l.length) := by
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      rw [hexp, pow_add, ENNReal.ofReal_mul (pow_nonneg hp0.le _), List.map_cons,
        List.prod_cons]
      exact mul_le_mul'
        (ofReal_pow_le_decMass_full hp0 h0 h2 hd (hl o (List.mem_cons_self ..)))
        (ih fun b hb ↦ hl b (List.mem_cons_of_mem _ hb))

/-- **`thm:shape-mass` (`it:shape-mass-point`) in the support**: the mass of a
shape in the support is a product of one factor per vertex, none of them `θ₁`, so it is at
least `p` to the size with `p` the least of `θ₀`, `θ₂` and the split weight. -/
theorem ofReal_pow_size_le_shapeMass_supported (hp0 : 0 < p) (h0 : p ≤ θ 0) (h2 : p ≤ θ 2)
    (hd : p ≤ θ 2 * 2 * θ.extinction) (hk : p ≤ θ.skeletonWeight 2) {σ : Shape}
    (hσ : Shape.Supported σ) :
    ENNReal.ofReal (p ^ σ.size) ≤ shapeMass θ σ := by
  have hsize : σ.size = ((σ.decs.map Tri.optSize).sum + σ.decs.length) + 1 := by
    rw [Shape.size_eq', Shape.neckLen, Shape.decs_length]
    omega
  rw [hsize, pow_succ, ENNReal.ofReal_mul (pow_nonneg hp0.le _), shapeMass]
  exact mul_le_mul' (ofReal_pow_le_prod_decMass_full hp0 h0 h2 hd σ.decs hσ)
    (ENNReal.ofReal_le_ofReal hk)

end Point

/-! ### The constant of the point bound -/

/-- The constant `p` of `thm:shape-mass` (`it:shape-mass-point`) in the support:
the least of `θ₀`, `θ₂` and the split weight `θ̃₂`. -/
noncomputable def shapeWeight (θ : Offspring 2) : ℝ :=
  min (min (θ 0) (θ 2)) (θ.skeletonWeight 2)

lemma shapeWeight_le_zero (θ : Offspring 2) : shapeWeight θ ≤ θ 0 :=
  (min_le_left _ _).trans (min_le_left _ _)

lemma shapeWeight_le_two (θ : Offspring 2) : shapeWeight θ ≤ θ 2 :=
  (min_le_left _ _).trans (min_le_right _ _)

lemma shapeWeight_le_skeletonWeight (θ : Offspring 2) :
    shapeWeight θ ≤ θ.skeletonWeight 2 := min_le_right _ _

lemma shapeWeight_pos (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) : 0 < shapeWeight θ := by
  have h0 : 0 < θ 0 := by
    rw [← mul_extinction_eq θ hq]
    exact mul_pos h2 hq0
  exact lt_min (lt_min h0 h2) (skeletonWeight_two_pos θ hq h2)

lemma shapeWeight_le_one (θ : Offspring 2) : shapeWeight θ ≤ 1 := by
  have htot := total_of_two θ
  have h0 := θ.nonneg 0
  have h1 := θ.nonneg 1
  exact (shapeWeight_le_two θ).trans (by linarith)

/-- **`thm:shape-mass` (`it:shape-mass-point`)** at the constant `shapeWeight`. -/
theorem ofReal_pow_size_le_shapeMass_of_supported (θ : Offspring 2)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {σ : Shape}
    (hσ : Shape.Supported σ) :
    ENNReal.ofReal (shapeWeight θ ^ σ.size) ≤ shapeMass θ σ := by
  have hd : shapeWeight θ ≤ θ 2 * 2 * θ.extinction := by
    rw [decoration_weight_eq θ hq]
    linarith [shapeWeight_le_zero θ, θ.nonneg 0]
  exact ofReal_pow_size_le_shapeMass_supported (shapeWeight_pos θ hq hq0 h2)
    (shapeWeight_le_zero θ) (shapeWeight_le_two θ) hd (shapeWeight_le_skeletonWeight θ) hσ

/-! ### The small shapes are one block of `def:shape-net` -/

/-- **`thm:shape-eta`, the collapse**: two shapes of size at most `K²` are
`9K³`-comparable, each being `K`-comparable to the one-vertex shape. -/
theorem markedQI_small_pair {K : ℝ} (hK : 1 ≤ K) {σ τ : Shape}
    (hσ : (σ.size : ℝ) ≤ K * K) (hτ : (τ.size : ℝ) ≤ K * K) :
    MarkedQI (9 * K ^ 3) (shapeSpace σ) (shapeSpace τ) := by
  have hK2 : (1 : ℝ) ≤ 3 * K ^ 2 := by nlinarith
  have h1 : MarkedQI K (shapeSpace σ) (listSpace []) := markedQI_collapse hK σ hσ
  have h2 : MarkedQI (3 * K ^ 2) (listSpace []) (shapeSpace τ) :=
    markedQI_symm hK (markedQI_collapse hK τ hτ)
  have h3 := markedQI_comp hK hK2 h1 h2
  have e : 3 * K * (3 * K ^ 2) = 9 * K ^ 3 := by ring
  rwa [e] at h3

/-- **The small block**: shapes of size at most `D²` are pairwise linked in
`def:shape-net`, the scale `9D³` of the collapse lying below the edge scale `27D⁴`. -/
theorem compat_shapeNet_of_small {Dq : ℝ} (hD : 1 ≤ Dq) {σ τ : Shape}
    (hσ : (σ.size : ℝ) ≤ Dq * Dq) (hτ : (τ.size : ℝ) ≤ Dq * Dq) :
    compat (shapeNet Dq) σ τ := by
  by_cases h : σ = τ
  · exact Or.inl h
  · have h3 : (1 : ℝ) ≤ Dq ^ 3 := one_le_pow₀ hD
    have h4 : Dq ^ 3 ≤ Dq ^ 4 := by nlinarith
    have hle : 9 * Dq ^ 3 ≤ 27 * Dq ^ 4 := by linarith
    have h0 : (0 : ℝ) ≤ 9 * Dq ^ 3 := by linarith
    exact Or.inr ⟨h, (markedQI_small_pair hD hσ hτ).mono h0 hle,
      (markedQI_small_pair hD hτ hσ).mono h0 hle⟩

/-! ### The shrinking, `eq:shape-domination` -/

/-- **`eq:shape-domination`, the geometry**: a shape is linked in `def:shape-net` to a
shape in the support of size at most `16(n/s+1)`.  The shrinking of
`thm:shape-shrink` (`it:shape-shrink`) is taken at the scale `3D²`, so that its
quasi-inverse is `27D⁴`-marked, which is the edge scale. -/
theorem exists_supported_compat_shapeNet {Dq : ℝ} (hD : 1 ≤ Dq) {s : ℕ} (hs : 1 ≤ s)
    (hsD : 2592 * (s : ℝ) ^ 2 ≤ 3 * Dq ^ 2) (σ : Shape) :
    ∃ σ₀ : Shape, Shape.Supported σ₀ ∧ σ₀.size ≤ 16 * (σ.size / s + 1) ∧
      compat (shapeNet Dq) σ σ₀ := by
  obtain ⟨σ₀, hsup, hsize, hqi⟩ := markedQI_shape_shrink_of_le hs hsD σ
  refine ⟨σ₀, hsup, hsize, ?_⟩
  by_cases h : σ = σ₀
  · exact Or.inl h
  · have h2 : (1 : ℝ) ≤ Dq ^ 2 := one_le_pow₀ hD
    have h4 : Dq ^ 2 ≤ Dq ^ 4 := by nlinarith
    have h1 : (1 : ℝ) ≤ 3 * Dq ^ 2 := by linarith
    have hback := markedQI_symm h1 hqi
    have e : 3 * (3 * Dq ^ 2) ^ 2 = 27 * Dq ^ 4 := by ring
    rw [e] at hback
    have hfwd : MarkedQI (27 * Dq ^ 4) (shapeSpace σ) (shapeSpace σ₀) :=
      hqi.mono (by linarith) (by linarith)
    exact Or.inr ⟨h, hfwd, hback⟩

/-- A power of `p` written as an exponential, the form `thm:shape-eta` reads the point
bound in. -/
lemma pow_eq_exp_neg_log_inv {p : ℝ} (hp : 0 < p) (m : ℕ) :
    p ^ m = Real.exp (-(Real.log p⁻¹ * (m : ℝ))) := by
  rw [Real.log_inv, show -(-Real.log p * (m : ℝ)) = Real.log p * (m : ℝ) by ring,
    exp_mul_nat, Real.exp_log hp]

/-- **`eq:shape-domination`**: the compatible mass at a shape of size `n` is at least the
point mass `p^{16(n/s+1)}` of the shape its shrinking lands in. -/
theorem pow_le_gdeg_shapeNet (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {Dq : ℝ} (hD : 1 ≤ Dq) {s : ℕ} (hs : 1 ≤ s)
    (hsD : 2592 * (s : ℝ) ^ 2 ≤ 3 * Dq ^ 2) (σ : Shape) :
    shapeWeight θ ^ (16 * (σ.size / s + 1))
      ≤ gdeg (shapePMF θ hq hq0 h2) (shapeNet Dq) σ := by
  obtain ⟨σ₀, hsup, hsize, hcompat⟩ := exists_supported_compat_shapeNet hD hs hsD σ
  have hp0 : 0 < shapeWeight θ := shapeWeight_pos θ hq hq0 h2
  have hmass : ENNReal.ofReal (shapeWeight θ ^ σ₀.size) ≤ shapePMF θ hq hq0 h2 σ₀ :=
    (ofReal_pow_size_le_shapeMass_of_supported θ hq hq0 h2 hsup).trans
      (shapeMass_le_shapePMF θ hq hq0 h2 hsup)
  have hle : shapePMF θ hq hq0 h2 σ₀
      ≤ rE (shapePMF θ hq hq0 h2) (compat (shapeNet Dq)) σ := by
    rw [rE]
    calc (shapePMF θ hq hq0 h2 σ₀ : ℝ≥0∞)
        = if compat (shapeNet Dq) σ σ₀ then shapePMF θ hq hq0 h2 σ₀ else 0 :=
          (if_pos hcompat).symm
      _ ≤ ∑' y, if compat (shapeNet Dq) σ y then shapePMF θ hq hq0 h2 y else 0 :=
          ENNReal.le_tsum σ₀
  have htoReal := ENNReal.toReal_mono
    (rE_ne_top (μ := shapePMF θ hq hq0 h2) (R := compat (shapeNet Dq)) (x := σ))
    (hmass.trans hle)
  rw [ENNReal.toReal_ofReal (pow_nonneg hp0.le _)] at htoReal
  show shapeWeight θ ^ (16 * (σ.size / s + 1))
    ≤ (rE (shapePMF θ hq hq0 h2) (compat (shapeNet Dq)) σ).toReal
  exact le_trans (pow_le_pow_of_le_one hp0.le (shapeWeight_le_one θ) hsize) htoReal

/-! ### The mass above a size threshold -/

/-- The mass splits at a size threshold. -/
lemma tsum_small_add_tsum_large {V : Type*} (μ : PMF V) (sz : V → ℕ) (N : ℕ) :
    (∑' y, if sz y ≤ N then μ y else 0) + (∑' y, if sz y ≤ N then 0 else μ y) = 1 := by
  rw [← ENNReal.tsum_add, ← μ.tsum_coe]
  exact tsum_congr fun y ↦ by split_ifs <;> simp

/-- **The block of `thm:shape-coupling`**: a vertex compatible with everything of size at
most `N` has ball mass at least `1-E` once the mass above `N` is at most `E`. -/
lemma one_sub_le_gdeg_of_small {V : Type*} (μ : PMF V) (G : SimpleGraph V) (sz : V → ℕ)
    (N : ℕ) (v : V) (hv : ∀ y, sz y ≤ N → compat G v y) {E : ℝ} (hE0 : 0 ≤ E)
    (hlarge : (∑' y, if sz y ≤ N then 0 else μ y) ≤ ENNReal.ofReal E) :
    1 - E ≤ gdeg μ G v := by
  have hsplit := tsum_small_add_tsum_large μ sz N
  have hsmallle : (∑' y, if sz y ≤ N then μ y else 0) ≤ rE μ (compat G) v := by
    rw [rE]
    refine ENNReal.tsum_le_tsum fun y ↦ ?_
    by_cases hy : sz y ≤ N
    · rw [if_pos hy, if_pos (hv y hy)]
    · rw [if_neg hy]
      exact zero_le
  have hA : (∑' y, if sz y ≤ N then μ y else 0) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit ▸ le_self_add)
  have hB : (∑' y, if sz y ≤ N then 0 else μ y) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit ▸ le_add_self)
  have hreal : (∑' y, if sz y ≤ N then μ y else 0).toReal
      + (∑' y, if sz y ≤ N then 0 else μ y).toReal = 1 := by
    rw [← ENNReal.toReal_add hA hB, hsplit, ENNReal.toReal_one]
  have hBle : (∑' y, if sz y ≤ N then 0 else μ y).toReal ≤ E := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlarge
    rwa [ENNReal.toReal_ofReal hE0] at h
  have hAle : (∑' y, if sz y ≤ N then μ y else 0).toReal ≤ (rE μ (compat G) v).toReal :=
    ENNReal.toReal_mono (rE_ne_top (μ := μ) (R := compat G) (x := v)) hsmallle
  show 1 - E ≤ (rE μ (compat G) v).toReal
  linarith

/-- **`thm:shape-mass` (`it:shape-mass-tail`) at the label law**: the labels of
size exceeding `N` carry mass at most `e^{-cN}`. -/
theorem tsum_shapePMF_large_le (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {c : ℝ} {n₀ : ℕ} (hc : 0 < c)
    (htail : ∀ N : ℕ, n₀ ≤ N → ∑' k : ℕ, fixSizeMass θ (k + N) ≤ Real.exp (-c * (N : ℝ)))
    {N : ℕ} (hN : n₀ ≤ N) :
    (∑' y : Shape, if y.size ≤ N then 0 else shapePMF θ hq hq0 h2 y)
      ≤ ENNReal.ofReal (Real.exp (-c * (N : ℝ))) := by
  have hfix0 : ∀ n : ℕ, 0 ≤ fixSizeMass θ n := fun n ↦ shapeStatMass_nonneg θ _ n
  have hfixsum : Summable (fixSizeMass θ) :=
    summable_shapeStatMass θ hq hq0 h2 fun σ ↦ σ.fix.size
  set hh : ℕ → ℝ := fun n ↦ if n ≤ N then 0 else fixSizeMass θ n with hhdef
  have hh0 : ∀ n, 0 ≤ hh n := by
    intro n
    rw [hhdef]
    by_cases hn : n ≤ N <;> simp [hn, hfix0 n]
  have hhle : ∀ n, hh n ≤ fixSizeMass θ n := by
    intro n
    rw [hhdef]
    by_cases hn : n ≤ N <;> simp [hn, hfix0 n]
  have hhsum : Summable hh := Summable.of_nonneg_of_le hh0 hhle hfixsum
  -- the tail sum, shifted past the threshold
  have hkey : ∑' n : ℕ, hh n ≤ Real.exp (-c * (N : ℝ)) := by
    have hzero : ∑ i ∈ Finset.range (N + 1), hh i = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hiN : i ≤ N := by
        have := Finset.mem_range.mp hi
        omega
      simp [hhdef, hiN]
    have hsplit := hhsum.sum_add_tsum_nat_add (N + 1)
    have hshift : ∀ k : ℕ, hh (k + (N + 1)) = fixSizeMass θ (k + (N + 1)) := by
      intro k
      have : ¬ (k + (N + 1) ≤ N) := by omega
      simp [hhdef, this]
    have heq : ∑' n : ℕ, hh n = ∑' k : ℕ, fixSizeMass θ (k + (N + 1)) := by
      rw [← tsum_congr hshift]
      linarith [hsplit, hzero]
    have hbnd := htail (N + 1) (by omega)
    have hmono : Real.exp (-c * ((N + 1 : ℕ) : ℝ)) ≤ Real.exp (-c * (N : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      push_cast
      nlinarith
    rw [heq]
    exact hbnd.trans hmono
  calc (∑' y : Shape, if y.size ≤ N then 0 else shapePMF θ hq hq0 h2 y)
      = ∑' n : ℕ, ∑' y : {y : Shape // y.size = n},
          (if (y : Shape).size ≤ N then 0 else shapePMF θ hq hq0 h2 y) :=
        tsum_fiber_size _ _
    _ = ∑' n : ℕ, ENNReal.ofReal (hh n) := by
        refine tsum_congr fun n ↦ ?_
        by_cases hn : n ≤ N
        · have hzero : ∀ y : {y : Shape // y.size = n},
              (if (y : Shape).size ≤ N then 0 else shapePMF θ hq hq0 h2 y) = 0 := by
            intro y
            rw [if_pos (by rw [y.2]; exact hn)]
          rw [tsum_congr hzero, tsum_zero, hhdef]
          simp [hn]
        · have hterm : ∀ y : {y : Shape // y.size = n},
              (if (y : Shape).size ≤ N then 0 else shapePMF θ hq hq0 h2 y)
                = shapePMF θ hq hq0 h2 y := by
            intro y
            rw [if_neg (by rw [y.2]; exact hn)]
          rw [tsum_congr hterm, tsum_fibre_size_shapePMF θ hq hq0 h2 n, hhdef]
          simp only [hn, if_false]
          exact (ofReal_shapeStatMass θ hq hq0 h2 (fun σ ↦ σ.fix.size) n).symm
    _ = ENNReal.ofReal (∑' n : ℕ, hh n) := (ENNReal.ofReal_tsum_of_nonneg hh0 hhsum).symm
    _ ≤ ENNReal.ofReal (Real.exp (-c * (N : ℝ))) := ENNReal.ofReal_le_ofReal hkey

/-! ### `eq:shape-eta` -/

/-- `y e^{-y} ≤ 1`, the inequality behind both largeness steps. -/
lemma mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 := by
  have h1 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-y), mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-y)).le]

/-- **`eq:shape-eta` for one law**: the potential of the label law of `thm:shape-coupling`
over the net `def:shape-net` at scale `D` is at most `e^{-cD²}`. -/
theorem exists_etaG_shapeNet_le (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      etaG (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ))
        ≤ ENNReal.ofReal (Real.exp (-(c * (D : ℝ) ^ 2))) := by
  classical
  obtain ⟨c, hc, n₀, htail⟩ := exists_fix_size_tail θ hq hq0 h2
  set p : ℝ := shapeWeight θ with hpdef
  have hp0 : 0 < p := shapeWeight_pos θ hq hq0 h2
  have hp1 : p ≤ 1 := shapeWeight_le_one θ
  set L : ℝ := Real.log p⁻¹ with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef, Real.log_inv]
    linarith [Real.log_nonpos hp0.le hp1]
  set C₁ : ℝ := 960 * L with hC₁def
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁def]; linarith
  set C₂ : ℝ := Real.exp (3 * C₁) * (1 - Real.exp (-(c / 2)))⁻¹ with hC₂def
  have hpos : (0 : ℝ) < 1 - Real.exp (-(c / 2)) := by
    linarith [exp_neg_half_lt_one hc]
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂def]
    positivity
  obtain ⟨D₁, hD₁⟩ := shape_eta_final (c := c) (C₂ := C₂) hc hC₂0
  have hfix0 : ∀ n : ℕ, 0 ≤ fixSizeMass θ n := fun n ↦ shapeStatMass_nonneg θ _ n
  have hfixsum : Summable (fixSizeMass θ) :=
    summable_shapeStatMass θ hq hq0 h2 fun σ ↦ σ.fix.size
  refine ⟨c / 4, by linarith, 58 + n₀ + ⌈1 / c⌉₊ + ⌈(5 * C₁ / c) ^ 2⌉₊ + D₁,
    fun D hD ↦ ?_⟩
  have hD58 : 58 ≤ D := by omega
  have hDn₀ : n₀ ≤ D := by omega
  have hDc1 : ⌈1 / c⌉₊ ≤ D := by omega
  have hDc2 : ⌈(5 * C₁ / c) ^ 2⌉₊ ≤ D := by omega
  have hDD₁ : D₁ ≤ D := by omega
  have hDsq : D ≤ D ^ 2 := Nat.le_self_pow (by norm_num) D
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  have hsqrtD : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hDpos
  have hsqrtle : Real.sqrt (D : ℝ) ≤ (D : ℝ) := by
    have hle : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (D : ℝ) ≤ Real.sqrt ((D : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = (D : ℝ) := Real.sqrt_sq (by linarith)
  -- the halving condition
  have hcD : 1 ≤ c * (D : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) / c ≤ (D : ℝ) :=
      (Nat.le_ceil (1 / c)).trans (by exact_mod_cast hDc1)
    rw [div_le_iff₀ hc] at h1
    nlinarith
  have hhalf : Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ 1 / 2 := by
    have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hinv : Real.exp (-1) ≤ 1 / 2 := by
      have he : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
      rw [he]
      have hy0 : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr (Real.exp_pos 1)
      have hmul : (Real.exp 1)⁻¹ * Real.exp 1 = 1 := inv_mul_cancel₀ (Real.exp_pos 1).ne'
      nlinarith
    have hmono : Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  -- the small block
  have hsmall : ∀ v : Shape, v.size ≤ D ^ 2 →
      1 - Real.exp (-(c * ((D : ℝ) ^ 2)))
        ≤ gdeg (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) v := by
    intro v hv
    have hcastsq : ∀ w : Shape, w.size ≤ D ^ 2 → (w.size : ℝ) ≤ (D : ℝ) * (D : ℝ) := by
      intro w hw
      have h := (Nat.cast_le (α := ℝ)).mpr hw
      calc (w.size : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := h
        _ = (D : ℝ) * (D : ℝ) := by push_cast; ring
    refine one_sub_le_gdeg_of_small _ _ Shape.size (D ^ 2) v
      (fun y hy ↦ compat_shapeNet_of_small hDR (hcastsq v hv) (hcastsq y hy))
      (Real.exp_pos _).le ?_
    have h := tsum_shapePMF_large_le θ hq hq0 h2 hc htail (N := D ^ 2) (by omega)
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    congr 1
    push_cast
    ring
  -- the mass of the sizes above the block
  set g : ℕ → ℝ := fun n ↦ if n ≤ D ^ 2 then 0 else fixSizeMass θ n with hgdef
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    rw [hgdef]
    by_cases hn : n ≤ D ^ 2 <;> simp [hn, hfix0 n]
  have hgvan : ∀ n ≤ D ^ 2, g n = 0 := by
    intro n hn
    rw [hgdef]
    simp [hn]
  have hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))) := by
    intro n
    by_cases hn : n ≤ D ^ 2
    · rw [hgvan n hn]
      exact (Real.exp_pos _).le
    · have hne : n₀ ≤ n := by omega
      have hshiftsum : Summable fun k : ℕ ↦ fixSizeMass θ (k + n) :=
        (summable_nat_add_iff n).mpr hfixsum
      have hle : fixSizeMass θ n ≤ ∑' k : ℕ, fixSizeMass θ (k + n) := by
        have h := hshiftsum.le_tsum 0 fun j _ ↦ hfix0 _
        simpa using h
      have hbnd := htail n hne
      have hgn : g n = fixSizeMass θ n := by rw [hgdef]; simp [hn]
      rw [hgn, ← neg_mul]
      exact hle.trans hbnd
  have hmass : ∀ n, D ^ 2 < n →
      ∑' v : {v : Shape // v.size = n}, shapePMF θ hq hq0 h2 (v : Shape)
        ≤ ENNReal.ofReal (g n) := by
    intro n hn
    have hne : ¬ (n ≤ D ^ 2) := by omega
    have hgn : g n = fixSizeMass θ n := by rw [hgdef]; simp [hne]
    rw [tsum_fibre_size_shapePMF θ hq hq0 h2 n, hgn]
    exact le_of_eq (ofReal_shapeStatMass θ hq hq0 h2 (fun σ ↦ σ.fix.size) n).symm
  -- the domination
  set s : ℕ := D / 30 with hsdef
  have hs : 1 ≤ s := by omega
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs60 : (D : ℝ) ≤ 60 * (s : ℝ) := by exact_mod_cast (by omega : D ≤ 60 * s)
  have hs30 : 30 * (s : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 30 * s ≤ D)
  have hsD : 2592 * (s : ℝ) ^ 2 ≤ 3 * (D : ℝ) ^ 2 := by nlinarith
  set bb : ℕ → ℝ := fun n ↦ Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt (D : ℝ) + 1))) with hbbdef
  have hbb : ∀ n : ℕ,
      Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt (D : ℝ) + 1))) ≤ bb n := fun n ↦ le_rfl
  have hbb1 : ∀ n, bb n ≤ 1 := by
    intro n
    have hfrac : 0 ≤ (n : ℝ) / Real.sqrt (D : ℝ) := by positivity
    have hx : -(C₁ * ((n : ℝ) / Real.sqrt (D : ℝ) + 1)) ≤ 0 := by nlinarith
    calc bb n ≤ Real.exp 0 := Real.exp_le_exp.mpr hx
      _ = 1 := Real.exp_zero
  have hball : ∀ v : Shape, D ^ 2 < v.size →
      bb v.size ≤ gdeg (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) v := by
    intro v _
    refine le_trans ?_ (pow_le_gdeg_shapeNet θ hq hq0 h2 hDR hs hsD v)
    rw [pow_eq_exp_neg_log_inv hp0, hbbdef]
    refine Real.exp_le_exp.mpr ?_
    have hY : ((v.size / s : ℕ) : ℝ) ≤ 60 * ((v.size : ℝ) / Real.sqrt (D : ℝ)) := by
      have h1 : ((v.size / s : ℕ) : ℝ) ≤ (v.size : ℝ) / (s : ℝ) := Nat.cast_div_le
      have h2 : (v.size : ℝ) / (s : ℝ) ≤ 60 * (v.size : ℝ) / (D : ℝ) := by
        rw [div_le_div_iff₀ hsR hDpos]
        nlinarith [Nat.cast_nonneg (α := ℝ) v.size]
      have h3 : 60 * (v.size : ℝ) / (D : ℝ) ≤ 60 * (v.size : ℝ) / Real.sqrt (D : ℝ) := by
        gcongr
      have h4 : 60 * (v.size : ℝ) / Real.sqrt (D : ℝ)
          = 60 * ((v.size : ℝ) / Real.sqrt (D : ℝ)) := by ring
      linarith [h1, h2, h3, h4.le, h4.ge]
    have hX0 : 0 ≤ (v.size : ℝ) / Real.sqrt (D : ℝ) := by positivity
    have hcast : ((16 * (v.size / s + 1) : ℕ) : ℝ)
        = 16 * (((v.size / s : ℕ) : ℝ) + 1) := by push_cast; ring
    rw [hcast, hC₁def]
    nlinarith
  -- the compatibility of the two rates
  have hcomp : 5 / 2 * C₁ / Real.sqrt (D : ℝ) ≤ c / 2 := by
    have hle : (5 * C₁ / c) ^ 2 ≤ (D : ℝ) := by
      have h1 := Nat.le_ceil ((5 * C₁ / c) ^ 2)
      have h2 : ((⌈(5 * C₁ / c) ^ 2⌉₊ : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDc2
      linarith
    have hsq : 5 * C₁ / c ≤ Real.sqrt (D : ℝ) := by
      calc 5 * C₁ / c = Real.sqrt ((5 * C₁ / c) ^ 2) :=
            (Real.sqrt_sq (div_nonneg (by linarith) hc.le)).symm
        _ ≤ Real.sqrt (D : ℝ) := Real.sqrt_le_sqrt hle
    have hmul : c * (5 * C₁ / c) = 5 * C₁ := by field_simp
    have h5 : 5 * C₁ ≤ c * Real.sqrt (D : ℝ) := by
      have := mul_le_mul_of_nonneg_left hsq hc.le
      linarith [hmul]
    rw [div_le_iff₀ hsqrtD]
    linarith
  -- the assembled bound
  have hmain := etaG_shape_le (c := c) (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ))
    Shape.size (C₁ := C₁) (D := D) (g := g) (bb := bb) hc hC₁0 hhalf hsmall hg0 hgle
    hgvan hmass hbb hbb1 hball hcomp
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hfin := hD₁ D hDD₁
  have hrw : 6 * Real.exp (-(c * ((D : ℝ) ^ 2)))
      + Real.exp (3 * C₁) * ((1 - Real.exp (-(c / 2)))⁻¹
          * Real.exp (-(c / 2) * ((D : ℝ) ^ 2)))
      = 6 * Real.exp (-(c * ((D : ℝ) ^ 2)))
        + C₂ * Real.exp (-(c / 2) * ((D : ℝ) ^ 2)) := by rw [hC₂def]; ring
  rw [hrw]
  refine hfin.trans (le_of_eq ?_)
  congr 1
  ring

/-- **`eq:shape-eta`, at an arbitrary threshold**: the potential of the label law is
eventually below any positive real, the decay `e^{-y}\leq y^{-1}` turning the exponential
bound into the largeness condition. -/
theorem exists_etaG_shapeNet_le_ofReal (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {r : ℝ} (hr : 0 < r) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 1 ≤ (D : ℝ) ∧
      etaG (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) ≤ ENNReal.ofReal r := by
  obtain ⟨c, hc, D₁, hD₁⟩ := exists_etaG_shapeNet_le θ hq hq0 h2
  refine ⟨D₁ + ⌈1 / (r * c)⌉₊ + 1, fun D hD ↦ ?_⟩
  have hDD₁ : D₁ ≤ D := by omega
  have hceil : ⌈1 / (r * c)⌉₊ ≤ D := by omega
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  refine ⟨hDR, (hD₁ D hDD₁).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hy : 0 < c * (D : ℝ) ^ 2 := by positivity
  have hkey := mul_exp_neg_le_one (c * (D : ℝ) ^ 2)
  have hge : 1 / (r * c) ≤ (D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  rw [div_le_iff₀ (by positivity)] at hge
  have hDsq : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have hge' : 1 ≤ r * (c * (D : ℝ) ^ 2) := by nlinarith
  nlinarith [Real.exp_pos (-(c * (D : ℝ) ^ 2))]

/-- **`eq:shape-eta`, the potential condition of `thm:matching`**: past a threshold the
potential of the label law is at most `10⁻⁴`. -/
theorem exists_etaG_shapeNet_small (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      etaG (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) ≤ 1 / 10000 := by
  obtain ⟨D₀, hD₀⟩ :=
    exists_etaG_shapeNet_le_ofReal θ hq hq0 h2 (r := 1 / 10000) (by norm_num)
  refine ⟨D₀, fun D hD ↦ (hD₀ D hD).2.trans (le_of_eq ?_)⟩
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
  norm_num

/-! ### `thm:hairy` for one law -/

/-- **`eq:hairy-rate`, one law**: past a threshold the failure probability of the
quasi-isometry between the two sampled trees at the scale `8·729²D⁸` is bounded by the
potential of the label law, with no hypothesis on the potential. -/
theorem hairy_rate_shape_tree (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      twoHairyMeasure θ θ
          {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
            IsSampleQI (8 * 729 ^ 2 * (D : ℝ) ^ 8) F}
        ≤ 16 * etaG (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) := by
  obtain ⟨D₀, hD₀⟩ := exists_etaG_shapeNet_small θ hq hq0 h2
  refine ⟨D₀ + 1, fun D hD ↦ ?_⟩
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  exact hairy_rate_shape_tree_self θ hq hq0 h2 hDR (hD₀ D (by omega))

/-- **`thm:hairy` for one law**: two independent samples of a supercritical law on
`{0,1,2}` with `θ₀>0` and `θ₂>0` are almost surely quasi-isometric.  The scales of
`def:shape-net` at which the potential is arbitrarily small are supplied by
`exists_etaG_shapeNet_le_ofReal`, so nothing is left to assume. -/
theorem hairy_ae_shape_tree (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) :
    twoHairyMeasure θ θ
      {ω | ¬ ∃ (L : ℝ) (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}),
        IsSampleQI L F} = 0 := by
  refine hairy_ae_shape_tree_self θ hq hq0 h2 fun ε hε ↦ ?_
  obtain ⟨D₀, hD₀⟩ := exists_etaG_shapeNet_small θ hq hq0 h2
  by_cases htop : ε = ⊤
  · refine ⟨((D₀ + 1 : ℕ) : ℝ), by exact_mod_cast (by omega : 1 ≤ D₀ + 1),
      hD₀ (D₀ + 1) (by omega), ?_⟩
    rw [htop]
    exact le_top
  · have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    obtain ⟨D₁, hD₁⟩ :=
      exists_etaG_shapeNet_le_ofReal θ hq hq0 h2 (r := ε.toReal / 16) (by positivity)
    obtain ⟨hDR, hle⟩ := hD₁ (max (D₀ + 1) D₁) (le_max_right _ _)
    refine ⟨((max (D₀ + 1) D₁ : ℕ) : ℝ), hDR,
      hD₀ _ (le_trans (Nat.le_succ D₀) (le_max_left _ _)), ?_⟩
    have h16 : (16 : ℝ≥0∞) * ENNReal.ofReal (ε.toReal / 16) = ε := by
      have hofn : ENNReal.ofReal (16 : ℝ) = (16 : ℝ≥0∞) := by simp
      rw [← hofn, ← ENNReal.ofReal_mul (by norm_num),
        show (16 : ℝ) * (ε.toReal / 16) = ε.toReal by ring]
      exact ENNReal.ofReal_toReal htop
    calc 16 * etaG (shapePMF θ hq hq0 h2) (shapeNet ((max (D₀ + 1) D₁ : ℕ) : ℝ))
        ≤ 16 * ENNReal.ofReal (ε.toReal / 16) := by gcongr
      _ = ε := h16

end ChainClasses

