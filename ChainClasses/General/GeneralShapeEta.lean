import ChainClasses.Bushy.ShapeEtaBlock
import ChainClasses.Bushy.ShapeEtaSelf
import ChainClasses.General.GeneralShapeTail
import ChainClasses.General.GeneralShapeCoupling
import ChainClasses.General.GeneralShrinkScale
import ChainClasses.General.GeneralShapeMetric

/-!
`thm:relabel` (`it:relabel-eta`) and
`thm:cross-relabel` (`it:cross-relabel-eta`) of `matching_classes_general.tex`:
the potential bound `thm:shape-eta` for the mixture `μ` of `thm:conditional-explicit`,
at the class law `μ_D = μ ∘ rep_D⁻¹` on the label graph `G_D` of `def:shape-net` at
general arity.  The two clauses are one statement, the law `μ_D` and the graph `G_D`
depending on the one law `θ` alone.

The vertices of `G_D` are the class indices, and a class carries the mass of its fibre
under the class map.  The summation follows the proof of `thm:shape-eta`: the potential
of a pushforward is a sum over the members, so the tail is grouped by the size of the
member, whose mass the tail clause of `thm:mass-uniform` bounds, and
`eq:shape-domination` bounds the ball mass of the class of a member of positive mass
by the point mass of its shrinking, at the scale `s = ⌊√(D/216J²)⌋` of
`thm:shape-shrink`, which is of order `√D`.  Every member of size at most `D²` collapses
onto the one-vertex shape, which heads the enumeration, so it lies in the class
`v₀ = 0`, whose mass is then the mass of the small shapes.

* `tsum_ite_map`, `gClassPMF`, `gClassPMF_eq_tsum`, `rE_gClassPMF`: **the class law
  `μ_D`**, the mass of a class as the sum of the mixture over its fibre, and the good
  degree of a class read off the shapes.
* `gShapeEnum_zero`, `markedQI_gCollapse_sq`, `gNetLab_eq_zero_of_size_le`: **the
  collapse**, a shape of size at most `D²` being `D`-comparable to the one-vertex shape,
  the first shape of the enumeration, so that `rep_D` sends it to `v₀`.
* `tsum_small_le_gClassPMF_zero`, `ofReal_one_sub_le_gClassPMF_zero`,
  `one_sub_le_gdeg_of_tsum_le`, `one_sub_le_gdeg_gClassPMF_zero`,
  `tsum_gMixPMF_large_le`, `gClassPMF_zero_ge`: **the mass of `v₀`**,
  `μ_D(v₀) ≥ μ(|S| ≤ D²) ≥ 1 - e^{-cD²} ≥ ½`, and the block term it gives.
* `etaG_map_eq_tsum`, `tsum_eq_size`, `tsum_mul_wgt_le_size`, `etaG_map_le_size`,
  `etaG_map_shape_le`: **the summation of `eq:potential` over the members** of a
  pushforward law, the analogue of `etaG_shape_le` in which the block and the
  domination are asked of the members of positive mass only.
* `compat_gNetGraph_of_markedQI`: two `D`-comparable shapes lie in equal or adjacent
  classes, the composition `3·(3·3D²·D)·D = 27D⁴` being the edge scale of
  `def:shape-net`.
* `pow_le_gdeg_gNetGraph`, `exists_gShrinkScale`, `exp_le_gdeg_gNetGraph`:
  **`eq:shape-domination` at general arity**, the ball mass of the class of a member of
  positive mass dominating the point mass `p^{3k(n/s+1)}` of its shrinking, which is
  `e^{-C₁(nD^{-1/2}+1)}` with `C₁ = 90kJ·log p⁻¹` at the scale of `thm:shape-shrink`.
* `rate_compat_of_ceil_le`, `tsum_gMixPMF_size_eq_le`: the compatibility of the two
  rates and the mass of the members of one size, the tail read one step below.
* `exists_etaG_gNetGraph_le`: **`thm:relabel` (`it:relabel-eta`)**, the bound
  `η_{G_D,5/2}(μ_D) ≤ e^{-cD²}` together with `μ_D(v₀) ≥ 1 - e^{-cD²}`, with
  `exists_etaG_gNetGraph_le_ofReal` and `exists_etaG_gNetGraph_small` the potential
  condition `η ≤ 10⁻⁴` of `thm:matching` together with `μ_D(v₀) ≥ ½`.
-/

namespace ChainClasses

open MeasureTheory GraphMatching
open BranchingProcess (Offspring)
open scoped ENNReal Classical

variable {J N : ℕ}

/-! ### The class law -/

/-- A sum over the pushforward of a law, read on the source: the mass the pushforward
gives to a set is the mass of its preimage. -/
lemma tsum_ite_map {W V : Type*} (μ : PMF W) (lab : W → V) (P : V → Prop) :
    (∑' v, if P v then μ.map lab v else 0) = ∑' σ, if P (lab σ) then μ σ else 0 := by
  calc (∑' v, if P v then μ.map lab v else 0)
      = ∑' v, ∑' σ, if P v ∧ v = lab σ then μ σ else 0 := by
        refine tsum_congr fun v ↦ ?_
        by_cases hv : P v
        · rw [ite_eq_left hv, PMF.map_apply]
          refine tsum_congr fun σ ↦ ?_
          by_cases h : v = lab σ
          · subst h
            simp [hv]
          · simp [h]
        · rw [ite_eq_right hv]
          symm
          refine (tsum_congr fun σ ↦ ?_).trans tsum_zero
          simp [hv]
    _ = ∑' σ, ∑' v, if P v ∧ v = lab σ then μ σ else 0 := ENNReal.tsum_comm
    _ = ∑' σ, if P (lab σ) then μ σ else 0 := by
        refine tsum_congr fun σ ↦ ?_
        rw [tsum_eq_single (lab σ) fun v hv ↦ ite_eq_right fun h ↦ hv h.2]
        simp

/-- **The class law `μ_D = μ ∘ rep_D⁻¹` of `thm:relabel`**: the mixture of
`thm:conditional-explicit` pushed forward along the class map of `def:shape-net`. -/
noncomputable def gClassPMF (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) (Dq : ℝ) : PMF ℕ :=
  (gMixPMF θ hJN hq hq0 hs1).map (gNetLab Dq)

/-- The class law evaluated, in the form of the pushforward. -/
lemma gClassPMF_apply (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) (Dq : ℝ) (v : ℕ) :
    gClassPMF θ hJN hq hq0 hs1 Dq v
      = ∑' σ : GShape, if v = gNetLab Dq σ then gMixPMF θ hJN hq hq0 hs1 σ else 0 := by
  rw [gClassPMF, PMF.map_apply]
  exact tsum_congr fun σ ↦ by split_ifs <;> rfl

/-- **The mass of a class** is the sum of the mixture over its fibre. -/
lemma gClassPMF_eq_tsum (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) (Dq : ℝ) (v : ℕ) :
    gClassPMF θ hJN hq hq0 hs1 Dq v
      = ∑' σ : GShape, if gNetLab Dq σ = v then gMixPMF θ hJN hq hq0 hs1 σ else 0 := by
  rw [gClassPMF_apply]
  refine tsum_congr fun σ ↦ ?_
  by_cases h : gNetLab Dq σ = v
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- **The ball mass of a class, on the shapes**: the mixture mass of the shapes whose
class is the given one or adjacent to it. -/
lemma rE_gClassPMF (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) (Dq : ℝ) (v : ℕ) :
    rE (gClassPMF θ hJN hq hq0 hs1 Dq) (compat (gNetGraph Dq)) v
      = ∑' σ : GShape,
          if compat (gNetGraph Dq) v (gNetLab Dq σ) then gMixPMF θ hJN hq hq0 hs1 σ else 0 := by
  rw [rE]
  exact tsum_ite_map _ _ _

/-- A shape in a class compatible with `v` carries its mass into the ball of `v`. -/
lemma gMixPMF_le_rE_gClassPMF (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) (Dq : ℝ) {v : ℕ} {σ : GShape}
    (h : compat (gNetGraph Dq) v (gNetLab Dq σ)) :
    gMixPMF θ hJN hq hq0 hs1 σ
      ≤ rE (gClassPMF θ hJN hq hq0 hs1 Dq) (compat (gNetGraph Dq)) v := by
  rw [rE_gClassPMF]
  calc gMixPMF θ hJN hq hq0 hs1 σ
      = (if compat (gNetGraph Dq) v (gNetLab Dq σ) then gMixPMF θ hJN hq hq0 hs1 σ else 0) :=
        (ite_eq_left h).symm
    _ ≤ ∑' τ : GShape,
          if compat (gNetGraph Dq) v (gNetLab Dq τ) then gMixPMF θ hJN hq hq0 hs1 τ else 0 :=
        ENNReal.le_tsum (f := fun τ : GShape ↦
          if compat (gNetGraph Dq) v (gNetLab Dq τ) then gMixPMF θ hJN hq hq0 hs1 τ else 0) σ

/-! ### The collapse onto the first class -/

/-- The enumeration of `𝒮` by size begins with the one-vertex shape, the only shape of
size one. -/
lemma gShapeEnum_zero : gShapeEnum 0 = gOne := by
  have hone : gOne.size = 1 := size_bareNeck 0
  have hzero : (gShapeEnum 0).size ≤ 1 := by
    have h := size_gShapeEnum_monotone (Nat.zero_le (gShapeIdx gOne))
    simp only [gShapeEnum_gShapeIdx] at h
    exact h.trans hone.le
  exact GShape.eq_of_size_le_one hzero hone.le

/-- The first member of the enumeration, as a marked space. -/
@[simp] lemma gShapeFamily_zero : gShapeFamily 0 = gShapeSpace gOne := by
  rw [gShapeFamily, gShapeEnum_zero]

/-- **The collapse at the square scale**: a shape of size at most `K²` is
`K`-comparable to the one-vertex shape, its diameter lying below `K²`. -/
theorem markedQI_gCollapse_sq {K : ℝ} (hK : 1 ≤ K) (σ : GShape)
    (hσ : (σ.size : ℝ) ≤ K * K) : MarkedQI K (gShapeSpace σ) (gShapeSpace gOne) :=
  markedQI_of_subsingleton hK fun a b ↦ (dist_lt_gSize σ a b).le.trans hσ

/-- **`thm:relabel` (`it:relabel-eta`), the collapse**: a shape of size at most
`D²` is `D`-comparable to the one-vertex shape, the first shape of the enumeration, so
`rep_D` sends it to the class `v₀ = 0`. -/
theorem gNetLab_eq_zero_of_size_le {Dq : ℝ} (hD : 1 ≤ Dq) {σ : GShape}
    (hσ : (σ.size : ℝ) ≤ Dq * Dq) : gNetLab Dq σ = 0 := by
  refine repIdx_eq_zero gShapeFamily Dq ?_
  rw [gShapeFamily_gShapeIdx, gShapeFamily_zero]
  exact markedQI_gCollapse_sq hD σ hσ

/-- The size bound `|σ| ≤ D²`, read over the reals. -/
lemma gSize_cast_le_of_le_sq {D : ℕ} {σ : GShape} (hσ : σ.size ≤ D ^ 2) :
    (σ.size : ℝ) ≤ (D : ℝ) * (D : ℝ) := by
  have h := (Nat.cast_le (α := ℝ)).mpr hσ
  calc (σ.size : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := h
    _ = (D : ℝ) * (D : ℝ) := by push_cast; ring

/-- **The mass of `v₀`**: the shapes of size at most `D²` carry their mass into the
class `v₀`. -/
lemma tsum_small_le_gClassPMF_zero (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {D : ℕ} (hD : 1 ≤ D) :
    (∑' σ : GShape, if σ.size ≤ D ^ 2 then gMixPMF θ hJN hq hq0 hs1 σ else 0)
      ≤ gClassPMF θ hJN hq hq0 hs1 D 0 := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  rw [gClassPMF_eq_tsum]
  refine ENNReal.tsum_le_tsum fun σ ↦ ?_
  by_cases hσ : σ.size ≤ D ^ 2
  · rw [ite_eq_left hσ, ite_eq_left (gNetLab_eq_zero_of_size_le hDR (gSize_cast_le_of_le_sq hσ))]
  · rw [ite_eq_right hσ]
    exact zero_le

/-- **`thm:relabel` (`it:relabel-eta`), the mass of `v₀`**: once the mass above
the size `D²` is at most `E`, the class `v₀` carries mass at least `1 - E`. -/
theorem ofReal_one_sub_le_gClassPMF_zero (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    {D : ℕ} (hD : 1 ≤ D) {E : ℝ} (hE0 : 0 ≤ E)
    (hlarge : (∑' σ : GShape, if σ.size ≤ D ^ 2 then 0 else gMixPMF θ hJN hq hq0 hs1 σ)
      ≤ ENNReal.ofReal E) :
    ENNReal.ofReal (1 - E) ≤ gClassPMF θ hJN hq hq0 hs1 D 0 := by
  have hsplit := tsum_small_add_tsum_large (gMixPMF θ hJN hq hq0 hs1) GShape.size (D ^ 2)
  have hB : (∑' σ : GShape, if σ.size ≤ D ^ 2 then 0 else gMixPMF θ hJN hq hq0 hs1 σ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlarge
  refine le_trans ?_ (tsum_small_le_gClassPMF_zero θ hJN hq hq0 hs1 hD)
  calc ENNReal.ofReal (1 - E) = 1 - ENNReal.ofReal E := by
        rw [ENNReal.ofReal_sub 1 hE0, ENNReal.ofReal_one]
    _ ≤ 1 - ∑' σ : GShape, if σ.size ≤ D ^ 2 then 0 else gMixPMF θ hJN hq hq0 hs1 σ :=
        tsub_le_tsub_left hlarge 1
    _ = ∑' σ : GShape, if σ.size ≤ D ^ 2 then gMixPMF θ hJN hq hq0 hs1 σ else 0 :=
        ENNReal.sub_eq_of_eq_add hB hsplit.symm

/-- **The block of `thm:shape-eta`**: a vertex whose ball carries the mass of the shapes
of size at most `N` has ball mass at least `1 - E` once the mass above `N` is at most
`E`. -/
lemma one_sub_le_gdeg_of_tsum_le {V W : Type*} (ν : PMF W) (sz : W → ℕ) (N : ℕ)
    (μ : PMF V) (G : SimpleGraph V) (v : V)
    (hsmall : (∑' y, if sz y ≤ N then ν y else 0) ≤ rE μ (compat G) v) {E : ℝ} (hE0 : 0 ≤ E)
    (hlarge : (∑' y, if sz y ≤ N then 0 else ν y) ≤ ENNReal.ofReal E) :
    1 - E ≤ gdeg μ G v := by
  have hsplit := tsum_small_add_tsum_large ν sz N
  have hA : (∑' y, if sz y ≤ N then ν y else 0) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit ▸ le_self_add)
  have hB : (∑' y, if sz y ≤ N then 0 else ν y) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit ▸ le_add_self)
  have hreal : (∑' y, if sz y ≤ N then ν y else 0).toReal
      + (∑' y, if sz y ≤ N then 0 else ν y).toReal = 1 := by
    rw [← ENNReal.toReal_add hA hB, hsplit, ENNReal.toReal_one]
  have hBle : (∑' y, if sz y ≤ N then 0 else ν y).toReal ≤ E := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlarge
    rwa [ENNReal.toReal_ofReal hE0] at h
  have hAle : (∑' y, if sz y ≤ N then ν y else 0).toReal ≤ (rE μ (compat G) v).toReal :=
    ENNReal.toReal_mono (rE_ne_top (μ := μ) (R := compat G) (x := v)) hsmall
  show 1 - E ≤ (rE μ (compat G) v).toReal
  linarith

/-- **The block of `thm:shape-eta` at the class `v₀`**: its ball mass is at least
`1 - E` once the mass above the size `D²` is at most `E`. -/
theorem one_sub_le_gdeg_gClassPMF_zero (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    {D : ℕ} (hD : 1 ≤ D) {E : ℝ} (hE0 : 0 ≤ E)
    (hlarge : (∑' σ : GShape, if σ.size ≤ D ^ 2 then 0 else gMixPMF θ hJN hq hq0 hs1 σ)
      ≤ ENNReal.ofReal E) :
    1 - E ≤ gdeg (gClassPMF θ hJN hq hq0 hs1 D) (gNetGraph D) 0 :=
  one_sub_le_gdeg_of_tsum_le (gMixPMF θ hJN hq hq0 hs1) GShape.size (D ^ 2) _ _ 0
    ((tsum_small_le_gClassPMF_zero θ hJN hq hq0 hs1 hD).trans
      (le_rE_of_refl (compat_refl _ _)))
    hE0 hlarge

/-- `e^{-y} ≤ ½` for `y ≥ 1`. -/
lemma exp_neg_le_half {y : ℝ} (hy : 1 ≤ y) : Real.exp (-y) ≤ 1 / 2 := by
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hinv : Real.exp (-1) ≤ 1 / 2 := by
    have he : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
    rw [he]
    have hy0 : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr (Real.exp_pos 1)
    have hmul : (Real.exp 1)⁻¹ * Real.exp 1 = 1 := inv_mul_cancel₀ (Real.exp_pos 1).ne'
    nlinarith
  exact (Real.exp_le_exp.mpr (by linarith)).trans hinv

/-- The threshold `½` of the mass of `v₀`, as an extended real. -/
lemma ofReal_half : ENNReal.ofReal (1 / 2) = 1 / 2 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
  norm_num

/-- `1 ≤ cD²` past the threshold `⌈1/c⌉₊`. -/
lemma one_le_mul_sq_of_ceil_le {c : ℝ} (hc : 0 < c) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : ⌈1 / c⌉₊ ≤ D) : 1 ≤ c * (D : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) / c ≤ (D : ℝ) := (Nat.le_ceil (1 / c)).trans (by exact_mod_cast hD)
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  rw [div_le_iff₀ hc] at h1
  nlinarith

/-- **`thm:mass-uniform`, the tail clause at the threshold `D²`**, in the form the
summation reads. -/
lemma tsum_gMixPMF_large_le (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {c : ℝ} {n₀ : ℕ}
    (htail : ∀ m : ℕ, n₀ ≤ m →
      (∑' y : GShape, if y.size ≤ m then 0 else gMixPMF θ hJN hq hq0 hs1 y)
        ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))))
    {D : ℕ} (hD : n₀ ≤ D ^ 2) :
    (∑' σ : GShape, if σ.size ≤ D ^ 2 then 0 else gMixPMF θ hJN hq hq0 hs1 σ)
      ≤ ENNReal.ofReal (Real.exp (-(c * (D : ℝ) ^ 2))) := by
  have h := htail (D ^ 2) hD
  have e : -c * ((D ^ 2 : ℕ) : ℝ) = -(c * (D : ℝ) ^ 2) := by push_cast; ring
  rwa [e] at h

/-- **`thm:relabel` (`it:relabel-eta`), the mass of `v₀`**: past a threshold the
class of the one-vertex shape carries mass at least `½`. -/
theorem gClassPMF_zero_ge (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 1 / 2 ≤ gClassPMF θ hJN hq hq0 hs1 D 0 := by
  obtain ⟨c, hc, n₀, htail⟩ := exists_gMix_size_tail θ hJN hq hq0 hs1
  refine ⟨n₀ + ⌈1 / c⌉₊ + 1, fun D hD ↦ ?_⟩
  have hD1 : 1 ≤ D := by omega
  have hDsq : D ≤ D ^ 2 := Nat.le_self_pow (by norm_num) D
  have hlarge := (tsum_gMixPMF_large_le θ hJN hq hq0 hs1 htail (D := D) (by omega)).trans
    (ENNReal.ofReal_le_ofReal (exp_neg_le_half (one_le_mul_sq_of_ceil_le hc hD1 (by omega))))
  have h := ofReal_one_sub_le_gClassPMF_zero θ hJN hq hq0 hs1 hD1 (by norm_num) hlarge
  rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ofReal_half] at h

/-! ### The summation over the members -/

/-- **`eq:etaG` for a pushforward law**, summed over the members: each member
contributes its mass at the ball mass of its class. -/
lemma etaG_map_eq_tsum {W V : Type*} (μ : PMF W) (lab : W → V) (G : SimpleGraph V) :
    etaG (μ.map lab) G
      = ∑' σ, μ σ * ENNReal.ofReal (wgt (gdeg (μ.map lab) G (lab σ))) := by
  rw [etaG_eq_tsum_wgt]
  calc ∑' v, (μ.map lab) v * ENNReal.ofReal (wgt (gdeg (μ.map lab) G v))
      = ∑' v, ∑' σ,
          (if v = lab σ then μ σ * ENNReal.ofReal (wgt (gdeg (μ.map lab) G v)) else 0) := by
        refine tsum_congr fun v ↦ ?_
        rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun σ ↦ ?_
        split_ifs <;> simp
    _ = ∑' σ, ∑' v,
          (if v = lab σ then μ σ * ENNReal.ofReal (wgt (gdeg (μ.map lab) G v)) else 0) :=
        ENNReal.tsum_comm
    _ = ∑' σ, μ σ * ENNReal.ofReal (wgt (gdeg (μ.map lab) G (lab σ))) := by
        refine tsum_congr fun σ ↦ ?_
        rw [tsum_eq_single (lab σ) fun v hv ↦ ite_eq_right hv]
        exact ite_eq_left rfl

/-- A sum over a size fibre, on the whole type. -/
lemma tsum_eq_size {W : Type*} (f : W → ℝ≥0∞) (sz : W → ℕ) (n : ℕ) :
    ∑' σ : {σ : W // sz σ = n}, f σ = ∑' σ, (if sz σ = n then f σ else 0) := by
  refine (tsum_subtype {σ : W | sz σ = n} f).trans (tsum_congr fun σ ↦ ?_)
  by_cases h : sz σ = n <;> simp [h]

/-- **`eq:etaG` over the size data, summed over the members.** The analogue of
`etaG_le_size` for a sum of one-site weights indexed by the members of a law: the
members of size at most `N` and positive mass see a ball mass of at least `1 - E`, and
a member of size `n > N` and positive mass a ball mass of at least `bb n`, the mass of
the members of size `n` being at most `g n`. -/
theorem tsum_mul_wgt_le_size {W : Type*} (μ : PMF W) (b : W → ℝ) (sz : W → ℕ) (N : ℕ)
    {E : ℝ} {g bb : ℕ → ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 1 / 2) (hb1 : ∀ σ, b σ ≤ 1)
    (hsmall : ∀ σ, μ σ ≠ 0 → sz σ ≤ N → 1 - E ≤ b σ)
    (hbb0 : ∀ n, 0 < bb n) (hbb1 : ∀ n, bb n ≤ 1) (hg0 : ∀ n, 0 ≤ g n)
    (hmass : ∀ n, N < n → ∑' σ : {σ : W // sz σ = n}, μ σ ≤ ENNReal.ofReal (g n))
    (hball : ∀ σ, μ σ ≠ 0 → N < sz σ → bb (sz σ) ≤ b σ)
    (hsum : Summable fun n ↦ g n * wgt (bb n)) :
    ∑' σ, μ σ * ENNReal.ofReal (wgt (b σ))
      ≤ ENNReal.ofReal (6 * E + ∑' n : ℕ, g n * wgt (bb n)) := by
  have hwgt0 : ∀ n, 0 ≤ g n * wgt (bb n) := fun n ↦
    mul_nonneg (hg0 n) (wgt_nonneg (hbb0 n) (hbb1 n))
  -- the block of small members
  have hblock :
      (∑' σ : {σ : W // sz σ ≤ N}, μ (σ : W) * ENNReal.ofReal (wgt (b (σ : W))))
        ≤ ENNReal.ofReal (6 * E) := by
    have hterm : ∀ σ : {σ : W // sz σ ≤ N},
        μ (σ : W) * ENNReal.ofReal (wgt (b (σ : W)))
          ≤ μ (σ : W) * ENNReal.ofReal (6 * E) := by
      intro w
      by_cases hμ : μ (w : W) = 0
      · rw [hμ, zero_mul]
        exact zero_le
      · have hb := hsmall (w : W) hμ w.2
        have hhalf : (1 : ℝ) / 2 ≤ b (w : W) := by linarith
        have hw : wgt (b (w : W)) ≤ 6 * E := by
          have := wgt_le_of_half hhalf (hb1 (w : W))
          linarith
        gcongr
    calc (∑' σ : {σ : W // sz σ ≤ N}, μ (σ : W) * ENNReal.ofReal (wgt (b (σ : W))))
        ≤ ∑' σ : {σ : W // sz σ ≤ N}, μ (σ : W) * ENNReal.ofReal (6 * E) :=
          ENNReal.tsum_le_tsum hterm
      _ = (∑' σ : {σ : W // sz σ ≤ N}, μ (σ : W)) * ENNReal.ofReal (6 * E) :=
          ENNReal.tsum_mul_right
      _ ≤ 1 * ENNReal.ofReal (6 * E) := by
          gcongr
          exact (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans_eq
            μ.tsum_coe
      _ = ENNReal.ofReal (6 * E) := one_mul _
  -- the fibres above the block
  have hfib : ∀ n : ℕ,
      (∑' σ : {σ : W // sz σ = n}, (if sz (σ : W) ≤ N then 0
        else μ (σ : W) * ENNReal.ofReal (wgt (b (σ : W)))))
        ≤ ENNReal.ofReal (g n * wgt (bb n)) := by
    intro n
    by_cases hn : N < n
    · have hterm : ∀ σ : {σ : W // sz σ = n},
          (if sz (σ : W) ≤ N then 0 else μ (σ : W) * ENNReal.ofReal (wgt (b (σ : W))))
            ≤ μ (σ : W) * ENNReal.ofReal (wgt (bb n)) := by
        intro w
        have hw : sz (w : W) = n := w.2
        rw [ite_eq_right (by omega)]
        by_cases hμ : μ (w : W) = 0
        · rw [hμ, zero_mul]
          exact zero_le
        · gcongr
          refine wgt_le_wgt_of_le (hbb0 n) ?_ (hb1 (w : W))
          have hb := hball (w : W) hμ (by omega)
          rwa [hw] at hb
      calc (∑' σ : {σ : W // sz σ = n}, (if sz (σ : W) ≤ N then 0
              else μ (σ : W) * ENNReal.ofReal (wgt (b (σ : W)))))
          ≤ ∑' σ : {σ : W // sz σ = n}, μ (σ : W) * ENNReal.ofReal (wgt (bb n)) :=
            ENNReal.tsum_le_tsum hterm
        _ = (∑' σ : {σ : W // sz σ = n}, μ (σ : W)) * ENNReal.ofReal (wgt (bb n)) :=
            ENNReal.tsum_mul_right
        _ ≤ ENNReal.ofReal (g n) * ENNReal.ofReal (wgt (bb n)) := by
            gcongr
            exact hmass n hn
        _ = ENNReal.ofReal (g n * wgt (bb n)) := (ENNReal.ofReal_mul (hg0 n)).symm
    · have hzero : ∀ σ : {σ : W // sz σ = n},
          (if sz (σ : W) ≤ N then 0
            else μ (σ : W) * ENNReal.ofReal (wgt (b (σ : W)))) = 0 := by
        intro w
        have hw : sz (w : W) = n := w.2
        rw [ite_eq_left (by omega)]
      rw [tsum_congr hzero, tsum_zero]
      exact zero_le
  have htail :
      (∑' n : ℕ, ∑' σ : {σ : W // sz σ = n}, (if sz (σ : W) ≤ N then 0
        else μ (σ : W) * ENNReal.ofReal (wgt (b (σ : W)))))
        ≤ ENNReal.ofReal (∑' n : ℕ, g n * wgt (bb n)) :=
    (ENNReal.tsum_le_tsum hfib).trans_eq
      (ENNReal.ofReal_tsum_of_nonneg hwgt0 hsum).symm
  rw [tsum_split_size (fun σ ↦ μ σ * ENNReal.ofReal (wgt (b σ))) sz N,
    ENNReal.ofReal_add (by linarith) (tsum_nonneg hwgt0)]
  exact add_le_add hblock htail

/-- **`eq:etaG` for a pushforward law over the size data of the members.**  The
pushforward is carried as an equation, so that the class law of `thm:relabel` is read
in without unfolding. -/
theorem etaG_map_le_size {W V : Type*} (μ : PMF W) (lab : W → V) (ν : PMF V)
    (hν : ν = μ.map lab) (G : SimpleGraph V) (sz : W → ℕ) (N : ℕ) {E : ℝ} {g bb : ℕ → ℝ}
    (hE0 : 0 ≤ E) (hE : E ≤ 1 / 2)
    (hsmall : ∀ σ, μ σ ≠ 0 → sz σ ≤ N → 1 - E ≤ gdeg ν G (lab σ))
    (hbb0 : ∀ n, 0 < bb n) (hbb1 : ∀ n, bb n ≤ 1) (hg0 : ∀ n, 0 ≤ g n)
    (hmass : ∀ n, N < n → ∑' σ : {σ : W // sz σ = n}, μ σ ≤ ENNReal.ofReal (g n))
    (hball : ∀ σ, μ σ ≠ 0 → N < sz σ → bb (sz σ) ≤ gdeg ν G (lab σ))
    (hsum : Summable fun n ↦ g n * wgt (bb n)) :
    etaG ν G ≤ ENNReal.ofReal (6 * E + ∑' n : ℕ, g n * wgt (bb n)) := by
  subst hν
  rw [etaG_map_eq_tsum]
  exact tsum_mul_wgt_le_size μ (fun σ ↦ gdeg (μ.map lab) G (lab σ)) sz N hE0 hE
    (fun σ ↦ gdeg_le_one _ _ _) hsmall hbb0 hbb1 hg0 hmass hball hsum

/-- **`thm:shape-eta`, the summation for a pushforward law**: the combination of
`etaG_map_le_size` with the tail estimate `eta_tail_le` at the block threshold `D²`,
the conclusion being that of `etaG_shape_le`. -/
theorem etaG_map_shape_le {W V : Type*} (μ : PMF W) (lab : W → V) (ν : PMF V)
    (hν : ν = μ.map lab) (G : SimpleGraph V) (sz : W → ℕ) {c C₁ : ℝ} {D : ℕ}
    {g bb : ℕ → ℝ} (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    (hhalf : Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ 1 / 2)
    (hsmall : ∀ σ, μ σ ≠ 0 → sz σ ≤ D ^ 2 →
      1 - Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ gdeg ν G (lab σ))
    (hg0 : ∀ n, 0 ≤ g n) (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))))
    (hgvan : ∀ n ≤ D ^ 2, g n = 0)
    (hmass : ∀ n, D ^ 2 < n → ∑' σ : {σ : W // sz σ = n}, μ σ ≤ ENNReal.ofReal (g n))
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n)
    (hbb1 : ∀ n, bb n ≤ 1)
    (hball : ∀ σ, μ σ ≠ 0 → D ^ 2 < sz σ → bb (sz σ) ≤ gdeg ν G (lab σ))
    (hcomp : 5 / 2 * C₁ / Real.sqrt D ≤ c / 2) :
    etaG ν G ≤ ENNReal.ofReal (6 * Real.exp (-(c * ((D : ℝ) ^ 2)))
      + Real.exp (3 * C₁) * ((1 - Real.exp (-(c / 2)))⁻¹
          * Real.exp (-(c / 2) * ((D : ℝ) ^ 2)))) := by
  have hbb0 : ∀ n, 0 < bb n := fun n ↦ lt_of_lt_of_le (Real.exp_pos _) (hbb n)
  refine (etaG_map_le_size μ lab ν hν G sz (D ^ 2) (Real.exp_pos _).le hhalf hsmall hbb0 hbb1
    hg0 hmass hball (summable_g_wgt hc hC₁ hg0 hgle hbb hbb1 hcomp)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have := eta_tail_le hc hC₁ hg0 hgle hgvan hbb hbb1 hcomp
  linarith

/-! ### `eq:shape-domination` at general arity -/

/-- **Comparable shapes lie in equal or adjacent classes**: a `D`-marked quasi-isometry
between two shapes, composed with the `3D²`-marked quasi-inverse of the first's map to
its representative and the `D`-marked map of the second to its representative, is
`3·(3·3D²·D)·D = 27D⁴`-marked, which is the edge scale of `def:shape-net`. -/
theorem compat_gNetGraph_of_markedQI {Dq : ℝ} (hD : 1 ≤ Dq) {σ τ : GShape}
    (h : MarkedQI Dq (gShapeSpace σ) (gShapeSpace τ)) :
    compat (gNetGraph Dq) (gNetLab Dq σ) (gNetLab Dq τ) := by
  by_cases heq : gNetLab Dq σ = gNetLab Dq τ
  · exact Or.inl heq
  · have hD2 : (1 : ℝ) ≤ 3 * Dq ^ 2 := by nlinarith
    have h1 : MarkedQI (3 * Dq ^ 2) (gShapeFamily (gNetLab Dq σ)) (gShapeSpace σ) :=
      markedQI_symm hD (markedQI_gNetLab hD σ)
    have h2 := markedQI_comp hD2 hD h1 h
    have h3 : (1 : ℝ) ≤ 3 * (3 * Dq ^ 2) * Dq := by nlinarith
    have h4 := markedQI_comp h3 hD h2 (markedQI_gNetLab hD τ)
    have e : 3 * (3 * (3 * Dq ^ 2) * Dq) * Dq = 27 * Dq ^ 4 := by ring
    rw [e] at h4
    refine Or.inr ?_
    rw [gNetGraph, SimpleGraph.fromRel_adj]
    exact ⟨heq, Or.inl ⟨heq, netMem_repIdx gShapeFamily Dq hD _,
      netMem_repIdx gShapeFamily Dq hD _, h4⟩⟩

/-- **`eq:shape-domination` at general arity**: the ball mass of the class of a shape of
positive mass dominates the point mass `p^{3k(n/s+1)}` of its shrinking, a charged shape
of size at most `3k(n/s+1)` whose class is equal or adjacent, the shrinking being
`D`-marked at a scale `s` with `216 J² s² ≤ D`. -/
theorem pow_le_gdeg_gNetGraph (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {k : ℕ} (h0 : 0 < θ 0)
    (hk : 0 < θ k) (hk2 : 2 ≤ k) {D s : ℕ} (hD : 1 ≤ D) (hs : 1 ≤ s)
    (hsD : 216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D : ℝ)) {σ : GShape}
    (hσ : gMixPMF θ hJN hq hq0 hs1 σ ≠ 0) :
    gPointBase θ ^ (3 * k * (σ.size / s + 1))
      ≤ gdeg (gClassPMF θ hJN hq hq0 hs1 D) (gNetGraph D) (gNetLab D σ) := by
  have hJ : 1 ≤ J := le_trans (by omega) (offspring_le_of_pos θ hk)
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  obtain ⟨hch, hsize, hqi⟩ := markedQI_gShrink_of_le hJ hs hsD h0 hk hk2
    (degLe_of_gMixPMF_ne_zero θ hJN hq hq0 hs1 hσ)
  have hcompat := compat_gNetGraph_of_markedQI hDR hqi
  have hp0 : 0 < gPointBase θ := gPointBase_pos θ hq hq0
  have hp1 : gPointBase θ ≤ 1 := gPointBase_le_one θ hq hq0
  have hpt := ofReal_pow_le_gMixMass θ hJN hq hq0 hk2 hch
  rw [← gMixPMF_apply θ hJN hq hq0 hs1] at hpt
  have hmass : ENNReal.ofReal (gPointBase θ ^ (gShrink k s σ).size)
      ≤ rE (gClassPMF θ hJN hq hq0 hs1 D) (compat (gNetGraph D)) (gNetLab D σ) :=
    hpt.trans (gMixPMF_le_rE_gClassPMF θ hJN hq hq0 hs1 D hcompat)
  have htoReal := ENNReal.toReal_mono
    (rE_ne_top (μ := gClassPMF θ hJN hq hq0 hs1 D) (R := compat (gNetGraph D))
      (x := gNetLab D σ)) hmass
  rw [ENNReal.toReal_ofReal (pow_nonneg hp0.le _)] at htoReal
  show gPointBase θ ^ (3 * k * (σ.size / s + 1))
    ≤ (rE (gClassPMF θ hJN hq hq0 hs1 D) (compat (gNetGraph D)) (gNetLab D σ)).toReal
  exact le_trans (pow_le_pow_of_le_one hp0.le hp1 hsize) htoReal

/-- **The scale of the shrinking is of order `√D`**: the scale `s = ⌊√(D/216J²)⌋` of
`thm:shape-shrink` is at least `1` once `D ≥ 216J²`, its constant `216J²s²` is at most
`D`, and `√D ≤ 30 J s`. -/
lemma exists_gShrinkScale {D : ℕ} (hJ : 1 ≤ J) (hD : 216 * J ^ 2 ≤ D) :
    ∃ s : ℕ, 1 ≤ s ∧ 216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D : ℝ)
      ∧ Real.sqrt D ≤ 30 * (J : ℝ) * (s : ℝ) := by
  have hJ2pos : 0 < 216 * J ^ 2 := by positivity
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = D / (216 * J ^ 2) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = Nat.sqrt m := ⟨_, rfl⟩
  have hsm : gShrinkScale J D = s := by rw [hsdef, hmdef, gShrinkScale]
  have hm1 : 1 ≤ m := by
    rw [hmdef]
    exact (Nat.le_div_iff_mul_le hJ2pos).mpr (by omega)
  have hs : 1 ≤ s := by
    rw [hsdef]
    exact Nat.sqrt_pos.mpr hm1
  have hsD := gShrinkScale_le J D
  rw [hsm] at hsD
  refine ⟨s, hs, hsD, ?_⟩
  have hDlt : D < m * (216 * J ^ 2) + 216 * J ^ 2 := by
    rw [hmdef]
    exact Nat.lt_div_mul_add hJ2pos
  have hm : m + 1 ≤ (s + 1) ^ 2 := by
    rw [hsdef]
    exact Nat.lt_succ_sqrt' m
  have hDlt' : (D : ℝ) < (m : ℝ) * (216 * (J : ℝ) ^ 2) + 216 * (J : ℝ) ^ 2 := by
    exact_mod_cast hDlt
  have hm' : (m : ℝ) + 1 ≤ ((s : ℝ) + 1) ^ 2 := by exact_mod_cast hm
  have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hJ' : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hsq : ((s : ℝ) + 1) ^ 2 ≤ 4 * (s : ℝ) ^ 2 := by nlinarith
  have hJ2 : (0 : ℝ) ≤ 216 * (J : ℝ) ^ 2 := by positivity
  have hD' : (D : ℝ) ≤ (30 * (J : ℝ) * (s : ℝ)) ^ 2 := by
    have h1 : (D : ℝ) < 216 * (J : ℝ) ^ 2 * ((m : ℝ) + 1) := by linarith
    have h2 : 216 * (J : ℝ) ^ 2 * ((m : ℝ) + 1) ≤ 216 * (J : ℝ) ^ 2 * (4 * (s : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (hm'.trans hsq) hJ2
    nlinarith [sq_nonneg ((J : ℝ) * (s : ℝ))]
  calc Real.sqrt D ≤ Real.sqrt ((30 * (J : ℝ) * (s : ℝ)) ^ 2) := Real.sqrt_le_sqrt hD'
    _ = 30 * (J : ℝ) * (s : ℝ) := Real.sqrt_sq (by positivity)

/-- **`eq:shape-domination` at general arity, in exponential form**: at a scale `s`
with `216J²s² ≤ D` and `√D ≤ 30Js`, the ball mass of the class of a member of size
`n` and positive mass is at least `e^{-C₁(nD^{-1/2}+1)}` with `C₁ = 90kJ·log p⁻¹`,
`p` the base `gPointBase` of the point clause of `thm:mass-uniform`. -/
theorem exp_le_gdeg_gNetGraph (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {k : ℕ} (h0 : 0 < θ 0)
    (hk : 0 < θ k) (hk2 : 2 ≤ k) {D s : ℕ} (hD : 1 ≤ D) (hs : 1 ≤ s)
    (hsD : 216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D : ℝ))
    (hsqrt : Real.sqrt D ≤ 30 * (J : ℝ) * (s : ℝ)) {σ : GShape}
    (hσ : gMixPMF θ hJN hq hq0 hs1 σ ≠ 0) :
    Real.exp (-(90 * k * J * Real.log (gPointBase θ)⁻¹
        * ((σ.size : ℝ) / Real.sqrt (D : ℝ) + 1)))
      ≤ gdeg (gClassPMF θ hJN hq hq0 hs1 D) (gNetGraph D) (gNetLab D σ) := by
  have hJ : 1 ≤ J := le_trans (by omega) (offspring_le_of_pos θ hk)
  have hp0 : 0 < gPointBase θ := gPointBase_pos θ hq hq0
  have hp1 : gPointBase θ ≤ 1 := gPointBase_le_one θ hq hq0
  have hL0 : 0 ≤ Real.log (gPointBase θ)⁻¹ := by
    rw [Real.log_inv]
    linarith [Real.log_nonpos hp0.le hp1]
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hsqrtD : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hJR : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  refine le_trans ?_ (pow_le_gdeg_gNetGraph θ hJN hq hq0 hs1 h0 hk hk2 hD hs hsD hσ)
  rw [pow_eq_exp_neg_log_inv hp0]
  refine Real.exp_le_exp.mpr ?_
  have hX0 : 0 ≤ (σ.size : ℝ) / Real.sqrt (D : ℝ) := by positivity
  have hY : ((σ.size / s : ℕ) : ℝ) ≤ 30 * (J : ℝ) * ((σ.size : ℝ) / Real.sqrt (D : ℝ)) := by
    have h1 : ((σ.size / s : ℕ) : ℝ) ≤ (σ.size : ℝ) / (s : ℝ) := Nat.cast_div_le
    have h2 : (σ.size : ℝ) / (s : ℝ) ≤ 30 * (J : ℝ) * (σ.size : ℝ) / Real.sqrt (D : ℝ) := by
      rw [div_le_div_iff₀ hsR hsqrtD]
      nlinarith [Nat.cast_nonneg (α := ℝ) σ.size]
    have h3 : 30 * (J : ℝ) * (σ.size : ℝ) / Real.sqrt (D : ℝ)
        = 30 * (J : ℝ) * ((σ.size : ℝ) / Real.sqrt (D : ℝ)) := by ring
    linarith
  have hY1 : ((σ.size / s : ℕ) : ℝ) + 1
      ≤ 30 * (J : ℝ) * ((σ.size : ℝ) / Real.sqrt (D : ℝ) + 1) := by linarith
  have hcast : ((3 * k * (σ.size / s + 1) : ℕ) : ℝ)
      = 3 * (k : ℝ) * (((σ.size / s : ℕ) : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  have hkL : (0 : ℝ) ≤ 3 * (k : ℝ) * Real.log (gPointBase θ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hY1 hkL
  nlinarith

/-! ### The constants of the assembly -/

/-- **The compatibility of the two rates**: `(5/2)C₁D^{-1/2} ≤ c/2` past the threshold
`⌈(5C₁/c)²⌉₊`. -/
lemma rate_compat_of_ceil_le {c C₁ : ℝ} (hc : 0 < c) (hC₁ : 0 ≤ C₁) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : ⌈(5 * C₁ / c) ^ 2⌉₊ ≤ D) : 5 / 2 * C₁ / Real.sqrt D ≤ c / 2 := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hsqrtD : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hle : (5 * C₁ / c) ^ 2 ≤ (D : ℝ) := by
    have h1 := Nat.le_ceil ((5 * C₁ / c) ^ 2)
    have h2 : ((⌈(5 * C₁ / c) ^ 2⌉₊ : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
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

/-- **The mass of the members of one size**: the members of size `n` carry at most the
mass above `n - 1`, which the tail clause of `thm:mass-uniform` bounds by `e^{-c(n-1)}`,
at most `e^{-cn/2}` for `n ≥ 2`. -/
lemma tsum_gMixPMF_size_eq_le (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {c : ℝ} {n₀ : ℕ} (hc : 0 < c)
    (htail : ∀ m : ℕ, n₀ ≤ m →
      (∑' y : GShape, if y.size ≤ m then 0 else gMixPMF θ hJN hq hq0 hs1 y)
        ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))))
    {n : ℕ} (hn : n₀ + 2 ≤ n) :
    ∑' σ : {σ : GShape // σ.size = n}, gMixPMF θ hJN hq hq0 hs1 (σ : GShape)
      ≤ ENNReal.ofReal (Real.exp (-(c / 2 * (n : ℝ)))) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  calc ∑' σ : {σ : GShape // σ.size = n}, gMixPMF θ hJN hq hq0 hs1 (σ : GShape)
      = ∑' σ : GShape, (if σ.size = n then gMixPMF θ hJN hq hq0 hs1 σ else 0) :=
        tsum_eq_size _ _ n
    _ ≤ ∑' σ : GShape, (if σ.size ≤ n - 1 then 0 else gMixPMF θ hJN hq hq0 hs1 σ) := by
        refine ENNReal.tsum_le_tsum fun σ ↦ ?_
        by_cases hσ : σ.size = n
        · rw [ite_eq_left hσ, ite_eq_right (by omega)]
        · rw [ite_eq_right hσ]
          exact zero_le
    _ ≤ ENNReal.ofReal (Real.exp (-c * ((n - 1 : ℕ) : ℝ))) := htail (n - 1) (by omega)
    _ ≤ ENNReal.ofReal (Real.exp (-(c / 2 * (n : ℝ)))) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        rw [hcast]
        nlinarith

/-! ### `thm:relabel` (`it:relabel-eta`) -/

/-- **`thm:relabel` (`it:relabel-eta`)**, in the exponential form: the potential
of the class law `μ_D` over the label graph `G_D` at scale `D` is at most `e^{-cD²}`, and
the class `v₀` of the one-vertex shape carries mass at least `1 - e^{-cD²}`.  The same
statement is `thm:cross-relabel` (`it:cross-relabel-eta`), the law `μ_D` and the
graph `G_D` being those of the one law `θ`. -/
theorem exists_etaG_gNetGraph_le (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {k : ℕ} (h0 : 0 < θ 0)
    (hk : 0 < θ k) (hk2 : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      etaG (gClassPMF θ hJN hq hq0 hs1 D) (gNetGraph D)
          ≤ ENNReal.ofReal (Real.exp (-(c * (D : ℝ) ^ 2)))
        ∧ ENNReal.ofReal (1 - Real.exp (-(c * (D : ℝ) ^ 2)))
          ≤ gClassPMF θ hJN hq hq0 hs1 D 0 := by
  obtain ⟨c, hc, n₀, htail⟩ := exists_gMix_size_tail θ hJN hq hq0 hs1
  have hJ : 1 ≤ J := le_trans (by omega) (offspring_le_of_pos θ hk)
  -- the rate is halved, the mass of one size being read off the tail one step below
  set c' : ℝ := c / 2 with hc'def
  have hc' : 0 < c' := by rw [hc'def]; positivity
  have hp0 : 0 < gPointBase θ := gPointBase_pos θ hq hq0
  have hp1 : gPointBase θ ≤ 1 := gPointBase_le_one θ hq hq0
  have hL0 : 0 ≤ Real.log (gPointBase θ)⁻¹ := by
    rw [Real.log_inv]
    linarith [Real.log_nonpos hp0.le hp1]
  set C₁ : ℝ := 90 * k * J * Real.log (gPointBase θ)⁻¹ with hC₁def
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁def]; positivity
  set C₂ : ℝ := Real.exp (3 * C₁) * (1 - Real.exp (-(c' / 2)))⁻¹ with hC₂def
  have hpos : (0 : ℝ) < 1 - Real.exp (-(c' / 2)) := by
    linarith [exp_neg_half_lt_one hc']
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂def]
    positivity
  obtain ⟨D₁, hD₁⟩ := shape_eta_final (c := c') (C₂ := C₂) hc' hC₂0
  refine ⟨c' / 4, by positivity,
    216 * J ^ 2 + n₀ + ⌈1 / c'⌉₊ + ⌈(5 * C₁ / c') ^ 2⌉₊ + D₁ + 1, fun D hD ↦ ?_⟩
  have hD216 : 216 * J ^ 2 ≤ D := by omega
  have hDn₀ : n₀ + 1 ≤ D := by omega
  have hDc1 : ⌈1 / c'⌉₊ ≤ D := by omega
  have hDc2 : ⌈(5 * C₁ / c') ^ 2⌉₊ ≤ D := by omega
  have hDD₁ : D₁ ≤ D := by omega
  have hD1 : 1 ≤ D := by omega
  have hDsq : D ≤ D ^ 2 := Nat.le_self_pow (by norm_num) D
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  set μ := gMixPMF θ hJN hq hq0 hs1 with hμdef
  -- the halving condition
  have hhalf : Real.exp (-(c' * ((D : ℝ) ^ 2))) ≤ 1 / 2 :=
    exp_neg_le_half (one_le_mul_sq_of_ceil_le hc' hD1 hDc1)
  -- the mass above the block
  have hlarge : (∑' σ : GShape, if σ.size ≤ D ^ 2 then 0 else μ σ)
      ≤ ENNReal.ofReal (Real.exp (-(c' * (D : ℝ) ^ 2))) := by
    refine (tsum_gMixPMF_large_le θ hJN hq hq0 hs1 htail (D := D) (by omega)).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have : 0 ≤ c' * (D : ℝ) ^ 2 := by positivity
    rw [hc'def] at this ⊢
    linarith
  -- the small block
  have hsmall : ∀ σ : GShape, μ σ ≠ 0 → σ.size ≤ D ^ 2 →
      1 - Real.exp (-(c' * ((D : ℝ) ^ 2)))
        ≤ gdeg (gClassPMF θ hJN hq hq0 hs1 D) (gNetGraph D) (gNetLab D σ) := by
    intro σ _ hσ
    rw [gNetLab_eq_zero_of_size_le hDR (gSize_cast_le_of_le_sq hσ)]
    exact one_sub_le_gdeg_gClassPMF_zero θ hJN hq hq0 hs1 hD1 (Real.exp_pos _).le hlarge
  -- the mass of the sizes above the block
  set g : ℕ → ℝ := fun n ↦ if n ≤ D ^ 2 then 0 else Real.exp (-(c' * (n : ℝ))) with hgdef
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    rw [hgdef]
    by_cases hn : n ≤ D ^ 2 <;> simp [hn, (Real.exp_pos _).le]
  have hgvan : ∀ n ≤ D ^ 2, g n = 0 := by
    intro n hn
    rw [hgdef]
    simp [hn]
  have hgle : ∀ n, g n ≤ Real.exp (-(c' * (n : ℝ))) := by
    intro n
    rw [hgdef]
    by_cases hn : n ≤ D ^ 2 <;> simp [hn, (Real.exp_pos _).le]
  have hmass : ∀ n, D ^ 2 < n →
      ∑' σ : {σ : GShape // σ.size = n}, μ (σ : GShape) ≤ ENNReal.ofReal (g n) := by
    intro n hn
    have hne : ¬ (n ≤ D ^ 2) := by omega
    have hgn : g n = Real.exp (-(c' * (n : ℝ))) := by rw [hgdef]; simp [hne]
    rw [hgn, hc'def]
    exact tsum_gMixPMF_size_eq_le θ hJN hq hq0 hs1 hc htail (by nlinarith)
  -- the domination
  obtain ⟨s, hs, hsD, hsqrt⟩ := exists_gShrinkScale hJ hD216
  set bb : ℕ → ℝ := fun n ↦ Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt (D : ℝ) + 1))) with hbbdef
  have hbb : ∀ n : ℕ,
      Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt (D : ℝ) + 1))) ≤ bb n := fun n ↦ le_rfl
  have hbb1 : ∀ n, bb n ≤ 1 := by
    intro n
    have hfrac : 0 ≤ (n : ℝ) / Real.sqrt (D : ℝ) := by positivity
    have hx : -(C₁ * ((n : ℝ) / Real.sqrt (D : ℝ) + 1)) ≤ 0 := by nlinarith
    calc bb n ≤ Real.exp 0 := Real.exp_le_exp.mpr hx
      _ = 1 := Real.exp_zero
  have hball : ∀ σ : GShape, μ σ ≠ 0 → D ^ 2 < σ.size →
      bb σ.size ≤ gdeg (gClassPMF θ hJN hq hq0 hs1 D) (gNetGraph D) (gNetLab D σ) :=
    fun σ hσ _ ↦ exp_le_gdeg_gNetGraph θ hJN hq hq0 hs1 h0 hk hk2 hD1 hs hsD hsqrt hσ
  -- the compatibility of the two rates
  have hcomp : 5 / 2 * C₁ / Real.sqrt (D : ℝ) ≤ c' / 2 :=
    rate_compat_of_ceil_le hc' hC₁0 hD1 hDc2
  -- the assembled bound
  have hmain := etaG_map_shape_le (c := c') μ (gNetLab D) (gClassPMF θ hJN hq hq0 hs1 D) rfl
    (gNetGraph D) GShape.size (C₁ := C₁) (D := D) (g := g) (bb := bb) hc' hC₁0 hhalf hsmall
    hg0 hgle hgvan hmass hbb hbb1 hball hcomp
  refine ⟨hmain.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have hfin := hD₁ D hDD₁
    have hrw : 6 * Real.exp (-(c' * ((D : ℝ) ^ 2)))
        + Real.exp (3 * C₁) * ((1 - Real.exp (-(c' / 2)))⁻¹
            * Real.exp (-(c' / 2) * ((D : ℝ) ^ 2)))
        = 6 * Real.exp (-(c' * ((D : ℝ) ^ 2)))
          + C₂ * Real.exp (-(c' / 2) * ((D : ℝ) ^ 2)) := by rw [hC₂def]; ring
    rw [hrw]
    refine hfin.trans (le_of_eq ?_)
    congr 1
    ring
  · have hzero := ofReal_one_sub_le_gClassPMF_zero θ hJN hq hq0 hs1 hD1
      (E := Real.exp (-(c' * (D : ℝ) ^ 2))) (Real.exp_pos _).le hlarge
    have hmono : Real.exp (-(c' * (D : ℝ) ^ 2)) ≤ Real.exp (-(c' / 4 * (D : ℝ) ^ 2)) := by
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ c' * (D : ℝ) ^ 2 := by positivity
      linarith
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hzero

/-- **`thm:relabel` (`it:relabel-eta`), at an arbitrary threshold**: the potential
of the class law is eventually below any positive real, and the class `v₀` carries mass
at least `½`. -/
theorem exists_etaG_gNetGraph_le_ofReal (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {k : ℕ}
    (h0 : 0 < θ 0) (hk : 0 < θ k) (hk2 : 2 ≤ k) {r : ℝ} (hr : 0 < r) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 1 ≤ (D : ℝ) ∧
      etaG (gClassPMF θ hJN hq hq0 hs1 D) (gNetGraph D) ≤ ENNReal.ofReal r ∧
      1 / 2 ≤ gClassPMF θ hJN hq hq0 hs1 D 0 := by
  obtain ⟨c, hc, D₁, hD₁⟩ := exists_etaG_gNetGraph_le θ hJN hq hq0 hs1 h0 hk hk2
  refine ⟨D₁ + ⌈1 / (r * c)⌉₊ + ⌈1 / c⌉₊ + 1, fun D hD ↦ ?_⟩
  have hDD₁ : D₁ ≤ D := by omega
  have hceil : ⌈1 / (r * c)⌉₊ ≤ D := by omega
  have hceil' : ⌈1 / c⌉₊ ≤ D := by omega
  have hD1 : 1 ≤ D := by omega
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hDsq : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  obtain ⟨heta, hzero⟩ := hD₁ D hDD₁
  refine ⟨hDR, heta.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have hy : 0 < c * (D : ℝ) ^ 2 := by positivity
    have hkey := mul_exp_neg_le_one (c * (D : ℝ) ^ 2)
    have hge : 1 / (r * c) ≤ (D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    rw [div_le_iff₀ (by positivity)] at hge
    have hge' : 1 ≤ r * (c * (D : ℝ) ^ 2) := by nlinarith
    nlinarith [Real.exp_pos (-(c * (D : ℝ) ^ 2))]
  · have hhalf := exp_neg_le_half (one_le_mul_sq_of_ceil_le hc hD1 hceil')
    refine le_trans ?_ hzero
    rw [← ofReal_half]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **`thm:relabel` (`it:relabel-eta`), the potential condition of
`thm:matching`**: past a threshold the potential of the class law is at most `10⁻⁴` and
the class `v₀` of the one-vertex shape carries mass at least `½`.  This is also
`thm:cross-relabel` (`it:cross-relabel-eta`). -/
theorem exists_etaG_gNetGraph_small (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {k : ℕ}
    (h0 : 0 < θ 0) (hk : 0 < θ k) (hk2 : 2 ≤ k) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      etaG (gClassPMF θ hJN hq hq0 hs1 D) (gNetGraph D) ≤ 1 / 10000 ∧
      1 / 2 ≤ gClassPMF θ hJN hq hq0 hs1 D 0 := by
  obtain ⟨D₀, hD₀⟩ :=
    exists_etaG_gNetGraph_le_ofReal θ hJN hq hq0 hs1 h0 hk hk2 (r := 1 / 10000) (by norm_num)
  refine ⟨D₀, fun D hD ↦ ⟨(hD₀ D hD).2.1.trans (le_of_eq ?_), (hD₀ D hD).2.2⟩⟩
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
  norm_num

end ChainClasses
