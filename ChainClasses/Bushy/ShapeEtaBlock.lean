import ChainClasses.Scalar.ShapeEta
import GraphMatching.Graph

/-!
`sec:shape-coupling` of `gw_classes_simple.tex`: the potential bound
`thm:shape-coupling` (`it:shape-coupling-eta`), in the form the label graph of
`thm:hairy` asks for, where a vertex carries a shape and not a class.

`thm:shape-eta` sums `eq:potential` over classes.  There every shape of size at most `D²`
is identified with `v₀`, so the small shapes contribute the single term `wgt b₀` and the
remaining classes are indexed by the sizes of their members.  Over the coupling graph the
small shapes stay distinct vertices, each adjacent to the others, and the `v₀`-term becomes
a block.  The estimate is the one the proof of `thm:shape-coupling` makes: a small vertex
sees the whole small block, so its ball mass is at least `μ(small) ≥ 1 - e^{-cD²} ≥ ½` and
its weight is at most `6(1-b) ≤ 6e^{-cD²}`; the block carries total mass at most one, so it
sums to `6e^{-cD²}`, which is what the `v₀`-term gave.  The tail is unchanged.

* `wgt_le_wgt_of_le` is the monotonicity of the one-site weight in the ball mass, and
  `wgt_block_le` the block estimate.
* `wgt_bb_le`, `summable_g_wgt` and `eta_tail_le` are the tail half of `shape_eta_le`,
  isolated so that it can be recombined with a block in place of the `v₀`-term.
* `shape_eta_block_le` is the analogue of `shape_eta_le` over a block, with the same
  conclusion, so `shape_eta_final` closes it unchanged, and `shape_eta_le_of_block`
  recovers `shape_eta_le` from it at a one-element block.

The second half is the bridge between `eq:etaG`, a sum over vertices, and the data
`g`, `bb` indexed by size that the estimates above consume.

* `tsum_fiber_size` groups a sum over vertices by the value of the size, and
  `tsum_split_size` splits off the small block first.
* `etaG_le_size` is `eq:etaG` read through the two, over the mass of each size fibre and a
  lower bound on the ball masses it carries, and `etaG_shape_le` is its combination with
  the tail estimate.  The vertex type is arbitrary and the size is an arbitrary function to
  `ℕ`, so nothing here mentions shapes.
-/

namespace ChainClasses

open Real

variable {c : ℝ} {g : ℕ → ℝ}

/-! ### The small block -/

/-- The one-site weight decreases in the ball mass: more compatible mass, smaller weight. -/
lemma wgt_le_wgt_of_le {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (h : b₁ ≤ b₂) (hb₂ : b₂ ≤ 1) :
    wgt b₂ ≤ wgt b₁ := by
  have hb₂0 : (0 : ℝ) < b₂ := lt_of_lt_of_le hb₁ h
  have h₁ : (0 : ℝ) < b₁ ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hb₁ _
  have h₂ : (0 : ℝ) < b₂ ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hb₂0 _
  have hpow : b₁ ^ ((5 : ℝ) / 2) ≤ b₂ ^ ((5 : ℝ) / 2) :=
    Real.rpow_le_rpow hb₁.le h (by norm_num)
  rw [wgt, wgt, div_le_div_iff₀ h₂ h₁]
  nlinarith

/-- **The small block of `thm:shape-coupling`**: a family of vertices of total mass at most
one, each of ball mass at least `1 - E` with `E ≤ ½`, contributes at most `6E` to
`eq:potential`.  This is the `v₀`-term of `thm:shape-eta` spread over a block. -/
lemma wgt_block_le {ι : Type*} {a bs : ι → ℝ} {E : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 1 / 2)
    (ha0 : ∀ i, 0 ≤ a i) (hasum : Summable a) (hamass : ∑' i, a i ≤ 1)
    (hbs : ∀ i, 1 - E ≤ bs i) (hbs1 : ∀ i, bs i ≤ 1) :
    ∑' i, a i * wgt (bs i) ≤ 6 * E := by
  have hbspos : ∀ i, 0 < bs i := fun i => lt_of_lt_of_le (by linarith) (hbs i)
  have hw : ∀ i, wgt (bs i) ≤ 6 * E := by
    intro i
    have hhalf : (1 : ℝ) / 2 ≤ bs i := by linarith [hbs i]
    have := wgt_le_of_half hhalf (hbs1 i)
    linarith [hbs i]
  have hterm : ∀ i, a i * wgt (bs i) ≤ a i * (6 * E) := fun i =>
    mul_le_mul_of_nonneg_left (hw i) (ha0 i)
  have hsum : Summable fun i => a i * wgt (bs i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (ha0 i) (wgt_nonneg (hbspos i) (hbs1 i)))
      hterm (hasum.mul_right _)
  calc ∑' i, a i * wgt (bs i)
      ≤ ∑' i, a i * (6 * E) := Summable.tsum_le_tsum hterm hsum (hasum.mul_right _)
    _ = (∑' i, a i) * (6 * E) := tsum_mul_right
    _ ≤ 1 * (6 * E) := by
        refine mul_le_mul_of_nonneg_right hamass (by linarith)
    _ = 6 * E := one_mul _

/-! ### The tail of `thm:shape-eta` -/

/-- The tail weight of `eq:shape-domination`: the domination `b ≥ e^{-C₁(n/√D+1)}` dilates
the weight by `e^{3C₁}e^{γn}` with `γ = (5/2)C₁D^{-1/2}`. -/
lemma wgt_bb_le {C₁ : ℝ} {D : ℕ} {bb : ℕ → ℝ} (hC₁ : 0 ≤ C₁)
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n) (n : ℕ) :
    wgt (bb n) ≤ Real.exp (3 * C₁) * Real.exp (5 / 2 * C₁ / Real.sqrt D * (n : ℝ)) := by
  refine (wgt_le_of_exp (hbb n)).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hidem : 5 / 2 * (C₁ * ((n : ℝ) / Real.sqrt D + 1))
      = 5 / 2 * C₁ / Real.sqrt D * (n : ℝ) + 5 / 2 * C₁ := by ring
  rw [hidem]
  linarith

lemma wgt_bb_term_le {C₁ : ℝ} {D : ℕ} {bb : ℕ → ℝ} (hC₁ : 0 ≤ C₁) (hg0 : ∀ n, 0 ≤ g n)
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n) (n : ℕ) :
    g n * wgt (bb n)
      ≤ Real.exp (3 * C₁) * (g n * Real.exp (5 / 2 * C₁ / Real.sqrt D * (n : ℝ))) := by
  calc g n * wgt (bb n)
      ≤ g n * (Real.exp (3 * C₁) * Real.exp (5 / 2 * C₁ / Real.sqrt D * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (wgt_bb_le hC₁ hbb n) (hg0 n)
    _ = Real.exp (3 * C₁) * (g n * Real.exp (5 / 2 * C₁ / Real.sqrt D * (n : ℝ))) := by ring

/-- The tail of `eq:potential` is summable: the mass rate `c` beats the dilation. -/
lemma summable_g_wgt {C₁ : ℝ} {D : ℕ} {bb : ℕ → ℝ} (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    (hg0 : ∀ n, 0 ≤ g n) (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))))
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n)
    (hbb1 : ∀ n, bb n ≤ 1)
    (hcomp : 5 / 2 * C₁ / Real.sqrt D ≤ c / 2) :
    Summable fun n : ℕ => g n * wgt (bb n) := by
  have hbbpos : ∀ n, 0 < bb n := fun n => lt_of_lt_of_le (Real.exp_pos _) (hbb n)
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hg0 n) (wgt_nonneg (hbbpos n) (hbb1 n)))
    (wgt_bb_term_le hC₁ hg0 hbb)
    ((summable_eta_tail (γ := 5 / 2 * C₁ / Real.sqrt D) hc hg0 hgle hcomp).mul_left _)

/-- **The tail of `thm:shape-eta`**: the classes whose members all have size exceeding
`D²`, grouped by that size, contribute `e^{3C₁}(1-e^{-c/2})^{-1}e^{-cD²/2}`. -/
theorem eta_tail_le {C₁ : ℝ} {D : ℕ} {bb : ℕ → ℝ} (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    (hg0 : ∀ n, 0 ≤ g n) (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))))
    (hgvan : ∀ n ≤ D ^ 2, g n = 0)
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n)
    (hbb1 : ∀ n, bb n ≤ 1)
    (hcomp : 5 / 2 * C₁ / Real.sqrt D ≤ c / 2) :
    ∑' n : ℕ, g n * wgt (bb n)
      ≤ Real.exp (3 * C₁) * ((1 - Real.exp (-(c / 2)))⁻¹
          * Real.exp (-(c / 2) * ((D : ℝ) ^ 2))) := by
  have hsum1 := summable_g_wgt hc hC₁ hg0 hgle hbb hbb1 hcomp
  have hsum2 : Summable fun n : ℕ =>
      Real.exp (3 * C₁) * (g n * Real.exp (5 / 2 * C₁ / Real.sqrt D * (n : ℝ))) :=
    (summable_eta_tail (γ := 5 / 2 * C₁ / Real.sqrt D) hc hg0 hgle hcomp).mul_left _
  refine (Summable.tsum_le_tsum (wgt_bb_term_le hC₁ hg0 hbb) hsum1 hsum2).trans ?_
  rw [tsum_mul_left]
  have hgeo := eta_tail_sum (N := D ^ 2) (γ := 5 / 2 * C₁ / Real.sqrt D)
    hc hg0 hgle hgvan hcomp
  have hcast : ((D ^ 2 : ℕ) : ℝ) = (D : ℝ) ^ 2 := by push_cast; ring
  rw [hcast] at hgeo
  exact mul_le_mul_of_nonneg_left hgeo (Real.exp_pos _).le

/-! ### The assembled bound over a block -/

/-- **`thm:shape-coupling` (`it:shape-coupling-eta`), the summation.** The analogue
of `shape_eta_le` when the small shapes are not identified: the block of vertices of ball
mass at least `1-e^{-cD²}` contributes `6e^{-cD²}`, exactly what the `v₀`-term of
`thm:shape-eta` contributes, and the tail is unchanged.  The conclusion is that of
`shape_eta_le`, so `shape_eta_final` is the largeness step here too. -/
theorem shape_eta_block_le {ι : Type*} {C₁ : ℝ} {D : ℕ} {bb : ℕ → ℝ} {a bs : ι → ℝ}
    (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    (hhalf : Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ 1 / 2)
    (ha0 : ∀ i, 0 ≤ a i) (hasum : Summable a) (hamass : ∑' i, a i ≤ 1)
    (hbs : ∀ i, 1 - Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ bs i) (hbs1 : ∀ i, bs i ≤ 1)
    (hg0 : ∀ n, 0 ≤ g n) (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))))
    (hgvan : ∀ n ≤ D ^ 2, g n = 0)
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n)
    (hbb1 : ∀ n, bb n ≤ 1)
    (hcomp : 5 / 2 * C₁ / Real.sqrt D ≤ c / 2) :
    (∑' i, a i * wgt (bs i)) + ∑' n : ℕ, g n * wgt (bb n)
      ≤ 6 * Real.exp (-(c * ((D : ℝ) ^ 2)))
        + Real.exp (3 * C₁) * ((1 - Real.exp (-(c / 2)))⁻¹
            * Real.exp (-(c / 2) * ((D : ℝ) ^ 2))) :=
  add_le_add
    (wgt_block_le (Real.exp_pos _).le hhalf ha0 hasum hamass hbs hbs1)
    (eta_tail_le hc hC₁ hg0 hgle hgvan hbb hbb1 hcomp)

/-- The block bound at a one-element block is `shape_eta_le`: the statement of
`thm:shape-eta` follows from `shape_eta_block_le` by taking the block to be the single class
`v₀`, so the two conclusions are interchangeable. -/
theorem shape_eta_le_of_block {C₁ b₀ : ℝ} {D : ℕ} {bb : ℕ → ℝ}
    (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    (hhalf : Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ 1 / 2)
    (hb₀ : 1 - Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ b₀) (hb₀1 : b₀ ≤ 1)
    (hg0 : ∀ n, 0 ≤ g n) (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))))
    (hgvan : ∀ n ≤ D ^ 2, g n = 0)
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n)
    (hbb1 : ∀ n, bb n ≤ 1)
    (hcomp : 5 / 2 * C₁ / Real.sqrt D ≤ c / 2) :
    wgt b₀ + ∑' n : ℕ, g n * wgt (bb n)
      ≤ 6 * Real.exp (-(c * ((D : ℝ) ^ 2)))
        + Real.exp (3 * C₁) * ((1 - Real.exp (-(c / 2)))⁻¹
            * Real.exp (-(c / 2) * ((D : ℝ) ^ 2))) := by
  have h := shape_eta_block_le (ι := Unit) (a := fun _ => (1 : ℝ)) (bs := fun _ => b₀)
    hc hC₁ hhalf (fun _ => zero_le_one) Summable.of_finite (by simp)
    (fun _ => hb₀) (fun _ => hb₀1) hg0 hgle hgvan hbb hbb1 hcomp
  simpa using h

/-! ### `eq:etaG` regrouped by size -/

section Bridge

open GraphMatching
open scoped ENNReal

variable {V : Type*}

lemma gdeg_le_one (μ : PMF V) (G : SimpleGraph V) (v : V) : gdeg μ G v ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (rE_le_one (μ := μ) (R := compat G) (x := v))
  simpa [gdeg] using h

/-- `eq:etaG` written with the one-site weight of `eq:potential`. -/
lemma etaG_eq_tsum_wgt (μ : PMF V) (G : SimpleGraph V) :
    etaG μ G = ∑' v, μ v * ENNReal.ofReal (wgt (gdeg μ G v)) := rfl

/-- A sum over vertices, grouped by the value of the size. -/
lemma tsum_fiber_size (f : V → ℝ≥0∞) (sz : V → ℕ) :
    ∑' v, f v = ∑' n : ℕ, ∑' v : {v : V // sz v = n}, f v := by
  rw [← (Equiv.sigmaFiberEquiv sz).tsum_eq f, ENNReal.tsum_sigma']
  rfl

lemma tsum_small_size (f : V → ℝ≥0∞) (sz : V → ℕ) (N : ℕ) :
    ∑' v : {v : V // sz v ≤ N}, f v = ∑' v, (if sz v ≤ N then f v else 0) := by
  classical
  refine (tsum_subtype {v : V | sz v ≤ N} f).trans (tsum_congr fun v => ?_)
  by_cases hv : sz v ≤ N <;> simp [hv]

/-- **The split of `eq:etaG` by size**: the block of vertices of size at most `N`, and the
rest grouped by size.  The fibres of size at most `N` contribute nothing to the second sum,
which is the vanishing `hgvan` of `shape_eta_le` read on the vertices. -/
lemma tsum_split_size (f : V → ℝ≥0∞) (sz : V → ℕ) (N : ℕ) :
    ∑' v, f v = (∑' v : {v : V // sz v ≤ N}, f v)
      + ∑' n : ℕ, ∑' v : {v : V // sz v = n}, (if sz (v : V) ≤ N then 0 else f v) := by
  classical
  have hsplit : ∀ v : V,
      f v = (if sz v ≤ N then f v else 0) + (if sz v ≤ N then 0 else f v) := by
    intro v; split_ifs <;> simp
  rw [tsum_congr hsplit, ENNReal.tsum_add, tsum_small_size f sz N,
    tsum_fiber_size (fun v => if sz v ≤ N then 0 else f v) sz]

/-- **`eq:etaG` over the size data.** The vertices of size at most `N` form a block of ball
mass at least `1-E`, and the vertices of size `n > N` carry mass at most `g n` and ball mass
at least `bb n`.  The potential is then bounded by the block term `6E` of
`wgt_block_le` and the tail sum that `eta_tail_le` estimates. -/
theorem etaG_le_size (μ : PMF V) (G : SimpleGraph V) (sz : V → ℕ) (N : ℕ)
    {E : ℝ} {g bb : ℕ → ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 1 / 2)
    (hsmall : ∀ v : V, sz v ≤ N → 1 - E ≤ gdeg μ G v)
    (hbb0 : ∀ n, 0 < bb n) (hbb1 : ∀ n, bb n ≤ 1) (hg0 : ∀ n, 0 ≤ g n)
    (hmass : ∀ n, N < n → ∑' v : {v : V // sz v = n}, μ v ≤ ENNReal.ofReal (g n))
    (hball : ∀ v : V, N < sz v → bb (sz v) ≤ gdeg μ G v)
    (hsum : Summable fun n => g n * wgt (bb n)) :
    etaG μ G ≤ ENNReal.ofReal (6 * E + ∑' n : ℕ, g n * wgt (bb n)) := by
  classical
  have hwgt0 : ∀ n, 0 ≤ g n * wgt (bb n) := fun n =>
    mul_nonneg (hg0 n) (wgt_nonneg (hbb0 n) (hbb1 n))
  -- the block of small vertices
  have hblock :
      (∑' v : {v : V // sz v ≤ N}, μ (v : V) * ENNReal.ofReal (wgt (gdeg μ G (v : V))))
        ≤ ENNReal.ofReal (6 * E) := by
    have hterm : ∀ v : {v : V // sz v ≤ N},
        μ (v : V) * ENNReal.ofReal (wgt (gdeg μ G (v : V)))
          ≤ μ (v : V) * ENNReal.ofReal (6 * E) := by
      intro w
      have hb := hsmall (w : V) w.2
      have hb1 := gdeg_le_one μ G (w : V)
      have hhalf : (1 : ℝ) / 2 ≤ gdeg μ G (w : V) := by linarith
      have hw : wgt (gdeg μ G (w : V)) ≤ 6 * E := by
        have := wgt_le_of_half hhalf hb1
        linarith
      gcongr
    calc (∑' v : {v : V // sz v ≤ N}, μ (v : V) * ENNReal.ofReal (wgt (gdeg μ G (v : V))))
        ≤ ∑' v : {v : V // sz v ≤ N}, μ (v : V) * ENNReal.ofReal (6 * E) :=
          ENNReal.tsum_le_tsum hterm
      _ = (∑' v : {v : V // sz v ≤ N}, μ (v : V)) * ENNReal.ofReal (6 * E) :=
          ENNReal.tsum_mul_right
      _ ≤ 1 * ENNReal.ofReal (6 * E) := by
          gcongr
          exact (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans_eq
            μ.tsum_coe
      _ = ENNReal.ofReal (6 * E) := one_mul _
  -- the fibres above the block
  have hfib : ∀ n : ℕ,
      (∑' v : {v : V // sz v = n}, (if sz (v : V) ≤ N then 0
        else μ (v : V) * ENNReal.ofReal (wgt (gdeg μ G (v : V)))))
        ≤ ENNReal.ofReal (g n * wgt (bb n)) := by
    intro n
    by_cases hn : N < n
    · have hterm : ∀ v : {v : V // sz v = n},
          (if sz (v : V) ≤ N then 0
            else μ (v : V) * ENNReal.ofReal (wgt (gdeg μ G (v : V))))
            ≤ μ (v : V) * ENNReal.ofReal (wgt (bb n)) := by
        intro w
        have hw : sz (w : V) = n := w.2
        rw [if_neg (by omega)]
        gcongr
        refine wgt_le_wgt_of_le (hbb0 n) ?_ (gdeg_le_one μ G (w : V))
        have hb := hball (w : V) (by omega)
        rwa [hw] at hb
      calc (∑' v : {v : V // sz v = n}, (if sz (v : V) ≤ N then 0
              else μ (v : V) * ENNReal.ofReal (wgt (gdeg μ G (v : V)))))
          ≤ ∑' v : {v : V // sz v = n}, μ (v : V) * ENNReal.ofReal (wgt (bb n)) :=
            ENNReal.tsum_le_tsum hterm
        _ = (∑' v : {v : V // sz v = n}, μ (v : V)) * ENNReal.ofReal (wgt (bb n)) :=
            ENNReal.tsum_mul_right
        _ ≤ ENNReal.ofReal (g n) * ENNReal.ofReal (wgt (bb n)) := by
            gcongr
            exact hmass n hn
        _ = ENNReal.ofReal (g n * wgt (bb n)) := (ENNReal.ofReal_mul (hg0 n)).symm
    · have hzero : ∀ v : {v : V // sz v = n},
          (if sz (v : V) ≤ N then 0
            else μ (v : V) * ENNReal.ofReal (wgt (gdeg μ G (v : V)))) = 0 := by
        intro w
        have hw : sz (w : V) = n := w.2
        rw [if_pos (by omega)]
      rw [tsum_congr hzero, tsum_zero]
      exact zero_le
  have htail :
      (∑' n : ℕ, ∑' v : {v : V // sz v = n}, (if sz (v : V) ≤ N then 0
        else μ (v : V) * ENNReal.ofReal (wgt (gdeg μ G (v : V)))))
        ≤ ENNReal.ofReal (∑' n : ℕ, g n * wgt (bb n)) :=
    (ENNReal.tsum_le_tsum hfib).trans_eq
      (ENNReal.ofReal_tsum_of_nonneg hwgt0 hsum).symm
  rw [etaG_eq_tsum_wgt,
    tsum_split_size (fun v => μ v * ENNReal.ofReal (wgt (gdeg μ G v))) sz N,
    ENNReal.ofReal_add (by linarith) (tsum_nonneg hwgt0)]
  exact add_le_add hblock htail

/-- **`thm:shape-coupling` (`it:shape-coupling-eta`)** over the size data: the
combination of `etaG_le_size` with the tail estimate `eta_tail_le`, at the block threshold
`N = D²` of the paper.  `shape_eta_final` is again the largeness step. -/
theorem etaG_shape_le (μ : PMF V) (G : SimpleGraph V) (sz : V → ℕ)
    {C₁ : ℝ} {D : ℕ} {g bb : ℕ → ℝ} (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    (hhalf : Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ 1 / 2)
    (hsmall : ∀ v : V, sz v ≤ D ^ 2 →
      1 - Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ gdeg μ G v)
    (hg0 : ∀ n, 0 ≤ g n) (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))))
    (hgvan : ∀ n ≤ D ^ 2, g n = 0)
    (hmass : ∀ n, D ^ 2 < n → ∑' v : {v : V // sz v = n}, μ v ≤ ENNReal.ofReal (g n))
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n)
    (hbb1 : ∀ n, bb n ≤ 1)
    (hball : ∀ v : V, D ^ 2 < sz v → bb (sz v) ≤ gdeg μ G v)
    (hcomp : 5 / 2 * C₁ / Real.sqrt D ≤ c / 2) :
    etaG μ G ≤ ENNReal.ofReal (6 * Real.exp (-(c * ((D : ℝ) ^ 2)))
      + Real.exp (3 * C₁) * ((1 - Real.exp (-(c / 2)))⁻¹
          * Real.exp (-(c / 2) * ((D : ℝ) ^ 2)))) := by
  have hbb0 : ∀ n, 0 < bb n := fun n => lt_of_lt_of_le (Real.exp_pos _) (hbb n)
  refine (etaG_le_size μ G sz (D ^ 2) (Real.exp_pos _).le hhalf hsmall hbb0 hbb1 hg0
    hmass hball (summable_g_wgt hc hC₁ hg0 hgle hbb hbb1 hcomp)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have := eta_tail_le hc hC₁ hg0 hgle hgvan hbb hbb1 hcomp
  linarith

end Bridge

end ChainClasses
