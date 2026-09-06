import ChainClasses.General.GeneralShapeMass
import ChainClasses.Bushy.ShapeLabelLaw
import ChainClasses.General.GeneralHarris
import BranchingProcess.Progeny
import ChainClasses.Scalar.ShapeMass

/-!
`thm:mass-uniform` of `matching_classes_general.tex`, the tail clause: under every
conditional shape law `μ_κ` and under the mixture `μ`, the size of a shape has an
exponential tail with constants depending on the offspring law alone.

The method is the one of `ShapeSizeTail` at general bounded support.  A shape is its neck
length together with one bush list per neck vertex, so the size moment of the joint mass
`gPairMass` is a geometric series in the neck length whose ratio is `s` times the
decoration moment, the sum of the neck weights against the bush moment to the number of
bushes.  A bush list of `r` bushes is an `r`-tuple, so the decoration moment is a
polynomial of degree below `J` in the bush moment `∑_t ℙ(T = t) s^{|t|}`, which is the
exponential moment of the total progeny of the conjugate law: the bush of a dying subtree
has as many vertices as its sample, and the fibres of `bushRTree` partition the sample
space.  At `s = 1` the bush moment is at most one and the decoration moment is `θ̃₁ < 1`;
the conjugate law is subcritical, so the progeny equation of `BranchingProcess.Progeny`
keeps the bush moment within `1 + δ` at some `s ∈ (1, 1 + δ]`, and `δ` small against
`θ̃₁` keeps the ratio below one.  The split moments are finitely many finite sums, so one
`s` serves every arity, and Markov's inequality for the exponential moment turns the
moments into tails, the constants absorbed past a threshold chosen once for all arities.

* `mem_sample_iff_isAddr_rtreeOf`, `size_bushRTree`, `ae_size_bushRTree`: **the size of a
  bush**, the number of vertices of the sample.
* `bushMeasure_offspring_le_general`, `bushMeasure_survives_general`: the two null
  events of the bush law at general support.
* `skeletonWeight_one_eq_genDeriv`, `conjugate_mean_eq`, `conjugate_isSubcritical_general`:
  **the conjugate law is subcritical**, its mean being `f'(q) = θ̃₁`.
* `gBushMoment`, `tsum_bushMassR_mul_pow`, `exists_bush_moment_near_one`: **the bush moment**, read as the exponential moment of
  the total progeny, and kept within `1 + δ` at some `s > 1`.
* `gDecWeight`, `gDecMoment`, `gSplitMoment`, `gDecMoment_eq`, `gSplitMoment_eq`,
  `tsum_gDecWeight_one`, `gDecMoment_le`, `gSplitMoment_lt_top`: **the decoration and
  split moments**, polynomials in the bush moment.
* `gShapeSigmaEquiv`, `tsum_gPairMass_mul_pow`, `exists_gPairMass_moment`: **the size
  moment of the joint mass** as a geometric series, finite at one `s > 1` for every arity.
* `tail_le_of_moment_le`: Markov's inequality for the exponential moment in `ℝ≥0∞`.
* `exists_gShape_size_tail`, `exists_gCond_size_tail`, `exists_gMix_size_tail`:
  **`thm:mass-uniform`, the tail clause**, the exponential tail of the size under every
  `μ_κ` and under `μ`, with constants depending on `θ` alone.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BranchingProcess (sample Survives Offspring sampleMeasure survivalMeasure bushMeasure)

variable {J N : ℕ}

/-! ### The size of a bush -/

/-- **The vertices of a bush are the vertices of the sample**: within the alphabet bound
and past a height bound, a word lies in the sample exactly when it is an address of the
read tree. -/
lemma mem_sample_iff_isAddr_rtreeOf : ∀ (n : ℕ) {d : GWord N → ℕ}, (∀ v, d v ≤ N) →
    (∀ u ∈ sample d, u.length ≤ n) → ∀ v : GWord N,
    v ∈ sample d ↔ RTree.IsAddr (rtreeOf n d) (v.map Fin.val) := by
  intro n
  induction n with
  | zero =>
      intro d _ hn v
      cases v with
      | nil => exact iff_of_true (BranchingProcess.nil_mem_sample d) (RTree.isAddr_nil _)
      | cons i u =>
          refine iff_of_false (fun h ↦ ?_) ?_
          · have := hn _ h
            simp at this
          · show ¬ RTree.IsAddr (RTree.node []) (i.val :: u.map Fin.val)
            rw [RTree.isAddr_cons]
            rintro ⟨h, -⟩
            simp at h
  | succ n ih =>
      intro d hd hn v
      cases v with
      | nil => exact iff_of_true (BranchingProcess.nil_mem_sample d) (RTree.isAddr_nil _)
      | cons i u =>
          have hlen : (List.ofFn fun j : Fin (min (d []) N) ↦
              rtreeOf n
                (ambSub d [⟨(j : ℕ), lt_of_lt_of_le j.isLt (min_le_right _ _)⟩])).length
              = d [] := by
            rw [List.length_ofFn, min_eq_left (hd [])]
          have hd' : ∀ v, ambSub d [i] v ≤ N := fun v ↦ hd _
          show i :: u ∈ sample d ↔ RTree.IsAddr (RTree.node _) (i.val :: u.map Fin.val)
          rw [RTree.isAddr_cons, mem_sample_cons_ambSub]
          constructor
          · rintro ⟨hi, hu⟩
            refine ⟨by rwa [hlen], ?_⟩
            simp only [List.getElem_ofFn, Fin.eta]
            exact (ih hd' (sample_bound_ambSub hn i hi) u).mp hu
          · rintro ⟨h, hu⟩
            have hi : (i : ℕ) < d [] := by rwa [hlen] at h
            refine ⟨hi, (ih hd' (sample_bound_ambSub hn i hi) u).mpr ?_⟩
            simpa only [List.getElem_ofFn, Fin.eta] using hu

/-- The letters of an address of a read tree stay below the alphabet bound. -/
lemma lt_of_isAddr_rtreeOf : ∀ (n : ℕ) (d : GWord N → ℕ) (w : List ℕ),
    RTree.IsAddr (rtreeOf n d) w → ∀ i ∈ w, i < N := by
  intro n
  induction n with
  | zero =>
      intro d w hw i hi
      cases w with
      | nil => simp at hi
      | cons j w' =>
          change RTree.IsAddr (RTree.node []) (j :: w') at hw
          rw [RTree.isAddr_cons] at hw
          obtain ⟨h, -⟩ := hw
          simp at h
  | succ n ih =>
      intro d w hw i hi
      cases w with
      | nil => simp at hi
      | cons j w' =>
          change RTree.IsAddr (RTree.node _) (j :: w') at hw
          rw [RTree.isAddr_cons] at hw
          obtain ⟨h, hw'⟩ := hw
          rw [List.length_ofFn] at h
          rw [List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact lt_of_lt_of_le h (min_le_right _ _)
          · simp only [List.getElem_ofFn] at hw'
            exact ih _ _ hw' i hi

/-- A word of letters below the alphabet bound is the image of an ambient word. -/
lemma exists_map_val_eq : ∀ (w : List ℕ), (∀ i ∈ w, i < N) →
    ∃ v : GWord N, v.map Fin.val = w
  | [], _ => ⟨[], rfl⟩
  | i :: w, h => by
      obtain ⟨v, hv⟩ := exists_map_val_eq w fun j hj ↦ h j (List.mem_cons_of_mem i hj)
      exact ⟨⟨i, h i List.mem_cons_self⟩ :: v, by rw [List.map_cons, hv]⟩

/-- **The size of a bush**: the bush of a dying field supported within the alphabet has
as many vertices as the sample. -/
theorem size_bushRTree {d : GWord N → ℕ} (hd : ∀ v, d v ≤ N) (hfin : ¬ Survives d) :
    (bushRTree d).size = (sample d : Set (GWord N)).ncard := by
  classical
  have hn := sampleHeight_spec hfin
  have hinj : Function.Injective fun v : GWord N ↦ v.map Fin.val :=
    List.map_injective_iff.mpr Fin.val_injective
  have himage : (fun v : GWord N ↦ v.map Fin.val) '' (sample d : Set (GWord N))
      = ((RTree.addrList (bushRTree d)).toFinset : Set (List ℕ)) := by
    ext w
    simp only [Set.mem_image, SetLike.mem_coe, List.mem_toFinset,
      RTree.mem_addrList_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (mem_sample_iff_isAddr_rtreeOf _ hd hn v).mp hv
    · intro hw
      obtain ⟨v, rfl⟩ := exists_map_val_eq w (lt_of_isAddr_rtreeOf _ d w hw)
      exact ⟨v, (mem_sample_iff_isAddr_rtreeOf _ hd hn v).mpr hw, rfl⟩
  rw [← Set.ncard_image_of_injective (sample d : Set (GWord N)) hinj, himage,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup (RTree.nodup_addrList _),
    RTree.length_addrList]

/-! ### The two null events of the bush law -/

/-- Conditioning on extinction keeps the null events of the sample law null. -/
lemma bushMeasure_absolutelyContinuous_general (θ : Offspring J) :
    bushMeasure (N := N) θ ≪ sampleMeasure (N := N) θ :=
  ProbabilityTheory.cond_absolutelyContinuous

/-- A coordinate above the alphabet bound is null under the bush law. -/
lemma bushMeasure_coord_gt (θ : Offspring J) (hJN : J ≤ N) (v : GWord N) :
    bushMeasure (N := N) θ {c : GWord N → ℕ | N < c v} = 0 := by
  refine bushMeasure_absolutelyContinuous_general θ ?_
  have hdecomp : {c : GWord N → ℕ | N < c v}
      = ⋃ j : ℕ, {c : GWord N → ℕ | c v = N + 1 + j} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨c v - N - 1, by omega⟩
    · rintro ⟨j, hj⟩
      omega
  rw [hdecomp]
  refine measure_iUnion_null fun j ↦ ?_
  rw [BranchingProcess.sampleMeasure_coord θ v (N + 1 + j), θ.vanishing _ (by omega),
    ENNReal.ofReal_zero]

/-- Almost every bush is supported within the alphabet, which is what reading a bush off
a field asks for. -/
lemma bushMeasure_offspring_le_general (θ : Offspring J) (hJN : J ≤ N) :
    bushMeasure (N := N) θ {c : GWord N → ℕ | ¬ ∀ v, c v ≤ N} = 0 := by
  have he : {c : GWord N → ℕ | ¬ ∀ v, c v ≤ N}
      = ⋃ v : GWord N, {c : GWord N → ℕ | N < c v} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall, not_le]
  rw [he]
  exact measure_iUnion_null fun v ↦ bushMeasure_coord_gt θ hJN v

/-- Almost every bush dies: the law is conditioned on exactly that. -/
lemma bushMeasure_survives_general (θ : Offspring J) :
    bushMeasure (N := N) θ {c : GWord N → ℕ | Survives c} = 0 := by
  have hempty : {c : GWord N → ℕ | ¬ Survives c} ∩ {c : GWord N → ℕ | Survives c}
      = (∅ : Set (GWord N → ℕ)) := by
    ext c
    simp
  rw [BranchingProcess.bushMeasure_apply, hempty, measure_empty, mul_zero]

/-- The size of a bush agrees with the size of the sample almost surely. -/
lemma ae_size_bushRTree (θ : Offspring J) (hJN : J ≤ N) :
    ∀ᵐ d ∂(bushMeasure (N := N) θ),
      (bushRTree d).size = (sample d : Set (GWord N)).ncard := by
  have h1 : ∀ᵐ c ∂(bushMeasure (N := N) θ), ∀ v, c v ≤ N :=
    ae_iff.mpr (bushMeasure_offspring_le_general θ hJN)
  have h2 : ∀ᵐ c ∂(bushMeasure (N := N) θ), ¬ Survives c := by
    rw [ae_iff]
    have hset : {c : GWord N → ℕ | ¬ ¬ Survives c} = {c : GWord N → ℕ | Survives c} := by
      ext c
      simp
    rw [hset]
    exact bushMeasure_survives_general θ
  filter_upwards [h1, h2] with c hc1 hc2
  exact size_bushRTree hc1 hc2

/-! ### The conjugate law is subcritical -/

/-- **The skeleton weight at one is the derivative at the extinction probability**,
`θ̃₁ = f'(q)`. -/
lemma skeletonWeight_one_eq_genDeriv (θ : Offspring J) (hq : θ.extinction < 1) :
    θ.skeletonWeight 1 = genDeriv J θ θ.extinction := by
  rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ one_ne_zero]
  have h : θ.surviveWeight 1 = surviveCoeff J θ θ.extinction 1 := rfl
  rw [h, ← tilde_one J θ hq, tilde, if_neg one_ne_zero]

/-- **The mean of the conjugate law is `f'(q)`.** -/
lemma conjugate_mean_eq (θ : Offspring J) (hq0 : 0 < θ.extinction) :
    Offspring.mean (θ.conjugate hq0) = genDeriv J θ θ.extinction := by
  rw [Offspring.mean, ← conjugate_mean_general J θ hq0.ne']
  rfl

/-- **`thm:harris-general`, the arithmetic**: the conjugate law is subcritical exactly
in the chain regime, its mean being `f'(q) = θ̃₁ < 1`. -/
theorem conjugate_isSubcritical_general (θ : Offspring J) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) :
    (θ.conjugate hq0).IsSubcritical := by
  show Offspring.mean (θ.conjugate hq0) < 1
  rw [conjugate_mean_eq θ hq0, ← skeletonWeight_one_eq_genDeriv θ hq]
  exact hs1

/-! ### The bush moment -/

/-- **The bush moment**: the masses of the bushes against a power of the size, the
quantity the decoration and split moments are polynomials in. -/
noncomputable def gBushMoment (θ : Offspring J) (s : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t : RTree, bushMassR (N := N) θ t * s ^ t.size

/-- **The bush moment is the exponential moment of the total progeny**: the fibres of the
bush partition the sample space, and on almost every field the bush has as many vertices
as the sample. -/
theorem tsum_bushMassR_mul_pow (θ : Offspring J) (hJN : J ≤ N) (s : ℝ≥0∞) :
    gBushMoment (N := N) θ s
      = ∫⁻ d, s ^ ((sample d : Set (GWord N)).ncard) ∂(bushMeasure (N := N) θ) := by
  have hmeas : ∀ t : RTree, AEMeasurable
      (fun d : GWord N → ℕ ↦ Set.indicator {d : GWord N → ℕ | bushRTree d = t}
        (fun _ ↦ s ^ t.size) d) (bushMeasure (N := N) θ) :=
    fun t ↦ (measurable_const.indicator (fibreMeasurableG_bushRTree t)).aemeasurable
  have hpt : ∀ d : GWord N → ℕ,
      ∑' t : RTree, Set.indicator {d : GWord N → ℕ | bushRTree d = t} (fun _ ↦ s ^ t.size) d
        = s ^ ((bushRTree d).size) := by
    intro d
    refine (tsum_eq_single (bushRTree d) fun t ht ↦ ?_).trans ?_
    · have hnot : d ∉ {d' : GWord N → ℕ | bushRTree d' = t} :=
        fun h ↦ ht (h : bushRTree d = t).symm
      exact Set.indicator_of_notMem hnot _
    · have hmem : d ∈ {d' : GWord N → ℕ | bushRTree d' = bushRTree d} := rfl
      exact Set.indicator_of_mem hmem _
  have hae : ∫⁻ d, s ^ ((bushRTree d).size) ∂(bushMeasure (N := N) θ)
      = ∫⁻ d, s ^ ((sample d : Set (GWord N)).ncard) ∂(bushMeasure (N := N) θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_size_bushRTree θ hJN] with d hd
    rw [hd]
  calc gBushMoment (N := N) θ s
      = ∑' t : RTree, ∫⁻ d, Set.indicator {d : GWord N → ℕ | bushRTree d = t}
          (fun _ ↦ s ^ t.size) d ∂(bushMeasure (N := N) θ) := by
        refine tsum_congr fun t ↦ ?_
        rw [lintegral_indicator_const (fibreMeasurableG_bushRTree t), bushMassR, mul_comm]
    _ = ∫⁻ d, ∑' t : RTree, Set.indicator {d : GWord N → ℕ | bushRTree d = t}
          (fun _ ↦ s ^ t.size) d ∂(bushMeasure (N := N) θ) := (lintegral_tsum hmeas).symm
    _ = ∫⁻ d, s ^ ((bushRTree d).size) ∂(bushMeasure (N := N) θ) := lintegral_congr hpt
    _ = ∫⁻ d, s ^ ((sample d : Set (GWord N)).ncard) ∂(bushMeasure (N := N) θ) := hae

/-- The difference quotient of the generating function is monotone on the nonnegative
half-line. -/
lemma genSlope_mono (θ : Offspring J) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Offspring.genSlope θ s ≤ Offspring.genSlope θ t :=
  Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ hs hst i) (θ.nonneg j)

/-- Once the generating function drops below the diagonal at `y > 1`, it does so on all
of `(1, y]`. -/
lemma gen_lt_self_of_le (θ : Offspring J) {y y' : ℝ} (hy' : 1 < y') (hle : y' ≤ y)
    (hlt : Offspring.gen θ y < y) : Offspring.gen θ y' < y' := by
  have hslope : Offspring.genSlope θ y < 1 := by
    by_contra h
    push Not at h
    have h1 := θ.one_sub_gen y
    have h2 : (1 - y) * Offspring.genSlope θ y ≤ (1 - y) * 1 :=
      mul_le_mul_of_nonpos_left h (by linarith)
    linarith
  have hslope' : Offspring.genSlope θ y' < 1 :=
    lt_of_le_of_lt (genSlope_mono θ (by linarith) hle) hslope
  have h1 := θ.one_sub_gen y'
  have h2 : (1 - y') * 1 < (1 - y') * Offspring.genSlope θ y' :=
    mul_lt_mul_of_neg_left hslope' (by linarith)
  linarith

/-- **The bush moment stays near one**: at `y = 1 + δ` or below, the progeny equation is
solved by `s = y / f̂(y)`, which exceeds one and keeps the bush moment at most `y`. -/
theorem exists_bush_moment_near_one (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℝ, 1 < s ∧ s ≤ 1 + δ ∧
      gBushMoment (N := N) θ (ENNReal.ofReal s) ≤ ENNReal.ofReal (1 + δ) := by
  obtain ⟨y₀, hy₀, hlt₀⟩ :=
    (θ.conjugate hq0).exists_gen_lt_self (conjugate_isSubcritical_general θ hq hq0 hs1)
  set y : ℝ := min y₀ (1 + δ) with hy_def
  have hy1 : 1 < y := lt_min hy₀ (by linarith)
  have hyδ : y ≤ 1 + δ := min_le_right _ _
  have hlt : Offspring.gen (θ.conjugate hq0) y < y :=
    gen_lt_self_of_le _ hy1 (min_le_left _ _) hlt₀
  have hf1 : 1 ≤ Offspring.gen (θ.conjugate hq0) y := by
    calc (1 : ℝ) = Offspring.gen (θ.conjugate hq0) 1 := (Offspring.gen_one _).symm
      _ ≤ Offspring.gen (θ.conjugate hq0) y := Offspring.gen_mono _ zero_le_one hy1.le
  have hfpos : 0 < Offspring.gen (θ.conjugate hq0) y := by linarith
  refine ⟨y / Offspring.gen (θ.conjugate hq0) y, (one_lt_div hfpos).mpr hlt, ?_, ?_⟩
  · exact le_trans (div_le_self (by linarith) hf1) hyδ
  · rw [tsum_bushMassR_mul_pow θ hJN]
    refine le_trans (BranchingProcess.lintegral_pow_ncard_bushMeasure_le θ hJN hq0
      ((one_lt_div hfpos).mpr hlt).le hy1.le (div_mul_cancel₀ _ hfpos.ne')) ?_
    exact ENNReal.ofReal_le_ofReal hyδ

/-! ### The decoration and split moments -/

/-- The scalar factor of a decoration mass: `j` children of which `k` survive, against
the survival probability. -/
noncomputable def gDecWeight (θ : Offspring J) (j k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k)
    / (1 - θ.extinction))

lemma gDecWeight_eq_zero (θ : Offspring J) {j k : ℕ} (hj : J < j) : gDecWeight θ j k = 0 := by
  rw [gDecWeight, θ.vanishing j hj]
  simp

/-- The number of vertices of a forest is the sum of the sizes of its trees. -/
lemma RTree.sizeF_eq_sum_map : ∀ l : List RTree, RTree.sizeF l = (l.map RTree.size).sum
  | [] => rfl
  | c :: cs => by rw [RTree.sizeF, RTree.sizeF_eq_sum_map cs, List.map_cons, List.sum_cons]

lemma RTree.sizeF_ofFn {r : ℕ} (v : Fin r → RTree) :
    RTree.sizeF (List.ofFn v) = ∑ i, (v i).size := by
  rw [RTree.sizeF_eq_sum_map, List.map_ofFn, List.sum_ofFn]
  rfl

/-- **A decoration mass against a power of the size of its bushes**: the scalar weight
times one bush factor per entry of the tuple. -/
lemma decorationMass_ofFn_mul_pow (θ : Offspring J) (k : ℕ) {r : ℕ} (v : Fin r → RTree)
    (s : ℝ≥0∞) :
    BranchingProcess.decorationMass (N := N) θ (k + r) k (listSets (List.ofFn v))
        * s ^ RTree.sizeF (List.ofFn v)
      = gDecWeight θ (k + r) k * ∏ i, (bushMassR (N := N) θ (v i) * s ^ (v i).size) := by
  rw [gDecWeight, BranchingProcess.decorationMass, Nat.add_sub_cancel_left, Finset.prod_range,
    RTree.sizeF_ofFn, ← Finset.prod_pow_eq_pow_sum, mul_assoc, ← Finset.prod_mul_distrib]
  refine congrArg₂ _ rfl (Finset.prod_congr rfl fun i _ ↦ ?_)
  have hi : (i : ℕ) < (List.ofFn v).length := by
    rw [List.length_ofFn]
    exact i.isLt
  rw [bushMeasure_listSets hi, List.getElem_ofFn, Fin.eta]

/-- A sum over lists is a sum over tuples of every length. -/
lemma tsum_list_eq_tsum_tuple {α : Type*} (H : List α → ℝ≥0∞) :
    ∑' β : List α, H β = ∑' r : ℕ, ∑' v : Fin r → α, H (List.ofFn v) := by
  rw [← Equiv.tsum_eq List.equivSigmaTuple.symm H, ENNReal.tsum_sigma']
  rfl

/-- Summing a weight times a product over the tuples multiplies out. -/
lemma tsum_tuple_mul_prod {α : Type*} (r : ℕ) (w : ℝ≥0∞) (G : α → ℝ≥0∞) :
    ∑' v : Fin r → α, w * ∏ i, G (v i) = w * (∑' a, G a) ^ r := by
  rw [ENNReal.tsum_mul_left, tsum_pi_fin r fun _ a ↦ G a, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- **The decoration moment**: the neck masses against a power of the size of their
bushes, the ratio of the geometric series up to the factor `s` of the neck vertex. -/
noncomputable def gDecMoment (θ : Offspring J) (s : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' β : List RTree, gDecMass (N := N) θ β * s ^ RTree.sizeF β

/-- **The split moment**: the split masses at an arity against a power of the size of
the exit bouquet. -/
noncomputable def gSplitMoment (θ : Offspring J) (κ : ℕ) (s : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' β : List RTree, gSplitMass (N := N) θ κ β * s ^ RTree.sizeF β

/-- **The decoration moment is a polynomial in the bush moment**, one term per number
of bushes. -/
theorem gDecMoment_eq (θ : Offspring J) (s : ℝ≥0∞) :
    gDecMoment (N := N) θ s
      = ∑' r : ℕ, gDecWeight θ (1 + r) 1 * gBushMoment (N := N) θ s ^ r := by
  rw [gDecMoment, tsum_list_eq_tsum_tuple]
  refine tsum_congr fun r ↦ ?_
  rw [gBushMoment, ← tsum_tuple_mul_prod]
  refine tsum_congr fun v ↦ ?_
  rw [gDecMass_def, List.length_ofFn]
  exact decorationMass_ofFn_mul_pow θ 1 v s

/-- **The split moment is a polynomial in the bush moment.** -/
theorem gSplitMoment_eq (θ : Offspring J) (κ : ℕ) (s : ℝ≥0∞) :
    gSplitMoment (N := N) θ κ s
      = ∑' r : ℕ, gDecWeight θ (κ + r) κ * gBushMoment (N := N) θ s ^ r := by
  rw [gSplitMoment, tsum_list_eq_tsum_tuple]
  refine tsum_congr fun r ↦ ?_
  rw [gBushMoment, ← tsum_tuple_mul_prod]
  refine tsum_congr fun v ↦ ?_
  rw [gSplitMass_def, List.length_ofFn]
  exact decorationMass_ofFn_mul_pow θ κ v s

/-- **The neck weights sum to `θ̃₁`**: one survivor at every offspring count. -/
theorem tsum_gDecWeight_one (θ : Offspring J) (hq : θ.extinction < 1) :
    ∑' r : ℕ, gDecWeight θ (1 + r) 1 = ENNReal.ofReal (θ.skeletonWeight 1) := by
  have h1q : (0 : ℝ) < 1 - θ.extinction := by linarith
  have hnn : ∀ j : ℕ, 0 ≤ θ j * (j.choose 1 : ℝ) * (1 - θ.extinction) ^ 1
      * θ.extinction ^ (j - 1) / (1 - θ.extinction) := fun j ↦ by
    have := θ.nonneg j
    have := θ.extinction_nonneg
    positivity
  rw [tsum_eq_sum (s := Finset.range J) fun r hr ↦
    gDecWeight_eq_zero θ (by simp only [Finset.mem_range, not_lt] at hr; omega)]
  rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ one_ne_zero,
    BranchingProcess.Offspring.surviveWeight, Finset.sum_div,
    ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hnn j, Finset.sum_range_succ']
  simp only [Nat.choose_zero_succ, Nat.cast_zero, mul_zero, zero_mul, zero_div,
    ENNReal.ofReal_zero, add_zero]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [gDecWeight, add_comm]

/-- **The decoration moment at a bush moment near one**: every term carries at most `J`
bush factors, so the moment is at most `B^J θ̃₁`. -/
theorem gDecMoment_le (θ : Offspring J) (hq : θ.extinction < 1) {s : ℝ≥0∞} {B : ℝ}
    (hB1 : 1 ≤ B) (hB : gBushMoment (N := N) θ s ≤ ENNReal.ofReal B) :
    gDecMoment (N := N) θ s
      ≤ ENNReal.ofReal B ^ J * ENNReal.ofReal (θ.skeletonWeight 1) := by
  have hB1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal B := ENNReal.one_le_ofReal.mpr hB1
  rw [gDecMoment_eq, ← tsum_gDecWeight_one θ hq, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun r ↦ ?_
  by_cases hr : r < J
  · calc gDecWeight θ (1 + r) 1 * gBushMoment (N := N) θ s ^ r
        ≤ gDecWeight θ (1 + r) 1 * ENNReal.ofReal B ^ r :=
          mul_le_mul' le_rfl (pow_le_pow_left' hB r)
      _ ≤ gDecWeight θ (1 + r) 1 * ENNReal.ofReal B ^ J :=
          mul_le_mul' le_rfl (pow_le_pow_right' hB1' hr.le)
      _ = ENNReal.ofReal B ^ J * gDecWeight θ (1 + r) 1 := mul_comm _ _
  · rw [gDecWeight_eq_zero θ (by omega)]
    simp

/-- **The split moment is finite** whenever the bush moment is: it is a finite sum. -/
theorem gSplitMoment_lt_top (θ : Offspring J) (κ : ℕ) {s : ℝ≥0∞}
    (hB : gBushMoment (N := N) θ s < ⊤) : gSplitMoment (N := N) θ κ s < ⊤ := by
  rw [gSplitMoment_eq, tsum_eq_sum (s := Finset.range (J + 1)) fun r hr ↦ ?_]
  · exact ENNReal.sum_lt_top.mpr fun r _ ↦
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hB)
  · rw [gDecWeight_eq_zero θ (by simp only [Finset.mem_range, not_lt] at hr; omega), zero_mul]

/-! ### The size moment of the joint mass -/

/-- A shape is a neck length together with one bush list per neck vertex. -/
def gShapeSigmaEquiv : GShape ≃ Σ n : ℕ, Fin (n + 1) → List RTree where
  toFun σ := ⟨σ.necks, σ.dec⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The joint mass of a shape against a power of its size: one factor per neck vertex,
each carrying `s` for the vertex itself, and the split factor at the exit. -/
lemma gPairMass_mul_pow (θ : Offspring J) (κ : ℕ) (s : ℝ≥0∞) (σ : GShape) :
    gPairMass (N := N) θ κ σ * s ^ σ.size
      = (∏ i : Fin σ.necks,
          (s * (gDecMass (N := N) θ (σ.dec i.castSucc) * s ^ RTree.sizeF (σ.dec i.castSucc))))
        * (s * (gSplitMass (N := N) θ κ (σ.dec (Fin.last σ.necks))
            * s ^ RTree.sizeF (σ.dec (Fin.last σ.necks)))) := by
  have hprod : (σ.neckList.map (gDecMass (N := N) θ)).prod
      = ∏ i : Fin σ.necks, gDecMass (N := N) θ (σ.dec i.castSucc) := by
    rw [GShape.neckList, List.map_ofFn, List.prod_ofFn]
    rfl
  have hsize : σ.size = (∑ i : Fin σ.necks, RTree.sizeF (σ.dec i.castSucc))
      + RTree.sizeF (σ.dec (Fin.last σ.necks)) + (σ.necks + 1) := by
    rw [GShape.size_eq, GShape.neckLen, GShape.decs, List.map_ofFn, List.sum_ofFn,
      Fin.sum_univ_castSucc]
    simp only [Function.comp]
    omega
  rw [gPairMass_def, hprod, GShape.bouquet, hsize, pow_add, pow_add, pow_succ,
    ← Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **The size moment of the joint mass**: a geometric series in the neck length, the
ratio `s` times the decoration moment and the last term `s` times the split moment. -/
theorem tsum_gPairMass_mul_pow (θ : Offspring J) (κ : ℕ) (s : ℝ≥0∞) :
    ∑' σ : GShape, gPairMass (N := N) θ κ σ * s ^ σ.size
      = ∑' m : ℕ, (s * gDecMoment (N := N) θ s) ^ m * (s * gSplitMoment (N := N) θ κ s) := by
  set G : List RTree → ℝ≥0∞ :=
    fun β ↦ s * (gDecMass (N := N) θ β * s ^ RTree.sizeF β) with hG
  set H : List RTree → ℝ≥0∞ :=
    fun β ↦ s * (gSplitMass (N := N) θ κ β * s ^ RTree.sizeF β) with hH
  have hGsum : ∑' β, G β = s * gDecMoment (N := N) θ s := by
    rw [hG, gDecMoment, ENNReal.tsum_mul_left]
  have hHsum : ∑' β, H β = s * gSplitMoment (N := N) θ κ s := by
    rw [hH, gSplitMoment, ENNReal.tsum_mul_left]
  have hterm : ∀ σ : GShape, gPairMass (N := N) θ κ σ * s ^ σ.size
      = (∏ i : Fin σ.necks, G (σ.dec i.castSucc)) * H (σ.dec (Fin.last σ.necks)) :=
    fun σ ↦ gPairMass_mul_pow θ κ s σ
  have hsigma : ∑' σ : GShape, (∏ i : Fin σ.necks, G (σ.dec i.castSucc))
        * H (σ.dec (Fin.last σ.necks))
      = ∑' n : ℕ, ∑' f : Fin (n + 1) → List RTree,
          (∏ i : Fin n, G (f i.castSucc)) * H (f (Fin.last n)) := by
    rw [← Equiv.tsum_eq gShapeSigmaEquiv.symm, ENNReal.tsum_sigma']
    rfl
  have hfin : ∀ n : ℕ, ∑' f : Fin (n + 1) → List RTree,
        (∏ i : Fin n, G (f i.castSucc)) * H (f (Fin.last n))
      = (∑' β, G β) ^ n * ∑' β, H β := by
    intro n
    set g : Fin (n + 1) → List RTree → ℝ≥0∞ :=
      Fin.snoc (α := fun _ ↦ List RTree → ℝ≥0∞) (fun _ ↦ G) H with hg
    have hcast : ∀ i : Fin n, g i.castSucc = G := fun i ↦ by
      rw [hg, Fin.snoc_castSucc]
    have hlast : g (Fin.last n) = H := by rw [hg, Fin.snoc_last]
    have hprod : ∀ f : Fin (n + 1) → List RTree,
        (∏ i : Fin n, G (f i.castSucc)) * H (f (Fin.last n)) = ∏ i, g i (f i) := by
      intro f
      rw [Fin.prod_univ_castSucc, hlast]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦ by rw [hcast]
    rw [tsum_congr hprod, tsum_pi_fin (n + 1) g, Fin.prod_univ_castSucc, hlast]
    congr 1
    simp only [hcast, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [tsum_congr hterm, hsigma, tsum_congr hfin, hGsum, hHsum]

/-- **The size moment is finite** once the ratio of the geometric series is below one
and the split moment is finite. -/
theorem tsum_gPairMass_mul_pow_lt_top (θ : Offspring J) (κ : ℕ) {s : ℝ≥0∞}
    (hA : s * gDecMoment (N := N) θ s < 1) (hB : s * gSplitMoment (N := N) θ κ s < ⊤) :
    ∑' σ : GShape, gPairMass (N := N) θ κ σ * s ^ σ.size < ⊤ := by
  rw [tsum_gPairMass_mul_pow, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hA)) hB

/-- The joint mass vanishes above the support bound. -/
lemma gPairMass_eq_zero_of_gt (θ : Offspring J) {κ : ℕ} (hκ : J < κ) (σ : GShape) :
    gPairMass (N := N) θ κ σ = 0 := by
  rw [gPairMass_def, gSplitMass_def, BranchingProcess.decorationMass,
    θ.vanishing (κ + σ.bouquet.length) (by omega)]
  simp

/-- **The size of a shape has an exponential moment at one `s > 1` for every arity**: `δ`
small against `θ̃₁` keeps `(1+δ)^{J+1} θ̃₁` below one, and the bush moment is within
`1 + δ` at some `s ∈ (1, 1 + δ]`, which keeps the ratio of the geometric series below
one; the split moments are finite. -/
theorem exists_gPairMass_moment (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) :
    ∃ s : ℝ, 1 < s ∧ ∀ κ : ℕ,
      ∑' σ : GShape, gPairMass (N := N) θ κ σ * ENNReal.ofReal s ^ σ.size < ⊤ := by
  have hnn : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  obtain ⟨δ, hδ, hδlt⟩ :
      ∃ δ : ℝ, 0 < δ ∧ (1 + δ) ^ (J + 1) * θ.skeletonWeight 1 < 1 := by
    have hopen : IsOpen {x : ℝ | x ^ (J + 1) * θ.skeletonWeight 1 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    have hone : (1 : ℝ) ∈ {x : ℝ | x ^ (J + 1) * θ.skeletonWeight 1 < 1} := by
      show (1 : ℝ) ^ (J + 1) * θ.skeletonWeight 1 < 1
      rw [one_pow, one_mul]
      exact hs1
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
    refine ⟨ε / 2, by linarith, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  obtain ⟨s, hs, hsδ, hmom⟩ := exists_bush_moment_near_one θ hJN hq hq0 hs1 hδ
  refine ⟨s, hs, fun κ ↦ ?_⟩
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hδ0 : (0 : ℝ) ≤ 1 + δ := by linarith
  have hA : ENNReal.ofReal s * gDecMoment (N := N) θ (ENNReal.ofReal s) < 1 := by
    calc ENNReal.ofReal s * gDecMoment (N := N) θ (ENNReal.ofReal s)
        ≤ ENNReal.ofReal (1 + δ)
            * (ENNReal.ofReal (1 + δ) ^ J * ENNReal.ofReal (θ.skeletonWeight 1)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hsδ)
            (gDecMoment_le θ hq (by linarith) hmom)
      _ = ENNReal.ofReal ((1 + δ) ^ (J + 1) * θ.skeletonWeight 1) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hδ0, pow_succ]
          ring
      _ < 1 := ENNReal.ofReal_lt_one.mpr hδlt
  have hB : ENNReal.ofReal s * gSplitMoment (N := N) θ κ (ENNReal.ofReal s) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (gSplitMoment_lt_top θ κ (lt_of_le_of_lt hmom ENNReal.ofReal_lt_top))
  exact tsum_gPairMass_mul_pow_lt_top θ κ hA hB

/-! ### Markov's inequality for the exponential moment -/

/-- **Markov's inequality for the exponential moment, in `ℝ≥0∞`**: a law whose size
moment at `s > 1` is at most `M ≥ 1` has tail at most `M s^{-m}` above `m`, which is
`e^{-(log s / 2) m}` once `s^{m/2}` absorbs `M`. -/
theorem tail_le_of_moment_le {T : Type*} (size : T → ℕ) (q : T → ℝ≥0∞) {s M : ℝ}
    (hs : 1 < s) (hM : 1 ≤ M)
    (hmom : ∑' y : T, q y * ENNReal.ofReal s ^ size y ≤ ENNReal.ofReal M) {m : ℕ}
    (hm : 2 * Real.log M ≤ Real.log s * (m : ℝ)) :
    (∑' y : T, if size y ≤ m then 0 else q y)
      ≤ ENNReal.ofReal (Real.exp (-(Real.log s / 2) * (m : ℝ))) := by
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs
  have hs1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal s := ENNReal.one_le_ofReal.mpr hs.le
  have hpow_ne : ENNReal.ofReal s ^ m ≠ 0 :=
    pow_ne_zero m (ENNReal.ofReal_pos.mpr hs0).ne'
  have hpow_top : ENNReal.ofReal s ^ m ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hterm : ∀ y : T, (if size y ≤ m then 0 else q y)
      ≤ q y * ENNReal.ofReal s ^ size y * (ENNReal.ofReal s ^ m)⁻¹ := by
    intro y
    split_ifs with h
    · exact zero_le
    · push Not at h
      calc q y = q y * ENNReal.ofReal s ^ m * (ENNReal.ofReal s ^ m)⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel hpow_ne hpow_top, mul_one]
        _ ≤ q y * ENNReal.ofReal s ^ size y * (ENNReal.ofReal s ^ m)⁻¹ :=
            mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_right' hs1' h.le)) le_rfl
  have hinv : (ENNReal.ofReal s ^ m)⁻¹ = ENNReal.ofReal ((s ^ m)⁻¹) := by
    rw [← ENNReal.ofReal_pow hs0.le, ENNReal.ofReal_inv_of_pos (pow_pos hs0 m)]
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hreal : M * (s ^ m)⁻¹ ≤ Real.exp (-(Real.log s / 2) * (m : ℝ)) := by
    have hMle : M ≤ Real.exp (Real.log s * (m : ℝ) / 2) := by
      calc M = Real.exp (Real.log M) := (Real.exp_log hM0).symm
        _ ≤ Real.exp (Real.log s * (m : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
    have hsm : (s ^ m)⁻¹ = Real.exp (-((m : ℝ) * Real.log s)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hs0]
    rw [hsm]
    calc M * Real.exp (-((m : ℝ) * Real.log s))
        ≤ Real.exp (Real.log s * (m : ℝ) / 2) * Real.exp (-((m : ℝ) * Real.log s)) :=
          mul_le_mul_of_nonneg_right hMle (Real.exp_pos _).le
      _ = Real.exp (-(Real.log s / 2) * (m : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
  calc (∑' y : T, if size y ≤ m then 0 else q y)
      ≤ ∑' y : T, q y * ENNReal.ofReal s ^ size y * (ENNReal.ofReal s ^ m)⁻¹ :=
        ENNReal.tsum_le_tsum hterm
    _ = (∑' y : T, q y * ENNReal.ofReal s ^ size y) * (ENNReal.ofReal s ^ m)⁻¹ :=
        ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal s ^ m)⁻¹ := mul_le_mul' hmom le_rfl
    _ = ENNReal.ofReal (M * (s ^ m)⁻¹) := by
        rw [hinv, ENNReal.ofReal_mul hM0.le]
    _ ≤ ENNReal.ofReal (Real.exp (-(Real.log s / 2) * (m : ℝ))) :=
        ENNReal.ofReal_le_ofReal hreal

/-! ### The tails -/

/-- The reduced weight vanishes above the support bound. -/
lemma reducedWeight_eq_zero_of_gt (θ : Offspring J) {κ : ℕ} (hκ : J < κ) :
    reducedWeight θ κ = 0 := by
  rw [reducedWeight_def, skeletonWeight_eq_zero_of_gt θ (by omega) hκ, zero_div]

/-- The size moment of a conditional law is the moment of the joint mass against the
reduced weight. -/
lemma tsum_gCondMass_mul_pow (θ : Offspring J) (κ : ℕ) (s : ℝ≥0∞) :
    ∑' σ : GShape, gCondMass (N := N) θ κ σ * s ^ σ.size
      = (∑' σ : GShape, gPairMass (N := N) θ κ σ * s ^ σ.size)
          / ENNReal.ofReal (reducedWeight θ κ) := by
  rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun σ ↦ ?_
  rw [gCondMass_def, div_eq_mul_inv, mul_right_comm]

/-- The size moment of the mixture is the sum of the moments of the joint masses over
the arities. -/
lemma tsum_gMixMass_mul_pow (θ : Offspring J) (s : ℝ≥0∞) :
    ∑' σ : GShape, gMixMass (N := N) θ σ * s ^ σ.size
      = ∑' j : ℕ, ∑' σ : GShape, gPairMass (N := N) θ (j + 2) σ * s ^ σ.size := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun σ ↦ ?_
  rw [gMixMass, ENNReal.tsum_mul_right]

/-- **`thm:mass-uniform`, the tail clause**: under every conditional law `μ_κ` charging
its arity and under the mixture `μ`, the size of a shape has an exponential tail, the
rate and the threshold depending on the offspring law alone. -/
theorem exists_gShape_size_tail (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      (∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ κ), ∀ m : ℕ, n₀ ≤ m →
        (∑' y : GShape, if y.size ≤ m then 0 else gCondPMF θ hJN hq hq0 hs1 hκ hν y)
          ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))))
      ∧ (∀ m : ℕ, n₀ ≤ m →
        (∑' y : GShape, if y.size ≤ m then 0 else gMixPMF θ hJN hq hq0 hs1 y)
          ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ)))) := by
  obtain ⟨s, hs, hmom⟩ := exists_gPairMass_moment θ hJN hq hq0 hs1
  set momC : ℕ → ℝ≥0∞ := fun κ ↦
    ∑' σ : GShape, gCondMass (N := N) θ κ σ * ENNReal.ofReal s ^ σ.size with hmomC
  set momM : ℝ≥0∞ :=
    ∑' σ : GShape, gMixMass (N := N) θ σ * ENNReal.ofReal s ^ σ.size with hmomM
  have hmomC_lt : ∀ κ : ℕ, 0 < reducedWeight θ κ → momC κ < ⊤ := by
    intro κ hν
    rw [hmomC]
    simp only
    rw [tsum_gCondMass_mul_pow]
    exact ENNReal.div_lt_top (hmom κ).ne (ENNReal.ofReal_pos.mpr hν).ne'
  have hmomM_lt : momM < ⊤ := by
    rw [hmomM, tsum_gMixMass_mul_pow, tsum_eq_sum (s := Finset.range (J + 1)) fun j hj ↦ ?_]
    · exact ENNReal.sum_lt_top.mpr fun j _ ↦ hmom (j + 2)
    · simp only [Finset.mem_range, not_lt] at hj
      simp only [gPairMass_eq_zero_of_gt θ (by omega : J < j + 2), zero_mul, tsum_zero]
  set M : ℝ := 1 + momM.toReal + ∑ κ ∈ Finset.range (J + 1), (momC κ).toReal with hM_def
  have hsumnn : 0 ≤ ∑ κ ∈ Finset.range (J + 1), (momC κ).toReal :=
    Finset.sum_nonneg fun κ _ ↦ ENNReal.toReal_nonneg
  have hM1 : 1 ≤ M := by
    have := ENNReal.toReal_nonneg (a := momM)
    rw [hM_def]
    linarith
  have ht : 0 < Real.log s := Real.log_pos hs
  refine ⟨Real.log s / 2, by linarith, ⌈2 * Real.log M / Real.log s⌉₊, ?_, ?_⟩
  · intro κ hκ hν m hm
    have hκJ : κ ≤ J := by
      by_contra hgt
      rw [reducedWeight_eq_zero_of_gt θ (by omega)] at hν
      exact lt_irrefl 0 hν
    have hNge : 2 * Real.log M / Real.log s ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm)
    have hNt : 2 * Real.log M ≤ Real.log s * (m : ℝ) := by
      rw [div_le_iff₀ ht] at hNge
      linarith
    have hle : momC κ ≤ ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_toReal (hmomC_lt κ hν).ne]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsingle : (momC κ).toReal ≤ ∑ κ' ∈ Finset.range (J + 1), (momC κ').toReal :=
        Finset.single_le_sum (f := fun κ' ↦ (momC κ').toReal)
          (fun κ' _ ↦ ENNReal.toReal_nonneg) (Finset.mem_range.mpr (by omega))
      have := ENNReal.toReal_nonneg (a := momM)
      rw [hM_def]
      linarith
    exact tail_le_of_moment_le GShape.size (gCondPMF θ hJN hq hq0 hs1 hκ hν) hs hM1 hle hNt
  · intro m hm
    have hNge : 2 * Real.log M / Real.log s ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm)
    have hNt : 2 * Real.log M ≤ Real.log s * (m : ℝ) := by
      rw [div_le_iff₀ ht] at hNge
      linarith
    have hle : momM ≤ ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_toReal hmomM_lt.ne]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hM_def]
      linarith
    exact tail_le_of_moment_le GShape.size (gMixPMF θ hJN hq hq0 hs1) hs hM1 hle hNt

/-- **`thm:mass-uniform`, the tail clause for the conditional laws**: the size of a shape
has an exponential tail under every `μ_κ`, with constants depending on `θ` alone. -/
theorem exists_gCond_size_tail (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ κ), ∀ m : ℕ, n₀ ≤ m →
        (∑' y : GShape, if y.size ≤ m then 0 else gCondPMF θ hJN hq hq0 hs1 hκ hν y)
          ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))) := by
  obtain ⟨c, hc, n₀, h, -⟩ := exists_gShape_size_tail θ hJN hq hq0 hs1
  exact ⟨c, hc, n₀, h⟩

/-- **`thm:mass-uniform`, the tail clause for the mixture**: the size of a shape has an
exponential tail under `μ`, with the constants of the conditional laws. -/
theorem exists_gMix_size_tail (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ m : ℕ, n₀ ≤ m →
      (∑' y : GShape, if y.size ≤ m then 0 else gMixPMF θ hJN hq hq0 hs1 y)
        ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))) := by
  obtain ⟨c, hc, n₀, -, h⟩ := exists_gShape_size_tail θ hJN hq hq0 hs1
  exact ⟨c, hc, n₀, h⟩

end ChainClasses
