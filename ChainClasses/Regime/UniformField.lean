import ChainClasses.General.GeneralCoupling

/-!
`thm:relabel` (`it:relabel-law`) of `matching_classes_general.tex`: the
randomisation of the labelling, as a reusable layer.

The paper labels the reduced skeleton by `x(w) = ℓ_{k(w)}(S(w), U(w))`, with `(U(w))_w`
uniform on `[0,1)`, independent of one another and of the sample, and `ℓ_k(σ, u)` the
atom of the conditional law `π_k(·|σ)` whose interval of cumulative masses contains
`u`.  This file supplies the three ingredients over an arbitrary index type and an
arbitrary encodable type of atoms: the uniform field as the product of copies of the
uniform law, the draw of an atom by a uniform variable, whose fibres are the intervals
of cumulative masses, and the product formula of a probability space against the
uniform field, which decomposes a probe of the labels into rectangles, one per pattern
of the data, each carrying the mass of the pattern against the uniform masses of the
label fibres.  The `N = 2` form of the same mechanism is `uniField` of `CrossLaw`
together with the cut points of `Coupling`.

* `uniformField`, `uniformField_pattern`: the uniform field and its product formula
  over a finite set of indices.
* `cumMass`, `drawNat`, `drawNat_eq_iff`, `volume_drawNat_fibre`, `measurable_drawNat`:
  the draw on `ℕ` by the intervals of cumulative masses.
* `encMass`, `drawBy`, `volume_drawBy_fibre`, `measurableSet_drawBy_fibre`: **the draw
  of an atom of a law on an encodable type**, the map `ℓ(·, u)` at one law.
* `condPMF`, `condDraw`, `volume_condDraw_fibre`, `margFstT_mul_volume_condDraw_fibre`:
  **the conditional draw** `ℓ_k(σ, u)` from a coupling given its
  first coordinate, the fibre of an atom carrying `π_k(σ, τ)/μ_k(σ)`.
* `tsum_pi_prod`: a sum over patterns of a product is the product of the sums.
* `prod_uniformField_pattern`: **the product formula** of a probability space against
  the uniform field, over a finite probe of the labels.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/-! ### The uniform field -/

/-- **The uniform field**: one uniform variable on `[0,1)` at every index, the
variables independent. -/
noncomputable def uniformField (ι : Type*) : Measure (ι → ℝ) :=
  BranchingProcess.fieldMeasure (volume.restrict (Set.Ico (0 : ℝ) 1))

instance isProbabilityMeasure_uniformField (ι : Type*) :
    IsProbabilityMeasure (uniformField ι) :=
  inferInstanceAs (IsProbabilityMeasure
    (BranchingProcess.fieldMeasure (ι := ι) (volume.restrict (Set.Ico (0 : ℝ) 1))))

/-- **The uniform field factorises** over a finite set of indices. -/
lemma uniformField_pattern {ι : Type*} (F : Finset ι) (A : ι → Set ℝ)
    (hA : ∀ u ∈ F, MeasurableSet (A u)) :
    uniformField ι (⋂ u ∈ F, {U : ι → ℝ | U u ∈ A u})
      = ∏ u ∈ F, volume (A u ∩ Set.Ico (0 : ℝ) 1) := by
  have he : (⋂ u ∈ F, {U : ι → ℝ | U u ∈ A u})
      = ⋂ u ∈ F, (BranchingProcess.coord u : (ι → ℝ) → ℝ) ⁻¹' A u := rfl
  rw [he, uniformField, (BranchingProcess.coord_iIndepFun
    (volume.restrict (Set.Ico (0 : ℝ) 1))).measure_inter_preimage_eq_mul F hA]
  refine Finset.prod_congr rfl fun u hu ↦ ?_
  rw [BranchingProcess.coord_law _ u (hA u hu), Measure.restrict_apply (hA u hu)]

/-! ### The draw on `ℕ` -/

/-- The cumulative masses `c_{<n} = ∑_{i<n} p_i`. -/
noncomputable def cumMass (p : ℕ → ℝ≥0∞) (n : ℕ) : ℝ := (∑ i ∈ Finset.range n, p i).toReal

@[simp] lemma cumMass_zero (p : ℕ → ℝ≥0∞) : cumMass p 0 = 0 := by simp [cumMass]

lemma cumMass_nonneg (p : ℕ → ℝ≥0∞) (n : ℕ) : 0 ≤ cumMass p n := ENNReal.toReal_nonneg

lemma sum_range_ne_top_of_tsum {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, p i ≠ ⊤ :=
  ne_top_of_le_ne_top (hp ▸ ENNReal.one_ne_top) (ENNReal.sum_le_tsum _)

lemma ne_top_of_tsum {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) (n : ℕ) : p n ≠ ⊤ :=
  ne_top_of_le_ne_top (hp ▸ ENNReal.one_ne_top) (ENNReal.le_tsum n)

lemma cumMass_succ {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) (n : ℕ) :
    cumMass p (n + 1) = cumMass p n + (p n).toReal := by
  rw [cumMass, cumMass, Finset.sum_range_succ,
    ENNReal.toReal_add (sum_range_ne_top_of_tsum hp n) (ne_top_of_tsum hp n)]

lemma cumMass_mono {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) : Monotone (cumMass p) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [cumMass_succ hp]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

lemma cumMass_le_one {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) (n : ℕ) : cumMass p n ≤ 1 := by
  rw [cumMass, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (hp ▸ ENNReal.sum_le_tsum _)

lemma tendsto_cumMass {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) :
    Filter.Tendsto (cumMass p) Filter.atTop (nhds 1) := by
  have h := ENNReal.tendsto_nat_tsum p
  rw [hp] at h
  have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  rw [ENNReal.toReal_one] at this
  exact this

lemma exists_lt_cumMass {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) {u : ℝ} (hu : u < 1) :
    ∃ n, u < cumMass p (n + 1) := by
  obtain ⟨n, hn⟩ := ((tendsto_cumMass hp).eventually (eventually_gt_nhds hu)).exists
  exact ⟨n, lt_of_lt_of_le hn (cumMass_mono hp (Nat.le_succ n))⟩

/-- The selecting predicate of the draw: `u` lies below the upper cut of the atom, or no
cut exceeds `u`. -/
def drawPred (p : ℕ → ℝ≥0∞) (u : ℝ) (n : ℕ) : Prop :=
  u < cumMass p (n + 1) ∨ ∀ m, cumMass p (m + 1) ≤ u

lemma drawPred_exists (p : ℕ → ℝ≥0∞) (u : ℝ) : ∃ n, drawPred p u n := by
  by_cases h : ∃ m, u < cumMass p (m + 1)
  · obtain ⟨m, hm⟩ := h
    exact ⟨m, Or.inl hm⟩
  · push Not at h
    exact ⟨0, Or.inr h⟩

/-- **The draw on `ℕ`**: the atom whose interval `[c_{<n}, c_{≤n})` of cumulative masses
contains `u`. -/
noncomputable def drawNat (p : ℕ → ℝ≥0∞) (u : ℝ) : ℕ := Nat.find (drawPred_exists p u)

lemma drawNat_eq_iff {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} :
    drawNat p u = n ↔ cumMass p n ≤ u ∧ u < cumMass p (n + 1) := by
  have hne : ¬ ∀ m, cumMass p (m + 1) ≤ u := by
    push Not
    exact exists_lt_cumMass hp hu.2
  have hpred : ∀ m, drawPred p u m ↔ u < cumMass p (m + 1) := fun m ↦ or_iff_left hne
  rw [drawNat, Nat.find_eq_iff]
  simp only [hpred, not_lt]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    cases n with
    | zero => rw [cumMass_zero]; exact hu.1
    | succ m => exact h2 m (Nat.lt_succ_self m)
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun m hm ↦ le_trans (cumMass_mono hp (by omega : m + 1 ≤ n)) h1⟩

/-- The fibre of the draw over `[0,1)` is the interval of cumulative masses. -/
lemma drawNat_fibre {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) (n : ℕ) :
    {u ∈ Set.Ico (0 : ℝ) 1 | drawNat p u = n}
      = Set.Ico (cumMass p n) (cumMass p (n + 1)) := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_Ico]
  constructor
  · rintro ⟨hu, h⟩
    exact (drawNat_eq_iff hp hu).mp h
  · rintro ⟨h1, h2⟩
    have hu : u ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨le_trans (cumMass_nonneg p n) h1, lt_of_lt_of_le h2 (cumMass_le_one hp _)⟩
    exact ⟨hu, (drawNat_eq_iff hp hu).mpr ⟨h1, h2⟩⟩

/-- **The draw has the law `p`**: the uniform mass of the fibre of `n` is `p n`. -/
lemma volume_drawNat_fibre {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) (n : ℕ) :
    volume {u ∈ Set.Ico (0 : ℝ) 1 | drawNat p u = n} = p n := by
  rw [drawNat_fibre hp n, Real.volume_Ico, cumMass_succ hp, add_sub_cancel_left,
    ENNReal.ofReal_toReal (ne_top_of_tsum hp n)]

lemma measurable_drawNat (p : ℕ → ℝ≥0∞) : Measurable (drawNat p) := by
  unfold drawNat
  refine measurable_find (drawPred_exists p) fun k ↦ ?_
  have : {u : ℝ | drawPred p u k}
      = Set.Iio (cumMass p (k + 1)) ∪ ⋂ m, Set.Ici (cumMass p (m + 1)) := by
    ext u
    simp [drawPred]
  rw [this]
  exact measurableSet_Iio.union (MeasurableSet.iInter fun m ↦ measurableSet_Ici)

/-! ### The draw of an atom of a law on an encodable type -/

variable {T : Type*}

lemma margFstT_le_one (π : PMF (T × T)) (a : T) : margFstT π a ≤ 1 := by
  calc margFstT π a ≤ ∑' a', margFstT π a' := ENNReal.le_tsum a
    _ = ∑' p : T × T, π p := by rw [ENNReal.tsum_prod']; rfl
    _ = 1 := π.tsum_coe

lemma margFstT_ne_top (π : PMF (T × T)) (a : T) : margFstT π a ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (margFstT_le_one π a)

variable [Encodable T]

/-- The masses of a law along the encoding: `ν t` at `encode t`, zero off the range. -/
noncomputable def encMass (ν : PMF T) : ℕ → ℝ≥0∞ := Function.extend Encodable.encode ν 0

lemma encMass_encode (ν : PMF T) (t : T) : encMass ν (Encodable.encode t) = ν t :=
  Encodable.encode_injective.extend_apply _ _ _

lemma encMass_of_notMem_range (ν : PMF T) {n : ℕ}
    (hn : n ∉ Set.range (Encodable.encode : T → ℕ)) : encMass ν n = 0 :=
  Function.extend_apply' _ _ _ hn

lemma tsum_encMass (ν : PMF T) : ∑' n, encMass ν n = 1 := by
  rw [encMass, tsum_extend_zero Encodable.encode_injective]
  exact ν.tsum_coe

/-- **The draw of an atom**: `u` selects the interval of cumulative masses along the
encoding, and the atom is decoded; the default never occurs on `[0,1)`. -/
noncomputable def drawBy (ν : PMF T) (u : ℝ) : T :=
  (Encodable.decode (drawNat (encMass ν) u)).getD ν.support_nonempty.some

lemma drawBy_eq_iff (ν : PMF T) {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) (t : T) :
    drawBy ν u = t ↔ drawNat (encMass ν) u = Encodable.encode t := by
  constructor
  · intro h
    set n := drawNat (encMass ν) u with hn
    have hmem : n ∈ Set.range (Encodable.encode : T → ℕ) := by
      by_contra hnot
      have h0 : encMass ν n = 0 := encMass_of_notMem_range ν hnot
      have hc := (drawNat_eq_iff (tsum_encMass ν) hu).mp hn.symm
      rw [cumMass_succ (tsum_encMass ν), h0, ENNReal.toReal_zero, add_zero] at hc
      exact absurd hc.2 (not_lt.mpr hc.1)
    obtain ⟨t', ht'⟩ := hmem
    rw [drawBy, ← hn, ← ht', Encodable.encodek, Option.getD_some] at h
    rw [← ht', h]
  · intro h
    rw [drawBy, h, Encodable.encodek, Option.getD_some]

/-- **The draw has the law `ν`.** -/
lemma volume_drawBy_fibre (ν : PMF T) (t : T) :
    volume {u ∈ Set.Ico (0 : ℝ) 1 | drawBy ν u = t} = ν t := by
  have : {u ∈ Set.Ico (0 : ℝ) 1 | drawBy ν u = t}
      = {u ∈ Set.Ico (0 : ℝ) 1 | drawNat (encMass ν) u = Encodable.encode t} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    exact and_congr_right fun hu ↦ drawBy_eq_iff ν hu t
  rw [this, volume_drawNat_fibre (tsum_encMass ν), encMass_encode]

lemma measurableSet_drawBy_fibre (ν : PMF T) (t : T) :
    MeasurableSet {u : ℝ | drawBy ν u = t} :=
  measurable_drawNat (encMass ν)
    (MeasurableSet.of_discrete
      (s := {n : ℕ | (Encodable.decode n).getD ν.support_nonempty.some = t}))

/-! ### The conditional draw from a coupling -/

/-- **The conditional law** `π(·|σ)` of a coupling given its first coordinate. -/
noncomputable def condPMF (π : PMF (T × T)) (σ : T) (h : margFstT π σ ≠ 0) : PMF T :=
  ⟨fun τ ↦ π (σ, τ) / margFstT π σ, by
    have htotal : ∑' τ, π (σ, τ) / margFstT π σ = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      exact ENNReal.mul_inv_cancel h (margFstT_ne_top π σ)
    exact htotal ▸ ENNReal.summable.hasSum⟩

omit [Encodable T] in
@[simp] lemma condPMF_apply (π : PMF (T × T)) (σ : T) (h : margFstT π σ ≠ 0) (τ : T) :
    condPMF π σ h τ = π (σ, τ) / margFstT π σ := rfl

/-- **The conditional draw** `ℓ(σ, u)`: the atom of `π(·|σ)` drawn by `u`, with a
default where `σ` carries no mass. -/
noncomputable def condDraw (π : PMF (T × T)) (σ : T) (u : ℝ) : T :=
  if h : margFstT π σ ≠ 0 then drawBy (condPMF π σ h) u else π.support_nonempty.some.2

/-- **The conditional draw has the conditional law.** -/
lemma volume_condDraw_fibre (π : PMF (T × T)) {σ : T} (h : margFstT π σ ≠ 0) (τ : T) :
    volume {u ∈ Set.Ico (0 : ℝ) 1 | condDraw π σ u = τ} = π (σ, τ) / margFstT π σ := by
  simp only [condDraw, dite_eq_left h]
  exact volume_drawBy_fibre (condPMF π σ h) τ

/-- The conditional law against the mass of its condition is the coupling mass, the
identity `μ_k(σ) · π_k(τ|σ) = π_k(σ, τ)` at every `σ`. -/
lemma margFstT_mul_volume_condDraw_fibre (π : PMF (T × T)) (σ τ : T) :
    margFstT π σ * volume {u ∈ Set.Ico (0 : ℝ) 1 | condDraw π σ u = τ} = π (σ, τ) := by
  by_cases h : margFstT π σ = 0
  · rw [h, zero_mul]
    have hle : π (σ, τ) ≤ 0 := h ▸ le_margFstT π σ τ
    exact (le_antisymm hle bot_le).symm
  · rw [volume_condDraw_fibre π h τ, ENNReal.mul_div_cancel h (margFstT_ne_top π σ)]

lemma measurableSet_condDraw_fibre (π : PMF (T × T)) (σ τ : T) :
    MeasurableSet {u : ℝ | condDraw π σ u = τ} := by
  by_cases h : margFstT π σ ≠ 0
  · simp only [condDraw, dite_eq_left h]
    exact measurableSet_drawBy_fibre _ τ
  · simp only [condDraw, dite_eq_right h]
    exact MeasurableSet.const _

/-! ### A sum over patterns of a product -/

lemma tsum_pi_prod_fin {T : Type*} : ∀ (n : ℕ) (h : Fin n → T → ℝ≥0∞),
    ∑' g : Fin n → T, ∏ i, h i (g i) = ∏ i, ∑' t, h i t
  | 0, h => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact tsum_eq_single (fun i ↦ Fin.elim0 i) fun g hg ↦
        absurd (Subsingleton.elim g _) hg
  | n + 1, h => by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ T).tsum_eq, ENNReal.tsum_prod']
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right, tsum_pi_prod_fin n fun i t ↦ h i.succ t]

/-- **A sum over patterns of a product is the product of the sums**: over the patterns
`g : ι → T` on a finite index type, `∑_g ∏_i h_i(g_i) = ∏_i ∑_t h_i(t)`. -/
theorem tsum_pi_prod {ι T : Type*} [Fintype ι] (h : ι → T → ℝ≥0∞) :
    ∑' g : ι → T, ∏ i, h i (g i) = ∏ i, ∑' t, h i t := by
  set e := Fintype.equivFin ι
  rw [← (Equiv.arrowCongr e (Equiv.refl T)).symm.tsum_eq]
  have h1 : ∀ g' : Fin (Fintype.card ι) → T,
      ∏ i, h i ((Equiv.arrowCongr e (Equiv.refl T)).symm g' i)
        = ∏ j, h (e.symm j) (g' j) := fun g' ↦
    Fintype.prod_equiv e _ _ fun i ↦ by simp
  rw [tsum_congr h1, tsum_pi_prod_fin (Fintype.card ι) fun j t ↦ h (e.symm j) t]
  exact Fintype.prod_equiv e.symm _ _ fun j ↦ rfl

/-! ### The product formula against the uniform field -/

/-- **The product formula against the uniform field**: on a probability space carrying
a datum field with countably many values, against the uniform field, a probe of the
labels `lab u (X u) (U u)` over a finite set of indices decomposes into rectangles, one
per pattern of the data, each carrying the mass of the pattern against the uniform
masses of the label fibres. -/
theorem prod_uniformField_pattern {Ω ι T V : Type*} [MeasurableSpace Ω] [Countable T]
    (P : Measure Ω) (X : Ω → ι → T) (hX : ∀ u t, MeasurableSet {c : Ω | X c u = t})
    (lab : ι → T → ℝ → V) (hlab : ∀ u t v, MeasurableSet {r : ℝ | lab u t r = v})
    (F : Finset ι) (a : ι → V) :
    (P.prod (uniformField ι))
        (⋂ u ∈ F, {ω : Ω × (ι → ℝ) | lab u (X ω.1 u) (ω.2 u) = a u})
      = ∑' f : ↥F → T, P (⋂ u : ↥F, {c : Ω | X c u = f u})
          * ∏ u : ↥F, volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = a u} := by
  set CPart : (↥F → T) → Set Ω := fun f ↦ ⋂ u : ↥F, {c : Ω | X c u = f u} with hCPart
  set UPart : (↥F → T) → Set (ι → ℝ) :=
    fun f ↦ ⋂ u : ↥F, {U : ι → ℝ | lab u (f u) (U u) = a u} with hUPart
  have hcover : (⋂ u ∈ F, {ω : Ω × (ι → ℝ) | lab u (X ω.1 u) (ω.2 u) = a u})
      = ⋃ f : ↥F → T, CPart f ×ˢ UPart f := by
    ext ⟨c, U⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, hCPart,
      hUPart]
    constructor
    · intro h
      exact ⟨fun u ↦ X c u, fun u ↦ rfl, fun u ↦ h u u.2⟩
    · rintro ⟨f, hc, hU⟩ u hu
      have := hU ⟨u, hu⟩
      rw [← hc ⟨u, hu⟩] at this
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun f : ↥F → T ↦ CPart f ×ˢ UPart f) := by
    intro f f' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne ?_
    funext u
    have h1 := hω.1
    have h2 := hω'.1
    simp only [hCPart, Set.mem_iInter, Set.mem_ofPred_eq] at h1 h2
    rw [← h1 u, ← h2 u]
  have hmeas : ∀ f : ↥F → T, MeasurableSet (CPart f ×ˢ UPart f) := fun f ↦
    (MeasurableSet.iInter fun u : ↥F ↦ hX u (f u)).prod
      (MeasurableSet.iInter fun u : ↥F ↦
        BranchingProcess.measurable_coord (α := ℝ) (u : ι) (hlab u (f u) (a u)))
  rw [hcover, measure_iUnion hdisj hmeas]
  refine tsum_congr fun f ↦ ?_
  rw [Measure.prod_prod]
  congr 1
  set A : ι → Set ℝ := fun u ↦ {r : ℝ | ∀ hu : u ∈ F, lab u (f ⟨u, hu⟩) r = a u} with hA
  have hAeq : ∀ u (hu : u ∈ F), A u = {r : ℝ | lab u (f ⟨u, hu⟩) r = a u} := by
    intro u hu
    ext r
    simp only [hA, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ h hu, fun h _ ↦ h⟩
  have hAmeas : ∀ u ∈ F, MeasurableSet (A u) := fun u hu ↦ by
    rw [hAeq u hu]
    exact hlab u _ (a u)
  have hU : UPart f = ⋂ u ∈ F, {U : ι → ℝ | U u ∈ A u} := by
    ext U
    simp only [hUPart, hA, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h u hu hu' ↦ h ⟨u, hu'⟩, fun h u ↦ h u u.2 u.2⟩
  rw [hU, uniformField_pattern F A hAmeas, ← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  congr 1
  ext r
  simp only [hAeq u u.2, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact and_comm

end ChainClasses
