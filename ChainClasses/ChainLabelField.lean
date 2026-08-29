/-
`thm:chain-product-form` of `matching_classes_general.tex` and
`thm:chain-cross`\labelcref{it:chain-cross-product} of `trichotomy.tex`: the labelled
presented skeleton in the chain regime, over the constructed space.

In the chain regime `θ₀ = 0 < θ₁ < 1` no vertex carries a bush, the transform of
`thm:harris-general` is the identity, and the shape at a vertex of the reduced skeleton
is its neck alone.  The label of a vertex is the level class `ℓ_D(m(w))` of its neck
length, and across two laws the class map `ℓ'(λ', U)` of `thm:chain-coupling` replaces
`ℓ_D`, the uniform variable `U(w)` drawn from the uniform field of `UniformField`.  The
presented neck `bNeckAtC` of `BlobField` counts the neck steps before the split, the
paper's `m(w) - 1`, so both labels read the presented neck shifted by one; the factor
`θ₁^r` of `blob_iid` is then the mass of a neck of length `r + 1` with the split
probability `1 - θ₁` absorbed into the rule mass, and the presented arity law `ν̂` is
the coin-averaged rule mass renormalised by that split probability.  Summing `blob_iid`
over the necks of one class gives `thm:chain-product-form` uniformly in the rule, and
the product formula of `UniformField` against the one-vertex computation of
`thm:chain-coupling` gives the coupled labelling of the second law.

* `extinction_eq_zero_of_chain`, `extinction_lt_one_of_chain`,
  `skeletonWeight_eq_of_chain`, `skeletonWeight_one_eq_of_chain`: in the chain regime
  the extinction probability vanishes and the skeleton weights are the offspring
  masses.
* `qF_zero_ge_half`: the distinguished class carries at least half the mass once `D`
  is large, the second clause of `thm:chain-product-form`.
* `bRuleMass_eq_zero_of_lt_two`: no rule presents an arity below two.
* `measurableSet_coinPrefix_fibre`, `measurableSet_bNeckAtC_fibre`,
  `measurableSet_bArityAtC_fibre`: the presented fields are measurable on the sample
  against the coin field.
* `bArityLaw`, `bArityLaw_stopRule`, `bRuleMass_sum_tsum`, `bArityLaw_tsum`: **the
  presented arity law** `ν̂`, the reduced law `ν̃` at the identity presentation, the
  total rule mass as the split probability, and `ν̂` a probability law for every rule.
* `chainLab`, `measurableSet_chainLab_fibre`, `measurable_chainLab`: **the level
  label** `x(w) = ℓ_D(m(w))` and its measurability.
* `level_succ_eq_iff`, `chain_class_sum`, `chain_class_tsum`: the level class and its
  geometric mass read on the presented neck, `eq:qk` shifted by one.
* `blobMeasure_chainLab_pattern`, `blobMeasure_chainLab_marginal`,
  `chain_product_form`: **`thm:chain-product-form`**, the pairs of a level label and
  a presented arity i.i.d. with `μ_D ⊗ ν̂` for every rule, the marginal `μ_D` at the
  root, and the plain reduced skeleton with `ν̂ = ν̃`.
* `coupledBlobMeasure`, `crossLab`, `measurableSet_crossLab_fibre`,
  `measurable_crossLab`: **the labelled space of the second law and the coupled
  label** `ℓ'(m(w), U(w))`, with its measurability.
* `cross_class_sum`, `cross_class_tsum`: the one-vertex computation of
  `thm:chain-coupling` against the geometric neck mass.
* `crossLab_pattern`, `crossLab_marginal`:
  **`thm:chain-cross`\labelcref{it:chain-cross-product}**, the coupled labels of the
  second law against its presented arities are i.i.d. with `μ_* ⊗ ν̂'`, the class law
  `μ_* = μ_D` of the first law, and the marginal `μ_*` at the root.
-/
import ChainClasses.BlobLaw
import ChainClasses.UniformField
import ChainClasses.Coupling
import ChainClasses.CrossLaw
import ChainClasses.Quantise
import ChainClasses.ChainRegime

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (Offspring survivalMeasure)

variable {J N : ℕ} {σ : Type*}

/-! ### The chain regime: skeleton weights are offspring masses -/

/-- In the chain regime `θ₀ = 0` the extinction probability vanishes. -/
lemma extinction_eq_zero_of_chain (θ : Offspring J) (hθ0 : θ 0 = 0) : θ.extinction = 0 :=
  θ.extinction_eq_zero_iff.mpr hθ0

lemma extinction_lt_one_of_chain (θ : Offspring J) (hθ0 : θ 0 = 0) : θ.extinction < 1 := by
  rw [extinction_eq_zero_of_chain θ hθ0]
  exact zero_lt_one

/-- In the chain regime the transform of `thm:harris-general` is the identity:
`θ̃_k = θ_k`. -/
lemma skeletonWeight_eq_of_chain (θ : Offspring J) (hθ0 : θ 0 = 0) (k : ℕ) :
    θ.skeletonWeight k = θ k :=
  skeletonWeight_of_extinction_zero θ (extinction_eq_zero_of_chain θ hθ0) hθ0 k

/-- `θ̃₁ = θ₁` in the chain regime. -/
lemma skeletonWeight_one_eq_of_chain (θ : Offspring J) (hθ0 : θ 0 = 0) :
    θ.skeletonWeight 1 = θ 1 :=
  skeletonWeight_eq_of_chain θ hθ0 1

/-! ### The distinguished class carries half the mass -/

/-- The second clause of **`thm:chain-product-form`**: `μ_D(0) = 1 - θ₁^{D-1} ≥ 1/2` once
`D` is large. -/
lemma qF_zero_ge_half {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → 1 / 2 ≤ qF a D 0 := by
  have htend := tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
  have hev : ∀ᶠ n : ℕ in Filter.atTop, a ^ n ≤ 1 / 2 :=
    htend.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨n₀ + 1, fun D hD ↦ ?_⟩
  rw [qF_zero]
  have := hn₀ (D - 1) (by omega)
  linarith

/-! ### The rule mass below arity two -/

/-- Below arity two there is no atom, so the rule mass vanishes. -/
lemma bRuleMass_eq_zero_of_lt_two (θ : Offspring J) (R : ℕ) (ρr : BRule σ) (s : σ)
    {j : ℕ} (hj : j < 2) : bRuleMass θ R ρr s j = 0 := by
  have hempty : IsEmpty {ts : List BTrace // BAtom ρr s j ts} := by
    refine ⟨fun ts ↦ ?_⟩
    obtain ⟨-, -, hlen, hsum⟩ := ts.property
    omega
  rw [bRuleMass, tsum_empty]

/-! ### Measurability on the sample against the coin field -/

variable [MeasurableSpace σ] [MeasurableSingletonClass σ]

/-- A field read off the sample and the coins at the prefixes of one address is
measurable on the sample against the coin field: the event decomposes into finitely
many rectangles, one per pattern of the coins along the address. -/
lemma measurableSet_coinPrefix_fibre [Countable σ] {X : Type*} (u : List ℕ)
    (f : (GWord N → ℕ) → (List ℕ → σ) → X)
    (hcongr : ∀ (c : GWord N → ℕ) (b b' : List ℕ → σ),
      (∀ p : List ℕ, p <+: u → b p = b' p) → f c b = f c b')
    (hmeas : ∀ (b : List ℕ → σ) (x : X), MeasurableSet {c : GWord N → ℕ | f c b = x})
    (x : X) :
    MeasurableSet {ω : (GWord N → ℕ) × (List ℕ → σ) | f ω.1 ω.2 = x} := by
  set ext : (Fin (u.length + 1) → σ) → List ℕ → σ :=
    fun ε p ↦ ε ⟨min p.length u.length, Nat.lt_succ_of_le (min_le_right _ _)⟩ with hext
  have hext_prefix : ∀ (ε : Fin (u.length + 1) → σ) (b : List ℕ → σ),
      (∀ i : Fin (u.length + 1), b (u.take i) = ε i) →
      ∀ p : List ℕ, p <+: u → b p = ext ε p := by
    intro ε b hb p hp
    have hlen : min p.length u.length = p.length := min_eq_left hp.length_le
    have hfin : (⟨min p.length u.length, Nat.lt_succ_of_le (min_le_right _ _)⟩ :
        Fin (u.length + 1)) = ⟨p.length, Nat.lt_succ_of_le hp.length_le⟩ := Fin.ext hlen
    simp only [hext]
    rw [hfin, ← hb ⟨p.length, Nat.lt_succ_of_le hp.length_le⟩]
    congr 1
    exact List.prefix_iff_eq_take.mp hp
  have hset : {ω : (GWord N → ℕ) × (List ℕ → σ) | f ω.1 ω.2 = x}
      = ⋃ ε : Fin (u.length + 1) → σ,
          {c : GWord N → ℕ | f c (ext ε) = x}
            ×ˢ (⋂ i : Fin (u.length + 1), {b : List ℕ → σ | b (u.take i) = ε i}) := by
    ext ⟨c, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_iInter]
    constructor
    · intro h
      refine ⟨fun i ↦ b (u.take i), ?_, fun i ↦ rfl⟩
      rw [← hcongr c b (ext fun i ↦ b (u.take i)) (hext_prefix _ b fun i ↦ rfl)]
      exact h
    · rintro ⟨ε, h1, h2⟩
      rw [hcongr c b (ext ε) (hext_prefix ε b h2)]
      exact h1
  rw [hset]
  refine MeasurableSet.iUnion fun ε ↦ (hmeas (ext ε) x).prod
    (MeasurableSet.iInter fun i ↦ ?_)
  exact BranchingProcess.measurable_coord (u.take i) (measurableSet_singleton (ε i))

/-- The presented neck at an address is measurable on the sample against the coin
field. -/
lemma measurableSet_bNeckAtC_fibre [Countable σ] (R : ℕ) (ρr : BRule σ) (u : List ℕ)
    (r : ℕ) :
    MeasurableSet {ω : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr ω u = r} :=
  measurableSet_coinPrefix_fibre u (fun c b ↦ bNeckAtC R ρr (c, b) u)
    (fun c b b' h ↦ bNeckAtC_congr R ρr u c b b' h)
    (fun b r ↦ measurableSet_bNeckAtC_eq R ρr b u r) r

/-- The presented arity at an address is measurable on the sample against the coin
field. -/
lemma measurableSet_bArityAtC_fibre [Countable σ] (R : ℕ) (ρr : BRule σ) (u : List ℕ)
    (j : ℕ) :
    MeasurableSet {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr ω u = j} :=
  measurableSet_coinPrefix_fibre u (fun c b ↦ bArityAtC R ρr (c, b) u)
    (fun c b b' h ↦ bArityAtC_congr R ρr u c b b' h)
    (fun b j ↦ measurableSet_bArityAtC_eq R ρr b u j) j

/-! ### The presented arity law -/

/-- **The presented arity law** `ν̂` of a rule: the coin-averaged rule mass, renormalised
by the split probability `1 - θ̃₁` that `bRuleMass` carries. -/
noncomputable def bArityLaw (θ : Offspring J) (ρ : Measure σ) [Fintype σ] (R : ℕ)
    (ρr : BRule σ) (j : ℕ) : ℝ≥0∞ :=
  (∑ s : σ, ρ {s} * bRuleMass θ R ρr s j) / ENNReal.ofReal (1 - θ.skeletonWeight 1)

/-- **The identity presentation carries the reduced law**: `ν̂ = ν̃` at the rule that
always stops. -/
lemma bArityLaw_stopRule (θ : Offspring J) (hs1 : θ.skeletonWeight 1 < 1) [Fintype σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ] (R : ℕ) (j : ℕ) :
    bArityLaw θ ρ R (stopRule σ) j = ENNReal.ofReal (redNu θ j) := by
  have hsum : ∑ s : σ, ρ {s} = 1 := by
    rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
  have hpos : 0 < 1 - θ.skeletonWeight 1 := by linarith
  rcases lt_or_ge j 2 with hj | hj
  · have hz : ∀ s : σ, bRuleMass θ R (stopRule σ) s j = 0 :=
      fun s ↦ bRuleMass_eq_zero_of_lt_two θ R _ s hj
    have hr : redNu θ j = 0 := by
      interval_cases j
      · exact redNu_zero θ
      · exact redNu_one θ
    simp [bArityLaw, hz, hr]
  · rw [bArityLaw, Finset.sum_congr rfl fun s _ ↦ by rw [bRuleMass_stopRule θ R s hj],
      ← Finset.sum_mul, hsum, one_mul, redNu, if_neg (by omega), reducedWeight_def,
      ENNReal.ofReal_div_of_pos hpos]

/-- **The presented pairs at the root exhaust the space**: summing `blob_iid` over the
neck and the arity at the root gives one, which identifies the total rule mass with
the split probability. -/
lemma bRuleMass_sum_tsum (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) [Fintype σ] [Inhabited σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] (R : ℕ) (ρr : BRule σ) :
    ∑' j : ℕ, ∑ s : σ, ρ {s} * bRuleMass θ R ρr s j
      = ENNReal.ofReal (1 - θ.skeletonWeight 1) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have hprob : IsProbabilityMeasure (blobMeasure (N := N) θ ρ) :=
    inferInstanceAs (IsProbabilityMeasure
      ((survivalMeasure (N := N) θ).prod (BranchingProcess.fieldMeasure ρ)))
  set E : ℕ × ℕ → Set ((GWord N → ℕ) × (List ℕ → σ)) := fun p ↦
    {ω : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr ω [] = p.1}
      ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr ω [] = p.2} with hE
  have hcover : (⋃ p, E p) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, hE, Set.mem_inter_iff,
      Set.mem_setOf_eq, Prod.exists]
    exact ⟨_, _, rfl, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro p p' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne ?_
    simp only [hE, Set.mem_inter_iff, Set.mem_setOf_eq] at hω hω'
    exact Prod.ext (hω.1.symm.trans hω'.1) (hω.2.symm.trans hω'.2)
  have hmeas : ∀ p, MeasurableSet (E p) := fun p ↦
    (measurableSet_bNeckAtC_fibre R ρr [] p.1).inter
      (measurableSet_bArityAtC_fibre R ρr [] p.2)
  have hterm : ∀ p : ℕ × ℕ, blobMeasure (N := N) θ ρ (E p)
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ p.1
          * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s p.2 := by
    intro p
    have h := blob_iid (N := N) θ hJN hq hs1 ρ R ρr {[]} (by simp) (fun _ ↦ p.1)
      (fun _ ↦ p.2) (by simp)
    simp only [Finset.set_biInter_singleton, Finset.prod_singleton] at h
    exact h
  have htotal : ∑' p : ℕ × ℕ, blobMeasure (N := N) θ ρ (E p) = 1 := by
    rw [← measure_iUnion hdisj hmeas, hcover, measure_univ]
  rw [tsum_congr hterm, ENNReal.tsum_prod'] at htotal
  dsimp only at htotal
  simp_rw [ENNReal.tsum_mul_left] at htotal
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric] at htotal
  have hlt : ENNReal.ofReal (θ.skeletonWeight 1) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (BranchingProcess.Offspring.skeletonWeight_nonneg θ hq 1) |>.mpr hs1
  have hne0 : (1 : ℝ≥0∞) - ENNReal.ofReal (θ.skeletonWeight 1) ≠ 0 :=
    (tsub_pos_of_lt hlt).ne'
  have hnetop : (1 : ℝ≥0∞) - ENNReal.ofReal (θ.skeletonWeight 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hsub : ENNReal.ofReal (1 - θ.skeletonWeight 1)
      = 1 - ENNReal.ofReal (θ.skeletonWeight 1) := by
    rw [ENNReal.ofReal_sub _ (BranchingProcess.Offspring.skeletonWeight_nonneg θ hq 1),
      ENNReal.ofReal_one]
  rw [hsub]
  calc ∑' j : ℕ, ∑ s : σ, ρ {s} * bRuleMass θ R ρr s j
      = (1 - ENNReal.ofReal (θ.skeletonWeight 1))
          * ((1 - ENNReal.ofReal (θ.skeletonWeight 1))⁻¹
            * ∑' j : ℕ, ∑ s : σ, ρ {s} * bRuleMass θ R ρr s j) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
    _ = 1 - ENNReal.ofReal (θ.skeletonWeight 1) := by rw [htotal, mul_one]

/-- **The presented arity law is a law.** -/
lemma bArityLaw_tsum (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) [Fintype σ] [Inhabited σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] (R : ℕ) (ρr : BRule σ) :
    ∑' j : ℕ, bArityLaw θ ρ R ρr j = 1 := by
  have hpos : 0 < 1 - θ.skeletonWeight 1 := by linarith
  simp only [bArityLaw, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, bRuleMass_sum_tsum (N := N) θ hJN hq hs1 ρ R ρr]
  exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top

/-! ### The level label -/

/-- **The level label** `x(w) = ℓ_D(m(w))` of `thm:chain-product-form`: the level class
of the neck length, the presented neck `bNeckAtC` being `m(w) - 1`. -/
noncomputable def chainLab (D R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ))
    (u : List ℕ) : ℕ :=
  levelMap D (bNeckAtC R ρr ω u + 1)

/-- The level label is measurable on the sample against the coin field. -/
lemma measurableSet_chainLab_fibre [Countable σ] (D R : ℕ) (ρr : BRule σ) (u : List ℕ)
    (a : ℕ) :
    MeasurableSet {ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω u = a} := by
  have hset : {ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω u = a}
      = ⋃ r : {r : ℕ // levelMap D (r + 1) = a},
          {ω : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr ω u = r} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, chainLab, Subtype.exists, exists_prop]
    exact ⟨fun h ↦ ⟨_, h, rfl⟩, by rintro ⟨r, hr, h⟩; rw [h]; exact hr⟩
  rw [hset]
  exact MeasurableSet.iUnion fun r ↦ measurableSet_bNeckAtC_fibre R ρr u r

lemma measurable_chainLab [Countable σ] (D R : ℕ) (ρr : BRule σ) (u : List ℕ) :
    Measurable fun ω : (GWord N → ℕ) × (List ℕ → σ) ↦ chainLab D R ρr ω u :=
  measurable_to_countable' fun a ↦ measurableSet_chainLab_fibre D R ρr u a

/-! ### The geometric mass of a level class on the presented neck -/

/-- The level class read on the presented neck: `ℓ_D(n + 1) = k` iff
`D^k - 1 ≤ n < D^{k+1} - 1`. -/
lemma level_succ_eq_iff {D n k : ℕ} (hD : 2 ≤ D) :
    levelMap D (n + 1) = k ↔ n ∈ Finset.Ico (D ^ k - 1) (D ^ (k + 1) - 1) := by
  rw [level_eq_iff hD (by omega), Finset.mem_Ico]
  have h1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ D ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  omega

/-- `eq:qk` on the presented neck: the geometric weights `a^n` over the necks
`n = m - 1` of class `k` sum to `q_k/(1-a)`, the split probability `1 - a` left to the
rule mass. -/
lemma chain_class_sum {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    ∑ n ∈ Finset.Ico (D ^ k - 1) (D ^ (k + 1) - 1), a ^ n = qF a D k / (1 - a) := by
  have hpos : 0 < 1 - a := by linarith
  rw [eq_div_iff hpos.ne', Finset.sum_mul, ← class_sum ha hD k]
  have h1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : D ^ k ≤ D ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show D ^ (k + 1) - 1 - (D ^ k - 1) = D ^ (k + 1) - D ^ k by omega]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show D ^ k - 1 + i = D ^ k + i - 1 by omega]

/-- The class mass in `ℝ≥0∞`, as the sum over all presented necks selected by the
level label. -/
lemma chain_class_tsum {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    ∑' n : ℕ, (if levelMap D (n + 1) = k then ENNReal.ofReal a ^ n else 0)
      = ENNReal.ofReal (qF a D k) / ENNReal.ofReal (1 - a) := by
  have hpos : 0 < 1 - a := by linarith
  rw [tsum_eq_sum (s := Finset.Ico (D ^ k - 1) (D ^ (k + 1) - 1))
      (fun n hn ↦ by rw [if_neg fun h ↦ hn ((level_succ_eq_iff hD).mp h)]),
    Finset.sum_congr rfl (fun n hn ↦ by
      rw [if_pos ((level_succ_eq_iff hD).mpr hn), ← ENNReal.ofReal_pow ha]),
    ← ENNReal.ofReal_sum_of_nonneg (fun n _ ↦ pow_nonneg ha n), chain_class_sum ha ha1 hD k,
    ENNReal.ofReal_div_of_pos hpos]

/-! ### `thm:chain-product-form` -/

/-- **`thm:chain-product-form`, for every rule**: over the sample against the coin
field, the pairs of a level label and a presented arity over a prefix-closed probe of
the presented skeleton are independent with the product law `μ_D ⊗ ν̂`, the class law
`eq:chain-class-law` at ratio `θ₁` against the presented arity law. -/
theorem blobMeasure_chainLab_pattern (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) [Fintype σ] [Inhabited σ] (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (R : ℕ) (ρr : BRule σ) {D : ℕ} (hD : 2 ≤ D) (F : Finset (List ℕ))
    (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F) (a j : List ℕ → ℕ)
    (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    blobMeasure (N := N) θ ρ
        (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω u = a u}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr ω u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (qF (θ 1) D (a u)) * bArityLaw θ ρ R ρr (j u) := by
  classical
  have hq := extinction_lt_one_of_chain θ hθ0
  have hs1 : θ.skeletonWeight 1 < 1 := by
    rw [skeletonWeight_one_eq_of_chain θ hθ0]
    exact hθ1
  have ha0 : 0 ≤ θ 1 := θ.nonneg 1
  set rext : (↥F → ℕ) → List ℕ → ℕ :=
    fun g u ↦ if h : u ∈ F then g ⟨u, h⟩ else 0 with hrext
  have hrext_apply : ∀ (g : ↥F → ℕ) (u : ↥F), rext g u = g u := by
    intro g u
    simp only [hrext, dif_pos u.2]
  set S : Set (↥F → ℕ) := {g | ∀ u : ↥F, levelMap D (g u + 1) = a u} with hS
  set E : (↥F → ℕ) → Set ((GWord N → ℕ) × (List ℕ → σ)) := fun g ↦
    ⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr ω u = rext g u}
      ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr ω u = j u}) with hE
  have hcover : (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω u = a u}
        ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr ω u = j u}))
      = ⋃ g : ↥S, E g := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, chainLab,
      hE, hS, Subtype.exists, exists_prop]
    constructor
    · intro h
      refine ⟨fun u ↦ bNeckAtC R ρr ω u, fun u ↦ (h u u.2).1, fun u hu ↦ ⟨?_, (h u hu).2⟩⟩
      simp only [hrext, dif_pos hu]
    · rintro ⟨g, hgS, hg⟩ u hu
      obtain ⟨h1, h2⟩ := hg u hu
      refine ⟨?_, h2⟩
      rw [h1]
      simp only [hrext, dif_pos hu]
      exact hgS ⟨u, hu⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun g : ↥S ↦ E g) := by
    intro g g' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne (Subtype.ext (funext fun u ↦ ?_))
    simp only [hE, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hω hω'
    have e1 := (hω u u.2).1
    have e2 := (hω' u u.2).1
    rw [hrext_apply] at e1 e2
    rw [← e1, ← e2]
  have hmeas : ∀ g : ↥S, MeasurableSet (E g) := fun g ↦
    MeasurableSet.biInter F.countable_toSet fun u _ ↦
      (measurableSet_bNeckAtC_fibre R ρr u _).inter (measurableSet_bArityAtC_fibre R ρr u _)
  rw [hcover, measure_iUnion hdisj hmeas,
    tsum_congr fun g : ↥S ↦ blob_iid (N := N) θ hJN hq hs1 ρ R ρr F hpc (rext g) j hcomp]
  -- each pattern as a product over the probe, the class selected by the label
  have h1 : ∀ g : ↥F → ℕ, (∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (rext g u)
        * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u))
      = ∏ u : ↥F, ENNReal.ofReal (θ 1) ^ (g u)
          * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u) := by
    intro g
    rw [← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun u _ ↦ by
      rw [hrext_apply g u, skeletonWeight_one_eq_of_chain θ hθ0]
  have h2 : ∀ g : ↥S, (∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (rext g u)
        * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u))
      = ∏ u : ↥F, (if levelMap D ((g : ↥F → ℕ) u + 1) = a u
          then ENNReal.ofReal (θ 1) ^ ((g : ↥F → ℕ) u) else 0)
          * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u) := by
    intro g
    rw [h1]
    exact Finset.prod_congr rfl fun u _ ↦ by rw [if_pos (g.2 u)]
  rw [tsum_congr h2]
  rw [tsum_subtype_eq_of_support_subset (s := S) (f := fun g : ↥F → ℕ ↦
    ∏ u : ↥F, (if levelMap D (g u + 1) = a u then ENNReal.ofReal (θ 1) ^ (g u) else 0)
      * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u)) ?_]
  · rw [tsum_pi_prod fun (u : ↥F) (n : ℕ) ↦
        (if levelMap D (n + 1) = a u then ENNReal.ofReal (θ 1) ^ n else 0)
          * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u), ← Finset.prod_coe_sort F]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    rw [ENNReal.tsum_mul_right, chain_class_tsum ha0 hθ1 hD (a u), bArityLaw,
      skeletonWeight_one_eq_of_chain θ hθ0, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm,
      mul_assoc]
  · intro g hg
    by_contra hgS
    apply hg
    simp only [hS, Set.mem_setOf_eq, not_forall] at hgS
    obtain ⟨u, hu⟩ := hgS
    exact Finset.prod_eq_zero (Finset.mem_univ u) (by rw [if_neg hu, zero_mul])

/-- **The marginal of the level label at the root is `μ_D`**: the presented arity
summed out of `thm:chain-product-form`. -/
theorem blobMeasure_chainLab_marginal (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) [Fintype σ] [Inhabited σ] (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (R : ℕ) (ρr : BRule σ) {D : ℕ} (hD : 2 ≤ D) (a : ℕ) :
    blobMeasure (N := N) θ ρ {ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω [] = a}
      = ENNReal.ofReal (qF (θ 1) D a) := by
  have hq := extinction_lt_one_of_chain θ hθ0
  have hs1 : θ.skeletonWeight 1 < 1 := by
    rw [skeletonWeight_one_eq_of_chain θ hθ0]
    exact hθ1
  set A : ℕ → Set ((GWord N → ℕ) × (List ℕ → σ)) := fun κ ↦
    {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr ω [] = κ} with hA
  have hAmeas : ∀ κ, MeasurableSet (A κ) := fun κ ↦ measurableSet_bArityAtC_fibre R ρr [] κ
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    intro κ κ' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne ?_
    simp only [hA, Set.mem_setOf_eq] at hω hω'
    rw [← hω, ← hω']
  have hAcover : (⋃ κ, A κ) = Set.univ := by
    ext ω
    simp [hA]
  have hcover : {ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω [] = a}
      = ⋃ κ, ({ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω [] = a} ∩ A κ) := by
    rw [← Set.inter_iUnion, hAcover, Set.inter_univ]
  have hdisj : Pairwise (Function.onFun Disjoint fun κ ↦
      {ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω [] = a} ∩ A κ) :=
    fun κ κ' hne ↦ (hAdisj hne).mono Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ κ, MeasurableSet
      ({ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω [] = a} ∩ A κ) := fun κ ↦
    (measurableSet_chainLab_fibre D R ρr [] a).inter (hAmeas κ)
  have hterm : ∀ κ, blobMeasure (N := N) θ ρ
      ({ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R ρr ω [] = a} ∩ A κ)
        = ENNReal.ofReal (qF (θ 1) D a) * bArityLaw θ ρ R ρr κ := by
    intro κ
    have h := blobMeasure_chainLab_pattern (N := N) θ hJN hθ0 hθ1 ρ R ρr hD {[]} (by simp)
      (fun _ ↦ a) (fun _ ↦ κ) (by simp)
    simp only [Finset.set_biInter_singleton, Finset.prod_singleton] at h
    exact h
  rw [hcover, measure_iUnion hdisj hmeas, tsum_congr hterm, ENNReal.tsum_mul_left,
    bArityLaw_tsum (N := N) θ hJN hq hs1 ρ R ρr, mul_one]

/-- **`thm:chain-product-form`**: on the plain reduced skeleton, presented by the rule
that always stops, the pairs `(ℓ_D(m(w)), k(w))` over a prefix-closed probe are
independent with the product law `μ_D ⊗ ν̃`, the class law `eq:chain-class-law` at
ratio `θ₁` against the reduced law `ν̃_j = θ_j/(1-θ₁)` of `eq:chain-joint`. -/
theorem chain_product_form (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) [Fintype σ] [Inhabited σ] (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (R : ℕ) {D : ℕ} (hD : 2 ≤ D) (F : Finset (List ℕ))
    (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F) (a j : List ℕ → ℕ)
    (hj2 : ∀ u ∈ F, 2 ≤ j u) (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    blobMeasure (N := N) θ ρ
        (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → σ) | chainLab D R (stopRule σ) ω u = a u}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R (stopRule σ) ω u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (qF (θ 1) D (a u) * (θ (j u) / (1 - θ 1))) := by
  have hs1 : θ.skeletonWeight 1 < 1 := by
    rw [skeletonWeight_one_eq_of_chain θ hθ0]
    exact hθ1
  rw [blobMeasure_chainLab_pattern (N := N) θ hJN hθ0 hθ1 ρ R (stopRule σ) hD F hpc a j hcomp]
  refine Finset.prod_congr rfl fun u hu ↦ ?_
  rw [bArityLaw_stopRule θ hs1 ρ R, redNu, if_neg (by have := hj2 u hu; omega),
    reducedWeight_def, skeletonWeight_eq_of_chain θ hθ0, skeletonWeight_one_eq_of_chain θ hθ0,
    ENNReal.ofReal_mul (qF_nonneg (θ.nonneg 1) hθ1.le hD _)]

/-! ### The coupled label of the second law -/

/-- **The labelled space of the second law**: the sample against the coin field,
against the uniform field over the presented addresses, one uniform variable `U(w)` at
every address for the class map of `thm:chain-coupling`. -/
noncomputable def coupledBlobMeasure (θ' : Offspring J) (ρ' : Measure σ)
    [IsProbabilityMeasure ρ'] :
    Measure (((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ)) :=
  (blobMeasure (N := N) θ' ρ').prod (uniformField (List ℕ))

/-- **The coupled label** `ℓ'(m(w), U(w))` of `thm:chain-cross`: the class map `ellQ` of
`thm:chain-coupling` at the ratios `a = θ₁` and `b = θ₁'`, read on the presented neck
of the second law shifted to the neck length, and on the uniform variable at the
address. -/
noncomputable def crossLab (a b : ℝ) (D R : ℕ) (ρr : BRule σ)
    (ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ)) (u : List ℕ) : ℕ :=
  ellQ a b D (bNeckAtC R ρr ω.1 u + 1) (ω.2 u)

/-- The coupled label is measurable on the labelled space of the second law. -/
lemma measurableSet_crossLab_fibre [Countable σ] (a b : ℝ) (D R : ℕ) (ρr : BRule σ)
    (u : List ℕ) (k : ℕ) :
    MeasurableSet {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
      crossLab a b D R ρr ω u = k} := by
  have hset : {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
        crossLab a b D R ρr ω u = k}
      = ⋃ m : ℕ, {ω₁ : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr ω₁ u = m}
          ×ˢ {U : List ℕ → ℝ | ellQ a b D (m + 1) (U u) = k} := by
    ext ⟨ω₁, U⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, crossLab]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨m, h1, h2⟩
      rw [h1]
      exact h2
  rw [hset]
  exact MeasurableSet.iUnion fun m ↦ (measurableSet_bNeckAtC_fibre R ρr u m).prod
    (BranchingProcess.measurable_coord (α := ℝ) u (ellQ_section_measurable a b D (m + 1) k))

lemma measurable_crossLab [Countable σ] (a b : ℝ) (D R : ℕ) (ρr : BRule σ) (u : List ℕ) :
    Measurable fun ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) ↦
      crossLab a b D R ρr ω u :=
  measurable_to_countable' fun k ↦ measurableSet_crossLab_fibre a b D R ρr u k

/-! ### The one-vertex computation of `thm:chain-coupling` on the presented neck -/

/-- The scalar computation of clause (ii) of `thm:chain-coupling` on the presented
neck: the geometric weights `b^n` over the necks `n = m - 1`, each weighted by the
`u`-measure of class `k` at the length `m`, sum to `q_k/(1-b)`. -/
lemma cross_class_sum {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) :
    ∑ n ∈ Finset.Ico (DQ a b D k - 1) (DQ a b D (k + 1)), b ^ n * uWeight a b D k (n + 1)
      = qF a D k / (1 - b) := by
  have hpos : 0 < 1 - b := by linarith
  have hm1 := one_le_DQ (cgamma_pos ha ha1 hb hb1) hD k
  rw [eq_div_iff hpos.ne', Finset.sum_mul, ← coupling_sum ha ha1 hb hb1 hD hgD k]
  have hshift := Finset.sum_Ico_add' (fun m ↦ uWeight a b D k m * gmass b m)
    (DQ a b D k - 1) (DQ a b D (k + 1)) 1
  rw [show DQ a b D k - 1 + 1 = DQ a b D k by omega] at hshift
  rw [← hshift]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [gmass_succ]
  ring

/-- The same computation in `ℝ≥0∞`, summed over all presented necks. -/
lemma cross_class_tsum {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (k : ℕ) :
    ∑' n : ℕ, ENNReal.ofReal b ^ n * ENNReal.ofReal (uWeight a b D k (n + 1))
      = ENNReal.ofReal (qF a D k) / ENNReal.ofReal (1 - b) := by
  have hpos : 0 < 1 - b := by linarith
  have hm1 := one_le_DQ (cgamma_pos ha ha1 hb hb1) hD k
  have hDQ := DQ_lt_succ ha ha1 hb hb1 hD hgD k
  have hvan : ∀ n ∉ Finset.Ico (DQ a b D k - 1) (DQ a b D (k + 1)),
      ENNReal.ofReal b ^ n * ENNReal.ofReal (uWeight a b D k (n + 1)) = 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have e1 : ¬n + 1 = DQ a b D k := by omega
    have e2 : ¬n + 1 = DQ a b D (k + 1) := by omega
    have e3 : ¬(DQ a b D k < n + 1 ∧ n + 1 < DQ a b D (k + 1)) := by omega
    have hz : uWeight a b D k (n + 1) = 0 := by
      unfold uWeight
      rw [if_neg e1, if_neg e2, if_neg e3]
    rw [hz, ENNReal.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hvan, Finset.sum_congr rfl (fun n _ ↦ by
      rw [← ENNReal.ofReal_pow hb.le, ← ENNReal.ofReal_mul (pow_nonneg hb.le n)]),
    ← ENNReal.ofReal_sum_of_nonneg (fun n _ ↦
      mul_nonneg (pow_nonneg hb.le n) (uWeight_nonneg ha ha1 hb hb1 hD k (n + 1))),
    cross_class_sum ha ha1 hb hb1 hD hgD k, ENNReal.ofReal_div_of_pos hpos]

/-! ### `thm:chain-cross`, the coupled labelling -/

/-- **`thm:chain-cross`\labelcref{it:chain-cross-product}, the coupled side**: over the
labelled space of the second law, the pairs of a coupled label and a presented arity
over a prefix-closed probe of the presented skeleton are independent with the product
law `μ_* ⊗ ν̂'`, where `μ_* = μ_D` is the class law of the first law at ratio `θ₁`
and `ν̂'` the presented arity law of the second.  The hypotheses on the ratios and on
`D` are those of `thm:chain-coupling`: `θ₁, θ₁' ∈ (0,1)` and `γ(D-1) ≥ 1`. -/
theorem crossLab_pattern (θ' : Offspring J) (hJN' : J ≤ N) (hθ0' : θ' 0 = 0)
    (hθ1' : 0 < θ' 1) (hθ1'' : θ' 1 < 1) [Fintype σ] [Inhabited σ] (ρ' : Measure σ)
    [IsProbabilityMeasure ρ'] (R : ℕ) (ρr' : BRule σ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a (θ' 1) * ((D : ℝ) - 1))
    (F : Finset (List ℕ)) (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F)
    (x j : List ℕ → ℕ) (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    coupledBlobMeasure (N := N) θ' ρ'
        (⋂ u ∈ F, ({ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
            crossLab a (θ' 1) D R ρr' ω u = x u}
          ∩ {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
            bArityAtC R ρr' ω.1 u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (qF a D (x u)) * bArityLaw θ' ρ' R ρr' (j u) := by
  classical
  have hq := extinction_lt_one_of_chain θ' hθ0'
  have hs1 : θ'.skeletonWeight 1 < 1 := by
    rw [skeletonWeight_one_eq_of_chain θ' hθ0']
    exact hθ1''
  -- the event as a probe of the labels `lab u (X u) (U u)`
  set X : (GWord N → ℕ) × (List ℕ → σ) → List ℕ → ℕ × ℕ :=
    fun ω u ↦ (bNeckAtC R ρr' ω u, bArityAtC R ρr' ω u) with hX
  set lab : List ℕ → ℕ × ℕ → ℝ → ℕ × ℕ :=
    fun _ p r ↦ (ellQ a (θ' 1) D (p.1 + 1) r, p.2) with hlab
  set v : List ℕ → ℕ × ℕ := fun u ↦ (x u, j u) with hv
  have hevent : (⋂ u ∈ F, ({ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
          crossLab a (θ' 1) D R ρr' ω u = x u}
        ∩ {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
          bArityAtC R ρr' ω.1 u = j u}))
      = ⋂ u ∈ F, {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
          lab u (X ω.1 u) (ω.2 u) = v u} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, hlab, hX, hv, crossLab,
      Prod.mk.injEq]
  have hXm : ∀ u (t : ℕ × ℕ),
      MeasurableSet {ω : (GWord N → ℕ) × (List ℕ → σ) | X ω u = t} := by
    intro u t
    have : {ω : (GWord N → ℕ) × (List ℕ → σ) | X ω u = t}
        = {ω : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr' ω u = t.1}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr' ω u = t.2} := by
      ext ω
      simp [hX, Prod.ext_iff]
    rw [this]
    exact (measurableSet_bNeckAtC_fibre R ρr' u t.1).inter
      (measurableSet_bArityAtC_fibre R ρr' u t.2)
  have hlabm : ∀ u (t w : ℕ × ℕ), MeasurableSet {r : ℝ | lab u t r = w} := by
    intro u t w
    by_cases h : t.2 = w.2
    · have : {r : ℝ | lab u t r = w} = {r : ℝ | ellQ a (θ' 1) D (t.1 + 1) r = w.1} := by
        ext r
        simp [hlab, Prod.ext_iff, h]
      rw [this]
      exact ellQ_section_measurable a (θ' 1) D (t.1 + 1) w.1
    · have : {r : ℝ | lab u t r = w} = ∅ := by
        ext r
        simp [hlab, Prod.ext_iff, h]
      rw [this]
      exact MeasurableSet.empty
  rw [hevent, coupledBlobMeasure,
    prod_uniformField_pattern (blobMeasure (N := N) θ' ρ') X hXm lab hlabm F v]
  -- only the patterns with the prescribed arities contribute
  set emb : (↥F → ℕ) → (↥F → ℕ × ℕ) := fun g u ↦ (g u, j u) with hemb
  have hemb_inj : Function.Injective emb := by
    intro g g' h
    funext u
    have := congrFun h u
    simp only [hemb, Prod.mk.injEq] at this
    exact this.1
  set G : (↥F → ℕ × ℕ) → ℝ≥0∞ := fun f ↦
    blobMeasure (N := N) θ' ρ' (⋂ u : ↥F, {ω : (GWord N → ℕ) × (List ℕ → σ) | X ω u = f u})
      * ∏ u : ↥F, volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = v u} with hG
  have hsupp : Function.support G ⊆ Set.range emb := by
    intro f hf
    refine ⟨fun u ↦ (f u).1, ?_⟩
    by_contra hne
    apply hf
    have hu : ∃ u : ↥F, (f u).2 ≠ j u := by
      by_contra hall
      push Not at hall
      apply hne
      funext u
      simp only [hemb]
      exact Prod.ext rfl (hall u).symm
    obtain ⟨u, hu⟩ := hu
    have hzero : volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = v u} = 0 := by
      have : {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = v u} = ∅ := by
        ext r
        simp [hlab, hv, Prod.ext_iff, hu]
      rw [this, measure_empty]
    simp only [hG]
    rw [Finset.prod_eq_zero (Finset.mem_univ u) hzero, mul_zero]
  rw [← hemb_inj.tsum_eq hsupp]
  -- each pattern: `blob_iid` against the `u`-measures of the class fibres
  set rext : (↥F → ℕ) → List ℕ → ℕ :=
    fun g u ↦ if h : u ∈ F then g ⟨u, h⟩ else 0 with hrext
  have hrext_apply : ∀ (g : ↥F → ℕ) (u : ↥F), rext g u = g u := by
    intro g u
    simp only [hrext, dif_pos u.2]
  have hterm : ∀ g : ↥F → ℕ, G (emb g)
      = ∏ u : ↥F, ENNReal.ofReal (θ' 1) ^ (g u)
          * (∑ s : σ, ρ' {s} * bRuleMass θ' R ρr' s (j u))
          * ENNReal.ofReal (uWeight a (θ' 1) D (x u) (g u + 1)) := by
    intro g
    have hXset : (⋂ u : ↥F, {ω : (GWord N → ℕ) × (List ℕ → σ) | X ω u = emb g u})
        = ⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr' ω u = rext g u}
            ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr' ω u = j u}) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, hX, hemb, Prod.mk.injEq]
      constructor
      · intro h u hu
        obtain ⟨h1, h2⟩ := h ⟨u, hu⟩
        exact ⟨by rw [h1, hrext_apply g ⟨u, hu⟩], h2⟩
      · intro h u
        obtain ⟨h1, h2⟩ := h u u.2
        exact ⟨by rw [h1, hrext_apply g u], h2⟩
    have hvol : ∀ u : ↥F, volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (emb g u) r = v u}
        = ENNReal.ofReal (uWeight a (θ' 1) D (x u) (g u + 1)) := by
      intro u
      rw [← ellQ_section_volume ha ha1 hθ1' hθ1'' hD hgD (x u) (Nat.succ_pos (g u)),
        Measure.restrict_apply (ellQ_section_measurable a (θ' 1) D (g u + 1) (x u))]
      congr 1
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hlab, hemb, hv, Prod.mk.injEq, and_true]
      exact and_comm
    simp only [hG]
    rw [hXset, blob_iid (N := N) θ' hJN' hq hs1 ρ' R ρr' F hpc (rext g) j hcomp,
      Finset.prod_congr rfl fun u _ ↦ hvol u, ← Finset.prod_coe_sort F,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    rw [hrext_apply g u, skeletonWeight_one_eq_of_chain θ' hθ0']
  -- sum the patterns: one class mass per vertex
  rw [tsum_congr hterm, tsum_pi_prod fun (u : ↥F) (n : ℕ) ↦
      ENNReal.ofReal (θ' 1) ^ n * (∑ s : σ, ρ' {s} * bRuleMass θ' R ρr' s (j u))
        * ENNReal.ofReal (uWeight a (θ' 1) D (x u) (n + 1)), ← Finset.prod_coe_sort F]
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  have hre : ∀ n : ℕ, ENNReal.ofReal (θ' 1) ^ n
        * (∑ s : σ, ρ' {s} * bRuleMass θ' R ρr' s (j u))
        * ENNReal.ofReal (uWeight a (θ' 1) D (x u) (n + 1))
      = ENNReal.ofReal (θ' 1) ^ n * ENNReal.ofReal (uWeight a (θ' 1) D (x u) (n + 1))
        * ∑ s : σ, ρ' {s} * bRuleMass θ' R ρr' s (j u) := fun n ↦ by ring
  rw [tsum_congr hre, ENNReal.tsum_mul_right, cross_class_tsum ha ha1 hθ1' hθ1'' hD hgD (x u),
    bArityLaw, skeletonWeight_one_eq_of_chain θ' hθ0', div_eq_mul_inv, div_eq_mul_inv,
    mul_right_comm, mul_assoc]

/-- **The marginal of the coupled label at the root is `μ_*`**: the class law of the
first law, clause (ii) of `thm:chain-coupling` on the presented skeleton. -/
theorem crossLab_marginal (θ' : Offspring J) (hJN' : J ≤ N) (hθ0' : θ' 0 = 0)
    (hθ1' : 0 < θ' 1) (hθ1'' : θ' 1 < 1) [Fintype σ] [Inhabited σ] (ρ' : Measure σ)
    [IsProbabilityMeasure ρ'] (R : ℕ) (ρr' : BRule σ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a (θ' 1) * ((D : ℝ) - 1)) (x : ℕ) :
    coupledBlobMeasure (N := N) θ' ρ'
        {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) | crossLab a (θ' 1) D R ρr' ω [] = x}
      = ENNReal.ofReal (qF a D x) := by
  have hq := extinction_lt_one_of_chain θ' hθ0'
  have hs1 : θ'.skeletonWeight 1 < 1 := by
    rw [skeletonWeight_one_eq_of_chain θ' hθ0']
    exact hθ1''
  set A : ℕ → Set (((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ)) := fun κ ↦
    {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) | bArityAtC R ρr' ω.1 [] = κ} with hA
  have hAmeas : ∀ κ, MeasurableSet (A κ) := fun κ ↦
    measurable_fst (measurableSet_bArityAtC_fibre R ρr' [] κ)
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    intro κ κ' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne ?_
    simp only [hA, Set.mem_setOf_eq] at hω hω'
    rw [← hω, ← hω']
  have hAcover : (⋃ κ, A κ) = Set.univ := by
    ext ω
    simp [hA]
  have hcover : {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
        crossLab a (θ' 1) D R ρr' ω [] = x}
      = ⋃ κ, ({ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
          crossLab a (θ' 1) D R ρr' ω [] = x} ∩ A κ) := by
    rw [← Set.inter_iUnion, hAcover, Set.inter_univ]
  have hdisj : Pairwise (Function.onFun Disjoint fun κ ↦
      {ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
        crossLab a (θ' 1) D R ρr' ω [] = x} ∩ A κ) :=
    fun κ κ' hne ↦ (hAdisj hne).mono Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ κ, MeasurableSet ({ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
      crossLab a (θ' 1) D R ρr' ω [] = x} ∩ A κ) := fun κ ↦
    (measurableSet_crossLab_fibre a (θ' 1) D R ρr' [] x).inter (hAmeas κ)
  have hterm : ∀ κ, coupledBlobMeasure (N := N) θ' ρ'
      ({ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ) |
        crossLab a (θ' 1) D R ρr' ω [] = x} ∩ A κ)
        = ENNReal.ofReal (qF a D x) * bArityLaw θ' ρ' R ρr' κ := by
    intro κ
    have h := crossLab_pattern (N := N) θ' hJN' hθ0' hθ1' hθ1'' ρ' R ρr' ha ha1 hD hgD {[]}
      (by simp) (fun _ ↦ x) (fun _ ↦ κ) (by simp)
    simp only [Finset.set_biInter_singleton, Finset.prod_singleton] at h
    exact h
  rw [hcover, measure_iUnion hdisj hmeas, tsum_congr hterm, ENNReal.tsum_mul_left,
    bArityLaw_tsum (N := N) θ' hJN' hq hs1 ρ' R ρr', mul_one]

end ChainClasses
