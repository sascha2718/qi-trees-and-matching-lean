import ChainClasses.Engine.EngineBridge
import ChainClasses.Regime.ChainLabelField
import ChainClasses.Regime.MatchedRule
import ChainClasses.Regime.ChainCross
import ChainClasses.Chain.Eta

/-!
`thm:chain-cross` of `trichotomy.tex`, the identification with the engine's process: the
presented skeletons of the matched presentations of two chain-regime laws, labelled by the
level class of the presented neck on the `θ` side and by the coupled class of
`thm:chain-coupling` on the `θ'` side, are encoded on the binary tree `𝔹` as the composite
process of `thm:composite-matching`, and the two-law matching theorem is read off for two
independent presented samples.

The identification runs through `map_encLab_of_pattern` of `EngineBridge`, the law of the
encoded label field from a product formula over prefix-closed compatible probes; here the
product formulas are `blobMeasure_chainLab_pattern` and `crossLab_pattern` of
`ChainLabelField`, transported from the presented addresses to the words over the letter
range.  The engine is then applied at a tilt budget read off the floors `c δ` of
`thm:matched-presentation`, which do not depend on `D`, so that the constants
`K_{\vec ν}` and `ε_{\vec ν}` of `thm:composite-matching` are uniform in `D` although the
presented arity laws move with the miss mass `θ₁^{D²}`.

* `toAddr`, `fromAddr`, `pattern_of_listPattern`: the presented addresses of the blob
  presentation restricted to the words over `Fin N'`, and the transport of the product
  formula.
* `bArityPMF`: the presented arity law `ν̂` as a probability law.
* `chainLabW`, `bArityW`, `crossLabW`, `bArityW'`, `blobMeasure_map_encLab`,
  `coupledBlobMeasure_map_encLab`: **`thm:chain-cross` (`it:chain-cross-product`),
  the identification with the engine's process**: on either side the encoded label field
  at height `n` has the composite process law with the class law `μ_D` at ratio `θ₁` and
  the presented arity law.
* `map_prod_of_map_eq`: two independent encoded samples carry the product of the two
  process laws.
* `budgetX`, `budgetKc`, `budgetEtaStar`, `composite_matching_bound_budget`:
  **`thm:composite-matching` at a uniform tilt budget**, the mass-free two-law matching
  theorem with its constants read at a budget dominating both tilt sums.
* `shiftSupp`, `shiftLaw`, `chainCoinLaw`, `matchedBound`, `chainFloor`: the shifted
  support, the shift law, the coin law and the stopping bound of the matched presentation
  of `thm:matched-presentation`, and the floor `c δ`.
* `matchedArityPMF`, `matchedArityPMF_succ`, `matchedArityPMF_support_floor`: the
  presented arity law of the matched rule as a probability law, its support
  `1 + (Λ ∩ (0, L + M_A])` and its floor, clauses
  `it:matched-support`, `it:matched-mass` of `thm:matched-presentation`.
* `exists_chain_scale`, `chart_pack`, `compTiltBound_le_of_floor`: the largeness
  conditions from some scale on, the chart clauses of
  `thm:chain-cross` (`it:chain-cross-core`), and the tilt bound from a uniform floor.
* `chainTwoMeasure`, `chainEnc`, `crossEnc`, `exists_engine_match_chain`,
  `exists_engine_match_chain'`: **`thm:chain-cross`, the matching step**: two independent
  presented samples of the matched presentations at revealing depth `D²` admit one
  automorphism of `𝔹` matching their encoded label fields to within one class of the
  path graph with probability at least `1 - K · 16 θ₁^{D(D-5/2)}`, and so at least
  `1 - K' θ₁^{D²/2}`, for every `D` past a threshold, with `K, K'` depending on
  `θ, θ', L, δ` only.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure)
open GraphMarkovMatching.Support (FullLab restrictLab prodPMF)
open GraphMarkovMatching (leaf rootLab muM)
open GraphMarkovMatching.Composite (CtrC CState compK cT freshC markK val cRel)

variable {N' : ℕ}

/-! ### The words over `Fin N'` among the presented addresses -/

/-- A word over `Fin N'` as a presented address. -/
def toAddr (w : GWord N') : List ℕ := w.map Fin.val

/-- The word over `Fin N'` read off a presented address, the letters out of range dropped. -/
def fromAddr (N' : ℕ) (u : List ℕ) : GWord N' :=
  u.filterMap fun i => if h : i < N' then some ⟨i, h⟩ else none

@[simp] lemma toAddr_nil : toAddr ([] : GWord N') = [] := rfl

lemma toAddr_append (u v : GWord N') : toAddr (u ++ v) = toAddr u ++ toAddr v := by
  simp [toAddr]

lemma toAddr_singleton (j : Fin N') : toAddr [j] = [(j : ℕ)] := rfl

@[simp] lemma fromAddr_toAddr (w : GWord N') : fromAddr N' (toAddr w) = w := by
  induction w with
  | nil => rfl
  | cons j w ih =>
      simp only [toAddr, List.map_cons, fromAddr, List.filterMap_cons, Fin.is_lt, dite_true,
        Fin.eta]
      simp only [toAddr, fromAddr] at ih
      rw [ih]

lemma toAddr_injective : Function.Injective (toAddr (N' := N')) :=
  List.map_injective_iff.mpr Fin.val_injective

/-- A prefix of the address of a word is the address of a prefix of the word. -/
lemma exists_toAddr_of_prefix {u : GWord N'} {p' : List ℕ} (h : p' <+: toAddr u) :
    ∃ p : GWord N', p <+: u ∧ p' = toAddr p := by
  refine ⟨u.take p'.length, List.take_prefix _ _, ?_⟩
  show p' = List.map Fin.val (u.take p'.length)
  rw [List.map_take]
  exact List.prefix_iff_eq_take.mp h

/-- **The product formula transports** from the presented addresses to the words over
`Fin N'`: a prefix-closed compatible probe of words is a prefix-closed compatible probe of
addresses. -/
lemma pattern_of_listPattern {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {lab ar : Ω → List ℕ → ℕ} (μ ν : PMF ℕ)
    (hpat : ∀ F : Finset (List ℕ), (∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F) →
      ∀ a k : List ℕ → ℕ, (∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < k u) →
        P (⋂ u ∈ F, ({ω | lab ω u = a u} ∩ {ω | ar ω u = k u})) = ∏ u ∈ F, μ (a u) * ν (k u))
    (F : Finset (GWord N')) (hpc : ∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F)
    (a k : GWord N' → ℕ) (hcomp : ∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) :
    P (⋂ u ∈ F, ({ω | lab ω (toAddr u) = a u} ∩ {ω | ar ω (toAddr u) = k u}))
      = ∏ u ∈ F, μ (a u) * ν (k u) := by
  have hinj : Set.InjOn toAddr (F : Set (GWord N')) := toAddr_injective.injOn
  have h := hpat (F.image toAddr) ?_ (fun u' => a (fromAddr N' u')) (fun u' => k (fromAddr N' u'))
    ?_
  · rw [Finset.set_biInter_finset_image, Finset.prod_image hinj] at h
    simp only [fromAddr_toAddr] at h
    exact h
  · intro u' hu' p' hp'
    rw [Finset.mem_image] at hu' ⊢
    obtain ⟨u, hu, rfl⟩ := hu'
    obtain ⟨p, hp, rfl⟩ := exists_toAddr_of_prefix hp'
    exact ⟨p, hpc u hu p hp, rfl⟩
  · intro u' hu' i hi
    rw [Finset.mem_image] at hu' hi
    obtain ⟨u, hu, rfl⟩ := hu'
    obtain ⟨v, hv, hv'⟩ := hi
    obtain ⟨w, j, rfl⟩ : ∃ (w : GWord N') (j : Fin N'), v = w ++ [j] := by
      rcases List.eq_nil_or_concat v with rfl | ⟨w, j, hc⟩
      · simp [toAddr] at hv'
      · exact ⟨w, j, by rw [hc, List.concat_eq_append]⟩
    rw [toAddr_append, toAddr_singleton] at hv'
    obtain ⟨h1, h2⟩ := List.append_inj' hv' rfl
    have hji : (j : ℕ) = i := by simpa using h2
    have hwu : w = u := toAddr_injective h1
    subst hwu
    rw [fromAddr_toAddr, ← hji]
    exact hcomp w hu j hv

/-! ### The presented arity law as a probability law -/

section Chain

variable {J N : ℕ} {σ : Type*} [MeasurableSpace σ] [MeasurableSingletonClass σ] [Fintype σ]
  [Inhabited σ]

/-- **The presented arity law `ν̂` as a probability law on `ℕ`.** -/
noncomputable def bArityPMF (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) (ρ : Measure σ) [IsProbabilityMeasure ρ] (R : ℕ)
    (ρr : BRule σ) : PMF ℕ :=
  ⟨bArityLaw θ ρ R ρr, by
    have h := ENNReal.summable.hasSum (f := bArityLaw θ ρ R ρr)
    rwa [bArityLaw_tsum (N := N) θ hJN hq hs1 ρ R ρr] at h⟩

/-- In the chain regime `θ̃₁ = θ₁ < 1`. -/
lemma chain_hs1 (θ : Offspring J) (hθ0 : θ 0 = 0) (hθ1 : θ 1 < 1) :
    θ.skeletonWeight 1 < 1 := by
  rw [skeletonWeight_one_eq_of_chain θ hθ0]
  exact hθ1

/-! ### The presented fields over the words of `Fin N'` -/

/-- The level label of `thm:chain-product-form` over the words of `Fin N'`. -/
noncomputable def chainLabW (N' D R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ))
    (w : GWord N') : ℕ :=
  chainLab D R ρr ω (toAddr w)

/-- The presented arity over the words of `Fin N'`. -/
noncomputable def bArityW (N' R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ))
    (w : GWord N') : ℕ :=
  bArityAtC R ρr ω (toAddr w)

/-- The coupled label of `thm:chain-cross` over the words of `Fin N'`. -/
noncomputable def crossLabW (N' : ℕ) (a b : ℝ) (D R : ℕ) (ρr : BRule σ)
    (ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ)) (w : GWord N') : ℕ :=
  crossLab a b D R ρr ω (toAddr w)

/-- The presented arity of the second law over the words of `Fin N'`. -/
noncomputable def bArityW' (N' R : ℕ) (ρr : BRule σ)
    (ω : ((GWord N → ℕ) × (List ℕ → σ)) × (List ℕ → ℝ)) (w : GWord N') : ℕ :=
  bArityAtC R ρr ω.1 (toAddr w)

/-- **`thm:chain-cross` (`it:chain-cross-product`), the identification on the `θ`
side**: over the sample against the coin field, the level label and the presented arity
encode to the composite process with the class law `μ_D` at ratio `θ₁` and the presented
arity law `ν̂`, for every rule whose presented arities lie in the letter range. -/
theorem blobMeasure_map_encLab [Countable σ] (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (ρ : Measure σ) [IsProbabilityMeasure ρ] (R : ℕ) (ρr : BRule σ)
    {D : ℕ} (hD : 2 ≤ D) (hsupp : ∀ k, bArityLaw θ ρ R ρr k ≠ 0 → 2 ≤ k ∧ k ≤ N')
    {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (v0 n : ℕ) :
    (blobMeasure (N := N) θ ρ).map
        (fun ω => encLab exc (chainLabW N' D R ρr ω) (bArityW N' R ρr ω) v0 n)
      = (cT exc (qPMF (θ.nonneg 1) hθ1 hD)
          (bArityPMF θ hJN (extinction_lt_one_of_chain θ hθ0) (chain_hs1 θ hθ0 hθ1) ρ R ρr)
          v0 n).toMeasure :=
  map_encLab_of_pattern (blobMeasure (N := N) θ ρ)
    (fun w a => measurableSet_chainLab_fibre D R ρr (toAddr w) a)
    (fun w k => measurableSet_bArityAtC_fibre R ρr (toAddr w) k) _ _
    (pattern_of_listPattern (blobMeasure (N := N) θ ρ) _ _
      (fun F hpc a j hcomp => blobMeasure_chainLab_pattern θ hJN hθ0 hθ1 ρ R ρr hD F hpc a j
        hcomp))
    hsupp hexc v0 n

/-- **`thm:chain-cross` (`it:chain-cross-product`), the identification on the `θ'`
side**: over the labelled space of the second law, the coupled label and the presented
arity encode to the composite process with the class law `μ_D` of the first law at ratio
`θ₁` and the presented arity law `ν̂'` of the second. -/
theorem coupledBlobMeasure_map_encLab [Countable σ] (θ' : Offspring J) (hJN' : J ≤ N)
    (hθ0' : θ' 0 = 0)
    (hθ1' : 0 < θ' 1) (hθ1'' : θ' 1 < 1) (ρ' : Measure σ) [IsProbabilityMeasure ρ'] (R : ℕ)
    (ρr' : BRule σ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma a (θ' 1) * ((D : ℝ) - 1))
    (hsupp : ∀ k, bArityLaw θ' ρ' R ρr' k ≠ 0 → 2 ≤ k ∧ k ≤ N')
    {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (v0 n : ℕ) :
    (coupledBlobMeasure (N := N) θ' ρ').map
        (fun ω => encLab exc (crossLabW N' a (θ' 1) D R ρr' ω) (bArityW' N' R ρr' ω) v0 n)
      = (cT exc (qPMF ha.le ha1 hD)
          (bArityPMF θ' hJN' (extinction_lt_one_of_chain θ' hθ0') (chain_hs1 θ' hθ0' hθ1'')
            ρ' R ρr') v0 n).toMeasure :=
  map_encLab_of_pattern (coupledBlobMeasure (N := N) θ' ρ')
    (fun w x => measurableSet_crossLab_fibre a (θ' 1) D R ρr' (toAddr w) x)
    (fun w k => measurable_fst (measurableSet_bArityAtC_fibre R ρr' (toAddr w) k)) _ _
    (pattern_of_listPattern (coupledBlobMeasure (N := N) θ' ρ') _ _
      (fun F hpc x j hcomp => crossLab_pattern θ' hJN' hθ0' hθ1' hθ1'' ρ' R ρr' ha ha1 hD hgD
        F hpc x j hcomp))
    hsupp hexc v0 n

end Chain

/-! ### Two independent samples -/

/-- **Two independent encoded samples**: the law of the pair of encodings over the product
of two laws is the product of the two process laws. -/
lemma map_prod_of_map_eq {Ω₁ Ω₂ α β : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace α] [MeasurableSpace β] [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [SFinite P₁] [SFinite P₂] {X : Ω₁ → α} {Y : Ω₂ → β}
    (hX : Measurable X) (hY : Measurable Y) (p₁ : PMF α) (p₂ : PMF β)
    (h₁ : P₁.map X = p₁.toMeasure) (h₂ : P₂.map Y = p₂.toMeasure) :
    (P₁.prod P₂).map (fun ω => (X ω.1, Y ω.2)) = (prodPMF p₁ p₂).toMeasure := by
  refine Measure.ext_of_singleton fun z => ?_
  obtain ⟨x, y⟩ := z
  have hmeas : Measurable fun ω : Ω₁ × Ω₂ => (X ω.1, Y ω.2) :=
    (hX.comp measurable_fst).prodMk (hY.comp measurable_snd)
  rw [Measure.map_apply hmeas (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    GraphMarkovMatching.Support.prodPMF_apply]
  have hpre : (fun ω : Ω₁ × Ω₂ => (X ω.1, Y ω.2)) ⁻¹' {(x, y)} = (X ⁻¹' {x}) ×ˢ (Y ⁻¹' {y}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Prod.mk.injEq]
  rw [hpre, Measure.prod_prod, ← Measure.map_apply hX (measurableSet_singleton x),
    ← Measure.map_apply hY (measurableSet_singleton y), h₁, h₂,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]

/-! ### The composite matching theorem at a uniform tilt budget -/

section Budget

open GraphMarkovMatching.Composite

variable {V : Type} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The merged Green debt multiplier of `thm:composite-matching` at the tilt budget `T`. -/
noncomputable def budgetX (T : ℝ≥0∞) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  cX (2 * cNcBudget (8 * T) (cMx K1 K2)) (cRank N) (16 * T + 3)

/-- The failure constant `K_{\vec ν}` of `thm:composite-matching` at the tilt budget `T`. -/
noncomputable def budgetKc (T : ℝ≥0∞) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  compKcOf T (cMx K1 K2 : ℝ≥0∞) (budgetX T K1 K2 N)

/-- The threshold `ε_{\vec ν}` of `thm:composite-matching` at the tilt budget `T`. -/
noncomputable def budgetEtaStar (T : ℝ≥0∞) (K1 K2 : Finset ℕ) (N : ℕ) : ℝ≥0∞ :=
  min ((compC2Of T (cMx K1 K2 : ℝ≥0∞) (budgetX T K1 K2 N)
        + compC3Of T (cMx K1 K2 : ℝ≥0∞) (budgetX T K1 K2 N) + 1)⁻¹)
    (min ((compHuCOf T (cMx K1 K2 : ℝ≥0∞) (budgetX T K1 K2 N) (cLz N K1 K2))⁻¹)
      ((2 * budgetKc T K1 K2 N)⁻¹))

lemma budgetX_ne_top {T : ℝ≥0∞} (hT : T ≠ ⊤) (K1 K2 : Finset ℕ) (N : ℕ) :
    budgetX T K1 K2 N ≠ ⊤ := by
  have hC : 2 * cNcBudget (8 * T) (cMx K1 K2) ≠ ⊤ := by
    rw [cNcBudget]
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _), ?_⟩)
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)))
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT)
  rw [budgetX, cX, GraphMarkovMatching.graftGreenMultiplier,
    GraphMarkovMatching.graftGreenRemainder]
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ?_)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT, ENNReal.ofNat_ne_top⟩)
  exact ENNReal.sum_ne_top.mpr fun j _ => ENNReal.pow_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC)

lemma budgetKc_ne_top {T : ℝ≥0∞} (hT : T ≠ ⊤) (K1 K2 : Finset ℕ) (N : ℕ) :
    budgetKc T K1 K2 N ≠ ⊤ :=
  compKcOf_ne_top hT (ENNReal.natCast_ne_top _) (budgetX_ne_top hT K1 K2 N)

/-- The threshold at a finite budget is positive. -/
lemma budgetEtaStar_pos {T : ℝ≥0∞} (hT : T ≠ ⊤) (K1 K2 : Finset ℕ) (N : ℕ) :
    0 < budgetEtaStar T K1 K2 N := by
  have hκ : (cMx K1 K2 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hX := budgetX_ne_top hT K1 K2 N
  rw [budgetEtaStar]
  refine lt_min_iff.mpr ⟨?_, lt_min_iff.mpr ⟨?_, ?_⟩⟩
  · rw [ENNReal.inv_pos]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨compC2Of_ne_top hT hκ hX, compC3Of_ne_top hT hκ hX⟩, ENNReal.one_ne_top⟩
  · rw [ENNReal.inv_pos]
    exact compHuCOf_ne_top hT hκ hX _
  · rw [ENNReal.inv_pos]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (budgetKc_ne_top hT K1 K2 N)

/-- The threshold is at most one. -/
lemma budgetEtaStar_ne_top (T : ℝ≥0∞) (K1 K2 : Finset ℕ) (N : ℕ) :
    budgetEtaStar T K1 K2 N ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [budgetEtaStar]
  exact le_trans (min_le_left _ _) (ENNReal.inv_le_one.mpr le_add_self)

lemma mul_le_one_of_le_inv' {c η : ℝ≥0∞} (h : η ≤ c⁻¹) : c * η ≤ 1 :=
  le_trans (mul_le_mul_right h c) (ENNReal.mul_inv_le_one c)

/-- **`thm:composite-matching` at a uniform tilt budget**: the mass-free two-law matching
theorem with the tilt sums of both sides bounded by a budget `T`, the constants
`K_{\vec ν}` and `ε_{\vec ν}` being read at `T`, so that they depend on the two arity laws
only through their supports and the budget. -/
theorem composite_matching_bound_budget {Omega : Type*} [MeasurableSpace Omega]
    (Pm : Measure Omega) [IsProbabilityMeasure Pm]
    (Rv : V → V → Prop) (μ : PMF V) (v0 : V) (exc1 exc2 : ℕ → Option (ℕ × ℕ))
    (ν1 ν2 : PMF ℕ) (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p → p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p → p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (T : ℝ≥0∞) (hT1 : compTiltBound exc1 ν1 K1 ≤ T) (hT2 : compTiltBound exc2 ν2 K2 ≤ T)
    (heta : GraphMarkovMatching.etaG (5 / 2) Rv μ ≤ budgetEtaStar T K1 K2 N)
    (Xs Ys : (n : ℕ) → Omega → FullLab (CState V) n)
    (hXs : ∀ n omega, restrictLab n (Xs (n + 1) omega) = Xs n omega)
    (hYs : ∀ n omega, restrictLab n (Ys (n + 1) omega) = Ys n omega)
    (hpairM : ∀ n, Measurable (fun omega => (Xs n omega, Ys n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (Xs n omega, Ys n omega)) =
      (prodPMF (cT exc1 μ ν1 v0 n) (cT exc2 μ ν2 v0 n)).toMeasure) :
    1 - budgetKc T K1 K2 N * GraphMarkovMatching.etaG (5 / 2) Rv μ
      ≤ Pm {omega | GraphMarkovMatching.InfMatch (cRel Rv)
          (fun n => Xs n omega) (fun n => Ys n omega)} := by
  set κ : ℝ≥0∞ := (cMx K1 K2 : ℝ≥0∞) with hκ
  set X := budgetX T K1 K2 N with hX
  set C := 2 * cNcBudget (8 * T) (cMx K1 K2) with hC
  set cu := 16 * T + 3 with hcu
  have hT1' : cTiltSum (5 / 2) exc1 μ ν1 v0 ≤ T :=
    (cTiltSum_le_compTiltBound exc1 ν1 μ v0 hsup1 hhalf).trans hT1
  have hT2' : cTiltSum (5 / 2) exc2 μ ν2 v0 ≤ T :=
    (cTiltSum_le_compTiltBound exc2 ν2 μ v0 hsup2 hhalf).trans hT2
  have hκ1 : (K1.card : ℝ≥0∞) ≤ κ :=
    Nat.cast_le.mpr (le_trans (le_max_left _ _) (le_max_left _ _))
  have hκ2 : (K2.card : ℝ≥0∞) ≤ κ :=
    Nat.cast_le.mpr (le_trans (le_max_right _ _) (le_max_left _ _))
  have hCle : cNcBudget (8 * T) (cMx K1 K2)
      + cMpBudget (compEM exc1 exc2 ν1 ν2) (8 * T) (cMx K1 K2) ≤ C := by
    have heq : cMpBudget (compEM exc1 exc2 ν1 ν2) (8 * T) (cMx K1 K2)
        = compEM exc1 exc2 ν1 ν2 * cNcBudget (8 * T) (cMx K1 K2) := by
      rw [cMpBudget, cNcBudget]
      ring
    rw [heq, hC, two_mul]
    exact add_le_add le_rfl (mul_le_of_le_one_left' (compEM_le_one exc1 exc2 ν1 ν2))
  have hcu2 : 2 ≤ cu := le_trans (by norm_num : (2 : ℝ≥0∞) ≤ 3) le_add_self
  have hetaHu : compHuCOf T κ X (cLz N K1 K2) * GraphMarkovMatching.etaG (5 / 2) Rv μ ≤ 1 := by
    refine mul_le_one_of_le_inv' (le_trans heta ?_)
    rw [budgetEtaStar]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hu := cG_le_of_compHuCOf Rv μ v0 hhalf T κ X (cLz N K1 K2) hetaHu
  have hetaStar : GraphMarkovMatching.etaG (5 / 2) Rv μ
      ≤ cEtaStar (5 / 2) (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X := by
    refine le_trans heta (le_trans ?_ (compEtaOf_le_cEtaStar μ v0 hhalf _ _ _))
    rw [budgetEtaStar]
    exact min_le_left _ _
  have hKcle : cKc (1 / 8) (1 / 4) (4 / 27) μ v0 T κ X ≤ budgetKc T K1 K2 N := by
    rw [budgetKc]
    exact cKc_le_compKcOf μ v0 hhalf _ _ _
  have heM1 : cExcMass exc1 ν1 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_left _ _
  have heM2 : cExcMass exc2 ν2 ≤ compEM exc1 exc2 ν1 ν2 := by
    rw [compEM]
    exact le_max_right _ _
  have hmain := composite_matching_le_merged (5 / 2 : ℝ) Rv μ v0
    exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N Pm
    (δ := 1 / 8) (L := 1 / 4) (K := 4 / 27)
    (by norm_num) (by norm_num) (by norm_num) GraphMarkovMatching.quarter_L_bound
    (by norm_num) GraphMarkovMatching.fourTwentySeventh_K_bound
    hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
    hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2
    T 8 (compEM exc1 exc2 ν1 ν2) κ
    hT1' hT2' (GraphMarkovMatching.rootTilt_le Rv μ v0 hhalf) heM1 heM2 hκ1 hκ2
    compLamS_lt_one C cu hCle hcu2 hu hetaStar
    Xs Ys hXs hYs hpairM hlaw
  refine le_trans ?_ hmain
  exact tsub_le_tsub_left (mul_le_mul_left hKcle _) 1

end Budget

/-! ### The data of a chain-regime law -/

section ChainLaw

variable {J N : ℕ}

/-- The shifted support `A = supp ν̃ - 1` of a chain-regime law: the shifts `k - 1` of the
charged arities `k ≥ 2`, the generators of the branching semigroup
`def:branching-semigroup`. -/
noncomputable def shiftSupp (θ : Offspring J) : Finset ℕ :=
  ((Finset.range (J + 1)).filter fun k => 2 ≤ k ∧ θ k ≠ 0).image fun k => k - 1

lemma mem_shiftSupp (θ : Offspring J) {x : ℕ} : x ∈ shiftSupp θ ↔ 1 ≤ x ∧ θ (1 + x) ≠ 0 := by
  simp only [shiftSupp, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨hk, hk2, hθk⟩, rfl⟩
    refine ⟨by omega, ?_⟩
    rwa [show 1 + (k - 1) = k by omega]
  · rintro ⟨hx, hθ⟩
    refine ⟨1 + x, ⟨?_, by omega, hθ⟩, by omega⟩
    by_contra h
    exact hθ (θ.vanishing _ (by omega))

lemma shiftSupp_one_le (θ : Offspring J) : ∀ x ∈ shiftSupp θ, 1 ≤ x :=
  fun _ hx => ((mem_shiftSupp θ).mp hx).1

lemma shiftSupp_pos (θ : Offspring J) : ∀ x ∈ shiftSupp θ, 0 < x :=
  fun _ hx => ((mem_shiftSupp θ).mp hx).1

lemma shiftSupp_le (θ : Offspring J) : ∀ x ∈ shiftSupp θ, x ≤ J - 1 := by
  intro x hx
  obtain ⟨-, hθ⟩ := (mem_shiftSupp θ).mp hx
  by_contra h
  exact hθ (θ.vanishing _ (by omega))

lemma mem_shiftSupp_of (θ : Offspring J) (hθ0 : θ 0 = 0) :
    ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ shiftSupp θ := by
  intro x hx h
  rw [skeletonWeight_eq_of_chain θ hθ0] at h
  exact (mem_shiftSupp θ).mpr ⟨hx, h⟩

lemma max_mem_shiftSupp (θ : Offspring J) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) :
    J - 1 ∈ shiftSupp θ :=
  (mem_shiftSupp θ).mpr ⟨by omega, by rw [show 1 + (J - 1) = J by omega]; exact hθJ.ne'⟩

lemma shiftSupp_nonempty (θ : Offspring J) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) :
    (shiftSupp θ).Nonempty :=
  ⟨J - 1, max_mem_shiftSupp θ hJ2 hθJ⟩

/-- The shift law `P_x = ν̃_{1+x}` of a chain-regime law. -/
noncomputable def shiftLaw (θ : Offspring J) (x : ℕ) : ℝ := reducedWeight θ (1 + x)

lemma shiftLaw_nonneg (θ : Offspring J) (hθ0 : θ 0 = 0) (hθ1 : θ 1 < 1) :
    ∀ x ∈ shiftSupp θ, 0 ≤ shiftLaw θ x :=
  fun x _ => reducedWeight_nonneg θ (extinction_lt_one_of_chain θ hθ0) (chain_hs1 θ hθ0 hθ1) (1 + x)

lemma shiftLaw_sum (θ : Offspring J) (hθ0 : θ 0 = 0) (hθ1 : θ 1 < 1) :
    ∑ x ∈ shiftSupp θ, shiftLaw θ x = 1 :=
  Matched.sum_reducedWeight_shift θ (extinction_lt_one_of_chain θ hθ0) (chain_hs1 θ hθ0 hθ1)
    (shiftSupp_one_le θ) (mem_shiftSupp_of θ hθ0)

lemma shiftLaw_pos (θ : Offspring J) (hθ0 : θ 0 = 0) (hθ1 : θ 1 < 1) :
    ∀ x ∈ shiftSupp θ, 0 < shiftLaw θ x := by
  intro x hx
  obtain ⟨-, hθ⟩ := (mem_shiftSupp θ).mp hx
  rw [shiftLaw, reducedWeight_def, skeletonWeight_eq_of_chain θ hθ0,
    skeletonWeight_one_eq_of_chain θ hθ0]
  exact div_pos (lt_of_le_of_ne (θ.nonneg _) (Ne.symm hθ)) (by linarith)

lemma shiftLaw_le_one (θ : Offspring J) (hθ0 : θ 0 = 0) (hθ1 : θ 1 < 1) :
    ∀ x ∈ shiftSupp θ, shiftLaw θ x ≤ 1 := by
  intro x hx
  rw [← shiftLaw_sum θ hθ0 hθ1]
  exact Finset.single_le_sum (shiftLaw_nonneg θ hθ0 hθ1) hx

/-- **The coin law of the matched presentation** of a law against the chain law `θ'`: the
branch of mass `δ`, `T` simulated increments of the shift law of `θ'`, and `T` fair
stopping bits. -/
noncomputable def chainCoinLaw (θ' : Offspring J) (hθ0' : θ' 0 = 0) (hθ1' : θ' 1 < 1) (T : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : Measure (MatchedCoin (shiftSupp θ') T) :=
  matchedCoinLaw hδ0 hδ1 (shiftLaw_nonneg θ' hθ0' hθ1') (shiftLaw_sum θ' hθ0' hθ1')

instance (θ' : Offspring J) (hθ0' : θ' 0 = 0) (hθ1' : θ' 1 < 1) (T : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) : IsProbabilityMeasure (chainCoinLaw θ' hθ0' hθ1' T hδ0 hδ1) := by
  rw [chainCoinLaw]
  infer_instance

/-- The stopping bound of the matched rule of a law with `M_A = J - 1` against a law with
`M_B = J' - 1` at the window `L`: one above the fuel `F = 3L + 2M_A + M_B + 2`. -/
def matchedBound (J J' L : ℕ) : ℕ := 3 * L + 2 * (J - 1) + (J' - 1) + 2 + 1

/-- The floor `c δ` of `thm:matched-presentation` (`it:matched-mass`) at the
uniform floor `p` of the two shift laws and the window `L + M`, read at miss mass at most
`1/2`. -/
noncomputable def chainFloor (p δ : ℝ) (L M : ℕ) : ℝ := δ * ((1 / 2) * p * (p / 4) ^ (L + M))

lemma chainFloor_pos {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ) (L M : ℕ) : 0 < chainFloor p δ L M := by
  rw [chainFloor]
  positivity

lemma chainFloor_le_one {p δ : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (L M : ℕ) : chainFloor p δ L M ≤ 1 := by
  rw [chainFloor]
  have h1 : (p / 4) ^ (L + M) ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  have h2 : (1 / 2) * p * (p / 4) ^ (L + M) ≤ 1 := by nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ p / 4) (L + M)]
  nlinarith [mul_nonneg hδ0 (by positivity : (0 : ℝ) ≤ (1 / 2) * p * (p / 4) ^ (L + M))]

end ChainLaw

/-! ### The presented arity law of the matched rule: support and floor -/

section MatchedLaw

variable {J J' N : ℕ}

/-- The presented arity law of the matched presentation of `θ` against `θ'`. -/
noncomputable def matchedArityPMF (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (θ' : Offspring J') (hθ0' : θ' 0 = 0) (hθ1' : θ' 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') (L R : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : PMF ℕ :=
  haveI : Inhabited (shiftSupp θ') := ⟨⟨J' - 1, max_mem_shiftSupp θ' hJ2' hθJ'⟩⟩
  bArityPMF θ hJN (extinction_lt_one_of_chain θ hθ0) (chain_hs1 θ hθ0 hθ1)
    (chainCoinLaw θ' hθ0' hθ1' (matchedBound J J' L) hδ0 hδ1) R
    (matchedRule (shiftSupp θ') L (matchedBound J J' L))

lemma matchedArityPMF_apply (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (θ' : Offspring J') (hθ0' : θ' 0 = 0) (hθ1' : θ' 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') (L R : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    matchedArityPMF θ hJN hθ0 hθ1 θ' hθ0' hθ1' hJ2' hθJ' L R hδ0 hδ1 k
      = bArityLaw θ (chainCoinLaw θ' hθ0' hθ1' (matchedBound J J' L) hδ0 hδ1) R
          (matchedRule (shiftSupp θ') L (matchedBound J J' L)) k := rfl

/-- Below arity two the presented law vanishes. -/
lemma matchedArityPMF_eq_zero_of_lt_two (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (θ' : Offspring J') (hθ0' : θ' 0 = 0) (hθ1' : θ' 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') (L R : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k : ℕ} (hk : k < 2) :
    matchedArityPMF θ hJN hθ0 hθ1 θ' hθ0' hθ1' hJ2' hθJ' L R hδ0 hδ1 k = 0 := by
  rw [matchedArityPMF_apply, bArityLaw]
  rw [Finset.sum_eq_zero fun s _ => by rw [bRuleMass_eq_zero_of_lt_two θ R _ s hk, mul_zero],
    ENNReal.zero_div]

/-- **The presented arity law at arity `1 + j` is the presented shift law** at `j`. -/
lemma matchedArityPMF_succ (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (θ' : Offspring J') (hθ0' : θ' 0 = 0) (hθ1' : θ' 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') (L R : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (j : ℕ) :
    matchedArityPMF θ hJN hθ0 hθ1 θ' hθ0' hθ1' hJ2' hθJ' L R hδ0 hδ1 (1 + j)
      = ENNReal.ofReal (Matched.presentedShift θ R L (matchedBound J J' L) hδ0 hδ1
          (shiftLaw_nonneg θ' hθ0' hθ1') (shiftLaw_sum θ' hθ0' hθ1') j) := by
  have h : matchedArityPMF θ hJN hθ0 hθ1 θ' hθ0' hθ1' hJ2' hθJ' L R hδ0 hδ1 (1 + j)
      = (∑ s : MatchedCoin (shiftSupp θ') (matchedBound J J' L),
          matchedCoinLaw hδ0 hδ1 (shiftLaw_nonneg θ' hθ0' hθ1') (shiftLaw_sum θ' hθ0' hθ1') {s}
            * bRuleMass θ R (matchedRule (shiftSupp θ') L (matchedBound J J' L)) s (1 + j))
        / ENNReal.ofReal (1 - θ.skeletonWeight 1) := rfl
  rw [Matched.presentedShift, ← h, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- **The support and the floor of the presented arity law**
(`thm:matched-presentation` (`it:matched-support`, `it:matched-mass`) on the constructed
space): at miss mass `θ₁^R ≤ 1/2` and a window `L ≥ N₀ + M_A` past the cofiniteness
threshold, the law charges exactly the arities `1 + s`, `s ∈ Λ ∩ (0, L + M_A]`, each with
mass at least the floor `c δ`. -/
theorem matchedArityPMF_support_floor (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hθ0' : θ' 0 = 0) (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (N₀ : ℕ)
    (hN₀ : ∀ n, N₀ ≤ n → (shiftSupp θ).gcd id ∣ n →
      n ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ))
    {L : ℕ} (hL : N₀ + (J - 1) ≤ L) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hPp : ∀ a ∈ shiftSupp θ, p ≤ shiftLaw θ a) {R : ℕ} (hφ : θ 1 ^ R ≤ 1 / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (M : ℕ) (hM : J - 1 ≤ M) :
    (∀ k, matchedArityPMF θ hJN hθ0 hθ1' θ' hθ0' hθ1'' hJ2' hθJ' L R hδ0.le hδ1 k ≠ 0 ↔
      ∃ s, s ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) ∧ 0 < s ∧ s ≤ L + (J - 1) ∧
        k = 1 + s) ∧
    (∀ k, matchedArityPMF θ hJN hθ0 hθ1' θ' hθ0' hθ1'' hJ2' hθJ' L R hδ0.le hδ1 k ≠ 0 →
      ENNReal.ofReal (chainFloor p δ L M)
        ≤ matchedArityPMF θ hJN hθ0 hθ1' θ' hθ0' hθ1'' hJ2' hθJ' L R hδ0.le hδ1 k) := by
  have hq := extinction_lt_one_of_chain θ hθ0
  have hs1 := chain_hs1 θ hθ0 hθ1'
  have hA1 := shiftSupp_one_le θ
  have hAsupp := mem_shiftSupp_of θ hθ0
  have hMA := shiftSupp_le θ
  have hB0 := shiftSupp_pos θ'
  have hMB := shiftSupp_le θ'
  have hP' := shiftLaw_nonneg θ' hθ0' hθ1''
  have hP'1 := shiftLaw_sum θ' hθ0' hθ1''
  have hF : 3 * L + 2 * (J - 1) + (J' - 1) + 2 ≤ 3 * L + 2 * (J - 1) + (J' - 1) + 2 := le_rfl
  have hF' : 2 * L + 2 * (J - 1) + 2 ≤ 3 * L + 2 * (J - 1) + (J' - 1) + 2 := by omega
  have hT : 3 * L + 2 * (J - 1) + (J' - 1) + 2 + 1 ≤ matchedBound J J' L := le_rfl
  have hMAmem := max_mem_shiftSupp θ hJ2 hθJ
  have hMAL : J - 1 ≤ L := by omega
  have hφh : θ.skeletonWeight 1 ^ R ≤ 1 / 2 := by
    rwa [skeletonWeight_one_eq_of_chain θ hθ0]
  have hwin : ∀ s' : ℕ, s' ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) → L < s' →
      s' ≤ L + (J - 1) → s' - (J - 1) ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) :=
    fun s' hs'mem hs' _ => hN₀ _ (by omega)
      (Nat.dvd_sub (gcd_dvd_of_mem_closure hs'mem)
        (Finset.gcd_dvd (max_mem_shiftSupp θ hJ2 hθJ)))
  have hPp' : ∀ a ∈ shiftSupp θ, p ≤ reducedWeight θ (1 + a) := hPp
  have hpos := fun s => Matched.presentedShift_pos_iff θ hq hs1 R hA1 hAsupp hMA hB0 hMB hP'
    hP'1 hδ0.le hδ1 hF hF' hT hMAmem hMAL hp0 hp1 hPp' hφh hδ0 hwin (s := s)
  have hfloor := fun s => Matched.presentedShift_floor θ hq hs1 R hA1 hAsupp hMA hB0 hMB hP'
    hP'1 hδ0.le hδ1 hF hF' hT hMAmem hMAL hp0 hp1 hPp' hwin (s := s)
  have hsupp : ∀ k, matchedArityPMF θ hJN hθ0 hθ1' θ' hθ0' hθ1'' hJ2' hθJ' L R hδ0.le hδ1 k ≠ 0 ↔
      ∃ s, s ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) ∧ 0 < s ∧ s ≤ L + (J - 1) ∧
        k = 1 + s := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rw [matchedArityPMF_eq_zero_of_lt_two θ hJN hθ0 hθ1' θ' hθ0' hθ1'' hJ2' hθJ' L R hδ0.le
        hδ1 hk]
      simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
      intro s _ hs _
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = 1 + j := ⟨k - 1, by omega⟩
      rw [matchedArityPMF_succ, ne_eq, ENNReal.ofReal_eq_zero, not_le, hpos j]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨j, h1, h2, h3, rfl⟩
      · rintro ⟨s, h1, h2, h3, hs⟩
        have : s = j := by omega
        subst this
        exact ⟨h1, h2, h3⟩
  refine ⟨hsupp, fun k hk => ?_⟩
  obtain ⟨s, h1, h2, h3, rfl⟩ := (hsupp k).mp hk
  rw [matchedArityPMF_succ]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hfloor s h1 h2 h3))
  rw [chainFloor]
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hφ0 : 0 ≤ θ.skeletonWeight 1 ^ R := pow_nonneg ha0 R
  have hbase : p / 4 ≤ p * (1 - θ.skeletonWeight 1 ^ R) / 2 := by
    have : 1 / 2 ≤ 1 - θ.skeletonWeight 1 ^ R := by linarith
    nlinarith
  have hb0 : (0 : ℝ) ≤ p / 4 := by positivity
  have hb1 : p * (1 - θ.skeletonWeight 1 ^ R) / 2 ≤ 1 := by nlinarith
  have hpow1 : (p / 4) ^ (L + M) ≤ (p / 4) ^ (L + (J - 1)) :=
    pow_le_pow_of_le_one hb0 (by linarith) (by omega)
  have hpow2 : (p / 4) ^ (L + (J - 1)) ≤ (p * (1 - θ.skeletonWeight 1 ^ R) / 2) ^ (L + (J - 1)) :=
    pow_le_pow_left₀ hb0 hbase _
  have hc : 0 ≤ (1 / 2) * p := by positivity
  have := mul_le_mul_of_nonneg_left (hpow1.trans hpow2) hc
  exact mul_le_mul_of_nonneg_left this hδ0.le

end MatchedLaw

/-! ### The largeness conditions from some scale on -/

/-- `qBound` is antitone from `3` on. -/
lemma qBound_antitone {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {D D' : ℕ} (hD : 3 ≤ D)
    (hDD' : D ≤ D') : qBound a D' ≤ qBound a D := by
  rw [qBound, qBound]
  refine Real.sqrt_le_sqrt (pow_le_pow_of_le_one ha0 ha1 ?_)
  exact Nat.mul_le_mul hDD' (by omega)

/-- **The largeness conditions of `thm:chain-cross` hold from some scale on**: the four
conditions `eq:d0-conditions` of `thm:eta-bound`, the potential bound `16 a^{D(D-5/2)} ≤ ε`,
miss masses `θ₁^{D²}, θ₁'^{D²} ≤ 1/2`, and the cut-point condition `γ(D-1) ≥ 1` of
`thm:chain-coupling`. -/
theorem exists_chain_scale {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → 5 ≤ D ∧ a ^ (D - 1) ≤ 1 / 10 ∧ a ^ (D ^ 2 - D) ≤ 1 / 2 ∧
      36 * a ^ (5 * D - 2) ≤ 1 ∧ 16 * qBound a D ≤ ε ∧ a ^ (D ^ 2) ≤ 1 / 2 ∧
      b ^ (D ^ 2) ≤ 1 / 2 ∧ 1 ≤ cgamma a b * ((D : ℝ) - 1) := by
  obtain ⟨Da, hDa5, -, h1, h2, h3, -, hq⟩ := exists_scale ha0 ha1 hε 0
  obtain ⟨Db, hDb5, -, -, h2b, -, -, -⟩ := exists_scale hb0 hb1 one_pos 0
  have hγ := cgamma_pos ha0 ha1 hb0 hb1
  have hsq : ∀ n : ℕ, n ^ 2 - n = n * (n - 1) := fun n => by rw [sq, Nat.mul_sub_one]
  refine ⟨max (max Da Db) (⌈1 / cgamma a b⌉₊ + 1), fun D hD => ?_⟩
  have hDa : Da ≤ D := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hD)
  have hDb : Db ≤ D := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hD)
  have hDγ : ⌈1 / cgamma a b⌉₊ + 1 ≤ D := le_trans (le_max_right _ _) hD
  have hDa2 : Da ^ 2 - Da ≤ D ^ 2 := by
    have := Nat.pow_le_pow_left hDa 2
    omega
  have hDb2 : Db ^ 2 - Db ≤ D ^ 2 := by
    have := Nat.pow_le_pow_left hDb 2
    omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (pow_le_pow_of_le_one ha0.le ha1.le (by omega)) h1
  · refine le_trans (pow_le_pow_of_le_one ha0.le ha1.le ?_) h2
    rw [hsq, hsq]
    exact Nat.mul_le_mul hDa (by omega)
  · have := pow_le_pow_of_le_one ha0.le ha1.le (show 5 * Da - 2 ≤ 5 * D - 2 by omega)
    linarith
  · have hanti := qBound_antitone ha0.le ha1.le (by omega : 3 ≤ Da) hDa
    have hnn := qBound_nonneg a D
    linarith
  · exact le_trans (pow_le_pow_of_le_one ha0.le ha1.le hDa2) h2
  · exact le_trans (pow_le_pow_of_le_one hb0.le hb1.le hDb2) h2b
  · have hceil : 1 / cgamma a b ≤ (⌈1 / cgamma a b⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : ((⌈1 / cgamma a b⌉₊ + 1 : ℕ) : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hDγ
    push_cast at hcast
    calc (1 : ℝ) = cgamma a b * (1 / cgamma a b) := by
          rw [mul_one_div_cancel hγ.ne']
      _ ≤ cgamma a b * ((D : ℝ) - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hγ.le
          linarith

/-! ### The chart facts of `thm:chain-cross` -/

/-- **`thm:chain-cross` (`it:chain-cross-core`), the chart clauses**: a chart of
`exists_chart` on the side of support `1 + (Λ ∩ (0, L + M_x])` against a side of support
`1 + (Λ ∩ (0, L + M_y])`, the core ending at `1 + L + m`, satisfies the declared-pair,
chargedness, no-iteration and floor clauses of `thm:composite-matching`. -/
lemma chart_pack {Λ : AddSubmonoid ℕ} {L m Mx My : ℕ} (hmx : m ≤ Mx) (hmy : m ≤ My)
    {exc : ℕ → Option (ℕ × ℕ)} (hnone : ∀ j, j ≤ 1 + L + m → exc j = none)
    (hp : ∀ z q, exc z = some q →
      (∃ a ∈ Λ, 0 < a ∧ a ≤ L + m ∧ q.1 = 1 + a) ∧
      (∃ b ∈ Λ, 0 < b ∧ b ≤ L + m ∧ q.2 = 1 + b) ∧ q.1 + q.2 - 1 = z)
    (hw : ∀ lam ∈ Λ, L + m < lam → lam ≤ L + Mx → exc (1 + lam) ≠ none)
    {ν ν' : PMF ℕ} (hsup : ∀ k, ν k ≠ 0 ↔ ∃ s, s ∈ Λ ∧ 0 < s ∧ s ≤ L + Mx ∧ k = 1 + s)
    (hsup' : ∀ k, ν' k ≠ 0 ↔ ∃ s, s ∈ Λ ∧ 0 < s ∧ s ≤ L + My ∧ k = 1 + s) :
    (∀ k q, exc k = some q → q.1 ≤ 1 + L + m ∧ q.2 ≤ 1 + L + m ∧ ν' q.1 ≠ 0 ∧ ν' q.2 ≠ 0) ∧
    (∀ k, ν k ≠ 0 → exc k = none → k ≤ 1 + L + m ∧ ν' k ≠ 0) ∧
    (∀ k q, exc k = some q → ∀ j, j ≤ q.1 → exc j = none) ∧
    (∀ k q, exc k = some q → ν q.1 ≠ 0 ∧ ν q.2 ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k q hq
    obtain ⟨⟨a, haΛ, ha0, ham, hqa⟩, ⟨b, hbΛ, hb0, hbm, hqb⟩, -⟩ := hp k q hq
    refine ⟨by omega, by omega, ?_, ?_⟩
    · exact (hsup' _).mpr ⟨a, haΛ, ha0, by omega, hqa⟩
    · exact (hsup' _).mpr ⟨b, hbΛ, hb0, by omega, hqb⟩
  · intro k hk hnone'
    obtain ⟨s, hsΛ, hs0, hsM, rfl⟩ := (hsup k).mp hk
    by_cases hsm : s ≤ L + m
    · exact ⟨by omega, (hsup' _).mpr ⟨s, hsΛ, hs0, by omega, rfl⟩⟩
    · exact absurd hnone' (hw s hsΛ (by omega) hsM)
  · intro k q hq j hj
    obtain ⟨⟨a, -, -, ham, hqa⟩, -, -⟩ := hp k q hq
    exact hnone j (by omega)
  · intro k q hq
    obtain ⟨⟨a, haΛ, ha0, ham, hqa⟩, ⟨b, hbΛ, hb0, hbm, hqb⟩, -⟩ := hp k q hq
    exact ⟨(hsup _).mpr ⟨a, haΛ, ha0, by omega, hqa⟩, (hsup _).mpr ⟨b, hbΛ, hb0, by omega, hqb⟩⟩

/-- **The tilt bound from a uniform floor**: a law with floor `f` on its support of
cardinality at most `C` has μ-free tilt bound at most `C (f²/2)^{-5/2}`. -/
lemma compTiltBound_le_of_floor (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (Kx : Finset ℕ)
    (hsup : ∀ k, ν k ≠ 0 ↔ k ∈ Kx) {f : ℝ} (hf0 : 0 < f) (hf1 : f ≤ 1)
    (hfl : ∀ k, ν k ≠ 0 → ENNReal.ofReal f ≤ ν k)
    (hdecl : ∀ k q, exc k = some q → ν q.1 ≠ 0 ∧ ν q.2 ≠ 0) {C : ℕ} (hcard : Kx.card ≤ C) :
    GraphMarkovMatching.Composite.compTiltBound exc ν Kx
      ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (f ^ 2 / 2)) ^ (-(5 / 2 : ℝ)) := by
  rw [GraphMarkovMatching.Composite.compTiltBound]
  have hterm : ∀ k ∈ Kx, GraphMarkovMatching.Composite.compTiltFloor exc ν k ^ (-(5 / 2 : ℝ))
      ≤ (ENNReal.ofReal (f ^ 2 / 2)) ^ (-(5 / 2 : ℝ)) := by
    intro k hk
    refine GraphMarkovMatching.rpow_neg_antitone (by norm_num) ?_
    rcases h : exc k with _ | q
    · rw [GraphMarkovMatching.Composite.compTiltFloor_none exc ν h]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hfl k ((hsup k).mpr hk))
      nlinarith
    · rw [GraphMarkovMatching.Composite.compTiltFloor_some exc ν h]
      obtain ⟨h1, h2⟩ := hdecl k q h
      have heq : ENNReal.ofReal (f ^ 2 / 2) = 2⁻¹ * (ENNReal.ofReal f * ENNReal.ofReal f) := by
        rw [← ENNReal.ofReal_mul hf0.le, show f ^ 2 / 2 = 2⁻¹ * (f * f) by ring,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
          ENNReal.ofReal_ofNat]
      rw [heq]
      exact mul_le_mul_right (mul_le_mul' (hfl _ h1) (hfl _ h2)) _
  calc ∑ k ∈ Kx, GraphMarkovMatching.Composite.compTiltFloor exc ν k ^ (-(5 / 2 : ℝ))
      ≤ ∑ _k ∈ Kx, (ENNReal.ofReal (f ^ 2 / 2)) ^ (-(5 / 2 : ℝ)) := Finset.sum_le_sum hterm
    _ = (Kx.card : ℝ≥0∞) * (ENNReal.ofReal (f ^ 2 / 2)) ^ (-(5 / 2 : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (f ^ 2 / 2)) ^ (-(5 / 2 : ℝ)) :=
        mul_le_mul_left (Nat.cast_le.mpr hcard) _

/-! ### `thm:chain-cross`, the matching step -/

section Main

variable {J J' N N' : ℕ}

/-- The letter range of the encodings: the presented arities lie in
`[2, 1 + L + max(M_A, M_B)]`. -/
def chainRange (J J' L : ℕ) : ℕ := L + max (J - 1) (J' - 1) + 1

/-- **The two independent presented samples of `thm:chain-cross`**: the sample of `θ`
against the coin field of its matched rule, and the labelled space of `θ'` against the coin
field of its matched rule, the stopping bounds at the fuel of `thm:matched-presentation`. -/
noncomputable def chainTwoMeasure (θ : Offspring J) (hθ0 : θ 0 = 0) (hθ1 : θ 1 < 1)
    (θ' : Offspring J') (hθ0' : θ' 0 = 0) (hθ1' : θ' 1 < 1) (L : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    Measure (((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) ×
      (((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
        × (List ℕ → ℝ))) :=
  (blobMeasure (N := N) θ (chainCoinLaw θ' hθ0' hθ1' (matchedBound J J' L) hδ0 hδ1)).prod
    (coupledBlobMeasure (N := N') θ' (chainCoinLaw θ hθ0 hθ1 (matchedBound J' J L) hδ0 hδ1))

/-- **The encoded label field of the first sample** at scale `D`: the level label and the
presented arity of the matched rule at revealing depth `D²`, on the words over the letter
range, through the chart `exc`. -/
noncomputable def chainEnc (J : ℕ) (θ' : Offspring J') (L D : ℕ) (exc : ℕ → Option (ℕ × ℕ))
    (ω : (GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) (n : ℕ) :
    FullLab (CState ℕ) n :=
  encLab exc
    (chainLabW (chainRange J J' L) D (D ^ 2) (matchedRule (shiftSupp θ') L (matchedBound J J' L)) ω)
    (bArityW (chainRange J J' L) (D ^ 2) (matchedRule (shiftSupp θ') L (matchedBound J J' L)) ω)
    0 n

/-- **The encoded label field of the second sample** at scale `D`: the coupled label of
`thm:chain-coupling` and the presented arity of the matched rule at revealing depth `D²`. -/
noncomputable def crossEnc (θ : Offspring J) (θ' : Offspring J') (L D : ℕ)
    (exc : ℕ → Option (ℕ × ℕ))
    (ω : ((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
      × (List ℕ → ℝ)) (n : ℕ) : FullLab (CState ℕ) n :=
  encLab exc
    (crossLabW (chainRange J J' L) (θ 1) (θ' 1) D (D ^ 2)
      (matchedRule (shiftSupp θ) L (matchedBound J' J L)) ω)
    (bArityW' (chainRange J J' L) (D ^ 2) (matchedRule (shiftSupp θ) L (matchedBound J' J L)) ω)
    0 n

/-- **`thm:chain-cross`, the matching step.** For two chain-regime laws with equal branching
semigroups `Λ`, cofinite from `N₀` on, every window `L ≥ L₁` carries charts `exc₁, exc₂`
of `thm:chain-cross` (`it:chain-cross-core`) such that for every `δ ∈ (0, 1]` there
are a scale `D₇` and a constant `K`, depending on `θ, θ', L, δ` only, with the following
property: for every `D ≥ D₇`, two independent presented samples of the matched
presentations at revealing depth `D²` admit one automorphism of `𝔹` matching their
encoded label fields to within one class of the path graph at every vertex, with
probability at least `1 - K · 16 θ₁^{D(D-5/2)}`.  The constant `K` is the failure constant
of `thm:composite-matching` at the uniform tilt budget of the floors `c δ`, and the bound
`16 θ₁^{D(D-5/2)}` is the potential estimate of `thm:eta-bound`. -/
theorem exists_engine_match_chain (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0) (hθ1'₀ : 0 < θ' 1)
    (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      = AddSubmonoid.closure (shiftSupp θ' : Set ℕ))
    (N₀ : ℕ)
    (hN₀ : ∀ n, N₀ ≤ n → (shiftSupp θ).gcd id ∣ n →
      n ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ)) :
    ∃ L₁ : ℕ, ∀ L, L₁ ≤ L →
      ∃ exc1 exc2 : ℕ → Option (ℕ × ℕ), ExcCompat exc1 ∧ ExcCompat exc2 ∧
        ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1), ∃ (D₇ : ℕ) (K : ℝ), ∀ D, D₇ ≤ D →
          1 - ENNReal.ofReal (K * (16 * qBound (θ 1) D))
            ≤ chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1
              {ω | GraphMarkovMatching.InfMatch
                (cRel (GraphMatching.compat GraphMatching.pathGraph))
                (fun n => chainEnc J θ' L D exc1 ω.1 n)
                (fun n => crossEnc θ θ' L D exc2 ω.2 n)} := by
  classical
  -- the data of the two laws
  have hq := extinction_lt_one_of_chain θ hθ0
  have hq' := extinction_lt_one_of_chain θ' hθ0'
  have hAne := shiftSupp_nonempty θ hJ2 hθJ
  have hBne := shiftSupp_nonempty θ' hJ2' hθJ'
  haveI : Inhabited (shiftSupp θ) := ⟨⟨J - 1, max_mem_shiftSupp θ hJ2 hθJ⟩⟩
  haveI : Inhabited (shiftSupp θ') := ⟨⟨J' - 1, max_mem_shiftSupp θ' hJ2' hθJ'⟩⟩
  have hMA0 : 0 < J - 1 := by omega
  have hMB0 : 0 < J' - 1 := by omega
  have hMAΛ : J - 1 ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) :=
    AddSubmonoid.subset_closure (Finset.mem_coe.mpr (max_mem_shiftSupp θ hJ2 hθJ))
  have hMBΛ : J' - 1 ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) := by
    rw [hsem]
    exact AddSubmonoid.subset_closure (Finset.mem_coe.mpr (max_mem_shiftSupp θ' hJ2' hθJ'))
  have hgeq : (shiftSupp θ).gcd id = (shiftSupp θ').gcd id := gcd_eq_of_closure_eq hsem
  have hgpos : 0 < (shiftSupp θ).gcd id := by
    rcases Nat.eq_zero_or_pos ((shiftSupp θ).gcd id) with h0 | h0
    · exfalso
      rw [Finset.gcd_eq_zero_iff] at h0
      have h1 := h0 _ (max_mem_shiftSupp θ hJ2 hθJ)
      simp only [id] at h1
      omega
    · exact h0
  have hgleMA : (shiftSupp θ).gcd id ≤ J - 1 :=
    Nat.le_of_dvd (by omega) (Finset.gcd_dvd (max_mem_shiftSupp θ hJ2 hθJ))
  have hgleMB : (shiftSupp θ).gcd id ≤ J' - 1 := by
    rw [hgeq]
    exact Nat.le_of_dvd (by omega) (Finset.gcd_dvd (max_mem_shiftSupp θ' hJ2' hθJ'))
  have hΛg : ∀ n ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ),
      (shiftSupp θ).gcd id ∣ n := fun n hn => gcd_dvd_of_mem_closure hn
  have hN₀' : ∀ n, N₀ ≤ n → (shiftSupp θ').gcd id ∣ n →
      n ∈ AddSubmonoid.closure (shiftSupp θ' : Set ℕ) := by
    rw [← hsem, ← hgeq]
    exact hN₀
  -- the uniform floor of the two shift laws
  set p : ℝ := min ((shiftSupp θ).inf' hAne (shiftLaw θ)) ((shiftSupp θ').inf' hBne (shiftLaw θ'))
    with hpdef
  have hp0 : 0 < p :=
    lt_min ((Finset.lt_inf'_iff _).mpr (shiftLaw_pos θ hθ0 hθ1'))
      ((Finset.lt_inf'_iff _).mpr (shiftLaw_pos θ' hθ0' hθ1''))
  have hPp : ∀ a ∈ shiftSupp θ, p ≤ shiftLaw θ a :=
    fun a ha => le_trans (min_le_left _ _) (Finset.inf'_le _ ha)
  have hP'p : ∀ b ∈ shiftSupp θ', p ≤ shiftLaw θ' b :=
    fun b hb => le_trans (min_le_right _ _) (Finset.inf'_le _ hb)
  have hp1 : p ≤ 1 :=
    le_trans (hPp _ (max_mem_shiftSupp θ hJ2 hθJ))
      (shiftLaw_le_one θ hθ0 hθ1' _ (max_mem_shiftSupp θ hJ2 hθJ))
  -- the window
  refine ⟨2 * N₀ + 4 * max (J - 1) (J' - 1), fun L hL => ?_⟩
  set m := min (J - 1) (J' - 1) with hmdef
  set M := max (J - 1) (J' - 1) with hMdef
  have hmMA : m ≤ J - 1 := min_le_left _ _
  have hmMB : m ≤ J' - 1 := min_le_right _ _
  have hMAM : J - 1 ≤ M := le_max_left _ _
  have hMBM : J' - 1 ≤ M := le_max_right _ _
  -- the charts
  obtain ⟨exc1, he1N, -, he1p, he1w⟩ :=
    Matched.exists_chart hgpos hN₀ hΛg (m := m) (M := J - 1) (L := L) (by omega)
  obtain ⟨exc2, he2N, -, he2p, he2w⟩ :=
    Matched.exists_chart hgpos hN₀ hΛg (m := m) (M := J' - 1) (L := L) (by omega)
  have hexc1 : ExcCompat exc1 := by
    intro z q hq
    obtain ⟨⟨a, -, ha0, -, hqa⟩, ⟨b, -, hb0, -, hqb⟩, hsum⟩ := he1p z q hq
    omega
  have hexc2 : ExcCompat exc2 := by
    intro z q hq
    obtain ⟨⟨a, -, ha0, -, hqa⟩, ⟨b, -, hb0, -, hqb⟩, hsum⟩ := he2p z q hq
    omega
  refine ⟨exc1, exc2, hexc1, hexc2, fun δ hδ0 hδ1 => ?_⟩
  -- the supports, the core and the exceptional pairs
  set K1 : Finset ℕ := ((Finset.range (L + (J - 1) + 1)).filter
    fun s => s ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) ∧ 0 < s).image fun s => 1 + s
    with hK1
  set K2 : Finset ℕ := ((Finset.range (L + (J' - 1) + 1)).filter
    fun s => s ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) ∧ 0 < s).image fun s => 1 + s
    with hK2
  have hK1mem : ∀ k, k ∈ K1 ↔ ∃ s, s ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) ∧ 0 < s ∧
      s ≤ L + (J - 1) ∧ k = 1 + s := by
    intro k
    simp only [hK1, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨s, ⟨hs1, hs2, hs3⟩, rfl⟩
      exact ⟨s, hs2, hs3, by omega, rfl⟩
    · rintro ⟨s, h1, h2, h3, rfl⟩
      exact ⟨s, ⟨by omega, h1, h2⟩, rfl⟩
  have hK2mem : ∀ k, k ∈ K2 ↔ ∃ s, s ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) ∧ 0 < s ∧
      s ≤ L + (J' - 1) ∧ k = 1 + s := by
    intro k
    simp only [hK2, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨s, ⟨hs1, hs2, hs3⟩, rfl⟩
      exact ⟨s, hs2, hs3, by omega, rfl⟩
    · rintro ⟨s, h1, h2, h3, rfl⟩
      exact ⟨s, ⟨by omega, h1, h2⟩, rfl⟩
  have hK1card : K1.card ≤ chainRange J J' L := by
    rw [chainRange]
    refine le_trans Finset.card_image_le (le_trans (Finset.card_filter_le _ _) ?_)
    rw [Finset.card_range]
    omega
  have hK2card : K2.card ≤ chainRange J J' L := by
    rw [chainRange]
    refine le_trans Finset.card_image_le (le_trans (Finset.card_filter_le _ _) ?_)
    rw [Finset.card_range]
    omega
  set S : Finset ℕ := K1.filter fun k => exc1 k = none with hS
  set E1 : Finset (ℕ × ℕ) := (K1.filter fun z => exc1 z ≠ none).image fun z => (exc1 z).getD (0, 0)
    with hE1
  set E2 : Finset (ℕ × ℕ) := (K2.filter fun z => exc2 z ≠ none).image fun z => (exc2 z).getD (0, 0)
    with hE2
  set NE := 1 + L + m with hNE
  -- the floor and the uniform tilt budget
  set f₀ := chainFloor p δ L M with hf₀
  have hf0 : 0 < f₀ := chainFloor_pos hp0 hδ0 L M
  have hf1 : f₀ ≤ 1 := chainFloor_le_one hp0 hp1 hδ0.le hδ1 L M
  set T₀ : ℝ≥0∞ := (chainRange J J' L : ℝ≥0∞) * (ENNReal.ofReal (f₀ ^ 2 / 2)) ^ (-(5 / 2 : ℝ))
    with hT₀
  have hT₀ne : T₀ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_ne_top.mpr (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity))
      ENNReal.ofReal_ne_top).ne'
  set ε₀ := budgetEtaStar T₀ K1 K2 NE with hε₀
  have hε₀pos : 0 < ε₀ := budgetEtaStar_pos hT₀ne K1 K2 NE
  have hε₀ne : ε₀ ≠ ⊤ := budgetEtaStar_ne_top T₀ K1 K2 NE
  -- the scale
  obtain ⟨D₇, hD₇⟩ := exists_chain_scale hθ1 hθ1' hθ1'₀ hθ1''
    (ENNReal.toReal_pos hε₀pos.ne' hε₀ne)
  refine ⟨D₇, (budgetKc T₀ K1 K2 NE).toReal, fun D hD => ?_⟩
  obtain ⟨hD5, h1, h2, h3, hqB, hφa, hφb, hgD⟩ := hD₇ D hD
  have hD2 : 2 ≤ D := by omega
  -- the presented arity laws at this scale
  set ν1 := matchedArityPMF θ hJN hθ0 hθ1' θ' hθ0' hθ1'' hJ2' hθJ' L (D ^ 2) hδ0.le hδ1 with hν1
  set ν2 := matchedArityPMF θ' hJN' hθ0' hθ1'' θ hθ0 hθ1' hJ2 hθJ L (D ^ 2) hδ0.le hδ1 with hν2
  obtain ⟨hsup1', hfloor1⟩ := matchedArityPMF_support_floor θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hθ0'
    hθ1'' hJ2' hθJ' N₀ hN₀ (L := L) (by omega) hp0 hp1 hPp hφa hδ0 hδ1 M hMAM
  obtain ⟨hsup2', hfloor2⟩ := matchedArityPMF_support_floor θ' hJN' hθ0' hθ1'₀ hθ1'' hJ2' hθJ' θ
    hθ0 hθ1' hJ2 hθJ N₀ hN₀' (L := L) (by omega) hp0 hp1 hP'p hφb hδ0 hδ1 M hMBM
  have hsup2'' : ∀ k, ν2 k ≠ 0 ↔ ∃ s, s ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ) ∧ 0 < s ∧
      s ≤ L + (J' - 1) ∧ k = 1 + s := by
    intro k
    rw [hsup2' k, hsem]
  have hsup1 : ∀ k, ν1 k ≠ 0 ↔ k ∈ K1 := fun k => by rw [hsup1' k, hK1mem k]
  have hsup2 : ∀ k, ν2 k ≠ 0 ↔ k ∈ K2 := fun k => by rw [hsup2'' k, hK2mem k]
  obtain ⟨hdeclN1, hcharged1, hpair1, hdecl1⟩ :=
    chart_pack hmMA hmMB he1N he1p he1w hsup1' hsup2''
  obtain ⟨hdeclN2, hcharged2, hpair2, hdecl2⟩ :=
    chart_pack hmMB hmMA he2N he2p he2w hsup2'' hsup1'
  have hN : ∀ j, j ≤ NE → exc1 j = none ∧ exc2 j = none := fun j hj => ⟨he1N j hj, he2N j hj⟩
  have hS1 : ∀ k, k ∈ S ↔ ν1 k ≠ 0 ∧ exc1 k = none := fun k => by
    rw [hS, Finset.mem_filter, hsup1]
  have hSne : S.Nonempty := by
    refine ⟨1 + (J - 1), (hS1 _).mpr ⟨(hsup1' _).mpr ⟨J - 1, hMAΛ, hMA0, by omega, rfl⟩, ?_⟩⟩
    exact he1N _ (by omega)
  have hEg : ∀ (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (Kx : Finset ℕ),
      (∀ k, ν k ≠ 0 ↔ k ∈ Kx) → ∀ q, q ∈ (Kx.filter fun z => exc z ≠ none).image
        (fun z => (exc z).getD (0, 0)) ↔ ∃ z, ν z ≠ 0 ∧ exc z = some q := by
    intro exc ν Kx hsup q
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨z, ⟨hz, hne⟩, rfl⟩
      rcases h : exc z with _ | q'
      · exact absurd h hne
      · exact ⟨z, (hsup z).mpr hz, by rw [h, Option.getD_some]⟩
    · rintro ⟨z, hz, h⟩
      exact ⟨z, ⟨(hsup z).mp hz, by rw [h]; exact Option.some_ne_none _⟩, by rw [h, Option.getD_some]⟩
  have hEg1 := hEg exc1 ν1 K1 hsup1
  have hEg2 := hEg exc2 ν2 K2 hsup2
  -- the tilt budget
  have hT1 : GraphMarkovMatching.Composite.compTiltBound exc1 ν1 K1 ≤ T₀ :=
    compTiltBound_le_of_floor exc1 ν1 K1 hsup1 hf0 hf1 hfloor1 hdecl1 hK1card
  have hT2 : GraphMarkovMatching.Composite.compTiltBound exc2 ν2 K2 ≤ T₀ :=
    compTiltBound_le_of_floor exc2 ν2 K2 hsup2 hf0 hf1 hfloor2 hdecl2 hK2card
  -- the class law
  set μ := qPMF (θ.nonneg 1) hθ1' hD2 with hμ
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ μ 0 := by
    rw [hμ, qPMF_apply, qF_zero, show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hμ0 : μ 0 ≠ 0 := (lt_of_lt_of_le (by norm_num) hhalf).ne'
  have hetaμ : GraphMarkovMatching.etaG (5 / 2) (GraphMatching.compat GraphMatching.pathGraph) μ
      ≤ ENNReal.ofReal (16 * qBound (θ 1) D) := by
    rw [etaG_compat_eq]
    exact quantised_eta_le hθ1 hθ1' hD5 h1 h2 h3
  have heta : GraphMarkovMatching.etaG (5 / 2) (GraphMatching.compat GraphMatching.pathGraph) μ
      ≤ ε₀ :=
    le_trans hetaμ (le_trans (ENNReal.ofReal_le_ofReal hqB) (le_of_eq (ENNReal.ofReal_toReal hε₀ne)))
  -- the letter range
  have hsuppL1 : ∀ k, bArityLaw θ (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L) hδ0.le hδ1)
      (D ^ 2) (matchedRule (shiftSupp θ') L (matchedBound J J' L)) k ≠ 0 →
        2 ≤ k ∧ k ≤ chainRange J J' L := by
    intro k hk
    obtain ⟨s, -, hs0, hsM, rfl⟩ := (hsup1' k).mp hk
    rw [chainRange]
    omega
  have hsuppL2 : ∀ k, bArityLaw θ' (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L) hδ0.le hδ1)
      (D ^ 2) (matchedRule (shiftSupp θ) L (matchedBound J' J L)) k ≠ 0 →
        2 ≤ k ∧ k ≤ chainRange J J' L := by
    intro k hk
    obtain ⟨s, -, hs0, hsM, rfl⟩ := (hsup2'' k).mp hk
    rw [chainRange]
    omega
  -- the probability spaces
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  haveI hP1 : IsProbabilityMeasure (blobMeasure (N := N) θ
      (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L) hδ0.le hδ1)) :=
    inferInstanceAs (IsProbabilityMeasure ((survivalMeasure (N := N) θ).prod
      (BranchingProcess.fieldMeasure _)))
  haveI hP2' : IsProbabilityMeasure (blobMeasure (N := N') θ'
      (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L) hδ0.le hδ1)) :=
    inferInstanceAs (IsProbabilityMeasure ((survivalMeasure (N := N') θ').prod
      (BranchingProcess.fieldMeasure _)))
  haveI hP2 : IsProbabilityMeasure (coupledBlobMeasure (N := N') θ'
      (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L) hδ0.le hδ1)) :=
    inferInstanceAs (IsProbabilityMeasure ((blobMeasure (N := N') θ' _).prod
      (uniformField (List ℕ))))
  haveI hPm : IsProbabilityMeasure
      (chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.prod _ _))
  -- measurability of the encodings
  have hmeas1 : ∀ n, Measurable fun ω => chainEnc (N := N) J θ' L D exc1 ω n := fun n =>
    measurable_encLab_of (fun w a => measurableSet_chainLab_fibre D (D ^ 2) _ (toAddr w) a)
      (fun w k => measurableSet_bArityAtC_fibre (D ^ 2) _ (toAddr w) k) exc1 0 n
  have hmeas2 : ∀ n, Measurable fun ω => crossEnc (N' := N') θ θ' L D exc2 ω n := fun n =>
    measurable_encLab_of
      (fun w x => measurableSet_crossLab_fibre (θ 1) (θ' 1) D (D ^ 2) _ (toAddr w) x)
      (fun w k => measurable_fst (measurableSet_bArityAtC_fibre (D ^ 2) _ (toAddr w) k)) exc2 0 n
  have hpairM : ∀ n, Measurable fun ω :
      ((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) ×
        (((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
          × (List ℕ → ℝ)) =>
      (chainEnc J θ' L D exc1 ω.1 n, crossEnc θ θ' L D exc2 ω.2 n) := fun n =>
    ((hmeas1 n).comp measurable_fst).prodMk ((hmeas2 n).comp measurable_snd)
  -- the law of the pair of encodings
  have hlaw : ∀ n, (chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1).map
      (fun ω => (chainEnc J θ' L D exc1 ω.1 n, crossEnc θ θ' L D exc2 ω.2 n))
      = (prodPMF (cT exc1 μ ν1 0 n) (cT exc2 μ ν2 0 n)).toMeasure := by
    intro n
    refine map_prod_of_map_eq _ _ (hmeas1 n) (hmeas2 n) _ _ ?_ ?_
    · exact blobMeasure_map_encLab θ hJN hθ0 hθ1' _ (D ^ 2) _ hD2 hsuppL1 hexc1 0 n
    · exact coupledBlobMeasure_map_encLab θ' hJN' hθ0' hθ1'₀ hθ1'' _ (D ^ 2) _ hθ1 hθ1' hD2 hgD
        hsuppL2 hexc2 0 n
  -- the engine
  have hmain := composite_matching_bound_budget
    (chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1)
    (GraphMatching.compat GraphMatching.pathGraph) μ 0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 NE
    (GraphMatching.compat_refl _) (GraphMatching.compat_symm _) hμ0 hhalf hN
    hdeclN1 hcharged1 hdeclN2 hcharged2 hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne
    hEg1 hEg2 T₀ hT1 hT2 heta
    (fun n ω => chainEnc J θ' L D exc1 ω.1 n) (fun n ω => crossEnc θ θ' L D exc2 ω.2 n)
    (fun n ω => restrictLab_encLab _ _ _ 0 n) (fun n ω => restrictLab_encLab _ _ _ 0 n)
    hpairM hlaw
  refine le_trans ?_ hmain
  refine tsub_le_tsub_left ?_ 1
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (budgetKc_ne_top hT₀ne K1 K2 NE)]
  exact mul_le_mul_right hetaμ _

/-- The potential bound `a^{D(D-5/2)}` is at most `a^{D²/2}` from `D ≥ 5` on. -/
lemma qBound_le_rpow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 5 ≤ D) :
    qBound a D ≤ a ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2) := by
  rw [qBound, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
  refine Real.rpow_le_rpow_of_exponent_ge ha0 ha1.le ?_
  have hnat : D ^ 2 ≤ D * (2 * D - 5) := by
    rw [sq]
    exact Nat.mul_le_mul_left D (by omega)
  have hcast : ((D : ℝ) ^ 2) ≤ ((D * (2 * D - 5) : ℕ) : ℝ) := by
    rw [← Nat.cast_pow]
    exact Nat.cast_le.mpr hnat
  linarith

/-- **`thm:chain-cross`, the matching step, in the form `1 - K θ₁^{D²/2}`**: the bound of
`exists_engine_match_chain` with the potential estimate `16 θ₁^{D(D-5/2)} ≤ 16 θ₁^{D²/2}`,
summable in `D`. -/
theorem exists_engine_match_chain' (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0) (hθ1'₀ : 0 < θ' 1)
    (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      = AddSubmonoid.closure (shiftSupp θ' : Set ℕ))
    (N₀ : ℕ)
    (hN₀ : ∀ n, N₀ ≤ n → (shiftSupp θ).gcd id ∣ n →
      n ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ)) :
    ∃ L₁ : ℕ, ∀ L, L₁ ≤ L →
      ∃ exc1 exc2 : ℕ → Option (ℕ × ℕ), ExcCompat exc1 ∧ ExcCompat exc2 ∧
        ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1), ∃ (D₇ : ℕ) (K : ℝ), ∀ D, D₇ ≤ D →
          1 - ENNReal.ofReal (K * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2))
            ≤ chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1
              {ω | GraphMarkovMatching.InfMatch
                (cRel (GraphMatching.compat GraphMatching.pathGraph))
                (fun n => chainEnc J θ' L D exc1 ω.1 n)
                (fun n => crossEnc θ θ' L D exc2 ω.2 n)} := by
  obtain ⟨L₁, hL₁⟩ := exists_engine_match_chain θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hJN' hθ0' hθ1'₀
    hθ1'' hJ2' hθJ' hsem N₀ hN₀
  refine ⟨L₁, fun L hL => ?_⟩
  obtain ⟨exc1, exc2, hexc1, hexc2, hmain⟩ := hL₁ L hL
  refine ⟨exc1, exc2, hexc1, hexc2, fun δ hδ0 hδ1 => ?_⟩
  obtain ⟨D₇, K, hK⟩ := hmain δ hδ0 hδ1
  refine ⟨max D₇ 5, 16 * |K|, fun D hD => ?_⟩
  refine le_trans ?_ (hK D (le_trans (le_max_left _ _) hD))
  refine tsub_le_tsub_left (ENNReal.ofReal_le_ofReal ?_) 1
  have hq := qBound_le_rpow hθ1 hθ1' (le_trans (le_max_right _ _) hD)
  have hqn := qBound_nonneg (θ 1) D
  have hK0 : K ≤ |K| := le_abs_self K
  have hrpow : 0 ≤ θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2) := Real.rpow_nonneg hθ1.le _
  calc K * (16 * qBound (θ 1) D) ≤ |K| * (16 * qBound (θ 1) D) :=
        mul_le_mul_of_nonneg_right hK0 (by positivity)
    _ ≤ |K| * (16 * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
    _ = 16 * |K| * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2) := by ring

end Main

end ChainClasses
