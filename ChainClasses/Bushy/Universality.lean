import ChainClasses.Bushy.AssemblyRelabel
import ChainClasses.Chain.CrossLaw
import ChainClasses.Scalar.Bushy
import ChainClasses.Bushy.ShapeIID

/-!
The proposition labelled `thm:hairy` in `gw_classes_simple.tex`, whose printed
title is **Universality in the bushy regime**, assembled on the space of two
independent samples conditioned on survival.  Each sample also carries the
independent uniform field used in `thm:shape-coupling`.  The old word "hairy"
survives here only inside LaTeX labels such as `thm:hairy` and
`eq:hairy-rate`; Lean declarations use the paper's current bushy terminology.

The three clauses of `thm:shape-coupling` enter as hypotheses, in the form the
assembly consumes: the label fields are i.i.d. with the law `q` on the label
graph `𝖰` (`it:shape-coupling-law`, which `thm:shape-iid` turns into the
product formula over a finite set of copies), matched labels give comparable
shapes (`it:shape-coupling-qi`), and the potential of `q` is small
(`it:shape-coupling-eta`).  Everything else is proved here.

The product formula is asked for over prefix-closed finite sets of copies,
which is what `survivalMeasure_shapes` delivers, and the level-`h` addresses
`Vtx h` it is used on are prefix-closed (`prefixClosed_Vtx`).

* `BushySample`, `bushyMeasure`, `twoBushyMeasure`: one sample with its uniform
  field, its law, and the law of two independent such samples.
* `shapeLab`, `measurableSet_shapeLab_fibre`, `measurable_shapeLab`: the shape
  label field `x(w) = ℓ(S(w), U(w))` and its measurability, from the fibres of
  the shape field and the sections of the label map.
* `bushyX`, `bushyY`, `bushyMeasure_readLab`, `twoBushyMeasure_map`: the
  level-`h` projections of the two label fields and their joint law, two
  independent `μ_h`-labellings, the `hlaw` hypothesis of the i.i.d. matching
  theorem.
* `bushyMatchEvent`, `measurableSet_bushyMatchEvent`, `bushy_matching_prob_ge`,
  `portrait_of_bushyMatchEvent`: the matching event, its probability
  `≥ 1 - 16 η_{𝖰,5/2}(q)`, and the portrait read off it.
* `bushy_rate`: **`eq:hairy-rate` for the assemblies**, the failure probability
  of the `8K²`-quasi-isometry bounded by `16 η_{𝖰,5/2}(q)`, at the comparison
  scale `K` of the coupling.
* `IsSampleQI`, `isSampleQI_of_isQIMap`, `bushy_rate_tree`,
  `bushy_rate_tree_scale`, `bushy_ae_tree`: the same statements for the sampled
  trees themselves, the almost sure isometry of a sample with the assembly of
  its own shapes (`thm:shape-iid`) transporting the quasi-isometry, and the
  constants of `eq:hairy-rate` at the comparison scale `K = 972D⁴`, where the
  gluing is an `8·972²D⁸`-quasi-isometry.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory GraphMatching
open BranchingProcess (sample survivalMeasure Offspring)
open scoped ENNReal

/-! ### The bushy sample space -/

/-- **One bushy sample**: an offspring field on the ambient binary tree
together with the uniform field that randomises the label map of
`thm:shape-coupling`. -/
abbrev BushySample : Type := (Amb → ℕ) × (Word → ℝ)

/-- **The law of one bushy sample**: a sample conditioned on survival together
with the independent uniform field that randomises the label map of
`thm:shape-coupling`. -/
noncomputable def bushyMeasure (θ : Offspring 2) : Measure BushySample :=
  (survivalMeasure (N := 2) θ).prod uniField

/-- The law of one bushy sample is a probability measure. -/
lemma isProbabilityMeasure_bushyMeasure (θ : Offspring 2) (hq : θ.extinction < 1) :
    IsProbabilityMeasure (bushyMeasure θ) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  exact inferInstanceAs (IsProbabilityMeasure ((survivalMeasure (N := 2) θ).prod uniField))

/-- **The two-sample space for bushy universality** (`thm:hairy`): two
independent bushy samples drawn from the two offspring laws. -/
noncomputable def twoBushyMeasure (θ θ' : Offspring 2) :
    Measure (BushySample × BushySample) :=
  (bushyMeasure θ).prod (bushyMeasure θ')

/-- The two-sample law is a probability measure. -/
lemma isProbabilityMeasure_twoBushyMeasure (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq' : θ'.extinction < 1) : IsProbabilityMeasure (twoBushyMeasure θ θ') := by
  have _ := isProbabilityMeasure_bushyMeasure θ hq
  have _ := isProbabilityMeasure_bushyMeasure θ' hq'
  exact inferInstanceAs (IsProbabilityMeasure ((bushyMeasure θ).prod (bushyMeasure θ')))

/-! ### The shape label field -/

variable {V : Type*}

/-- **The shape label of a copy**: the label map of `thm:shape-coupling`
applied to the shape sitting at the copy and to the uniform variable sitting at
the same copy. -/
noncomputable def shapeLab (ℓ : Shape → ℝ → V) (ω : BushySample) (w : Word) : V :=
  ℓ (shapeAt ω.1 w) (ω.2 w)

/-- The label events are measurable: the shape field has measurable fibres and
the label map has measurable sections. -/
lemma measurableSet_shapeLab_fibre [MeasurableSpace V] {ℓ : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v}) (w : Word) (v : V) :
    MeasurableSet {ω : BushySample | shapeLab ℓ ω w = v} := by
  have hset : {ω : BushySample | shapeLab ℓ ω w = v}
      = ⋃ τ : Shape, {c : Amb → ℕ | shapeAt c w = τ} ×ˢ {u : Word → ℝ | ℓ τ (u w) = v} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, shapeLab]
    constructor
    · intro h
      exact ⟨shapeAt ω.1 w, rfl, h⟩
    · rintro ⟨τ, h1, h2⟩
      have hτ : shapeAt ω.1 w = τ := h1
      rw [hτ]
      exact h2
  rw [hset]
  refine MeasurableSet.iUnion fun τ ↦ (measurableSet_shapeAt_eq w τ).prod ?_
  exact (BranchingProcess.measurable_coord w) (hℓ τ v)

/-- The label at a copy is a measurable function of the sample. -/
lemma measurable_shapeLab [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    {ℓ : Shape → ℝ → V} (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v})
    (w : Word) : Measurable fun ω : BushySample ↦ shapeLab ℓ ω w :=
  measurable_to_countable' fun v ↦ measurableSet_shapeLab_fibre hℓ w v

/-! ### The level projections of the two label fields -/

/-- The level-`h` projection of the label field of the first sample. -/
noncomputable def bushyX (ℓ : Shape → ℝ → V) (h : ℕ)
    (ω : BushySample × BushySample) : FullLab V h :=
  readLab (fun s ↦ shapeLab ℓ ω.1 s) h

/-- The level-`h` projection of the label field of the second sample. -/
noncomputable def bushyY (ℓ' : Shape → ℝ → V) (h : ℕ)
    (ω : BushySample × BushySample) : FullLab V h :=
  readLab (fun s ↦ shapeLab ℓ' ω.2 s) h

/-- The projections are compatible: dropping the deepest level of `bushyX` at
height `h+1` gives `bushyX` at height `h`. -/
lemma restrictLab_bushyX (ℓ : Shape → ℝ → V) (h : ℕ)
    (ω : BushySample × BushySample) :
    restrictLab h (bushyX ℓ (h + 1) ω) = bushyX ℓ h ω :=
  restrictLab_readLab h _

/-- The same for the second sample. -/
lemma restrictLab_bushyY (ℓ' : Shape → ℝ → V) (h : ℕ)
    (ω : BushySample × BushySample) :
    restrictLab h (bushyY ℓ' (h + 1) ω) = bushyY ℓ' h ω :=
  restrictLab_readLab h _

/-- The pair of level-`h` projections is measurable. -/
lemma measurable_bushyXY [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    {ℓ ℓ' : Shape → ℝ → V} (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v})
    (hℓ' : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ' τ u = v}) (h : ℕ) :
    Measurable fun ω : BushySample × BushySample ↦
      (bushyX ℓ h ω, bushyY ℓ' h ω) := by
  have hfst : Measurable fun ω : BushySample × BushySample ↦
      fun s : Word ↦ shapeLab ℓ ω.1 s :=
    measurable_pi_lambda _ fun s ↦ (measurable_shapeLab hℓ s).comp measurable_fst
  have hsnd : Measurable fun ω : BushySample × BushySample ↦
      fun s : Word ↦ shapeLab ℓ' ω.2 s :=
    measurable_pi_lambda _ fun s ↦ (measurable_shapeLab hℓ' s).comp measurable_snd
  exact ((measurable_readLab h).comp hfst).prodMk ((measurable_readLab h).comp hsnd)

/-- The addresses of `𝔹_h` are prefix-closed: this is the form in which
`thm:shape-iid` supplies the product formula. -/
lemma prefixClosed_Vtx : ∀ (h : ℕ) (w : Word), w ∈ Vtx h → ∀ p, p <+: w → p ∈ Vtx h := by
  intro h
  induction h with
  | zero =>
      intro w hw p hp
      rw [mem_Vtx_zero] at hw ⊢
      subst hw
      exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (by simpa using hp.length_le))
  | succ h ih =>
      intro w hw p hp
      rw [mem_Vtx_succ] at hw
      rcases hw with rfl | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · rw [List.prefix_nil.mp hp, mem_Vtx_succ]
        exact Or.inl rfl
      · cases p with
        | nil => rw [mem_Vtx_succ]; exact Or.inl rfl
        | cons a p =>
            obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
            rw [mem_Vtx_succ]
            exact Or.inr (Or.inl ⟨p, ih t ht p hp', rfl⟩)
      · cases p with
        | nil => rw [mem_Vtx_succ]; exact Or.inl rfl
        | cons a p =>
            obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
            rw [mem_Vtx_succ]
            exact Or.inr (Or.inr ⟨p, ih t ht p hp', rfl⟩)

/-- **`it:shape-coupling-law` at level `h`**: a label field whose finite-
dimensional laws are the products of the masses of `q` reads a level-`h`
labelling with the i.i.d. law `μ_h`. -/
lemma bushyMeasure_readLab [MeasurableSpace V] (θ : Offspring 2) (q : PMF V)
    {ℓ : Shape → ℝ → V}
    (hprod : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ ω w = v w})
        = ∏ w ∈ S, q (v w))
    (h : ℕ) (x : FullLab V h) :
    bushyMeasure θ {ω : BushySample | readLab (fun s ↦ shapeLab ℓ ω s) h = x}
      = fullMu q h x := by
  have hset : {ω : BushySample | readLab (fun s ↦ shapeLab ℓ ω s) h = x}
      = ⋂ s ∈ Vtx h, {ω : BushySample |
          shapeLab ℓ ω s = GraphMatching.coord h x s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact readLab_eq_iff h _ x
  rw [hset, hprod (Vtx h) (prefixClosed_Vtx h) (fun s ↦ GraphMatching.coord h x s),
    fullMu_apply_prod]

/-- **The two-sample law**: the pair of level-`h` projections of the two label
fields is distributed as two independent `μ_h`-labellings.  This is the `hlaw`
hypothesis of `infinite_tree_matching_prob_of_law`. -/
lemma twoBushyMeasure_map [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable V] (θ θ' : Offspring 2) (hq : θ.extinction < 1) (hq' : θ'.extinction < 1)
    (q : PMF V) {ℓ ℓ' : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v})
    (hℓ' : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ' τ u = v})
    (hprod : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hprod' : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ' (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ' ω w = v w})
        = ∏ w ∈ S, q (v w))
    (h : ℕ) :
    (twoBushyMeasure θ θ').map (fun ω ↦ (bushyX ℓ h ω, bushyY ℓ' h ω))
      = (prodPMF (fullMu q h) (fullMu q h)).toMeasure := by
  have _ := isProbabilityMeasure_bushyMeasure θ hq
  have _ := isProbabilityMeasure_bushyMeasure θ' hq'
  refine Measure.ext_of_singleton fun z ↦ ?_
  obtain ⟨x, y⟩ := z
  rw [Measure.map_apply (measurable_bushyXY hℓ hℓ' h) (measurableSet_singleton _)]
  have hpre : (fun ω : BushySample × BushySample ↦
        (bushyX ℓ h ω, bushyY ℓ' h ω)) ⁻¹' {(x, y)}
      = {ω : BushySample | readLab (fun s ↦ shapeLab ℓ ω s) h = x}
        ×ˢ {ω : BushySample | readLab (fun s ↦ shapeLab ℓ' ω s) h = y} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_setOf_eq,
      Prod.mk.injEq, bushyX, bushyY]
  rw [hpre, twoBushyMeasure, Measure.prod_prod, bushyMeasure_readLab θ q hprod h x,
    bushyMeasure_readLab θ' q hprod' h y,
    PMF.toMeasure_apply_singleton _ (x, y) (measurableSet_singleton _), prodPMF_apply]

/-! ### The matching event -/

/-- **The matching event of `thm:hairy`**: a single automorphism of the
infinite binary tree matches the two shape label fields at every copy, matched
labels being equal or adjacent in the label graph. -/
def bushyMatchEvent (G : SimpleGraph V) (ℓ ℓ' : Shape → ℝ → V) :
    Set (BushySample × BushySample) :=
  {ω | InfMatch (compat G) (fun h ↦ bushyX ℓ h ω) (fun h ↦ bushyY ℓ' h ω)}

/-- The matching event is the intersection of the level-`h` matching events, so
it is measurable. -/
lemma measurableSet_bushyMatchEvent [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] (G : SimpleGraph V) {ℓ ℓ' : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v})
    (hℓ' : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ' τ u = v}) :
    MeasurableSet (bushyMatchEvent G ℓ ℓ') := by
  have hset : bushyMatchEvent G ℓ ℓ'
      = ⋂ h : ℕ, {ω : BushySample × BushySample |
          fullSim (compat G) h (bushyX ℓ h ω) (bushyY ℓ' h ω)} := by
    ext ω
    simp only [bushyMatchEvent, Set.mem_setOf_eq, Set.mem_iInter]
    exact infMatch_iff_forall_level (compat G) _ _ (fun h ↦ restrictLab_bushyX ℓ h ω)
      (fun h ↦ restrictLab_bushyY ℓ' h ω)
  rw [hset]
  refine MeasurableSet.iInter fun h ↦ ?_
  exact measurable_bushyXY hℓ hℓ' h
    ((Set.to_countable {p : FullLab V h × FullLab V h |
      fullSim (compat G) h p.1 p.2}).measurableSet)

/-- **The matching bound**: with the potential of the label law below `10⁻⁴`,
the matching event has probability at least `1 - 16 η_{𝖰,5/2}(q)`. -/
theorem bushy_matching_prob_ge [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (θ θ' : Offspring 2) (hq : θ.extinction < 1) (hq' : θ'.extinction < 1) (q : PMF V)
    (G : SimpleGraph V) {ℓ ℓ' : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v})
    (hℓ' : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ' τ u = v})
    (hprod : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hprod' : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ' (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ' ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hη : etaG q G ≤ 1 / 10000) :
    1 - 16 * etaG q G ≤ twoBushyMeasure θ θ' (bushyMatchEvent G ℓ ℓ') := by
  have _ := isProbabilityMeasure_twoBushyMeasure θ θ' hq hq'
  have hPhi : Phi q (compat G) ≤ 1 / 10000 := by rw [← etaG_eq_Phi]; exact hη
  have hmain := infinite_tree_matching_prob_of_law (twoBushyMeasure θ θ') q (compat G)
    (compat_refl G) (compat_symm G) hPhi (fun h ω ↦ bushyX ℓ h ω) (fun h ω ↦ bushyY ℓ' h ω)
    (fun h ω ↦ restrictLab_bushyX ℓ h ω) (fun h ω ↦ restrictLab_bushyY ℓ' h ω)
    (fun h ↦ measurable_bushyXY hℓ hℓ' h)
    (fun h ↦ twoBushyMeasure_map θ θ' hq hq' q hℓ hℓ' hprod hprod' h)
  rwa [← etaG_eq_Phi] at hmain

/-- On the matching event a single portrait matches the two label fields: the
label at `w` of the first sample is equal or adjacent to the label at
`autOf π w` of the second. -/
theorem portrait_of_bushyMatchEvent {G : SimpleGraph V} {ℓ ℓ' : Shape → ℝ → V}
    {ω : BushySample × BushySample}
    (hω : ω ∈ bushyMatchEvent G ℓ ℓ') :
    ∃ π : Word → Bool ≃ Bool, ∀ w : Word,
      compat G (shapeLab ℓ ω.1 w) (shapeLab ℓ' ω.2 (autOf π w)) :=
  exists_portrait_of_infMatch (compat G) (fun s ↦ shapeLab ℓ ω.1 s)
    (fun s ↦ shapeLab ℓ' ω.2 s) hω

/-! ### `eq:hairy-rate` for the assemblies -/

/-- Sixteen times a potential below `10⁻⁴` does not exceed one. -/
private lemma sixteen_mul_le_one {x : ℝ≥0∞} (hx : x ≤ 1 / 10000) : 16 * x ≤ 1 := by
  have h1 : (1 : ℝ≥0∞) / 10000 ≤ (16 : ℝ≥0∞)⁻¹ := by
    rw [one_div]
    exact ENNReal.inv_le_inv.mpr (by norm_num)
  calc (16 : ℝ≥0∞) * x ≤ 16 * (16 : ℝ≥0∞)⁻¹ := by gcongr; exact hx.trans h1
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- **`eq:hairy-rate`**: outside an event of probability at most
`16 η_{𝖰,5/2}(q)` the assemblies of the two samples admit an
`8K²`-quasi-isometry, at the comparison scale `K` of
`thm:shape-coupling`\ `it:shape-coupling-qi`, which is `972D⁴` at scale `D`.
On the matching event the matched labels give a `K`-marked quasi-isometry of
the shape at every copy with the shape at its image copy, and
`qi_of_shape_matching` glues these. -/
theorem bushy_rate [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (θ θ' : Offspring 2) (hq : θ.extinction < 1) (hq' : θ'.extinction < 1) (q : PMF V)
    (G : SimpleGraph V) {ℓ ℓ' : Shape → ℝ → V} {K : ℝ} (hK : 1 ≤ K)
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v})
    (hℓ' : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ' τ u = v})
    (hprod : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hprod' : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ' (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ' ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hqi : ∀ (τ τ' : Shape) (u u' : ℝ), compat G (ℓ τ u) (ℓ' τ' u') →
      MarkedQI K (shapeSpace τ) (shapeSpace τ'))
    (hη : etaG q G ≤ 1 / 10000) :
    twoBushyMeasure θ θ'
        {ω | ¬ ∃ f : Assembly (shapeAt ω.1.1) → Assembly (shapeAt ω.2.1),
          IsQIMap (8 * K ^ 2) f}
      ≤ 16 * etaG q G := by
  have _ := isProbabilityMeasure_twoBushyMeasure θ θ' hq hq'
  have hone : 16 * etaG q G ≤ 1 := sixteen_mul_le_one hη
  have hmc : twoBushyMeasure θ θ' (bushyMatchEvent G ℓ ℓ')ᶜ ≤ 16 * etaG q G := by
    rw [prob_compl_eq_one_sub (measurableSet_bushyMatchEvent G hℓ hℓ')]
    calc (1 : ℝ≥0∞) - twoBushyMeasure θ θ' (bushyMatchEvent G ℓ ℓ')
        ≤ 1 - (1 - 16 * etaG q G) :=
          tsub_le_tsub_left
            (bushy_matching_prob_ge θ θ' hq hq' q G hℓ hℓ' hprod hprod' hη) 1
      _ = 16 * etaG q G := ENNReal.sub_sub_cancel ENNReal.one_ne_top hone
  refine le_trans (measure_mono ?_) hmc
  intro ω hω
  by_cases hM : ω ∈ bushyMatchEvent G ℓ ℓ'
  · exfalso
    obtain ⟨π, hπ⟩ := portrait_of_bushyMatchEvent hM
    exact hω (qi_of_shape_matching hK π
      fun w ↦ hqi _ _ (ω.1.2 w) (ω.2.2 (autOf π w)) (hπ w))
  · exact hM

/-! ### `thm:hairy` for the sampled trees -/

/-- **`def:qi`** between two sampled trees, carried by the tree metric of the
ambient tree, with all three constants equal to `K`. -/
def IsSampleQI (K : ℝ) {c c' : Amb → ℕ}
    (F : {v : Amb // v ∈ sample c} → {v : Amb // v ∈ sample c'}) : Prop :=
  (∀ a b : {v : Amb // v ∈ sample c}, (BranchingProcess.treeDist (F a).1 (F b).1 : ℝ)
      ≤ K * (BranchingProcess.treeDist a.1 b.1 : ℝ) + K) ∧
    (∀ a b : {v : Amb // v ∈ sample c}, (BranchingProcess.treeDist a.1 b.1 : ℝ)
      ≤ K * (BranchingProcess.treeDist (F a).1 (F b).1 : ℝ) + K ^ 2) ∧
    ∀ b : {v : Amb // v ∈ sample c'}, ∃ a : {v : Amb // v ∈ sample c},
      (BranchingProcess.treeDist (F a).1 b.1 : ℝ) ≤ K

/-- **The transport of `thm:shape-iid`**: a quasi-isometry of the assemblies
of the two shape fields is a quasi-isometry of the two samples, read through
the isometries identifying each sample with the assembly of its own shapes. -/
theorem isSampleQI_of_isQIMap {c c' : Amb → ℕ} {L : ℝ}
    {Φ : Assembly (shapeAt c) → {v : Amb // v ∈ sample c}} (hΦ : Function.Bijective Φ)
    (hΦd : ∀ x y, (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y)
    {Φ' : Assembly (shapeAt c') → {v : Amb // v ∈ sample c'}} (hΦ' : Function.Bijective Φ')
    (hΦd' : ∀ x y, (BranchingProcess.treeDist (Φ' x).1 (Φ' y).1 : ℝ) = dist x y)
    {f : Assembly (shapeAt c) → Assembly (shapeAt c')} (hf : IsQIMap L f) :
    ∃ F : {v : Amb // v ∈ sample c} → {v : Amb // v ∈ sample c'}, IsSampleQI L F := by
  set e := Equiv.ofBijective Φ hΦ
  set e' := Equiv.ofBijective Φ' hΦ'
  have heapp : ∀ x, Φ (e.symm x) = x := fun x ↦ e.apply_symm_apply x
  have heapp' : ∀ x, Φ' (e'.symm x) = x := fun x ↦ e'.apply_symm_apply x
  refine ⟨fun x ↦ Φ' (f (e.symm x)), fun a b ↦ ?_, fun a b ↦ ?_, fun b ↦ ?_⟩
  · rw [hΦd' (f (e.symm a)) (f (e.symm b))]
    have hab : (BranchingProcess.treeDist a.1 b.1 : ℝ) = dist (e.symm a) (e.symm b) := by
      rw [← hΦd (e.symm a) (e.symm b), heapp, heapp]
    rw [hab]
    exact hf.upper _ _
  · rw [hΦd' (f (e.symm a)) (f (e.symm b))]
    have hab : (BranchingProcess.treeDist a.1 b.1 : ℝ) = dist (e.symm a) (e.symm b) := by
      rw [← hΦd (e.symm a) (e.symm b), heapp, heapp]
    rw [hab]
    exact hf.lower _ _
  · obtain ⟨a, ha⟩ := hf.dense (e'.symm b)
    refine ⟨Φ a, ?_⟩
    have hsymm : e.symm (Φ a) = a := e.symm_apply_apply a
    have hd := hΦd' (f a) (e'.symm b)
    rw [heapp' b] at hd
    show (BranchingProcess.treeDist (Φ' (f (e.symm (Φ a)))).1 b.1 : ℝ) ≤ L
    rw [hsymm, hd]
    exact ha

/-- A null event of the sample stays null after the uniform field is added. -/
lemma bushyMeasure_prod_null (θ : Offspring 2) (hq : θ.extinction < 1) {A : Set (Amb → ℕ)}
    (hA : survivalMeasure (N := 2) θ A = 0) :
    bushyMeasure θ (A ×ˢ (Set.univ : Set (Word → ℝ))) = 0 := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  rw [bushyMeasure, Measure.prod_prod, hA, zero_mul]

/-- Null events of the first sample stay null on the two-sample space. -/
lemma twoBushyMeasure_fst_null (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq' : θ'.extinction < 1) {A : Set (Amb → ℕ)} (hA : survivalMeasure (N := 2) θ A = 0) :
    twoBushyMeasure θ θ'
      {ω : BushySample × BushySample | ω.1.1 ∈ A} = 0 := by
  have _ := isProbabilityMeasure_bushyMeasure θ hq
  have _ := isProbabilityMeasure_bushyMeasure θ' hq'
  have hset : {ω : BushySample × BushySample | ω.1.1 ∈ A}
      = (A ×ˢ (Set.univ : Set (Word → ℝ)))
        ×ˢ (Set.univ : Set BushySample) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
  rw [hset, twoBushyMeasure, Measure.prod_prod, bushyMeasure_prod_null θ hq hA, zero_mul]

/-- Null events of the second sample stay null on the two-sample space. -/
lemma twoBushyMeasure_snd_null (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq' : θ'.extinction < 1) {A : Set (Amb → ℕ)} (hA : survivalMeasure (N := 2) θ' A = 0) :
    twoBushyMeasure θ θ'
      {ω : BushySample × BushySample | ω.2.1 ∈ A} = 0 := by
  have _ := isProbabilityMeasure_bushyMeasure θ hq
  have _ := isProbabilityMeasure_bushyMeasure θ' hq'
  have hset : {ω : BushySample × BushySample | ω.2.1 ∈ A}
      = (Set.univ : Set BushySample)
        ×ˢ (A ×ˢ (Set.univ : Set (Word → ℝ))) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, and_true]
  rw [hset, twoBushyMeasure, Measure.prod_prod, bushyMeasure_prod_null θ' hq' hA, mul_zero]

/-- The samples that `thm:shape-iid` misses: those not isometric to the
assembly of their own shapes. -/
def notAssembled : Set (Amb → ℕ) :=
  {c | ¬ ∃ Φ : Assembly (shapeAt c) → {v : Amb // v ∈ sample c},
    Function.Bijective Φ ∧ ∀ x y : Assembly (shapeAt c),
      (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y}

/-- **`thm:shape-iid`, the last clause**: almost every sample is isometric to
the assembly of its own shapes. -/
lemma survivalMeasure_notAssembled (θ : Offspring 2) (hq : θ.extinction < 1) (h2 : 0 < θ 2) :
    survivalMeasure (N := 2) θ notAssembled = 0 := by
  have hae := ae_assembly_isometric_sample θ hq h2
  rw [ae_iff] at hae
  exact hae

/-- **`eq:hairy-rate`**: outside an event of probability at most
`16 η_{𝖰,5/2}(q)` the two sampled trees admit an `8K²`-quasi-isometry.  The
failure event differs from the one of `bushy_rate` only inside the null event
that a sample fails to be isometric to the assembly of its own shapes. -/
theorem bushy_rate_tree [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (θ θ' : Offspring 2) (hq : θ.extinction < 1) (hq' : θ'.extinction < 1)
    (h2 : 0 < θ 2) (h2' : 0 < θ' 2) (q : PMF V)
    (G : SimpleGraph V) {ℓ ℓ' : Shape → ℝ → V} {K : ℝ} (hK : 1 ≤ K)
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v})
    (hℓ' : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ' τ u = v})
    (hprod : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hprod' : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ' (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ' ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hqi : ∀ (τ τ' : Shape) (u u' : ℝ), compat G (ℓ τ u) (ℓ' τ' u') →
      MarkedQI K (shapeSpace τ) (shapeSpace τ'))
    (hη : etaG q G ≤ 1 / 10000) :
    twoBushyMeasure θ θ'
        {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI (8 * K ^ 2) F}
      ≤ 16 * etaG q G := by
  have hnull := survivalMeasure_notAssembled θ hq h2
  have hnull' := survivalMeasure_notAssembled θ' hq' h2'
  have hsub : {ω : BushySample × BushySample |
        ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI (8 * K ^ 2) F}
      ⊆ {ω | ¬ ∃ f : Assembly (shapeAt ω.1.1) → Assembly (shapeAt ω.2.1),
            IsQIMap (8 * K ^ 2) f}
        ∪ ({ω | ω.1.1 ∈ notAssembled} ∪ {ω | ω.2.1 ∈ notAssembled}) := by
    intro ω hω
    by_cases hb : ω.1.1 ∈ notAssembled
    · exact Or.inr (Or.inl hb)
    by_cases hb' : ω.2.1 ∈ notAssembled
    · exact Or.inr (Or.inr hb')
    refine Or.inl fun hcon ↦ hω ?_
    obtain ⟨f, hf⟩ := hcon
    obtain ⟨Φ, hΦ, hΦd⟩ := not_not.mp hb
    obtain ⟨Φ', hΦ', hΦd'⟩ := not_not.mp hb'
    exact isSampleQI_of_isQIMap hΦ hΦd hΦ' hΦd' hf
  calc twoBushyMeasure θ θ'
        {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI (8 * K ^ 2) F}
      ≤ twoBushyMeasure θ θ'
          ({ω | ¬ ∃ f : Assembly (shapeAt ω.1.1) → Assembly (shapeAt ω.2.1),
              IsQIMap (8 * K ^ 2) f} ∪ ({ω | ω.1.1 ∈ notAssembled} ∪ {ω | ω.2.1 ∈ notAssembled})) :=
        measure_mono hsub
    _ ≤ twoBushyMeasure θ θ'
          {ω | ¬ ∃ f : Assembly (shapeAt ω.1.1) → Assembly (shapeAt ω.2.1),
            IsQIMap (8 * K ^ 2) f}
        + twoBushyMeasure θ θ' ({ω | ω.1.1 ∈ notAssembled} ∪ {ω | ω.2.1 ∈ notAssembled}) := measure_union_le _ _
    _ ≤ 16 * etaG q G := by
        have hz : twoBushyMeasure θ θ' ({ω | ω.1.1 ∈ notAssembled} ∪ {ω | ω.2.1 ∈ notAssembled}) = 0 :=
          measure_union_null (twoBushyMeasure_fst_null θ θ' hq hq' hnull)
            (twoBushyMeasure_snd_null θ θ' hq hq' hnull')
        rw [hz, add_zero]
        exact bushy_rate θ θ' hq hq' q G hK hℓ hℓ' hprod hprod' hqi hη

/-- **`eq:hairy-rate` with the constants of `thm:hairy`**: at the comparison
scale `K = 972D⁴` of `thm:shape-coupling`\ `it:shape-coupling-qi` the gluing
delivers an `8·972²D⁸`-quasi-isometry of the two sampled trees, outside an
event of probability at most `16 η_{𝖰,5/2}(q)`. -/
theorem bushy_rate_tree_scale [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (θ θ' : Offspring 2) (hq : θ.extinction < 1) (hq' : θ'.extinction < 1)
    (h2 : 0 < θ 2) (h2' : 0 < θ' 2) (q : PMF V)
    (G : SimpleGraph V) {ℓ ℓ' : Shape → ℝ → V} {D : ℕ} (hD : 1 ≤ D)
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v})
    (hℓ' : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ' τ u = v})
    (hprod : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hprod' : ∀ S : Finset Word, (∀ w ∈ S, ∀ p, p <+: w → p ∈ S) → ∀ v : Word → V,
      bushyMeasure θ' (⋂ w ∈ S, {ω : BushySample | shapeLab ℓ' ω w = v w})
        = ∏ w ∈ S, q (v w))
    (hqi : ∀ (τ τ' : Shape) (u u' : ℝ), compat G (ℓ τ u) (ℓ' τ' u') →
      MarkedQI (972 * (D : ℝ) ^ 4) (shapeSpace τ) (shapeSpace τ'))
    (hη : etaG q G ≤ 1 / 10000) :
    twoBushyMeasure θ θ'
        {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI (8 * 972 ^ 2 * (D : ℝ) ^ 8) F}
      ≤ 16 * etaG q G := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD4 : (1 : ℝ) ≤ (D : ℝ) ^ 4 := one_le_pow₀ hD1
  have hK : (1 : ℝ) ≤ 972 * (D : ℝ) ^ 4 := by nlinarith
  have hmain := bushy_rate_tree θ θ' hq hq' h2 h2' q G hK hℓ hℓ' hprod hprod' hqi hη
  rwa [glued_scale (D : ℝ)] at hmain

/-- **The almost sure statement of `thm:hairy`**: if the failure probability
of `eq:hairy-rate` can be made arbitrarily small, then almost surely the two
sampled trees are quasi-isometric. -/
theorem bushy_ae_tree (θ θ' : Offspring 2)
    (hscale : ∀ ε : ℝ≥0∞, 0 < ε → ∃ L : ℝ, twoBushyMeasure θ θ'
      {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
        IsSampleQI L F} ≤ ε) :
    twoBushyMeasure θ θ'
      {ω | ¬ ∃ (L : ℝ) (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}),
        IsSampleQI L F} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) zero_le
  obtain ⟨L, hL⟩ := hscale (ε : ℝ≥0∞) (ENNReal.coe_pos.mpr hε)
  have hsub : {ω : BushySample × BushySample |
        ¬ ∃ (L : ℝ) (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}),
          IsSampleQI L F}
      ⊆ {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI L F} := by
    rintro ω hω ⟨F, hF⟩
    exact hω ⟨L, F, hF⟩
  calc twoBushyMeasure θ θ' {ω | ¬ ∃ (L : ℝ)
          (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}), IsSampleQI L F}
      ≤ twoBushyMeasure θ θ'
          {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
            IsSampleQI L F} := measure_mono hsub
    _ ≤ (ε : ℝ≥0∞) := hL
    _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm

end ChainClasses
