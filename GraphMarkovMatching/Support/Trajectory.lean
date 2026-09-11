/-
The trajectory measure behind the infinite-tree matching theorems.

The infinite endpoints consume a probability space carrying, for each height, a level
labelling, consistent under restriction, measurable, and with the process pair law.  This
file constructs that space for any projectively consistent family of level laws: the
one-step conditional law of a height-`(n+1)` labelling given its restriction, the
Ionescu-Tulcea trajectory measure iterating it from the root law, and the level processes
read off the trajectory, patched through a section of the restriction so that consistency
holds at every point and not only almost surely.

* `extendLab`, `restrictLab_extendLab`: a section of `restrictLab`, duplicating the last
  level.
* `stepPMF`, `stepPMF_bind`: **the conditional law of one more level**, supported on the
  fibre of the restriction, with `(T n).bind (stepPMF n) = T (n + 1)`.
* `stepK`, `histK`, `trajLab`: the kernels and the Ionescu-Tulcea trajectory measure.
* `trajLab_map_eval`: **the marginals**: the height-`n` coordinate has law `T n`.
* `consLab`, `restrictLab_consLab`, `consLab_ae_eval`, `trajLab_map_consLab`: **the level
  processes**: consistent under restriction everywhere, measurable, almost surely the
  coordinates, and with the level laws.
* `trajPairLab`, `trajPairLab_map_consLab`: **two independent samples**: the product of two
  trajectory measures, whose pair of level processes has the product law at every height.
-/
import GraphMarkovMatching.Support.Measure
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

namespace GraphMarkovMatching.Support

open scoped ENNReal Classical
open MeasureTheory ProbabilityTheory Preorder

universe u
variable {V : Type u}

/-! ### A section of the restriction -/

/-- **A section of `restrictLab`**: extend a height-`n` labelling by giving both children
of every new vertex the label of their parent. -/
def extendLab : (n : ℕ) → FullLab V n → FullLab V (n + 1)
  | 0, x => (x, x, x)
  | n + 1, x => (x.1, extendLab n x.2.1, extendLab n x.2.2)

lemma restrictLab_extendLab : ∀ (n : ℕ) (x : FullLab V n),
    restrictLab n (extendLab n x) = x
  | 0, _ => rfl
  | n + 1, x => by
      obtain ⟨a, l, r⟩ := x
      show (a, restrictLab n (extendLab n l), restrictLab n (extendLab n r)) = (a, l, r)
      rw [restrictLab_extendLab n, restrictLab_extendLab n]

variable [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-! ### The one-step conditional law -/

/-- **The conditional law of one more level**: given a height-`n` labelling `x`, the law of
a height-`(n + 1)` labelling restricting to `x`, the ratio of the two level laws on the
fibre of the restriction.  Off the support of the level law the fibre carries no
conditional mass and the extension by `extendLab` stands in. -/
noncomputable def stepPMF (T : (n : ℕ) → PMF (FullLab V n))
    (hT : ∀ n, (T (n + 1)).map (restrictLab n) = T n) (n : ℕ) (x : FullLab V n) :
    PMF (FullLab V (n + 1)) :=
  if hx : T n x = 0 then PMF.pure (extendLab n x)
  else ⟨fun y => if restrictLab n y = x then T (n + 1) y / T n x else 0, by
    have hfib : ∑' y : FullLab V (n + 1),
        (if restrictLab n y = x then T (n + 1) y else 0) = T n x := by
      conv_rhs => rw [← hT n, PMF.map_apply]
      refine tsum_congr fun y => ?_
      by_cases h : restrictLab n y = x
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg fun hh => h hh.symm]
    have htotal : ∑' y : FullLab V (n + 1),
        (if restrictLab n y = x then T (n + 1) y / T n x else 0) = 1 := by
      have hsplit : ∀ y : FullLab V (n + 1),
          (if restrictLab n y = x then T (n + 1) y / T n x else 0)
            = (if restrictLab n y = x then T (n + 1) y else 0) * (T n x)⁻¹ := by
        intro y
        by_cases h : restrictLab n y = x
        · rw [if_pos h, if_pos h, ENNReal.div_eq_inv_mul, mul_comm]
        · rw [if_neg h, if_neg h, zero_mul]
      rw [tsum_congr hsplit, ENNReal.tsum_mul_right, hfib,
        ENNReal.mul_inv_cancel hx (PMF.apply_ne_top _ _)]
    exact htotal ▸ ENNReal.summable.hasSum⟩

variable (T : (n : ℕ) → PMF (FullLab V n))
  (hT : ∀ n, (T (n + 1)).map (restrictLab n) = T n)

omit [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] in
lemma stepPMF_apply_of_ne_zero {n : ℕ} {x : FullLab V n} (hx : T n x ≠ 0)
    (y : FullLab V (n + 1)) :
    stepPMF T hT n x y = if restrictLab n y = x then T (n + 1) y / T n x else 0 := by
  rw [stepPMF, dif_neg hx]
  rfl

omit [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- The conditional law is supported on the fibre of the restriction. -/
lemma restrictLab_of_stepPMF_ne_zero {n : ℕ} {x : FullLab V n} {y : FullLab V (n + 1)}
    (hy : stepPMF T hT n x y ≠ 0) : restrictLab n y = x := by
  by_cases hx : T n x = 0
  · rw [stepPMF, dif_pos hx] at hy
    have hyx : y = extendLab n x := by
      by_contra hne
      rw [PMF.pure_apply, if_neg hne] at hy
      exact hy rfl
    rw [hyx, restrictLab_extendLab]
  · rw [stepPMF_apply_of_ne_zero T hT hx] at hy
    by_contra h
    rw [if_neg h] at hy
    exact hy rfl

omit [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] in
include hT in
/-- A level law dominates each member of its fibre. -/
lemma apply_le_of_restrictLab {n : ℕ} (y : FullLab V (n + 1)) :
    T (n + 1) y ≤ T n (restrictLab n y) := by
  conv_rhs => rw [← hT n, PMF.map_apply]
  exact le_trans (le_of_eq (if_pos rfl).symm) (ENNReal.le_tsum y)

omit [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- **The one-step identity**: drawing a level from the level law and one more level from
the conditional law reproduces the next level law. -/
lemma stepPMF_bind (n : ℕ) : (T n).bind (stepPMF T hT n) = T (n + 1) := by
  refine PMF.ext fun y => ?_
  rw [PMF.bind_apply]
  by_cases hy : T n (restrictLab n y) = 0
  · have hy1 : T (n + 1) y = 0 :=
      le_antisymm (hy ▸ apply_le_of_restrictLab T hT y) zero_le
    rw [hy1, ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : T n x = 0
    · rw [hx, zero_mul]
    · rw [stepPMF_apply_of_ne_zero T hT hx]
      by_cases hxy : restrictLab n y = x
      · rw [if_pos hxy, hy1, ENNReal.zero_div, mul_zero]
      · rw [if_neg hxy, mul_zero]
  · have hsingle : (∑' x : FullLab V n, T n x * stepPMF T hT n x y)
        = T n (restrictLab n y) * stepPMF T hT n (restrictLab n y) y := by
      refine tsum_eq_single _ fun x hx => ?_
      by_cases hx0 : T n x = 0
      · rw [hx0, zero_mul]
      · rw [stepPMF_apply_of_ne_zero T hT hx0, if_neg fun h => hx h.symm, mul_zero]
    rw [hsingle, stepPMF_apply_of_ne_zero T hT hy, if_pos rfl,
      ENNReal.mul_div_cancel' (fun h0 => absurd h0 hy)
        (fun htop => absurd htop (PMF.apply_ne_top _ _))]

/-! ### The kernels and the trajectory measure -/

/-- The conditional law as a kernel. -/
noncomputable def stepK (n : ℕ) : Kernel (FullLab V n) (FullLab V (n + 1)) where
  toFun x := (stepPMF T hT n x).toMeasure
  measurable' := measurable_of_countable _

instance (n : ℕ) : IsMarkovKernel (stepK T hT n) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

lemma stepK_apply (n : ℕ) (x : FullLab V n) :
    stepK T hT n x = (stepPMF T hT n x).toMeasure := rfl

/-- The conditional law as a kernel on histories, reading the last level. -/
noncomputable def histK (n : ℕ) :
    Kernel (Π i : Finset.Iic n, FullLab V (i : ℕ)) (FullLab V (n + 1)) :=
  (stepK T hT n).comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance (n : ℕ) : IsMarkovKernel (histK T hT n) := by
  rw [histK]
  infer_instance

/-- **The trajectory measure**: the Ionescu-Tulcea measure on infinite trajectories of
level labellings, starting from the root law and iterating the conditional laws. -/
noncomputable def trajLab : Measure (Π n, FullLab V n) :=
  Kernel.trajMeasure ((T 0).toMeasure) (histK T hT)

instance : IsProbabilityMeasure (trajLab T hT) := by
  rw [trajLab]
  infer_instance

/-! ### The marginals of the trajectory measure -/

/-- The composition of a comapped kernel is the composition against the pushforward. -/
lemma comap_comp {A C : Type u} {B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (κ : Kernel A B) (g : C → A) (hg : Measurable g) (m : Measure C) :
    (κ.comap g hg) ∘ₘ m = κ ∘ₘ (m.map g) := by
  show Measure.join (Measure.map (⇑(κ.comap g hg)) m)
    = Measure.join (Measure.map ⇑κ (m.map g))
  rw [Measure.map_map κ.measurable hg]
  rfl

/-- The composition of a kernel of conditional laws against the measure of a law is the
measure of the bind. -/
lemma pmf_comp_toMeasure {A B : Type u} [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Countable B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (p : PMF A) (q : A → PMF B) (κ : Kernel A B)
    (hκ : ∀ a, κ a = (q a).toMeasure) :
    κ ∘ₘ p.toMeasure = (p.bind q).toMeasure := by
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.bind_apply (measurableSet_singleton b) κ.measurable.aemeasurable,
    lintegral_countable',
    PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b), PMF.bind_apply]
  refine tsum_congr fun a => ?_
  rw [hκ a, PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b),
    PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a), mul_comm]

/-- The height-`0` marginal of the trajectory measure, through the one-point index. -/
lemma trajLab_map_frestrictLe_zero :
    (trajLab T hT).map (frestrictLe 0) = ((T 0).toMeasure).map
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => FullLab V (i : ℕ))).symm := by
  rw [trajLab, Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  rfl

/-- **The marginals of the trajectory measure**: the height-`n` coordinate has the
height-`n` level law. -/
theorem trajLab_map_eval : ∀ n, (trajLab T hT).map (fun ω => ω n) = (T n).toMeasure
  | 0 => by
    have h0 : (trajLab T hT).map (fun ω => ω 0)
        = ((trajLab T hT).map (frestrictLe 0)).map
            (fun x : Π i : Finset.Iic 0, FullLab V (i : ℕ) => x default) := by
      rw [Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe 0)]
      rfl
    rw [h0, trajLab_map_frestrictLe_zero T hT,
      Measure.map_map (measurable_pi_apply _) (MeasurableEquiv.measurable _)]
    have hid : ((fun x : Π i : Finset.Iic 0, FullLab V (i : ℕ) => x default)
        ∘ (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => FullLab V (i : ℕ))).symm)
          = id := by
      funext y
      exact (MeasurableEquiv.piUnique
        (fun i : Finset.Iic 0 => FullLab V (i : ℕ))).apply_symm_apply y
    rw [hid, Measure.map_id]
  | n + 1 => by
    haveI : IsProbabilityMeasure ((trajLab T hT).map (frestrictLe n)) :=
      Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
    have hpair := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (μ₀ := (T 0).toMeasure) (κ := histK T hT) (a := n)
    have hsnd : (trajLab T hT).map (fun ω => ω (n + 1))
        = ((trajLab T hT).map (fun ω => (frestrictLe n ω, ω (n + 1)))).snd := by
      rw [Measure.snd, Measure.map_map measurable_snd
        ((measurable_frestrictLe n).prodMk (measurable_pi_apply _))]
      rfl
    have hlast : ((trajLab T hT).map (frestrictLe n)).map
        (fun x : Π i : Finset.Iic n, FullLab V (i : ℕ) =>
          x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = (trajLab T hT).map (fun ω => ω n) := by
      rw [Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe n)]
      rfl
    rw [show Kernel.trajMeasure ((T 0).toMeasure) (histK T hT) = trajLab T hT from rfl]
      at hpair
    rw [hsnd, ← hpair, Measure.snd_compProd, histK,
      comap_comp (stepK T hT n)
        (fun x : Π i : Finset.Iic n, FullLab V (i : ℕ) =>
          x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _),
      hlast, trajLab_map_eval n,
      pmf_comp_toMeasure (T n) (stepPMF T hT n) (stepK T hT n) (stepK_apply T hT n),
      stepPMF_bind T hT n]

/-! ### Almost sure consistency of the coordinates -/

/-- The trajectory coordinates are almost surely consistent under restriction: the
conditional law charges only the fibre, and the level law charges only its support. -/
theorem ae_restrictLab_coord (n : ℕ) :
    ∀ᵐ ω ∂(trajLab T hT), restrictLab n (ω (n + 1)) = ω n := by
  haveI : IsProbabilityMeasure ((trajLab T hT).map (frestrictLe n)) :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
  rw [ae_iff]
  have hpre : {ω : Π m, FullLab V m | ¬ restrictLab n (ω (n + 1)) = ω n}
      = (fun ω : Π m, FullLab V m => (frestrictLe n ω, ω (n + 1))) ⁻¹'
        {z : (Π i : Finset.Iic n, FullLab V (i : ℕ)) × FullLab V (n + 1) |
          ¬ restrictLab n z.2 = z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩} := rfl
  have hmeas : ∀ x : Π i : Finset.Iic n, FullLab V (i : ℕ),
      MeasurableSet {y : FullLab V (n + 1) |
        ¬ restrictLab n y = x ⟨n, Finset.mem_Iic.mpr le_rfl⟩} := fun x =>
    (Set.to_countable _).measurableSet
  have hset : MeasurableSet {z : (Π i : Finset.Iic n, FullLab V (i : ℕ)) ×
      FullLab V (n + 1) | ¬ restrictLab n z.2 = z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩} := by
    have h : {z : (Π i : Finset.Iic n, FullLab V (i : ℕ)) × FullLab V (n + 1) |
        ¬ restrictLab n z.2 = z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩}
          = {p : (Π i : Finset.Iic n, FullLab V (i : ℕ)) × FullLab V (n + 1) |
            restrictLab n p.2 = p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩}ᶜ := rfl
    rw [h]
    refine MeasurableSet.compl ?_
    have hgraph : {p : (Π i : Finset.Iic n, FullLab V (i : ℕ)) × FullLab V (n + 1) |
        restrictLab n p.2 = p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩}
          = ⋃ y : FullLab V (n + 1),
            {x : Π i : Finset.Iic n, FullLab V (i : ℕ) |
              restrictLab n y = x ⟨n, Finset.mem_Iic.mpr le_rfl⟩} ×ˢ {y} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨p.2, h, rfl⟩, fun ⟨y, hy, h2⟩ => h2 ▸ hy⟩
    rw [hgraph]
    refine MeasurableSet.iUnion fun y => MeasurableSet.prod ?_ (measurableSet_singleton y)
    exact measurable_pi_apply _ (Set.to_countable _).measurableSet
  rw [hpre, ← Measure.map_apply
    ((measurable_frestrictLe n).prodMk (measurable_pi_apply _)) hset,
    show (trajLab T hT) = Kernel.trajMeasure ((T 0).toMeasure) (histK T hT) from rfl,
    ← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.compProd_apply hset]
  have hbound : ∀ x : Π i : Finset.Iic n, FullLab V (i : ℕ),
      histK T hT n x (Prod.mk x ⁻¹' {z : (Π i : Finset.Iic n, FullLab V (i : ℕ)) ×
          FullLab V (n + 1) | ¬ restrictLab n z.2 = z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩})
        ≤ Set.indicator {x : Π i : Finset.Iic n, FullLab V (i : ℕ) |
            T n (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = 0} (fun _ => 1) x := by
    intro x
    by_cases hx : T n (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = 0
    · refine le_trans prob_le_one (le_of_eq ?_)
      exact (Set.indicator_of_mem
        (show x ∈ {x : Π i : Finset.Iic n, FullLab V (i : ℕ) |
          T n (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = 0} from hx) (fun _ => 1)).symm
    · rw [Set.indicator_of_notMem
        (show x ∉ {x : Π i : Finset.Iic n, FullLab V (i : ℕ) |
          T n (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = 0} from hx)]
      have hzero : histK T hT n x (Prod.mk x ⁻¹'
          {z : (Π i : Finset.Iic n, FullLab V (i : ℕ)) × FullLab V (n + 1) |
            ¬ restrictLab n z.2 = z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩}) = 0 := by
        rw [histK, Kernel.comap_apply, stepK_apply]
        refine (PMF.toMeasure_apply_eq_zero_iff _ (hmeas x)).mpr ?_
        rw [Set.disjoint_right]
        intro y hy hysupp
        exact hy (restrictLab_of_stepPMF_ne_zero T hT ((PMF.mem_support_iff _ _).mp hysupp))
      rw [hzero]
  refine le_antisymm (le_trans (lintegral_mono hbound) ?_) zero_le
  rw [lintegral_indicator ?_]
  · rw [MeasureTheory.setLIntegral_one]
    have hnull : ((trajLab T hT).map (frestrictLe n))
        {x : Π i : Finset.Iic n, FullLab V (i : ℕ) |
          T n (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = 0} = 0 := by
      have hp : {x : Π i : Finset.Iic n, FullLab V (i : ℕ) |
          T n (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = 0}
            = (fun x : Π i : Finset.Iic n, FullLab V (i : ℕ) =>
              x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) ⁻¹' {v : FullLab V n | T n v = 0} := rfl
      rw [hp, ← Measure.map_apply (measurable_pi_apply _) (Set.to_countable _).measurableSet]
      have hlast : ((trajLab T hT).map (frestrictLe n)).map
          (fun x : Π i : Finset.Iic n, FullLab V (i : ℕ) =>
            x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = (trajLab T hT).map (fun ω => ω n) := by
        rw [Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe n)]
        rfl
      rw [hlast, trajLab_map_eval T hT n]
      refine (PMF.toMeasure_apply_eq_zero_iff _ (Set.to_countable _).measurableSet).mpr ?_
      rw [Set.disjoint_right]
      intro v hv hvsupp
      exact (PMF.mem_support_iff _ _).mp hvsupp hv
    exact le_of_eq hnull
  · exact (Set.to_countable _).measurableSet

/-! ### The consistent level processes -/

/-- **The level processes**: the trajectory coordinates, patched through `extendLab`
whenever a coordinate fails to restrict to its predecessor, so that consistency holds at
every point of the trajectory space. -/
noncomputable def consLab : (n : ℕ) → (Π m, FullLab V m) → FullLab V n
  | 0 => fun ω => ω 0
  | n + 1 => fun ω =>
      if restrictLab n (ω (n + 1)) = consLab n ω then ω (n + 1)
      else extendLab n (consLab n ω)

omit [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- The level processes are consistent under restriction, everywhere. -/
lemma restrictLab_consLab (n : ℕ) (ω : Π m, FullLab V m) :
    restrictLab n (consLab (n + 1) ω) = consLab n ω := by
  show restrictLab n (if restrictLab n (ω (n + 1)) = consLab n ω then ω (n + 1)
    else extendLab n (consLab n ω)) = consLab n ω
  by_cases h : restrictLab n (ω (n + 1)) = consLab n ω
  · rw [if_pos h, h]
  · rw [if_neg h, restrictLab_extendLab]

lemma measurable_consLab : ∀ n, Measurable (consLab (V := V) n)
  | 0 => measurable_pi_apply 0
  | n + 1 => by
      have h : consLab (V := V) (n + 1)
          = (fun z : FullLab V (n + 1) × FullLab V n =>
              if restrictLab n z.1 = z.2 then z.1 else extendLab n z.2)
            ∘ (fun ω => (ω (n + 1), consLab n ω)) := rfl
      rw [h]
      exact (measurable_of_countable _).comp
        ((measurable_pi_apply _).prodMk (measurable_consLab n))

/-- The level processes are almost surely the coordinates. -/
theorem consLab_ae_eval : ∀ n, consLab n =ᵐ[trajLab T hT] fun ω => ω n
  | 0 => Filter.EventuallyEq.rfl
  | n + 1 => by
      filter_upwards [ae_restrictLab_coord T hT n, consLab_ae_eval n] with ω h1 h2
      show (if restrictLab n (ω (n + 1)) = consLab n ω then ω (n + 1)
        else extendLab n (consLab n ω)) = ω (n + 1)
      rw [if_pos (h1.trans h2.symm)]

/-- **The law of the level processes**: at every height the level process has the level
law. -/
theorem trajLab_map_consLab (n : ℕ) :
    (trajLab T hT).map (consLab n) = (T n).toMeasure := by
  rw [Measure.map_congr (consLab_ae_eval T hT n), trajLab_map_eval T hT n]

/-! ### Two independent samples -/

variable (T' : (n : ℕ) → PMF (FullLab V n))
  (hT' : ∀ n, (T' (n + 1)).map (restrictLab n) = T' n)

/-- **Two independent infinite samples**: the product of the two trajectory measures. -/
noncomputable def trajPairLab : Measure ((Π n, FullLab V n) × (Π n, FullLab V n)) :=
  (trajLab T hT).prod (trajLab T' hT')

instance : IsProbabilityMeasure (trajPairLab T hT T' hT') := by
  rw [trajPairLab]
  infer_instance

lemma measurable_consLab_pair (n : ℕ) :
    Measurable fun ω : (Π m, FullLab V m) × (Π m, FullLab V m) =>
      (consLab n ω.1, consLab n ω.2) :=
  ((measurable_consLab n).comp measurable_fst).prodMk
    ((measurable_consLab n).comp measurable_snd)

/-- The product of the measures of two laws is the measure of the product law. -/
lemma prodPMF_toMeasure_eq_prod {A B : Type u} [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Countable B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (p : PMF A) (q : PMF B) :
    (p.toMeasure).prod (q.toMeasure) = (prodPMF p q).toMeasure := by
  refine Measure.ext_of_singleton fun z => ?_
  obtain ⟨a, b⟩ := z
  rw [show ({(a, b)} : Set (A × B)) = {a} ×ˢ {b} from (Set.singleton_prod_singleton).symm,
    Measure.prod_prod, PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a),
    PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b),
    show ({a} : Set A) ×ˢ ({b} : Set B) = {(a, b)} from Set.singleton_prod_singleton,
    PMF.toMeasure_apply_singleton _ (a, b) (measurableSet_singleton _), prodPMF_apply]

/-- **The pair law of the level processes**: at every height the pair of level processes
has the product of the two level laws. -/
theorem trajPairLab_map_consLab (n : ℕ) :
    (trajPairLab T hT T' hT').map
        (fun ω : (Π m, FullLab V m) × (Π m, FullLab V m) =>
          (consLab n ω.1, consLab n ω.2))
      = (prodPMF (T n) (T' n)).toMeasure := by
  rw [show (fun ω : (Π m, FullLab V m) × (Π m, FullLab V m) =>
      (consLab n ω.1, consLab n ω.2)) = Prod.map (consLab n) (consLab n) from rfl,
    trajPairLab, ← Measure.map_prod_map _ _ (measurable_consLab n) (measurable_consLab n),
    trajLab_map_consLab, trajLab_map_consLab, prodPMF_toMeasure_eq_prod]

end GraphMarkovMatching.Support
