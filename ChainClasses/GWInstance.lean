/-
The chain half of `thm:geometric` of `matching_classes_simple.tex` on a concrete
probability space. `ChainClasses.Geometric` carries the probabilistic content
over an assumed i.i.d. offspring field; the space is supplied here by the
Bernoulli field of `BranchingProcess.Field`, indexed by `Word`, so the offspring
field of `sec:encoding` is a coordinate family and the hypotheses of the chain
half are discharged rather than assumed.

* `chainMeasure`: the offspring field in which each vertex independently has two
  children with probability `t = θ₂` and one otherwise, with its
  `IsProbabilityMeasure` instance.
* `measurable_chainMeasure_coord`, `chainMeasure_iIndepFun`,
  `chainMeasure_coord_true`: the three hypotheses of the chain half, for the
  coordinate field.
* `chainMeasure_chains_ae`: the event that every chain terminates has full
  probability.
* `chainMeasure_exploration`: `eq:exploration`, the product formula over a
  prefix-closed finite set of binary words.
* `chainMeasure_label_marginal`: the geometric law `ℙ(λ(w) = m) = θ₁^(m-1) θ₂`.
* `chainMeasure_label_iIndepFun`, `chainMeasure_quantised_label_iIndepFun`: the
  labels and the quantised labels form independent families.
* `exists_chain_field`: the packaging theorem, the existence of a probability
  space carrying an offspring field with all five conclusions at once.
-/
import ChainClasses.Geometric
import BranchingProcess.Field

namespace ChainClasses

open MeasureTheory ProbabilityTheory BranchingProcess

/-! ### The offspring field -/

/-- The offspring field of `sec:encoding`: on the space of `Bool`-valued fields
indexed by the binary words, each vertex independently has two children with
probability `t`, the paper's `θ₂`, and one otherwise. -/
noncomputable def chainMeasure {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : Measure (Word → Bool) :=
  bernoulliField ht.le ht1

instance isProbabilityMeasure_chainMeasure {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (chainMeasure ht ht1) :=
  inferInstanceAs (IsProbabilityMeasure (bernoulliField ht.le ht1))

/-! ### The three hypotheses of the chain half -/

/-- Each vertex of the offspring field is a measurable function. -/
lemma measurable_chainMeasure_coord (v : Word) :
    Measurable (coord v : (Word → Bool) → Bool) :=
  measurable_bernoulliField_coord v

/-- The offspring field is independent across vertices. -/
theorem chainMeasure_iIndepFun {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    iIndepFun (fun v : Word ↦ (coord v : (Word → Bool) → Bool)) (chainMeasure ht ht1) :=
  bernoulliField_iIndepFun ht.le ht1

/-- Each vertex of the offspring field has two children with probability `t`. -/
theorem chainMeasure_coord_true {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (v : Word) :
    chainMeasure ht ht1 {ω | coord v ω = true} = ENNReal.ofReal t :=
  bernoulliField_apply_true ht.le ht1 v

/-! ### The conclusions of the chain half, on the concrete space -/

/-- **`Ω₀` has full probability**: almost surely every chain of the offspring
field terminates. -/
theorem chainMeasure_chains_ae {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    chainMeasure ht ht1 {ω | Chains ω} = 1 :=
  chains_ae (chainMeasure ht ht1) (fun v : Word ↦ (coord v : (Word → Bool) → Bool)) t
    measurable_chainMeasure_coord (chainMeasure_iIndepFun ht ht1)
    (chainMeasure_coord_true ht ht1) ht

/-- **`eq:exploration`**: for a prefix-closed finite set of binary words the
label events of the offspring field factorise into the geometric masses. -/
theorem chainMeasure_exploration {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (s : Finset Word)
    (hs : ∀ w ∈ s, ∀ p, p <+: w → p ∈ s) (n : Word → ℕ) (hn : ∀ w ∈ s, 1 ≤ n w) :
    chainMeasure ht ht1 (⋂ w ∈ s, {ω | labAux ω w = n w})
      = ∏ w ∈ s, ENNReal.ofReal ((1 - t) ^ (n w - 1) * t) :=
  exploration (chainMeasure ht ht1) (fun v : Word ↦ (coord v : (Word → Bool) → Bool)) t
    measurable_chainMeasure_coord (chainMeasure_iIndepFun ht ht1)
    (chainMeasure_coord_true ht ht1) ht1 ht.le s hs n hn

/-- **`thm:geometric`, the marginal law**: each label of the offspring field is
geometric, `ℙ(λ(w) = m) = θ₁^(m-1) θ₂`. -/
theorem chainMeasure_label_marginal {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (w : Word)
    {m : ℕ} (hm : 1 ≤ m) :
    chainMeasure ht ht1 {ω | labAux ω w = m} = ENNReal.ofReal ((1 - t) ^ (m - 1) * t) :=
  label_marginal (chainMeasure ht ht1) (fun v : Word ↦ (coord v : (Word → Bool) → Bool)) t
    measurable_chainMeasure_coord (chainMeasure_iIndepFun ht ht1)
    (chainMeasure_coord_true ht ht1) ht ht1 w hm

/-- **`thm:geometric`, independence**: the chain labels of the offspring field
form an independent family. -/
theorem chainMeasure_label_iIndepFun {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    iIndepFun (fun (w : Word) (ω : Word → Bool) ↦ labAux ω w) (chainMeasure ht ht1) :=
  label_iIndepFun (chainMeasure ht ht1) (fun v : Word ↦ (coord v : (Word → Bool) → Bool)) t
    measurable_chainMeasure_coord (chainMeasure_iIndepFun ht ht1)
    (chainMeasure_coord_true ht ht1) ht ht1

/-- **The independence clause of `thm:chain-classes`**: the quantised labels
`ℓ_D(λ(w))`, `w ∈ 𝔹`, of the offspring field form an independent family. -/
theorem chainMeasure_quantised_label_iIndepFun {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (D : ℕ) :
    iIndepFun (fun (w : Word) (ω : Word → Bool) ↦ levelMap D (labAux ω w))
      (chainMeasure ht ht1) :=
  quantised_label_iIndepFun (chainMeasure ht ht1)
    (fun v : Word ↦ (coord v : (Word → Bool) → Bool)) t D
    measurable_chainMeasure_coord (chainMeasure_iIndepFun ht ht1)
    (chainMeasure_coord_true ht ht1) ht ht1

/-! ### The packaged statement -/

/-- **The chain half on a concrete space.** For `0 < t ≤ 1` there is a
probability space carrying a measurable, independent offspring field, each
vertex having two children with probability `t`, on which every chain terminates
almost surely, the label events obey `eq:exploration` over prefix-closed finite
sets, every label is geometric with parameter `t`, and the labels and their
quantisations `ℓ_D` form independent families. The space is `Word → Bool` under
`chainMeasure`. -/
theorem exists_chain_field {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : Word → Ω → Bool),
      (∀ v, Measurable (X v)) ∧ iIndepFun X P ∧
      (∀ v, P {ω | X v ω = true} = ENNReal.ofReal t) ∧
      P {ω | Chains fun v ↦ X v ω} = 1 ∧
      (∀ s : Finset Word, (∀ w ∈ s, ∀ p, p <+: w → p ∈ s) → ∀ n : Word → ℕ,
        (∀ w ∈ s, 1 ≤ n w) →
        P (⋂ w ∈ s, {ω | labAux (fun v ↦ X v ω) w = n w})
          = ∏ w ∈ s, ENNReal.ofReal ((1 - t) ^ (n w - 1) * t)) ∧
      (∀ (w : Word) (m : ℕ), 1 ≤ m →
        P {ω | labAux (fun v ↦ X v ω) w = m} = ENNReal.ofReal ((1 - t) ^ (m - 1) * t)) ∧
      iIndepFun (fun w ω ↦ labAux (fun v ↦ X v ω) w) P ∧
      ∀ D : ℕ, iIndepFun (fun w ω ↦ levelMap D (labAux (fun v ↦ X v ω) w)) P :=
  ⟨Word → Bool, inferInstance, chainMeasure ht ht1, inferInstance,
    fun v : Word ↦ (coord v : (Word → Bool) → Bool),
    measurable_chainMeasure_coord, chainMeasure_iIndepFun ht ht1,
    chainMeasure_coord_true ht ht1, chainMeasure_chains_ae ht ht1,
    fun s hs n hn ↦ chainMeasure_exploration ht ht1 s hs n hn,
    fun w _ hm ↦ chainMeasure_label_marginal ht ht1 w hm,
    chainMeasure_label_iIndepFun ht ht1,
    fun D ↦ chainMeasure_quantised_label_iIndepFun ht ht1 D⟩

end ChainClasses
