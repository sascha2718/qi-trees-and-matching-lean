/-
The concrete probability space carrying an i.i.d. field of coordinates indexed
by an arbitrary type. The space is the function type `ι → α`, the measure is the
infinite product of copies of a single law `μ`, and the field is the family of
coordinate maps, which is independent with each coordinate distributed as `μ`.
The index type is arbitrary, so the module depends on nothing else in the
library; the offspring and label fields instantiate it.

* `fieldMeasure`: the product measure on `ι → α`, a probability measure.
* `coord`, `measurable_coord`: the coordinate maps and their measurability.
* `coord_iIndepFun`: independence of the coordinate family.
* `map_coord`, `coord_law`: each coordinate has law `μ`.
* `bernoulliLaw`, `bernoulliField`: the specialisation to `α = Bool` at success
  probability `t`, with `bernoulliField_apply_true`, `bernoulliField_iIndepFun`
  and `measurable_bernoulliField_coord`.
* `exists_bernoulli_field`: the packaging theorem, the existence of a probability
  space carrying an independent family of Bernoulli(`t`) coordinates.
-/
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi

namespace BranchingProcess

open MeasureTheory ProbabilityTheory

universe u

section Field

variable {ι : Type*} {α : Type*}

/-- The `i`-th coordinate of a field of labels indexed by `ι`. -/
def coord (i : ι) : (ι → α) → α := fun ω ↦ ω i

variable [MeasurableSpace α]

/-- The i.i.d. field measure: the infinite product on `ι → α` of copies of `μ`,
one for each index. No countability hypothesis on `ι` is needed. -/
noncomputable def fieldMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Measure (ι → α) :=
  Measure.infinitePi (fun _ : ι ↦ μ)

instance isProbabilityMeasure_fieldMeasure (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (fieldMeasure (ι := ι) μ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ι ↦ μ)))

/-- Every coordinate is measurable. -/
lemma measurable_coord (i : ι) : Measurable (coord i : (ι → α) → α) :=
  measurable_pi_apply i

/-- **Independence of the field.** Under the product measure the coordinates form
an independent family. -/
theorem coord_iIndepFun (μ : Measure α) [IsProbabilityMeasure μ] :
    iIndepFun (fun i : ι ↦ (coord i : (ι → α) → α)) (fieldMeasure μ) := by
  have h := iIndepFun_infinitePi (Ω := fun _ : ι ↦ α) (P := fun _ : ι ↦ μ)
    (X := fun _ : ι ↦ (id : α → α)) (fun _ ↦ measurable_id)
  exact h

/-- **The one-coordinate law.** The pushforward of the field measure under a
coordinate is `μ`; the coordinates are identically distributed. -/
theorem map_coord (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
    (fieldMeasure (ι := ι) μ).map (coord i) = μ :=
  Measure.infinitePi_map_eval (fun _ : ι ↦ μ) i

/-- The set form of the one-coordinate law. -/
theorem coord_law (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {s : Set α}
    (hs : MeasurableSet s) : fieldMeasure (ι := ι) μ (coord i ⁻¹' s) = μ s := by
  rw [← Measure.map_apply (measurable_coord i) hs, map_coord]

end Field

section Bernoulli

variable {ι : Type*} {t : ℝ}

/-- The Bernoulli law on `Bool` with success probability `t`: mass `t` at `true`
and `1 - t` at `false`. -/
noncomputable def bernoulliLaw (ht : 0 ≤ t) (ht1 : t ≤ 1) : Measure Bool :=
  bernoulliMeasure true false ⟨t, ht, ht1⟩

instance isProbabilityMeasure_bernoulliLaw (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (bernoulliLaw ht ht1) :=
  inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure true false ⟨t, ht, ht1⟩))

/-- The Bernoulli law gives mass `t` to `{true}`. -/
lemma bernoulliLaw_apply_true (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    bernoulliLaw ht ht1 {true} = ENNReal.ofReal t := by
  show bernoulliMeasure true false ⟨t, ht, ht1⟩ {true} = ENNReal.ofReal t
  rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton true) rfl (by simp),
    ENNReal.ofReal_eq_coe_nnreal ht]
  rfl

/-- The Bernoulli field: the i.i.d. field on `ι → Bool` whose coordinates are
Bernoulli with success probability `t`. -/
noncomputable def bernoulliField (ht : 0 ≤ t) (ht1 : t ≤ 1) : Measure (ι → Bool) :=
  fieldMeasure (bernoulliLaw ht ht1)

instance isProbabilityMeasure_bernoulliField (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (bernoulliField (ι := ι) ht ht1) :=
  inferInstanceAs (IsProbabilityMeasure (fieldMeasure (bernoulliLaw ht ht1)))

/-- Every coordinate of the Bernoulli field is measurable. -/
lemma measurable_bernoulliField_coord (i : ι) : Measurable (coord i : (ι → Bool) → Bool) :=
  measurable_coord i

/-- The coordinates of the Bernoulli field are independent. -/
theorem bernoulliField_iIndepFun (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    iIndepFun (fun i : ι ↦ (coord i : (ι → Bool) → Bool)) (bernoulliField ht ht1) :=
  coord_iIndepFun (bernoulliLaw ht ht1)

/-- Each coordinate of the Bernoulli field is open with probability `t`. -/
theorem bernoulliField_apply_true (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : ι) :
    bernoulliField ht ht1 {ω : ι → Bool | ω i = true} = ENNReal.ofReal t := by
  show fieldMeasure (bernoulliLaw ht ht1) (coord i ⁻¹' {true}) = ENNReal.ofReal t
  rw [coord_law _ i (measurableSet_singleton true), bernoulliLaw_apply_true]

/-- **The Bernoulli field exists in the packaged shape.** For `0 ≤ t ≤ 1` and an
arbitrary index type `ι` there is a probability space carrying a measurable,
independent family of `Bool`-valued coordinates, each open with probability `t`.
The space is `ι → Bool` under `bernoulliField`, so it lives in the universe
of `ι`. -/
theorem exists_bernoulli_field (ι : Type u) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ι → Ω → Bool),
      (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
      (∀ i, P {ω | X i ω = true} = ENNReal.ofReal t) :=
  ⟨ι → Bool, inferInstance, bernoulliField ht ht1, inferInstance, fun i ↦ coord i,
    fun i ↦ measurable_bernoulliField_coord i, bernoulliField_iIndepFun ht ht1,
    fun i ↦ bernoulliField_apply_true ht ht1 i⟩

end Bernoulli

end BranchingProcess
