import BranchingProcess.Progeny
import ChainClasses.Scalar.ShapeEta
import ChainClasses.Bushy.ShapeMassPoint

/-!
`sec:shape-harris` of `matching_classes_simple.tex`: the two inputs `thm:shape-mass` takes
from the bushes, the point mass of a prescribed bush and the exponential tail of its size.

`ShapeMassPoint` factorises the mass of a shape into one factor per vertex and carries the
bush input as the hypothesis `BushPointBound`; `ShapeMass` carries the tail clause over an
exponential moment.  Both are discharged here against `BranchingProcess.Progeny`.  A finite
tree is presented by the offspring field cutting it out, and a field agreeing with that one
on the tree cuts out the same tree, so the point mass of a bush is the mass of a cylinder
event.  Reading a bush off a field asks for the offspring bound at every vertex, which
holds almost surely, so the mass is unchanged by intersecting with that event.  The bush of
a field is its sample, so the size of a bush is the number of vertices of the sample, and
the conjugate law of a hairy law is subcritical, which is what the exponential moment of
the total progeny asks for.

* `Tri.ext_isAddr`: **extensionality by addresses**, two finite trees with the same
  addresses are the same tree.
* `bitOf`, `bits`: the ambient alphabet read as bits, inverse to `letters`.
* `Tri.addrSet`, `Tri.mem_addrSet`, `Tri.card_addrSet`: the vertices of a finite tree and
  their number.
* `Tri.count`, `Tri.mem_sample_count`, `Tri.ncard_sample_count`:
  **the field of a finite tree**, the offspring counts cutting it out.
* `bushMeasure_offspring_le`, `bushMeasure_survives`: the two null events of the bush law,
  the support bound and survival.
* `bushPointBound`: **the bush input of
  `thm:shape-mass` (`it:shape-mass-point`)**, the hypothesis `BushPointBound`
  discharged.
* `size_bushTri`: **the size of a bush**, the number of vertices of the sample.
* `mul_extinction_eq`, `pos_two_of_extinction_pos`, `conjugate_isSubcritical`: **the
  conjugate law is subcritical**, its mean being `f'(q) = θ₁ + 2θ₂q = θ₁ + 2θ₀ = θ̃₁`.
* `bushSizeMass`, `lintegral_pow_ncard_eq_tsum`, `summable_bushSizeMass_mgf`: **the
  exponential moment of the size of a bush** as the real series `chernoff_tail` consumes,
  the integral read as a sum over the possible sizes.
* `exists_bush_size_tail`: **the exponential tail of the size of a bush**, the input
  `thm:shape-mass` (`it:shape-mass-tail`) takes from
  `thm:harris` (`it:harris-bushes`).
* `ofReal_pow_size_le_shapeMass_of_weights`:
  **`thm:shape-mass` (`it:shape-mass-point`)** at the shape law, over the
  offspring weights alone.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (sample Survives sampleMeasure bushMeasure Offspring)
open scoped ENNReal

/-! ### Finite trees are determined by their addresses -/

/-- **Extensionality by addresses**: two finite trees with the same addresses are the
same tree. -/
theorem Tri.ext_isAddr : ∀ (s t : Tri), (∀ a : Word, s.IsAddr a ↔ t.IsAddr a) → s = t := by
  intro s
  induction s with
  | leaf =>
      intro t h
      cases t with
      | leaf => rfl
      | one t => exact absurd ((h [false]).mpr (by simp)) (by simp)
      | two l r => exact absurd ((h [false]).mpr (by simp)) (by simp)
  | one s ih =>
      intro t h
      cases t with
      | leaf => exact absurd ((h [false]).mp (by simp)) (by simp)
      | one t => rw [ih t fun a ↦ by simpa using h (false :: a)]
      | two l r => exact absurd ((h [true]).mpr (by simp)) (by simp)
  | two sl sr ihl ihr =>
      intro t h
      cases t with
      | leaf => exact absurd ((h [false]).mp (by simp)) (by simp)
      | one t => exact absurd ((h [true]).mp (by simp)) (by simp)
      | two l r =>
          rw [ihl l fun a ↦ by simpa using h (false :: a),
            ihr r fun a ↦ by simpa using h (true :: a)]

/-! ### The two alphabets -/

/-- The letter of the ambient alphabet read as a bit, inverse to `letterOf`. -/
def bitOf (i : Fin 2) : Bool := decide (i = 1)

@[simp] lemma letterOf_bitOf (i : Fin 2) : letterOf (bitOf i) = i := by revert i; decide

@[simp] lemma bitOf_letterOf (b : Bool) : bitOf (letterOf b) = b := by cases b <;> rfl

/-- An ambient address read as a word of the index alphabet. -/
def bits (v : Amb) : Word := v.map bitOf

@[simp] lemma bits_nil : bits [] = [] := rfl

@[simp] lemma bits_cons (i : Fin 2) (v : Amb) : bits (i :: v) = bitOf i :: bits v := rfl

@[simp] lemma letters_bits (v : Amb) : letters (bits v) = v := by
  have h : letterOf ∘ bitOf = id := funext letterOf_bitOf
  rw [letters, bits, List.map_map, h, List.map_id]

@[simp] lemma bits_letters (a : Word) : bits (letters a) = a := by
  have h : bitOf ∘ letterOf = id := funext bitOf_letterOf
  rw [letters, bits, List.map_map, h, List.map_id]

lemma fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by revert i; decide

@[simp] lemma bitOf_zero : bitOf 0 = false := rfl

@[simp] lemma bitOf_one : bitOf 1 = true := rfl

/-! ### The vertices of a finite tree -/

/-- The vertices of a finite tree, named by their addresses in the ambient alphabet. -/
def Tri.addrSet : Tri → Finset Amb
  | .leaf => {[]}
  | .one t => insert [] (t.addrSet.image fun w ↦ (0 : Fin 2) :: w)
  | .two l r =>
      insert [] ((l.addrSet.image fun w ↦ (0 : Fin 2) :: w)
        ∪ (r.addrSet.image fun w ↦ (1 : Fin 2) :: w))

lemma Tri.mem_addrSet : ∀ (t : Tri) (v : Amb), v ∈ t.addrSet ↔ t.IsAddr (bits v) := by
  intro t
  induction t with
  | leaf =>
      intro v
      cases v with
      | nil => simp [addrSet]
      | cons i u => simp [addrSet]
  | one t ih =>
      intro v
      cases v with
      | nil => simp [addrSet]
      | cons i u =>
          rcases fin_two_cases i with rfl | rfl <;> simp [addrSet, ih]
  | two l r ihl ihr =>
      intro v
      cases v with
      | nil => simp [addrSet]
      | cons i u =>
          rcases fin_two_cases i with rfl | rfl <;> simp [addrSet, ihl, ihr]

lemma amb_cons_injective (i : Fin 2) : Function.Injective (fun w : Amb ↦ i :: w) := by
  intro a b h
  simpa using h

lemma Tri.card_addrSet : ∀ t : Tri, t.addrSet.card = t.size := by
  intro t
  induction t with
  | leaf => rfl
  | one t ih =>
      have hnot : ([] : Amb) ∉ t.addrSet.image fun w ↦ (0 : Fin 2) :: w := by simp
      rw [addrSet, Finset.card_insert_of_notMem hnot,
        Finset.card_image_of_injective _ (amb_cons_injective 0), ih, Tri.size]
      omega
  | two l r ihl ihr =>
      have hdisj : Disjoint (l.addrSet.image fun w ↦ (0 : Fin 2) :: w)
          (r.addrSet.image fun w ↦ (1 : Fin 2) :: w) := by
        refine Finset.disjoint_left.mpr fun v hv hv' ↦ ?_
        simp only [Finset.mem_image] at hv hv'
        obtain ⟨a, -, rfl⟩ := hv
        obtain ⟨b, -, hb⟩ := hv'
        simp at hb
      have hnot : ([] : Amb) ∉ (l.addrSet.image fun w ↦ (0 : Fin 2) :: w)
          ∪ (r.addrSet.image fun w ↦ (1 : Fin 2) :: w) := by simp
      rw [addrSet, Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (amb_cons_injective 0),
        Finset.card_image_of_injective _ (amb_cons_injective 1), ihl, ihr, Tri.size]
      omega

/-! ### The field cutting out a finite tree -/

/-- The offspring field of a finite tree: the number of children at each of its
vertices, and none off the tree. -/
def Tri.count : Tri → Amb → ℕ
  | .leaf, _ => 0
  | .one _, [] => 1
  | .one t, i :: w => if i = 0 then t.count w else 0
  | .two _ _, [] => 2
  | .two l r, i :: w => if i = 0 then l.count w else r.count w

@[simp] lemma Tri.count_leaf (v : Amb) : Tri.leaf.count v = 0 := rfl

@[simp] lemma Tri.count_one_nil (t : Tri) : (Tri.one t).count [] = 1 := rfl

@[simp] lemma Tri.count_two_nil (l r : Tri) : (Tri.two l r).count [] = 2 := rfl

lemma Tri.count_one_cons (t : Tri) (i : Fin 2) (w : Amb) :
    (Tri.one t).count (i :: w) = if i = 0 then t.count w else 0 := rfl

lemma Tri.count_two_cons (l r : Tri) (i : Fin 2) (w : Amb) :
    (Tri.two l r).count (i :: w) = if i = 0 then l.count w else r.count w := rfl

lemma Tri.count_le_two : ∀ (t : Tri) (v : Amb), t.count v ≤ 2 := by
  intro t
  induction t with
  | leaf => intro v; simp
  | one t ih =>
      intro v
      cases v with
      | nil => simp
      | cons i w =>
          rw [Tri.count_one_cons]
          split
          · exact ih w
          · omega
  | two l r ihl ihr =>
      intro v
      cases v with
      | nil => simp
      | cons i w =>
          rw [Tri.count_two_cons]
          split
          · exact ihl w
          · exact ihr w

@[simp] lemma Tri.shift_count_one (t : Tri) : shift (Tri.one t).count [0] = t.count := rfl

@[simp] lemma Tri.shift_count_two_zero (l r : Tri) :
    shift (Tri.two l r).count [0] = l.count := rfl

@[simp] lemma Tri.shift_count_two_one (l r : Tri) :
    shift (Tri.two l r).count [1] = r.count := rfl

/-- **The field cuts out the tree**: the vertices of the sample of `Tri.count t` are the
addresses of `t`. -/
lemma Tri.mem_sample_count : ∀ (t : Tri) (v : Amb), v ∈ sample t.count ↔ t.IsAddr (bits v) := by
  intro t
  induction t with
  | leaf =>
      intro v
      cases v with
      | nil => simp
      | cons i u => rw [mem_sample_cons]; simp
  | one t ih =>
      intro v
      cases v with
      | nil => simp
      | cons i u =>
          rw [mem_sample_cons]
          rcases fin_two_cases i with rfl | rfl <;> simp [ih u]
  | two l r ihl ihr =>
      intro v
      cases v with
      | nil => simp
      | cons i u =>
          rw [mem_sample_cons]
          rcases fin_two_cases i with rfl | rfl <;> simp [ihl u, ihr u]

lemma Tri.coe_sample_count (t : Tri) : (sample t.count : Set Amb) = (t.addrSet : Set Amb) := by
  ext v
  simp only [SetLike.mem_coe, Tri.mem_addrSet, Tri.mem_sample_count]

lemma Tri.finite_sample_count (t : Tri) : (sample t.count : Set Amb).Finite := by
  rw [Tri.coe_sample_count]
  exact t.addrSet.finite_toSet

/-- The sample of the field of a tree has as many vertices as the tree. -/
lemma Tri.ncard_sample_count (t : Tri) : (sample t.count : Set Amb).ncard = t.size := by
  rw [Tri.coe_sample_count, Set.ncard_coe_finset, Tri.card_addrSet]

/-! ### The two null events of the bush law -/

/-- Conditioning on extinction keeps the null events of the sample law null. -/
lemma bushMeasure_absolutelyContinuous (θ : Offspring 2) :
    bushMeasure (N := 2) θ ≪ sampleMeasure (N := 2) θ :=
  ProbabilityTheory.cond_absolutelyContinuous

/-- Almost every bush is supported on `{0,1,2}`, which is what reading a bush off a field
asks for. -/
lemma bushMeasure_offspring_le (θ : Offspring 2) :
    bushMeasure (N := 2) θ {c : Amb → ℕ | ¬ ∀ v, c v ≤ 2} = 0 :=
  bushMeasure_absolutelyContinuous θ (sampleMeasure_offspring_le θ)

/-- Almost every bush dies: the law is conditioned on exactly that. -/
lemma bushMeasure_survives (θ : Offspring 2) :
    bushMeasure (N := 2) θ {c : Amb → ℕ | Survives c} = 0 := by
  have hempty : {c : Amb → ℕ | ¬ Survives c} ∩ {c : Amb → ℕ | Survives c}
      = (∅ : Set (Amb → ℕ)) := by
    ext c
    simp
  rw [BranchingProcess.bushMeasure_apply, hempty, measure_empty, mul_zero]

/-! ### The point mass of a bush -/

/-- **`thm:shape-mass` (`it:shape-mass-point`), the bush input**: a bush of `n`
vertices has mass at least `p^n`, `p` a lower bound for the three offspring weights.  The
field of the tree cuts it out, and a field agreeing with it on the tree cuts out the same
tree; almost surely the field is supported on `{0,1,2}`, which is what reading the bush
off the sample asks for. -/
theorem bushPointBound (θ : Offspring 2) {p : ℝ} (hp0 : 0 ≤ p) (h0 : p ≤ θ 0)
    (h1 : p ≤ θ 1) (h2 : p ≤ θ 2) : BushPointBound θ p := by
  have hnull := bushMeasure_offspring_le θ
  intro t
  have hfin := t.finite_sample_count
  have hmass : ∀ v ∈ sample t.count, p ≤ θ (t.count v) := by
    intro v _
    have hle := t.count_le_two v
    have hcases : t.count v = 0 ∨ t.count v = 1 ∨ t.count v = 2 := by omega
    rcases hcases with h | h | h <;> rw [h] <;> assumption
  have hbase := BranchingProcess.ofReal_pow_le_bushMeasure_sample_eq (N := 2) θ hfin hmass
  have hsub : {c : Amb → ℕ | (sample c : Set Amb) = (sample t.count : Set Amb)}
      \ {c : Amb → ℕ | ¬ ∀ v, c v ≤ 2} ⊆ {d : Amb → ℕ | bushTri d = t} := by
    rintro c ⟨hc, hc2⟩
    have hd : ∀ v, c v ≤ 2 := not_not.mp hc2
    have hcfin : ¬ Survives c := by
      rw [Survives, hc]
      exact Set.not_infinite.mpr hfin
    refine Tri.ext_isAddr _ _ fun a ↦ ?_
    have hmem := Set.ext_iff.mp hc (letters a)
    simp only [SetLike.mem_coe] at hmem
    rw [isAddr_bushTri hd hcfin a, hmem, Tri.mem_sample_count, bits_letters]
  calc ENNReal.ofReal (p ^ t.size)
      = ENNReal.ofReal p ^ t.size := ENNReal.ofReal_pow hp0 _
    _ = ENNReal.ofReal p ^ (sample t.count : Set Amb).ncard := by rw [t.ncard_sample_count]
    _ ≤ bushMeasure (N := 2) θ
          {c : Amb → ℕ | (sample c : Set Amb) = (sample t.count : Set Amb)} := hbase
    _ = bushMeasure (N := 2) θ
          ({c : Amb → ℕ | (sample c : Set Amb) = (sample t.count : Set Amb)}
            \ {c : Amb → ℕ | ¬ ∀ v, c v ≤ 2}) := (measure_sdiff_null hnull).symm
    _ ≤ bushMeasure (N := 2) θ {d : Amb → ℕ | bushTri d = t} := measure_mono hsub

/-! ### The size of a bush -/

/-- **The bush has as many vertices as the subtree it reads**: the addresses of the bush
of a dying field are the vertices of its sample. -/
theorem size_bushTri {d : Amb → ℕ} (hd : ∀ v, d v ≤ 2) (hfin : ¬ Survives d) :
    (bushTri d).size = (sample d : Set Amb).ncard := by
  have hset : ((bushTri d).addrSet : Set Amb) = (sample d : Set Amb) := by
    ext v
    simp only [SetLike.mem_coe, Tri.mem_addrSet]
    rw [isAddr_bushTri hd hfin (bits v), letters_bits]
  rw [← Tri.card_addrSet, ← Set.ncard_coe_finset, hset]

/-! ### The conjugate law is subcritical -/

/-- The generating function of a law on `{0,1,2}`, written out. -/
lemma gen_eq_of_two (θ : Offspring 2) (s : ℝ) :
    Offspring.gen θ s = θ 0 + θ 1 * s + θ 2 * s ^ 2 := by
  rw [Offspring.gen, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

/-- The weights of a law on `{0,1,2}` sum to one. -/
lemma total_of_two (θ : Offspring 2) : θ 0 + θ 1 + θ 2 = 1 := by
  have h := θ.total
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  linarith

/-- **The extinction probability of a hairy law is `θ₀/θ₂`**, in the form
`θ₂q = θ₀`: the fixed-point equation factors as `(s-1)(θ₂s-θ₀)`, and `q < 1`. -/
lemma mul_extinction_eq (θ : Offspring 2) (hq : θ.extinction < 1) :
    θ 2 * θ.extinction = θ 0 := by
  have hfix : θ 0 + θ 1 * θ.extinction + θ 2 * θ.extinction ^ 2 = θ.extinction := by
    rw [← gen_eq_of_two]
    exact θ.gen_extinction
  have htot := total_of_two θ
  have hfac : (θ.extinction - 1) * (θ 2 * θ.extinction - θ 0) = 0 := by
    linear_combination hfix - θ.extinction * htot
  have hne : θ.extinction - 1 ≠ 0 := by linarith
  have := mul_eq_zero.mp hfac
  rcases this with h | h
  · exact absurd h hne
  · linarith

/-- Positive extinction forces a positive weight at two: otherwise `θ₀ = θ₂q = 0`. -/
lemma pos_two_of_extinction_pos (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) : 0 < θ 2 := by
  rcases lt_or_eq_of_le (θ.nonneg 2) with h | h
  · exact h
  · exfalso
    have h0 : θ 0 = 0 := by
      have := mul_extinction_eq θ hq
      rw [← h] at this
      linarith
    exact absurd (θ.extinction_eq_zero_iff.mpr h0) hq0.ne'

/-- **`thm:harris` (`it:harris-bushes`), the arithmetic**: the conjugate law of a
hairy offspring law is subcritical.  Its mean is `f'(q) = θ₁ + 2θ₂q = θ₁ + 2θ₀`, which is
the skeleton weight `θ̃₁`, and `θ₀ < θ₂` because `q < 1`. -/
theorem conjugate_isSubcritical (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) : (θ.conjugate hq0).IsSubcritical := by
  have hq0' : θ.extinction ≠ 0 := hq0.ne'
  have hkey := mul_extinction_eq θ hq
  have htot := total_of_two θ
  have h2 := pos_two_of_extinction_pos θ hq hq0
  have hmean : Offspring.mean (θ.conjugate hq0) = θ 1 + 2 * θ 0 := by
    rw [Offspring.mean, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [Offspring.conjugate_apply, Offspring.conjugateWeight]
    have e1 : θ 1 * θ.extinction ^ 1 / θ.extinction = θ 1 := by
      rw [pow_one, mul_div_assoc, div_self hq0', mul_one]
    have e2 : θ 2 * θ.extinction ^ 2 / θ.extinction = θ 0 := by
      rw [pow_two, ← mul_assoc, hkey, mul_div_assoc, div_self hq0', mul_one]
    rw [e1, e2]
    push_cast
    ring
  have hlt : θ 0 < θ 2 := by
    rw [← hkey]
    nlinarith
  show Offspring.mean (θ.conjugate hq0) < 1
  rw [hmean]
  linarith

/-! ### The exponential moment of the size of a bush as a sum -/

/-- The size of a bush is a random variable. -/
lemma measurable_ncard_sample :
    Measurable fun c : Amb → ℕ ↦ (sample c : Set Amb).ncard :=
  (measurable_to_countable' fun n ↦ BranchingProcess.measurableSet_ncard_eq n).comp
    BranchingProcess.measurable_sample

/-- The law of the size of a bush. -/
noncomputable def bushSizeMass (θ : Offspring 2) (n : ℕ) : ℝ :=
  (bushMeasure (N := 2) θ {c : Amb → ℕ | (sample c : Set Amb).ncard = n}).toReal

lemma bushSizeMass_nonneg (θ : Offspring 2) (n : ℕ) : 0 ≤ bushSizeMass θ n :=
  ENNReal.toReal_nonneg

/-- **The exponential moment read off the law of the size**: the integral is the sum over
the possible sizes. -/
lemma lintegral_pow_ncard_eq_tsum (θ : Offspring 2) (s : ℝ≥0∞) :
    ∫⁻ c, s ^ ((sample c : Set Amb).ncard) ∂(bushMeasure (N := 2) θ)
      = ∑' n : ℕ, s ^ n
          * bushMeasure (N := 2) θ {c : Amb → ℕ | (sample c : Set Amb).ncard = n} := by
  have hmeas : Measurable fun c : Amb → ℕ ↦ (sample c : Set Amb).ncard :=
    measurable_ncard_sample
  have h1 : ∫⁻ c, s ^ ((sample c : Set Amb).ncard) ∂(bushMeasure (N := 2) θ)
      = ∫⁻ n : ℕ, s ^ n
          ∂((bushMeasure (N := 2) θ).map fun c ↦ (sample c : Set Amb).ncard) :=
    (lintegral_map Measurable.of_discrete hmeas).symm
  rw [h1, lintegral_countable']
  refine tsum_congr fun n ↦ ?_
  rw [Measure.map_apply hmeas (measurableSet_singleton n)]
  rfl

/-- **The exponential moment in the form `chernoff_tail` consumes**: a finite moment
`∫ σ^{|T|}` is a summable real series over the possible sizes, and its sum is the
integral. -/
theorem summable_bushSizeMass_mgf (θ : Offspring 2) (hq0 : 0 < θ.extinction) {t : ℝ}
    (hmom : ∫⁻ c, ENNReal.ofReal (Real.exp t) ^ ((sample c : Set Amb).ncard)
        ∂(bushMeasure (N := 2) θ) ≠ ⊤) :
    Summable (fun n : ℕ ↦ Real.exp (t * (n : ℝ)) * bushSizeMass θ n) ∧
      ∑' n : ℕ, Real.exp (t * (n : ℝ)) * bushSizeMass θ n
        = (∫⁻ c, ENNReal.ofReal (Real.exp t) ^ ((sample c : Set Amb).ncard)
            ∂(bushMeasure (N := 2) θ)).toReal := by
  have _ := BranchingProcess.isProbabilityMeasure_bushMeasure θ le_rfl hq0
  set G : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (Real.exp t) ^ n
      * bushMeasure (N := 2) θ {c : Amb → ℕ | (sample c : Set Amb).ncard = n} with hG
  have hsum : ∑' n, G n
      = ∫⁻ c, ENNReal.ofReal (Real.exp t) ^ ((sample c : Set Amb).ncard)
          ∂(bushMeasure (N := 2) θ) := (lintegral_pow_ncard_eq_tsum θ _).symm
  have hne : ∀ n, G n ≠ ⊤ := fun n ↦
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  have htoReal : ∀ n : ℕ, (G n).toReal = Real.exp (t * (n : ℝ)) * bushSizeMass θ n := by
    intro n
    rw [hG]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (Real.exp_pos t).le, exp_mul_nat]
    rfl
  have hsummable : Summable fun n : ℕ ↦ (G n).toReal :=
    ENNReal.summable_toReal (by rw [hsum]; exact hmom)
  constructor
  · exact hsummable.congr htoReal
  · rw [← hsum, ENNReal.tsum_toReal_eq hne]
    exact tsum_congr fun n ↦ (htoReal n).symm

/-! ### The exponential tail of the size of a bush -/

/-- **`thm:shape-mass` (`it:shape-mass-tail`) for the bushes**: the size of a bush
has an exponential tail.  The conjugate law is subcritical, so its total progeny has an
exponential moment, and `shape_mass_tail` absorbs the moment constant past a threshold. -/
theorem exists_bush_size_tail (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      ∑' k : ℕ, bushSizeMass θ (k + N) ≤ Real.exp (-c * (N : ℝ)) := by
  have _ := BranchingProcess.isProbabilityMeasure_bushMeasure θ le_rfl hq0
  obtain ⟨s, hs1, hmom⟩ := BranchingProcess.exists_exponential_moment_bushMeasure θ le_rfl hq0
    (conjugate_isSubcritical θ hq hq0)
  set t : ℝ := Real.log s with ht_def
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  have hexp : Real.exp t = s := Real.exp_log hs0
  have ht : 0 < t := Real.log_pos hs1
  rw [← hexp] at hmom
  have hmomne := hmom.ne
  set M : ℝ := (∫⁻ c, ENNReal.ofReal (Real.exp t) ^ ((sample c : Set Amb).ncard)
      ∂(bushMeasure (N := 2) θ)).toReal with hM_def
  have hone : (1 : ℝ≥0∞) ≤ ∫⁻ c, ENNReal.ofReal (Real.exp t) ^ ((sample c : Set Amb).ncard)
      ∂(bushMeasure (N := 2) θ) := by
    have hle : ∀ c : Amb → ℕ,
        (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp t) ^ ((sample c : Set Amb).ncard) := by
      intro c
      refine one_le_pow₀ ?_
      rw [← ENNReal.ofReal_one, hexp]
      exact ENNReal.ofReal_le_ofReal hs1.le
    calc (1 : ℝ≥0∞) = ∫⁻ _ : Amb → ℕ, 1 ∂(bushMeasure (N := 2) θ) := by simp
      _ ≤ _ := lintegral_mono hle
  have hM1 : (1 : ℝ) ≤ M := by
    have h := ENNReal.toReal_mono hmomne hone
    rw [ENNReal.toReal_one] at h
    rw [hM_def]
    exact h
  obtain ⟨hsummable, hsumeq⟩ := summable_bushSizeMass_mgf θ hq0 hmomne
  refine ⟨t / 2, by linarith, ⌈2 * Real.log M / t⌉₊, fun N hN ↦ ?_⟩
  have hNge : 2 * Real.log M / t ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNt : 2 * Real.log M ≤ t * (N : ℝ) := by
    rw [div_le_iff₀ ht] at hNge
    linarith
  have hMle : ∑' n : ℕ, Real.exp (t * (n : ℝ)) * bushSizeMass θ n ≤ M := le_of_eq hsumeq
  exact shape_mass_tail ht hM1 (bushSizeMass_nonneg θ) hsummable hMle hNt

/-! ### The point clause of `thm:shape-mass` with the bush input discharged -/

/-- The decoration weight of a bush is `2θ₀`: the extinction probability satisfies
`θ₂q = θ₀`. -/
lemma decoration_weight_eq (θ : Offspring 2) (hq : θ.extinction < 1) :
    θ 2 * 2 * θ.extinction = 2 * θ 0 := by
  have h := mul_extinction_eq θ hq
  linarith [h]

/-- **`thm:shape-mass` (`it:shape-mass-point`)** at the shape law, over the
offspring weights alone: the mass of a shape is at least `p` to its size, `p` a positive
lower bound for `θ₀`, `θ₁`, `θ₂` and the split weight `θ̃₂`. -/
theorem ofReal_pow_size_le_shapeMass_of_weights (θ : Offspring 2) (hq : θ.extinction < 1)
    {p : ℝ} (hp0 : 0 < p) (h0 : p ≤ θ 0) (h1 : p ≤ θ 1) (h2 : p ≤ θ 2)
    (hk : p ≤ θ.skeletonWeight 2) (σ : Shape) :
    ENNReal.ofReal (p ^ σ.size) ≤ shapeMass θ σ := by
  have hd : p ≤ θ 2 * 2 * θ.extinction := by
    rw [decoration_weight_eq θ hq]
    linarith [θ.nonneg 0]
  exact ofReal_pow_size_le_shapeMass hp0 h1 hd hk (bushPointBound θ hp0.le h0 h1 h2) σ

end ChainClasses
