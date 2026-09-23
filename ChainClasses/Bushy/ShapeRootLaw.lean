import ChainClasses.Bushy.ShapeLaw
import BranchingProcess.Decorated

/-!
`sec:shape-harris` of `matching_classes_simple.tex`: the law of the shape at the root,
the law `μ` of `thm:shape-iid`.

`ShapeLaw` has the neck length, which the branching property of the skeleton gives on its
own.  The decorations need the joint law of the surviving and the dying subtree at a neck
vertex, which is `BranchingProcess.Decorated`.  Read in the shape, that law is the step
of a recursion: conditioned on survival, a root with one skeleton child carries its
decoration with mass `decMass` and hands the rest of the chain to its surviving subtree,
an independent copy of the conditioned law.  Iterating along the chain and closing at the
split gives the mass of `thm:shape-iid`, one decoration factor per neck vertex and the
split weight `θ̃₂` at the end.

The events of the recursion are the ones of `ShapeDecomposition`, so they carry the junk
of an offspring count above the support bound; every step is therefore taken modulo the
event `IsBushySample`, which `ae_isBushySample_of_pos` gives full measure.

* `measure_eq_of_inter_ae`: two events agreeing on an event of full measure have the same
  mass, the form every step below is transported in.
* `bushLetter_notMem_survivors`, `eq_bushLetter_of_notMem`, `decAt_shift`: the decoration
  of the root as the dying child, and the decoration read in a subtree.
* `decMass`: **the mass of a decoration**, `θ₁` for no bush and `2θ₂q` times the bush law
  of the tree it realises otherwise.
* `survivalMeasure_neck_step`: **`thm:harris` (`it:harris-bushes`) in the
  shape**, the decorated neck step.
* `neckRay_shift_base`, `splitDepth_bushAt`,
  `decAt_neckRay_succ`: the chain of the root one step down, and the hypotheses of
  `sec:shapes` inherited by the surviving subtree.
* `Shape.eq_of_decs`, `decs_shapeAt_nil_cons`: a shape is its list of decorations, and
  **the recursion of the shape at the root**.
* `survivalMeasure_decs_shapeAt_nil` and `survivalMeasure_shapeAt_nil`:
  **`thm:shape-iid`, the shape law at the root**.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (sample Survives survivors skeletonDegree Offspring sampleMeasure
  survivalMeasure bushMeasure bushAt)

/-! ### Events that differ inside a null set -/

/-- Two events agreeing on an event of full measure have the same mass. -/
lemma measure_eq_of_inter_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {s E E' : Set α}
    (hs : μ sᶜ = 0) (h : E ∩ s = E' ∩ s) : μ E = μ E' := by
  refine measure_congr (Filter.eventuallyEqSet_iff.mpr ?_)
  have hmem : ∀ᵐ x ∂μ, x ∈ s := by
    rw [ae_iff]
    exact hs
  filter_upwards [hmem] with x hx
  constructor
  · intro hE
    have hx' : x ∈ E ∩ s := ⟨hE, hx⟩
    rw [h] at hx'
    exact hx'.1
  · intro hE'
    have hx' : x ∈ E' ∩ s := ⟨hE', hx⟩
    rw [← h] at hx'
    exact hx'.1

/-! ### The decoration of the root -/

variable {c : Amb → ℕ}

/-- At a neck vertex with two children the bush letter names the dying one. -/
lemma bushLetter_notMem_survivors (hdeg : skeletonDegree c = 1) (h2 : c [] = 2) :
    bushLetter c [] ∉ survivors c := by
  have hsurv : Survives (shift c []) := by
    simpa using BranchingProcess.survives_iff_skeletonDegree_ne_zero.mpr (by omega : skeletonDegree c ≠ 0)
  have hfin := not_survives_bush hsurv (by simpa using hdeg) (by simpa using h2)
  intro hmem
  have hmem' : bushLetter c [] ∈ survivors (shift c []) := by simpa using hmem
  exact hfin (by simpa using (mem_survivors_shift.mp hmem').2)

/-- Two letters differing from a third agree: the alphabet has two letters. -/
lemma eq_of_ne_of_ne {x y z : Fin 2} (hx : x ≠ z) (hy : y ≠ z) : x = y := by
  have hall : ∀ x y z : Fin 2, x ≠ z → y ≠ z → x = y := by decide
  exact hall x y z hx hy

/-- At a neck vertex with two children the dying child is the bush letter. -/
lemma eq_bushLetter_of_notMem (hdeg : skeletonDegree c = 1) {i : Fin 2}
    (hi : i ∉ survivors c) : i = bushLetter c [] := by
  have hsurv : Survives (shift c []) := by
    simpa using BranchingProcess.survives_iff_skeletonDegree_ne_zero.mpr (by omega : skeletonDegree c ≠ 0)
  have hn : neckLetter c [] ∈ survivors c := by
    simpa using neckLetter_mem_survivors hsurv
  have hb : bushLetter c [] ≠ neckLetter c [] := bushLetter_ne_neckLetter c []
  have hine : i ≠ neckLetter c [] := fun h ↦ hi (h ▸ hn)
  exact eq_of_ne_of_ne hine hb

/-- The decoration read in a subtree. -/
lemma decAt_shift (c : Amb → ℕ) (v u : Amb) : decAt (shift c v) u = decAt c (v ++ u) := by
  rw [decAt, decAt, shift_apply, bushLetter, bushLetter, shift_shift, shift_shift,
    ← List.append_assoc]

/-- **The mass of a decoration**: no bush contributes `θ₁`, a bush `2θ₂q` times the bush law of
the tree it realises. -/
noncomputable def decMass (θ : Offspring 2) : Option Tri → ENNReal
  | none => ENNReal.ofReal (θ 1)
  | some t =>
      ENNReal.ofReal (θ 2 * 2 * θ.extinction) * bushMeasure θ {d : Amb → ℕ | bushTri d = t}

/-- The bush of a field is a measurable function of it. -/
lemma measurableSet_bushTri_eq (t : Tri) : MeasurableSet {d : Amb → ℕ | bushTri d = t} :=
  ((fibreMeasurable_bushTri []).congr fun d ↦ by rw [shift_nil]) t

/-! ### The decorated neck step -/

/-- **`thm:harris` (`it:harris-bushes`) in the shape**: conditioned on survival,
a root with one skeleton child carries the decoration `o` with mass `decMass θ o`, and
the surviving subtree is an independent copy of the conditioned law. -/
theorem survivalMeasure_neck_step (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (o : Option Tri) {A : Set (Amb → ℕ)}
    (hA : MeasurableSet A) :
    survivalMeasure (N := 2) θ
        (({c : Amb → ℕ | skeletonDegree c = 1} ∩ {c : Amb → ℕ | decAt c [] = o})
          ∩ {c : Amb → ℕ | bushAt c 0 ∈ A})
      = decMass θ o * survivalMeasure (N := 2) θ A := by
  have hnull : survivalMeasure (N := 2) θ {c : Amb → ℕ | IsBushySample c}ᶜ = 0 := by
    have hae := ae_isBushySample_of_pos θ hq h2
    rw [ae_iff] at hae
    exact hae
  cases o with
  | none =>
      have hset : (({c : Amb → ℕ | skeletonDegree c = 1} ∩ {c : Amb → ℕ | decAt c [] = none})
            ∩ {c : Amb → ℕ | bushAt c 0 ∈ A}) ∩ {c : Amb → ℕ | IsBushySample c}
          = ((({c : Amb → ℕ | c [] = 1} ∩ {c : Amb → ℕ | skeletonDegree c = 1})
                ∩ {c : Amb → ℕ | bushAt c 0 ∈ A})
              ∩ {c : Amb → ℕ | ∀ i : Fin 2, i ∉ survivors c → (i : ℕ) < 1 →
                  (fun w : Amb ↦ c (i :: w)) ∈ (Set.univ : Set (Amb → ℕ))})
            ∩ {c : Amb → ℕ | IsBushySample c} := by
        ext c
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, implies_true, and_true]
        constructor
        · rintro ⟨⟨⟨hdeg, hdec⟩, hbush⟩, hbushy⟩
          have hne : c [] ≠ 2 := by
            by_contra hc
            rw [decAt, ite_eq_left hc] at hdec
            exact absurd hdec (by simp)
          have hsurv : Survives (shift c []) := by
            simpa using BranchingProcess.survives_iff_skeletonDegree_ne_zero.mpr
              (by omega : skeletonDegree c ≠ 0)
          have hone : c [] = 1 := by
            rcases eq_one_or_two_of_survives hbushy hsurv with h | h
            · simpa using h
            · exact absurd (by simpa using h) hne
          exact ⟨⟨⟨hone, hdeg⟩, hbush⟩, hbushy⟩
        · rintro ⟨⟨⟨hone, hdeg⟩, hbush⟩, hbushy⟩
          refine ⟨⟨⟨hdeg, ?_⟩, hbush⟩, hbushy⟩
          rw [decAt, ite_eq_right (by rw [hone]; omega)]
      rw [measure_eq_of_inter_ae hnull hset,
        BranchingProcess.survivalMeasure_root_one_survivor θ le_rfl hq hq0 (by norm_num) hA
          MeasurableSet.univ]
      simp [decMass]
  | some t =>
      have hset : (({c : Amb → ℕ | skeletonDegree c = 1} ∩ {c : Amb → ℕ | decAt c [] = some t})
            ∩ {c : Amb → ℕ | bushAt c 0 ∈ A}) ∩ {c : Amb → ℕ | IsBushySample c}
          = ((({c : Amb → ℕ | c [] = 2} ∩ {c : Amb → ℕ | skeletonDegree c = 1})
                ∩ {c : Amb → ℕ | bushAt c 0 ∈ A})
              ∩ {c : Amb → ℕ | ∀ i : Fin 2, i ∉ survivors c → (i : ℕ) < 2 →
                  (fun w : Amb ↦ c (i :: w)) ∈ {d : Amb → ℕ | bushTri d = t}})
            ∩ {c : Amb → ℕ | IsBushySample c} := by
        ext c
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨⟨hdeg, hdec⟩, hbush⟩, hbushy⟩
          have hc2 : c [] = 2 := by
            by_contra hc
            rw [decAt, ite_eq_right hc] at hdec
            exact absurd hdec (by simp)
          rw [decAt, ite_eq_left hc2] at hdec
          have htri : bushTri (shift c ([] ++ [bushLetter c []])) = t := by
            simpa using hdec
          refine ⟨⟨⟨⟨hc2, hdeg⟩, hbush⟩, fun i hi _ ↦ ?_⟩, hbushy⟩
          have hib : i = bushLetter c [] := eq_bushLetter_of_notMem hdeg hi
          have hshift : (fun w : Amb ↦ c (i :: w)) = shift c ([] ++ [bushLetter c []]) := by
            funext w
            rw [hib, shift_apply]
            rfl
          rw [hshift]
          exact htri
        · rintro ⟨⟨⟨⟨hc2, hdeg⟩, hbush⟩, hdying⟩, hbushy⟩
          refine ⟨⟨⟨hdeg, ?_⟩, hbush⟩, hbushy⟩
          have hnot := bushLetter_notMem_survivors hdeg hc2
          have hlt : (bushLetter c [] : ℕ) < 2 := (bushLetter c []).isLt
          have hval := hdying (bushLetter c []) hnot hlt
          rw [decAt, ite_eq_left hc2]
          have hshift : (fun w : Amb ↦ c (bushLetter c [] :: w))
              = shift c ([] ++ [bushLetter c []]) := by
            funext w
            rw [shift_apply]
            rfl
          rw [hshift] at hval
          rw [hval]
      rw [measure_eq_of_inter_ae hnull hset,
        BranchingProcess.survivalMeasure_root_one_survivor θ le_rfl hq hq0 (by norm_num) hA
          (measurableSet_bushTri_eq t)]
      rw [decMass]
      have hexp : (2 : ℕ) - 1 = 1 := rfl
      have hcast : θ 2 * ((2 : ℕ) : ℝ) = θ 2 * 2 := by norm_num
      rw [hexp, pow_one, pow_one, hcast]
      ring

/-! ### The chain of the root, one step down -/

/-- The neck ray of a vertex of a subtree, read in the whole sample. -/
lemma neckRay_shift_base (c : Amb → ℕ) (u v : Amb) :
    ∀ k, u ++ neckRay (shift c u) v k = neckRay c (u ++ v) k
  | 0 => rfl
  | k + 1 => by
      have ih := neckRay_shift_base c u v k
      rw [neckRay_succ, neckRay_succ, ← List.append_assoc, ih, neckLetter_shift, ih]

/-- **The chain of the root, one step down**: at a neck vertex the chain of the root is
one longer than the chain of the surviving subtree. -/
lemma splitDepth_bushAt {c : Amb → ℕ} (hc : IsBushySample c) (hdeg : skeletonDegree c = 1) :
    splitDepth c [] = splitDepth (bushAt c 0) [] + 1 := by
  have hroot : Survives (shift c []) := by simpa using hc.survives
  have hne : ∃ k, 2 ≤ skeletonDegree (shift c (neckRay c [] k)) := hc.splits [] hroot
  have hmem : 2 ≤ skeletonDegree (shift c (neckRay c [] (splitDepth c []))) :=
    Nat.sInf_mem hne
  have hzero : splitDepth c [] ≠ 0 := by
    intro h0
    rw [h0, neckRay_zero, shift_nil, hdeg] at hmem
    omega
  obtain ⟨m, hm⟩ : ∃ m, splitDepth c [] = m + 1 := ⟨splitDepth c [] - 1, by omega⟩
  have hmd : 2 ≤ skeletonDegree (shift (bushAt c 0) (neckRay (bushAt c 0) [] m)) := by
    rw [← shift_neckRay_succ hdeg m, ← hm]
    exact hmem
  have hle : splitDepth (bushAt c 0) [] ≤ m := Nat.sInf_le hmd
  have hge : m ≤ splitDepth (bushAt c 0) [] := by
    by_contra hlt
    have hmem2 : 2 ≤ skeletonDegree (shift (bushAt c 0)
        (neckRay (bushAt c 0) [] (splitDepth (bushAt c 0) []))) :=
      Nat.sInf_mem (s := {k | 2 ≤ skeletonDegree (shift (bushAt c 0)
        (neckRay (bushAt c 0) [] k))}) ⟨m, hmd⟩
    have hk2 : 2 ≤ skeletonDegree
        (shift c (neckRay c [] (splitDepth (bushAt c 0) [] + 1))) := by
      rw [shift_neckRay_succ hdeg]
      exact hmem2
    have hles : splitDepth c [] ≤ splitDepth (bushAt c 0) [] + 1 := Nat.sInf_le hk2
    omega
  omega

/-- The decorations of the chain past its first vertex are the decorations of the
surviving subtree. -/
lemma decAt_neckRay_succ {c : Amb → ℕ} (hdeg : skeletonDegree c = 1) (i : ℕ) :
    decAt c (neckRay c [] (i + 1)) = decAt (bushAt c 0) (neckRay (bushAt c 0) [] i) := by
  have hb : bushAt c 0 = shift c [neckLetter c []] := bushAt_zero_eq_shift hdeg
  rw [neckRay_succ_left, List.nil_append, hb, decAt_shift]
  congr 1
  rw [neckRay_shift_base]
  simp

/-! ### The shape at the root -/

/-- A shape is determined by its list of decorations. -/
lemma Shape.eq_of_decs {σ τ : Shape} (h : σ.decs = τ.decs) : σ = τ := by
  obtain ⟨n, f⟩ := σ
  obtain ⟨m, g⟩ := τ
  have hlen : n = m := by
    have hl := congrArg List.length h
    simpa [Shape.decs] using hl
  subst hlen
  have hf : f = g := List.ofFn_injective h
  rw [hf]

lemma decs_shapeAt_nil (c : Amb → ℕ) :
    (shapeAt c []).decs
      = List.ofFn fun i : Fin (splitDepth c []) ↦ decAt c (neckRay c [] i) := by
  rw [shapeAt_decs, entryV_nil]

/-- **The recursion of the shape at the root**: the shape of a bushy sample is its first
decoration followed by the shape of the surviving subtree. -/
lemma decs_shapeAt_nil_cons {c : Amb → ℕ} (hc : IsBushySample c) (o : Option Tri)
    (l : List (Option Tri)) :
    (shapeAt c []).decs = o :: l
      ↔ (skeletonDegree c = 1 ∧ decAt c [] = o ∧ (shapeAt (bushAt c 0) []).decs = l) := by
  have hroot : Survives (shift c []) := by simpa using hc.survives
  constructor
  · intro h
    have hlen : splitDepth c [] = l.length + 1 := by
      have hl := congrArg List.length h
      rw [decs_shapeAt_nil] at hl
      simpa using hl
    have hdeg : skeletonDegree c = 1 := by
      have hmin := splitDepth_min hroot (k := 0) (by omega)
      rwa [neckRay_zero, shift_nil] at hmin
    have hsd : splitDepth (bushAt c 0) [] = l.length := by
      have h1 := splitDepth_bushAt hc hdeg
      omega
    rw [decs_shapeAt_nil, hlen, List.ofFn_succ] at h
    simp only [Fin.val_zero, Fin.val_succ, neckRay_zero] at h
    obtain ⟨h0, htail⟩ := List.cons_eq_cons.mp h
    refine ⟨hdeg, h0, Eq.trans ?_ htail⟩
    rw [decs_shapeAt_nil, hsd]
    exact congrArg List.ofFn (funext fun i : Fin l.length ↦ (decAt_neckRay_succ hdeg i).symm)
  · rintro ⟨hdeg, hdec, htail⟩
    have hsd : splitDepth (bushAt c 0) [] = l.length := by
      have hl := congrArg List.length htail
      rw [decs_shapeAt_nil] at hl
      simpa using hl
    have hlen : splitDepth c [] = l.length + 1 := by
      have h1 := splitDepth_bushAt hc hdeg
      omega
    rw [decs_shapeAt_nil, hlen, List.ofFn_succ]
    simp only [Fin.val_zero, Fin.val_succ, neckRay_zero]
    refine List.cons_eq_cons.mpr ⟨hdec, Eq.trans ?_ htail⟩
    rw [decs_shapeAt_nil, hsd]
    exact congrArg List.ofFn (funext fun i : Fin l.length ↦ decAt_neckRay_succ hdeg i)

/-- The shape at the root with a prescribed decoration list is an event. -/
lemma measurableSet_decs_shapeAt_nil (l : List (Option Tri)) :
    MeasurableSet {c : Amb → ℕ | (shapeAt c []).decs = l} := by
  have he : {c : Amb → ℕ | (shapeAt c []).decs = l}
      = {c : Amb → ℕ | shapeAt c [] = Shape.ofList l} := by
    ext c
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact Shape.eq_of_decs (by rw [h, Shape.decs_ofList])
    · intro h
      rw [h, Shape.decs_ofList]
  rw [he]
  exact fibreMeasurable_shapeAt [] _

/-- **`thm:shape-iid`, the shape law at the root**: conditioned on survival the shape of
the root carries one decoration factor per neck vertex and the split weight `θ̃₂` at the
end, which is the law `μ`. -/
theorem survivalMeasure_decs_shapeAt_nil (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (l : List (Option Tri)) :
    survivalMeasure (N := 2) θ {c : Amb → ℕ | (shapeAt c []).decs = l}
      = (l.map (decMass θ)).prod * ENNReal.ofReal (θ.skeletonWeight 2) := by
  have hnull : survivalMeasure (N := 2) θ {c : Amb → ℕ | IsBushySample c}ᶜ = 0 := by
    have hae := ae_isBushySample_of_pos θ hq h2
    rw [ae_iff] at hae
    exact hae
  induction l with
  | nil =>
      have hset : {c : Amb → ℕ | (shapeAt c []).decs = ([] : List (Option Tri))}
          = {c : Amb → ℕ | (shapeAt c []).neckLen = 1} := by
        ext c
        have hne : (shapeAt c []).neckLen = splitDepth c [] + 1 := by
          rw [Shape.neckLen, shapeAt_necks, entryV_nil]
        have hlen : (shapeAt c []).decs.length = splitDepth c [] := by
          rw [decs_shapeAt_nil, List.length_ofFn]
        simp only [Set.mem_ofPred_eq, hne]
        constructor
        · intro h
          have := congrArg List.length h
          rw [hlen] at this
          simp only [List.length_nil] at this
          omega
        · intro h
          have hzero : (shapeAt c []).decs.length = 0 := by rw [hlen]; omega
          exact List.eq_nil_of_length_eq_zero hzero
      rw [hset, survivalMeasure_neckLen θ hq h2 1 le_rfl]
      simp
  | cons o l ih =>
      have hset : {c : Amb → ℕ | (shapeAt c []).decs = o :: l}
            ∩ {c : Amb → ℕ | IsBushySample c}
          = (({c : Amb → ℕ | skeletonDegree c = 1} ∩ {c : Amb → ℕ | decAt c [] = o})
              ∩ {c : Amb → ℕ | bushAt c 0 ∈ {d : Amb → ℕ | (shapeAt d []).decs = l}})
            ∩ {c : Amb → ℕ | IsBushySample c} := by
        ext c
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h, hc⟩
          obtain ⟨h1, h2', h3⟩ := (decs_shapeAt_nil_cons hc o l).mp h
          exact ⟨⟨⟨h1, h2'⟩, h3⟩, hc⟩
        · rintro ⟨⟨⟨h1, h2'⟩, h3⟩, hc⟩
          exact ⟨(decs_shapeAt_nil_cons hc o l).mpr ⟨h1, h2', h3⟩, hc⟩
      rw [measure_eq_of_inter_ae hnull hset,
        survivalMeasure_neck_step θ hq hq0 h2 o (measurableSet_decs_shapeAt_nil l), ih,
        List.map_cons, List.prod_cons, mul_assoc]

/-- **`thm:shape-iid`, the shape law at the root**, read off the shape itself. -/
theorem survivalMeasure_shapeAt_nil (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (σ : Shape) :
    survivalMeasure (N := 2) θ {c : Amb → ℕ | shapeAt c [] = σ}
      = (σ.decs.map (decMass θ)).prod * ENNReal.ofReal (θ.skeletonWeight 2) := by
  have he : {c : Amb → ℕ | shapeAt c [] = σ} = {c : Amb → ℕ | (shapeAt c []).decs = σ.decs} := by
    ext c
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h ↦ by rw [h], fun h ↦ Shape.eq_of_decs h⟩
  rw [he, survivalMeasure_decs_shapeAt_nil θ hq hq0 h2]

end ChainClasses
