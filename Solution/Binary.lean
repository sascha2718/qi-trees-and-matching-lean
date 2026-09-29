import Solution.Infrastructure

/-! Transports between the `Fin 2` vertex addresses in the challenge and the Boolean
addresses used by the matching and two-value libraries. -/

open scoped ENNReal Classical
open MeasureTheory Challenge

namespace Solution.Binary

/-- Relabel each binary edge by `0 ↔ false`, `1 ↔ true`. -/
def wordEquiv : Word ≃ Infrastructure.Word := Equiv.listEquivOfEquiv finTwoEquiv

@[simp] lemma wordEquiv_nil : wordEquiv [] = [] := rfl
@[simp] lemma wordEquiv_symm_nil : wordEquiv.symm [] = [] := rfl
@[simp] lemma wordEquiv_length (w : Word) : (wordEquiv w).length = w.length :=
  List.length_map _
@[simp] lemma wordEquiv_symm_length (w : Infrastructure.Word) :
    (wordEquiv.symm w).length = w.length := List.length_map _
@[simp] lemma wordEquiv_append (v w : Word) :
    wordEquiv (v ++ w) = wordEquiv v ++ wordEquiv w := List.map_append
@[simp] lemma wordEquiv_symm_append (v w : Infrastructure.Word) :
    wordEquiv.symm (v ++ w) = wordEquiv.symm v ++ wordEquiv.symm w := List.map_append
@[simp] lemma wordEquiv_zero : wordEquiv [0] = [false] := rfl
@[simp] lemma wordEquiv_one : wordEquiv [1] = [true] := rfl
@[simp] lemma wordEquiv_symm_false : wordEquiv.symm [false] = [0] := rfl
@[simp] lemma wordEquiv_symm_true : wordEquiv.symm [true] = [1] := rfl

lemma child_iff (s t : Word) :
    (∃ b, wordEquiv t = wordEquiv s ++ [b]) ↔ ∃ c, t = s ++ [c] := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨finTwoEquiv.symm b, wordEquiv.injective ?_⟩
    simpa [wordEquiv, Equiv.listEquivOfEquiv] using hb
  · rintro ⟨c, rfl⟩
    exact ⟨finTwoEquiv c, List.map_append⟩

lemma treeAdj_iff (s t : Word) :
    Infrastructure.treeAdj (wordEquiv s) (wordEquiv t) ↔ treeAdj s t :=
  or_congr (child_iff s t) (child_iff t s)

/-- Conjugate a Boolean tree automorphism by the address equivalence. -/
def treeAut (g : Infrastructure.Word ≃ Infrastructure.Word) : Word ≃ Word :=
  wordEquiv.trans (g.trans wordEquiv.symm)

lemma isTreeAut {g : Infrastructure.Word ≃ Infrastructure.Word}
    (hg : Infrastructure.IsTreeAut g) : IsTreeAut (treeAut g) := by
  refine ⟨?_, fun s t => ?_⟩
  · change wordEquiv.symm (g (wordEquiv [])) = []
    simp [hg.1]
  · rw [← treeAdj_iff, ← treeAdj_iff]
    simpa [treeAut] using hg.2 (wordEquiv s) (wordEquiv t)

lemma coord_eq {V : Type*} : ∀ h (x : FullLab V h) w,
    coord h x w = Infrastructure.coord h x (wordEquiv w)
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | h + 1, x, c :: w => by
      fin_cases c
      · simpa [coord, wordEquiv, Equiv.listEquivOfEquiv, finTwoEquiv,
          Infrastructure.coord] using coord_eq h x.2.1 w
      · simpa [coord, wordEquiv, Equiv.listEquivOfEquiv, finTwoEquiv,
          Infrastructure.coord] using coord_eq h x.2.2 w

lemma coord_at {V : Type*} (X : (h : ℕ) → FullLab V h) (w : Word) :
    coord w.length (X w.length) w =
      Infrastructure.coord (wordEquiv w).length (X (wordEquiv w).length) (wordEquiv w) := by
  rw [coord_eq]
  exact congrArg (fun n => Infrastructure.coord n (X n) (wordEquiv w))
    (wordEquiv_length w).symm

/-- Transport an infinite matching without changing its probability space or laws. -/
lemma infiniteMatching {V : Type u} [MeasurableSpace V] (R : V → V → Prop)
    (μ ν : (h : ℕ) → PMF (FullLab V h)) (p : ℝ≥0∞)
    (h : ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : (h : ℕ) → Ω → FullLab V h),
      (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
      (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
      (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
      (∀ h, P.map (fun ω => (X h ω, Y h ω)) = (prodPMF (μ h) (ν h)).toMeasure) ∧
      p ≤ P {ω | ∃ g : Infrastructure.Word ≃ Infrastructure.Word,
        Infrastructure.IsTreeAut g ∧ ∀ w,
          R (Infrastructure.coord (g w).length (X (g w).length ω) (g w))
            (Infrastructure.coord w.length (Y w.length ω) w)}) :
    InfiniteMatching R μ ν p := by
  obtain ⟨Ω, mΩ, P, hP, X, Y, hX, hY, hm, hlaw, hb⟩ := h
  refine ⟨Ω, mΩ, P, hP, X, Y, hX, hY, hm, hlaw, hb.trans (measure_mono ?_)⟩
  rintro ω ⟨g, hg, hw⟩
  refine ⟨treeAut g, isTreeAut hg, fun w => ?_⟩
  have hx := (coord_at (fun n => X n ω) (treeAut g w)).trans
    (congrArg (fun v => Infrastructure.coord v.length (X v.length ω) v)
      (show wordEquiv (treeAut g w) = g (wordEquiv w) from
        wordEquiv.apply_symm_apply _))
  rw [hx, coord_at (fun n => Y n ω) w]
  exact hw (wordEquiv w)

/-- Reindex a Bernoulli field along the address equivalence. -/
def fieldEquiv : (Infrastructure.Word → Bool) ≃ᵐ (Word → Bool) where
  toFun χ := χ ∘ wordEquiv
  invFun χ := χ ∘ wordEquiv.symm
  left_inv χ := by funext w; simp
  right_inv χ := by funext w; simp
  measurable_toFun := Measurable.of_eval fun _ => measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun _ => measurable_pi_apply _

@[simp] lemma fieldEquiv_apply (χ : Infrastructure.Word → Bool) (w : Word) :
    fieldEquiv χ w = χ (wordEquiv w) := rfl

lemma inTree_toBool {χ : Infrastructure.Word → Bool} {w : Word}
    (h : InTree (fieldEquiv χ) w) : Infrastructure.InTree χ (wordEquiv w) := by
  induction h with
  | root => exact .root
  | one _ ih => simpa using Infrastructure.InTree.one ih
  | two _ hχ ih => simpa using Infrastructure.InTree.two ih hχ

lemma inTree_fromBool {χ : Infrastructure.Word → Bool} {w : Infrastructure.Word}
    (h : Infrastructure.InTree χ w) : InTree (fieldEquiv χ) (wordEquiv.symm w) := by
  induction h with
  | root => exact .root
  | one _ ih => simpa using InTree.one ih
  | two _ hχ ih =>
      simpa using InTree.two ih (by simpa using hχ)

lemma inTree_iff (χ : Infrastructure.Word → Bool) (w : Word) :
    InTree (fieldEquiv χ) w ↔ Infrastructure.InTree χ (wordEquiv w) :=
  ⟨inTree_toBool, fun h => by simpa using inTree_fromBool h⟩

def sampleEquiv (χ : Infrastructure.Word → Bool) :
    {w // InTree (fieldEquiv χ) w} ≃ {w // Infrastructure.InTree χ w} where
  toFun w := ⟨wordEquiv w, inTree_toBool w.2⟩
  invFun w := ⟨wordEquiv.symm w, inTree_fromBool w.2⟩
  left_inv w := Subtype.ext (wordEquiv.symm_apply_apply w)
  right_inv w := Subtype.ext (wordEquiv.apply_symm_apply w)

def sampleIso (χ : Infrastructure.Word → Bool) :
    wordGraph (InTree (fieldEquiv χ)) ≃g wordGraph (Infrastructure.InTree χ) where
  toEquiv := sampleEquiv χ
  map_rel_iff' := by
    intro u v
    change (sampleEquiv χ u ≠ sampleEquiv χ v ∧
      Infrastructure.treeAdj (wordEquiv u.1) (wordEquiv v.1)) ↔
        (u ≠ v ∧ treeAdj u.1 v.1)
    exact and_congr (not_congr (sampleEquiv χ).injective.eq_iff) (treeAdj_iff u.1 v.1)

lemma iso_dist {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H)
    (u v : A) : H.dist (e u) (e v) = G.dist u v := by
  rw [SimpleGraph.dist_eq_sInf, SimpleGraph.dist_eq_sInf]
  congr 1
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    let q : G.Walk u v := (p.map e.symm.toHom).copy (by simp) (by simp)
    exact ⟨q, by simp [q]⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.map e.toHom, p.length_map e.toHom⟩

lemma field_map {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (Infrastructure.bernoulliField ht ht1).map fieldEquiv = bernoulliField ht ht1 :=
  Measure.map_infinitePi_infinitePi_of_inj wordEquiv.injective

lemma field_pair_map {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ((Infrastructure.bernoulliField ht ht1).prod (Infrastructure.bernoulliField ht ht1)).map
      (fieldEquiv.prodCongr fieldEquiv) =
        (bernoulliField ht ht1).prod (bernoulliField ht ht1) := by
  let : IsProbabilityMeasure (Infrastructure.bernoulliField ht ht1) := by
    unfold Infrastructure.bernoulliField
    infer_instance
  change ((Infrastructure.bernoulliField ht ht1).prod (Infrastructure.bernoulliField ht ht1)).map
    (Prod.map fieldEquiv fieldEquiv) = _
  rw [← Measure.map_prod_map _ _ fieldEquiv.measurable fieldEquiv.measurable,
    field_map]

/-- Address relabelling preserves the quasi-isometry constant and the root. -/
lemma qi {χ χ' : Infrastructure.Word → Bool} {K : ℕ}
    {f : {w // Infrastructure.InTree χ w} → {w // Infrastructure.InTree χ' w}}
    (hf : GraphQIWith K (wordGraph (Infrastructure.InTree χ))
      (wordGraph (Infrastructure.InTree χ')) f)
    (hroot : f ⟨[], Infrastructure.InTree.root⟩ = ⟨[], Infrastructure.InTree.root⟩) :
    ∃ g : {w // InTree (fieldEquiv χ) w} → {w // InTree (fieldEquiv χ') w},
      GraphQIWith K (wordGraph (InTree (fieldEquiv χ)))
        (wordGraph (InTree (fieldEquiv χ'))) g ∧
      g ⟨[], InTree.root⟩ = ⟨[], InTree.root⟩ := by
  let e := sampleIso χ
  let e' := sampleIso χ'
  let g := fun x => e'.symm (f (e x))
  refine ⟨g, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y
    rw [← iso_dist e' (g x) (g y), ← iso_dist e x y]
    simpa [g] using hf.upper (e x) (e y)
  · intro x y
    rw [← iso_dist e x y, ← iso_dist e' (g x) (g y)]
    simpa [g] using hf.lower (e x) (e y)
  · intro y
    obtain ⟨x, hx⟩ := hf.dense (e' y)
    refine ⟨e.symm x, ?_⟩
    rw [← iso_dist e' (g (e.symm x)) y]
    simpa [g] using hx
  · change e'.symm (f ⟨[], Infrastructure.InTree.root⟩) = _
    rw [hroot]
    rfl

end Solution.Binary
