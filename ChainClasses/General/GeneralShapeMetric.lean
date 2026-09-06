import ChainClasses.General.GeneralDecomposition
import ChainClasses.Shape.ContractAddr
import ChainClasses.Shape.ShapeMetric
import ChainClasses.Scalar.Hairy
import ChainClasses.General.GeneralConstants

/-!
`sec:general-shapes` and `sec:general-cross` of `matching_classes_general.tex`: the
metric realisation of `def:shape-general` and the comparability clause of
`thm:cross-relabel`.

A shape at general arity realises to a rose tree, and `ContractAddr` already carries
the address layer of a rose tree with its parent-child graph and graph metric.  What a
shape adds is its exit: the address of the terminating split, one letter per neck
vertex, each naming the child past the bushes.  With entry and exit marked, the
realisations are the marked spaces `thm:shape-net` compares, the net machinery of
`MarkedQI` applies verbatim over the enumeration of `𝒮` by size, and the comparability
clause of `thm:cross-relabel` is the composition of the coupling legs with the class
bound, at the constant `3¹⁵D¹⁶` of the paper.

* `gExitAddr`, `GShape.exitAddr`, `isAddr_realiseAux_gExitAddr`: the exit of a
  realisation, and that it is an address.
* `gSpace`, `gShapeSpace`: **`def:shape-general` as a marked space**, the entry at the
  root and the exit at the terminating split.
* `gCodeList` with `codeF_false_append_inj`, `gShapeKey`, `gShapeEnum`,
  `gShapeFamily`: **`def:shape-net` at general arity**, the enumeration of `𝒮` by
  size: the bush lists are coded by the prefix-free tree codes with a two-letter
  separator per vertex of the neck, so the key has `2|σ|` bits and grows with the
  size.
* `gSize_repIdx_le`: **`thm:shape-net`** at general shapes, `|rep_D(σ)| ≤ |σ|`.
* `gShapeIdx`, `gNetGraph`, `gNetLab`: the label graph `G_D` on the classes and the
  class map.
* `crossRelabel_qi`: **`thm:cross-relabel` (`it:cross-relabel-qi`)**, the
  directed form: two shapes whose coupling partners lie in equal classes, or in
  classes joined by a `27D⁴`-comparability running with the chain, admit a
  `3¹⁵D¹⁶`-marked quasi-isometry.
* `crossRelabel_qi_compat`: the same clause over the symmetric edge of `G_D`: the
  comparability may run against the chain, and then it is the reversed pair that
  reaches the constant, so the conclusion holds in one of the two directions.
-/

namespace ChainClasses

open RTree

/-! ### The exit of a realisation -/

/-- The address of the terminating split in the realisation of a bush-list: one letter
per neck vertex, naming the child past the bushes. -/
def gExitAddr : List (List RTree) → List ℕ
  | [] => []
  | [_] => []
  | β :: r :: rest => β.length :: gExitAddr (r :: rest)

@[simp] lemma gExitAddr_nil : gExitAddr [] = [] := rfl

@[simp] lemma gExitAddr_singleton (β : List RTree) : gExitAddr [β] = [] := rfl

lemma gExitAddr_cons₂ (β r : List RTree) (rest : List (List RTree)) :
    gExitAddr (β :: r :: rest) = β.length :: gExitAddr (r :: rest) := rfl

/-- The exit is an address of the realisation. -/
lemma isAddr_realiseAux_gExitAddr :
    ∀ L : List (List RTree), IsAddr (GShape.realiseAux L) (gExitAddr L)
  | [] => isAddr_nil _
  | [β] => isAddr_nil _
  | β :: r :: rest => by
      rw [show GShape.realiseAux (β :: r :: rest)
          = .node (β ++ [GShape.realiseAux (r :: rest)]) from rfl, gExitAddr_cons₂,
        isAddr_cons]
      refine ⟨by simp, ?_⟩
      have hget : (β ++ [GShape.realiseAux (r :: rest)])[β.length]'(by simp)
          = GShape.realiseAux (r :: rest) := by
        simp
      rw [hget]
      exact isAddr_realiseAux_gExitAddr (r :: rest)

/-- **The exit of a shape**: the address of its terminating split. -/
def GShape.exitAddr (σ : GShape) : List ℕ := gExitAddr σ.decs

lemma GShape.exitAddr_mem_addrList (σ : GShape) : σ.exitAddr ∈ addrList σ.realise :=
  mem_addrList_iff.mpr (isAddr_realiseAux_gExitAddr σ.decs)

/-! ### The marked space of a shape -/

/-- A rose tree with a marked address, as a marked metric space: the entry at the root,
the exit at the address when it is one. -/
noncomputable def gSpace (t : RTree) (e : List ℕ) : MarkedSpace where
  carrier := Vert t
  entry := rootVert t
  exit := if he : e ∈ addrList t then ⟨e, he⟩ else rootVert t

@[simp] lemma carrier_gSpace (t : RTree) (e : List ℕ) : (gSpace t e).carrier = Vert t := rfl

@[simp] lemma entry_gSpace (t : RTree) (e : List ℕ) : (gSpace t e).entry = rootVert t := rfl

lemma exit_gSpace_of_mem {t : RTree} {e : List ℕ} (he : e ∈ addrList t) :
    (gSpace t e).exit = ⟨e, he⟩ := dif_pos he

/-- **`def:shape-general` as a marked space**: the realisation with the entry at the
root and the exit at the terminating split. -/
noncomputable def gShapeSpace (σ : GShape) : MarkedSpace := gSpace σ.realise σ.exitAddr

lemma exit_gShapeSpace (σ : GShape) :
    (gShapeSpace σ).exit = ⟨σ.exitAddr, σ.exitAddr_mem_addrList⟩ :=
  exit_gSpace_of_mem σ.exitAddr_mem_addrList

/-! ### The base of the descent -/

/-- Every shape has at least its neck. -/
lemma GShape.size_pos (σ : GShape) : 1 ≤ σ.size := by
  have h := σ.size_eq
  rw [GShape.neckLen] at h
  omega

/-- Every rose tree in a bush list carries at least one vertex, so an empty bush sum
means empty bush lists. -/
lemma sizeF_eq_zero_iff {β : List RTree} : RTree.sizeF β = 0 ↔ β = [] := by
  cases β with
  | nil => simp [RTree.sizeF]
  | cons c cs =>
      simp only [RTree.sizeF, List.cons_ne_nil, iff_false]
      have := RTree.size_pos c
      omega

/-- **The base of the descent**: the only shape of size one is the bare split. -/
lemma GShape.eq_of_size_le_one {σ τ : GShape} (hσ : σ.size ≤ 1) (hτ : τ.size ≤ 1) :
    σ = τ := by
  have key : ∀ ρ : GShape, ρ.size ≤ 1 → ρ.decs = [([] : List RTree)] := by
    rintro ⟨n, f⟩ hρ
    have h : (GShape.mk n f).size
        = n + 1 + (((GShape.mk n f).decs).map RTree.sizeF).sum := (GShape.mk n f).size_eq
    have hnecks : n = 0 := by omega
    subst hnecks
    have hd : (GShape.mk 0 f).decs = [f 0] := by
      simp [GShape.decs, List.ofFn_succ]
    have hsum : ((GShape.mk 0 f).decs.map RTree.sizeF).sum = 0 := by omega
    rw [hd] at hsum ⊢
    have hzero : RTree.sizeF (f 0) = 0 := by simpa using hsum
    rw [sizeF_eq_zero_iff.mp hzero]
  exact GShape.eq_of_decs ((key σ hσ).trans (key τ hτ).symm)

/-! ### The enumeration of `𝒮` by size -/

/-- The length of a forest code: two bits per vertex. -/
lemma length_codeF (l : List RTree) : (RTree.codeF l).length = 2 * RTree.sizeF l := by
  induction l with
  | nil => simp [RTree.codeF, RTree.sizeF]
  | cons c cs ih =>
      rw [RTree.codeF, List.length_append, RTree.code_length, ih, RTree.sizeF]
      ring

/-- A forest followed by a terminator is decodable: the tree codes are prefix-free and
begin with the letter `1`, which the terminator is not. -/
lemma codeF_false_append_inj :
    ∀ (l₁ l₂ : List RTree) (u₁ u₂ : List Bool),
      RTree.codeF l₁ ++ false :: u₁ = RTree.codeF l₂ ++ false :: u₂ → l₁ = l₂ ∧ u₁ = u₂
  | [], [], _, _, h => ⟨rfl, by simpa [RTree.codeF] using h⟩
  | [], c :: cs, u₁, u₂, h => by
      obtain ⟨w, hw⟩ := RTree.code_eq_cons c
      simp only [RTree.codeF, hw] at h
      simp at h
  | c :: cs, [], u₁, u₂, h => by
      obtain ⟨w, hw⟩ := RTree.code_eq_cons c
      simp only [RTree.codeF, hw] at h
      simp at h
  | c :: cs, d :: ds, u₁, u₂, h => by
      simp only [RTree.codeF] at h
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := RTree.code_append_inj c d _ _ h
      obtain ⟨rfl, h3⟩ := codeF_false_append_inj cs ds u₁ u₂ h2
      exact ⟨rfl, h3⟩

/-- The code of a bush list: the forest codes, a two-letter separator per vertex of the
neck. -/
def gCodeList : List (List RTree) → List Bool
  | [] => []
  | β :: rest => RTree.codeF β ++ false :: false :: gCodeList rest

/-- The code has two bits per vertex of the realisation. -/
lemma length_gCodeList :
    ∀ L : List (List RTree),
      (gCodeList L).length = 2 * ((L.map RTree.sizeF).sum + L.length)
  | [] => by simp [gCodeList]
  | β :: rest => by
      simp only [gCodeList]
      rw [List.length_append, length_codeF, List.map_cons, List.sum_cons,
        List.length_cons, List.length_cons, List.length_cons,
        length_gCodeList rest]
      ring

/-- The code determines the bush list. -/
lemma gCodeList_injective : Function.Injective gCodeList := by
  intro L₁
  induction L₁ with
  | nil =>
      intro L₂ h
      cases L₂ with
      | nil => rfl
      | cons β rest => simp [gCodeList] at h
  | cons β rest ih =>
      intro L₂ h
      cases L₂ with
      | nil => simp [gCodeList] at h
      | cons γ rest' =>
          simp only [gCodeList] at h
          obtain ⟨rfl, h2⟩ := codeF_false_append_inj β γ _ _ h
          rw [List.cons.injEq] at h2
          rw [ih h2.2]

/-- The key of the enumeration: the code of the bush lists read as a number, so that a
larger shape has a larger key. -/
def gShapeKey (σ : GShape) : ℕ := numOf (gCodeList σ.decs)

/-- The key determines the shape. -/
lemma gShapeKey_injective : Function.Injective gShapeKey := fun _ _ h =>
  GShape.eq_of_decs (gCodeList_injective (numOf_injective h))

/-- The code of a shape has two bits per vertex. -/
lemma length_gCodeList_decs (σ : GShape) : (gCodeList σ.decs).length = 2 * σ.size := by
  rw [length_gCodeList, σ.size_eq, GShape.decs_length, GShape.neckLen]
  ring

/-- The key grows with the size, which is what makes the enumeration one by size. -/
lemma gShapeKey_lt_of_size_lt {σ τ : GShape} (h : σ.size < τ.size) :
    gShapeKey σ < gShapeKey τ := by
  refine numOf_lt_of_length_lt ?_
  rw [length_gCodeList_decs, length_gCodeList_decs]
  omega

/-- The bare split, the least shape. -/
instance : Inhabited GShape := ⟨⟨0, fun _ => []⟩⟩

/-- The bare necks have every size. -/
lemma size_bareNeck (n : ℕ) : (GShape.mk n fun _ => []).size = n + 1 := by
  have h := (GShape.mk n fun _ => []).size_eq
  have hsum : (((GShape.mk n fun _ => []).decs).map RTree.sizeF).sum = 0 := by
    rw [GShape.decs]
    simp [RTree.sizeF]
  rw [hsum, GShape.neckLen] at h
  omega

/-- `𝒮` is infinite: the bare necks have every size. -/
instance : Infinite GShape := by
  refine Infinite.of_injective (fun n : ℕ => (GShape.mk n fun _ => []))
    fun n m h => ?_
  have hs := congrArg GShape.size h
  rw [size_bareNeck, size_bareNeck] at hs
  omega

/-- One key occurs for each of the infinitely many shapes. -/
lemma gShapeKey_range_infinite : (setOf (fun k => k ∈ Set.range gShapeKey)).Infinite := by
  rw [Set.setOf_mem_eq]
  exact Set.infinite_range_of_injective gShapeKey_injective

/-- **`def:shape-net` at general arity**: the enumeration of `𝒮` by size, the ties
broken by the key. -/
noncomputable def gShapeEnum (n : ℕ) : GShape :=
  Function.invFun gShapeKey (Nat.nth (fun k => k ∈ Set.range gShapeKey) n)

/-- The `n`-th shape carries the `n`-th key. -/
lemma gShapeKey_gShapeEnum (n : ℕ) :
    gShapeKey (gShapeEnum n) = Nat.nth (fun k => k ∈ Set.range gShapeKey) n :=
  Function.invFun_eq (Nat.nth_mem_of_infinite gShapeKey_range_infinite n)

/-- The enumeration lists each shape once. -/
lemma gShapeEnum_injective : Function.Injective gShapeEnum := by
  intro m n h
  have hk := congrArg gShapeKey h
  rw [gShapeKey_gShapeEnum, gShapeKey_gShapeEnum] at hk
  exact Nat.nth_injective gShapeKey_range_infinite hk

/-- The enumeration lists every shape. -/
lemma gShapeEnum_surjective : Function.Surjective gShapeEnum := by
  classical
  intro σ
  refine ⟨Nat.count (fun k => k ∈ Set.range gShapeKey) (gShapeKey σ), gShapeKey_injective ?_⟩
  rw [gShapeKey_gShapeEnum]
  exact Nat.nth_count (p := fun k => k ∈ Set.range gShapeKey) ⟨σ, rfl⟩

/-- **`def:shape-net`**: the enumeration is by size. -/
lemma size_gShapeEnum_monotone : Monotone fun n => (gShapeEnum n).size := by
  intro m n hmn
  by_contra hlt
  push Not at hlt
  have h1 := gShapeKey_lt_of_size_lt hlt
  rw [gShapeKey_gShapeEnum, gShapeKey_gShapeEnum] at h1
  have := (Nat.nth_lt_nth gShapeKey_range_infinite).mp h1
  omega

/-- **`def:shape-net`**: the shapes enumerated by size, as marked spaces. -/
noncomputable def gShapeFamily (n : ℕ) : MarkedSpace := gShapeSpace (gShapeEnum n)

/-- **`thm:shape-net` at general shapes**: `|rep_D(σ)| ≤ |σ|`. -/
theorem gSize_repIdx_le {Dq : ℝ} (hD : 1 ≤ Dq) (n : ℕ) :
    (gShapeEnum (repIdx gShapeFamily Dq n)).size ≤ (gShapeEnum n).size :=
  sz_repIdx_le gShapeFamily Dq hD size_gShapeEnum_monotone n

/-! ### The label graph on the classes -/

/-- The index of a shape in the enumeration the net is built on. -/
noncomputable def gShapeIdx (σ : GShape) : ℕ :=
  (Equiv.ofBijective gShapeEnum ⟨gShapeEnum_injective, gShapeEnum_surjective⟩).symm σ

@[simp] lemma gShapeEnum_gShapeIdx (σ : GShape) : gShapeEnum (gShapeIdx σ) = σ :=
  (Equiv.ofBijective gShapeEnum
    ⟨gShapeEnum_injective, gShapeEnum_surjective⟩).apply_symm_apply σ

@[simp] lemma gShapeFamily_gShapeIdx (σ : GShape) :
    gShapeFamily (gShapeIdx σ) = gShapeSpace σ := by
  rw [gShapeFamily, gShapeEnum_gShapeIdx]

/-- **The label graph `G_D` at general arity**: the net on the shapes, two classes
linked when they are `27D⁴`-comparable. -/
def gNetGraph (Dq : ℝ) : SimpleGraph ℕ := SimpleGraph.fromRel (NetAdj gShapeFamily Dq)

/-- **The class map**: a shape is labelled by the class of its representative. -/
noncomputable def gNetLab (Dq : ℝ) (σ : GShape) : ℕ := repIdx gShapeFamily Dq (gShapeIdx σ)

/-- A shape is comparable to the class it is labelled by. -/
lemma markedQI_gNetLab {Dq : ℝ} (hD : 1 ≤ Dq) (σ : GShape) :
    MarkedQI Dq (gShapeSpace σ) (gShapeFamily (gNetLab Dq σ)) := by
  have h := markedQI_repIdx gShapeFamily Dq hD (gShapeIdx σ)
  rwa [gShapeFamily_gShapeIdx] at h

/-! ### The comparability clause of `thm:cross-relabel` -/

/-- **`thm:cross-relabel` (`it:cross-relabel-qi`), the directed form**: two
shapes reaching coupling partners by `9D³`-marked quasi-isometries, the partners in
equal classes or in classes joined by a `27D⁴`-comparability running with the chain,
admit a `3¹⁵D¹⁶`-marked quasi-isometry. -/
theorem crossRelabel_qi {Dq : ℝ} (hD : 1 ≤ Dq) {σ σ' : GShape} {n n' : ℕ}
    (hσ : MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeFamily n))
    (hσ' : MarkedQI (9 * Dq ^ 3) (gShapeSpace σ') (gShapeFamily n'))
    (hcls : repIdx gShapeFamily Dq n = repIdx gShapeFamily Dq n'
      ∨ MarkedQI (27 * Dq ^ 4) (gShapeFamily (repIdx gShapeFamily Dq n))
          (gShapeFamily (repIdx gShapeFamily Dq n'))) :
    MarkedQI (14348907 * Dq ^ 16) (gShapeSpace σ) (gShapeSpace σ') := by
  have hD0 : (0 : ℝ) ≤ Dq := zero_le_one.trans hD
  have h3 : (1 : ℝ) ≤ Dq ^ 3 := one_le_pow₀ hD
  have h7 : (1 : ℝ) ≤ Dq ^ 7 := one_le_pow₀ hD
  have h9 : (1 : ℝ) ≤ 9 * Dq ^ 3 := by nlinarith
  have h729 : (1 : ℝ) ≤ 729 * Dq ^ 7 := by nlinarith
  have hmid : MarkedQI (729 * Dq ^ 7) (gShapeFamily n) (gShapeFamily n') := by
    rcases hcls with heq | hadj
    · refine (markedQI_of_repIdx_eq gShapeFamily Dq hD heq).mono (by positivity) ?_
      have hpow : Dq ^ 3 ≤ Dq ^ 7 := pow_le_pow_right₀ hD (by omega)
      nlinarith
    · exact markedQI_of_repIdx_adjacent gShapeFamily Dq hD hadj
  have hall := markedQI_relabel h9 h729 hσ hmid hσ'
  rwa [relabel_scale] at hall

/-- **`thm:cross-relabel` (`it:cross-relabel-qi`), over the symmetric edge**:
if the two class labels are equal or adjacent in `G_D`, the pair reaches the constant
`3¹⁵D¹⁶` in one of its two directions, the one along which the edge's comparability
runs. -/
theorem crossRelabel_qi_compat {Dq : ℝ} (hD : 1 ≤ Dq) {σ σ' τ τ' : GShape}
    (hστ : MarkedQI (9 * Dq ^ 3) (gShapeSpace σ) (gShapeSpace τ))
    (hσ'τ' : MarkedQI (9 * Dq ^ 3) (gShapeSpace σ') (gShapeSpace τ'))
    (h : gNetLab Dq τ = gNetLab Dq τ' ∨ (gNetGraph Dq).Adj (gNetLab Dq τ) (gNetLab Dq τ')) :
    MarkedQI (14348907 * Dq ^ 16) (gShapeSpace σ) (gShapeSpace σ')
      ∨ MarkedQI (14348907 * Dq ^ 16) (gShapeSpace σ') (gShapeSpace σ) := by
  have hτ : gShapeSpace τ = gShapeFamily (gShapeIdx τ) := (gShapeFamily_gShapeIdx τ).symm
  have hτ' : gShapeSpace τ' = gShapeFamily (gShapeIdx τ') := (gShapeFamily_gShapeIdx τ').symm
  rw [hτ] at hστ
  rw [hτ'] at hσ'τ'
  rcases h with heq | hadj
  · exact Or.inl (crossRelabel_qi hD hστ hσ'τ' (Or.inl heq))
  · rw [gNetGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with hab | hba
    · exact Or.inl (crossRelabel_qi hD hστ hσ'τ' (Or.inr hab.2.2.2))
    · exact Or.inr (crossRelabel_qi hD hσ'τ' hστ (Or.inr hba.2.2.2))

end ChainClasses
