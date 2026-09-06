import ChainClasses.General.GeneralCoupling
import ChainClasses.General.GeneralShapeTail
import ChainClasses.General.GeneralShrinkScale

/-!
`thm:relabel` and `thm:cross-relabel` of `matching_classes_general.tex`, the coupling
legs: the cascade of `thm:shape-coupling`, run for the pair `(μ'_κ, μ)` of a conditional
law and the mixture, produces a coupling supported on `9D³`-comparable pairs.

The cascade of `GeneralCoupling` takes two shrinkings, one per side, and asks of each
that it land in the support of the law of the other side.  The shrinking `gShrink` of
`GeneralShrinkScale` lands in the shapes charged at a support point `k` with an empty
bouquet, which is the support of the mixture; the conditional law `μ'_κ` at an arity
`κ` charges the bouquets of size `k' - κ` at a support point `k' ≥ κ` instead, so the
shrinking into its support pads the bouquet with `k' - κ` one-vertex bushes, a
`1`-marked quasi-isometry adding `k' - κ` vertices.  The comparability of a cascade
pair needs the offspring bound of the source shape, which a shape of positive mass
satisfies: a nonzero decoration, split or bush mass forces its degrees below `J`, the
bush law vanishing above `J` coordinate by coordinate.  The capacity bound
`eq:capacity` then follows from `capacity_of_mass_boundsT_const` at the shrinking
constant `4 max(k, k')`, the point bounds of `thm:mass-uniform` at the common base
`min(gPointBase θ, gPointBase θ')` and the tail bounds at the common rate, and the
coupling is read at the scale `s = ⌊√(D/216 max(J,J')²)⌋`, the cut `D²` and the
thresholds `D ≥ 30` and `216 max(J,J')² A² + A ≤ D`.

* `gBouquetPadDecs`, `gBouquetPad`, `markedQI_gBouquetPad`, `size_gBouquetPad`,
  `chargedG_gBouquetPad`: **the support fix at an arity**, the bouquet padded by
  one-vertex bushes, a `1`-marked quasi-isometry into the support of `μ'_κ`.
* `gShrinkAt`, `markedQI_gShrinkAt`, `size_gShrinkAt_le`, `chargedG_gShrinkAt`: **the
  shrinking into the support of a conditional law**, with its three clauses.
* `degLe_rtreeOf`, `bushMeasure_coord_gt_bound`, `degLe_of_bushMassR_ne_zero`,
  `degLe_of_gDecMass_ne_zero`, `degLe_of_gSplitMass_ne_zero`,
  `degLe_of_gPairMass_ne_zero`, `degLe_of_gCondPMF_ne_zero`,
  `degLe_of_gMixPMF_ne_zero`: **a shape of positive mass realises within the offspring
  bound**.
* `exists_gCapacity_cond_mix`: **`eq:capacity` for the pair `(μ'_κ, μ)`**, past a
  common threshold on the scale and on the cut.
* `markedQI_gShrink_pair`, `markedQI_gShrinkAt_pair`: a cascade pair is
  `9D³`-comparable both ways.
* `exists_gShapeCoupling_cond_mix`: **`thm:cross-relabel`, the coupling** `π'_κ` of
  `μ'_κ` with `μ`, at every `D` past a threshold depending on the two laws.
* `exists_gShapeCoupling_relabel`: **`thm:relabel`, the coupling** `π_κ` of `μ_κ` with
  `μ`, the case of one law.
-/

namespace ChainClasses

open MeasureTheory RTree
open scoped ENNReal Classical
open BranchingProcess (Offspring sampleMeasure bushMeasure)

variable {J N J' N' : ℕ}

/-! ### The support fix at an arity: padding the bouquet -/

/-- **The bouquet padding on the bush lists**: `r` one-vertex bushes appended to the
last list, the neck lists left. -/
def gBouquetPadDecs (r : ℕ) : List (List RTree) → List (List RTree)
  | [] => []
  | [β] => [β ++ List.replicate r (.node [])]
  | β :: γ :: rest => β :: gBouquetPadDecs r (γ :: rest)

@[simp] lemma gBouquetPadDecs_nil (r : ℕ) : gBouquetPadDecs r [] = [] := rfl
@[simp] lemma gBouquetPadDecs_singleton (r : ℕ) (β : List RTree) :
    gBouquetPadDecs r [β] = [β ++ List.replicate r (.node [])] := rfl
lemma gBouquetPadDecs_cons_cons (r : ℕ) (β γ : List RTree) (rest : List (List RTree)) :
    gBouquetPadDecs r (β :: γ :: rest) = β :: gBouquetPadDecs r (γ :: rest) := rfl

lemma gBouquetPadDecs_ne_nil (r : ℕ) {L : List (List RTree)} (hL : L ≠ []) :
    gBouquetPadDecs r L ≠ [] := by
  cases L with
  | nil => exact absurd rfl hL
  | cons β rest => cases rest <;> simp [gBouquetPadDecs_cons_cons]

/-- The bouquet padding acts on the last list only. -/
lemma gBouquetPadDecs_append_singleton (r : ℕ) : ∀ (L : List (List RTree)) (b : List RTree),
    gBouquetPadDecs r (L ++ [b]) = L ++ [b ++ List.replicate r (.node [])]
  | [], b => rfl
  | [β], b => rfl
  | β :: γ :: rest, b => by
      rw [List.cons_append, List.cons_append, gBouquetPadDecs_cons_cons, ← List.cons_append,
        gBouquetPadDecs_append_singleton r (γ :: rest) b]
      simp

/-- **The support fix at an arity**: the shape with `r` one-vertex bushes appended to
its bouquet. -/
def gBouquetPad (r : ℕ) (σ : GShape) : GShape := gOfList (gBouquetPadDecs r σ.decs)

lemma decs_gBouquetPad (r : ℕ) (σ : GShape) :
    (gBouquetPad r σ).decs = gBouquetPadDecs r σ.decs :=
  decs_gOfList (gBouquetPadDecs_ne_nil r σ.decs_ne_nil)

/-- The neck lists of the padded shape are unchanged, and the bouquet carries the added
bushes. -/
lemma neckList_bouquet_gBouquetPad (r : ℕ) (σ : GShape) :
    (gBouquetPad r σ).neckList = σ.neckList
      ∧ (gBouquetPad r σ).bouquet = σ.bouquet ++ List.replicate r (.node []) := by
  have h := (gBouquetPad r σ).decs_eq_append
  rw [decs_gBouquetPad, σ.decs_eq_append, gBouquetPadDecs_append_singleton] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h (by simp)
  exact ⟨h1.symm, by simpa using h2.symm⟩

lemma gShapeSpace_gBouquetPad (r : ℕ) (σ : GShape) :
    gShapeSpace (gBouquetPad r σ)
      = gSpace (GShape.realiseAux (gBouquetPadDecs r σ.decs))
          (gExitAddr (gBouquetPadDecs r σ.decs)) := by
  rw [gShapeSpace, GShape.realise, GShape.exitAddr, decs_gBouquetPad]

/-- **The size of the padded shape**: one vertex per added bush. -/
theorem size_gBouquetPad (r : ℕ) (σ : GShape) : (gBouquetPad r σ).size = σ.size + r := by
  have h1 := (gBouquetPad r σ).size_eq
  have h2 := σ.size_eq
  have hl1 := (gBouquetPad r σ).decs_length
  have hl2 := σ.decs_length
  rw [GShape.neckLen] at h1 h2
  rw [decs_gBouquetPad, σ.decs_eq_append, gBouquetPadDecs_append_singleton] at h1 hl1
  rw [σ.decs_eq_append] at h2 hl2
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, RTree.sizeF_append, sizeF_replicate_leaf, List.length_append,
    List.length_cons, List.length_nil] at h1 h2 hl1 hl2
  omega

/-- **The support clause of the bouquet padding**: a shape charged at a support point `k`
with an empty bouquet is padded into the support of the law at any arity `κ ≤ k`. -/
theorem chargedG_gBouquetPad {θ : Offspring J} {k κ : ℕ} (h0 : 0 < θ 0) (hk : 0 < θ k)
    (hκk : κ ≤ k) {σ : GShape} (hch : GShape.ChargedG θ k σ) (hbq : σ.bouquet = []) :
    GShape.ChargedG θ κ (gBouquetPad (k - κ) σ) := by
  obtain ⟨hN, hB⟩ := neckList_bouquet_gBouquetPad (k - κ) σ
  refine ⟨?_, ?_⟩
  · rw [hN]
    exact hch.1
  · rw [hB, hbq, List.nil_append]
    refine ⟨?_, ?_⟩
    · rw [List.length_replicate, show κ + (k - κ) = k by omega]
      exact hk
    · intro t ht
      rw [List.mem_replicate] at ht
      rw [ht.2]
      exact ⟨by simpa using h0, by simp⟩

/-! ### The addresses of the padded shape -/

/-- The addresses below a node widened by leaves: the node, and the new leaves. -/
lemma isAddr_node_append_replicate {β : List RTree} {r i : ℕ} {z : List ℕ} :
    IsAddr (.node (β ++ List.replicate r (.node []))) (i :: z) ↔
      IsAddr (.node β) (i :: z) ∨ (β.length ≤ i ∧ i < β.length + r ∧ z = []) := by
  rw [isAddr_cons, isAddr_cons]
  constructor
  · rintro ⟨h, hz⟩
    rcases lt_or_ge i β.length with hi | hi
    · refine Or.inl ⟨hi, ?_⟩
      rwa [List.getElem_append_left hi] at hz
    · refine Or.inr ⟨hi, by simpa using h, ?_⟩
      rw [List.getElem_append_right hi, List.getElem_replicate] at hz
      exact isAddr_node_nil_iff.mp hz
  · rintro (⟨hi, hz⟩ | ⟨hi, hm, rfl⟩)
    · refine ⟨by simp; omega, ?_⟩
      rwa [List.getElem_append_left hi]
    · exact ⟨by simp; omega, isAddr_nil _⟩

/-- The exit of the padded shape is the exit. -/
lemma gExitAddr_gBouquetPadDecs (r : ℕ) : ∀ L : List (List RTree),
    gExitAddr (gBouquetPadDecs r L) = gExitAddr L
  | [] => rfl
  | [β] => rfl
  | β :: γ :: rest => by
      obtain ⟨γ', rest', hr⟩ : ∃ γ' rest', gBouquetPadDecs r (γ :: rest) = γ' :: rest' := by
        cases h : gBouquetPadDecs r (γ :: rest) with
        | nil => exact absurd h (gBouquetPadDecs_ne_nil r (by simp))
        | cons γ' rest' => exact ⟨γ', rest', rfl⟩
      rw [gBouquetPadDecs_cons_cons, hr, gExitAddr_cons₂, gExitAddr_cons₂, ← hr,
        gExitAddr_gBouquetPadDecs r (γ :: rest)]

/-- Every address of the realisation is an address of the padded realisation. -/
lemma isAddr_gBouquetPadDecs (r : ℕ) : ∀ L : List (List RTree), ∀ w,
    IsAddr (GShape.realiseAux L) w → IsAddr (GShape.realiseAux (gBouquetPadDecs r L)) w
  | [], w, hw => hw
  | [β], w, hw => by
      rw [gBouquetPadDecs_singleton]
      show IsAddr (.node (β ++ List.replicate r (.node []))) w
      exact isAddr_node_append_left _ hw
  | β :: γ :: rest, [], _ => isAddr_nil _
  | β :: γ :: rest, i :: z, hw => by
      rw [realiseAux_cons_of_ne_nil _ (by simp), isAddr_node_append_single'] at hw
      rw [gBouquetPadDecs_cons_cons,
        realiseAux_cons_of_ne_nil _ (gBouquetPadDecs_ne_nil r (by simp)),
        isAddr_node_append_single']
      rcases hw with hw | ⟨rfl, hz⟩
      · exact Or.inl hw
      · exact Or.inr ⟨rfl, isAddr_gBouquetPadDecs r (γ :: rest) z hz⟩

/-- **The retraction of the bouquet padding**: an added leaf goes to the exit, every
other address stays. -/
def gBouquetPadInv : List (List RTree) → List ℕ → List ℕ
  | [], y => y
  | [_], [] => []
  | [β], i :: z => if i < β.length then i :: z else []
  | _ :: _ :: _, [] => []
  | β :: γ :: rest, i :: z => if i = β.length then i :: gBouquetPadInv (γ :: rest) z else i :: z

@[simp] lemma gBouquetPadInv_nil_list (y : List ℕ) : gBouquetPadInv [] y = y := rfl
@[simp] lemma gBouquetPadInv_singleton_nil (β : List RTree) : gBouquetPadInv [β] [] = [] := rfl
lemma gBouquetPadInv_singleton_cons (β : List RTree) (i : ℕ) (z : List ℕ) :
    gBouquetPadInv [β] (i :: z) = if i < β.length then i :: z else [] := rfl
@[simp] lemma gBouquetPadInv_cons_cons_nil (β γ : List RTree) (rest : List (List RTree)) :
    gBouquetPadInv (β :: γ :: rest) [] = [] := rfl
lemma gBouquetPadInv_cons_cons_cons (β γ : List RTree) (rest : List (List RTree)) (i : ℕ)
    (z : List ℕ) :
    gBouquetPadInv (β :: γ :: rest) (i :: z)
      = if i = β.length then i :: gBouquetPadInv (γ :: rest) z else i :: z := rfl

lemma gBouquetPadInv_nil : ∀ L : List (List RTree), gBouquetPadInv L [] = []
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- The retraction lands in the realisation. -/
lemma isAddr_gBouquetPadInv (r : ℕ) : ∀ L : List (List RTree), ∀ y,
    IsAddr (GShape.realiseAux (gBouquetPadDecs r L)) y →
      IsAddr (GShape.realiseAux L) (gBouquetPadInv L y)
  | [], y, hy => hy
  | [β], [], _ => isAddr_nil _
  | [β], i :: z, hy => by
      rw [gBouquetPadInv_singleton_cons]
      have hy' : IsAddr (.node (β ++ List.replicate r (.node []))) (i :: z) := hy
      rw [isAddr_node_append_replicate] at hy'
      split_ifs with hi
      · rcases hy' with hy' | ⟨h, -, -⟩
        · exact hy'
        · omega
      · exact isAddr_nil _
  | β :: γ :: rest, [], _ => isAddr_nil _
  | β :: γ :: rest, i :: z, hy => by
      rw [gBouquetPadDecs_cons_cons,
        realiseAux_cons_of_ne_nil _ (gBouquetPadDecs_ne_nil r (by simp)),
        isAddr_node_append_single'] at hy
      rw [gBouquetPadInv_cons_cons_cons, realiseAux_cons_of_ne_nil _ (by simp)]
      rcases hy with hy | ⟨rfl, hz⟩
      · rw [if_neg fun h ↦ not_isAddr_of_length_le (le_of_eq h.symm) hy,
          isAddr_node_append_single']
        exact Or.inl hy
      · rw [if_pos rfl, isAddr_node_append_single']
        exact Or.inr ⟨rfl, isAddr_gBouquetPadInv r (γ :: rest) z hz⟩

/-- The retraction fixes the addresses of the realisation. -/
lemma gBouquetPadInv_of_isAddr : ∀ L : List (List RTree), ∀ w,
    IsAddr (GShape.realiseAux L) w → gBouquetPadInv L w = w
  | [], _, _ => rfl
  | [β], [], _ => rfl
  | [β], i :: z, hw => by
      have hw' : IsAddr (.node β) (i :: z) := hw
      rw [isAddr_cons] at hw'
      obtain ⟨hi, -⟩ := hw'
      rw [gBouquetPadInv_singleton_cons, if_pos hi]
  | β :: γ :: rest, [], _ => rfl
  | β :: γ :: rest, i :: z, hw => by
      rw [realiseAux_cons_of_ne_nil _ (by simp), isAddr_node_append_single'] at hw
      rw [gBouquetPadInv_cons_cons_cons]
      rcases hw with hw | ⟨rfl, hz⟩
      · rw [if_neg fun h ↦ not_isAddr_of_length_le (le_of_eq h.symm) hw]
      · rw [if_pos rfl, gBouquetPadInv_of_isAddr (γ :: rest) z hz]

/-- The retraction moves parent-child pairs by at most one. -/
lemma addrDist_gBouquetPadInv_append (r : ℕ) : ∀ L : List (List RTree), ∀ y b,
    IsAddr (GShape.realiseAux (gBouquetPadDecs r L)) (y ++ [b]) →
      addrDist (gBouquetPadInv L (y ++ [b])) (gBouquetPadInv L y) ≤ 1
  | [], y, b, _ => by simp
  | [β], [], b, _ => by
      rw [List.nil_append, gBouquetPadInv_singleton_cons, gBouquetPadInv_singleton_nil]
      split_ifs <;> simp
  | [β], i :: y, b, _ => by
      rw [List.cons_append, gBouquetPadInv_singleton_cons, gBouquetPadInv_singleton_cons]
      split_ifs <;> simp
  | β :: γ :: rest, [], b, _ => by
      rw [List.nil_append, gBouquetPadInv_cons_cons_cons, gBouquetPadInv_cons_cons_nil]
      by_cases h : b = β.length
      · rw [if_pos h, gBouquetPadInv_nil]
        simp
      · rw [if_neg h]
        simp
  | β :: γ :: rest, i :: y, b, hy => by
      rw [List.cons_append, gBouquetPadDecs_cons_cons,
        realiseAux_cons_of_ne_nil _ (gBouquetPadDecs_ne_nil r (by simp)),
        isAddr_node_append_single'] at hy
      rw [List.cons_append, gBouquetPadInv_cons_cons_cons, gBouquetPadInv_cons_cons_cons]
      by_cases h : i = β.length
      · rw [if_pos h, if_pos h, addrDist_cons_cons_self]
        rcases hy with hy | ⟨-, hz⟩
        · exact absurd hy (not_isAddr_of_length_le (le_of_eq h.symm))
        · exact addrDist_gBouquetPadInv_append r (γ :: rest) y b hz
      · rw [if_neg h, if_neg h]
        simp

/-- The image is `1`-dense: every added leaf is one step from the exit. -/
lemma addrDist_gBouquetPadInv_self (r : ℕ) : ∀ L : List (List RTree), ∀ y,
    IsAddr (GShape.realiseAux (gBouquetPadDecs r L)) y →
      addrDist (gBouquetPadInv L y) y ≤ 1
  | [], y, _ => by simp
  | [β], [], _ => by simp
  | [β], i :: z, hy => by
      rw [gBouquetPadInv_singleton_cons]
      have hy' : IsAddr (.node (β ++ List.replicate r (.node []))) (i :: z) := hy
      rw [isAddr_node_append_replicate] at hy'
      split_ifs with hi
      · simp
      · rcases hy' with hy' | ⟨-, -, rfl⟩
        · rw [isAddr_cons] at hy'
          obtain ⟨h, -⟩ := hy'
          omega
        · simp
  | β :: γ :: rest, [], _ => by simp
  | β :: γ :: rest, i :: z, hy => by
      rw [gBouquetPadDecs_cons_cons,
        realiseAux_cons_of_ne_nil _ (gBouquetPadDecs_ne_nil r (by simp)),
        isAddr_node_append_single'] at hy
      rw [gBouquetPadInv_cons_cons_cons]
      by_cases h : i = β.length
      · rw [if_pos h, addrDist_cons_cons_self]
        rcases hy with hy | ⟨-, hz⟩
        · exact absurd hy (not_isAddr_of_length_le (le_of_eq h.symm))
        · exact addrDist_gBouquetPadInv_self r (γ :: rest) z hz
      · rw [if_neg h]
        simp

/-- **The bouquet padding is a `1`-marked quasi-isometry**: the inclusion of addresses
has `1`-dense image and carries the entry to the entry and the exit to the exit. -/
theorem markedQI_gBouquetPad (r : ℕ) (σ : GShape) :
    MarkedQI 1 (gShapeSpace σ) (gShapeSpace (gBouquetPad r σ)) := by
  rw [gShapeSpace_gBouquetPad]
  have h := markedQI_gSpace_of_addrMaps (K := 1) le_rfl id (gBouquetPadInv σ.decs)
    (fun w hw ↦ isAddr_gBouquetPadDecs r σ.decs w hw) (isAddr_gBouquetPadInv r σ.decs)
    (fun u a _ ↦ by simp)
    (addrDist_gBouquetPadInv_append r σ.decs)
    (fun w hw ↦ by simpa using gBouquetPadInv_of_isAddr σ.decs w hw)
    (fun y hy ↦ by simpa using addrDist_gBouquetPadInv_self r σ.decs y hy)
    (by simp)
    (isAddr_realiseAux_gExitAddr σ.decs) (isAddr_realiseAux_gExitAddr _)
    (by rw [gExitAddr_gBouquetPadDecs]; simp)
  exact_mod_cast h

/-! ### The shrinking into the support of a conditional law -/

/-- The shrinking lands with an empty bouquet. -/
lemma bouquet_gShrink (k s : ℕ) (σ : GShape) : (gShrink k s σ).bouquet = [] := by
  rw [gShrink, gShrinkOf, (neckList_bouquet_gPad _ _).2, bouquet_gNeckShape]

/-- **The shrinking into the support of `μ_κ`**: the shrinking at the support point `k`,
its bouquet padded by `k - κ` one-vertex bushes. -/
def gShrinkAt (k κ s : ℕ) (σ : GShape) : GShape := gBouquetPad (k - κ) (gShrink k s σ)

/-- **The quasi-isometry clause**: the shrinking into the support of `μ_κ` is
`648 J² s²`-marked, the composition of the `216 J² s²`-marked shrinking with the
`1`-marked bouquet padding. -/
theorem markedQI_gShrinkAt {s : ℕ} (hJ : 1 ≤ J) (hs : 1 ≤ s) {σ : GShape}
    (hσ : DegLe J σ.realise) (k κ : ℕ) :
    MarkedQI (648 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2) (gShapeSpace σ)
      (gShapeSpace (gShrinkAt k κ s σ)) := by
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hK : (1 : ℝ) ≤ 216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) ^ 2 := one_le_pow₀ hJ1
    have h2 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := one_le_pow₀ hs1
    nlinarith
  have h := markedQI_comp hK le_rfl (markedQI_gShrink hJ hs hσ k)
    (markedQI_gBouquetPad (k - κ) (gShrink k s σ))
  exact h.mono (by positivity) (le_of_eq (by ring))

/-- **The size clause**: at most `4k(n/s + 1)` vertices, the `3k(n/s + 1)` of the
shrinking and the at most `k` added bushes. -/
theorem size_gShrinkAt_le {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s) (κ : ℕ) (σ : GShape) :
    (gShrinkAt k κ s σ).size ≤ 4 * k * (σ.size / s + 1) := by
  rw [gShrinkAt, size_gBouquetPad]
  have h1 := size_gShrink_le hk hs σ
  have h2 : k - κ ≤ k := Nat.sub_le k κ
  have h3 : k ≤ k * (σ.size / s + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos _)
  generalize σ.size / s + 1 = q at h1 h3 ⊢
  nlinarith

/-- **The support clause**: the shrinking into the support of `μ_κ` is charged at the
arity `κ` once leaves and a support point `k ≥ κ` carry mass. -/
theorem chargedG_gShrinkAt {θ : Offspring J} {k κ : ℕ} (h0 : 0 < θ 0) (hk : 0 < θ k)
    (hk2 : 2 ≤ k) (hκk : κ ≤ k) (s : ℕ) (σ : GShape) :
    GShape.ChargedG θ κ (gShrinkAt k κ s σ) :=
  chargedG_gBouquetPad h0 hk hκk (chargedG_gShrink h0 hk hk2 s σ) (bouquet_gShrink k s σ)

/-! ### A shape of positive mass realises within the offspring bound -/

/-- A field with coordinates at most `J` reads as a rose tree with offspring at most
`J`, at any fuel. -/
lemma degLe_rtreeOf {d : GWord N → ℕ} (hd : ∀ v, d v ≤ J) :
    ∀ n : ℕ, DegLe J (rtreeOf n d) := by
  intro n
  induction n generalizing d with
  | zero =>
      rw [rtreeOf]
      exact ⟨by simp, by simp⟩
  | succ n ih =>
      rw [rtreeOf]
      refine ⟨?_, ?_⟩
      · rw [List.length_ofFn]
        exact le_trans (min_le_left _ _) (hd [])
      · intro c hc
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        exact ih fun v ↦ hd _

/-- A coordinate above the support bound is null under the bush law. -/
lemma bushMeasure_coord_gt_bound (θ : Offspring J) (v : GWord N) :
    bushMeasure (N := N) θ {c : GWord N → ℕ | J < c v} = 0 := by
  refine bushMeasure_absolutelyContinuous_general θ ?_
  have hdecomp : {c : GWord N → ℕ | J < c v}
      = ⋃ j : ℕ, {c : GWord N → ℕ | c v = J + 1 + j} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨c v - J - 1, by omega⟩
    · rintro ⟨j, hj⟩
      omega
  rw [hdecomp]
  refine measure_iUnion_null fun j ↦ ?_
  rw [BranchingProcess.sampleMeasure_coord θ v (J + 1 + j), θ.vanishing _ (by omega),
    ENNReal.ofReal_zero]

/-- Almost every field has coordinates at most `J`. -/
lemma bushMeasure_offspring_le_bound (θ : Offspring J) :
    bushMeasure (N := N) θ {c : GWord N → ℕ | ¬ ∀ v, c v ≤ J} = 0 := by
  have he : {c : GWord N → ℕ | ¬ ∀ v, c v ≤ J}
      = ⋃ v : GWord N, {c : GWord N → ℕ | J < c v} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall, not_le]
  rw [he]
  exact measure_iUnion_null fun v ↦ bushMeasure_coord_gt_bound θ v

/-- **A bush of positive mass has offspring at most `J`**: otherwise its fibre lies in
the null set of fields with a coordinate above `J`. -/
theorem degLe_of_bushMassR_ne_zero (θ : Offspring J) {t : RTree}
    (h : bushMassR (N := N) θ t ≠ 0) : DegLe J t := by
  by_contra hnot
  refine h (measure_mono_null (fun d hd ↦ ?_) (bushMeasure_offspring_le_bound θ))
  intro hall
  exact hnot ((hd : bushRTree d = t) ▸ degLe_rtreeOf hall _)

/-- **A neck decoration of positive mass**: its count lies in the support and its bushes
have offspring at most `J`. -/
theorem degLe_of_gDecMass_ne_zero (θ : Offspring J) {β : List RTree}
    (h : gDecMass (N := N) θ β ≠ 0) : 1 + β.length ≤ J ∧ ∀ t ∈ β, DegLe J t := by
  rw [gDecMass_def, BranchingProcess.decorationMass] at h
  obtain ⟨hw, hprod⟩ := mul_ne_zero_iff.mp h
  refine ⟨?_, fun t ht ↦ ?_⟩
  · by_contra hgt
    rw [θ.vanishing _ (by omega)] at hw
    simp at hw
  · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp ht
    have hm' : m ∈ Finset.range (1 + β.length - 1) := Finset.mem_range.mpr (by omega)
    have hfac := Finset.prod_ne_zero_iff.mp hprod m hm'
    rw [bushMeasure_listSets hm] at hfac
    exact degLe_of_bushMassR_ne_zero θ hfac

/-- **A terminating split of positive mass**: its count lies in the support and its
bouquet has offspring at most `J`. -/
theorem degLe_of_gSplitMass_ne_zero (θ : Offspring J) {κ : ℕ} {β : List RTree}
    (h : gSplitMass (N := N) θ κ β ≠ 0) : κ + β.length ≤ J ∧ ∀ t ∈ β, DegLe J t := by
  rw [gSplitMass_def, BranchingProcess.decorationMass] at h
  obtain ⟨hw, hprod⟩ := mul_ne_zero_iff.mp h
  refine ⟨?_, fun t ht ↦ ?_⟩
  · by_contra hgt
    rw [θ.vanishing _ (by omega)] at hw
    simp at hw
  · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp ht
    have hm' : m ∈ Finset.range (κ + β.length - κ) := Finset.mem_range.mpr (by omega)
    have hfac := Finset.prod_ne_zero_iff.mp hprod m hm'
    rw [bushMeasure_listSets hm] at hfac
    exact degLe_of_bushMassR_ne_zero θ hfac

/-- **A shape of positive joint mass realises with offspring at most `J`.** -/
theorem degLe_of_gPairMass_ne_zero (θ : Offspring J) {κ : ℕ} (hκ : 1 ≤ κ) {σ : GShape}
    (h : gPairMass (N := N) θ κ σ ≠ 0) : DegLe J σ.realise := by
  rw [gPairMass_def] at h
  obtain ⟨hneck, hsplit⟩ := mul_ne_zero_iff.mp h
  have hdec : ∀ β ∈ σ.neckList, gDecMass (N := N) θ β ≠ 0 := fun β hβ h0 ↦
    hneck (List.prod_eq_zero (List.mem_map.mpr ⟨β, hβ, h0⟩))
  have hmem : ∀ j : Fin σ.necks, σ.dec j.castSucc ∈ σ.neckList := by
    intro j
    rw [GShape.neckList]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  refine GShape.realise_degLe σ (fun i ↦ ?_) (fun i t ht ↦ ?_)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have := (degLe_of_gDecMass_ne_zero θ (hdec _ (hmem j))).1
      omega
    · have := (degLe_of_gSplitMass_ne_zero θ hsplit).1
      show (σ.bouquet).length + 1 ≤ J
      omega
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact (degLe_of_gDecMass_ne_zero θ (hdec _ (hmem j))).2 t ht
    · exact (degLe_of_gSplitMass_ne_zero θ hsplit).2 t ht

/-- **A shape charged by a conditional law realises with offspring at most `J`.** -/
theorem degLe_of_gCondPMF_ne_zero (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ)
    (hν : 0 < reducedWeight θ κ) {σ : GShape}
    (h : gCondPMF θ hJN hq hq0 hs1 hκ hν σ ≠ 0) : DegLe J σ.realise := by
  rw [gCondPMF_apply, gCondMass_def] at h
  refine degLe_of_gPairMass_ne_zero (N := N) θ (κ := κ) (by omega) fun h0 ↦ h ?_
  rw [h0, ENNReal.zero_div]

/-- **A shape charged by the mixture realises with offspring at most `J`.** -/
theorem degLe_of_gMixPMF_ne_zero (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {σ : GShape}
    (h : gMixPMF θ hJN hq hq0 hs1 σ ≠ 0) : DegLe J σ.realise := by
  rw [gMixPMF_apply, gMixMass] at h
  obtain ⟨j, hj⟩ : ∃ j : ℕ, gPairMass (N := N) θ (j + 2) σ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h (ENNReal.tsum_eq_zero.mpr hall)
  exact degLe_of_gPairMass_ne_zero θ (by omega) hj

/-! ### `eq:capacity` for a conditional law and the mixture -/

/-- The base of the point bound is at most one. -/
lemma gPointBase_le_one (θ : Offspring J) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) :
    gPointBase θ ≤ 1 :=
  (gPointBase_le_pminOff θ hq hq0).trans (pminOff_le_one θ)

/-- **`eq:capacity` for the pair `(μ'_κ, μ)`**: past a common threshold on the shrinking
scale and on the size cut, the fibre of a target under the shrinking into the support of
the other law carries at most half of its mass, in both directions.  The shrinking
constant is `4 max(k, k')`, the base of the point bounds the smaller of the two bases,
and the tail rate the smaller of the two rates. -/
theorem exists_gCapacity_cond_mix (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {k : ℕ} (h0 : 0 < θ 0)
    (hk : 0 < θ k) (hk2 : 2 ≤ k)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) {k' : ℕ} (h0' : 0 < θ' 0)
    (hk' : 0 < θ' k') {κ : ℕ} (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ) (hκk : κ ≤ k') :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ s Ncut : ℕ, A ≤ s → A ≤ Ncut →
      (∀ a : GShape,
        (∑' τ : {τ : GShape // Ncut < τ.size ∧ gShrinkAt k' κ s τ = a},
            gMixPMF θ hJN hq hq0 hs1 τ.1)
          ≤ gCondPMF θ' hJN' hq' hq0' hs1' hκ hν a / 2) ∧
      (∀ b : GShape,
        (∑' τ : {τ : GShape // Ncut < τ.size ∧ gShrink k s τ = b},
            gCondPMF θ' hJN' hq' hq0' hs1' hκ hν τ.1)
          ≤ gMixPMF θ hJN hq hq0 hs1 b / 2) := by
  obtain ⟨c₁, hc₁, n₁, -, htail₁⟩ := exists_gShape_size_tail θ hJN hq hq0 hs1
  obtain ⟨c₂, hc₂, n₂, htail₂, -⟩ := exists_gShape_size_tail θ' hJN' hq' hq0' hs1'
  set c : ℝ := min c₁ c₂ with hcdef
  have hc : 0 < c := lt_min hc₁ hc₂
  set p : ℝ := min (gPointBase θ) (gPointBase θ') with hpdef
  have hp0 : 0 < p := lt_min (gPointBase_pos θ hq hq0) (gPointBase_pos θ' hq' hq0')
  have hp1 : p ≤ 1 := le_trans (min_le_left _ _) (gPointBase_le_one θ hq hq0)
  have hlogp : 0 ≤ Real.log p⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hp0, hp1⟩)
  set C : ℕ := 4 * max k k' with hCdef
  have hkC : 3 * k ≤ C := by
    have := le_max_left k k'
    omega
  have hk'C : 4 * k' ≤ C := by
    have := le_max_right k k'
    omega
  have hC : 1 ≤ C := by omega
  have hCR : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hC0 : (0 : ℝ) < 4 * (C : ℝ) := by linarith
  set X : ℝ := Real.log 2 + 4 * (C : ℝ) * Real.log p⁻¹ with hXdef
  have hX0 : 0 ≤ X := by
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨max (max 1 (max n₁ n₂)) ⌈X / c⌉₊, le_trans (le_max_left 1 _) (le_max_left _ _),
    fun s Ncut hsA hNA ↦ ?_⟩
  have hs1n : 1 ≤ s := le_trans (le_trans (le_max_left 1 _) (le_max_left _ _)) hsA
  have hXs : X ≤ c * (s : ℝ) := by
    have h1 : X / c ≤ (s : ℝ) := by
      refine le_trans (Nat.le_ceil (X / c)) ?_
      exact_mod_cast le_trans (le_max_right (max 1 (max n₁ n₂)) ⌈X / c⌉₊) hsA
    rw [div_le_iff₀ hc] at h1
    linarith
  have hXN : X ≤ c * (Ncut : ℝ) := by
    have h1 : X / c ≤ (Ncut : ℝ) := by
      refine le_trans (Nat.le_ceil (X / c)) ?_
      exact_mod_cast le_trans (le_max_right (max 1 (max n₁ n₂)) ⌈X / c⌉₊) hNA
    rw [div_le_iff₀ hc] at h1
    linarith
  have hsmall : Real.log 2 + 4 * (C : ℝ) * Real.log p⁻¹ ≤ c * (Ncut : ℝ) := hXN
  have hlarge : Real.log 2 / (4 * (C : ℝ)) + Real.log p⁻¹ ≤ c * (s : ℝ) / (4 * (C : ℝ)) := by
    rw [div_add' _ _ _ hC0.ne', div_le_div_iff_of_pos_right hC0]
    linarith
  have hn₁ : n₁ ≤ Ncut := le_trans (le_trans (le_trans (le_max_left n₁ n₂) (le_max_right 1 _))
    (le_max_left _ _)) hNA
  have hn₂ : n₂ ≤ Ncut := le_trans (le_trans (le_trans (le_max_right n₁ n₂) (le_max_right 1 _))
    (le_max_left _ _)) hNA
  -- the tail bounds at the common rate
  have hrate : ∀ {c' : ℝ}, c ≤ c' → ∀ m : ℕ,
      ENNReal.ofReal (Real.exp (-c' * (m : ℝ))) ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))) := by
    intro c' hc' m
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have htailM : ∀ m : ℕ, n₁ ≤ m →
      (∑' y : GShape, if y.size ≤ m then 0 else gMixPMF θ hJN hq hq0 hs1 y)
        ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))) :=
    fun m hm ↦ le_trans (htail₁ m hm) (hrate (min_le_left _ _) m)
  have htailC : ∀ m : ℕ, n₂ ≤ m →
      (∑' y : GShape, if y.size ≤ m then 0 else gCondPMF θ' hJN' hq' hq0' hs1' hκ hν y)
        ≤ ENNReal.ofReal (Real.exp (-c * (m : ℝ))) :=
    fun m hm ↦ le_trans (htail₂ κ hκ hν m hm) (hrate (min_le_right _ _) m)
  -- the point bounds at the common base
  have hpointC : ∀ a : GShape, GShape.ChargedG θ' κ a →
      ENNReal.ofReal (p ^ a.size) ≤ gCondPMF θ' hJN' hq' hq0' hs1' hκ hν a := by
    intro a ha
    rw [gCondPMF_apply]
    refine le_trans (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ hp0.le (min_le_right _ _) a.size)) ?_
    exact ofReal_pow_le_gCondMass θ' hJN' hq' hq0' hs1' hκ ha
  have hpointM : ∀ a : GShape, GShape.ChargedG θ k a →
      ENNReal.ofReal (p ^ a.size) ≤ gMixPMF θ hJN hq hq0 hs1 a := by
    intro a ha
    rw [gMixPMF_apply]
    refine le_trans (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ hp0.le (min_le_left _ _) a.size)) ?_
    exact ofReal_pow_le_gMixMass θ hJN hq hq0 hk2 ha
  constructor
  · intro a
    refine capacity_of_mass_boundsT_const (size := GShape.size)
      (Supp := GShape.ChargedG θ' κ) (C := C) hC hs1n hp0 hp1 hc
      (fun τ ↦ chargedG_gShrinkAt h0' hk' (by omega) hκk s τ)
      (fun τ ↦ le_trans (size_gShrinkAt_le (by omega) hs1n κ τ)
        (Nat.mul_le_mul_right _ hk'C))
      hpointC htailM hn₁ hsmall hlarge a
  · intro b
    refine capacity_of_mass_boundsT_const (size := GShape.size)
      (Supp := GShape.ChargedG θ k) (C := C) hC hs1n hp0 hp1 hc
      (fun τ ↦ chargedG_gShrink h0 hk hk2 s τ)
      (fun τ ↦ le_trans (size_gShrink_le (by omega) hs1n τ) (Nat.mul_le_mul_right _ hkC))
      hpointM htailC hn₂ hsmall hlarge b

/-! ### The coupling of `thm:relabel` and `thm:cross-relabel` -/

/-- **A cascade pair through the shrinking is comparable**: a shape with offspring at
most `J` and its shrinking are `9D³`-comparable both ways, the shrinking being
`D`-marked and its quasi-inverse `3D²`-marked. -/
lemma markedQI_gShrink_pair {D s : ℕ} (hD : 1 ≤ D) (hJ : 1 ≤ J) (hs : 1 ≤ s)
    (hsD : 216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D : ℝ)) {σ : GShape}
    (hσ : DegLe J σ.realise) (k : ℕ) :
    MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace σ) (gShapeSpace (gShrink k s σ)) ∧
      MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShrink k s σ)) (gShapeSpace σ) := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hfwd : MarkedQI (D : ℝ) (gShapeSpace σ) (gShapeSpace (gShrink k s σ)) :=
    (markedQI_gShrink hJ hs hσ k).mono (by positivity) hsD
  have hback := markedQI_symm hDR hfwd
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := le_trans zero_le_one hDR
  have hsq : (1 : ℝ) ≤ (D : ℝ) ^ 2 := one_le_pow₀ hDR
  have hcube : (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 3 := by nlinarith
  exact ⟨hfwd.mono hD0 (by nlinarith), hback.mono (by nlinarith) (by nlinarith)⟩

/-- **A cascade pair through the shrinking into the support of `μ_κ` is comparable**:
a shape with offspring at most `J` and its shrinking are `9D³`-comparable both ways,
the shrinking being `3D`-marked and its quasi-inverse `27D²`-marked. -/
lemma markedQI_gShrinkAt_pair {D s : ℕ} (hD : 3 ≤ D) (hJ : 1 ≤ J) (hs : 1 ≤ s)
    (hsD : 216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D : ℝ)) {σ : GShape}
    (hσ : DegLe J σ.realise) (k κ : ℕ) :
    MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace σ) (gShapeSpace (gShrinkAt k κ s σ)) ∧
      MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShrinkAt k κ s σ)) (gShapeSpace σ) := by
  have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hfwd : MarkedQI (3 * (D : ℝ)) (gShapeSpace σ) (gShapeSpace (gShrinkAt k κ s σ)) :=
    (markedQI_gShrinkAt hJ hs hσ k κ).mono (by positivity) (by linarith)
  have hback := markedQI_symm (by linarith) hfwd
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := by linarith
  have hsq : (9 : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have hcube : 3 * (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 3 := by nlinarith
  exact ⟨hfwd.mono (by positivity) (by nlinarith), hback.mono (by nlinarith) (by nlinarith)⟩

/-- **`thm:cross-relabel`, the coupling**: the cascade of `thm:shape-coupling`, run for
the pair `(μ'_κ, μ)` of a conditional law of `θ'` and the mixture of `θ`, produces a
coupling supported on `9D³`-comparable pairs at every `D` past a threshold depending on
the two laws.  The shrinking of the `μ'_κ` side lands in the support of `μ` at a support
point `k` of `θ`, the shrinking of the `μ` side in the support of `μ'_κ` at a support
point `k' ≥ κ` of `θ'`, both at the scale `⌊√(D/216 max(J,J')²)⌋` with the cut `D²`;
the mass bounds are those of `thm:mass-uniform`. -/
theorem exists_gShapeCoupling_cond_mix (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {k : ℕ}
    (h0 : 0 < θ 0) (hk : 0 < θ k) (hk2 : 2 ≤ k)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) {k' : ℕ} (h0' : 0 < θ' 0)
    (hk' : 0 < θ' k') {κ : ℕ} (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ) (hκk : κ ≤ k') :
    ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → ∃ π : PMF (GShape × GShape),
      IsGShapeCoupling (D : ℝ) (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν)
        (gMixPMF θ hJN hq hq0 hs1) π := by
  obtain ⟨A, hA1, hA⟩ := exists_gCapacity_cond_mix θ hJN hq hq0 hs1 h0 hk hk2 θ' hJN' hq'
    hq0' hs1' h0' hk' hκ hν hκk
  have hJ : 1 ≤ J := by
    have := offspring_le_of_pos θ hk
    omega
  have hJ' : 1 ≤ J' := by
    have := offspring_le_of_pos θ' hk'
    omega
  set M : ℕ := max J J' with hMdef
  have hM : 1 ≤ M := le_trans hJ (le_max_left _ _)
  refine ⟨max 30 (216 * M ^ 2 * (A * A) + A), fun D hD ↦ ?_⟩
  have hD30 : 30 ≤ D := le_trans (le_max_left _ _) hD
  have hDA : 216 * M ^ 2 * (A * A) + A ≤ D := le_trans (le_max_right _ _) hD
  have hD1 : 1 ≤ D := by omega
  -- the shrinking scale
  set s : ℕ := gShrinkScale M D with hsdef
  have hsqrt : A * A ≤ D / (216 * M ^ 2) := by
    refine (Nat.le_div_iff_mul_le (by positivity)).mpr ?_
    calc A * A * (216 * M ^ 2) = 216 * M ^ 2 * (A * A) := by ring
      _ ≤ D := by omega
  have hsA : A ≤ s := by
    have h := Nat.sqrt_le_sqrt hsqrt
    rwa [Nat.sqrt_eq] at h
  have hs1n : 1 ≤ s := le_trans hA1 hsA
  have hsD : 216 * (M : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D : ℝ) := gShrinkScale_le M D
  have hJM : (J : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left J J'
  have hJ'M : (J' : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_right J J'
  have hsDJ : 216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D : ℝ) :=
    le_trans (by gcongr) hsD
  have hsDJ' : 216 * (J' : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D : ℝ) :=
    le_trans (by gcongr) hsD
  have hND : A ≤ D ^ 2 := by nlinarith
  obtain ⟨hcap₁, hcap₂⟩ := hA s (D ^ 2) hsA hND
  -- the small pairs
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hsize : ∀ a : GShape, ¬ (D ^ 2 < a.size) → (a.size : ℝ) ≤ (D : ℝ) ^ 2 := by
    intro a ha
    have h : a.size ≤ D ^ 2 := by omega
    exact_mod_cast h
  have hsq : (1 : ℝ) ≤ (D : ℝ) ^ 2 := one_le_pow₀ hDR
  have hcube : (D : ℝ) ^ 2 ≤ 9 * (D : ℝ) ^ 3 := by nlinarith
  refine exists_gShapeCoupling_of_capacity₂' (fun σ ↦ D ^ 2 < σ.size) (gShrinkAt k' κ s)
    (gShrink k s) ?_ ?_ ?_ hcap₁ hcap₂
  · intro σ _ hσ
    exact markedQI_gShrink_pair hD1 hJ' hs1n hsDJ'
      (degLe_of_gCondPMF_ne_zero θ' hJN' hq' hq0' hs1' hκ hν hσ) k
  · intro σ _ hσ
    exact markedQI_gShrinkAt_pair (by omega) hJ hs1n hsDJ
      (degLe_of_gMixPMF_ne_zero θ hJN hq hq0 hs1 hσ) k' κ
  · intro σ τ hσ hτ _ _
    exact ⟨(markedQI_gSmallPair hsq σ τ (hsize σ hσ) (hsize τ hτ)).mono (by positivity) hcube,
      (markedQI_gSmallPair hsq τ σ (hsize τ hτ) (hsize σ hσ)).mono (by positivity) hcube⟩

/-- **`thm:relabel`, the coupling**: the cascade of `thm:shape-coupling`, run for the pair
`(μ_κ, μ)` of a conditional law and the mixture of one law, produces a coupling supported
on `9D³`-comparable pairs at every `D` past a threshold depending on the law. -/
theorem exists_gShapeCoupling_relabel (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {k : ℕ}
    (h0 : 0 < θ 0) (hk : 0 < θ k) (hk2 : 2 ≤ k) {κ : ℕ} (hκ : 2 ≤ κ)
    (hν : 0 < reducedWeight θ κ) (hκk : κ ≤ k) :
    ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → ∃ π : PMF (GShape × GShape),
      IsGShapeCoupling (D : ℝ) (gCondPMF θ hJN hq hq0 hs1 hκ hν) (gMixPMF θ hJN hq hq0 hs1) π :=
  exists_gShapeCoupling_cond_mix θ hJN hq hq0 hs1 h0 hk hk2 θ hJN hq hq0 hs1 h0 hk hκ hν hκk

end ChainClasses
