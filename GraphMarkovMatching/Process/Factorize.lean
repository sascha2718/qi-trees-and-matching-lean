/-
The multi-member Hall factorization behind the screen outputs of the
transfer rows (`arbitrary_offspring_matching.tex` `sec:rows`),
generalizing the single-target `deadScreen_factorize` of the ledger to a
finite list of product targets: when every member target is square-dead
at a source pair, the Hall classification of `thm:hall` routes all zero
requirements through one distinguished child (linear terms, the
successor screens over the full component list) or splits them across
the two children (quadratic products of singleton screens).

* `hallInd_le`: the pointwise indicator bound: the dead-event
  indicator is below the two child zero-event indicators plus the
  product of the two dead-component counting sums;
* `hallFactorize`: the integrated form: the tilted dead-event mass is
  below two full-list screens times tilted moments plus a product of
  summed singleton screens.
-/
import GraphMarkovMatching.Process.Coordinates

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### List calculus -/

/-- In `ℝ≥0∞` every member of a list is at most the list sum. -/
private lemma le_list_sum {a : ℝ≥0∞} {l : List ℝ≥0∞} (h : a ∈ l) :
    a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_self_add
    · exact le_trans (ih h') le_add_self

/-- One dead member makes the dead-component counting sum at least one. -/
private lemma one_le_deadSum {X : Type} (R : X → X → Prop)
    (zs : List (PMF X)) (x : X) {t : PMF X} (htz : t ∈ zs)
    (ht0 : rE t R x = 0) :
    (1 : ℝ≥0∞)
      ≤ (zs.map fun ρ => if rE ρ R x = 0 then (1 : ℝ≥0∞) else 0).sum := by
  have hm : (if rE t R x = 0 then (1 : ℝ≥0∞) else 0)
      ∈ zs.map fun ρ => if rE ρ R x = 0 then (1 : ℝ≥0∞) else 0 :=
    List.mem_map.mpr ⟨t, htz, rfl⟩
  calc (1 : ℝ≥0∞) = if rE t R x = 0 then (1 : ℝ≥0∞) else 0 :=
        (if_pos ht0).symm
    _ ≤ _ := le_list_sum hm

/-- The tilted mass of the dead-component counting sum is the sum of the
singleton screens. -/
private lemma tsum_deadSum_eq {X : Type} (ρs : PMF X) (R : X → X → Prop)
    (zs : List (PMF X)) (G : X → ℝ≥0∞) :
    ∑' x, ρs x
        * ((zs.map fun ρ => if rE ρ R x = 0 then (1 : ℝ≥0∞) else 0).sum)
        * G x
      = (zs.map fun ρ => screenE ρs R [ρ] G).sum := by
  induction zs with
  | nil => simp
  | cons ρc t ih =>
    have hpt : ∀ x, ρs x
        * (((ρc :: t).map fun ρ =>
            if rE ρ R x = 0 then (1 : ℝ≥0∞) else 0).sum)
        * G x
        = ρs x * ((if rE ρc R x = 0 then (1 : ℝ≥0∞) else 0) * G x)
          + ρs x
            * ((t.map fun ρ => if rE ρ R x = 0 then (1 : ℝ≥0∞) else 0).sum)
            * G x := by
      intro x
      rw [List.map_cons, List.sum_cons]
      ring
    rw [tsum_congr hpt, ENNReal.tsum_add, ← screenE_singleton, ih,
      List.map_cons, List.sum_cons]

/-! ### The Hall indicator bound -/

/-- **The pointwise Hall routing** (`sec:rows`, the pointwise bound of
`thm:hall-factor`; the zero-row/zero-column dichotomy of `thm:hall`
applied to every member):
if every member target of `ms` is square-dead at `(x₀, x₁)`, then either
one child is dead against the whole component list `zs` (a full zero
event at that child), or each child kills some component, in which case
the product of the two dead-component counting sums is at least one. -/
lemma hallInd_le {X : Type} (R : X → X → Prop) (ms : List (PMF X × PMF X))
    (zs : List (PMF X))
    (hmem : ∀ p ∈ ms, p.1 ∈ zs ∧ p.2 ∈ zs)
    (hcov : ∀ ρ ∈ zs, ∃ p ∈ ms, ρ = p.1 ∨ ρ = p.2) (x₀ x₁ : X) :
    (if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) (x₀, x₁) = 0
        then (1 : ℝ≥0∞) else 0)
      ≤ screenInd R zs x₀ + screenInd R zs x₁
        + ((zs.map fun ρ => if rE ρ R x₀ = 0 then (1 : ℝ≥0∞) else 0).sum)
          * ((zs.map fun ρ => if rE ρ R x₁ = 0 then (1 : ℝ≥0∞) else 0).sum) := by
  by_cases hms : ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) (x₀, x₁) = 0
  case neg => rw [if_neg hms]; exact zero_le
  rw [if_pos hms]
  -- the quadratic escape: one dead witness at each child
  have hprod : ∀ t₀ ∈ zs, rE t₀ R x₀ = 0 → ∀ t₁ ∈ zs, rE t₁ R x₁ = 0 →
      (1 : ℝ≥0∞) ≤ screenInd R zs x₀ + screenInd R zs x₁
        + ((zs.map fun ρ => if rE ρ R x₀ = 0 then (1 : ℝ≥0∞) else 0).sum)
          * ((zs.map fun ρ => if rE ρ R x₁ = 0 then (1 : ℝ≥0∞) else 0).sum) := by
    intro t₀ ht₀z ht₀ t₁ ht₁z ht₁
    refine le_trans ?_ le_add_self
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ _ := mul_le_mul' (one_le_deadSum R zs x₀ ht₀z ht₀)
          (one_le_deadSum R zs x₁ ht₁z ht₁)
  by_cases hall0 : ∀ ρ ∈ zs, rE ρ R x₀ = 0
  · calc (1 : ℝ≥0∞) = screenInd R zs x₀ := by rw [screenInd, if_pos hall0]
      _ ≤ screenInd R zs x₀ + screenInd R zs x₁ := le_self_add
      _ ≤ _ := le_self_add
  by_cases hall1 : ∀ ρ ∈ zs, rE ρ R x₁ = 0
  · calc (1 : ℝ≥0∞) = screenInd R zs x₁ := by rw [screenInd, if_pos hall1]
      _ ≤ screenInd R zs x₀ + screenInd R zs x₁ := le_add_self
      _ ≤ _ := le_self_add
  -- both children see a live component: extract the two witnesses
  push Not at hall0 hall1
  obtain ⟨ρ₀, hρ₀z, hρ₀⟩ := hall0
  obtain ⟨ρ₁, hρ₁z, hρ₁⟩ := hall1
  obtain ⟨p, hpm, hρ₀p⟩ := hcov ρ₀ hρ₀z
  obtain ⟨p', hpm', hρ₁p'⟩ := hcov ρ₁ hρ₁z
  -- the member covering the x₀-live component kills something at x₁
  have hw1 : (∃ t ∈ zs, rE t R x₀ = 0 ∧ rE t R x₁ = 0)
      ∨ (∃ t ∈ zs, rE t R x₁ = 0) := by
    have hnr0 : ¬ (rE p.1 R x₀ = 0 ∧ rE p.2 R x₀ = 0) := by
      rintro ⟨h1, h2⟩
      rcases hρ₀p with rfl | rfl
      · exact hρ₀ h1
      · exact hρ₀ h2
    rcases (rE_square_eq_zero_iff_hall p.1 p.2 R x₀ x₁).mp (hms p hpm) with
      (hrow0 | hrow1) | (hcol1 | hcol2)
    · exact absurd hrow0 hnr0
    · exact Or.inr ⟨p.1, (hmem p hpm).1, hrow1.1⟩
    · exact Or.inl ⟨p.1, (hmem p hpm).1, hcol1⟩
    · exact Or.inl ⟨p.2, (hmem p hpm).2, hcol2⟩
  -- the member covering the x₁-live component kills something at x₀
  have hw0 : (∃ t ∈ zs, rE t R x₀ = 0 ∧ rE t R x₁ = 0)
      ∨ (∃ t ∈ zs, rE t R x₀ = 0) := by
    have hnr1 : ¬ (rE p'.1 R x₁ = 0 ∧ rE p'.2 R x₁ = 0) := by
      rintro ⟨h1, h2⟩
      rcases hρ₁p' with rfl | rfl
      · exact hρ₁ h1
      · exact hρ₁ h2
    rcases (rE_square_eq_zero_iff_hall p'.1 p'.2 R x₀ x₁).mp (hms p' hpm') with
      (hrow0 | hrow1) | (hcol1 | hcol2)
    · exact Or.inr ⟨p'.1, (hmem p' hpm').1, hrow0.1⟩
    · exact absurd hrow1 hnr1
    · exact Or.inl ⟨p'.1, (hmem p' hpm').1, hcol1⟩
    · exact Or.inl ⟨p'.2, (hmem p' hpm').2, hcol2⟩
  rcases hw1 with ⟨t, htz, ht0, ht1⟩ | ⟨t₁, ht₁z, ht₁⟩
  · exact hprod t htz ht0 t htz ht1
  rcases hw0 with ⟨t, htz, ht0, ht1⟩ | ⟨t₀, ht₀z, ht₀⟩
  · exact hprod t htz ht0 t htz ht1
  · exact hprod t₀ ht₀z ht₀ t₁ ht₁z ht₁

/-! ### The integrated Hall factorization -/

/-- **The multi-member Hall factorization** (`sec:rows`,
`thm:hall-factor`): the tilted mass of the joint dead event of a finite member
list splits into two full-list screens times tilted moments (all zero
requirements routed through one child) plus a product of summed
singleton screens (requirements split across the children). -/
lemma hallFactorize {X : Type} (ρa ρb : PMF X) (R : X → X → Prop)
    (ms : List (PMF X × PMF X)) (zs : List (PMF X))
    (hmem : ∀ p ∈ ms, p.1 ∈ zs ∧ p.2 ∈ zs)
    (hcov : ∀ ρ ∈ zs, ∃ p ∈ ms, ρ = p.1 ∨ ρ = p.2)
    (G₀ G₁ : X → ℝ≥0∞) :
    ∑' xp : X × X, prodPMF ρa ρb xp
        * ((if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
              then (1 : ℝ≥0∞) else 0)
          * (G₀ xp.1 * G₁ xp.2))
      ≤ screenE ρa R zs G₀ * (∑' x, ρb x * G₁ x)
        + (∑' x, ρa x * G₀ x) * screenE ρb R zs G₁
        + (zs.map fun ρ => screenE ρa R [ρ] G₀).sum
          * (zs.map fun ρ' => screenE ρb R [ρ'] G₁).sum := by
  have hpt : ∀ xp : X × X, prodPMF ρa ρb xp
      * ((if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
            then (1 : ℝ≥0∞) else 0)
        * (G₀ xp.1 * G₁ xp.2))
      ≤ prodPMF ρa ρb xp * (screenInd R zs xp.1 * (G₀ xp.1 * G₁ xp.2))
        + prodPMF ρa ρb xp * (screenInd R zs xp.2 * (G₀ xp.1 * G₁ xp.2))
        + prodPMF ρa ρb xp
          * (((zs.map fun ρ => if rE ρ R xp.1 = 0 then (1 : ℝ≥0∞) else 0).sum
              * (zs.map fun ρ => if rE ρ R xp.2 = 0 then (1 : ℝ≥0∞) else 0).sum)
            * (G₀ xp.1 * G₁ xp.2)) := by
    rintro ⟨x₀, x₁⟩
    refine le_trans (mul_le_mul_right
      (mul_le_mul_left (hallInd_le R ms zs hmem hcov x₀ x₁) _) _)
      (le_of_eq ?_)
    ring
  calc ∑' xp : X × X, prodPMF ρa ρb xp
        * ((if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
              then (1 : ℝ≥0∞) else 0)
          * (G₀ xp.1 * G₁ xp.2))
      ≤ (∑' xp : X × X, prodPMF ρa ρb xp
          * (screenInd R zs xp.1 * (G₀ xp.1 * G₁ xp.2)))
        + (∑' xp : X × X, prodPMF ρa ρb xp
          * (screenInd R zs xp.2 * (G₀ xp.1 * G₁ xp.2)))
        + (∑' xp : X × X, prodPMF ρa ρb xp
          * (((zs.map fun ρ => if rE ρ R xp.1 = 0 then (1 : ℝ≥0∞) else 0).sum
              * (zs.map fun ρ => if rE ρ R xp.2 = 0 then (1 : ℝ≥0∞) else 0).sum)
            * (G₀ xp.1 * G₁ xp.2))) := by
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum hpt
    _ = screenE ρa R zs G₀ * (∑' x, ρb x * G₁ x)
        + (∑' x, ρa x * G₀ x) * screenE ρb R zs G₁
        + (zs.map fun ρ => screenE ρa R [ρ] G₀).sum
          * (zs.map fun ρ' => screenE ρb R [ρ'] G₁).sum := by
        have e0 : (∑' xp : X × X, prodPMF ρa ρb xp
            * (screenInd R zs xp.1 * (G₀ xp.1 * G₁ xp.2)))
            = screenE ρa R zs G₀ * (∑' x, ρb x * G₁ x) := by
          rw [tsum_congr fun xp : X × X => show prodPMF ρa ρb xp
              * (screenInd R zs xp.1 * (G₀ xp.1 * G₁ xp.2))
              = (ρa xp.1 * screenInd R zs xp.1 * G₀ xp.1)
                * (ρb xp.2 * G₁ xp.2)
              from by rw [prodPMF_apply]; ring,
            tsum_prod_split (fun x => ρa x * screenInd R zs x * G₀ x)
              (fun x => ρb x * G₁ x), screenE]
        have e1 : (∑' xp : X × X, prodPMF ρa ρb xp
            * (screenInd R zs xp.2 * (G₀ xp.1 * G₁ xp.2)))
            = (∑' x, ρa x * G₀ x) * screenE ρb R zs G₁ := by
          rw [tsum_congr fun xp : X × X => show prodPMF ρa ρb xp
              * (screenInd R zs xp.2 * (G₀ xp.1 * G₁ xp.2))
              = (ρa xp.1 * G₀ xp.1)
                * (ρb xp.2 * screenInd R zs xp.2 * G₁ xp.2)
              from by rw [prodPMF_apply]; ring,
            tsum_prod_split (fun x => ρa x * G₀ x)
              (fun x => ρb x * screenInd R zs x * G₁ x), screenE]
        have e2 : (∑' xp : X × X, prodPMF ρa ρb xp
            * (((zs.map fun ρ =>
                  if rE ρ R xp.1 = 0 then (1 : ℝ≥0∞) else 0).sum
                * (zs.map fun ρ =>
                  if rE ρ R xp.2 = 0 then (1 : ℝ≥0∞) else 0).sum)
              * (G₀ xp.1 * G₁ xp.2)))
            = (zs.map fun ρ => screenE ρa R [ρ] G₀).sum
              * (zs.map fun ρ' => screenE ρb R [ρ'] G₁).sum := by
          rw [tsum_congr fun xp : X × X => show prodPMF ρa ρb xp
              * (((zs.map fun ρ =>
                    if rE ρ R xp.1 = 0 then (1 : ℝ≥0∞) else 0).sum
                  * (zs.map fun ρ =>
                    if rE ρ R xp.2 = 0 then (1 : ℝ≥0∞) else 0).sum)
                * (G₀ xp.1 * G₁ xp.2))
              = (ρa xp.1
                  * (zs.map fun ρ =>
                    if rE ρ R xp.1 = 0 then (1 : ℝ≥0∞) else 0).sum
                  * G₀ xp.1)
                * (ρb xp.2
                  * (zs.map fun ρ =>
                    if rE ρ R xp.2 = 0 then (1 : ℝ≥0∞) else 0).sum
                  * G₁ xp.2)
              from by rw [prodPMF_apply]; ring,
            tsum_prod_split
              (fun x => ρa x
                * (zs.map fun ρ =>
                  if rE ρ R x = 0 then (1 : ℝ≥0∞) else 0).sum * G₀ x)
              (fun x => ρb x
                * (zs.map fun ρ =>
                  if rE ρ R x = 0 then (1 : ℝ≥0∞) else 0).sum * G₁ x),
            tsum_deadSum_eq ρa R zs G₀, tsum_deadSum_eq ρb R zs G₁]
        rw [e0, e1, e2]

end GraphMarkovMatching
