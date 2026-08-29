/-
Exact binary prefix templates and direct Hall minorization for grafted rare
counters.  The 11 template is obtained by grafting a balanced 5 counter into
the unique depth-two leaf of the balanced 7 template; the 13 template grafts
a balanced 5 counter into a fixed depth-three leaf of the balanced 9 template.
-/
import GraphMarkovMatching.Obstructions.DepthPairing
import GraphMarkovMatching.Closure.RareMatrix

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

def graftFrontier (F : List BinaryAddress) (u : BinaryAddress)
    (G : List BinaryAddress) : List BinaryAddress :=
  (F.filter (· != u)) ++ G.map (u ++ ·)

def counterSevenFreshFrontier : List BinaryAddress :=
  counterFreshFrontier 7

def counterNineFreshFrontier : List BinaryAddress :=
  counterFreshFrontier 9

def graftedElevenFreshFrontier : List BinaryAddress :=
  graftFrontier counterSevenFreshFrontier [false, true]
    counterFiveFreshFrontier

def graftedThirteenFreshFrontier : List BinaryAddress :=
  graftFrontier counterNineFreshFrontier [true, true, true]
    counterFiveFreshFrontier

@[simp] theorem counterFreshFrontier_seven :
    counterFreshFrontier 7 =
      [[false, false, false], [false, false, true], [false, true],
       [true, false, false], [true, false, true],
       [true, true, false], [true, true, true]] := by
  simp [counterFreshFrontier, prefixFrontier]

@[simp] theorem counterFreshFrontier_nine :
    counterFreshFrontier 9 =
      [[false, false, false], [false, false, true],
       [false, true, false], [false, true, true],
       [true, false, false], [true, false, true],
       [true, true, false, false], [true, true, false, true],
       [true, true, true]] := by
  simp [counterFreshFrontier, prefixFrontier]

@[simp] theorem graftedElevenFreshFrontier_eq :
    graftedElevenFreshFrontier =
      [[false, false, false], [false, false, true],
       [true, false, false], [true, false, true],
       [true, true, false], [true, true, true],
       [false, true, false, false], [false, true, false, true],
       [false, true, true, false, false],
       [false, true, true, false, true],
       [false, true, true, true]] := by
  simp [graftedElevenFreshFrontier, graftFrontier,
    counterSevenFreshFrontier, counterFiveFreshFrontier]

@[simp] theorem graftedThirteenFreshFrontier_eq :
    graftedThirteenFreshFrontier =
      [[false, false, false], [false, false, true],
       [false, true, false], [false, true, true],
       [true, false, false], [true, false, true],
       [true, true, false, false], [true, true, false, true],
       [true, true, true, false, false],
       [true, true, true, false, true],
       [true, true, true, true, false, false],
       [true, true, true, true, false, true],
       [true, true, true, true, true]] := by
  simp [graftedThirteenFreshFrontier, graftFrontier,
    counterNineFreshFrontier, counterFiveFreshFrontier]

def frontierDepthCount (F : List BinaryAddress) (d : ℕ) : ℕ :=
  (F.filter (fun u => u.length = d)).length

def PrefixFreeFrontier (F : List BinaryAddress) : Prop :=
  F.Nodup ∧ ∀ u ∈ F, ∀ v ∈ F, u <+: v → u = v

def kraftNumerator (F : List BinaryAddress) (D : ℕ) : ℕ :=
  (F.map fun u => 2 ^ (D - u.length)).sum

theorem graftedEleven_depth_profile :
    frontierDepthCount graftedElevenFreshFrontier 3 = 6 ∧
    frontierDepthCount graftedElevenFreshFrontier 4 = 3 ∧
    frontierDepthCount graftedElevenFreshFrontier 5 = 2 ∧
    graftedElevenFreshFrontier.length = 11 := by
  rw [graftedElevenFreshFrontier_eq]
  decide

theorem graftedThirteen_depth_profile :
    frontierDepthCount graftedThirteenFreshFrontier 3 = 6 ∧
    frontierDepthCount graftedThirteenFreshFrontier 4 = 2 ∧
    frontierDepthCount graftedThirteenFreshFrontier 5 = 3 ∧
    frontierDepthCount graftedThirteenFreshFrontier 6 = 2 ∧
    graftedThirteenFreshFrontier.length = 13 := by
  rw [graftedThirteenFreshFrontier_eq]
  decide

theorem graftedEleven_prefixFree :
    PrefixFreeFrontier graftedElevenFreshFrontier := by
  simp [PrefixFreeFrontier]

theorem graftedThirteen_prefixFree :
    PrefixFreeFrontier graftedThirteenFreshFrontier := by
  simp [PrefixFreeFrontier]

/-- Kraft equality at the maximal depth: the eleven addresses are the leaves
of a complete finite binary template. -/
theorem graftedEleven_kraft :
    kraftNumerator graftedElevenFreshFrontier 5 = 2 ^ 5 := by
  rw [graftedElevenFreshFrontier_eq]
  decide

/-- The corresponding completeness check for the thirteen template. -/
theorem graftedThirteen_kraft :
    kraftNumerator graftedThirteenFreshFrontier 6 = 2 ^ 6 := by
  rw [graftedThirteenFreshFrontier_eq]
  decide

noncomputable def replacementMass (wRoot mu0 wFive : ℝ≥0∞) : ℝ≥0∞ :=
  wRoot * mu0 * wFive

lemma replacementMass_half_lower {wRoot mu0 wFive : ℝ≥0∞}
    (hmu : 2⁻¹ ≤ mu0) :
    2⁻¹ * (wRoot * wFive) ≤ replacementMass wRoot mu0 wFive := by
  dsimp [replacementMass]
  calc
    2⁻¹ * (wRoot * wFive) = wRoot * 2⁻¹ * wFive := by ring
    _ ≤ wRoot * mu0 * wFive := by gcongr

lemma rare_rpow_price_le {ε p c : ℝ≥0∞} {α : ℝ}
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤)
    (hε : ε ≤ c * p ^ α) :
    ε * p ^ (-α) ≤ c := by
  calc
    ε * p ^ (-α) ≤ (c * p ^ α) * p ^ (-α) := by gcongr
    _ = c * (p ^ α * p ^ (-α)) := by ring
    _ = c := by
      rw [← ENNReal.rpow_add α (-α) hp0 hpT, add_neg_cancel,
        ENNReal.rpow_zero, mul_one]

section HallMinorization

variable {X : Type}

/-- A replacement component with positive good degree on every charged
source atom removes the zero interface after it is inserted with positive
mass into the target law. -/
lemma zMass_eq_zero_of_replacement_component
    (ρs ρrep ρt : PMF X) (R : X → X → Prop)
    {p : ℝ≥0∞} (hp : p ≠ 0)
    (hsupp : ∀ x, ρs x ≠ 0 → rE ρrep R x ≠ 0)
    (hmin : ∀ x, p * rE ρrep R x ≤ rE ρt R x) :
    zMass ρs ρt R = 0 := by
  rw [zMass]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : ρs x = 0
  · simp [hx]
  · have hrt : rE ρt R x ≠ 0 := by
      intro hrt0
      have hm := hmin x
      rw [hrt0] at hm
      exact (mul_ne_zero hp (hsupp x hx)) (le_antisymm hm zero_le)
    simp [hrt]

/-- A positive replacement component removes the zero interface. -/
lemma zMass_eq_zero_of_replacement_minorization
    (ρs ρt : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    {p : ℝ≥0∞} (hp : p ≠ 0)
    (hmin : ∀ x, p * rE ρs R x ≤ rE ρt R x) :
    zMass ρs ρt R = 0 := by
  rw [zMass]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : ρs x = 0
  · simp [hx]
  · have hrs : rE ρs R x ≠ 0 := by
      intro hrs0
      have hxx : ρs x ≤ rE ρs R x := le_rE_of_refl (hrefl x)
      rw [hrs0] at hxx
      exact hx (le_antisymm hxx zero_le)
    have hrt : rE ρt R x ≠ 0 := by
      intro hrt0
      have hm := hmin x
      rw [hrt0] at hm
      exact (mul_ne_zero hp hrs) (le_antisymm hm zero_le)
    simp [hrt]

lemma WresD_le_replacement_minorization {α : ℝ} (hα : 0 ≤ α)
    (ρs ρt : PMF X) (R : X → X → Prop) {p : ℝ≥0∞}
    (hp0 : p ≠ 0)
    (hmin : ∀ x, p * rE ρs R x ≤ rE ρt R x)
    {x : X} (hrs : rE ρs R x ≠ 0) :
    WresD α ρt R x ≤ p ^ (-α) * WresD α ρs R x := by
  have hrt : rE ρt R x ≠ 0 := by
    intro hrt0
    have hm := hmin x
    rw [hrt0] at hm
    exact (mul_ne_zero hp0 hrs) (le_antisymm hm zero_le)
  rw [← rE_rpow_neg_eq_WresD ρt R x hrt,
    ← rE_rpow_neg_eq_WresD ρs R x hrs]
  calc
    (rE ρt R x) ^ (-α)
        ≤ (p * rE ρs R x) ^ (-α) :=
      rpow_neg_antitone hα (hmin x)
    _ = p ^ (-α) * (rE ρs R x) ^ (-α) := by
      rw [ENNReal.mul_rpow_of_ne_zero hp0 hrs]

/-- The inverse tilt toward a target containing a replacement component is
priced by the component mass and the inverse tilt toward that component. -/
lemma WresD_le_replacement_component {α : ℝ} (hα : 0 ≤ α)
    (ρrep ρt : PMF X) (R : X → X → Prop) {p : ℝ≥0∞}
    (hp0 : p ≠ 0)
    (hmin : ∀ x, p * rE ρrep R x ≤ rE ρt R x)
    {x : X} (hrep : rE ρrep R x ≠ 0) :
    WresD α ρt R x ≤ p ^ (-α) * WresD α ρrep R x := by
  exact WresD_le_replacement_minorization hα ρrep ρt R hp0 hmin hrep

lemma PhiDres_le_tsum_WresD {α : ℝ} (hα : 0 < α)
    (ρs ρt : PMF X) (R : X → X → Prop) :
    PhiDres α ρs ρt R ≤ ∑' x, ρs x * WresD α ρt R x := by
  rw [PhiDres]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hrt : rE ρt R x = 0
  · simp [hrt, WresD]
  · rw [if_neg hrt, ← rE_rpow_neg_eq_WresD ρt R x hrt]
    rw [phiE_eq_qE_mul_rpow α R ρt hα x]
    have hinner : qE ρt R x * (rE ρt R x) ^ (-α)
        ≤ 1 * (rE ρt R x) ^ (-α) :=
      mul_le_mul_left qE_le_one _
    calc
      ρs x * (qE ρt R x * (rE ρt R x) ^ (-α))
          ≤ ρs x * (1 * (rE ρt R x) ^ (-α)) :=
        mul_le_mul_right hinner _
      _ = ρs x * (rE ρt R x) ^ (-α) := by rw [one_mul]

/-- **Direct replacement Hall bound.**  Once a finite macro replacement is
visible with mass `p`, its cross potential has only the single inverse price
`p^{-α}`.  The right side is the ordinary potential toward the replacement
component; no path resolvent or Green denominator occurs. -/
lemma PhiDres_le_of_replacement_component {α : ℝ} (hα : 1 ≤ α)
    (ρs ρrep ρt : PMF X) (R : X → X → Prop)
    {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hsupp : ∀ x, ρs x ≠ 0 → rE ρrep R x ≠ 0)
    (hmin : ∀ x, p * rE ρrep R x ≤ rE ρt R x) :
    PhiDres α ρs ρt R
      ≤ p ^ (-α) *
        (1 + ENNReal.ofReal α * PhiDres α ρs ρrep R) := by
  calc
    PhiDres α ρs ρt R
        ≤ ∑' x, ρs x * WresD α ρt R x :=
      PhiDres_le_tsum_WresD (by linarith) ρs ρt R
    _ ≤ ∑' x, ρs x * (p ^ (-α) * WresD α ρrep R x) := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : ρs x = 0
      · simp [hx]
      · exact mul_le_mul_right
          (WresD_le_replacement_component (by linarith)
            ρrep ρt R hp0 hmin (hsupp x hx)) _
    _ = ∑' x, p ^ (-α) * (ρs x * WresD α ρrep R x) := by
      apply tsum_congr
      intro x
      ring
    _ = p ^ (-α) * ∑' x, ρs x * WresD α ρrep R x := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ p ^ (-α) *
        (1 + ENNReal.ofReal α * PhiDres α ρs ρrep R) := by
      gcongr
      exact tsum_WresD_le hα ρs ρrep R

/-- The corresponding rare-mass estimate.  The condition
`ε ≤ c p^α` cancels the only inverse replacement price. -/
lemma rare_mul_PhiDres_le_of_replacement_component
    {α : ℝ} (hα : 1 ≤ α)
    (ρs ρrep ρt : PMF X) (R : X → X → Prop)
    {ε p c : ℝ≥0∞} (hp0 : p ≠ 0) (hpT : p ≠ ⊤)
    (hsmall : ε ≤ c * p ^ α)
    (hsupp : ∀ x, ρs x ≠ 0 → rE ρrep R x ≠ 0)
    (hmin : ∀ x, p * rE ρrep R x ≤ rE ρt R x) :
    ε * PhiDres α ρs ρt R
      ≤ c * (1 + ENNReal.ofReal α * PhiDres α ρs ρrep R) := by
  calc
    ε * PhiDres α ρs ρt R
        ≤ ε * (p ^ (-α) *
          (1 + ENNReal.ofReal α * PhiDres α ρs ρrep R)) := by
      gcongr
      exact PhiDres_le_of_replacement_component hα ρs ρrep ρt R
        hp0 hsupp hmin
    _ = (ε * p ^ (-α)) *
          (1 + ENNReal.ofReal α * PhiDres α ρs ρrep R) := by ring
    _ ≤ c * (1 + ENNReal.ofReal α * PhiDres α ρs ρrep R) := by
      gcongr
      exact rare_rpow_price_le hp0 hpT hsmall

/-- Direct Hall estimate for a rare component that is minorized by a
replacement cylinder of mass `p`.  There is no Green denominator: the
replacement is visible in the same finite macro block. -/
lemma PhiDres_le_of_replacement_minorization {α : ℝ} (hα : 1 ≤ α)
    (ρs ρt : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hmin : ∀ x, p * rE ρs R x ≤ rE ρt R x) :
    PhiDres α ρs ρt R
      ≤ p ^ (-α) * (1 + ENNReal.ofReal α * PhiDres α ρs ρs R) := by
  calc
    PhiDres α ρs ρt R
        ≤ ∑' x, ρs x * WresD α ρt R x :=
      PhiDres_le_tsum_WresD (by linarith) ρs ρt R
    _ ≤ ∑' x, ρs x * (p ^ (-α) * WresD α ρs R x) := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : ρs x = 0
      · simp [hx]
      · have hrs : rE ρs R x ≠ 0 := by
          intro hrs0
          have hxx : ρs x ≤ rE ρs R x := le_rE_of_refl (hrefl x)
          rw [hrs0] at hxx
          exact hx (le_antisymm hxx zero_le)
        exact mul_le_mul_right
          (WresD_le_replacement_minorization (by linarith)
            ρs ρt R hp0 hmin hrs) _
    _ = ∑' x, p ^ (-α) * (ρs x * WresD α ρs R x) := by
      apply tsum_congr
      intro x
      ring
    _ = p ^ (-α) * ∑' x, ρs x * WresD α ρs R x := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ p ^ (-α) * (1 + ENNReal.ofReal α * PhiDres α ρs ρs R) := by
      gcongr
      exact tsum_WresD_le hα ρs ρs R

/-- The replacement cylinder estimate after restoring the exceptional
source mass. -/
lemma rare_mul_PhiDres_le_of_replacement {α : ℝ} (hα : 1 ≤ α)
    (ρs ρt : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    {ε p c : ℝ≥0∞} (hp0 : p ≠ 0) (hpT : p ≠ ⊤)
    (hsmall : ε ≤ c * p ^ α)
    (hmin : ∀ x, p * rE ρs R x ≤ rE ρt R x) :
    ε * PhiDres α ρs ρt R
      ≤ c * (1 + ENNReal.ofReal α * PhiDres α ρs ρs R) := by
  calc
    ε * PhiDres α ρs ρt R
        ≤ ε * (p ^ (-α) *
          (1 + ENNReal.ofReal α * PhiDres α ρs ρs R)) := by
      gcongr
      exact PhiDres_le_of_replacement_minorization hα ρs ρt R hrefl
        hp0 hmin
    _ = (ε * p ^ (-α)) *
          (1 + ENNReal.ofReal α * PhiDres α ρs ρs R) := by ring
    _ ≤ c * (1 + ENNReal.ofReal α * PhiDres α ρs ρs R) := by
      gcongr
      exact rare_rpow_price_le hp0 hpT hsmall

/-- A charged component is its own replacement cylinder inside a target
mixture.  This is the form used after identifying a grafted exceptional
template with the corresponding common two-stage cylinder. -/
lemma component_PhiDres_bind_le {A : Type} {α : ℝ} (hα : 1 ≤ α)
    (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (hrefl : ∀ x, R x x) (a : A) (ha : (w a : ℝ≥0∞) ≠ 0) :
    PhiDres α (f a) (w.bind f) R
      ≤ (w a : ℝ≥0∞) ^ (-α) *
        (1 + ENNReal.ofReal α * PhiDres α (f a) (f a) R) := by
  exact PhiDres_le_of_replacement_minorization hα (f a) (w.bind f) R
    hrefl ha
    (fun x => mul_rE_le_rE_bind w f R x a)

/-- Restoring a rare source coefficient costs only the ratio
`ε / p^α`; it creates neither a zero-interface debt nor an additional
Green factor. -/
lemma rare_component_PhiDres_bind_le {A : Type} {α : ℝ} (hα : 1 ≤ α)
    (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (hrefl : ∀ x, R x x) (a : A) {ε c : ℝ≥0∞}
    (ha : (w a : ℝ≥0∞) ≠ 0)
    (hsmall : ε ≤ c * (w a : ℝ≥0∞) ^ α) :
    ε * PhiDres α (f a) (w.bind f) R
      ≤ c * (1 + ENNReal.ofReal α * PhiDres α (f a) (f a) R) := by
  exact rare_mul_PhiDres_le_of_replacement hα (f a) (w.bind f) R
    hrefl ha (PMF.apply_ne_top w a) hsmall
    (fun x => mul_rE_le_rE_bind w f R x a)

end HallMinorization

end GraphMarkovMatching
