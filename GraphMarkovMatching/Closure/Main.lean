/-
The general-ν uniform failure theorem and its infinite-tree form
(`arbitrary_offspring_matching.tex`, `thm:closure-form` in
`sec:recursion`, feeding `thm:main-matching`): for an arbitrary
finitely supported offspring law, the matching failure of the
varying-offspring process is at most `Kc·η` at every height, from the
ledger constants, the level hypotheses, and the two closure
inequalities alone; the nilpotence of the accessible screen block is
certified internally through the anchored acyclicity, with no
nilpotence hypothesis remaining.

* `varying_failure_uniform`: the assembled closure: the engine
  `screened_uniform_bound_mono` at the accessible coordinates, the
  block matrix `accN`, the certified steps `genPsi_step` and
  `genE_step`, the base bounds, and the failure bridge;
* `varying_matching_infinite_closed`: the König packaging of the
  bound on the infinite tree.
-/
import GraphMarkovMatching.Closure.EStep
import GraphMarkovMatching.Closure.Infinite

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (ν : PMF ℕ) (v0 : V) (N : ℕ) (S : Finset ℕ)

/-- **The general uniform failure bound** (`thm:closure-form`, feeding
`thm:main-matching`):
with the four-law constants, a reflexive symmetric label graph whose
base label carries at least half the mass, a bounded support captured
by the grammar parameters, finite tilt constants, and the level and
closure hypotheses at the bounds `Kc·η`, `u`, `Ξ`, the
expected bad degree of the varying-offspring process is at most
`Kc·η` at every height.  The nilpotence of the screen block carries
no hypothesis: it is certified by the anchored acyclicity of the
accessible index. -/
theorem varying_failure_uniform {δ L K : ℝ}
    (hα : 1 ≤ α) (hδ : 0 < δ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (Tν RT FM FT CW : ℝ≥0∞)
    (hTν : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (hFM : (∑' v, if Rv v v0 then 0 else μ v) ≤ FM)
    (hFT : (∑' v, if Rv v v0 then 0 else μ v * WresD α μ Rv v) ≤ FT)
    (hCW4 : 4 ≤ CW) (hCWRT : 4 * (RT * Tν) ≤ CW)
    (Kc u Ξ : ℝ≥0∞)
    (hb1 : etaG α Rv μ + phiE α (q μ Rv v0) ≤ Kc * etaG α Rv μ)
    (hb2 : baseScreenBound α Rv μ ≤ u)
    (hXi : (∑ j ∈ Finset.range
          (Fintype.card {sc // sc ∈ scrIndex N S} + 1),
          (CW * (scrIndex N S).card) ^ j) * u ≤ Ξ)
    (hu : genG α Tν RT FM FT (tgtUniv N).card
        (Kc * etaG α Rv μ) Ξ ≤ u)
    (hclose : genF α δ L K (etaG α Rv μ + phiE α (q μ Rv v0)) Tν S.card
        (Kc * etaG α Rv μ) Ξ ≤ Kc * etaG α Rv μ) :
    ∀ h, (∑' x, Tlaw μ ν v0 h x
        * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x)
      ≤ Kc * etaG α Rv μ := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hαpos : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα
  have hpos : (μ v0 : ℝ≥0∞) ≠ 0 := by
    intro h0
    rw [h0] at hhalf
    exact absurd (le_antisymm hhalf zero_le)
      (by norm_num : ((2 : ℝ≥0∞))⁻¹ ≠ 0)
  have hmain : ∀ h, genPsi α Rv μ ν v0 N S h ≤ Kc * etaG α Rv μ := by
    refine screened_uniform_bound_mono (Nat.succ_pos _)
      (genPsi α Rv μ ν v0 N S) (genE α Rv μ ν v0 N S)
      (genF α δ L K (etaG α Rv μ + phiE α (q μ Rv v0)) Tν S.card)
      (genG α Tν RT FM FT (tgtUniv N).card)
      (fun _ _ _ _ ha hb => genF_mono α δ L K _ Tν S.card ha hb)
      (fun _ _ _ _ ha hb => genG_mono α Tν RT FM FT _ ha hb)
      Kc (etaG α Rv μ) u Ξ
      (accN_nilpotent hN hS CW (fun _ => u))
      (fun i => le_trans
        (nilSum_le_geom (accN_row_sum_le N S CW) _ u i) hXi)
      (le_trans (genPsi_base α Rv μ ν v0 N S hα0 hrefl) hb1)
      (fun i => le_trans
        (genE_base α Rv μ ν v0 N S hαpos hrefl hsymm hhalf i) hb2)
      (fun h => genPsi_step α Rv μ ν v0 N S hα hδ hL0 hL hK0 hK hrefl
        hsymm hN hS hSsupp Tν hTν h)
      (fun h i => genE_step α Rv μ ν v0 N S hα hrefl hN hS hSne hSsupp
        hpos Tν RT FM FT CW hTν hRT hFM hFT hCW4 hCWRT h i)
      hu hclose
  intro h
  exact le_trans
    (failure_le_genPsi α Rv μ ν v0 N S hα0 hN hS hrefl h) (hmain h)

/-- **The general matching theorem on the infinite tree**
(`thm:closure-form` with the König packaging, feeding `thm:main-matching`): under the hypotheses of
the uniform failure bound, two independent infinite varying-offspring
labellings admit a single automorphism of the infinite binary tree
matching every vertex with probability at least `1 - Kc·η`. -/
theorem varying_matching_infinite_closed {δ L K : ℝ}
    {Ω : Type*} [MeasurableSpace Ω]
    (Pm : Measure Ω) [IsProbabilityMeasure Pm] [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (hα : 1 ≤ α) (hδ : 0 < δ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (Tν RT FM FT CW : ℝ≥0∞)
    (hTν : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (hFM : (∑' v, if Rv v v0 then 0 else μ v) ≤ FM)
    (hFT : (∑' v, if Rv v v0 then 0 else μ v * WresD α μ Rv v) ≤ FT)
    (hCW4 : 4 ≤ CW) (hCWRT : 4 * (RT * Tν) ≤ CW)
    (Kc u Ξ : ℝ≥0∞)
    (hb1 : etaG α Rv μ + phiE α (q μ Rv v0) ≤ Kc * etaG α Rv μ)
    (hb2 : baseScreenBound α Rv μ ≤ u)
    (hXi : (∑ j ∈ Finset.range
          (Fintype.card {sc // sc ∈ scrIndex N S} + 1),
          (CW * (scrIndex N S).card) ^ j) * u ≤ Ξ)
    (hu : genG α Tν RT FM FT (tgtUniv N).card
        (Kc * etaG α Rv μ) Ξ ≤ u)
    (hclose : genF α δ L K (etaG α Rv μ + phiE α (q μ Rv v0)) Tν S.card
        (Kc * etaG α Rv μ) Ξ ≤ Kc * etaG α Rv μ)
    (X Y : (n : ℕ) → Ω → FullLab (V × ℕ) n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Pm.map (fun ω => (X n ω, Y n ω))
        = (prodPMF (Tlaw μ ν v0 n) (Tlaw μ ν v0 n)).toMeasure) :
    1 - Kc * etaG α Rv μ
      ≤ Pm {ω | InfMatch (labRel Rv)
          (fun n => X n ω) (fun n => Y n ω)} :=
  varyingMatching_infinite Rv μ ν v0 Pm (Kc * etaG α Rv μ)
    (varying_failure_uniform α Rv μ ν v0 N S hα hδ hL0 hL hK0 hK hrefl
      hsymm hhalf hN hS hSne hSsupp Tν RT FM FT CW hTν hRT hFM hFT
      hCW4 hCWRT Kc u Ξ hb1 hb2 hXi hu hclose)
    X Y hX hY hpair hlaw

end GraphMarkovMatching
