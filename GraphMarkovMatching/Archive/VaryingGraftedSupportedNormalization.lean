/-
The literal fixed-law fresh/fresh normalization row.

The target law is a mixture.  We never condition the graph-label law on an
offspring event.  Instead, for every charged source arity we select one
compatible common target component.  Independence says that the mass of a
literal two-stage replacement component is the product of its offspring and
graph-label masses.  Since this component is already part of the target
mixture, it pointwise minorizes the matching degree of the whole mixture.
There is therefore no separate "rare target" or failed-zero remainder.
-/
import GraphMarkovMatching.Archive.VaryingGraftedFinal

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {V : Type}

/-- The common target component used for a source arity.  Common arities
select themselves, while the two exceptional arities select the literal
compatible common components `11 -> 7` and `13 -> 9`. -/
def graftCompatibleIndex (k : ℕ) : Fin 4 :=
  match k with
  | 3 => ⟨0, by omega⟩
  | 5 => ⟨1, by omega⟩
  | 7 => ⟨2, by omega⟩
  | 9 => ⟨3, by omega⟩
  | 11 => ⟨2, by omega⟩
  | 13 => ⟨3, by omega⟩
  | _ => ⟨0, by omega⟩

/-- On the actual five-point support of either side, the selected common
arity is exactly `graftCompatibleArity`. -/
lemma graftCommonArity_compatibleIndex
    (leftSource : Bool) (k : ℕ)
    (hk : k ∈ insert (graftRareArity leftSource)
      elevenThirteenCommonCore) :
    graftCommonArity (graftCompatibleIndex k) =
      graftCompatibleArity leftSource k := by
  cases leftSource with
  | false =>
      simp only [graftRareArity, elevenThirteenCommonCore,
        Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        rfl
  | true =>
      simp only [graftRareArity, elevenThirteenCommonCore,
        Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        rfl

/-- The fixed 11/13 fresh/fresh screen row with the target normalization
pruned to a source-dependent common component.  The displayed sum contains
only common target inverse weights.  In particular it has no
`zeta^(-alpha)` target coefficient and no zero-label defect term. -/
theorem graftFreshScreen_some_fresh_le_fixed_supported_far_add_hall
    (alpha : ℝ) (halpha : 1 ≤ alpha) (Rv : V → V → Prop)
    (mu : PMF V) (v0 : V) (nuL nuR : PMF ℕ) {zeta : ℝ≥0∞}
    (hrefl : ∀ v, Rv v v)
    (hLaw : IsFixedPositiveElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (leftSource : Bool) (h : ℕ) (z : Finset GraftTgt)
    (RT FT M : ℝ≥0∞)
    (hRT : (∑' v, (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) ≤ RT)
    (hFT : (∑' v, if Rv v v0 then 0 else
      (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) ≤ FT)
    (hMom : ∀ k, ((if leftSource then nuL else nuR) k : ℝ≥0∞) ≠ 0 →
      PhiDres alpha
        (graftXi leftSource mu (if leftSource then nuL else nuR) v0
          (.ordinary k) h)
        (graftXiBar (!leftSource) mu
          (if leftSource then nuR else nuL) v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) ≤ M) :
    screenE
        (graftInterp mu v0 leftSource
          (if leftSource then nuL else nuR) (h + 1) .F)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp mu v0 (!leftSource)
          (if leftSource then nuR else nuL) (h + 1)))
        (WresD alpha
          (graftInterp mu v0 (!leftSource)
            (if leftSource then nuR else nuL) (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      FT * (1 + ENNReal.ofReal alpha * M) +
        RT * ∑' k, ((if leftSource then nuL else nuR) k : ℝ≥0∞) *
          (((if leftSource then nuR else nuL)
              (graftCompatibleArity leftSource k) : ℝ≥0∞) ^ (-alpha) *
            graftFreshHallTerm Rv mu v0 alpha leftSource (!leftSource)
              (if leftSource then nuL else nuR)
              (if leftSource then nuR else nuL) h z
              (graftSupportedPair leftSource k).1
              (graftSupportedPair leftSource k).2
              (graftCompatibleArity leftSource k)) := by
  have hpair : IsElevenThirteenLawPair nuL nuR zeta := hLaw.1
  have hssupp : ∀ k,
      ((if leftSource then nuL else nuR) k : ℝ≥0∞) ≠ 0 →
        k ∈ insert (graftRareArity leftSource)
          elevenThirteenCommonCore := by
    intro k hk
    cases leftSource with
    | false => exact hpair.2.2.2.2 k hk
    | true => exact hpair.2.2.2.1 k hk
  have hcommon : ∀ i : Fin 4,
      ((if leftSource then nuR else nuL)
        (graftCommonArity i) : ℝ≥0∞) ≠ 0 := by
    intro i
    have hi : graftCommonArity i ∈ elevenThirteenCommonCore := by
      fin_cases i <;> simp [graftCommonArity, elevenThirteenCommonCore]
    cases leftSource with
    | false => exact hLaw.left_common_pos hi
    | true => exact hLaw.right_common_pos hi
  have hcompat : ∀ k,
      ((if leftSource then nuL else nuR) k : ℝ≥0∞) ≠ 0 →
      HasMatchingSupport
        (graftXi leftSource mu (if leftSource then nuL else nuR) v0
          (.ordinary k) h)
        (graftXi (!leftSource) mu
          (if leftSource then nuR else nuL) v0
          (.ordinary (graftCommonArity (graftCompatibleIndex k))) h)
        (SquareRel (fullSim (graftLabRel Rv) h)) := by
    intro k hk
    have hks := hssupp k hk
    rw [graftCommonArity_compatibleIndex leftSource k hks]
    exact graftXi_compatible_component_support Rv mu nuL nuR v0 hrefl
      hpair hp11 hp13 leftSource h k hks
  have hrow := graftFreshScreen_some_fresh_le_supported_far_add_hall
    alpha halpha Rv mu v0 leftSource (!leftSource)
    (if leftSource then nuL else nuR)
    (if leftSource then nuR else nuL)
    hssupp hcommon hrefl h z graftCompatibleIndex hcompat
    RT FT M hRT hFT hMom
  refine hrow.trans_eq ?_
  congr 2
  refine tsum_congr fun k => ?_
  by_cases hk : ((if leftSource then nuL else nuR) k : ℝ≥0∞) = 0
  · simp [hk]
  · rw [graftCommonArity_compatibleIndex leftSource k (hssupp k hk)]

/-- Graph-potential specialization of the exact fixed-law normalization
row.  The only graph-label error is the usual far-root potential; the
offspring and label laws remain independent throughout. -/
theorem graftFreshScreen_some_fresh_le_fixed_supported_eta_add_hall
    (alpha : ℝ) (halpha : 1 ≤ alpha) (Rv : V → V → Prop)
    (mu : PMF V) (v0 : V) (nuL nuR : PMF ℕ) {zeta : ℝ≥0∞}
    (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ v w, Rv v w → Rv w v)
    (hhalf : 2⁻¹ ≤ (mu v0 : ℝ≥0∞))
    (hLaw : IsFixedPositiveElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (leftSource : Bool) (h : ℕ) (z : Finset GraftTgt) (M : ℝ≥0∞)
    (hMom : ∀ k, ((if leftSource then nuL else nuR) k : ℝ≥0∞) ≠ 0 →
      PhiDres alpha
        (graftXi leftSource mu (if leftSource then nuL else nuR) v0
          (.ordinary k) h)
        (graftXiBar (!leftSource) mu
          (if leftSource then nuR else nuL) v0 h)
        (SquareRel (fullSim (graftLabRel Rv) h)) ≤ M) :
    screenE
        (graftInterp mu v0 leftSource
          (if leftSource then nuL else nuR) (h + 1) .F)
        (fullSim (graftLabRel Rv) (h + 1))
        (z.toList.map (graftInterp mu v0 (!leftSource)
          (if leftSource then nuR else nuL) (h + 1)))
        (WresD alpha
          (graftInterp mu v0 (!leftSource)
            (if leftSource then nuR else nuL) (h + 1) .F)
          (fullSim (graftLabRel Rv) (h + 1))) ≤
      (2 * etaG alpha Rv mu) * (1 + ENNReal.ofReal alpha * M) +
        ((2 : ℝ≥0∞) ^ alpha + 2 * etaG alpha Rv mu) *
          ∑' k, ((if leftSource then nuL else nuR) k : ℝ≥0∞) *
            (((if leftSource then nuR else nuL)
                (graftCompatibleArity leftSource k) : ℝ≥0∞) ^ (-alpha) *
              graftFreshHallTerm Rv mu v0 alpha leftSource (!leftSource)
                (if leftSource then nuL else nuR)
                (if leftSource then nuR else nuL) h z
                (graftSupportedPair leftSource k).1
                (graftSupportedPair leftSource k).2
                (graftCompatibleArity leftSource k)) := by
  apply graftFreshScreen_some_fresh_le_fixed_supported_far_add_hall
    alpha halpha Rv mu v0 nuL nuR hrefl hLaw hp11 hp13 leftSource h z
    ((2 : ℝ≥0∞) ^ alpha + 2 * etaG alpha Rv mu)
    (2 * etaG alpha Rv mu) M
  · exact tilt_le_pow_add alpha Rv mu v0 (by linarith) hsymm hhalf
  · calc
      (∑' v, if Rv v v0 then 0 else
          (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha)) =
        ∑' v, if Rv v0 v then 0 else
          (mu v : ℝ≥0∞) * (rE mu Rv v) ^ (-alpha) := by
            refine tsum_congr fun v => ?_
            have hviff : Rv v v0 ↔ Rv v0 v :=
              ⟨hsymm v v0, hsymm v0 v⟩
            by_cases hv : Rv v v0
            · rw [if_pos hv, if_pos (hviff.mp hv)]
            · rw [if_neg hv, if_neg (fun hc => hv (hviff.mpr hc))]
      _ ≤ 2 * etaG alpha Rv mu :=
        far_tilt_le alpha Rv mu v0 (by linarith) hsymm hhalf
  · exact hMom

end GraphMarkovMatching
