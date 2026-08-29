import GraphMarkovMatching.Archive.VaryingGraftedHeavyIntegrated

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {V : Type}

lemma graftCommonSucc_nonempty (t : GraftTgt) :
    (graftCommonSucc t).Nonempty := by
  cases t <;> simp [graftCommonSucc, graftCommonFreshSucc, graftForcedPair]

lemma graftZSuccCommon_nonempty {z : Finset GraftTgt} (hz : z.Nonempty) :
    (graftZSuccCommon z).Nonempty := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨u, hu⟩ := graftCommonSucc_nonempty t
  exact ⟨u, Finset.mem_biUnion.mpr ⟨t, ht, hu⟩⟩

theorem graftLiveSuccessor_le_common_mulVec
    (alpha : ℝ) (Rv : V → V → Prop) (mu : PMF V)
    (nuL nuR : PMF ℕ) (v0 : V) (CW : ℝ≥0∞)
    (i : GraftLedgerIndex) (h : ℕ) (sc' : GraftScreen)
    (hsucc : sc' ∈ graftScreenSuccCommon i.2.val)
    (hlive : sc' ∈ graftLiveScreens) :
    CW * graftBiScreen alpha Rv mu nuL nuR v0 i.1 h sc' ≤
      mulVecInf (graftCommonN CW)
        (graftE alpha Rv mu nuL nuR v0 h) i := by
  let j : GraftLedgerIndex := (i.1, ⟨sc', hlive⟩)
  calc
    CW * graftBiScreen alpha Rv mu nuL nuR v0 i.1 h sc' =
      graftCommonN CW i j * graftE alpha Rv mu nuL nuR v0 h j := by
        simp [graftCommonN, graftE, j, hsucc]
    _ ≤ mulVecInf (graftCommonN CW)
        (graftE alpha Rv mu nuL nuR v0 h) i := by
      rw [mulVecInf]
      exact ENNReal.le_tsum j

theorem graftSuccessorScreen_le_common_mulVec_add_ordinary
    (alpha : ℝ) (halpha : 1 ≤ alpha) (Rv : V → V → Prop)
    (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (CW : ℝ≥0∞) (i : GraftLedgerIndex) (h : ℕ) (sc' : GraftScreen)
    (hsucc : sc' ∈ graftScreenSuccCommon i.2.val) :
    CW * graftBiScreen alpha Rv mu nuL nuR v0 i.1 h sc' ≤
      mulVecInf (graftCommonN CW)
          (graftE alpha Rv mu nuL nuR v0 h) i +
        CW * (graftPsi alpha Rv mu nuL nuR v0 h +
          ENNReal.ofReal alpha * graftPsi alpha Rv mu nuL nuR v0 h) := by
  have hz : sc'.zlist.Nonempty := by
    rw [graftScreenSuccCommon_zlist hsucc]
    exact graftZSuccCommon_nonempty (graftLiveScreen_nonempty i.2)
  by_cases hlive : sc' ∈ graftLiveScreens
  · exact (graftLiveSuccessor_le_common_mulVec alpha Rv mu nuL nuR v0
      CW i h sc' hsucc hlive).trans le_self_add
  · have hordinary := graftNonliveScreen_le_graftPsi
      alpha Rv mu nuL nuR v0 halpha hrefl hLaw hp11 hp13
        i.1 h sc' hz hlive
    calc
      CW * graftBiScreen alpha Rv mu nuL nuR v0 i.1 h sc' ≤
          CW * (graftPsi alpha Rv mu nuL nuR v0 h +
            ENNReal.ofReal alpha * graftPsi alpha Rv mu nuL nuR v0 h) :=
        mul_le_mul_right hordinary CW
      _ ≤ mulVecInf (graftCommonN CW)
            (graftE alpha Rv mu nuL nuR v0 h) i +
          CW * (graftPsi alpha Rv mu nuL nuR v0 h +
            ENNReal.ofReal alpha * graftPsi alpha Rv mu nuL nuR v0 h) :=
        le_add_left le_rfl

theorem graftLiveScreen_le_rare_mulVec
    (alpha : ℝ) (Rv : V → V → Prop) (mu : PMF V)
    (nuL nuR : PMF ℕ) (v0 : V) (RW : ℝ≥0∞)
    (i : GraftLedgerIndex) (h : ℕ) (sc' : GraftScreen)
    (hlive : sc' ∈ graftLiveScreens) :
    RW * graftBiScreen alpha Rv mu nuL nuR v0 i.1 h sc' ≤
      mulVecInf (graftRareM RW)
        (graftE alpha Rv mu nuL nuR v0 h) i := by
  let j : GraftLedgerIndex := (i.1, ⟨sc', hlive⟩)
  calc
    RW * graftBiScreen alpha Rv mu nuL nuR v0 i.1 h sc' =
      graftRareM RW i j * graftE alpha Rv mu nuL nuR v0 h j := by
        simp [graftRareM, graftE, j]
    _ ≤ mulVecInf (graftRareM RW)
        (graftE alpha Rv mu nuL nuR v0 h) i := by
      rw [mulVecInf]
      exact ENNReal.le_tsum j

lemma graftSupportedPair_common (left : Bool) (i : Fin 4) :
    graftSupportedPair left (graftCommonArity i) = graftCommonPair i := by
  fin_cases i <;>
    simp [graftSupportedPair, graftCommonArity, graftCommonPair]

lemma graftCommonPair_fst_mem (i : Fin 4) :
    (graftCommonPair i).1 ∈ graftCommonFreshSucc := by
  fin_cases i <;> simp [graftCommonPair, graftCommonFreshSucc]

lemma graftCommonPair_snd_mem (i : Fin 4) :
    (graftCommonPair i).2 ∈ graftCommonFreshSucc := by
  fin_cases i <;> simp [graftCommonPair, graftCommonFreshSucc]

theorem graftFreshHall_fullScreen_mem_commonSucc
    (z : Finset GraftTgt) (is it : Fin 4)
    (a : GraftTgt) (ha : a = (graftCommonPair is).1 ∨
      a = (graftCommonPair is).2)
    (u : GraftTgt) (hu : u = (graftCommonPair it).1 ∨
      u = (graftCommonPair it).2) :
    (⟨a, graftZSuccCommon z, some u⟩ : GraftScreen) ∈
      graftScreenSuccCommon ⟨.F, z, some .F⟩ := by
  rw [graftScreenSuccCommon]
  apply Finset.mem_image.mpr
  refine ⟨(a, some u), ?_, rfl⟩
  rw [Finset.mem_product]
  constructor
  · rw [graftCommonSucc]
    rcases ha with rfl | rfl
    · exact graftCommonPair_fst_mem is
    · exact graftCommonPair_snd_mem is
  · rw [graftNormSuccCommon, Finset.mem_image]
    refine ⟨u, ?_, rfl⟩
    rw [graftCommonSucc]
    rcases hu with rfl | rfl
    · exact graftCommonPair_fst_mem it
    · exact graftCommonPair_snd_mem it

/-- Exact common-plus-exceptional decomposition of a weighted sum against
the left offspring law.  In particular, the exceptional Hall output keeps
its literal coefficient `zeta`. -/
theorem elevenThirteen_left_weighted_split
    {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta) (H : ℕ → ℝ≥0∞) :
    (∑' k, (nuL k : ℝ≥0∞) * H k) =
      (∑ i : Fin 4,
        (nuL (graftCommonArity i) : ℝ≥0∞) * H (graftCommonArity i)) +
        zeta * H 11 := by
  have hout : ∀ k ∉ insert 11 elevenThirteenCommonCore,
      (nuL k : ℝ≥0∞) * H k = 0 := by
    intro k hk
    have hz : (nuL k : ℝ≥0∞) = 0 := by
      by_contra hn
      exact hk (hLaw.2.2.2.1 k hn)
    simp [hz]
  rw [tsum_eq_sum hout]
  simp [elevenThirteenCommonCore, graftCommonArity, Fin.sum_univ_four,
    hLaw.1, add_assoc, add_comm]

/-- Exact common-plus-exceptional decomposition of a weighted sum against
the right offspring law. -/
theorem elevenThirteen_right_weighted_split
    {nuL nuR : PMF ℕ} {zeta : ℝ≥0∞}
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta) (H : ℕ → ℝ≥0∞) :
    (∑' k, (nuR k : ℝ≥0∞) * H k) =
      (∑ i : Fin 4,
        (nuR (graftCommonArity i) : ℝ≥0∞) * H (graftCommonArity i)) +
        zeta * H 13 := by
  have hout : ∀ k ∉ insert 13 elevenThirteenCommonCore,
      (nuR k : ℝ≥0∞) * H k = 0 := by
    intro k hk
    have hz : (nuR k : ℝ≥0∞) = 0 := by
      by_contra hn
      exact hk (hLaw.2.2.2.2 k hn)
    simp [hz]
  rw [tsum_eq_sum hout]
  simp [elevenThirteenCommonCore, graftCommonArity, Fin.sum_univ_four,
    hLaw.2.1, add_assoc, add_comm]

end GraphMarkovMatching
