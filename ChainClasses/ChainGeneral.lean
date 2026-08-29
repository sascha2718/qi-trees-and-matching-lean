/-
`thm:chain-general` of `trichotomy.tex`, the assembly: two finitely supported supercritical
chain-regime laws with equal branching semigroups, sampled independently, are almost surely
quasi-isometric.

The engine of `ChainEngineBridge` aligns the encoded label fields of the two presented
samples with probability at least `1 - K θ₁^{D²/2}`.  The alignment lives on `𝔹`: a
presented vertex sits at the root of its cascade and its presented children at the slots,
so the slot geometry of `HairyGeneral` reads the presented skeleton as a cascade encoding,
over the presented arities truncated to zero off the skeleton, which the encoding never
reads.  The matching automorphism is a portrait of `𝔹`, and matched labels are equal or
adjacent level classes, which by `thm:level` and the cut-point clause of
`thm:chain-coupling` make the two presented necks comparable at scale `D²`; the flat
configurations being bare necks, the comparison is the floor map between two segments.
The glued transfer over `𝔹` then turns the alignment into a quasi-isometry of the
`𝔹`-assemblies, which the flattening of `BlobAssembly` carries back to the samples at a
constant polynomial in `D`.  The failure probabilities vanish as `D` grows, and the
coin fields and the uniform field are integrated out.

* `flatVert`, `eq_flatVert`, `dist_flatVert`, `floorMap`, `floorMap_bracket`,
  `flatG_markedQI`: **the comparison of two bare necks**, the floor map between segments
  whose vertex counts have ratio at most `c` being a `(2c + 1)`-marked quasi-isometry.
* `chainRatio`, `one_le_min_mul_chainRatio`, `neck_ratio_of_compat`: **equal or adjacent
  classes make the necks comparable**: a level class of the first law and a coupled class of
  the second that are equal or adjacent in the path graph force the neck lengths within the
  factor `chainRatio · D²` of one another, by `thm:level` and the sandwich and cut-point
  clauses of `thm:chain-coupling`.
* `truncAr`, `sample_truncAr`, `skelBounded_truncAr`, `arityBounded_truncAr`, `truncAr_le`:
  the presented arities truncated to zero off the presented skeleton, cutting out the same
  skeleton.
* `encSub_congr`, `encLab_congr`: **the encoding reads the arities on the skeleton only**.
* `mem_sample_bArityW_iff`, `toAddr_fromAddr_of_lt`, `presented_letters_lt`,
  `exists_word_of_presented`: the skeleton of the presented arity field over the letter
  range is the presented skeleton.
* `gCopyAddr_congr`, `flatShape`, `gCopyAddr_liftN_flatShape`, `skelToFlat`,
  `skelToFlat_injective`, `skelToFlat_surjective`, `dist_skelToFlat`,
  `IsQIMap.isometry_comp_left`: **the flat assembly is the skeleton assembly of the
  bare-neck shapes**, isometrically.
* `chainCascade`, `chainCascade_inClosure`, `bFamily_chainCascade_cases`,
  `exists_flat_to_bAssembly`: **the presented skeleton as a cascade encoding**: the shape
  over `𝔹` at a word is the bare neck of the presented vertex encoded there or the
  one-vertex shape, with the matching label, and the `𝔹`-assembly is reached from the flat
  assembly by a quasi-isometry at the letter range.
* `chainQIConst`, `sample_qi_of_chain_match`: **the deterministic core of
  `thm:chain-general`**: an alignment of the encoded label fields of two presented chain
  samples to within one class of the path graph gives a quasi-isometry of the samples at
  an explicit constant polynomial in `D`.
* `survives_of_one_le`, `law_Iic_one`, `survivalMeasure_neck_forever_null`,
  `ae_isChainField`, `ae_skelBounded_of_pattern`, `two_le_bArityAtC_of_presented`,
  `bArityLaw_matched_range`: **the almost sure events**: a conditioned chain sample is a
  chain field, and the presented arities on the presented skeleton lie in the letter range.
* `measurable_chainEnc`, `measurable_crossEnc`, `measurableSet_chain_match`: the matching
  event is measurable.
* `chain_general_rate`, `chain_general_ae_small`, `ae_prod_fst_of_triple`,
  `chain_general_ae`: **`thm:chain-general`**, the failure rate `K θ₁^{D²/2}` of the
  quasi-isometry at scale `D` and the almost sure statement on the two survival
  measures; the cofiniteness threshold in the gcd lattice enters the rate as a
  hypothesis and `semigroup_cofinite_gcd` supplies it in the almost sure statement.
-/
import ChainClasses.ChainEngineBridge
import ChainClasses.HairyGeneral
import ChainClasses.BlobAssembly

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure sample Survives)
open GraphMarkovMatching.Support (FullLab restrictLab InfMatchK)
open GraphMarkovMatching.Composite (CtrC CState cRel)

/-! ### The comparison of two bare necks -/

/-- The neck vertex `i` steps below the root of the bare neck of `n` edges. -/
def flatVert (n : ℕ) (i : ℕ) (hi : i ≤ n) : (gShapeSpace (flatG n)).carrier :=
  ⟨pRep i, (mem_addrList_flatG n _).mpr (pRep_prefix_pRep hi)⟩

lemma flatVert_val (n i : ℕ) (hi : i ≤ n) : (flatVert n i hi).1 = pRep i := rfl

/-- Every vertex of a bare neck is a neck vertex. -/
lemma eq_flatVert (n : ℕ) (x : (gShapeSpace (flatG n)).carrier) :
    ∃ (i : ℕ) (hi : i ≤ n), x = flatVert n i hi := by
  have hx : x.1 <+: pRep n := (mem_addrList_flatG n _).mp x.2
  have hlen : x.1.length ≤ n := by simpa using hx.length_le
  refine ⟨x.1.length, hlen, Subtype.ext ?_⟩
  rw [flatVert_val]
  exact eq_pRep_of_prefix hx

/-- The distance along a bare neck is the difference of the depths. -/
lemma dist_flatVert (n i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    dist (flatVert n i hi) (flatVert n j hj) = |(i : ℝ) - j| := by
  rw [GAssembly.dist_gShapeSpace, flatVert_val, flatVert_val]
  rcases le_total i j with h | h
  · rw [addrDist_of_prefix (pRep_prefix_pRep h), pRep_length, pRep_length,
      abs_sub_comm, abs_of_nonneg (by simpa using h)]
    push_cast [h]
    ring
  · rw [addrDist_comm, addrDist_of_prefix (pRep_prefix_pRep h), pRep_length, pRep_length,
      abs_of_nonneg (by simpa using h)]
    push_cast [h]
    ring

lemma entry_flatG (n : ℕ) : (gShapeSpace (flatG n)).entry = flatVert n 0 (Nat.zero_le n) := rfl

lemma exit_flatG (n : ℕ) : (gShapeSpace (flatG n)).exit = flatVert n n le_rfl := by
  rw [exit_gShapeSpace]
  exact Subtype.ext (flatG_exitAddr n)

/-- The floor map `i ↦ ⌊i n' / n⌋` between two segments. -/
def floorMap (n n' i : ℕ) : ℕ := i * n' / n

lemma floorMap_le (n n' : ℕ) {i : ℕ} (hi : i ≤ n) : floorMap n n' i ≤ n' := by
  rw [floorMap]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right n' hi)

lemma floorMap_mono (n n' : ℕ) {i j : ℕ} (h : i ≤ j) : floorMap n n' i ≤ floorMap n n' j :=
  Nat.div_le_div_right (Nat.mul_le_mul_right n' h)

/-- The two bracketing facts of the floor: `⌊i n'/n⌋ n ≤ i n' < (⌊i n'/n⌋ + 1) n`. -/
lemma floorMap_bracket (n n' i : ℕ) (hn : 0 < n) :
    ((floorMap n n' i : ℝ) * n ≤ i * n') ∧ ((i : ℝ) * n' < (floorMap n n' i + 1) * n) := by
  constructor
  · have := Nat.div_mul_le_self (i * n') n
    rw [floorMap]
    exact_mod_cast this
  · have := Nat.lt_mul_div_succ (i * n') hn
    rw [floorMap]
    have h' : i * n' < (i * n' / n + 1) * n := by rw [mul_comm (i * n' / n + 1) n]; exact this
    exact_mod_cast h'

/-- **The comparison of two bare necks**: segments whose lengths (counted in vertices) have
ratio at most `c` are `(2c + 1)`-comparable through the floor map. -/
theorem flatG_markedQI {c : ℝ} (hc : 1 ≤ c) {n n' : ℕ}
    (h1 : ((n' : ℝ) + 1) ≤ c * ((n : ℝ) + 1)) (h2 : ((n : ℝ) + 1) ≤ c * ((n' : ℝ) + 1)) :
    MarkedQI (2 * c + 1) (gShapeSpace (flatG n)) (gShapeSpace (flatG n')) := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  set K : ℝ := 2 * c + 1 with hK
  have hK1 : (1 : ℝ) ≤ K := by linarith
  -- the map
  let f : (gShapeSpace (flatG n)).carrier → (gShapeSpace (flatG n')).carrier := fun x =>
    flatVert n' (floorMap n n' x.1.length)
      (floorMap_le n n' (by simpa using ((mem_addrList_flatG n _).mp x.2).length_le))
  have hf : ∀ (i : ℕ) (hi : i ≤ n), f (flatVert n i hi)
      = flatVert n' (floorMap n n' i) (floorMap_le n n' hi) := by
    intro i hi
    simp only [f, flatVert_val, pRep_length]
  -- the one-sided estimates for `i ≤ j`
  have hup : ∀ i j : ℕ, i ≤ j → j ≤ n →
      (floorMap n n' j : ℝ) - floorMap n n' i ≤ 2 * c * ((j : ℝ) - i) + 1 := by
    intro i j hij hjn
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0; subst hj0
      simp
    · obtain ⟨hj1, -⟩ := floorMap_bracket n n' j hn
      obtain ⟨-, hi2⟩ := floorMap_bracket n n' i hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn' : (n' : ℝ) ≤ 2 * c * n := by nlinarith
      have hji : (0 : ℝ) ≤ (j : ℝ) - i := by
        have : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
      have key : ((floorMap n n' j : ℝ) - floorMap n n' i) * n ≤ (2 * c * ((j : ℝ) - i) + 1) * n := by
        have h3 : ((j : ℝ) - i) * n' ≤ ((j : ℝ) - i) * (2 * c * n) :=
          mul_le_mul_of_nonneg_left hn' hji
        nlinarith
      exact le_of_mul_le_mul_right key hnR
  have hlow : ∀ i j : ℕ, i ≤ j → j ≤ n →
      (j : ℝ) - i ≤ 2 * c * ((floorMap n n' j : ℝ) - floorMap n n' i) + 2 * c := by
    intro i j hij hjn
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0; subst hj0
      simp
      linarith
    · rcases Nat.eq_zero_or_pos n' with rfl | hn'
      · have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn
        have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        simp only [floorMap, mul_zero, Nat.zero_div, Nat.cast_zero, sub_zero, mul_zero, zero_add]
        push_cast at h2
        linarith
      · obtain ⟨-, hj2⟩ := floorMap_bracket n n' j hn
        obtain ⟨hi1, -⟩ := floorMap_bracket n n' i hn
        have hn'R : (0 : ℝ) < n' := by exact_mod_cast hn'
        have hn'1 : (1 : ℝ) ≤ n' := by exact_mod_cast hn'
        have hnn' : (n : ℝ) ≤ 2 * c * n' := by nlinarith
        have hq : (0 : ℝ) ≤ (floorMap n n' j : ℝ) - floorMap n n' i + 1 := by
          have : (floorMap n n' i : ℝ) ≤ floorMap n n' j := by
            exact_mod_cast floorMap_mono n n' hij
          linarith
        have key : ((j : ℝ) - i) * n' ≤ (2 * c * ((floorMap n n' j : ℝ) - floorMap n n' i) + 2 * c) * n' := by
          have h3 : ((floorMap n n' j : ℝ) - floorMap n n' i + 1) * n
              ≤ ((floorMap n n' j : ℝ) - floorMap n n' i + 1) * (2 * c * n') :=
            mul_le_mul_of_nonneg_left hnn' hq
          nlinarith
        exact le_of_mul_le_mul_right key hn'R
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · -- upper
    intro a b
    obtain ⟨i, hi, rfl⟩ := eq_flatVert n a
    obtain ⟨j, hj, rfl⟩ := eq_flatVert n b
    rw [hf, hf, dist_flatVert, dist_flatVert]
    rcases le_total i j with hij | hij
    · have h := hup i j hij hj
      have hm : (floorMap n n' i : ℝ) ≤ floorMap n n' j := by
        exact_mod_cast floorMap_mono n n' hij
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [hK]
      nlinarith
    · have h := hup j i hij hi
      have hm : (floorMap n n' j : ℝ) ≤ floorMap n n' i := by
        exact_mod_cast floorMap_mono n n' hij
      have hij' : (j : ℝ) ≤ i := by exact_mod_cast hij
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      rw [hK]
      nlinarith
  · -- lower
    intro a b
    obtain ⟨i, hi, rfl⟩ := eq_flatVert n a
    obtain ⟨j, hj, rfl⟩ := eq_flatVert n b
    rw [hf, hf, dist_flatVert, dist_flatVert]
    rcases le_total i j with hij | hij
    · have h := hlow i j hij hj
      have hm : (floorMap n n' i : ℝ) ≤ floorMap n n' j := by
        exact_mod_cast floorMap_mono n n' hij
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [hK]
      have hd : (0 : ℝ) ≤ (floorMap n n' j : ℝ) - floorMap n n' i := by linarith
      nlinarith
    · have h := hlow j i hij hi
      have hm : (floorMap n n' j : ℝ) ≤ floorMap n n' i := by
        exact_mod_cast floorMap_mono n n' hij
      have hij' : (j : ℝ) ≤ i := by exact_mod_cast hij
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      rw [hK]
      have hd : (0 : ℝ) ≤ (floorMap n n' i : ℝ) - floorMap n n' j := by linarith
      nlinarith
  · -- dense
    intro y
    obtain ⟨m, hm, rfl⟩ := eq_flatVert n' y
    rcases Nat.eq_zero_or_pos n' with rfl | hn'
    · have hm0 : m = 0 := by omega
      subst hm0
      refine ⟨flatVert n 0 (Nat.zero_le n), ?_⟩
      rw [hf, dist_flatVert]
      simp [floorMap]
      linarith
    · -- the preimage `⌊m n / n'⌋`
      set i : ℕ := m * n / n' with hi
      have hin : i ≤ n := by
        rw [hi]
        exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right n hm)
      refine ⟨flatVert n i hin, ?_⟩
      rw [hf, dist_flatVert]
      have hn'R : (0 : ℝ) < n' := by exact_mod_cast hn'
      -- `⌊i n'/n⌋ ≤ m` and `m < ⌊i n'/n⌋ + 1 + n'/n`
      have hq_le : floorMap n n' i ≤ m := by
        rw [floorMap]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · refine Nat.div_le_of_le_mul ?_
          have : i * n' ≤ m * n := by
            rw [hi]
            exact Nat.div_mul_le_self _ _
          rw [mul_comm n m]
          exact this
      have hq_ge : (m : ℝ) ≤ floorMap n n' i + 2 * c + 1 := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have hm' : (m : ℝ) ≤ n' := by exact_mod_cast hm
          have : (n' : ℝ) + 1 ≤ c := by simpa using h1
          have : (0 : ℝ) ≤ floorMap 0 n' i := Nat.cast_nonneg _
          linarith
        · obtain ⟨-, hi2⟩ := floorMap_bracket n n' i hn
          have hmn : (m : ℝ) * n < (i + 1) * n' := by
            have := Nat.lt_mul_div_succ (m * n) hn'
            rw [← hi] at this
            have h' : m * n < (i + 1) * n' := by rw [mul_comm (i + 1) n']; exact this
            exact_mod_cast h'
          have hnR : (0 : ℝ) < n := by exact_mod_cast hn
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have hn' : (n' : ℝ) ≤ 2 * c * n := by nlinarith
          have key : (m : ℝ) * n ≤ ((floorMap n n' i : ℝ) + 2 * c + 1) * n := by nlinarith
          exact le_of_mul_le_mul_right key hnR
      have hq_le' : (floorMap n n' i : ℝ) ≤ m := by exact_mod_cast hq_le
      rw [abs_sub_comm, abs_of_nonneg (by linarith), hK]
      linarith
  · -- entry
    rw [entry_flatG, entry_flatG, hf, dist_flatVert]
    simp [floorMap]
    linarith
  · -- exit
    rw [exit_flatG, exit_flatG, hf, dist_flatVert]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : (n' : ℝ) + 1 ≤ c := by simpa using h1
      simp [floorMap]
      linarith
    · have : floorMap n n' n = n' := by
        rw [floorMap, mul_comm, Nat.mul_div_cancel _ hn]
      rw [this]
      simp
      linarith

/-! ### Equal or adjacent classes make the necks comparable -/

/-- The ratio constant `max(1, γ, 2/γ)` of the two neck laws: the cut points of
`thm:chain-coupling` track the powers of `D` within the factors `min(1, γ/2)` and
`max(1, γ)`. -/
noncomputable def chainRatio (a b : ℝ) : ℝ := max (max 1 (cgamma a b)) (2 / cgamma a b)

lemma one_le_chainRatio (a b : ℝ) : 1 ≤ chainRatio a b :=
  le_trans (le_max_left _ _) (le_max_left _ _)

lemma max_one_le_chainRatio (a b : ℝ) : max 1 (cgamma a b) ≤ chainRatio a b := le_max_left _ _

/-- The lower cut-point factor against the ratio constant is at least one. -/
lemma one_le_min_mul_chainRatio {a b : ℝ} (hγ : 0 < cgamma a b) :
    1 ≤ min 1 (cgamma a b / 2) * chainRatio a b := by
  rcases le_total 1 (cgamma a b / 2) with h | h
  · rw [min_eq_left h, one_mul]
    exact one_le_chainRatio a b
  · rw [min_eq_right h]
    have h2 : 2 / cgamma a b ≤ chainRatio a b := le_max_right _ _
    calc (1 : ℝ) = cgamma a b / 2 * (2 / cgamma a b) := by field_simp
      _ ≤ cgamma a b / 2 * chainRatio a b :=
          mul_le_mul_of_nonneg_left h2 (by linarith)

/-- **Equal or adjacent classes make the necks comparable.**  A presented neck `n` of the
first law in the level class `ℓ_D(n + 1)` and a presented neck `n'` of the second law in the
coupled class `ℓ'(n' + 1, u)`, the two classes equal or adjacent in the path graph, have
lengths within the factor `chainRatio · D²` of one another: `thm:level` on the first side
and the sandwich and cut-point clauses of `thm:chain-coupling` on the second. -/
theorem neck_ratio_of_compat {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) {n n' : ℕ} {u : ℝ}
    (h : GraphMatching.compat GraphMatching.pathGraph (levelMap D (n + 1))
      (ellQ a b D (n' + 1) u)) :
    ((n' : ℝ) + 1) ≤ chainRatio a b * (D : ℝ) ^ 2 * ((n : ℝ) + 1) ∧
      ((n : ℝ) + 1) ≤ chainRatio a b * (D : ℝ) ^ 2 * ((n' : ℝ) + 1) := by
  have hγ := cgamma_pos ha ha1 hb hb1
  set k := levelMap D (n + 1) with hk
  set k' := ellQ a b D (n' + 1) u with hk'
  obtain ⟨hk1, hk2⟩ := (level_eq_iff hD (by omega)).mp hk.symm
  obtain ⟨hk1', hk2'⟩ := ellQ_sandwich_upper ha ha1 hb hb1 hD hgD (by omega) hk'.symm
  have hr1 := (DQ_ratio ha ha1 hb hb1 hD k').1
  have hr2 := (DQ_ratio ha ha1 hb hb1 hD (k' + 1)).2
  have hkk' : k' ≤ k + 1 ∧ k ≤ k' + 1 := by
    rcases h with h | h
    · omega
    · rw [GraphMatching.pathGraph_adj] at h
      omega
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := by linarith
  have hcr := one_le_chainRatio a b
  have hmax := max_one_le_chainRatio a b
  have hDk : ((D : ℝ) ^ k) ≤ (n : ℝ) + 1 := by exact_mod_cast hk1
  have hnD : (n : ℝ) + 1 < (D : ℝ) ^ (k + 1) := by exact_mod_cast hk2
  have hDk'1 : ((DQ a b D k' : ℕ) : ℝ) ≤ (n' : ℝ) + 1 := by exact_mod_cast hk1'
  have hn'D : (n' : ℝ) + 1 ≤ ((DQ a b D (k' + 1) : ℕ) : ℝ) := by exact_mod_cast hk2'
  constructor
  · calc (n' : ℝ) + 1 ≤ (DQ a b D (k' + 1) : ℝ) := hn'D
      _ ≤ max 1 (cgamma a b) * (D : ℝ) ^ (k' + 1) := hr2
      _ ≤ max 1 (cgamma a b) * (D : ℝ) ^ (k + 2) := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD1 (by omega)) ?_
          exact le_trans zero_le_one (le_max_left _ _)
      _ = max 1 (cgamma a b) * (D : ℝ) ^ 2 * (D : ℝ) ^ k := by ring
      _ ≤ chainRatio a b * (D : ℝ) ^ 2 * ((n : ℝ) + 1) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hmax (by positivity)) hDk
            (by positivity) (by positivity)
  · have hmin := one_le_min_mul_chainRatio hγ
    have hDk' : (D : ℝ) ^ k' ≤ ((n' : ℝ) + 1) * chainRatio a b := by
      calc (D : ℝ) ^ k' = (D : ℝ) ^ k' * 1 := (mul_one _).symm
        _ ≤ (D : ℝ) ^ k' * (min 1 (cgamma a b / 2) * chainRatio a b) :=
            mul_le_mul_of_nonneg_left hmin (by positivity)
        _ = (min 1 (cgamma a b / 2) * (D : ℝ) ^ k') * chainRatio a b := by ring
        _ ≤ (DQ a b D k' : ℝ) * chainRatio a b :=
            mul_le_mul_of_nonneg_right hr1 (by linarith)
        _ ≤ ((n' : ℝ) + 1) * chainRatio a b :=
            mul_le_mul_of_nonneg_right hDk'1 (by linarith)
    calc (n : ℝ) + 1 ≤ (D : ℝ) ^ (k + 1) := hnD.le
      _ ≤ (D : ℝ) ^ (k' + 2) := pow_le_pow_right₀ hD1 (by omega)
      _ = (D : ℝ) ^ 2 * (D : ℝ) ^ k' := by ring
      _ ≤ (D : ℝ) ^ 2 * (((n' : ℝ) + 1) * chainRatio a b) :=
          mul_le_mul_of_nonneg_left hDk' (by positivity)
      _ = chainRatio a b * (D : ℝ) ^ 2 * ((n' : ℝ) + 1) := by ring

/-! ### The presented arities truncated off the presented skeleton -/

section Trunc

variable {N' : ℕ}

/-- The arity field truncated to zero off its own skeleton. -/
noncomputable def truncAr (ar : GWord N' → ℕ) (u : GWord N') : ℕ :=
  if u ∈ sample ar then ar u else 0

lemma truncAr_of_mem {ar : GWord N' → ℕ} {u : GWord N'} (hu : u ∈ sample ar) :
    truncAr ar u = ar u := by
  rw [truncAr, if_pos hu]

lemma truncAr_of_not_mem {ar : GWord N' → ℕ} {u : GWord N'} (hu : u ∉ sample ar) :
    truncAr ar u = 0 := by
  rw [truncAr, if_neg hu]

/-- The truncated field cuts out the same skeleton. -/
lemma sample_truncAr (ar : GWord N' → ℕ) : sample (truncAr ar) = sample ar := by
  ext u
  rw [mem_sample_iff_prefix, mem_sample_iff_prefix]
  constructor
  · intro h p i hpi
    have hi := h p i hpi
    have hp : p ∈ sample ar := by
      by_contra hc
      rw [truncAr_of_not_mem hc] at hi
      omega
    rwa [truncAr_of_mem hp] at hi
  · intro h p i hpi
    have hp : p ∈ sample ar := by
      have hu : u ∈ sample ar := (mem_sample_iff_prefix u).mpr h
      exact BranchingProcess.Subtree.mem_of_prefix ((List.prefix_append p [i]).trans hpi) hu
    rw [truncAr_of_mem hp]
    exact h p i hpi

lemma skelBounded_truncAr {L : ℕ} {ar : GWord N' → ℕ} (hs : SkelBounded L ar) :
    SkelBounded L (truncAr ar) := by
  intro u hu
  rw [sample_truncAr] at hu
  rw [truncAr_of_mem hu]
  exact hs u hu

lemma arityBounded_truncAr {L : ℕ} {ar : GWord N' → ℕ} (hs : SkelBounded L ar) :
    ArityBounded L (truncAr ar) :=
  arityBounded_of_skelBounded (skelBounded_truncAr hs) fun u hu => by
    rw [sample_truncAr] at hu
    exact truncAr_of_not_mem hu

lemma truncAr_le {L : ℕ} {ar : GWord N' → ℕ} (hs : SkelBounded L ar) (u : GWord N') :
    truncAr ar u ≤ L := by
  by_cases hu : u ∈ sample ar
  · rw [truncAr_of_mem hu]; exact (hs u hu).2
  · rw [truncAr_of_not_mem hu]; exact Nat.zero_le _

/-! ### The encoding reads the arities on the skeleton only -/

/-- **The encoding below a cascade vertex reads the arities on the skeleton only**: two
arity fields agreeing on the skeleton of the first, bounded there by the letter range,
encode a label field identically below any valid vertex serving slots within the arity. -/
lemma encSub_congr {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (lab : GWord N' → ℕ)
    {ar ar' : GWord N' → ℕ} (hs : SkelBounded N' ar)
    (hagree : ∀ u, u ∈ sample ar → ar' u = ar u) (v0 : ℕ) :
    ∀ (n : ℕ) (u : GWord N') (off : ℕ) (s : CState ℕ), u ∈ sample ar → validS (0, s.2) →
      off + servedC s.2 ≤ ar u →
      encSub exc lab ar v0 n u off s = encSub exc lab ar' v0 n u off s
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, u, off, s, hu, hv, hoff => by
      rw [encSub_succ, encSub_succ, stepKind_eq_zero exc off s]
      obtain ⟨h1, h2, h3, h4, h5⟩ := stepKind_spec hexc 0 off hv
      -- one child at a time
      have key : ∀ c : ChildK, validK 0 c → startK c + servedK c ≤ ar u →
          encSub exc lab ar v0 n (childAddr u c).1 (childAddr u c).2 (childState lab ar v0 u c)
            = encSub exc lab ar' v0 n (childAddr u c).1 (childAddr u c).2
                (childState lab ar' v0 u c) := by
        intro c hc hrange
        cases c with
        | internal o t =>
            simp only [childAddr, childState]
            simp only [startK, servedK] at hrange
            exact encSub_congr hexc lab hs hagree v0 n u o (v0, t) hu hc hrange
        | slot j =>
            simp only [childAddr, childState]
            simp only [startK, servedK] at hrange
            have hju : j < ar u := by omega
            have hjN : j < N' := lt_of_lt_of_le hju (hs u hu).2
            have hmem : gChild u j ∈ sample ar := by
              rw [gChild_of_lt u hjN]
              exact BranchingProcess.mem_sample_append_singleton.mpr ⟨hu, hju⟩
            rw [hagree _ hmem]
            exact encSub_congr hexc lab hs hagree v0 n (gChild u j) 0 _ hmem (hs _ hmem).1
              (by simp only [servedC]; omega)
      have h3' : servedK (stepKind exc off (0, s.2)).1 + servedK (stepKind exc off (0, s.2)).2
          = servedC s.2 := h3
      rw [key _ h4 (by omega), key _ h5 (by omega)]

/-- **The encoded label field reads the arities on the skeleton only.** -/
lemma encLab_congr {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc) (lab : GWord N' → ℕ)
    {ar ar' : GWord N' → ℕ} (hs : SkelBounded N' ar)
    (hagree : ∀ u, u ∈ sample ar → ar' u = ar u) (v0 n : ℕ) :
    encLab exc lab ar v0 n = encLab exc lab ar' v0 n := by
  have hnil : ([] : GWord N') ∈ sample ar := BranchingProcess.nil_mem_sample _
  rw [encLab, encLab, hagree _ hnil]
  exact encSub_congr hexc lab hs hagree v0 n [] 0 _ hnil (hs _ hnil).1
    (by simp only [servedC]; omega)

end Trunc

/-! ### The presented skeleton over the letter range -/

section Presented

variable {N Nenc : ℕ} [NeZero N] {σ : Type*} (R : ℕ) (ρr : BRule σ)
  (ω : (GWord N → ℕ) × (List ℕ → σ))

omit [NeZero N] in
/-- **The presented arity field over the letter range cuts out the presented skeleton.** -/
lemma mem_sample_bArityW_iff :
    ∀ u : GWord Nenc, u ∈ sample (bArityW Nenc R ρr ω) ↔ Presented R ρr ω (toAddr u) := by
  intro u
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u i ih =>
      rw [BranchingProcess.mem_sample_append_singleton, ih, toAddr_append, toAddr_singleton,
        presented_concat]
      rfl

omit [NeZero N] in
/-- A word whose letters lie in the range is the address of its reading. -/
lemma toAddr_fromAddr_of_lt : ∀ {w : List ℕ}, (∀ i ∈ w, i < Nenc) → toAddr (fromAddr Nenc w) = w
  | [], _ => rfl
  | i :: w, h => by
      have hi : i < Nenc := h i (List.mem_cons_self ..)
      have hw : ∀ j ∈ w, j < Nenc := fun j hj => h j (List.mem_cons_of_mem i hj)
      simp only [fromAddr, List.filterMap_cons, dif_pos hi, toAddr, List.map_cons]
      have := toAddr_fromAddr_of_lt hw
      simp only [fromAddr, toAddr] at this
      rw [this]

omit [NeZero N] in
/-- The letters of a presented address lie below the presented arities along it. -/
lemma presented_letters_lt (hs : ∀ w, Presented R ρr ω w → bArityAtC R ρr ω w ≤ Nenc)
    {w : List ℕ} (hw : Presented R ρr ω w) : ∀ i ∈ w, i < Nenc := by
  intro i hi
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hi
  have hlt := PIdx.letter_lt (flat_pIdx R ρr ω) hw
  rw [flatAt, flatPiece_nports] at hlt
  have hs' : Presented R ρr ω s :=
    PIdx.of_prefix (flat_pIdx R ρr ω) ⟨i :: t, rfl⟩ hw
  exact lt_of_lt_of_le hlt (hs s hs')

omit [NeZero N] in
/-- A presented address is the address of a word of the skeleton over the letter range,
once the presented arities along the skeleton lie in the range. -/
lemma exists_word_of_presented (hs : SkelBounded Nenc (bArityW Nenc R ρr ω)) :
    ∀ {w : List ℕ}, Presented R ρr ω w →
      ∃ u : GWord Nenc, u ∈ sample (bArityW Nenc R ρr ω) ∧ toAddr u = w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _; exact ⟨[], BranchingProcess.nil_mem_sample _, rfl⟩
  | append_singleton w j ih =>
      intro hw
      rw [presented_concat] at hw
      obtain ⟨u, hu, rfl⟩ := ih hw.1
      have hj : j < Nenc := lt_of_lt_of_le hw.2 (hs u hu).2
      refine ⟨u ++ [⟨j, hj⟩], BranchingProcess.mem_sample_append_singleton.mpr ⟨hu, hw.2⟩, ?_⟩
      rw [toAddr_append, toAddr_singleton]

end Presented

/-! ### The flat assembly as a skeleton assembly -/

/-- The planting of the copies reads the shapes at the strict prefixes only. -/
lemma gCopyAddr_congr {τ τ' : List ℕ → GShape} :
    ∀ w : List ℕ, (∀ p, p <+: w → p ≠ w → τ p = τ' p) → gCopyAddr τ w = gCopyAddr τ' w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton w j ih =>
      intro h
      rw [gCopyAddr_concat, gCopyAddr_concat, ih, h w (List.prefix_append _ _) (by simp)]
      intro p hp hne
      refine h p (hp.trans (List.prefix_append _ _)) ?_
      rintro rfl
      have := hp.length_le
      simp at this

section SkelFlat

variable {N Nenc : ℕ} [NeZero N] {σ : Type*} (R : ℕ) (ρr : BRule σ)
  (ω : (GWord N → ℕ) × (List ℕ → σ))

/-- **The flat blob shapes over the letter range**: the bare neck of the presented neck
length at every word. -/
noncomputable def flatShape (u : GWord Nenc) : GShape := flatG (bNeckAtC R ρr ω (toAddr u))

omit [NeZero N] in
/-- The shapes read over `ℕ` agree with the bare necks of the presented necks along the
skeleton. -/
lemma gCopyAddr_liftN_flatShape (u : GWord Nenc) :
    gCopyAddr (liftN Nenc (flatShape R ρr ω)) (vals u)
      = gCopyAddr (fun w => flatG (bNeckAtC R ρr ω w)) (toAddr u) := by
  refine gCopyAddr_congr (vals u) fun p hp _ => ?_
  obtain ⟨u', -, rfl⟩ := exists_toAddr_of_prefix (N' := Nenc) hp
  show liftN Nenc (flatShape R ρr ω) (vals u') = flatG (bNeckAtC R ρr ω (toAddr u'))
  rw [liftN_vals]
  rfl

variable {k : GWord Nenc → ℕ}
  (hIdx : ∀ u : GWord Nenc, u ∈ sample k ↔ Presented R ρr ω (toAddr u))

/-- **The skeleton assembly of the bare-neck shapes inside the assembly of the bare necks
over the presented skeleton.** -/
noncomputable def skelToFlat (x : SkelAssembly k (flatShape R ρr ω)) :
    {y : GAssembly (fun w => flatG (bNeckAtC R ρr ω w)) // Presented R ρr ω y.copy} :=
  ⟨⟨toAddr x.copy, x.vert⟩, (hIdx x.copy).mp x.skel⟩

omit [NeZero N] in
lemma skelToFlat_injective : Function.Injective (skelToFlat R ρr ω hIdx) := by
  intro x y h
  have h1 : toAddr x.copy = toAddr y.copy := congrArg (fun z => z.1.copy) h
  have h2 : x.vert.1 = y.vert.1 := congrArg (fun z => z.1.vert.1) h
  exact SkelAssembly.ext (toAddr_injective h1) h2

omit [NeZero N] in
lemma skelToFlat_surjective (hs : ∀ w, Presented R ρr ω w → bArityAtC R ρr ω w ≤ Nenc) :
    Function.Surjective (skelToFlat R ρr ω hIdx) := by
  rintro ⟨⟨w, p⟩, hw⟩
  have hwu : toAddr (fromAddr Nenc w) = w :=
    toAddr_fromAddr_of_lt (presented_letters_lt R ρr ω hs hw)
  have hshape : flatG (bNeckAtC R ρr ω w) = flatShape R ρr ω (fromAddr Nenc w) := by
    rw [flatShape, hwu]
  refine ⟨⟨fromAddr Nenc w, (hIdx _).mpr (by rw [hwu]; exact hw), castVert hshape p⟩, ?_⟩
  refine Subtype.ext ?_
  exact GAssembly.vert_eq hwu rfl

omit [NeZero N] in
lemma dist_skelToFlat (x y : SkelAssembly k (flatShape R ρr ω)) :
    dist (skelToFlat R ρr ω hIdx x) (skelToFlat R ρr ω hIdx y) = dist x y := by
  show dist (skelToFlat R ρr ω hIdx x).1 (skelToFlat R ρr ω hIdx y).1
    = dist (SkelAssembly.toG x) (SkelAssembly.toG y)
  rw [GAssembly.dist_code, GAssembly.dist_code]
  simp only [GAssembly.code, SkelAssembly.toG_copy, SkelAssembly.toG_vert_val, skelToFlat,
    gCopyAddr_liftN_flatShape]

end SkelFlat

/-- A quasi-isometry precomposed with a surjective isometry. -/
lemma IsQIMap.isometry_comp_left {K : ℝ} {X X' Y : Type*} [MetricSpace X] [MetricSpace X']
    [MetricSpace Y] {Φ : X → X'} (hΦ : Function.Surjective Φ)
    (hΦd : ∀ x y, dist (Φ x) (Φ y) = dist x y) {f : X' → Y} (hf : IsQIMap K f) :
    IsQIMap K (fun x => f (Φ x)) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun y => ?_⟩
  · rw [← hΦd]; exact hf.upper _ _
  · rw [← hΦd]; exact hf.lower _ _
  · obtain ⟨x', hx'⟩ := hf.dense y
    obtain ⟨x, rfl⟩ := hΦ x'
    exact ⟨x, hx'⟩

/-! ### The presented skeleton as a cascade encoding -/

section Cascade

variable {N Nenc : ℕ} [NeZero N] {σ : Type*} {R : ℕ} {ρr : BRule σ}
  {ω : (GWord N → ℕ) × (List ℕ → σ)} {exc : ℕ → Option (ℕ × ℕ)} (hexc : ExcCompat exc)
  (hs : SkelBounded Nenc (bArityW Nenc R ρr ω))

/-- **The presented skeleton as a cascade encoding**: the engine's slot geometry over the
presented arities truncated off the presented skeleton. -/
noncomputable def chainCascade : CascadeEnc Nenc Nenc :=
  engineEnc exc Nenc (truncAr (bArityW Nenc R ρr ω)) hexc (arityBounded_truncAr hs)

omit [NeZero N] in
lemma chainCascade_k : (chainCascade hexc hs).k = truncAr (bArityW Nenc R ρr ω) := rfl

omit [NeZero N] in
/-- The prefix closure of the encoded presented skeleton is `𝔹`. -/
lemma chainCascade_inClosure (w : List Bool) : (chainCascade hexc hs).InClosure (bnat w) :=
  engineEnc_inClosure hexc _ (skelBounded_truncAr hs) (truncAr_le hs) w

omit [NeZero N] in
/-- **The shape over `𝔹` at a word and its label**: at the encoding of a presented vertex
the bare neck of its presented neck with the label of the vertex, and at an internal cascade
vertex the one-vertex shape with the label `0`. -/
lemma bFamily_chainCascade_cases (w : List Bool) :
    (∃ u : GWord Nenc, u ∈ sample (bArityW Nenc R ρr ω) ∧
      (chainCascade hexc hs).bFamily (flatShape R ρr ω) (bnat w)
        = flatG (bNeckAtC R ρr ω (toAddr u)) ∧
      ∀ lab : GWord Nenc → ℕ, (encField exc lab (truncAr (bArityW Nenc R ρr ω)) 0 w).1 = lab u)
    ∨ ((chainCascade hexc hs).bFamily (flatShape R ρr ω) (bnat w) = flatG 0 ∧
      ∀ lab : GWord Nenc → ℕ, (encField exc lab (truncAr (bArityW Nenc R ρr ω)) 0 w).1 = 0) := by
  set E := chainCascade hexc hs with hE
  set arT := truncAr (bArityW Nenc R ρr ω) with harT
  have har : ArityBounded Nenc arT := arityBounded_truncAr hs
  by_cases h : ∃ u, u ∈ sample arT ∧ w = engineEncWord exc Nenc arT u
  · obtain ⟨u, hu, rfl⟩ := h
    left
    refine ⟨u, by rw [harT, sample_truncAr] at hu; exact hu, ?_, fun lab => ?_⟩
    · exact CascadeEnc.bFamily_enc (E := E) hu
    · rw [encField_enc hexc lab har 0 hu]
  · right
    refine ⟨?_, fun lab => ?_⟩
    · have hb : E.bFamily (flatShape R ρr ω) (bnat w) = gOne := by
        refine CascadeEnc.bFamily_of_not_isImage ?_
        rintro ⟨u, hu, hw⟩
        exact h ⟨u, hu, bnat_injective hw⟩
      rw [hb]
      rfl
    · exact encField_of_not_image hexc lab har (skelBounded_truncAr hs) (truncAr_le hs) 0 h

omit [NeZero N] in
/-- **The flat assembly reaches the `𝔹`-assembly of the cascade encoding**: the flat
configurations are the bare-neck shapes over the presented skeleton, and reading the copies
at their encodings is a quasi-isometry at the letter range. -/
theorem exists_flat_to_bAssembly (hNenc : 1 ≤ Nenc) :
    ∃ e : PAssembly (flatAt R ρr ω) (Presented R ρr ω) (flat_pIdx R ρr ω)
        → BAssembly (chainCascade hexc hs) (flatShape R ρr ω),
      IsQIMap (Nenc : ℝ) e := by
  have hIdx : ∀ u : GWord Nenc, u ∈ sample (truncAr (bArityW Nenc R ρr ω))
      ↔ Presented R ρr ω (toAddr u) := by
    intro u
    rw [sample_truncAr, mem_sample_bArityW_iff]
  have hbound : ∀ w, Presented R ρr ω w → bArityAtC R ρr ω w ≤ Nenc := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := exists_word_of_presented R ρr ω hs hw
    exact (hs u hu).2
  have hΨ : Function.Bijective (skelToFlat R ρr ω hIdx) :=
    ⟨skelToFlat_injective R ρr ω hIdx, skelToFlat_surjective R ρr ω hIdx hbound⟩
  have h1 := IsQIMap.comp_isometry_symm hΨ (dist_skelToFlat R ρr ω hIdx)
    (CascadeEnc.skelToB_isQIMap (E := chainCascade hexc hs) (σ := flatShape R ρr ω) hNenc)
  obtain ⟨hΦ, hΦd⟩ := flatToG_isometry (bNeckAtC R ρr ω) (bArityAtC R ρr ω) (flat_pIdx R ρr ω)
  exact ⟨_, IsQIMap.isometry_comp_left hΦ.2 hΦd h1⟩

end Cascade

/-! ### The deterministic core of `thm:chain-general` -/

/-- **The quasi-isometry constant of `thm:chain-general` at scale `D`**: the flattening
scales of the two matched presentations at revealing depth `D²`, the letter range of the
encodings, and the glued transfer over `𝔹` at the neck comparison
`2 · chainRatio · D² + 1`, composed through `sample_qi_of_blob_matching`. -/
noncomputable def chainQIConst (J J' L D : ℕ) (a b : ℝ) : ℝ :=
  3 * (3 * (3 * (3 * flatScale (D ^ 2) (matchedBound J J' L) * (chainRange J J' L : ℝ))
    * (8 * (2 * (chainRatio a b * (D : ℝ) ^ 2) + 1) ^ 2)) * (3 * (chainRange J J' L : ℝ) ^ 2))
    * (3 * flatScale (D ^ 2) (matchedBound J' J L) ^ 2)

/-- **The deterministic core of `thm:chain-general`**: two chain-regime samples presented by
their matched rules at revealing depth `D²`, the presented arities within the letter range,
whose encoded label fields are aligned by one automorphism of `𝔹` to within one class of
the path graph, are `⌈chainQIConst⌉`-quasi-isometric as graphs.  The alignment is a
portrait of `𝔹`; at every word the shapes over `𝔹` are bare necks carrying the level class
and the coupled class of their lengths, equal or adjacent, so the necks are comparable at
`2 · chainRatio · D² + 1`; the glued transfer over `𝔹` gives a quasi-isometry of the
`𝔹`-assemblies, which the flattening carries back to the samples. -/
theorem sample_qi_of_chain_match {J J' N N' L D : ℕ} [NeZero N] [NeZero N']
    {θ : Offspring J} {θ' : Offspring J'}
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hθ1'₀ : 0 < θ' 1) (hθ1'' : θ' 1 < 1) (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma (θ 1) (θ' 1) * ((D : ℝ) - 1))
    {exc1 exc2 : ℕ → Option (ℕ × ℕ)} (hexc1 : ExcCompat exc1) (hexc2 : ExcCompat exc2)
    {ω : (GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))}
    {ω' : ((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
      × (List ℕ → ℝ)}
    (hd : IsChainField N ω.1) (hd' : IsChainField N' ω'.1.1)
    (hs : SkelBounded (chainRange J J' L) (bArityW (chainRange J J' L) (D ^ 2)
      (matchedRule (shiftSupp θ') L (matchedBound J J' L)) ω))
    (hs' : SkelBounded (chainRange J J' L) (bArityW (chainRange J J' L) (D ^ 2)
      (matchedRule (shiftSupp θ) L (matchedBound J' J L)) ω'.1))
    (hm : GraphMarkovMatching.InfMatch (cRel (GraphMatching.compat GraphMatching.pathGraph))
      (fun n => chainEnc J θ' L D exc1 ω n) (fun n => crossEnc θ θ' L D exc2 ω' n)) :
    ∃ F : {v : GWord N // v ∈ sample ω.1} → {v : GWord N' // v ∈ sample ω'.1.1},
      BranchingProcess.IsQIWith ⌈chainQIConst J J' L D (θ 1) (θ' 1)⌉₊
        (wordGraphN (· ∈ sample ω.1)) (wordGraphN (· ∈ sample ω'.1.1)) F := by
  set Nenc := chainRange J J' L with hNencdef
  set R := D ^ 2 with hRdef
  set ρr := matchedRule (shiftSupp θ') L (matchedBound J J' L) with hρr
  set ρr' := matchedRule (shiftSupp θ) L (matchedBound J' J L) with hρr'
  set lab₁ := chainLabW Nenc D R ρr ω with hlab₁
  set lab₂ := crossLabW Nenc (θ 1) (θ' 1) D R ρr' ω' with hlab₂
  set ar₁ := bArityW Nenc R ρr ω with har₁
  set ar₂ := bArityW Nenc R ρr' ω'.1 with har₂
  have hR : 1 ≤ R := Nat.one_le_pow _ _ (by omega)
  have hNenc : 1 ≤ Nenc := by rw [hNencdef, chainRange]; omega
  have hNencR : (1 : ℝ) ≤ (Nenc : ℝ) := by exact_mod_cast hNenc
  -- the neck comparison constant
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  set c : ℝ := chainRatio (θ 1) (θ' 1) * (D : ℝ) ^ 2 with hc
  have hc1 : (1 : ℝ) ≤ c := by
    have h1 := one_le_chainRatio (θ 1) (θ' 1)
    have h2 : (1 : ℝ) ≤ (D : ℝ) ^ 2 := one_le_pow₀ hD1
    rw [hc]
    nlinarith
  set K : ℝ := 2 * c + 1 with hK
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; linarith
  have hK8 : (1 : ℝ) ≤ 8 * K ^ 2 := by nlinarith
  -- the matching over the truncated arities
  have hm' : InfMatchK (cRel (GraphMatching.compat GraphMatching.pathGraph)) 1 0
      (fun n => encLab exc1 lab₁ (truncAr ar₁) 0 n)
      (fun n => encLab exc2 lab₂ (truncAr ar₂) 0 n) := by
    have h1 : (fun n => chainEnc J θ' L D exc1 ω n)
        = fun n => encLab exc1 lab₁ (truncAr ar₁) 0 n :=
      funext fun n => encLab_congr hexc1 lab₁ hs (fun u hu => truncAr_of_mem hu) 0 n
    have h2 : (fun n => crossEnc θ θ' L D exc2 ω' n)
        = fun n => encLab exc2 lab₂ (truncAr ar₂) 0 n :=
      funext fun n => encLab_congr hexc2 lab₂ hs' (fun u hu => truncAr_of_mem hu) 0 n
    have hm0 : InfMatchK (cRel (GraphMatching.compat GraphMatching.pathGraph)) 1 0
        (fun n => chainEnc J θ' L D exc1 ω n) (fun n => crossEnc θ θ' L D exc2 ω' n) := hm
    rw [h1, h2] at hm0
    exact hm0
  obtain ⟨π, hπ⟩ := exists_portrait_of_infMatchK _ hm'
  set E := chainCascade hexc1 hs with hE
  set E' := chainCascade hexc2 hs' with hE'
  -- the comparability of the shapes over `𝔹`
  have hcomp : ∀ w : Word, MarkedQI K (gShapeSpace (E.bFamily (flatShape R ρr ω) (bnat w)))
      (gShapeSpace (E'.bFamily (flatShape R ρr' ω'.1) (bnat (autOf π w)))) := by
    intro w
    have hrel := hπ w
    rw [labelAt_encLab _ _ _ _ le_rfl, labelAt_encLab _ _ _ _ (by rw [autOf_length])] at hrel
    have hrel' : GraphMatching.compat GraphMatching.pathGraph
        (encField exc1 lab₁ (truncAr ar₁) 0 w).1
        (encField exc2 lab₂ (truncAr ar₂) 0 (autOf π w)).1 := hrel
    obtain ⟨n₁, hb₁, hl₁⟩ : ∃ n₁, E.bFamily (flatShape R ρr ω) (bnat w) = flatG n₁ ∧
        (encField exc1 lab₁ (truncAr ar₁) 0 w).1 = levelMap D (n₁ + 1) := by
      rcases bFamily_chainCascade_cases hexc1 hs w with ⟨u, -, hb, hl⟩ | ⟨hb, hl⟩
      · exact ⟨_, hb, by rw [hl lab₁]; rfl⟩
      · exact ⟨0, hb, by rw [hl lab₁, levelMap, Nat.log_one_right]⟩
    obtain ⟨n₂, u₂, hb₂, hl₂⟩ : ∃ (n₂ : ℕ) (u₂ : ℝ),
        E'.bFamily (flatShape R ρr' ω'.1) (bnat (autOf π w)) = flatG n₂ ∧
        (encField exc2 lab₂ (truncAr ar₂) 0 (autOf π w)).1 = ellQ (θ 1) (θ' 1) D (n₂ + 1) u₂ := by
      rcases bFamily_chainCascade_cases hexc2 hs' (autOf π w) with ⟨u, -, hb, hl⟩ | ⟨hb, hl⟩
      · exact ⟨_, ω'.2 (toAddr u), hb, by rw [hl lab₂]; rfl⟩
      · exact ⟨0, 0, hb, by rw [hl lab₂, ellQ_one hθ1 hθ1' hθ1'₀ hθ1'' hD hgD]⟩
    rw [hl₁, hl₂] at hrel'
    obtain ⟨hr1, hr2⟩ := neck_ratio_of_compat hθ1 hθ1' hθ1'₀ hθ1'' hD hgD hrel'
    rw [hb₁, hb₂]
    exact flatG_markedQI hc1 hr1 hr2
  obtain ⟨g, hg⟩ := CascadeEnc.qi_of_bShape_matching hK1 π
    (fun w => ⟨fun _ => chainCascade_inClosure hexc2 hs' _,
      fun _ => chainCascade_inClosure hexc1 hs _⟩) hcomp
  obtain ⟨e, he⟩ := exists_flat_to_bAssembly hexc1 hs hNenc
  obtain ⟨e', he'⟩ := exists_flat_to_bAssembly hexc2 hs' hNenc
  obtain ⟨F, hF⟩ := sample_qi_of_blob_matching R ρr ρr' hR hd hd' hNencR hK8 he he' hg
  refine ⟨F, ?_⟩
  have hpos : (0 : ℝ) ≤ 3 * (3 * (3 * (3 * flatScale R ρr.T * (Nenc : ℝ)) * (8 * K ^ 2))
      * (3 * (Nenc : ℝ) ^ 2)) * (3 * flatScale R ρr'.T ^ 2) := by
    have := one_le_flatScale R ρr.T
    have := one_le_flatScale R ρr'.T
    positivity
  exact quasiIsometric_of_isSampleQIN hpos hF

/-! ### The almost sure events -/

section AlmostSure

variable {J N : ℕ}

/-- A field with a child at every vertex survives. -/
lemma survives_of_one_le [NeZero N] {c : GWord N → ℕ} (h : ∀ v, 1 ≤ c v) : Survives c := by
  have hmem : ∀ n, rep N n ∈ sample c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [rep_succ, BranchingProcess.mem_sample_append_singleton]
        exact ⟨ih, by simpa using Nat.lt_of_lt_of_le Nat.zero_lt_one (h (rep N n))⟩
  exact Set.infinite_of_injective_forall_mem
    (fun a b h => by simpa using congrArg List.length h) hmem

lemma rep_injective [NeZero N] : Function.Injective (rep N) :=
  fun a b h => by simpa using congrArg List.length h

/-- The mass of the one-vertex law at `{0, 1}` is `θ₁` in the chain regime. -/
lemma law_Iic_one (θ : Offspring J) (hθ0 : θ 0 = 0) :
    θ.law (Set.Iic 1) = ENNReal.ofReal (θ 1) := by
  have hset : (Set.Iic 1 : Set ℕ) = ↑({0, 1} : Finset ℕ) := by
    ext k
    simp only [Set.mem_Iic, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  rw [hset, Offspring.law, PMF.toMeasure_apply_finset, Finset.sum_pair (by norm_num),
    Offspring.toPMF_apply, Offspring.toPMF_apply, hθ0, ENNReal.ofReal_zero, zero_add]

/-- **The chain of first children splits almost surely**: the event that every vertex of the
chain has at most one child has mass at most `θ₁^M` for every `M`. -/
lemma survivalMeasure_neck_forever_null [NeZero N] (θ : Offspring J) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) :
    survivalMeasure (N := N) θ {c : GWord N → ℕ | ∀ n, c (rep N n) ≤ 1} = 0 := by
  have hsample : ∀ M : ℕ, BranchingProcess.sampleMeasure (N := N) θ
      {c : GWord N → ℕ | ∀ n, c (rep N n) ≤ 1} ≤ ENNReal.ofReal (θ 1) ^ M := by
    intro M
    have hsub : {c : GWord N → ℕ | ∀ n, c (rep N n) ≤ 1}
        ⊆ ⋂ v ∈ (Finset.range M).image (rep N),
          (BranchingProcess.coord v : (GWord N → ℕ) → ℕ) ⁻¹' Set.Iic 1 := by
      intro c hc
      simp only [Set.mem_iInter, Finset.mem_image, Finset.mem_range, Set.mem_preimage,
        Set.mem_Iic]
      rintro v ⟨n, -, rfl⟩
      exact hc n
    refine le_trans (measure_mono hsub) ?_
    have hind := (BranchingProcess.coord_iIndepFun (ι := GWord N) θ.law).measure_inter_preimage_eq_mul
      ((Finset.range M).image (rep N)) (sets := fun _ => Set.Iic 1) (fun _ _ => measurableSet_Iic)
    show BranchingProcess.fieldMeasure θ.law _ ≤ _
    rw [hind]
    have hfac : ∀ v ∈ (Finset.range M).image (rep N),
        BranchingProcess.fieldMeasure θ.law (BranchingProcess.coord v ⁻¹' Set.Iic 1)
          = ENNReal.ofReal (θ 1) := by
      intro v _
      rw [BranchingProcess.coord_law _ v measurableSet_Iic, law_Iic_one θ hθ0]
    rw [Finset.prod_congr rfl hfac, Finset.prod_const,
      Finset.card_image_of_injective _ rep_injective, Finset.card_range]
  have hlt : ENNReal.ofReal (θ 1) < 1 := ENNReal.ofReal_lt_one.mpr hθ1
  have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  have h0 : BranchingProcess.sampleMeasure (N := N) θ {c : GWord N → ℕ | ∀ n, c (rep N n) ≤ 1}
      = 0 :=
    nonpos_iff_eq_zero.mp (ge_of_tendsto' htend hsample)
  rw [BranchingProcess.survivalMeasure_apply, measure_mono_null Set.inter_subset_right h0,
    mul_zero]

/-- **A conditioned chain-regime sample is a chain field almost surely**: every vertex has
between one and `N` children, and the chain of first children below every vertex splits. -/
theorem ae_isChainField [NeZero N] (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, IsChainField N c := by
  have h1 := ae_forall_pos_of_zero (N := N) θ hθ0
  have h2 : ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v, c v ≤ N := by
    refine ae_all_iff.mpr fun v => ?_
    rw [ae_iff]
    have := BranchingProcess.survivalMeasure_coord_gt θ hJN v
    simpa [not_le] using this
  have hS := survivalMeasure_neck_forever_null (N := N) θ hθ0 hθ1
  have h3 : ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v, Survives (ambSub c v) →
      ∃ n, 2 ≤ c (v ++ rep N n) := by
    refine ae_all_iff.mpr fun v => ?_
    rw [ae_iff]
    refine measure_mono_null (fun c hc => ?_) (survivalMeasure_ambSub_null θ hS v)
    simp only [Set.mem_setOf_eq, Classical.not_imp, not_exists, not_le] at hc ⊢
    exact ⟨hc.1, fun n => by rw [ambSub_apply]; have := hc.2 n; omega⟩
  filter_upwards [h1, h2, h3] with c hc1 hc2 hc3
  exact ⟨hc1, hc2, fun v => hc3 v (survives_of_one_le fun w => hc1 _)⟩

/-- **The presented arities lie in the letter range on the presented skeleton almost
surely**, over any space carrying a label field and an arity field whose pairs are i.i.d.
with a product law over prefix-closed compatible probes: the arity of a skeleton vertex
outside the support of the arity law is a pattern of mass zero. -/
theorem ae_skelBounded_of_pattern {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Nenc : ℕ}
    {lab ar : Ω → GWord Nenc → ℕ} (μ ν : PMF ℕ)
    (hpat : ∀ F : Finset (GWord Nenc), (∀ u ∈ F, ∀ p : GWord Nenc, p <+: u → p ∈ F) →
      ∀ a k : GWord Nenc → ℕ, (∀ u ∈ F, ∀ i : Fin Nenc, u ++ [i] ∈ F → (i : ℕ) < k u) →
        P (⋂ u ∈ F, ({ω | lab ω u = a u} ∩ {ω | ar ω u = k u})) = ∏ u ∈ F, μ (a u) * ν (k u))
    {M : ℕ} (hsupp : ∀ k, ν k ≠ 0 → k ≤ M) :
    ∀ᵐ ω ∂P, ∀ u, u ∈ sample (ar ω) → ar ω u ≤ M := by
  refine ae_all_iff.mpr fun u => ?_
  rw [ae_iff]
  set F : Finset (GWord Nenc) := u.inits.toFinset with hF
  have hmemF : ∀ p, p ∈ F ↔ p <+: u := fun p => by
    rw [hF, List.mem_toFinset, List.mem_inits]
  have huF : u ∈ F := (hmemF u).mpr (List.prefix_refl u)
  have hpc : ∀ p ∈ F, ∀ q : GWord Nenc, q <+: p → q ∈ F := fun p hp q hq =>
    (hmemF q).mpr (hq.trans ((hmemF p).mp hp))
  let ext : (↥F → ℕ × ℕ) → (GWord Nenc → ℕ) × (GWord Nenc → ℕ) := fun g =>
    (fun p => if h : p ∈ F then (g ⟨p, h⟩).1 else 0,
      fun p => if h : p ∈ F then (g ⟨p, h⟩).2 else 0)
  let Good : (↥F → ℕ × ℕ) → Prop := fun g =>
    (∀ (p : ↥F) (i : Fin Nenc), (p : GWord Nenc) ++ [i] ∈ F → (i : ℕ) < (g p).2) ∧
      M < (g ⟨u, huF⟩).2
  let A : (↥F → ℕ × ℕ) → Set Ω := fun g =>
    ⋂ p ∈ F, ({ω | lab ω p = (ext g).1 p} ∩ {ω | ar ω p = (ext g).2 p})
  have hA : ∀ g, Good g → P (A g) = 0 := by
    intro g hg
    have hext2 : ∀ p : ↥F, (ext g).2 p = (g p).2 := fun p => by
      simp only [ext, dif_pos p.2]
    rw [hpat F hpc (ext g).1 (ext g).2
      (fun p hp i hpi => by rw [hext2 ⟨p, hp⟩]; exact hg.1 ⟨p, hp⟩ i hpi)]
    refine Finset.prod_eq_zero huF ?_
    rw [hext2 ⟨u, huF⟩]
    have hν : ν (g ⟨u, huF⟩).2 = 0 := by
      by_contra h
      exact absurd (hsupp _ h) (not_le.mpr hg.2)
    rw [hν, mul_zero]
  have hN : P (⋃ (g : ↥F → ℕ × ℕ) (_ : Good g), A g) = 0 :=
    measure_iUnion_null fun g => measure_iUnion_null fun hg => hA g hg
  refine measure_mono_null (fun ω hω => ?_) hN
  simp only [Set.mem_setOf_eq, Classical.not_imp, not_le] at hω
  obtain ⟨hu, hbad⟩ := hω
  refine Set.mem_iUnion.mpr ⟨fun p => (lab ω p, ar ω p), Set.mem_iUnion.mpr
    ⟨⟨fun p i hpi => ?_, hbad⟩, ?_⟩⟩
  · exact (mem_sample_iff_prefix u).mp hu p i ((hmemF _).mp hpi)
  · simp only [A, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, ext]
    intro p hp
    simp only [dif_pos hp, and_self]

/-- The presented arity of a presented vertex of a chain field is at least two. -/
lemma two_le_bArityAtC_of_presented [NeZero N] {σ : Type*} {R : ℕ} (ρr : BRule σ)
    {ω : (GWord N → ℕ) × (List ℕ → σ)} (hR : 1 ≤ R) (hd : IsChainField N ω.1) {u : List ℕ}
    (hu : Presented R ρr ω u) : 2 ≤ bArityAtC R ρr ω u := by
  have h := (presented_spec R ρr hR u ω hd hu).1
  rw [bArityAtC, bArityC]
  have := h.two_le_gArity
  omega

end AlmostSure

/-! ### The presented arity law of the matched rule lies in the letter range -/

section Range

variable {J J' N : ℕ}

/-- **The support of the presented arity law of the matched rule lies in the letter range**
`[2, chainRange J J' L]`, for a window past the cofiniteness threshold and a miss mass at
most one half: clause \labelcref{it:matched-support} of `thm:matched-presentation`. -/
lemma bArityLaw_matched_range (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hθ0' : θ' 0 = 0) (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (N₀ : ℕ)
    (hN₀ : ∀ n, N₀ ≤ n → (shiftSupp θ).gcd id ∣ n →
      n ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ))
    {L : ℕ} (hL : N₀ + (J - 1) ≤ L) {R : ℕ} (hφ : θ 1 ^ R ≤ 1 / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    haveI : Inhabited (shiftSupp θ') := ⟨⟨J' - 1, max_mem_shiftSupp θ' hJ2' hθJ'⟩⟩
    ∀ k, bArityLaw θ (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L) hδ0.le hδ1) R
      (matchedRule (shiftSupp θ') L (matchedBound J J' L)) k ≠ 0 →
        2 ≤ k ∧ k ≤ chainRange J J' L := by
  haveI : Inhabited (shiftSupp θ') := ⟨⟨J' - 1, max_mem_shiftSupp θ' hJ2' hθJ'⟩⟩
  have hAne := shiftSupp_nonempty θ hJ2 hθJ
  set p : ℝ := (shiftSupp θ).inf' hAne (shiftLaw θ) with hpdef
  have hp0 : 0 < p := (Finset.lt_inf'_iff _).mpr (shiftLaw_pos θ hθ0 hθ1')
  have hPp : ∀ a ∈ shiftSupp θ, p ≤ shiftLaw θ a := fun a ha => Finset.inf'_le _ ha
  have hp1 : p ≤ 1 :=
    le_trans (hPp _ (max_mem_shiftSupp θ hJ2 hθJ))
      (shiftLaw_le_one θ hθ0 hθ1' _ (max_mem_shiftSupp θ hJ2 hθJ))
  obtain ⟨hsup, -⟩ := matchedArityPMF_support_floor θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hθ0' hθ1''
    hJ2' hθJ' N₀ hN₀ hL hp0 hp1 hPp hφ hδ0 hδ1 (J - 1) le_rfl
  intro k hk
  obtain ⟨s, -, hs0, hsM, rfl⟩ := (hsup k).mp hk
  rw [chainRange]
  omega

/-- The letter range is symmetric in the two laws. -/
lemma chainRange_comm (J J' L : ℕ) : chainRange J' J L = chainRange J J' L := by
  rw [chainRange, chainRange, max_comm]

end Range

/-! ### The matching event is measurable -/

section Measurable

variable {J J' N N' : ℕ}

lemma measurable_chainEnc (θ' : Offspring J') (L D : ℕ) (exc : ℕ → Option (ℕ × ℕ)) (n : ℕ) :
    Measurable fun ω : (GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))
      => chainEnc J θ' L D exc ω n :=
  measurable_encLab_of (fun w a => measurableSet_chainLab_fibre D (D ^ 2) _ (toAddr w) a)
    (fun w k => measurableSet_bArityAtC_fibre (D ^ 2) _ (toAddr w) k) exc 0 n

lemma measurable_crossEnc (θ : Offspring J) (θ' : Offspring J') (L D : ℕ)
    (exc : ℕ → Option (ℕ × ℕ)) (n : ℕ) :
    Measurable fun ω : ((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
      × (List ℕ → ℝ) => crossEnc θ θ' L D exc ω n :=
  measurable_encLab_of
    (fun w x => measurableSet_crossLab_fibre (θ 1) (θ' 1) D (D ^ 2) _ (toAddr w) x)
    (fun w k => measurable_fst (measurableSet_bArityAtC_fibre (D ^ 2) _ (toAddr w) k)) exc 0 n

/-- **The matching event is measurable**: the intersection over the heights of the
preimages of countable sets. -/
lemma measurableSet_chain_match (θ : Offspring J) (θ' : Offspring J') (L D : ℕ)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) :
    MeasurableSet {ω : ((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) ×
        (((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
          × (List ℕ → ℝ)) |
      GraphMarkovMatching.InfMatch (cRel (GraphMatching.compat GraphMatching.pathGraph))
        (fun n => chainEnc J θ' L D exc1 ω.1 n) (fun n => crossEnc θ θ' L D exc2 ω.2 n)} := by
  set Rv := cRel (GraphMatching.compat GraphMatching.pathGraph) with hRv
  have hset : {ω : ((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) ×
        (((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
          × (List ℕ → ℝ)) |
        GraphMarkovMatching.InfMatch Rv
          (fun n => chainEnc J θ' L D exc1 ω.1 n) (fun n => crossEnc θ θ' L D exc2 ω.2 n)}
      = ⋂ n, (fun ω : ((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) ×
          (((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
            × (List ℕ → ℝ)) =>
          (chainEnc J θ' L D exc1 ω.1 n, crossEnc θ θ' L D exc2 ω.2 n)) ⁻¹'
          {p | GraphMarkovMatching.Support.fullSimK Rv 1 0 n p.1 p.2} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact GraphMarkovMatching.Support.infMatchK_iff_forall_level Rv 1 0 _ _
      (fun n => restrictLab_encLab exc1 _ _ 0 n) (fun n => restrictLab_encLab exc2 _ _ 0 n)
  rw [hset]
  refine MeasurableSet.iInter fun n => ?_
  exact (((measurable_chainEnc θ' L D exc1 n).comp measurable_fst).prodMk
    ((measurable_crossEnc θ θ' L D exc2 n).comp measurable_snd))
    ((Set.to_countable _).measurableSet)

end Measurable

/-! ### `thm:chain-general`: the rate and the almost sure statement -/

section Main

variable {J J' N N' : ℕ}

/-- **`thm:chain-general`, the rate.**  For two chain-regime laws with equal branching
semigroups, cofinite from `N₀` on, every window `L` past a threshold and every `δ ∈ (0, 1]`
give a scale `D₇` and a constant `K` such that for every `D ≥ D₇`, two independent presented
samples of the matched presentations at revealing depth `D²` fail to be
`⌈chainQIConst⌉`-quasi-isometric with probability at most `K θ₁^{D²/2}`. -/
theorem chain_general_rate (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0) (hθ1'₀ : 0 < θ' 1)
    (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      = AddSubmonoid.closure (shiftSupp θ' : Set ℕ))
    (N₀ : ℕ)
    (hN₀ : ∀ n, N₀ ≤ n → (shiftSupp θ).gcd id ∣ n →
      n ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ)) :
    ∃ L₁ : ℕ, ∀ L, L₁ ≤ L →
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1), ∃ (D₇ : ℕ) (K : ℝ), ∀ D, D₇ ≤ D →
        chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1
          {ω | ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1.1},
            BranchingProcess.IsQIWith ⌈chainQIConst J J' L D (θ 1) (θ' 1)⌉₊
              (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1.1)) F}
          ≤ ENNReal.ofReal (K * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2)) := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero N' := ⟨by omega⟩
  haveI : Inhabited (shiftSupp θ) := ⟨⟨J - 1, max_mem_shiftSupp θ hJ2 hθJ⟩⟩
  haveI : Inhabited (shiftSupp θ') := ⟨⟨J' - 1, max_mem_shiftSupp θ' hJ2' hθJ'⟩⟩
  have hq := extinction_lt_one_of_chain θ hθ0
  have hq' := extinction_lt_one_of_chain θ' hθ0'
  have hN₀' : ∀ n, N₀ ≤ n → (shiftSupp θ').gcd id ∣ n →
      n ∈ AddSubmonoid.closure (shiftSupp θ' : Set ℕ) := by
    rw [← hsem, ← gcd_eq_of_closure_eq hsem]
    exact hN₀
  obtain ⟨L₁, hL₁⟩ := exists_engine_match_chain' θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hJN' hθ0' hθ1'₀
    hθ1'' hJ2' hθJ' hsem N₀ hN₀
  refine ⟨max L₁ (N₀ + max (J - 1) (J' - 1)), fun L hL δ hδ0 hδ1 => ?_⟩
  have hLL₁ : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLM : N₀ + max (J - 1) (J' - 1) ≤ L := le_trans (le_max_right _ _) hL
  have hLN : N₀ + (J - 1) ≤ L := by
    have := le_max_left (J - 1) (J' - 1)
    omega
  have hLN' : N₀ + (J' - 1) ≤ L := by
    have := le_max_right (J - 1) (J' - 1)
    omega
  obtain ⟨exc1, exc2, hexc1, hexc2, hmain⟩ := hL₁ L hLL₁
  obtain ⟨D₇, K, hK⟩ := hmain δ hδ0 hδ1
  obtain ⟨D₀, hD₀⟩ := exists_chain_scale hθ1 hθ1' hθ1'₀ hθ1'' (ε := 1) one_pos
  refine ⟨max D₇ D₀, K, fun D hD => ?_⟩
  have hDD₇ : D₇ ≤ D := le_trans (le_max_left _ _) hD
  have hDD₀ : D₀ ≤ D := le_trans (le_max_right _ _) hD
  obtain ⟨hD5, -, -, -, -, hφa, hφb, hgD⟩ := hD₀ D hDD₀
  have hD2 : 2 ≤ D := by omega
  have hR : 1 ≤ D ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hbound := hK D hDD₇
  -- the probability spaces
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  haveI hP1 : IsProbabilityMeasure (blobMeasure (N := N) θ
      (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L) hδ0.le hδ1)) :=
    inferInstanceAs (IsProbabilityMeasure ((survivalMeasure (N := N) θ).prod
      (BranchingProcess.fieldMeasure _)))
  haveI hP2' : IsProbabilityMeasure (blobMeasure (N := N') θ'
      (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L) hδ0.le hδ1)) :=
    inferInstanceAs (IsProbabilityMeasure ((survivalMeasure (N := N') θ').prod
      (BranchingProcess.fieldMeasure _)))
  haveI hP2 : IsProbabilityMeasure (coupledBlobMeasure (N := N') θ'
      (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L) hδ0.le hδ1)) :=
    inferInstanceAs (IsProbabilityMeasure ((blobMeasure (N := N') θ' _).prod
      (uniformField (List ℕ))))
  haveI hPm : IsProbabilityMeasure
      (chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.prod _ _))
  -- the matching event fails with probability at most `K θ₁^{D²/2}`
  set M := {ω : ((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) ×
      (((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
        × (List ℕ → ℝ)) |
    GraphMarkovMatching.InfMatch (cRel (GraphMatching.compat GraphMatching.pathGraph))
      (fun n => chainEnc J θ' L D exc1 ω.1 n) (fun n => crossEnc θ θ' L D exc2 ω.2 n)} with hM
  have hfail : chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1 Mᶜ
      ≤ ENNReal.ofReal (K * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2)) := by
    rw [prob_compl_eq_one_sub (measurableSet_chain_match θ θ' L D exc1 exc2)]
    have h1 := tsub_le_iff_right.mp hbound
    rw [add_comm] at h1
    exact tsub_le_iff_right.mpr h1
  -- the good events: chain fields whose presented arities lie in the letter range
  set Nenc := chainRange J J' L with hNenc
  set ρr := matchedRule (shiftSupp θ') L (matchedBound J J' L) with hρr
  set ρr' := matchedRule (shiftSupp θ) L (matchedBound J' J L) with hρr'
  have hsupp1 := bArityLaw_matched_range θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hθ0' hθ1'' hJ2' hθJ' N₀
    hN₀ hLN hφa hδ0 hδ1
  have hsupp2 := bArityLaw_matched_range θ' hJN' hθ0' hθ1'₀ hθ1'' hJ2' hθJ' θ hθ0 hθ1' hJ2 hθJ
    N₀ hN₀' hLN' hφb hδ0 hδ1
  have hgood₁ : ∀ᵐ ω ∂blobMeasure (N := N) θ
      (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L) hδ0.le hδ1),
      IsChainField N ω.1 ∧ SkelBounded Nenc (bArityW Nenc (D ^ 2) ρr ω) := by
    have hbd := ae_skelBounded_of_pattern
      (blobMeasure (N := N) θ (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L) hδ0.le hδ1))
      (lab := fun ω => chainLabW Nenc D (D ^ 2) ρr ω) (ar := fun ω => bArityW Nenc (D ^ 2) ρr ω)
      (qPMF (θ.nonneg 1) hθ1' hD2)
      (bArityPMF θ hJN hq (chain_hs1 θ hθ0 hθ1') _ (D ^ 2) ρr)
      (pattern_of_listPattern _ _ _
        (fun F hpc a j hcomp => blobMeasure_chainLab_pattern θ hJN hθ0 hθ1' _ (D ^ 2) ρr hD2
          F hpc a j hcomp))
      (M := Nenc) (fun k hk => (hsupp1 k hk).2)
    filter_upwards [ae_of_fst (ν := BranchingProcess.fieldMeasure _)
      (ae_isChainField θ hJN hθ0 hθ1'), hbd] with ω h1 h2
    refine ⟨h1, fun u hu => ⟨?_, h2 u hu⟩⟩
    exact two_le_bArityAtC_of_presented ρr hR h1 ((mem_sample_bArityW_iff _ _ _ u).mp hu)
  have hgood₂ : ∀ᵐ ω ∂coupledBlobMeasure (N := N') θ'
      (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L) hδ0.le hδ1),
      IsChainField N' ω.1.1 ∧ SkelBounded Nenc (bArityW Nenc (D ^ 2) ρr' ω.1) := by
    have hbd := ae_skelBounded_of_pattern
      (coupledBlobMeasure (N := N') θ' (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L) hδ0.le hδ1))
      (lab := fun ω => crossLabW Nenc (θ 1) (θ' 1) D (D ^ 2) ρr' ω)
      (ar := fun ω => bArityW' Nenc (D ^ 2) ρr' ω)
      (qPMF hθ1.le hθ1' hD2)
      (bArityPMF θ' hJN' hq' (chain_hs1 θ' hθ0' hθ1'') _ (D ^ 2) ρr')
      (pattern_of_listPattern _ _ _
        (fun F hpc x j hcomp => crossLab_pattern θ' hJN' hθ0' hθ1'₀ hθ1'' _ (D ^ 2) ρr' hθ1 hθ1'
          hD2 hgD F hpc x j hcomp))
      (M := Nenc) (fun k hk => by rw [hNenc, ← chainRange_comm]; exact (hsupp2 k hk).2)
    filter_upwards [ae_of_fst (ν := uniformField (List ℕ))
      (ae_of_fst (ν := BranchingProcess.fieldMeasure _) (ae_isChainField θ' hJN' hθ0' hθ1'')),
      hbd] with ω h1 h2
    refine ⟨h1, fun u hu => ⟨?_, h2 u hu⟩⟩
    exact two_le_bArityAtC_of_presented ρr' hR h1 ((mem_sample_bArityW_iff _ _ _ u).mp hu)
  have hgood : ∀ᵐ ω ∂chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1,
      (IsChainField N ω.1.1 ∧ SkelBounded Nenc (bArityW Nenc (D ^ 2) ρr ω.1)) ∧
      (IsChainField N' ω.2.1.1 ∧ SkelBounded Nenc (bArityW Nenc (D ^ 2) ρr' ω.2.1)) := by
    rw [chainTwoMeasure]
    filter_upwards [ae_of_fst (ν := coupledBlobMeasure (N := N') θ'
        (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L) hδ0.le hδ1)) hgood₁,
      ae_of_snd (μ := blobMeasure (N := N) θ
        (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L) hδ0.le hδ1)) hgood₂] with ω h1 h2
    exact ⟨h1, h2⟩
  -- on the good matching event the samples are quasi-isometric
  have hsub : {ω : ((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) ×
        (((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
          × (List ℕ → ℝ)) |
        ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1.1},
          BranchingProcess.IsQIWith ⌈chainQIConst J J' L D (θ 1) (θ' 1)⌉₊
            (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1.1)) F}
      ⊆ Mᶜ ∪ {ω | ¬ ((IsChainField N ω.1.1 ∧ SkelBounded Nenc (bArityW Nenc (D ^ 2) ρr ω.1)) ∧
      (IsChainField N' ω.2.1.1 ∧ SkelBounded Nenc (bArityW Nenc (D ^ 2) ρr' ω.2.1)))} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hm, ⟨hd, hs⟩, ⟨hd', hs'⟩⟩ := hcon
    exact hω (sample_qi_of_chain_match hθ1 hθ1' hθ1'₀ hθ1'' hD2 hgD hexc1 hexc2 hd hd' hs hs' hm)
  calc chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1 _
      ≤ chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1 (Mᶜ ∪ _) :=
        measure_mono hsub
    _ ≤ chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1 Mᶜ
        + chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1 _ :=
        measure_union_le _ _
    _ = chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1 Mᶜ + 0 := by
        rw [ae_iff.mp hgood]
    _ ≤ ENNReal.ofReal (K * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2)) := by rw [add_zero]; exact hfail

/-- **`thm:chain-general`, the almost sure statement on the presented space**: the failure
rates `K θ₁^{D²/2}` fall below every threshold, so almost surely some scale succeeds. -/
theorem chain_general_ae_small (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0) (hθ1'₀ : 0 < θ' 1)
    (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      = AddSubmonoid.closure (shiftSupp θ' : Set ℕ))
    (N₀ : ℕ)
    (hN₀ : ∀ n, N₀ ≤ n → (shiftSupp θ).gcd id ∣ n →
      n ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ)) :
    ∃ L₁ : ℕ, ∀ L, L₁ ≤ L → ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1),
      ∀ᵐ ω ∂chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1,
        BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1.1))
          (wordGraphN (· ∈ sample ω.2.1.1)) := by
  obtain ⟨L₁, hL₁⟩ := chain_general_rate θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hJN' hθ0' hθ1'₀ hθ1''
    hJ2' hθJ' hsem N₀ hN₀
  refine ⟨L₁, fun L hL δ hδ0 hδ1 => ?_⟩
  obtain ⟨D₇, K, hrate⟩ := hL₁ L hL δ hδ0 hδ1
  rw [ae_iff]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  have hεpos : (0 : ℝ) < ε := hε
  have hKpos : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ε / max K 1) (by positivity) hθ1'
  set D := max (max D₇ n) 2 with hD
  have hD₇ : D₇ ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
  have hnD : n ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
  have hD2 : 2 ≤ D := le_max_right _ _
  have hsmall : K * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2) ≤ ε := by
    have hexp : (n : ℝ) ≤ (1 / 2 : ℝ) * (D : ℝ) ^ 2 := by
      have h1 : (n : ℝ) ≤ D := by exact_mod_cast hnD
      have h2 : (2 : ℝ) ≤ D := by exact_mod_cast hD2
      nlinarith
    have h1 : θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2) ≤ θ 1 ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hθ1 hθ1'.le hexp
    rw [Real.rpow_natCast] at h1
    have h2 : K ≤ max K 1 := le_max_left _ _
    have h3 : 0 ≤ θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2) := Real.rpow_nonneg hθ1.le _
    calc K * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2)
        ≤ max K 1 * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ max K 1 * θ 1 ^ n := mul_le_mul_of_nonneg_left h1 hKpos.le
      _ ≤ max K 1 * (ε / max K 1) := mul_le_mul_of_nonneg_left hn.le hKpos.le
      _ = ε := mul_div_cancel₀ (ε : ℝ) hKpos.ne'
  have hsub : {ω : ((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L))) ×
        (((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L)))
          × (List ℕ → ℝ)) |
        ¬ BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1.1))
          (wordGraphN (· ∈ sample ω.2.1.1))}
      ⊆ {ω | ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1.1},
          BranchingProcess.IsQIWith ⌈chainQIConst J J' L D (θ 1) (θ' 1)⌉₊
            (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1.1)) F} := by
    rintro ω hω ⟨F, hF⟩
    exact hω ⟨_, F, hF⟩
  calc chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1 _
      ≤ chainTwoMeasure (N := N) (N' := N') θ hθ0 hθ1' θ' hθ0' hθ1'' L hδ0.le hδ1 _ :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (K * θ 1 ^ ((1 / 2 : ℝ) * (D : ℝ) ^ 2)) := hrate D hD₇
    _ ≤ (ε : ℝ≥0∞) := ENNReal.ofReal_le_of_le_toReal (by simpa using hsmall)
    _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm

/-- An almost sure property of the first two coordinates of a triple product descends to
the product of the first two factors. -/
lemma ae_prod_fst_of_triple {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {τ : Measure γ} [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure τ] {p : α × β → Prop}
    (h : ∀ᵐ ω ∂(μ.prod (ν.prod τ)), p (ω.1, ω.2.1)) : ∀ᵐ ω ∂(μ.prod ν), p ω := by
  rw [ae_iff] at h ⊢
  exact null_of_prod_assoc μ ν τ h

/-- **`thm:chain-general`**: two finitely supported supercritical chain-regime laws
`θ₀ = 0 < θ₁ < 1` with equal branching semigroups, sampled independently, are almost
surely quasi-isometric; the cofiniteness threshold in the gcd lattice comes from
`semigroup_cofinite_gcd`, and the coin fields of the matched presentations and the
uniform field of the coupled labelling are integrated out. -/
theorem chain_general_ae (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0) (hθ1'₀ : 0 < θ' 1)
    (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      = AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) :
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) := by
  obtain ⟨N₀, hN₀⟩ := semigroup_cofinite_gcd (shiftSupp θ)
  haveI : Inhabited (shiftSupp θ) := ⟨⟨J - 1, max_mem_shiftSupp θ hJ2 hθJ⟩⟩
  haveI : Inhabited (shiftSupp θ') := ⟨⟨J' - 1, max_mem_shiftSupp θ' hJ2' hθJ'⟩⟩
  have hq := extinction_lt_one_of_chain θ hθ0
  have hq' := extinction_lt_one_of_chain θ' hθ0'
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  obtain ⟨L₁, hL₁⟩ := chain_general_ae_small θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hJN' hθ0' hθ1'₀ hθ1''
    hJ2' hθJ' hsem N₀ hN₀
  have h := hL₁ L₁ le_rfl 1 one_pos le_rfl
  haveI hP1 : IsProbabilityMeasure (blobMeasure (N := N) θ
      (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L₁) zero_le_one le_rfl)) :=
    inferInstanceAs (IsProbabilityMeasure ((survivalMeasure (N := N) θ).prod
      (BranchingProcess.fieldMeasure _)))
  haveI hP2' : IsProbabilityMeasure (blobMeasure (N := N') θ'
      (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L₁) zero_le_one le_rfl)) :=
    inferInstanceAs (IsProbabilityMeasure ((survivalMeasure (N := N') θ').prod
      (BranchingProcess.fieldMeasure _)))
  rw [chainTwoMeasure] at h
  have h2 := ae_prod_fst_of_triple
    (μ := blobMeasure (N := N) θ (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L₁) zero_le_one le_rfl))
    (ν := blobMeasure (N := N') θ' (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L₁) zero_le_one le_rfl))
    (τ := uniformField (List ℕ))
    (p := fun z : ((GWord N → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ') (matchedBound J J' L₁))) ×
        ((GWord N' → ℕ) × (List ℕ → MatchedCoin (shiftSupp θ) (matchedBound J' J L₁))) =>
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample z.1.1))
        (wordGraphN (· ∈ sample z.2.1))) h
  exact ae_prod_fst_fst (μ := survivalMeasure (N := N) θ)
    (ν := BranchingProcess.fieldMeasure (chainCoinLaw θ' hθ0' hθ1'' (matchedBound J J' L₁) zero_le_one le_rfl))
    (μ' := survivalMeasure (N := N') θ')
    (ν' := BranchingProcess.fieldMeasure (chainCoinLaw θ hθ0 hθ1' (matchedBound J' J L₁) zero_le_one le_rfl)) h2


end Main

end ChainClasses
