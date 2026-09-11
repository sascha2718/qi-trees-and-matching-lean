import ChainClasses.Universality.SampleAssembly
import ChainClasses.Regime.ChainNeckLaw
import ChainClasses.Chain.Coupling

/-!
Bare-neck shapes and the marked metric comparison used by the direct chain application.
The neck coupling acts only on lengths; the reduced arity laws remain unchanged.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (sample Survives skeletonDegree survivors childSet bushAt)

/-- The address `n` steps down the neck: `n` zeros. -/
def pRep (n : ℕ) : List ℕ := List.replicate n 0

@[simp] lemma pRep_zero : pRep 0 = [] := rfl

@[simp] lemma pRep_length (n : ℕ) : (pRep n).length = n := by simp [pRep]

lemma pRep_prefix_pRep {i n : ℕ} (h : i ≤ n) : pRep i <+: pRep n := by
  rw [pRep, pRep, List.prefix_replicate_iff]
  simp [h]

/-- A prefix of the neck is a neck vertex. -/
lemma eq_pRep_of_prefix {p : List ℕ} {n : ℕ} (h : p <+: pRep n) : p = pRep p.length := by
  rw [pRep, List.prefix_replicate_iff] at h
  exact h.2

/-- The bare neck of `n` edges as a shape: `n + 1` neck vertices, no bushes, an empty
bouquet. -/
def flatG (n : ℕ) : GShape := ⟨n, fun _ => []⟩

/-- The path of `n` edges as a rose tree. -/
def pathTree : ℕ → RTree
  | 0 => .node []
  | n + 1 => .node [pathTree n]

lemma flatG_decs (n : ℕ) : (flatG n).decs = List.replicate (n + 1) [] := by
  rw [GShape.decs, flatG]
  exact List.ofFn_const (n + 1) []

lemma realiseAux_replicate : ∀ n : ℕ,
    GShape.realiseAux (List.replicate (n + 1) []) = pathTree n
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, List.replicate_succ]
      show RTree.node ([] ++ [GShape.realiseAux ([] :: List.replicate n [])]) = _
      rw [← List.replicate_succ, realiseAux_replicate n]
      rfl

lemma flatG_realise (n : ℕ) : (flatG n).realise = pathTree n := by
  rw [GShape.realise, flatG_decs, realiseAux_replicate]

lemma gExitAddr_replicate : ∀ n : ℕ, gExitAddr (List.replicate (n + 1) ([] : List RTree)) = pRep n
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, List.replicate_succ, gExitAddr_cons₂, ← List.replicate_succ,
        gExitAddr_replicate n, pRep, pRep, List.replicate_succ]
      rfl

lemma flatG_exitAddr (n : ℕ) : (flatG n).exitAddr = pRep n := by
  rw [GShape.exitAddr, flatG_decs, gExitAddr_replicate]

lemma flatG_bouquet (n : ℕ) : (flatG n).bouquet = [] := rfl

/-- The addresses of the path are the neck vertices. -/
lemma isAddr_pathTree : ∀ (n : ℕ) (p : List ℕ), RTree.IsAddr (pathTree n) p ↔ p <+: pRep n
  | 0, [] => by simp
  | 0, i :: q => by
      rw [pathTree, RTree.isAddr_cons]
      simp
  | n + 1, [] => by simp
  | n + 1, i :: q => by
      rw [pathTree, RTree.isAddr_cons, pRep, List.replicate_succ, List.cons_prefix_cons, ← pRep]
      constructor
      · rintro ⟨hi, h⟩
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨rfl, (isAddr_pathTree n q).mp (by simpa using h)⟩
      · rintro ⟨rfl, h⟩
        exact ⟨by simp, by simpa using (isAddr_pathTree n q).mpr h⟩

/-- The vertices of the bare-neck shape are the neck vertices. -/
lemma mem_addrList_flatG (n : ℕ) (p : List ℕ) :
    p ∈ RTree.addrList (flatG n).realise ↔ p <+: pRep n := by
  rw [RTree.mem_addrList_iff, flatG_realise, isAddr_pathTree]

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


variable {N : ℕ}

/-- A field with a child at every vertex survives. -/
lemma survives_of_one_le [NeZero N] {c : GWord N → ℕ}
    (h : ∀ v, 1 ≤ c v) : Survives c := by
  have hmem : ∀ n, List.replicate n (0 : Fin N) ∈ sample c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [List.replicate_succ', BranchingProcess.mem_sample_append_singleton]
        exact ⟨ih, by simpa using Nat.lt_of_lt_of_le Nat.zero_lt_one (h _)⟩
  exact Set.infinite_of_injective_forall_mem
    (fun a b h => by simpa using congrArg List.length h) hmem

/-- If there are no leaves anywhere, every actual child survives. -/
lemma skeletonDegree_eq_of_one_le [NeZero N] {c : GWord N → ℕ}
    (h1 : ∀ v, 1 ≤ c v) (hN : c [] ≤ N) : skeletonDegree c = c [] := by
  have hs : survivors c = childSet N (c []) := by
    ext i
    rw [BranchingProcess.mem_survivors, BranchingProcess.mem_childSet]
    exact ⟨fun h => h.1, fun hi => ⟨hi, survives_of_one_le (fun _ => h1 _)⟩⟩
  rw [skeletonDegree, hs, BranchingProcess.card_childSet hN]

/-- A shape of a leaf-free field consists of its neck alone. -/
lemma gShapeRoot_eq_flatG [NeZero N] {c : GWord N → ℕ}
    (h1 : ∀ v, 1 ≤ c v) (hN : ∀ v, c v ≤ N) :
    gShapeRoot c = flatG (gSplitDepth c) := by
  have hs := survives_of_one_le h1
  have hdec : ∀ i, gDecList (neckIter c i) = [] := by
    intro i
    apply List.eq_nil_of_length_eq_zero
    rw [length_gDecList, neckIter_eq_ambSub_neckPath hs]
    rw [skeletonDegree_eq_of_one_le (c := ambSub c (neckPath c i))
      (fun _ => h1 _) (by simpa [ambSub_apply] using hN _)]
    exact Nat.sub_self _
  change (⟨gSplitDepth c, fun i => gDecList (neckIter c (i : ℕ))⟩ : GShape) = _
  congr 1
  funext i
  exact hdec i

/-- The original reduced shape field is the bare-neck field in the chain regime. -/
theorem gShapeAt_eq_flatG [NeZero N] {c : GWord N → ℕ}
    (hc : IsGHairySample c) (h1 : ∀ v, 1 ≤ c v) {u : GWord N}
    (hu : u ∈ sample (gArityAt c)) :
    gShapeAt c u = flatG (neckAt c u) := by
  rw [gShapeAt, neckAt, (redSub_eq_ambSub_gEntryV' hc hu).1]
  exact gShapeRoot_eq_flatG (fun _ => h1 _) (fun _ => hc.offspring _)

end ChainClasses
