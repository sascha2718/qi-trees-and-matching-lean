import ChainClasses.Chain.GWInstance
import ChainClasses.Chain.Transfer
import Mathlib.Probability.BorelCantelli

/-!
`thm:bottleneck` and the binary-tree half of `thm:converse` of `prelims.tex`:
long chains force balls that are too small, so a chain-regime sample is almost
surely not quasi-isometric to the binary tree.

* `wordsOf`, `card_wordsOf`: the `2^n` words of length `n`.
* `treeDist_append_left`: the invariance of the ambient metric of `𝒩` inside a
  cone.
* `HasThinBalls`: the hypothesis of `thm:bottleneck` in cardinality form, that
  at every radius `ℓ` some ball is covered by `2ℓ+1` vertices, as it is when the
  ball is a segment of `ℤ`.
* `not_isQIWith_binary_of_thinBalls`: `thm:bottleneck`. The count runs on the
  sphere of radius `R` around the image of the thin centre: coarse density picks
  a preimage for each of its `2^R` vertices, the lower quasi-isometry bound
  confines those preimages to the thin ball, and two vertices of the sphere
  sharing a preimage agree off their last `K` letters, so a fibre has at most
  `2^K` elements.
* `assoc_ball_subset_chain`, `hasThinBalls_assoc`: the ball of radius `ℓ` at
  level `ℓ` of a chain of length at least `2ℓ+1` stays on that chain, so a
  labelling with chains of every length has thin balls.
* `chainMeasure_labels_unbounded`: the labels are almost surely unbounded, by
  the second Borel-Cantelli lemma along the leftmost ray.
* `converse_binary_ae`: the binary-tree half of `thm:converse`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory

/-! ### The words of a given length -/

/-- The words of length `n`. -/
def wordsOf : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 => ((Finset.univ : Finset Bool) ×ˢ wordsOf n).image fun p ↦ p.1 :: p.2

/-- Consing is injective on pairs. -/
lemma cons_injective : Function.Injective fun p : Bool × Word ↦ p.1 :: p.2 := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [List.cons.injEq] at h
  simp [h.1, h.2]

@[simp] lemma mem_wordsOf {n : ℕ} {u : Word} : u ∈ wordsOf n ↔ u.length = n := by
  induction n generalizing u with
  | zero =>
      show u ∈ ({[]} : Finset Word) ↔ _
      simp
  | succ n ih =>
      show u ∈ ((Finset.univ : Finset Bool) ×ˢ wordsOf n).image (fun p ↦ p.1 :: p.2) ↔ _
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨b, x⟩, hx, rfl⟩
        simp [ih.mp hx]
      · intro h
        match u with
        | [] => simp at h
        | b :: x =>
            exact ⟨(b, x), ih.mpr (by simpa using h), rfl⟩

/-- There are `2^n` words of length `n`. -/
lemma card_wordsOf (n : ℕ) : (wordsOf n).card = 2 ^ n := by
  induction n with
  | zero => show ({[]} : Finset Word).card = _; simp
  | succ n ih =>
      show (((Finset.univ : Finset Bool) ×ˢ wordsOf n).image
        (fun p ↦ p.1 :: p.2)).card = _
      rw [Finset.card_image_of_injective _ cons_injective, Finset.card_product, ih,
        Finset.card_univ, Fintype.card_bool, pow_succ]
      ring

/-! ### The ambient metric -/

/-- The wedge inside a cone: a common prefix factors out. -/
lemma wedge_append (a x y : Word) : wedge (a ++ x) (a ++ y) = a ++ wedge x y := by
  induction a with
  | nil => simp
  | cons c a ih => simp [wedge_cons_cons, ih]

/-- The metric of `𝒩` is invariant inside a cone. -/
lemma treeDist_append_left (a x y : Word) : treeDist (a ++ x) (a ++ y) = treeDist x y := by
  have h1 := wedge_length_le_left x y
  have h2 := wedge_length_le_right x y
  simp only [treeDist, wedge_append, List.length_append]
  omega

/-! ### `thm:bottleneck` -/

/-- Enlarging the constant weakens the quasi-isometry bounds. -/
lemma IsQIWith.mono {K K' : ℕ} (h : K ≤ K') {T T' : Word → Prop} {f : Word → Word}
    (hf : IsQIWith K T T' f) : IsQIWith K' T T' f where
  maps := hf.maps
  upper x y hx hy :=
    le_trans (hf.upper x y hx hy)
      (Nat.add_le_add (Nat.mul_le_mul_right _ h) h)
  lower x y hx hy :=
    le_trans (hf.lower x y hx hy)
      (Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.mul_le_mul h h))
  dense y' hy' := by
    obtain ⟨x, hx, hd⟩ := hf.dense y' hy'
    exact ⟨x, hx, le_trans hd h⟩

/-- The hypothesis of `thm:bottleneck`: at every radius `ℓ` the tree `T` has a
vertex whose ball of radius `ℓ` is covered by `2ℓ+1` vertices. A ball isometric
to a segment of `ℤ` has this form. -/
def HasThinBalls (T : Word → Prop) : Prop :=
  ∀ ℓ : ℕ, ∃ v : Word, T v ∧ ∃ S : Finset Word,
    S.card ≤ 2 * ℓ + 1 ∧ ∀ x, T x → treeDist x v ≤ ℓ → x ∈ S

/-- Exponential growth beats a linear bound: `2^R` outgrows `a·R + b` at some
radius. -/
lemma exists_two_pow_gt (a b : ℕ) : ∃ R : ℕ, a * R + b < 2 ^ R := by
  refine ⟨2 * (a + b) + 2, ?_⟩
  have h : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
  have h' : a + b + 1 ≤ 2 ^ (a + b) := h
  have hx : (a + b + 1) * (a + b + 1) ≤ 2 ^ (a + b) * 2 ^ (a + b) := Nat.mul_le_mul h' h'
  have hpow : 2 ^ (2 * (a + b) + 2) = 2 ^ (a + b) * 2 ^ (a + b) * 4 := by
    rw [show 2 * (a + b) + 2 = a + b + (a + b + 2) by ring, pow_add, pow_add]
    ring
  rw [hpow]
  nlinarith [hx, Nat.zero_le a, Nat.zero_le b]

/-- **`thm:bottleneck`**: a tree with a thin ball at every radius is not
quasi-isometric to the binary tree. -/
theorem not_isQIWith_binary_of_thinBalls {T : Word → Prop} (hT : HasThinBalls T)
    (K₀ : ℕ) (f : Word → Word) : ¬ IsQIWith K₀ T (fun _ ↦ True) f := by
  intro hqi₀
  obtain ⟨K, -, hqi⟩ : ∃ K, 1 ≤ K ∧ IsQIWith K T (fun _ ↦ True) f :=
    ⟨K₀ + 1, Nat.le_add_left 1 K₀, hqi₀.mono (Nat.le_succ K₀)⟩
  obtain ⟨R', hR'⟩ := exists_two_pow_gt (2 * K) (6 * K * K + 1)
  set R := K + R' with hR
  set ℓ := K * R + 2 * K * K with hℓ
  obtain ⟨v, hv, S, hScard, hSmem⟩ := hT ℓ
  have hdense : ∀ u : Word, ∃ x, T x ∧ treeDist (f x) (f v ++ u) ≤ K :=
    fun u ↦ hqi.dense _ trivial
  choose g hg1 hg2 using hdense
  have hdv : ∀ u : Word, treeDist (f v ++ u) (f v) = u.length := by
    intro u
    rw [treeDist_comm, treeDist_of_prefix (List.prefix_append (f v) u)]
    simp
  have hgS : ∀ u : Word, u.length = R → g u ∈ S := by
    intro u hu
    refine hSmem _ (hg1 u) ?_
    have h1 : treeDist (f (g u)) (f v) ≤ K + R := by
      have h := treeDist_triangle (f (g u)) (f v ++ u) (f v)
      have h2 := hg2 u
      rw [hdv u, hu] at h
      omega
    calc treeDist (g u) v ≤ K * treeDist (f (g u)) (f v) + K * K :=
          hqi.lower (g u) v (hg1 u) hv
      _ ≤ K * (K + R) + K * K := Nat.add_le_add_right (Nat.mul_le_mul_left K h1) _
      _ = K * R + 2 * K * K := by ring
      _ = ℓ := hℓ.symm
  have hcount : (wordsOf R).card ≤ (S ×ˢ wordsOf K).card := by
    refine Finset.card_le_card_of_injOn (fun u ↦ (g u, u.drop R')) ?_ ?_
    · intro u hu
      rw [Finset.mem_coe, mem_wordsOf] at hu
      refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hgS u hu, ?_⟩)
      rw [mem_wordsOf, List.length_drop, hu]
      omega
    · intro u hu u' hu' heq
      rw [Finset.mem_coe, mem_wordsOf] at hu hu'
      have hgg : g u = g u' := congrArg Prod.fst heq
      have hdrop : u.drop R' = u'.drop R' := congrArg Prod.snd heq
      have h1 : treeDist (f v ++ u) (f (g u')) ≤ K := by
        rw [treeDist_comm, ← hgg]
        exact hg2 u
      have h2 : treeDist (f (g u')) (f v ++ u') ≤ K := hg2 u'
      have h3 := treeDist_triangle (f v ++ u) (f (g u')) (f v ++ u')
      rw [treeDist_append_left] at h3
      have hadd := treeDist_add_wedge_length u u'
      rw [hu, hu'] at hadd
      have hge : R' ≤ (wedge u u').length := by omega
      have hqu : (wedge u u').take R' <+: u :=
        (List.take_prefix R' _).trans (wedge_prefix_left u u')
      have hqu' : (wedge u u').take R' <+: u' :=
        (List.take_prefix R' _).trans (wedge_prefix_right u u')
      have hql : ((wedge u u').take R').length = R' := by
        rw [List.length_take]; omega
      have e1 : (wedge u u').take R' = u.take R' := by
        have h := List.prefix_iff_eq_take.mp hqu
        rwa [hql] at h
      have e2 : (wedge u u').take R' = u'.take R' := by
        have h := List.prefix_iff_eq_take.mp hqu'
        rwa [hql] at h
      have hu1 : u = (wedge u u').take R' ++ u.drop R' := by
        rw [e1]; exact (List.take_append_drop R' u).symm
      have hu2 : u' = (wedge u u').take R' ++ u'.drop R' := by
        rw [e2]; exact (List.take_append_drop R' u').symm
      calc u = (wedge u u').take R' ++ u.drop R' := hu1
        _ = (wedge u u').take R' ++ u'.drop R' := by rw [hdrop]
        _ = u' := hu2.symm
  have hfin : 2 ^ R ≤ (2 * ℓ + 1) * 2 ^ K :=
    calc 2 ^ R = (wordsOf R).card := (card_wordsOf R).symm
      _ ≤ (S ×ˢ wordsOf K).card := hcount
      _ = S.card * 2 ^ K := by rw [Finset.card_product, card_wordsOf]
      _ ≤ (2 * ℓ + 1) * 2 ^ K := Nat.mul_le_mul_right _ hScard
  have hnum : (2 * ℓ + 1) * 2 ^ K < 2 ^ R := by
    have hp : 0 < 2 ^ K := pow_pos (by norm_num) K
    have he : 2 * ℓ + 1 = 2 * K * R' + (6 * K * K + 1) := by rw [hℓ, hR]; ring
    calc (2 * ℓ + 1) * 2 ^ K = (2 * K * R' + (6 * K * K + 1)) * 2 ^ K := by rw [he]
      _ < 2 ^ R' * 2 ^ K := mul_lt_mul_of_pos_right hR' hp
      _ = 2 ^ R := by rw [← pow_add]; congr 1; omega
  exact absurd hfin (Nat.not_le.mpr hnum)

/-! ### Thin balls in the middle of a long chain -/

/-- The address of a chain start grows by at least the full label across a strict extension. -/
lemma iotaL_length_lt {lam : Word → ℕ} (hlam : ∀ u, 1 ≤ lam u) {u u' : Word}
    (hpre : u <+: u') (hne : u ≠ u') :
    (iotaL lam u).length + lam u ≤ (iotaL lam u').length := by
  obtain ⟨s, rfl⟩ := hpre
  match s with
  | [] => exact absurd (by simp) hne
  | c :: s =>
      have h1 : iotaL lam (u ++ [c]) <+: iotaL lam (u ++ c :: s) :=
        iotaL_prefix lam ⟨s, by simp⟩
      have h2 := iotaL_concat_length lam (hlam u) c
      have h3 := h1.length_le
      omega

/-- The ball of radius `ℓ` around the level-`ℓ` vertex of a chain of length at
least `2ℓ+1` stays on that chain: every vertex of the associated tree within `ℓ`
of it is one of the first `2ℓ+1` vertices of the chain. -/
lemma assoc_ball_subset_chain {lam : Word → ℕ} (hlam : ∀ u, 1 ≤ lam u) {w : Word} {ℓ : ℕ}
    (hw : 2 * ℓ + 1 ≤ lam w) {x : Word} (hx : InAssoc lam x)
    (hd : treeDist x (iotaL lam w ++ List.replicate ℓ false) ≤ ℓ) :
    ∃ j ≤ 2 * ℓ, x = iotaL lam w ++ List.replicate j false := by
  obtain ⟨w', j, hj, rfl⟩ := hx
  have hℓw : ℓ ≤ lam w - 1 := by have := hlam w; omega
  by_cases hww : w' = w
  · subst hww
    rw [treeDist_replicate] at hd
    exact ⟨j, by omega, rfl⟩
  refine absurd hd (Nat.not_le.mpr ?_)
  by_cases hp1 : w <+: w'
  · have hne : w ≠ w' := fun h ↦ hww h.symm
    have hpre := assoc_prefix lam hp1 hne hℓw j
    rw [treeDist_comm, treeDist_of_prefix hpre]
    simp only [List.length_append, List.length_replicate]
    have := iotaL_length_lt hlam hp1 hne
    omega
  by_cases hp2 : w' <+: w
  · have hpre := assoc_prefix lam hp2 hww hj ℓ
    rw [treeDist_of_prefix hpre]
    simp only [List.length_append, List.length_replicate]
    have := iotaL_length_lt hlam hp2 hww
    have := hlam w'
    omega
  · obtain ⟨p, a, b, hab, hpa, hpb⟩ := exists_diverge hp1 hp2
    have hwedge := assoc_wedge_diverge lam hab hpa hpb ℓ j
    have htd := treeDist_add_wedge_length (iotaL lam w ++ List.replicate ℓ false)
      (iotaL lam w' ++ List.replicate j false)
    have hwr := wedge_length_le_right (iotaL lam w ++ List.replicate ℓ false)
      (iotaL lam w' ++ List.replicate j false)
    rw [hwedge] at htd hwr
    have hle : (iotaL lam (p ++ [a])).length ≤ (iotaL lam w).length :=
      (iotaL_prefix lam hpa).length_le
    have hcl : (iotaL lam (p ++ [a])).length = (iotaL lam p).length + lam p :=
      iotaL_concat_length lam (hlam p) a
    simp only [List.length_append, List.length_replicate] at htd hwr
    have hp1' := hlam p
    rw [treeDist_comm]
    omega

/-- A labelling with chains of every length has thin balls: the ball of radius
`ℓ` at level `ℓ` of a chain of length at least `2ℓ+1` is covered by the first
`2ℓ+1` vertices of that chain. -/
theorem hasThinBalls_assoc {lam : Word → ℕ} (hlam : ∀ u, 1 ≤ lam u)
    (hlong : ∀ n : ℕ, ∃ w : Word, n ≤ lam w) : HasThinBalls (InAssoc lam) := by
  intro ℓ
  obtain ⟨w, hw⟩ := hlong (2 * ℓ + 1)
  refine ⟨iotaL lam w ++ List.replicate ℓ false, ⟨w, ℓ, by omega, rfl⟩,
    (Finset.range (2 * ℓ + 1)).image (fun j ↦ iotaL lam w ++ List.replicate j false),
    le_trans Finset.card_image_le (by simp), ?_⟩
  intro x hx hdx
  obtain ⟨j, hj, rfl⟩ := assoc_ball_subset_chain hlam hw hx hdx
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

/-! ### Chains of unbounded length -/

/-- The label events along the leftmost ray are independent. -/
lemma chainMeasure_ray_iIndepSet {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (n : ℕ) :
    iIndepSet (fun k : ℕ ↦ {χ : Word → Bool | labAux χ (List.replicate k false) = n})
      (chainMeasure ht ht1) := by
  have hmeas : ∀ k : ℕ,
      MeasurableSet {χ : Word → Bool | labAux χ (List.replicate k false) = n} := fun k ↦
    measurableSet_labAux (fun v : Word ↦ (BranchingProcess.coord v : (Word → Bool) → Bool))
      measurable_chainMeasure_coord _ n
  rw [iIndepSet_iff_meas_biInter hmeas]
  intro s
  have hinj : ∀ k ∈ s, ∀ k' ∈ s,
      (List.replicate k false : Word) = List.replicate k' false → k = k' := by
    intro k _ k' _ h
    simpa using congrArg List.length h
  have hprod := (chainMeasure_label_iIndepFun ht ht1).measure_inter_preimage_eq_mul
    (s.image fun k : ℕ ↦ (List.replicate k false : Word))
    (sets := fun _ ↦ {n}) (fun _ _ ↦ measurableSet_singleton n)
  have hset : (⋂ w ∈ s.image (fun k : ℕ ↦ (List.replicate k false : Word)),
        (fun ω : Word → Bool ↦ labAux ω w) ⁻¹' {n})
      = ⋂ k ∈ s, {χ : Word → Bool | labAux χ (List.replicate k false) = n} := by
    ext χ
    simp only [Set.mem_iInter, Finset.mem_image, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    constructor
    · intro h k hk
      exact h _ ⟨k, hk, rfl⟩
    · rintro h w ⟨k, hk, rfl⟩
      exact h k hk
  have hpr : (∏ w ∈ s.image (fun k : ℕ ↦ (List.replicate k false : Word)),
        chainMeasure ht ht1 ((fun ω : Word → Bool ↦ labAux ω w) ⁻¹' {n}))
      = ∏ k ∈ s,
        chainMeasure ht ht1 {χ : Word → Bool | labAux χ (List.replicate k false) = n} :=
    Finset.prod_image hinj
  rw [← hset, ← hpr]
  exact hprod

/-- **Chains of unbounded length**: almost surely, for every `n` some vertex
carries a label at least `n`. The labels along the leftmost ray are independent
with a common positive chance of equalling `n`, so the second Borel-Cantelli
lemma places infinitely many of them at `n`. -/
theorem chainMeasure_labels_unbounded {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂(chainMeasure ht ht1.le), ∀ n : ℕ, ∃ w : Word, n ≤ labAux ω w := by
  refine ae_all_iff.mpr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Filter.Eventually.of_forall fun _ ↦ ⟨[], Nat.zero_le _⟩
  have hmeas : ∀ k : ℕ,
      MeasurableSet {χ : Word → Bool | labAux χ (List.replicate k false) = n} := fun k ↦
    measurableSet_labAux (fun v : Word ↦ (BranchingProcess.coord v : (Word → Bool) → Bool))
      measurable_chainMeasure_coord _ n
  have hval : ∀ k : ℕ,
      chainMeasure ht ht1.le {χ : Word → Bool | labAux χ (List.replicate k false) = n}
        = ENNReal.ofReal ((1 - t) ^ (n - 1) * t) :=
    fun k ↦ chainMeasure_label_marginal ht ht1.le _ hn
  have hpos : ENNReal.ofReal ((1 - t) ^ (n - 1) * t) ≠ 0 := by
    have h1t : 0 < 1 - t := by linarith
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos (pow_pos h1t _) ht
  have hsum : (∑' k : ℕ,
      chainMeasure ht ht1.le {χ : Word → Bool | labAux χ (List.replicate k false) = n}) = ⊤ := by
    simp only [hval]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hpos
  have hlim := measure_limsup_eq_one hmeas (chainMeasure_ray_iIndepSet ht ht1.le n) hsum
  have hcompl : chainMeasure ht ht1.le
      (Filter.limsup (fun k : ℕ ↦ {χ : Word → Bool | labAux χ (List.replicate k false) = n})
        Filter.atTop)ᶜ = 0 := by
    rw [measure_compl (MeasurableSet.measurableSet_limsup hmeas) (measure_ne_top _ _), hlim,
      measure_univ, tsub_self]
  rw [ae_iff]
  refine measure_mono_null (fun ω hω ↦ ?_) hcompl
  refine Set.mem_compl fun hmem ↦ hω ?_
  obtain ⟨k, hk⟩ := (Filter.mem_limsup_iff_frequently_mem.mp hmem).exists
  exact ⟨List.replicate k false, le_of_eq (hk : labAux ω (List.replicate k false) = n).symm⟩

/-! ### `thm:converse` against the binary tree -/

/-- **The binary-tree half of `thm:converse`**: almost surely the tree of the
chain-regime sample admits no quasi-isometry onto the binary tree. -/
theorem converse_binary_ae {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂(chainMeasure ht ht1.le),
      ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K (InAssoc (labAux ω)) (fun _ ↦ True) f := by
  have hchains : ∀ᵐ ω ∂(chainMeasure ht ht1.le), Chains ω := by
    rw [ae_iff]
    exact not_chains_null (chainMeasure ht ht1.le)
      (fun v : Word ↦ (BranchingProcess.coord v : (Word → Bool) → Bool)) t
      measurable_chainMeasure_coord (chainMeasure_iIndepFun ht ht1.le)
      (chainMeasure_coord_true ht ht1.le) ht
  filter_upwards [hchains, chainMeasure_labels_unbounded ht ht1] with ω hω hlong
  rintro ⟨K, f, hf⟩
  exact not_isQIWith_binary_of_thinBalls
    (hasThinBalls_assoc (one_le_labAux hω) hlong) K f hf

end ChainClasses
