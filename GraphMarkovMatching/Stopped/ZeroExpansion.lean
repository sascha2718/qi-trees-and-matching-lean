/-
The unweighted stopped expansion of `markov_matching_new_proof.tex`
(`sec:unweighted`, `thm:explicit-zero-bound`).

* `zeroEv_succ_imp`: the dichotomy of an impossible comparison at a compatible source
  root: one source child has degree zero against every child type, or both source
  children have degree zero against some child type;
* `zeroMass_succ_le`: the expansion step, with the incompatible root contributing at most
  `δ` and the split contributing the product of the two union masses;
* `zeroMass_zero_le`: the height-zero terminal case;
* `zeroMass_le_of_stops`: the stopped expansion, `G_n(2) (δ + T² m²)` under `Stops`;
* `z_le_of_returns` (`thm:explicit-zero-bound`): the recurrence
  `z_h ≤ S_H δ + S_H T² (max_{j<h} z_j)²`;
* `z_le_fixed`: any `Z` with `S_H (δ + T² Z²) ≤ Z` bounds every `z_h`.
-/
import GraphMarkovMatching.Stopped.Moments

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

namespace Model

variable {V I : Type} (M : Model V I)

/-- **The dichotomy of an impossible comparison** (`sec:unweighted`): at a source root
compatible with `0`, degree zero against every type of `D` at height `h+1` forces, on the
child pair, degree zero of one child against every child type, or degree zero of both
children against some child type. -/
lemma zeroEv_succ_imp (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) {D : Set I}
    {h : ℕ} {s : I × V} (hs : s.2 ∈ M.Vmu) (hs0 : M.R s.2 M.zero)
    {p : FullLab (I × V) h × FullLab (I × V) h} (hz : M.ZeroEv D (h + 1) (branch s p)) :
    M.ZeroEv (M.children D) h p.1 ∨ M.ZeroEv (M.children D) h p.2
      ∨ (M.UnionEv (M.children D) h p.1 ∧ M.UnionEv (M.children D) h p.2) := by
  -- every charged transition of a type in `D` has both pairings blocked
  have key : ∀ t ∈ D, ∀ j : I × I, M.π t j ≠ 0 →
      (M.deg j.1 h p.1 = 0 ∨ M.deg j.2 h p.2 = 0)
        ∧ (M.deg j.1 h p.2 = 0 ∨ M.deg j.2 h p.1 = 0) := by
    intro t ht j hj
    have h1 : M.deg t (h + 1) (branch s p) = 0 := hz t ht
    rw [deg_succ, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (M.rootDeg_ne_zero hc hb0 t hs hs0)
    rw [childMix, rE_bind_eq_zero_iff] at h1
    rcases h1 j with h1 | h1
    · exact absurd h1 hj
    have h2 := (rE_square_eq_zero_iff (M.rho j.1 h) (M.rho j.2 h) (M.sim h) p.1 p.2).1 h1
    simp only [mul_eq_zero] at h2
    exact h2
  by_cases h1 : M.ZeroEv (M.children D) h p.1
  · exact Or.inl h1
  by_cases h2 : M.ZeroEv (M.children D) h p.2
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · -- a positive comparison of the second child forces a zero of the first child
    unfold ZeroEv at h2
    push Not at h2
    obtain ⟨t', ht', hne⟩ := h2
    obtain ⟨t, ht, j, hj, hj'⟩ := ht'
    obtain ⟨k1, k2⟩ := key t ht j hj
    rcases hj' with rfl | rfl
    · exact ⟨j.2, ⟨t, ht, j, hj, Or.inr rfl⟩, k2.resolve_left hne⟩
    · exact ⟨j.1, ⟨t, ht, j, hj, Or.inl rfl⟩, k1.resolve_right hne⟩
  · -- a positive comparison of the first child forces a zero of the second child
    unfold ZeroEv at h1
    push Not at h1
    obtain ⟨t', ht', hne⟩ := h1
    obtain ⟨t, ht, j, hj, hj'⟩ := ht'
    obtain ⟨k1, k2⟩ := key t ht j hj
    rcases hj' with rfl | rfl
    · exact ⟨j.2, ⟨t, ht, j, hj, Or.inr rfl⟩, k1.resolve_left hne⟩
    · exact ⟨j.1, ⟨t, ht, j, hj, Or.inl rfl⟩, k2.resolve_right hne⟩

/-- The split indicator of a source child pair against the child types `D'`
(`sec:unweighted`): one child in the zero event, or both children in the union event. -/
private noncomputable def splitInd (D' : Set I) (h : ℕ)
    (p : FullLab (I × V) h × FullLab (I × V) h) : ℝ≥0∞ :=
  (if M.ZeroEv D' h p.1 then 1 else 0) + (if M.ZeroEv D' h p.2 then 1 else 0)
    + (if M.UnionEv D' h p.1 then 1 else 0) * (if M.UnionEv D' h p.2 then 1 else 0)

/-- The split indicator integrates, against an independent child pair, to the two zero
masses plus the product of the two union masses. -/
private lemma tsum_prodPMF_splitInd (D' : Set I) (h : ℕ) (j : I × I) :
    ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * M.splitInd D' h p
      = M.zeroMass j.1 D' h + M.zeroMass j.2 D' h
          + M.unionMass j.1 D' h * M.unionMass j.2 D' h := by
  simp only [splitInd, prodPMF_apply, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add]
  have e1 : ∑' p : FullLab (I × V) h × FullLab (I × V) h,
      M.rho j.1 h p.1 * M.rho j.2 h p.2 * (if M.ZeroEv D' h p.1 then 1 else 0)
      = M.zeroMass j.1 D' h := by
    calc ∑' p : FullLab (I × V) h × FullLab (I × V) h,
          M.rho j.1 h p.1 * M.rho j.2 h p.2 * (if M.ZeroEv D' h p.1 then 1 else 0)
        = ∑' p : FullLab (I × V) h × FullLab (I × V) h,
          (M.rho j.1 h p.1 * (if M.ZeroEv D' h p.1 then 1 else 0)) * M.rho j.2 h p.2 :=
          tsum_congr fun p => by ring
      _ = (∑' x, M.rho j.1 h x * (if M.ZeroEv D' h x then 1 else 0)) * ∑' y, M.rho j.2 h y :=
          tsum_prod_split (fun x => M.rho j.1 h x * (if M.ZeroEv D' h x then 1 else 0))
            (fun y => M.rho j.2 h y)
      _ = M.zeroMass j.1 D' h := by rw [PMF.tsum_coe, mul_one]; rfl
  have e2 : ∑' p : FullLab (I × V) h × FullLab (I × V) h,
      M.rho j.1 h p.1 * M.rho j.2 h p.2 * (if M.ZeroEv D' h p.2 then 1 else 0)
      = M.zeroMass j.2 D' h := by
    calc ∑' p : FullLab (I × V) h × FullLab (I × V) h,
          M.rho j.1 h p.1 * M.rho j.2 h p.2 * (if M.ZeroEv D' h p.2 then 1 else 0)
        = ∑' p : FullLab (I × V) h × FullLab (I × V) h,
          M.rho j.1 h p.1 * (M.rho j.2 h p.2 * (if M.ZeroEv D' h p.2 then 1 else 0)) :=
          tsum_congr fun p => by ring
      _ = (∑' x, M.rho j.1 h x) * ∑' y, M.rho j.2 h y * (if M.ZeroEv D' h y then 1 else 0) :=
          tsum_prod_split (fun x => M.rho j.1 h x)
            (fun y => M.rho j.2 h y * (if M.ZeroEv D' h y then 1 else 0))
      _ = M.zeroMass j.2 D' h := by rw [PMF.tsum_coe, one_mul]; rfl
  have e3 : ∑' p : FullLab (I × V) h × FullLab (I × V) h,
      M.rho j.1 h p.1 * M.rho j.2 h p.2
        * ((if M.UnionEv D' h p.1 then 1 else 0) * (if M.UnionEv D' h p.2 then 1 else 0))
      = M.unionMass j.1 D' h * M.unionMass j.2 D' h := by
    calc ∑' p : FullLab (I × V) h × FullLab (I × V) h,
          M.rho j.1 h p.1 * M.rho j.2 h p.2
            * ((if M.UnionEv D' h p.1 then 1 else 0) * (if M.UnionEv D' h p.2 then 1 else 0))
        = ∑' p : FullLab (I × V) h × FullLab (I × V) h,
          (M.rho j.1 h p.1 * (if M.UnionEv D' h p.1 then 1 else 0))
            * (M.rho j.2 h p.2 * (if M.UnionEv D' h p.2 then 1 else 0)) :=
          tsum_congr fun p => by ring
      _ = (∑' x, M.rho j.1 h x * (if M.UnionEv D' h x then 1 else 0))
            * ∑' y, M.rho j.2 h y * (if M.UnionEv D' h y then 1 else 0) :=
          tsum_prod_split (fun x => M.rho j.1 h x * (if M.UnionEv D' h x then 1 else 0))
            (fun y => M.rho j.2 h y * (if M.UnionEv D' h y then 1 else 0))
      _ = M.unionMass j.1 D' h * M.unionMass j.2 D' h := rfl
  rw [e1, e2, e3]

/-- **The expansion step**: the zero mass at height `h+1` is at most `δ` plus, averaged
over the source transition, the two continuing zero masses and the product of the two
union masses of the children. -/
lemma zeroMass_succ_le (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) (s : I) (D : Set I)
    (h : ℕ) :
    M.zeroMass s D (h + 1)
      ≤ M.delta + ∑' j, M.π s j * (M.zeroMass j.1 (M.children D) h
          + M.zeroMass j.2 (M.children D) h
          + M.unionMass j.1 (M.children D) h * M.unionMass j.2 (M.children D) h) := by
  -- the incompatible-root indicator
  set c : V → ℝ≥0∞ := fun v => if M.R v M.zero then 0 else 1 with hcdef
  -- the integrated split indicator
  set A : ℝ≥0∞ := ∑' p, M.childMix s h p * M.splitInd (M.children D) h p with hA
  -- the pointwise bound on the indicator of the zero event at a charged root state
  have hpt : ∀ (v : V), M.rootLaw s v ≠ 0 → ∀ p,
      (if M.ZeroEv D (h + 1) (branch (s, v) p) then 1 else 0)
        ≤ c v + M.splitInd (M.children D) h p := by
    intro v hv p
    by_cases hz : M.ZeroEv D (h + 1) (branch (s, v) p)
    · rw [if_pos hz]
      by_cases hv0 : M.R v M.zero
      · have hmem : v ∈ M.Vmu := M.rootLaw_mem_Vmu hv
        refine le_add_left ?_
        rcases M.zeroEv_succ_imp hc hb0 (s := (s, v)) hmem hv0 hz with h1 | h2 | ⟨h3, h4⟩
        · simp only [splitInd, if_pos h1]
          exact le_add_right le_self_add
        · simp only [splitInd, if_pos h2]
          exact le_add_right le_add_self
        · simp only [splitInd, if_pos h3, if_pos h4, mul_one]
          exact le_add_self
      · simp only [hcdef, if_neg hv0]
        exact le_self_add
    · rw [if_neg hz]
      exact zero_le
  calc M.zeroMass s D (h + 1)
      = ∑' v, M.rootLaw s v * ∑' p, M.childMix s h p
          * (if M.ZeroEv D (h + 1) (branch (s, v) p) then 1 else 0) := by
        rw [zeroMass, rho_succ, tsum_bind_mul, rootT, tsum_map_mul]
        exact tsum_congr fun v => by rw [tsum_map_mul]
    _ ≤ ∑' v, M.rootLaw s v
          * ∑' p, M.childMix s h p * (c v + M.splitInd (M.children D) h p) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : M.rootLaw s v = 0
        · simp [hv]
        exact mul_le_mul_right (ENNReal.tsum_le_tsum fun p => mul_le_mul_right (hpt v hv p) _) _
    _ = ∑' v, M.rootLaw s v * (c v + A) := by
        refine tsum_congr fun v => ?_
        congr 1
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = (∑' v, M.rootLaw s v * c v) + A := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ M.delta + A := add_le_add_left (M.rootLaw_incompatible_le hc s) _
    _ = M.delta + ∑' j, M.π s j * (M.zeroMass j.1 (M.children D) h
          + M.zeroMass j.2 (M.children D) h
          + M.unionMass j.1 (M.children D) h * M.unionMass j.2 (M.children D) h) := by
        congr 1
        rw [hA, childMix, tsum_bind_mul]
        exact tsum_congr fun j => by rw [tsum_prodPMF_splitInd]

/-- **The height-zero terminal case**: against a nonempty `D`, the zero mass at height zero
is at most `δ`. -/
lemma zeroMass_zero_le (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) (s : I) {D : Set I}
    (hD : D.Nonempty) : M.zeroMass s D 0 ≤ M.delta := by
  calc M.zeroMass s D 0
      = ∑' v, M.rootLaw s v * (if M.ZeroEv D 0 (leaf (s, v)) then 1 else 0) := by
        rw [zeroMass, rho_zero, tsum_map_mul, rootT, tsum_map_mul]
    _ ≤ ∑' v, M.rootLaw s v * (if M.R v M.zero then 0 else 1) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : M.rootLaw s v = 0
        · simp [hv]
        refine mul_le_mul_right ?_ _
        by_cases hz : M.ZeroEv D 0 (leaf (s, v))
        · have hmem : v ∈ M.Vmu := M.rootLaw_mem_Vmu hv
          have hv0 := M.zeroEv_zero_imp hc hb0 hD (s := (s, v)) hmem hz
          rw [if_pos hz, if_neg hv0]
        · rw [if_neg hz]
          exact zero_le
    _ ≤ M.delta := M.rootLaw_incompatible_le hc s

/-- The zero mass against a singleton at height zero is at most `δ`. -/
lemma z_zero_le (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) (s t : I) :
    M.z s t 0 ≤ M.delta := by
  rw [← M.zeroMass_singleton]
  exact M.zeroMass_zero_le hc hb0 s (Set.singleton_nonempty t)

/-- **The stopped expansion**: with all equal-phase zero masses at heights below `h` at
most `m`, every stopping source–target pair of equal phase has zero mass at most
`G_n(2) (δ + T² m²)`. -/
theorem zeroMass_le_of_stops [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    (hFP : M.FreshPositive) {g : ℕ} (Θ : Phase M g) {T : ℕ} (hT : ∀ i, Θ.count i ≤ T)
    {h : ℕ} {m : ℝ≥0∞} (hm : ∀ j < h, ∀ s t, Θ.θ s = Θ.θ t → M.z s t j ≤ m) :
    ∀ (n : ℕ) (s : I) (D : Set I), D.Nonempty → (∀ t ∈ D, Θ.θ t = Θ.θ s) →
      M.Stops s D n → M.zeroMass s D h ≤ SHe n * (M.delta + (T : ℝ≥0∞) ^ 2 * m ^ 2) := by
  intro n
  induction n generalizing h with
  | zero =>
    intro s D _ _ hst
    obtain ⟨hs, f, hfD, hf⟩ := hst.zero
    rw [M.zeroMass_eq_zero_of_fresh hFP hs hf hfD h]
    exact zero_le
  | succ n ih =>
    intro s D hD hθ hst
    set X := M.delta + (T : ℝ≥0∞) ^ 2 * m ^ 2 with hX
    by_cases h0 : M.fresh s ∧ ∃ f ∈ D, M.fresh f
    · obtain ⟨hs, f, hfD, hf⟩ := h0
      rw [M.zeroMass_eq_zero_of_fresh hFP hs hf hfD h]
      exact zero_le
    cases h with
    | zero =>
      calc M.zeroMass s D 0 ≤ M.delta := M.zeroMass_zero_le hc hb0 s hD
        _ ≤ X := le_self_add
        _ ≤ SHe (n + 1) * X := le_mul_of_one_le_left zero_le (one_le_SHe _)
    | succ h' =>
      have hm' : ∀ j < h', ∀ s t, Θ.θ s = Θ.θ t → M.z s t j ≤ m :=
        fun j hj => hm j (Nat.lt_succ_of_lt hj)
      have hD' : (M.children D).Nonempty := M.children_nonempty hD
      have hcls : M.children D ⊆ ↑(Θ.cls (Θ.θ s + 1)) := Θ.children_subset_cls hθ
      have hcard : (Θ.cls (Θ.θ s + 1)).card ≤ T := by
        rw [Phase.card_cls]
        exact hT _
      -- a continuing child stops one step earlier against the child types
      have hcont : ∀ t', M.child s t' → M.zeroMass t' (M.children D) h' ≤ SHe n * X := by
        intro t' ht'
        refine ih hm' t' (M.children D) hD' ?_ (hst.succ h0 ht')
        intro t ht
        obtain ⟨t₀, ht₀, hch⟩ := ht
        rw [Θ.child_eq hch, Θ.child_eq ht', hθ t₀ ht₀]
      -- a split child carries a union over the successor phase class
      have hsplit : ∀ t', M.child s t' →
          M.unionMass t' (M.children D) h' ≤ (T : ℝ≥0∞) * m := by
        intro t' ht'
        calc M.unionMass t' (M.children D) h'
            ≤ M.unionMass t' (↑(Θ.cls (Θ.θ s + 1))) h' := M.unionMass_mono hcls h'
          _ ≤ (Θ.cls (Θ.θ s + 1)).card * m := by
              refine M.unionMass_le_card_mul t' _ h' fun t ht => ?_
              simp only [Phase.cls, Finset.mem_filter, Finset.mem_univ, true_and] at ht
              exact hm h' (Nat.lt_succ_self h') t' t (by rw [Θ.child_eq ht', ht])
          _ ≤ (T : ℝ≥0∞) * m := mul_le_mul_left (by exact_mod_cast hcard) _
      -- the bound on each summand of the expansion
      have hsum : ∀ j : I × I, M.π s j * (M.zeroMass j.1 (M.children D) h'
          + M.zeroMass j.2 (M.children D) h'
          + M.unionMass j.1 (M.children D) h' * M.unionMass j.2 (M.children D) h')
          ≤ M.π s j * (2 * (SHe n * X) + (T : ℝ≥0∞) ^ 2 * m ^ 2) := by
        intro j
        by_cases hj : M.π s j = 0
        · simp [hj]
        refine mul_le_mul_right ?_ _
        have h1 : M.child s j.1 := ⟨j, hj, Or.inl rfl⟩
        have h2 : M.child s j.2 := ⟨j, hj, Or.inr rfl⟩
        calc M.zeroMass j.1 (M.children D) h' + M.zeroMass j.2 (M.children D) h'
              + M.unionMass j.1 (M.children D) h' * M.unionMass j.2 (M.children D) h'
            ≤ SHe n * X + SHe n * X + (T : ℝ≥0∞) * m * ((T : ℝ≥0∞) * m) :=
              add_le_add (add_le_add (hcont _ h1) (hcont _ h2))
                (mul_le_mul' (hsplit _ h1) (hsplit _ h2))
          _ = 2 * (SHe n * X) + (T : ℝ≥0∞) ^ 2 * m ^ 2 := by ring
      calc M.zeroMass s D (h' + 1)
          ≤ M.delta + ∑' j, M.π s j * (M.zeroMass j.1 (M.children D) h'
              + M.zeroMass j.2 (M.children D) h'
              + M.unionMass j.1 (M.children D) h' * M.unionMass j.2 (M.children D) h') :=
            M.zeroMass_succ_le hc hb0 s D h'
        _ ≤ M.delta + ∑' j, M.π s j * (2 * (SHe n * X) + (T : ℝ≥0∞) ^ 2 * m ^ 2) :=
            add_le_add_right (ENNReal.tsum_le_tsum hsum) _
        _ = M.delta + (2 * (SHe n * X) + (T : ℝ≥0∞) ^ 2 * m ^ 2) := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        _ = SHe (n + 1) * X := by
            rw [SHe_succ, hX]; ring

/-- **`thm:explicit-zero-bound`**: under common returns within `H`,
`z_h ≤ S_H δ + S_H T² (max_{j<h} z_j)²` for every equal-phase pair. -/
theorem z_le_of_returns [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    (hFP : M.FreshPositive) {g : ℕ} (Θ : Phase M g) {T : ℕ} (hT : ∀ i, Θ.count i ≤ T)
    {H : ℕ} (hCR : M.CommonReturns Θ H) {h : ℕ} {m : ℝ≥0∞}
    (hm : ∀ j < h, ∀ s t, Θ.θ s = Θ.θ t → M.z s t j ≤ m) :
    ∀ s t, Θ.θ s = Θ.θ t →
      M.z s t h ≤ SHe H * (M.delta + (T : ℝ≥0∞) ^ 2 * m ^ 2) := by
  intro s t hst
  rw [← M.zeroMass_singleton]
  refine M.zeroMass_le_of_stops hc hb0 hFP Θ hT hm H s {t} (Set.singleton_nonempty t) ?_
    (hCR s t hst)
  intro t' ht'
  rw [Set.mem_singleton_iff.1 ht', hst]

/-- **The uniform zero bound**: any `Z` with `S_H (δ + T² Z²) ≤ Z` bounds every
equal-phase zero mass at every height. -/
theorem z_le_fixed [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    (hFP : M.FreshPositive) {g : ℕ} (Θ : Phase M g) {T : ℕ} (hT : ∀ i, Θ.count i ≤ T)
    {H : ℕ} (hCR : M.CommonReturns Θ H) {Z : ℝ≥0∞}
    (hZ : SHe H * (M.delta + (T : ℝ≥0∞) ^ 2 * Z ^ 2) ≤ Z) :
    ∀ h s t, Θ.θ s = Θ.θ t → M.z s t h ≤ Z := by
  intro h
  refine Nat.strong_induction_on h ?_
  intro h ih s t hst
  exact (M.z_le_of_returns hc hb0 hFP Θ hT hCR (fun j hj => ih j hj) s t hst).trans hZ

end Model

end GraphMarkovMatching.Stopped
