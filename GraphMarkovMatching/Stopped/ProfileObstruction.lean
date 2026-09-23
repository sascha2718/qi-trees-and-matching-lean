/-
The obstruction for preassigned profiles of `arbitrary_offspring_matching.tex`
(`sec:profile-obstruction`): equal branching semigroups alone do not ensure matching for
fixed binary encodings.  The two varying-offspring processes of `Models/Counter.lean` with
`ν_L = δ₄` and `ν_R = (δ₄ + δ₇)/2`, the path relation `0 – 1 – 2` on `Fin 3` and the
state law `μ_t = (1/2) δ₀ + (1/2 - t) δ₁ + t δ₂` have

* `η_α(μ_t) = t/(2(1-t)^α) + 2^{α-1} t → 0` (`etaG_muT`, `etaG_muT_tendsto`);
* every odd-depth vertex of the left process in the forced state `0`
  (`left_odd_depth_zero`);
* a fresh spine `u_0, u_1, …` of the right process (`spineAddr`, with `|u_i| ≤ 3i` in
  `spineAddr_length_le`) along which each step lands at odd depth with probability `1/2`
  and then carries the state `2` with probability `t` (the event `E_n` is `Spine`, in
  address form `Spine_iff`; its mass is `spineMass`, bounded in `spineMass_le`), so that
  `P(M_{3n}) ≤ (1 - t/2)^n` (`match_le`), the finite matching probabilities tend to `0`
  (`match_tendsto_zero`) and the infinite matching probability vanishes
  (`infMatch_eq_zero`).

The last paragraph of the section, the law `(1-t) δ₂ + t δ₁` with `η_α = 0` and `b(0) = t`,
is `etaG_muTwoOne_eq_zero` and `rE_zero_muTwoOne`.
-/
import GraphMarkovMatching.Stopped.Paths
import GraphMarkovMatching.Models.Counter
import GraphMarkovMatching.Models.Examples
import GraphMarkovMatching.Support.Trajectory

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-! ### Subtrees and addresses (`sec:profile-obstruction`) -/

section Addresses

variable {S : Type u}

/-- The first subtree of a labelling of positive height. -/
def sub1 {h : ℕ} (x : FullLab S (h + 1)) : FullLab S h := x.2.1

/-- The second subtree of a labelling of positive height. -/
def sub2 {h : ℕ} (x : FullLab S (h + 1)) : FullLab S h := x.2.2

@[simp] lemma sub1_branch {h : ℕ} (s : S) (p : FullLab S h × FullLab S h) :
    sub1 (branch s p) = p.1 := rfl

@[simp] lemma sub2_branch {h : ℕ} (s : S) (p : FullLab S h × FullLab S h) :
    sub2 (branch s p) = p.2 := rfl

/-- Every labelling of positive height is a branch of its root and its two subtrees. -/
lemma eq_branch_sub {h : ℕ} (x : FullLab S (h + 1)) :
    x = branch (rootLab (h + 1) x) (sub1 x, sub2 x) := rfl

/-- The label at the address `v` (a word over `{1,2}`, encoded as a list of booleans with
`false` for the first child): the root when `v` is empty, and the label of the remaining
address in the corresponding subtree otherwise.  Addresses longer than the height stop at
the leaf reached. -/
def coordLab : (h : ℕ) → FullLab S h → List Bool → S
  | 0, x, _ => rootLab 0 x
  | h + 1, x, [] => rootLab (h + 1) x
  | h + 1, x, false :: v => coordLab h (sub1 x) v
  | h + 1, x, true :: v => coordLab h (sub2 x) v

@[simp] lemma coordLab_nil (h : ℕ) (x : FullLab S h) : coordLab h x [] = rootLab h x := by
  cases h <;> rfl

@[simp] lemma coordLab_cons_false (h : ℕ) (x : FullLab S (h + 1)) (v : List Bool) :
    coordLab (h + 1) x (false :: v) = coordLab h (sub1 x) v := rfl

@[simp] lemma coordLab_cons_true (h : ℕ) (x : FullLab S (h + 1)) (v : List Bool) :
    coordLab (h + 1) x (true :: v) = coordLab h (sub2 x) v := rfl

end Addresses

/-! ### The path relation and the state law (`sec:profile-obstruction`) -/

/-- The path relation `0 – 1 – 2` on `Fin 3`, including the reflexive pairs. -/
def pathRel3 : Fin 3 → Fin 3 → Prop := fun a b => a.val ≤ b.val + 1 ∧ b.val ≤ a.val + 1

instance : DecidableRel pathRel3 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma pathRel3_refl (a : Fin 3) : pathRel3 a a := ⟨by omega, by omega⟩

lemma pathRel3_symm (a b : Fin 3) (h : pathRel3 a b) : pathRel3 b a := ⟨h.2, h.1⟩

lemma not_pathRel3_zero_two : ¬ pathRel3 0 2 := by decide

/-- A state compatible with `0` is not `2`. -/
lemma ne_two_of_pathRel3_zero {a : Fin 3} (h : pathRel3 0 a) : a ≠ 2 := by
  rintro rfl
  exact not_pathRel3_zero_two h

/-- The state law `μ_t = (1/2) δ₀ + (1/2 - t) δ₁ + t δ₂` for `0 < t < 1/2`. -/
noncomputable def muT (t : ℝ) (h0 : 0 < t) (h1 : t < 1 / 2) : PMF (Fin 3) :=
  PMF.ofFintype
    (fun v => if v = 0 then ENNReal.ofReal (1 / 2)
      else if v = 1 then ENNReal.ofReal (1 / 2 - t) else ENNReal.ofReal t)
    (by
      rw [Fin.sum_univ_three]
      simp only [ite_true, Fin.isValue, one_ne_zero, ite_false, Fin.reduceEq]
      rw [← ENNReal.ofReal_add (by norm_num) (by linarith), ← ENNReal.ofReal_add
        (by linarith) h0.le]
      rw [show (1 : ℝ) / 2 + (1 / 2 - t) + t = 1 by ring, ENNReal.ofReal_one])

lemma muT_zero {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) : muT t h0 h1 0 = ENNReal.ofReal (1 / 2) :=
  rfl

lemma muT_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    muT t h0 h1 1 = ENNReal.ofReal (1 / 2 - t) := rfl

lemma muT_two {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) : muT t h0 h1 2 = ENNReal.ofReal t := rfl

/-- The total version of `muT`: the point mass at `0` outside `0 < t < 1/2`. -/
noncomputable def muT' (t : ℝ) : PMF (Fin 3) :=
  if h : 0 < t ∧ t < 1 / 2 then muT t h.1 h.2 else PMF.pure 0

lemma muT'_of {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) : muT' t = muT t h0 h1 :=
  dite_eq_left ⟨h0, h1⟩

/-! ### The one-site potential of `μ_t` (`sec:profile-obstruction`) -/

/-- The bad degrees of `μ_t` on the path: `q(0) = t`, `q(1) = 0`, `q(2) = 1/2`. -/
lemma qE_muT_zero {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    qE (muT t h0 h1) pathRel3 0 = ENNReal.ofReal t := by
  rw [qE, tsum_fintype, Fin.sum_univ_three]
  simp [pathRel3, muT_two]

lemma qE_muT_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    qE (muT t h0 h1) pathRel3 1 = 0 := by
  rw [qE, tsum_fintype, Fin.sum_univ_three]
  simp [pathRel3]

lemma qE_muT_two {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    qE (muT t h0 h1) pathRel3 2 = ENNReal.ofReal (1 / 2) := by
  rw [qE, tsum_fintype, Fin.sum_univ_three]
  simp [pathRel3, muT_zero]

/-- `η_α(μ_t) = t/(2(1-t)^α) + 2^{α-1} t` (`sec:profile-obstruction`). -/
theorem etaG_muT (α : ℝ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    etaG α pathRel3 (muT t h0 h1)
      = ENNReal.ofReal (t / (2 * (1 - t) ^ α) + 2 ^ (α - 1) * t) := by
  have hq0 : q (muT t h0 h1) pathRel3 0 = t := by
    rw [q, qE_muT_zero, ENNReal.toReal_ofReal h0.le]
  have hq1 : q (muT t h0 h1) pathRel3 1 = 0 := by
    rw [q, qE_muT_one, ENNReal.toReal_zero]
  have hq2 : q (muT t h0 h1) pathRel3 2 = 1 / 2 := by
    rw [q, qE_muT_two, ENNReal.toReal_ofReal (by norm_num)]
  have ht1 : t < 1 := by linarith
  have hpos : (0 : ℝ) < (1 - t) ^ α := Real.rpow_pos_of_pos (by linarith) α
  have hphi0 : phi α t = t / (1 - t) ^ α := rfl
  have hphi2 : phi α (1 / 2) = 2 ^ (α - 1) := by
    rw [phi, Real.rpow_sub_one (by norm_num), show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num,
      Real.inv_rpow (by norm_num)]
    field_simp
  rw [etaG, PhiD, tsum_fintype, Fin.sum_univ_three, hq0, hq1, hq2, phiE_zero, mul_zero, add_zero,
    phiE_of_lt ht1, phiE_of_lt (by norm_num), muT_zero, muT_two, hphi0, hphi2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul h0.le,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp

/-- The potential of `μ_t` tends to `0` as `t ↓ 0` (`sec:profile-obstruction`). -/
theorem etaG_muT_tendsto (α : ℝ) :
    Filter.Tendsto (fun t => (etaG α pathRel3 (muT' t)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont : ContinuousAt (fun t : ℝ => t / (2 * (1 - t) ^ α) + 2 ^ (α - 1) * t) 0 := by
    refine ContinuousAt.add (ContinuousAt.div continuousAt_id ?_ ?_) ?_
    · exact continuousAt_const.mul
        ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num)))
    · simp
    · exact continuousAt_const.mul continuousAt_id
  have hlim : Filter.Tendsto (fun t : ℝ => t / (2 * (1 - t) ^ α) + 2 ^ (α - 1) * t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi 0) hcont.tendsto
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
  have hnn : 0 ≤ t / (2 * (1 - t) ^ α) + 2 ^ (α - 1) * t :=
    add_nonneg
      (div_nonneg ht.1.le (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [ht.2]) α)))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) ht.1.le)
  rw [muT'_of ht.1 ht.2, etaG_muT α ht.1 ht.2, ENNReal.toReal_ofReal hnn]

/-! ### Odd depths in the left process (`sec:profile-obstruction`) -/

section Left

variable {V : Type}

/-- Every vertex at an address `v` with `d + |v|` odd carries a label with first coordinate
`v0`: the invariant of the left process, `d` being the depth of the root. -/
def OddZ (v0 : V) : ℕ → (h : ℕ) → FullLab (V × ℕ) h → Prop
  | d, 0, x => Odd d → (rootLab 0 x).1 = v0
  | d, h + 1, x => (Odd d → (rootLab (h + 1) x).1 = v0)
      ∧ OddZ v0 (d + 1) h (sub1 x) ∧ OddZ v0 (d + 1) h (sub2 x)

lemma OddZ.root {v0 : V} {d h : ℕ} {x : FullLab (V × ℕ) h} (hx : OddZ v0 d h x) (hd : Odd d) :
    (rootLab h x).1 = v0 := by
  cases h with
  | zero => exact hx hd
  | succ h => exact hx.1 hd

lemma OddZ.left {v0 : V} {d h : ℕ} {x : FullLab (V × ℕ) (h + 1)} (hx : OddZ v0 d (h + 1) x) :
    OddZ v0 (d + 1) h (sub1 x) := hx.2.1

lemma OddZ.right {v0 : V} {d h : ℕ} {x : FullLab (V × ℕ) (h + 1)} (hx : OddZ v0 d (h + 1) x) :
    OddZ v0 (d + 1) h (sub2 x) := hx.2.2

/-- The invariant in address form: every address of odd total depth carries `v0`. -/
lemma OddZ.coordLab {v0 : V} : ∀ {d h : ℕ} {x : FullLab (V × ℕ) h}, OddZ v0 d h x →
    ∀ (v : List Bool), v.length ≤ h → Odd (d + v.length) → (coordLab h x v).1 = v0 := by
  intro d h
  induction h generalizing d with
  | zero =>
      intro x hx v hv hodd
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hv)] at hodd ⊢
      rw [coordLab_nil]
      exact hx.root (by simpa using hodd)
  | succ h ih =>
      intro x hx v hv hodd
      match v with
      | [] =>
          rw [coordLab_nil]
          exact hx.root (by simpa using hodd)
      | false :: v =>
          rw [coordLab_cons_false]
          refine ih hx.left v (by simpa using hv) ?_
          rw [List.length_cons] at hodd
          convert hodd using 1
          ring
      | true :: v =>
          rw [coordLab_cons_true]
          refine ih hx.right v (by simpa using hv) ?_
          rw [List.length_cons] at hodd
          convert hodd using 1
          ring

variable (μ : PMF V) (v0 : V)

/-- A charged sample of the pushforward under `branch s` is a branch of a charged pair. -/
lemma exists_of_map_branch_ne_zero {h : ℕ}
    (P : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h)) (s : V × ℕ)
    {x : FullLab (V × ℕ) (h + 1)} (hx : (P.map (branch s)) x ≠ 0) :
    ∃ p, P p ≠ 0 ∧ x = branch s p := by
  have := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hx)
  obtain ⟨p, hp, rfl⟩ := this
  exact ⟨p, hp, rfl⟩

/-- A charged fresh state of the law `δ₄` carries the counter `4`. -/
lemma freshQ_nuFour_ne_zero {s : V × ℕ} (hs : freshQ μ nuFour s ≠ 0) : s.2 = 4 := by
  rw [freshQ, prodPMF_apply, nuFour] at hs
  by_contra h
  rw [PMF.pure_apply, ite_eq_right h, mul_zero] at hs
  exact hs rfl

/-- The invariant of the left process: below a fresh counter-`4` root at even depth and
below a forced counter-`2` root at odd depth, every odd-depth vertex carries `v0`. -/
lemma left_invariant : ∀ (h : ℕ) (d : ℕ),
    (∀ (v : V) (x : FullLab (V × ℕ) h), Even d →
      muM (varyK μ nuFour v0) (v, 4) h x ≠ 0 → OddZ v0 d h x)
    ∧ (∀ (x : FullLab (V × ℕ) h), Odd d → muM (varyK μ nuFour v0) (v0, 2) h x ≠ 0 →
      OddZ v0 d h x) := by
  intro h
  induction h with
  | zero =>
      intro d
      refine ⟨fun v x hd hx hodd => absurd hd (Nat.not_even_iff_odd.mpr hodd), ?_⟩
      intro x _ hx _
      rw [muM_zero, PMF.pure_apply] at hx
      by_cases hxs : x = leaf (v0, 2)
      · rw [hxs]
        rfl
      · rw [ite_eq_right hxs] at hx
        exact absurd rfl hx
  | succ h ih =>
      intro d
      constructor
      · intro v x hd hx
        rw [muM_varyK_succ, Xi_of_four_le μ nuFour v0 (le_refl 4)] at hx
        obtain ⟨p, hp, rfl⟩ := exists_of_map_branch_ne_zero _ _ hx
        rw [prodPMF_apply] at hp
        have hp1 := left_ne_zero_of_mul hp
        have hp2 := right_ne_zero_of_mul hp
        have hd1 : Odd (d + 1) := hd.add_one
        refine ⟨fun hodd => absurd hd (Nat.not_even_iff_odd.mpr hodd), ?_, ?_⟩
        · exact (ih (d + 1)).2 p.1 hd1 hp1
        · exact (ih (d + 1)).2 p.2 hd1 hp2
      · intro x hd hx
        rw [muM_varyK_succ, Xi_of_le_two μ nuFour v0 (le_refl 2)] at hx
        obtain ⟨p, hp, rfl⟩ := exists_of_map_branch_ne_zero _ _ hx
        rw [prodPMF_apply] at hp
        have hp1 := left_ne_zero_of_mul hp
        have hp2 := right_ne_zero_of_mul hp
        have hd1 : Even (d + 1) := hd.add_one
        have key : ∀ y : FullLab (V × ℕ) h,
            Tlaw μ nuFour v0 h y ≠ 0 → OddZ v0 (d + 1) h y := by
          intro y hy
          rw [Tlaw] at hy
          obtain ⟨s, hs, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp
            ((PMF.mem_support_iff _ _).mpr hy)
          have h4 := freshQ_nuFour_ne_zero μ hs
          have hs' : s = (s.1, 4) := by
            rw [← h4]
          rw [hs'] at hy
          exact (ih (d + 1)).1 s.1 y hd1 hy
        exact ⟨fun _ => rfl, key p.1 hp1, key p.2 hp2⟩

/-- **Odd depths in the left process** (`sec:profile-obstruction`): every vertex of odd depth
of a charged sample of the left process carries the forced label `v0`, in the invariant
form. -/
lemma left_oddZ (h : ℕ) (x : FullLab (V × ℕ) h) (hx : Tlaw μ nuFour v0 h x ≠ 0) :
    OddZ v0 0 h x := by
  rw [Tlaw] at hx
  obtain ⟨s, hs, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hx)
  have h4 := freshQ_nuFour_ne_zero μ hs
  have hs' : s = (s.1, 4) := by
    rw [← h4]
  rw [hs'] at hx
  exact (left_invariant μ v0 h 0).1 s.1 x ⟨0, rfl⟩ hx

end Left

/-- **Odd depths in the left process** (`sec:profile-obstruction`): in every charged sample
of the left process, the vertex at any address of odd depth carries the state `0`. -/
theorem left_odd_depth_zero {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) (h : ℕ)
    (x : FullLab (Fin 3 × ℕ) h) (hx : Tlaw (muT t h0 h1) nuFour 0 h x ≠ 0) (v : List Bool)
    (hv : v.length ≤ h) (hodd : Odd v.length) : (coordLab h x v).1 = 0 :=
  (left_oddZ (muT t h0 h1) 0 h x hx).coordLab v hv (by simpa using hodd)

/-! ### The fresh spine of the right process (`sec:profile-obstruction`) -/

section Right

variable {V : Type} (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- Integrating a function of the first coordinate against a product law. -/
lemma tsum_prodPMF_fst {A B : Type} (P : PMF A) (Q : PMF B) (G : A → ℝ≥0∞) :
    ∑' p : A × B, prodPMF P Q p * G p.1 = ∑' a, P a * G a := by
  calc ∑' p : A × B, prodPMF P Q p * G p.1
      = ∑' p : A × B, (P p.1 * G p.1) * Q p.2 := tsum_congr fun p => by
          rw [prodPMF_apply]; ring
    _ = (∑' a, P a * G a) * ∑' b, Q b := tsum_prod_split (fun a => P a * G a) (fun b => Q b)
    _ = ∑' a, P a * G a := by rw [PMF.tsum_coe, mul_one]

/-- Integrating a function of the second coordinate against a product law. -/
lemma tsum_prodPMF_snd {A B : Type} (P : PMF A) (Q : PMF B) (G : B → ℝ≥0∞) :
    ∑' p : A × B, prodPMF P Q p * G p.2 = ∑' b, Q b * G b := by
  calc ∑' p : A × B, prodPMF P Q p * G p.2
      = ∑' p : A × B, P p.1 * (Q p.2 * G p.2) := tsum_congr fun p => by
          rw [prodPMF_apply]; ring
    _ = (∑' a, P a) * ∑' b, Q b * G b := tsum_prod_split (fun a => P a) (fun b => Q b * G b)
    _ = ∑' b, Q b * G b := by rw [PMF.tsum_coe, one_mul]

/-- The forced counter-`2` law: two independent fresh subtrees below the root `(v0, 2)`. -/
lemma Zlaw_two_succ (h : ℕ) :
    Zlaw μ ν v0 2 (h + 1)
      = (prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h)).map (branch (v0, 2)) := by
  rw [Zlaw, muM_varyK_succ, Xi_of_le_two μ ν v0 (le_refl 2)]

/-- The forced counter-`4` law: two forced counter-`2` subtrees below the root `(v0, 4)`. -/
lemma Zlaw_four_succ (h : ℕ) :
    Zlaw μ ν v0 4 (h + 1)
      = (prodPMF (Zlaw μ ν v0 2 h) (Zlaw μ ν v0 2 h)).map (branch (v0, 4)) := by
  rw [Zlaw, muM_varyK_succ, Xi_of_four_le μ ν v0 (le_refl 4)]

/-- Below a fresh counter-`4` root the vertex at address `[false, false]` is fresh with the
height-`(h+1)` law (`sec:profile-obstruction`). -/
lemma tsum_muM_four (v : V) (h : ℕ) (G : FullLab (V × ℕ) (h + 1) → ℝ≥0∞) :
    ∑' x, muM (varyK μ ν v0) (v, 4) (h + 3) x * G (sub1 (sub1 x))
      = ∑' z, Tlaw μ ν v0 (h + 1) z * G z := by
  calc ∑' x, muM (varyK μ ν v0) (v, 4) (h + 3) x * G (sub1 (sub1 x))
      = ∑' p, Xi μ ν v0 4 (h + 2) p * G (sub1 p.1) := by
        rw [muM_varyK_succ, tsum_map_mul]
        rfl
    _ = ∑' y, Zlaw μ ν v0 2 (h + 2) y * G (sub1 y) := by
        rw [Xi_of_four_le μ ν v0 (le_refl 4)]
        exact tsum_prodPMF_fst _ _ (fun y => G (sub1 y))
    _ = ∑' q, prodPMF (Tlaw μ ν v0 (h + 1)) (Tlaw μ ν v0 (h + 1)) q * G q.1 := by
        rw [Zlaw_two_succ, tsum_map_mul]
        rfl
    _ = ∑' z, Tlaw μ ν v0 (h + 1) z * G z := tsum_prodPMF_fst _ _ G

/-- Below a fresh counter-`7` root the vertex at address `[true, false, false]` is fresh with
the height-`h` law (`sec:profile-obstruction`). -/
lemma tsum_muM_seven (v : V) (h : ℕ) (G : FullLab (V × ℕ) h → ℝ≥0∞) :
    ∑' x, muM (varyK μ ν v0) (v, 7) (h + 3) x * G (sub1 (sub1 (sub2 x)))
      = ∑' z, Tlaw μ ν v0 h z * G z := by
  calc ∑' x, muM (varyK μ ν v0) (v, 7) (h + 3) x * G (sub1 (sub1 (sub2 x)))
      = ∑' p, Xi μ ν v0 7 (h + 2) p * G (sub1 (sub1 p.2)) := by
        rw [muM_varyK_succ, tsum_map_mul]
        rfl
    _ = ∑' y, Zlaw μ ν v0 4 (h + 2) y * G (sub1 (sub1 y)) := by
        rw [Xi_of_four_le μ ν v0 (by norm_num : 4 ≤ 7)]
        exact tsum_prodPMF_snd _ _ (fun y => G (sub1 (sub1 y)))
    _ = ∑' q, prodPMF (Zlaw μ ν v0 2 (h + 1)) (Zlaw μ ν v0 2 (h + 1)) q * G (sub1 q.1) := by
        rw [Zlaw_four_succ, tsum_map_mul]
        rfl
    _ = ∑' w, Zlaw μ ν v0 2 (h + 1) w * G (sub1 w) := tsum_prodPMF_fst _ _ (fun w => G (sub1 w))
    _ = ∑' r, prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) r * G r.1 := by
        rw [Zlaw_two_succ, tsum_map_mul]
        rfl
    _ = ∑' z, Tlaw μ ν v0 h z * G z := tsum_prodPMF_fst _ _ G

/-- The law `(δ₄ + δ₇)/2` integrates to the average of the two arities. -/
lemma tsum_nuFourSeven (B : ℕ → ℝ≥0∞) :
    ∑' k, nuFourSeven k * B k = 2⁻¹ * (B 4 + B 7) := by
  rw [nuFourSeven, tsum_map_mul, tsum_fintype, Fintype.sum_bool]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, Bool.false_eq_true,
    ite_true, ite_false]
  ring

/-- The fresh law of the right process is the state mixture of the two arity laws. -/
lemma tsum_Tlaw_fourSeven (h : ℕ) (F : FullLab (V × ℕ) h → ℝ≥0∞) :
    ∑' y, Tlaw μ nuFourSeven v0 h y * F y
      = ∑' v, μ v * (2⁻¹ * (∑' y, muM (varyK μ nuFourSeven v0) (v, 4) h y * F y
          + ∑' y, muM (varyK μ nuFourSeven v0) (v, 7) h y * F y)) := by
  rw [Tlaw, tsum_bind_mul, ENNReal.tsum_prod']
  refine tsum_congr fun v => ?_
  calc ∑' k, freshQ μ nuFourSeven (v, k) * ∑' y, muM (varyK μ nuFourSeven v0) (v, k) h y * F y
      = μ v * ∑' k, nuFourSeven k * ∑' y, muM (varyK μ nuFourSeven v0) (v, k) h y * F y := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun k => by rw [freshQ, prodPMF_apply]; ring
    _ = _ := by rw [tsum_nuFourSeven]

end Right

/-! ### The spine event (`sec:profile-obstruction`) -/

/-- The spine event `E_n` along the fresh spine `u_0, …, u_n` of the right process, for a
root at depth `d`: from a counter-`4` vertex the spine continues at the address
`[false, false]` (depth `+2`), from any other vertex at `[true, false, false]` (depth `+3`),
and at every spine vertex of odd depth the state is not `2`.  At heights below `3` with
steps remaining the event is trivial; it is only used at heights `≥ 3n`. -/
def Spine : ℕ → ℕ → (h : ℕ) → FullLab (Fin 3 × ℕ) h → Prop
  | 0, _, _, _ => True
  | n + 1, d, h + 3, x =>
      if (rootLab (h + 3) x).2 = 4 then
        (Odd (d + 2) → (rootLab (h + 1) (sub1 (sub1 x))).1 ≠ 2)
          ∧ Spine n (d + 2) (h + 1) (sub1 (sub1 x))
      else
        (Odd (d + 3) → (rootLab h (sub1 (sub1 (sub2 x)))).1 ≠ 2)
          ∧ Spine n (d + 3) h (sub1 (sub1 (sub2 x)))
  | _ + 1, _, 0, _ => True
  | _ + 1, _, 1, _ => True
  | _ + 1, _, 2, _ => True

lemma Spine_zero (d h : ℕ) (x : FullLab (Fin 3 × ℕ) h) : Spine 0 d h x := by
  simp [Spine]

lemma Spine_height_zero (n d : ℕ) (x : FullLab (Fin 3 × ℕ) 0) : Spine n d 0 x := by
  cases n <;> simp [Spine]

lemma Spine_succ (n d h : ℕ) (x : FullLab (Fin 3 × ℕ) (h + 3)) :
    Spine (n + 1) d (h + 3) x
      = if (rootLab (h + 3) x).2 = 4 then
          (Odd (d + 2) → (rootLab (h + 1) (sub1 (sub1 x))).1 ≠ 2)
            ∧ Spine n (d + 2) (h + 1) (sub1 (sub1 x))
        else
          (Odd (d + 3) → (rootLab h (sub1 (sub1 (sub2 x)))).1 ≠ 2)
            ∧ Spine n (d + 3) h (sub1 (sub1 (sub2 x))) := rfl

/-- The spine event does not depend on the root state. -/
lemma Spine_branch_iff (n d h : ℕ) (v v' : Fin 3) (k : ℕ)
    (p : FullLab (Fin 3 × ℕ) h × FullLab (Fin 3 × ℕ) h) :
    Spine n d (h + 1) (branch (v, k) p) ↔ Spine n d (h + 1) (branch (v', k) p) := by
  cases n with
  | zero => exact ⟨fun _ => Spine_zero _ _ _, fun _ => Spine_zero _ _ _⟩
  | succ n =>
      match h with
      | 0 => exact Iff.rfl
      | 1 => exact Iff.rfl
      | h + 2 => exact Iff.rfl

/-- The address of the spine vertex `u_n` of the right process as a function of the
labelling (`sec:profile-obstruction`): from a counter-`4` vertex the spine continues at
`[false, false]`, from any other vertex at `[true, false, false]`.  At heights below `3`
with steps remaining the address stops. -/
def spineAddr : ℕ → (h : ℕ) → FullLab (Fin 3 × ℕ) h → List Bool
  | 0, _, _ => []
  | n + 1, h + 3, x =>
      if (rootLab (h + 3) x).2 = 4 then false :: false :: spineAddr n (h + 1) (sub1 (sub1 x))
      else true :: false :: false :: spineAddr n h (sub1 (sub1 (sub2 x)))
  | _ + 1, 0, _ => []
  | _ + 1, 1, _ => []
  | _ + 1, 2, _ => []

@[simp] lemma spineAddr_zero (h : ℕ) (x : FullLab (Fin 3 × ℕ) h) : spineAddr 0 h x = [] := by
  simp [spineAddr]

lemma spineAddr_succ (n h : ℕ) (x : FullLab (Fin 3 × ℕ) (h + 3)) :
    spineAddr (n + 1) (h + 3) x
      = if (rootLab (h + 3) x).2 = 4 then false :: false :: spineAddr n (h + 1) (sub1 (sub1 x))
        else true :: false :: false :: spineAddr n h (sub1 (sub1 (sub2 x))) := rfl

/-- `|u_n| ≤ 3n` (`sec:profile-obstruction`). -/
lemma spineAddr_length_le : ∀ (n h : ℕ) (x : FullLab (Fin 3 × ℕ) h),
    (spineAddr n h x).length ≤ 3 * n := by
  intro n
  induction n with
  | zero => intro h x; simp
  | succ n ih =>
      intro h x
      match h with
      | 0 => simp [spineAddr]
      | 1 => simp [spineAddr]
      | 2 => simp [spineAddr]
      | h + 3 =>
          rw [spineAddr_succ]
          split_ifs
          · have := ih (h + 1) (sub1 (sub1 x))
            simp only [List.length_cons]
            omega
          · have := ih h (sub1 (sub1 (sub2 x)))
            simp only [List.length_cons]
            omega

/-- Reindexing a bounded universal statement over `1 ≤ i ≤ n + 1`. -/
private lemma forall_pos_le_succ_iff (P : ℕ → Prop) (n : ℕ) :
    (∀ i, 0 < i → i ≤ n + 1 → P i) ↔ P 1 ∧ ∀ i, 0 < i → i ≤ n → P (i + 1) := by
  constructor
  · intro H
    exact ⟨H 1 one_pos (by omega), fun i hi hin => H (i + 1) (by omega) (by omega)⟩
  · rintro ⟨H1, H⟩ i hi hin
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    cases j with
    | zero => exact H1
    | succ j => exact H (j + 1) (by omega) (by omega)

/-- **The spine event in address form** (`sec:profile-obstruction`): at height `≥ 3n`, the
event `E_n` holds iff for every `1 ≤ i ≤ n` with `d + |u_i|` odd the state at `u_i` is
not `2`. -/
lemma Spine_iff : ∀ (n d h : ℕ), 3 * n ≤ h → ∀ (y : FullLab (Fin 3 × ℕ) h),
    Spine n d h y ↔ ∀ i, 0 < i → i ≤ n → Odd (d + (spineAddr i h y).length) →
      (coordLab h y (spineAddr i h y)).1 ≠ 2 := by
  intro n
  induction n with
  | zero =>
      intro d h _ y
      simp only [Spine_zero, true_iff]
      intro i hi hin
      omega
  | succ n ih =>
      intro d h hh y
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 3 := ⟨h - 3, by omega⟩
      rw [Spine_succ, forall_pos_le_succ_iff]
      split_ifs with hk
      · rw [ih (d + 2) (h' + 1) (by omega)]
        simp only [spineAddr_succ, ite_eq_left hk, spineAddr_zero, List.length_cons,
          List.length_nil, coordLab_cons_false, coordLab_nil, Nat.odd_iff]
        constructor
        · rintro ⟨h0, hrest⟩
          exact ⟨fun hodd => h0 (by omega), fun i hi hin hodd => hrest i hi hin (by omega)⟩
        · rintro ⟨h0, hrest⟩
          exact ⟨fun hodd => h0 (by omega), fun i hi hin hodd => hrest i hi hin (by omega)⟩
      · rw [ih (d + 3) h' (by omega)]
        simp only [spineAddr_succ, ite_eq_right hk, spineAddr_zero, List.length_cons,
          List.length_nil, coordLab_cons_false, coordLab_cons_true, coordLab_nil, Nat.odd_iff]
        constructor
        · rintro ⟨h0, hrest⟩
          exact ⟨fun hodd => h0 (by omega), fun i hi hin hodd => hrest i hi hin (by omega)⟩
        · rintro ⟨h0, hrest⟩
          exact ⟨fun hodd => h0 (by omega), fun i hi hin hodd => hrest i hi hin (by omega)⟩

section SpineMass

variable (μ : PMF (Fin 3))

/-- The right-process mass of the spine event, `P(E_n)` for a root at depth `d`. -/
noncomputable def spineMass (n d h : ℕ) : ℝ≥0∞ :=
  ∑' y, Tlaw μ nuFourSeven 0 h y * (if Spine n d h y then 1 else 0)

lemma spineMass_zero (d h : ℕ) : spineMass μ 0 d h = 1 := by
  simp only [spineMass, Spine_zero, ite_true, mul_one]
  exact PMF.tsum_coe _

/-- The mass of the spine event below a fixed counter does not depend on the root state. -/
lemma tsum_muM_spine_indep (n d h : ℕ) (v v' : Fin 3) (k : ℕ) :
    ∑' y, muM (varyK μ nuFourSeven 0) (v, k) h y * (if Spine n d h y then 1 else 0)
      = ∑' y, muM (varyK μ nuFourSeven 0) (v', k) h y * (if Spine n d h y then 1 else 0) := by
  cases h with
  | zero =>
      simp only [Spine_height_zero, ite_true, mul_one]
      rw [PMF.tsum_coe, PMF.tsum_coe]
  | succ h =>
      rw [muM_varyK_succ, muM_varyK_succ, tsum_map_mul, tsum_map_mul]
      refine tsum_congr fun p => ?_
      rw [propext (Spine_branch_iff n d h v v' k p)]

/-- The mass of the states other than `2`. -/
lemma tsum_ne_two : ∑' v : Fin 3, μ v * (if v ≠ 2 then 1 else 0) = 1 - μ 2 := by
  have hsum : μ 0 + μ 1 + μ 2 = 1 := by
    rw [← PMF.tsum_coe μ, tsum_fintype, Fin.sum_univ_three]
  rw [tsum_fintype, Fin.sum_univ_three]
  simp only [ne_eq, Fin.isValue, Fin.reduceEq, not_false_eq_true, ite_true, mul_one,
    not_true_eq_false, ite_false, mul_zero, add_zero]
  exact ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top _ _) hsum

/-- The spine event together with a root state other than `2` has mass `(1 - μ(2)) P(E_n)`:
the fresh root state is independent of the rest of the spine. -/
lemma tsum_Tlaw_root_filter (n d h : ℕ) :
    ∑' y, Tlaw μ nuFourSeven 0 h y
        * (if (rootLab h y).1 ≠ 2 ∧ Spine n d h y then 1 else 0)
      = (1 - μ 2) * spineMass μ n d h := by
  have hpt : ∀ (v : Fin 3) (k : ℕ) (y : FullLab (Fin 3 × ℕ) h),
      muM (varyK μ nuFourSeven 0) (v, k) h y
          * (if (rootLab h y).1 ≠ 2 ∧ Spine n d h y then 1 else 0)
        = (if v ≠ 2 then 1 else 0)
          * (muM (varyK μ nuFourSeven 0) (v, k) h y * (if Spine n d h y then 1 else 0)) := by
    intro v k y
    by_cases hy : muM (varyK μ nuFourSeven 0) (v, k) h y = 0
    · rw [hy, zero_mul, zero_mul, mul_zero]
    · rw [rootLab_of_ne_zero _ h _ y hy]
      by_cases h1 : v ≠ 2 <;> by_cases h2 : Spine n d h y <;> simp [h1, h2]
  set B4 := ∑' y, muM (varyK μ nuFourSeven 0) (0, 4) h y * (if Spine n d h y then 1 else 0)
    with hB4
  set B7 := ∑' y, muM (varyK μ nuFourSeven 0) (0, 7) h y * (if Spine n d h y then 1 else 0)
    with hB7
  have hS : spineMass μ n d h = 2⁻¹ * (B4 + B7) := by
    rw [spineMass, tsum_Tlaw_fourSeven]
    calc ∑' v, μ v * (2⁻¹ * (∑' y, muM (varyK μ nuFourSeven 0) (v, 4) h y
            * (if Spine n d h y then 1 else 0)
          + ∑' y, muM (varyK μ nuFourSeven 0) (v, 7) h y * (if Spine n d h y then 1 else 0)))
        = ∑' v, μ v * (2⁻¹ * (B4 + B7)) := tsum_congr fun v => by
          rw [tsum_muM_spine_indep μ n d h v 0 4, tsum_muM_spine_indep μ n d h v 0 7]
      _ = 2⁻¹ * (B4 + B7) := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [tsum_Tlaw_fourSeven, hS]
  calc ∑' v, μ v * (2⁻¹ * (∑' y, muM (varyK μ nuFourSeven 0) (v, 4) h y
          * (if (rootLab h y).1 ≠ 2 ∧ Spine n d h y then 1 else 0)
        + ∑' y, muM (varyK μ nuFourSeven 0) (v, 7) h y
          * (if (rootLab h y).1 ≠ 2 ∧ Spine n d h y then 1 else 0)))
      = ∑' v, (μ v * (if v ≠ 2 then 1 else 0)) * (2⁻¹ * (B4 + B7)) := by
        refine tsum_congr fun v => ?_
        simp only [hpt, ENNReal.tsum_mul_left]
        rw [tsum_muM_spine_indep μ n d h v 0 4, tsum_muM_spine_indep μ n d h v 0 7]
        ring
    _ = (1 - μ 2) * (2⁻¹ * (B4 + B7)) := by rw [ENNReal.tsum_mul_right, tsum_ne_two]

/-- The parity-weighted mass of one spine step: the next spine vertex has depth `d'` and,
when `d'` is odd, its state avoids `2` with probability `1 - μ(2)`. -/
lemma tsum_Tlaw_step (n d' h : ℕ) :
    ∑' z, Tlaw μ nuFourSeven 0 h z
        * (if (Odd d' → (rootLab h z).1 ≠ 2) ∧ Spine n d' h z then 1 else 0)
      = (if Odd d' then 1 - μ 2 else 1) * spineMass μ n d' h := by
  by_cases hd : Odd d'
  · rw [ite_eq_left hd, ← tsum_Tlaw_root_filter]
    refine tsum_congr fun z => ?_
    simp [hd]
  · rw [ite_eq_right hd, one_mul, spineMass]
    refine tsum_congr fun z => ?_
    simp [hd]

/-- **One step of the spine** (`sec:profile-obstruction`): with probability `1/2` each the
next spine vertex lies at depth `d + 2` or `d + 3`, and whichever of the two is odd carries
the additional factor `1 - μ(2)`. -/
lemma spineMass_succ (n d h : ℕ) :
    spineMass μ (n + 1) d (h + 3)
      = 2⁻¹ * ((if Odd (d + 2) then 1 - μ 2 else 1) * spineMass μ n (d + 2) (h + 1)
          + (if Odd (d + 3) then 1 - μ 2 else 1) * spineMass μ n (d + 3) h) := by
  have h4 : ∀ v : Fin 3, ∑' x, muM (varyK μ nuFourSeven 0) (v, 4) (h + 3) x
        * (if Spine (n + 1) d (h + 3) x then 1 else 0)
      = (if Odd (d + 2) then 1 - μ 2 else 1) * spineMass μ n (d + 2) (h + 1) := by
    intro v
    rw [← tsum_Tlaw_step, ← tsum_muM_four]
    refine tsum_congr fun x => ?_
    by_cases hx : muM (varyK μ nuFourSeven 0) (v, 4) (h + 3) x = 0
    · rw [hx, zero_mul, zero_mul]
    · rw [Spine_succ, rootLab_of_ne_zero _ _ _ x hx, ite_eq_left (rfl : (4 : ℕ) = 4)]
      split_ifs <;> rfl
  have h7 : ∀ v : Fin 3, ∑' x, muM (varyK μ nuFourSeven 0) (v, 7) (h + 3) x
        * (if Spine (n + 1) d (h + 3) x then 1 else 0)
      = (if Odd (d + 3) then 1 - μ 2 else 1) * spineMass μ n (d + 3) h := by
    intro v
    rw [← tsum_Tlaw_step, ← tsum_muM_seven]
    refine tsum_congr fun x => ?_
    by_cases hx : muM (varyK μ nuFourSeven 0) (v, 7) (h + 3) x = 0
    · rw [hx, zero_mul, zero_mul]
    · rw [Spine_succ, rootLab_of_ne_zero _ _ _ x hx,
        ite_eq_right (show ¬ ((7 : ℕ) = 4) by norm_num)]
      split_ifs <;> rfl
  rw [spineMass, tsum_Tlaw_fourSeven]
  simp only [h4, h7]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The real form of one spine step. -/
private lemma step_arith {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal x + (1 - ENNReal.ofReal a) * ENNReal.ofReal x)
      = ENNReal.ofReal ((1 - a / 2) * x) := by
  have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [h2, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ ha0,
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add hx (by nlinarith),
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- **The spine bound** (`sec:profile-obstruction`): `P(E_n) ≤ (1 - μ(2)/2)^n` at every
height `≥ 3n` and every root depth. -/
lemma spineMass_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hμ : μ 2 = ENNReal.ofReal a) :
    ∀ (n d h : ℕ), 3 * n ≤ h → spineMass μ n d h ≤ ENNReal.ofReal ((1 - a / 2) ^ n) := by
  intro n
  induction n with
  | zero =>
      intro d h _
      rw [spineMass_zero, pow_zero, ENNReal.ofReal_one]
  | succ n ih =>
      intro d h hh
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 3 := ⟨h - 3, by omega⟩
      have hq : 0 ≤ (1 - a / 2) ^ n := pow_nonneg (by linarith) n
      have h2 := ih (d + 2) (h' + 1) (by omega)
      have h3 := ih (d + 3) h' (by omega)
      rw [spineMass_succ, hμ, pow_succ, mul_comm ((1 - a / 2) ^ n), ← step_arith ha0 ha1 hq]
      rcases Nat.even_or_odd d with hd | hd
      · have hd2 : ¬ Odd (d + 2) := by
          rw [Nat.not_odd_iff_even]
          exact hd.add (by decide)
        have hd3 : Odd (d + 3) := by
          rw [show d + 3 = d + 2 + 1 by ring]
          exact (hd.add (by decide : Even 2)).add_one
        rw [ite_eq_right hd2, ite_eq_left hd3, one_mul]
        gcongr
      · have hd2 : Odd (d + 2) := hd.add_even (by decide)
        have hd3 : ¬ Odd (d + 3) := by
          rw [Nat.not_odd_iff_even, show d + 3 = d + 2 + 1 by ring]
          exact (hd.add_even (by decide : Even 2)).add_one
        rw [ite_eq_left hd2, ite_eq_right hd3, one_mul, add_comm]
        gcongr

end SpineMass

/-! ### Matching forces the spine event (`sec:profile-obstruction`) -/

section Matching

variable {S : Type u} {R : S → S → Prop}

/-- A matching at positive height matches the first subtree of the target with one of the
two subtrees of the source. -/
lemma sim_sub1 {h : ℕ} {x y : FullLab S (h + 1)} (hxy : fullSim R (h + 1) x y) :
    ∃ x₁, (x₁ = sub1 x ∨ x₁ = sub2 x) ∧ fullSim R h x₁ (sub1 y) := by
  have := (fullSim_branch R h (rootLab (h + 1) x) (rootLab (h + 1) y) (sub1 x, sub2 x)
    (sub1 y, sub2 y)).mp hxy
  rcases this.2 with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact ⟨sub1 x, Or.inl rfl, h1⟩
  · exact ⟨sub2 x, Or.inr rfl, h2⟩

/-- A matching at positive height matches the second subtree of the target with one of the
two subtrees of the source. -/
lemma sim_sub2 {h : ℕ} {x y : FullLab S (h + 1)} (hxy : fullSim R (h + 1) x y) :
    ∃ x₁, (x₁ = sub1 x ∨ x₁ = sub2 x) ∧ fullSim R h x₁ (sub2 y) := by
  have := (fullSim_branch R h (rootLab (h + 1) x) (rootLab (h + 1) y) (sub1 x, sub2 x)
    (sub1 y, sub2 y)).mp hxy
  rcases this.2 with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact ⟨sub2 x, Or.inr rfl, h2⟩
  · exact ⟨sub1 x, Or.inl rfl, h1⟩

end Matching

/-- The invariant passes to either subtree. -/
lemma OddZ.of_sub {V : Type} {v0 : V} {d h : ℕ} {x : FullLab (V × ℕ) (h + 1)}
    (hx : OddZ v0 d (h + 1) x) {x₁ : FullLab (V × ℕ) h}
    (h₁ : x₁ = sub1 x ∨ x₁ = sub2 x) :
    OddZ v0 (d + 1) h x₁ := by
  rcases h₁ with rfl | rfl
  · exact hx.left
  · exact hx.right

/-- **Matching forces the spine event** (`sec:profile-obstruction`): a rooted automorphism
preserves depth, every odd-depth vertex of the source carries `0`, and `0 ≁ 2`; hence the
spine vertices of odd depth of a matched target avoid the state `2`. -/
lemma spine_of_fullSim : ∀ (n d h : ℕ), 3 * n ≤ h → ∀ (x y : FullLab (Fin 3 × ℕ) h),
    OddZ 0 d h x → fullSim (labRel pathRel3) h x y → Spine n d h y := by
  intro n
  induction n with
  | zero => intro d h _ x y _ _; exact Spine_zero d h y
  | succ n ih =>
      intro d h hh x y hx hxy
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 3 := ⟨h - 3, by omega⟩
      rw [Spine_succ]
      split_ifs with hk
      · obtain ⟨x₁, hx₁, hs₁⟩ := sim_sub1 hxy
        obtain ⟨x₂, hx₂, hs₂⟩ := sim_sub1 hs₁
        have hx₂' : OddZ 0 (d + 2) (h' + 1) x₂ := (hx.of_sub hx₁).of_sub hx₂
        refine ⟨fun hodd => ?_, ih (d + 2) (h' + 1) (by omega) x₂ _ hx₂' hs₂⟩
        have hroot : pathRel3 (rootLab (h' + 1) x₂).1 (rootLab (h' + 1) (sub1 (sub1 y))).1 :=
          fullSim_root _ _ _ _ hs₂
        rw [hx₂'.root hodd] at hroot
        exact ne_two_of_pathRel3_zero hroot
      · obtain ⟨x₁, hx₁, hs₁⟩ := sim_sub2 hxy
        obtain ⟨x₂, hx₂, hs₂⟩ := sim_sub1 hs₁
        obtain ⟨x₃, hx₃, hs₃⟩ := sim_sub1 hs₂
        have hx₃' : OddZ 0 (d + 3) h' x₃ := ((hx.of_sub hx₁).of_sub hx₂).of_sub hx₃
        refine ⟨fun hodd => ?_, ih (d + 3) h' (by omega) x₃ _ hx₃' hs₃⟩
        have hroot : pathRel3 (rootLab h' x₃).1 (rootLab h' (sub1 (sub1 (sub2 y)))).1 :=
          fullSim_root _ _ _ _ hs₃
        rw [hx₃'.root hodd] at hroot
        exact ne_two_of_pathRel3_zero hroot

/-! ### The obstruction (`sec:profile-obstruction`) -/

section Obstruction

variable (μ : PMF (Fin 3))

/-- The height-`h` matching probability `P(M_h)` of the left process `δ₄` against the right
process `(δ₄ + δ₇)/2`, both with state law `μ`. -/
noncomputable def matchProb (h : ℕ) : ℝ≥0∞ :=
  ∑' p : FullLab (Fin 3 × ℕ) h × FullLab (Fin 3 × ℕ) h,
    prodPMF (Tlaw μ nuFour 0 h) (Tlaw μ nuFourSeven 0 h) p
      * (if fullSim (labRel pathRel3) h p.1 p.2 then 1 else 0)

/-- `P(M_h) ≤ P(E_n)` for `h ≥ 3n` (`sec:profile-obstruction`). -/
lemma matchProb_le_spineMass (n h : ℕ) (hh : 3 * n ≤ h) :
    matchProb μ h ≤ spineMass μ n 0 h := by
  calc matchProb μ h
      ≤ ∑' p : FullLab (Fin 3 × ℕ) h × FullLab (Fin 3 × ℕ) h,
          prodPMF (Tlaw μ nuFour 0 h) (Tlaw μ nuFourSeven 0 h) p
            * (if Spine n 0 h p.2 then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        by_cases hL : Tlaw μ nuFour 0 h p.1 = 0
        · simp [prodPMF_apply, hL]
        · refine mul_le_mul_right ?_ _
          split_ifs with h1 h2
          · exact le_rfl
          · exact absurd (spine_of_fullSim n 0 h hh p.1 p.2 (left_oddZ μ 0 h p.1 hL) h1) h2
          · exact zero_le
          · exact le_rfl
    _ = spineMass μ n 0 h := tsum_prodPMF_snd _ _ (fun y => if Spine n 0 h y then 1 else 0)

/-- Pushing both coordinates of a product law forward. -/
lemma tsum_prodPMF_map_mul {A B A' B' : Type} (P : PMF A) (Q : PMF B) (f : A → A')
    (g : B → B') (F : A' × B' → ℝ≥0∞) :
    ∑' p : A' × B', prodPMF (P.map f) (Q.map g) p * F p
      = ∑' p : A × B, prodPMF P Q p * F (f p.1, g p.2) := by
  rw [← prodPMF_map_prodMap, tsum_map_mul]
  rfl

/-- The finite matching probabilities decrease with the height: a height-`(h+1)` matching
restricts to a height-`h` one, and the laws are consistent. -/
lemma matchProb_succ_le (h : ℕ) : matchProb μ (h + 1) ≤ matchProb μ h := by
  calc matchProb μ (h + 1)
      ≤ ∑' p : FullLab (Fin 3 × ℕ) (h + 1) × FullLab (Fin 3 × ℕ) (h + 1),
          prodPMF (Tlaw μ nuFour 0 (h + 1)) (Tlaw μ nuFourSeven 0 (h + 1)) p
            * (if fullSim (labRel pathRel3) h (restrictLab h p.1) (restrictLab h p.2)
                then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun p => mul_le_mul_right ?_ _
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd (fullSimK_restrict _ 1 0 h _ _ h1) h2
        · exact zero_le
        · exact le_rfl
    _ = matchProb μ h := by
        rw [matchProb, ← Tlaw_map_restrictLab μ nuFour 0 h,
          ← Tlaw_map_restrictLab μ nuFourSeven 0 h, tsum_prodPMF_map_mul]

lemma matchProb_antitone : Antitone (matchProb μ) :=
  antitone_nat_of_succ_le (matchProb_succ_le μ)

end Obstruction

/-- **The obstruction** (`sec:profile-obstruction`): `P(M_{3n}) ≤ (1 - t/2)^n`. -/
theorem match_le {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) (n : ℕ) :
    ∑' p : FullLab (Fin 3 × ℕ) (3 * n) × FullLab (Fin 3 × ℕ) (3 * n),
      prodPMF (Tlaw (muT t h0 h1) nuFour 0 (3 * n)) (Tlaw (muT t h0 h1) nuFourSeven 0 (3 * n)) p
        * (if fullSim (labRel pathRel3) (3 * n) p.1 p.2 then 1 else 0)
      ≤ ENNReal.ofReal ((1 - t / 2) ^ n) :=
  (matchProb_le_spineMass _ n _ le_rfl).trans
    (spineMass_le _ h0.le (by linarith) (muT_two h0 h1) n 0 _ le_rfl)

/-- The obstruction at every height `h ≥ 3n`, by monotonicity of matching under restriction
(`sec:profile-obstruction`). -/
theorem match_le_of_le {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) (n h : ℕ) (hh : 3 * n ≤ h) :
    ∑' p : FullLab (Fin 3 × ℕ) h × FullLab (Fin 3 × ℕ) h,
      prodPMF (Tlaw (muT t h0 h1) nuFour 0 h) (Tlaw (muT t h0 h1) nuFourSeven 0 h) p
        * (if fullSim (labRel pathRel3) h p.1 p.2 then 1 else 0)
      ≤ ENNReal.ofReal ((1 - t / 2) ^ n) :=
  (matchProb_antitone _ hh).trans (match_le h0 h1 n)

/-- **The finite matching probabilities tend to zero** (`sec:profile-obstruction`). -/
theorem match_tendsto_zero {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    Filter.Tendsto (fun h : ℕ => ∑' p : FullLab (Fin 3 × ℕ) h × FullLab (Fin 3 × ℕ) h,
        prodPMF (Tlaw (muT t h0 h1) nuFour 0 h) (Tlaw (muT t h0 h1) nuFourSeven 0 h) p
          * (if fullSim (labRel pathRel3) h p.1 p.2 then 1 else 0))
      Filter.atTop (nhds 0) := by
  have hdiv : Filter.Tendsto (fun h : ℕ => h / 3) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨3 * b, fun h hh => by omega⟩
  have hb : Filter.Tendsto (fun h : ℕ => ENNReal.ofReal ((1 - t / 2) ^ (h / 3)))
      Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp hdiv)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le)
    (fun h => match_le_of_le h0 h1 (h / 3) h (Nat.mul_div_le h 3))

/-- **The infinite matching probability vanishes** (`sec:profile-obstruction`): on the product
of the two trajectory measures of the left and the right process, no rooted automorphism of
the infinite binary tree matches every vertex, almost surely. -/
theorem infMatch_eq_zero {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    trajPairLab (Tlaw (muT t h0 h1) nuFour 0) (Tlaw_map_restrictLab (muT t h0 h1) nuFour 0)
        (Tlaw (muT t h0 h1) nuFourSeven 0) (Tlaw_map_restrictLab (muT t h0 h1) nuFourSeven 0)
        {ω | InfMatch (labRel pathRel3) (fun n => consLab n ω.1) (fun n => consLab n ω.2)}
      = 0 := by
  set Pm := trajPairLab (Tlaw (muT t h0 h1) nuFour 0)
    (Tlaw_map_restrictLab (muT t h0 h1) nuFour 0) (Tlaw (muT t h0 h1) nuFourSeven 0)
    (Tlaw_map_restrictLab (muT t h0 h1) nuFourSeven 0) with hPm
  have hsub : ∀ n, {ω | InfMatch (labRel pathRel3) (fun n => consLab n ω.1)
        (fun n => consLab n ω.2)}
      ⊆ (fun ω : (Π m, FullLab (Fin 3 × ℕ) m) × (Π m, FullLab (Fin 3 × ℕ) m) =>
          (consLab (3 * n) ω.1, consLab (3 * n) ω.2)) ⁻¹'
        {p : FullLab (Fin 3 × ℕ) (3 * n) × FullLab (Fin 3 × ℕ) (3 * n)
          | fullSim (labRel pathRel3) (3 * n) p.1 p.2} := by
    intro n ω hω
    exact (infMatchK_iff_forall_level _ 1 0 _ _ (fun m => restrictLab_consLab m ω.1)
      (fun m => restrictLab_consLab m ω.2)).mp hω (3 * n)
  have hmeas : ∀ n, MeasurableSet
      {p : FullLab (Fin 3 × ℕ) (3 * n) × FullLab (Fin 3 × ℕ) (3 * n)
        | fullSim (labRel pathRel3) (3 * n) p.1 p.2} :=
    fun n => (Set.to_countable _).measurableSet
  have hle : ∀ n, Pm {ω | InfMatch (labRel pathRel3) (fun n => consLab n ω.1)
        (fun n => consLab n ω.2)} ≤ ENNReal.ofReal ((1 - t / 2) ^ n) := by
    intro n
    refine (MeasureTheory.measure_mono (hsub n)).trans ?_
    rw [← MeasureTheory.Measure.map_apply (measurable_consLab_pair _) (hmeas n), hPm,
      trajPairLab_map_consLab, PMF.toMeasure_apply _ (hmeas n)]
    refine le_trans (le_of_eq ?_) (match_le h0 h1 n)
    refine tsum_congr fun p => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  refine le_antisymm ?_ zero_le
  have hb : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal ((1 - t / 2) ^ n))
      Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith))
  exact ge_of_tendsto' hb hle

/-! ### The forced-state term (`sec:profile-obstruction`, last paragraph) -/

/-- The state law `(1-t) δ₂ + t δ₁` on the path, for `0 ≤ t ≤ 1`. -/
noncomputable def muTwoOne (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : PMF (Fin 3) :=
  PMF.ofFintype
    (fun v => if v = 0 then 0 else if v = 1 then ENNReal.ofReal t else ENNReal.ofReal (1 - t))
    (by
      rw [Fin.sum_univ_three]
      simp only [ite_true, Fin.isValue, one_ne_zero, ite_false, Fin.reduceEq, zero_add]
      rw [← ENNReal.ofReal_add h0 (by linarith), show t + (1 - t) = 1 by ring,
        ENNReal.ofReal_one])

lemma muTwoOne_zero {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : muTwoOne t h0 h1 0 = 0 := rfl

lemma muTwoOne_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    muTwoOne t h0 h1 1 = ENNReal.ofReal t := rfl

lemma muTwoOne_two {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    muTwoOne t h0 h1 2 = ENNReal.ofReal (1 - t) := rfl

/-- The supported states `1` and `2` are mutually compatible, so `η_α = 0`
(`sec:profile-obstruction`). -/
theorem etaG_muTwoOne_eq_zero (α : ℝ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    etaG α pathRel3 (muTwoOne t h0 h1) = 0 := by
  have hq1 : q (muTwoOne t h0 h1) pathRel3 1 = 0 := by
    rw [q, qE, tsum_fintype, Fin.sum_univ_three]
    simp [pathRel3]
  have hq2 : q (muTwoOne t h0 h1) pathRel3 2 = 0 := by
    rw [q, qE, tsum_fintype, Fin.sum_univ_three]
    simp [pathRel3, muTwoOne_zero]
  rw [etaG, PhiD, tsum_fintype, Fin.sum_univ_three, hq1, hq2, phiE_zero, muTwoOne_zero]
  simp

/-- The forced state `0` is compatible with the fresh mass `t` only: `b(0) = t`
(`sec:profile-obstruction`). -/
theorem rE_zero_muTwoOne {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    rE (muTwoOne t h0 h1) pathRel3 0 = ENNReal.ofReal t := by
  rw [rE, tsum_fintype, Fin.sum_univ_three]
  simp [pathRel3, muTwoOne_zero, muTwoOne_one]

end GraphMarkovMatching.Stopped
