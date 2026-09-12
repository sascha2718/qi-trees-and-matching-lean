/-
The moment estimates of `markov_matching_new_proof.tex`, `sec:restricted-potential`,
`sec:positive-degrees`, and the root contributions of `sec:root-contributions`:

* `moment_le` (`eq:moment`): `∫ W_{u,h} dρ_{s,h} ≤ 1 + α P_h(s,u)`;
* `wZero_le_moment`, `wUnion_le` (`eq:zero-moment`, `eq:zero-union-moment`): the
  weighted zero integrals, the union bound applied to the constant part only;
* `WresD_childMix_le` (`eq:selected-inverse-mixture`): the selected inverse mixture,
  with total coefficient at most the bound `B`;
* `deg_ne_zero_of_delta_zero` (`sec:positive-degrees`): when `δ = 0` every charged
  realisation of any type has positive degree against every type;
* `z_eq_zero_of_delta_zero`, `wZero_eq_zero_of_delta_zero`: the zero events are empty
  when `δ = 0`;
* `root_incompatible_le`, `root_compatible_le`: the averaged root factors `f` and `R_μ`.
-/
import GraphMarkovMatching.Stopped.Paths

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- The restricted weight depends on the target law only through the good degree
(`sec:restricted-potential`): `q = 1 - r` and `W = 𝟙[r > 0] (1-q)^{-α}`. -/
lemma WresD_eq_of_rE_eq {X Y : Type} {α : ℝ} {ρ : PMF X} {R : X → X → Prop} {x : X}
    {ρ' : PMF Y} {R' : Y → Y → Prop} {y : Y} (h : rE ρ R x = rE ρ' R' y) :
    WresD α ρ R x = WresD α ρ' R' y := by
  have hq : ∀ {Z : Type} (ν : PMF Z) (S : Z → Z → Prop) (z : Z),
      qE ν S z = 1 - rE ν S z := fun ν S z =>
    ENNReal.eq_sub_of_add_eq rE_ne_top (by rw [add_comm]; exact rE_add_qE ν S z)
  simp only [WresD, WnnD, q, hq, h]

namespace Model

variable {V I : Type} (M : Model V I)

/-- **The inverse moment** (`eq:moment`): `∫ W_{u,h} dρ_{s,h} ≤ 1 + α P_h(s,u)`. -/
lemma moment_le {α : ℝ} (hα : 1 ≤ α) (s u : I) (h : ℕ) :
    ∑' x, M.rho s h x * M.W α u h x ≤ 1 + ENNReal.ofReal α * M.P α s u h :=
  tsum_WresD_le hα _ _ _

/-- A weighted zero integral is at most the full moment. -/
lemma wZero_le_moment {α : ℝ} (s : I) (D : Set I) (u : I) (h : ℕ) :
    M.wZero α s D u h ≤ ∑' x, M.rho s h x * M.W α u h x := by
  unfold wZero
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : M.ZeroEv D h x
  · rw [if_pos hx]
  · rw [if_neg hx, mul_zero]
    exact zero_le

/-- The weighted zero integral is at most `1 + α P_h(s,u)`. -/
lemma wZero_le_Ufun {α : ℝ} (hα : 1 ≤ α) (s : I) (D : Set I) (u : I) (h : ℕ) :
    M.wZero α s D u h ≤ Ufun α (M.P α s u h) :=
  (M.wZero_le_moment s D u h).trans (M.moment_le hα s u h)

/-- The restricted weight in the inverse-degree form used by the abstract inverse
moment (`sec:restricted-potential`). -/
lemma W_eq_ite (α : ℝ) (u : I) (h : ℕ) (x : FullLab (I × V) h) :
    M.W α u h x
      = (if rE (M.rho u h) (M.sim h) x = 0 then 0 else (rE (M.rho u h) (M.sim h) x) ^ (-α)) := by
  by_cases h0 : rE (M.rho u h) (M.sim h) x = 0
  · rw [if_pos h0, W, WresD, if_pos h0]
  · rw [if_neg h0, W, rE_rpow_neg_eq_WresD _ _ _ h0]

/-- **The weighted union bound** (`eq:zero-union-moment`): the probability union bound is
applied to the constant part of the weight only, the potential part is integrated once. -/
lemma wUnion_le {α : ℝ} (hα : 1 ≤ α) (s : I) (D : Set I) (u : I) (h : ℕ) :
    M.wUnion α s D u h ≤ M.unionMass s D h + ENNReal.ofReal α * M.P α s u h := by
  have key := tsum_wres_restrict_le hα (M.rho s h) (rE (M.rho u h) (M.sim h))
    (fun _ => rE_le_one) {x | M.UnionEv D h x}
  have hL : M.wUnion α s D u h
      = ∑' x, M.rho s h x * (if x ∈ {x | M.UnionEv D h x} then
          (if rE (M.rho u h) (M.sim h) x = 0 then 0
            else (rE (M.rho u h) (M.sim h) x) ^ (-α)) else 0) := by
    unfold wUnion
    refine tsum_congr fun x => ?_
    by_cases hx : M.UnionEv D h x
    · rw [if_pos hx, if_pos (show x ∈ {x | M.UnionEv D h x} from hx), W_eq_ite]
    · rw [if_neg hx, if_neg (show x ∉ {x | M.UnionEv D h x} from hx)]
  have hU : M.unionMass s D h
      = ∑' x, M.rho s h x * (if x ∈ {x | M.UnionEv D h x} then 1 else 0) := by
    unfold unionMass
    refine tsum_congr fun x => ?_
    by_cases hx : M.UnionEv D h x
    · rw [if_pos hx, if_pos (show x ∈ {x | M.UnionEv D h x} from hx)]
    · rw [if_neg hx, if_neg (show x ∉ {x | M.UnionEv D h x} from hx)]
  have hP : ∑' x, M.rho s h x * (if x ∈ {x | M.UnionEv D h x} then
          (if rE (M.rho u h) (M.sim h) x = 0 then 0
            else phiE α (1 - (rE (M.rho u h) (M.sim h) x).toReal)) else 0)
      ≤ M.P α s u h := by
    unfold P PhiDres
    refine ENNReal.tsum_le_tsum fun x => ?_
    refine mul_le_mul_right ?_ _
    by_cases hx : x ∈ {x | M.UnionEv D h x}
    · rw [if_pos hx]
      by_cases h0 : rE (M.rho u h) (M.sim h) x = 0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0, toReal_rE_eq, sub_sub_cancel]
    · rw [if_neg hx]
      exact zero_le
  rw [hL, hU]
  exact key.trans (add_le_add_right (mul_le_mul_right hP _) _)

/-- **The weighted union bound over a finite phase class**: at most `T Z + α P_h(s,u)`
when the union runs over at most `T` types each of zero mass at most `Z`. -/
lemma wUnion_le_card {α : ℝ} (hα : 1 ≤ α) (s : I) (D : Finset I) (u : I) (h : ℕ)
    {Zm : ℝ≥0∞} (hz : ∀ t ∈ D, M.z s t h ≤ Zm) :
    M.wUnion α s (↑D) u h ≤ D.card * Zm + ENNReal.ofReal α * M.P α s u h :=
  (M.wUnion_le hα s (↑D) u h).trans
    (add_le_add_left (M.unionMass_le_card_mul s D h hz) _)

/-- **The selected inverse mixture** (`eq:selected-inverse-mixture`): on a source child
pair with states in `V_μ`, the restricted inverse mixture degree is at most the selected
sum of inverse probabilities times restricted inverse component degrees. -/
lemma WresD_childMix_le {α : ℝ} (hα : 0 ≤ α) (Sel : Selection M) (t : I) (h : ℕ)
    (p : FullLab (I × V) h × FullLab (I × V) h)
    (hp1 : StatesIn M.Vmu h p.1) (hp2 : StatesIn M.Vmu h p.2) :
    WresD α (M.childMix t h) (SquareRel (M.sim h)) p
      ≤ ∑ j ∈ Sel.J t, (M.π t j) ^ (-α)
          * WresD α (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) p := by
  by_cases hbar : rE (M.childMix t h) (SquareRel (M.sim h)) p = 0
  · rw [WresD, if_pos hbar]
    exact zero_le
  · obtain ⟨j, hj, hjpos⟩ := Sel.positive t h p hp1 hp2 hbar
    have hπ : M.π t j ≠ 0 := Sel.charged t j hj
    have hmin : M.π t j * rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) p
        ≤ rE (M.childMix t h) (SquareRel (M.sim h)) p :=
      mul_rE_le_rE_bind (M.π t) (fun j => prodPMF (M.rho j.1 h) (M.rho j.2 h)) _ p j
    have hstep : WresD α (M.childMix t h) (SquareRel (M.sim h)) p
        ≤ (M.π t j) ^ (-α)
          * WresD α (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) p := by
      rw [← rE_rpow_neg_eq_WresD _ _ _ hbar, ← rE_rpow_neg_eq_WresD _ _ _ hjpos,
        ← ENNReal.mul_rpow_of_ne_zero hπ hjpos (-α)]
      exact rpow_neg_antitone hα hmin
    refine hstep.trans ?_
    exact Finset.single_le_sum
      (f := fun j => (M.π t j) ^ (-α)
        * WresD α (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) p)
      (fun _ _ => zero_le) hj

/-- **The restricted pair weight** splits along a successful pairing: at most the sum over
the two pairings of the products of the child weights. -/
lemma WresD_pair_le {α : ℝ} (hα : 0 ≤ α) (a b : I) (h : ℕ)
    (p : FullLab (I × V) h × FullLab (I × V) h) :
    WresD α (prodPMF (M.rho a h) (M.rho b h)) (SquareRel (M.sim h)) p
      ≤ M.W α a h p.1 * M.W α b h p.2 + M.W α b h p.1 * M.W α a h p.2 :=
  WresD_square_le_sum hα _ _ _ _

/-! ### Positivity when `δ = 0` (`sec:positive-degrees`) -/

/-- When `δ = 0` every charged fresh state is compatible with `0` (`sec:positive-degrees`). -/
lemma R_zero_of_delta_zero (hδ : M.delta = 0) {v : V} (hv : M.μ v ≠ 0) : M.R M.zero v := by
  rw [delta, qE, ENNReal.tsum_eq_zero] at hδ
  by_contra hR
  have := hδ v
  rw [if_neg hR] at this
  exact hv this

/-- When `δ = 0` every realised state is compatible with `0` (`sec:positive-degrees`). -/
lemma R_zero_of_mem_Vmu (hc : M.IsCompat) (hδ : M.delta = 0) {v : V} (hv : v ∈ M.Vmu) :
    M.R v M.zero := by
  rcases hv with hv | hv
  · exact hc.symm _ _ (M.R_zero_of_delta_zero hδ hv)
  · rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact hc.refl _

/-- When `δ = 0` the compatible root mass `b(0)` is one, in particular positive
(`sec:positive-degrees`). -/
lemma rE_zero_ne_zero_of_delta_zero (hδ : M.delta = 0) : rE M.μ M.R M.zero ≠ 0 := by
  have h := rE_add_qE M.μ M.R M.zero
  rw [delta] at hδ
  rw [hδ, add_zero] at h
  rw [h]
  exact one_ne_zero

/-- **Positivity when `δ = 0`** (`sec:positive-degrees`): every charged realisation of any
type has positive degree against every type, by induction on the height. -/
lemma deg_ne_zero_of_delta_zero (hc : M.IsCompat) (hδ : M.delta = 0) :
    ∀ (h : ℕ) (s t : I) (x : FullLab (I × V) h), M.rho s h x ≠ 0 → M.deg t h x ≠ 0 := by
  have hb0 := M.rE_zero_ne_zero_of_delta_zero hδ
  intro h
  induction h with
  | zero =>
    intro s t x hx
    have hx' : M.rho s 0 (leaf x) ≠ 0 := hx
    obtain ⟨-, hroot⟩ := (M.rho_zero_ne_zero_iff s x).mp hx'
    have hv : x.2 ∈ M.Vmu := M.rootLaw_mem_Vmu hroot
    show M.deg t 0 (leaf x) ≠ 0
    rw [deg_zero]
    exact M.rootDeg_ne_zero hc hb0 t hv (M.R_zero_of_mem_Vmu hc hδ hv)
  | succ h ih =>
    intro s t x hx
    have hx' : M.rho s (h + 1) (branch x.1 (x.2.1, x.2.2)) ≠ 0 := hx
    obtain ⟨-, hroot, j, -, h1, h2⟩ :=
      (M.rho_succ_ne_zero_iff s h x.1 (x.2.1, x.2.2)).mp hx'
    show M.deg t (h + 1) (branch x.1 (x.2.1, x.2.2)) ≠ 0
    rw [deg_succ]
    have hv : x.1.2 ∈ M.Vmu := M.rootLaw_mem_Vmu hroot
    refine mul_ne_zero (M.rootDeg_ne_zero hc hb0 t hv (M.R_zero_of_mem_Vmu hc hδ hv)) ?_
    obtain ⟨j', hj'⟩ := (M.π t).support_nonempty
    rw [PMF.mem_support_iff] at hj'
    have hd1 : rE (M.rho j'.1 h) (M.sim h) x.2.1 ≠ 0 := ih j.1 j'.1 x.2.1 h1
    have hd2 : rE (M.rho j'.2 h) (M.sim h) x.2.2 ≠ 0 := ih j.2 j'.2 x.2.2 h2
    intro h0
    have hle : M.π t j' * (rE (M.rho j'.1 h) (M.sim h) x.2.1
          * rE (M.rho j'.2 h) (M.sim h) x.2.2)
        ≤ rE (M.childMix t h) (SquareRel (M.sim h)) (x.2.1, x.2.2) :=
      (mul_le_mul_right (straight_le_rE_square _ _ _ _ _) _).trans
        (mul_rE_le_rE_bind (M.π t) (fun j => prodPMF (M.rho j.1 h) (M.rho j.2 h)) _ _ j')
    rw [h0] at hle
    have hzero := le_antisymm hle (zero_le)
    rcases mul_eq_zero.mp hzero with hπ | hprod
    · exact hj' hπ
    · rcases mul_eq_zero.mp hprod with hz1 | hz2
      · exact hd1 hz1
      · exact hd2 hz2

/-- When `δ = 0` the zero masses vanish. -/
lemma z_eq_zero_of_delta_zero (hc : M.IsCompat) (hδ : M.delta = 0) (s t : I) (h : ℕ) :
    M.z s t h = 0 := by
  rw [z, zMass, ENNReal.tsum_eq_zero]
  intro x
  by_cases hx : M.rho s h x = 0
  · rw [hx, zero_mul]
  · have hd : rE (M.rho t h) (M.sim h) x ≠ 0 := M.deg_ne_zero_of_delta_zero hc hδ h s t x hx
    rw [if_neg hd, mul_zero]

/-- When `δ = 0` the weighted zero integrals vanish for nonempty `D`. -/
lemma wZero_eq_zero_of_delta_zero (hc : M.IsCompat) (hδ : M.delta = 0) {α : ℝ} (s : I)
    {D : Set I} (hD : D.Nonempty) (u : I) (h : ℕ) : M.wZero α s D u h = 0 := by
  rw [wZero, ENNReal.tsum_eq_zero]
  intro x
  by_cases hx : M.rho s h x = 0
  · rw [hx, zero_mul]
  · have hz : ¬ M.ZeroEv D h x := by
      intro hz
      obtain ⟨t, ht⟩ := hD
      exact M.deg_ne_zero_of_delta_zero hc hδ h s t x hx (hz t ht)
    rw [if_neg hz, mul_zero]

/-- When `δ = 0`, fresh positivity holds. -/
lemma freshPositive_of_delta_zero (hc : M.IsCompat) (hδ : M.delta = 0) : M.FreshPositive :=
  fun h f f' x _ _ hx => M.deg_ne_zero_of_delta_zero hc hδ h f f' x hx

/-! ### The root contributions (`sec:root-contributions`) -/

/-- **The height-zero zero event**: a source root compatible with `0` has positive degree
against every type, so the zero event at height zero against a nonempty `D` is contained
in the incompatible-root event. -/
lemma zeroEv_zero_imp (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) {D : Set I}
    (hD : D.Nonempty) {s : I × V} (hs : s.2 ∈ M.Vmu) (hz : M.ZeroEv D 0 (leaf s)) :
    ¬ M.R s.2 M.zero := by
  intro hR
  obtain ⟨t, ht⟩ := hD
  have hdeg := hz t ht
  rw [deg_zero] at hdeg
  exact M.rootDeg_ne_zero hc hb0 t hs hR hdeg

/-- The restricted weight of a forced normaliser is the compatibility indicator against
`0`: weight one at a compatible root, zero at an incompatible one
(`sec:root-contributions`). -/
lemma WresD_rootLaw_forced (α : ℝ) {u : I} (hu : ¬ M.fresh u) (v : V) :
    WresD α (M.rootLaw u) M.R v = if M.R v M.zero then 1 else 0 := by
  have hr : rE (M.rootLaw u) M.R v = if M.R v M.zero then 1 else 0 := by
    rw [rootLaw_forced M hu, rE_pure]
  by_cases hv : M.R v M.zero
  · rw [if_pos hv] at hr ⊢
    rw [← rE_rpow_neg_eq_WresD _ _ _ (by rw [hr]; exact one_ne_zero), hr, ENNReal.one_rpow]
  · rw [if_neg hv] at hr ⊢
    rw [WresD, if_pos hr]

/-- **The incompatible-root factor**: the root-state average of the normalising weight
over roots incompatible with `0` is at most `f` for a fresh normaliser and zero for a
forced one. -/
lemma root_incompatible_le {α : ℝ} (hc : M.IsCompat) (s u : I) :
    ∑' v, M.rootLaw s v * (if M.R v M.zero then 0 else WresD α (M.rootLaw u) M.R v)
      ≤ if M.fresh u then M.fRoot α else 0 := by
  by_cases hu : M.fresh u
  · rw [if_pos hu, rootLaw_fresh M hu]
    by_cases hs : M.fresh s
    · rw [rootLaw_fresh M hs, fRoot]
    · rw [rootLaw_forced M hs, tsum_pure_mul, if_pos (hc.refl _)]
      exact zero_le
  · rw [if_neg hu]
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun v => ?_)
    by_cases hv : M.R v M.zero
    · rw [if_pos hv, mul_zero]
    · rw [if_neg hv, WresD_rootLaw_forced M α hu, if_neg hv, mul_zero]

/-- **The compatible-root factor**: the root-state average of the normalising weight over
roots compatible with `0` is at most `R_μ`, for every source and normalising type. -/
lemma root_compatible_le {α : ℝ} (hc : M.IsCompat) (s u : I) :
    ∑' v, M.rootLaw s v * (if M.R v M.zero then WresD α (M.rootLaw u) M.R v else 0)
      ≤ M.RmuC α := by
  by_cases hu : M.fresh u
  · rw [rootLaw_fresh M hu]
    by_cases hs : M.fresh s
    · rw [rootLaw_fresh M hs]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    · rw [rootLaw_forced M hs, tsum_pure_mul, if_pos (hc.refl _)]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
  · calc ∑' v, M.rootLaw s v * (if M.R v M.zero then WresD α (M.rootLaw u) M.R v else 0)
        ≤ ∑' v, M.rootLaw s v := by
          refine ENNReal.tsum_le_tsum fun v => ?_
          by_cases hv : M.R v M.zero
          · rw [if_pos hv, WresD_rootLaw_forced M α hu, if_pos hv, mul_one]
          · rw [if_neg hv, mul_zero]
            exact zero_le
      _ = 1 := (M.rootLaw s).tsum_coe
      _ ≤ M.RmuC α := M.one_le_RmuC α

/-- The restricted root weight is the restricted weight of the root factor. -/
lemma W_zero (α : ℝ) (u : I) (s : I × V) :
    M.W α u 0 (leaf s) = WresD α (M.rootLaw u) M.R s.2 :=
  WresD_eq_of_rE_eq (M.deg_zero u s)

/-- **The weight recursion**: the restricted weight of a branch is the restricted root
weight times the restricted child-pair mixture weight. -/
lemma W_succ (α : ℝ) (u : I) (h : ℕ) (s : I × V)
    (p : FullLab (I × V) h × FullLab (I × V) h) :
    M.W α u (h + 1) (branch s p)
      = WresD α (M.rootLaw u) M.R s.2 * WresD α (M.childMix u h) (SquareRel (M.sim h)) p := by
  have hd : rE (M.rho u (h + 1)) (M.sim (h + 1)) (branch s p)
      = rE (M.rootLaw u) M.R s.2 * rE (M.childMix u h) (SquareRel (M.sim h)) p :=
    M.deg_succ u h s p
  by_cases h1 : rE (M.rootLaw u) M.R s.2 = 0
  · have hz : rE (M.rho u (h + 1)) (M.sim (h + 1)) (branch s p) = 0 := by
      rw [hd, h1, zero_mul]
    unfold W WresD
    rw [if_pos hz, if_pos h1, zero_mul]
  · by_cases h2 : rE (M.childMix u h) (SquareRel (M.sim h)) p = 0
    · have hz : rE (M.rho u (h + 1)) (M.sim (h + 1)) (branch s p) = 0 := by
        rw [hd, h2, mul_zero]
      unfold W WresD
      rw [if_pos hz, if_pos h2, mul_zero]
    · have hz : rE (M.rho u (h + 1)) (M.sim (h + 1)) (branch s p) ≠ 0 := by
        rw [hd]
        exact mul_ne_zero h1 h2
      rw [W, ← rE_rpow_neg_eq_WresD _ _ _ hz, ← rE_rpow_neg_eq_WresD _ _ _ h1,
        ← rE_rpow_neg_eq_WresD _ _ _ h2, hd, ENNReal.mul_rpow_of_ne_zero h1 h2]

/-- The incompatible-root mass of a root law is at most `δ`. -/
lemma rootLaw_incompatible_le (hc : M.IsCompat) (s : I) :
    ∑' v, M.rootLaw s v * (if M.R v M.zero then 0 else 1) ≤ M.delta := by
  by_cases hs : M.fresh s
  · rw [rootLaw_fresh M hs, delta, qE]
    refine le_of_eq (tsum_congr fun v => ?_)
    by_cases hv : M.R v M.zero
    · rw [if_pos hv, mul_zero, if_pos (hc.symm _ _ hv)]
    · rw [if_neg hv, mul_one, if_neg (fun h => hv (hc.symm _ _ h))]
  · rw [rootLaw_forced M hs, tsum_pure_mul, if_pos (hc.refl _)]
    exact zero_le

end Model

end GraphMarkovMatching.Stopped
