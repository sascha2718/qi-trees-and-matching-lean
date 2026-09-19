/-
The restricted potentials, zero events, phases, possible paths, stopping predicate and
transition selections of `arbitrary_offspring_matching.tex` (`sec:restricted-potential`,
`sec:finite-hypotheses`, `sec:unweighted`):

* `P`, `z`, `failProb`, `W`: the restricted potential `P_h(s,t)`, the zero mass
  `ρ_{s,h}{r_{t,h} = 0}`, the failure probability, the restricted weight `W_{t,h}`;
* `ZeroEv`, `UnionEv`, `zeroMass`, `unionMass`, `wZero`, `wUnion`: the zero events against
  a set of types and their plain and weighted masses;
* `Phase`, `child`, `children`, `reach`, `IsPath`, `Stops`, `CommonReturns`,
  `FreshPositive`: the phase maps, possible paths, and the two finite-type hypotheses;
* `Selection`, `Selection.inverseSum`, `Selection.full`: the transition selections and the
  bound `B` of `eq:transition-budget`;
* `SHe`, `GHe`, `Ufun`, `Efun`, `Qfun`, `Cmix`: the explicit scalar functions of
  `eq:explicit-zero-bound`, `eq:explicit-weighted-error` and `sec:averaging`, in `ℝ≥0∞`.

In formal field and lemma names, `charged` means simply "has nonzero mass
under the relevant PMF".  The prose below usually says "positive-mass" to
make that meaning explicit.
-/
import GraphMarkovMatching.Stopped.Constants

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

namespace Model

variable {V I : Type} (M : Model V I)

/-! ### Restricted potentials, zero masses, failure -/

/-- The restricted potential `P_h(s,t) = ∫_{r_{t,h} > 0} φ_α(1 - r_{t,h}) dρ_{s,h}`. -/
noncomputable def P (α : ℝ) (s t : I) (h : ℕ) : ℝ≥0∞ :=
  PhiDres α (M.rho s h) (M.rho t h) (M.sim h)

/-- The zero mass `ρ_{s,h}{r_{t,h} = 0}`. -/
noncomputable def z (s t : I) (h : ℕ) : ℝ≥0∞ :=
  zMass (M.rho s h) (M.rho t h) (M.sim h)

/-- The failure probability `P(M_h(s,t)^c) = ∑_x ρ_{s,h}(x) q_{ρ_{t,h}}(x)`. -/
noncomputable def failProb (s t : I) (h : ℕ) : ℝ≥0∞ :=
  failureD (M.rho s h) (M.rho t h) (M.sim h)

/-- The restricted weight `W_{t,h}(x)`. -/
noncomputable def W (α : ℝ) (t : I) (h : ℕ) (x : FullLab (I × V) h) : ℝ≥0∞ :=
  WresD α (M.rho t h) (M.sim h) x

/-- The failure probability is at most the zero mass plus the restricted potential
(`sec:completion`). -/
lemma failProb_le (α : ℝ) (hα : 0 ≤ α) (s t : I) (h : ℕ) :
    M.failProb s t h ≤ M.P α s t h + M.z s t h :=
  failureD_le_PhiDres_add_zMass α hα _ _ _

/-- The failure probability is the product-law mass of the non-matching pairs. -/
lemma failProb_eq_prodPMF (s t : I) (h : ℕ) :
    M.failProb s t h = ∑' p : FullLab (I × V) h × FullLab (I × V) h,
      prodPMF (M.rho s h) (M.rho t h) p * (if M.sim h p.1 p.2 then 0 else 1) := by
  rw [failProb, failureD, ENNReal.tsum_prod']
  refine tsum_congr fun x => ?_
  rw [qE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  simp only [prodPMF_apply]
  split_ifs <;> simp

/-- The zero event against every type in `D`: `r_{t,h}(x) = 0` for all `t ∈ D`. -/
def ZeroEv (D : Set I) (h : ℕ) (x : FullLab (I × V) h) : Prop := ∀ t ∈ D, M.deg t h x = 0

/-- The union of zero events over `D`: `r_{t,h}(x) = 0` for some `t ∈ D`. -/
def UnionEv (D : Set I) (h : ℕ) (x : FullLab (I × V) h) : Prop := ∃ t ∈ D, M.deg t h x = 0

/-- The mass of the zero event `ρ_{s,h}{r_{t,h} = 0 for every t ∈ D}`. -/
noncomputable def zeroMass (s : I) (D : Set I) (h : ℕ) : ℝ≥0∞ :=
  ∑' x, M.rho s h x * (if M.ZeroEv D h x then 1 else 0)

/-- The mass of the union of zero events over `D`. -/
noncomputable def unionMass (s : I) (D : Set I) (h : ℕ) : ℝ≥0∞ :=
  ∑' x, M.rho s h x * (if M.UnionEv D h x then 1 else 0)

/-- The weighted zero integral `∫ 𝟙{r_{t,h} = 0 for all t ∈ D} W_{u,h} dρ_{s,h}`. -/
noncomputable def wZero (α : ℝ) (s : I) (D : Set I) (u : I) (h : ℕ) : ℝ≥0∞ :=
  ∑' x, M.rho s h x * (if M.ZeroEv D h x then M.W α u h x else 0)

/-- The weighted union integral `∫ 𝟙{r_{t,h} = 0 for some t ∈ D} W_{u,h} dρ_{s,h}`. -/
noncomputable def wUnion (α : ℝ) (s : I) (D : Set I) (u : I) (h : ℕ) : ℝ≥0∞ :=
  ∑' x, M.rho s h x * (if M.UnionEv D h x then M.W α u h x else 0)

/-- The zero mass against a singleton is the zero mass `z` of `sec:restricted-potential`. -/
lemma zeroMass_singleton (s t : I) (h : ℕ) : M.zeroMass s {t} h = M.z s t h := by
  rw [zeroMass, z, zMass]
  refine tsum_congr fun x => ?_
  simp [ZeroEv, deg]

/-- Enlarging the target set shrinks the zero event (`sec:unweighted`). -/
lemma zeroMass_mono {s : I} {D D' : Set I} (hD : D ⊆ D') (h : ℕ) :
    M.zeroMass s D' h ≤ M.zeroMass s D h := by
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases hx : M.ZeroEv D' h x
  · have hx' : M.ZeroEv D h x := fun t ht => hx t (hD ht)
    rw [if_pos hx, if_pos hx']
  · rw [if_neg hx]
    exact zero_le

/-- Enlarging the target set enlarges the union of zero events (`sec:unweighted`). -/
lemma unionMass_mono {s : I} {D D' : Set I} (hD : D ⊆ D') (h : ℕ) :
    M.unionMass s D h ≤ M.unionMass s D' h := by
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases hx : M.UnionEv D h x
  · obtain ⟨t, ht, h0⟩ := hx
    have hx' : M.UnionEv D' h x := ⟨t, hD ht, h0⟩
    rw [if_pos ⟨t, ht, h0⟩, if_pos hx']
  · rw [if_neg hx]
    exact zero_le

/-- The weighted zero integral is antitone in the target set (`sec:unweighted`). -/
lemma wZero_mono {α : ℝ} {s u : I} {D D' : Set I} (hD : D ⊆ D') (h : ℕ) :
    M.wZero α s D' u h ≤ M.wZero α s D u h := by
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases hx : M.ZeroEv D' h x
  · have hx' : M.ZeroEv D h x := fun t ht => hx t (hD ht)
    rw [if_pos hx, if_pos hx']
  · rw [if_neg hx]
    exact zero_le

/-- The weighted union integral is monotone in the target set (`eq:zero-union-moment`). -/
lemma wUnion_mono {α : ℝ} {s u : I} {D D' : Set I} (hD : D ⊆ D') (h : ℕ) :
    M.wUnion α s D u h ≤ M.wUnion α s D' u h := by
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases hx : M.UnionEv D h x
  · obtain ⟨t, ht, h0⟩ := hx
    have hx' : M.UnionEv D' h x := ⟨t, hD ht, h0⟩
    rw [if_pos ⟨t, ht, h0⟩, if_pos hx']
  · rw [if_neg hx]
    exact zero_le

/-- The mass of a finite union of zero events is at most the sum of the zero masses. -/
lemma unionMass_le_sum (s : I) (D : Finset I) (h : ℕ) :
    M.unionMass s (↑D) h ≤ ∑ t ∈ D, M.z s t h := by
  induction D using Finset.induction_on with
  | empty => simp [unionMass, UnionEv]
  | insert a D ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans ?_ (add_le_add (le_of_eq (M.zeroMass_singleton s a h)) ih)
    rw [zeroMass, unionMass, unionMass, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← mul_add]
    refine mul_le_mul_right ?_ _
    by_cases hx : M.UnionEv (↑(insert a D)) h x
    · rw [if_pos hx]
      obtain ⟨t, ht, h0⟩ := hx
      rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ht
      rcases ht with rfl | ht
      · have hz : M.ZeroEv {t} h x := fun t' ht' => by
          rw [Set.mem_singleton_iff] at ht'
          rw [ht']
          exact h0
        rw [if_pos hz]
        exact le_add_right le_rfl
      · have hu : M.UnionEv (↑D) h x := ⟨t, ht, h0⟩
        rw [if_pos hu]
        exact le_add_left le_rfl
    · rw [if_neg hx]
      exact zero_le

/-- The mass of a union of at most `T` zero events, each of mass at most `Z`, is at most
`T Z`. -/
lemma unionMass_le_card_mul (s : I) (D : Finset I) (h : ℕ) {Zm : ℝ≥0∞}
    (hz : ∀ t ∈ D, M.z s t h ≤ Zm) : M.unionMass s (↑D) h ≤ D.card * Zm := by
  refine (M.unionMass_le_sum s D h).trans ?_
  rw [← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul D _ _ hz

/-! ### Phases, paths, and the hypotheses -/

/-- A phase map (`sec:finite-hypotheses`): fresh types have phase zero and every child in
a charged transition has phase one greater than its parent. -/
structure Phase (M : Model V I) (g : ℕ) where
  θ : I → ZMod g
  fresh_zero : ∀ t, M.fresh t → θ t = 0
  child : ∀ t j, M.π t j ≠ 0 → θ j.1 = θ t + 1 ∧ θ j.2 = θ t + 1

/-- The trivial phase map, `g = 1`. -/
def Phase.trivial : Phase M 1 where
  θ := fun _ => 0
  fresh_zero := fun _ _ => Subsingleton.elim _ _
  child := fun _ _ _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The number of types of phase `i`. -/
noncomputable def Phase.count {M : Model V I} [Fintype I] {g : ℕ} (Θ : Phase M g)
    (i : ZMod g) : ℕ :=
  (Finset.univ.filter fun t => Θ.θ t = i).card

/-- The finite set of types of phase `i`. -/
noncomputable def Phase.cls {M : Model V I} [Fintype I] {g : ℕ} (Θ : Phase M g) (i : ZMod g) :
    Finset I :=
  Finset.univ.filter fun t => Θ.θ t = i

lemma Phase.card_cls {M : Model V I} [Fintype I] {g : ℕ} (Θ : Phase M g) (i : ZMod g) :
    (Θ.cls i).card = Θ.count i := rfl

/-- A possible child: some charged transition produces it. -/
def child (t t' : I) : Prop := ∃ j, M.π t j ≠ 0 ∧ (t' = j.1 ∨ t' = j.2)

/-- The possible children of a set of types. -/
def children (D : Set I) : Set I := {t' | ∃ t ∈ D, M.child t t'}

/-- The types reachable from `D` by possible paths of length `n`. -/
def reach (D : Set I) : ℕ → Set I
  | 0 => D
  | n + 1 => children M (reach D n)

lemma reach_zero (D : Set I) : M.reach D 0 = D := rfl

lemma reach_succ (D : Set I) (n : ℕ) : M.reach D (n + 1) = M.children (M.reach D n) := rfl

/-- A possible type path of length `n`: successive possible children. -/
def IsPath (p : ℕ → I) (n : ℕ) : Prop := ∀ i < n, M.child (p i) (p (i + 1))

/-- **The stopping predicate**: every possible source path of length `n` from `s` passes,
at some depth `k ≤ n`, a fresh type at which some type reachable from `D` in `k` steps is
fresh. -/
def Stops (s : I) (D : Set I) (n : ℕ) : Prop :=
  ∀ p : ℕ → I, p 0 = s → M.IsPath p n → ∃ k ≤ n, M.fresh (p k) ∧ ∃ f ∈ M.reach D k, M.fresh f

/-- **Common returns** (`sec:finite-hypotheses`): from any two equal-phase types, every
possible source path reaches a fresh type at a depth at most `H` at which some possible
target path is fresh as well. -/
def CommonReturns {g : ℕ} (Θ : Phase M g) (H : ℕ) : Prop :=
  ∀ s t, Θ.θ s = Θ.θ t → M.Stops s {t} H

/-- **Fresh positivity** (`sec:finite-hypotheses`): every charged realisation of a fresh
type has positive degree against every fresh type. -/
def FreshPositive : Prop :=
  ∀ (h : ℕ) (f f' : I) (x : FullLab (I × V) h),
    M.fresh f → M.fresh f' → M.rho f h x ≠ 0 → M.deg f' h x ≠ 0

/-- The zero event against a fresh target is empty for a fresh source under fresh
positivity, so the weighted zero integral vanishes whenever `D` holds a fresh type. -/
lemma wZero_eq_zero_of_fresh {α : ℝ} (hFP : M.FreshPositive) {s f : I} (hs : M.fresh s)
    (hf : M.fresh f) {D : Set I} (hfD : f ∈ D) (u : I) (h : ℕ) :
    M.wZero α s D u h = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : M.rho s h x = 0
  · rw [hx, zero_mul]
  · have hne : ¬ M.ZeroEv D h x := fun hz => hFP h s f x hs hf hx (hz f hfD)
    rw [if_neg hne, mul_zero]

/-- The zero mass against a fresh target is zero for a fresh source under fresh
positivity. -/
lemma zeroMass_eq_zero_of_fresh (hFP : M.FreshPositive) {s f : I} (hs : M.fresh s)
    (hf : M.fresh f) {D : Set I} (hfD : f ∈ D) (h : ℕ) :
    M.zeroMass s D h = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : M.rho s h x = 0
  · rw [hx, zero_mul]
  · have hne : ¬ M.ZeroEv D h x := fun hz => hFP h s f x hs hf hx (hz f hfD)
    rw [if_neg hne, mul_zero]

/-- A nonempty set of types has a possible child, since every kernel `π_t` is charged
somewhere (`sec:finite-hypotheses`). -/
lemma children_nonempty {D : Set I} (hD : D.Nonempty) : (M.children D).Nonempty := by
  obtain ⟨t, ht⟩ := hD
  obtain ⟨j, hj⟩ := (M.π t).support_nonempty
  exact ⟨j.1, t, ht, j, (PMF.mem_support_iff _ _).mp hj, Or.inl rfl⟩

/-- Every reachable set from a nonempty set of types is nonempty (`sec:finite-hypotheses`). -/
lemma reach_nonempty {D : Set I} (hD : D.Nonempty) (n : ℕ) : (M.reach D n).Nonempty := by
  induction n with
  | zero => exact hD
  | succ n ih => exact M.children_nonempty ih

/-- The possible children are monotone in the set of types (`sec:finite-hypotheses`). -/
lemma children_mono {D D' : Set I} (hD : D ⊆ D') : M.children D ⊆ M.children D' := by
  rintro t' ⟨t, ht, hc⟩
  exact ⟨t, hD ht, hc⟩

/-- The reachable sets are monotone in the initial set (`sec:finite-hypotheses`). -/
lemma reach_mono {D D' : Set I} (hD : D ⊆ D') (n : ℕ) : M.reach D n ⊆ M.reach D' n := by
  induction n with
  | zero => exact hD
  | succ n ih => exact M.children_mono ih

/-- Reaching `n` steps from the children is reaching `n + 1` steps from the parents
(`sec:finite-hypotheses`). -/
lemma reach_children (D : Set I) (n : ℕ) :
    M.reach (M.children D) n = M.reach D (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show M.children (M.reach (M.children D) n) = M.children (M.reach D (n + 1))
    rw [ih]

lemma reach_singleton_subset {t : I} {D : Set I} (ht : t ∈ D) (n : ℕ) :
    M.reach {t} n ⊆ M.reach D n :=
  M.reach_mono (Set.singleton_subset_iff.mpr ht) n

/-- The stopping predicate is monotone in the target set. -/
lemma Stops.mono {M : Model V I} {s : I} {D D' : Set I} (hD : D ⊆ D') {n : ℕ}
    (h : M.Stops s D n) :
    M.Stops s D' n := by
  intro p hp0 hp
  obtain ⟨k, hk, hf, f, hfD, hff⟩ := h p hp0 hp
  exact ⟨k, hk, hf, f, M.reach_mono hD k hfD, hff⟩

/-- A nonempty target set of a stopping pair contains a stopping singleton: any member. -/
lemma stops_of_mem {M : Model V I} {s t : I} {D : Set I} (ht : t ∈ D) {n : ℕ}
    (h : M.Stops s {t} n) :
    M.Stops s D n :=
  h.mono (Set.singleton_subset_iff.mpr ht)

/-- **The descent of the stopping predicate**: unless the pair already stops at depth
zero, every possible child of the source stops against the children of the targets one
step earlier. -/
lemma Stops.succ {M : Model V I} {s : I} {D : Set I} {n : ℕ} (h : M.Stops s D (n + 1))
    (h0 : ¬ (M.fresh s ∧ ∃ f ∈ D, M.fresh f)) {s' : I} (hs' : M.child s s') :
    M.Stops s' (M.children D) n := by
  intro p' hp0 hp
  let p : ℕ → I := fun i => Nat.casesOn i s p'
  have hp' : M.IsPath p (n + 1) := by
    intro i hi
    cases i with
    | zero =>
      show M.child s (p' 0)
      rw [hp0]
      exact hs'
    | succ i => exact hp i (Nat.lt_of_succ_lt_succ hi)
  obtain ⟨k, hk, hf, f, hfD, hff⟩ := h p rfl hp'
  cases k with
  | zero => exact (h0 ⟨hf, f, hfD, hff⟩).elim
  | succ k =>
    refine ⟨k, Nat.le_of_succ_le_succ hk, hf, f, ?_, hff⟩
    rw [M.reach_children]
    exact hfD

/-- Stopping at depth zero is the fresh-fresh case. -/
lemma Stops.zero {M : Model V I} {s : I} {D : Set I} (h : M.Stops s D 0) :
    M.fresh s ∧ ∃ f ∈ D, M.fresh f := by
  obtain ⟨k, hk, hf, f, hfD, hff⟩ :=
    h (fun _ => s) rfl (fun i hi => absurd hi (Nat.not_lt_zero i))
  obtain rfl : k = 0 := Nat.le_zero.mp hk
  exact ⟨hf, f, hfD, hff⟩

/-- The children of equal-phase types have the successor phase. -/
lemma Phase.children_subset_cls {M : Model V I} [Fintype I] {g : ℕ} (Θ : Phase M g)
    {D : Set I} {i : ZMod g}
    (hD : ∀ t ∈ D, Θ.θ t = i) : M.children D ⊆ ↑(Θ.cls (i + 1)) := by
  rintro t' ⟨t, ht, j, hj, rfl | rfl⟩
  · rw [Finset.mem_coe, Phase.cls, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [(Θ.child t j hj).1, hD t ht]⟩
  · rw [Finset.mem_coe, Phase.cls, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [(Θ.child t j hj).2, hD t ht]⟩

/-- A possible child has the successor phase (`sec:finite-hypotheses`). -/
lemma Phase.child_eq {M : Model V I} {g : ℕ} (Θ : Phase M g) {t t' : I} (h : M.child t t') :
    Θ.θ t' = Θ.θ t + 1 := by
  obtain ⟨j, hj, rfl | rfl⟩ := h
  · exact (Θ.child t j hj).1
  · exact (Θ.child t j hj).2

/-! ### Transition selections (`eq:transition-budget`) -/

/-- A transition selection: for every target type a nonempty finite set of positive-mass
child pairs such that, for every source child pair with states in `V_μ`, positive degree against
the full child-pair mixture implies positive degree against some selected component. -/
structure Selection (M : Model V I) where
  J : I → Finset (I × I)
  nonempty : ∀ t, (J t).Nonempty
  charged : ∀ t, ∀ j ∈ J t, M.π t j ≠ 0
  positive : ∀ (t : I) (h : ℕ) (p : FullLab (I × V) h × FullLab (I × V) h),
    StatesIn M.Vmu h p.1 → StatesIn M.Vmu h p.2 →
    rE (M.childMix t h) (SquareRel (M.sim h)) p ≠ 0 →
    ∃ j ∈ J t, rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) p ≠ 0

/-- The inverse-probability sum `∑_{j ∈ J_t} π_t(j)^{-α}` of a type. -/
noncomputable def Selection.inverseSum {M : Model V I} (Sel : Selection M) (α : ℝ) (t : I) :
    ℝ≥0∞ :=
  ∑ j ∈ Sel.J t, (M.π t j) ^ (-α)

/-- The inverse-probability sum is at least one. -/
lemma Selection.one_le_inverseSum {M : Model V I} (Sel : Selection M) {α : ℝ} (hα : 0 ≤ α)
    (t : I) :
    1 ≤ Sel.inverseSum α t := by
  obtain ⟨j, hj⟩ := Sel.nonempty t
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => zero_le) hj)
  calc (1 : ℝ≥0∞) = (M.π t j) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
    _ ≤ (M.π t j) ^ (-α) :=
      ENNReal.rpow_le_rpow_of_exponent_ge (PMF.coe_le_one _ _) (by linarith)

/-- The full transition support is a selection when the type set is finite. -/
noncomputable def Selection.full [Fintype I] : Selection M where
  J := fun t => Finset.univ.filter fun j => M.π t j ≠ 0
  nonempty := fun t => by
    obtain ⟨j, hj⟩ := (M.π t).support_nonempty
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (PMF.mem_support_iff _ _).mp hj⟩⟩
  charged := fun _ _ hj => (Finset.mem_filter.mp hj).2
  positive := fun t h p _ _ hr => by
    rw [childMix, Ne, rE_bind_eq_zero_iff] at hr
    push Not at hr
    obtain ⟨j, hj, hj'⟩ := hr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hj'⟩

/-! ### The explicit scalar functions -/

/-- `S_H = ∑_{d ≤ H} 2^d = 2^{H+1} - 1`, in `ℝ≥0∞`. -/
noncomputable def SHe (H : ℕ) : ℝ≥0∞ := ∑ d ∈ Finset.range (H + 1), (2 : ℝ≥0∞) ^ d

/-- `G_H(x) = ∑_{d ≤ H} x^d`, in `ℝ≥0∞`. -/
noncomputable def GHe (H : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ := ∑ d ∈ Finset.range (H + 1), x ^ d

/-- `U(M) = 1 + α M`. -/
noncomputable def Ufun (α : ℝ) (Mb : ℝ≥0∞) : ℝ≥0∞ := 1 + ENNReal.ofReal α * Mb

/-- The weighted stopped bound `E(M)` of `eq:explicit-weighted-error`, with the root
quantities `f`, `R_μ` and the zero bound `Z` as parameters. -/
noncomputable def Efun (α : ℝ) (H : ℕ) (T B f Rμ Zm Mb : ℝ≥0∞) : ℝ≥0∞ :=
  GHe H (4 * B * Rμ * Ufun α Mb)
    * (2 * B * (Ufun α Mb) ^ 2 * f + 2 * B * Rμ * (T * Zm + ENNReal.ofReal α * Mb) ^ 2)

/-- The single child bound `Q(M) = a M + b M^2 + (γ + 4αM) Z + C (1 + αM) E`
(`sec:averaging`). -/
noncomputable def Qfun (α : ℝ) (a b γ C Zm E Mb : ℝ≥0∞) : ℝ≥0∞ :=
  a * Mb + b * Mb ^ 2 + (γ + 4 * ENNReal.ofReal α * Mb) * Zm
    + C * (1 + ENNReal.ofReal α * Mb) * E

/-- The mixture constant `C = 4 + 8(α+1)B` of the finite alternative. -/
noncomputable def Cmix (α : ℝ) (B : ℝ≥0∞) : ℝ≥0∞ := 4 + 8 * ENNReal.ofReal (α + 1) * B

/-- The recursion `S_{H+1} = 1 + 2 S_H` of `eq:explicit-zero-bound`. -/
lemma SHe_succ (H : ℕ) : SHe (H + 1) = 1 + 2 * SHe H := by
  rw [SHe, SHe, Finset.sum_range_succ' (fun d => (2 : ℝ≥0∞) ^ d)]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  ring

/-- The recursion `G_{H+1}(x) = 1 + x G_H(x)` of `eq:explicit-weighted-error`. -/
lemma GHe_succ (H : ℕ) (x : ℝ≥0∞) : GHe (H + 1) x = 1 + x * GHe H x := by
  rw [GHe, GHe, Finset.sum_range_succ' (fun d => x ^ d)]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  ring

/-- `S_H ≥ 1` (`eq:explicit-zero-bound`). -/
lemma one_le_SHe (H : ℕ) : 1 ≤ SHe H := by
  induction H with
  | zero => simp [SHe]
  | succ H _ =>
    rw [SHe_succ]
    exact le_add_right le_rfl

/-- `G_H(x) ≥ 1` (`eq:explicit-weighted-error`). -/
lemma one_le_GHe (H : ℕ) (x : ℝ≥0∞) : 1 ≤ GHe H x := by
  induction H with
  | zero => simp [GHe]
  | succ H _ =>
    rw [GHe_succ]
    exact le_add_right le_rfl

/-- `G_H` is monotone in its argument (`eq:explicit-weighted-error`). -/
lemma GHe_mono_left (H : ℕ) {x y : ℝ≥0∞} (hxy : x ≤ y) : GHe H x ≤ GHe H y :=
  Finset.sum_le_sum fun d _ => pow_le_pow_left' hxy d

end Model

end GraphMarkovMatching.Stopped
