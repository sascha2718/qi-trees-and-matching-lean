/-
The phases and the return bound of `markov_matching_new_proof.tex` (`sec:markov-hypotheses`, "Available
fresh return times", `thm:bounded-return`) for the Markov model of a common-core
presentation.

* `Model.reach_trans`, `Model.mem_reach_succ_of_child`, `Model.Phase.reach_eq`,
  `Model.Phase.path_eq`: reachability composes and the phase advances by one per step;
* `schur_threshold_bound`: every multiple of the gcd `g` of a finite set of positive
  integers with least element `a` and greatest element `b` that is at least
  `g (a/g - 1)(b/g - 1)` is a sum of elements of the set;
* `coreDepths`, `gPhase`, `Gamma`: the core leaf depths `R_0`, their gcd `g` and the
  semigroup `Γ = ⟨R_0⟩`;
* `leafDepths_mem_Gamma`, `leafDepths_congr`: every leaf depth of a composite profile lies
  in `Γ`, and the leaf depths of a live remaining tree are congruent modulo `g`;
* `theta`, `phase`, `count_le_card`: the phase map (fresh types have phase `0`, a forced
  type with a remaining leaf at depth `d` has phase `-d`) and the phase count;
* `exists_fresh_reach`, `fresh_within_ell`, `gamma_return`: a fresh type is reachable
  within `ℓ` steps, every possible path is fresh within `ℓ` steps of every position, and
  every element of `Γ` is a fresh-to-fresh return length;
* `exists_returnThreshold`, `commonReturns_explicit`, `commonReturns`, `commonReturns_depthOne`,
  `returnThreshold_bound`: `thm:bounded-return` with `H = c_Γ + 2ℓ`, the depth-one case
  `H = 2ℓ`, and the explicit return threshold `g (a_0 - 1)(b_0 - 1)`.
-/
import GraphMarkovMatching.Stopped.Presentation
import GraphMarkovMatching.Support.Arithmetic

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### Reachability and phases along paths -/

namespace Model

variable {V I : Type} {M : Model V I}

/-- Reachability composes: `n` steps to `t` followed by `m` steps from `t` are `n + m`
steps (`sec:finite-hypotheses`). -/
lemma reach_trans {D : Set I} {t f : I} {n : ℕ} (ht : t ∈ M.reach D n) :
    ∀ {m : ℕ}, f ∈ M.reach {t} m → f ∈ M.reach D (n + m) := by
  intro m
  induction m generalizing f with
  | zero =>
    intro hf
    rw [reach_zero, Set.mem_singleton_iff] at hf
    rw [hf]
    exact ht
  | succ m ih =>
    rintro ⟨f', hf', hc⟩
    exact ⟨f', ih hf', hc⟩

/-- A step to a possible child followed by `m` steps is `m + 1` steps
(`sec:finite-hypotheses`). -/
lemma mem_reach_succ_of_child {t t' f : I} (hc : M.child t t') {m : ℕ}
    (hf : f ∈ M.reach {t'} m) : f ∈ M.reach {t} (m + 1) := by
  rw [← M.reach_children]
  have ht' : t' ∈ M.children {t} := ⟨t, Set.mem_singleton t, hc⟩
  exact M.reach_mono (Set.singleton_subset_iff.mpr ht') m hf

/-- The phase advances by one per step: a type reached in `d` steps has phase `θ t + d`
(`sec:markov-hypotheses`). -/
lemma Phase.reach_eq {g : ℕ} (Θ : Phase M g) {t : I} :
    ∀ {d : ℕ} {f : I}, f ∈ M.reach {t} d → Θ.θ f = Θ.θ t + d := by
  intro d
  induction d with
  | zero =>
    intro f hf
    rw [reach_zero, Set.mem_singleton_iff] at hf
    rw [hf, Nat.cast_zero, add_zero]
  | succ d ih =>
    rintro f ⟨f', hf', hc⟩
    rw [Θ.child_eq hc, ih hf', Nat.cast_succ, add_assoc]

/-- The phase along a possible path: position `k` has phase `θ (p 0) + k` (`sec:markov-hypotheses`). -/
lemma Phase.path_eq {g : ℕ} (Θ : Phase M g) {p : ℕ → I} {n : ℕ} (hp : M.IsPath p n) :
    ∀ k ≤ n, Θ.θ (p k) = Θ.θ (p 0) + k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [Nat.cast_zero, add_zero]
  | succ k ih =>
    intro hk
    rw [Θ.child_eq (hp k (Nat.lt_of_succ_le hk)), ih (Nat.le_of_succ_le hk), Nat.cast_succ,
      add_assoc]

end Model

/-! ### The threshold of a numerical semigroup (`thm:bounded-return`) -/

/-- **The residue-class argument of `thm:bounded-return`**: let `A` be a finite set of
positive integers, all multiples of `g > 0`, with least element `a` and greatest element
`b`, such that every large multiple of `g` is a sum of elements of `A`. Then every multiple
of `g` that is at least `g (a/g - 1)(b/g - 1)` is a sum of elements of `A`: the residues
modulo `a` of the sums of at most `m` elements strictly grow with `m` until they fill the
`a/g` classes of multiples of `g`, so every class has a representative at most
`(a/g - 1) b`. -/
theorem schur_core (A : Finset ℕ) (g a b : ℕ) (hg0 : 0 < g) (hgA : ∀ r ∈ A, g ∣ r)
    (haA : a ∈ A) (hbA : b ∈ A) (ha : ∀ r ∈ A, a ≤ r) (hb : ∀ r ∈ A, r ≤ b) (ha0 : 0 < a)
    (hcond : ∃ N, ∀ m, N ≤ m → g ∣ m → m ∈ AddSubmonoid.closure (↑A : Set ℕ)) :
    ∀ n, g * ((a / g - 1) * (b / g - 1)) ≤ n → g ∣ n →
      n ∈ AddSubmonoid.closure (↑A : Set ℕ) := by
  obtain ⟨N, hN⟩ := hcond
  set Γ := AddSubmonoid.closure (↑A : Set ℕ) with hΓ
  have hmemΓ : ∀ r ∈ A, r ∈ Γ := fun r hr => AddSubmonoid.subset_closure (Finset.mem_coe.mpr hr)
  have hgdvd : ∀ x ∈ Γ, g ∣ x := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => exact hgA x (Finset.mem_coe.mp hx)
    | zero => exact dvd_zero _
    | add x y _ _ hx hy => exact dvd_add hx hy
  have hga : g ∣ a := hgA a haA
  -- the residues modulo `a` of the semigroup elements of size at most `m b`
  let C : ℕ → Finset ℕ := fun m =>
    (Finset.range a).filter fun j => ∃ x ∈ Γ, x ≤ m * b ∧ x % a = j
  -- the residues modulo `a` that are multiples of `g`
  let all : Finset ℕ := (Finset.range a).filter fun j => g ∣ j
  have hC_sub : ∀ m, C m ⊆ all := by
    intro m j hj
    rw [Finset.mem_filter] at hj ⊢
    obtain ⟨hja, x, hxΓ, -, rfl⟩ := hj
    exact ⟨hja, (Nat.dvd_mod_iff hga).mpr (hgdvd x hxΓ)⟩
  have hC_mono : ∀ m, C m ⊆ C (m + 1) := by
    intro m j hj
    rw [Finset.mem_filter] at hj ⊢
    obtain ⟨hja, x, hxΓ, hxle, hxj⟩ := hj
    exact ⟨hja, x, hxΓ, hxle.trans (Nat.mul_le_mul_right b (Nat.le_succ m)), hxj⟩
  have hC_zero : ∀ m, 0 ∈ C m := by
    intro m
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr ha0, 0, Γ.zero_mem, Nat.zero_le _, Nat.zero_mod a⟩
  -- a residue set closed under the generators contains every class
  have hclosed : ∀ m, (∀ j ∈ C m, ∀ r ∈ A, (j + r) % a ∈ C m) → all ⊆ C m := by
    intro m hcl j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hja, hgj⟩ := hj
    have hcl' : ∀ y ∈ Γ, ∀ j ∈ C m, (j + y) % a ∈ C m := by
      intro y hy
      induction hy using AddSubmonoid.closure_induction with
      | mem r hr => exact fun j hj => hcl j hj r (Finset.mem_coe.mp hr)
      | zero =>
        intro j hj
        rwa [add_zero, Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)]
      | add y z _ _ ihy ihz =>
        intro j hj
        rw [← add_assoc, ← Nat.mod_add_mod]
        exact ihz _ (ihy j hj)
    have hx : j + a * N ∈ Γ := by
      refine hN _ ?_ (dvd_add hgj (Dvd.dvd.mul_right hga N))
      have := Nat.le_mul_of_pos_left N ha0
      omega
    have := hcl' _ hx 0 (hC_zero m)
    rwa [zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hja] at this
  -- otherwise the residue set strictly grows
  have hstep : ∀ m, ¬ (∀ j ∈ C m, ∀ r ∈ A, (j + r) % a ∈ C m) → C m ⊂ C (m + 1) := by
    intro m hncl
    push Not at hncl
    obtain ⟨j, hj, r, hr, hnot⟩ := hncl
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hC_mono m, fun heq => hnot ?_⟩
    rw [heq, Finset.mem_filter]
    rw [Finset.mem_filter] at hj
    obtain ⟨-, x, hxΓ, hxle, hxj⟩ := hj
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ ha0), x + r, Γ.add_mem hxΓ (hmemΓ r hr), ?_, ?_⟩
    · have := hb r hr
      rw [add_mul, one_mul]
      omega
    · rw [← hxj, Nat.mod_add_mod]
  have hind : ∀ m, all ⊆ C m ∨ m + 1 ≤ (C m).card := by
    intro m
    induction m with
    | zero => exact Or.inr (Finset.card_pos.mpr ⟨0, hC_zero 0⟩)
    | succ m ih =>
      rcases ih with h | h
      · exact Or.inl (h.trans (hC_mono m))
      · by_cases hcl : ∀ j ∈ C m, ∀ r ∈ A, (j + r) % a ∈ C m
        · exact Or.inl ((hclosed m hcl).trans (hC_mono m))
        · have := Finset.card_lt_card (hstep m hcl)
          exact Or.inr (by omega)
  -- there are `a / g` classes of multiples of `g`
  have hall_card : all.card ≤ a / g := by
    have : all.card ≤ (Finset.range (a / g)).card := by
      refine Finset.card_le_card_of_injOn (· / g) ?_ ?_
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
        rw [Finset.mem_coe, Finset.mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hga hj.1
      · intro j₁ hj₁ j₂ hj₂ heq
        rw [Finset.mem_coe, Finset.mem_filter] at hj₁ hj₂
        have e1 := Nat.mul_div_cancel' hj₁.2
        have e2 := Nat.mul_div_cancel' hj₂.2
        simp only at heq
        rw [← e1, ← e2, heq]
    rwa [Finset.card_range] at this
  have ha₀ : 1 ≤ a / g := Nat.div_pos (Nat.le_of_dvd ha0 hga) hg0
  have hfinal : all ⊆ C (a / g - 1) := by
    rcases hind (a / g - 1) with h | h
    · exact h
    · have hcard : all.card ≤ (C (a / g - 1)).card := by omega
      rw [Finset.eq_of_subset_of_card_le (hC_sub _) hcard]
  -- conclusion
  intro n hn hdvd
  have hnall : n % a ∈ all := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt _ ha0, (Nat.dvd_mod_iff hga).mpr hdvd⟩
  obtain ⟨-, x, hxΓ, hxle, hxmod⟩ := Finset.mem_filter.mp (hfinal hnall)
  by_cases hxn : x ≤ n
  · obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxmod.symm)
    have hn' : n = x + t * a := by
      rw [mul_comm]
      omega
    rw [hn']
    refine Γ.add_mem hxΓ ?_
    rw [← smul_eq_mul]
    exact Γ.nsmul_mem (hmemΓ a haA) t
  · exfalso
    push Not at hxn
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxmod)
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · omega
      · exact h
    have hxn' : n + a ≤ x := by
      have : a ≤ a * t := Nat.le_mul_of_pos_right a ht1
      omega
    obtain ⟨a₀, rfl⟩ := hga
    obtain ⟨b₀, rfl⟩ := hgA b hbA
    rw [Nat.mul_div_cancel_left a₀ hg0, Nat.mul_div_cancel_left b₀ hg0] at hn
    rw [Nat.mul_div_cancel_left a₀ hg0] at hxle
    have hab := ha _ hbA
    have ha₀pos : 0 < a₀ := Nat.pos_of_mul_pos_left ha0
    have hb₀pos : 0 < b₀ := Nat.pos_of_mul_pos_left (lt_of_lt_of_le ha0 hab)
    obtain ⟨a₁, rfl⟩ : ∃ a₁, a₀ = a₁ + 1 := ⟨a₀ - 1, by omega⟩
    obtain ⟨b₁, rfl⟩ : ∃ b₁, b₀ = b₁ + 1 := ⟨b₀ - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hn hxle
    nlinarith

/-- **Schur's bound on the threshold** (`thm:bounded-return`): for a nonempty finite set `A` of
positive integers with gcd `g`, least element `a` and greatest element `b`, every multiple
of `g` that is at least `g (a/g - 1)(b/g - 1)` is a sum of elements of `A`. -/
theorem schur_threshold_bound (A : Finset ℕ) (hA : A.Nonempty) (h0 : 0 ∉ A) :
    ∀ n, A.gcd id * ((A.min' hA / A.gcd id - 1) * (A.max' hA / A.gcd id - 1)) ≤ n →
      A.gcd id ∣ n → n ∈ AddSubmonoid.closure (↑A : Set ℕ) := by
  have haA := Finset.min'_mem A hA
  have hbA := Finset.max'_mem A hA
  have ha0 : 0 < A.min' hA := Nat.pos_of_ne_zero fun h => h0 (h ▸ haA)
  have hgA : ∀ r ∈ A, A.gcd id ∣ r := fun _ hr => Finset.gcd_dvd hr
  have hg0 : 0 < A.gcd id := by
    refine Nat.pos_of_ne_zero fun h => ?_
    have := hgA _ haA
    rw [h, zero_dvd_iff] at this
    omega
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (↑A : Set ℕ)
  rw [setGcd_coe_finset] at hN
  exact schur_core A _ _ _ hg0 hgA haA hbA (fun r hr => Finset.min'_le A r hr)
    (fun r hr => Finset.le_max' A r hr) ha0 ⟨N, fun m hm => hN m hm⟩

/-! ### Phases of a presentation (`sec:markov-hypotheses`) -/

namespace Presentation

variable (P : Presentation) {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V)

/-- The core leaf depths `R_0`: the leaf depths of the core profiles (`sec:markov-hypotheses`). -/
noncomputable def coreDepths : Finset ℕ := P.S.biUnion fun a => (P.D a).leafDepths

/-- `g = gcd R_0` (`sec:markov-hypotheses`). -/
noncomputable def gPhase : ℕ := P.coreDepths.gcd id

/-- `Γ = ⟨R_0⟩` (`sec:markov-hypotheses`). -/
noncomputable def Gamma : AddSubmonoid ℕ := AddSubmonoid.closure ↑P.coreDepths

/-- The core leaf depths lie in `Γ` (`sec:markov-hypotheses`). -/
lemma coreDepths_subset_Gamma : ∀ d ∈ P.coreDepths, d ∈ P.Gamma :=
  fun _ hd => AddSubmonoid.subset_closure (Finset.mem_coe.mpr hd)

/-- Every element of `Γ` is a multiple of `g` (`sec:markov-hypotheses`). -/
lemma gPhase_dvd_of_mem_Gamma {n : ℕ} (hn : n ∈ P.Gamma) : P.gPhase ∣ n := by
  unfold Gamma at hn
  induction hn using AddSubmonoid.closure_induction with
  | mem x hx => exact Finset.gcd_dvd (Finset.mem_coe.mp hx)
  | zero => exact dvd_zero _
  | add x y _ _ hx hy => exact dvd_add hx hy

/-- The residue modulo `g` of an element of `Γ` vanishes (`sec:markov-hypotheses`). -/
lemma cast_eq_zero_of_mem_Gamma {n : ℕ} (hn : n ∈ P.Gamma) : (n : ZMod P.gPhase) = 0 :=
  (CharP.cast_eq_zero_iff (ZMod P.gPhase) P.gPhase n).mpr (P.gPhase_dvd_of_mem_Gamma hn)

/-- The core leaf depths are nonempty when the core is. -/
lemma coreDepths_nonempty (hS : P.S.Nonempty) : P.coreDepths.Nonempty := by
  obtain ⟨a, ha⟩ := hS
  exact ⟨_, Finset.mem_biUnion.mpr ⟨a, ha, MTree.minLeafDepth_mem_leafDepths _⟩⟩

/-- No core profile has a leaf at depth zero: every core profile is a node. -/
lemma zero_not_mem_coreDepths : 0 ∉ P.coreDepths := by
  intro h
  rw [coreDepths, Finset.mem_biUnion] at h
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨l, r, hD⟩ := P.D_node a ha
  rw [hD] at h
  simp [MTree.leafDepths] at h

/-- Every leaf depth of a composite profile is a leaf depth of its flattening plus an
element of `Γ` (`sec:markov-hypotheses`: a leaf depth of a composite profile is a sum of core leaf
depths). -/
private lemma leafDepths_aux : ∀ t : MTree, MTree.AllComp P.S P.D t →
    ∀ d ∈ t.leafDepths, ∃ d' ∈ t.flatten.leafDepths, ∃ e ∈ P.Gamma, d = d' + e := by
  intro t
  induction t with
  | leaf =>
    intro _ d hd
    exact ⟨d, hd, 0, P.Gamma.zero_mem, (add_zero d).symm⟩
  | node l r ihl ihr =>
    intro ht d hd
    simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    rcases hd₀ with hd₀ | hd₀
    · obtain ⟨d', hd', e, he, rfl⟩ := ihl ht.1 d₀ hd₀
      refine ⟨d' + 1, ?_, e, he, by ring⟩
      simp only [MTree.flatten, MTree.leafDepths, Finset.mem_image, Finset.mem_union]
      exact ⟨d', Or.inl hd', rfl⟩
    · obtain ⟨d', hd', e, he, rfl⟩ := ihr ht.2 d₀ hd₀
      refine ⟨d' + 1, ?_, e, he, by ring⟩
      simp only [MTree.flatten, MTree.leafDepths, Finset.mem_image, Finset.mem_union]
      exact ⟨d', Or.inr hd', rfl⟩
  | gnode l r ihl ihr =>
    intro ht d hd
    obtain ⟨⟨a, ha, hDa⟩, hl, hr⟩ := ht
    simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have hcore : ∀ d'' ∈ (MTree.node l.flatten r.flatten).leafDepths, d'' ∈ P.Gamma := by
      intro d'' h
      apply P.coreDepths_subset_Gamma
      rw [coreDepths, Finset.mem_biUnion]
      exact ⟨a, ha, hDa ▸ h⟩
    refine ⟨0, by simp [MTree.flatten, MTree.leafDepths], ?_⟩
    rcases hd₀ with hd₀ | hd₀
    · obtain ⟨d', hd', e, he, rfl⟩ := ihl hl d₀ hd₀
      refine ⟨d' + 1 + e, P.Gamma.add_mem (hcore _ ?_) he, by ring⟩
      simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
      exact ⟨d', Or.inl hd', rfl⟩
    · obtain ⟨d', hd', e, he, rfl⟩ := ihr hr d₀ hd₀
      refine ⟨d' + 1 + e, P.Gamma.add_mem (hcore _ ?_) he, by ring⟩
      simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
      exact ⟨d', Or.inr hd', rfl⟩

/-- Every leaf depth of a composite profile lies in `Γ` (`sec:markov-hypotheses`: a sum of core leaf
depths). -/
theorem leafDepths_mem_Gamma (t : MTree) (ht : MTree.AllComp P.S P.D t)
    (hg : ∃ l r, t = MTree.gnode l r) : ∀ d ∈ t.leafDepths, d ∈ P.Gamma := by
  obtain ⟨l, r, rfl⟩ := hg
  intro d hd
  obtain ⟨d', hd', e, he, rfl⟩ := P.leafDepths_aux _ ht d hd
  have h0 : d' = 0 := by simpa [MTree.flatten, MTree.leafDepths] using hd'
  rw [h0, zero_add]
  exact he

/-- A subtree sits at some depth `m` of the ambient tree: its leaf depths shifted by `m`
are leaf depths of the ambient tree. -/
private lemma exists_shift_of_mem_subtrees : ∀ (t τ : MTree), τ ∈ t.subtrees →
    ∃ m, ∀ d ∈ τ.leafDepths, m + d ∈ t.leafDepths := by
  intro t
  induction t with
  | leaf =>
    intro τ hτ
    simp only [MTree.subtrees, Finset.mem_singleton] at hτ
    subst hτ
    exact ⟨0, fun d hd => by rwa [zero_add]⟩
  | node l r ihl ihr =>
    intro τ hτ
    simp only [MTree.subtrees, Finset.mem_insert, Finset.mem_union] at hτ
    rcases hτ with rfl | hτ | hτ
    · exact ⟨0, fun d hd => by rwa [zero_add]⟩
    · obtain ⟨m, hm⟩ := ihl τ hτ
      refine ⟨m + 1, fun d hd => ?_⟩
      simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
      exact ⟨m + d, Or.inl (hm d hd), by ring⟩
    · obtain ⟨m, hm⟩ := ihr τ hτ
      refine ⟨m + 1, fun d hd => ?_⟩
      simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
      exact ⟨m + d, Or.inr (hm d hd), by ring⟩
  | gnode l r ihl ihr =>
    intro τ hτ
    simp only [MTree.subtrees, Finset.mem_insert, Finset.mem_union] at hτ
    rcases hτ with rfl | hτ | hτ
    · exact ⟨0, fun d hd => by rwa [zero_add]⟩
    · obtain ⟨m, hm⟩ := ihl τ hτ
      refine ⟨m + 1, fun d hd => ?_⟩
      simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
      exact ⟨m + d, Or.inl (hm d hd), by ring⟩
    · obtain ⟨m, hm⟩ := ihr τ hτ
      refine ⟨m + 1, fun d hd => ?_⟩
      simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
      exact ⟨m + d, Or.inr (hm d hd), by ring⟩

/-- A live forced type has as remaining tree a proper subtree, other than a leaf, of a
supported profile of its side. -/
lemma of_mem_live_forced (σ : Bool) (τ : MTree) (h : (σ, some τ) ∈ P.live) :
    ∃ k ∈ P.supp σ, τ ∈ (P.C σ k).subtrees ∧ τ ≠ P.C σ k ∧ τ ≠ MTree.leaf := by
  simp only [live, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter,
    Prod.mk.injEq, Option.some.injEq, reduceCtorEq, and_false, or_self, false_or] at h
  obtain ⟨σ', k, hk, τ', ⟨h1, h2, h3⟩, rfl, rfl⟩ := h
  exact ⟨k, hk, h1, h2, h3⟩

/-- All leaf depths of a live remaining tree are congruent modulo `g` (`sec:markov-hypotheses`). -/
theorem leafDepths_congr (σ : Bool) (τ : MTree) (h : (σ, some τ) ∈ P.live) :
    ∀ d ∈ τ.leafDepths, ∀ d' ∈ τ.leafDepths, (d : ZMod P.gPhase) = d' := by
  obtain ⟨k, hk, hsub, -, -⟩ := P.of_mem_live_forced σ τ h
  obtain ⟨m, hm⟩ := exists_shift_of_mem_subtrees _ _ hsub
  have hΓ := P.leafDepths_mem_Gamma (P.C σ k) (P.C_allComp σ k hk) (P.C_gnode σ k hk)
  intro d hd d' hd'
  have h1 := P.cast_eq_zero_of_mem_Gamma (hΓ _ (hm d hd))
  have h2 := P.cast_eq_zero_of_mem_Gamma (hΓ _ (hm d' hd'))
  rw [Nat.cast_add] at h1 h2
  linear_combination h1 - h2

/-- The type below a non-leaf remaining tree is the forced type. -/
lemma typeOf_of_ne_leaf' (σ : Bool) {τ : MTree} (hτ : τ ≠ MTree.leaf) :
    typeOf σ τ = (σ, some τ) := by
  cases τ with
  | leaf => exact absurd rfl hτ
  | node l r => rfl
  | gnode l r => rfl

/-- The coercion into the live types is the identity on live types. -/
lemma toLive_of_mem' {t : PType} (h : t ∈ P.live) : P.toLive t = ⟨t, h⟩ := by
  unfold toLive
  rw [dif_pos h]

/-- The underlying raw type of the coercion of a live type. -/
lemma toLive_val {t : PType} (h : t ∈ P.live) : (P.toLive t).1 = t := by
  rw [P.toLive_of_mem' h]

/-- The coercion of a fresh raw type is the fresh live type. -/
lemma toLive_fresh (σ : Bool) : P.toLive (σ, none) = P.freshL σ :=
  P.toLive_of_mem' (P.fresh_mem_live σ)

/-- The phase of a live type (`sec:markov-hypotheses`): `0` at a fresh type, `-d (mod g)` at a forced
type with a leaf at depth `d`. -/
noncomputable def theta (t : P.Live) : ZMod P.gPhase :=
  match t.1 with
  | (_, none) => 0
  | (_, some τ) => -(τ.minLeafDepth : ZMod P.gPhase)

/-- The phase of a fresh type is zero. -/
lemma theta_fresh (σ : Bool) (h : (σ, none) ∈ P.live) : P.theta ⟨(σ, none), h⟩ = 0 := rfl

/-- The phase of a forced type is minus its least leaf depth. -/
lemma theta_forced (σ : Bool) (τ : MTree) (h : (σ, some τ) ∈ P.live) :
    P.theta ⟨(σ, some τ), h⟩ = -(τ.minLeafDepth : ZMod P.gPhase) := rfl

/-- The phase of the type below a remaining tree is minus its least leaf depth. -/
lemma theta_of_val_eq_typeOf (u : P.Live) (σ : Bool) (τ : MTree) (hu : u.1 = typeOf σ τ) :
    P.theta u = -(τ.minLeafDepth : ZMod P.gPhase) := by
  obtain ⟨u, hmem⟩ := u
  simp only at hu
  subst hu
  cases τ with
  | leaf =>
    show (0 : ZMod P.gPhase) = -((MTree.leaf.minLeafDepth : ℕ) : ZMod P.gPhase)
    simp [MTree.minLeafDepth]
  | node l r => rfl
  | gnode l r => rfl

/-- A charged raw transition at a fresh type places a supported profile. -/
lemma rawKernel_fresh_ne_zero_iff' (σ : Bool) (p : PType × PType) :
    P.rawKernel (σ, none) p ≠ 0 ↔ ∃ k ∈ P.supp σ, rootPair σ (P.C σ k) = p := by
  change (P.ν σ).map (fun k => rootPair σ (P.C σ k)) p ≠ 0 ↔ _
  rw [← PMF.mem_support_iff, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, (P.mem_supp σ k).mp ((PMF.mem_support_iff _ _).mp hk), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, (PMF.mem_support_iff _ _).mpr ((P.mem_supp σ k).mpr hk), rfl⟩

/-- A charged raw transition at a forced type is the root pair of its remaining tree. -/
lemma rawKernel_forced_ne_zero_iff' (σ : Bool) (τ : MTree) (p : PType × PType) :
    P.rawKernel (σ, some τ) p ≠ 0 ↔ p = rootPair σ τ := by
  change PMF.pure (rootPair σ τ) p ≠ 0 ↔ _
  rw [← PMF.mem_support_iff, PMF.mem_support_pure_iff]

/-- The children in a charged transition are the types below the two root children of a
profile, and their least leaf depths plus one are congruent to minus the parent phase
(`sec:markov-hypotheses`: each child has phase one greater than its parent). -/
lemma theta_of_charged (t : P.Live) (p : PType × PType) (hp : P.rawKernel t.1 p ≠ 0) :
    ∃ σ l r, p = (typeOf σ l, typeOf σ r)
      ∧ (l.minLeafDepth : ZMod P.gPhase) + 1 = -P.theta t
      ∧ (r.minLeafDepth : ZMod P.gPhase) + 1 = -P.theta t := by
  obtain ⟨⟨σ, o⟩, hmem⟩ := t
  cases o with
  | none =>
    obtain ⟨k, hk, rfl⟩ := (P.rawKernel_fresh_ne_zero_iff' σ p).mp hp
    obtain ⟨l, r, hC⟩ := P.C_gnode σ k hk
    have hΓ := P.leafDepths_mem_Gamma (P.C σ k) (P.C_allComp σ k hk) ⟨l, r, hC⟩
    rw [hC] at hΓ ⊢
    refine ⟨σ, l, r, rfl, ?_, ?_⟩
    · rw [theta_fresh, neg_zero]
      have := P.cast_eq_zero_of_mem_Gamma (hΓ (l.minLeafDepth + 1) (by
        simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
        exact ⟨_, Or.inl (MTree.minLeafDepth_mem_leafDepths l), rfl⟩))
      exact_mod_cast this
    · rw [theta_fresh, neg_zero]
      have := P.cast_eq_zero_of_mem_Gamma (hΓ (r.minLeafDepth + 1) (by
        simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
        exact ⟨_, Or.inr (MTree.minLeafDepth_mem_leafDepths r), rfl⟩))
      exact_mod_cast this
  | some τ =>
    obtain rfl := (P.rawKernel_forced_ne_zero_iff' σ τ p).mp hp
    obtain ⟨-, -, -, -, hleaf⟩ := P.of_mem_live_forced σ τ hmem
    have hcongr := P.leafDepths_congr σ τ hmem
    cases τ with
    | leaf => exact absurd rfl hleaf
    | node l r =>
      refine ⟨σ, l, r, rfl, ?_, ?_⟩
      · rw [theta_forced, neg_neg]
        have := hcongr (l.minLeafDepth + 1) (by
          simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
          exact ⟨_, Or.inl (MTree.minLeafDepth_mem_leafDepths l), rfl⟩)
          _ (MTree.minLeafDepth_mem_leafDepths _)
        exact_mod_cast this
      · rw [theta_forced, neg_neg]
        have := hcongr (r.minLeafDepth + 1) (by
          simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
          exact ⟨_, Or.inr (MTree.minLeafDepth_mem_leafDepths r), rfl⟩)
          _ (MTree.minLeafDepth_mem_leafDepths _)
        exact_mod_cast this
    | gnode l r =>
      refine ⟨σ, l, r, rfl, ?_, ?_⟩
      · rw [theta_forced, neg_neg]
        have := hcongr (l.minLeafDepth + 1) (by
          simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
          exact ⟨_, Or.inl (MTree.minLeafDepth_mem_leafDepths l), rfl⟩)
          _ (MTree.minLeafDepth_mem_leafDepths _)
        exact_mod_cast this
      · rw [theta_forced, neg_neg]
        have := hcongr (r.minLeafDepth + 1) (by
          simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union]
          exact ⟨_, Or.inr (MTree.minLeafDepth_mem_leafDepths r), rfl⟩)
          _ (MTree.minLeafDepth_mem_leafDepths _)
        exact_mod_cast this

/-- **The phase map** (`sec:markov-hypotheses`): fresh types have phase `0`, children have phase one
greater. -/
noncomputable def phase : Model.Phase (P.toModel R zero μ) P.gPhase where
  θ := P.theta
  fresh_zero := fun t ht => by
    obtain ⟨⟨σ, o⟩, hmem⟩ := t
    have ho : o = none := ht
    subst ho
    rfl
  child := fun t j hj => by
    rw [show (P.toModel R zero μ).π = P.kernelL from rfl, kernelL_ne_zero_iff] at hj
    obtain ⟨σ, l, r, hp, hl, hr⟩ := P.theta_of_charged t _ hj
    simp only [Prod.mk.injEq] at hp
    constructor
    · rw [P.theta_of_val_eq_typeOf j.1 σ l hp.1]
      linear_combination -hl
    · rw [P.theta_of_val_eq_typeOf j.2 σ r hp.2]
      linear_combination -hr

/-- The phase class count is at most the number of live types. -/
lemma count_le_card (i : ZMod P.gPhase) : (P.phase R zero μ).count i ≤ P.live.card := by
  unfold Model.Phase.count
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ]
  exact le_of_eq (Fintype.card_coe P.live)

/-! ### Possible paths of a presentation (`sec:markov-hypotheses`) -/

/-- A possible child of a live type is a component of a charged raw transition. -/
lemma child_iff (t t' : P.Live) :
    (P.toModel R zero μ).child t t'
      ↔ ∃ p, P.rawKernel t.1 p ≠ 0 ∧ (t'.1 = p.1 ∨ t'.1 = p.2) := by
  constructor
  · rintro ⟨j, hj, hj'⟩
    refine ⟨(j.1.1, j.2.1), (P.kernelL_ne_zero_iff t j).mp hj, ?_⟩
    rcases hj' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro ⟨p, hp, hp'⟩
    obtain ⟨h1, h2⟩ := P.rawKernel_live t p hp
    refine ⟨(⟨p.1, h1⟩, ⟨p.2, h2⟩), (P.kernelL_ne_zero_iff t _).mpr hp, ?_⟩
    rcases hp' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

/-- The two components of a charged raw transition are possible children. -/
lemma child_toLive_of_raw (t : P.Live) (p : PType × PType) (hp : P.rawKernel t.1 p ≠ 0) :
    (P.toModel R zero μ).child t (P.toLive p.1)
      ∧ (P.toModel R zero μ).child t (P.toLive p.2) := by
  obtain ⟨h1, h2⟩ := P.rawKernel_live t p hp
  exact ⟨(P.child_iff R zero μ t _).mpr ⟨p, hp, Or.inl (P.toLive_val h1)⟩,
    (P.child_iff R zero μ t _).mpr ⟨p, hp, Or.inr (P.toLive_val h2)⟩⟩

/-- Following a leaf of the remaining tree at depth `d` reaches the fresh type of the side
in `d` steps (`sec:markov-hypotheses`). -/
lemma freshL_mem_reach (σ : Bool) : ∀ (τ : MTree), typeOf σ τ ∈ P.live →
    ∀ d ∈ τ.leafDepths,
      P.freshL σ ∈ (P.toModel R zero μ).reach {P.toLive (typeOf σ τ)} d := by
  intro τ
  induction τ with
  | leaf =>
    intro _ d hd
    have hd0 : d = 0 := by simpa [MTree.leafDepths] using hd
    subst hd0
    rw [show typeOf σ MTree.leaf = (σ, none) from rfl, P.toLive_fresh]
    exact Set.mem_singleton _
  | node l r ihl ihr =>
    intro hτ d hd
    simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have hp : P.rawKernel (P.toLive (typeOf σ (MTree.node l r))).1
        (rootPair σ (MTree.node l r)) ≠ 0 := by
      rw [P.toLive_val hτ]
      exact (P.rawKernel_forced_ne_zero_iff' σ _ _).mpr rfl
    obtain ⟨hl, hr⟩ := P.rawKernel_live _ _ hp
    obtain ⟨hcl, hcr⟩ := P.child_toLive_of_raw R zero μ _ _ hp
    rcases hd₀ with hd₀ | hd₀
    · exact Model.mem_reach_succ_of_child hcl (ihl hl d₀ hd₀)
    · exact Model.mem_reach_succ_of_child hcr (ihr hr d₀ hd₀)
  | gnode l r ihl ihr =>
    intro hτ d hd
    simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have hp : P.rawKernel (P.toLive (typeOf σ (MTree.gnode l r))).1
        (rootPair σ (MTree.gnode l r)) ≠ 0 := by
      rw [P.toLive_val hτ]
      exact (P.rawKernel_forced_ne_zero_iff' σ _ _).mpr rfl
    obtain ⟨hl, hr⟩ := P.rawKernel_live _ _ hp
    obtain ⟨hcl, hcr⟩ := P.child_toLive_of_raw R zero μ _ _ hp
    rcases hd₀ with hd₀ | hd₀
    · exact Model.mem_reach_succ_of_child hcl (ihl hl d₀ hd₀)
    · exact Model.mem_reach_succ_of_child hcr (ihr hr d₀ hd₀)

/-- From every live type some possible path reaches a fresh type within `ℓ` steps
(`sec:markov-hypotheses`: choose a leaf of the remaining tree). -/
theorem exists_fresh_reach (t : P.Live) :
    ∃ d ≤ P.ell, ∃ f ∈ (P.toModel R zero μ).reach {t} d, (P.toModel R zero μ).fresh f := by
  obtain ⟨⟨σ, o⟩, hmem⟩ := t
  cases o with
  | none => exact ⟨0, Nat.zero_le _, ⟨(σ, none), hmem⟩, Set.mem_singleton _, rfl⟩
  | some τ =>
    obtain ⟨-, -, -, -, hleaf⟩ := P.of_mem_live_forced σ τ hmem
    have hτ : typeOf σ τ ∈ P.live := by
      rw [typeOf_of_ne_leaf' σ hleaf]
      exact hmem
    have hreach := P.freshL_mem_reach R zero μ σ τ hτ τ.minLeafDepth
      (MTree.minLeafDepth_mem_leafDepths τ)
    have heq : (⟨typeOf σ τ, hτ⟩ : P.Live) = ⟨(σ, some τ), hmem⟩ :=
      Subtype.ext (typeOf_of_ne_leaf' σ hleaf)
    rw [P.toLive_of_mem' hτ, heq] at hreach
    exact ⟨τ.minLeafDepth,
      (MTree.minLeafDepth_le_height τ).trans (P.height_le_ell σ τ hmem), P.freshL σ, hreach,
      rfl⟩

/-- The height of the remaining tree of a raw type (`0` at a fresh type). -/
def remHeight : PType → ℕ
  | (_, none) => 0
  | (_, some τ) => τ.height

/-- The remaining height below a remaining tree is its height. -/
lemma remHeight_typeOf (σ : Bool) (τ : MTree) : remHeight (typeOf σ τ) = τ.height := by
  cases τ <;> rfl

/-- The remaining height of a live type is at most `ℓ`. -/
lemma remHeight_le_ell (t : P.Live) : remHeight t.1 ≤ P.ell := by
  obtain ⟨⟨σ, o⟩, hmem⟩ := t
  cases o with
  | none => exact Nat.zero_le _
  | some τ => exact P.height_le_ell σ τ hmem

/-- The remaining height of a forced live type is positive. -/
lemma one_le_remHeight {t : P.Live} (hnf : ¬ (P.toModel R zero μ).fresh t) :
    1 ≤ remHeight t.1 := by
  obtain ⟨⟨σ, o⟩, hmem⟩ := t
  cases o with
  | none => exact absurd rfl hnf
  | some τ =>
    obtain ⟨-, -, -, -, hleaf⟩ := P.of_mem_live_forced σ τ hmem
    cases τ with
    | leaf => exact absurd rfl hleaf
    | node l r =>
      simp only [remHeight, MTree.height]
      omega
    | gnode l r =>
      simp only [remHeight, MTree.height]
      omega

/-- A possible child of a forced type has a remaining tree of smaller height. -/
lemma remHeight_lt_of_child {t t' : P.Live} (hc : (P.toModel R zero μ).child t t')
    (hnf : ¬ (P.toModel R zero μ).fresh t) : remHeight t'.1 < remHeight t.1 := by
  obtain ⟨p, hp, hp'⟩ := (P.child_iff R zero μ t t').mp hc
  obtain ⟨⟨σ, o⟩, hmem⟩ := t
  cases o with
  | none => exact absurd rfl hnf
  | some τ =>
    obtain rfl := (P.rawKernel_forced_ne_zero_iff' σ τ p).mp hp
    obtain ⟨-, -, -, -, hleaf⟩ := P.of_mem_live_forced σ τ hmem
    cases τ with
    | leaf => exact absurd rfl hleaf
    | node l r =>
      have hτ : remHeight (σ, some (MTree.node l r)) = max l.height r.height + 1 := rfl
      rcases hp' with h | h
      · rw [h, show (rootPair σ (MTree.node l r)).1 = typeOf σ l from rfl, remHeight_typeOf,
          hτ]
        omega
      · rw [h, show (rootPair σ (MTree.node l r)).2 = typeOf σ r from rfl, remHeight_typeOf,
          hτ]
        omega
    | gnode l r =>
      have hτ : remHeight (σ, some (MTree.gnode l r)) = max l.height r.height + 1 := rfl
      rcases hp' with h | h
      · rw [h, show (rootPair σ (MTree.gnode l r)).1 = typeOf σ l from rfl, remHeight_typeOf,
          hτ]
        omega
      · rw [h, show (rootPair σ (MTree.gnode l r)).2 = typeOf σ r from rfl, remHeight_typeOf,
          hτ]
        omega

/-- Along every possible path, from every position a fresh type is visited within `ℓ`
steps (`sec:markov-hypotheses`: gaps between fresh visits are at most `ℓ`). -/
theorem fresh_within_ell (p : ℕ → P.Live) (n : ℕ) (hp : (P.toModel R zero μ).IsPath p n)
    (i : ℕ) (hi : i + P.ell ≤ n) :
    ∃ k, i ≤ k ∧ k ≤ i + P.ell ∧ (P.toModel R zero μ).fresh (p k) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ j, j ≤ P.ell → remHeight (p (i + j)).1 + j ≤ remHeight (p i).1 := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      have h1 := ih (Nat.le_of_succ_le hj)
      have hc : (P.toModel R zero μ).child (p (i + j)) (p (i + j + 1)) := hp (i + j) (by omega)
      have h2 := P.remHeight_lt_of_child R zero μ hc (hcon (i + j) (by omega) (by omega))
      show remHeight (p (i + j + 1)).1 + (j + 1) ≤ remHeight (p i).1
      omega
  have h1 := key P.ell le_rfl
  have h2 := P.remHeight_le_ell (p i)
  have h3 := P.one_le_remHeight R zero μ (hcon (i + P.ell) (by omega) le_rfl)
  omega

/-- From a fresh type, every element of `Γ` is a possible fresh-to-fresh return length
(`sec:markov-hypotheses`: choose core arities and follow a leaf of the required depth). -/
theorem gamma_return (σ : Bool) (d : ℕ) (hd : d ∈ P.Gamma) :
    P.freshL σ ∈ (P.toModel R zero μ).reach {P.freshL σ} d := by
  unfold Gamma at hd
  induction hd using AddSubmonoid.closure_induction with
  | mem x hx =>
    rw [Finset.mem_coe, coreDepths, Finset.mem_biUnion] at hx
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨l, r, hD⟩ := P.D_node a ha
    have hka : a ∈ P.supp σ := P.S_subset_supp σ ha
    have hC : P.C σ a = MTree.gnode l r := by
      rw [P.C_core σ a ha, hD]
      rfl
    have hp : P.rawKernel (P.freshL σ).1 (rootPair σ (P.C σ a)) ≠ 0 :=
      (P.rawKernel_fresh_ne_zero_iff' σ _).mpr ⟨a, hka, rfl⟩
    obtain ⟨hl, hr⟩ := P.rawKernel_live _ _ hp
    obtain ⟨hcl, hcr⟩ := P.child_toLive_of_raw R zero μ _ _ hp
    rw [hC] at hl hr hcl hcr
    rw [hD] at hx
    simp only [MTree.leafDepths, Finset.mem_image, Finset.mem_union] at hx
    obtain ⟨d₀, hd₀, rfl⟩ := hx
    rcases hd₀ with hd₀ | hd₀
    · exact Model.mem_reach_succ_of_child hcl (P.freshL_mem_reach R zero μ σ l hl d₀ hd₀)
    · exact Model.mem_reach_succ_of_child hcr (P.freshL_mem_reach R zero μ σ r hr d₀ hd₀)
  | zero => exact Set.mem_singleton _
  | add x y _ _ hx hy => exact Model.reach_trans hx hy

/-- The return threshold: every multiple of `g` at least `c_Γ` lies in `Γ`
(`thm:bounded-return`, from `Nat.exists_mem_closure_of_ge`). -/
theorem exists_returnThreshold : ∃ c : ℕ, ∀ n, c ≤ n → P.gPhase ∣ n → n ∈ P.Gamma := by
  obtain ⟨c, hc⟩ := Nat.exists_mem_closure_of_ge (↑P.coreDepths : Set ℕ)
  rw [setGcd_coe_finset] at hc
  exact ⟨c, fun n hn hdvd => hc n hn hdvd⟩

/-- **`thm:bounded-return`** with an explicit return threshold: if every multiple of `g` at least
`c` lies in `Γ`, common returns hold with `H = c + 2ℓ`. -/
theorem commonReturns_explicit (hS : P.S.Nonempty) {c : ℕ}
    (hc : ∀ n, c ≤ n → P.gPhase ∣ n → n ∈ P.Gamma) :
    (P.toModel R zero μ).CommonReturns (P.phase R zero μ) (c + 2 * P.ell) := by
  have _ := hS
  intro s t hst p hp0 hp
  obtain ⟨d, hd, f, hf, hff⟩ := P.exists_fresh_reach R zero μ t
  obtain ⟨k, hik, hk, hfk⟩ := P.fresh_within_ell R zero μ p _ hp (c + P.ell) (by omega)
  refine ⟨k, by omega, hfk, f, ?_, hff⟩
  have hdk : d ≤ k := by omega
  -- the phases: `k ≡ -θ s` and `d ≡ -θ t` modulo `g`
  have hkθ := (P.phase R zero μ).path_eq hp k (by omega)
  rw [(P.phase R zero μ).fresh_zero _ hfk, hp0] at hkθ
  have hfθ := (P.phase R zero μ).reach_eq hf
  rw [(P.phase R zero μ).fresh_zero _ hff] at hfθ
  have hkd : ((k - d : ℕ) : ZMod P.gPhase) = 0 := by
    rw [Nat.cast_sub hdk]
    linear_combination -hkθ + hfθ - hst
  have hΓ : k - d ∈ P.Gamma :=
    hc _ (by omega) ((CharP.cast_eq_zero_iff (ZMod P.gPhase) P.gPhase (k - d)).mp hkd)
  -- the fresh target is a fresh live type, from which `Γ` gives the return
  obtain ⟨⟨σ, o⟩, hfmem⟩ := f
  have ho : o = none := hff
  subst ho
  have hfeq : (⟨(σ, none), hfmem⟩ : P.Live) = P.freshL σ := rfl
  rw [hfeq] at hf ⊢
  have := Model.reach_trans hf (P.gamma_return R zero μ σ (k - d) hΓ)
  rwa [Nat.add_sub_of_le hdk] at this

/-- **`thm:bounded-return`**: with `H = c_Γ + 2ℓ` for a return threshold `c_Γ`, common returns
hold. -/
theorem commonReturns (hS : P.S.Nonempty) :
    ∃ H, (P.toModel R zero μ).CommonReturns (P.phase R zero μ) H := by
  obtain ⟨c, hc⟩ := P.exists_returnThreshold
  exact ⟨c + 2 * P.ell, P.commonReturns_explicit R zero μ hS hc⟩

/-- The depth-one case of `thm:bounded-return`: if some core profile has a leaf at depth
one, `g = 1` and `H = 2ℓ` works. -/
theorem commonReturns_depthOne (hS : P.S.Nonempty) (h1 : ∃ a ∈ P.S, 1 ∈ (P.D a).leafDepths) :
    P.gPhase = 1 ∧ (P.toModel R zero μ).CommonReturns (P.phase R zero μ) (2 * P.ell) := by
  obtain ⟨a, ha, h1a⟩ := h1
  have h1Γ : 1 ∈ P.Gamma :=
    P.coreDepths_subset_Gamma 1 (Finset.mem_biUnion.mpr ⟨a, ha, h1a⟩)
  refine ⟨Nat.dvd_one.mp (P.gPhase_dvd_of_mem_Gamma h1Γ), ?_⟩
  have hc : ∀ n, 0 ≤ n → P.gPhase ∣ n → n ∈ P.Gamma := fun n _ _ => by
    have := P.Gamma.nsmul_mem h1Γ n
    rwa [smul_eq_mul, mul_one] at this
  have := P.commonReturns_explicit R zero μ hS hc
  rwa [zero_add] at this

/-- The explicit return-threshold bound of `sec:markov-hypotheses`: with `a₀ = min R_0/g` and
`b₀ = max R_0/g`, every multiple of `g` at least `g (a₀-1)(b₀-1)` lies in `Γ`. -/
theorem returnThreshold_bound (hS : P.S.Nonempty) :
    ∀ n, P.gPhase * ((P.coreDepths.min' (P.coreDepths_nonempty hS) / P.gPhase - 1)
      * (P.coreDepths.max' (P.coreDepths_nonempty hS) / P.gPhase - 1)) ≤ n →
      P.gPhase ∣ n → n ∈ P.Gamma :=
  schur_threshold_bound P.coreDepths (P.coreDepths_nonempty hS) P.zero_not_mem_coreDepths

end Presentation

end GraphMarkovMatching.Stopped
