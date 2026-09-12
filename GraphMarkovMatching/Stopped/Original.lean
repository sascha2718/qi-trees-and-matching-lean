/-
The original Markov statements (`markov_matching_new_proof.tex`, `sec:original-statements`,
"A single bounded counter law"): the varying-offspring process of `Models/Counter.lean`
(kernel `varyK`, fresh law `Tlaw`) as an instance of the Markov model of a presentation.

* `rem`: the balanced profile below a vertex with counter `k`, a graft-free tree with
  `max k 2` leaves (`rem_leaves`, `rem_noGraft`);
* `nuBar`, `suppBar`: the merged law `ν̄` with the masses of the counters `0, 1, 2`
  combined at `2`, and its support;
* `balancedPresentation`: the presentation of a finitely supported counter law with the
  balanced profiles as common core on both sides;
* `Tlaw_states_eq`: **the law identification**, the state labelling of `Tlaw μ ν v0 h` has
  the law of the state labelling of a fresh type of the balanced presentation of `ν̄`;
* `fullSim_labRel_iff`, `failProb_Tlaw_eq`: matching depends only on
  the states, hence the failure probabilities agree;
* `inverseSum_nuBar_le`: the inverse-sum comparison `∑ ν̄(k)^{-α} ≤ ∑ ν(k)^{-5/2}` for `α ≤ 5/2`;
* `original_one_law_matching`, `original_one_law_matching_two`,
  `original_one_law_matching_fiveHalf`: the one-law statement recovered for the original
  process;
* `graftPort`, `compProfile`, `CompositeData`, `CompositeData.toPresentation`: the composite
  profiles of the declared pairs and the presentation of the prescribed composite two-law
  process (`sec:composite-process`);
* `cT_states_eq`, `cFailProb_eq`: the law identification for the composite kernel `compK` of
  `Models/Composite.lean` and the agreement of the two-law failure probabilities;
* `composite_two_law_matching`: the two-law statement recovered for the composite
  processes, with the bound `B = max_σ ∑_{k ∈ S} ν_σ(k)^{-α}` of `sec:composite-process`.
-/
import GraphMarkovMatching.Stopped.Exponent
import GraphMarkovMatching.Stopped.PresentationLaws
import GraphMarkovMatching.Stopped.Application
import GraphMarkovMatching.Stopped.Consequences
import GraphMarkovMatching.Models.Counter
import GraphMarkovMatching.Process.Recursion
import GraphMarkovMatching.Models.Composite

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Model
open scoped ENNReal Classical

/-! ### The balanced profiles (`sec:single-counter-law`) -/

/-- The balanced profile below a vertex carrying the counter `j` (`sec:single-counter-law`):
a counter `j ≥ 4` has forced children with counters `⌊j/2⌋` and `⌈j/2⌉`, a counter `3` one
forced child of counter `2` and one fresh child, a counter at most `2` two fresh children. -/
def rem (j : ℕ) : MTree :=
  if h4 : 4 ≤ j then MTree.node (rem (j / 2)) (rem (j - j / 2))
  else if j = 3 then MTree.node (MTree.node MTree.leaf MTree.leaf) MTree.leaf
  else MTree.node MTree.leaf MTree.leaf
termination_by j
decreasing_by all_goals omega

/-- The balanced profile of a counter `j ≥ 4`. -/
lemma rem_of_four_le {j : ℕ} (hj : 4 ≤ j) :
    rem j = MTree.node (rem (j / 2)) (rem (j - j / 2)) := by
  rw [rem, dif_pos hj]

/-- The balanced profile of the counter `3`. -/
lemma rem_three : rem 3 = MTree.node (MTree.node MTree.leaf MTree.leaf) MTree.leaf := by
  rw [rem, dif_neg (by omega), if_pos rfl]

/-- The balanced profile of a counter at most `2`. -/
lemma rem_of_le_two {j : ℕ} (hj : j ≤ 2) : rem j = MTree.node MTree.leaf MTree.leaf := by
  rw [rem, dif_neg (by omega), if_neg (by omega)]

/-- The balanced profile of the counter `2`. -/
lemma rem_two : rem 2 = MTree.node MTree.leaf MTree.leaf := rem_of_le_two le_rfl

/-- The balanced profile of a counter has `max j 2` leaves (`sec:single-counter-law`). -/
lemma rem_leaves (j : ℕ) : (rem j).leaves = max j 2 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h4 : 4 ≤ j
    · rw [rem_of_four_le h4, MTree.leaves, ih (j / 2) (by omega), ih (j - j / 2) (by omega)]
      omega
    · by_cases h3 : j = 3
      · subst h3
        rw [rem_three]
        rfl
      · rw [rem_of_le_two (by omega)]
        show 2 = max j 2
        omega

/-- The balanced profiles are graft-free. -/
lemma rem_noGraft (j : ℕ) : (rem j).NoGraft := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h4 : 4 ≤ j
    · rw [rem_of_four_le h4]
      exact ⟨ih (j / 2) (by omega), ih (j - j / 2) (by omega)⟩
    · by_cases h3 : j = 3
      · subst h3
        rw [rem_three]
        exact ⟨⟨trivial, trivial⟩, trivial⟩
      · rw [rem_of_le_two (by omega)]
        exact ⟨trivial, trivial⟩

/-- Every balanced profile is a node. -/
lemma rem_node (j : ℕ) : ∃ l r, rem j = MTree.node l r := by
  by_cases h4 : 4 ≤ j
  · exact ⟨_, _, rem_of_four_le h4⟩
  · by_cases h3 : j = 3
    · exact ⟨_, _, h3 ▸ rem_three⟩
    · exact ⟨_, _, rem_of_le_two (by omega)⟩

/-- A balanced profile is not a leaf. -/
lemma rem_ne_leaf (j : ℕ) : rem j ≠ MTree.leaf := by
  obtain ⟨l, r, h⟩ := rem_node j
  rw [h]
  exact MTree.noConfusion

/-- The type of a balanced profile is the forced type with that remaining tree. -/
lemma typeOf_rem (σ : Bool) (j : ℕ) : typeOf σ (rem j) = (σ, some (rem j)) :=
  Presentation.typeOf_of_ne_leaf σ (rem_ne_leaf j)

/-- The balanced profile depends on the counter only through `max j 2`
(`sec:single-counter-law`: the counters `0, 1, 2` have the same profile). -/
lemma rem_max (j : ℕ) : rem (max j 2) = rem j := by
  by_cases hj : j ≤ 2
  · rw [max_eq_right hj, rem_two, rem_of_le_two hj]
  · rw [max_eq_left (by omega)]

/-! ### The merged law (`sec:single-counter-law`) -/

/-- The merged law `ν̄`: the masses of the counters `0, 1, 2` combined at `2`, the other
masses unchanged (`sec:single-counter-law`); the pushforward of `ν` under `k ↦ max k 2`. -/
noncomputable def nuBar (ν : PMF ℕ) : PMF ℕ := ν.map fun k => max k 2

/-- The support of the merged law: the supported counters with `0, 1` replaced by `2`. -/
def suppBar (supp : Finset ℕ) : Finset ℕ := supp.image fun k => max k 2

/-- The masses of the merged law (`sec:single-counter-law`). -/
lemma nuBar_apply (ν : PMF ℕ) (k : ℕ) :
    nuBar ν k = if k = 2 then ν 0 + ν 1 + ν 2 else if k < 2 then 0 else ν k := by
  rw [nuBar, PMF.map_apply]
  by_cases h2 : k = 2
  · subst h2
    rw [if_pos rfl, tsum_eq_sum (s := {0, 1, 2}) (fun b hb => by
      rw [if_neg]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      omega)]
    simp [Finset.sum_insert, add_assoc]
  · rw [if_neg h2]
    by_cases hk : k < 2
    · rw [if_pos hk]
      exact ENNReal.tsum_eq_zero.mpr fun a => by rw [if_neg (by omega)]
    · rw [if_neg hk]
      refine (tsum_congr fun a => ?_).trans (tsum_ite_eq k ν)
      by_cases hak : a = k
      · subst hak
        rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hak, if_neg (by omega)]

/-- The merged law charges exactly the merged support. -/
lemma nuBar_ne_zero_iff (ν : PMF ℕ) (supp : Finset ℕ) (hsupp : ∀ k, ν k ≠ 0 ↔ k ∈ supp)
    (k : ℕ) : nuBar ν k ≠ 0 ↔ k ∈ suppBar supp := by
  rw [← PMF.mem_support_iff, nuBar, PMF.support_map, suppBar, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (hsupp a).mp ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (hsupp a).mpr ha, rfl⟩

/-- The mass of a counter is at most the merged mass of its merged counter. -/
lemma le_nuBar (ν : PMF ℕ) (k : ℕ) : ν k ≤ nuBar ν (max k 2) := by
  rw [nuBar, PMF.map_apply]
  refine le_trans ?_ (ENNReal.le_tsum k)
  rw [if_pos rfl]

/-- Every merged counter is at least `2`. -/
lemma two_le_of_mem_suppBar {supp : Finset ℕ} {k : ℕ} (hk : k ∈ suppBar supp) : 2 ≤ k := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hk
  exact le_max_right _ _

/-! ### The balanced presentation (`sec:single-counter-law`) -/

/-- The presentation of a finitely supported counter law with the balanced profiles as
common core on both sides (`sec:single-counter-law`): the core `S = supp ν̄`, the core
profiles `D k = rem k`, the composite profiles `C σ k = markRoot (rem k)`, and the merged
law `ν̄` on both sides. -/
noncomputable def balancedPresentation (ν : PMF ℕ) (supp : Finset ℕ)
    (hsupp : ∀ k, ν k ≠ 0 ↔ k ∈ supp) (hne : supp.Nonempty) : Presentation where
  S := suppBar supp
  D := rem
  ν := fun _ => nuBar ν
  supp := fun _ => suppBar supp
  C := fun _ k => MTree.markRoot (rem k)
  mem_supp := fun _ k => nuBar_ne_zero_iff ν supp hsupp k
  S_nonempty := hne.image _
  two_le_S := fun _ ha => two_le_of_mem_suppBar ha
  D_leaves := fun a ha => by rw [rem_leaves, max_eq_left (two_le_of_mem_suppBar ha)]
  D_noGraft := fun a _ => rem_noGraft a
  D_node := fun a _ => rem_node a
  S_subset_supp := fun _ => Finset.Subset.refl _
  two_le_supp := fun _ _ hk => two_le_of_mem_suppBar hk
  C_leaves := fun _ k hk => by
    rw [MTree.leaves_markRoot, rem_leaves, max_eq_left (two_le_of_mem_suppBar hk)]
  C_gnode := fun _ k _ => by
    obtain ⟨l, r, h⟩ := rem_node k
    exact ⟨l, r, by rw [h]; rfl⟩
  C_allComp := fun _ k hk => by
    obtain ⟨l, r, h⟩ := rem_node k
    have hng := rem_noGraft k
    rw [h] at hng ⊢
    refine ⟨⟨k, hk, ?_⟩, MTree.allComp_of_noGraft hng.1, MTree.allComp_of_noGraft hng.2⟩
    rw [MTree.flatten_eq_self_of_noGraft hng.1, MTree.flatten_eq_self_of_noGraft hng.2, h]
  C_core := fun _ _ _ => rfl

/-! ### Forgetting the counters and the types -/

variable {V : Type}

/-- Matching of state-and-counter labellings sees only the states
(`sec:single-counter-law`). -/
lemma fullSim_labRel_iff (Rv : V → V → Prop) (h : ℕ) (x y : FullLab (V × ℕ) h) :
    fullSim (labRel Rv) h x y ↔ fullSim Rv h (statesOf h x) (statesOf h y) :=
  exists_congr fun π => fullMatchesK_fst_iff Rv h π x y

/-- Matching of state-and-tagged-counter labellings sees only the states
(`sec:composite-process`). -/
lemma fullSim_cRel_iff (Rv : V → V → Prop) (h : ℕ)
    (x y : FullLab (Composite.CState V) h) :
    fullSim (Composite.cRel Rv) h x y ↔ fullSim Rv h (statesOf h x) (statesOf h y) :=
  exists_congr fun π => fullMatchesK_fst_iff Rv h π x y

/-! ### The law identification (`sec:single-counter-law`) -/

section Identification

variable (μ : PMF V) (ν : PMF ℕ) (v0 : V) (supp : Finset ℕ)
  (hsupp : ∀ k, ν k ≠ 0 ↔ k ∈ supp) (hne : supp.Nonempty) (Rv : V → V → Prop) (σ : Bool)

set_option quotPrecheck false in
/-- The balanced presentation of the section's counter law. -/
local notation "bP" => balancedPresentation ν supp hsupp hne

set_option quotPrecheck false in
/-- The Markov model of the balanced presentation over the section's state space. -/
local notation "bM" => (balancedPresentation ν supp hsupp hne).toModel Rv v0 μ

/-- The balanced profile of the counter `3` in terms of the profile of the counter `2`. -/
lemma rem_three' : rem 3 = MTree.node (rem 2) MTree.leaf := by
  rw [rem_three, rem_two]

/-- The root pair of a marked balanced profile is that of the profile. -/
lemma rootPair_markRoot_rem (k : ℕ) :
    rootPair σ (MTree.markRoot (rem k)) = rootPair σ (rem k) := by
  obtain ⟨l, r, h⟩ := rem_node k
  rw [h]
  rfl

/-- The forced identity at height `h` (`sec:single-counter-law`): below a vertex with the
counter `j`, the state labelling of the varying-offspring tree law has the law of the state
labelling of the tree law of the forced type with the balanced profile `rem j`, for every
root state. -/
def ForcedClaim (h : ℕ) : Prop :=
  ∀ j : ℕ, (σ, some (rem j)) ∈ (bP).live → ∀ v : V,
    (muM (varyK μ ν v0) (v, j) h).map (statesOf h)
      = (muM (bM).kernel ((bP).toLive (σ, some (rem j)), v) h).map (statesOf' h)

/-- The fresh identity at height `h` (`sec:single-counter-law`): below a fresh vertex, the
`ν`-mixture over the counter of the state labellings of the varying-offspring tree laws has
the law of the state labelling of the tree law of the fresh type, for every root state. -/
def FreshClaim (h : ℕ) : Prop :=
  ∀ v : V, (ν.bind fun k => (muM (varyK μ ν v0) (v, k) h).map (statesOf h))
    = (muM (bM).kernel ((bP).freshL σ, v) h).map (statesOf' h)

/-- The pair identity at height `h` (`sec:single-counter-law`): the state labellings of the
child pair below a counter `k` have the law of the state labellings of the child pair below
the balanced profile `rem k`. -/
def PairClaim (h : ℕ) : Prop :=
  ∀ k : ℕ, (rootPair σ (rem k)).1 ∈ (bP).live → (rootPair σ (rem k)).2 ∈ (bP).live →
    (Xi μ ν v0 k h).map (Prod.map (statesOf h) (statesOf h))
      = (prodPMF ((bM).rho ((bP).toLive (rootPair σ (rem k)).1) h)
          ((bM).rho ((bP).toLive (rootPair σ (rem k)).2) h)).map
            (Prod.map (statesOf' h) (statesOf' h))

/-- The fresh identity gives the identification of the fresh laws at height `h`. -/
lemma Tlaw_map_eq_of_fresh (h : ℕ) (hF : FreshClaim μ ν v0 supp hsupp hne Rv σ h) :
    (Tlaw μ ν v0 h).map (statesOf h) = ((bM).rho ((bP).freshL σ) h).map (statesOf' h) := by
  rw [Tlaw, freshQ, prodPMF_bind_eq, PMF.map_bind, (bP).rho_fresh_eq, PMF.map_bind]
  refine congrArg _ (funext fun v => ?_)
  rw [PMF.map_bind]
  exact hF v

/-- The forced identity at height `0`. -/
lemma forcedClaim_zero : ForcedClaim μ ν v0 supp hsupp hne Rv σ 0 := by
  intro j _ v
  rw [muM_zero, muM_zero, PMF.pure_map, PMF.pure_map]
  rfl

/-- The fresh identity at height `0`. -/
lemma freshClaim_zero : FreshClaim μ ν v0 supp hsupp hne Rv σ 0 := by
  intro v
  simp only [muM_zero, PMF.pure_map]
  show ν.bind (fun _ => PMF.pure (leaf v)) = PMF.pure (leaf v)
  exact PMF.bind_const ν _

/-- The pair identity at height `h` from the forced and fresh identities at height `h`
(`sec:single-counter-law`: the three splitting rules). -/
lemma pairClaim_of (h : ℕ) (hZ : ForcedClaim μ ν v0 supp hsupp hne Rv σ h)
    (hF : FreshClaim μ ν v0 supp hsupp hne Rv σ h) :
    PairClaim μ ν v0 supp hsupp hne Rv σ h := by
  intro k h1 h2
  by_cases h4 : 4 ≤ k
  · rw [rem_of_four_le h4] at h1 h2 ⊢
    simp only [Presentation.rootPair_node, typeOf_rem] at h1 h2 ⊢
    rw [Xi_of_four_le μ ν v0 h4, prodPMF_map_prod, prodPMF_map_prod, Zlaw, Zlaw,
      hZ (k / 2) h1 v0, hZ (k - k / 2) h2 v0, (bP).rho_forced_eq' Rv v0 μ h1,
      (bP).rho_forced_eq' Rv v0 μ h2]
  · by_cases h3 : k = 3
    · subst h3
      rw [rem_three'] at h1 h2 ⊢
      simp only [Presentation.rootPair_node, typeOf_rem, Presentation.typeOf_leaf] at h1 h2 ⊢
      rw [Xi_three, prodPMF_map_prod, prodPMF_map_prod, Zlaw, hZ 2 h1 v0,
        (bP).rho_forced_eq' Rv v0 μ h1, (bP).toLive_fresh,
        Tlaw_map_eq_of_fresh μ ν v0 supp hsupp hne Rv σ h hF]
    · have hk : k ≤ 2 := by omega
      rw [rem_of_le_two hk] at h1 h2 ⊢
      simp only [Presentation.rootPair_node, Presentation.typeOf_leaf] at h1 h2 ⊢
      rw [Xi_of_le_two μ ν v0 hk, prodPMF_map_prod, prodPMF_map_prod, (bP).toLive_fresh,
        Tlaw_map_eq_of_fresh μ ν v0 supp hsupp hne Rv σ h hF]

/-- The forced identity at height `h + 1` from the pair identity at height `h`. -/
lemma forcedClaim_succ (h : ℕ) (hX : PairClaim μ ν v0 supp hsupp hne Rv σ h) :
    ForcedClaim μ ν v0 supp hsupp hne Rv σ (h + 1) := by
  intro j hj v
  rw [muM_varyK_succ, PMF.map_comp, muM_succ, Model.pairMix_kernel, PMF.map_comp,
    (bP).childMix_forced' Rv v0 μ hj]
  obtain ⟨hl, hr⟩ := (bP).rootPair_mem_live_of_mem hj
  show (Xi μ ν v0 j h).map (branch v ∘ Prod.map (statesOf h) (statesOf h))
    = PMF.map (branch v ∘ Prod.map (statesOf' h) (statesOf' h)) _
  rw [← PMF.map_comp, ← PMF.map_comp, hX j hl hr]

/-- The fresh identity at height `h + 1` from the pair identity at height `h`
(`sec:single-counter-law`: the merged law charges the same profiles). -/
lemma freshClaim_succ (h : ℕ) (hX : PairClaim μ ν v0 supp hsupp hne Rv σ h) :
    FreshClaim μ ν v0 supp hsupp hne Rv σ (h + 1) := by
  intro v
  simp only [muM_varyK_succ, PMF.map_comp]
  rw [muM_succ, Model.pairMix_kernel, PMF.map_comp, (bP).childMix_fresh, PMF.map_bind]
  show ν.bind _ = (ν.map fun k => max k 2).bind _
  rw [PMF.bind_map]
  refine bind_congr_of_ne_zero ν fun k hk => ?_
  simp only [Function.comp_apply]
  have hC : rootPair σ ((bP).C σ (max k 2)) = rootPair σ (rem k) := by
    show rootPair σ (MTree.markRoot (rem (max k 2))) = _
    rw [rootPair_markRoot_rem, rem_max]
  have hk' : max k 2 ∈ (bP).supp σ := Finset.mem_image_of_mem _ ((hsupp k).mp hk)
  obtain ⟨hl, hr⟩ := (bP).rootPair_mem_live hk' (MTree.mem_subtrees_self _)
  rw [hC] at hl hr ⊢
  show (Xi μ ν v0 k h).map (branch v ∘ Prod.map (statesOf h) (statesOf h))
    = PMF.map (branch v ∘ Prod.map (statesOf' h) (statesOf' h)) _
  rw [← PMF.map_comp, ← PMF.map_comp, hX k hl hr]

/-- The forced and fresh identities at every height. -/
theorem forcedClaim_and_freshClaim :
    ∀ h, ForcedClaim μ ν v0 supp hsupp hne Rv σ h ∧ FreshClaim μ ν v0 supp hsupp hne Rv σ h
  | 0 => ⟨forcedClaim_zero μ ν v0 supp hsupp hne Rv σ,
      freshClaim_zero μ ν v0 supp hsupp hne Rv σ⟩
  | h + 1 =>
    have ih := forcedClaim_and_freshClaim h
    have hX := pairClaim_of μ ν v0 supp hsupp hne Rv σ h ih.1 ih.2
    ⟨forcedClaim_succ μ ν v0 supp hsupp hne Rv σ h hX,
      freshClaim_succ μ ν v0 supp hsupp hne Rv σ h hX⟩

/-- **The law identification** (`sec:single-counter-law`: "The state-labelled process is
unchanged in law"): the state labelling of the varying-offspring process `Tlaw μ ν v0 h`
and the state labelling of a fresh type of the balanced presentation of `ν̄` have the same
law, at every height. -/
theorem Tlaw_states_eq (h : ℕ) :
    (Tlaw μ ν v0 h).map (statesOf h)
      = (((balancedPresentation ν supp hsupp hne).toModel Rv v0 μ).rho
          ((balancedPresentation ν supp hsupp hne).freshL σ) h).map (statesOf' h) :=
  Tlaw_map_eq_of_fresh μ ν v0 supp hsupp hne Rv σ h
    (forcedClaim_and_freshClaim μ ν v0 supp hsupp hne Rv σ h).2

end Identification

/-! ### The failure probability (`sec:single-counter-law`) -/

/-- The directed failure mass under pushforwards: when the relation factors through two maps,
the failure mass of two laws is that of their pushforwards. -/
lemma failureD_map_eq {X X' : Type} (ρs ρt : PMF X) (Q : X → X → Prop) (f g : X → X')
    (Q' : X' → X' → Prop) (hQ : ∀ x y, Q x y ↔ Q' (f x) (g y)) :
    failureD ρs ρt Q = failureD (ρs.map f) (ρt.map g) Q' := by
  rw [failureD, failureD, tsum_map_mul]
  refine tsum_congr fun x => ?_
  congr 1
  rw [qE_eq_tsum_mul, qE_eq_tsum_mul, tsum_map_mul]
  refine tsum_congr fun y => ?_
  congr 1
  simp only [badInd]
  by_cases h : Q x y
  · rw [if_pos h, if_pos ((hQ x y).mp h)]
  · rw [if_neg h, if_neg fun h' => h ((hQ x y).mpr h')]

section Identification

variable (μ : PMF V) (ν : PMF ℕ) (v0 : V) (supp : Finset ℕ)
  (hsupp : ∀ k, ν k ≠ 0 ↔ k ∈ supp) (hne : supp.Nonempty) (Rv : V → V → Prop)

/-- **The failure probabilities agree** (`sec:single-counter-law`): the failure probability
of the varying-offspring process against itself at height `h` is the failure probability of
any two fresh types of the balanced presentation of `ν̄`. -/
theorem failProb_Tlaw_eq (h : ℕ) (σ σ' : Bool) :
    ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x
      = ((balancedPresentation ν supp hsupp hne).toModel Rv v0 μ).failProb
          ((balancedPresentation ν supp hsupp hne).freshL σ)
          ((balancedPresentation ν supp hsupp hne).freshL σ') h := by
  rw [Model.failProb, failureD_map_eq _ _ _ (statesOf' h) (statesOf' h) (fullSim Rv h)
    (fullSim_srel_iff _ h), ← Tlaw_states_eq μ ν v0 supp hsupp hne Rv σ h,
    ← Tlaw_states_eq μ ν v0 supp hsupp hne Rv σ' h]
  exact failureD_map_eq _ _ _ (statesOf h) (statesOf h) (fullSim Rv h) (fullSim_labRel_iff Rv h)

end Identification

/-! ### The inverse-sum and potential comparisons (`sec:single-counter-law`) -/

/-- **The inverse-sum comparison** (`sec:single-counter-law`): combining components only reduces
the required sum, and `p^{-α} ≤ p^{-5/2}` for `0 < p ≤ 1` and `α ≤ 5/2`, so
`∑_{k ∈ supp ν̄} ν̄(k)^{-α} ≤ ∑_{k ∈ supp ν} ν(k)^{-5/2}`. -/
theorem inverseSum_nuBar_le (ν : PMF ℕ) (supp : Finset ℕ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α ≤ 5 / 2) :
    ∑ k ∈ suppBar supp, (nuBar ν k) ^ (-α) ≤ ∑ k ∈ supp, (ν k) ^ (-(5 / 2 : ℝ)) := by
  rw [suppBar]
  refine le_trans (Finset.sum_image_le_of_nonneg fun _ _ => zero_le) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  calc (nuBar ν (max k 2)) ^ (-α) ≤ (ν k) ^ (-α) := rpow_neg_antitone hα0 (le_nuBar ν k)
    _ ≤ (ν k) ^ (-(5 / 2 : ℝ)) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (PMF.coe_le_one _ _) (by linarith)

/-- The inverse-sum comparison at exponent `2` (`sec:single-counter-law`). -/
theorem inverseSum_nuBar_le_two (ν : PMF ℕ) (supp : Finset ℕ) :
    ∑ k ∈ suppBar supp, (nuBar ν k) ^ (-(2 : ℝ)) ≤ ∑ k ∈ supp, (ν k) ^ (-(5 / 2 : ℝ)) :=
  inverseSum_nuBar_le ν supp (by norm_num) (by norm_num)

/-! ### The one-law statement recovered (`sec:single-counter-law`) -/

/-- The return bound `H` of the balanced presentation of a support, a function of the
support alone (`sec:single-counter-law`: the profiles are prescribed by the counters). -/
noncomputable def HretBal (supp : Finset ℕ) : ℕ :=
  HretOf (suppBar supp) rem (fun _ => suppBar supp) fun _ k => MTree.markRoot (rem k)

/-- The type count `T` of the balanced presentation of a support. -/
noncomputable def TcountBal (supp : Finset ℕ) : ℕ :=
  TcountOf (fun _ => suppBar supp) fun _ k => MTree.markRoot (rem k)

/-- The return bound of the balanced presentation is `HretBal`. -/
lemma balancedPresentation_Hret (ν : PMF ℕ) (supp : Finset ℕ)
    (hsupp : ∀ k, ν k ≠ 0 ↔ k ∈ supp) (hne : supp.Nonempty) :
    (balancedPresentation ν supp hsupp hne).Hret = HretBal supp := rfl

/-- The type count of the balanced presentation is `TcountBal`. -/
lemma balancedPresentation_Tcount (ν : PMF ℕ) (supp : Finset ℕ)
    (hsupp : ∀ k, ν k ≠ 0 ↔ k ∈ supp) (hne : supp.Nonempty) :
    (balancedPresentation ν supp hsupp hne).Tcount = TcountBal supp := rfl

/-- `1 ≤ T` for the balanced presentation. -/
lemma one_le_TcountBal (supp : Finset ℕ) : 1 ≤ TcountBal supp := one_le_TcountOf _ _

/-- **The one-law statement recovered, with explicit constants**
(`sec:single-counter-law`): for an exponent parameter set with `α ≤ 5/2`, a finite counter
support, and a bound `T₀ ≥ ∑_{k ∈ supp ν} ν(k)^{-5/2}`, with `H = HretBal supp`,
`T = TcountBal supp`, `B = max T₀ 1` and any `K > K₀(H, B)`: for every counter law with
that support, every state space with a reflexive symmetric compatibility, a distinguished
state of mass at least `1/2` and `η_α(μ) ≤ ε_K / 2`, the varying-offspring process fails
to match itself at height `h` with probability at most `2 K_match η_α(μ)`. -/
theorem original_one_law_matching_explicit (p : Params) (hα : p.α ≤ 5 / 2) (supp : Finset ℕ)
    (hne : supp.Nonempty) (T0 : ℝ) (Kc : ℝ)
    (hK : finiteK0 p (HretBal supp) (max T0 1) < Kc) (ν : PMF ℕ)
    (hsupp : ∀ k, ν k ≠ 0 ↔ k ∈ supp)
    (hbud : ∑ k ∈ supp, (ν k) ^ (-(5 / 2 : ℝ)) ≤ ENNReal.ofReal T0)
    {V : Type} (Rv : V → V → Prop) (v0 : V) (μ : PMF V) (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ v w, Rv v w → Rv w v) (hμ : ENNReal.ofReal (1 / 2) ≤ μ v0)
    (hη : PhiD p.α μ μ Rv ≤ ENNReal.ofReal
      (1 / 2 * finiteEps p (HretBal supp) (TcountBal supp) (max T0 1) Kc)) (h : ℕ) :
    ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x
      ≤ ENNReal.ofReal (finiteKmatch (HretBal supp) Kc / (1 / 2)) * PhiD p.α μ μ Rv := by
  rw [failProb_Tlaw_eq μ ν v0 supp hsupp hne Rv h false false]
  set P := balancedPresentation ν supp hsupp hne with hP
  set M := P.toModel Rv v0 μ with hM
  have hcompat : M.IsCompat := ⟨hrefl, hsymm⟩
  have hp : ENNReal.ofReal (1 / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hp1 : ENNReal.ofReal (1 / 2) ≤ 1 := ENNReal.ofReal_le_one.mpr (by norm_num)
  have hζη : M.zeta p.α ≤ M.eta p.α / ENNReal.ofReal (1 / 2) :=
    M.zeta_le_eta_div hcompat p.α_nonneg hp hp1 hμ
  have hζtop : M.zeta p.α ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hζη
    exact ENNReal.div_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hη) hp
  have hb0 : rE μ Rv v0 ≠ 0 := M.rE_zero_ne_zero_of_zeta_ne_top hζtop
  have hB : 1 ≤ max T0 1 := le_max_right _ _
  have hBs : ∀ t, (P.selection Rv v0 μ hcompat hb0).inverseSum p.α t ≤ ENNReal.ofReal (max T0 1) := by
    intro t
    refine (P.inverseSum_le Rv v0 μ hcompat hb0 p.α_nonneg t).trans ?_
    have key : ∑ a ∈ suppBar supp, (nuBar ν a) ^ (-p.α) ≤ ENNReal.ofReal (max T0 1) :=
      (inverseSum_nuBar_le ν supp p.α_nonneg hα).trans
        (hbud.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    exact max_le key key
  exact markov_matching_finite_eta p (HretBal supp) (TcountBal supp) (one_le_TcountBal supp)
    (max T0 1) hB Kc hK M hcompat (P.phase Rv v0 μ) (P.count_le_card Rv v0 μ)
    (P.selection Rv v0 μ hcompat hb0) hBs (P.freshPositive Rv v0 μ hcompat hb0)
    (P.commonReturns_Hret Rv v0 μ) (by norm_num) (by norm_num) hμ hη (P.freshL false)
    (P.freshL false) (P.phase_freshL_eq Rv v0 μ false false) h

/-- **The one-law statement recovered** (`sec:single-counter-law`): for an exponent
parameter set with `α ≤ 5/2`, a finite counter support and a bound `T₀`, there are
constants `K, ε` depending only on these data such that, for every counter law `ν` with that
support and `∑_{k ∈ supp ν} ν(k)^{-5/2} ≤ T₀`, every state space with a reflexive symmetric
compatibility, a distinguished state `0` of mass at least `1/2` and `η_α(μ) ≤ ε`, the
varying-offspring process of the manuscript fails to match itself at every height with
probability at most `K η_α(μ)`. -/
theorem original_one_law_matching (p : Params) (hα : p.α ≤ 5 / 2) (supp : Finset ℕ)
    (hne : supp.Nonempty) (T0 : ℝ) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ ν : PMF ℕ, (∀ k, ν k ≠ 0 ↔ k ∈ supp) →
      ∑ k ∈ supp, (ν k) ^ (-(5 / 2 : ℝ)) ≤ ENNReal.ofReal T0 →
      ∀ {V : Type} (Rv : V → V → Prop) (v0 : V) (μ : PMF V),
        (∀ v, Rv v v) → (∀ v w, Rv v w → Rv w v) → ENNReal.ofReal (1 / 2) ≤ μ v0 →
        PhiD p.α μ μ Rv ≤ ENNReal.ofReal ε →
        ∀ h, ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x
          ≤ ENNReal.ofReal Kc * PhiD p.α μ μ Rv := by
  set K0 := finiteK0 p (HretBal supp) (max T0 1) with hK0
  have hK : K0 < K0 + 1 := by linarith
  have hεpos := finiteEps_pos p (HretBal supp) (TcountBal supp) (one_le_TcountBal supp)
    (max T0 1) (le_max_right _ _) (K0 + 1) hK
  refine ⟨finiteKmatch (HretBal supp) (K0 + 1) / (1 / 2),
    1 / 2 * finiteEps p (HretBal supp) (TcountBal supp) (max T0 1) (K0 + 1), by positivity, ?_⟩
  intro ν hsupp hbud V Rv v0 μ hrefl hsymm hμ hη h
  exact original_one_law_matching_explicit p hα supp hne T0 (K0 + 1) hK ν hsupp hbud Rv v0 μ
    hrefl hsymm hμ hη h

/-- **The one-law statement at exponent `2`** (`sec:single-counter-law`): the hypotheses
`∑ ν(k)^{-5/2} ≤ T₀`, `μ(0) ≥ 1/2` and `η_2(μ) ≤ ε` of the manuscript give failure
probability at most `K η_2(μ)` at every height, with `K, ε` depending only on `T₀` and the
counter support. -/
theorem original_one_law_matching_two (supp : Finset ℕ) (hne : supp.Nonempty) (T0 : ℝ) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ ν : PMF ℕ, (∀ k, ν k ≠ 0 ↔ k ∈ supp) →
      ∑ k ∈ supp, (ν k) ^ (-(5 / 2 : ℝ)) ≤ ENNReal.ofReal T0 →
      ∀ {V : Type} (Rv : V → V → Prop) (v0 : V) (μ : PMF V),
        (∀ v, Rv v v) → (∀ v w, Rv v w → Rv w v) → ENNReal.ofReal (1 / 2) ≤ μ v0 →
        PhiD 2 μ μ Rv ≤ ENNReal.ofReal ε →
        ∀ h, ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x
          ≤ ENNReal.ofReal Kc * PhiD 2 μ μ Rv :=
  original_one_law_matching paramsTwo (by rw [paramsTwo_α]; norm_num) supp hne T0

/-- **The one-law statement at exponent `2` under the `η_{5/2}` hypothesis**
(`sec:single-counter-law`: `η_2(μ) ≤ η_{5/2}(μ)`, so the original hypotheses imply the new
ones): `η_{5/2}(μ) ≤ ε` gives failure probability at most `K η_{5/2}(μ)`. -/
theorem original_one_law_matching_fiveHalf (supp : Finset ℕ) (hne : supp.Nonempty) (T0 : ℝ) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ ν : PMF ℕ, (∀ k, ν k ≠ 0 ↔ k ∈ supp) →
      ∑ k ∈ supp, (ν k) ^ (-(5 / 2 : ℝ)) ≤ ENNReal.ofReal T0 →
      ∀ {V : Type} (Rv : V → V → Prop) (v0 : V) (μ : PMF V),
        (∀ v, Rv v v) → (∀ v w, Rv v w → Rv w v) → ENNReal.ofReal (1 / 2) ≤ μ v0 →
        PhiD (5 / 2) μ μ Rv ≤ ENNReal.ofReal ε →
        ∀ h, ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x
          ≤ ENNReal.ofReal Kc * PhiD (5 / 2) μ μ Rv := by
  obtain ⟨Kc, ε, hε, hbound⟩ := original_one_law_matching_two supp hne T0
  refine ⟨Kc, ε, hε, ?_⟩
  intro ν hsupp hbud V Rv v0 μ hrefl hsymm hμ hη h
  have h25 : PhiD 2 μ μ Rv ≤ PhiD (5 / 2) μ μ Rv := PhiD_mono_exponent μ μ Rv (by norm_num)
  calc ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x
      ≤ ENNReal.ofReal Kc * PhiD 2 μ μ Rv :=
        hbound ν hsupp hbud Rv v0 μ hrefl hsymm hμ (h25.trans hη) h
    _ ≤ ENNReal.ofReal Kc * PhiD (5 / 2) μ μ Rv := mul_le_mul_right h25 _

/-- **Any fixed positive lower bound on the matching probability** (`sec:single-counter-law`:
"The conclusion with any fixed positive lower bound on matching probability follows by
decreasing the threshold further"): for every `δ > 0` a threshold `ε` such that `η_α(μ) ≤ ε`
gives failure probability at most `δ` at every height. -/
theorem original_one_law_matching_prob (p : Params) (hα : p.α ≤ 5 / 2) (supp : Finset ℕ)
    (hne : supp.Nonempty) (T0 : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : PMF ℕ, (∀ k, ν k ≠ 0 ↔ k ∈ supp) →
      ∑ k ∈ supp, (ν k) ^ (-(5 / 2 : ℝ)) ≤ ENNReal.ofReal T0 →
      ∀ {V : Type} (Rv : V → V → Prop) (v0 : V) (μ : PMF V),
        (∀ v, Rv v v) → (∀ v w, Rv v w → Rv w v) → ENNReal.ofReal (1 / 2) ≤ μ v0 →
        PhiD p.α μ μ Rv ≤ ENNReal.ofReal ε →
        ∀ h, ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x
          ≤ ENNReal.ofReal δ := by
  obtain ⟨Kc, ε, hε, hbound⟩ := original_one_law_matching p hα supp hne T0
  have hden : 0 < |Kc| + 1 := by positivity
  refine ⟨min ε (δ / (|Kc| + 1)), lt_min hε (by positivity), ?_⟩
  intro ν hsupp hbud V Rv v0 μ hrefl hsymm hμ hη h
  have hη' : PhiD p.α μ μ Rv ≤ ENNReal.ofReal ε :=
    hη.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hη'' : PhiD p.α μ μ Rv ≤ ENNReal.ofReal (δ / (|Kc| + 1)) :=
    hη.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  refine (hbound ν hsupp hbud Rv v0 μ hrefl hsymm hμ hη' h).trans ?_
  by_cases hK : 0 ≤ Kc
  · calc ENNReal.ofReal Kc * PhiD p.α μ μ Rv
        ≤ ENNReal.ofReal Kc * ENNReal.ofReal (δ / (|Kc| + 1)) := mul_le_mul_right hη'' _
      _ = ENNReal.ofReal (Kc * (δ / (|Kc| + 1))) := (ENNReal.ofReal_mul hK).symm
      _ ≤ ENNReal.ofReal δ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [abs_of_nonneg hK, mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]
    exact zero_le

/-! ### The composite profiles (`sec:composite-process`) -/

/-- The balanced profile of the counter `v` with the designated leaf, the leftmost of the
next fresh vertices of minimal depth (`sec:composite-process`), replaced by the tree `g`
(`sec:composite-process`: "inserting one core descent into a specified leaf of another"). -/
def graftPort (g : MTree) (v : ℕ) : MTree :=
  if h4 : 4 ≤ v then MTree.node (graftPort g (v / 2)) (rem (v - v / 2))
  else if v = 3 then MTree.node (rem 2) g
  else MTree.node g MTree.leaf
termination_by v
decreasing_by all_goals omega

/-- The grafted profile of a counter `v ≥ 4`: the designated path continues to the left. -/
lemma graftPort_of_four_le (g : MTree) {v : ℕ} (hv : 4 ≤ v) :
    graftPort g v = MTree.node (graftPort g (v / 2)) (rem (v - v / 2)) := by
  rw [graftPort, dif_pos hv]

/-- The grafted profile of the counter `3`: the designated leaf is the right child. -/
lemma graftPort_three (g : MTree) : graftPort g 3 = MTree.node (rem 2) g := by
  rw [graftPort, dif_neg (by omega), if_pos rfl]

/-- The grafted profile of a counter at most `2`: the designated leaf is the left child. -/
lemma graftPort_of_le_two (g : MTree) {v : ℕ} (hv : v ≤ 2) :
    graftPort g v = MTree.node g MTree.leaf := by
  rw [graftPort, dif_neg (by omega), if_neg (by omega)]

/-- The grafted profile has `max v 2 - 1` leaves of the balanced profile plus the leaves of
the graft (`sec:composite-process`: the arity `a + b - 1`). -/
lemma graftPort_leaves (g : MTree) (v : ℕ) :
    (graftPort g v).leaves = max v 2 - 1 + g.leaves := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    by_cases h4 : 4 ≤ v
    · rw [graftPort_of_four_le g h4, MTree.leaves, ih (v / 2) (by omega), rem_leaves]
      omega
    · by_cases h3 : v = 3
      · subst h3
        rw [graftPort_three, MTree.leaves, rem_leaves]
        omega
      · rw [graftPort_of_le_two g (by omega), MTree.leaves, MTree.leaves]
        omega

/-- The grafted profile flattens to the balanced profile when the graft flattens to a
leaf. -/
lemma graftPort_flatten {g : MTree} (hg : g.flatten = MTree.leaf) (v : ℕ) :
    (graftPort g v).flatten = rem v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    by_cases h4 : 4 ≤ v
    · rw [graftPort_of_four_le g h4, MTree.flatten, ih (v / 2) (by omega),
        MTree.flatten_eq_self_of_noGraft (rem_noGraft _), rem_of_four_le h4]
    · by_cases h3 : v = 3
      · subst h3
        rw [graftPort_three, MTree.flatten, hg, MTree.flatten_eq_self_of_noGraft (rem_noGraft _),
          rem_three, rem_two]
      · rw [graftPort_of_le_two g (by omega), MTree.flatten, hg, MTree.flatten,
          rem_of_le_two (by omega)]

/-- Every grafted profile is a node. -/
lemma graftPort_node (g : MTree) (v : ℕ) : ∃ l r, graftPort g v = MTree.node l r := by
  by_cases h4 : 4 ≤ v
  · exact ⟨_, _, graftPort_of_four_le g h4⟩
  · by_cases h3 : v = 3
    · exact ⟨_, _, h3 ▸ graftPort_three g⟩
    · exact ⟨_, _, graftPort_of_le_two g (by omega)⟩

/-- A grafted profile is not a leaf. -/
lemma graftPort_ne_leaf (g : MTree) (v : ℕ) : graftPort g v ≠ MTree.leaf := by
  obtain ⟨l, r, h⟩ := graftPort_node g v
  rw [h]
  exact MTree.noConfusion

/-- The type of a grafted profile is the forced type with that remaining tree. -/
lemma typeOf_graftPort (σ : Bool) (g : MTree) (v : ℕ) :
    typeOf σ (graftPort g v) = (σ, some (graftPort g v)) :=
  Presentation.typeOf_of_ne_leaf σ (graftPort_ne_leaf g v)

/-- The grafted profile depends on the counter only through `max v 2`. -/
lemma graftPort_max (g : MTree) (v : ℕ) : graftPort g (max v 2) = graftPort g v := by
  by_cases hv : v ≤ 2
  · rw [max_eq_right hv, graftPort_of_le_two g le_rfl, graftPort_of_le_two g hv]
  · rw [max_eq_left (by omega)]

/-- A grafted profile is a composite profile when the graft is. -/
lemma allComp_graftPort {S : Finset ℕ} {D : ℕ → MTree} {g : MTree}
    (hg : MTree.AllComp S D g) (v : ℕ) : MTree.AllComp S D (graftPort g v) := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    by_cases h4 : 4 ≤ v
    · rw [graftPort_of_four_le g h4]
      exact ⟨ih (v / 2) (by omega), MTree.allComp_of_noGraft (rem_noGraft _)⟩
    · by_cases h3 : v = 3
      · subst h3
        rw [graftPort_three]
        exact ⟨MTree.allComp_of_noGraft (rem_noGraft _), hg⟩
      · rw [graftPort_of_le_two g (by omega)]
        exact ⟨hg, trivial⟩

/-- The marked balanced profile of a core counter is a composite profile. -/
lemma allComp_markRoot_rem {S : Finset ℕ} {b : ℕ} (hb : max b 2 ∈ S) :
    MTree.AllComp S rem (MTree.markRoot (rem b)) := by
  obtain ⟨l, r, h⟩ := rem_node b
  have hng := rem_noGraft b
  rw [h] at hng ⊢
  refine ⟨⟨max b 2, hb, ?_⟩, MTree.allComp_of_noGraft hng.1, MTree.allComp_of_noGraft hng.2⟩
  rw [MTree.flatten_eq_self_of_noGraft hng.1, MTree.flatten_eq_self_of_noGraft hng.2, rem_max, h]

/-- The composite profile of a counter under the exceptional data `exc`
(`sec:composite-process`): the balanced profile of `a` with the
marked balanced profile of `b` at the designated leaf for a declared pair `(a, b)`, the
marked balanced profile otherwise. -/
def compProfile (exc : ℕ → Option (ℕ × ℕ)) (k : ℕ) : MTree :=
  match exc k with
  | some p => MTree.markRoot (graftPort (MTree.markRoot (rem p.2)) p.1)
  | none => MTree.markRoot (rem k)

/-- The composite profile of a declared exceptional counter. -/
lemma compProfile_of_some {exc : ℕ → Option (ℕ × ℕ)} {k : ℕ} {p : ℕ × ℕ} (h : exc k = some p) :
    compProfile exc k = MTree.markRoot (graftPort (MTree.markRoot (rem p.2)) p.1) := by
  simp only [compProfile, h]

/-- The composite profile of an ordinary counter. -/
lemma compProfile_of_none {exc : ℕ → Option (ℕ × ℕ)} {k : ℕ} (h : exc k = none) :
    compProfile exc k = MTree.markRoot (rem k) := by
  simp only [compProfile, h]

/-- The root pair of a marked node is that of the node. -/
lemma rootPair_markRoot_node (σ : Bool) (l r : MTree) :
    rootPair σ (MTree.markRoot (MTree.node l r)) = rootPair σ (MTree.node l r) := rfl

/-- The data of the prescribed composite two-law process (`sec:composite-process`,
`sec:composite-process`): on each side `σ`, a counter law `ν σ` with finite support `K σ`
and exceptional data `exc σ`; a common core `S` of counters at least `2` and at most `N`;
no counter at most `N` is exceptional; every charged ordinary counter merges into the core;
every declared pair merges into the core and its counter is the arity `a + b - 1`
(`sec:composite-process`) of the composite profile. -/
structure CompositeData where
  /-- the exceptional data of each side -/
  exc : Bool → ℕ → Option (ℕ × ℕ)
  /-- the counter laws -/
  ν : Bool → PMF ℕ
  /-- the finite supports of the counter laws -/
  K : Bool → Finset ℕ
  /-- the common core -/
  S : Finset ℕ
  /-- the bound above which the exceptional counters lie (`sec:composite-process`) -/
  N : ℕ
  mem_K : ∀ σ k, ν σ k ≠ 0 ↔ k ∈ K σ
  exc_none : ∀ σ j, j ≤ N → exc σ j = none
  two_le_S : ∀ a ∈ S, 2 ≤ a
  S_le_N : ∀ a ∈ S, a ≤ N
  S_subset_K : ∀ σ, S ⊆ K σ
  S_nonempty : S.Nonempty
  core_of_none : ∀ σ k, k ∈ K σ → exc σ k = none → max k 2 ∈ S
  pair_spec : ∀ σ z p, exc σ z = some p →
    max p.1 2 ∈ S ∧ max p.2 2 ∈ S ∧ z = max p.1 2 + max p.2 2 - 1

namespace CompositeData

variable (C : CompositeData)

/-- The core is at most `N`, so `2 ≤ N`. -/
lemma two_le_N : 2 ≤ C.N := by
  obtain ⟨a, ha⟩ := C.S_nonempty
  exact (C.two_le_S a ha).trans (C.S_le_N a ha)

/-- A declared exceptional counter exceeds `N`. -/
lemma lt_of_exc_some {σ : Bool} {z : ℕ} {p : ℕ × ℕ} (h : C.exc σ z = some p) : C.N < z := by
  by_contra hle
  rw [C.exc_none σ z (by omega)] at h
  cases h

/-- The members of a declared pair are at most `N`. -/
lemma pair_le_N {σ : Bool} {z : ℕ} {p : ℕ × ℕ} (h : C.exc σ z = some p) :
    p.1 ≤ C.N ∧ p.2 ≤ C.N := by
  obtain ⟨h1, h2, -⟩ := C.pair_spec σ z p h
  exact ⟨(le_max_left _ _).trans (C.S_le_N _ h1), (le_max_left _ _).trans (C.S_le_N _ h2)⟩

/-- **The presentation of the composite process** (`sec:composite-process`): the merged laws
on both sides, the balanced core profiles, and the composite profiles of the declared
pairs. -/
noncomputable def toPresentation : Presentation where
  S := C.S
  D := rem
  ν := fun σ => nuBar (C.ν σ)
  supp := fun σ => suppBar (C.K σ)
  C := fun σ k => compProfile (C.exc σ) k
  mem_supp := fun σ k => nuBar_ne_zero_iff (C.ν σ) (C.K σ) (C.mem_K σ) k
  S_nonempty := C.S_nonempty
  two_le_S := C.two_le_S
  D_leaves := fun a ha => by rw [rem_leaves, max_eq_left (C.two_le_S a ha)]
  D_noGraft := fun a _ => rem_noGraft a
  D_node := fun a _ => rem_node a
  S_subset_supp := fun σ a ha => by
    refine Finset.mem_image.mpr ⟨a, C.S_subset_K σ ha, ?_⟩
    exact max_eq_left (C.two_le_S a ha)
  two_le_supp := fun _ _ hk => two_le_of_mem_suppBar hk
  C_leaves := fun σ k hk => by
    rcases h : C.exc σ k with _ | p
    · rw [compProfile_of_none h, MTree.leaves_markRoot, rem_leaves,
        max_eq_left (two_le_of_mem_suppBar hk)]
    · obtain ⟨-, -, hz⟩ := C.pair_spec σ k p h
      rw [compProfile_of_some h, MTree.leaves_markRoot, graftPort_leaves, MTree.leaves_markRoot,
        rem_leaves, hz]
      omega
  C_gnode := fun σ k _ => by
    rcases h : C.exc σ k with _ | p
    · rw [compProfile_of_none h]
      obtain ⟨l, r, hlr⟩ := rem_node k
      exact ⟨l, r, by rw [hlr]; rfl⟩
    · rw [compProfile_of_some h]
      obtain ⟨l, r, hlr⟩ := graftPort_node (MTree.markRoot (rem p.2)) p.1
      exact ⟨l, r, by rw [hlr]; rfl⟩
  C_allComp := fun σ k hk => by
    rcases h : C.exc σ k with _ | p
    · rw [compProfile_of_none h]
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hk
      have hnone : C.exc σ k' = none := by
        by_cases hk2 : k' ≤ 2
        · exact C.exc_none σ k' (hk2.trans C.two_le_N)
        · rwa [max_eq_left (by omega)] at h
      have hk'2 : max k' 2 ∈ C.S := C.core_of_none σ k' hk' hnone
      refine allComp_markRoot_rem ?_
      rw [max_eq_left (le_max_right k' 2)]
      exact hk'2
    · obtain ⟨ha, hb, -⟩ := C.pair_spec σ k p h
      rw [compProfile_of_some h]
      obtain ⟨l, r, hlr⟩ := graftPort_node (MTree.markRoot (rem p.2)) p.1
      have hcomp := allComp_graftPort (S := C.S) (allComp_markRoot_rem hb) p.1
      rw [hlr] at hcomp ⊢
      refine ⟨⟨max p.1 2, ha, ?_⟩, hcomp.1, hcomp.2⟩
      have hfl := graftPort_flatten (MTree.flatten_markRoot (rem p.2)) p.1
      rw [hlr] at hfl
      rw [MTree.flatten] at hfl
      rw [hfl, rem_max]
  C_core := fun σ a ha => by
    show compProfile (C.exc σ) a = MTree.markRoot (rem a)
    exact compProfile_of_none (C.exc_none σ a (C.S_le_N a ha))

end CompositeData

/-! ### The law identification for the composite process (`sec:composite-process`) -/

section CompositeIdentification

open Composite

variable (C : CompositeData) (μ : PMF V) (v0 : V) (Rv : V → V → Prop) (σ : Bool)

set_option quotPrecheck false in
/-- The presentation of the section's composite data. -/
local notation "cP" => CompositeData.toPresentation C

set_option quotPrecheck false in
/-- The Markov model of the composite presentation over the section's state space. -/
local notation "cM" => (CompositeData.toPresentation C).toModel Rv v0 μ

set_option quotPrecheck false in
/-- The composite kernel of the section's side. -/
local notation "cK" => compK (C.exc σ) μ (C.ν σ) v0

/-- The composite kernel ignores the state of the root. -/
lemma compK_fst (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (v : V) (c : CtrC) :
    compK exc μ ν v0 (v, c) = compK exc μ ν v0 (v0, c) := by
  cases c <;> rfl

/-- The pair mixture of the composite kernel is the cell law of the tagged counter. -/
lemma pairMix_compK (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (v : V) (c : CtrC) (h : ℕ) :
    pairMix (compK exc μ ν v0) (v, c) h = cXi exc μ ν v0 c h := by
  rw [pairMix, compK_fst]
  rfl

/-- The tree law of the composite kernel at height `h + 1`. -/
lemma muM_compK_succ (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (v : V) (c : CtrC) (h : ℕ) :
    muM (compK exc μ ν v0) (v, c) (h + 1) = (cXi exc μ ν v0 c h).map (branch (v, c)) := by
  rw [muM_succ, pairMix_compK]

/-- The frozen law is the tree law from the forced root. -/
lemma cZ_eq (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (c : CtrC) (h : ℕ) :
    cZ exc μ ν v0 c h = muM (compK exc μ ν v0) (v0, c) h := rfl

/-- The running value of the designated path is at most the counter. -/
lemma val_le (a i : ℕ) : val a i ≤ a := Nat.div_le_self _ _

/-- The type of a marked balanced profile is the forced type with that remaining tree. -/
lemma typeOf_markRoot_rem (b : ℕ) :
    typeOf σ (MTree.markRoot (rem b)) = (σ, some (MTree.markRoot (rem b))) := by
  obtain ⟨l, r, h⟩ := rem_node b
  rw [h]
  rfl

/-- The forced identity for ordinary counters at height `h` (`sec:composite-process`):
below a forced vertex with an ordinary counter `j ≤ N`, whether a plain or a graft root, the
state labelling of the composite tree law has the law of the state labelling of the tree law
of the forced type with the balanced profile. -/
def CForcedClaim (h : ℕ) : Prop :=
  ∀ j, j ≤ C.N → ∀ τ, (τ = rem j ∨ τ = MTree.markRoot (rem j)) → (σ, some τ) ∈ (cP).live →
    ∀ v : V, (muM cK (v, CtrC.ord j) h).map (statesOf h)
      = (muM (cM).kernel ((cP).toLive (σ, some τ), v) h).map (statesOf' h)

/-- The forced identity for marked counters at height `h` (`sec:composite-process`): below a
marked vertex of the pair `(a, b)` at stage `i`, the state labelling of the composite tree
law has the law of the state labelling of the tree law of the forced type with the grafted
profile of the running value. -/
def CMarkClaim (h : ℕ) : Prop :=
  ∀ a b i, a ≤ C.N → b ≤ C.N →
    (σ, some (graftPort (MTree.markRoot (rem b)) (val a i))) ∈ (cP).live →
    ∀ v : V, (muM cK (v, CtrC.mark a b i) h).map (statesOf h)
      = (muM (cM).kernel
          ((cP).toLive (σ, some (graftPort (MTree.markRoot (rem b)) (val a i))), v) h).map
            (statesOf' h)

/-- The fresh identity at height `h` for the composite process (`sec:composite-process`). -/
def CFreshClaim (h : ℕ) : Prop :=
  ∀ v : V, ((C.ν σ).bind fun k => (muM cK (v, CtrC.ord k) h).map (statesOf h))
    = (muM (cM).kernel ((cP).freshL σ, v) h).map (statesOf' h)

/-- The pair identity for ordinary counters at height `h`. -/
def CPairOrd (h : ℕ) : Prop :=
  ∀ j, j ≤ C.N → (rootPair σ (rem j)).1 ∈ (cP).live → (rootPair σ (rem j)).2 ∈ (cP).live →
    (cXi (C.exc σ) μ (C.ν σ) v0 (CtrC.ord j) h).map (Prod.map (statesOf h) (statesOf h))
      = (prodPMF ((cM).rho ((cP).toLive (rootPair σ (rem j)).1) h)
          ((cM).rho ((cP).toLive (rootPair σ (rem j)).2) h)).map
            (Prod.map (statesOf' h) (statesOf' h))

/-- The pair identity for marked counters at height `h`. -/
def CPairMark (h : ℕ) : Prop :=
  ∀ a b i, a ≤ C.N → b ≤ C.N →
    (rootPair σ (graftPort (MTree.markRoot (rem b)) (val a i))).1 ∈ (cP).live →
    (rootPair σ (graftPort (MTree.markRoot (rem b)) (val a i))).2 ∈ (cP).live →
    (cXi (C.exc σ) μ (C.ν σ) v0 (CtrC.mark a b i) h).map (Prod.map (statesOf h) (statesOf h))
      = (prodPMF
          ((cM).rho ((cP).toLive (rootPair σ (graftPort (MTree.markRoot (rem b)) (val a i))).1) h)
          ((cM).rho ((cP).toLive (rootPair σ (graftPort (MTree.markRoot (rem b)) (val a i))).2)
            h)).map (Prod.map (statesOf' h) (statesOf' h))

/-- The fresh identity gives the identification of the fresh laws at height `h`. -/
lemma cT_map_eq_of_fresh (h : ℕ) (hF : CFreshClaim C μ v0 Rv σ h) :
    (cT (C.exc σ) μ (C.ν σ) v0 h).map (statesOf h)
      = ((cM).rho ((cP).freshL σ) h).map (statesOf' h) := by
  rw [cT, freshC, PMF.bind_map, freshQ, prodPMF_bind_eq, PMF.map_bind, (cP).rho_fresh_eq,
    PMF.map_bind]
  refine congrArg _ (funext fun v => ?_)
  rw [PMF.map_bind]
  exact hF v

/-- The forced identity for ordinary counters at height `0`. -/
lemma cForcedClaim_zero : CForcedClaim C μ v0 Rv σ 0 := by
  intro j _ τ _ _ v
  rw [muM_zero, muM_zero, PMF.pure_map, PMF.pure_map]
  rfl

/-- The forced identity for marked counters at height `0`. -/
lemma cMarkClaim_zero : CMarkClaim C μ v0 Rv σ 0 := by
  intro a b i _ _ _ v
  rw [muM_zero, muM_zero, PMF.pure_map, PMF.pure_map]
  rfl

/-- The fresh identity at height `0`. -/
lemma cFreshClaim_zero : CFreshClaim C μ v0 Rv σ 0 := by
  intro v
  simp only [muM_zero, PMF.pure_map]
  show (C.ν σ).bind (fun _ => PMF.pure (leaf v)) = PMF.pure (leaf v)
  exact PMF.bind_const (C.ν σ) _

/-- The pair identity for ordinary counters at height `h` from the forced and fresh
identities at height `h` (`sec:composite-process`, rule (i)). -/
lemma cPairOrd_of (h : ℕ) (hZ : CForcedClaim C μ v0 Rv σ h) (hF : CFreshClaim C μ v0 Rv σ h) :
    CPairOrd C μ v0 Rv σ h := by
  intro j hjN h1 h2
  by_cases h4 : 4 ≤ j
  · rw [rem_of_four_le h4] at h1 h2 ⊢
    simp only [Presentation.rootPair_node, typeOf_rem] at h1 h2 ⊢
    rw [cXi_ord_none_of_ge _ _ _ _ (C.exc_none σ j hjN) h4, prodPMF_map_prod, prodPMF_map_prod,
      cZ_eq, cZ_eq, hZ (j / 2) (by omega) _ (Or.inl rfl) h1 v0,
      hZ (j - j / 2) (by omega) _ (Or.inl rfl) h2 v0, (cP).rho_forced_eq' Rv v0 μ h1,
      (cP).rho_forced_eq' Rv v0 μ h2]
  · by_cases h3 : j = 3
    · subst h3
      rw [rem_three'] at h1 h2 ⊢
      simp only [Presentation.rootPair_node, typeOf_rem, Presentation.typeOf_leaf] at h1 h2 ⊢
      rw [cXi_ord_none_three _ _ _ _ (C.exc_none σ 3 hjN) rfl, prodPMF_map_prod,
        prodPMF_map_prod, cZ_eq, hZ 2 (by omega) _ (Or.inl rfl) h1 v0,
        (cP).rho_forced_eq' Rv v0 μ h1, (cP).toLive_fresh, cT_map_eq_of_fresh C μ v0 Rv σ h hF]
    · have hk : j ≤ 2 := by omega
      rw [rem_of_le_two hk] at h1 h2 ⊢
      simp only [Presentation.rootPair_node, Presentation.typeOf_leaf] at h1 h2 ⊢
      rw [cXi_ord_none_le_two _ _ _ _ (C.exc_none σ j hjN) hk, prodPMF_map_prod,
        prodPMF_map_prod, (cP).toLive_fresh, cT_map_eq_of_fresh C μ v0 Rv σ h hF]

/-- The pair identity for marked counters at height `h` from the forced, marked and fresh
identities at height `h` (`sec:composite-process`, rules (ii) and (iii)). -/
lemma cPairMark_of (h : ℕ) (hZ : CForcedClaim C μ v0 Rv σ h) (hMk : CMarkClaim C μ v0 Rv σ h)
    (hF : CFreshClaim C μ v0 Rv σ h) : CPairMark C μ v0 Rv σ h := by
  intro a b i haN hbN h1 h2
  have hvN : val a i ≤ C.N := (val_le a i).trans haN
  by_cases h4 : 4 ≤ val a i
  · rw [graftPort_of_four_le _ h4] at h1 h2 ⊢
    simp only [Presentation.rootPair_node, typeOf_rem, typeOf_graftPort] at h1 h2 ⊢
    rw [cXi_mark_of_ge _ _ _ _ h4, prodPMF_map_prod, prodPMF_map_prod, cZ_eq, cZ_eq]
    rw [← val_succ] at h1 h2 ⊢
    rw [hMk a b (i + 1) haN hbN h1 v0,
      hZ (val a i - val a (i + 1)) (by omega) _ (Or.inl rfl) h2 v0,
      (cP).rho_forced_eq' Rv v0 μ h1, (cP).rho_forced_eq' Rv v0 μ h2]
  · by_cases h3 : val a i = 3
    · rw [h3, graftPort_three] at h1 h2 ⊢
      simp only [Presentation.rootPair_node, typeOf_rem, typeOf_markRoot_rem] at h1 h2 ⊢
      rw [cXi_mark_three _ _ _ _ h3, prodPMF_map_prod, prodPMF_map_prod, cZ_eq, cZ_eq,
        hZ 2 (by omega) _ (Or.inl rfl) h1 v0, hZ b hbN _ (Or.inr rfl) h2 v0,
        (cP).rho_forced_eq' Rv v0 μ h1, (cP).rho_forced_eq' Rv v0 μ h2]
    · have hk : val a i ≤ 2 := by omega
      rw [graftPort_of_le_two _ hk] at h1 h2 ⊢
      simp only [Presentation.rootPair_node, typeOf_markRoot_rem, Presentation.typeOf_leaf]
        at h1 h2 ⊢
      rw [cXi_mark_le_two _ _ _ _ hk, prodPMF_map_prod, prodPMF_map_prod, cZ_eq,
        hZ b hbN _ (Or.inr rfl) h1 v0, (cP).rho_forced_eq' Rv v0 μ h1, (cP).toLive_fresh,
        cT_map_eq_of_fresh C μ v0 Rv σ h hF]

/-- The forced identity for ordinary counters at height `h + 1` from the pair identity at
height `h`. -/
lemma cForcedClaim_succ (h : ℕ) (hX : CPairOrd C μ v0 Rv σ h) :
    CForcedClaim C μ v0 Rv σ (h + 1) := by
  intro j hjN τ hτ hj v
  rw [muM_compK_succ, PMF.map_comp, muM_succ, Model.pairMix_kernel, PMF.map_comp,
    (cP).childMix_forced' Rv v0 μ hj]
  obtain ⟨hl, hr⟩ := (cP).rootPair_mem_live_of_mem hj
  have hrp : rootPair σ τ = rootPair σ (rem j) := by
    rcases hτ with rfl | rfl
    · rfl
    · exact rootPair_markRoot_rem σ j
  rw [hrp] at hl hr ⊢
  show (cXi (C.exc σ) μ (C.ν σ) v0 (CtrC.ord j) h).map
      (branch v ∘ Prod.map (statesOf h) (statesOf h))
    = PMF.map (branch v ∘ Prod.map (statesOf' h) (statesOf' h)) _
  rw [← PMF.map_comp, ← PMF.map_comp, hX j hjN hl hr]

/-- The forced identity for marked counters at height `h + 1` from the pair identity at
height `h`. -/
lemma cMarkClaim_succ (h : ℕ) (hX : CPairMark C μ v0 Rv σ h) :
    CMarkClaim C μ v0 Rv σ (h + 1) := by
  intro a b i haN hbN hj v
  rw [muM_compK_succ, PMF.map_comp, muM_succ, Model.pairMix_kernel, PMF.map_comp,
    (cP).childMix_forced' Rv v0 μ hj]
  obtain ⟨hl, hr⟩ := (cP).rootPair_mem_live_of_mem hj
  show (cXi (C.exc σ) μ (C.ν σ) v0 (CtrC.mark a b i) h).map
      (branch v ∘ Prod.map (statesOf h) (statesOf h))
    = PMF.map (branch v ∘ Prod.map (statesOf' h) (statesOf' h)) _
  rw [← PMF.map_comp, ← PMF.map_comp, hX a b i haN hbN hl hr]

/-- The fresh identity at height `h + 1` from the pair identities at height `h`
(`sec:composite-process`: the fresh mixture runs over the ordinary and the exceptional
counters of the side). -/
lemma cFreshClaim_succ (h : ℕ) (hO : CPairOrd C μ v0 Rv σ h) (hMk : CPairMark C μ v0 Rv σ h) :
    CFreshClaim C μ v0 Rv σ (h + 1) := by
  intro v
  simp only [muM_compK_succ, PMF.map_comp]
  rw [muM_succ, Model.pairMix_kernel, PMF.map_comp, (cP).childMix_fresh, PMF.map_bind]
  show (C.ν σ).bind _ = ((C.ν σ).map fun k => max k 2).bind _
  rw [PMF.bind_map]
  refine bind_congr_of_ne_zero (C.ν σ) fun k hk => ?_
  simp only [Function.comp_apply]
  have hkK : k ∈ C.K σ := (C.mem_K σ k).mp hk
  have hkK' : max k 2 ∈ (cP).supp σ := Finset.mem_image_of_mem _ hkK
  obtain ⟨hl, hr⟩ := (cP).rootPair_mem_live hkK' (MTree.mem_subtrees_self _)
  have h2N := C.two_le_N
  rcases hexc : C.exc σ k with _ | p
  · have hnone : C.exc σ (max k 2) = none := by
      by_cases hk2 : k ≤ 2
      · rw [max_eq_right hk2]
        exact C.exc_none σ 2 h2N
      · rwa [max_eq_left (by omega)]
    have hkN : k ≤ C.N :=
      (le_max_left k 2).trans (C.S_le_N _ (C.core_of_none σ k hkK hexc))
    have hC : rootPair σ ((cP).C σ (max k 2)) = rootPair σ (rem k) := by
      show rootPair σ (compProfile (C.exc σ) (max k 2)) = _
      rw [compProfile_of_none hnone, rootPair_markRoot_rem, rem_max]
    rw [hC] at hl hr ⊢
    show (cXi (C.exc σ) μ (C.ν σ) v0 (CtrC.ord k) h).map
        (branch v ∘ Prod.map (statesOf h) (statesOf h))
      = PMF.map (branch v ∘ Prod.map (statesOf' h) (statesOf' h)) _
    rw [← PMF.map_comp, ← PMF.map_comp, hO k hkN hl hr]
  · have hkN : C.N < k := C.lt_of_exc_some hexc
    have hmax : max k 2 = k := max_eq_left (by omega)
    have hC : rootPair σ ((cP).C σ (max k 2))
        = rootPair σ (graftPort (MTree.markRoot (rem p.2)) (val p.1 0)) := by
      show rootPair σ (compProfile (C.exc σ) (max k 2)) = _
      rw [hmax, compProfile_of_some hexc, val_zero]
      obtain ⟨l, r, hlr⟩ := graftPort_node (MTree.markRoot (rem p.2)) p.1
      rw [hlr]
      rfl
    obtain ⟨haN, hbN⟩ := C.pair_le_N hexc
    rw [hC] at hl hr ⊢
    rw [cXi_ord_exc _ _ _ _ hexc]
    show (cXi (C.exc σ) μ (C.ν σ) v0 (CtrC.mark p.1 p.2 0) h).map
        (branch v ∘ Prod.map (statesOf h) (statesOf h))
      = PMF.map (branch v ∘ Prod.map (statesOf' h) (statesOf' h)) _
    rw [← PMF.map_comp, ← PMF.map_comp, hMk p.1 p.2 0 haN hbN hl hr]

/-- The three identities at every height. -/
theorem cClaims : ∀ h, CForcedClaim C μ v0 Rv σ h ∧ CMarkClaim C μ v0 Rv σ h
    ∧ CFreshClaim C μ v0 Rv σ h
  | 0 => ⟨cForcedClaim_zero C μ v0 Rv σ, cMarkClaim_zero C μ v0 Rv σ,
      cFreshClaim_zero C μ v0 Rv σ⟩
  | h + 1 =>
    have ih := cClaims h
    have hO := cPairOrd_of C μ v0 Rv σ h ih.1 ih.2.2
    have hM := cPairMark_of C μ v0 Rv σ h ih.1 ih.2.1 ih.2.2
    ⟨cForcedClaim_succ C μ v0 Rv σ h hO, cMarkClaim_succ C μ v0 Rv σ h hM,
      cFreshClaim_succ C μ v0 Rv σ h hO hM⟩

/-- **The law identification for the composite process** (`sec:composite-process`: "the
new proof covers the original composite Markov kernels exactly"): the state labelling of the
fresh law of the composite kernel of side `σ` has the law of the state labelling of the fresh
type of side `σ` of the composite presentation, at every height. -/
theorem cT_states_eq (h : ℕ) :
    (cT (C.exc σ) μ (C.ν σ) v0 h).map (statesOf h)
      = ((C.toPresentation.toModel Rv v0 μ).rho (C.toPresentation.freshL σ) h).map
          (statesOf' h) :=
  cT_map_eq_of_fresh C μ v0 Rv σ h (cClaims C μ v0 Rv σ h).2.2

end CompositeIdentification

section CompositeFailure

variable (C : CompositeData) (μ : PMF V) (v0 : V) (Rv : V → V → Prop)

/-- **The two-law failure probabilities agree** (`sec:composite-process`): the failure
probability of the left composite process against the right one at height `h` is the failure
probability of the two fresh types of the composite presentation. -/
theorem cFailProb_eq (h : ℕ) :
    ∑' x, Composite.cT (C.exc false) μ (C.ν false) v0 h x
        * qE (Composite.cT (C.exc true) μ (C.ν true) v0 h) (fullSim (Composite.cRel Rv) h) x
      = (C.toPresentation.toModel Rv v0 μ).failProb (C.toPresentation.freshL false)
          (C.toPresentation.freshL true) h := by
  rw [Model.failProb, failureD_map_eq _ _ _ (statesOf' h) (statesOf' h) (fullSim Rv h)
    (fullSim_srel_iff _ h), ← cT_states_eq C μ v0 Rv false h, ← cT_states_eq C μ v0 Rv true h]
  exact failureD_map_eq _ _ _ (statesOf h) (statesOf h) (fullSim Rv h) (fullSim_cRel_iff Rv h)

end CompositeFailure

/-! ### The two-law statement recovered (`sec:composite-process`) -/

/-- The return bound `H` of the composite presentation, a function of the exceptional data,
the supports and the core alone. -/
noncomputable def HretComp (exc : Bool → ℕ → Option (ℕ × ℕ)) (K : Bool → Finset ℕ)
    (S : Finset ℕ) : ℕ :=
  HretOf S rem (fun σ => suppBar (K σ)) fun σ k => compProfile (exc σ) k

/-- The type count `T` of the composite presentation. -/
noncomputable def TcountComp (exc : Bool → ℕ → Option (ℕ × ℕ)) (K : Bool → Finset ℕ) : ℕ :=
  TcountOf (fun σ => suppBar (K σ)) fun σ k => compProfile (exc σ) k

namespace CompositeData

variable (C : CompositeData)

/-- The return bound of the composite presentation is `HretComp`. -/
lemma Hret_eq : C.toPresentation.Hret = HretComp C.exc C.K C.S := rfl

/-- The type count of the composite presentation is `TcountComp`. -/
lemma Tcount_eq : C.toPresentation.Tcount = TcountComp C.exc C.K := rfl

/-- The core bound of the merged law is at most that of the original law
(`sec:composite-process`: `B = max_σ ∑_{k ∈ S} ν_σ(k)^{-α}`). -/
lemma inverseSum_nuBar_le {α : ℝ} (hα : 0 ≤ α) (σ : Bool) :
    ∑ a ∈ C.S, (nuBar (C.ν σ) a) ^ (-α) ≤ ∑ a ∈ C.S, (C.ν σ a) ^ (-α) := by
  refine Finset.sum_le_sum fun a ha => ?_
  refine rpow_neg_antitone hα ?_
  have := le_nuBar (C.ν σ) a
  rwa [max_eq_left (C.two_le_S a ha)] at this

end CompositeData

/-- `1 ≤ T` for the composite presentation. -/
lemma one_le_TcountComp (exc : Bool → ℕ → Option (ℕ × ℕ)) (K : Bool → Finset ℕ) :
    1 ≤ TcountComp exc K := one_le_TcountOf _ _

/-- **The two-law statement recovered, with explicit constants** (`sec:composite-process`):
for composite data with bound `B ≥ max_σ ∑_{k ∈ S} ν_σ(k)^{-α}`, with `H = HretComp`,
`T = TcountComp` and any `K > K₀(H, B)`, every state space with a reflexive symmetric
compatibility, a distinguished state of mass at least `1/2` and `η_α(μ) ≤ ε_K / 2` has the
two composite processes failing to match at height `h` with probability at most
`2 K_match η_α(μ)`. -/
theorem composite_two_law_matching_explicit (p : Params) (C : CompositeData) (B : ℝ)
    (hB : 1 ≤ B) (hbud : ∀ σ, ∑ a ∈ C.S, (C.ν σ a) ^ (-p.α) ≤ ENNReal.ofReal B) (Kc : ℝ)
    (hK : finiteK0 p (HretComp C.exc C.K C.S) B < Kc) {V : Type} (Rv : V → V → Prop) (v0 : V)
    (μ : PMF V) (hrefl : ∀ v, Rv v v) (hsymm : ∀ v w, Rv v w → Rv w v)
    (hμ : ENNReal.ofReal (1 / 2) ≤ μ v0)
    (hη : PhiD p.α μ μ Rv ≤ ENNReal.ofReal
      (1 / 2 * finiteEps p (HretComp C.exc C.K C.S) (TcountComp C.exc C.K) B Kc)) (h : ℕ) :
    ∑' x, Composite.cT (C.exc false) μ (C.ν false) v0 h x
        * qE (Composite.cT (C.exc true) μ (C.ν true) v0 h) (fullSim (Composite.cRel Rv) h) x
      ≤ ENNReal.ofReal (finiteKmatch (HretComp C.exc C.K C.S) Kc / (1 / 2))
          * PhiD p.α μ μ Rv := by
  rw [cFailProb_eq C μ v0 Rv h]
  set P := C.toPresentation with hP
  set M := P.toModel Rv v0 μ with hM
  have hcompat : M.IsCompat := ⟨hrefl, hsymm⟩
  have hp : ENNReal.ofReal (1 / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hp1 : ENNReal.ofReal (1 / 2) ≤ 1 := ENNReal.ofReal_le_one.mpr (by norm_num)
  have hζη : M.zeta p.α ≤ M.eta p.α / ENNReal.ofReal (1 / 2) :=
    M.zeta_le_eta_div hcompat p.α_nonneg hp hp1 hμ
  have hζtop : M.zeta p.α ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hζη
    exact ENNReal.div_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hη) hp
  have hb0 : rE μ Rv v0 ≠ 0 := M.rE_zero_ne_zero_of_zeta_ne_top hζtop
  have hBs : ∀ t, (P.selection Rv v0 μ hcompat hb0).inverseSum p.α t ≤ ENNReal.ofReal B := by
    intro t
    refine (P.inverseSum_le Rv v0 μ hcompat hb0 p.α_nonneg t).trans ?_
    have key : ∀ σ, ∑ a ∈ C.S, (nuBar (C.ν σ) a) ^ (-p.α) ≤ ENNReal.ofReal B :=
      fun σ => (C.inverseSum_nuBar_le p.α_nonneg σ).trans (hbud σ)
    exact max_le (key false) (key true)
  exact markov_matching_finite_eta p (HretComp C.exc C.K C.S) (TcountComp C.exc C.K)
    (one_le_TcountComp _ _) B hB Kc hK M hcompat (P.phase Rv v0 μ) (P.count_le_card Rv v0 μ)
    (P.selection Rv v0 μ hcompat hb0) hBs (P.freshPositive Rv v0 μ hcompat hb0)
    (P.commonReturns_Hret Rv v0 μ) (by norm_num) (by norm_num) hμ hη (P.freshL false)
    (P.freshL true) (P.phase_freshL_eq Rv v0 μ false true) h

/-- **The two-law statement recovered** (`sec:composite-process`
of the manuscript): for an exponent parameter set, exceptional data, supports, a common
core and a bound `B`, there are constants `K, ε` such that, for every pair of counter laws
forming composite data with these parameters and `max_σ ∑_{k ∈ S} ν_σ(k)^{-α} ≤ B`, every
state space with a reflexive symmetric compatibility, a distinguished state of mass at least
`1/2` and `η_α(μ) ≤ ε` has the two composite processes failing to match at every height with
probability at most `K η_α(μ)`. -/
theorem composite_two_law_matching (p : Params) (exc : Bool → ℕ → Option (ℕ × ℕ))
    (K : Bool → Finset ℕ) (S : Finset ℕ) (B : ℝ) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ C : CompositeData, C.exc = exc → C.K = K → C.S = S →
      (∀ σ, ∑ a ∈ S, (C.ν σ a) ^ (-p.α) ≤ ENNReal.ofReal B) →
      ∀ {V : Type} (Rv : V → V → Prop) (v0 : V) (μ : PMF V),
        (∀ v, Rv v v) → (∀ v w, Rv v w → Rv w v) → ENNReal.ofReal (1 / 2) ≤ μ v0 →
        PhiD p.α μ μ Rv ≤ ENNReal.ofReal ε →
        ∀ h, ∑' x, Composite.cT (exc false) μ (C.ν false) v0 h x
            * qE (Composite.cT (exc true) μ (C.ν true) v0 h) (fullSim (Composite.cRel Rv) h) x
          ≤ ENNReal.ofReal Kc * PhiD p.α μ μ Rv := by
  set K0 := finiteK0 p (HretComp exc K S) (max B 1) with hK0
  have hK : K0 < K0 + 1 := by linarith
  have hεpos := finiteEps_pos p (HretComp exc K S) (TcountComp exc K) (one_le_TcountComp _ _)
    (max B 1) (le_max_right _ _) (K0 + 1) hK
  refine ⟨finiteKmatch (HretComp exc K S) (K0 + 1) / (1 / 2),
    1 / 2 * finiteEps p (HretComp exc K S) (TcountComp exc K) (max B 1) (K0 + 1),
    by positivity, ?_⟩
  intro C hexc hKC hS hbud V Rv v0 μ hrefl hsymm hμ hη h
  subst hexc hKC hS
  have hbud' : ∀ σ, ∑ a ∈ C.S, (C.ν σ a) ^ (-p.α) ≤ ENNReal.ofReal (max B 1) :=
    fun σ => (hbud σ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact composite_two_law_matching_explicit p C (max B 1) (le_max_right _ _) hbud' (K0 + 1) hK
    Rv v0 μ hrefl hsymm hμ hη h

/-- **The two-law statement recovered at exponent `2`** (`sec:composite-process`: "The
exponent `2` already suffices"): the constants of `paramsTwo` and the `η_2` hypothesis. -/
theorem composite_two_law_matching_two (exc : Bool → ℕ → Option (ℕ × ℕ))
    (K : Bool → Finset ℕ) (S : Finset ℕ) (B : ℝ) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ C : CompositeData, C.exc = exc → C.K = K → C.S = S →
      (∀ σ, ∑ a ∈ S, (C.ν σ a) ^ (-(2 : ℝ)) ≤ ENNReal.ofReal B) →
      ∀ {V : Type} (Rv : V → V → Prop) (v0 : V) (μ : PMF V),
        (∀ v, Rv v v) → (∀ v w, Rv v w → Rv w v) → ENNReal.ofReal (1 / 2) ≤ μ v0 →
        PhiD 2 μ μ Rv ≤ ENNReal.ofReal ε →
        ∀ h, ∑' x, Composite.cT (exc false) μ (C.ν false) v0 h x
            * qE (Composite.cT (exc true) μ (C.ν true) v0 h) (fullSim (Composite.cRel Rv) h) x
          ≤ ENNReal.ofReal Kc * PhiD 2 μ μ Rv :=
  composite_two_law_matching paramsTwo exc K S B

end GraphMarkovMatching.Stopped
