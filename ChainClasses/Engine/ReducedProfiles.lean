import ChainClasses.General.GeneralShapeTail
import GraphMarkovMatching.Stopped.Application

/-!
The original reduced arity laws and their common binary profiles. The arity laws,
supports, profiles and positive core floors depend only on the offspring laws, not
on the geometric scale used to quantise the labels.
-/

namespace ChainClasses

open scoped ENNReal Classical
open BranchingProcess (Offspring)
open GraphMarkovMatching.Stopped

variable {J J' : ℕ}

lemma reducedWeight_nonneg (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (κ : ℕ) : 0 ≤ reducedWeight θ' κ := by
  rw [reducedWeight_def]
  exact div_nonneg (θ'.skeletonWeight_nonneg hq' κ) (by linarith)

/-- The reduced weights sum to one over the arities at least `2`. -/
lemma sum_reducedWeight (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') :
    ∑ κ ∈ Finset.range (J' + 1), (if 2 ≤ κ then reducedWeight θ' κ else 0) = 1 := by
  have hsum := θ'.sum_skeletonWeight hq'
  have hJ : J' + 1 = (J' - 1) + 1 + 1 := by omega
  rw [hJ, Finset.sum_range_succ', Finset.sum_range_succ'] at hsum ⊢
  rw [θ'.skeletonWeight_zero] at hsum
  have e1 : ∀ i ∈ Finset.range (J' - 1),
      (if 2 ≤ i + 1 + 1 then reducedWeight θ' (i + 1 + 1) else 0)
        = θ'.skeletonWeight (i + 1 + 1) / (1 - θ'.skeletonWeight 1) := fun i _ => by
    rw [ite_eq_left (by omega), reducedWeight_def]
  have h1 : 0 < 1 - θ'.skeletonWeight 1 := by linarith
  rw [Finset.sum_congr rfl e1, ite_eq_right (by norm_num), ite_eq_right (by norm_num), add_zero, add_zero,
    ← Finset.sum_div, div_eq_one_iff_eq h1.ne']
  linarith

/-- **The reduced law `ν̃` as a probability law on `ℕ`**: the weight `ν̃_κ` at every arity
`κ ≥ 2`, which vanishes above `J'`. -/
noncomputable def reducedPMF (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') : PMF ℕ :=
  PMF.ofFinset (fun κ => if 2 ≤ κ then ENNReal.ofReal (reducedWeight θ' κ) else 0)
    (Finset.range (J' + 1))
    (by
      have h := sum_reducedWeight θ' hq' hs1' hJ2'
      have e : ∀ κ, (if 2 ≤ κ then ENNReal.ofReal (reducedWeight θ' κ) else 0)
          = ENNReal.ofReal (if 2 ≤ κ then reducedWeight θ' κ else 0) := fun κ => by
        split_ifs <;> simp
      simp_rw [e]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun κ _ => ?_), h, ENNReal.ofReal_one]
      split_ifs
      · exact reducedWeight_nonneg θ' hq' hs1' κ
      · exact le_rfl)
    (by
      intro κ hκ
      rw [Finset.mem_range, not_lt] at hκ
      split_ifs with h2
      · rw [reducedWeight_eq_zero_of_gt θ' (by omega), ENNReal.ofReal_zero]
      · rfl)

lemma reducedPMF_apply (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') (κ : ℕ) :
    reducedPMF θ' hq' hs1' hJ2' κ = if 2 ≤ κ then ENNReal.ofReal (reducedWeight θ' κ) else 0 :=
  PMF.ofFinset_apply _ _ κ

lemma reducedPMF_of_le (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') {κ : ℕ} (hκ : 2 ≤ κ) :
    reducedPMF θ' hq' hs1' hJ2' κ = ENNReal.ofReal (reducedWeight θ' κ) := by
  rw [reducedPMF_apply, ite_eq_left hκ]

lemma reducedPMF_eq_zero (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') {κ : ℕ} (hκ : ¬ (2 ≤ κ ∧ κ ≤ J')) :
    reducedPMF θ' hq' hs1' hJ2' κ = 0 := by
  rw [reducedPMF_apply]
  split_ifs with h2
  · rw [reducedWeight_eq_zero_of_gt θ' (by omega), ENNReal.ofReal_zero]
  · rfl

/-- **The support of the reduced law** is `{2, …, J'}` (`thm:full-support`). -/
lemma reducedPMF_ne_zero_iff (θ' : Offspring J') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') (κ : ℕ) :
    reducedPMF θ' hq' hs1' hJ2' κ ≠ 0 ↔ 2 ≤ κ ∧ κ ≤ J' := by
  constructor
  · intro h
    by_contra hκ
    exact h (reducedPMF_eq_zero θ' hq' hs1' hJ2' hκ)
  · intro hκ
    rw [reducedPMF_of_le θ' hq' hs1' hJ2' hκ.1]
    exact (ENNReal.ofReal_pos.mpr (reducedWeight_pos θ' hq' hq0' hJ2' hθJ' hκ.1 hκ.2)).ne'


/-- **The chain regime of `thm:harris-general`**: with no extinction the transform is
the identity, so every skeleton weight is the offspring mass itself. -/
lemma skeletonWeight_of_extinction_zero (θ : Offspring J) (h0 : θ.extinction = 0)
    (hθ0 : θ 0 = 0) (k : ℕ) : θ.skeletonWeight k = θ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [θ.skeletonWeight_zero, hθ0]
  · rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ (by omega),
      BranchingProcess.Offspring.surviveWeight, h0]
    have hterm : ∀ j ∈ Finset.range (J + 1),
        θ j * (j.choose k : ℝ) * (1 - 0) ^ k * (0 : ℝ) ^ (j - k)
          = if j = k then θ k else 0 := by
      intro j _
      rcases lt_trichotomy j k with hjk | rfl | hjk
      · rw [Nat.choose_eq_zero_of_lt hjk, ite_eq_right (by omega)]
        simp
      · simp
      · rw [ite_eq_right (by omega), zero_pow (by omega : j - k ≠ 0)]
        ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (J + 1)) k
      (fun _ ↦ θ k)]
    by_cases hkJ : k ∈ Finset.range (J + 1)
    · rw [ite_eq_left hkJ]
      simp
    · rw [ite_eq_right hkJ, θ.vanishing k (by
        rw [Finset.mem_range] at hkJ
        omega)]
      simp


/-- In the chain regime `θ₀ = 0` the extinction probability vanishes. -/
lemma extinction_eq_zero_of_chain (θ : Offspring J) (hθ0 : θ 0 = 0) : θ.extinction = 0 :=
  θ.extinction_eq_zero_iff.mpr hθ0

lemma extinction_lt_one_of_chain (θ : Offspring J) (hθ0 : θ 0 = 0) : θ.extinction < 1 := by
  rw [extinction_eq_zero_of_chain θ hθ0]
  exact zero_lt_one

/-- In the chain regime the transform of `thm:harris-general` is the identity:
`θ̃_k = θ_k`. -/
lemma skeletonWeight_eq_of_chain (θ : Offspring J) (hθ0 : θ 0 = 0) (k : ℕ) :
    θ.skeletonWeight k = θ k :=
  skeletonWeight_of_extinction_zero θ (extinction_eq_zero_of_chain θ hθ0) hθ0 k

/-- `θ̃₁ = θ₁` in the chain regime. -/
lemma skeletonWeight_one_eq_of_chain (θ : Offspring J) (hθ0 : θ 0 = 0) :
    θ.skeletonWeight 1 = θ 1 :=
  skeletonWeight_eq_of_chain θ hθ0 1


/-- In the chain regime `θ̃₁ = θ₁ < 1`. -/
lemma chain_hs1 (θ : Offspring J) (hθ0 : θ 0 = 0) (hθ1 : θ 1 < 1) :
    θ.skeletonWeight 1 < 1 := by
  rw [skeletonWeight_one_eq_of_chain θ hθ0]
  exact hθ1


/-- The shifted support `A = supp ν̃ - 1` of a chain-regime law: the shifts `k - 1` of the
charged arities `k ≥ 2`, the generators of the branching semigroup
`def:branching-semigroup`. -/
noncomputable def shiftSupp (θ : Offspring J) : Finset ℕ :=
  ((Finset.range (J + 1)).filter fun k => 2 ≤ k ∧ θ k ≠ 0).image fun k => k - 1

lemma mem_shiftSupp (θ : Offspring J) {x : ℕ} : x ∈ shiftSupp θ ↔ 1 ≤ x ∧ θ (1 + x) ≠ 0 := by
  simp only [shiftSupp, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨hk, hk2, hθk⟩, rfl⟩
    refine ⟨by omega, ?_⟩
    rwa [show 1 + (k - 1) = k by omega]
  · rintro ⟨hx, hθ⟩
    refine ⟨1 + x, ⟨?_, by omega, hθ⟩, by omega⟩
    by_contra h
    exact hθ (θ.vanishing _ (by omega))

lemma shiftSupp_one_le (θ : Offspring J) : ∀ x ∈ shiftSupp θ, 1 ≤ x :=
  fun _ hx => ((mem_shiftSupp θ).mp hx).1

lemma shiftSupp_pos (θ : Offspring J) : ∀ x ∈ shiftSupp θ, 0 < x :=
  fun _ hx => ((mem_shiftSupp θ).mp hx).1

lemma shiftSupp_le (θ : Offspring J) : ∀ x ∈ shiftSupp θ, x ≤ J - 1 := by
  intro x hx
  obtain ⟨-, hθ⟩ := (mem_shiftSupp θ).mp hx
  by_contra h
  exact hθ (θ.vanishing _ (by omega))

lemma mem_shiftSupp_of (θ : Offspring J) (hθ0 : θ 0 = 0) :
    ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ shiftSupp θ := by
  intro x hx h
  rw [skeletonWeight_eq_of_chain θ hθ0] at h
  exact (mem_shiftSupp θ).mpr ⟨hx, h⟩

lemma max_mem_shiftSupp (θ : Offspring J) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) :
    J - 1 ∈ shiftSupp θ :=
  (mem_shiftSupp θ).mpr ⟨by omega, by rw [show 1 + (J - 1) = J by omega]; exact hθJ.ne'⟩

lemma shiftSupp_nonempty (θ : Offspring J) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) :
    (shiftSupp θ).Nonempty :=
  ⟨J - 1, max_mem_shiftSupp θ hJ2 hθJ⟩


/-! ### The original chain support and its atomic presentation -/

/-- The supported original arities after unary vertices are removed. -/
noncomputable def reducedSupport (θ : Offspring J) : Finset ℕ :=
  (Finset.range (J + 1)).filter fun k => 2 ≤ k ∧ θ k ≠ 0

lemma mem_reducedSupport (θ : Offspring J) (k : ℕ) :
    k ∈ reducedSupport θ ↔ 2 ≤ k ∧ θ k ≠ 0 := by
  simp only [reducedSupport, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by by_contra hk; exact h.2 (θ.vanishing k (by omega)), h⟩

lemma reducedSupport_nonempty (θ : Offspring J) (hJ : 2 ≤ J) (hθJ : 0 < θ J) :
    (reducedSupport θ).Nonempty :=
  ⟨J, (mem_reducedSupport θ J).mpr ⟨hJ, hθJ.ne'⟩⟩

lemma chain_reducedPMF_ne_zero_iff (θ : Offspring J) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (hJ : 2 ≤ J) (k : ℕ) :
    reducedPMF θ (extinction_lt_one_of_chain θ hθ0) (chain_hs1 θ hθ0 hθ1) hJ k ≠ 0
      ↔ k ∈ reducedSupport θ := by
  rw [reducedPMF_apply, mem_reducedSupport]
  by_cases hk : 2 ≤ k
  · rw [ite_eq_left hk, reducedWeight_def, skeletonWeight_eq_of_chain θ hθ0,
      skeletonWeight_eq_of_chain θ hθ0]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, hk, true_and]
    constructor
    · intro h hzero
      simp [hzero] at h
    · intro h
      exact div_pos (lt_of_le_of_ne (θ.nonneg k) (Ne.symm h)) (sub_pos.mpr hθ1)
  · simp [hk]

lemma shiftSemigroup_reducedSupport (θ : Offspring J) :
    shiftSemigroup (reducedSupport θ : Set ℕ) =
      AddSubmonoid.closure (shiftSupp θ : Set ℕ) := by
  simp only [shiftSemigroup, shiftSupp, reducedSupport, Finset.coe_image]

/-- Common atomic profiles for the original reduced laws of two chain offspring laws.
Every parameter here is independent of the geometric quantisation scale. -/
noncomputable def chainPresentation (θ : Offspring J) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (hJ : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hθ0' : θ' 0 = 0) (hθ1' : θ' 1 < 1) (hJ' : 2 ≤ J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ) =
      AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) : Presentation :=
  atomicPresentation
    (reducedPMF θ (extinction_lt_one_of_chain θ hθ0) (chain_hs1 θ hθ0 hθ1) hJ)
    (reducedPMF θ' (extinction_lt_one_of_chain θ' hθ0') (chain_hs1 θ' hθ0' hθ1') hJ')
    (reducedSupport θ) (reducedSupport θ')
    (chain_reducedPMF_ne_zero_iff θ hθ0 hθ1 hJ)
    (chain_reducedPMF_ne_zero_iff θ' hθ0' hθ1' hJ')
    (fun k hk => ((mem_reducedSupport θ k).mp hk).1)
    (fun k hk => ((mem_reducedSupport θ' k).mp hk).1)
    (reducedSupport_nonempty θ hJ hθJ)
    (by simpa only [shiftSemigroup_reducedSupport] using hsem)

/-! ### Balanced profiles from the binary core -/

namespace BinaryProfiles

/-- A balanced profile with every binary split marked as a core replacement. -/
def balanced (k : ℕ) : MTree :=
  if h4 : 4 ≤ k then .gnode (balanced (k / 2)) (balanced (k - k / 2))
  else if k = 3 then .gnode (.gnode .leaf .leaf) .leaf
  else .gnode .leaf .leaf
termination_by k
decreasing_by all_goals omega

lemma balanced_two : balanced 2 = .gnode .leaf .leaf := by
  rw [balanced, dite_eq_right (by omega), ite_eq_right (by omega)]

lemma balanced_gnode (k : ℕ) : ∃ l r, balanced k = .gnode l r := by
  rw [balanced]
  split_ifs <;> exact ⟨_, _, rfl⟩

lemma balanced_flatten (k : ℕ) : (balanced k).flatten = .leaf := by
  obtain ⟨l, r, h⟩ := balanced_gnode k
  rw [h, MTree.flatten]

lemma balanced_leaves (k : ℕ) : (balanced k).leaves = max k 2 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [balanced]
    split_ifs with h4 h3
    · simp only [MTree.leaves, ih (k / 2) (by omega), ih (k - k / 2) (by omega)]
      omega
    · subst h3
      rfl
    · simp only [MTree.leaves]
      omega

lemma balanced_allComp (k : ℕ) :
    MTree.AllComp {2} (fun _ => .node .leaf .leaf) (balanced k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [balanced]
    split_ifs with h4 h3
    · refine ⟨⟨2, by simp, ?_⟩, ih (k / 2) (by omega), ih (k - k / 2) (by omega)⟩
      rw [balanced_flatten, balanced_flatten]
    · simp [MTree.AllComp, MTree.flatten]
    · simp [MTree.AllComp, MTree.flatten]

/-- Both laws need only charge arity two. Every other balanced profile is built from
the same two-leaf profile, regardless of the relative bounds on the supports. -/
noncomputable def presentation (νL νR : PMF ℕ) (suppL suppR : Finset ℕ)
    (hL : ∀ k, νL k ≠ 0 ↔ k ∈ suppL) (hR : ∀ k, νR k ≠ 0 ↔ k ∈ suppR)
    (h2L : ∀ k ∈ suppL, 2 ≤ k) (h2R : ∀ k ∈ suppR, 2 ≤ k)
    (htwoL : 2 ∈ suppL) (htwoR : 2 ∈ suppR) : Presentation where
  S := {2}
  D := fun _ => .node .leaf .leaf
  ν := fun σ => if σ then νR else νL
  supp := fun σ => if σ then suppR else suppL
  C := fun _ k => balanced k
  mem_supp := by intro σ k; cases σ <;> simp [hL, hR]
  S_nonempty := Finset.singleton_nonempty 2
  two_le_S := by simp
  D_leaves := by intro a ha; simpa [MTree.leaves] using (Finset.mem_singleton.mp ha).symm
  D_noGraft := by intro a ha; exact ⟨trivial, trivial⟩
  D_node := by intro a ha; exact ⟨_, _, rfl⟩
  S_subset_supp := by
    intro σ a ha
    have ha2 := Finset.mem_singleton.mp ha
    subst a
    cases σ <;> simpa using (by assumption : 2 ∈ _)
  two_le_supp := by
    intro σ k hk
    cases σ
    · exact h2L k (by simpa using hk)
    · exact h2R k (by simpa using hk)
  C_leaves := by
    intro σ k hk
    rw [balanced_leaves, max_eq_left]
    cases σ
    · exact h2L k (by simpa using hk)
    · exact h2R k (by simpa using hk)
  C_gnode := fun _ k _ => balanced_gnode k
  C_allComp := fun _ k _ => balanced_allComp k
  C_core := by intro σ a ha; rw [Finset.mem_singleton.mp ha, balanced_two]; rfl

end BinaryProfiles

end ChainClasses
