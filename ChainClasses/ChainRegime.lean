/-
`sec:general-chain` of `matching_classes_general.tex`: the chain regime
`θ₀ = 0`, `θ₁ ∈ (0,1)` at general support.

With no extinction the transform of `thm:harris-general` is the identity, no
vertex carries a bush, and the shape at a vertex of the reduced skeleton is its
neck alone.  What has to be certified is therefore scalar: that the neck length
and the terminating arity are independent, and that the cluster presentation
used across two laws keeps that independence while moving the arity law.

* `chain_joint_factor`: `eq:chain-joint`, the factorisation
  `θ₁^{r-1} θ_j = [θ₁^{r-1}(1-θ₁)] ν̃_j` behind `thm:chain-independence`.
  `chain_reduced_sum` is the arity marginal and `geometric_law_tsum` (in
  `GeneralHarris`) the neck marginal.
* `shiftConv`, `shiftConv_tsum`: the shifted convolution
  `(ν ⊛ ν)(j) = ∑_{a+b=j+1} ν_a ν_b` of `thm:cluster-law`, and that it is a
  probability law when `ν` is one supported away from `0`.
* `clusterLaw`, `clusterLaw_tsum`, `clusterLaw_nonneg`: the presented arity law
  `eq:cluster-law`, `ν_t = (1-t)ν + t(ν ⊛ ν)`.
* `clusterLaw_range`: `t = β(1 - θ₁^L)` sweeps `[0, 1 - θ₁^L]` as `β` sweeps
  `[0,1]`, the tuning range of `thm:cluster-law`.
* `cluster_shift_add`, `cluster_arity_mem`: `thm:reachable-arity`, that the
  presented arity of a merged pair is `k₁ + k₂ - 1` and that its shift lies in
  the branching semigroup.
* `markedQI_of_collapse`: `thm:cluster-flat`, a surjection that never increases
  distances, loses at most `L`, and moves the marks by at most `L` is an
  `L`-marked quasi-isometry.
* `clusterLaw_two_point`: the guiding example `ex:chain-cross`, where the law
  supported on `{1,3}` presents `a δ₃ + b δ₅` at `t = b`.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import ChainClasses.MarkedQI
import ChainClasses.GeneralHarris
import ChainClasses.SemigroupMerge

namespace ChainClasses

/-! ### `thm:chain-independence`: the joint law factorises -/

/-- **`eq:chain-joint`**: with `θ₀ = 0` the probability of a neck of length `r`
terminated by a split of arity `j` is `θ₁^{r-1} θ_j`, which is the geometric
neck law times the reduced arity law.  The two marginals are therefore
independent, which is what makes `Q = μ ⊗ ν̃` a product with no repair. -/
theorem chain_joint_factor {θ₁ : ℝ} (θ : ℕ → ℝ) (h1 : θ₁ < 1) (r j : ℕ) :
    θ₁ ^ (r - 1) * θ j
      = (θ₁ ^ (r - 1) * (1 - θ₁)) * (θ j / (1 - θ₁)) := by
  have hne : (1 : ℝ) - θ₁ ≠ 0 := by linarith
  field_simp

/-- The arity marginal is a probability law: with `θ₀ = 0` the reduced law
`ν̃_j = θ_j/(1-θ₁)` sums to one over `j ≥ 2`. -/
theorem chain_reduced_sum {θ₁ : ℝ} (N : ℕ) (θ : ℕ → ℝ) (hN : 2 ≤ N)
    (hsum : ∑ j ∈ Finset.range (N + 1), θ j = 1) (h0 : θ 0 = 0) (h1 : θ 1 = θ₁)
    (hlt : θ₁ < 1) :
    ∑ j ∈ Finset.Icc 2 N, θ j / (1 - θ₁) = 1 := by
  have hne : (1 : ℝ) - θ₁ ≠ 0 := by linarith
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico]
  have hsplit := Finset.sum_Ico_consecutive θ (by omega : 0 ≤ 2) (by omega : 2 ≤ N + 1)
  have hfull : ∑ j ∈ Finset.Ico 0 (N + 1), θ j = 1 := by
    rwa [← Finset.range_eq_Ico]
  have h01 : ∑ j ∈ Finset.Ico 0 2, θ j = θ₁ := by
    rw [← Finset.range_eq_Ico, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, zero_add]
  have htail : ∑ j ∈ Finset.Ico 2 (N + 1), θ j = 1 - θ₁ := by
    rw [hfull, h01] at hsplit; linarith
  rw [hIcc, ← Finset.sum_div, htail, div_self hne]

/-! ### `thm:cluster-law`: the presented arity law -/

/-- The **shifted convolution** of `eq:cluster-law`: the law of `k₁ + k₂ - 1`
for independent `k₁, k₂`, which is the presented arity of a merged pair. -/
noncomputable def shiftConv (ν : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal (j + 1), ν p.1 * ν p.2

lemma shiftConv_nonneg {ν : ℕ → ℝ} (hnn : ∀ j, 0 ≤ ν j) (j : ℕ) : 0 ≤ shiftConv ν j :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hnn _) (hnn _)

lemma shiftConv_summable {ν : ℕ → ℝ} (hnn : ∀ j, 0 ≤ ν j) (hsum : Summable ν) :
    Summable (shiftConv ν) := by
  have hnorm : Summable fun j => ‖ν j‖ := by
    simpa [Real.norm_of_nonneg (hnn _)] using hsum
  have hC : Summable (fun n => ∑ p ∈ Finset.antidiagonal n, ν p.1 * ν p.2) :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hnorm hnorm).of_norm
  exact (summable_nat_add_iff
    (f := fun n => ∑ p ∈ Finset.antidiagonal n, ν p.1 * ν p.2) 1).mpr hC

/-- **The shifted convolution of a law is a law.** The `n = 0` term of the
Cauchy product is `ν₀²`, which vanishes because a split has arity at least
two, so the shift by one loses nothing. -/
theorem shiftConv_tsum {ν : ℕ → ℝ} (hnn : ∀ j, 0 ≤ ν j) (hsum : Summable ν)
    (hone : ∑' j, ν j = 1) (h0 : ν 0 = 0) :
    ∑' j, shiftConv ν j = 1 := by
  have hnorm : Summable fun j => ‖ν j‖ := by
    simpa [Real.norm_of_nonneg (hnn _)] using hsum
  set C : ℕ → ℝ := fun n => ∑ p ∈ Finset.antidiagonal n, ν p.1 * ν p.2 with hC
  have hCsum : Summable C := by
    have := summable_norm_sum_mul_antidiagonal_of_summable_norm hnorm hnorm
    exact this.of_norm
  have hCtot : ∑' n, C n = 1 := by
    have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm
    rw [hone, mul_one] at h
    exact h.symm
  have hC0 : C 0 = 0 := by
    simp [hC, h0]
  have hshift := hCsum.sum_add_tsum_nat_add 1
  rw [hCtot, Finset.sum_range_one, hC0, zero_add] at hshift
  have hcongr : ∀ j : ℕ, C (j + 1) = shiftConv ν j := fun _ => rfl
  calc ∑' j, shiftConv ν j = ∑' j, C (j + 1) := tsum_congr fun j => (hcongr j).symm
    _ = 1 := hshift

/-- **`eq:cluster-law`**: the presented arity law `ν_t = (1-t)ν + t(ν ⊛ ν)`. -/
noncomputable def clusterLaw (t : ℝ) (ν : ℕ → ℝ) (j : ℕ) : ℝ :=
  (1 - t) * ν j + t * shiftConv ν j

lemma clusterLaw_nonneg {t : ℝ} {ν : ℕ → ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hnn : ∀ j, 0 ≤ ν j) (j : ℕ) : 0 ≤ clusterLaw t ν j :=
  add_nonneg (mul_nonneg (by linarith) (hnn j))
    (mul_nonneg ht0 (shiftConv_nonneg hnn j))

/-- The presented arity law is a probability law for every mixing weight. -/
theorem clusterLaw_tsum {t : ℝ} {ν : ℕ → ℝ} (hnn : ∀ j, 0 ≤ ν j) (hsum : Summable ν)
    (hone : ∑' j, ν j = 1) (h0 : ν 0 = 0) :
    ∑' j, clusterLaw t ν j = 1 := by
  have hSC : Summable (shiftConv ν) := shiftConv_summable hnn hsum
  have hSCone : ∑' j, shiftConv ν j = 1 := shiftConv_tsum hnn hsum hone h0
  have hA : HasSum (fun j => (1 - t) * ν j) (1 - t) := by
    have h := hsum.hasSum.mul_left (1 - t)
    rwa [hone, mul_one] at h
  have hB : HasSum (fun j => t * shiftConv ν j) t := by
    have h := hSC.hasSum.mul_left t
    rwa [hSCone, mul_one] at h
  have hAB := hA.add hB
  rw [show (1 - t) + t = 1 from by ring] at hAB
  exact hAB.tsum_eq

/-- **The tuning range of `thm:cluster-law`**: the absorption weight
`t = β(1 - θ₁^L)` sweeps `[0, 1 - θ₁^L]` as `β` sweeps `[0,1]`, so any target
below the threshold mass is reachable. -/
lemma clusterLaw_range {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (L : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 - a ^ L) :
    ∃ β ∈ Set.Icc (0 : ℝ) 1, β * (1 - a ^ L) = u := by
  have hpow : a ^ L ≤ 1 := pow_le_one₀ ha0 ha1.le
  rcases eq_or_lt_of_le hpow with heq | hlt
  · refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
    rw [heq] at hu1 ⊢
    simp only [sub_self, mul_zero]
    linarith
  · have hpos : 0 < 1 - a ^ L := by linarith
    refine ⟨u / (1 - a ^ L), ⟨div_nonneg hu0 hpos.le, ?_⟩, div_mul_cancel₀ u (ne_of_gt hpos)⟩
    rw [div_le_one hpos]
    exact hu1

/-! ### `thm:reachable-arity` -/

/-- **`thm:reachable-arity`**: a merged pair of splits of arities `k₁, k₂` has
presented arity `k₁ + k₂ - 1`, whose shift is the sum of the two shifts. -/
lemma cluster_shift_add {k₁ k₂ : ℕ} (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂) :
    (k₁ + k₂ - 1) - 1 = (k₁ - 1) + (k₂ - 1) := by omega

/-- The presented shift stays in the branching semigroup, so merging never
leaves it; this is `merge_step` read for the cluster presentation. -/
lemma cluster_arity_mem {Λ : AddSubmonoid ℕ} {k₁ k₂ : ℕ} (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (m₁ : k₁ - 1 ∈ Λ) (m₂ : k₂ - 1 ∈ Λ) : (k₁ + k₂ - 1) - 1 ∈ Λ := by
  rw [cluster_shift_add h₁ h₂]
  exact add_mem m₁ m₂

/-! ### `thm:cluster-flat`: flattening the presented cluster -/

/-- **`thm:cluster-flat`**: a surjection that never increases distances, loses
at most `L`, and moves each mark by at most `L` is an `L`-marked
quasi-isometry.  Collapsing the inner neck of a merged cluster onto the exit of
the outer one is such a map, with `L` the threshold of `def:cluster`. -/
theorem markedQI_of_collapse {L : ℝ} (hL : 1 ≤ L) {X Y : MarkedSpace}
    (f : X.carrier → Y.carrier)
    (hcontract : ∀ a b, dist (f a) (f b) ≤ dist a b)
    (hlose : ∀ a b, dist a b ≤ dist (f a) (f b) + L)
    (hsurj : Function.Surjective f)
    (hentry : dist (f X.entry) Y.entry ≤ L)
    (hexit : dist (f X.exit) Y.exit ≤ L) :
    MarkedQI L X Y := by
  have hL0 : (0 : ℝ) ≤ L := zero_le_one.trans hL
  refine ⟨f, fun a b => ?_, fun a b => ?_, fun y => ?_, hentry, hexit⟩
  · have h1 := hcontract a b
    have h2 : dist a b ≤ L * dist a b := by
      nlinarith [dist_nonneg (x := a) (y := b)]
    linarith
  · have h1 := hlose a b
    have h2 : dist (f a) (f b) ≤ L * dist (f a) (f b) := by
      nlinarith [dist_nonneg (x := f a) (y := f b)]
    nlinarith
  · obtain ⟨a, rfl⟩ := hsurj y
    exact ⟨a, by simpa using hL0⟩

/-! ### `thm:blob-law`: convolution powers and their mixtures -/

/-- The `m`-fold convolution power of a shift law, shifted so that `convPow m`
is the arity law of a blob that absorbs `m` times. -/
noncomputable def convPow (ν : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun j => if j = 0 then 1 else 0
  | m + 1 => fun j => ∑ p ∈ Finset.antidiagonal j, convPow ν m p.1 * ν p.2

lemma convPow_nonneg {ν : ℕ → ℝ} (hnn : ∀ j, 0 ≤ ν j) : ∀ m j, 0 ≤ convPow ν m j
  | 0, j => by
      show (0 : ℝ) ≤ if j = 0 then 1 else 0
      split <;> norm_num
  | m + 1, j => by
      rw [convPow]
      exact Finset.sum_nonneg fun p _ => mul_nonneg (convPow_nonneg hnn m p.1) (hnn p.2)

lemma convPow_summable {ν : ℕ → ℝ} (hnn : ∀ j, 0 ≤ ν j) (hsum : Summable ν) :
    ∀ m, Summable (convPow ν m)
  | 0 => by
      show Summable fun j : ℕ => if j = 0 then (1 : ℝ) else 0
      exact (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  | m + 1 => by
      have hprev := convPow_summable hnn hsum m
      have hnormP : Summable fun j => ‖convPow ν m j‖ := by
        simpa [Real.norm_of_nonneg (convPow_nonneg hnn m _)] using hprev
      have hnormN : Summable fun j => ‖ν j‖ := by
        simpa [Real.norm_of_nonneg (hnn _)] using hsum
      have := summable_norm_sum_mul_antidiagonal_of_summable_norm hnormP hnormN
      have h2 := this.of_norm
      exact h2

/-- **`thm:blob-law`**: each convolution power is a probability law, so a blob
that absorbs a fixed number of times presents a law. -/
theorem convPow_tsum {ν : ℕ → ℝ} (hnn : ∀ j, 0 ≤ ν j) (hsum : Summable ν)
    (hone : ∑' j, ν j = 1) : ∀ m, ∑' j, convPow ν m j = 1
  | 0 => by
      show ∑' j : ℕ, (if j = 0 then (1 : ℝ) else 0) = 1
      exact (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).tsum_eq
  | m + 1 => by
      have hprev := convPow_tsum hnn hsum hone m
      have hnormP : Summable fun j => ‖convPow ν m j‖ := by
        simpa [Real.norm_of_nonneg (convPow_nonneg hnn m _)] using
          convPow_summable hnn hsum m
      have hnormN : Summable fun j => ‖ν j‖ := by
        simpa [Real.norm_of_nonneg (hnn _)] using hsum
      have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnormP hnormN
      rw [hprev, hone, mul_one] at h
      rw [convPow]
      exact h.symm

/-- **`eq:reach-mix`**: a finite mixture of convolution powers is a law, which
is the arity law of a blob whose number of absorptions is drawn in advance. -/
theorem mixPow_tsum {ν : ℕ → ℝ} (hnn : ∀ j, 0 ≤ ν j) (hsum : Summable ν)
    (hone : ∑' j, ν j = 1) {n : ℕ} (a : ℕ → ℝ)
    (hasum : ∑ m ∈ Finset.range n, a m = 1) :
    ∑' j, (∑ m ∈ Finset.range n, a m * convPow ν (m + 1) j) = 1 := by
  have hswap : ∑' j, (∑ m ∈ Finset.range n, a m * convPow ν (m + 1) j)
      = ∑ m ∈ Finset.range n, ∑' j, a m * convPow ν (m + 1) j :=
    Summable.tsum_finsetSum fun m _ => (convPow_summable hnn hsum (m + 1)).mul_left (a m)
  rw [hswap]
  have hterm : ∀ m ∈ Finset.range n, ∑' j, a m * convPow ν (m + 1) j = a m := by
    intro m _
    rw [tsum_mul_left, convPow_tsum hnn hsum hone (m + 1), mul_one]
  rw [Finset.sum_congr rfl hterm, hasum]

/-! ### `thm:least-shift`: the least shift is common to both laws -/

/-- Every nonzero element of a submonoid of `ℕ` dominates some nonzero
generator. -/
lemma exists_generator_le {G : Set ℕ} :
    ∀ x ∈ AddSubmonoid.closure G, 0 < x → ∃ g ∈ G, 0 < g ∧ g ≤ x := by
  intro x hx
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy => exact fun hpos => ⟨y, hy, hpos, le_refl y⟩
  | zero => exact fun h => absurd h (lt_irrefl 0)
  | add u v _ _ ihu ihv =>
      intro hpos
      rcases Nat.eq_zero_or_pos u with rfl | hu
      · obtain ⟨g, hg, hg0, hgv⟩ := ihv (by omega)
        exact ⟨g, hg, hg0, by omega⟩
      · obtain ⟨g, hg, hg0, hgu⟩ := ihu hu
        exact ⟨g, hg, hg0, by omega⟩

/-- **`thm:least-shift`**: the least nonzero element of a numerical semigroup
lies in every generating set, since it is not a sum of two nonzero elements.
So two chain-regime laws with the same branching semigroup charge the same
least shift, and indeed the same minimal generators. -/
theorem min_mem_of_generates {G : Set ℕ} {s : ℕ} (hs : 0 < s)
    (hmem : s ∈ AddSubmonoid.closure G)
    (hmin : ∀ x ∈ AddSubmonoid.closure G, 0 < x → s ≤ x) : s ∈ G := by
  obtain ⟨g, hgG, hg0, hgs⟩ := exists_generator_le s hmem hs
  have hgmem : g ∈ AddSubmonoid.closure G := AddSubmonoid.subset_closure hgG
  have := hmin g hgmem hg0
  have : g = s := le_antisymm hgs this
  rwa [this] at hgG

/-! ### `rem:fixed-levels`: blocks of fixed depth cannot work -/

/-- **`rem:fixed-levels`**: a complete block of depth `d` on the `{1,3}` side
has arity `3^d`, and one of depth `e` on the `{1,3,5}` side charges `5^e`.
These never coincide, so no pair of depths equalises the two arity laws, even
though `3^d/5^e` comes arbitrarily close to `1`. -/
theorem three_pow_ne_five_pow {d e : ℕ} (hd : 1 ≤ d) : (3 : ℕ) ^ d ≠ 5 ^ e := by
  intro h
  have h3 : (3 : ℕ) ∣ 3 ^ d := dvd_pow_self 3 (by omega)
  rw [h] at h3
  have h5 : (3 : ℕ) ∣ 5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

/-! ### `ex:chain-cross`: the guiding example -/

/-- The point mass at `k`, the reduced law of a support with a single split
arity. -/
noncomputable def deltaAt (k : ℕ) : ℕ → ℝ := fun j => if j = k then 1 else 0

lemma shiftConv_delta (k : ℕ) (hk : 1 ≤ k) :
    shiftConv (deltaAt k) = deltaAt (2 * k - 1) := by
  funext j
  unfold shiftConv deltaAt
  have hterm : ∀ p : ℕ × ℕ,
      (if p.1 = k then (1 : ℝ) else 0) * (if p.2 = k then (1 : ℝ) else 0)
        = if p = (k, k) then (1 : ℝ) else 0 := by
    intro p
    by_cases h1 : p.1 = k <;> by_cases h2 : p.2 = k <;>
      simp [h1, h2, Prod.ext_iff]
  simp only [hterm]
  rw [Finset.sum_ite_eq' (Finset.antidiagonal (j + 1)) (k, k) (fun _ => (1 : ℝ))]
  simp only [Finset.mem_antidiagonal]
  by_cases hj : j = 2 * k - 1
  · rw [if_pos (by omega : k + k = j + 1), if_pos hj]
  · rw [if_neg (by omega : ¬ (k + k = j + 1)), if_neg hj]

/-- **`ex:chain-cross`**: the law supported on `{1,3}` has `ν̃ = δ₃`, so its
cluster presentation at weight `t` is `(1-t)δ₃ + t δ₅`.  Choosing `t = b`
reproduces the reduced law `a δ₃ + b δ₅` of a law supported on `{1,3,5}`. -/
theorem clusterLaw_two_point {a b : ℝ} (hab : a + b = 1) :
    clusterLaw b (deltaAt 3) = fun j => a * deltaAt 3 j + b * deltaAt 5 j := by
  have h : shiftConv (deltaAt 3) = deltaAt 5 := by
    have h3 := shiftConv_delta 3 (by norm_num)
    norm_num at h3
    exact h3
  funext j
  simp only [clusterLaw, h]
  rw [show (1 : ℝ) - b = a from by linarith]

end ChainClasses