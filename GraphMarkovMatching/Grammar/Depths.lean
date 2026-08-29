/-
The renewal-depth combinatorics of the varying-offspring process
(`arbitrary_offspring_matching.tex`, `def:renewal` and
`thm:semigroup`): the return lengths from an exposed counter to the
next fresh state along descendant rays of the kernel, their finiteness
and bounds, and the numerical-semigroup input of the nilpotence
theorem, imported from mathlib.

* `toFresh k`: the finite set of distances from a vertex with counter
  `k` to the next fresh state below it, following the kernel: counters
  `k ≤ 2` emit two fresh children, `k = 3` emits the forced counter
  `2` and one fresh child, `k ≥ 4` forces the split `(k/2, k - k/2)`;
* `toFresh_nonempty`, `one_le_of_mem_toFresh`, `le_of_mem_toFresh`:
  every counter reaches a fresh state, in at least one and at most
  `k + 1` steps;
* `sq_le_eight_mul_succ_of_mem_toFresh`: the quantitative cascade
  estimate `d^2 \le 8(k+1)`, used by the exponential-tail ledger;
* `depthSet S`: the return lengths `𝒟_ν` of a support `S`;
* `setGcd_coe_finset`: the mathlib set-gcd of a finite set is its
  finset gcd;
* `depths_semigroup`: every sufficiently large multiple of
  `gcd 𝒟_ν` is a sum of return lengths (`thm:semigroup`, from
  `Nat.exists_mem_closure_of_ge`).
-/
import Mathlib.NumberTheory.FrobeniusNumber

namespace GraphMarkovMatching

/-- The return lengths from an exposed counter `k`: the distances to
the next fresh state along descendant rays of the varying-offspring
kernel. -/
def toFresh : ℕ → Finset ℕ
  | 0 => {1}
  | 1 => {1}
  | 2 => {1}
  | 3 => insert 1 ((toFresh 2).image (· + 1))
  | k + 4 => ((toFresh ((k + 4) / 2)).image (· + 1))
      ∪ ((toFresh (k + 4 - (k + 4) / 2)).image (· + 1))
decreasing_by all_goals omega

/-- Small counters reach a fresh state in one step. -/
lemma toFresh_le_two {k : ℕ} (hk : k ≤ 2) : toFresh k = {1} := by
  match k, hk with
  | 0, _ => simp [toFresh]
  | 1, _ => simp [toFresh]
  | 2, _ => simp [toFresh]

/-- The ternary counter reaches a fresh state in one or two steps. -/
lemma toFresh_three : toFresh 3 = {1, 2} := by
  rw [show toFresh 3 = insert 1 ((toFresh 2).image (· + 1)) from by
      simp [toFresh],
    toFresh_le_two (by omega), Finset.image_singleton]

/-- The forced-split recursion for large counters. -/
lemma toFresh_of_ge {k : ℕ} (hk : 4 ≤ k) :
    toFresh k = ((toFresh (k / 2)).image (· + 1))
      ∪ ((toFresh (k - k / 2)).image (· + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  rw [toFresh]

/-- A natural number is a power of two.  This local predicate is used to
state the exact structural distinction for the balanced counter cascade. -/
def IsPowerOfTwo (k : ℕ) : Prop := ∃ n : ℕ, k = 2 ^ n

/-- A counter which is at least two and is not a power of two exposes fresh
descendants on two consecutive levels.  Thus a single such counter already
removes the return-depth gcd obstruction. -/
theorem exists_consecutive_mem_toFresh : ∀ k, 2 ≤ k → ¬ IsPowerOfTwo k →
    ∃ d, d ∈ toFresh k ∧ d + 1 ∈ toFresh k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hk2 hpow
      by_cases h2 : k ≤ 2
      · have hk : k = 2 := by omega
        exfalso
        apply hpow
        exact ⟨1, by simp [hk]⟩
      · by_cases h3 : k = 3
        · subst k
          exact ⟨1, by simp [toFresh_three]⟩
        · have h4 : 4 ≤ k := by omega
          let l := k / 2
          let u := k - k / 2
          have hl2 : 2 ≤ l := by simp [l]; omega
          have hu2 : 2 ≤ u := by simp [u]; omega
          have hlk : l < k := by simp [l]; omega
          have huk : u < k := by simp [u]; omega
          have hnotboth : ¬ (IsPowerOfTwo l ∧ IsPowerOfTwo u) := by
            rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
            have hsum : l + u = k := by
              have hdiv : k / 2 ≤ k := Nat.div_le_self k 2
              simp [l, u]
              omega
            have hlu : u = l ∨ u = l + 1 := by
              simp [l, u]
              omega
            rcases hlu with hlu | hlu
            · apply hpow
              refine ⟨m + 1, ?_⟩
              rw [← hsum, hlu, hm, pow_succ]
              ring
            · cases m with
              | zero => simp at hm; omega
              | succ m =>
                  cases n with
                  | zero => simp at hn; omega
                  | succ n =>
                      have hlEven : ∃ a, l = 2 * a := by
                        refine ⟨2 ^ m, ?_⟩
                        rw [hm, pow_succ]
                        ring
                      have huEven : ∃ a, u = 2 * a := by
                        refine ⟨2 ^ n, ?_⟩
                        rw [hn, pow_succ]
                        ring
                      obtain ⟨a, ha⟩ := hlEven
                      obtain ⟨b, hb⟩ := huEven
                      omega
          rcases not_and_or.mp hnotboth with hlpow | hupow
          · obtain ⟨d, hd, hd1⟩ := ih l hlk hl2 hlpow
            refine ⟨d + 1, ?_, ?_⟩
            · rw [toFresh_of_ge h4]
              exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
            · rw [toFresh_of_ge h4]
              exact Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨d + 1, hd1, by omega⟩)
          · obtain ⟨d, hd, hd1⟩ := ih u huk hu2 hupow
            refine ⟨d + 1, ?_, ?_⟩
            · rw [toFresh_of_ge h4]
              exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
            · rw [toFresh_of_ge h4]
              exact Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨d + 1, hd1, by omega⟩)

/-- Every counter reaches a fresh state. -/
lemma toFresh_nonempty : ∀ k, (toFresh k).Nonempty := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h2 : k ≤ 2
    · rw [toFresh_le_two h2]
      exact ⟨1, Finset.mem_singleton_self 1⟩
    · by_cases h3 : k = 3
      · subst h3
        rw [toFresh_three]
        exact ⟨1, by simp⟩
      · have h4 : 4 ≤ k := by omega
        obtain ⟨d, hd⟩ := ih (k / 2) (by omega)
        rw [toFresh_of_ge h4]
        exact ⟨d + 1,
          Finset.mem_union_left _ (Finset.mem_image_of_mem _ hd)⟩

/-- Return lengths are positive. -/
lemma one_le_of_mem_toFresh : ∀ k, ∀ d ∈ toFresh k, 1 ≤ d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hd
    by_cases h2 : k ≤ 2
    · rw [toFresh_le_two h2] at hd
      simp at hd
      omega
    · by_cases h3 : k = 3
      · subst h3
        rw [toFresh_three] at hd
        simp at hd
        omega
      · have h4 : 4 ≤ k := by omega
        rw [toFresh_of_ge h4] at hd
        rcases Finset.mem_union.mp hd with h | h <;>
          · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp h
            omega

/-- Return lengths are at most `k + 1`. -/
lemma le_of_mem_toFresh : ∀ k, ∀ d ∈ toFresh k, d ≤ k + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hd
    by_cases h2 : k ≤ 2
    · rw [toFresh_le_two h2] at hd
      simp at hd
      omega
    · by_cases h3 : k = 3
      · subst h3
        rw [toFresh_three] at hd
        simp at hd
        omega
      · have h4 : 4 ≤ k := by omega
        rw [toFresh_of_ge h4] at hd
        rcases Finset.mem_union.mp hd with h | h
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
          have := ih (k / 2) (by omega) e he
          omega
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
          have := ih (k - k / 2) (by omega) e he
          omega

/-- **Quadratic cascade bound.**  A return from counter `k` at depth
`d` satisfies `d² ≤ 8(k+1)`.  The true order is logarithmic, but this
weaker estimate is deliberately used by the exponential-tail proof:
it is elementary to propagate through the two halving branches, and
it already turns an exponential counter tail into Gaussian decay in
the length of a live screen path. -/
lemma sq_le_eight_mul_succ_of_mem_toFresh :
    ∀ k, ∀ d ∈ toFresh k, d * d ≤ 8 * (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hd
    by_cases h2 : k ≤ 2
    · rw [toFresh_le_two h2] at hd
      have : d = 1 := Finset.mem_singleton.mp hd
      subst d
      omega
    · by_cases h3 : k = 3
      · subst h3
        rw [toFresh_three] at hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl <;> norm_num
      · have h4 : 4 ≤ k := by omega
        rw [toFresh_of_ge h4] at hd
        rcases Finset.mem_union.mp hd with hd | hd
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
          have hsquare := ih (k / 2) (by omega) e he
          have hlinear := le_of_mem_toFresh (k / 2) e he
          have hhalf : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
          nlinarith
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
          have hsquare := ih (k - k / 2) (by omega) e he
          have hlinear := le_of_mem_toFresh (k - k / 2) e he
          have hhalf : 2 * (k - k / 2) ≤ k + 1 := by omega
          nlinarith

/-- The return lengths `𝒟_ν` of a support `S`. -/
def depthSet (S : Finset ℕ) : Finset ℕ := S.biUnion toFresh

/-- If a finite offspring support contains one non-power-of-two counter,
then its return-depth set has gcd one.  This is the formal form of the
claim that the exceptional descendant tree appears on consecutive levels,
so it cannot carry a persistent depth-period obstruction. -/
theorem depthSet_gcd_eq_one_of_nonpower_mem {S : Finset ℕ} {k : ℕ}
    (hkS : k ∈ S) (hk2 : 2 ≤ k) (hpow : ¬ IsPowerOfTwo k) :
    (depthSet S).gcd id = 1 := by
  obtain ⟨d, hd, hd1⟩ := exists_consecutive_mem_toFresh k hk2 hpow
  have hdS : d ∈ depthSet S := Finset.mem_biUnion.mpr ⟨k, hkS, hd⟩
  have hd1S : d + 1 ∈ depthSet S := Finset.mem_biUnion.mpr ⟨k, hkS, hd1⟩
  apply Nat.eq_one_of_dvd_one
  have hdiv1 : (depthSet S).gcd id ∣ d + 1 := Finset.gcd_dvd hd1S
  have hdiv0 : (depthSet S).gcd id ∣ d := Finset.gcd_dvd hdS
  simpa using Nat.dvd_sub hdiv1 hdiv0

/-- A nonempty support has a return length. -/
lemma depthSet_nonempty {S : Finset ℕ} (hS : S.Nonempty) :
    (depthSet S).Nonempty := by
  obtain ⟨k, hk⟩ := hS
  obtain ⟨d, hd⟩ := toFresh_nonempty k
  exact ⟨d, Finset.mem_biUnion.mpr ⟨k, hk, hd⟩⟩

/-- Return lengths of a bounded support are bounded. -/
lemma depthSet_le {S : Finset ℕ} {N : ℕ} (hS : ∀ k ∈ S, k ≤ N) :
    ∀ d ∈ depthSet S, d ≤ N + 1 := by
  intro d hd
  obtain ⟨k, hk, hdk⟩ := Finset.mem_biUnion.mp hd
  have h1 := le_of_mem_toFresh k d hdk
  have h2 := hS k hk
  omega

/-- The mathlib set-gcd of a finite set is its finset gcd. -/
lemma setGcd_coe_finset (D : Finset ℕ) :
    Nat.setGcd (D : Set ℕ) = D.gcd id := by
  refine Nat.dvd_antisymm ?_ ?_
  · exact Finset.dvd_gcd fun i hi => Nat.setGcd_dvd_of_mem hi
  · exact Nat.dvd_setGcd_iff.mpr fun m hm => Finset.gcd_dvd hm

/-- **The numerical semigroup lemma** (`thm:semigroup`): every
sufficiently large multiple of `gcd 𝒟_ν` is a sum of return
lengths. -/
theorem depths_semigroup (S : Finset ℕ) :
    ∃ R, ∀ m, R ≤ m → (depthSet S).gcd id ∣ m →
      m ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)) := by
  obtain ⟨R, hR⟩ := Nat.exists_mem_closure_of_ge ((depthSet S : Set ℕ))
  refine ⟨R, fun m hm hdvd => hR m hm ?_⟩
  rw [setGcd_coe_finset]
  exact hdvd

/-- Two finite supports which each contain a non-power-of-two counter have
all sufficiently large return depths in common.  Equality at small levels is
neither claimed nor needed: this is exactly the eventual compatibility used
by the rare two-law zipper. -/
theorem eventually_common_depths_of_nonpower_mem
    (A B : Finset ℕ) {a b : ℕ}
    (haA : a ∈ A) (ha2 : 2 ≤ a) (hpa : ¬ IsPowerOfTwo a)
    (hbB : b ∈ B) (hb2 : 2 ≤ b) (hpb : ¬ IsPowerOfTwo b) :
    ∃ R, ∀ m, R ≤ m →
      m ∈ AddSubmonoid.closure ((depthSet A : Set ℕ)) ∧
      m ∈ AddSubmonoid.closure ((depthSet B : Set ℕ)) := by
  have hgA : (depthSet A).gcd id = 1 :=
    depthSet_gcd_eq_one_of_nonpower_mem haA ha2 hpa
  have hgB : (depthSet B).gcd id = 1 :=
    depthSet_gcd_eq_one_of_nonpower_mem hbB hb2 hpb
  obtain ⟨RA, hA⟩ := depths_semigroup A
  obtain ⟨RB, hB⟩ := depths_semigroup B
  refine ⟨max RA RB, fun m hm => ?_⟩
  constructor
  · apply hA m (le_trans (le_max_left _ _) hm)
    rw [hgA]
    exact one_dvd m
  · apply hB m (le_trans (le_max_right _ _) hm)
    rw [hgB]
    exact one_dvd m

end GraphMarkovMatching
