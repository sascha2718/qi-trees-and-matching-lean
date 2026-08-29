/-
Finite cross-law screen grammar.

The one-law grammar uses the same support when the distinguished source cell
and the target zero list descend.  For two offspring laws these are different
operations: the source cell follows `SL`, while target zeros and the optional
normalization follow `SR`.  This file defines that asymmetric successor and
proves that it is still closed in the same bounded screen universe.

The final finite zipper alphabet is the product of a nonzero asynchronous lag
phase and a bounded cross screen.  No claim about transition weights is hidden
in this definition; those are supplied by `Obstructions/FiniteZipper.lean`
once the concrete macro outcomes have been chosen.
-/
import GraphMarkovMatching.Grammar.SourceRay
import GraphMarkovMatching.Grammar.Nilpotence
import ChainClasses.RenewalAlignment

namespace GraphMarkovMatching

open scoped ENNReal Classical

/-- Cross-law successor screens: source cells use the left support, whereas
target zero lists and normalizations use the right support. -/
def crossScreenSucc (SL SR : Finset ℕ) (sc : GScreen) : Finset GScreen :=
  ((tgtSucc SL sc.cell) ×ˢ normSucc SR sc.norm).image
    fun p => ⟨p.1, zsucc SR sc.zlist, p.2⟩

/-- The asymmetric screen grammar remains inside the common bounded universe
when both finite supports are bounded by `N`. -/
theorem crossScreenSucc_subset {N : ℕ} {SL SR : Finset ℕ} {sc : GScreen}
    (hN : 2 ≤ N) (hSL : ∀ k ∈ SL, k ≤ N) (hSR : ∀ k ∈ SR, k ≤ N)
    (hsc : sc ∈ screenUniv N) :
    crossScreenSucc SL SR sc ⊆ screenUniv N := by
  obtain ⟨hcell, hz, hnorm⟩ := mem_screenUniv.mp hsc
  intro sc' hsc'
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hsc'
  obtain ⟨hpcell, hpnorm⟩ := Finset.mem_product.mp hp
  refine mem_screenUniv.mpr
    ⟨tgtSucc_subset hN hSL hcell hpcell, zsucc_subset hN hSR hz,
      fun u hu => ?_⟩
  have hu' : p.2 = some u := hu
  cases hn : sc.norm with
  | none =>
      rw [hn] at hpnorm
      simp only [normSucc, Finset.mem_singleton] at hpnorm
      rw [hpnorm] at hu'
      exact absurd hu' (by simp)
  | some v =>
      rw [hn] at hpnorm
      simp only [normSucc] at hpnorm
      obtain ⟨w, hw, hwp⟩ := Finset.mem_image.mp hpnorm
      rw [← hwp] at hu'
      rw [← Option.some_inj.mp hu']
      exact tgtSucc_subset hN hSR (hnorm v hn) hw

/-! ### Cross-law self-pruning -/

/-- The zero list of a cross-law successor follows the right support. -/
lemma crossScreenSucc_zlist {SL SR : Finset ℕ} {sc sc' : GScreen}
    (h : sc' ∈ crossScreenSucc SL SR sc) :
    sc'.zlist = zsucc SR sc.zlist := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
  rfl

/-- The distinguished cell of a cross-law successor follows the left
support. -/
lemma crossScreenSucc_cell {SL SR : Finset ℕ} {sc sc' : GScreen}
    (h : sc' ∈ crossScreenSucc SL SR sc) :
    sc'.cell ∈ tgtSucc SL sc.cell := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
  exact (Finset.mem_product.mp hp).1

/-- Along a cross-law path the target zero list is the corresponding
iterate of the right-support successor. -/
lemma crossScreenPath_zlist {SL SR : Finset ℕ} (sc : ℕ → GScreen)
    (hpath : ∀ n, sc (n + 1) ∈ crossScreenSucc SL SR (sc n)) :
    ∀ n, (sc n).zlist = (zsucc SR)^[n] ((sc 0).zlist) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ihn =>
      rw [Function.iterate_succ_apply', ← ihn]
      exact crossScreenSucc_zlist (hpath n)

/-- **Cross-law self-pruning.**  If the return-depth set of the right
support has gcd one, there is no infinite cross-law screen path with a
nonempty zero list all of whose screens are live.  No equality of the two
supports is used: the source merely has to return to `F`, whereas cofiniteness
of the right return semigroup lets the target zero list wait for that return.
-/
theorem no_cross_live_path_of_depth_gcd_one
    {SL SR : Finset ℕ} (hgcd : (depthSet SR).gcd id = 1)
    (sc : ℕ → GScreen)
    (hpath : ∀ n, sc (n + 1) ∈ crossScreenSucc SL SR (sc n))
    (hne : (sc 0).zlist.Nonempty)
    (hlive : ∀ n, (sc n).cell ∉ (sc n).zlist) : False := by
  have hzl := crossScreenPath_zlist sc hpath
  have hcpath : ∀ n, (sc (n + 1)).cell ∈ tgtSucc SL ((sc n).cell) :=
    fun n => crossScreenSucc_cell (hpath n)
  -- First expose a fresh state from an arbitrary member of the target list.
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨s, hs⟩ : ∃ s, Descend SR s t₀ Tgt.F := by
    cases t₀ with
    | F => exact ⟨0, Descend.refl _⟩
    | Z j =>
        obtain ⟨d, hd⟩ := toFresh_nonempty j
        exact ⟨d, descend_of_mem_toFresh j d hd _ (fun x hx => hx)⟩
    | Fk k =>
        obtain ⟨d, hd⟩ := toFresh_nonempty k
        exact ⟨d, descend_of_mem_toFresh k d hd _ (fun x hx => hx)⟩
  have hFs : Tgt.F ∈ (zsucc SR)^[s] ((sc 0).zlist) :=
    mem_zsucc_iter_of_descend ht₀ hs
  -- Beyond the conductor, every length is a right-support return length.
  obtain ⟨R, hR⟩ := depths_semigroup SR
  -- From every position the distinguished source cell reaches `F` again.
  have hhits : ∀ n₀, ∃ m, (sc (n₀ + m)).cell = Tgt.F := by
    intro n₀
    cases hc0 : (sc n₀).cell with
    | F => exact ⟨0, by rw [Nat.add_zero]; exact hc0⟩
    | Z j =>
        have h := hcpath n₀
        rw [hc0] at h
        obtain ⟨m, _, hF⟩ := hits_F_of_gpair hcpath j n₀ h
        exact ⟨m, hF⟩
    | Fk k =>
        have h := hcpath n₀
        rw [hc0] at h
        obtain ⟨m, _, hF⟩ := hits_F_of_gpair hcpath k n₀ h
        exact ⟨m, hF⟩
  obtain ⟨m, hFcell⟩ := hhits (s + R)
  have hclgap : R + m ∈ AddSubmonoid.closure ((depthSet SR : Set ℕ)) := by
    apply hR (R + m) (by omega)
    rw [hgcd]
    exact one_dvd _
  -- The target fresh state persists to the same time through a fresh-to-fresh
  -- descent, contradicting liveness of the source fresh cell.
  have hFn : Tgt.F ∈ (sc (s + R + m)).zlist := by
    rw [hzl (s + R + m),
      show s + R + m = R + m + s from by omega,
      Function.iterate_add_apply]
    exact mem_zsucc_iter_of_descend hFs (descend_closure hclgap)
  exact hlive (s + R + m) (by rw [hFcell]; exact hFn)

/-- Periodic form of cross-law self-pruning. -/
theorem no_cross_live_cycle_of_depth_gcd_one
    {SL SR : Finset ℕ} (hgcd : (depthSet SR).gcd id = 1)
    {p : ℕ} (hp : 0 < p) (sc : ℕ → GScreen)
    (hpath : ∀ n, sc (n + 1) ∈ crossScreenSucc SL SR (sc n))
    (hper : ∀ n, sc (n + p) = sc n)
    (hne : (sc 0).zlist.Nonempty)
    (hlive : ∀ n < p, (sc n).cell ∉ (sc n).zlist) : False := by
  have hmod : ∀ n, sc n = sc (n % p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      by_cases hn : n < p
      · rw [Nat.mod_eq_of_lt hn]
      · have h1 : n - p + p = n := by omega
        have h2 := hper (n - p)
        rw [h1] at h2
        have h3 : (n - p) % p = n % p := by
          conv_rhs => rw [← h1]
          rw [Nat.add_mod_right]
        calc sc n = sc (n - p) := h2
          _ = sc ((n - p) % p) := ihn (n - p) (by omega)
          _ = sc (n % p) := by rw [h3]
  refine no_cross_live_path_of_depth_gcd_one hgcd sc hpath hne (fun n => ?_)
  rw [hmod n]
  exact hlive (n % p) (Nat.mod_lt n hp)

/-! ### The finite cross-law live block -/

/-- All bounded live screens with a nonempty zero list.  Accessibility is
unnecessary here: cross-law self-pruning already excludes cycles on this
larger finite family. -/
noncomputable def crossLiveScreens (N : ℕ) : Finset GScreen :=
  (screenUniv N).filter fun sc =>
    sc.zlist.Nonempty ∧ sc.cell ∉ sc.zlist
      ∧ ∀ u, sc.norm = some u → u ∉ sc.zlist

/-- The constant-weight support matrix of the cross-law live grammar. -/
noncomputable def crossN (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞) :
    {sc // sc ∈ crossLiveScreens N} →
      {sc // sc ∈ crossLiveScreens N} → ℝ≥0∞ :=
  fun i j => if j.val ∈ crossScreenSucc SL SR i.val then CW else 0

private lemma crossN_support {N : ℕ} {SL SR : Finset ℕ} {CW : ℝ≥0∞}
    {i j : {sc // sc ∈ crossLiveScreens N}}
    (h : crossN N SL SR CW i j ≠ 0) :
    j.val ∈ crossScreenSucc SL SR i.val := by
  by_contra hne
  apply h
  simp only [crossN]
  exact if_neg hne

/-- A finite transitive cycle can be unfolded into an indexed closed chain. -/
private lemma cross_transGen_exists_chain
    {ι : Type} {r : ι → ι → Prop} {a : ι}
    (h : Relation.TransGen r a a) :
    ∃ p : ℕ, 0 < p ∧ ∃ g : ℕ → ι, g 0 = a ∧ g p = a
      ∧ ∀ n < p, r (g n) (g (n + 1)) := by
  have unfold : ∀ {a b : ι}, Relation.TransGen r a b →
      ∃ p : ℕ, 0 < p ∧ ∃ g : ℕ → ι, g 0 = a ∧ g p = b
        ∧ ∀ n < p, r (g n) (g (n + 1)) := by
    intro a b hab
    induction hab with
    | @single c hac =>
        refine ⟨1, Nat.one_pos, fun n => if n = 0 then a else c, ?_, ?_, ?_⟩
        · exact if_pos rfl
        · exact if_neg Nat.one_ne_zero
        · intro n hn
          have hn0 : n = 0 := by omega
          subst hn0
          simpa using hac
    | @tail b c hab hbc ih =>
        obtain ⟨p, hp, g, hg0, hgp, hstep⟩ := ih
        refine ⟨p + 1, by omega, fun n => if n ≤ p then g n else c,
          ?_, ?_, ?_⟩
        · exact (if_pos (Nat.zero_le p)).trans hg0
        · exact if_neg (by omega)
        · intro n hn
          show r (if n ≤ p then g n else c)
            (if n + 1 ≤ p then g (n + 1) else c)
          by_cases hnp : n + 1 ≤ p
          · rw [if_pos (by omega), if_pos hnp]
            exact hstep n (by omega)
          · have hne : n = p := by omega
            subst n
            rw [if_pos (le_refl p), if_neg hnp, hgp]
            exact hbc
  exact unfold h

/-- A non-power-of-two atom in the right support makes the finite cross-law
screen block acyclic. -/
theorem crossN_acyclic_of_nonpower_right
    {N : ℕ} {SL SR : Finset ℕ} {b : ℕ}
    (hb : b ∈ SR) (hb2 : 2 ≤ b) (hbpow : ¬ IsPowerOfTwo b)
    (CW : ℝ≥0∞) :
    ∀ i, ¬ Relation.TransGen (supportRel (crossN N SL SR CW)) i i := by
  intro i hcyc
  obtain ⟨p, hp, g, hg0, hgp, hstep⟩ := cross_transGen_exists_chain hcyc
  have hedge : ∀ n, n < p →
      (g (n + 1)).val ∈ crossScreenSucc SL SR ((g n).val) :=
    fun n hn => crossN_support (hstep n hn)
  have hprops : ∀ m : ℕ,
      (g m).val.zlist.Nonempty
        ∧ (g m).val.cell ∉ (g m).val.zlist
        ∧ ∀ u, (g m).val.norm = some u → u ∉ (g m).val.zlist :=
    fun m => (Finset.mem_filter.mp (g m).property).2
  have hmod1 : ∀ n : ℕ, (n + 1) % p = (n % p + 1) % p :=
    fun n => (Nat.mod_add_mod n p 1).symm
  have hpath : ∀ n : ℕ,
      (g ((n + 1) % p)).val ∈
        crossScreenSucc SL SR ((g (n % p)).val) := by
    intro n
    have hm : n % p < p := Nat.mod_lt n hp
    by_cases hcase : n % p + 1 < p
    · have h1 : (n + 1) % p = n % p + 1 := by
        rw [hmod1 n, Nat.mod_eq_of_lt hcase]
      rw [h1]
      exact hedge (n % p) hm
    · have hpe : n % p + 1 = p := by omega
      have h1 : (n + 1) % p = 0 := by
        rw [hmod1 n, hpe, Nat.mod_self]
      have h2 := hedge (n % p) hm
      rw [hpe, hgp, ← hg0] at h2
      rw [h1]
      exact h2
  have hper : ∀ n : ℕ,
      (g ((n + p) % p)).val = (g (n % p)).val := by
    intro n
    rw [Nat.add_mod_right]
  exact no_cross_live_cycle_of_depth_gcd_one
    (depthSet_gcd_eq_one_of_nonpower_mem hb hb2 hbpow) hp
    (fun n => (g (n % p)).val) hpath hper
    (hprops (0 % p)).1 (fun n _ => (hprops (n % p)).2.1)

/-- Consequently the finite cross-law screen block is nilpotent. -/
theorem crossN_nilpotent_of_nonpower_right
    {N : ℕ} {SL SR : Finset ℕ} {b : ℕ}
    (hb : b ∈ SR) (hb2 : 2 ≤ b) (hbpow : ¬ IsPowerOfTwo b)
    (CW : ℝ≥0∞) :
    ∀ x, (mulVec (crossN N SL SR CW))^[
        Fintype.card {sc // sc ∈ crossLiveScreens N} + 1] x = fun _ => 0 := by
  intro x
  have h := nilpotent_of_acyclic (crossN N SL SR CW)
    (crossN_acyclic_of_nonpower_right hb hb2 hbpow CW)
  rw [Function.iterate_succ_apply]
  exact h (mulVec (crossN N SL SR CW) x)

/-- The explicit finite alphabet for the combined arity-lag/screen zipper.
Zero lag is omitted because it is the killed/closed macro state. -/
noncomputable def crossPhaseFinset (N MA MB : ℕ) :
    Finset (ℤ × GScreen) :=
  ((ChainClasses.renewalLagStates MA MB).filter (· ≠ 0)) ×ˢ screenUniv N

/-- Combined live phases as a genuine finite type. -/
abbrev CrossPhase (N MA MB : ℕ) := ↥(crossPhaseFinset N MA MB)

lemma crossPhase_val_mem_lag {N MA MB : ℕ} (p : CrossPhase N MA MB) :
    p.1.1 ∈ ChainClasses.renewalLagStates MA MB := by
  exact (Finset.mem_filter.mp (Finset.mem_product.mp p.2).1).1

lemma crossPhase_val_ne_zero {N MA MB : ℕ} (p : CrossPhase N MA MB) :
    p.1.1 ≠ 0 := by
  exact (Finset.mem_filter.mp (Finset.mem_product.mp p.2).1).2

lemma crossPhase_screen_mem {N MA MB : ℕ} (p : CrossPhase N MA MB) :
    p.1.2 ∈ screenUniv N :=
  (Finset.mem_product.mp p.2).2

end GraphMarkovMatching
