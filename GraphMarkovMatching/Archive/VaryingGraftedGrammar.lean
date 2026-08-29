/-
The finite level-synchronous target grammar for the literal grafted 11/13
kernel.

Only seven recursive laws occur below a fresh vertex: the fresh law, the
ordinary frozen counters 2--5, and the two provenance markers.  The common
offspring atoms 3,5,7,9 produce the same formal successors on both sides;
the exceptional 11/13 atoms are kept separate and will carry their literal
coefficient zeta in the semantic ledger.

The important combinatorial fact is particularly short for this example.
Under the common support, every nonempty target zero list contains `F` after
two steps, while every source path meets `F` within five steps.  Hence the
common live-screen graph is acyclic.  This is the nilpotent `N` block needed
by `VaryingGraftedEstimate`.
-/
import GraphMarkovMatching.Archive.VaryingGraftedKernel
import GraphMarkovMatching.Grammar.Nilpotence

namespace GraphMarkovMatching

open scoped ENNReal Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The complete recursive target alphabet below the two exceptional root
components. -/
inductive GraftTgt where
  | F
  | Z2 | Z3 | Z4 | Z5
  | M3 | M5
deriving DecidableEq, Fintype, Repr

/-- The two child targets of a frozen recursive target. -/
def graftForcedPair : GraftTgt → Option (GraftTgt × GraftTgt)
  | .F => none
  | .Z2 => some (.F, .F)
  | .Z3 => some (.Z2, .F)
  | .Z4 => some (.Z2, .Z2)
  | .Z5 => some (.Z2, .Z3)
  | .M3 => some (.Z2, .Z5)
  | .M5 => some (.Z2, .M3)

/-- Component targets contributed by the four common offspring atoms
`3,5,7,9`. -/
def graftCommonFreshSucc : Finset GraftTgt :=
  {.F, .Z2, .Z3, .Z4, .Z5}

/-- Common/deterministic successor targets.  Marker descent is coefficient
free: its exceptional coefficient was paid when the marker was entered. -/
def graftCommonSucc : GraftTgt → Finset GraftTgt
  | .F => graftCommonFreshSucc
  | t => match graftForcedPair t with
    | none => ∅
    | some p => {p.1, p.2}

/-- The left exceptional root component `11 -> (M3,Z4)`. -/
def graftLeftRareSucc : Finset GraftTgt := {.M3, .Z4}

/-- The right exceptional root component `13 -> (Z4,M5)`. -/
def graftRightRareSucc : Finset GraftTgt := {.Z4, .M5}

def graftRareSucc (left : Bool) : GraftTgt → Finset GraftTgt
  | .F => if left then graftLeftRareSucc else graftRightRareSucc
  | _ => ∅

/-- A finite semantic screen: a source cell, a nonempty target zero list,
and an optional target normalization. -/
structure GraftScreen where
  cell : GraftTgt
  zlist : Finset GraftTgt
  norm : Option GraftTgt
deriving DecidableEq, Fintype

def graftNormSuccCommon : Option GraftTgt → Finset (Option GraftTgt)
  | none => {none}
  | some t => (graftCommonSucc t).image some

def graftZSuccCommon (z : Finset GraftTgt) : Finset GraftTgt :=
  z.biUnion graftCommonSucc

/-- One common-core screen step. -/
def graftScreenSuccCommon (sc : GraftScreen) : Finset GraftScreen :=
  ((graftCommonSucc sc.cell) ×ˢ graftNormSuccCommon sc.norm).image
    fun p => ⟨p.1, graftZSuccCommon sc.zlist, p.2⟩

/-- The finite live block.  Formal source/zero diagonals and normalization
diagonals are diverted to the inhomogeneous zero-interface ledger. -/
def graftLiveScreens : Finset GraftScreen :=
  Finset.univ.filter fun sc =>
    sc.zlist.Nonempty ∧ sc.cell ∉ sc.zlist ∧
      ∀ u, sc.norm = some u → u ∉ sc.zlist

lemma graftLiveScreen_nonempty (i : {sc // sc ∈ graftLiveScreens}) :
    i.val.zlist.Nonempty :=
  (Finset.mem_filter.mp i.property).2.1

lemma graftLiveScreen_cell_not_mem (i : {sc // sc ∈ graftLiveScreens}) :
    i.val.cell ∉ i.val.zlist :=
  (Finset.mem_filter.mp i.property).2.2.1

lemma graftScreenSuccCommon_cell {sc sc' : GraftScreen}
    (h : sc' ∈ graftScreenSuccCommon sc) :
    sc'.cell ∈ graftCommonSucc sc.cell := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
  exact (Finset.mem_product.mp hp).1

lemma graftScreenSuccCommon_zlist {sc sc' : GraftScreen}
    (h : sc' ∈ graftScreenSuccCommon sc) :
    sc'.zlist = graftZSuccCommon sc.zlist := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp h
  rfl

/-! ### The two-step target and five-step source certificates -/

@[simp] lemma graft_F_mem_commonSucc : GraftTgt.F ∈ graftCommonSucc .F := by
  simp [graftCommonSucc, graftCommonFreshSucc]

lemma graft_F_persists {z : Finset GraftTgt} (hF : GraftTgt.F ∈ z) :
    GraftTgt.F ∈ graftZSuccCommon z := by
  rw [graftZSuccCommon, Finset.mem_biUnion]
  exact ⟨.F, hF, graft_F_mem_commonSucc⟩

/-- From every target symbol, the union successor contains `F` after two
steps. -/
lemma graft_F_mem_two_zsteps_singleton (t : GraftTgt) :
    GraftTgt.F ∈
      graftZSuccCommon (graftZSuccCommon {t}) := by
  cases t <;> decide

lemma graft_F_mem_two_zsteps {z : Finset GraftTgt} (hz : z.Nonempty) :
    GraftTgt.F ∈ graftZSuccCommon (graftZSuccCommon z) := by
  obtain ⟨t, ht⟩ := hz
  have hmono1 : graftZSuccCommon {t} ⊆ graftZSuccCommon z := by
    intro u hu
    rw [graftZSuccCommon, Finset.mem_biUnion] at hu ⊢
    obtain ⟨s, hs, hus⟩ := hu
    have hst : s = t := by simpa using hs
    subst s
    exact ⟨t, ht, hus⟩
  have hmono2 :
      graftZSuccCommon (graftZSuccCommon {t}) ⊆
        graftZSuccCommon (graftZSuccCommon z) := by
    intro u hu
    rw [graftZSuccCommon, Finset.mem_biUnion] at hu ⊢
    obtain ⟨s, hs, hus⟩ := hu
    exact ⟨s, hmono1 hs, hus⟩
  exact hmono2 (graft_F_mem_two_zsteps_singleton t)

/-- A decreasing rank away from `F`. -/
def graftSourceRank : GraftTgt → ℕ
  | .F => 0
  | .Z2 => 1
  | .Z3 => 2
  | .Z4 => 2
  | .Z5 => 3
  | .M3 => 4
  | .M5 => 5

lemma graftSourceRank_le_five (t : GraftTgt) : graftSourceRank t ≤ 5 := by
  cases t <;> decide

lemma graftSourceRank_zero_iff (t : GraftTgt) :
    graftSourceRank t = 0 ↔ t = .F := by
  cases t <;> decide

lemma graftSourceRank_decreases {s t : GraftTgt}
    (hs : s ≠ .F) (ht : t ≠ .F) (hst : t ∈ graftCommonSucc s) :
    graftSourceRank t < graftSourceRank s := by
  cases s <;> cases t <;> simp_all [graftCommonSucc, graftForcedPair,
    graftSourceRank]

/-- Every infinite common successor path hits `F` in its first five edges. -/
lemma graft_source_hits_F (c : ℕ → GraftTgt)
    (hpath : ∀ n, c (n + 1) ∈ graftCommonSucc (c n)) :
    ∃ n ≤ 5, c n = .F := by
  by_contra h
  push Not at h
  have hdec : ∀ n < 5,
      graftSourceRank (c (n + 1)) < graftSourceRank (c n) := by
    intro n hn
    exact graftSourceRank_decreases (h n (by omega))
      (h (n + 1) (by omega)) (hpath n)
  have h01 : graftSourceRank (c 1) < graftSourceRank (c 0) := by
    simpa using hdec 0 (by omega)
  have h12 : graftSourceRank (c 2) < graftSourceRank (c 1) := by
    simpa using hdec 1 (by omega)
  have h23 : graftSourceRank (c 3) < graftSourceRank (c 2) := by
    simpa using hdec 2 (by omega)
  have h34 : graftSourceRank (c 4) < graftSourceRank (c 3) := by
    simpa using hdec 3 (by omega)
  have h45 : graftSourceRank (c 5) < graftSourceRank (c 4) := by
    simpa using hdec 4 (by omega)
  have hr := graftSourceRank_le_five (c 0)
  have hz : graftSourceRank (c 5) = 0 := by omega
  exact h 5 (by omega) ((graftSourceRank_zero_iff (c 5)).mp hz)

/-! ### Acyclicity and nilpotence -/

private lemma graft_transGen_exists_chain
    {iota : Type} {r : iota → iota → Prop} {a : iota}
    (h : Relation.TransGen r a a) :
    ∃ p : ℕ, 0 < p ∧ ∃ g : ℕ → iota, g 0 = a ∧ g p = a ∧
      ∀ n < p, r (g n) (g (n + 1)) := by
  have unfold : ∀ {a b : iota}, Relation.TransGen r a b →
      ∃ p : ℕ, 0 < p ∧ ∃ g : ℕ → iota, g 0 = a ∧ g p = b ∧
        ∀ n < p, r (g n) (g (n + 1)) := by
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

/-- The common screen matrix, in both directions. -/
noncomputable def graftCommonN (CW : ℝ≥0∞) :
    (Bool × {sc // sc ∈ graftLiveScreens}) →
      (Bool × {sc // sc ∈ graftLiveScreens}) → ℝ≥0∞ :=
  fun i j => if i.1 = j.1 ∧ j.2.val ∈ graftScreenSuccCommon i.2.val
    then CW else 0

private lemma graftCommonN_support {CW : ℝ≥0∞}
    {i j : Bool × {sc // sc ∈ graftLiveScreens}}
    (h : graftCommonN CW i j ≠ 0) :
    i.1 = j.1 ∧ j.2.val ∈ graftScreenSuccCommon i.2.val := by
  by_contra hn
  rw [graftCommonN, if_neg hn] at h
  exact h rfl

/-- The literal common tagged live block has no directed cycle. -/
theorem graftCommonN_acyclic (CW : ℝ≥0∞) :
    ∀ i, ¬ Relation.TransGen (supportRel (graftCommonN CW)) i i := by
  intro i hcyc
  obtain ⟨p, hp, g, hg0, hgp, hstep⟩ := graft_transGen_exists_chain hcyc
  have hedge : ∀ n, n < p →
      (g (n + 1)).2.val ∈ graftScreenSuccCommon (g n).2.val :=
    fun n hn => (graftCommonN_support (hstep n hn)).2
  have hmod1 : ∀ n : ℕ, (n + 1) % p = (n % p + 1) % p :=
    fun n => (Nat.mod_add_mod n p 1).symm
  let sc : ℕ → GraftScreen := fun n => (g (n % p)).2.val
  have hpath : ∀ n, sc (n + 1) ∈ graftScreenSuccCommon (sc n) := by
    intro n
    have hm : n % p < p := Nat.mod_lt n hp
    by_cases hcase : n % p + 1 < p
    · have h1 : (n + 1) % p = n % p + 1 := by
        rw [hmod1 n, Nat.mod_eq_of_lt hcase]
      simpa [sc, h1] using hedge (n % p) hm
    · have heq : n % p + 1 = p := by omega
      have h1 : (n + 1) % p = 0 := by
        rw [hmod1 n, heq, Nat.mod_self]
      have hlast := hedge (n % p) hm
      rw [heq, hgp, ← hg0] at hlast
      simpa [sc, h1] using hlast
  have hzstep : ∀ n, (sc (n + 1)).zlist =
      graftZSuccCommon (sc n).zlist :=
    fun n => graftScreenSuccCommon_zlist (hpath n)
  have hzF2 : GraftTgt.F ∈ (sc 2).zlist := by
    rw [hzstep 1, hzstep 0]
    exact graft_F_mem_two_zsteps (graftLiveScreen_nonempty (g (0 % p)).2)
  have hzF : ∀ n, GraftTgt.F ∈ (sc (2 + n)).zlist := by
    intro n
    induction n with
    | zero => simpa using hzF2
    | succ n ih =>
        rw [show 2 + (n + 1) = (2 + n) + 1 by omega, hzstep (2 + n)]
        exact graft_F_persists ih
  have hcpath : ∀ n,
      (sc (2 + (n + 1))).cell ∈ graftCommonSucc (sc (2 + n)).cell := by
    intro n
    exact graftScreenSuccCommon_cell (hpath (2 + n))
  obtain ⟨m, hm5, hmF⟩ := graft_source_hits_F
    (fun n => (sc (2 + n)).cell) hcpath
  have hlive : (sc (2 + m)).cell ∉ (sc (2 + m)).zlist := by
    exact graftLiveScreen_cell_not_mem (g ((2 + m) % p)).2
  exact hlive (hmF ▸ hzF m)

/-- Nilpotence of the common tagged block. -/
theorem graftCommonN_nilpotent (CW : ℝ≥0∞) :
    ∀ x, (mulVec (graftCommonN CW))^[
        Fintype.card (Bool × {sc // sc ∈ graftLiveScreens})] x =
      fun _ => 0 :=
  nilpotent_of_acyclic (graftCommonN CW) (graftCommonN_acyclic CW)

lemma graftCommonN_row_sum_le (CW : ℝ≥0∞)
    (i : Bool × {sc // sc ∈ graftLiveScreens}) :
    ∑ j, graftCommonN CW i j ≤
      CW * Fintype.card (Bool × {sc // sc ∈ graftLiveScreens}) := by
  calc
    ∑ j, graftCommonN CW i j ≤ ∑ _j, CW := by
      exact Finset.sum_le_sum fun j _ => by
        by_cases h : i.1 = j.1 ∧
            j.2.val ∈ graftScreenSuccCommon i.2.val
        · rw [graftCommonN, if_pos h]
        · rw [graftCommonN, if_neg h]
          exact zero_le
    _ = (Fintype.card (Bool × {sc // sc ∈ graftLiveScreens}) : ℝ≥0∞) * CW := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = CW * Fintype.card (Bool × {sc // sc ∈ graftLiveScreens}) :=
      mul_comm _ _

end GraphMarkovMatching
