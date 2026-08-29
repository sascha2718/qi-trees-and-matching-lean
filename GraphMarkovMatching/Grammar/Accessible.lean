/-
Accessibility and the acyclicity of the screen graph
(`arbitrary_offspring_matching.tex`: `thm:descend-realise`,
`thm:coverage`, `def:anchored`, `thm:anchor-step`, and
`thm:nilpotence`; the definitions `def:ordacc` and `def:scracc` live
in `Grammar/Index.lean`): provenance is captured by an anchoring predicate,
every fresh-to-fresh descent length lies in the semigroup, anchoring
propagates along the grammar, and no infinite (hence no periodic)
anchored live screen path exists.

* `descend_split` (`thm:descend-realise`, decomposition): a
  fresh-to-fresh descent
    length lies in `Σ_ν`, and a descent to fresh from inside the
  cascade of `j` completes it at a length in `toFresh j` plus an
  element of `Σ_ν`;
* `TgtAnchored` / `Anchored`: the anchoring of `def:anchored` in
  invariant form: every fresh completion of the target (of the cell
  and of every zero-list member) ends at an absolute depth in `Σ_ν`;
  `TgtAnchored.step` and `Anchored.step` propagate it along the
  grammar (`thm:anchor-step`), and `screenPath_zlist` iterates zero
  lists along screen paths (`thm:coverage`);
* `no_anchored_live_path` (**`thm:nilpotence`, acyclicity**): an
  infinite screen path of anchored screens with nonempty seed zero
  list reaches a screen whose zero list contains its own cell, so
  the path is not live: the alignment is the Frobenius step
  `depths_semigroup`, since both the source fresh depth and the
  target fresh-entry depth are anchored in `Σ_ν`;
* `no_anchored_live_cycle`: the periodic form: a cycle of anchored
  live screens is impossible.
-/
import GraphMarkovMatching.Grammar.SourceRay

namespace GraphMarkovMatching

/-- **The cascade decomposition of descents** (`thm:descend-realise`,
decomposition): a fresh-to-fresh descent
length lies in the semigroup, and a descent to fresh from inside the
cascade of `j` completes it at a return length of `j` plus a semigroup
element. -/
lemma descend_split {S : Finset ℕ} : ∀ m,
    (Descend S m Tgt.F Tgt.F
      → m ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)))
    ∧ (∀ j x, x ∈ gpair j → Descend S m x Tgt.F →
        ∃ g ∈ toFresh j,
          ∃ r ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)),
            m + 1 = g + r) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hA : Descend S m Tgt.F Tgt.F
        → m ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)) := by
      intro hd
      cases hd with
      | refl => exact AddSubmonoid.zero_mem _
      | @step m' _ y _ h h' =>
          obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.mp h
          obtain ⟨g, hg, r, hr, hEq⟩ := (ih m' (by omega)).2 k y hx h'
          rw [hEq]
          exact AddSubmonoid.add_mem _
            (AddSubmonoid.subset_closure (Finset.mem_coe.mpr
              (Finset.mem_biUnion.mpr ⟨k, hk, hg⟩))) hr
    refine ⟨hA, ?_⟩
    intro j x hx hd
    cases x with
    | F =>
        have hk3 : j ≤ 3 := by
          by_contra hgt
          rw [gpair, if_pos (by omega)] at hx
          simp at hx
        have h1 : (1 : ℕ) ∈ toFresh j := by
          by_cases h2 : j ≤ 2
          · rw [toFresh_le_two h2]
            exact Finset.mem_singleton_self _
          · rw [show j = 3 from by omega, toFresh_three]
            simp
        exact ⟨1, h1, m, hA hd, by omega⟩
    | Z i =>
        cases hd with
        | @step m' _ y _ h h' =>
            rw [gpair] at hx
            split_ifs at hx with h4 h3
            · simp only [Finset.mem_insert, Finset.mem_singleton,
                Tgt.Z.injEq] at hx
              obtain ⟨g', hg', r, hr, hEq⟩ :=
                (ih m' (by omega)).2 i y h h'
              rcases hx with rfl | rfl
              · refine ⟨g' + 1, ?_, r, hr, by omega⟩
                rw [toFresh_of_ge h4]
                exact Finset.mem_union_left _
                  (Finset.mem_image_of_mem _ hg')
              · refine ⟨g' + 1, ?_, r, hr, by omega⟩
                rw [toFresh_of_ge h4]
                exact Finset.mem_union_right _
                  (Finset.mem_image_of_mem _ hg')
            · subst h3
              simp only [Finset.mem_insert, Finset.mem_singleton,
                Tgt.Z.injEq] at hx
              rcases hx with rfl | hx
              · obtain ⟨g', hg', r, hr, hEq⟩ :=
                  (ih m' (by omega)).2 2 y h h'
                rw [toFresh_le_two (by omega)] at hg'
                have hg1 := Finset.mem_singleton.mp hg'
                refine ⟨2, ?_, r, hr, by omega⟩
                rw [toFresh_three]
                simp
              · exact absurd hx (by simp)
            · rw [Finset.mem_singleton] at hx
              exact absurd hx (by simp)
    | Fk i =>
        rw [gpair] at hx
        split_ifs at hx <;> simp at hx

/-- Fresh-to-fresh descent lengths lie in the semigroup
(`thm:descend-realise`). -/
lemma descend_FF_closure {S : Finset ℕ} {m : ℕ}
    (hd : Descend S m Tgt.F Tgt.F) :
    m ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)) :=
  (descend_split m).1 hd

/-- Every target reaches the fresh state by some descent
(`thm:descend-realise`). -/
lemma exists_descend_F (S : Finset ℕ) (t : Tgt) :
    ∃ s, Descend S s t Tgt.F := by
  cases t with
  | F => exact ⟨0, Descend.refl _⟩
  | Z j =>
      obtain ⟨d, hd⟩ := toFresh_nonempty j
      exact ⟨d, descend_of_mem_toFresh j d hd _ (fun x hx => hx)⟩
  | Fk k =>
      obtain ⟨d, hd⟩ := toFresh_nonempty k
      exact ⟨d, descend_of_mem_toFresh k d hd _ (fun x hx => hx)⟩

/-! ### Anchoring (`def:anchored`) -/

/-- A target is anchored at absolute depth `d` if every
fresh-completion lands at an absolute depth in the semigroup: the
invariant form of `def:anchored`. -/
def TgtAnchored (S : Finset ℕ) (d : ℕ) (t : Tgt) : Prop :=
  ∀ m, Descend S m t Tgt.F
    → d + m ∈ AddSubmonoid.closure ((depthSet S : Set ℕ))

/-- A screen is anchored if its cell and every zero-list member
are. -/
def Anchored (S : Finset ℕ) (d : ℕ) (sc : GScreen) : Prop :=
  TgtAnchored S d sc.cell ∧ ∀ t ∈ sc.zlist, TgtAnchored S d t

/-- Anchoring propagates one grammar step (`thm:anchor-step`). -/
lemma TgtAnchored.step {S : Finset ℕ} {d : ℕ} {t t' : Tgt}
    (h : TgtAnchored S d t) (ht' : t' ∈ tgtSucc S t) :
    TgtAnchored S (d + 1) t' := by
  intro m hm
  have h2 := h (m + 1) (Descend.step ht' hm)
  rwa [show d + (m + 1) = d + 1 + m from by omega] at h2

/-- Anchoring propagates along the screen grammar
(`thm:anchor-step`). -/
lemma Anchored.step {S : Finset ℕ} {d : ℕ} {sc sc' : GScreen}
    (h : Anchored S d sc) (h' : sc' ∈ screenSucc S sc) :
    Anchored S (d + 1) sc' := by
  refine ⟨h.1.step (screenSucc_cell h'), fun t ht => ?_⟩
  rw [screenSucc_zlist h'] at ht
  obtain ⟨u, hu, htu⟩ := Finset.mem_biUnion.mp ht
  exact (h.2 u hu).step htu

/-- An anchored fresh target sits at a semigroup depth
(`thm:anchor-step`). -/
lemma TgtAnchored.mem_of_F {S : Finset ℕ} {d : ℕ}
    (h : TgtAnchored S d Tgt.F) :
    d ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)) := by
  have h2 := h 0 (Descend.refl _)
  rwa [Nat.add_zero] at h2

/-- Zero lists along a screen path iterate the successor step
(`thm:coverage`). -/
lemma screenPath_zlist {S : Finset ℕ} (sc : ℕ → GScreen)
    (hpath : ∀ n, sc (n + 1) ∈ screenSucc S (sc n)) :
    ∀ n, (sc n).zlist = (zsucc S)^[n] ((sc 0).zlist) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ihn =>
      rw [Function.iterate_succ_apply', ← ihn]
      exact screenSucc_zlist (hpath n)

/-! ### The acyclicity theorem -/

/-- **Acyclicity of the anchored screen graph** (`thm:nilpotence`):
there is no infinite screen path of anchored screens, with nonempty
seed zero list, all whose screens are live (zero list avoiding the
cell).  The alignment is the Frobenius step: both the source fresh
depth and the target fresh-entry depth are anchored in the semigroup,
so their difference is a large multiple of `gcd 𝒟_ν`. -/
theorem no_anchored_live_path {S : Finset ℕ} {d₀ : ℕ}
    (sc : ℕ → GScreen)
    (hpath : ∀ n, sc (n + 1) ∈ screenSucc S (sc n))
    (hanch : Anchored S d₀ (sc 0))
    (hne : (sc 0).zlist.Nonempty)
    (hlive : ∀ n, (sc n).cell ∉ (sc n).zlist) : False := by
  have hanchn : ∀ n, Anchored S (d₀ + n) (sc n) := by
    intro n
    induction n with
    | zero => exact hanch
    | succ n ihn => exact ihn.step (hpath n)
  have hzl := screenPath_zlist sc hpath
  have hcpath : ∀ n, (sc (n + 1)).cell ∈ tgtSucc S ((sc n).cell) :=
    fun n => screenSucc_cell (hpath n)
  -- the target side: enter the fresh state at an anchored depth `s`
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨s, hs⟩ := exists_descend_F S t₀
  have hFs : Tgt.F ∈ (zsucc S)^[s] ((sc 0).zlist) :=
    mem_zsucc_iter_of_descend ht₀ hs
  have hds : d₀ + s ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)) :=
    (hanchn 0).2 t₀ ht₀ s hs
  -- the Frobenius bound
  obtain ⟨R, hR⟩ := depths_semigroup S
  -- the source side: a fresh cell beyond `s + R`
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
  -- the fresh cell depth is anchored
  have hdn : d₀ + (s + R + m)
      ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)) := by
    have h1 := (hanchn (s + R + m)).1
    rw [hFcell] at h1
    exact h1.mem_of_F
  -- alignment: the gap is a large multiple of the gcd
  have hgs : (depthSet S).gcd id ∣ d₀ + s := by
    have h1 := Nat.setGcd_dvd_of_mem_closure hds
    rwa [setGcd_coe_finset] at h1
  have hgn : (depthSet S).gcd id ∣ d₀ + (s + R + m) := by
    have h1 := Nat.setGcd_dvd_of_mem_closure hdn
    rwa [setGcd_coe_finset] at h1
  have hgap : (depthSet S).gcd id ∣ R + m := by
    have h1 := Nat.dvd_sub hgn hgs
    rwa [show d₀ + (s + R + m) - (d₀ + s) = R + m from by omega] at h1
  have hclgap : R + m ∈ AddSubmonoid.closure ((depthSet S : Set ℕ)) :=
    hR (R + m) (by omega) hgap
  -- coverage: the fresh state is in the zero list at the fresh cell
  have hFn : Tgt.F ∈ (sc (s + R + m)).zlist := by
    rw [hzl (s + R + m),
      show s + R + m = R + m + s from by omega,
      Function.iterate_add_apply]
    exact mem_zsucc_iter_of_descend hFs (descend_closure hclgap)
  exact hlive (s + R + m) (by rw [hFcell]; exact hFn)

/-- **No anchored live cycle** (`thm:nilpotence`, periodic form): a
cycle of anchored live screens with nonempty zero list is
impossible. -/
theorem no_anchored_live_cycle {S : Finset ℕ} {d₀ p : ℕ} (hp : 0 < p)
    (sc : ℕ → GScreen)
    (hpath : ∀ n, sc (n + 1) ∈ screenSucc S (sc n))
    (hper : ∀ n, sc (n + p) = sc n)
    (hanch : Anchored S d₀ (sc 0))
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
  refine no_anchored_live_path sc hpath hanch hne (fun n => ?_)
  rw [hmod n]
  exact hlive (n % p) (Nat.mod_lt n hp)

end GraphMarkovMatching
