/-
Anchoring and the acyclicity of the common block
(`arbitrary_offspring_matching.tex`, `sec:composite`,
`def:composite-anchored`, `thm:composite-anchor`,
`thm:composite-acyclic`).

* `Anchored S E δ t`: every descent from `t` to the fresh letter lands at
  an absolute depth in `Σ_S` (`def:composite-anchored`);
* `Anchored.step`: anchoring propagates one level down
  (`thm:composite-anchor`);
* `Screen`, `CommonStep`, `ScreenAnchored`: the cell/zero-list part of a
  formal screen, the common full-successor step (the cell advances by a
  common letter, the zero list by the entire target successor set), and
  screen anchoring;
* `no_live_common_cycle` (`thm:composite-acyclic`, combinatorial core):
  no periodic path of common full-successor steps, anchored at its origin
  and with nonempty zero lists, avoids the fresh diagonal: some screen on
  the cycle has fresh cell and the fresh letter in its zero list.  Such a
  screen is exactly zero by the support pruning
  (`thm:exact-pruning`), so no cycle of common edges passes through live
  screens.

The proof is the semigroup alignment of the tex: the cell visits the
fresh letter infinitely often; anchoring places all its visit depths and
one zero-list completion depth in `Σ_S`; the Frobenius threshold of
`depths_semigroup` aligns the two along the cycle.

The entrance-inclusive strengthening lives at the end of the file:
`CommonStepE` lets the cell advance through an exceptional entrance of
the target side, and `Anchored.stepE` and `ScreenAnchored.stepE`
propagate anchoring along such steps through the chart returns
`chartPorts_cases`.  `CommonStepES` is the two-set variant matching the
composite ledger exactly: the cell enters through the source side's
declared pairs while the zero list advances with the target side's;
`no_live_step_cycleS` is its cycle refutation, by the same alignment,
under the standing membership of the declared pairs of the source side
in the common support.
-/
import GraphMarkovMatching.Composite.Grammar

namespace GraphMarkovMatching
namespace Composite

/-- A letter is anchored at depth `δ` when every descent to the fresh
letter lands in the return-depth monoid (`def:composite-anchored`). -/
def Anchored (S : Finset ℕ) (E : Finset (ℕ × ℕ)) (δ : ℕ) (t : Letter) : Prop :=
  ∀ m, Descend S E t m .F → δ + m ∈ SigmaS S

/-- The depth of an anchored fresh letter lies in the monoid. -/
lemma Anchored.depth_mem {S : Finset ℕ} {E : Finset (ℕ × ℕ)} {δ : ℕ}
    (h : Anchored S E δ .F) : δ ∈ SigmaS S := by
  simpa using h 0 (.refl _)

/-- Conversely a fresh letter is anchored at every monoid depth. -/
lemma anchored_F_of_mem {S : Finset ℕ} {E : Finset (ℕ × ℕ)} {δ : ℕ}
    (hE : ∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S) (hδ : δ ∈ SigmaS S) :
    Anchored S E δ .F := fun _ hm =>
  add_mem hδ ((descend_F_iff_mem_sigmaS hE).mp hm)

/-- Anchoring propagates along successors (`thm:composite-anchor`). -/
lemma Anchored.step {S : Finset ℕ} {E : Finset (ℕ × ℕ)} {δ : ℕ}
    {t t' : Letter} (h : Anchored S E δ t) (h' : t' ∈ succ S E t) :
    Anchored S E (δ + 1) t' := by
  intro m hm
  have hmem := h (m + 1) (.step h' hm)
  rw [show δ + 1 + m = δ + (m + 1) by omega]
  exact hmem

/-- The cell/zero-list part of a formal screen.  The normalization
coordinate of the full ledger rides along without affecting the cycle
argument: a cycle of full screens projects to a cycle of these pairs. -/
structure Screen where
  cell : Letter
  zlist : Finset Letter
deriving DecidableEq

/-- A common full-successor step: the cell advances by a common letter
(no exceptional entrance), the zero list advances to the entire successor
set on the target side. -/
structure CommonStep (S : Finset ℕ) (Etgt : Finset (ℕ × ℕ))
    (s s' : Screen) : Prop where
  cell_mem : s'.cell ∈ succ S ∅ s.cell
  zlist_eq : s'.zlist = s.zlist.biUnion (succ S Etgt)

/-- A screen is anchored at depth `δ` when its cell is anchored on the
source side and every zero-list member on the target side. -/
structure ScreenAnchored (S : Finset ℕ) (Esrc Etgt : Finset (ℕ × ℕ))
    (δ : ℕ) (s : Screen) : Prop where
  cell : Anchored S Esrc δ s.cell
  zlist : ∀ t ∈ s.zlist, Anchored S Etgt δ t

/-- Screen anchoring propagates along common steps. -/
lemma ScreenAnchored.step {S : Finset ℕ} {Esrc Etgt : Finset (ℕ × ℕ)}
    {δ : ℕ} {s s' : Screen} (h : ScreenAnchored S Esrc Etgt δ s)
    (hstep : CommonStep S Etgt s s') :
    ScreenAnchored S Esrc Etgt (δ + 1) s' := by
  constructor
  · exact h.cell.step (succ_empty_subset S Esrc _ hstep.cell_mem)
  · intro t' ht'
    rw [hstep.zlist_eq] at ht'
    obtain ⟨t, ht, hmem⟩ := Finset.mem_biUnion.mp ht'
    exact (h.zlist t ht).step hmem

/-- A target-side descent moves zero-list membership along the path. -/
lemma mem_zlist_of_descend {S : Finset ℕ} {Etgt : Finset (ℕ × ℕ)}
    {path : ℕ → Screen}
    (hstep : ∀ j, CommonStep S Etgt (path j) (path (j + 1)))
    {t u : Letter} {m : ℕ} (hd : Descend S Etgt t m u) :
    ∀ j, t ∈ (path j).zlist → u ∈ (path (j + m)).zlist := by
  induction hd with
  | refl t =>
      intro j hj
      simpa using hj
  | @step t₁ t₂ t₃ m₁ hmem hd ih =>
      intro j hj
      have h1 : t₂ ∈ (path (j + 1)).zlist := by
        rw [(hstep j).zlist_eq]
        exact Finset.mem_biUnion.mpr ⟨t₁, hj, hmem⟩
      have h2 := ih (j + 1) h1
      rw [show j + (m₁ + 1) = j + 1 + m₁ by omega]
      exact h2

/-- Along a path of common steps the cell reaches the fresh letter. -/
lemma exists_cell_F {S : Finset ℕ} {Etgt : Finset (ℕ × ℕ)}
    {path : ℕ → Screen}
    (hstep : ∀ j, CommonStep S Etgt (path j) (path (j + 1))) (j : ℕ) :
    ∃ i, (path (j + i)).cell = .F := by
  suffices h : ∀ M j, meas (path j).cell ≤ M →
      ∃ i, (path (j + i)).cell = .F from h (meas (path j).cell) j le_rfl
  intro M
  induction M with
  | zero =>
      intro j hM
      by_cases hF : (path j).cell = .F
      · exact ⟨0, by simpa using hF⟩
      · by_cases hF' : (path (j + 1)).cell = .F
        · exact ⟨1, hF'⟩
        · exact absurd
            (lt_of_lt_of_le (meas_lt_of_mem_succ hF hF' (hstep j).cell_mem) hM)
            (Nat.not_lt_zero _)
  | succ M ih =>
      intro j hM
      by_cases hF : (path j).cell = .F
      · exact ⟨0, by simpa using hF⟩
      · by_cases hF' : (path (j + 1)).cell = .F
        · exact ⟨1, hF'⟩
        · have hlt := meas_lt_of_mem_succ hF hF' (hstep j).cell_mem
          obtain ⟨i, hi⟩ := ih (j + 1) (by omega)
          exact ⟨i + 1, by rw [show j + (i + 1) = j + 1 + i by omega]; exact hi⟩

/-- Elements of the return-depth monoid are multiples of the gcd of the
return depths. -/
lemma gcd_dvd_of_mem_sigmaS {S : Finset ℕ} {m : ℕ} (hm : m ∈ SigmaS S) :
    (depthSet S).gcd id ∣ m := by
  refine AddSubmonoid.closure_induction (fun d hd => ?_) (dvd_zero _)
    (fun x y _ _ hx hy => dvd_add hx hy) hm
  exact Finset.gcd_dvd (Finset.mem_coe.mp hd)

/-- **Acyclicity of the common block** (`thm:composite-acyclic`,
combinatorial core).  A periodic path of common full-successor steps,
anchored at its origin and with a nonempty zero list, must contain a
screen whose cell is the fresh letter and whose zero list contains the
fresh letter.  Since such a screen is exactly zero by the support
pruning `thm:exact-pruning` and hence not live, no cycle of common edges
passes through live screens. -/
theorem no_live_common_cycle
    (S : Finset ℕ) (hSne : S.Nonempty) (Esrc Etgt : Finset (ℕ × ℕ))
    (path : ℕ → Screen) (n : ℕ) (hn : 1 ≤ n)
    (hstep : ∀ j, CommonStep S Etgt (path j) (path (j + 1)))
    (hper : ∀ j, path (j + n) = path j)
    (δ0 : ℕ) (hanch0 : ScreenAnchored S Esrc Etgt δ0 (path 0))
    (hne : ((path 0).zlist).Nonempty)
    (hdiag : ∀ j, ¬((path j).cell = .F ∧ .F ∈ (path j).zlist)) :
    False := by
  -- anchoring propagates along the whole path
  have hanch : ∀ j, ScreenAnchored S Esrc Etgt (δ0 + j) (path j) := by
    intro j
    induction j with
    | zero => simpa using hanch0
    | succ j ih => exact ih.step (hstep j)
  -- zero lists stay nonempty
  have hzne : ∀ j, ((path j).zlist).Nonempty := by
    intro j
    induction j with
    | zero => exact hne
    | succ j ih =>
        obtain ⟨t, ht⟩ := ih
        obtain ⟨t', ht'⟩ := succ_nonempty hSne Etgt t
        rw [(hstep j).zlist_eq]
        exact ⟨t', Finset.mem_biUnion.mpr ⟨t, ht, ht'⟩⟩
  -- a position with fresh cell
  obtain ⟨i0, hi0⟩ := exists_cell_F hstep 0
  have hcell : (path i0).cell = .F := by simpa using hi0
  -- periodicity along multiples of the cycle length
  have hperiodic : ∀ q, path (i0 + q * n) = path i0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have harith : i0 + (q + 1) * n = i0 + q * n + n := by ring
        rw [harith, hper, ih]
  -- the depths of the fresh-cell occurrences lie in the monoid
  have hdepth : ∀ q, δ0 + (i0 + q * n) ∈ SigmaS S := by
    intro q
    have h1 := (hanch (i0 + q * n)).cell
    rw [hperiodic q, hcell] at h1
    exact h1.depth_mem
  -- a zero-list member and one completion
  obtain ⟨t, ht⟩ := hzne i0
  obtain ⟨m, hm⟩ := exists_descend_F (S := S) (E := Etgt) t
  have hdm : δ0 + i0 + m ∈ SigmaS S := (hanch i0).zlist t ht m hm
  -- the fresh letter enters the zero list and persists at monoid times
  have hFz : Letter.F ∈ (path (i0 + m)).zlist :=
    mem_zlist_of_descend hstep hm i0 ht
  have hFz' : ∀ m', m' ∈ SigmaS S →
      Letter.F ∈ (path (i0 + m + m')).zlist := fun m' hm' =>
    mem_zlist_of_descend hstep (descend_F_of_mem_sigmaS hm') (i0 + m) hFz
  -- Frobenius alignment
  obtain ⟨R, hR⟩ := depths_semigroup S
  have hqn : m + R ≤ (m + R) * n := by
    calc m + R = (m + R) * 1 := (mul_one _).symm
    _ ≤ (m + R) * n := Nat.mul_le_mul_left _ hn
  have hd1 : (depthSet S).gcd id ∣ δ0 + (i0 + (m + R) * n) :=
    gcd_dvd_of_mem_sigmaS (hdepth (m + R))
  have hd2 : (depthSet S).gcd id ∣ δ0 + i0 + m := gcd_dvd_of_mem_sigmaS hdm
  have hdvd : (depthSet S).gcd id ∣ (m + R) * n - m := by
    have hsub := Nat.dvd_sub hd1 hd2
    rwa [show δ0 + (i0 + (m + R) * n) - (δ0 + i0 + m) = (m + R) * n - m
      by omega] at hsub
  have hmem : (m + R) * n - m ∈ SigmaS S := hR _ (by omega) hdvd
  have hfinal : Letter.F ∈ (path (i0 + (m + R) * n)).zlist := by
    have hstepF := hFz' ((m + R) * n - m) hmem
    rwa [show i0 + m + ((m + R) * n - m) = i0 + (m + R) * n by omega] at hstepF
  rw [hperiodic (m + R)] at hfinal
  exact hdiag i0 ⟨hcell, hfinal⟩

/-! ### Entrance-inclusive steps

The entrance-inclusive strengthening of the acyclicity theorem: the cell
may advance through an exceptional entrance of the target side.  Every
ingredient of the cycle refutation is generic in the entrance set; the
one new obligation is the anchoring of an entrance target, discharged by
the chart returns `chartPorts_cases` under the standing membership of
the declared pairs in the common support. -/

/-- Anchoring propagates along entrance-inclusive successors: a common
successor is handled by `Anchored.step`, and an exceptional entrance
target is anchored through the chart returns `chartPorts_cases`, using
the membership of the declared pairs of both sides in the common
support. -/
lemma Anchored.stepE {S : Finset ℕ} {Esrc Etgt : Finset (ℕ × ℕ)} {δ : ℕ}
    {t t' : Letter} (hEsrc : ∀ p ∈ Esrc, p.1 ∈ S ∧ p.2 ∈ S)
    (hEtgt : ∀ p ∈ Etgt, p.1 ∈ S ∧ p.2 ∈ S)
    (h : Anchored S Esrc δ t) (h' : t' ∈ succ S Etgt t) :
    Anchored S Esrc (δ + 1) t' := by
  cases t with
  | F =>
      rcases Finset.mem_union.mp h' with hcom | hexc
      · exact h.step (Finset.mem_union_left _ hcom)
      · obtain ⟨p, hp, ht'⟩ := Finset.mem_biUnion.mp hexc
        intro m hm
        obtain ⟨e, he, s, hs, rfl⟩ := exists_ports_decomp hEsrc hm rfl
        have hport : e + 1 ∈ chartPorts p.2 (val p.1 0) :=
          add_one_mem_chartPorts_of_mem_succM ht' he
        rw [val_zero] at hport
        have hmem : e + 1 ∈ SigmaS S := by
          rcases chartPorts_cases p.2 p.1 (e + 1) hport with
            h1 | ⟨d, hd, f, hf, heq⟩
          · exact mem_sigmaS_of_mem_depthSet
              (Finset.mem_biUnion.mpr ⟨p.1, (hEtgt p hp).1, h1⟩)
          · rw [heq]
            exact add_mem
              (mem_sigmaS_of_mem_depthSet
                (Finset.mem_biUnion.mpr ⟨p.1, (hEtgt p hp).1, hd⟩))
              (mem_sigmaS_of_mem_depthSet
                (Finset.mem_biUnion.mpr ⟨p.2, (hEtgt p hp).2, hf⟩))
        rw [show δ + 1 + (e + s) = δ + (e + 1) + s by omega]
        exact add_mem (add_mem h.depth_mem hmem) hs
  | Z j => exact h.step h'
  | Fk k => exact h.step h'
  | M a b i => exact h.step h'

/-- An entrance-inclusive full-successor step: the cell advances by any
successor of the target side, exceptional entrances included, and the
zero list advances to the entire successor set on the target side. -/
structure CommonStepE (S : Finset ℕ) (Etgt : Finset (ℕ × ℕ))
    (s s' : Screen) : Prop where
  cell_mem : s'.cell ∈ succ S Etgt s.cell
  zlist_eq : s'.zlist = s.zlist.biUnion (succ S Etgt)

/-- Screen anchoring propagates along entrance-inclusive steps, under
the membership of the declared pairs of both sides in the common
support. -/
lemma ScreenAnchored.stepE {S : Finset ℕ} {Esrc Etgt : Finset (ℕ × ℕ)}
    {δ : ℕ} {s s' : Screen} (hEsrc : ∀ p ∈ Esrc, p.1 ∈ S ∧ p.2 ∈ S)
    (hEtgt : ∀ p ∈ Etgt, p.1 ∈ S ∧ p.2 ∈ S)
    (h : ScreenAnchored S Esrc Etgt δ s)
    (hstep : CommonStepE S Etgt s s') :
    ScreenAnchored S Esrc Etgt (δ + 1) s' := by
  constructor
  · exact h.cell.stepE hEsrc hEtgt hstep.cell_mem
  · intro t' ht'
    rw [hstep.zlist_eq] at ht'
    obtain ⟨t, ht, hmem⟩ := Finset.mem_biUnion.mp ht'
    exact (h.zlist t ht).step hmem

/-! ### Entrance-inclusive steps with source-side cell entrances

The rare edges of the composite screen ledger advance the cell through
an exceptional entrance declared on the source side, while the zero
list advances by the full successor set of the target side.  The step
relation of this section records exactly that shape; the cycle
refutation runs the semigroup alignment with the cell propagation
`Anchored.stepE` instantiated at the source-side entrance set. -/

/-- An entrance-inclusive full-successor step with source-side cell
entrances: the cell advances by any successor of the source side,
exceptional entrances included, and the zero list advances to the
entire successor set on the target side. -/
structure CommonStepES (S : Finset ℕ) (Esrc Etgt : Finset (ℕ × ℕ))
    (s s' : Screen) : Prop where
  cell_mem : s'.cell ∈ succ S Esrc s.cell
  zlist_eq : s'.zlist = s.zlist.biUnion (succ S Etgt)

/-- A common step is in particular a source-entrance step. -/
lemma CommonStep.toES {S : Finset ℕ} {Esrc Etgt : Finset (ℕ × ℕ)}
    {s s' : Screen} (h : CommonStep S Etgt s s') :
    CommonStepES S Esrc Etgt s s' :=
  ⟨succ_empty_subset S Esrc _ h.cell_mem, h.zlist_eq⟩

/-- Screen anchoring propagates along source-entrance steps, under the
membership of the declared pairs of the source side in the common
support: the cell is anchored on the source side and steps through the
source side's entrances, so `Anchored.stepE` applies with both entrance
sets instantiated at the source side. -/
lemma ScreenAnchored.stepES {S : Finset ℕ} {Esrc Etgt : Finset (ℕ × ℕ)}
    {δ : ℕ} {s s' : Screen} (hEsrc : ∀ p ∈ Esrc, p.1 ∈ S ∧ p.2 ∈ S)
    (h : ScreenAnchored S Esrc Etgt δ s)
    (hstep : CommonStepES S Esrc Etgt s s') :
    ScreenAnchored S Esrc Etgt (δ + 1) s' := by
  constructor
  · exact h.cell.stepE hEsrc hEsrc hstep.cell_mem
  · intro t' ht'
    rw [hstep.zlist_eq] at ht'
    obtain ⟨t, ht, hmem⟩ := Finset.mem_biUnion.mp ht'
    exact (h.zlist t ht).step hmem

/-- A target-side descent moves zero-list membership along a path of
source-entrance steps. -/
lemma mem_zlist_of_descendES {S : Finset ℕ} {Esrc Etgt : Finset (ℕ × ℕ)}
    {path : ℕ → Screen}
    (hstep : ∀ j, CommonStepES S Esrc Etgt (path j) (path (j + 1)))
    {t u : Letter} {m : ℕ} (hd : Descend S Etgt t m u) :
    ∀ j, t ∈ (path j).zlist → u ∈ (path (j + m)).zlist := by
  induction hd with
  | refl t =>
      intro j hj
      simpa using hj
  | @step t₁ t₂ t₃ m₁ hmem hd ih =>
      intro j hj
      have h1 : t₂ ∈ (path (j + 1)).zlist := by
        rw [(hstep j).zlist_eq]
        exact Finset.mem_biUnion.mpr ⟨t₁, hj, hmem⟩
      have h2 := ih (j + 1) h1
      rw [show j + (m₁ + 1) = j + 1 + m₁ by omega]
      exact h2

/-- Along a path of source-entrance steps the cell reaches the fresh
letter: the forced-depth measure decreases under an arbitrary entrance
set. -/
lemma exists_cell_FES {S : Finset ℕ} {Esrc Etgt : Finset (ℕ × ℕ)}
    {path : ℕ → Screen}
    (hstep : ∀ j, CommonStepES S Esrc Etgt (path j) (path (j + 1)))
    (j : ℕ) :
    ∃ i, (path (j + i)).cell = .F := by
  suffices h : ∀ M j, meas (path j).cell ≤ M →
      ∃ i, (path (j + i)).cell = .F from h (meas (path j).cell) j le_rfl
  intro M
  induction M with
  | zero =>
      intro j hM
      by_cases hF : (path j).cell = .F
      · exact ⟨0, by simpa using hF⟩
      · by_cases hF' : (path (j + 1)).cell = .F
        · exact ⟨1, hF'⟩
        · exact absurd
            (lt_of_lt_of_le (meas_lt_of_mem_succ hF hF' (hstep j).cell_mem) hM)
            (Nat.not_lt_zero _)
  | succ M ih =>
      intro j hM
      by_cases hF : (path j).cell = .F
      · exact ⟨0, by simpa using hF⟩
      · by_cases hF' : (path (j + 1)).cell = .F
        · exact ⟨1, hF'⟩
        · have hlt := meas_lt_of_mem_succ hF hF' (hstep j).cell_mem
          obtain ⟨i, hi⟩ := ih (j + 1) (by omega)
          exact ⟨i + 1, by rw [show j + (i + 1) = j + 1 + i by omega]; exact hi⟩

/-- **Acyclicity, source-entrance form** (`thm:composite-acyclic`,
combinatorial core).  A periodic path of source-entrance full-successor
steps, anchored at its origin and with a nonempty zero list, must
contain a screen whose cell is the fresh letter and whose zero list
contains the fresh letter, provided every declared pair of the source
side lies in the common support. -/
theorem no_live_step_cycleS
    (S : Finset ℕ) (hSne : S.Nonempty) (Esrc Etgt : Finset (ℕ × ℕ))
    (hEsrc : ∀ p ∈ Esrc, p.1 ∈ S ∧ p.2 ∈ S)
    (path : ℕ → Screen) (n : ℕ) (hn : 1 ≤ n)
    (hstep : ∀ j, CommonStepES S Esrc Etgt (path j) (path (j + 1)))
    (hper : ∀ j, path (j + n) = path j)
    (δ0 : ℕ) (hanch0 : ScreenAnchored S Esrc Etgt δ0 (path 0))
    (hne : ((path 0).zlist).Nonempty)
    (hdiag : ∀ j, ¬((path j).cell = .F ∧ .F ∈ (path j).zlist)) :
    False := by
  -- anchoring propagates along the whole path
  have hanch : ∀ j, ScreenAnchored S Esrc Etgt (δ0 + j) (path j) := by
    intro j
    induction j with
    | zero => simpa using hanch0
    | succ j ih => exact ih.stepES hEsrc (hstep j)
  -- zero lists stay nonempty
  have hzne : ∀ j, ((path j).zlist).Nonempty := by
    intro j
    induction j with
    | zero => exact hne
    | succ j ih =>
        obtain ⟨t, ht⟩ := ih
        obtain ⟨t', ht'⟩ := succ_nonempty hSne Etgt t
        rw [(hstep j).zlist_eq]
        exact ⟨t', Finset.mem_biUnion.mpr ⟨t, ht, ht'⟩⟩
  -- a position with fresh cell
  obtain ⟨i0, hi0⟩ := exists_cell_FES hstep 0
  have hcell : (path i0).cell = .F := by simpa using hi0
  -- periodicity along multiples of the cycle length
  have hperiodic : ∀ q, path (i0 + q * n) = path i0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have harith : i0 + (q + 1) * n = i0 + q * n + n := by ring
        rw [harith, hper, ih]
  -- the depths of the fresh-cell occurrences lie in the monoid
  have hdepth : ∀ q, δ0 + (i0 + q * n) ∈ SigmaS S := by
    intro q
    have h1 := (hanch (i0 + q * n)).cell
    rw [hperiodic q, hcell] at h1
    exact h1.depth_mem
  -- a zero-list member and one completion
  obtain ⟨t, ht⟩ := hzne i0
  obtain ⟨m, hm⟩ := exists_descend_F (S := S) (E := Etgt) t
  have hdm : δ0 + i0 + m ∈ SigmaS S := (hanch i0).zlist t ht m hm
  -- the fresh letter enters the zero list and persists at monoid times
  have hFz : Letter.F ∈ (path (i0 + m)).zlist :=
    mem_zlist_of_descendES hstep hm i0 ht
  have hFz' : ∀ m', m' ∈ SigmaS S →
      Letter.F ∈ (path (i0 + m + m')).zlist := fun m' hm' =>
    mem_zlist_of_descendES hstep (descend_F_of_mem_sigmaS hm') (i0 + m) hFz
  -- Frobenius alignment
  obtain ⟨R, hR⟩ := depths_semigroup S
  have hqn : m + R ≤ (m + R) * n := by
    calc m + R = (m + R) * 1 := (mul_one _).symm
    _ ≤ (m + R) * n := Nat.mul_le_mul_left _ hn
  have hd1 : (depthSet S).gcd id ∣ δ0 + (i0 + (m + R) * n) :=
    gcd_dvd_of_mem_sigmaS (hdepth (m + R))
  have hd2 : (depthSet S).gcd id ∣ δ0 + i0 + m := gcd_dvd_of_mem_sigmaS hdm
  have hdvd : (depthSet S).gcd id ∣ (m + R) * n - m := by
    have hsub := Nat.dvd_sub hd1 hd2
    rwa [show δ0 + (i0 + (m + R) * n) - (δ0 + i0 + m) = (m + R) * n - m
      by omega] at hsub
  have hmem : (m + R) * n - m ∈ SigmaS S := hR _ (by omega) hdvd
  have hfinal : Letter.F ∈ (path (i0 + (m + R) * n)).zlist := by
    have hstepF := hFz' ((m + R) * n - m) hmem
    rwa [show i0 + m + ((m + R) * n - m) = i0 + (m + R) * n by omega] at hstepF
  rw [hperiodic (m + R)] at hfinal
  exact hdiag i0 ⟨hcell, hfinal⟩

end Composite
end GraphMarkovMatching
