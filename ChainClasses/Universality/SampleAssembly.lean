import ChainClasses.Universality.AssemblyAut

/-!
`thm:hairy-general`, the deterministic geometry, third part: letterwise translations of
addresses over `ℕ`, the letter map of a vertex of a sample, the addresses of a realisation
at general arity, the skeleton of a sample in the ambient tree, the children of a vertex
of the skeleton assembly, the dictionary between the copies and the sample, the vertices
of the assembly and of the sample, and the sample as the assembly of its shapes over its
reduced skeleton.  `BAssembly` states the deterministic core.
-/

namespace ChainClasses

open BranchingProcess (sample Survives survivors skeletonDegree)

variable {N : ℕ}

/-! ### Letterwise translations of addresses over `ℕ` -/

/-- **The address translation of a field of letter maps**, over `ℕ`: the word `a` is
read letter by letter, the letter `m` at the vertex already reached being sent to
`Λ v m`.  The translation preserves lengths and the prefix order, so it is an isometry as
soon as every `Λ v` is injective. -/
def transN (Λ : List ℕ → ℕ → ℕ) (a : List ℕ) : List ℕ :=
  a.foldl (fun v m ↦ v ++ [Λ v m]) []

section transN

variable {Λ : List ℕ → ℕ → ℕ}

@[simp] lemma transN_nil : transN Λ [] = [] := rfl

/-- The recursion of the translation: one further letter is read at the vertex reached. -/
lemma transN_concat (a : List ℕ) (m : ℕ) :
    transN Λ (a ++ [m]) = transN Λ a ++ [Λ (transN Λ a) m] := by
  simp [transN, List.foldl_append]

@[simp] lemma transN_length (a : List ℕ) : (transN Λ a).length = a.length := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a m ih => simp [transN_concat, ih]

/-- The translation only appends, so it is monotone for the prefix order. -/
lemma transN_prefix {a a' : List ℕ} (h : a <+: a') : transN Λ a <+: transN Λ a' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc, transN_concat]
      exact ih.trans (List.prefix_append _ _)

/-- **The translation is injective** when the letter maps are. -/
lemma transN_injective (hΛ : ∀ v, Function.Injective (Λ v)) : Function.Injective (transN Λ) := by
  intro a
  induction a using List.reverseRecOn with
  | nil =>
      intro a' h
      have hlen := congrArg List.length h
      simp only [transN_nil, transN_length, List.length_nil] at hlen
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton a b ih =>
      intro a' h
      rcases List.eq_nil_or_concat a' with rfl | ⟨a₀, b₀, rfl⟩
      · have hlen := congrArg List.length h
        simp only [transN_length, List.length_append, List.length_singleton,
          List.length_nil] at hlen
        omega
      · rw [List.concat_eq_append] at h ⊢
        rw [transN_concat, transN_concat] at h
        have hlen : (transN Λ a).length = (transN Λ a₀).length := by
          have := congrArg List.length h
          simp only [List.length_append, List.length_singleton, transN_length] at this
          simp only [transN_length]
          omega
        obtain ⟨h1, h2⟩ := List.append_inj h hlen
        have ha : a = a₀ := ih h1
        subst ha
        have hb : Λ (transN Λ a) b = Λ (transN Λ a) b₀ := by simpa using h2
        rw [hΛ _ hb]

/-- A prefix of a translated word is the translation of the prefix. -/
lemma transN_take (a : List ℕ) (k : ℕ) : transN Λ (a.take k) = (transN Λ a).take k := by
  have hpre : transN Λ (a.take k) <+: transN Λ a := transN_prefix (List.take_prefix k a)
  rw [List.prefix_iff_eq_take.mp hpre, transN_length, List.length_take]
  rcases le_total k a.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le (by simp),
      List.take_of_length_le (by simpa using h)]

/-- **The translation reflects the prefix order.** -/
lemma transN_prefix_iff (hΛ : ∀ v, Function.Injective (Λ v)) {a a' : List ℕ} :
    transN Λ a <+: transN Λ a' ↔ a <+: a' := by
  refine ⟨fun h ↦ ?_, transN_prefix⟩
  have heq : transN Λ a = transN Λ (a'.take a.length) := by
    rw [transN_take, List.prefix_iff_eq_take.mp h, transN_length]
  rw [transN_injective hΛ heq]
  exact List.take_prefix _ _

/-- The translation carries wedges to wedges. -/
lemma transN_wedgeN (hΛ : ∀ v, Function.Injective (Λ v)) (a a' : List ℕ) :
    wedgeN (transN Λ a) (transN Λ a') = transN Λ (wedgeN a a') := by
  have hle : transN Λ (wedgeN a a') <+: wedgeN (transN Λ a) (transN Λ a') :=
    prefix_wedgeN (transN_prefix (wedgeN_prefix_left a a'))
      (transN_prefix (wedgeN_prefix_right a a'))
  set z := wedgeN (transN Λ a) (transN Λ a') with hz
  have hza : z <+: transN Λ a := wedgeN_prefix_left _ _
  have hza' : z <+: transN Λ a' := wedgeN_prefix_right _ _
  have hzt : z = transN Λ (a.take z.length) := by
    rw [transN_take, ← List.prefix_iff_eq_take.mp hza]
  have h1 : a.take z.length <+: a := List.take_prefix _ _
  have h2 : a.take z.length <+: a' := by
    rw [← transN_prefix_iff hΛ, ← hzt]
    exact hza'
  have h3 : a.take z.length <+: wedgeN a a' := prefix_wedgeN h1 h2
  have hlen : z.length ≤ (transN Λ (wedgeN a a')).length := by
    have h4 := (transN_prefix (Λ := Λ) h3).length_le
    rw [← hzt] at h4
    exact h4
  exact (hle.eq_of_length (le_antisymm hle.length_le hlen)).symm

/-- **The translation is an isometry** of the address metric. -/
theorem transN_addrDist (hΛ : ∀ v, Function.Injective (Λ v)) (a a' : List ℕ) :
    addrDist (transN Λ a) (transN Λ a') = addrDist a a' := by
  rw [addrDist, addrDist, transN_wedgeN hΛ, transN_length, transN_length, transN_length]

end transN

/-! ### The letter map of a vertex of a sample -/

open BranchingProcess (childSet bushAt dyingAt)

/-- The dying children of the root of a field: the children that are not survivors. -/
noncomputable def dyingSet (d : GWord N → ℕ) : Finset (Fin N) := childSet N (d []) \ survivors d

/-- The letter of the `j`-th surviving child of the root, in letter order; past the
skeleton degree a junk letter outside the alphabet. -/
noncomputable def survLetter (d : GWord N → ℕ) (j : ℕ) : ℕ :=
  if h : j < (survivors d).card then (((survivors d).orderEmbOfFin rfl ⟨j, h⟩ : Fin N) : ℕ)
  else N + j

/-- The letter of the `m`-th dying child of the root, in letter order; past their
number a junk letter outside the alphabet. -/
noncomputable def dyingLetter (d : GWord N → ℕ) (m : ℕ) : ℕ :=
  if h : m < (dyingSet d).card then (((dyingSet d).orderEmbOfFin rfl ⟨m, h⟩ : Fin N) : ℕ)
  else N + m

/-- **The letter map of a vertex**: the child indices of the realisation of a shape, the
bushes first and the surviving children after them, sent to the letters of the ambient
tree naming those children. -/
noncomputable def letterMap (d : GWord N → ℕ) (m : ℕ) : ℕ :=
  if m < (dyingSet d).card then dyingLetter d m else survLetter d (m - (dyingSet d).card)

lemma survivors_card_add_dyingSet_card {d : GWord N → ℕ} (hd : d [] ≤ N) :
    (dyingSet d).card + skeletonDegree d = d [] := by
  rw [dyingSet, skeletonDegree, Finset.card_sdiff_of_subset (BranchingProcess.survivors_subset d),
    BranchingProcess.card_childSet hd]
  have := Finset.card_le_card (BranchingProcess.survivors_subset d)
  rw [BranchingProcess.card_childSet hd] at this
  omega

lemma survLetter_of_lt {d : GWord N → ℕ} {j : ℕ} (h : j < (survivors d).card) :
    survLetter d j = (((survivors d).orderEmbOfFin rfl ⟨j, h⟩ : Fin N) : ℕ) := by
  rw [survLetter, dif_pos h]

lemma survLetter_mem {d : GWord N → ℕ} {j : ℕ} (h : j < (survivors d).card) :
    ∃ i ∈ survivors d, survLetter d j = (i : ℕ) :=
  ⟨_, Finset.orderEmbOfFin_mem _ _ _, survLetter_of_lt h⟩

lemma survLetter_lt {d : GWord N → ℕ} {j : ℕ} (h : j < (survivors d).card) :
    survLetter d j < N := by
  rw [survLetter_of_lt h]
  exact Fin.isLt _

lemma survLetter_of_le {d : GWord N → ℕ} {j : ℕ} (h : (survivors d).card ≤ j) :
    survLetter d j = N + j := by
  rw [survLetter, dif_neg (by omega)]

lemma dyingLetter_of_lt {d : GWord N → ℕ} {m : ℕ} (h : m < (dyingSet d).card) :
    dyingLetter d m = (((dyingSet d).orderEmbOfFin rfl ⟨m, h⟩ : Fin N) : ℕ) := by
  rw [dyingLetter, dif_pos h]

lemma dyingLetter_mem {d : GWord N → ℕ} {m : ℕ} (h : m < (dyingSet d).card) :
    ∃ i ∈ dyingSet d, dyingLetter d m = (i : ℕ) :=
  ⟨_, Finset.orderEmbOfFin_mem _ _ _, dyingLetter_of_lt h⟩

lemma mem_dyingSet {d : GWord N → ℕ} {i : Fin N} :
    i ∈ dyingSet d ↔ (i : ℕ) < d [] ∧ i ∉ survivors d := by
  rw [dyingSet, Finset.mem_sdiff, BranchingProcess.mem_childSet]

/-- The letter map sends the child indices below the offspring count onto letters below
it, and nothing else there. -/
lemma letterMap_lt_iff {d : GWord N → ℕ} (hd : d [] ≤ N) (m : ℕ) :
    letterMap d m < d [] ↔ m < d [] := by
  have hsum := survivors_card_add_dyingSet_card hd
  rw [skeletonDegree] at hsum
  rw [letterMap]
  by_cases hm : m < (dyingSet d).card
  · rw [if_pos hm]
    obtain ⟨i, hi, hieq⟩ := dyingLetter_mem hm
    rw [hieq]
    exact iff_of_true (mem_dyingSet.mp hi).1 (by omega)
  · rw [if_neg hm]
    by_cases hj : m - (dyingSet d).card < (survivors d).card
    · obtain ⟨i, hi, hieq⟩ := survLetter_mem hj
      rw [hieq]
      exact iff_of_true (BranchingProcess.mem_survivors.mp hi).1 (by omega)
    · rw [survLetter_of_le (by omega)]
      exact iff_of_false (by omega) (by omega)

/-- The letter map is injective: distinct bushes get distinct letters, distinct surviving
children likewise, a bush and a surviving child never share a letter, and the junk
letters lie outside the alphabet. -/
lemma letterMap_injective (d : GWord N → ℕ) : Function.Injective (letterMap d) := by
  intro m m' h
  simp only [letterMap] at h
  have hdy : ∀ {a b : ℕ} (ha : a < (dyingSet d).card) (hb : b < (dyingSet d).card),
      dyingLetter d a = dyingLetter d b → a = b := by
    intro a b ha hb hab
    rw [dyingLetter_of_lt ha, dyingLetter_of_lt hb] at hab
    have := ((dyingSet d).orderEmbOfFin rfl).injective (Fin.ext hab)
    simpa using this
  have hsv : ∀ {a b : ℕ}, survLetter d a = survLetter d b → a = b := by
    intro a b hab
    by_cases ha : a < (survivors d).card
    · by_cases hb : b < (survivors d).card
      · rw [survLetter_of_lt ha, survLetter_of_lt hb] at hab
        have := ((survivors d).orderEmbOfFin rfl).injective (Fin.ext hab)
        simpa using this
      · rw [survLetter_of_lt ha, survLetter_of_le (by omega)] at hab
        have := Fin.isLt ((survivors d).orderEmbOfFin rfl ⟨a, ha⟩)
        omega
    · by_cases hb : b < (survivors d).card
      · rw [survLetter_of_le (by omega), survLetter_of_lt hb] at hab
        have := Fin.isLt ((survivors d).orderEmbOfFin rfl ⟨b, hb⟩)
        omega
      · rw [survLetter_of_le (by omega), survLetter_of_le (by omega)] at hab
        omega
  have hmix : ∀ {a b : ℕ}, a < (dyingSet d).card → dyingLetter d a ≠ survLetter d b := by
    intro a b ha hab
    obtain ⟨i, hi, hieq⟩ := dyingLetter_mem ha
    by_cases hb : b < (survivors d).card
    · obtain ⟨i', hi', hieq'⟩ := survLetter_mem hb
      rw [hieq, hieq'] at hab
      have : i = i' := Fin.ext hab
      subst this
      exact (mem_dyingSet.mp hi).2 hi'
    · rw [hieq, survLetter_of_le (by omega)] at hab
      have := i.isLt
      omega
  by_cases hm : m < (dyingSet d).card <;> by_cases hm' : m' < (dyingSet d).card
  · rw [if_pos hm, if_pos hm'] at h
    exact hdy hm hm' h
  · rw [if_pos hm, if_neg hm'] at h
    exact absurd h (hmix hm)
  · rw [if_neg hm, if_pos hm'] at h
    exact absurd h.symm (hmix hm')
  · rw [if_neg hm, if_neg hm'] at h
    have := hsv h
    omega

/-- Every element of a finite set of letters is enumerated by its rank. -/
lemma exists_orderEmbOfFin_eq {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) :
    ∃ m, ∃ h : m < S.card, S.orderEmbOfFin rfl ⟨m, h⟩ = i := by
  have hmem : i ∈ Set.range (S.orderEmbOfFin (rfl : S.card = S.card)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi
  obtain ⟨⟨m, hm⟩, hmeq⟩ := hmem
  exact ⟨m, hm, hmeq⟩

/-- The letter map is onto the children: every child letter is the image of a child
index below the offspring count. -/
lemma letterMap_surj {d : GWord N → ℕ} (hd : d [] ≤ N) {j : ℕ} (hj : j < d []) :
    ∃ m, m < d [] ∧ letterMap d m = j := by
  have hsum := survivors_card_add_dyingSet_card hd
  set i : Fin N := ⟨j, by omega⟩ with hi
  by_cases hs : i ∈ survivors d
  · obtain ⟨m, hm, hmeq⟩ := exists_orderEmbOfFin_eq hs
    refine ⟨(dyingSet d).card + m, by rw [skeletonDegree] at hsum; omega, ?_⟩
    rw [letterMap, if_neg (by omega), Nat.add_sub_cancel_left, survLetter_of_lt hm, hmeq]
  · have hdy : i ∈ dyingSet d := mem_dyingSet.mpr ⟨hj, hs⟩
    obtain ⟨m, hm, hmeq⟩ := exists_orderEmbOfFin_eq hdy
    exact ⟨m, by omega, by rw [letterMap, if_pos hm, dyingLetter_of_lt hm, hmeq]⟩

/-- In a dying subtree every child is a dying child and the letter map is the identity
on the children. -/
lemma letterMap_of_not_survives {d : GWord N → ℕ} (hd : d [] ≤ N) (hfin : ¬ Survives d) {m : ℕ}
    (hm : m < d []) : letterMap d m = m := by
  have hemp : survivors d = ∅ := BranchingProcess.not_survives_iff_survivors_eq_empty.mp hfin
  have hdy : dyingSet d = childSet N (d []) := by rw [dyingSet, hemp, Finset.sdiff_empty]
  have hcard : (dyingSet d).card = d [] := by rw [hdy, BranchingProcess.card_childSet hd]
  have hm' : m < (dyingSet d).card := by omega
  rw [letterMap, if_pos hm', dyingLetter_of_lt hm']
  have hf : (fun x : Fin (dyingSet d).card ↦ (⟨(x : ℕ), by omega⟩ : Fin N))
      = (dyingSet d).orderEmbOfFin rfl := by
    refine Finset.orderEmbOfFin_unique rfl (fun x ↦ ?_) (fun x y hxy ↦ ?_)
    · rw [mem_dyingSet, hemp]
      have := x.isLt
      exact ⟨by simp only; omega, Finset.notMem_empty _⟩
    · exact hxy
  have := congrFun hf ⟨m, hm'⟩
  simp only at this
  rw [← this]

/-! ### The addresses of a realisation at general arity -/

open RTree (IsAddr)
open GShape (realiseAux)

/-- The address of the `i`-th neck vertex of the realisation of a bush-list: one letter
per neck vertex passed, naming the child past its bushes. -/
def neckAddr (L : List (List RTree)) (i : ℕ) : List ℕ := (L.take i).map List.length

@[simp] lemma neckAddr_zero (L : List (List RTree)) : neckAddr L 0 = [] := rfl

lemma neckAddr_cons (β : List RTree) (M : List (List RTree)) (i : ℕ) :
    neckAddr (β :: M) (i + 1) = β.length :: neckAddr M i := by
  simp [neckAddr]

lemma neckAddr_length {L : List (List RTree)} {i : ℕ} (hi : i ≤ L.length) :
    (neckAddr L i).length = i := by
  rw [neckAddr, List.length_map, List.length_take, min_eq_left hi]

/-- One further neck vertex extends the neck address by the number of bushes. -/
lemma neckAddr_succ {L : List (List RTree)} {i : ℕ} (hi : i < L.length) :
    neckAddr L (i + 1) = neckAddr L i ++ [L[i].length] := by
  rw [neckAddr, neckAddr, List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]
  rfl

/-- The neck addresses are nested. -/
lemma neckAddr_prefix (L : List (List RTree)) {i j : ℕ} (hij : i ≤ j) :
    neckAddr L i <+: neckAddr L j := by
  rw [neckAddr, neckAddr]
  exact (List.take_prefix_take_left hij).map _

/-- The exit is the last neck address. -/
lemma gExitAddr_eq_neckAddr : ∀ L : List (List RTree), gExitAddr L = neckAddr L (L.length - 1)
  | [] => rfl
  | [_] => rfl
  | β :: r :: rest => by
      rw [gExitAddr_cons₂, gExitAddr_eq_neckAddr (r :: rest), List.length_cons,
        Nat.add_sub_cancel, List.length_cons, Nat.add_sub_cancel, ← neckAddr_cons]
      rfl

/-- **The children of a neck vertex**: its bushes, and the next neck vertex when there
is one. -/
lemma isAddr_realiseAux_neck_concat : ∀ (L : List (List RTree)) (i : ℕ) (hi : i < L.length)
    (m : ℕ), IsAddr (realiseAux L) (neckAddr L i ++ [m])
      ↔ (m < L[i].length ∨ (m = L[i].length ∧ i + 1 < L.length))
  | [], i, hi, _ => by simp at hi
  | [β], 0, _, m => by
      rw [neckAddr_zero, List.nil_append, show realiseAux [β] = .node β from rfl,
        RTree.isAddr_cons]
      simp
  | [β], i + 1, hi, _ => by simp at hi
  | β :: r :: rest, 0, _, m => by
      rw [neckAddr_zero, List.nil_append,
        show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl,
        RTree.isAddr_cons]
      simp only [List.length_append, List.getElem_cons_zero, List.length_cons, List.length_nil]
      constructor
      · rintro ⟨h, -⟩
        omega
      · intro h
        refine ⟨by omega, ?_⟩
        rcases h with h | ⟨h, -⟩
        · rw [List.getElem_append_left h]
          exact RTree.isAddr_nil _
        · subst h
          rw [List.getElem_append_right le_rfl]
          simp
  | β :: r :: rest, i + 1, hi, m => by
      rw [neckAddr_cons, List.cons_append,
        show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl,
        isAddr_append_last_eq, isAddr_realiseAux_neck_concat (r :: rest) i (by simpa using hi)]
      simp

/-- **The bush of a neck vertex**: the addresses below the `m`-th bush index of the `i`-th
neck vertex are the addresses of that bush. -/
lemma isAddr_realiseAux_bush : ∀ (L : List (List RTree)) (i : ℕ) (hi : i < L.length) (m : ℕ)
    (hm : m < L[i].length) (z : List ℕ),
    IsAddr (realiseAux L) (neckAddr L i ++ m :: z) ↔ IsAddr L[i][m] z
  | [], i, hi, _, _, _ => by simp at hi
  | [β], 0, _, m, hm, z => by
      rw [neckAddr_zero, List.nil_append, show realiseAux [β] = .node β from rfl,
        RTree.isAddr_cons]
      simp only [List.getElem_cons_zero] at hm ⊢
      exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hm, h⟩⟩
  | [β], i + 1, hi, _, _, _ => by simp at hi
  | β :: r :: rest, 0, _, m, hm, z => by
      rw [neckAddr_zero, List.nil_append,
        show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl]
      simp only [List.getElem_cons_zero] at hm ⊢
      rw [isAddr_append_last_lt hm, RTree.isAddr_cons]
      exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hm, h⟩⟩
  | β :: r :: rest, i + 1, hi, m, hm, z => by
      rw [neckAddr_cons, List.cons_append,
        show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl,
        isAddr_append_last_eq]
      exact isAddr_realiseAux_bush (r :: rest) i (by simpa using hi) m (by simpa using hm) z

/-- **The addresses of a realisation**: every vertex is a neck vertex or a vertex of a
bush of a neck vertex. -/
lemma isAddr_realiseAux_cases : ∀ (L : List (List RTree)), L ≠ [] → ∀ {p : List ℕ},
    IsAddr (realiseAux L) p →
      (∃ i, i < L.length ∧ p = neckAddr L i) ∨
      (∃ i, ∃ hi : i < L.length, ∃ m, ∃ hm : m < L[i].length, ∃ z,
        IsAddr L[i][m] z ∧ p = neckAddr L i ++ m :: z)
  | [], h, _, _ => absurd rfl h
  | [β], _, p, hp => by
      cases p with
      | nil => exact Or.inl ⟨0, by simp, rfl⟩
      | cons m z =>
          rw [show realiseAux [β] = .node β from rfl, RTree.isAddr_cons] at hp
          obtain ⟨hm, hz⟩ := hp
          exact Or.inr ⟨0, by simp, m, by simpa using hm, z, by simpa using hz, rfl⟩
  | β :: r :: rest, _, p, hp => by
      cases p with
      | nil => exact Or.inl ⟨0, by simp, rfl⟩
      | cons m z =>
          rw [show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl]
            at hp
          by_cases hm : m < β.length
          · rw [isAddr_append_last_lt hm, RTree.isAddr_cons] at hp
            obtain ⟨_, hz⟩ := hp
            exact Or.inr ⟨0, by simp, m, by simpa using hm, z, by simpa using hz, rfl⟩
          · have hlen : m < (β ++ [realiseAux (r :: rest)]).length := by
              rw [RTree.isAddr_cons] at hp
              exact hp.1
            have hmeq : m = β.length := by
              simp only [List.length_append, List.length_singleton] at hlen
              omega
            subst hmeq
            rw [isAddr_append_last_eq] at hp
            rcases isAddr_realiseAux_cases (r :: rest) (by simp) hp with
              ⟨i, hi, rfl⟩ | ⟨i, hi, m', hm', z', hz', rfl⟩
            · exact Or.inl ⟨i + 1, by simpa using hi, (neckAddr_cons _ _ _).symm⟩
            · refine Or.inr ⟨i + 1, by simpa using hi, m', by simpa using hm', z',
                by simpa using hz', ?_⟩
              rw [neckAddr_cons]
              rfl

/-! ### The skeleton of a sample in the ambient tree -/

/-- **The deterministic hypotheses of `thm:hairy-general`** at general arity: the
offspring counts lie within the alphabet, the sample survives, and every neck ray of the
skeleton meets a split, which is the event `Ω₀` of `thm:chains` read for the skeleton. -/
structure IsGHairySample (c : GWord N → ℕ) : Prop where
  /-- The offspring counts lie within the alphabet. -/
  offspring : ∀ v, c v ≤ N
  /-- The sample is infinite. -/
  survives : Survives c
  /-- Every neck ray of the skeleton meets a split. -/
  splits : ∀ v : GWord N, Survives (ambSub c v) →
    ∃ n, 2 ≤ skeletonDegree (neckIter (ambSub c v) n)

/-- The descent, one step at the bottom. -/
lemma neckIter_succ' (d : GWord N → ℕ) : ∀ n, neckIter d (n + 1) = bushAt (neckIter d n) 0 := by
  intro n
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [neckIter_succ, ih, ← neckIter_succ]

/-- The descent of a surviving field stays in the skeleton. -/
lemma survives_neckIter {d : GWord N → ℕ} (hd : Survives d) : ∀ n, Survives (neckIter d n)
  | 0 => hd
  | n + 1 => by
      rw [neckIter_succ']
      exact BranchingProcess.survives_bushAt (Nat.pos_of_ne_zero
        (BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp (survives_neckIter hd n)))

lemma unval_singleton {ℓ : ℕ} (h : ℓ < N) : unval N [ℓ] = [⟨ℓ, h⟩] := by
  simp [unval, h]

lemma ambSub_root (e : GWord N → ℕ) (v : GWord N) : ambSub e v [] = e v := by
  rw [ambSub_apply, List.append_nil]

/-- The `j`-th surviving subtree is the subtree at the letter of the `j`-th surviving
child. -/
lemma bushAt_eq_ambSub {e : GWord N → ℕ} {j : ℕ} (hj : j < skeletonDegree e) :
    bushAt e j = ambSub e (unval N [survLetter e j]) := by
  have hj' : j < (survivors e).card := hj
  rw [BranchingProcess.bushAt_of_lt hj', survLetter_of_lt hj', unval_singleton (Fin.isLt _)]
  rfl

/-- The `m`-th dying subtree is the subtree at the letter of the `m`-th dying child. -/
lemma dyingAt_eq_ambSub {e : GWord N → ℕ} {m : ℕ} (hm : m < (dyingSet e).card) :
    dyingAt e m = ambSub e (unval N [dyingLetter e m]) := by
  rw [dyingLetter_of_lt hm, unval_singleton (Fin.isLt _)]
  show BranchingProcess.bushOf (dyingSet e) m e = _
  rw [BranchingProcess.bushOf, dif_pos hm]
  rfl

/-- A dying subtree does not survive. -/
lemma not_survives_dyingAt {e : GWord N → ℕ} {m : ℕ} (hm : m < (dyingSet e).card) :
    ¬ Survives (dyingAt e m) := by
  rw [dyingAt_eq_ambSub hm]
  obtain ⟨i, hi, hieq⟩ := dyingLetter_mem hm
  rw [hieq, unval_singleton i.isLt]
  intro hs
  exact (mem_dyingSet.mp hi).2 (BranchingProcess.mem_survivors.mpr ⟨(mem_dyingSet.mp hi).1, hs⟩)

/-- **The neck ray of the root in the ambient tree**: the path of the descent, one
surviving child after the other. -/
noncomputable def neckPath (d : GWord N → ℕ) : ℕ → GWord N
  | 0 => []
  | n + 1 => neckPath d n ++ unval N [survLetter (ambSub d (neckPath d n)) 0]

@[simp] lemma neckPath_zero (d : GWord N → ℕ) : neckPath d 0 = [] := rfl

/-- The descent is the field along the neck ray. -/
lemma neckIter_eq_ambSub_neckPath {d : GWord N → ℕ} (hd : Survives d) :
    ∀ n, neckIter d n = ambSub d (neckPath d n)
  | 0 => by simp
  | n + 1 => by
      have ih := neckIter_eq_ambSub_neckPath hd n
      have hs := survives_neckIter hd n
      rw [neckIter_succ', bushAt_eq_ambSub (j := 0) (Nat.pos_of_ne_zero
        (BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp hs)), ih, ambSub_ambSub]
      rfl

lemma skeletonDegree_neckIter_pos {d : GWord N → ℕ} (hd : Survives d) (n : ℕ) :
    0 < skeletonDegree (neckIter d n) :=
  Nat.pos_of_ne_zero
    (BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp (survives_neckIter hd n))

/-- The neck ray read over `ℕ`, one step. -/
lemma vals_neckPath_succ {d : GWord N → ℕ} (hd : Survives d) (n : ℕ) :
    vals (neckPath d (n + 1)) = vals (neckPath d n) ++ [survLetter (neckIter d n) 0] := by
  have hlt : survLetter (neckIter d n) 0 < N := survLetter_lt (skeletonDegree_neckIter_pos hd n)
  rw [neckPath, ← neckIter_eq_ambSub_neckPath hd n, unval_singleton hlt, vals_append]
  rfl

/-- The neck ray of a vertex of the sample stays in the sample. -/
lemma neckPath_mem_sample {c : GWord N → ℕ} {y : GWord N} (hy : y ∈ sample c)
    (hs : Survives (ambSub c y)) : ∀ n, y ++ neckPath (ambSub c y) n ∈ sample c
  | 0 => by simpa using hy
  | n + 1 => by
      have ih := neckPath_mem_sample hy hs n
      have hpos := skeletonDegree_neckIter_pos hs n
      have hlt : survLetter (neckIter (ambSub c y) n) 0 < N := survLetter_lt hpos
      rw [neckPath, ← neckIter_eq_ambSub_neckPath hs n, unval_singleton hlt, ← List.append_assoc,
        BranchingProcess.mem_sample_append_singleton]
      refine ⟨ih, ?_⟩
      obtain ⟨i, hi, hieq⟩ := survLetter_mem (d := neckIter (ambSub c y) n) hpos
      have h1 := (BranchingProcess.mem_survivors.mp hi).1
      rw [neckIter_eq_ambSub_neckPath hs n, ambSub_root, ambSub_apply] at h1
      simp only [hieq]
      exact h1

/-- Below its split, every vertex of a neck ray has one surviving child. -/
lemma skeletonDegree_neckIter_eq_one {d : GWord N → ℕ} (hd : Survives d) {i : ℕ}
    (hi : i < gSplitDepth d) : skeletonDegree (neckIter d i) = 1 := by
  have hnot : ¬ 2 ≤ skeletonDegree (neckIter d i) := fun hmem ↦
    absurd (Nat.sInf_le (show i ∈ {n | 2 ≤ skeletonDegree (neckIter d n)} from hmem))
      (not_le.mpr hi)
  have := skeletonDegree_neckIter_pos hd i
  omega

/-- The split ending the chain of the root, in the ambient tree. -/
noncomputable def splitPath (d : GWord N → ℕ) : GWord N := neckPath d (gSplitDepth d)

/-- **The entry vertex of a copy** (**`thm:shape-iid`** at general arity): the chain of
the root is followed to its split, and each letter of the address picks a surviving child
of the split reached. -/
noncomputable def gEntryV : (GWord N → ℕ) → GWord N → GWord N
  | _, [] => []
  | d, i :: u =>
      (splitPath d ++ unval N [survLetter (gSplitField d) i]) ++ gEntryV (gSplitBush d i) u

@[simp] lemma gEntryV_nil (d : GWord N → ℕ) : gEntryV d [] = [] := rfl

lemma gEntryV_cons (d : GWord N → ℕ) (i : Fin N) (u : GWord N) :
    gEntryV d (i :: u)
      = (splitPath d ++ unval N [survLetter (gSplitField d) i]) ++ gEntryV (gSplitBush d i) u :=
  rfl

/-- The recursion of the entry map at the last letter: the copy `uj` starts at the
`j`-th surviving child of the split ending the chain of `u`. -/
lemma gEntryV_concat (d : GWord N → ℕ) (u : GWord N) (j : Fin N) :
    gEntryV d (u ++ [j])
      = gEntryV d u ++ (splitPath (redSub d u)
          ++ unval N [survLetter (gSplitField (redSub d u)) j]) := by
  induction u generalizing d with
  | nil => simp [gEntryV_cons]
  | cons i u ih =>
      rw [List.cons_append, gEntryV_cons, ih, gEntryV_cons, redSub_cons]
      simp only [List.append_assoc]

/-- The skeleton of the arity field, one letter down. -/
lemma mem_sample_gArityAt_cons {d : GWord N → ℕ} {i : Fin N} {u : GWord N} :
    i :: u ∈ sample (gArityAt d) ↔ (i : ℕ) < gArity d ∧ u ∈ sample (gArityAt (gSplitBush d i)) := by
  rw [mem_sample_cons_ambSub, gArityAt_nil]
  have : ambSub (gArityAt d) [i] = gArityAt (gSplitBush d i) := by
    funext w
    rw [ambSub_apply, List.singleton_append, gArityAt_cons]
  rw [this]

/-- **The copies are the subtrees at the entry vertices**: along the reduced skeleton
the subfield of a copy is the ambient subfield at its entry vertex, and it survives. -/
lemma redSub_eq_ambSub_gEntryV {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∀ (u y : GWord N), Survives (ambSub c y) → u ∈ sample (gArityAt (ambSub c y)) →
      redSub (ambSub c y) u = ambSub c (y ++ gEntryV (ambSub c y) u)
        ∧ Survives (redSub (ambSub c y) u)
  | [], y, hs, _ => by simpa using hs
  | i :: u, y, hs, hu => by
      obtain ⟨hi, hu'⟩ := mem_sample_gArityAt_cons.mp hu
      have hbush : gSplitBush (ambSub c y) i
          = ambSub c (y ++ (splitPath (ambSub c y)
              ++ unval N [survLetter (gSplitField (ambSub c y)) i])) := by
        rw [gSplitBush, bushAt_eq_ambSub hi, gSplitField, neckIter_eq_ambSub_neckPath hs,
          ambSub_ambSub, ambSub_ambSub, splitPath]
      have hsurv' : Survives (gSplitBush (ambSub c y) i) := BranchingProcess.survives_bushAt hi
      rw [hbush] at hsurv' hu'
      obtain ⟨ih1, ih2⟩ := redSub_eq_ambSub_gEntryV hc u _ hsurv' hu'
      rw [ih1] at ih2
      rw [redSub_cons, hbush, gEntryV_cons, hbush, ih1]
      simp only [List.append_assoc, true_and]
      simp only [List.append_assoc] at ih2
      exact ih2

/-- The subfield of a copy, at the root. -/
lemma redSub_eq_ambSub_gEntryV' {c : GWord N → ℕ} (hc : IsGHairySample c) {u : GWord N}
    (hu : u ∈ sample (gArityAt c)) :
    redSub c u = ambSub c (gEntryV c u) ∧ Survives (redSub c u) := by
  have h := redSub_eq_ambSub_gEntryV hc u [] (by simpa using hc.survives) (by simpa using hu)
  simpa using h

/-- The entry vertices lie in the sample. -/
lemma gEntryV_mem_sample {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∀ (u y : GWord N), y ∈ sample c → Survives (ambSub c y) → u ∈ sample (gArityAt (ambSub c y)) →
      y ++ gEntryV (ambSub c y) u ∈ sample c
  | [], y, hy, _, _ => by simpa using hy
  | i :: u, y, hy, hs, hu => by
      obtain ⟨hi, hu'⟩ := mem_sample_gArityAt_cons.mp hu
      have hbush : gSplitBush (ambSub c y) i
          = ambSub c (y ++ (splitPath (ambSub c y)
              ++ unval N [survLetter (gSplitField (ambSub c y)) i])) := by
        rw [gSplitBush, bushAt_eq_ambSub hi, gSplitField, neckIter_eq_ambSub_neckPath hs,
          ambSub_ambSub, ambSub_ambSub, splitPath]
      have hsurv' : Survives (gSplitBush (ambSub c y) i) := BranchingProcess.survives_bushAt hi
      rw [hbush] at hsurv' hu'
      have hmem : y ++ (splitPath (ambSub c y)
          ++ unval N [survLetter (gSplitField (ambSub c y)) i]) ∈ sample c := by
        have hsp := neckPath_mem_sample hy hs (gSplitDepth (ambSub c y))
        have hlt : survLetter (gSplitField (ambSub c y)) i < N := survLetter_lt hi
        rw [← List.append_assoc, unval_singleton hlt,
          BranchingProcess.mem_sample_append_singleton]
        refine ⟨hsp, ?_⟩
        obtain ⟨i', hi', hieq⟩ := survLetter_mem (d := gSplitField (ambSub c y)) hi
        have h1 := (BranchingProcess.mem_survivors.mp hi').1
        rw [gSplitField, neckIter_eq_ambSub_neckPath hs, ambSub_root, ambSub_apply] at h1
        simp only [hieq]
        exact h1
      have ih := gEntryV_mem_sample hc u _ hmem hsurv' hu'
      rw [gEntryV_cons, hbush]
      simp only [List.append_assoc] at ih ⊢
      exact ih

/-! ### The children of a vertex of the skeleton assembly -/

namespace SkelAssembly

variable {k : GWord N → ℕ} {σ : GWord N → GShape}

/-- The address of a vertex of the skeleton assembly in the ambient tree of the assembly. -/
def code (x : SkelAssembly k σ) : List ℕ := GAssembly.code (toG x)

lemma code_eq (x : SkelAssembly k σ) :
    x.code = gCopyAddr (liftN N σ) (vals x.copy) ++ x.vert.1 := rfl

lemma code_injective : Function.Injective (code (k := k) (σ := σ)) :=
  fun _ _ h ↦ toG_injective (GAssembly.code_injective h)

/-- A word over `ℕ` ending in a letter of the alphabet is read from an ambient word. -/
lemma vals_eq_append_singleton_iff {v : GWord N} {w : List ℕ} {m : ℕ} :
    vals v = w ++ [m] ↔ ∃ (v' : GWord N) (j : Fin N), v = v' ++ [j] ∧ vals v' = w ∧ (j : ℕ) = m := by
  constructor
  · intro h
    rcases List.eq_nil_or_concat v with rfl | ⟨v', j, rfl⟩
    · have := congrArg List.length h
      simp at this
    · rw [List.concat_eq_append, vals_append, vals_cons, vals_nil] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by
        have := congrArg List.length h
        simp only [List.length_append, List.length_singleton] at this
        omega)
      exact ⟨v', j, List.concat_eq_append, h1, by simpa using h2⟩
  · rintro ⟨v', j, rfl, rfl, rfl⟩
    simp

/-- **The children of a vertex of the skeleton assembly**: inside a copy they are the
children of the realisation, and the exit of a copy is joined to the entries of the
copies below it, one per letter below the arity. -/
lemma exists_code_concat_iff (x : SkelAssembly k σ) (m : ℕ) :
    (∃ y : SkelAssembly k σ, y.code = x.code ++ [m])
      ↔ ((x.vert.1 = (σ x.copy).exitAddr
            ∧ ∃ j : Fin N, (j : ℕ) < k x.copy ∧ m = (σ x.copy).bouquet.length + j)
          ∨ IsAddr (σ x.copy).realise (x.vert.1 ++ [m])) := by
  obtain ⟨u, hu, p⟩ := x
  dsimp only
  constructor
  · rintro ⟨⟨v, hv, q⟩, hy⟩
    have hd1 : addrDist (GAssembly.code (toG ⟨u, hu, p⟩)) (GAssembly.code (toG ⟨v, hv, q⟩)) = 1 := by
      change addrDist (code ⟨u, hu, p⟩) (code ⟨v, hv, q⟩) = 1
      rw [hy, addrDist_append_right, List.length_singleton]
    have hadj : GAssembly.Adj (toG ⟨u, hu, p⟩) (toG ⟨v, hv, q⟩) := by
      refine (GAssembly.dist_eq_one_iff_adj _ _).mp ?_
      rw [GAssembly.dist_code, hd1]
      norm_num
    have hlen : (code ⟨v, hv, q⟩).length = (code ⟨u, hu, p⟩).length + 1 := by
      rw [hy]; simp
    simp only [code_eq, List.length_append] at hlen
    rcases hadj with ⟨hcopy, hor⟩ | ⟨j', hj', hglue, hnil⟩ | ⟨j', hj', hglue, hnil⟩
    · simp only [toG_copy] at hcopy
      have huv : u = v := vals_injective hcopy
      subst huv
      rcases hor with ⟨b, hb⟩ | ⟨b, hb⟩
      · simp only [toG_vert_val] at hb
        have hcode : code ⟨u, hu, q⟩ = code ⟨u, hu, p⟩ ++ [b] := by
          simp only [code_eq, hb, List.append_assoc]
        rw [hcode] at hy
        have hbm : b = m := by simpa using List.append_cancel_left hy
        subst hbm
        exact Or.inr (hb ▸ RTree.mem_addrList_iff.mp q.2)
      · exfalso
        simp only [toG_vert_val] at hb
        rw [hb] at hlen
        simp only [List.length_append, List.length_singleton] at hlen
        omega
    · simp only [toG_copy, toG_vert_val] at hj' hglue hnil
      obtain ⟨v', j, rfl, hv', hjm⟩ := vals_eq_append_singleton_iff.mp hj'
      have huv : u = v' := vals_injective hv'.symm
      subst huv
      have hj : (j : ℕ) < k u := (BranchingProcess.mem_sample_append_singleton.mp hv).2
      refine Or.inl ⟨by rw [hglue, liftN_vals], j, hj, ?_⟩
      simp only [code_eq, hnil, List.append_nil, vals_append, vals_cons, vals_nil,
        gCopyAddr_concat, liftN_vals, hglue, List.append_assoc] at hy
      have := List.append_cancel_left hy
      simpa using this.symm
    · exfalso
      simp only [toG_copy, toG_vert_val] at hj' hglue hnil
      obtain ⟨u', j, rfl, hu', hjm⟩ := vals_eq_append_singleton_iff.mp hj'
      have huv : v = u' := vals_injective hu'.symm
      subst huv
      simp only [vals_append, vals_cons, vals_nil, gCopyAddr_concat, List.length_append,
        hglue, hnil, List.length_singleton, List.length_nil] at hlen
      omega
  · rintro (⟨hexit, j, hj, rfl⟩ | hchild)
    · refine ⟨⟨u ++ [j], BranchingProcess.mem_sample_append_singleton.mpr ⟨hu, hj⟩,
        (gShapeSpace (σ (u ++ [j]))).entry⟩, ?_⟩
      simp only [code_eq, GAssembly.entry_gShapeSpace_val, List.append_nil, vals_append,
        vals_cons, vals_nil, gCopyAddr_concat, liftN_vals, hexit, List.append_assoc]
    · exact ⟨⟨u, hu, ⟨p.1 ++ [m], RTree.mem_addrList_iff.mpr hchild⟩⟩,
        by simp only [code_eq, List.append_assoc]⟩

end SkelAssembly

/-! ### The dictionary between the copies and the sample -/

/-- **The letter map of a sample**, read at words over `ℕ`: the letter map of the
subfield at the vertex the word names. -/
noncomputable def sampleLetterN (c : GWord N → ℕ) (w : List ℕ) : ℕ → ℕ :=
  letterMap (ambSub c (unval N w))

lemma sampleLetterN_injective (c : GWord N → ℕ) (w : List ℕ) :
    Function.Injective (sampleLetterN c w) :=
  letterMap_injective _

lemma sampleLetterN_vals (c : GWord N → ℕ) (y : GWord N) :
    sampleLetterN c (vals y) = letterMap (ambSub c y) := by
  rw [sampleLetterN, unval_vals]

/-- **The sample read from the skeleton assembly**: the address translation along the
letter map of the sample. -/
noncomputable def transSampleN (c : GWord N → ℕ) : List ℕ → List ℕ := transN (sampleLetterN c)

lemma transSampleN_injective (c : GWord N → ℕ) : Function.Injective (transSampleN c) :=
  transN_injective (sampleLetterN_injective c)

lemma transSampleN_concat (c : GWord N → ℕ) (a : List ℕ) (m : ℕ) :
    transSampleN c (a ++ [m]) = transSampleN c a ++ [sampleLetterN c (transSampleN c a) m] :=
  transN_concat a m

@[simp] lemma transSampleN_nil (c : GWord N → ℕ) : transSampleN c [] = [] := rfl

/-- The bush lists of the shape at the root, read off the descent. -/
lemma decs_gShapeRoot_length (d : GWord N → ℕ) :
    (gShapeRoot d).decs.length = gSplitDepth d + 1 :=
  GShape.decs_length _

lemma decs_gShapeRoot_ne_nil (d : GWord N → ℕ) : (gShapeRoot d).decs ≠ [] :=
  GShape.decs_ne_nil _

lemma decs_gShapeRoot_getElem (d : GWord N → ℕ) {i : ℕ} (hi : i < (gShapeRoot d).decs.length) :
    (gShapeRoot d).decs[i] = gDecList (neckIter d i) := by
  simp only [decs_gShapeRoot, List.getElem_ofFn]

lemma gShapeRoot_exitAddr (d : GWord N → ℕ) :
    (gShapeRoot d).exitAddr = neckAddr (gShapeRoot d).decs (gSplitDepth d) := by
  rw [GShape.exitAddr, gExitAddr_eq_neckAddr, decs_gShapeRoot_length, Nat.add_sub_cancel]

lemma gShapeRoot_bouquet (d : GWord N → ℕ) : (gShapeRoot d).bouquet = gDecList (gSplitField d) :=
  rfl

lemma gShapeRoot_realise (d : GWord N → ℕ) :
    (gShapeRoot d).realise = realiseAux (gShapeRoot d).decs := rfl

/-- The number of bushes of a vertex is the number of its dying children. -/
lemma length_gDecList_eq {e : GWord N → ℕ} (he : e [] ≤ N) :
    (gDecList e).length = (dyingSet e).card := by
  rw [length_gDecList]
  have := survivors_card_add_dyingSet_card he
  omega

lemma neckIter_root {c : GWord N → ℕ} {y : GWord N} (hs : Survives (ambSub c y)) (i : ℕ) :
    neckIter (ambSub c y) i [] = c (y ++ neckPath (ambSub c y) i) := by
  rw [neckIter_eq_ambSub_neckPath hs, ambSub_root, ambSub_apply]

/-- **The neck of a copy is the chain of its entry**: the translation carries the neck
addresses of the shape at a vertex to its neck ray. -/
lemma transSampleN_neck {c : GWord N → ℕ} (hc : IsGHairySample c) {a : List ℕ} {y : GWord N}
    (ha : transSampleN c a = vals y) (hs : Survives (ambSub c y)) :
    ∀ i, i ≤ gSplitDepth (ambSub c y) →
      transSampleN c (a ++ neckAddr (gShapeRoot (ambSub c y)).decs i)
        = vals (y ++ neckPath (ambSub c y) i)
  | 0, _ => by simpa using ha
  | i + 1, hi => by
      have ih := transSampleN_neck hc ha hs i (by omega)
      have hi' : i < (gShapeRoot (ambSub c y)).decs.length := by
        rw [decs_gShapeRoot_length]; omega
      have hN : neckIter (ambSub c y) i [] ≤ N := by
        rw [neckIter_root hs]
        exact hc.offspring _
      rw [neckAddr_succ hi', ← List.append_assoc, transSampleN_concat, ih, sampleLetterN_vals,
        ← ambSub_ambSub, ← neckIter_eq_ambSub_neckPath hs i, decs_gShapeRoot_getElem _ hi',
        length_gDecList_eq hN, vals_append, vals_append, vals_neckPath_succ hs i,
        ← List.append_assoc, letterMap, if_neg (lt_irrefl _), Nat.sub_self]

/-- The entry vertices lie in the sample, at the root. -/
lemma gEntryV_mem_sample' {c : GWord N → ℕ} (hc : IsGHairySample c) {u : GWord N}
    (hu : u ∈ sample (gArityAt c)) : gEntryV c u ∈ sample c := by
  have h := gEntryV_mem_sample hc u [] (BranchingProcess.nil_mem_sample c)
    (by simpa using hc.survives) (by simpa using hu)
  simpa using h

/-- **The entry of a copy**: the translation carries the planting of the copy at `u` to
its entry vertex. -/
lemma transSampleN_gCopyAddr {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∀ {u : GWord N}, u ∈ sample (gArityAt c) →
      transSampleN c (gCopyAddr (liftN N (gShapeAt c)) (vals u)) = vals (gEntryV c u) := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton u j ih =>
      intro hu
      obtain ⟨hu', hj⟩ := BranchingProcess.mem_sample_append_singleton.mp hu
      obtain ⟨hred, hsurv⟩ := redSub_eq_ambSub_gEntryV' hc hu'
      have hs : Survives (ambSub c (gEntryV c u)) := hred ▸ hsurv
      have hih := ih hu'
      have hsf : gSplitField (ambSub c (gEntryV c u))
          = neckIter (ambSub c (gEntryV c u)) (gSplitDepth (ambSub c (gEntryV c u))) := rfl
      have hN : gSplitField (ambSub c (gEntryV c u)) [] ≤ N := by
        rw [hsf, neckIter_root hs]
        exact hc.offspring _
      have hj' : (j : ℕ) < skeletonDegree (gSplitField (ambSub c (gEntryV c u))) := by
        have : gArityAt c u = gArity (redSub c u) := rfl
        rw [this, hred] at hj
        exact hj
      have hlt : survLetter (gSplitField (ambSub c (gEntryV c u))) j < N := survLetter_lt hj'
      rw [vals_append, vals_cons, vals_nil, gCopyAddr_concat, liftN_vals, gShapeAt, hred,
        gShapeRoot_exitAddr, transSampleN_concat, transSampleN_neck hc hih hs _ le_rfl,
        gShapeRoot_bouquet, gEntryV_concat, hred, splitPath, unval_singleton hlt,
        sampleLetterN_vals, ← ambSub_ambSub, ← neckIter_eq_ambSub_neckPath hs, ← hsf,
        length_gDecList_eq hN, letterMap, if_neg (by omega), Nat.add_sub_cancel_left]
      simp only [vals_append, vals_cons, vals_nil, List.append_assoc]

/-- A vertex of a finite subtree founds a finite subtree. -/
lemma not_survives_ambSub_of_mem {e : GWord N → ℕ} (hfin : ¬ Survives e) {v : GWord N}
    (hv : v ∈ sample e) : ¬ Survives (ambSub e v) := by
  intro hs
  have hs' : (sample (ambSub e v) : Set (GWord N)).Infinite := hs
  have hsub : (fun z : GWord N ↦ v ++ z) '' (sample (ambSub e v) : Set (GWord N))
      ⊆ (sample e : Set (GWord N)) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, BranchingProcess.append_mem_sample_iff]
    exact ⟨hv, hz⟩
  have himg := hs'.image (f := fun z : GWord N ↦ v ++ z)
    (fun z _ z' _ h ↦ List.append_cancel_left h)
  exact hfin (himg.mono hsub)

/-- **The translation inside a bush**: below a dying vertex the translation reads the
letters one for one. -/
lemma transSampleN_bush {c : GWord N → ℕ} (hc : IsGHairySample c) {a : List ℕ} {y : GWord N}
    (ha : transSampleN c a = vals y) (hfin : ¬ Survives (ambSub c y)) :
    ∀ v : GWord N, v ∈ sample (ambSub c y) → transSampleN c (a ++ vals v) = vals (y ++ v) := by
  intro v
  induction v using List.reverseRecOn with
  | nil => simpa using ha
  | append_singleton v j ih =>
      intro hv
      obtain ⟨hv', hj⟩ := BranchingProcess.mem_sample_append_singleton.mp hv
      have hnot : ¬ Survives (ambSub c (y ++ v)) := by
        rw [← ambSub_ambSub]
        exact not_survives_ambSub_of_mem hfin hv'
      have hj' : (j : ℕ) < ambSub c (y ++ v) [] := by
        rw [ambSub_root]
        exact hj
      rw [vals_append, vals_cons, vals_nil, ← List.append_assoc, transSampleN_concat, ih hv',
        sampleLetterN_vals, letterMap_of_not_survives (by rw [ambSub_root]; exact hc.offspring _)
          hnot hj', ← List.append_assoc, vals_append, vals_append, vals_cons, vals_nil,
        vals_append]

/-- **The addresses of a bush are the vertices of the dying subtree.** -/
lemma isAddr_bushRTree_iff {e : GWord N → ℕ} (he : ∀ v, e v ≤ N) (hfin : ¬ Survives e)
    (w : List ℕ) : IsAddr (bushRTree e) w ↔ ∃ v ∈ sample e, w = vals v := by
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := exists_map_val_eq w (lt_of_isAddr_rtreeOf _ e w hw)
    exact ⟨v, (mem_sample_iff_isAddr_rtreeOf _ he (sampleHeight_spec hfin) v).mpr hw, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact (mem_sample_iff_isAddr_rtreeOf _ he (sampleHeight_spec hfin) v).mp hv

/-! ### The vertices of the assembly and the vertices of the sample -/

/-- The neck-vertex case of the dictionary: a neck address of the shape at a vertex
translates to a vertex of its neck ray, whose children are counted by its bushes and its
surviving children. -/
lemma transSampleN_spec_neck {c : GWord N → ℕ} (hc : IsGHairySample c) {a : List ℕ}
    {y₀ : GWord N} (ha : transSampleN c a = vals y₀) (hy₀ : y₀ ∈ sample c)
    (hs : Survives (ambSub c y₀)) {i : ℕ} (hi : i < (gShapeRoot (ambSub c y₀)).decs.length) :
    ∃ v ∈ sample c, transSampleN c (a ++ neckAddr (gShapeRoot (ambSub c y₀)).decs i) = vals v ∧
      ∀ m, ((neckAddr (gShapeRoot (ambSub c y₀)).decs i = (gShapeRoot (ambSub c y₀)).exitAddr
            ∧ ∃ j : Fin N, (j : ℕ) < gArity (ambSub c y₀)
              ∧ m = (gShapeRoot (ambSub c y₀)).bouquet.length + j)
          ∨ IsAddr (gShapeRoot (ambSub c y₀)).realise
              (neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [m])) ↔ m < c v := by
  have hLlen : (gShapeRoot (ambSub c y₀)).decs.length = gSplitDepth (ambSub c y₀) + 1 := decs_gShapeRoot_length (ambSub c y₀)
  have hin : i ≤ gSplitDepth (ambSub c y₀) := by omega
  have hroot : c (y₀ ++ neckPath (ambSub c y₀) i) = neckIter (ambSub c y₀) i [] := (neckIter_root hs i).symm
  have hN : neckIter (ambSub c y₀) i [] ≤ N := by rw [← hroot]; exact hc.offspring _
  have hcard : (gShapeRoot (ambSub c y₀)).decs[i].length = (dyingSet (neckIter (ambSub c y₀) i)).card := by
    rw [decs_gShapeRoot_getElem (ambSub c y₀) hi, length_gDecList_eq hN]
  have hsum := survivors_card_add_dyingSet_card hN
  refine ⟨y₀ ++ neckPath (ambSub c y₀) i, neckPath_mem_sample hy₀ hs i,
    transSampleN_neck hc ha hs i hin, fun m ↦ ?_⟩
  rw [hroot, gShapeRoot_realise, gShapeRoot_exitAddr,
    isAddr_realiseAux_neck_concat (gShapeRoot (ambSub c y₀)).decs i hi m, hcard, hLlen]
  rcases Nat.lt_or_ge i (gSplitDepth (ambSub c y₀)) with hlt | hge
  · have hdeg : skeletonDegree (neckIter (ambSub c y₀) i) = 1 := skeletonDegree_neckIter_eq_one hs hlt
    have hne : neckAddr (gShapeRoot (ambSub c y₀)).decs i ≠ neckAddr (gShapeRoot (ambSub c y₀)).decs (gSplitDepth (ambSub c y₀)) := by
      intro h
      have := congrArg List.length h
      rw [neckAddr_length (by omega), neckAddr_length (by omega)] at this
      omega
    simp only [hne, false_and, false_or]
    omega
  · have hin' : i = gSplitDepth (ambSub c y₀) := le_antisymm hin hge
    subst hin'
    have hκ : gArity (ambSub c y₀)
        = skeletonDegree (neckIter (ambSub c y₀) (gSplitDepth (ambSub c y₀))) := rfl
    have hbq : (gShapeRoot (ambSub c y₀)).bouquet.length
        = (dyingSet (neckIter (ambSub c y₀) (gSplitDepth (ambSub c y₀)))).card := by
      rw [gShapeRoot_bouquet, ← hcard, decs_gShapeRoot_getElem (ambSub c y₀) hi]
      rfl
    rw [hκ, hbq]
    constructor
    · rintro (⟨-, j, hj, rfl⟩ | h | ⟨-, h⟩)
      · omega
      · omega
      · omega
    · intro hm
      by_cases hm' : m < (dyingSet (neckIter (ambSub c y₀) (gSplitDepth (ambSub c y₀)))).card
      · exact Or.inr (Or.inl hm')
      · exact Or.inl ⟨rfl, ⟨m - (dyingSet (neckIter (ambSub c y₀) (gSplitDepth (ambSub c y₀)))).card,
          by omega⟩, by simp only; omega, by simp only; omega⟩

/-- The bush case of the dictionary: a bush address of the shape at a vertex translates
to a vertex of the dying subtree hanging off its neck ray, whose children are the
children of that vertex. -/
lemma transSampleN_spec_bush {c : GWord N → ℕ} (hc : IsGHairySample c) {a : List ℕ}
    {y₀ : GWord N} (ha : transSampleN c a = vals y₀) (hy₀ : y₀ ∈ sample c)
    (hs : Survives (ambSub c y₀)) {i : ℕ} (hi : i < (gShapeRoot (ambSub c y₀)).decs.length)
    {m₀ : ℕ} (hm₀ : m₀ < (gShapeRoot (ambSub c y₀)).decs[i].length) {z : List ℕ}
    (hz : IsAddr (gShapeRoot (ambSub c y₀)).decs[i][m₀] z) :
    ∃ v ∈ sample c,
      transSampleN c (a ++ (neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: z)) = vals v ∧
      ∀ m, ((neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: z
              = (gShapeRoot (ambSub c y₀)).exitAddr
            ∧ ∃ j : Fin N, (j : ℕ) < gArity (ambSub c y₀)
              ∧ m = (gShapeRoot (ambSub c y₀)).bouquet.length + j)
          ∨ IsAddr (gShapeRoot (ambSub c y₀)).realise
              ((neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: z) ++ [m])) ↔ m < c v := by
  have hLlen : (gShapeRoot (ambSub c y₀)).decs.length = gSplitDepth (ambSub c y₀) + 1 := decs_gShapeRoot_length (ambSub c y₀)
  have hin : i ≤ gSplitDepth (ambSub c y₀) := by omega
  have hroot : c (y₀ ++ neckPath (ambSub c y₀) i) = neckIter (ambSub c y₀) i [] := (neckIter_root hs i).symm
  have hN : neckIter (ambSub c y₀) i [] ≤ N := by rw [← hroot]; exact hc.offspring _
  have hLi : (gShapeRoot (ambSub c y₀)).decs[i] = gDecList (neckIter (ambSub c y₀) i) := decs_gShapeRoot_getElem (ambSub c y₀) hi
  have hcard : (gShapeRoot (ambSub c y₀)).decs[i].length = (dyingSet (neckIter (ambSub c y₀) i)).card := by
    rw [hLi, length_gDecList_eq hN]
  have hm₀' : m₀ < (dyingSet (neckIter (ambSub c y₀) i)).card := by rw [← hcard]; exact hm₀
  have hm₀'' : m₀ < (gDecList (neckIter (ambSub c y₀) i)).length := by
    rw [length_gDecList_eq hN]; exact hm₀'
  have hbush : (gShapeRoot (ambSub c y₀)).decs[i][m₀] = bushRTree (dyingAt (neckIter (ambSub c y₀) i) m₀) := by
    rw [List.getElem_of_eq hLi hm₀, getElem_gDecList _ hm₀'']
  rw [hbush] at hz
  have hy₁mem : y₀ ++ neckPath (ambSub c y₀) i ∈ sample c := neckPath_mem_sample hy₀ hs i
  have he1 : ambSub c (y₀ ++ neckPath (ambSub c y₀) i) = neckIter (ambSub c y₀) i := by
    rw [← ambSub_ambSub, neckIter_eq_ambSub_neckPath hs i]
  obtain ⟨ℓ, hℓ, hℓeq⟩ := dyingLetter_mem hm₀'
  have hℓlt : dyingLetter (neckIter (ambSub c y₀) i) m₀ < N := by rw [hℓeq]; exact ℓ.isLt
  have he2 : dyingAt (neckIter (ambSub c y₀) i) m₀
      = ambSub c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀]) := by
    rw [dyingAt_eq_ambSub hm₀', ← ambSub_ambSub, he1]
  have hfin : ¬ Survives (ambSub c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀])) :=
    he2 ▸ not_survives_dyingAt hm₀'
  have hN2 : ∀ v, ambSub c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀]) v ≤ N :=
    fun v ↦ hc.offspring _
  rw [he2, isAddr_bushRTree_iff hN2 hfin] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  have hy₂mem : y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀] ∈ sample c := by
    rw [unval_singleton hℓlt, BranchingProcess.mem_sample_append_singleton]
    refine ⟨hy₁mem, ?_⟩
    show dyingLetter (neckIter (ambSub c y₀) i) m₀ < c (y₀ ++ neckPath (ambSub c y₀) i)
    rw [hroot, hℓeq]
    exact (mem_dyingSet.mp hℓ).1
  have htrans2 : transSampleN c (a ++ neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [m₀])
      = vals (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀]) := by
    rw [transSampleN_concat, transSampleN_neck hc ha hs i hin, sampleLetterN_vals, he1,
      letterMap, if_pos hm₀', unval_singleton hℓlt]
    simp only [vals_append, vals_cons, vals_nil]
  have htrans : transSampleN c (a ++ (neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: vals v))
      = vals (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀] ++ v) := by
    have heq : a ++ (neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: vals v)
        = (a ++ neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [m₀]) ++ vals v := by
      simp [List.append_assoc]
    rw [heq]
    exact transSampleN_bush hc htrans2 hfin v hv
  refine ⟨_, (BranchingProcess.append_mem_sample_iff c _ v).mpr ⟨hy₂mem, hv⟩, htrans,
    fun m ↦ ?_⟩
  have hne : neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: vals v ≠ (gShapeRoot (ambSub c y₀)).exitAddr := by
    rw [gShapeRoot_exitAddr]
    intro h
    have hlen := congrArg List.length h
    have hin2 : i ≤ (gShapeRoot (ambSub c y₀)).decs.length := by omega
    have hn2 : gSplitDepth (ambSub c y₀) ≤ (gShapeRoot (ambSub c y₀)).decs.length := by omega
    simp only [List.length_append, List.length_cons, neckAddr_length hin2,
      neckAddr_length hn2] at hlen
    have hlt : i < gSplitDepth (ambSub c y₀) := by omega
    have h1 : neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [m₀] <+: neckAddr (gShapeRoot (ambSub c y₀)).decs (gSplitDepth (ambSub c y₀)) := by
      rw [← h]
      exact ⟨vals v, by simp⟩
    have h2 : neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [(gShapeRoot (ambSub c y₀)).decs[i].length]
        <+: neckAddr (gShapeRoot (ambSub c y₀)).decs (gSplitDepth (ambSub c y₀)) := by
      rw [← neckAddr_succ hi]
      exact neckAddr_prefix _ (by omega)
    have h3 := List.prefix_of_prefix_length_le h1 h2 (by simp)
    have h4 := h3.eq_of_length (by simp)
    have h5 := List.append_cancel_left h4
    simp only [List.cons.injEq, and_true] at h5
    omega
  simp only [hne, false_and, false_or]
  have hassoc : neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: vals v ++ [m]
      = neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: (vals v ++ [m]) := by
    simp
  rw [hassoc, gShapeRoot_realise, isAddr_realiseAux_bush _ i hi m₀ hm₀, hbush, he2,
    isAddr_bushRTree_iff hN2 hfin]
  have hcv : c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀] ++ v)
      = ambSub c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀]) v :=
    (ambSub_apply c _ v).symm
  rw [hcv]
  constructor
  · rintro ⟨v', hv', heq⟩
    obtain ⟨v'', j, rfl, hv'', rfl⟩ := SkelAssembly.vals_eq_append_singleton_iff.mp heq.symm
    have : v'' = v := vals_injective hv''
    subst this
    exact (BranchingProcess.mem_sample_append_singleton.mp hv').2
  · intro hm
    have hmN : m < N := lt_of_lt_of_le hm (hN2 v)
    exact ⟨v ++ [⟨m, hmN⟩], BranchingProcess.mem_sample_append_singleton.mpr ⟨hv, hm⟩, by simp⟩

/-- **The dictionary** (**`thm:shape-iid`** at general arity): the translation carries a
vertex of the skeleton assembly to a vertex of the sample, and the children of the two
agree through the letter map. -/
theorem transSampleN_code_spec {c : GWord N → ℕ} (hc : IsGHairySample c)
    (x : SkelAssembly (gArityAt c) (gShapeAt c)) :
    (∃ v ∈ sample c, transSampleN c x.code = vals v) ∧
      ∀ m : ℕ, (∃ y : SkelAssembly (gArityAt c) (gShapeAt c), y.code = x.code ++ [m])
        ↔ sampleLetterN c (transSampleN c x.code) m < c (unval N (transSampleN c x.code)) := by
  obtain ⟨u, hu, pw, hpw⟩ := x
  obtain ⟨hred, hsurv⟩ := redSub_eq_ambSub_gEntryV' hc hu
  have hs : Survives (ambSub c (gEntryV c u)) := hred ▸ hsurv
  have hy₀mem : gEntryV c u ∈ sample c := gEntryV_mem_sample' hc hu
  have ha := transSampleN_gCopyAddr hc hu
  have hshape : gShapeAt c u = gShapeRoot (ambSub c (gEntryV c u)) := by rw [gShapeAt, hred]
  have harity : gArityAt c u = gArity (ambSub c (gEntryV c u)) := by rw [gArityAt, hred]
  have hp : IsAddr (realiseAux (gShapeRoot (ambSub c (gEntryV c u))).decs) pw := by
    have := RTree.mem_addrList_iff.mp hpw
    rwa [hshape] at this
  have hmain : ∃ v ∈ sample c,
      transSampleN c (SkelAssembly.code ⟨u, hu, ⟨pw, hpw⟩⟩) = vals v ∧
      ∀ m, ((pw = (gShapeRoot (ambSub c (gEntryV c u))).exitAddr
            ∧ ∃ j : Fin N, (j : ℕ) < gArity (ambSub c (gEntryV c u))
              ∧ m = (gShapeRoot (ambSub c (gEntryV c u))).bouquet.length + j)
          ∨ IsAddr (gShapeRoot (ambSub c (gEntryV c u))).realise (pw ++ [m])) ↔ m < c v := by
    rw [SkelAssembly.code_eq]
    dsimp only
    rcases isAddr_realiseAux_cases _ (decs_gShapeRoot_ne_nil _) hp with
      ⟨i, hi, hpi⟩ | ⟨i, hi, m₀, hm₀, z, hz, hpz⟩
    · rw [hpi]
      exact transSampleN_spec_neck hc ha hy₀mem hs hi
    · rw [hpz]
      exact transSampleN_spec_bush hc ha hy₀mem hs hi hm₀ hz
  obtain ⟨v, hv, htrans, hcond⟩ := hmain
  refine ⟨⟨v, hv, htrans⟩, fun m ↦ ?_⟩
  rw [SkelAssembly.exists_code_concat_iff, htrans, sampleLetterN_vals, unval_vals]
  dsimp only
  rw [hshape, harity, hcond m]
  have h := letterMap_lt_iff (d := ambSub c v) (by rw [ambSub_root]; exact hc.offspring v) m
  rw [ambSub_root] at h
  exact h.symm

/-! ### The sample is the assembly of its shapes over its reduced skeleton -/

/-- Every vertex of the sample is the translation of a vertex of the skeleton assembly:
the chains of the skeleton and their bushes exhaust the sample. -/
lemma exists_code_transSampleN {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∀ v : GWord N, v ∈ sample c →
      ∃ x : SkelAssembly (gArityAt c) (gShapeAt c), transSampleN c x.code = vals v := by
  intro v
  induction v using List.reverseRecOn with
  | nil =>
      intro _
      exact ⟨⟨[], BranchingProcess.nil_mem_sample _, (gShapeSpace _).entry⟩,
        by simp [SkelAssembly.code_eq]⟩
  | append_singleton v j ih =>
      intro hv
      obtain ⟨hv', hj⟩ := BranchingProcess.mem_sample_append_singleton.mp hv
      obtain ⟨x, hx⟩ := ih hv'
      obtain ⟨m, -, hmeq⟩ := letterMap_surj (d := ambSub c v)
        (by rw [ambSub_root]; exact hc.offspring v) (by rw [ambSub_root]; exact hj)
      have hspec := (transSampleN_code_spec hc x).2 m
      rw [hx, sampleLetterN_vals, unval_vals] at hspec
      have hchild : letterMap (ambSub c v) m < c v := by rw [hmeq]; exact hj
      obtain ⟨y, hy⟩ := hspec.mpr hchild
      refine ⟨y, ?_⟩
      rw [hy, transSampleN_concat, hx, sampleLetterN_vals, hmeq, vals_append, vals_cons, vals_nil]

/-- **`thm:shape-iid` at general arity, the isometry** (the premise of
**`it:general-glued`**): a bushy sample is isometric to the assembly of its own shapes
over its reduced skeleton.  The isometry is the address translation: it reads the
letters of the assembly one for one, sending the neck of a copy to the chain of its entry
vertex, its bushes to the dying subtrees hanging off that chain, and the copies below
its exit to the surviving children of the split, so it preserves lengths and the prefix
order, and with them every distance. -/
theorem gAssembly_isometric_sample {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∃ Φ : SkelAssembly (gArityAt c) (gShapeAt c) → {v : GWord N // v ∈ sample c},
      Function.Bijective Φ ∧
      ∀ x y, (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y := by
  have hmem : ∀ x : SkelAssembly (gArityAt c) (gShapeAt c),
      unval N (transSampleN c x.code) ∈ sample c
        ∧ vals (unval N (transSampleN c x.code)) = transSampleN c x.code := by
    intro x
    obtain ⟨v, hv, hx⟩ := (transSampleN_code_spec hc x).1
    rw [hx, unval_vals]
    exact ⟨hv, rfl⟩
  refine ⟨fun x ↦ ⟨unval N (transSampleN c x.code), (hmem x).1⟩, ⟨?_, ?_⟩, ?_⟩
  · intro x y h
    have h1 : unval N (transSampleN c x.code) = unval N (transSampleN c y.code) :=
      congrArg Subtype.val h
    have h2 : transSampleN c x.code = transSampleN c y.code := by
      rw [← (hmem x).2, ← (hmem y).2, h1]
    exact SkelAssembly.code_injective (transSampleN_injective c h2)
  · rintro ⟨v, hv⟩
    obtain ⟨x, hx⟩ := exists_code_transSampleN hc v hv
    exact ⟨x, Subtype.ext (by simp only; rw [hx, unval_vals])⟩
  · intro x y
    simp only
    rw [← addrDist_vals, (hmem x).2, (hmem y).2, transSampleN,
      transN_addrDist (sampleLetterN_injective c)]
    rfl


end ChainClasses
