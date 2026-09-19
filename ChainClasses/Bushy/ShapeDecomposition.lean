import ChainClasses.Shape.Assembly
import BranchingProcess.Skeleton

/-!
`sec:shape-harris` of `matching_classes_simple.tex`: the deterministic half of
`thm:shape-iid`, the shape decomposition of a sample.

Two alphabets are in play.  A sample is cut out of the ambient binary tree by a field of
offspring counts, `Amb` naming its vertices, while the copies of the assembly are indexed
by the binary words `Word` of `sec:encoding` and a copy is addressed inside the
realisation of its shape.  The two are related by an address translation: a word of the
index alphabet is read letter by letter, the letter read at a vertex being chosen by the
letter map of that vertex, which sends `false` to the bush and `true` to the neck at a
decorated neck vertex and `false` to the child `0` and `true` to the child `1` everywhere
else.  A translation of that shape preserves lengths and the prefix order, hence the
wedge and every distance, so the isometry of `thm:shape-iid` comes down to identifying
the image of the addresses of the assembly with the vertices of the sample.  That
identification is one case analysis over `def:shape`: an address of a realisation is a
neck vertex or a vertex of the bush of one, and the two families read as the chain of a
skeleton vertex and the dying subtrees hanging off it.

The i.i.d. clause of `thm:shape-iid` needs the joint law of the skeleton and its bushes,
of which `BranchingProcess.Skeleton` carries the two marginals; the shapes are exhibited
here as a measurable field, which is the form that clause is stated over.

* `letterOf`, `letters`, `transWith`: **the address translation** of a field of letter
  maps, with `transWith_length`, `transWith_prefix`, `transWith_injective` and
  `transWith_prefix_iff`; `transWith_wedge` and `transWith_treeDist` are the isometry it
  carries, the wedge being determined by the prefix order alone.
* `shift`, `triOf`, `treeHeight`, `bushTri`: **`def:shape`, the bushes**.  A dying
  subtree is finite, so a fuel exceeding its height reads it off the offspring field as a
  term of `Tri`, and `isAddr_bushTri` identifies its addresses with the vertices of the
  subtree.
* `neckLetter`, `bushLetter`, `neckRay`, `splitDepth`: **`thm:harris`**, the skeleton of
  a sample read in the sample itself: the surviving child, the dying one, the ray of
  surviving children and the depth of the split ending it.  `neckLetter_mem_survivors` is
  that the skeleton has no leaves and `not_survives_bush` that a neck vertex with two
  children has a dying one.
* `IsBushySample`: the deterministic hypotheses of `sec:shapes`, offspring in `{0,1,2}`,
  survival, and every neck ray meeting a split, which is `Ω₀` read for the skeleton;
  `splitDepth_spec` and `splitDepth_min` are `thm:chains` for it.
* `entryV`, `decAt`, `shapeAt`: **`thm:shape-iid`**, the entry vertex of a copy and the
  shape it carries, the chain of the entry together with the bushes of its neck vertices.
* `sampleLetter`, `transSample`: the letter map of a sample and the translation it
  carries.
* `Shape.isAddr_neckAddr_concat_none`, `Shape.isAddr_neckAddr_concat_some`,
  `Shape.isAddr_bush` and `Shape.isAddr_cases`: the
  addresses of a realisation, their children, and the decomposition of `def:shape` every
  case analysis below runs on.
* `transSample_neck`, `transSample_copyAddr`, `transSample_bush`: **the dictionary**.  The
  translation carries the planting of a copy to the entry vertex of its chain, the neck
  address to the neck ray, and the bush addresses to the dying subtrees.
* `Assembly.exists_code_concat_iff` and `transSample_code_spec`: the children of a vertex
  of the assembly, and the dictionary in the form the induction consumes, a vertex of the
  sample with the same children.
* `exists_code_transSample` and `assembly_isometric_sample`: **`thm:shape-iid`, the last
  clause**.  The chains and their bushes exhaust the sample, so the translation is a
  bijection onto it, and it is an isometry.
* `FibreMeasurable` with `map`, `prod`, `comp` and `pi`, and `measurableSet_sInf_eq`: the
  measurability of a countably valued function of the field, stated through its fibres
  since words, trees and shapes carry no measurable structure.
* `fibreMeasurable_shapeAt` and `measurableSet_shapeAt_eq`: **the shape field is
  measurable**, the event that a copy carries a given shape.
* `sampleMeasure_offspring_le` and `ae_isBushySample`: the standing hypotheses under the
  conditioned law.  The support bound and survival hold almost surely, so what
  `IsBushySample` asks beyond them is the event that every ray of the skeleton meets a
  split, which enters as a hypothesis.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (sample Survives skeleton survivors skeletonDegree Offspring
  sampleMeasure survivalMeasure)

/-- A vertex of the ambient binary tree in which the sample lives, a word over the
alphabet `Fin 2`, as against the index tree `𝔹 = Word` of the copies. -/
abbrev Amb : Type := BranchingProcess.Word 2

/-! ### Letterwise translations of addresses -/

/-- The letter of the ambient alphabet named by a letter of the index alphabet:
`false` is `0` and `true` is `1`. -/
def letterOf (b : Bool) : Fin 2 := if b then 1 else 0

lemma letterOf_injective : Function.Injective letterOf := by decide

@[simp] lemma letterOf_false : letterOf false = 0 := rfl

@[simp] lemma letterOf_true : letterOf true = 1 := rfl

/-- A word of the index alphabet read letter by letter in the ambient alphabet. -/
def letters (a : Word) : Amb := a.map letterOf

@[simp] lemma letters_nil : letters [] = [] := rfl

@[simp] lemma letters_cons (b : Bool) (a : Word) : letters (b :: a) = letterOf b :: letters a :=
  rfl

@[simp] lemma letters_append (a a' : Word) : letters (a ++ a') = letters a ++ letters a' := by
  simp [letters]

@[simp] lemma letters_length (a : Word) : (letters a).length = a.length := by
  simp [letters]

/-- **The address translation of a field of letter maps**: the word `a` is read letter
by letter, the letter `b` at the vertex already reached being sent to `L v b`.  The
translation preserves lengths and the prefix order, so it is an isometry as soon as
every `L v` is injective. -/
def transWith (L : Amb → Bool → Fin 2) (a : Word) : Amb :=
  a.foldl (fun v b => v ++ [L v b]) []

variable {L : Amb → Bool → Fin 2}

@[simp] lemma transWith_nil : transWith L [] = [] := rfl

/-- The recursion of the translation: one further letter is read at the vertex the
translation has reached. -/
lemma transWith_concat (a : Word) (b : Bool) :
    transWith L (a ++ [b]) = transWith L a ++ [L (transWith L a) b] := by
  simp [transWith, List.foldl_append]

@[simp] lemma transWith_length (a : Word) : (transWith L a).length = a.length := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a b ih => simp [transWith_concat, ih]

/-- The translation only appends, so it is monotone for the prefix order. -/
lemma transWith_prefix {a a' : Word} (h : a <+: a') : transWith L a <+: transWith L a' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc, transWith_concat]
      exact ih.trans (List.prefix_append _ _)

/-- **The translation is injective**: the letter maps are, and the vertex reached is
determined by the word already read. -/
lemma transWith_injective (hL : ∀ v, Function.Injective (L v)) :
    Function.Injective (transWith L) := by
  intro a
  induction a using List.reverseRecOn with
  | nil =>
      intro a' h
      have hlen := congrArg List.length h
      simp only [transWith_nil, transWith_length, List.length_nil] at hlen
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton a b ih =>
      intro a' h
      rcases List.eq_nil_or_concat a' with rfl | ⟨a₀, b₀, rfl⟩
      · have hlen := congrArg List.length h
        simp only [transWith_length, List.length_append,
          List.length_singleton, List.length_nil] at hlen
        omega
      · rw [List.concat_eq_append] at h ⊢
        rw [transWith_concat, transWith_concat] at h
        have hlen : (transWith L a).length = (transWith L a₀).length := by
          simp only [transWith_length]
          have := congrArg List.length h
          simp only [List.length_append, List.length_singleton, transWith_length] at this
          omega
        obtain ⟨h1, h2⟩ := List.append_inj h hlen
        have ha : a = a₀ := ih h1
        subst ha
        have hb : L (transWith L a) b = L (transWith L a) b₀ := by
          simpa using h2
        rw [hL _ hb]

/-- A prefix of a translated word is the translation of a prefix. -/
lemma transWith_take (a : Word) (k : ℕ) :
    transWith L (a.take k) = (transWith L a).take k := by
  have hpre : transWith L (a.take k) <+: transWith L a :=
    transWith_prefix (List.take_prefix k a)
  rw [List.prefix_iff_eq_take.mp hpre, transWith_length, List.length_take]
  rcases le_total k a.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le (by simp),
      List.take_of_length_le (by simpa using h)]

/-- **The translation reflects the prefix order**, so it is an order isomorphism onto
its image. -/
lemma transWith_prefix_iff (hL : ∀ v, Function.Injective (L v)) {a a' : Word} :
    transWith L a <+: transWith L a' ↔ a <+: a' := by
  refine ⟨fun h ↦ ?_, transWith_prefix⟩
  have hlen : a.length ≤ a'.length := by
    have := h.length_le
    simpa using this
  have heq : transWith L a = transWith L (a'.take a.length) := by
    rw [transWith_take, List.prefix_iff_eq_take.mp h, transWith_length]
  rw [transWith_injective hL heq]
  exact List.take_prefix _ _

/-- The translation carries wedges to wedges: the meet of two words is read off the
prefix order, which the translation preserves in both directions. -/
lemma transWith_wedge (hL : ∀ v, Function.Injective (L v)) (a a' : Word) :
    BranchingProcess.wedge (transWith L a) (transWith L a') = transWith L (wedge a a') := by
  have hle : transWith L (wedge a a') <+:
      BranchingProcess.wedge (transWith L a) (transWith L a') :=
    BranchingProcess.prefix_wedge_of_prefix (transWith_prefix (wedge_prefix_left a a'))
      (transWith_prefix (wedge_prefix_right a a'))
  set z : Amb := BranchingProcess.wedge (transWith L a) (transWith L a') with hz
  have hza : z <+: transWith L a := BranchingProcess.wedge_prefix_left _ _
  have hza' : z <+: transWith L a' := BranchingProcess.wedge_prefix_right _ _
  have hzt : z = transWith L (a.take z.length) := by
    rw [transWith_take, ← List.prefix_iff_eq_take.mp hza]
  have h1 : a.take z.length <+: a := List.take_prefix _ _
  have h2 : a.take z.length <+: a' := by
    rw [← transWith_prefix_iff hL, ← hzt]
    exact hza'
  have h3 : a.take z.length <+: wedge a a' := prefix_wedge h1 h2
  have hlen : z.length ≤ (transWith L (wedge a a')).length := by
    have h4 := (transWith_prefix (L := L) h3).length_le
    rw [← hzt] at h4
    exact h4
  exact (hle.eq_of_length (le_antisymm hle.length_le hlen)).symm

/-- **The translation is an isometry**: the tree distance is read off lengths and the
length of the wedge, and the translation preserves both. -/
theorem transWith_treeDist (hL : ∀ v, Function.Injective (L v)) (a a' : Word) :
    BranchingProcess.treeDist (transWith L a) (transWith L a') = treeDist a a' := by
  rw [BranchingProcess.treeDist, treeDist, transWith_wedge hL, transWith_length,
    transWith_length, transWith_length]

/-! ### The bushes as finite trees -/

/-- The offspring field shifted to a vertex, the field of the subtree there. -/
def shift (c : Amb → ℕ) (v : Amb) : Amb → ℕ := fun w ↦ c (v ++ w)

@[simp] lemma shift_nil (c : Amb → ℕ) : shift c [] = c := by
  funext w; rw [shift, List.nil_append]

lemma shift_shift (c : Amb → ℕ) (v u : Amb) : shift (shift c v) u = shift c (v ++ u) := by
  funext w; simp [shift, List.append_assoc]

lemma shift_apply (c : Amb → ℕ) (v w : Amb) : shift c v w = c (v ++ w) := rfl

/-- **`def:shape`**, a bush read off an offspring field: a tree of at most the given
height, with the child `0` at `false` and the child `1` at `true`.  The height is a
fuel, and `isAddr_triOf` reads the tree once the fuel exceeds the height of the
sample. -/
def triOf : ℕ → (Amb → ℕ) → Tri
  | 0, _ => Tri.leaf
  | n + 1, d =>
      if d [] = 0 then Tri.leaf
      else if d [] = 1 then Tri.one (triOf n (shift d [0]))
      else Tri.two (triOf n (shift d [0])) (triOf n (shift d [1]))

/-- A child of the root of a sample, unfolded through the shift. -/
lemma mem_sample_cons {d : Amb → ℕ} {i : Fin 2} {u : Amb} :
    i :: u ∈ sample d ↔ (i : ℕ) < d [] ∧ u ∈ sample (shift d [i]) := by
  have h : (i :: u : Amb) = [i] ++ u := rfl
  rw [h, BranchingProcess.append_mem_sample_iff, BranchingProcess.singleton_mem_sample_iff]
  exact Iff.rfl

/-- The subtree of a sample of height at most `n + 1` has height at most `n`. -/
lemma height_shift {d : Amb → ℕ} {n : ℕ} (hn : ∀ u ∈ sample d, u.length ≤ n + 1) (i : Fin 2)
    (hi : (i : ℕ) < d []) : ∀ u ∈ sample (shift d [i]), u.length ≤ n := by
  intro u hu
  have hmem : i :: u ∈ sample d := mem_sample_cons.mpr ⟨hi, hu⟩
  have := hn _ hmem
  simp only [List.length_cons] at this
  omega

/-- **The bush of a field**: the addresses of the tree read off a field of offspring
counts are the vertices of its sample, provided the fuel exceeds the height. -/
lemma isAddr_triOf : ∀ (n : ℕ) {d : Amb → ℕ}, (∀ v, d v ≤ 2) →
    (∀ u ∈ sample d, u.length ≤ n) → ∀ a : Word,
    (triOf n d).IsAddr a ↔ letters a ∈ sample d := by
  intro n
  induction n with
  | zero =>
      intro d _ hn a
      rw [triOf]
      constructor
      · intro ha
        rw [Tri.eq_nil_of_isAddr_leaf ha]
        exact BranchingProcess.nil_mem_sample d
      · intro ha
        have hlen := hn _ ha
        rw [letters_length] at hlen
        rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)]
        simp
  | succ n ih =>
      intro d hd hn a
      rw [triOf]
      by_cases h0 : d [] = 0
      · rw [if_pos h0]
        constructor
        · intro ha
          rw [Tri.eq_nil_of_isAddr_leaf ha]
          exact BranchingProcess.nil_mem_sample d
        · intro ha
          rcases a with _ | ⟨b, r⟩
          · simp
          · exfalso
            rw [letters_cons, mem_sample_cons] at ha
            omega
      · rw [if_neg h0]
        have h1 : 1 ≤ d [] := Nat.one_le_iff_ne_zero.mpr h0
        by_cases h1' : d [] = 1
        · rw [if_pos h1']
          have hsub : ∀ u ∈ sample (shift d [(0 : Fin 2)]), u.length ≤ n :=
            height_shift hn 0 (by omega)
          have hIH := ih (d := shift d [(0 : Fin 2)]) (fun v ↦ hd _) hsub
          rcases a with _ | ⟨b, r⟩
          · simp [BranchingProcess.nil_mem_sample]
          · cases b with
            | false =>
                rw [Tri.isAddr_one_false, hIH, letters_cons, letterOf_false, mem_sample_cons]
                simp [h1']
            | true =>
                rw [letters_cons, letterOf_true, mem_sample_cons]
                simp [h1']
        · rw [if_neg h1']
          have h2 : d [] = 2 := by have := hd ([] : Amb); omega
          have hsub0 : ∀ u ∈ sample (shift d [(0 : Fin 2)]), u.length ≤ n :=
            height_shift hn 0 (by omega)
          have hsub1 : ∀ u ∈ sample (shift d [(1 : Fin 2)]), u.length ≤ n :=
            height_shift hn 1 (by omega)
          have hIH0 := ih (d := shift d [(0 : Fin 2)]) (fun v ↦ hd _) hsub0
          have hIH1 := ih (d := shift d [(1 : Fin 2)]) (fun v ↦ hd _) hsub1
          rcases a with _ | ⟨b, r⟩
          · simp [BranchingProcess.nil_mem_sample]
          · cases b with
            | false =>
                rw [Tri.isAddr_two_false, hIH0, letters_cons, letterOf_false, mem_sample_cons]
                simp [h2]
            | true =>
                rw [Tri.isAddr_two_true, hIH1, letters_cons, letterOf_true, mem_sample_cons]
                simp [h2]

/-- The height of a finite sample: the least bound on the lengths of its vertices. -/
noncomputable def treeHeight (d : Amb → ℕ) : ℕ := sInf {n | ∀ u ∈ sample d, u.length ≤ n}

/-- A dying subtree is finite, so its height is a genuine bound. -/
lemma treeHeight_spec {d : Amb → ℕ} (hfin : ¬ Survives d) :
    ∀ u ∈ sample d, u.length ≤ treeHeight d := by
  have hfin' : (sample d : Set Amb).Finite := Set.not_infinite.mp hfin
  obtain ⟨n, hn⟩ := (hfin'.image List.length).bddAbove
  have hmem : n ∈ {n | ∀ u ∈ sample d, u.length ≤ n} := fun u hu ↦ hn ⟨u, hu, rfl⟩
  exact Nat.sInf_mem ⟨n, hmem⟩

/-- **`def:shape`**, the bush at a dying vertex: the finite tree its subtree realises. -/
noncomputable def bushTri (d : Amb → ℕ) : Tri := triOf (treeHeight d) d

/-- **The bush is the subtree**: the addresses of the bush of a dying field are the
vertices of its sample. -/
theorem isAddr_bushTri {d : Amb → ℕ} (hd : ∀ v, d v ≤ 2) (hfin : ¬ Survives d) (a : Word) :
    (bushTri d).IsAddr a ↔ letters a ∈ sample d :=
  isAddr_triOf _ hd (treeHeight_spec hfin) a

/-! ### The skeleton of a sample -/

variable {c : Amb → ℕ}

/-- A surviving child of a vertex, unfolded through the shift. -/
lemma mem_survivors_shift {v : Amb} {i : Fin 2} :
    i ∈ survivors (shift c v) ↔ (i : ℕ) < c v ∧ Survives (shift c (v ++ [i])) := by
  rw [BranchingProcess.mem_survivors]
  have h1 : shift c v [] = c v := by rw [shift_apply, List.append_nil]
  have h2 : (fun w ↦ shift c v (i :: w)) = shift c (v ++ [i]) := by
    funext w
    simp [shift_apply, List.append_assoc]
  rw [h1, h2]

/-- At most two children of a vertex survive. -/
lemma skeletonDegree_le_two (d : Amb → ℕ) : skeletonDegree d ≤ 2 := by
  rw [BranchingProcess.skeletonDegree_eq_card]
  simpa using Finset.card_le_univ (survivors d)

/-- A split has both of its children surviving. -/
lemma survivors_eq_univ {d : Amb → ℕ} (h : skeletonDegree d = 2) :
    survivors d = Finset.univ := by
  rw [BranchingProcess.skeletonDegree_eq_card] at h
  exact Finset.eq_univ_of_card _ (by simpa using h)

/-- The letter along which the neck continues: the least surviving child. -/
noncomputable def neckLetter (c : Amb → ℕ) (v : Amb) : Fin 2 :=
  if (0 : Fin 2) ∈ survivors (shift c v) then 0 else 1

/-- The letter of the bush at a neck vertex: the child that is not the neck. -/
noncomputable def bushLetter (c : Amb → ℕ) (v : Amb) : Fin 2 :=
  if (0 : Fin 2) ∈ survivors (shift c v) then 1 else 0

lemma bushLetter_ne_neckLetter (c : Amb → ℕ) (v : Amb) : bushLetter c v ≠ neckLetter c v := by
  rw [bushLetter, neckLetter]
  split <;> decide

/-- **The skeleton has no leaves**: a surviving vertex has a surviving child, and the
neck follows it. -/
lemma neckLetter_mem_survivors {v : Amb} (h : Survives (shift c v)) :
    neckLetter c v ∈ survivors (shift c v) := by
  have hne : (survivors (shift c v)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun hc ↦ (BranchingProcess.not_survives_iff_survivors_eq_empty.mpr hc) h
  rw [neckLetter]
  by_cases h0 : (0 : Fin 2) ∈ survivors (shift c v)
  · rwa [if_pos h0]
  · rw [if_neg h0]
    obtain ⟨i, hi⟩ := hne
    have : i = 1 := by
      fin_cases i
      · exact absurd hi h0
      · rfl
    rwa [this] at hi

/-- The vertex the neck reaches survives. -/
lemma survives_neck {v : Amb} (h : Survives (shift c v)) :
    Survives (shift c (v ++ [neckLetter c v])) :=
  (mem_survivors_shift.mp (neckLetter_mem_survivors h)).2

/-- The vertex the neck reaches is a vertex of the sample. -/
lemma mem_sample_neck {v : Amb} (hv : v ∈ sample c) (h : Survives (shift c v)) :
    v ++ [neckLetter c v] ∈ sample c :=
  BranchingProcess.mem_sample_append_singleton.mpr
    ⟨hv, (mem_survivors_shift.mp (neckLetter_mem_survivors h)).1⟩

/-- A surviving vertex with one child continues its neck along that child. -/
lemma neckLetter_eq_zero {v : Amb} (h : Survives (shift c v)) (h2 : c v ≠ 2)
    (hle : c v ≤ 2) : neckLetter c v = 0 := by
  have hlt := (mem_survivors_shift.mp (neckLetter_mem_survivors h)).1
  have hval : (neckLetter c v : ℕ) = 0 := by omega
  exact Fin.ext hval

/-- **`thm:harris`**, the decoration of a neck vertex: a neck vertex with two children
has a dying one, and the neck follows the other. -/
lemma not_survives_bush {v : Amb} (h : Survives (shift c v))
    (hdeg : skeletonDegree (shift c v) = 1) (hc : c v = 2) :
    ¬ Survives (shift c (v ++ [bushLetter c v])) := by
  rw [BranchingProcess.skeletonDegree_eq_card] at hdeg
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdeg
  have hmem := neckLetter_mem_survivors h
  rw [ha, Finset.mem_singleton] at hmem
  intro hs
  have hlt : (bushLetter c v : ℕ) < c v := by
    have := (bushLetter c v).isLt
    omega
  have hb : bushLetter c v ∈ survivors (shift c v) := mem_survivors_shift.mpr ⟨hlt, hs⟩
  rw [ha, Finset.mem_singleton] at hb
  exact bushLetter_ne_neckLetter c v (hb.trans hmem.symm)

/-- The bush of a neck vertex with two children is one of its children. -/
lemma bushLetter_lt {v : Amb} (hc : c v = 2) : (bushLetter c v : ℕ) < c v := by
  have := (bushLetter c v).isLt
  omega

/-! ### Chains of the skeleton -/

/-- **The neck ray of a skeleton vertex**: the vertices reached by following the
surviving child, the ray of `thm:chains` read in the sample. -/
noncomputable def neckRay (c : Amb → ℕ) (v : Amb) : ℕ → Amb
  | 0 => v
  | k + 1 => neckRay c v k ++ [neckLetter c (neckRay c v k)]

@[simp] lemma neckRay_zero (c : Amb → ℕ) (v : Amb) : neckRay c v 0 = v := rfl

lemma neckRay_succ (c : Amb → ℕ) (v : Amb) (k : ℕ) :
    neckRay c v (k + 1) = neckRay c v k ++ [neckLetter c (neckRay c v k)] := rfl

/-- The neck ray stays in the skeleton. -/
lemma survives_neckRay {v : Amb} (h : Survives (shift c v)) :
    ∀ k, Survives (shift c (neckRay c v k))
  | 0 => h
  | k + 1 => by
      rw [neckRay_succ]
      exact survives_neck (survives_neckRay h k)

/-- The neck ray stays in the sample. -/
lemma mem_sample_neckRay {v : Amb} (hv : v ∈ sample c) (h : Survives (shift c v)) :
    ∀ k, neckRay c v k ∈ sample c
  | 0 => hv
  | k + 1 => by
      rw [neckRay_succ]
      exact mem_sample_neck (mem_sample_neckRay hv h k) (survives_neckRay h k)

@[simp] lemma neckRay_length (c : Amb → ℕ) (v : Amb) (k : ℕ) :
    (neckRay c v k).length = v.length + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [neckRay_succ]; simp [ih]; omega

/-- **`eq:lambda-def`**, the chain length in the sample: the depth of the first split
along the neck ray. -/
noncomputable def splitDepth (c : Amb → ℕ) (v : Amb) : ℕ :=
  sInf {k | 2 ≤ skeletonDegree (shift c (neckRay c v k))}

/-- **The deterministic hypotheses of `sec:shapes`**: the offspring counts lie in
`{0,1,2}`, the sample survives, and every ray of the skeleton meets a split, which is
the event `Ω₀` of `thm:chains` read for the skeleton. -/
structure IsBushySample (c : Amb → ℕ) : Prop where
  /-- The offspring counts lie in `{0,1,2}`. -/
  offspring : ∀ v, c v ≤ 2
  /-- The sample is infinite. -/
  survives : Survives c
  /-- Every neck ray of the skeleton meets a split. -/
  splits : ∀ v : Amb, Survives (shift c v) → ∃ k, 2 ≤ skeletonDegree (shift c (neckRay c v k))

/-- **`thm:chains`**: the neck ray of a skeleton vertex ends at a split. -/
lemma splitDepth_spec (hc : IsBushySample c) {v : Amb} (h : Survives (shift c v)) :
    skeletonDegree (shift c (neckRay c v (splitDepth c v))) = 2 := by
  have hmem := Nat.sInf_mem (hc.splits v h)
  exact le_antisymm (skeletonDegree_le_two _) hmem

/-- Below the split the skeleton vertices of the chain have one skeleton child. -/
lemma splitDepth_min {v : Amb} (h : Survives (shift c v)) {k : ℕ} (hk : k < splitDepth c v) :
    skeletonDegree (shift c (neckRay c v k)) = 1 := by
  have hnot : ¬ (2 ≤ skeletonDegree (shift c (neckRay c v k))) := fun hmem ↦
    absurd (Nat.sInf_le (m := k) hmem) (not_le.mpr hk)
  have hpos : skeletonDegree (shift c (neckRay c v k)) ≠ 0 :=
    BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp (survives_neckRay h k)
  omega

/-- A split has two children. -/
lemma eq_two_of_skeletonDegree_two {v : Amb} (hc : IsBushySample c)
    (h : skeletonDegree (shift c v) = 2) : c v = 2 := by
  have huniv := survivors_eq_univ h
  have h1 : (1 : Fin 2) ∈ survivors (shift c v) := by rw [huniv]; exact Finset.mem_univ _
  have hlt := (mem_survivors_shift.mp h1).1
  have := hc.offspring v
  simp only [Fin.val_one] at hlt
  omega

/-- A neck vertex with two children has one child dying. -/
lemma eq_one_or_two_of_survives {v : Amb} (hc : IsBushySample c) (h : Survives (shift c v)) :
    c v = 1 ∨ c v = 2 := by
  have hlt := (mem_survivors_shift.mp (neckLetter_mem_survivors h)).1
  have := hc.offspring v
  omega

/-! ### The shapes of a sample -/

/-- **`thm:shape-iid`**, the entry vertex of a copy: the chain of `w` is followed to
its split, whose two children found the copies `w1` and `w2`. -/
noncomputable def entryV (c : Amb → ℕ) (w : Word) : Amb :=
  w.foldl (fun v j ↦ neckRay c v (splitDepth c v) ++ [letterOf j]) []

@[simp] lemma entryV_nil (c : Amb → ℕ) : entryV c [] = [] := rfl

/-- The recursion of the entry map: the copy `wj` starts at the child `j` of the split
ending the chain of `w`. -/
lemma entryV_concat (c : Amb → ℕ) (w : Word) (j : Bool) :
    entryV c (w ++ [j])
      = neckRay c (entryV c w) (splitDepth c (entryV c w)) ++ [letterOf j] := by
  simp [entryV, List.foldl_append]

/-- Every entry vertex is a skeleton vertex. -/
lemma entryV_mem_skeleton (hc : IsBushySample c) (w : Word) :
    entryV c w ∈ sample c ∧ Survives (shift c (entryV c w)) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨BranchingProcess.nil_mem_sample c, by simpa using hc.survives⟩
  | append_singleton w j ih =>
      obtain ⟨hmem, hsurv⟩ := ih
      set v := entryV c w with hv
      set u := neckRay c v (splitDepth c v) with hu
      have humem : u ∈ sample c := mem_sample_neckRay hmem hsurv _
      have husurv : Survives (shift c u) := survives_neckRay hsurv _
      have hdeg : skeletonDegree (shift c u) = 2 := splitDepth_spec hc hsurv
      have hjmem : letterOf j ∈ survivors (shift c u) := by
        rw [survivors_eq_univ hdeg]
        exact Finset.mem_univ _
      obtain ⟨hlt, hjsurv⟩ := mem_survivors_shift.mp hjmem
      rw [entryV_concat]
      exact ⟨BranchingProcess.mem_sample_append_singleton.mpr ⟨humem, hlt⟩, hjsurv⟩

/-- **`def:shape`**, the decoration of a neck vertex: its dying child, read as a finite
tree, when it has two children, and nothing when it has one. -/
noncomputable def decAt (c : Amb → ℕ) (v : Amb) : Option Tri :=
  if c v = 2 then some (bushTri (shift c (v ++ [bushLetter c v]))) else none

/-- **`thm:shape-iid`**, the shape at a copy: the chain of `w` in the skeleton
together with the bushes of its neck vertices. -/
noncomputable def shapeAt (c : Amb → ℕ) (w : Word) : Shape where
  necks := splitDepth c (entryV c w)
  dec i := decAt c (neckRay c (entryV c w) i)

@[simp] lemma shapeAt_necks (c : Amb → ℕ) (w : Word) :
    (shapeAt c w).necks = splitDepth c (entryV c w) := rfl

lemma shapeAt_decs (c : Amb → ℕ) (w : Word) :
    (shapeAt c w).decs
      = List.ofFn fun i : Fin (splitDepth c (entryV c w)) ↦
          decAt c (neckRay c (entryV c w) i) := rfl

/-- **The letter map of a sample**: at a neck vertex carrying a bush the bush sits at
`false` and the neck at `true`, as in the realisation of a shape; everywhere else
`false` is the child `0` and `true` the child `1`. -/
noncomputable def sampleLetter (c : Amb → ℕ) (v : Amb) (b : Bool) : Fin 2 :=
  if skeletonDegree (shift c v) = 1 ∧ c v = 2 then (if b then neckLetter c v else bushLetter c v)
  else letterOf b

lemma sampleLetter_injective (c : Amb → ℕ) (v : Amb) :
    Function.Injective (sampleLetter c v) := by
  intro b b' h
  rw [sampleLetter, sampleLetter] at h
  by_cases hcase : skeletonDegree (shift c v) = 1 ∧ c v = 2
  · rw [if_pos hcase, if_pos hcase] at h
    cases b <;> cases b' <;> simp_all [bushLetter_ne_neckLetter c v,
      (bushLetter_ne_neckLetter c v).symm]
  · rw [if_neg hcase, if_neg hcase] at h
    exact letterOf_injective h

/-- **The sample read from the index tree**: the address translation along the letter
map of the sample. -/
noncomputable def transSample (c : Amb → ℕ) : Word → Amb := transWith (sampleLetter c)

lemma transSample_injective (c : Amb → ℕ) : Function.Injective (transSample c) :=
  transWith_injective (sampleLetter_injective c)

lemma transSample_concat (c : Amb → ℕ) (a : Word) (b : Bool) :
    transSample c (a ++ [b]) = transSample c a ++ [sampleLetter c (transSample c a) b] :=
  transWith_concat a b

/-! ### The addresses of a realisation -/

/-- The neck address reads the decorations: an undecorated vertex passes the neck to
`false` and a decorated one to `true`. -/
lemma Shape.neckAddr_eq_map (l : List (Option Tri)) :
    Shape.neckAddr l = l.map (fun o ↦ o.isSome) := by
  induction l with
  | nil => rfl
  | cons o l ih => cases o <;> simp [ih]

/-- The neck addresses of the initial segments are the prefixes of the neck address. -/
lemma Shape.neckAddr_take (l : List (Option Tri)) (i : ℕ) :
    Shape.neckAddr (l.take i) = (Shape.neckAddr l).take i := by
  rw [Shape.neckAddr_eq_map, Shape.neckAddr_eq_map, List.map_take]

/-- **The children of an undecorated neck vertex**: the neck continues at `false` and
nothing else hangs there. -/
lemma Shape.isAddr_neckAddr_concat_none : ∀ (l : List (Option Tri)) (i : ℕ),
    l[i]? = some none → ∀ b : Bool,
      ((Shape.realiseAux l).IsAddr (Shape.neckAddr (l.take i) ++ [b]) ↔ b = false)
  | [], i, hi, _ => by simp at hi
  | o :: l, 0, ho, b => by
      have : o = none := by simpa using ho
      subst this
      cases b <;> simp [Shape.realiseAux]
  | o :: l, i + 1, ho, b => by
      have ho' : l[i]? = some none := by simpa using ho
      have ih := Shape.isAddr_neckAddr_concat_none l i ho' b
      cases o with
      | none => simpa [Shape.realiseAux] using ih
      | some d => simpa [Shape.realiseAux] using ih

/-- **The children of a decorated neck vertex**: the bush hangs at `false` and the neck
continues at `true`. -/
lemma Shape.isAddr_neckAddr_concat_some : ∀ (l : List (Option Tri)) (i : ℕ) (t : Tri),
    l[i]? = some (some t) → ∀ b : Bool,
      (Shape.realiseAux l).IsAddr (Shape.neckAddr (l.take i) ++ [b])
  | [], i, _, hi, _ => by simp at hi
  | o :: l, 0, t, ho, b => by
      have : o = some t := by simpa using ho
      subst this
      cases b <;> simp [Shape.realiseAux]
  | o :: l, i + 1, t, ho, b => by
      have ho' : l[i]? = some (some t) := by simpa using ho
      have ih := Shape.isAddr_neckAddr_concat_some l i t ho' b
      cases o with
      | none => simpa [Shape.realiseAux] using ih
      | some d => simpa [Shape.realiseAux] using ih

/-- **The bush of a neck vertex**: the addresses below the bush letter of the `i`-th
neck vertex are the addresses of its decoration. -/
lemma Shape.isAddr_bush : ∀ (l : List (Option Tri)) (i : ℕ) (t : Tri),
    l[i]? = some (some t) → ∀ z : Word,
      ((Shape.realiseAux l).IsAddr (Shape.neckAddr (l.take i) ++ false :: z) ↔ t.IsAddr z)
  | [], i, _, hi, _ => by simp at hi
  | o :: l, 0, t, ho, z => by
      have : o = some t := by simpa using ho
      subst this
      simp [Shape.realiseAux]
  | o :: l, i + 1, t, ho, z => by
      have ho' : l[i]? = some (some t) := by simpa using ho
      have ih := Shape.isAddr_bush l i t ho' z
      cases o with
      | none => simpa [Shape.realiseAux] using ih
      | some d => simpa [Shape.realiseAux] using ih

/-- **The addresses of a realisation**: every vertex is a neck vertex or a vertex of the
bush of a neck vertex. -/
lemma Shape.isAddr_cases : ∀ (l : List (Option Tri)) {p : Word},
    (Shape.realiseAux l).IsAddr p →
      (∃ i, i ≤ l.length ∧ p = Shape.neckAddr (l.take i)) ∨
      (∃ i, ∃ t : Tri, l[i]? = some (some t) ∧
        ∃ z, t.IsAddr z ∧ p = Shape.neckAddr (l.take i) ++ false :: z)
  | [], p, hp => by
      rw [Tri.eq_nil_of_isAddr_leaf hp]
      exact Or.inl ⟨0, Nat.zero_le _, rfl⟩
  | o :: l, [], _ => Or.inl ⟨0, Nat.zero_le _, rfl⟩
  | none :: l, b :: p, hp => by
      cases b with
      | true => exact absurd hp (by simp [Shape.realiseAux])
      | false =>
          have hp' : (Shape.realiseAux l).IsAddr p := by simpa [Shape.realiseAux] using hp
          rcases Shape.isAddr_cases l hp' with ⟨i, hi, rfl⟩ | ⟨i, t, ht, z, hz, rfl⟩
          · exact Or.inl ⟨i + 1, by simpa using hi, by simp⟩
          · exact Or.inr ⟨i + 1, t, by simpa using ht, z, hz, by simp⟩
  | some d :: l, b :: p, hp => by
      cases b with
      | false =>
          have hp' : d.IsAddr p := by simpa [Shape.realiseAux] using hp
          exact Or.inr ⟨0, d, by simp, p, hp', by simp⟩
      | true =>
          have hp' : (Shape.realiseAux l).IsAddr p := by simpa [Shape.realiseAux] using hp
          rcases Shape.isAddr_cases l hp' with ⟨i, hi, rfl⟩ | ⟨i, t, ht, z, hz, rfl⟩
          · exact Or.inl ⟨i + 1, by simpa using hi, by simp⟩
          · exact Or.inr ⟨i + 1, t, by simpa using ht, z, hz, by simp⟩

/-! ### The dictionary between the copies and the sample -/

/-- A vertex of a finite subtree founds a finite subtree. -/
lemma not_survives_shift_of_mem {d : Amb → ℕ} {r : Amb} (hfin : ¬ Survives d)
    (hr : r ∈ sample d) : ¬ Survives (shift d r) := by
  intro hs
  have hs' : (sample (shift d r) : Set Amb).Infinite := hs
  have hsub : (fun z : Amb ↦ r ++ z) '' (sample (shift d r) : Set Amb)
      ⊆ (sample d : Set Amb) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, BranchingProcess.append_mem_sample_iff]
    exact ⟨hr, hz⟩
  have himg := hs'.image (f := fun z : Amb ↦ r ++ z)
    (fun z _ z' _ h ↦ List.append_cancel_left h)
  exact hfin (himg.mono hsub)

/-- Inside a bush the letter map is the plain one: no vertex of a finite subtree has a
surviving child, so none of them carries a neck. -/
lemma sampleLetter_of_not_survives {v : Amb} (h : ¬ Survives (shift c v)) (b : Bool) :
    sampleLetter c v b = letterOf b := by
  have hdeg : skeletonDegree (shift c v) = 0 := by
    by_contra hne
    exact h (BranchingProcess.survives_iff_skeletonDegree_ne_zero.mpr hne)
  rw [sampleLetter, if_neg (by rw [hdeg]; simp)]

/-- **The translation inside a bush**: below a dying vertex the translation reads the
letters one for one. -/
lemma transSample_append_letters {a : Word} {y : Amb} (hay : transSample c a = y)
    (hfin : ¬ Survives (shift c y)) :
    ∀ z : Word, letters z ∈ sample (shift c y) → transSample c (a ++ z) = y ++ letters z := by
  intro z
  induction z using List.reverseRecOn with
  | nil => simpa using hay
  | append_singleton z b ih =>
      intro hz
      have hz' : letters z ∈ sample (shift c y) := by
        refine BranchingProcess.Subtree.mem_of_prefix ?_ hz
        rw [letters_append]
        exact List.prefix_append _ _
      have hstep := ih hz'
      have hnot : ¬ Survives (shift c (y ++ letters z)) := by
        rw [← shift_shift]
        exact not_survives_shift_of_mem hfin hz'
      rw [← List.append_assoc, transSample_concat, hstep,
        sampleLetter_of_not_survives hnot, letters_append]
      simp

/-- The decorations of a shape read off the neck ray. -/
lemma shapeAt_decs_length (c : Amb → ℕ) (w : Word) :
    (shapeAt c w).decs.length = splitDepth c (entryV c w) := by
  rw [Shape.decs_length, shapeAt_necks]

lemma shapeAt_decs_getElem? (c : Amb → ℕ) (w : Word) {i : ℕ}
    (hi : i < splitDepth c (entryV c w)) :
    (shapeAt c w).decs[i]? = some (decAt c (neckRay c (entryV c w) i)) := by
  have hlen : i < (shapeAt c w).decs.length := by rw [shapeAt_decs_length]; exact hi
  rw [List.getElem?_eq_getElem hlen]
  congr 1
  simp [shapeAt_decs]

/-- One further decoration extends the neck address by the bit that names it. -/
lemma Shape.neckAddr_take_succ {l : List (Option Tri)} {i : ℕ} {o : Option Tri}
    (h : l[i]? = some o) :
    Shape.neckAddr (l.take (i + 1)) = Shape.neckAddr (l.take i) ++ [o.isSome] := by
  have hl : l.take (i + 1) = l.take i ++ [o] := by rw [List.take_add_one, h]; rfl
  rw [hl, Shape.neckAddr_eq_map, Shape.neckAddr_eq_map, List.map_append]
  rfl

/-- **The neck of a copy is the chain of its entry**: the translation carries the neck
address of the shape at `w` to the neck ray of the entry vertex. -/
lemma transSample_neck (hc : IsBushySample c) (w : Word)
    (hbase : transSample c (copyAddr (shapeAt c) w) = entryV c w) :
    ∀ i, i ≤ splitDepth c (entryV c w) →
      transSample c (copyAddr (shapeAt c) w ++ Shape.neckAddr ((shapeAt c w).decs.take i))
        = neckRay c (entryV c w) i := by
  obtain ⟨hmem, hsurv⟩ := entryV_mem_skeleton hc w
  intro i
  induction i with
  | zero => intro _; simpa using hbase
  | succ i ih =>
      intro hi
      have hi' : i < splitDepth c (entryV c w) := by omega
      set u := neckRay c (entryV c w) i with hu
      have husurv : Survives (shift c u) := survives_neckRay hsurv i
      have hdeg : skeletonDegree (shift c u) = 1 := splitDepth_min hsurv hi'
      have hget := shapeAt_decs_getElem? c w hi'
      rw [Shape.neckAddr_take_succ hget, ← List.append_assoc, transSample_concat,
        ih (by omega)]
      have hletter : sampleLetter c u (decAt c u).isSome = neckLetter c u := by
        by_cases h2 : c u = 2
        · rw [decAt, if_pos h2]
          simp only [Option.isSome_some]
          rw [sampleLetter, if_pos ⟨hdeg, h2⟩]
          simp
        · rw [decAt, if_neg h2]
          simp only [Option.isSome_none]
          rw [sampleLetter, if_neg (by tauto), letterOf_false,
            neckLetter_eq_zero husurv h2 (hc.offspring u)]
      rw [hletter, neckRay_succ]

/-- **The entry of a copy**: the translation carries the planting of the copy `w` to the
entry vertex of its chain. -/
lemma transSample_copyAddr (hc : IsBushySample c) (w : Word) :
    transSample c (copyAddr (shapeAt c) w) = entryV c w := by
  induction w using List.reverseRecOn with
  | nil => simp [transSample]
  | append_singleton w j ih =>
      obtain ⟨hmem, hsurv⟩ := entryV_mem_skeleton hc w
      set v := entryV c w with hv
      set n := splitDepth c v with hn
      have hfull : (shapeAt c w).decs.take n = (shapeAt c w).decs := by
        rw [List.take_of_length_le]
        rw [shapeAt_decs_length]
      have hneck := transSample_neck hc w ih n le_rfl
      rw [hfull] at hneck
      have hdeg : skeletonDegree (shift c (neckRay c v n)) = 2 := splitDepth_spec hc hsurv
      rw [copyAddr_concat, transSample_concat, hneck, entryV_concat,
        sampleLetter, if_neg (by rw [hdeg]; simp)]

/-- **The bush of a neck vertex**: the translation carries the bush address of the
`i`-th neck vertex of the copy `w` to the dying subtree there. -/
lemma transSample_bush (hc : IsBushySample c) (w : Word) {i : ℕ}
    (hi : i < splitDepth c (entryV c w)) (h2 : c (neckRay c (entryV c w) i) = 2)
    {z : Word}
    (hz : letters z ∈ sample (shift c (neckRay c (entryV c w) i ++
      [bushLetter c (neckRay c (entryV c w) i)]))) :
    transSample c (copyAddr (shapeAt c) w ++ Shape.neckAddr ((shapeAt c w).decs.take i)
        ++ false :: z)
      = neckRay c (entryV c w) i ++ [bushLetter c (neckRay c (entryV c w) i)] ++ letters z := by
  obtain ⟨hmem, hsurv⟩ := entryV_mem_skeleton hc w
  set u := neckRay c (entryV c w) i with hu
  have husurv : Survives (shift c u) := survives_neckRay hsurv i
  have hdeg : skeletonDegree (shift c u) = 1 := splitDepth_min hsurv hi
  have hneck := transSample_neck hc w (transSample_copyAddr hc w) i (le_of_lt hi)
  have hstep : transSample c (copyAddr (shapeAt c) w
      ++ Shape.neckAddr ((shapeAt c w).decs.take i) ++ [false]) = u ++ [bushLetter c u] := by
    rw [transSample_concat, hneck, sampleLetter, if_pos ⟨hdeg, h2⟩]
    simp [hu]
  have hfin : ¬ Survives (shift c (u ++ [bushLetter c u])) := not_survives_bush husurv hdeg h2
  have := transSample_append_letters hstep hfin z hz
  rw [List.append_assoc _ [false] z] at this
  simpa using this

/-! ### The vertices of the assembly and the vertices of the sample -/

/-- **The children of a vertex of the assembly**: inside a copy they are the children of
the realisation, and the exit of a copy is joined to the entries of the two copies
below it. -/
lemma Assembly.exists_code_concat_iff {σ : Word → Shape} (x : Assembly σ) (b : Bool) :
    (∃ y : Assembly σ, Assembly.code y = Assembly.code x ++ [b])
      ↔ (x.vert.1 = Shape.neckAddr (σ x.copy).decs
          ∨ (Shape.realiseAux (σ x.copy).decs).IsAddr (x.vert.1 ++ [b])) := by
  obtain ⟨u, p, hp⟩ := x
  dsimp only
  constructor
  · rintro ⟨y, hy⟩
    have hlen : (Assembly.code y).length
        = (Assembly.code (⟨u, p, hp⟩ : Assembly σ)).length + 1 := by
      rw [hy]; simp
    have hd1 : treeDist (Assembly.code (⟨u, p, hp⟩ : Assembly σ)) (Assembly.code y) = 1 := by
      rw [hy, treeDist_of_prefix (List.prefix_append _ _)]
      simp
    have hadj : Assembly.Adj (⟨u, p, hp⟩ : Assembly σ) y := by
      refine (Assembly.dist_eq_one_iff_adj _ y).mp ?_
      rw [Assembly.dist_code, hd1]
      norm_num
    obtain ⟨v, q, hq⟩ := y
    rcases hadj with ⟨hcopy, hor⟩ | ⟨j, hj, hglue, _⟩ | ⟨j, hj, hglue, hnil⟩
    · dsimp only at hcopy
      subst hcopy
      rcases hor with ⟨b', hb'⟩ | ⟨b', hb'⟩
      · dsimp only at hb'
        subst hb'
        have hcode : Assembly.code (⟨u, p ++ [b'], hq⟩ : Assembly σ)
            = Assembly.code (⟨u, p, hp⟩ : Assembly σ) ++ [b'] := by
          simp only [Assembly.code, List.append_assoc]
        rw [hcode] at hy
        have : b' = b := by
          have := List.append_cancel_left hy
          simpa using this
        subst this
        exact Or.inr hq
      · exfalso
        dsimp only at hb'
        simp only [Assembly.code, List.length_append, hb'] at hlen
        simp only [List.length_singleton] at hlen
        omega
    · exact Or.inl hglue
    · exfalso
      dsimp only at hj hglue hnil
      subst hj
      simp only [Assembly.code, copyAddr_concat, List.length_append, hglue, hnil] at hlen
      simp only [List.length_singleton, List.length_nil] at hlen
      omega
  · rintro (hexit | hchild)
    · refine ⟨⟨u ++ [b], [], by simp⟩, ?_⟩
      simp only [Assembly.code, copyAddr_concat, List.append_nil, hexit]
    · exact ⟨⟨u, p ++ [b], hchild⟩, by simp only [Assembly.code, List.append_assoc]⟩

/-- **`thm:shape-iid`**, the dictionary: the translation carries a vertex of the
assembly of the shapes to a vertex of the sample, and the children of the two agree. -/
lemma transSample_code_spec (hc : IsBushySample c) (x : Assembly (shapeAt c)) :
    transSample c (Assembly.code x) ∈ sample c ∧
      ∀ b : Bool, ((x.vert.1 = Shape.neckAddr (shapeAt c x.copy).decs
          ∨ (Shape.realiseAux (shapeAt c x.copy).decs).IsAddr (x.vert.1 ++ [b]))
        ↔ (sampleLetter c (transSample c (Assembly.code x)) b : ℕ)
            < c (transSample c (Assembly.code x))) := by
  obtain ⟨w, p, hp⟩ := x
  dsimp only
  simp only [Assembly.code]
  obtain ⟨hmem0, hsurv0⟩ := entryV_mem_skeleton hc w
  have hllen : (shapeAt c w).decs.length = splitDepth c (entryV c w) := shapeAt_decs_length c w
  rcases Shape.isAddr_cases (shapeAt c w).decs hp with ⟨i, hi, rfl⟩ | ⟨i, t, hget, z, hz, rfl⟩
  · -- a neck vertex of the copy
    rw [hllen] at hi
    have hneck := transSample_neck hc w (transSample_copyAddr hc w) i hi
    rw [hneck]
    set u := neckRay c (entryV c w) i with hu
    have husurv : Survives (shift c u) := survives_neckRay hsurv0 i
    have humem : u ∈ sample c := mem_sample_neckRay hmem0 hsurv0 i
    refine ⟨humem, fun b ↦ ?_⟩
    rcases eq_or_lt_of_le hi with heq | hlt
    · -- the exit of the copy: a split, both letters available
      have hfull : (shapeAt c w).decs.take i = (shapeAt c w).decs :=
        List.take_of_length_le (by rw [hllen]; omega)
      have hdeg : skeletonDegree (shift c u) = 2 := by
        rw [hu, heq]
        exact splitDepth_spec hc hsurv0
      have h2 : c u = 2 := eq_two_of_skeletonDegree_two hc hdeg
      have hlt2 : (sampleLetter c u b : ℕ) < c u := by
        have := (sampleLetter c u b).isLt
        omega
      simp only [hlt2, iff_true]
      exact Or.inl (congrArg Shape.neckAddr hfull)
    · -- an interior neck vertex
      have hdeg : skeletonDegree (shift c u) = 1 := splitDepth_min hsurv0 hlt
      have hne : Shape.neckAddr ((shapeAt c w).decs.take i) ≠ Shape.neckAddr (shapeAt c w).decs := by
        intro heq
        have := congrArg List.length heq
        rw [Shape.neckAddr_length, Shape.neckAddr_length, List.length_take, hllen] at this
        omega
      have hgeti : (shapeAt c w).decs[i]? = some (decAt c u) := shapeAt_decs_getElem? c w hlt
      by_cases h2 : c u = 2
      · have hsome : (shapeAt c w).decs[i]?
            = some (some (bushTri (shift c (u ++ [bushLetter c u])))) := by
          rw [hgeti, decAt, if_pos h2]
        have hchild := Shape.isAddr_neckAddr_concat_some (shapeAt c w).decs i _ hsome b
        have hlt2 : (sampleLetter c u b : ℕ) < c u := by
          have := (sampleLetter c u b).isLt
          omega
        simp [hchild, hlt2]
      · have hnone : (shapeAt c w).decs[i]? = some none := by rw [hgeti, decAt, if_neg h2]
        have hchild := Shape.isAddr_neckAddr_concat_none (shapeAt c w).decs i hnone b
        have h1 : c u = 1 := by
          rcases eq_one_or_two_of_survives hc husurv with h | h
          · exact h
          · exact absurd h h2
        have hletter : sampleLetter c u b = letterOf b := by
          rw [sampleLetter, if_neg (by tauto)]
        rw [hchild, hletter, h1]
        simp only [hne, false_or]
        cases b <;> simp
  · -- a vertex of the bush of a neck vertex
    have hilt : i < splitDepth c (entryV c w) := by
      rw [← hllen]
      exact List.getElem?_eq_some_iff.mp hget |>.1
    set u := neckRay c (entryV c w) i with hu
    have husurv : Survives (shift c u) := survives_neckRay hsurv0 i
    have humem : u ∈ sample c := mem_sample_neckRay hmem0 hsurv0 i
    have hdeg : skeletonDegree (shift c u) = 1 := splitDepth_min hsurv0 hilt
    have hgeti : (shapeAt c w).decs[i]? = some (decAt c u) := shapeAt_decs_getElem? c w hilt
    have hdec : decAt c u = some t := by
      rw [hgeti] at hget
      simpa using hget
    have h2 : c u = 2 := by
      by_contra hne
      rw [decAt, if_neg hne] at hdec
      simp at hdec
    have hteq : t = bushTri (shift c (u ++ [bushLetter c u])) := by
      rw [decAt, if_pos h2] at hdec
      simpa using hdec.symm
    set y := u ++ [bushLetter c u] with hy
    have hymem : y ∈ sample c :=
      BranchingProcess.mem_sample_append_singleton.mpr ⟨humem, bushLetter_lt h2⟩
    have hfin : ¬ Survives (shift c y) := not_survives_bush husurv hdeg h2
    have hbush : ∀ r : Word, t.IsAddr r ↔ letters r ∈ sample (shift c y) := by
      intro r
      rw [hteq]
      exact isAddr_bushTri (fun _ ↦ hc.offspring _) hfin r
    have hzs : letters z ∈ sample (shift c y) := (hbush z).mp hz
    have htrans := transSample_bush hc w hilt h2 hzs
    rw [← List.append_assoc, htrans]
    have hvmem : y ++ letters z ∈ sample c := by
      rw [BranchingProcess.append_mem_sample_iff]
      exact ⟨hymem, hzs⟩
    refine ⟨hvmem, fun b ↦ ?_⟩
    have hnotsurv : ¬ Survives (shift c (y ++ letters z)) := by
      rw [← shift_shift]
      exact not_survives_shift_of_mem hfin hzs
    have hletter : sampleLetter c (y ++ letters z) b = letterOf b :=
      sampleLetter_of_not_survives hnotsurv b
    have hne : Shape.neckAddr ((shapeAt c w).decs.take i) ++ false :: z
        ≠ Shape.neckAddr (shapeAt c w).decs := by
      intro heq
      have h1 : Shape.neckAddr ((shapeAt c w).decs.take i) ++ [false]
          <+: Shape.neckAddr (shapeAt c w).decs := by
        rw [← heq]
        exact ⟨z, by simp⟩
      have h2' : Shape.neckAddr ((shapeAt c w).decs.take i) ++ [true]
          <+: Shape.neckAddr (shapeAt c w).decs := by
        have hstep : Shape.neckAddr ((shapeAt c w).decs.take (i + 1))
            = Shape.neckAddr ((shapeAt c w).decs.take i) ++ [true] := by
          rw [Shape.neckAddr_take_succ hget]
          rfl
        rw [← hstep, Shape.neckAddr_take]
        exact List.take_prefix _ _
      have := prefix_eq_of_length h1 h2' (by simp)
      simp at this
    have hstep : (Shape.neckAddr ((shapeAt c w).decs.take i) ++ false :: z) ++ [b]
        = Shape.neckAddr ((shapeAt c w).decs.take i) ++ false :: (z ++ [b]) := by
      simp
    rw [hstep, Shape.isAddr_bush (shapeAt c w).decs i t hget (z ++ [b]), hbush,
      letters_append, hletter]
    simp only [hne, false_or, letters_cons, letters_nil]
    rw [BranchingProcess.mem_sample_append_singleton]
    constructor
    · rintro ⟨-, hlt⟩
      rw [shift_apply] at hlt
      exact hlt
    · intro hlt
      exact ⟨hzs, by rw [shift_apply]; exact hlt⟩

/-! ### The sample is the assembly of its shapes -/

/-- Every vertex of the sample is the translation of a vertex of the assembly: the
chains of the skeleton and their bushes exhaust the sample. -/
lemma exists_code_transSample (hc : IsBushySample c) : ∀ v : Amb, v ∈ sample c →
    ∃ x : Assembly (shapeAt c), transSample c (Assembly.code x) = v := by
  intro v
  induction v using List.reverseRecOn with
  | nil =>
      intro _
      exact ⟨⟨[], [], by simp⟩, by simp [Assembly.code, transSample]⟩
  | append_singleton v j ih =>
      intro hv
      obtain ⟨hv', hj⟩ := BranchingProcess.mem_sample_append_singleton.mp hv
      obtain ⟨x, hx⟩ := ih hv'
      obtain ⟨b, hb⟩ : ∃ b : Bool, sampleLetter c v b = j := by
        have hbij := (Fintype.bijective_iff_injective_and_card (sampleLetter c v)).mpr
          ⟨sampleLetter_injective c v, by simp⟩
        exact hbij.2 j
      have hspec := (transSample_code_spec hc x).2 b
      rw [hx] at hspec
      have hchild : (sampleLetter c v b : ℕ) < c v := by rw [hb]; exact hj
      obtain ⟨y, hy⟩ := (Assembly.exists_code_concat_iff x b).mpr (hspec.mpr hchild)
      exact ⟨y, by rw [hy, transSample_concat, hx, hb]⟩

/-- **`thm:shape-iid`, the last clause**: a bushy sample is isometric to the assembly
of its own shapes.  The isometry is the address translation: it reads the letters of the
assembly one for one, sending the neck of a copy to the chain of its entry vertex and
the decorations to the bushes hanging off that chain, so it preserves lengths and the
prefix order, and with them every distance. -/
theorem assembly_isometric_sample (hc : IsBushySample c) :
    ∃ Φ : Assembly (shapeAt c) → {v : Amb // v ∈ sample c}, Function.Bijective Φ ∧
      ∀ x y : Assembly (shapeAt c),
        (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y := by
  refine ⟨fun x ↦ ⟨transSample c (Assembly.code x), (transSample_code_spec hc x).1⟩,
    ⟨?_, ?_⟩, ?_⟩
  · intro x y h
    exact Assembly.code_injective (transSample_injective c (congrArg Subtype.val h))
  · rintro ⟨v, hv⟩
    obtain ⟨x, hx⟩ := exists_code_transSample hc v hv
    exact ⟨x, Subtype.ext hx⟩
  · intro x y
    rw [Assembly.dist_code]
    exact_mod_cast transWith_treeDist (sampleLetter_injective c) _ _

/-! ### The shapes as a measurable field -/

/-- **A countably valued function of the offspring field, presented by its fibres.**  The
values below are words, finite trees and shapes, none of which carries a measurable
structure, so measurability is stated as the events `{c | f c = x}` throughout. -/
def FibreMeasurable {X : Type*} (f : (Amb → ℕ) → X) : Prop :=
  ∀ x : X, MeasurableSet {c : Amb → ℕ | f c = x}

lemma FibreMeasurable.congr {X : Type*} {f g : (Amb → ℕ) → X} (hf : FibreMeasurable f)
    (h : ∀ c, f c = g c) : FibreMeasurable g := by
  intro x
  have he : {c : Amb → ℕ | g c = x} = {c : Amb → ℕ | f c = x} := by
    ext c
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h c]
  rw [he]
  exact hf x

lemma fibreMeasurable_const {X : Type*} (x₀ : X) : FibreMeasurable (fun _ : Amb → ℕ ↦ x₀) := by
  intro x
  by_cases h : x₀ = x
  · have he : {c : Amb → ℕ | x₀ = x} = Set.univ := by ext c; simp [h]
    rw [he]
    exact MeasurableSet.univ
  · have he : {c : Amb → ℕ | x₀ = x} = ∅ := by ext c; simp [h]
    rw [he]
    exact MeasurableSet.empty

/-- A countable family of values is an event. -/
lemma FibreMeasurable.preimage {X : Type*} [Countable X] {f : (Amb → ℕ) → X}
    (hf : FibreMeasurable f) (s : Set X) : MeasurableSet {c : Amb → ℕ | f c ∈ s} := by
  have he : {c : Amb → ℕ | f c ∈ s} = ⋃ x ∈ s, {c : Amb → ℕ | f c = x} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun hc ↦ ⟨f c, hc, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact hx⟩
  rw [he]
  exact MeasurableSet.biUnion (Set.to_countable _) fun x _ ↦ hf x

lemma FibreMeasurable.map {X Y : Type*} [Countable X] {g : (Amb → ℕ) → X}
    (hg : FibreMeasurable g) (φ : X → Y) : FibreMeasurable (fun c ↦ φ (g c)) := fun y ↦ by
  have he : {c : Amb → ℕ | φ (g c) = y} = {c : Amb → ℕ | g c ∈ {x : X | φ x = y}} := rfl
  rw [he]
  exact hg.preimage _

lemma FibreMeasurable.prod {X Y : Type*} {f : (Amb → ℕ) → X} {g : (Amb → ℕ) → Y}
    (hf : FibreMeasurable f) (hg : FibreMeasurable g) :
    FibreMeasurable (fun c ↦ (f c, g c)) := by
  rintro ⟨x, y⟩
  have he : {c : Amb → ℕ | (f c, g c) = (x, y)}
      = {c : Amb → ℕ | f c = x} ∩ {c : Amb → ℕ | g c = y} := by
    ext c
    simp [Prod.ext_iff]
  rw [he]
  exact (hf x).inter (hg y)

/-- Substituting a countably valued function into a family keeps the fibres events. -/
lemma FibreMeasurable.comp {X Y : Type*} [Countable X] {g : (Amb → ℕ) → X}
    {h : X → (Amb → ℕ) → Y} (hg : FibreMeasurable g) (hh : ∀ x, FibreMeasurable (h x)) :
    FibreMeasurable (fun c ↦ h (g c) c) := by
  intro y
  have he : {c : Amb → ℕ | h (g c) c = y}
      = ⋃ x : X, ({c : Amb → ℕ | g c = x} ∩ {c : Amb → ℕ | h x c = y}) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun hc ↦ ⟨g c, rfl, hc⟩, by rintro ⟨x, hx, hc⟩; rw [hx]; exact hc⟩
  rw [he]
  exact MeasurableSet.iUnion fun x ↦ (hg x).inter (hh x y)

lemma FibreMeasurable.pi {X ι : Type*} [Countable ι] {g : ι → (Amb → ℕ) → X}
    (hg : ∀ i, FibreMeasurable (g i)) : FibreMeasurable (fun c ↦ fun i ↦ g i c) := by
  intro f
  have he : {c : Amb → ℕ | (fun i ↦ g i c) = f} = ⋂ i, {c : Amb → ℕ | g i c = f i} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, funext_iff]
  rw [he]
  exact MeasurableSet.iInter fun i ↦ hg i (f i)

/-- The first index at which a family of events occurs is countably valued and its
fibres are events. -/
lemma measurableSet_sInf_eq {P : ℕ → Set (Amb → ℕ)} (hP : ∀ k, MeasurableSet (P k)) (n : ℕ) :
    MeasurableSet {c : Amb → ℕ | sInf {k | c ∈ P k} = n} := by
  have hle : ∀ (c : Amb → ℕ) (k : ℕ), c ∈ P k → sInf {k | c ∈ P k} ≤ k :=
    fun c k hk ↦ Nat.sInf_le (show k ∈ {k | c ∈ P k} from hk)
  have hmem : ∀ (c : Amb → ℕ) (k : ℕ), c ∈ P k → c ∈ P (sInf {k | c ∈ P k}) :=
    fun c k hk ↦ Nat.sInf_mem (s := {k | c ∈ P k}) ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have he : {c : Amb → ℕ | sInf {k | c ∈ P k} = 0} = P 0 ∪ ⋂ k : ℕ, (P k)ᶜ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · intro h
        by_cases hex : ∃ k, c ∈ P k
        · obtain ⟨k, hk⟩ := hex
          have hc := hmem c k hk
          rw [h] at hc
          exact Or.inl hc
        · exact Or.inr fun k hk ↦ hex ⟨k, hk⟩
      · rintro (h0 | hall)
        · exact Nat.le_zero.mp (hle c 0 h0)
        · have hempty : {k | c ∈ P k} = ∅ := by ext k; simp [hall k]
          rw [hempty, Nat.sInf_empty]
    rw [he]
    exact (hP 0).union (MeasurableSet.iInter fun k ↦ (hP k).compl)
  · have he : {c : Amb → ℕ | sInf {k | c ∈ P k} = n}
        = P n ∩ ⋂ k ∈ Finset.range n, (P k)ᶜ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Finset.mem_range]
      constructor
      · intro h
        have hex : ∃ k, c ∈ P k := by
          by_contra hno
          have hempty : {k | c ∈ P k} = ∅ := by
            ext k
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            exact fun hk ↦ hno ⟨k, hk⟩
          rw [hempty, Nat.sInf_empty] at h
          omega
        obtain ⟨k, hk⟩ := hex
        refine ⟨by rw [← h]; exact hmem c k hk, fun j hj hjc ↦ ?_⟩
        have := hle c j hjc
        omega
      · rintro ⟨hn', hmin⟩
        refine le_antisymm (hle c n hn') ?_
        by_contra hlt
        rw [not_le] at hlt
        exact hmin _ hlt (hmem c n hn')
    rw [he]
    exact (hP n).inter (MeasurableSet.biInter (Set.to_countable _) fun k _ ↦ (hP k).compl)

/-- The field shifted to a vertex is a measurable function of the field. -/
lemma measurable_shiftMap (v : Amb) : Measurable (fun c : Amb → ℕ ↦ shift c v) :=
  measurable_pi_lambda _ fun w ↦ measurable_pi_apply (v ++ w)

lemma fibreMeasurable_coord (v : Amb) : FibreMeasurable (fun c : Amb → ℕ ↦ c v) := by
  intro j
  have he : {c : Amb → ℕ | c v = j} = (fun c : Amb → ℕ ↦ c v) ⁻¹' {j} := rfl
  rw [he]
  exact measurable_pi_apply v MeasurableSet.of_discrete

lemma fibreMeasurable_skeletonDegree (v : Amb) :
    FibreMeasurable (fun c ↦ skeletonDegree (shift c v)) := fun k ↦
  measurable_shiftMap v (BranchingProcess.measurableSet_skeletonDegree_eq k)

/-- The letter continuing the neck is measurable: it is read off one survival event. -/
lemma fibreMeasurable_neckLetter (v : Amb) : FibreMeasurable (fun c ↦ neckLetter c v) := by
  have hA : MeasurableSet {c : Amb → ℕ | (0 : Fin 2) ∈ survivors (shift c v)} :=
    measurable_shiftMap v (BranchingProcess.measurableSet_mem_survivors 0)
  intro i
  by_cases hi : i = 0
  · subst hi
    have he : {c : Amb → ℕ | neckLetter c v = 0}
        = {c : Amb → ℕ | (0 : Fin 2) ∈ survivors (shift c v)} := by
      ext c
      by_cases h : (0 : Fin 2) ∈ survivors (shift c v) <;> simp [neckLetter, h]
    rw [he]
    exact hA
  · have hi1 : i = 1 := by
      have hlt := i.isLt
      have hne : (i : ℕ) ≠ 0 := fun h ↦ hi (Fin.ext h)
      exact Fin.ext (by omega)
    subst hi1
    have he : {c : Amb → ℕ | neckLetter c v = 1}
        = {c : Amb → ℕ | (0 : Fin 2) ∈ survivors (shift c v)}ᶜ := by
      ext c
      by_cases h : (0 : Fin 2) ∈ survivors (shift c v) <;> simp [neckLetter, h]
    rw [he]
    exact hA.compl

/-- The letter of the bush is measurable, by the same survival event. -/
lemma fibreMeasurable_bushLetter (v : Amb) : FibreMeasurable (fun c ↦ bushLetter c v) := by
  have hA : MeasurableSet {c : Amb → ℕ | (0 : Fin 2) ∈ survivors (shift c v)} :=
    measurable_shiftMap v (BranchingProcess.measurableSet_mem_survivors 0)
  intro i
  by_cases hi : i = 1
  · subst hi
    have he : {c : Amb → ℕ | bushLetter c v = 1}
        = {c : Amb → ℕ | (0 : Fin 2) ∈ survivors (shift c v)} := by
      ext c
      by_cases h : (0 : Fin 2) ∈ survivors (shift c v) <;> simp [bushLetter, h]
    rw [he]
    exact hA
  · have hi0 : i = 0 := by
      have hlt := i.isLt
      have hne : (i : ℕ) ≠ 1 := fun h ↦ hi (Fin.ext h)
      exact Fin.ext (by omega)
    subst hi0
    have he : {c : Amb → ℕ | bushLetter c v = 0}
        = {c : Amb → ℕ | (0 : Fin 2) ∈ survivors (shift c v)}ᶜ := by
      ext c
      by_cases h : (0 : Fin 2) ∈ survivors (shift c v) <;> simp [bushLetter, h]
    rw [he]
    exact hA.compl

lemma fibreMeasurable_neckRay (v : Amb) (k : ℕ) : FibreMeasurable (fun c ↦ neckRay c v k) := by
  induction k with
  | zero => exact fibreMeasurable_const v
  | succ k ih =>
      exact ih.comp fun u ↦ (fibreMeasurable_neckLetter u).map (fun i ↦ u ++ [i])

lemma fibreMeasurable_splitDepth (v : Amb) : FibreMeasurable (fun c ↦ splitDepth c v) := by
  refine measurableSet_sInf_eq fun k ↦ ?_
  exact (fibreMeasurable_neckRay v k).comp
    (fun u ↦ fibreMeasurable_skeletonDegree u) |>.preimage {m : ℕ | 2 ≤ m}

lemma fibreMeasurable_treeHeight (y : Amb) :
    FibreMeasurable (fun c ↦ treeHeight (shift c y)) := by
  intro m
  have hP : ∀ n : ℕ,
      MeasurableSet {c : Amb → ℕ | ∀ u ∈ sample (shift c y), u.length ≤ n} := by
    intro n
    have he : {c : Amb → ℕ | ∀ u ∈ sample (shift c y), u.length ≤ n}
        = ⋂ u ∈ {u : Amb | n < u.length}, {c : Amb → ℕ | u ∈ sample (shift c y)}ᶜ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · intro h u hu hmem
        have hlen := h u hmem
        have hu' : n < u.length := hu
        omega
      · intro h u hu
        by_contra hlt
        exact h u (show n < u.length by omega) hu
    rw [he]
    exact MeasurableSet.biInter (Set.to_countable _)
      fun u _ ↦ (measurable_shiftMap y (BranchingProcess.measurableSet_mem_sample u)).compl
  exact measurableSet_sInf_eq hP m

lemma fibreMeasurable_triOf : ∀ (n : ℕ) (y : Amb),
    FibreMeasurable (fun c ↦ triOf n (shift c y))
  | 0, y => fibreMeasurable_const _
  | n + 1, y => by
      have heq : ∀ c : Amb → ℕ, (if c y = 0 then Tri.leaf
            else if c y = 1 then Tri.one (triOf n (shift c (y ++ [0])))
            else Tri.two (triOf n (shift c (y ++ [0]))) (triOf n (shift c (y ++ [1]))))
          = triOf (n + 1) (shift c y) := by
        intro c
        have h0 : shift c y [] = c y := by rw [shift_apply, List.append_nil]
        have h1 : shift (shift c y) [(0 : Fin 2)] = shift c (y ++ [0]) := shift_shift c y _
        have h2 : shift (shift c y) [(1 : Fin 2)] = shift c (y ++ [1]) := shift_shift c y _
        rw [triOf, h0, h1, h2]
      have hpair := ((fibreMeasurable_coord y).prod
        ((fibreMeasurable_triOf n (y ++ [0])).prod (fibreMeasurable_triOf n (y ++ [1]))))
      exact (hpair.map (fun p : ℕ × Tri × Tri ↦
        if p.1 = 0 then Tri.leaf
        else if p.1 = 1 then Tri.one p.2.1 else Tri.two p.2.1 p.2.2)).congr heq

lemma fibreMeasurable_bushTri (y : Amb) : FibreMeasurable (fun c ↦ bushTri (shift c y)) :=
  (fibreMeasurable_treeHeight y).comp fun n ↦ fibreMeasurable_triOf n y

lemma fibreMeasurable_decAt (v : Amb) : FibreMeasurable (fun c ↦ decAt c v) := by
  have key : ∀ i : Fin 2, FibreMeasurable
      (fun c ↦ if c v = 2 then some (bushTri (shift c (v ++ [i]))) else none) := by
    intro i
    exact ((fibreMeasurable_coord v).prod (fibreMeasurable_bushTri (v ++ [i]))).map
      (fun p : ℕ × Tri ↦ if p.1 = 2 then some p.2 else none)
  exact (fibreMeasurable_bushLetter v).comp key

lemma fibreMeasurable_entryV (w : Word) : FibreMeasurable (fun c ↦ entryV c w) := by
  induction w using List.reverseRecOn with
  | nil => exact fibreMeasurable_const []
  | append_singleton w j ih =>
      have key : ∀ v : Amb,
          FibreMeasurable (fun c ↦ neckRay c v (splitDepth c v) ++ [letterOf j]) := by
        intro v
        have key2 : ∀ n : ℕ, FibreMeasurable (fun c ↦ neckRay c v n ++ [letterOf j]) :=
          fun n ↦ (fibreMeasurable_neckRay v n).map (fun u ↦ u ++ [letterOf j])
        exact (fibreMeasurable_splitDepth v).comp key2
      exact (ih.comp key).congr fun c ↦ (entryV_concat c w j).symm

/-- **`thm:shape-iid`**, the shape field is measurable: for every copy `w` and every
shape `σ` the event that the copy carries `σ` is measurable, so the shapes are a random
field over the index tree. -/
theorem fibreMeasurable_shapeAt (w : Word) : FibreMeasurable (fun c ↦ shapeAt c w) := by
  have key : ∀ v : Amb,
      FibreMeasurable (fun c ↦ (⟨splitDepth c v, fun i ↦ decAt c (neckRay c v i)⟩ : Shape)) := by
    intro v
    have key2 : ∀ n : ℕ,
        FibreMeasurable (fun c ↦ (⟨n, fun i : Fin n ↦ decAt c (neckRay c v i)⟩ : Shape)) := by
      intro n
      have hvec : FibreMeasurable (fun c ↦ (fun i : Fin n ↦ decAt c (neckRay c v i))) :=
        FibreMeasurable.pi fun i ↦
          FibreMeasurable.comp (h := fun u c ↦ decAt c u) (fibreMeasurable_neckRay v i)
            fun u ↦ fibreMeasurable_decAt u
      exact hvec.map (fun f ↦ (⟨n, f⟩ : Shape))
    exact FibreMeasurable.comp
      (h := fun n c ↦ (⟨n, fun i : Fin n ↦ decAt c (neckRay c v i)⟩ : Shape))
      (fibreMeasurable_splitDepth v) key2
  exact FibreMeasurable.comp
    (h := fun v c ↦ (⟨splitDepth c v, fun i ↦ decAt c (neckRay c v i)⟩ : Shape))
    (fibreMeasurable_entryV w) key

/-- The same statement unfolded: the event that the copy `w` of a sample carries the
shape `σ`. -/
theorem measurableSet_shapeAt_eq (w : Word) (σ : Shape) :
    MeasurableSet {c : Amb → ℕ | shapeAt c w = σ} := fibreMeasurable_shapeAt w σ

/-! ### The hypotheses of `sec:shapes` under the conditioned law -/

/-- **`sec:shapes`, the support hypothesis**: an offspring count above the support bound
is null, so almost every field is supported on `{0,1,2}`. -/
lemma sampleMeasure_offspring_le (θ : Offspring 2) :
    sampleMeasure (N := 2) θ {c : Amb → ℕ | ¬ ∀ v, c v ≤ 2} = 0 := by
  have he : {c : Amb → ℕ | ¬ ∀ v, c v ≤ 2}
      = ⋃ v : Amb, ⋃ k ∈ {k : ℕ | 2 < k}, {c : Amb → ℕ | c v = k} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, not_forall, not_le]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v, c v, hv, rfl⟩
    · rintro ⟨v, k, hk, rfl⟩
      exact ⟨v, hk⟩
  rw [he]
  refine measure_iUnion_null fun v ↦ ?_
  refine (measure_biUnion_null_iff (Set.to_countable _)).mpr fun k hk ↦ ?_
  rw [BranchingProcess.sampleMeasure_coord, θ.vanishing k hk, ENNReal.ofReal_zero]

/-- Conditioning on survival keeps the null events null. -/
lemma survivalMeasure_absolutelyContinuous (θ : Offspring 2) :
    survivalMeasure (N := 2) θ ≪ sampleMeasure (N := 2) θ :=
  cond_absolutelyContinuous

/-- **`thm:shape-iid`, the standing hypotheses**: conditioned on survival, almost every
field is supported on `{0,1,2}` and survives, so `IsBushySample` reduces to the event
that every ray of the skeleton meets a split, which is `Ω₀` read for the skeleton. -/
theorem ae_isBushySample (θ : Offspring 2) (hq : θ.extinction < 1)
    (hsplits : ∀ᵐ c ∂(survivalMeasure (N := 2) θ), ∀ v : Amb, Survives (shift c v) →
      ∃ k, 2 ≤ skeletonDegree (shift c (neckRay c v k))) :
    ∀ᵐ c ∂(survivalMeasure (N := 2) θ), IsBushySample c := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  have hoff : ∀ᵐ c ∂(survivalMeasure (N := 2) θ), ∀ v : Amb, c v ≤ 2 :=
    (survivalMeasure_absolutelyContinuous θ).ae_le
      (ae_iff.mpr (sampleMeasure_offspring_le θ))
  have hsurv : ∀ᵐ c ∂(survivalMeasure (N := 2) θ), Survives c := by
    rw [ae_iff]
    have hcompl : {c : Amb → ℕ | ¬ Survives c} = {c : Amb → ℕ | Survives c}ᶜ := rfl
    rw [hcompl, measure_compl BranchingProcess.measurableSet_survives (measure_ne_top _ _),
      BranchingProcess.survivalMeasure_survives θ le_rfl hq, measure_univ, tsub_self]
  filter_upwards [hoff, hsurv, hsplits] with c h1 h2 h3
  exact ⟨h1, h2, h3⟩

end ChainClasses
