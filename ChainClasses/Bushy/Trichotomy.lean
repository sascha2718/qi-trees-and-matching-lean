import ChainClasses.Bushy.Bushes
import ChainClasses.Bushy.ShapeCouplingBuild

/-!
Implementation of `thm:trichotomy-simple` of `gw_classes_simple.tex`, the quasi-isometry
classification for offspring laws supported on `{0,1,2}`.  The public result names are exported
by `ChainClasses.Classification.Simple`.

Everything is stated for the graph `wordGraph T` of a prefix-closed set `T` of
binary words, the setting of `BranchingProcess.Geometry`, and the regimes
supply four such sets:

* class (R), the ray `RayWord`;
* class (F), the binary tree `fun _ ↦ True`;
* class `(C_ℕ₀)`, the sample tree `InTree χ` of an offspring field `χ : Word → Bool` under
  `chainMeasure`;
* class (B), the sample tree of an offspring field `c : Amb → ℕ` under
  `survivalMeasure`, read as a set of binary words through the alphabet
  translation `letters` of `ShapeDecomposition`.

The law of a pair is the product of the two laws, so the four classes also sit
on one probabilistic footing.  The auxiliary uniform fields used in
`thm:cross-law` and in the bushy-universality proposition labelled
`thm:hairy` are carried along; where they are not part of the sample space,
`null_of_prod_assoc` removes them.

* `isQIWith_of_isSampleQI`, `quasiIsometric_sampleWord`: over the alphabet
  translation of `Bushes.lean`, `IsSampleQI` read as `IsQIWith`, which carries
  bushy universality (`thm:hairy`) to the graph footing.
* `isLine_of`, `downWord`, `upWord`, `exists_isLine_through`, `NearLine`,
  `nearLine_of_split`, `nearLine_true`, `nearLine_inTree`:
  **`thm:regime-obstructions` (`it:obstr-lines`)**.  A tree in which
  every vertex has a chain child and which is a chain above one split carries a
  line through every vertex below the split, and the vertices above it lie on
  the chain of the root: the binary tree and, on `Ω₀`, the sample tree of the
  chain regime.
* `HasThreeRays`, `not_quasiIsometric_rayGraph_of_threeRays`,
  `not_quasiIsometric_of_bushes_of_nearLine`: the two obstructions of
  `thm:bush-separation` and `thm:three-rays` for sets of words, the bushes
  supplied by `Bushes.lean`.
* `hasThreeRays_of`, `childRay`, `upRay`, `hasThreeRays_sampleWord`,
  `raysInBushyRegime`: **`thm:regime-obstructions` (`it:obstr-rays`) in
  class (B)**, the three rays out of the split below the second child of the
  first split.
* `quasiIsometric_refl`, `QuasiIsometric.symm`, `QuasiIsometric.trans`:
  reflexivity, the quasi-inverse coarse density supplies, and composition.
* `RayWord`, `treeDist_rayWord`, `quasiIsometric_rayWord_rayGraph`: the ray as
  a set of binary words, isometric to `rayGraph`.
* `SampleLaw`, `rayLaw`, `binaryLaw`, `chainLaw`, `bushySampleLaw`, `PairQI`:
  **the four simple-support classes as laws of a random tree**.
* `ray_ray_ae`, `binary_binary_ae`, `chain_chain_ae`, `bushy_bushy_ae`: **the
  four positive statements**, and `chain_binary_ae`, `binary_chain_ae`,
  `bushy_chain_ae`, `chain_bushy_ae`, `bushy_binary_ae`, `binary_bushy_ae`,
  `binary_ray_ae`, `ray_binary_ae`, `chain_ray_ae`, `ray_chain_ae`,
  `bushy_ray_ae`, `ray_bushy_ae`, `not_ray_binary`, `not_ray_chain`,
  `not_ray_bushy` the separations.
* `Regime`, `Regime.Valid`, `Regime.sampleLaw`, `Regime.kind`,
  `same_regime_ae`, `diff_regime_ae`, `not_ray_ae`, `trichotomy_simple`:
  **`thm:trichotomy-simple`**.

`thm:regime-obstructions` (`it:obstr-bushes`) is `unbounded_bushes_ae` of
`Bushes.lean`; it enters the two separations of (B) from (F) and from `(C_ℕ₀)`, and
through them the different-class clause of the classification.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (Offspring QuasiIsometric IsRay IsLine IsBush rayGraph sample
  survivalMeasure Survives survivors skeletonDegree)

/-! ### Bushy universality (`thm:hairy`) on the word footing -/

open Classical in
/-- **A quasi-isometry of two samples is one of the two word sets.** The map is
transported along the alphabet translation and totalised off the source by the
identity, and the real constant is rounded up. -/
theorem isQIWith_of_isSampleQI {c c' : Amb → ℕ} {L : ℝ}
    {F : {v : Amb // v ∈ sample c} → {v : Amb // v ∈ sample c'}} (hF : IsSampleQI L F) :
    ∃ (K : ℕ) (f : Word → Word), IsQIWith K (sampleWord c) (sampleWord c') f := by
  obtain ⟨hup, hlow, hdense⟩ := hF
  -- the constant is nonnegative, since it bounds a distance
  have hL0 : 0 ≤ L := by
    obtain ⟨a, ha⟩ := hdense ⟨[], BranchingProcess.nil_mem_sample c'⟩
    exact le_trans (by positivity) ha
  set K : ℕ := ⌈L⌉₊ with hK
  have hLK : L ≤ (K : ℝ) := Nat.le_ceil L
  refine ⟨K, fun a ↦ if h : sampleWord c a then unletters (F ⟨letters a, h⟩).1 else a, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [dif_pos ha]
    show letters (unletters _) ∈ sample c'
    rw [letters_unletters]
    exact (F ⟨letters a, ha⟩).2
  · intro a b ha hb
    rw [dif_pos ha, dif_pos hb]
    have hd : treeDist (unletters (F ⟨letters a, ha⟩).1) (unletters (F ⟨letters b, hb⟩).1)
        = BranchingProcess.treeDist (F ⟨letters a, ha⟩).1 (F ⟨letters b, hb⟩).1 := by
      rw [← letters_treeDist, letters_unletters, letters_unletters]
    have h := hup ⟨letters a, ha⟩ ⟨letters b, hb⟩
    rw [← hd, letters_treeDist] at h
    have hmono : L * (treeDist a b : ℝ) + L ≤ (K : ℝ) * (treeDist a b : ℝ) + K := by
      have : L * (treeDist a b : ℝ) ≤ (K : ℝ) * (treeDist a b : ℝ) := by
        exact mul_le_mul_of_nonneg_right hLK (by positivity)
      linarith
    have hcast : (treeDist (unletters (F ⟨letters a, ha⟩).1)
        (unletters (F ⟨letters b, hb⟩).1) : ℝ) ≤ ((K * treeDist a b + K : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  · intro a b ha hb
    rw [dif_pos ha, dif_pos hb]
    have hd : treeDist (unletters (F ⟨letters a, ha⟩).1) (unletters (F ⟨letters b, hb⟩).1)
        = BranchingProcess.treeDist (F ⟨letters a, ha⟩).1 (F ⟨letters b, hb⟩).1 := by
      rw [← letters_treeDist, letters_unletters, letters_unletters]
    have h := hlow ⟨letters a, ha⟩ ⟨letters b, hb⟩
    rw [← hd, letters_treeDist] at h
    have hsq : L ^ 2 ≤ (K : ℝ) * K := by
      calc L ^ 2 ≤ (K : ℝ) ^ 2 := by nlinarith
        _ = (K : ℝ) * K := by ring
    have hmono : L * (treeDist (unletters (F ⟨letters a, ha⟩).1)
          (unletters (F ⟨letters b, hb⟩).1) : ℝ) + L ^ 2
        ≤ (K : ℝ) * (treeDist (unletters (F ⟨letters a, ha⟩).1)
          (unletters (F ⟨letters b, hb⟩).1) : ℝ) + (K : ℝ) * K := by
      have : L * (treeDist (unletters (F ⟨letters a, ha⟩).1)
            (unletters (F ⟨letters b, hb⟩).1) : ℝ)
          ≤ (K : ℝ) * (treeDist (unletters (F ⟨letters a, ha⟩).1)
            (unletters (F ⟨letters b, hb⟩).1) : ℝ) :=
        mul_le_mul_of_nonneg_right hLK (by positivity)
      linarith
    have hcast : (treeDist a b : ℝ)
        ≤ ((K * treeDist (unletters (F ⟨letters a, ha⟩).1)
            (unletters (F ⟨letters b, hb⟩).1) + K * K : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  · intro y hy
    obtain ⟨x, hx⟩ := hdense ⟨letters y, hy⟩
    refine ⟨unletters x.1, ?_, ?_⟩
    · show letters (unletters x.1) ∈ sample c
      rw [letters_unletters]
      exact x.2
    · have hxm : sampleWord c (unletters x.1) := by
        show letters (unletters x.1) ∈ sample c
        rw [letters_unletters]; exact x.2
      rw [dif_pos hxm]
      have hxe : (⟨letters (unletters x.1), hxm⟩ : {v : Amb // v ∈ sample c}) = x :=
        Subtype.ext (letters_unletters x.1)
      rw [hxe]
      have hd : treeDist (unletters (F x).1) y
          = BranchingProcess.treeDist (F x).1 (letters y) := by
        rw [← letters_treeDist, letters_unletters]
      rw [hd]
      have : ((BranchingProcess.treeDist (F x).1 (letters y) : ℕ) : ℝ) ≤ (K : ℝ) :=
        le_trans hx hLK
      exact_mod_cast this

/-- **Bushy universality (`thm:hairy`) on the word footing**: a quasi-isometry of two samples is a
quasi-isometry of the graphs of the two word sets. -/
theorem quasiIsometric_sampleWord {c c' : Amb → ℕ} {L : ℝ}
    {F : {v : Amb // v ∈ sample c} → {v : Amb // v ∈ sample c'}} (hF : IsSampleQI L F) :
    QuasiIsometric (wordGraph (sampleWord c)) (wordGraph (sampleWord c')) := by
  obtain ⟨K, f, hf⟩ := isQIWith_of_isSampleQI hF
  exact quasiIsometric_wordGraph (prefixClosed_sampleWord c) (prefixClosed_sampleWord c') hf

/-! ### Lines in the graph of a set of words

`thm:regime-obstructions` (`it:obstr-lines`): a tree whose vertices all
have a child, and which is a chain above one split, carries a line through
every vertex below the split. -/

variable {T : Word → Prop}

/-- **A line out of two rays** leaving a common vertex in opposite directions:
the two rays are at distance the sum of their parameters. -/
lemma isLine_of {V : Type*} {G : SimpleGraph V} {r s : ℕ → V} (hr : IsRay G r) (hs : IsRay G s)
    (hcross : ∀ m n, G.dist (r m) (s n) = m + n) :
    IsLine G (fun k : ℤ ↦ if 0 ≤ k then r k.toNat else s (-k).toNat) := by
  intro m n
  rcases le_or_gt 0 m with hm | hm <;> rcases le_or_gt 0 n with hn | hn
  · simp only [if_pos hm, if_pos hn]
    rw [hr]
    unfold Nat.dist
    omega
  · simp only [if_pos hm, if_neg (not_le.mpr hn), hcross]
    omega
  · simp only [if_neg (not_le.mpr hm), if_pos hn]
    rw [SimpleGraph.dist_comm, hcross]
    omega
  · simp only [if_neg (not_le.mpr hm), if_neg (not_le.mpr hn)]
    rw [hs]
    unfold Nat.dist
    omega

/-! #### The ray descending the chain letter -/

/-- The ray descending the chain letter from a vertex. -/
def downWord (v : Word) (n : ℕ) : Word := v ++ List.replicate n false

@[simp] lemma downWord_zero (v : Word) : downWord v 0 = v := by simp [downWord]

lemma downWord_succ (v : Word) (n : ℕ) : downWord v (n + 1) = downWord v n ++ [false] := by
  rw [downWord, downWord, List.replicate_succ', ← List.append_assoc]

lemma treeDist_downWord_step (v : Word) (n : ℕ) :
    treeDist (downWord v n) (downWord v (n + 1)) = 1 := by
  rw [downWord, downWord, treeDist_of_prefix (append_replicate_prefix v false (Nat.le_succ n))]
  simp only [List.length_append, List.length_replicate]
  omega

lemma treeDist_downWord (v : Word) (n : ℕ) : treeDist v (downWord v n) = n := by
  rw [downWord, treeDist_of_prefix (List.prefix_append v _)]
  simp

lemma downWord_mem (hchain : ∀ u, T u → T (u ++ [false])) {v : Word} (hv : T v) :
    ∀ n, T (downWord v n)
  | 0 => by simpa using hv
  | n + 1 => by rw [downWord_succ]; exact hchain _ (downWord_mem hchain hv n)

/-! #### The ray climbing to the split and descending its other child -/

/-- The ray climbing from `v` to the split `b` above it and descending the
child of `b` that `v` does not lie below. -/
def upWord (b v : Word) (a : Bool) (n : ℕ) : Word :=
  if n ≤ v.length - b.length then v.take (v.length - n)
  else (b ++ [a]) ++ List.replicate (n - (v.length - b.length) - 1) false

variable {b v : Word} {a : Bool}

lemma upWord_le {n : ℕ} (hn : n ≤ v.length - b.length) :
    upWord b v a n = v.take (v.length - n) := if_pos hn

lemma upWord_gt {n : ℕ} (hn : ¬ n ≤ v.length - b.length) :
    upWord b v a n = (b ++ [a]) ++ List.replicate (n - (v.length - b.length) - 1) false :=
  if_neg hn

@[simp] lemma upWord_zero : upWord b v a 0 = v := by
  rw [upWord_le (Nat.zero_le _)]
  simp

lemma upWord_prefix {n : ℕ} (hn : n ≤ v.length - b.length) : upWord b v a n <+: v := by
  rw [upWord_le hn]
  exact List.take_prefix _ _

lemma upWord_length {n : ℕ} (hn : n ≤ v.length - b.length) :
    (upWord b v a n).length = v.length - n := by
  rw [upWord_le hn, List.length_take]
  omega

/-- Past the split the climbing ray descends the other child. -/
lemma upWord_eq_downWord {n : ℕ} (hn : ¬ n ≤ v.length - b.length) :
    upWord b v a n = downWord (b ++ [a]) (n - (v.length - b.length) - 1) := upWord_gt hn

section Split

variable (hbv : b ++ [!a] <+: v)
include hbv

lemma le_length_of_split : b.length + 1 ≤ v.length := by
  have := hbv.length_le
  simp only [List.length_append, List.length_singleton] at this
  omega

lemma prefix_of_split : b <+: v := (List.prefix_append b [!a]).trans hbv

lemma upWord_split : upWord b v a (v.length - b.length) = b := by
  have hlen := le_length_of_split hbv
  rw [upWord_le le_rfl, show v.length - (v.length - b.length) = b.length by omega]
  exact (List.prefix_iff_eq_take.mp (prefix_of_split hbv)).symm

/-- The wedge of the far part of the climbing ray with anything below `v` is
the split: the two leave `b` by different letters. -/
lemma wedge_upWord {n : ℕ} (hn : ¬ n ≤ v.length - b.length) {x : Word} (hx : v <+: x) :
    wedge x (upWord b v a n) = b := by
  rw [upWord_gt hn]
  exact wedge_of_diverge (Bool.not_ne_self a) (hbv.trans hx) (List.prefix_append _ _)

lemma treeDist_upWord (n : ℕ) : treeDist v (upWord b v a n) = n := by
  have hlen := le_length_of_split hbv
  by_cases hn : n ≤ v.length - b.length
  · rw [treeDist_comm, treeDist_of_prefix (upWord_prefix hn), upWord_length hn]
    omega
  · have hw := treeDist_add_wedge_length v (upWord b v a n)
    rw [wedge_upWord hbv hn (List.prefix_refl v)] at hw
    have hlen2 : (upWord b v a n).length
        = b.length + 1 + (n - (v.length - b.length) - 1) := by
      rw [upWord_gt hn]
      simp only [List.length_append, List.length_replicate, List.length_singleton]
    omega

/-- The two rays out of `v` are at distance the sum of their parameters. -/
lemma treeDist_downWord_upWord (m n : ℕ) :
    treeDist (downWord v m) (upWord b v a n) = m + n := by
  have hlen := le_length_of_split hbv
  by_cases hn : n ≤ v.length - b.length
  · have hpre : upWord b v a n <+: downWord v m :=
      (upWord_prefix hn).trans (List.prefix_append v _)
    rw [treeDist_comm, treeDist_of_prefix hpre, upWord_length hn]
    simp only [downWord, List.length_append, List.length_replicate]
    omega
  · have hw := treeDist_add_wedge_length (downWord v m) (upWord b v a n)
    rw [wedge_upWord (x := downWord v m) hbv hn (List.prefix_append v _)] at hw
    have hlen2 : (upWord b v a n).length
        = b.length + 1 + (n - (v.length - b.length) - 1) := by
      rw [upWord_gt hn]
      simp only [List.length_append, List.length_replicate, List.length_singleton]
    have hlen3 : (downWord v m).length = v.length + m := by
      simp [downWord]
    omega

lemma treeDist_upWord_step (n : ℕ) :
    treeDist (upWord b v a n) (upWord b v a (n + 1)) = 1 := by
  have hlen := le_length_of_split hbv
  by_cases hn : n + 1 ≤ v.length - b.length
  · have hn' : n ≤ v.length - b.length := by omega
    have hpre : upWord b v a (n + 1) <+: upWord b v a n := by
      rw [upWord_le hn, upWord_le hn']
      exact prefix_of_prefix_of_length_le (List.take_prefix _ _) (List.take_prefix _ _)
        (by simp only [List.length_take]; omega)
    rw [treeDist_comm, treeDist_of_prefix hpre, upWord_length hn, upWord_length hn']
    omega
  · by_cases hn' : n ≤ v.length - b.length
    · have hnv : n = v.length - b.length := by omega
      have h1 : upWord b v a n = b := by rw [hnv]; exact upWord_split hbv
      have h2 : upWord b v a (n + 1) = b ++ [a] := by
        rw [upWord_gt hn, show n + 1 - (v.length - b.length) - 1 = 0 by omega]
        simp
      rw [h1, h2, treeDist_of_prefix (List.prefix_append b [a])]
      simp
    · rw [upWord_gt hn, upWord_gt hn',
        treeDist_of_prefix (append_replicate_prefix (b ++ [a]) false
          (show n - (v.length - b.length) - 1 ≤ n + 1 - (v.length - b.length) - 1 by omega))]
      simp only [List.length_append, List.length_replicate]
      omega

omit hbv in
lemma upWord_mem (hT : PrefixClosed T) (hchain : ∀ u, T u → T (u ++ [false]))
    (hb : T (b ++ [a])) (hv : T v) (n : ℕ) : T (upWord b v a n) := by
  by_cases hn : n ≤ v.length - b.length
  · exact hT (upWord_prefix hn) hv
  · rw [upWord_eq_downWord hn]
    exact downWord_mem hchain hb _

/-- **A line through a vertex below a split.**  The chain child of `v` carries
one ray, and the climb to the split followed by its other child carries the
other. -/
theorem exists_isLine_through (hT : PrefixClosed T) (hchain : ∀ u, T u → T (u ++ [false]))
    (hb : T (b ++ [a])) (hv : T v) :
    ∃ l : ℤ → {w : Word // T w}, IsLine (wordGraph T) l ∧ (l 0).1 = v := by
  classical
  set r : ℕ → {w : Word // T w} := fun n ↦ ⟨downWord v n, downWord_mem hchain hv n⟩ with hr
  set s : ℕ → {w : Word // T w} :=
    fun n ↦ ⟨upWord b v a n, upWord_mem hT hchain hb hv n⟩ with hs
  have hray : IsRay (wordGraph T) r := by
    refine isRay_of hT r (fun n ↦ treeDist_downWord_step v n) (fun n ↦ ?_)
    show treeDist (downWord v 0) (downWord v n) = n
    rw [downWord_zero]
    exact treeDist_downWord v n
  have hray' : IsRay (wordGraph T) s := by
    refine isRay_of hT s (fun n ↦ treeDist_upWord_step hbv n) (fun n ↦ ?_)
    show treeDist (upWord b v a 0) (upWord b v a n) = n
    rw [upWord_zero]
    exact treeDist_upWord hbv n
  refine ⟨fun k : ℤ ↦ if 0 ≤ k then r k.toNat else s (-k).toNat,
    isLine_of hray hray' (fun m n ↦ ?_), by simp [hr]⟩
  rw [wordGraph_dist hT]
  exact treeDist_downWord_upWord hbv m n

end Split

/-- **`thm:regime-obstructions` (`it:obstr-lines`), the deterministic
form.**  A tree in which every vertex has a chain child, which carries a split
at `b` and is a chain above it, has all of its vertices within `|b|+1` of a
line. -/
theorem exists_near_isLine (hT : PrefixClosed T) (hchain : ∀ u, T u → T (u ++ [false]))
    (hb0 : T (b ++ [false])) (hb1 : T (b ++ [true]))
    (hcomp : ∀ w, T w → b <+: w ∨ w <+: b) (u : {w : Word // T w}) :
    ∃ (l : ℤ → {w : Word // T w}) (k : ℤ),
      IsLine (wordGraph T) l ∧ (wordGraph T).dist u (l k) ≤ b.length + 1 := by
  -- the vertices weakly above the split use the line through its chain child
  have hB : ∀ w : {x : Word // T x}, w.1 <+: b →
      ∃ (l : ℤ → {x : Word // T x}) (k : ℤ),
        IsLine (wordGraph T) l ∧ (wordGraph T).dist w (l k) ≤ b.length + 1 := by
    intro w hw
    obtain ⟨l, hl, hl0⟩ :=
      exists_isLine_through (a := true) (v := b ++ [false]) (List.prefix_refl _) hT hchain hb1 hb0
    refine ⟨l, 0, hl, ?_⟩
    rw [wordGraph_dist hT, hl0, treeDist_of_prefix (hw.trans (List.prefix_append b [false]))]
    simp
  rcases hcomp u.1 u.2 with hbu | hub
  · rcases eq_or_ne b u.1 with heq | hne
    · exact hB u (heq ▸ List.prefix_refl _)
    · obtain ⟨t, ht⟩ := hbu
      obtain ⟨x, t', rfl⟩ : ∃ (x : Bool) (t' : Word), t = x :: t' := by
        cases t with
        | nil => exact absurd (by simpa using ht) hne
        | cons x t' => exact ⟨x, t', rfl⟩
      have hxu : b ++ [!!x] <+: u.1 := by
        rw [Bool.not_not, ← ht]
        exact ⟨t', by simp⟩
      have hbx : T (b ++ [!x]) := by cases x <;> simpa using ‹_›
      obtain ⟨l, hl, hl0⟩ := exists_isLine_through hxu hT hchain hbx u.2
      refine ⟨l, 0, hl, ?_⟩
      rw [wordGraph_dist hT, hl0]
      simp
  · exact hB u hub

/-- **`thm:regime-obstructions` (`it:obstr-lines`)**, in the form
`thm:bush-separation` consumes: every vertex lies within a bounded distance of
a line. -/
def NearLine (T : Word → Prop) : Prop :=
  ∃ R : ℕ, ∀ u : {w : Word // T w}, ∃ (l : ℤ → {w : Word // T w}) (k : ℤ),
    IsLine (wordGraph T) l ∧ (wordGraph T).dist u (l k) ≤ R

theorem nearLine_of_split (hT : PrefixClosed T) (hchain : ∀ u, T u → T (u ++ [false]))
    (hb0 : T (b ++ [false])) (hb1 : T (b ++ [true]))
    (hcomp : ∀ w, T w → b <+: w ∨ w <+: b) : NearLine T :=
  ⟨b.length + 1, exists_near_isLine hT hchain hb0 hb1 hcomp⟩

/-! #### The two regimes without leaves -/

/-- **The binary tree is a union of lines.** -/
theorem nearLine_true : NearLine (fun _ : Word ↦ True) :=
  nearLine_of_split (b := []) prefixClosed_true (fun _ _ ↦ trivial) trivial trivial
    (fun _ _ ↦ Or.inl List.nil_prefix)

/-- Above the first branch point the sample tree of the chain regime is a
chain. -/
lemma prefix_or_prefix_split {χ : Word → Bool} (hχ : Chains χ) {v : Word} (hv : InTree χ v) :
    List.replicate (kappa hχ [] - 1) false <+: v ∨ v <+: List.replicate (kappa hχ [] - 1) false := by
  induction hv with
  | root => exact Or.inr List.nil_prefix
  | @one w _ ih =>
      rcases ih with h | h
      · exact Or.inl (h.trans (List.prefix_append _ _))
      · have hlen : w.length ≤ kappa hχ [] - 1 := by
          have := h.length_le
          simpa using this
        rcases eq_or_lt_of_le hlen with heq | hlt
        · have hw : w = List.replicate (kappa hχ [] - 1) false :=
            h.eq_of_length (by simp [heq])
          exact Or.inl (hw ▸ List.prefix_append _ _)
        · have hmem : ∀ x ∈ w, x = false := fun x hx ↦ List.eq_of_mem_replicate (h.subset hx)
          have hrep : w = List.replicate w.length false :=
            List.eq_replicate_iff.mpr ⟨rfl, hmem⟩
          refine Or.inr ?_
          calc w ++ [false] = List.replicate (w.length + 1) false := by
                rw [List.replicate_succ', ← hrep]
            _ <+: List.replicate (kappa hχ [] - 1) false := by
                simpa using append_replicate_prefix [] false (show w.length + 1 ≤ _ by omega)
  | @two w _ hχw ih =>
      rcases ih with h | h
      · exact Or.inl (h.trans (List.prefix_append _ _))
      · have hlen : w.length ≤ kappa hχ [] - 1 := by
          have := h.length_le
          simpa using this
        rcases eq_or_lt_of_le hlen with heq | hlt
        · have hw : w = List.replicate (kappa hχ [] - 1) false :=
            h.eq_of_length (by simp [heq])
          exact Or.inl (hw ▸ List.prefix_append _ _)
        · exfalso
          have hmem : ∀ x ∈ w, x = false := fun x hx ↦ List.eq_of_mem_replicate (h.subset hx)
          have hrep : w = List.replicate w.length false :=
            List.eq_replicate_iff.mpr ⟨rfl, hmem⟩
          have hfalse : χ w = false := by
            rw [hrep]
            have := kappa_min hχ [] (l := w.length) hlt
            simpa using this
          rw [hfalse] at hχw
          exact Bool.false_ne_true hχw

/-- **`thm:regime-obstructions` (`it:obstr-lines`) in the chain
regime.**  Every vertex of the sample tree lies within `λ(∅)` of a line: the
first branch point carries one, every vertex below it lies on one, and the
vertices above it lie on the chain of the root. -/
theorem nearLine_inTree {χ : Word → Bool} (hχ : Chains χ) : NearLine (InTree χ) := by
  have hbmem : InTree χ (List.replicate (kappa hχ [] - 1) false) := by
    have h := ray_mem_tree (InTree.root (χ := χ)) (kappa hχ [] - 1)
    rwa [List.nil_append] at h
  have hsplit : χ (List.replicate (kappa hχ [] - 1) false) = true := by
    have h := kappa_spec hχ []
    rwa [List.nil_append] at h
  exact nearLine_of_split (prefixClosed_inTree χ) (fun _ hu ↦ InTree.one hu)
    (InTree.one hbmem) (InTree.two hbmem hsplit) (fun _ hw ↦ prefix_or_prefix_split hχ hw)

/-! ### Three rays -/

/-- **`thm:regime-obstructions` (`it:obstr-rays`)**, in the form
`thm:three-rays` consumes: three rays out of one vertex, pairwise meeting only
there. -/
def HasThreeRays (T : Word → Prop) : Prop :=
  ∃ (v : {w : Word // T w}) (ray : Fin 3 → ℕ → {w : Word // T w}),
    (∀ i, IsRay (wordGraph T) (ray i)) ∧ (∀ i, ray i 0 = v) ∧
      ∀ i j, i ≠ j → ∀ m n, ray i m = ray j n → ray i m = v

theorem not_quasiIsometric_rayGraph_of_threeRays (hT : PrefixClosed T) (h : HasThreeRays T) :
    ¬ QuasiIsometric (wordGraph T) rayGraph := by
  obtain ⟨v, ray, hray, hbase, hmeet⟩ := h
  exact BranchingProcess.not_quasiIsometric_rayGraph (wordGraph_isTree hT ⟨v⟩) hray hbase hmeet

/-- **`thm:three-rays` for the binary tree**: the vertex `2` carries three
rays, two into its children and one through the root. -/
theorem not_quasiIsometric_rayGraph_true :
    ¬ QuasiIsometric (wordGraph (fun _ : Word ↦ True)) rayGraph :=
  not_quasiIsometric_rayGraph_of_splits (T := fun _ : Word ↦ True) (u := []) (k := 0)
    prefixClosed_true (fun _ ↦ trivial) (fun _ ↦ trivial) (fun _ ↦ trivial)

/-! ### Bushes -/

/-- **`thm:bush-separation` for two sets of words.** -/
theorem not_quasiIsometric_of_bushes_of_nearLine {T T' : Word → Prop} (hT : PrefixClosed T)
    (hT' : PrefixClosed T') (hne : T []) (hne' : T' [])
    (hbush : UnboundedBushes T) (hline : NearLine T') :
    ¬ QuasiIsometric (wordGraph T) (wordGraph T') := by
  obtain ⟨R, hR⟩ := hline
  exact BranchingProcess.not_quasiIsometric_of_bush_of_line (R := R)
    (wordGraph_isTree hT ⟨⟨[], hne⟩⟩) (wordGraph_isTree hT' ⟨⟨[], hne'⟩⟩) hbush hR

/-! ### Quasi-isometry is reflexive, symmetric and transitive -/

theorem quasiIsometric_refl {V : Type*} (G : SimpleGraph V) : QuasiIsometric G G :=
  ⟨1, id, ⟨fun x y ↦ by simp, fun x y ↦ by simp, fun y ↦ ⟨y, by simp⟩⟩⟩

/-- **A quasi-isometry has a quasi-inverse.**  A vertex of the target is sent
to one of the preimages coarse density supplies, and the three conditions
follow from the triangle inequality. -/
theorem QuasiIsometric.symm {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}
    (hG' : G'.Connected) (h : QuasiIsometric G G') : QuasiIsometric G' G := by
  classical
  obtain ⟨D, f, hf⟩ := h
  choose g hg using hf.dense
  have hcomm : ∀ y', G'.dist y' (f (g y')) ≤ D := by
    intro y'
    rw [SimpleGraph.dist_comm (u := y') (v := f (g y'))]
    exact hg y'
  refine ⟨3 * (D * D) + D, g, ⟨fun x y ↦ ?_, fun x y ↦ ?_, fun x ↦ ⟨f x, ?_⟩⟩⟩
  · have h1 : G'.dist (f (g x)) (f (g y)) ≤ D + G'.dist x y + D := by
      have h2 : G'.dist (f (g x)) (f (g y)) ≤ G'.dist (f (g x)) x + G'.dist x (f (g y)) :=
        hG'.dist_triangle
      have h3 : G'.dist x (f (g y)) ≤ G'.dist x y + G'.dist y (f (g y)) := hG'.dist_triangle
      have h4 := hg x
      have h5 := hcomm y
      omega
    have hm : D * G'.dist x y ≤ (3 * (D * D) + D) * G'.dist x y :=
      Nat.mul_le_mul_right _ (by omega)
    calc G.dist (g x) (g y) ≤ D * G'.dist (f (g x)) (f (g y)) + D * D := hf.lower _ _
      _ ≤ D * (D + G'.dist x y + D) + D * D := by gcongr
      _ = D * G'.dist x y + 3 * (D * D) := by ring
      _ ≤ (3 * (D * D) + D) * G'.dist x y + (3 * (D * D) + D) := by omega
  · have h4 := hcomm x
    have h5 := hg y
    have hm : D * G.dist (g x) (g y) ≤ (3 * (D * D) + D) * G.dist (g x) (g y) :=
      Nat.mul_le_mul_right _ (by omega)
    have hc : 3 * D ≤ (3 * (D * D) + D) * (3 * (D * D) + D) := by
      rcases Nat.eq_zero_or_pos D with rfl | hD
      · simp
      · have hDD : D ≤ D * D := Nat.le_mul_of_pos_left D hD
        have hpos : 0 < 3 * (D * D) + D := by omega
        calc 3 * D ≤ 3 * (D * D) + D := by omega
          _ ≤ (3 * (D * D) + D) * (3 * (D * D) + D) := Nat.le_mul_of_pos_left _ hpos
    calc G'.dist x y ≤ G'.dist x (f (g x)) + G'.dist (f (g x)) y := hG'.dist_triangle
      _ ≤ G'.dist x (f (g x)) + (G'.dist (f (g x)) (f (g y)) + G'.dist (f (g y)) y) := by
          gcongr
          exact hG'.dist_triangle
      _ ≤ D + ((D * G.dist (g x) (g y) + D) + D) := by
          gcongr
          exact hf.upper _ _
      _ = D * G.dist (g x) (g y) + 3 * D := by ring
      _ ≤ (3 * (D * D) + D) * G.dist (g x) (g y) + (3 * (D * D) + D) * (3 * (D * D) + D) := by omega
  · calc G.dist (g (f x)) x ≤ D * G'.dist (f (g (f x))) (f x) + D * D := hf.lower _ _
      _ ≤ D * D + D * D := by gcongr; exact hg (f x)
      _ ≤ 3 * (D * D) + D := by omega

/-- **Quasi-isometries of graphs compose.** -/
theorem QuasiIsometric.trans {V V' V'' : Type*} {G : SimpleGraph V}
    {G' : SimpleGraph V'} {G'' : SimpleGraph V''} (hG'' : G''.Connected)
    (h : QuasiIsometric G G') (h' : QuasiIsometric G' G'') :
    QuasiIsometric G G'' := by
  obtain ⟨D, f, hf⟩ := h
  obtain ⟨D', g, hg⟩ := h'
  refine ⟨D * D' + D + 2 * D' + 1, fun v ↦ g (f v), ⟨?_, ?_, ?_⟩⟩
  · intro x y
    have h1 := hg.upper (f x) (f y)
    have h2 := hf.upper x y
    have h3 : D' * G'.dist (f x) (f y) ≤ D' * (D * G.dist x y + D) :=
      Nat.mul_le_mul_left D' h2
    have h4 : D' * (D * G.dist x y + D) = D * D' * G.dist x y + D * D' := by ring
    have h5 : D * D' * G.dist x y ≤ (D * D' + D + 2 * D' + 1) * G.dist x y :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · intro x y
    have h1 := hf.lower x y
    have h2 := hg.lower (f x) (f y)
    have h3 : D * G'.dist (f x) (f y)
        ≤ D * (D' * G''.dist (g (f x)) (g (f y)) + D' * D') :=
      Nat.mul_le_mul_left D h2
    have h4 : D * (D' * G''.dist (g (f x)) (g (f y)) + D' * D')
        = D * D' * G''.dist (g (f x)) (g (f y)) + D * D' * D' := by ring
    have h5 : D * D' * G''.dist (g (f x)) (g (f y))
        ≤ (D * D' + D + 2 * D' + 1) * G''.dist (g (f x)) (g (f y)) :=
      Nat.mul_le_mul_right _ (by omega)
    have h6 : D * D' * D' + D * D
        ≤ (D * D' + D + 2 * D' + 1) * (D * D' + D + 2 * D' + 1) := by
      nlinarith [Nat.zero_le (D * D'), Nat.zero_le D, Nat.zero_le D',
        Nat.zero_le (D * D' * D'), Nat.zero_le (D * D)]
    omega
  · intro z
    obtain ⟨y, hy⟩ := hg.dense z
    obtain ⟨x, hx⟩ := hf.dense y
    refine ⟨x, ?_⟩
    have h2 : G''.dist (g (f x)) z ≤ G''.dist (g (f x)) (g y) + G''.dist (g y) z :=
      hG''.dist_triangle
    have h3 : G''.dist (g (f x)) (g y) ≤ D' * G'.dist (f x) y + D' := hg.upper _ _
    have h4 : D' * G'.dist (f x) y ≤ D' * D := Nat.mul_le_mul_left D' hx
    have h5 : D' * D = D * D' := by ring
    omega

/-! ### Dropping the auxiliary randomisation

`thm:cross-law` is proved on the space carrying, besides the two samples, the
uniform field of `thm:chain-coupling`.  The conclusion speaks of the two
samples only, so the third factor drops out. -/

lemma preimage_null_of_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : μ.map e = ν) {S : Set β}
    (h : ν S = 0) : μ (e ⁻¹' S) = 0 := by
  rw [← MeasurableEquiv.map_apply, he]
  exact h

/-- **The third factor drops out.**  An event of the first two coordinates that
is null for the law of the three is null for the law of the two. -/
theorem null_of_prod_assoc {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure τ] {S : Set (α × β)}
    (h : (μ.prod (ν.prod τ)) {ω : α × β × γ | (ω.1, ω.2.1) ∈ S} = 0) : (μ.prod ν) S = 0 := by
  have hpre := preimage_null_of_map (MeasurableEquiv.prodAssoc)
    (measurePreserving_prodAssoc μ ν τ).map_eq h
  have hset : (MeasurableEquiv.prodAssoc ⁻¹' {ω : α × β × γ | (ω.1, ω.2.1) ∈ S})
      = S ×ˢ (Set.univ : Set γ) := by
    ext ⟨⟨a, b⟩, c⟩
    simp [MeasurableEquiv.prodAssoc]
  rw [hset, Measure.prod_prod, measure_univ, mul_one] at hpre
  exact hpre

/-- An almost sure property of one sample holds almost surely for a pair. -/
lemma ae_of_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [IsProbabilityMeasure ν] {p : α → Prop} (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ ω ∂(μ.prod ν), p ω.1 := by
  rw [ae_iff] at h ⊢
  have hset : {ω : α × β | ¬ p ω.1} = {a : α | ¬ p a} ×ˢ (Set.univ : Set β) := by
    ext ⟨a, b⟩; simp
  rw [hset, Measure.prod_prod, h, zero_mul]

/-- An almost sure property of one sample holds almost surely for a pair. -/
lemma ae_of_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [IsProbabilityMeasure μ] [SFinite ν] {p : β → Prop} (h : ∀ᵐ b ∂ν, p b) :
    ∀ᵐ ω ∂(μ.prod ν), p ω.2 := by
  rw [ae_iff] at h ⊢
  have hset : {ω : α × β | ¬ p ω.2} = (Set.univ : Set α) ×ˢ {b : β | ¬ p b} := by
    ext ⟨a, b⟩; simp
  rw [hset, Measure.prod_prod, h, mul_zero]

/-- An almost sure property of the first two coordinates of a triple product descends to
the product of the first two factors. -/
lemma ae_prod_fst_of_triple {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {τ : Measure γ} [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure τ] {p : α × β → Prop}
    (h : ∀ᵐ ω ∂(μ.prod (ν.prod τ)), p (ω.1, ω.2.1)) : ∀ᵐ ω ∂(μ.prod ν), p ω := by
  rw [ae_iff] at h ⊢
  exact null_of_prod_assoc μ ν τ h

/-- An almost sure property of the first two coordinates lifts to the triple
product. -/
lemma ae_pair_fst {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    [SFinite μ] [SFinite ν] [IsProbabilityMeasure τ] {p : α × β → Prop}
    (h : ∀ᵐ ω ∂(μ.prod ν), p ω) :
    ∀ᵐ ω ∂(μ.prod (ν.prod τ)), p (ω.1, ω.2.1) := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hmeas, hnull⟩ := exists_measurable_superset_of_null h
  refine measure_mono_null (t := (fun ω : α × β × γ ↦ (ω.1, ω.2.1)) ⁻¹' T)
    (fun ω hω ↦ Set.mem_preimage.mpr (hsub hω)) ?_
  show μ.prod (ν.prod τ) ((fun ω : α × β × γ ↦ (ω.1, ω.2.1)) ⁻¹' T) = 0
  have hpre : (MeasurableEquiv.prodAssoc ⁻¹'
      ((fun ω : α × β × γ ↦ (ω.1, ω.2.1)) ⁻¹' T)) = T ×ˢ (Set.univ : Set γ) := by
    ext ⟨⟨a, b⟩, c⟩
    simp [MeasurableEquiv.prodAssoc]
  have hmp := (measurePreserving_prodAssoc μ ν τ).map_eq
  rw [← hmp, MeasurableEquiv.map_apply, hpre, Measure.prod_prod, hnull, zero_mul]

/-- An almost sure property of the outer two coordinates of the triple product
descends to their product, through one Fubini slice in the middle
coordinate. -/
lemma ae_pair_outer {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite τ] [IsProbabilityMeasure ν] {p : α × γ → Prop}
    (h : ∀ᵐ ω ∂(μ.prod (ν.prod τ)), p (ω.1, ω.2.2)) :
    ∀ᵐ ω ∂(μ.prod τ), p ω := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hmeas, hnull⟩ := exists_measurable_superset_of_null h
  -- move the middle coordinate to the front
  have hmpInv : MeasurePreserving (fun ω : β × α × γ ↦ (ω.2.1, (ω.1, ω.2.2)))
      (ν.prod (μ.prod τ)) (μ.prod (ν.prod τ)) := by
    have mp1 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm)
        (ν.prod (μ.prod τ)) ((ν.prod μ).prod τ) :=
      (measurePreserving_prodAssoc ν μ τ).symm MeasurableEquiv.prodAssoc
    have mp2 : MeasurePreserving (Prod.map Prod.swap (id : γ → γ))
        ((ν.prod μ).prod τ) ((μ.prod ν).prod τ) :=
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).prod (MeasurePreserving.id τ)
    have mp3 : MeasurePreserving (MeasurableEquiv.prodAssoc)
        ((μ.prod ν).prod τ) (μ.prod (ν.prod τ)) :=
      measurePreserving_prodAssoc μ ν τ
    exact (mp3.comp mp2).comp mp1
  set T' : Set (β × α × γ) := (fun ω : β × α × γ ↦ (ω.2.1, (ω.1, ω.2.2))) ⁻¹' T
    with hT'
  have hT'meas : MeasurableSet T' := hmpInv.measurable hmeas
  have hT'null : ν.prod (μ.prod τ) T' = 0 := by
    rw [hT', hmpInv.measure_preimage hmeas.nullMeasurableSet, hnull]
  have hsec := (Measure.measure_prod_null hT'meas).mp hT'null
  have hexists : ∃ b : β, μ.prod τ (Prod.mk b ⁻¹' T') = 0 := by
    have hne : ν ≠ 0 := IsProbabilityMeasure.ne_zero ν
    have : (MeasureTheory.ae ν).NeBot := ae_neBot.mpr hne
    exact hsec.exists
  obtain ⟨b, hb⟩ := hexists
  refine measure_mono_null (fun ac hac ↦ ?_) hb
  show (b, ac) ∈ T'
  rw [hT']
  exact Set.mem_preimage.mpr (hsub hac)

/-- An almost sure property of the first coordinates of two products descends to the
product of the first factors: one reassociation and two Fubini slices. -/
lemma ae_prod_fst_fst {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] {μ : Measure α} {ν : Measure β} {μ' : Measure γ}
    {ν' : Measure δ} [SFinite μ] [IsProbabilityMeasure ν] [SFinite μ'] [IsProbabilityMeasure ν']
    {p : α × γ → Prop} (h : ∀ᵐ ω ∂((μ.prod ν).prod (μ'.prod ν')), p (ω.1.1, ω.2.1)) :
    ∀ᵐ ω ∂(μ.prod μ'), p ω := by
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc.symm) (μ.prod (ν.prod (μ'.prod ν')))
      ((μ.prod ν).prod (μ'.prod ν')) :=
    (measurePreserving_prodAssoc μ ν (μ'.prod ν')).symm MeasurableEquiv.prodAssoc
  rw [← hmp.map_eq] at h
  have h1 := ae_of_ae_map hmp.measurable.aemeasurable h
  have h2 : ∀ᵐ ω ∂(μ.prod (ν.prod (μ'.prod ν'))), p (ω.1, ω.2.2.1) := h1
  have h3 := ae_pair_outer (p := fun z : α × (γ × δ) => p (z.1, z.2.1)) h2
  rw [ae_iff] at h3 ⊢
  exact null_of_prod_assoc μ μ' ν' h3

/-! ### The ray as a set of words -/

/-- The ray as a set of binary words: the words all of whose letters are the
chain letter. -/
def RayWord (w : Word) : Prop := ∀ b ∈ w, b = false

lemma prefixClosed_rayWord : PrefixClosed RayWord :=
  fun _ _ huv hv b hb ↦ hv b (huv.subset hb)

lemma rayWord_nil : RayWord [] := fun _ hb ↦ absurd hb List.not_mem_nil

/-- Two words of the ray are comparable: the shorter is a prefix of the longer. -/
lemma rayWord_prefix_of_length_le {u v : Word} (hu : RayWord u) (hv : RayWord v)
    (h : u.length ≤ v.length) : u <+: v := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_take]
    exact (hu _ (List.getElem_mem _)).trans (hv _ (List.getElem_mem _)).symm

/-- Along the ray the tree metric is the distance of the depths. -/
lemma treeDist_rayWord {u v : Word} (hu : RayWord u) (hv : RayWord v) :
    treeDist u v = Nat.dist u.length v.length := by
  rcases le_total u.length v.length with h | h
  · rw [treeDist_of_prefix (rayWord_prefix_of_length_le hu hv h), Nat.dist_eq_sub_of_le h]
  · rw [treeDist_comm, treeDist_of_prefix (rayWord_prefix_of_length_le hv hu h),
      Nat.dist_eq_sub_of_le_right h]

/-- **The ray as a set of words is quasi-isometric to `rayGraph`**: the depth
is an isometry. -/
theorem quasiIsometric_rayWord_rayGraph : QuasiIsometric (wordGraph RayWord) rayGraph := by
  refine ⟨1, fun w ↦ w.1.length, fun x y ↦ ?_, fun x y ↦ ?_, fun n ↦ ?_⟩
  · rw [BranchingProcess.rayGraph_dist, wordGraph_dist prefixClosed_rayWord,
      treeDist_rayWord x.2 y.2]
    omega
  · rw [BranchingProcess.rayGraph_dist, wordGraph_dist prefixClosed_rayWord,
      treeDist_rayWord x.2 y.2]
    omega
  · refine ⟨⟨List.replicate n false, fun b hb ↦ List.eq_of_mem_replicate hb⟩, ?_⟩
    simp

/-! ### The four classes as laws of a random tree -/

/-- **A law of a random tree**: a probability space carrying a prefix-closed
set of binary words, the vertex set of the sample. -/
structure SampleLaw : Type 1 where
  /-- The sample space. -/
  Ω : Type
  /-- Its measurable structure. -/
  meas : MeasurableSpace Ω
  /-- The law of the sample. -/
  law : Measure Ω
  /-- The law is a probability measure. -/
  isProb : IsProbabilityMeasure law
  /-- The sample tree, as a set of binary words. -/
  tree : Ω → Word → Prop
  /-- The sample tree is prefix-closed. -/
  prefixClosed : ∀ ω, PrefixClosed (tree ω)
  /-- The sample tree contains the root. -/
  root : ∀ ω, tree ω []

attribute [instance] SampleLaw.meas SampleLaw.isProb

/-- The graph of the sample. -/
abbrev SampleLaw.graph (L : SampleLaw) (ω : L.Ω) : SimpleGraph {w : Word // L.tree ω w} :=
  wordGraph (L.tree ω)

/-- **Class (F)**: the binary tree, a single sample. -/
noncomputable def binaryLaw : SampleLaw where
  Ω := Unit
  meas := inferInstance
  law := Measure.dirac ()
  isProb := inferInstance
  tree := fun _ ↦ fun _ ↦ True
  prefixClosed := fun _ ↦ prefixClosed_true
  root := fun _ ↦ trivial

/-- **Class (R)**: the ray, a single sample. -/
noncomputable def rayLaw : SampleLaw where
  Ω := Unit
  meas := inferInstance
  law := Measure.dirac ()
  isProb := inferInstance
  tree := fun _ ↦ RayWord
  prefixClosed := fun _ ↦ prefixClosed_rayWord
  root := fun _ ↦ rayWord_nil

/-- **Class `(C_ℕ₀)`**: the two-value family, `θ₂ = t` and `θ₁ = 1 - t`. -/
noncomputable def chainLaw {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : SampleLaw where
  Ω := Word → Bool
  meas := inferInstance
  law := chainMeasure ht ht1.le
  isProb := inferInstance
  tree := InTree
  prefixClosed := prefixClosed_inTree
  root := fun _ ↦ InTree.root

/-- **Class (B)**: an offspring law on `{0,1,2}` with `θ₀ > 0`, conditioned on
survival, carrying the uniform field of `thm:shape-coupling`. -/
noncomputable def bushySampleLaw (θ : Offspring 2) (hq : θ.extinction < 1) : SampleLaw where
  Ω := BushySample
  meas := inferInstance
  law := bushyMeasure θ
  isProb := isProbabilityMeasure_bushyMeasure θ hq
  tree := fun ω ↦ sampleWord ω.1
  prefixClosed := fun ω ↦ prefixClosed_sampleWord ω.1
  root := fun ω ↦ sampleWord_nil ω.1

/-- Quasi-isometry of the two sample trees of a pair of laws. -/
def PairQI (L L' : SampleLaw) (ω : L.Ω × L'.Ω) : Prop :=
  QuasiIsometric (L.graph ω.1) (L'.graph ω.2)

/-! ### The four positive statements -/

/-- **Universality in class (F)**: the two samples are the binary tree. -/
theorem binary_binary_ae :
    ∀ᵐ ω ∂(binaryLaw.law.prod binaryLaw.law), PairQI binaryLaw binaryLaw ω :=
  Filter.Eventually.of_forall fun _ ↦ quasiIsometric_refl _

/-- **Universality in class (R)**: the two samples are the ray. -/
theorem ray_ray_ae : ∀ᵐ ω ∂(rayLaw.law.prod rayLaw.law), PairQI rayLaw rayLaw ω :=
  Filter.Eventually.of_forall fun _ ↦ quasiIsometric_refl _

/-- **Universality in class `(C_ℕ₀)`**, `thm:cross-law` on the law of the two
samples: the uniform field of `thm:chain-coupling` drops out. -/
theorem chain_chain_ae {t t' : ℝ} (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1) :
    ∀ᵐ ω ∂((chainLaw ht ht1).law.prod (chainLaw ht' ht1').law),
      PairQI (chainLaw ht ht1) (chainLaw ht' ht1') ω := by
  rw [ae_iff]
  refine null_of_prod_assoc (chainMeasure ht ht1.le) (chainMeasure ht' ht1'.le) uniField ?_
  refine measure_mono_null ?_ (crosslaw_ae_tree ht ht1 ht' ht1')
  rintro ω hω ⟨K, f, hf⟩
  exact hω (quasiIsometric_wordGraph (prefixClosed_inTree _) (prefixClosed_inTree _) hf)

/-- **Universality in class (B)**, `thm:hairy` on the graph footing. -/
theorem bushy_bushy_ae (θ θ' : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (hq' : θ'.extinction < 1) (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) :
    ∀ᵐ ω ∂((bushySampleLaw θ hq).law.prod (bushySampleLaw θ' hq').law),
      PairQI (bushySampleLaw θ hq) (bushySampleLaw θ' hq') ω := by
  rw [ae_iff]
  refine measure_mono_null ?_
    (bushy_ae_shape_tree_two_law θ θ' hq hq0 h2 hq' hq0' h2')
  rintro ω hω ⟨L, F, hF⟩
  exact hω (quasiIsometric_sampleWord hF)

/-! ### The two obstructions for the non-ray classes -/

/-- **`Ω₀` has full probability**, in the form the obstructions consume. -/
lemma ae_chains {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂(chainMeasure ht ht1.le), Chains ω := by
  rw [ae_iff]
  exact not_chains_null (chainMeasure ht ht1.le)
    (fun v : Word ↦ (BranchingProcess.coord v : (Word → Bool) → Bool)) t
    measurable_chainMeasure_coord (chainMeasure_iIndepFun ht ht1.le)
    (chainMeasure_coord_true ht ht1.le) ht

/-- **`thm:regime-obstructions` (`it:obstr-rays`) in class (B)**, the
form the separation from the ray consumes; `raysInBushyRegime` proves it. -/
def RaysInBushyRegime : Prop :=
  ∀ θ : Offspring 2, θ.extinction < 1 → 0 < θ.extinction → 0 < θ 2 →
    ∀ᵐ c ∂(survivalMeasure (N := 2) θ), HasThreeRays (sampleWord c)

/-! ### The separations -/

/-- **Class `(C_ℕ₀)` against class (F)**, `thm:converse`. -/
theorem chain_binary_ae {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂((chainLaw ht ht1).law.prod binaryLaw.law),
      ¬ PairQI (chainLaw ht ht1) binaryLaw ω := by
  filter_upwards [ae_of_fst (ν := binaryLaw.law) (converse_ae ht ht1)] with ω hω
  exact hω.1

/-- **Class (F) against class `(C_ℕ₀)`**, `thm:converse` read backwards. -/
theorem binary_chain_ae {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂(binaryLaw.law.prod (chainLaw ht ht1).law),
      ¬ PairQI binaryLaw (chainLaw ht ht1) ω := by
  filter_upwards [ae_of_snd (μ := binaryLaw.law) (converse_ae ht ht1)] with ω hω hqi
  exact hω.1 (QuasiIsometric.symm
    (wordGraph_connected (prefixClosed_inTree _) ⟨⟨[], InTree.root⟩⟩) hqi)

/-- **Class (B) against class `(C_ℕ₀)`**: the bushy sample has bushes of unbounded
depth and the chain sample is a union of lines. -/
theorem bushy_chain_ae (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂((bushySampleLaw θ hq).law.prod (chainLaw ht ht1).law),
      ¬ PairQI (bushySampleLaw θ hq) (chainLaw ht ht1) ω := by
  filter_upwards [ae_of_fst (ν := (chainLaw ht ht1).law)
      (ae_of_fst (unbounded_bushes_ae θ hq hq0 h2)),
    ae_of_snd (μ := (bushySampleLaw θ hq).law) (ae_chains ht ht1)] with ω hh hc
  exact not_quasiIsometric_of_bushes_of_nearLine (prefixClosed_sampleWord _)
    (prefixClosed_inTree _) (sampleWord_nil _) InTree.root hh (nearLine_inTree hc)

/-- **Class `(C_ℕ₀)` against class (B)**. -/
theorem chain_bushy_ae (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂((chainLaw ht ht1).law.prod (bushySampleLaw θ hq).law),
      ¬ PairQI (chainLaw ht ht1) (bushySampleLaw θ hq) ω := by
  filter_upwards [ae_of_snd (μ := (chainLaw ht ht1).law)
      (ae_of_fst (unbounded_bushes_ae θ hq hq0 h2)),
    ae_of_fst (ν := (bushySampleLaw θ hq).law) (ae_chains ht ht1)] with ω hh hc hqi
  exact not_quasiIsometric_of_bushes_of_nearLine (prefixClosed_sampleWord _)
    (prefixClosed_inTree _) (sampleWord_nil _) InTree.root hh (nearLine_inTree hc)
    (QuasiIsometric.symm (wordGraph_connected (prefixClosed_sampleWord _)
      ⟨⟨[], sampleWord_nil _⟩⟩) hqi)

/-- **Class (B) against class (F)**. -/
theorem bushy_binary_ae (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) :
    ∀ᵐ ω ∂((bushySampleLaw θ hq).law.prod binaryLaw.law),
      ¬ PairQI (bushySampleLaw θ hq) binaryLaw ω := by
  filter_upwards [ae_of_fst (ν := binaryLaw.law)
    (ae_of_fst (unbounded_bushes_ae θ hq hq0 h2))] with ω hh
  exact not_quasiIsometric_of_bushes_of_nearLine (prefixClosed_sampleWord _)
    prefixClosed_true (sampleWord_nil _) trivial hh nearLine_true

/-- **Class (F) against class (B)**. -/
theorem binary_bushy_ae (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) :
    ∀ᵐ ω ∂(binaryLaw.law.prod (bushySampleLaw θ hq).law),
      ¬ PairQI binaryLaw (bushySampleLaw θ hq) ω := by
  filter_upwards [ae_of_snd (μ := binaryLaw.law)
    (ae_of_fst (unbounded_bushes_ae θ hq hq0 h2))] with ω hh hqi
  exact not_quasiIsometric_of_bushes_of_nearLine (prefixClosed_sampleWord _)
    prefixClosed_true (sampleWord_nil _) trivial hh nearLine_true
    (QuasiIsometric.symm (wordGraph_connected (prefixClosed_sampleWord _)
      ⟨⟨[], sampleWord_nil _⟩⟩) hqi)

/-! ### Separation from the ray -/

/-- **`thm:three-rays` in class (F)**. -/
theorem not_ray_binary : ∀ᵐ ω ∂binaryLaw.law,
    ¬ QuasiIsometric (binaryLaw.graph ω) rayGraph :=
  Filter.Eventually.of_forall fun _ ↦ not_quasiIsometric_rayGraph_true

/-- **`thm:three-rays` in class `(C_ℕ₀)`**. -/
theorem not_ray_chain {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂(chainLaw ht ht1).law, ¬ QuasiIsometric ((chainLaw ht ht1).graph ω) rayGraph := by
  filter_upwards [converse_ae ht ht1] with ω hω
  exact hω.2

/-- **`thm:three-rays` in class (B)**, over the three rays of
`thm:regime-obstructions` (`it:obstr-rays`). -/
theorem not_ray_bushy (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (hrays : RaysInBushyRegime) :
    ∀ᵐ ω ∂(bushySampleLaw θ hq).law, ¬ QuasiIsometric ((bushySampleLaw θ hq).graph ω) rayGraph := by
  filter_upwards [ae_of_fst (hrays θ hq hq0 h2)] with ω hω
  exact not_quasiIsometric_rayGraph_of_threeRays (prefixClosed_sampleWord _) hω

/-! ### Separations of the ray regime -/

/-- A sample quasi-isometric to the ray sample is quasi-isometric to the ray. -/
lemma quasiIsometric_rayGraph_of_pairQI {L : SampleLaw} {ω : L.Ω × Unit}
    (h : PairQI L rayLaw ω) : QuasiIsometric (L.graph ω.1) rayGraph :=
  QuasiIsometric.trans BranchingProcess.rayGraph_connected h quasiIsometric_rayWord_rayGraph

/-- The mirror form, for the ray sample on the left. -/
lemma quasiIsometric_rayGraph_of_pairQI' {L : SampleLaw} {ω : Unit × L.Ω}
    (h : PairQI rayLaw L ω) : QuasiIsometric (L.graph ω.2) rayGraph :=
  quasiIsometric_rayGraph_of_pairQI (L := L) (ω := (ω.2, ω.1))
    (QuasiIsometric.symm (wordGraph_connected (L.prefixClosed ω.2) ⟨⟨[], L.root ω.2⟩⟩) h)

/-- **Separation (F)-(R)**. -/
theorem binary_ray_ae :
    ∀ᵐ ω ∂(binaryLaw.law.prod rayLaw.law), ¬ PairQI binaryLaw rayLaw ω :=
  Filter.Eventually.of_forall fun _ h ↦
    not_quasiIsometric_rayGraph_true (quasiIsometric_rayGraph_of_pairQI h)

/-- **Separation (R)-(F)**. -/
theorem ray_binary_ae :
    ∀ᵐ ω ∂(rayLaw.law.prod binaryLaw.law), ¬ PairQI rayLaw binaryLaw ω :=
  Filter.Eventually.of_forall fun _ h ↦
    not_quasiIsometric_rayGraph_true (quasiIsometric_rayGraph_of_pairQI' h)

/-- **Separation (C_ℕ₀)-(R)**. -/
theorem chain_ray_ae {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂((chainLaw ht ht1).law.prod rayLaw.law), ¬ PairQI (chainLaw ht ht1) rayLaw ω := by
  filter_upwards [ae_of_fst (ν := rayLaw.law) (not_ray_chain ht ht1)] with ω hω h
  exact hω (quasiIsometric_rayGraph_of_pairQI h)

/-- **Separation (R)-(C_ℕ₀)**. -/
theorem ray_chain_ae {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂(rayLaw.law.prod (chainLaw ht ht1).law), ¬ PairQI rayLaw (chainLaw ht ht1) ω := by
  filter_upwards [ae_of_snd (μ := rayLaw.law) (not_ray_chain ht ht1)] with ω hω h
  exact hω (quasiIsometric_rayGraph_of_pairQI' h)

/-! ### Three rays in the bushy sample

`thm:regime-obstructions` (`it:obstr-rays`) in class (B). On the event
`IsBushySample` the chain of the root ends at a split `u`, and the chain of the
second child of `u` ends at a further split `v`.  Two rays descend the children
of `v` along their necks, and the third climbs from `v` to `u` and descends the
first child of `u`. -/

/-- **Three rays out of one vertex**, pairwise meeting only there. -/
lemma hasThreeRays_of {T : Word → Prop} {v : {w : Word // T w}} {r s t : ℕ → {w : Word // T w}}
    (hr : IsRay (wordGraph T) r) (hs : IsRay (wordGraph T) s) (ht : IsRay (wordGraph T) t)
    (hr0 : r 0 = v) (hs0 : s 0 = v) (ht0 : t 0 = v)
    (hrs : ∀ m n, m ≠ 0 → n ≠ 0 → r m ≠ s n)
    (hrt : ∀ m n, m ≠ 0 → n ≠ 0 → r m ≠ t n)
    (hst : ∀ m n, m ≠ 0 → n ≠ 0 → s m ≠ t n) : HasThreeRays T := by
  refine ⟨v, ![r, s, t], fun i ↦ ?_, fun i ↦ ?_, fun i j hij m n hmn ↦ ?_⟩
  · fin_cases i
    exacts [hr, hs, ht]
  · fin_cases i
    exacts [hr0, hs0, ht0]
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · fin_cases i
      exacts [hr0, hs0, ht0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hmn]
      fin_cases j
      exacts [hr0, hs0, ht0]
    fin_cases i
    · fin_cases j
      · exact absurd rfl hij
      · exact absurd hmn (hrs m n hm.ne' hn.ne')
      · exact absurd hmn (hrt m n hm.ne' hn.ne')
    · fin_cases j
      · exact absurd hmn fun h ↦ hrs n m hn.ne' hm.ne' h.symm
      · exact absurd rfl hij
      · exact absurd hmn (hst m n hm.ne' hn.ne')
    · fin_cases j
      · exact absurd hmn fun h ↦ hrt n m hn.ne' hm.ne' h.symm
      · exact absurd hmn fun h ↦ hst n m hn.ne' hm.ne' h.symm
      · exact absurd rfl hij

variable {c : Amb → ℕ}

lemma prefix_neckRay (c : Amb → ℕ) (v : Amb) : ∀ k, v <+: neckRay c v k
  | 0 => List.prefix_refl _
  | k + 1 => by
      rw [neckRay_succ]
      exact (prefix_neckRay c v k).trans (List.prefix_append _ _)

lemma neckRay_children (c : Amb → ℕ) (v : Amb) (k : ℕ) :
    neckRay c v (k + 1) ∈ BranchingProcess.Word.children (neckRay c v k) :=
  ⟨neckLetter c (neckRay c v k), neckRay_succ c v k⟩

/-- The ray descending a child of a split along its neck. -/
noncomputable def childRay (c : Amb → ℕ) (v : Amb) (j : Fin 2) (n : ℕ) : Amb :=
  if n = 0 then v else neckRay c (v ++ [j]) (n - 1)

@[simp] lemma childRay_zero (c : Amb → ℕ) (v : Amb) (j : Fin 2) : childRay c v j 0 = v := rfl

lemma childRay_chain (c : Amb → ℕ) (v : Amb) (j : Fin 2) (n : ℕ) :
    childRay c v j (n + 1) ∈ BranchingProcess.Word.children (childRay c v j n) := by
  cases n with
  | zero => exact ⟨j, by simp [childRay]⟩
  | succ m =>
      have h1 : childRay c v j (m + 1) = neckRay c (v ++ [j]) m := by simp [childRay]
      have h2 : childRay c v j (m + 1 + 1) = neckRay c (v ++ [j]) (m + 1) := by simp [childRay]
      rw [h1, h2]
      exact neckRay_children c (v ++ [j]) m

lemma childRay_mem {v : Amb} (hv : v ∈ sample c) {j : Fin 2} (hjm : v ++ [j] ∈ sample c)
    (hj : Survives (shift c (v ++ [j]))) (n : ℕ) : childRay c v j n ∈ sample c := by
  cases n with
  | zero => exact hv
  | succ m =>
      have h1 : childRay c v j (m + 1) = neckRay c (v ++ [j]) m := by simp [childRay]
      rw [h1]
      exact mem_sample_neckRay hjm hj m

lemma prefix_childRay (c : Amb → ℕ) (v : Amb) (j : Fin 2) {n : ℕ} (hn : n ≠ 0) :
    v ++ [j] <+: childRay c v j n := by
  have h1 : childRay c v j n = neckRay c (v ++ [j]) (n - 1) := by simp [childRay, hn]
  rw [h1]
  exact prefix_neckRay c (v ++ [j]) _

/-- The ray climbing from `v` to the split `u` above it and descending the
first child of `u`. -/
noncomputable def upRay (c : Amb → ℕ) (u v : Amb) (k n : ℕ) : Amb :=
  if n ≤ k + 1 then v.take (v.length - n) else neckRay c (u ++ [0]) (n - k - 2)

@[simp] lemma upRay_zero (c : Amb → ℕ) (u v : Amb) (k : ℕ) : upRay c u v k 0 = v := by
  rw [upRay, if_pos (Nat.zero_le _)]
  simp

section BushyRays

variable {u v : Amb} {k : ℕ}

lemma upRay_le {n : ℕ} (hn : n ≤ k + 1) : upRay c u v k n = v.take (v.length - n) := if_pos hn

lemma upRay_gt {n : ℕ} (hn : ¬ n ≤ k + 1) :
    upRay c u v k n = neckRay c (u ++ [0]) (n - k - 2) := if_neg hn

variable (hlen : v.length = u.length + 1 + k) (hpre : u ++ [1] <+: v)
include hlen

lemma upRay_length {n : ℕ} (hn : n ≤ k + 1) : (upRay c u v k n).length = v.length - n := by
  rw [upRay_le hn, List.length_take]
  omega

include hpre in
lemma upRay_split : upRay c u v k (k + 1) = u := by
  rw [upRay_le le_rfl, show v.length - (k + 1) = u.length by omega]
  exact (List.prefix_iff_eq_take.mp ((List.prefix_append u [1]).trans hpre)).symm

omit hlen in
include hpre in
/-- The far part of the climbing ray meets `v` at the split `u`. -/
lemma wedge_upRay (j : ℕ) : BranchingProcess.wedge v (neckRay c (u ++ [0]) j) = u := by
  obtain ⟨s, hs⟩ := hpre
  obtain ⟨s', hs'⟩ := prefix_neckRay c (u ++ [0]) j
  rw [← hs, ← hs', List.append_assoc, List.append_assoc,
    BranchingProcess.wedge_append_append]
  simp only [List.singleton_append, BranchingProcess.wedge_cons_cons, if_neg (by decide :
    ¬ ((1 : Fin 2) = 0))]
  simp

include hpre in
lemma treeDist_upRay (n : ℕ) : BranchingProcess.treeDist v (upRay c u v k n) = n := by
  by_cases hn : n ≤ k + 1
  · rw [BranchingProcess.treeDist_comm, upRay_le hn,
      BranchingProcess.treeDist_of_prefix (List.take_prefix _ _), List.length_take]
    omega
  · rw [upRay_gt hn]
    have hw := BranchingProcess.treeDist_add v (neckRay c (u ++ [0]) (n - k - 2))
    rw [wedge_upRay hpre _, neckRay_length] at hw
    simp only [List.length_append, List.length_singleton] at hw
    omega

include hpre in
lemma treeDist_upRay_step (n : ℕ) :
    BranchingProcess.treeDist (upRay c u v k n) (upRay c u v k (n + 1)) = 1 := by
  by_cases hn : n + 1 ≤ k + 1
  · have hn' : n ≤ k + 1 := by omega
    have hp : upRay c u v k (n + 1) <+: upRay c u v k n := by
      rw [upRay_le hn, upRay_le hn']
      exact List.prefix_take_iff.mpr ⟨List.take_prefix _ _, by simp; omega⟩
    rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix hp,
      upRay_length hlen hn, upRay_length hlen hn']
    omega
  · by_cases hn' : n ≤ k + 1
    · have hnk : n = k + 1 := by omega
      rw [hnk, upRay_split hlen hpre, upRay_gt (by omega),
        show k + 1 + 1 - k - 2 = 0 by omega, neckRay_zero]
      simp
    · rw [upRay_gt hn', upRay_gt (by omega),
        show n + 1 - k - 2 = (n - k - 2) + 1 by omega]
      exact BranchingProcess.treeDist_of_mem_children (neckRay_children c (u ++ [0]) _)

/-- Past its initial vertex the climbing ray is either shorter than `v` or
descends the other child of `u`. -/
lemma upRay_cases {n : ℕ} (hn : n ≠ 0) :
    (upRay c u v k n).length < v.length ∨ u ++ [(0 : Fin 2)] <+: upRay c u v k n := by
  by_cases hnk : n ≤ k + 1
  · refine Or.inl ?_
    rw [upRay_length hlen hnk]
    omega
  · exact Or.inr (by rw [upRay_gt hnk]; exact prefix_neckRay c (u ++ [0]) _)

end BushyRays

/-! ### The rays in the sample tree read as a set of words -/

/-- **`thm:regime-obstructions` (`it:obstr-rays`) in class (B)**, the
deterministic form. -/
theorem hasThreeRays_sampleWord (hc : IsBushySample c) : HasThreeRays (sampleWord c) := by
  classical
  -- the split ending the chain of the root
  have hsurv0 : Survives (shift c []) := by simpa using hc.survives
  have hmem0 : ([] : Amb) ∈ sample c := BranchingProcess.nil_mem_sample c
  set u : Amb := neckRay c [] (splitDepth c []) with hu
  have humem : u ∈ sample c := mem_sample_neckRay hmem0 hsurv0 _
  have hudeg : skeletonDegree (shift c u) = 2 := splitDepth_spec hc hsurv0
  have huchild : ∀ j : Fin 2, u ++ [j] ∈ sample c ∧ Survives (shift c (u ++ [j])) := by
    intro j
    have hj : j ∈ survivors (shift c u) := by
      rw [survivors_eq_univ hudeg]; exact Finset.mem_univ _
    obtain ⟨hlt, hjs⟩ := mem_survivors_shift.mp hj
    exact ⟨BranchingProcess.mem_sample_append_singleton.mpr ⟨humem, hlt⟩, hjs⟩
  -- the split ending the chain of its second child
  set k : ℕ := splitDepth c (u ++ [1]) with hk
  set v : Amb := neckRay c (u ++ [1]) k with hv
  have hvmem : v ∈ sample c := mem_sample_neckRay (huchild 1).1 (huchild 1).2 _
  have hvdeg : skeletonDegree (shift c v) = 2 := splitDepth_spec hc (huchild 1).2
  have hvchild : ∀ j : Fin 2, v ++ [j] ∈ sample c ∧ Survives (shift c (v ++ [j])) := by
    intro j
    have hj : j ∈ survivors (shift c v) := by
      rw [survivors_eq_univ hvdeg]; exact Finset.mem_univ _
    obtain ⟨hlt, hjs⟩ := mem_survivors_shift.mp hj
    exact ⟨BranchingProcess.mem_sample_append_singleton.mpr ⟨hvmem, hlt⟩, hjs⟩
  have hpre : u ++ [1] <+: v := prefix_neckRay c (u ++ [1]) k
  have hlen : v.length = u.length + 1 + k := by
    rw [hv, neckRay_length]
    simp only [List.length_append, List.length_singleton]
  -- the three rays, as vertices of the word set
  have hmemC : ∀ (j : Fin 2) (n : ℕ), sampleWord c (unletters (childRay c v j n)) :=
    fun j n ↦ sampleWord_unletters (childRay_mem hvmem (hvchild j).1 (hvchild j).2 n)
  have hmemU : ∀ n : ℕ, sampleWord c (unletters (upRay c u v k n)) := by
    intro n
    refine sampleWord_unletters ?_
    by_cases hn : n ≤ k + 1
    · rw [upRay_le hn]
      exact BranchingProcess.Subtree.mem_of_prefix (List.take_prefix _ _) hvmem
    · rw [upRay_gt hn]
      exact mem_sample_neckRay (huchild 0).1 (huchild 0).2 _
  set R : Fin 2 → ℕ → {w : Word // sampleWord c w} :=
    fun j n ↦ ⟨unletters (childRay c v j n), hmemC j n⟩ with hR
  set S : ℕ → {w : Word // sampleWord c w} :=
    fun n ↦ ⟨unletters (upRay c u v k n), hmemU n⟩ with hS
  -- each is a ray
  have hrayC : ∀ j : Fin 2, IsRay (wordGraph (sampleWord c)) (R j) := by
    intro j
    refine isRay_of (prefixClosed_sampleWord c) _ (fun n ↦ ?_) (fun n ↦ ?_)
    · show treeDist (unletters (childRay c v j n)) (unletters (childRay c v j (n + 1))) = 1
      rw [treeDist_unletters]
      exact BranchingProcess.treeDist_of_mem_children (childRay_chain c v j n)
    · show treeDist (unletters (childRay c v j 0)) (unletters (childRay c v j n)) = n
      rw [treeDist_unletters, BranchingProcess.treeDist_of_chain (childRay_chain c v j) 0 n]
      unfold Nat.dist
      omega
  have hrayS : IsRay (wordGraph (sampleWord c)) S := by
    refine isRay_of (prefixClosed_sampleWord c) _ (fun n ↦ ?_) (fun n ↦ ?_)
    · show treeDist (unletters (upRay c u v k n)) (unletters (upRay c u v k (n + 1))) = 1
      rw [treeDist_unletters]
      exact treeDist_upRay_step hlen hpre n
    · show treeDist (unletters (upRay c u v k 0)) (unletters (upRay c u v k n)) = n
      rw [upRay_zero, treeDist_unletters]
      exact treeDist_upRay hlen hpre n
  -- the three rays part at `v`
  have hvlt : ∀ (j : Fin 2) (m : ℕ), m ≠ 0 → v.length < (childRay c v j m).length := by
    intro j m hm
    have h := (prefix_childRay c v j hm).length_le
    simp only [List.length_append, List.length_singleton] at h
    omega
  have hupre : ∀ (j : Fin 2) (m : ℕ), m ≠ 0 → u ++ [(1 : Fin 2)] <+: childRay c v j m :=
    fun j m hm ↦ hpre.trans ((List.prefix_append v [j]).trans (prefix_childRay c v j hm))
  have hsep : ∀ (j j' : Fin 2), j ≠ j' → ∀ m n, m ≠ 0 → n ≠ 0 →
      childRay c v j m ≠ childRay c v j' n := by
    intro j j' hjj m n hm hn heq
    have h1 := prefix_childRay c v j hm
    have h2 := prefix_childRay c v j' hn
    rw [← heq] at h2
    have h3 : (v ++ [j] : Amb) = v ++ [j'] := eq_of_prefix_of_length h1 h2 (by simp)
    exact hjj (by simpa using h3)
  have hsepU : ∀ (j : Fin 2) (m n : ℕ), m ≠ 0 → n ≠ 0 →
      childRay c v j m ≠ upRay c u v k n := by
    intro j m n hm hn heq
    rcases upRay_cases hlen hn with hshort | hlong
    · rw [← heq] at hshort
      exact absurd hshort (not_lt.mpr (hvlt j m hm).le)
    · rw [← heq] at hlong
      have h1 := hupre j m hm
      have h3 : (u ++ [(0 : Fin 2)] : Amb) = u ++ [1] :=
        eq_of_prefix_of_length hlong h1 (by simp)
      simp at h3
  exact hasThreeRays_of (v := ⟨unletters v, sampleWord_unletters hvmem⟩)
    (hrayC 0) (hrayC 1) hrayS rfl rfl (Subtype.ext (by simp [hS]))
    (fun m n hm hn h ↦ hsep 0 1 (by decide) m n hm hn
      (unletters_injective (congrArg Subtype.val h)))
    (fun m n hm hn h ↦ hsepU 0 m n hm hn (unletters_injective (congrArg Subtype.val h)))
    (fun m n hm hn h ↦ hsepU 1 m n hm hn (unletters_injective (congrArg Subtype.val h)))

/-- **`thm:regime-obstructions` (`it:obstr-rays`) in class (B)**: the
three rays are there almost surely, since `IsBushySample` is. -/
theorem raysInBushyRegime : RaysInBushyRegime := by
  intro θ hq _ h2
  filter_upwards [ae_isBushySample_of_pos θ hq h2] with c hc
  exact hasThreeRays_sampleWord hc

/-- **Separation (B)-(R)**. -/
theorem bushy_ray_ae (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) :
    ∀ᵐ ω ∂((bushySampleLaw θ hq).law.prod rayLaw.law),
      ¬ PairQI (bushySampleLaw θ hq) rayLaw ω := by
  filter_upwards [ae_of_fst (ν := rayLaw.law)
    (not_ray_bushy θ hq hq0 h2 raysInBushyRegime)] with ω hω h
  exact hω (quasiIsometric_rayGraph_of_pairQI h)

/-- **Separation (R)-(B)**. -/
theorem ray_bushy_ae (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) :
    ∀ᵐ ω ∂(rayLaw.law.prod (bushySampleLaw θ hq).law),
      ¬ PairQI rayLaw (bushySampleLaw θ hq) ω := by
  filter_upwards [ae_of_snd (μ := rayLaw.law)
    (not_ray_bushy θ hq hq0 h2 raysInBushyRegime)] with ω hω h
  exact hω (quasiIsometric_rayGraph_of_pairQI' h)

/-! ### The classification -/

/-- **The four simple-support classes of `thm:trichotomy-simple`.** -/
inductive Regime : Type
  /-- Class (F), `θ₀ = θ₁ = 0`: the binary tree. -/
  | binary : Regime
  /-- Class `(C_ℕ₀)`, `θ₀ = 0 < θ₁`: the two-value family, with `θ₂ = t`. -/
  | chain (t : ℝ) : Regime
  /-- Class (B), `θ₀ > 0`. -/
  | bushy (θ : Offspring 2) : Regime
  /-- Class (R), `θ₁ = 1`: the ray. -/
  | ray : Regime

/-- Supercriticality and the inequalities defining the class. In class (B)
the extinction probability is positive exactly when `θ₀ > 0`. -/
def Regime.Valid : Regime → Prop
  | .binary => True
  | .chain t => 0 < t ∧ t < 1
  | .bushy θ => θ.extinction < 1 ∧ 0 < θ.extinction ∧ 0 < θ 2
  | .ray => True

/-- The law of the sample in a regime. -/
noncomputable def Regime.sampleLaw : (r : Regime) → r.Valid → SampleLaw
  | .binary, _ => binaryLaw
  | .chain _, h => chainLaw h.1 h.2
  | .bushy θ, h => bushySampleLaw θ h.1
  | .ray, _ => rayLaw

/-- The name of the class: the invariant used by the classification. -/
def Regime.kind : Regime → ℕ
  | .binary => 0
  | .chain _ => 1
  | .bushy _ => 2
  | .ray => 3

/-- **The same-class clause of `thm:trichotomy-simple`**: two laws in the same class give
quasi-isometric samples almost surely. -/
theorem same_regime_ae (r r' : Regime) (hr : r.Valid) (hr' : r'.Valid)
    (hk : r.kind = r'.kind) :
    ∀ᵐ ω ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
      PairQI (r.sampleLaw hr) (r'.sampleLaw hr') ω := by
  cases r with
  | binary =>
      cases r' with
      | binary => exact binary_binary_ae
      | chain t => simp [Regime.kind] at hk
      | bushy θ => simp [Regime.kind] at hk
      | ray => simp [Regime.kind] at hk
  | chain t =>
      cases r' with
      | binary => simp [Regime.kind] at hk
      | chain t' =>
          exact chain_chain_ae hr.1 hr.2 hr'.1 hr'.2
      | bushy θ => simp [Regime.kind] at hk
      | ray => simp [Regime.kind] at hk
  | bushy θ =>
      cases r' with
      | binary => simp [Regime.kind] at hk
      | chain t => simp [Regime.kind] at hk
      | bushy θ' => exact bushy_bushy_ae θ θ' hr.1 hr.2.1 hr.2.2 hr'.1 hr'.2.1 hr'.2.2
      | ray => simp [Regime.kind] at hk
  | ray =>
      cases r' with
      | binary => simp [Regime.kind] at hk
      | chain t => simp [Regime.kind] at hk
      | bushy θ => simp [Regime.kind] at hk
      | ray => exact ray_ray_ae

/-- **The different-class clause of `thm:trichotomy-simple`**: two laws in different classes give
samples that are almost surely not quasi-isometric. -/
theorem diff_regime_ae (r r' : Regime) (hr : r.Valid)
    (hr' : r'.Valid) (hk : r.kind ≠ r'.kind) :
    ∀ᵐ ω ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
      ¬ PairQI (r.sampleLaw hr) (r'.sampleLaw hr') ω := by
  cases r with
  | binary =>
      cases r' with
      | binary => simp [Regime.kind] at hk
      | chain t => exact binary_chain_ae hr'.1 hr'.2
      | bushy θ => exact binary_bushy_ae θ hr'.1 hr'.2.1 hr'.2.2
      | ray => exact binary_ray_ae
  | chain t =>
      cases r' with
      | binary => exact chain_binary_ae hr.1 hr.2
      | chain t' => simp [Regime.kind] at hk
      | bushy θ => exact chain_bushy_ae θ hr'.1 hr'.2.1 hr'.2.2 hr.1 hr.2
      | ray => exact chain_ray_ae hr.1 hr.2
  | bushy θ =>
      cases r' with
      | binary => exact bushy_binary_ae θ hr.1 hr.2.1 hr.2.2
      | chain t => exact bushy_chain_ae θ hr.1 hr.2.1 hr.2.2 hr'.1 hr'.2
      | bushy θ' => simp [Regime.kind] at hk
      | ray => exact bushy_ray_ae θ hr.1 hr.2.1 hr.2.2
  | ray =>
      cases r' with
      | binary => exact ray_binary_ae
      | chain t => exact ray_chain_ae hr'.1 hr'.2
      | bushy θ => exact ray_bushy_ae θ hr'.1 hr'.2.1 hr'.2.2
      | ray => simp [Regime.kind] at hk

/-- **The ray is separated from the other three classes**: no sample outside the ray class is
quasi-isometric to the ray. -/
theorem not_ray_ae (r : Regime) (hr : r.Valid) (hray : r ≠ Regime.ray) :
    ∀ᵐ ω ∂(r.sampleLaw hr).law, ¬ QuasiIsometric ((r.sampleLaw hr).graph ω) rayGraph := by
  cases r with
  | binary => exact not_ray_binary
  | chain t => exact not_ray_chain hr.1 hr.2
  | bushy θ => exact not_ray_bushy θ hr.1 hr.2.1 hr.2.2 raysInBushyRegime
  | ray => exact absurd rfl hray

/-- **The offspring-`{0,1,2}` classification of `thm:trichotomy-simple`.** Two independent
samples, conditioned on survival, are almost surely quasi-isometric when their laws belong to the
same class and almost surely not quasi-isometric when their laws belong to different classes. No
sample outside the ray class is quasi-isometric to the ray. -/
theorem trichotomy_simple (r r' : Regime) (hr : r.Valid) (hr' : r'.Valid) :
    (r.kind = r'.kind → ∀ᵐ ω ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
        PairQI (r.sampleLaw hr) (r'.sampleLaw hr') ω)
      ∧ (r.kind ≠ r'.kind → ∀ᵐ ω ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
        ¬ PairQI (r.sampleLaw hr) (r'.sampleLaw hr') ω)
      ∧ (r ≠ Regime.ray → ∀ᵐ ω ∂(r.sampleLaw hr).law,
          ¬ QuasiIsometric ((r.sampleLaw hr).graph ω) rayGraph) :=
  ⟨same_regime_ae r r' hr hr', diff_regime_ae r r' hr hr', not_ray_ae r hr⟩

end ChainClasses
