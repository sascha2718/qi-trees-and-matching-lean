import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ChainClasses.Shape.Shape

/-!
`sec:shape-net` of `matching_classes_simple.tex`: `thm:dilution`, entropy
dilution.

The proof has three ingredients, and the two combinatorial ones are certified
here; the third, that a shape and its contraction are `2s`-comparable, is
geometric and waits on the metric realisation of shapes.

* **The cut.** A realisation is cut greedily: walking up from the leaves, the
  part being accumulated is cut off as soon as it reaches `s` vertices.
  `remSize_lt` is the invariant that the accumulator never reaches `s`,
  `maxPart_le` bounds every cut part by `2s-1`, and `cut_le` gives
  `s·(number of parts) + (remainder) ≤ |σ|`, hence
  `cutCount_le_div`: at most `|σ|/s` parts, and with the remainder at most
  `|σ|/s + 1`.
* **The count.** A tree is coded by a vertex of `𝔹`, recursively: the letter
  `1`, the codes of the children in order, then the letter `2` (`RTree.code`,
  with `true` for `1` and `false` for `2`), so the
  code has `2|t|` bits (`code_length`) and determines the tree
  (`code_append_inj`, in the strengthened form that it also determines the rest
  of the word). A marked tree is a tree together with one of its at most `K`
  vertices, so `dilution_count`: such a family has at most
  `2^{2K+1}·K = 2^{2K}·2K ≤ 2^{3K} = 8^K ≤ e^{3K}` members, the middle step
  being `two_mul_le_two_pow`.
* **The scale.** `s = ⌊(D/72)^{1/3}⌋` obeys `72s³ ≤ D < 72(s+1)³`, whence
  `D ≤ 729s³` (`cube_bound`) and `s^{-1} ≤ 9D^{-1/3}`
  (`inv_le_nine_rpow`), which turns the count `e^{3(n/s+1)}` into
  `e^{27(nD^{-1/3}+1)}`, the constant `c₀ = 27` of the statement. The regime
  `D ≤ 729` uses `D^{-1/3} ≥ 1/9` directly (`one_le_nine_rpow`).
-/

namespace ChainClasses

/-! ### The greedy cut of a realisation -/

namespace Tri

variable (s : ℕ)

/-- The size of the remainder left by the greedy cut at scale `s`: the part
being accumulated is cut off as soon as it reaches `s` vertices. -/
def remSize (s : ℕ) : Tri → ℕ
  | leaf => if s ≤ 1 then 0 else 1
  | one t => if s ≤ 1 + remSize s t then 0 else 1 + remSize s t
  | two l r =>
      if s ≤ 1 + remSize s l + remSize s r then 0 else 1 + remSize s l + remSize s r

/-- The number of parts the greedy cut produces. -/
def cutCount (s : ℕ) : Tri → ℕ
  | leaf => if s ≤ 1 then 1 else 0
  | one t => cutCount s t + if s ≤ 1 + remSize s t then 1 else 0
  | two l r =>
      cutCount s l + cutCount s r + if s ≤ 1 + remSize s l + remSize s r then 1 else 0

/-- The largest part the greedy cut produces, `0` if there is none. -/
def maxPart (s : ℕ) : Tri → ℕ
  | leaf => if s ≤ 1 then 1 else 0
  | one t => max (maxPart s t) (if s ≤ 1 + remSize s t then 1 + remSize s t else 0)
  | two l r =>
      max (max (maxPart s l) (maxPart s r))
        (if s ≤ 1 + remSize s l + remSize s r then 1 + remSize s l + remSize s r else 0)

/-- The invariant of the cut: the remainder never reaches `s` vertices. -/
lemma remSize_lt (hs : 1 ≤ s) (t : Tri) : remSize s t < s := by
  cases t <;> (rw [remSize]; split <;> omega)

/-- Every part has at most `2s-1` vertices: a cut is made at a vertex whose
children's remainders are each below `s`. -/
lemma maxPart_le (hs : 1 ≤ s) (t : Tri) : maxPart s t ≤ 2 * s - 1 := by
  induction t with
  | leaf => rw [maxPart]; split <;> omega
  | one t ih =>
      have hr := remSize_lt s hs t
      rw [maxPart]; split <;> omega
  | two l r ihl ihr =>
      have hrl := remSize_lt s hs l
      have hrr := remSize_lt s hs r
      rw [maxPart]; split <;> omega

/-- The parts are disjoint and each carries at least `s` vertices, so
`s·(number of parts) + (remainder) ≤ |t|`. -/
lemma cut_le (hs : 1 ≤ s) (t : Tri) : s * cutCount s t + remSize s t ≤ t.size := by
  induction t with
  | leaf =>
      by_cases h : s ≤ 1
      · simp only [cutCount, remSize, size, ite_eq_left h]; omega
      · simp only [cutCount, remSize, size, ite_eq_right h]; omega
  | one t ih =>
      by_cases h : s ≤ 1 + remSize s t
      · simp only [cutCount, remSize, size, ite_eq_left h, Nat.mul_add, Nat.mul_one]; omega
      · simp only [cutCount, remSize, size, ite_eq_right h, Nat.mul_add, Nat.mul_zero]; omega
  | two l r ihl ihr =>
      by_cases h : s ≤ 1 + remSize s l + remSize s r
      · simp only [cutCount, remSize, size, ite_eq_left h, Nat.mul_add, Nat.mul_one]; omega
      · simp only [cutCount, remSize, size, ite_eq_right h, Nat.mul_add, Nat.mul_zero]; omega

/-- **`thm:dilution`, the cut**: at most `|t|/s` parts are cut off, so the cut
and the remainder together are at most `|t|/s + 1` parts, each with at most
`2s-1` vertices. -/
theorem cutCount_le_div (hs : 1 ≤ s) (t : Tri) : cutCount s t ≤ t.size / s := by
  have h := cut_le s hs t
  have h1 : s * cutCount s t ≤ t.size := by omega
  rw [Nat.mul_comm] at h1
  exact (Nat.le_div_iff_mul_le (by omega)).mpr h1

end Tri

/-! ### Finite rooted trees and their codes -/

/-- Finite rooted trees of arbitrary arity: the contractions of
`thm:dilution`. -/
inductive RTree where
  | node : List RTree → RTree

namespace RTree

/-- The induction principle of the nested inductive: a property holds of every
tree once it is inherited from the children. -/
@[elab_as_elim]
theorem ind {P : RTree → Prop} (h : ∀ cs : List RTree, (∀ c ∈ cs, P c) → P (.node cs))
    (t : RTree) : P t :=
  RTree.rec (motive_1 := P) (motive_2 := fun cs => ∀ c ∈ cs, P c)
    (fun cs ih => h cs ih)
    (fun c hc => absurd hc (by simp))
    (fun _ _ ihh iht c hc => by
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact ihh
      · exact iht c hc')
    t

mutual

/-- The number of vertices. -/
def size : RTree → ℕ
  | .node cs => 1 + sizeF cs

/-- The number of vertices of a forest. -/
def sizeF : List RTree → ℕ
  | [] => 0
  | c :: cs => size c + sizeF cs

end

lemma size_pos (t : RTree) : 0 < t.size := by
  cases t with | node cs => rw [size]; omega

mutual

/-- The code of a tree as a vertex of `𝔹`: the letter `1`, the codes of the
children in order, then the letter `2`, written here with `true` for `1` and
`false` for `2`. -/
def code : RTree → List Bool
  | .node cs => true :: (codeF cs ++ [false])

/-- The codes of a forest, in order. -/
def codeF : List RTree → List Bool
  | [] => []
  | c :: cs => code c ++ codeF cs

end

/-- The code has two bits per vertex. -/
lemma code_length (t : RTree) : t.code.length = 2 * t.size := by
  have key : ∀ l : List RTree, (∀ c ∈ l, c.code.length = 2 * c.size) →
      (codeF l).length = 2 * sizeF l := by
    intro l
    induction l with
    | nil => simp [codeF, sizeF]
    | cons c cs ihcs =>
        intro hall
        have h1 := hall c (by simp)
        have h2 := ihcs fun x hx => hall x (by simp [hx])
        simp only [codeF, sizeF, List.length_append]
        omega
  induction t using ind with
  | _ cs ih =>
      have hk := key cs ih
      simp only [code, size, List.length_cons, List.length_append, List.length_nil]
      omega

/-- Every code begins with the letter `1`. -/
lemma code_eq_cons (t : RTree) : ∃ w, t.code = true :: w := by
  cases t with | node cs => exact ⟨codeF cs ++ [false], rfl⟩

/-- The code is prefix-free: a coded tree determines both itself and the rest
of the word. -/
theorem code_append_inj : ∀ (t₁ t₂ : RTree) (u₁ u₂ : List Bool),
    t₁.code ++ u₁ = t₂.code ++ u₂ → t₁ = t₂ ∧ u₁ = u₂ := by
  have key : ∀ (l₁ : List RTree),
      (∀ c ∈ l₁, ∀ (t₂ : RTree) (v₁ v₂ : List Bool),
        c.code ++ v₁ = t₂.code ++ v₂ → c = t₂ ∧ v₁ = v₂) →
      ∀ (l₂ : List RTree), ∀ u₁ u₂,
        codeF l₁ ++ false :: u₁ = codeF l₂ ++ false :: u₂ → l₁ = l₂ ∧ u₁ = u₂ := by
    intro l₁
    induction l₁ with
    | nil =>
        intro _ l₂ u₁ u₂ h
        cases l₂ with
        | nil => refine ⟨rfl, ?_⟩; simpa [codeF] using h
        | cons d ds =>
            obtain ⟨w, hw⟩ := code_eq_cons d
            simp [codeF, hw] at h
    | cons c cs ihcs =>
        intro hall l₂ u₁ u₂ h
        cases l₂ with
        | nil =>
            obtain ⟨w, hw⟩ := code_eq_cons c
            simp [codeF, hw] at h
        | cons d ds =>
            simp only [codeF, List.append_assoc] at h
            obtain ⟨hcd, h2⟩ := hall c (by simp) d (codeF cs ++ false :: u₁)
              (codeF ds ++ false :: u₂) h
            obtain ⟨hcs, hu⟩ := ihcs (fun x hx => hall x (by simp [hx])) ds u₁ u₂ h2
            exact ⟨by rw [hcd, hcs], hu⟩
  intro t₁
  induction t₁ using ind with
  | _ cs ih =>
      intro t₂ u₁ u₂ h
      cases t₂ with
      | node ds =>
          simp only [code, List.cons_append, List.cons.injEq, true_and,
            List.append_assoc] at h
          obtain ⟨hcs, hu⟩ := key cs ih ds u₁ u₂ h
          exact ⟨by rw [hcs], hu⟩

lemma code_injective : Function.Injective code := fun t₁ t₂ h =>
  (code_append_inj t₁ t₂ [] [] (by rw [h])).1

instance : Countable RTree := code_injective.countable

/-! ### The entropy count -/

/-- A bit word read as a binary numeral with a leading `1`, so that the length
is recorded and the reading is injective. -/
def bitVal : List Bool → ℕ
  | [] => 1
  | b :: w => 2 * bitVal w + b.toNat

lemma one_le_bitVal (w : List Bool) : 1 ≤ bitVal w := by
  induction w with
  | nil => simp [bitVal]
  | cons b w ih => rw [bitVal]; omega

lemma bitVal_lt (w : List Bool) : bitVal w < 2 ^ (w.length + 1) := by
  induction w with
  | nil => simp [bitVal]
  | cons b w ih =>
      have hb : b.toNat ≤ 1 := by cases b <;> simp
      rw [bitVal, List.length_cons, pow_succ]
      omega

lemma bitVal_injective : Function.Injective bitVal := by
  intro w₁
  induction w₁ with
  | nil =>
      intro w₂ h
      cases w₂ with
      | nil => rfl
      | cons b w =>
          have h1 := one_le_bitVal w
          have hb : b.toNat ≤ 1 := by cases b <;> simp
          rw [bitVal, bitVal] at h
          exfalso; omega
  | cons b₁ v₁ ih =>
      intro w₂ h
      cases w₂ with
      | nil =>
          have h1 := one_le_bitVal v₁
          have hb : b₁.toNat ≤ 1 := by cases b₁ <;> simp
          rw [bitVal, bitVal] at h
          exfalso; omega
      | cons b₂ v₂ =>
          rw [bitVal, bitVal] at h
          cases b₁ with
          | false =>
              cases b₂ with
              | false =>
                  simp only [Bool.toNat_false] at h
                  rw [ih (show bitVal v₁ = bitVal v₂ by omega)]
              | true =>
                  simp only [Bool.toNat_false, Bool.toNat_true] at h
                  exfalso; omega
          | true =>
              cases b₂ with
              | false =>
                  simp only [Bool.toNat_false, Bool.toNat_true] at h
                  exfalso; omega
              | true =>
                  simp only [Bool.toNat_true] at h
                  rw [ih (show bitVal v₁ = bitVal v₂ by omega)]

/-- `2K ≤ 2^K`, the room the choice of a marked vertex needs. -/
lemma two_mul_le_two_pow : ∀ K : ℕ, 2 * K ≤ 2 ^ K
  | 0 => by norm_num
  | 1 => by norm_num
  | (k + 2) => by
      have ih := two_mul_le_two_pow (k + 1)
      have h2 : 2 ≤ 2 ^ (k + 1) := by
        have : (2 : ℕ) ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using this
      have hpow : (2 : ℕ) ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by
        rw [pow_succ]; ring
      omega

/-- **`thm:dilution`, the count.** A family of rooted trees with a marked
vertex, pairwise distinct and each of at most `K` vertices, has at most
`8^K ≤ e^{3K}` members: the depth-first code has `2|t|` bits, and a marked tree
is a tree together with one of its at most `K` vertices. -/
theorem dilution_count (F : Finset (RTree × ℕ)) (K : ℕ)
    (hF : ∀ p ∈ F, p.1.size ≤ K ∧ p.2 < p.1.size) :
    (F.card : ℝ) ≤ Real.exp (3 * K) := by
  classical
  -- the code of the tree together with the index of the mark
  set enc : RTree × ℕ → ℕ × ℕ := fun p => (bitVal p.1.code, p.2) with henc
  have hmaps : ∀ p ∈ F, enc p ∈ Finset.range (2 ^ (2 * K + 1)) ×ˢ Finset.range K := by
    intro p hp
    obtain ⟨h1, h2⟩ := hF p hp
    have hlen := code_length p.1
    have hlt := bitVal_lt p.1.code
    have hmono : (2 : ℕ) ^ (p.1.code.length + 1) ≤ 2 ^ (2 * K + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (lt_of_lt_of_le hlt hmono),
        Finset.mem_range.mpr (lt_of_lt_of_le h2 h1)⟩
  have hinj : Set.InjOn enc (F : Set (RTree × ℕ)) := by
    intro p _ q _ h
    simp only [henc, Prod.mk.injEq] at h
    exact Prod.ext (code_injective (bitVal_injective h.1)) h.2
  have hcard : F.card ≤ 2 ^ (2 * K + 1) * K := by
    have := Finset.card_le_card_of_injOn enc hmaps hinj
    simpa [Finset.card_product] using this
  -- `2^{2K+1} K = 2^{2K} (2K) ≤ 2^{2K} 2^K = 8^K`
  have hpowK : F.card ≤ 2 ^ (3 * K) := by
    have hsplit : 2 ^ (2 * K + 1) * K = 2 ^ (2 * K) * (2 * K) := by rw [pow_succ]; ring
    have hmul : 2 ^ (2 * K) * (2 * K) ≤ 2 ^ (2 * K) * 2 ^ K :=
      Nat.mul_le_mul_left _ (two_mul_le_two_pow K)
    have hadd : (2 : ℕ) ^ (2 * K) * 2 ^ K = 2 ^ (3 * K) := by
      rw [← pow_add]; ring_nf
    omega
  -- `8^K ≤ e^{3K}`
  have hexp3 : (8 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2 : ℝ) ^ (3 : ℕ) ≤ Real.exp 1 ^ (3 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1 3
    rw [h2]; norm_num at h3; linarith
  have hpow : ((2 : ℝ) ^ (3 * K)) ≤ Real.exp (3 * K) := by
    have h1 : ((2 : ℝ) ^ (3 * K)) = (8 : ℝ) ^ K := by
      rw [pow_mul]; norm_num
    have h2 : Real.exp (3 * (K : ℝ)) = Real.exp 3 ^ K := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h1, h2]
    exact pow_le_pow_left₀ (by norm_num) hexp3 K
  calc (F.card : ℝ) ≤ ((2 ^ (3 * K) : ℕ) : ℝ) := by exact_mod_cast hpowK
    _ = (2 : ℝ) ^ (3 * K) := by push_cast; ring
    _ ≤ Real.exp (3 * K) := hpow

end RTree

/-! ### The scale of `thm:dilution` -/

/-- `s = ⌊(D/72)^{1/3}⌋ ≥ 2` gives `D ≤ 729s³`, so `D^{1/3} ≤ 9s`. -/
lemma cube_bound {D s : ℕ} (hs : 2 ≤ s) (hlt : D < 72 * (s + 1) ^ 3) : D ≤ 729 * s ^ 3 := by
  have h : 72 * (s + 1) ^ 3 ≤ 729 * s ^ 3 := by nlinarith [hs, sq_nonneg s]
  omega

/-- The regime `D > 729` of `thm:dilution`: `s^{-1} ≤ 9D^{-1/3}`. -/
lemma inv_le_nine_rpow {D s : ℕ} (hs : 1 ≤ s) (hD : 0 < D) (h : D ≤ 729 * s ^ 3) :
    (1 : ℝ) / s ≤ 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hcube : (D : ℝ) ^ ((1 : ℝ) / 3) ≤ 9 * s := by
    have hle : (D : ℝ) ≤ (9 * s) ^ (3 : ℕ) := by
      have : ((D : ℕ) : ℝ) ≤ ((729 * s ^ 3 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this ⊢
      nlinarith
    have h9 : (0 : ℝ) ≤ 9 * (s : ℝ) := by positivity
    calc (D : ℝ) ^ ((1 : ℝ) / 3) ≤ ((9 * (s : ℝ)) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hD0.le hle (by norm_num)
      _ = 9 * s := by
          rw [← Real.rpow_natCast (9 * (s : ℝ)) 3, ← Real.rpow_mul h9]
          norm_num
  have hpos : (0 : ℝ) < (D : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hD0 _
  have hneg : (D : ℝ) ^ (-(1 : ℝ) / 3) = ((D : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [← Real.rpow_neg hD0.le]
    norm_num
  rw [hneg, div_le_iff₀ hs0]
  have hinv0 : (0 : ℝ) < ((D : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by positivity
  have hxinv : (D : ℝ) ^ ((1 : ℝ) / 3) * ((D : ℝ) ^ ((1 : ℝ) / 3))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hpos)
  have hstep := mul_le_mul_of_nonneg_right hcube hinv0.le
  rw [hxinv] at hstep
  have hcomm : 9 * (s : ℝ) * ((D : ℝ) ^ ((1 : ℝ) / 3))⁻¹
      = 9 * ((D : ℝ) ^ ((1 : ℝ) / 3))⁻¹ * s := by ring
  linarith [hstep, hcomm.symm.le, hcomm.le]

/-- The regime `D ≤ 729` of `thm:dilution`: `1 ≤ 9D^{-1/3}`, so the crude count
`e^{3n}` is already `e^{27nD^{-1/3}}`. -/
lemma one_le_nine_rpow {D : ℕ} (hD : 0 < D) (h : D ≤ 729) :
    (1 : ℝ) ≤ 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) := by
  simpa using inv_le_nine_rpow (s := 1) le_rfl hD (by simpa using h)

end ChainClasses
