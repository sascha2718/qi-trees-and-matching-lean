/-
`thm:transfer` of `matching_classes_simple.tex` at a real constant: multiplicative
comparability of two labellings at a real constant `C ≥ 1` gives a `(C+3)`-quasi-isometry
of the associated trees, with the constant of the paper and no rounding.

The map is the `ψ` of `Transfer.lean`; only the numeric estimates change.  The `ℕ`-division
arithmetic of the level maps is compared against the real constant through the floor
bridges `q·m ≤ x` and `x < (q+1)·m`, and the distance bookkeeping of the three cases is
the one of `Transfer.lean` verbatim.

* `IsQIWithR`: the quasi-isometry predicate on subtrees of `𝒩` with a real constant.
* `mul_div_le_mulR`, `le_mul_div_addR`, `same_word_boundsR`, `chain_tail_upperR`,
  `chain_tail_lowerR`, `density_geR`, `iotaL_length_add_leR`: the real forms of the
  division estimates.
* `transfer_dist_sameR`, `transfer_dist_prefixR`, `transfer_dist_divergeR`,
  `transfer_boundsR`, `transfer_denseR`: the three cases and the density.
* `transferR`: **`thm:transfer` at a real constant**: comparability at `C` gives a
  `(C+3)`-quasi-isometry.
* `IsQIWithR.comp_isometry`: an isometry appended to a real quasi-isometry.
-/
import ChainClasses.Transfer

namespace ChainClasses

/-- A `C`-quasi-isometry between vertex sets `T`, `T'` of the ambient tree, at a real
constant: `def:qi` with the three constants equal to `C`, the lower bound carried in the
subtraction-free form `d ≤ C d' + C²`. -/
structure IsQIWithR (C : ℝ) (T T' : Word → Prop) (f : Word → Word) : Prop where
  maps : ∀ x, T x → T' (f x)
  upper : ∀ x y, T x → T y → (treeDist (f x) (f y) : ℝ) ≤ C * treeDist x y + C
  lower : ∀ x y, T x → T y → (treeDist x y : ℝ) ≤ C * treeDist (f x) (f y) + C * C
  dense : ∀ y', T' y' → ∃ x, T x ∧ (treeDist (f x) y' : ℝ) ≤ C

/-! ### Division arithmetic at a real constant -/

/-- The upper half of `eq:chain-ratio` at a real constant. -/
lemma mul_div_le_mulR {m k : ℕ} {C : ℝ} (hm : 0 < m) (hk : (k : ℝ) + 1 ≤ C * m) (i : ℕ) :
    ((i * k / m : ℕ) : ℝ) ≤ C * i := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine le_trans (Nat.cast_div_le) ?_
  rw [Nat.cast_mul, div_le_iff₀ hmR]
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

/-- The lower half of `eq:chain-ratio` at a real constant. -/
lemma le_mul_div_addR {m k i : ℕ} {C : ℝ} (hm : 0 < m) (hC : 1 ≤ C)
    (hmD : (m : ℝ) ≤ C * ((k : ℝ) + 1)) (hi : i ≤ m) :
    (i : ℝ) ≤ C * ((i * k / m : ℕ) : ℝ) + 2 * C := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hq := Nat.div_add_mod (i * k) m
  have hr := Nat.mod_lt (i * k) hm
  have he : (m : ℝ) * ((i * k / m : ℕ) : ℝ) + ((i * k % m : ℕ) : ℝ) = (i : ℝ) * k := by
    exact_mod_cast hq
  have hrR : ((i * k % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hr
  have hiR : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
  have key : (i : ℝ) * m ≤ (C * ((i * k / m : ℕ) : ℝ) + 2 * C) * m := by
    nlinarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) (i * k / m),
      mul_le_mul_of_nonneg_right hmD (Nat.cast_nonneg (α := ℝ) i)]
  exact le_of_mul_le_mul_right key hmR

/-- The same-chain estimates of `thm:transfer` at a real constant. -/
lemma same_word_boundsR {m k : ℕ} {C : ℝ} (hm : 0 < m) (hC : 1 ≤ C)
    (hup : (k : ℝ) + 1 ≤ C * m) (hdown : (m : ℝ) ≤ C * ((k : ℝ) + 1))
    {u v : ℕ} (huv : u ≤ v) (hv : v ≤ m) :
    ((v * k / m - u * k / m : ℕ) : ℝ) ≤ C * ((v - u : ℕ) : ℝ) + 2 ∧
      ((v - u : ℕ) : ℝ) ≤ C * ((v * k / m - u * k / m : ℕ) : ℝ) + 4 * C := by
  obtain ⟨a, rfl⟩ := Nat.le.dest huv
  simp only [Nat.add_sub_cancel_left]
  have hstep : (u + a) * k / m ≤ u * k / m + a * k / m + 1 := by
    calc (u + a) * k / m = (u * k + a * k) / m := by rw [Nat.add_mul]
      _ ≤ u * k / m + a * k / m + 1 := add_div_le_add_div_succ hm _ _
  have hsuper : u * k / m + a * k / m ≤ (u + a) * k / m := by
    have h := div_add_div_le hm (u * k) (a * k)
    rwa [← Nat.add_mul] at h
  have htipa : ((a * k / m : ℕ) : ℝ) ≤ C * a := mul_div_le_mulR hm hup a
  have htipa' : (a : ℝ) ≤ C * ((a * k / m : ℕ) : ℝ) + 2 * C :=
    le_mul_div_addR hm hC hdown (by omega)
  have hC0 : (0 : ℝ) ≤ C := by linarith
  constructor
  · have hsub : (u + a) * k / m - u * k / m ≤ a * k / m + 1 :=
      Nat.sub_le_iff_le_add.mpr (by linarith)
    have hcast : (((u + a) * k / m - u * k / m : ℕ) : ℝ) ≤ ((a * k / m : ℕ) : ℝ) + 1 := by
      exact_mod_cast hsub
    linarith
  · have hsub2 : a * k / m ≤ (u + a) * k / m - u * k / m :=
      Nat.le_sub_of_add_le (by linarith)
    have hcast : ((a * k / m : ℕ) : ℝ) ≤ (((u + a) * k / m - u * k / m : ℕ) : ℝ) := by
      exact_mod_cast hsub2
    nlinarith [mul_le_mul_of_nonneg_left hcast hC0]

/-- The tail estimate of the prefix case, upper direction, at a real constant. -/
lemma chain_tail_upperR {m k l a : ℕ} {C : ℝ} (hm : 0 < m) (hsplit : m = l + a)
    (hup : (k : ℝ) + 1 ≤ C * m) :
    (k : ℝ) + 1 ≤ ((l * k / m : ℕ) : ℝ) + C * a + 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hq := Nat.div_add_mod (l * k) m
  have hr := Nat.mod_lt (l * k) hm
  have he : (m : ℝ) * ((l * k / m : ℕ) : ℝ) + ((l * k % m : ℕ) : ℝ) = (l : ℝ) * k := by
    exact_mod_cast hq
  have hrR : ((l * k % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hr
  have hmsplit : (m : ℝ) = (l : ℝ) + (a : ℝ) := by exact_mod_cast hsplit
  have key : ((k : ℝ) + 1) * m ≤ (((l * k / m : ℕ) : ℝ) + C * a + 2) * m := by
    nlinarith [mul_le_mul_of_nonneg_right hup (Nat.cast_nonneg (α := ℝ) a),
      Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) a]
  exact le_of_mul_le_mul_right key hmR

/-- The tail estimate of the prefix case, lower direction, at a real constant. -/
lemma chain_tail_lowerR {m k l : ℕ} {C : ℝ} (hm : 0 < m) (hC : 1 ≤ C)
    (hmD : (m : ℝ) ≤ C * ((k : ℝ) + 1)) (hl : l ≤ m) :
    (m : ℝ) + C * ((l * k / m : ℕ) : ℝ) ≤ (l : ℝ) + C * ((k : ℝ) + 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdivN : l * k / m * m ≤ l * k := Nat.div_mul_le_self _ _
  have hdiv : (m : ℝ) * ((l * k / m : ℕ) : ℝ) ≤ (l : ℝ) * k := by
    have h : ((l * k / m * m : ℕ) : ℝ) ≤ ((l * k : ℕ) : ℝ) := by exact_mod_cast hdivN
    push_cast at h
    linarith
  have hlR : (l : ℝ) ≤ (m : ℝ) := by exact_mod_cast hl
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have key : ((m : ℝ) + C * ((l * k / m : ℕ) : ℝ)) * m ≤ ((l : ℝ) + C * ((k : ℝ) + 1)) * m := by
    nlinarith [mul_le_mul_of_nonneg_left hdiv hC0,
      mul_le_mul_of_nonneg_right hmD (show (0 : ℝ) ≤ (m : ℝ) - l by linarith),
      Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) l]
  exact le_of_mul_le_mul_right key hmR

/-- The second density floor estimate at a real constant: the composed floors undershoot
by at most `C + 2`. -/
lemma density_geR {m k l' : ℕ} {C : ℝ} (hm : 0 < m) (hkD : (k : ℝ) + 1 ≤ C * m)
    (hl' : l' ≤ k) :
    (l' : ℝ) ≤ ((l' * m / (k + 1) * k / m : ℕ) : ℝ) + C + 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hq1 := Nat.div_add_mod (l' * m) (k + 1)
  have hr1 := Nat.mod_lt (l' * m) (show 0 < k + 1 by omega)
  have hq2 := Nat.div_add_mod (l' * m / (k + 1) * k) m
  have hr2 := Nat.mod_lt (l' * m / (k + 1) * k) hm
  have he1 : ((k : ℝ) + 1) * ((l' * m / (k + 1) : ℕ) : ℝ) + ((l' * m % (k + 1) : ℕ) : ℝ)
      = (l' : ℝ) * m := by exact_mod_cast hq1
  have he2 : (m : ℝ) * ((l' * m / (k + 1) * k / m : ℕ) : ℝ)
      + ((l' * m / (k + 1) * k % m : ℕ) : ℝ)
      = ((l' * m / (k + 1) : ℕ) : ℝ) * k := by exact_mod_cast hq2
  have hb1 : (l' : ℝ) ≤ (k : ℝ) := by exact_mod_cast hl'
  have hbr1 : ((l' * m % (k + 1) : ℕ) : ℝ) ≤ (k : ℝ) := by
    have : l' * m % (k + 1) ≤ k := by omega
    exact_mod_cast this
  have hbr2 : ((l' * m / (k + 1) * k % m : ℕ) : ℝ) ≤ (m : ℝ) := by
    have : l' * m / (k + 1) * k % m ≤ m := hr2.le
    exact_mod_cast this
  have key : (m : ℝ) * ((k : ℝ) + 1) * l'
      ≤ (m : ℝ) * ((k : ℝ) + 1) * (((l' * m / (k + 1) * k / m : ℕ) : ℝ) + C + 2) := by
    nlinarith [he1, he2, hb1, hbr1, hbr2, hkD,
      Nat.cast_nonneg (α := ℝ) (l' * m / (k + 1)),
      Nat.cast_nonneg (α := ℝ) (l' * m % (k + 1)),
      Nat.cast_nonneg (α := ℝ) (l' * m / (k + 1) * k % m),
      Nat.cast_nonneg (α := ℝ) l', Nat.cast_nonneg (α := ℝ) k,
      mul_le_mul_of_nonneg_left hkD (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
  have hpos : (0 : ℝ) < (m : ℝ) * ((k : ℝ) + 1) := by positivity
  exact le_of_mul_le_mul_left key hpos

/-- The `ι`-length growth comparison along a prefix, at a real constant. -/
lemma iotaL_length_add_leR (mu mu' : Word → ℕ) (hmu : ∀ u, 1 ≤ mu u)
    (hmu' : ∀ u, 1 ≤ mu' u) {C : ℝ} (hcomp : ∀ u, ((mu' u : ℕ) : ℝ) ≤ C * mu u)
    {w w'' : Word} (h : w <+: w'') :
    ((iotaL mu' w'').length : ℝ) + C * (iotaL mu w).length
      ≤ ((iotaL mu' w).length : ℝ) + C * (iotaL mu w'').length := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc, iotaL_concat_length mu (hmu (w ++ u)) j,
        iotaL_concat_length mu' (hmu' (w ++ u)) j]
      have hc := hcomp (w ++ u)
      push_cast
      linarith

/-! ### The three cases of `thm:transfer` at a real constant -/

section Cases

variable {lam lam' : Word → ℕ} {C : ℝ}

/-- The two comparability hypotheses at one word, in the `(k, m)` shape the division
arithmetic reads, with `m = λ(w)` and `k = λ'(w) - 1`. -/
lemma cast_pred (hlam' : ∀ u, 1 ≤ lam' u) (w : Word) :
    ((lam' w - 1 : ℕ) : ℝ) = (lam' w : ℝ) - 1 := by
  rw [Nat.cast_sub (hlam' w), Nat.cast_one]

lemma hupR (hlam' : ∀ u, 1 ≤ lam' u)
    (hcomp : ∀ u, (lam u : ℝ) ≤ C * lam' u ∧ (lam' u : ℝ) ≤ C * lam u) (w : Word) :
    ((lam' w - 1 : ℕ) : ℝ) + 1 ≤ C * lam w := by
  rw [cast_pred hlam' w]
  have h := (hcomp w).2
  linarith

lemma hdownR (hlam' : ∀ u, 1 ≤ lam' u)
    (hcomp : ∀ u, (lam u : ℝ) ≤ C * lam' u ∧ (lam' u : ℝ) ≤ C * lam u) (w : Word) :
    (lam w : ℝ) ≤ C * (((lam' w - 1 : ℕ) : ℝ) + 1) := by
  rw [cast_pred hlam' w]
  have h := (hcomp w).1
  have he : (lam' w : ℝ) - 1 + 1 = (lam' w : ℝ) := by ring
  rw [he]
  exact h

/-- Both estimates of `thm:transfer` at a real constant when the two vertices lie on one
chain. -/
lemma transfer_dist_sameR (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hC : 1 ≤ C)
    (hcomp : ∀ u, (lam u : ℝ) ≤ C * lam' u ∧ (lam' u : ℝ) ≤ C * lam u) {w : Word} {l l' : ℕ}
    (hl : l ≤ lam w - 1) (hl' : l' ≤ lam w - 1) :
    (treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
        (psi lam lam' (iotaL lam w ++ List.replicate l' false)) : ℝ)
      ≤ C * treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w ++ List.replicate l' false) + 2 ∧
      (treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w ++ List.replicate l' false) : ℝ)
        ≤ C * treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
            (psi lam lam' (iotaL lam w ++ List.replicate l' false)) + 4 * C := by
  have hm : 0 < lam w := hlam w
  rw [psi_apply hlam hl, psi_apply hlam hl', treeDist_replicate, treeDist_replicate]
  rcases le_total l l' with hll | hll
  · have hmono : levelPhi lam lam' w l ≤ levelPhi lam lam' w l' :=
      Nat.div_le_div_right (Nat.mul_le_mul hll (le_refl _))
    rw [max_eq_right hll, min_eq_left hll, max_eq_right hmono, min_eq_left hmono]
    exact same_word_boundsR hm hC (hupR hlam' hcomp w) (hdownR hlam' hcomp w) hll
      (le_trans hl' (Nat.sub_le _ _))
  · have hmono : levelPhi lam lam' w l' ≤ levelPhi lam lam' w l :=
      Nat.div_le_div_right (Nat.mul_le_mul hll (le_refl _))
    rw [max_eq_left hll, min_eq_right hll, max_eq_left hmono, min_eq_right hmono]
    exact same_word_boundsR hm hC (hupR hlam' hcomp w) (hdownR hlam' hcomp w) hll
      (le_trans hl (Nat.sub_le _ _))

/-- Both estimates of `thm:transfer` at a real constant when one word strictly precedes
the other. -/
lemma transfer_dist_prefixR (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hC : 1 ≤ C)
    (hcomp : ∀ u, (lam u : ℝ) ≤ C * lam' u ∧ (lam' u : ℝ) ≤ C * lam u) {w w' : Word}
    {l l' : ℕ}
    (hpre : w <+: w') (hne : w ≠ w') (hl : l ≤ lam w - 1) (hl' : l' ≤ lam w' - 1) :
    (treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
        (psi lam lam' (iotaL lam w' ++ List.replicate l' false)) : ℝ)
      ≤ C * treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w' ++ List.replicate l' false) + 2 ∧
      (treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w' ++ List.replicate l' false) : ℝ)
        ≤ C * treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
            (psi lam lam' (iotaL lam w' ++ List.replicate l' false)) + 4 * C := by
  have hxy := assoc_prefix lam hpre hne hl l'
  have hpsi := assoc_prefix lam' hpre hne (levelPhi_le w (hlam w) hl)
    (levelPhi lam lam' w' l')
  rw [psi_apply hlam hl, psi_apply hlam hl', treeDist_of_prefix hxy,
    treeDist_of_prefix hpsi]
  simp only [List.length_append, List.length_replicate]
  have hmw : 0 < lam w := hlam w
  have hmw' : 0 < lam w' := hlam w'
  have hla : l ≤ lam w := le_trans hl (Nat.sub_le _ _)
  obtain ⟨a, ha⟩ := Nat.le.dest hla
  have hφ : levelPhi lam lam' w l ≤ lam' w :=
    le_trans (levelPhi_le w (hlam w) hl) (Nat.sub_le _ _)
  obtain ⟨A', hA'⟩ := Nat.le.dest hφ
  have hA'R : ((levelPhi lam lam' w l : ℕ) : ℝ) + (A' : ℝ) = (lam' w : ℝ) := by
    exact_mod_cast hA'
  have haR : (l : ℝ) + (a : ℝ) = (lam w : ℝ) := by exact_mod_cast ha
  have htail_upR : (lam' w : ℝ) ≤ ((levelPhi lam lam' w l : ℕ) : ℝ) + C * a + 2 := by
    have h := chain_tail_upperR (C := C) hmw ha.symm (hupR hlam' hcomp w)
    have h2 : ((l * (lam' w - 1) / lam w : ℕ) : ℝ)
        = ((levelPhi lam lam' w l : ℕ) : ℝ) := rfl
    rw [h2, cast_pred hlam' w] at h
    linarith
  have htail_lowR : (lam w : ℝ) + C * ((levelPhi lam lam' w l : ℕ) : ℝ)
      ≤ (l : ℝ) + C * lam' w := by
    have h := chain_tail_lowerR (C := C) hmw hC (hdownR hlam' hcomp w) hla
    have h2 : ((l * (lam' w - 1) / lam w : ℕ) : ℝ)
        = ((levelPhi lam lam' w l : ℕ) : ℝ) := rfl
    rw [h2, cast_pred hlam' w] at h
    have he : (lam' w : ℝ) - 1 + 1 = (lam' w : ℝ) := by ring
    rw [he] at h
    exact h
  have htip_upR : ((levelPhi lam lam' w' l' : ℕ) : ℝ) ≤ C * l' := by
    have h := mul_div_le_mulR (C := C) hmw' (hupR hlam' hcomp w') l'
    exact h
  have htip_lowR : (l' : ℝ) ≤ C * ((levelPhi lam lam' w' l' : ℕ) : ℝ) + 2 * C := by
    have h := le_mul_div_addR (C := C) hmw' hC (hdownR hlam' hcomp w')
      (le_trans hl' (Nat.sub_le _ _))
    exact h
  obtain ⟨u, rfl⟩ := hpre
  cases u with
  | nil => exact absurd (by simp) hne
  | cons j rest =>
      have hstep : w ++ [j] <+: w ++ j :: rest := ⟨rest, by simp⟩
      obtain ⟨Δ, hΔ⟩ := Nat.le.dest (iotaL_prefix lam hstep).length_le
      obtain ⟨Δ', hΔ'⟩ := Nat.le.dest (iotaL_prefix lam' hstep).length_le
      have hcl : (iotaL lam (w ++ [j])).length = (iotaL lam w).length + lam w :=
        iotaL_concat_length lam (hlam w) j
      have hcl' : (iotaL lam' (w ++ [j])).length = (iotaL lam' w).length + lam' w :=
        iotaL_concat_length lam' (hlam' w) j
      have hd1R : (Δ' : ℝ) ≤ C * Δ := by
        have h1 := iotaL_length_add_leR lam lam' hlam hlam'
          (fun u ↦ (hcomp u).2) hstep
        have ebig : ((iotaL lam (w ++ j :: rest)).length : ℝ)
            = ((iotaL lam (w ++ [j])).length : ℝ) + Δ := by exact_mod_cast hΔ.symm
        have ebig' : ((iotaL lam' (w ++ j :: rest)).length : ℝ)
            = ((iotaL lam' (w ++ [j])).length : ℝ) + Δ' := by exact_mod_cast hΔ'.symm
        rw [ebig, ebig'] at h1
        linarith
      have hd2R : (Δ : ℝ) ≤ C * Δ' := by
        have h1 := iotaL_length_add_leR lam' lam hlam' hlam
          (fun u ↦ (hcomp u).1) hstep
        have ebig : ((iotaL lam (w ++ j :: rest)).length : ℝ)
            = ((iotaL lam (w ++ [j])).length : ℝ) + Δ := by exact_mod_cast hΔ.symm
        have ebig' : ((iotaL lam' (w ++ j :: rest)).length : ℝ)
            = ((iotaL lam' (w ++ [j])).length : ℝ) + Δ' := by exact_mod_cast hΔ'.symm
        rw [ebig, ebig'] at h1
        linarith
      have e1 : (iotaL lam (w ++ j :: rest)).length + l' - ((iotaL lam w).length + l)
          = a + Δ + l' := by
        omega
      have e2 : (iotaL lam' (w ++ j :: rest)).length
            + levelPhi lam lam' (w ++ j :: rest) l'
            - ((iotaL lam' w).length + levelPhi lam lam' w l)
          = A' + Δ' + levelPhi lam lam' (w ++ j :: rest) l' := by
        omega
      rw [e1, e2]
      have hAbound : (A' : ℝ) ≤ C * a + 2 := by linarith
      have habound : (a : ℝ) ≤ C * A' := by
        have h := htail_lowR
        nlinarith [hA'R, haR, htail_lowR]
      have htipc_upR : ((levelPhi lam lam' (w ++ j :: rest) l' : ℕ) : ℝ) ≤ C * l' :=
        htip_upR
      have htipc_lowR : (l' : ℝ)
          ≤ C * ((levelPhi lam lam' (w ++ j :: rest) l' : ℕ) : ℝ) + 2 * C := htip_lowR
      constructor
      · push_cast
        linarith [htipc_upR, hAbound, hd1R]
      · push_cast
        have hC0 : (0 : ℝ) ≤ C := by linarith
        linarith [htipc_lowR, habound, hd2R]

/-- Both estimates of `thm:transfer` at a real constant when neither word precedes the
other. -/
lemma transfer_dist_divergeR (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hC : 1 ≤ C)
    (hcomp : ∀ u, (lam u : ℝ) ≤ C * lam' u ∧ (lam' u : ℝ) ≤ C * lam u) {w w' : Word}
    {l l' : ℕ}
    (h1 : ¬ w <+: w') (h2 : ¬ w' <+: w) (hl : l ≤ lam w - 1) (hl' : l' ≤ lam w' - 1) :
    (treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
        (psi lam lam' (iotaL lam w' ++ List.replicate l' false)) : ℝ)
      ≤ C * treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w' ++ List.replicate l' false) + 2 ∧
      (treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w' ++ List.replicate l' false) : ℝ)
        ≤ C * treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
            (psi lam lam' (iotaL lam w' ++ List.replicate l' false)) + 4 * C := by
  obtain ⟨p, a, b, hab, hpa, hpb⟩ := exists_diverge h1 h2
  rw [psi_apply hlam hl, psi_apply hlam hl']
  have ht1 := treeDist_add_wedge_length (iotaL lam w ++ List.replicate l false)
    (iotaL lam w' ++ List.replicate l' false)
  rw [assoc_wedge_diverge lam hab hpa hpb l l'] at ht1
  have ht2 := treeDist_add_wedge_length
    (iotaL lam' w ++ List.replicate (levelPhi lam lam' w l) false)
    (iotaL lam' w' ++ List.replicate (levelPhi lam lam' w' l') false)
  rw [assoc_wedge_diverge lam' hab hpa hpb _ _] at ht2
  simp only [List.length_append, List.length_replicate] at ht1 ht2
  obtain ⟨Δa, hΔa⟩ := Nat.le.dest (iotaL_prefix lam hpa).length_le
  obtain ⟨Δb, hΔb⟩ := Nat.le.dest (iotaL_prefix lam hpb).length_le
  obtain ⟨Δa', hΔa'⟩ := Nat.le.dest (iotaL_prefix lam' hpa).length_le
  obtain ⟨Δb', hΔb'⟩ := Nat.le.dest (iotaL_prefix lam' hpb).length_le
  have hca : (iotaL lam (p ++ [a])).length = (iotaL lam p).length + lam p :=
    iotaL_concat_length lam (hlam p) a
  have hcb : (iotaL lam (p ++ [b])).length = (iotaL lam p).length + lam p :=
    iotaL_concat_length lam (hlam p) b
  have hca' : (iotaL lam' (p ++ [a])).length = (iotaL lam' p).length + lam' p :=
    iotaL_concat_length lam' (hlam' p) a
  have hcb' : (iotaL lam' (p ++ [b])).length = (iotaL lam' p).length + lam' p :=
    iotaL_concat_length lam' (hlam' p) b
  have hda1 : (Δa' : ℝ) ≤ C * Δa := by
    have hh := iotaL_length_add_leR lam lam' hlam hlam' (fun u ↦ (hcomp u).2) hpa
    have ebig : ((iotaL lam w).length : ℝ) = ((iotaL lam (p ++ [a])).length : ℝ) + Δa := by
      exact_mod_cast hΔa.symm
    have ebig' : ((iotaL lam' w).length : ℝ)
        = ((iotaL lam' (p ++ [a])).length : ℝ) + Δa' := by exact_mod_cast hΔa'.symm
    rw [ebig, ebig'] at hh
    linarith
  have hda2 : (Δa : ℝ) ≤ C * Δa' := by
    have hh := iotaL_length_add_leR lam' lam hlam' hlam (fun u ↦ (hcomp u).1) hpa
    have ebig : ((iotaL lam w).length : ℝ) = ((iotaL lam (p ++ [a])).length : ℝ) + Δa := by
      exact_mod_cast hΔa.symm
    have ebig' : ((iotaL lam' w).length : ℝ)
        = ((iotaL lam' (p ++ [a])).length : ℝ) + Δa' := by exact_mod_cast hΔa'.symm
    rw [ebig, ebig'] at hh
    linarith
  have hdb1 : (Δb' : ℝ) ≤ C * Δb := by
    have hh := iotaL_length_add_leR lam lam' hlam hlam' (fun u ↦ (hcomp u).2) hpb
    have ebig : ((iotaL lam w').length : ℝ) = ((iotaL lam (p ++ [b])).length : ℝ) + Δb := by
      exact_mod_cast hΔb.symm
    have ebig' : ((iotaL lam' w').length : ℝ)
        = ((iotaL lam' (p ++ [b])).length : ℝ) + Δb' := by exact_mod_cast hΔb'.symm
    rw [ebig, ebig'] at hh
    linarith
  have hdb2 : (Δb : ℝ) ≤ C * Δb' := by
    have hh := iotaL_length_add_leR lam' lam hlam' hlam (fun u ↦ (hcomp u).1) hpb
    have ebig : ((iotaL lam w').length : ℝ) = ((iotaL lam (p ++ [b])).length : ℝ) + Δb := by
      exact_mod_cast hΔb.symm
    have ebig' : ((iotaL lam' w').length : ℝ)
        = ((iotaL lam' (p ++ [b])).length : ℝ) + Δb' := by exact_mod_cast hΔb'.symm
    rw [ebig, ebig'] at hh
    linarith
  have htipa_up : ((levelPhi lam lam' w l : ℕ) : ℝ) ≤ C * l :=
    mul_div_le_mulR (hlam w) (hupR hlam' hcomp w) l
  have htipa_low : (l : ℝ) ≤ C * ((levelPhi lam lam' w l : ℕ) : ℝ) + 2 * C :=
    le_mul_div_addR (hlam w) hC (hdownR hlam' hcomp w) (le_trans hl (Nat.sub_le _ _))
  have htipb_up : ((levelPhi lam lam' w' l' : ℕ) : ℝ) ≤ C * l' :=
    mul_div_le_mulR (hlam w') (hupR hlam' hcomp w') l'
  have htipb_low : (l' : ℝ) ≤ C * ((levelPhi lam lam' w' l' : ℕ) : ℝ) + 2 * C :=
    le_mul_div_addR (hlam w') hC (hdownR hlam' hcomp w') (le_trans hl' (Nat.sub_le _ _))
  have hp1 : 1 ≤ lam p := hlam p
  have hp1' : 1 ≤ lam' p := hlam' p
  have ed : treeDist (iotaL lam w ++ List.replicate l false)
      (iotaL lam w' ++ List.replicate l' false) = Δa + l + 1 + (Δb + l' + 1) := by omega
  have ed' : treeDist (iotaL lam' w ++ List.replicate (levelPhi lam lam' w l) false)
        (iotaL lam' w' ++ List.replicate (levelPhi lam lam' w' l') false)
      = Δa' + levelPhi lam lam' w l + 1 + (Δb' + levelPhi lam lam' w' l' + 1) := by omega
  rw [ed, ed']
  have hC0 : (0 : ℝ) ≤ C := by linarith
  constructor
  · push_cast
    linarith [hda1, hdb1, htipa_up, htipb_up]
  · push_cast
    linarith [hda2, hdb2, htipa_low, htipb_low]

/-- The two distance estimates of `thm:transfer` at a real constant, assembled from the
three cases. -/
lemma transfer_boundsR (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hC : 1 ≤ C)
    (hcomp : ∀ u, (lam u : ℝ) ≤ C * lam' u ∧ (lam' u : ℝ) ≤ C * lam u) {x y : Word}
    (hx : InAssoc lam x) (hy : InAssoc lam y) :
    (treeDist (psi lam lam' x) (psi lam lam' y) : ℝ) ≤ C * treeDist x y + 2 ∧
      (treeDist x y : ℝ) ≤ C * treeDist (psi lam lam' x) (psi lam lam' y) + 4 * C := by
  obtain ⟨w, l, hl, rfl⟩ := hx
  obtain ⟨w', l', hl', rfl⟩ := hy
  by_cases hww : w = w'
  · subst hww
    exact transfer_dist_sameR hlam hlam' hC hcomp hl hl'
  by_cases hp : w <+: w'
  · exact transfer_dist_prefixR hlam hlam' hC hcomp hp hww hl hl'
  by_cases hp' : w' <+: w
  · have h := transfer_dist_prefixR hlam hlam' hC hcomp hp' (Ne.symm hww) hl' hl
    refine ⟨?_, ?_⟩
    · rw [treeDist_comm (psi lam lam' (iotaL lam w ++ List.replicate l false)),
        treeDist_comm (iotaL lam w ++ List.replicate l false)]
      exact h.1
    · rw [treeDist_comm (iotaL lam w ++ List.replicate l false),
        treeDist_comm (psi lam lam' (iotaL lam w ++ List.replicate l false))]
      exact h.2
  · exact transfer_dist_divergeR hlam hlam' hC hcomp hp hp' hl hl'

/-- Coarse density of `thm:transfer` at a real constant: every vertex of the target tree
lies within `C + 2` of an image. -/
lemma transfer_denseR (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u)
    (hcomp : ∀ u, (lam u : ℝ) ≤ C * lam' u ∧ (lam' u : ℝ) ≤ C * lam u) {y' : Word}
    (hy' : InAssoc lam' y') :
    ∃ x, InAssoc lam x ∧ (treeDist (psi lam lam' x) y' : ℝ) ≤ C + 2 := by
  obtain ⟨w, l', hl', rfl⟩ := hy'
  have hk1 : lam' w - 1 + 1 = lam' w := by have := hlam' w; omega
  set l := l' * lam w / (lam' w - 1 + 1) with hldef
  have hlle : l ≤ lam w - 1 := density_level (m := lam w) (k := lam' w - 1) (hlam w) hl'
  refine ⟨iotaL lam w ++ List.replicate l false, ⟨w, l, hlle, rfl⟩, ?_⟩
  rw [psi_apply hlam hlle, treeDist_replicate]
  have hle : levelPhi lam lam' w l ≤ l' :=
    density_le (m := lam w) (k := lam' w - 1) (l' := l') (hlam w)
  have hge : (l' : ℝ) ≤ ((levelPhi lam lam' w l : ℕ) : ℝ) + C + 2 :=
    density_geR (m := lam w) (k := lam' w - 1) (hlam w) (hupR hlam' hcomp w) hl'
  rw [max_eq_right hle, min_eq_left hle]
  have hcast : ((l' - levelPhi lam lam' w l : ℕ) : ℝ)
      = (l' : ℝ) - ((levelPhi lam lam' w l : ℕ) : ℝ) := Nat.cast_sub hle
  rw [hcast]
  linarith

/-- **The Transfer lemma at a real constant** (`thm:transfer`): if two labellings are
multiplicatively `C`-comparable for a real `C ≥ 1`, then `ψ` is a `(C+3)`-quasi-isometry
between the associated trees, with the constant of the paper and no rounding. -/
theorem transferR (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hC : 1 ≤ C)
    (hcomp : ∀ u, (lam u : ℝ) ≤ C * lam' u ∧ (lam' u : ℝ) ≤ C * lam u) :
    IsQIWithR (C + 3) (InAssoc lam) (InAssoc lam') (psi lam lam') := by
  constructor
  · rintro x ⟨w, l, hl, rfl⟩
    rw [psi_apply hlam hl]
    exact ⟨w, levelPhi lam lam' w l, levelPhi_le w (hlam w) hl, rfl⟩
  · intro x y hx hy
    have h := (transfer_boundsR hlam hlam' hC hcomp hx hy).1
    have hd0 : (0 : ℝ) ≤ (treeDist x y : ℝ) := Nat.cast_nonneg _
    nlinarith
  · intro x y hx hy
    have h := (transfer_boundsR hlam hlam' hC hcomp hx hy).2
    have hd0 : (0 : ℝ) ≤ (treeDist (psi lam lam' x) (psi lam lam' y) : ℝ) := Nat.cast_nonneg _
    nlinarith
  · intro y' hy'
    obtain ⟨x, hx, hd⟩ := transfer_denseR hlam hlam' hcomp hy'
    exact ⟨x, hx, by linarith⟩

/-- A real quasi-isometry followed by an isometry onto a third tree is a real
quasi-isometry with the same constant. -/
lemma IsQIWithR.comp_isometry {C : ℝ} {T T₂ T' : Word → Prop} {f g : Word → Word}
    (hf : IsQIWithR C T T₂ f) (hmaps : ∀ x, T₂ x → T' (g x))
    (honto : ∀ y, T' y → ∃ x, T₂ x ∧ g x = y)
    (hdist : ∀ x y, T₂ x → T₂ y → treeDist (g x) (g y) = treeDist x y) :
    IsQIWithR C T T' (fun x ↦ g (f x)) := by
  refine ⟨fun x hx ↦ hmaps _ (hf.maps x hx), fun x y hx hy ↦ ?_, fun x y hx hy ↦ ?_,
    fun y' hy' ↦ ?_⟩
  · rw [hdist _ _ (hf.maps x hx) (hf.maps y hy)]
    exact hf.upper x y hx hy
  · rw [hdist _ _ (hf.maps x hx) (hf.maps y hy)]
    exact hf.lower x y hx hy
  · obtain ⟨z, hz, rfl⟩ := honto y' hy'
    obtain ⟨x, hx, hd⟩ := hf.dense z hz
    exact ⟨x, hx, by rw [hdist _ _ (hf.maps x hx) hz]; exact hd⟩

/-- An integer quasi-isometry is a real one at the cast constant. -/
lemma IsQIWithR.of_isQIWith {K : ℕ} {T T' : Word → Prop} {f : Word → Word}
    (hf : IsQIWith K T T' f) : IsQIWithR (K : ℝ) T T' f := by
  refine ⟨hf.maps, fun x y hx hy ↦ ?_, fun x y hx hy ↦ ?_, fun y' hy' ↦ ?_⟩
  · have h := hf.upper x y hx hy
    have hcast : (treeDist (f x) (f y) : ℝ) ≤ ((K * treeDist x y + K : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hcast
    linarith
  · have h := hf.lower x y hx hy
    have hcast : (treeDist x y : ℝ) ≤ ((K * treeDist (f x) (f y) + K * K : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hcast
    linarith
  · obtain ⟨x, hx, hd⟩ := hf.dense y' hy'
    exact ⟨x, hx, by exact_mod_cast hd⟩

end Cases



end ChainClasses
