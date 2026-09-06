import Mathlib.Tactic
import ChainClasses.Chain.Labelling

/-!
`thm:transfer` of `matching_classes_simple.tex`, the Transfer lemma: multiplicative
comparability of two labellings gives a quasi-isometry of the associated trees.

* `IsQIWith`: the quasi-isometry predicate on subtrees of `𝒩`, with `ℕ` constants.
* `levelPhi`: the level map `l ↦ ⌊l·k'/(k+1)⌋` on one chain.
* `psi`: the map `ψ`, defined on normal forms via classical choice; `psi_apply`
  aligns it with the paper's formula, `levelPhi_le` is well-definedness.
* The three cases of the proof (same word, prefix, divergent), the coarse
  density estimate, and the packaging `transfer` into a `(D+3)`-quasi-isometry.
-/

namespace ChainClasses

/-- A `K`-quasi-isometry between vertex sets `T`, `T'` of the ambient tree. -/
structure IsQIWith (K : ℕ) (T T' : Word → Prop) (f : Word → Word) : Prop where
  maps : ∀ x, T x → T' (f x)
  upper : ∀ x y, T x → T y → treeDist (f x) (f y) ≤ K * treeDist x y + K
  lower : ∀ x y, T x → T y → treeDist x y ≤ K * treeDist (f x) (f y) + K * K
  dense : ∀ y', T' y' → ∃ x, T x ∧ treeDist (f x) y' ≤ K

/-- The level map on the chain of `w`: the paper's `⌊l·k'/(k+1)⌋` with
`k = lam w - 1`, `k' = lam' w - 1`. -/
def levelPhi (lam lam' : Word → ℕ) (w : Word) (l : ℕ) : ℕ := l * (lam' w - 1) / lam w

open Classical in
/-- The map `ψ` of `thm:transfer`, via classical choice on the normal form. -/
noncomputable def psi (lam lam' : Word → ℕ) (x : Word) : Word :=
  if h : InAssoc lam x then
    iotaL lam' h.choose ++ List.replicate (levelPhi lam lam' h.choose h.choose_spec.choose) false
  else x

/-- Well-definedness of `ψ`: the image level stays on the chain of `w`. -/
lemma levelPhi_le {lam lam' : Word → ℕ} (w : Word) (hw : 1 ≤ lam w) {l : ℕ}
    (hl : l ≤ lam w - 1) : levelPhi lam lam' w l ≤ lam' w - 1 := by
  have h1 : l * (lam' w - 1) ≤ (lam' w - 1) * lam w := by
    rw [mul_comm]
    exact Nat.mul_le_mul (le_refl _) (le_trans hl (Nat.sub_le _ _))
  calc levelPhi lam lam' w l ≤ (lam' w - 1) * lam w / lam w := Nat.div_le_div_right h1
    _ = lam' w - 1 := Nat.mul_div_cancel _ (by omega)

/-- `ψ` on a normal form: the paper's formula for `ψ`. -/
lemma psi_apply {lam lam' : Word → ℕ} (hlam : ∀ u, 1 ≤ lam u) {w : Word} {l : ℕ}
    (hl : l ≤ lam w - 1) :
    psi lam lam' (iotaL lam w ++ List.replicate l false)
      = iotaL lam' w ++ List.replicate (levelPhi lam lam' w l) false := by
  have hx : InAssoc lam (iotaL lam w ++ List.replicate l false) := ⟨w, l, hl, rfl⟩
  rw [psi, dif_pos hx]
  obtain ⟨hle, heq⟩ := hx.choose_spec.choose_spec
  obtain ⟨h1, h2⟩ := assoc_rep_unique lam hlam hle hl heq.symm
  rw [h2, h1]

/-! ### Division arithmetic for `eq:chain-ratio` -/

/-- Subadditivity of `ℕ`-division, with error one. -/
lemma add_div_le_add_div_succ {m : ℕ} (hm : 0 < m) (x y : ℕ) :
    (x + y) / m ≤ x / m + y / m + 1 := by
  rw [Nat.div_le_iff_le_mul_add_pred hm]
  have hx := Nat.div_add_mod x m
  have hy := Nat.div_add_mod y m
  have hmx := Nat.mod_lt x hm
  have hmy := Nat.mod_lt y hm
  have hexp : m * (x / m + y / m + 1) = m * (x / m) + m * (y / m) + m := by ring
  have h1 : m - 1 + 1 = m := by omega
  rw [hexp]
  linarith

/-- Superadditivity of `ℕ`-division. -/
lemma div_add_div_le {m : ℕ} (hm : 0 < m) (x y : ℕ) :
    x / m + y / m ≤ (x + y) / m := by
  rw [Nat.le_div_iff_mul_le hm]
  have hx : x / m * m ≤ x := Nat.div_mul_le_self x m
  have hy : y / m * m ≤ y := Nat.div_mul_le_self y m
  calc (x / m + y / m) * m = x / m * m + y / m * m := by ring
    _ ≤ x + y := Nat.add_le_add hx hy

/-- The upper half of `eq:chain-ratio`: `k'/(k+1) ≤ D` after scaling by `i`. -/
lemma mul_div_le_mul {m k D : ℕ} (hm : 0 < m) (hk : k + 1 ≤ D * m) (i : ℕ) :
    i * k / m ≤ D * i := by
  have h1 : i * k ≤ D * i * m := by
    calc i * k ≤ i * (D * m) := Nat.mul_le_mul (le_refl i) (by omega)
      _ = D * i * m := by ring
  calc i * k / m ≤ D * i * m / m := Nat.div_le_div_right h1
    _ = D * i := Nat.mul_div_cancel _ hm

/-- The lower half of `eq:chain-ratio`: `k'/(k+1) ≥ D⁻¹ - 1/(k+1)` after scaling
by `i ≤ m` and clearing denominators. -/
lemma le_mul_div_add {m k D : ℕ} (hm : 0 < m) (hmD : m ≤ D * (k + 1))
    {i : ℕ} (hi : i ≤ m) : i ≤ D * (i * k / m) + 2 * D := by
  have hq := Nat.div_add_mod (i * k) m
  have hr := Nat.mod_lt (i * k) hm
  have key : i * m ≤ (D * (i * k / m) + 2 * D) * m := by
    nlinarith [Nat.mul_le_mul (le_refl i) hmD, Nat.mul_le_mul (le_refl D) hi,
      Nat.mul_le_mul (le_refl D) hr.le]
  exact Nat.le_of_mul_le_mul_right key hm

/-- The same-chain estimates of `thm:transfer`: the image level difference
against the level difference, in both directions. -/
lemma same_word_bounds {m k D : ℕ} (hm : 0 < m) (hD : 1 ≤ D)
    (hup : k + 1 ≤ D * m) (hdown : m ≤ D * (k + 1))
    {u v : ℕ} (huv : u ≤ v) (hv : v ≤ m) :
    v * k / m - u * k / m ≤ D * (v - u) + 2 ∧
      v - u ≤ D * (v * k / m - u * k / m) + 4 * D := by
  obtain ⟨a, rfl⟩ := Nat.le.dest huv
  simp only [Nat.add_sub_cancel_left]
  have hstep : (u + a) * k / m ≤ u * k / m + D * a + 1 := by
    calc (u + a) * k / m = (u * k + a * k) / m := by rw [Nat.add_mul]
      _ ≤ u * k / m + a * k / m + 1 := add_div_le_add_div_succ hm _ _
      _ ≤ u * k / m + D * a + 1 :=
          Nat.add_le_add (Nat.add_le_add (le_refl _) (mul_div_le_mul hm hup a)) (le_refl 1)
  have hsuper : u * k / m + a * k / m ≤ (u + a) * k / m := by
    have h := div_add_div_le hm (u * k) (a * k)
    rwa [← Nat.add_mul] at h
  constructor
  · exact Nat.sub_le_of_le_add (by linarith)
  · have h5 : a ≤ D * (a * k / m) + 2 * D := le_mul_div_add hm hdown (by omega)
    have h7 : a * k / m ≤ (u + a) * k / m - u * k / m :=
      Nat.le_sub_of_add_le (by linarith)
    have h8 : D * (a * k / m) ≤ D * ((u + a) * k / m - u * k / m) :=
      Nat.mul_le_mul (le_refl D) h7
    linarith

/-- The tail estimate of the prefix case, upper direction: the identity
`k'+1 - l·k'/(k+1) = (k'/(k+1))(k+1-l) + 1` of the tex, bounded via
`eq:chain-ratio`, with `m = k+1 = l + a`. -/
lemma chain_tail_upper {m k D l a : ℕ} (hm : 0 < m) (hsplit : m = l + a)
    (hup : k + 1 ≤ D * m) : k + 1 ≤ l * k / m + D * a + 2 := by
  have hq := Nat.div_add_mod (l * k) m
  have hr := Nat.mod_lt (l * k) hm
  have hkm : k * m = k * l + k * a := by rw [hsplit]; ring
  have key : (k + 1) * m ≤ (l * k / m + D * a + 2) * m := by
    nlinarith [hkm, Nat.mul_le_mul hup (le_refl a)]
  exact Nat.le_of_mul_le_mul_right key hm

/-- The tail estimate of the prefix case, lower direction, in additive form:
`m - l ≤ D·(k+1 - l·k/m)` without truncated subtractions. -/
lemma chain_tail_lower {m k D l : ℕ} (hm : 0 < m) (hmD : m ≤ D * (k + 1))
    (hl : l ≤ m) : m + D * (l * k / m) ≤ l + D * (k + 1) := by
  obtain ⟨c, rfl⟩ := Nat.le.dest hl
  have hq := Nat.div_add_mod (l * k) (l + c)
  have hqD : D * ((l + c) * (l * k / (l + c))) ≤ D * (l * k) :=
    Nat.mul_le_mul (le_refl D) (Nat.le.intro hq)
  have key : (c + D * (l * k / (l + c))) * (l + c) ≤ D * (k + 1) * (l + c) := by
    nlinarith [hqD, Nat.mul_le_mul (le_refl c) hmD]
  have := Nat.le_of_mul_le_mul_right key hm
  linarith

/-- Well-definedness of the density witness: `⌊l'·m/(k+1)⌋ ≤ m - 1`. -/
lemma density_level {m k l' : ℕ} (hm : 0 < m) (hl' : l' ≤ k) :
    l' * m / (k + 1) ≤ m - 1 := by
  have h1 : l' * m / (k + 1) ≤ k * m / (k + 1) :=
    Nat.div_le_div_right (Nat.mul_le_mul hl' (le_refl m))
  have h2 : k * m / (k + 1) < m := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < k + 1)]
    nlinarith
  exact Nat.le_pred_of_lt (lt_of_le_of_lt h1 h2)

/-- The first density floor estimate of the tex: the composed floors do not
overshoot `l'`. -/
lemma density_le {m k l' : ℕ} (hm : 0 < m) :
    l' * m / (k + 1) * k / m ≤ l' := by
  have h1 : l' * m / (k + 1) * (k + 1) ≤ l' * m := Nat.div_mul_le_self _ _
  rw [Nat.div_le_iff_le_mul_add_pred hm]
  nlinarith [h1]

/-- The second density floor estimate of the tex: the composed floors undershoot
`l'` by at most `D + 2`. -/
lemma density_ge {m k D l' : ℕ} (hm : 0 < m) (hkD : k + 1 ≤ D * m) (hl' : l' ≤ k) :
    l' ≤ l' * m / (k + 1) * k / m + D + 2 := by
  have hq1 := Nat.div_add_mod (l' * m) (k + 1)
  have hr1 := Nat.mod_lt (l' * m) (show 0 < k + 1 by omega)
  have hq2 := Nat.div_add_mod (l' * m / (k + 1) * k) m
  have hr2 := Nat.mod_lt (l' * m / (k + 1) * k) hm
  set q1 := l' * m / (k + 1) with hq1def
  set r1 := l' * m % (k + 1) with hr1def
  set q2 := q1 * k / m with hq2def
  set r2 := q1 * k % m with hr2def
  have e1 : k * ((k + 1) * q1 + r1) = k * (l' * m) := by rw [hq1]
  have e2 : (k + 1) * (m * q2 + r2) = (k + 1) * (q1 * k) := by rw [hq2]
  have b1 : m * l' ≤ m * k := Nat.mul_le_mul (le_refl m) hl'
  have b2 : k * r1 ≤ k * k := Nat.mul_le_mul (le_refl k) (by omega : r1 ≤ k)
  have b3 : (k + 1) * r2 ≤ (k + 1) * m := Nat.mul_le_mul (le_refl (k + 1)) hr2.le
  have b4 : (k + 1) * (k + 1) ≤ (k + 1) * (D * m) := Nat.mul_le_mul (le_refl (k + 1)) hkD
  have key : m * (k + 1) * l' ≤ m * (k + 1) * (q2 + D + 2) := by
    nlinarith [e1, e2, b1, b2, b3, b4]
  exact Nat.le_of_mul_le_mul_left key (Nat.mul_pos hm (by omega))

/-! ### Length bookkeeping along prefixes -/

/-- The `ι`-length growth under `mu'` along a prefix is at most `D` times the
growth under `mu`, in additive form free of truncated subtraction. -/
lemma iotaL_length_add_le (mu mu' : Word → ℕ) (hmu : ∀ u, 1 ≤ mu u)
    (hmu' : ∀ u, 1 ≤ mu' u) {D : ℕ} (hcomp : ∀ u, mu' u ≤ D * mu u)
    {w w'' : Word} (h : w <+: w'') :
    (iotaL mu' w'').length + D * (iotaL mu w).length
      ≤ (iotaL mu' w).length + D * (iotaL mu w'').length := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc, iotaL_concat_length mu (hmu (w ++ u)) j,
        iotaL_concat_length mu' (hmu' (w ++ u)) j]
      have hc := hcomp (w ++ u)
      linarith [ih, hc]

/-- The distance of two vertices on one chain. -/
lemma treeDist_replicate (u : Word) (c : Bool) (l l' : ℕ) :
    treeDist (u ++ List.replicate l c) (u ++ List.replicate l' c)
      = max l l' - min l l' := by
  rw [treeDist, wedge_append_replicate]
  simp only [List.length_append, List.length_replicate]
  omega

/-! ### The three cases of `thm:transfer` -/

/-- Both estimates of `thm:transfer` when the two vertices lie on one chain. -/
lemma transfer_dist_same {lam lam' : Word → ℕ} {D : ℕ}
    (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hD : 1 ≤ D)
    (hcomp : ∀ u, lam u ≤ D * lam' u ∧ lam' u ≤ D * lam u) {w : Word} {l l' : ℕ}
    (hl : l ≤ lam w - 1) (hl' : l' ≤ lam w - 1) :
    treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
        (psi lam lam' (iotaL lam w ++ List.replicate l' false))
      ≤ D * treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w ++ List.replicate l' false) + 2 ∧
      treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w ++ List.replicate l' false)
        ≤ D * treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
            (psi lam lam' (iotaL lam w ++ List.replicate l' false)) + 4 * D := by
  have hm : 0 < lam w := hlam w
  have hk1 : lam' w - 1 + 1 = lam' w := by have := hlam' w; omega
  have hup : lam' w - 1 + 1 ≤ D * lam w := by rw [hk1]; exact (hcomp w).2
  have hdown : lam w ≤ D * (lam' w - 1 + 1) := by rw [hk1]; exact (hcomp w).1
  rw [psi_apply hlam hl, psi_apply hlam hl', treeDist_replicate, treeDist_replicate]
  rcases le_total l l' with hll | hll
  · have hmono : levelPhi lam lam' w l ≤ levelPhi lam lam' w l' :=
      Nat.div_le_div_right (Nat.mul_le_mul hll (le_refl _))
    rw [max_eq_right hll, min_eq_left hll, max_eq_right hmono, min_eq_left hmono]
    exact same_word_bounds hm hD hup hdown hll (le_trans hl' (Nat.sub_le _ _))
  · have hmono : levelPhi lam lam' w l' ≤ levelPhi lam lam' w l :=
      Nat.div_le_div_right (Nat.mul_le_mul hll (le_refl _))
    rw [max_eq_left hll, min_eq_right hll, max_eq_left hmono, min_eq_right hmono]
    exact same_word_bounds hm hD hup hdown hll (le_trans hl (Nat.sub_le _ _))

/-- Both estimates of `thm:transfer` when one word strictly precedes the other:
the vertices are nested, and both distances are length differences. -/
lemma transfer_dist_prefix {lam lam' : Word → ℕ} {D : ℕ}
    (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hD : 1 ≤ D)
    (hcomp : ∀ u, lam u ≤ D * lam' u ∧ lam' u ≤ D * lam u) {w w' : Word} {l l' : ℕ}
    (hpre : w <+: w') (hne : w ≠ w') (hl : l ≤ lam w - 1) (hl' : l' ≤ lam w' - 1) :
    treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
        (psi lam lam' (iotaL lam w' ++ List.replicate l' false))
      ≤ D * treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w' ++ List.replicate l' false) + 2 ∧
      treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w' ++ List.replicate l' false)
        ≤ D * treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
            (psi lam lam' (iotaL lam w' ++ List.replicate l' false)) + 4 * D := by
  have hxy := assoc_prefix lam hpre hne hl l'
  have hpsi := assoc_prefix lam' hpre hne (levelPhi_le w (hlam w) hl)
    (levelPhi lam lam' w' l')
  rw [psi_apply hlam hl, psi_apply hlam hl', treeDist_of_prefix hxy,
    treeDist_of_prefix hpsi]
  simp only [List.length_append, List.length_replicate]
  have hmw : 0 < lam w := hlam w
  have hmw' : 0 < lam w' := hlam w'
  have hk1 : lam' w - 1 + 1 = lam' w := by have := hlam' w; omega
  have hk1' : lam' w' - 1 + 1 = lam' w' := by have := hlam' w'; omega
  have hla : l ≤ lam w := le_trans hl (Nat.sub_le _ _)
  obtain ⟨a, ha⟩ := Nat.le.dest hla
  have hφ : levelPhi lam lam' w l ≤ lam' w :=
    le_trans (levelPhi_le w (hlam w) hl) (Nat.sub_le _ _)
  obtain ⟨A', hA'⟩ := Nat.le.dest hφ
  have htail_up : lam' w ≤ levelPhi lam lam' w l + D * a + 2 := by
    have h := chain_tail_upper hmw ha.symm (by rw [hk1]; exact (hcomp w).2)
    rw [hk1] at h
    exact h
  have htail_low : lam w + D * levelPhi lam lam' w l ≤ l + D * lam' w := by
    have h := chain_tail_lower hmw (by rw [hk1]; exact (hcomp w).1) hla
    rw [hk1] at h
    exact h
  have htip_up : levelPhi lam lam' w' l' ≤ D * l' :=
    mul_div_le_mul hmw' (by rw [hk1']; exact (hcomp w').2) l'
  have htip_low : l' ≤ D * levelPhi lam lam' w' l' + 2 * D :=
    le_mul_div_add hmw' (by rw [hk1']; exact (hcomp w').1) (le_trans hl' (Nat.sub_le _ _))
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
      have hlen1 := iotaL_length_add_le lam lam' hlam hlam' (fun u => (hcomp u).2) hstep
      have hlen2 := iotaL_length_add_le lam' lam hlam' hlam (fun u => (hcomp u).1) hstep
      rw [← hΔ, ← hΔ'] at hlen1 hlen2
      have hd1 : Δ' ≤ D * Δ := by linarith
      have hd2 : Δ ≤ D * Δ' := by linarith
      have e1 : (iotaL lam (w ++ j :: rest)).length + l' - ((iotaL lam w).length + l)
          = a + Δ + l' := by omega
      have e2 : (iotaL lam' (w ++ j :: rest)).length
            + levelPhi lam lam' (w ++ j :: rest) l'
            - ((iotaL lam' w).length + levelPhi lam lam' w l)
          = A' + Δ' + levelPhi lam lam' (w ++ j :: rest) l' := by omega
      rw [e1, e2]
      rw [← hA'] at htail_up
      rw [← hA', ← ha] at htail_low
      constructor
      · linarith [hd1, htip_up, htail_up]
      · linarith [hd2, htip_low, htail_low]

/-- Both estimates of `thm:transfer` when neither word precedes the other: the
wedges sit at the branch points over the common prefix, and both distances
split into two tip contributions. -/
lemma transfer_dist_diverge {lam lam' : Word → ℕ} {D : ℕ}
    (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hD : 1 ≤ D)
    (hcomp : ∀ u, lam u ≤ D * lam' u ∧ lam' u ≤ D * lam u) {w w' : Word} {l l' : ℕ}
    (h1 : ¬ w <+: w') (h2 : ¬ w' <+: w) (hl : l ≤ lam w - 1) (hl' : l' ≤ lam w' - 1) :
    treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
        (psi lam lam' (iotaL lam w' ++ List.replicate l' false))
      ≤ D * treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w' ++ List.replicate l' false) + 2 ∧
      treeDist (iotaL lam w ++ List.replicate l false)
          (iotaL lam w' ++ List.replicate l' false)
        ≤ D * treeDist (psi lam lam' (iotaL lam w ++ List.replicate l false))
            (psi lam lam' (iotaL lam w' ++ List.replicate l' false)) + 4 * D := by
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
  have hlenA := iotaL_length_add_le lam lam' hlam hlam' (fun u => (hcomp u).2) hpa
  have hlenA2 := iotaL_length_add_le lam' lam hlam' hlam (fun u => (hcomp u).1) hpa
  have hlenB := iotaL_length_add_le lam lam' hlam hlam' (fun u => (hcomp u).2) hpb
  have hlenB2 := iotaL_length_add_le lam' lam hlam' hlam (fun u => (hcomp u).1) hpb
  rw [← hΔa, ← hΔa'] at hlenA hlenA2
  rw [← hΔb, ← hΔb'] at hlenB hlenB2
  have hda1 : Δa' ≤ D * Δa := by linarith
  have hda2 : Δa ≤ D * Δa' := by linarith
  have hdb1 : Δb' ≤ D * Δb := by linarith
  have hdb2 : Δb ≤ D * Δb' := by linarith
  have hk1 : lam' w - 1 + 1 = lam' w := by have := hlam' w; omega
  have hk1' : lam' w' - 1 + 1 = lam' w' := by have := hlam' w'; omega
  have htipa_up : levelPhi lam lam' w l ≤ D * l :=
    mul_div_le_mul (hlam w) (by rw [hk1]; exact (hcomp w).2) l
  have htipa_low : l ≤ D * levelPhi lam lam' w l + 2 * D :=
    le_mul_div_add (hlam w) (by rw [hk1]; exact (hcomp w).1) (le_trans hl (Nat.sub_le _ _))
  have htipb_up : levelPhi lam lam' w' l' ≤ D * l' :=
    mul_div_le_mul (hlam w') (by rw [hk1']; exact (hcomp w').2) l'
  have htipb_low : l' ≤ D * levelPhi lam lam' w' l' + 2 * D :=
    le_mul_div_add (hlam w') (by rw [hk1']; exact (hcomp w').1) (le_trans hl' (Nat.sub_le _ _))
  have hp1 : 1 ≤ lam p := hlam p
  have hp1' : 1 ≤ lam' p := hlam' p
  have ed : treeDist (iotaL lam w ++ List.replicate l false)
      (iotaL lam w' ++ List.replicate l' false) = Δa + l + 1 + (Δb + l' + 1) := by omega
  have ed' : treeDist (iotaL lam' w ++ List.replicate (levelPhi lam lam' w l) false)
        (iotaL lam' w' ++ List.replicate (levelPhi lam lam' w' l') false)
      = Δa' + levelPhi lam lam' w l + 1 + (Δb' + levelPhi lam lam' w' l' + 1) := by omega
  rw [ed, ed']
  constructor
  · linarith [hda1, hdb1, htipa_up, htipb_up]
  · linarith [hda2, hdb2, htipa_low, htipb_low]

/-- The two distance estimates of `thm:transfer` for an arbitrary pair of
vertices, assembled from the three cases. -/
lemma transfer_bounds {lam lam' : Word → ℕ} {D : ℕ}
    (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u) (hD : 1 ≤ D)
    (hcomp : ∀ u, lam u ≤ D * lam' u ∧ lam' u ≤ D * lam u) {x y : Word}
    (hx : InAssoc lam x) (hy : InAssoc lam y) :
    treeDist (psi lam lam' x) (psi lam lam' y) ≤ D * treeDist x y + 2 ∧
      treeDist x y ≤ D * treeDist (psi lam lam' x) (psi lam lam' y) + 4 * D := by
  obtain ⟨w, l, hl, rfl⟩ := hx
  obtain ⟨w', l', hl', rfl⟩ := hy
  by_cases hww : w = w'
  · subst hww
    exact transfer_dist_same hlam hlam' hD hcomp hl hl'
  by_cases hp : w <+: w'
  · exact transfer_dist_prefix hlam hlam' hD hcomp hp hww hl hl'
  by_cases hp' : w' <+: w
  · have h := transfer_dist_prefix hlam hlam' hD hcomp hp' (Ne.symm hww) hl' hl
    refine ⟨?_, ?_⟩
    · rw [treeDist_comm (psi lam lam' (iotaL lam w ++ List.replicate l false)),
        treeDist_comm (iotaL lam w ++ List.replicate l false)]
      exact h.1
    · rw [treeDist_comm (iotaL lam w ++ List.replicate l false),
        treeDist_comm (psi lam lam' (iotaL lam w ++ List.replicate l false))]
      exact h.2
  · exact transfer_dist_diverge hlam hlam' hD hcomp hp hp' hl hl'

/-- Coarse density of `thm:transfer`: every vertex of the target tree lies
within `D + 2` of the image of the vertex at level `⌊l'·λ(w)/λ'(w)⌋`. -/
lemma transfer_dense {lam lam' : Word → ℕ} {D : ℕ}
    (hlam : ∀ u, 1 ≤ lam u) (hlam' : ∀ u, 1 ≤ lam' u)
    (hcomp : ∀ u, lam u ≤ D * lam' u ∧ lam' u ≤ D * lam u) {y' : Word}
    (hy' : InAssoc lam' y') :
    ∃ x, InAssoc lam x ∧ treeDist (psi lam lam' x) y' ≤ D + 2 := by
  obtain ⟨w, l', hl', rfl⟩ := hy'
  have hk1 : lam' w - 1 + 1 = lam' w := by have := hlam' w; omega
  set l := l' * lam w / lam' w with hldef
  have hlle : l ≤ lam w - 1 := by
    have h := density_level (m := lam w) (k := lam' w - 1) (hlam w) hl'
    rw [hk1] at h
    exact h
  refine ⟨iotaL lam w ++ List.replicate l false, ⟨w, l, hlle, rfl⟩, ?_⟩
  rw [psi_apply hlam hlle, treeDist_replicate]
  have hle : levelPhi lam lam' w l ≤ l' := by
    have h := density_le (m := lam w) (k := lam' w - 1) (l' := l') (hlam w)
    rw [hk1] at h
    exact h
  have hge : l' ≤ levelPhi lam lam' w l + D + 2 := by
    have h := density_ge (m := lam w) (k := lam' w - 1) (hlam w)
      (by rw [hk1]; exact (hcomp w).2) hl'
    rw [hk1] at h
    exact h
  rw [max_eq_right hle, min_eq_left hle]
  omega

/-- **The Transfer lemma** (`thm:transfer`): if two labellings are
multiplicatively `D`-comparable, then `ψ` is a `(D+3)`-quasi-isometry between
the associated trees. -/
theorem transfer {lam lam' : Word → ℕ} (hlam : ∀ u, 1 ≤ lam u)
    (hlam' : ∀ u, 1 ≤ lam' u) {D : ℕ} (hD : 1 ≤ D)
    (hcomp : ∀ u, lam u ≤ D * lam' u ∧ lam' u ≤ D * lam u) :
    IsQIWith (D + 3) (InAssoc lam) (InAssoc lam') (psi lam lam') := by
  constructor
  · rintro x ⟨w, l, hl, rfl⟩
    rw [psi_apply hlam hl]
    exact ⟨w, levelPhi lam lam' w l, levelPhi_le w (hlam w) hl, rfl⟩
  · intro x y hx hy
    have h := (transfer_bounds hlam hlam' hD hcomp hx hy).1
    have hmul : D * treeDist x y ≤ (D + 3) * treeDist x y :=
      Nat.mul_le_mul (by omega) (le_refl _)
    linarith
  · intro x y hx hy
    have h := (transfer_bounds hlam hlam' hD hcomp hx hy).2
    have hmul : D * treeDist (psi lam lam' x) (psi lam lam' y)
        ≤ (D + 3) * treeDist (psi lam lam' x) (psi lam lam' y) :=
      Nat.mul_le_mul (by omega) (le_refl _)
    have hsq : 4 * D ≤ (D + 3) * (D + 3) := by nlinarith
    linarith
  · intro y' hy'
    obtain ⟨x, hx, hd⟩ := transfer_dense hlam hlam' hcomp hy'
    exact ⟨x, hx, le_trans hd (by omega)⟩

end ChainClasses
