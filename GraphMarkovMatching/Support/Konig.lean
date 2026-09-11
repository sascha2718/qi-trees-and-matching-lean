/-
The infinite-tree König step for `G_k`. A restricted automorphism of `𝔹_{n+1}` restricts to one
of `𝔹_n` at the same phase (`restrictAutK`), and restriction preserves matching
(`fullMatchesK_restrict`). So if a matching automorphism exists at every finite
height, the sets `𝓕_n ⊆ AutK k m n` are nonempty and finite and form an
infinite, finitely-branching tree; Kőnig's infinity lemma
(`exists_seq_forall_proj_of_forall_finite`) provides a compatible branch
`(σ_n)`, whose common extension matches every vertex of the infinite tree.
-/
import GraphMarkovMatching.Support.Tree
import Mathlib.Order.KonigLemma

namespace GraphMarkovMatching.Support

open scoped Classical

/-! ### Restriction of restricted automorphisms -/

/-- Restrict an `AutK k m (n+1)`-automorphism to `𝔹_n` at the same phase: keep
the swap bits of the top `n` levels, drop the deepest. -/
def restrictAutK (k : ℕ) : (m n : ℕ) → AutK k m (n + 1) → AutK k m n
  | _, 0, _ => ()
  | 0, n + 1, π =>
      (π.1, restrictAutK k (k - 1) n π.2.1, restrictAutK k (k - 1) n π.2.2)
  | _ + 1, n + 1, π =>
      (restrictAutK k _ n π.1, restrictAutK k _ n π.2)

/-- The `i ≤ j` projection `AutK k m j → AutK k m i`, iterating `restrictAutK`. -/
def projAutK {k m i : ℕ} : ∀ {j : ℕ}, i ≤ j → AutK k m j → AutK k m i :=
  Nat.leRec (motive := fun j _ => AutK k m j → AutK k m i) id
    (fun {j} _ ih π => ih (restrictAutK k m j π))

lemma projAutK_refl {k m i : ℕ} (a : AutK k m i) : projAutK (le_refl i) a = a := by
  simp only [projAutK, Nat.leRec_self, id_eq]

lemma projAutK_succ {k m i j : ℕ} (h : i ≤ j) (a : AutK k m (j + 1)) :
    projAutK (Nat.le_succ_of_le h) a = projAutK h (restrictAutK k m j a) := by
  rw [projAutK, Nat.leRec_succ _ _ h]; rfl

lemma projAutK_trans {k m i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) (a : AutK k m l) :
    projAutK hij (projAutK hjl a) = projAutK (hij.trans hjl) a := by
  induction hjl with
  | refl => rw [projAutK_refl]
  | step hjl ih => rw [projAutK_succ hjl, ih, ← projAutK_succ (hij.trans hjl)]

lemma projAutK_le_succ {k m n : ℕ} (x : AutK k m (n + 1)) :
    projAutK n.le_succ x = restrictAutK k m n x := by
  rw [projAutK_succ (le_refl n), projAutK_refl]

/-! ### Kőnig's lemma for the automorphism tower -/

/-- **Kőnig's infinity lemma** for the matching automorphisms at phase `m`:
if a family `Good n ⊆ AutK k m n` is nonempty at every height and closed under
restriction, there is a compatible branch. Specialises Mathlib's
`exists_seq_forall_proj_of_forall_finite`. -/
theorem exists_compat_branchK {k m : ℕ} (Good : (n : ℕ) → AutK k m n → Prop)
    (hcompat : ∀ n (π : AutK k m (n + 1)),
      Good (n + 1) π → Good n (restrictAutK k m n π))
    (hne : ∀ n, ∃ π : AutK k m n, Good n π) :
    ∃ σ : (n : ℕ) → AutK k m n,
      (∀ n, Good n (σ n)) ∧ ∀ n, restrictAutK k m n (σ (n + 1)) = σ n := by
  have hgood : ∀ {i j : ℕ} (hij : i ≤ j) (π : AutK k m j),
      Good j π → Good i (projAutK hij π) := by
    intro i j hij
    induction hij with
    | refl => intro π hπ; rw [projAutK_refl]; exact hπ
    | step hij ih => intro π hπ; rw [projAutK_succ hij]; exact ih _ (hcompat _ π hπ)
  haveI : ∀ n, Nonempty {π : AutK k m n // Good n π} := fun n =>
    (hne n).elim fun π h => ⟨π, h⟩
  haveI : ∀ n, Finite (AutK k m n) := fun n => autK_finite k m n
  let proj : ∀ {i j : ℕ}, i ≤ j → {π : AutK k m j // Good j π}
      → {π : AutK k m i // Good i π} :=
    fun {i j} hij π => ⟨projAutK hij π.1, hgood hij π.1 π.2⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => {π : AutK k m n // Good n π}) (π := fun {i j} hij => proj hij)
    (by intro i a; exact Subtype.ext (projAutK_refl a.1))
    (by intro i j l hij hjl a; exact Subtype.ext (projAutK_trans hij hjl a.1))
    (by intro i a; exact Set.toFinite _)
  refine ⟨fun n => (f n).1, fun n => (f n).2, fun n => ?_⟩
  have h3 := congrArg Subtype.val (hf n.le_succ : proj n.le_succ (f (n + 1)) = f n)
  simpa [proj, projAutK_le_succ] using h3

/-! ### Restriction preserves matching -/

universe u
variable {V : Type u}

/-- Restrict a full labelling of `𝔹_{n+1}` to `𝔹_n`. -/
def restrictLab : (n : ℕ) → FullLab V (n + 1) → FullLab V n
  | 0, x => x.1
  | n + 1, x => (x.1, restrictLab n x.2.1, restrictLab n x.2.2)

/-- Restriction commutes with matching: a matching restricted automorphism of
`𝔹_{n+1}` restricts to a matching one of `𝔹_n`, at every phase. -/
lemma fullMatchesK_restrict (R₀ : V → V → Prop) (k : ℕ) :
    ∀ (n m : ℕ) (π : AutK k m (n + 1)) (X Y : FullLab V (n + 1)),
      fullMatchesK R₀ k m (n + 1) π X Y →
        fullMatchesK R₀ k m n (restrictAutK k m n π) (restrictLab n X) (restrictLab n Y) := by
  intro n
  induction n with
  | zero =>
      intro m π X Y h
      match m with
      | 0 => exact h.1
      | m + 1 => exact h.1
  | succ n ih =>
      intro m π X Y h
      match m with
      | 0 =>
          obtain ⟨b, π₀, π₁⟩ := π
          obtain ⟨a, x₀, x₁⟩ := X
          obtain ⟨c, y₀, y₁⟩ := Y
          obtain ⟨hroot, h₀, h₁⟩ := h
          refine ⟨hroot, ?_, ?_⟩
          · have := ih (k - 1) π₀ x₀ (bif b then y₁ else y₀) h₀
            cases b <;> simpa [restrictAutK, restrictLab] using this
          · have := ih (k - 1) π₁ x₁ (bif b then y₀ else y₁) h₁
            cases b <;> simpa [restrictAutK, restrictLab] using this
      | m + 1 =>
          obtain ⟨π₀, π₁⟩ := π
          obtain ⟨a, x₀, x₁⟩ := X
          obtain ⟨c, y₀, y₁⟩ := Y
          obtain ⟨hroot, h₀, h₁⟩ := h
          exact ⟨hroot, ih m π₀ x₀ y₀ h₀, ih m π₁ x₁ y₁ h₁⟩

/-! ### The infinite matching -/

/-- Two infinite labellings (compatible sequences of finite labellings) admit
an infinite-tree matching in the restricted group at phase `m`: a compatible
sequence `σ_n ∈ AutK k m n` matching every vertex at every height. -/
def InfMatchK (R₀ : V → V → Prop) (k m : ℕ) (X Y : (n : ℕ) → FullLab V n) : Prop :=
  ∃ σ : (n : ℕ) → AutK k m n,
    (∀ n, restrictAutK k m n (σ (n + 1)) = σ n)
      ∧ ∀ n, fullMatchesK R₀ k m n (σ n) (X n) (Y n)

/-- **The König step (`⊇` of `M = ⋂ E_n`)** for `G_k`: if a matching
restricted automorphism exists at every finite height, an infinite-tree one
exists. -/
theorem infinite_matchingK_of_forall_level (R₀ : V → V → Prop) (k m : ℕ)
    (X Y : (n : ℕ) → FullLab V n)
    (hX : ∀ n, restrictLab n (X (n + 1)) = X n)
    (hY : ∀ n, restrictLab n (Y (n + 1)) = Y n)
    (hlevel : ∀ n, ∃ π : AutK k m n, fullMatchesK R₀ k m n π (X n) (Y n)) :
    InfMatchK R₀ k m X Y := by
  obtain ⟨σ, hgood, hcompat⟩ :=
    exists_compat_branchK (fun n π => fullMatchesK R₀ k m n π (X n) (Y n))
      (fun n π h => by
        have := fullMatchesK_restrict R₀ k n m π (X (n + 1)) (Y (n + 1)) h
        rwa [hX n, hY n] at this)
      hlevel
  exact ⟨σ, hcompat, hgood⟩

end GraphMarkovMatching.Support
