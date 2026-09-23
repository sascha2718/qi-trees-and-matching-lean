/-
`sec:reduction` of `graph_matching_selfcontained.tex`, the infinite-tree / König step.
An automorphism of `𝔹_{h+1}` restricts to one of `𝔹_h` (`restrictAut`), and this
restriction preserves matching (`fullMatchesA_restrict`). So if a matching
automorphism exists at every finite level, the sets `𝓕_h ⊆ Aut(𝔹_h)` are
nonempty and finite and form an infinite, finitely-branching tree; Kőnig's
infinity lemma (`exists_seq_forall_proj_of_forall_finite`) provides a
compatible branch `(σ_h)`, whose common extension matches every vertex.

`infinite_matching_of_forall_level` is the combinatorial core of `M = ⋂ 𝓜_h`
(the `⊇` direction). The measure-theoretic `P(M) = lim P(𝓜_h)` (continuity from
above) is the remaining, standard, step.
-/
import GraphMatching.Tree
import Mathlib.Order.KonigLemma

namespace GraphMatching

open scoped Classical

/-! ### Restriction of automorphisms, and finiteness -/

/-- Restrict a `𝔹_{h+1}`-automorphism to `𝔹_h`: keep the swap bits of the top `h`
levels, drop the deepest. -/
def restrictAut : (h : ℕ) → Aut (h + 1) → Aut h
  | 0, _ => ()
  | h + 1, π => (π.1, restrictAut h π.2.1, restrictAut h π.2.2)

instance instFiniteAut (h : ℕ) : Finite (Aut h) := by
  induction h with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ h ih => have := ih; show Finite (Bool × Aut h × Aut h); infer_instance

/-- The `i ≤ j` projection `Aut j → Aut i`, iterating `restrictAut`. -/
def projAut {i : ℕ} : ∀ {j : ℕ}, i ≤ j → Aut j → Aut i :=
  Nat.leRec (motive := fun m _ => Aut m → Aut i) id
    (fun {m} _ ih π => ih (restrictAut m π))

lemma projAut_refl {i : ℕ} (a : Aut i) : projAut (le_refl i) a = a := by
  simp only [projAut, Nat.leRec_self, id_eq]

lemma projAut_succ {i k : ℕ} (hle : i ≤ k) (a : Aut (k + 1)) :
    projAut (Nat.le_succ_of_le hle) a = projAut hle (restrictAut k a) := by
  rw [projAut, Nat.leRec_succ _ _ hle]; rfl

lemma projAut_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : Aut k) :
    projAut hij (projAut hjk a) = projAut (hij.trans hjk) a := by
  induction hjk with
  | refl => rw [projAut_refl]
  | step hjk ih => rw [projAut_succ hjk, ih, ← projAut_succ (hij.trans hjk)]

lemma projAut_le_succ {h : ℕ} (x : Aut (h + 1)) : projAut h.le_succ x = restrictAut h x := by
  rw [projAut_succ (le_refl h), projAut_refl]

/-! ### Kőnig's lemma for the automorphism tower -/

/-- **Kőnig's infinity lemma** for the matching automorphisms: if a family
`Good h ⊆ Aut h` is nonempty at every level and closed under restriction, there
is a compatible branch (`σ_h ∈ Good h`, `restrictAut h σ_{h+1} = σ_h`). This is a
specialisation of Mathlib's `exists_seq_forall_proj_of_forall_finite`. -/
theorem exists_compat_branch (Good : (h : ℕ) → Aut h → Prop)
    (hcompat : ∀ h (π : Aut (h + 1)), Good (h + 1) π → Good h (restrictAut h π))
    (hne : ∀ h, ∃ π : Aut h, Good h π) :
    ∃ σ : (h : ℕ) → Aut h, (∀ h, Good h (σ h)) ∧ ∀ h, restrictAut h (σ (h + 1)) = σ h := by
  have hgood : ∀ {i j : ℕ} (hij : i ≤ j) (π : Aut j), Good j π → Good i (projAut hij π) := by
    intro i j hij
    induction hij with
    | refl => intro π hπ; rw [projAut_refl]; exact hπ
    | step hij ih => intro π hπ; rw [projAut_succ hij]; exact ih _ (hcompat _ π hπ)
  have : ∀ h, Nonempty {π : Aut h // Good h π} := fun h => (hne h).elim fun π hπ => ⟨π, hπ⟩
  let proj : ∀ {i j : ℕ}, i ≤ j → {π : Aut j // Good j π} → {π : Aut i // Good i π} :=
    fun {i j} hij π => ⟨projAut hij π.1, hgood hij π.1 π.2⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun h => {π : Aut h // Good h π}) (π := fun {i j} hij => proj hij)
    (by intro i a; exact Subtype.ext (projAut_refl a.1))
    (by intro i j k hij hjk a; exact Subtype.ext (projAut_trans hij hjk a.1))
    (by intro i a; exact Set.toFinite _)
  refine ⟨fun h => (f h).1, fun h => (f h).2, fun h => ?_⟩
  have h3 := congrArg Subtype.val (hf h.le_succ : proj h.le_succ (f (h + 1)) = f h)
  simpa [proj, projAut_le_succ] using h3

/-! ### Restriction preserves matching -/

universe u
variable {V : Type u}

/-- Restrict a full labelling of `𝔹_{h+1}` to `𝔹_h`: keep the root and the top
`h` levels of each subtree. -/
def restrictLab : (h : ℕ) → FullLab V (h + 1) → FullLab V h
  | 0, x => x.1
  | h + 1, x => (x.1, restrictLab h x.2.1, restrictLab h x.2.2)

/-- Restriction commutes with matching: a matching automorphism of `𝔹_{h+1}`
restricts to a matching automorphism of `𝔹_h`. -/
lemma fullMatchesA_restrict (R₀ : V → V → Prop) (h : ℕ) (π : Aut (h + 1))
    (x y : FullLab V (h + 1)) (hm : fullMatchesA R₀ (h + 1) π x y) :
    fullMatchesA R₀ h (restrictAut h π) (restrictLab h x) (restrictLab h y) := by
  induction h with
  | zero => exact hm.1
  | succ h ih =>
      obtain ⟨b, π₀, π₁⟩ := π
      obtain ⟨a, x₀, x₁⟩ := x
      obtain ⟨c, y₀, y₁⟩ := y
      obtain ⟨hroot, h₀, h₁⟩ := hm
      refine ⟨hroot, ?_, ?_⟩
      · have := ih π₀ x₀ (bif b then y₁ else y₀) h₀
        cases b <;> simpa [restrictAut, restrictLab] using this
      · have := ih π₁ x₁ (bif b then y₀ else y₁) h₁
        cases b <;> simpa [restrictAut, restrictLab] using this

/-! ### The infinite matching -/

/-- Two infinite labellings (compatible sequences of finite labellings) admit an
infinite-tree matching automorphism: a compatible sequence `σ_h ∈ Aut(𝔹_h)`
matching every vertex at every level. -/
def InfMatch (R₀ : V → V → Prop) (X Y : (h : ℕ) → FullLab V h) : Prop :=
  ∃ σ : (h : ℕ) → Aut h,
    (∀ h, restrictAut h (σ (h + 1)) = σ h) ∧ ∀ h, fullMatchesA R₀ h (σ h) (X h) (Y h)

/-- **The König step (`⊇` of `M = ⋂ 𝓜_h`)**: if a matching automorphism exists at
every finite level, an infinite-tree matching automorphism exists. -/
theorem infinite_matching_of_forall_level (R₀ : V → V → Prop) (X Y : (h : ℕ) → FullLab V h)
    (hX : ∀ h, restrictLab h (X (h + 1)) = X h) (hY : ∀ h, restrictLab h (Y (h + 1)) = Y h)
    (hlevel : ∀ h, ∃ π : Aut h, fullMatchesA R₀ h π (X h) (Y h)) :
    InfMatch R₀ X Y := by
  obtain ⟨σ, hgood, hcompat⟩ :=
    exists_compat_branch (fun h π => fullMatchesA R₀ h π (X h) (Y h))
      (fun h π hm => by
        have := fullMatchesA_restrict R₀ h π (X (h + 1)) (Y (h + 1)) hm
        rwa [hX h, hY h] at this)
      hlevel
  exact ⟨σ, hcompat, hgood⟩

end GraphMatching
