/-
Bridging identities for the general-ν closure
(`arbitrary_offspring_matching.tex`, the assembly of the transfer rows
of `sec:rows` into the block recursion of `sec:recursion`; the
geometric half is `thm:geom`): the ledger quantities appearing on the
right-hand sides of the transfer rows are interpretations of explicit
formal screens, and the nilpotent invariant admits a crude geometric
bound from a uniform row bound.

* `interpScreen_singleton_none` / `interpScreen_singleton_some` /
  `interpScreen_pair_some`: reversed zero masses, resolved singleton
  screens, and two-member screens as interpreted formal screens;
* `mulVec_le_of_row_sum` / `nilSum_le_geom`: the invariant vector of
  the screen block is at most the geometric sum of the uniform row
  bound, which discharges the level hypothesis `hΞ` numerically.
-/
import GraphMarkovMatching.Process.Coordinates
import GraphMarkovMatching.Closure.Block

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (ν : PMF ℕ) (v0 : V)

/-- Unit-normalized singleton screens interpret to reversed zero
masses. -/
lemma interpScreen_singleton_none (h : ℕ) (s t : Tgt) :
    interpScreen α Rv μ ν v0 h ⟨s, {t}, none⟩
      = zMass (interpT μ ν v0 h s) (interpT μ ν v0 h t)
          (fullSim (labRel Rv) h) := by
  rw [interpScreen, show (⟨s, {t}, none⟩ : GScreen).zlist = {t} from rfl,
    Finset.toList_singleton]
  exact screenE_one_eq_zMass _ _ _

/-- Singleton screens with a tilt normalization interpret to the
resolved screen values of the one-cell ledger row. -/
lemma interpScreen_singleton_some (h : ℕ) (s t w : Tgt) :
    interpScreen α Rv μ ν v0 h ⟨s, {t}, some w⟩
      = screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
          [interpT μ ν v0 h t]
          (WresD α (interpT μ ν v0 h w) (fullSim (labRel Rv) h)) := by
  rw [interpScreen, show (⟨s, {t}, some w⟩ : GScreen).zlist = {t} from rfl,
    Finset.toList_singleton]
  rfl

/-- Two-member screens with a tilt normalization interpret to the
two-list screen values of the Hall factorization, independently of the
list order and of coincidences among the members. -/
lemma interpScreen_pair_some (h : ℕ) (s a b w : Tgt) :
    interpScreen α Rv μ ν v0 h ⟨s, {a, b}, some w⟩
      = screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
          [interpT μ ν v0 h a, interpT μ ν v0 h b]
          (WresD α (interpT μ ν v0 h w) (fullSim (labRel Rv) h)) := by
  rw [interpScreen, show (⟨s, {a, b}, some w⟩ : GScreen).zlist = {a, b}
      from rfl]
  refine screenE_congr_mem _ _ (fun ρ => ?_) _
  constructor
  · intro hρ
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hρ
    rcases Finset.mem_insert.mp (Finset.mem_toList.mp ht) with rfl | ht2
    · exact List.mem_cons_self ..
    · rw [Finset.mem_singleton.mp ht2]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · intro hρ
    rcases List.mem_cons.mp hρ with rfl | hρ2
    · exact List.mem_map.mpr ⟨a, Finset.mem_toList.mpr
        (Finset.mem_insert_self _ _), rfl⟩
    · rw [List.mem_singleton.mp hρ2]
      exact List.mem_map.mpr ⟨b, Finset.mem_toList.mpr
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), rfl⟩

/-! ### The geometric bound on the nilpotent invariant -/

variable {ι : Type} [Fintype ι]

/-- A uniform row bound controls the matrix action against a uniform
vector bound (`thm:geom`). -/
lemma mulVec_le_of_row_sum {M : ι → ι → ℝ≥0∞} {c : ℝ≥0∞}
    (hrow : ∀ i, ∑ j, M i j ≤ c) {x : ι → ℝ≥0∞} {b : ℝ≥0∞}
    (hx : ∀ j, x j ≤ b) (i : ι) :
    mulVec M x i ≤ c * b := by
  calc mulVec M x i ≤ ∑ j, M i j * b :=
        Finset.sum_le_sum fun j _ => mul_le_mul_right (hx j) _
    _ = (∑ j, M i j) * b := (Finset.sum_mul _ _ _).symm
    _ ≤ c * b := mul_le_mul_left (hrow i) _

/-- Iterates of the matrix action on the constant vector stay below
the geometric powers of the row bound (`thm:geom`). -/
lemma iterate_mulVec_le {M : ι → ι → ℝ≥0∞} {c : ℝ≥0∞}
    (hrow : ∀ i, ∑ j, M i j ≤ c) (u : ℝ≥0∞) :
    ∀ n i, (mulVec M)^[n] (fun _ => u) i ≤ c ^ n * u := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
      intro i
      rw [Function.iterate_succ_apply']
      calc mulVec M ((mulVec M)^[n] (fun _ => u)) i
          ≤ c * (c ^ n * u) := mulVec_le_of_row_sum hrow ih i
        _ = c ^ (n + 1) * u := by ring

/-- **The geometric bound on the nilpotent invariant** (`thm:geom`): a
uniform row bound `c` gives `nilSum ≤ (∑_{j<r} c^j)·u` pointwise.  This discharges
the level hypothesis on the invariant vector from countable data. -/
lemma nilSum_le_geom {M : ι → ι → ℝ≥0∞} {c : ℝ≥0∞}
    (hrow : ∀ i, ∑ j, M i j ≤ c) (r : ℕ) (u : ℝ≥0∞) (i : ι) :
    nilSum M r u i ≤ (∑ j ∈ Finset.range r, c ^ j) * u := by
  rw [nilSum, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => iterate_mulVec_le hrow u j i

end GraphMarkovMatching
