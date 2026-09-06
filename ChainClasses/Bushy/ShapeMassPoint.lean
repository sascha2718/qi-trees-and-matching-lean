import ChainClasses.Bushy.ShapeLabelLaw
import ChainClasses.Scalar.ShapeMass

/-!
`sec:shape-harris` of `matching_classes_simple.tex`:
**`thm:shape-mass` (`it:shape-mass-point`)** at the shape law itself.

`ShapeMass` proves the clause over a list of factors: a mass that is a product of at most
`2n` factors, each at least `p`, is at least `e^{-Cn}` with `C = 2 log p⁻¹`.  The shape law
of `thm:shape-iid` is such a product, and the factors are read off `shapeMass`: one
decoration factor per neck vertex and the split weight at the end, the decoration factor
being `θ₁` when the neck vertex is bare and `2θ₂q` times the bush mass of the tree it
carries otherwise.  Counting the bush mass as one factor per vertex of the bush, the
number of factors is exactly `|σ|`, so the bound comes out at the sharper exponent
`p^{|σ|}` and a fortiori at the paper's `e^{-2 log p⁻¹ |σ|}`.

What the bush contributes is the one input the shape law does not carry itself, the point
mass of the conjugate Galton-Watson tree: a finite tree of `n` vertices has bush mass at
least `p^n`.  It is stated as `BushPointBound` and carried as a hypothesis; everything
else is discharged.

* `BushPointBound`: **the bush input**, the point mass of the conjugate tree.
* `ofReal_pow_le_decMass`, `ofReal_pow_le_prod_decMass`: the decoration factors, one power
  of `p` per vertex of the decoration and one for the neck vertex carrying it.
* `ofReal_pow_size_le_shapeMass`: **`thm:shape-mass` (`it:shape-mass-point`)** at
  `shapeMass`, in the sharp form `p^{|σ|} ≤ μ(σ)`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (survivalMeasure bushMeasure Offspring)
open scoped ENNReal

/-! ### The bush input -/

/-- **The point mass of the conjugate tree**: a bush of `n` vertices has mass at least
`p^n`.  This is the one factorisation of `thm:shape-mass` (`it:shape-mass-point`)
that the shape law does not carry itself. -/
def BushPointBound (θ : Offspring 2) (p : ℝ) : Prop :=
  ∀ t : Tri, ENNReal.ofReal (p ^ t.size) ≤ bushMeasure θ {d : Amb → ℕ | bushTri d = t}

/-! ### The decoration factors -/

variable {θ : Offspring 2} {p : ℝ}

/-- A decoration contributes one power of `p` per vertex of its bush and one for the neck vertex
carrying it. -/
lemma ofReal_pow_le_decMass (hp0 : 0 < p) (h1 : p ≤ θ 1)
    (h2 : p ≤ θ 2 * 2 * θ.extinction) (hbush : BushPointBound θ p) (o : Option Tri) :
    ENNReal.ofReal (p ^ (Tri.optSize o + 1)) ≤ decMass θ o := by
  cases o with
  | none =>
      rw [decMass]
      simpa using ENNReal.ofReal_le_ofReal h1
  | some t =>
      have hsplit : p ^ (Tri.optSize (some t) + 1) = p * p ^ t.size := by
        rw [Tri.optSize_some, pow_succ]
        ring
      rw [decMass, hsplit, ENNReal.ofReal_mul hp0.le]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal h2) (hbush t)

/-- The decorations of a shape contribute one power of `p` per vertex of the decorations and one
per neck vertex carrying them. -/
lemma ofReal_pow_le_prod_decMass (hp0 : 0 < p) (h1 : p ≤ θ 1)
    (h2 : p ≤ θ 2 * 2 * θ.extinction) (hbush : BushPointBound θ p) :
    ∀ l : List (Option Tri),
      ENNReal.ofReal (p ^ ((l.map Tri.optSize).sum + l.length))
        ≤ (l.map (decMass θ)).prod := by
  intro l
  induction l with
  | nil => simp
  | cons o l ih =>
      have hexp : ((o :: l).map Tri.optSize).sum + (o :: l).length
          = (Tri.optSize o + 1) + ((l.map Tri.optSize).sum + l.length) := by
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      rw [hexp, pow_add, ENNReal.ofReal_mul (pow_nonneg hp0.le _), List.map_cons,
        List.prod_cons]
      exact mul_le_mul' (ofReal_pow_le_decMass hp0 h1 h2 hbush o) ih

/-! ### The point mass of a shape -/

/-- **`thm:shape-mass` (`it:shape-mass-point`)** at the shape law: the mass of a
shape is a product of one factor per vertex, so it is at least `p` to the size. -/
theorem ofReal_pow_size_le_shapeMass (hp0 : 0 < p) (h1 : p ≤ θ 1)
    (h2 : p ≤ θ 2 * 2 * θ.extinction) (hk : p ≤ θ.skeletonWeight 2)
    (hbush : BushPointBound θ p) (σ : Shape) :
    ENNReal.ofReal (p ^ σ.size) ≤ shapeMass θ σ := by
  have hsize : σ.size = ((σ.decs.map Tri.optSize).sum + σ.decs.length) + 1 := by
    rw [Shape.size_eq', Shape.neckLen, Shape.decs_length]
    omega
  rw [hsize, pow_succ, ENNReal.ofReal_mul (pow_nonneg hp0.le _), shapeMass]
  exact mul_le_mul' (ofReal_pow_le_prod_decMass hp0 h1 h2 hbush σ.decs)
    (ENNReal.ofReal_le_ofReal hk)

end ChainClasses
