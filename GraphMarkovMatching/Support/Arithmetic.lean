import Mathlib.NumberTheory.FrobeniusNumber

namespace GraphMarkovMatching

lemma setGcd_coe_finset (D : Finset ℕ) :
    Nat.setGcd (D : Set ℕ) = D.gcd id := by
  refine Nat.dvd_antisymm ?_ ?_
  · exact Finset.dvd_gcd fun i hi => Nat.setGcd_dvd_of_mem hi
  · exact Nat.dvd_setGcd_iff.mpr fun m hm => Finset.gcd_dvd hm

end GraphMarkovMatching
