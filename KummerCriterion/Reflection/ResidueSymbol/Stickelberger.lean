module

public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity.Finset

/-!
# Stickelberger-style prime factorization of residue Gauss sums

This file collects algebraic lemmas used by the Stickelberger prime
factorization argument for residue Gauss sums.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

namespace Furtwaengler

variable {R' : Type*} [CommRing R']

/-- If `x - 1` lies in an ideal, then so does `x^n - 1`. -/
theorem pow_sub_one_mem_of_sub_one_mem
    {R : Type*} [CommRing R] (x : R) (n : ℕ)
    {I : Ideal R} (h : x - 1 ∈ I) :
    x ^ n - 1 ∈ I := by
  obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one x n
  rw [hc]
  exact Ideal.mul_mem_right _ _ h

end Furtwaengler

end KummerCriterion
