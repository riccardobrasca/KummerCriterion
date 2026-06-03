module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import KummerCriterion.GaussSum.SignInvariant.BranchChoice
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Final quadratic Gauss-sum endpoint

This module repackages the sign-invariant endpoint theorems into the final
quadratic Gauss-sum statement used downstream.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

section GaussSum

variable (p : ℕ) [hp : Fact p.Prime]

/-- In the `p ≡ 3 [ZMOD 4]` branch, the quadratic Gauss sum
the raw quadratic character equals `I * √p`. -/
theorem gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N := p)) = Complex.I * (Real.sqrt p : ℂ) := by
  simpa [quadraticCharComplex] using
    gaussSum_quadraticCharComplex_eq_I_mul_sqrt_of_mod_four_eq_three (p := p) hp₂ hp₄

end GaussSum

end KummerCriterion
