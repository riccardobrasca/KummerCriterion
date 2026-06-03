module

public import KummerCriterion.GaussSum.SignInvariant.BranchChoice

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

/-- **T023d1g3**: In the `p ≡ 3 [ZMOD 4]` branch, the quadratic Gauss sum for
the raw quadratic character equals `I * √p`. -/
theorem gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N := p)) = Complex.I * (Real.sqrt p : ℂ) := by
  simpa [quadraticCharComplex] using
    gaussSum_quadraticCharComplex_eq_I_mul_sqrt_of_mod_four_eq_three (p := p) hp₂ hp₄

end GaussSum

end KummerCriterion
