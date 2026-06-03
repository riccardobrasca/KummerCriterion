module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import KummerCriterion.Reflection.Local.Basic

/-!
# First graded piece of the principal-unit filtration

This file begins the first graded-piece layer. It constructs the
standard homomorphism from multiplicative principal units to the additive
cotangent space `I / I^2`, sending `u` to `u - 1`, and identifies its kernel.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion

namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The global cyclotomic prime `lambda` is maximal. -/
theorem cyclotomicLambda_isMaximal : (cyclotomicLambda p K).IsMaximal := by
  simpa [cyclotomicLambda] using
    (Ideal.IsPrime.isMaximal (zetaPrime_isPrime p K) (zetaPrime_ne_bot p K))

/-- The global residue ring at `lambda` has cardinality `p`. -/
theorem globalCyclotomicResidueCard : Nat.card (𝓞 K ⧸ cyclotomicLambda p K) = p := by
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by simp
  have hAbs : Ideal.absNorm (cyclotomicLambda p K) = p := by
    simpa [cyclotomicLambda, zetaPrime] using
      (IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p 0 hζ)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hAbs
  exact hAbs

end CyclotomicSetup

end Local
end Reflection
end KummerCriterion
