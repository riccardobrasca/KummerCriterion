module

public import KummerCriterion.TotallyRealSubfield.ZetaPrime
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# The rational `p`-adic base place for the lambda-local correction

This file records the rational height-one prime `(p)` and proves that the
cyclotomic `lambda` prime lies over it. These are the concrete inputs
extending the rational map `ℚ → K` to the corresponding valuation completions.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The rational prime ideal `(p)` in `ℤ`. -/
def lambdaRationalPrimeIdeal : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)

/-- The height-one spectrum point of `ℤ` attached to the rational prime `p`. -/
def lambdaRationalHeightOneSpectrum : IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := lambdaRationalPrimeIdeal p
  isPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  ne_bot := by
    rw [lambdaRationalPrimeIdeal, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

/-- The cyclotomic `lambda` prime lies over the rational prime `(p)`. -/
theorem zetaPrime_liesOver_lambdaRationalPrimeIdeal :
    (zetaPrime p K).LiesOver (lambdaRationalPrimeIdeal p) := by
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζpow : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  have h :
      (Ideal.span
          ({((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)} :
            Set (𝓞 K))).LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
    IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one
      (p := p) (k := 0) (K := K) (hζ := hζpow)
  simpa [zetaPrime, lambdaRationalPrimeIdeal] using h

end KummerArtinHasse
end Furtwaengler
end KummerCriterion
