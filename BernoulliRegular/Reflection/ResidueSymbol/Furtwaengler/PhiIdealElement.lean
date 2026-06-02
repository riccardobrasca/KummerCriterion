module

public import Mathlib.RingTheory.Ideal.Int
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiIdeal
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical

/-!
# Data-carrying ideal Φ-elements

K2-2 proves the prime Φ-symbol identity for the actual descended Gauss-sum
element attached to a prime ideal.  K2-3 is the multiplicative ideal-level
extension: for a nonzero ideal `A`, define `Φ(A)` as the product of the
actual prime Φ-elements over `normalizedFactors A`, counted with
multiplicity.

The key point is the same as in `PhiPrimeElement.lean`: this file never
replaces the actual Gauss-sum element by an arbitrary generator of the same
Stickelberger ideal.  Arbitrary generators carry the explicit unit correction
proved in K2-2c.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement










namespace PhiIdealElement

/-! ### Span of the actual multiplicative Φ element -/




















/-! ### Principal actual-Φ corollary (K2-4) -/




/-! ### Positive-orientation principal actual-Φ corollary -/






end PhiIdealElement

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
