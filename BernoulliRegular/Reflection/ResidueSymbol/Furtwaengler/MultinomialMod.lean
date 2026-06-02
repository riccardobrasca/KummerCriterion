module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitSum
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.BigOperators.Associated

/-!
# Multinomial coefficients modulo the residue characteristic (Layer 1, REF-18c2c4)

This file records the elementary prime-to-`ℓ` facts needed for the
digit-sum form of Stickelberger's congruence.

The coefficient that appears in the leading Stickelberger term is controlled
by the factorials of the base-`ℓ` digits. Since every digit is `< ℓ`, their
factorials are all prime to `ℓ`, and so is their product. We also include the
carry-free multinomial corollary: if the total degree is `< ℓ`, then the
corresponding multinomial coefficient is non-zero modulo `ℓ`.
-/

@[expose] public section

namespace BernoulliRegular

namespace Furtwaengler








end Furtwaengler

end BernoulliRegular
