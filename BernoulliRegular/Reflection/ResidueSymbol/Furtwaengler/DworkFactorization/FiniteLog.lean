module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogBounds
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.LocalDenominators

/-!
# Finite logarithm on principal `Q`-units

This file defines the finite logarithm

`Log_N(1 + x) = sum_{1 <= n < ell * (N + 1)} (-1)^(n+1) x^n / n`

in `𝓞 R' / Q^(N+1)` for lifts `x ∈ Q`.  Division by the `ell`-power part of
`n` uses the local-denominator bridge, while the prime-to-`Q` part of `n` is
inverted directly in the quotient.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w


end Furtwaengler

end BernoulliRegular
