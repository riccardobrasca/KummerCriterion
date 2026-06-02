module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Local denominator estimates for the finite Dwork telescope

This file connects the exact `Q`-adic order of powers of the rational
residue characteristic with the quotient-local fraction evaluator from
`ConcreteSetup`.  The denominator `ℓ^m` is not invertible at `Q`, so the API
uses an actual local representation `ℓ^m * y = d * x` with
`d ∉ Q`; then `y / d` is the `Q`-local value of `x / ℓ^m`.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open WithZero Multiplicative IsDedekindDomain

namespace BernoulliRegular

namespace Furtwaengler

universe u v w


end Furtwaengler

end BernoulliRegular
