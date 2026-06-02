module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.UnitQuotient.DeltaAction
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.ZMod.Units

/-!
# Cyclotomic Galois lifts for the `{p, ℓ}` field

This file packages the CRT construction of the cyclotomic automorphism of
`ℚ(ζ_{pℓ})` whose exponent is a prescribed unit modulo `p` and is `1`
modulo `ℓ`. This is the Galois-theoretic input needed by the REF-18
covariance bridge: it gives honest automorphisms fixing the additive
`ℓ`-root while restricting to the standard `p`-cyclotomic action.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]


/-! ### Source-conductor cyclotomic lifts -/





































end Furtwaengler

end BernoulliRegular
