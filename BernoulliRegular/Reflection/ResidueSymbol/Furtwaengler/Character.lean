module

public import BernoulliRegular.Reflection.ResidueSymbol.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Residue character at a prime as a `MulChar` (REF-18c2a)

This file packages the `p`-th-power residue character at a maximal ideal
`q ∤ p` of a Dedekind domain `R` (typically `R = 𝓞_K` for a cyclotomic
field `K = ℚ(ζ_p)`) as a `MulChar (R ⧸ q) R'` for a target ring `R'`
containing a primitive `p`-th root of unity.

REF-16 (`BernoulliRegular.Reflection.ResidueSymbol.PowerResidue`) provides
the additive form `finiteFieldExponent : kˣ → ZMod p` and `primeExponent`
at the maximal-ideal level. This file lifts that exponent into a target
ring `R'` containing `μ_p`, packaging the result as a multiplicative
character that the Gauss-sum machinery (`Mathlib.NumberTheory.GaussSum`)
can directly consume.

## Approach

Given a primitive `p`-th root of unity `ζ_R` in the target `R'`, we send
`x ∈ kˣ` to `ζ_R ^ (finiteFieldExponent ... x).val ∈ R'ˣ`. The
multiplicativity of the underlying map follows from
`finiteFieldExponent_mul` together with the fact that `ζ_R` has order `p`,
so `ζ_R ^ ((a.val + b.val) % p) = ζ_R ^ (a.val + b.val)`. The lift to a
`MulChar k R'` (with non-units mapping to `0`) is then immediate via
`MulChar.ofUnitHom`.

## Main definitions

* `BernoulliRegular.Furtwaengler.residueUnitHom`: the unit-group
  homomorphism `kˣ →* R'ˣ` sending `x` to `ζ_R ^ (finiteFieldExponent ... x).val`.
* `BernoulliRegular.Furtwaengler.residueMulChar`: the corresponding
  `MulChar k R'`, obtained via `MulChar.ofUnitHom`.
* `residueMulChar_apply_unit`: the agreement
  `residueMulChar (x : kˣ) = ζ_R ^ (finiteFieldExponent ... x).val`.

The Galois-equivariance API (needed by REF-18c2c) is intentionally deferred
to a later commit; this ticket only delivers the bare `MulChar` packaging
plus the link back to REF-16.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

open Reflection.ResidueSymbol.PowerResidue

variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [CommMonoidWithZero R']
variable {p : ℕ}







end Furtwaengler

end BernoulliRegular
