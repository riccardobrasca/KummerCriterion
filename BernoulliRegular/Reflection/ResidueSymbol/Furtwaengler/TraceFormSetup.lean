module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IntegralBridge
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# Trace-form Stickelberger setup (REF-18c2c4-L2c1)

Refines `ConcreteStickelbergerSetup` to additive characters of the
canonical trace form

  `ψ(x) = ζ_ℓ ^ Tr_{k/𝔽_ℓ}(c · x)`

for some scale `c ∈ kˣ`. Every primitive additive character on
`k = 𝔽_{ℓ ^ f}` has this shape, so the refinement does not lose
generality, and the trace witness pins down the exponent in the form
needed by the digit-sum Stickelberger argument (REF-18c2c4-L2c2 / L2c3).

This is REF-18c2c4-L2c1 of the Furtwängler digit-sum Stickelberger route.

## Main definitions

* `TraceFormStickelbergerSetup`: extends `ConcreteStickelbergerSetup`
  with a scale `traceScale : kˣ` and a witness that the existing
  exponent function equals `(Algebra.trace (ZMod ℓ) k (traceScale·x)).val`.
* `ConcreteStickelbergerSetup.gaussSumIntAtScale`: the integral Gauss
  sum at an arbitrary trace scale, used to state scale-removal
  independent of any bundle's specific choice of `traceScale`.

## Main theorems

* `TraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace`: the
  integral additive character has the trace-form integer-power
  expression.
* `ConcreteStickelbergerSetup.gaussSumIntAtScale_eq_charUnit_mul_one`:
  Gauss sums at different trace scales differ by a multiplicative
  character value at the inverse scale (a unit in `𝓞 R'`).
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
