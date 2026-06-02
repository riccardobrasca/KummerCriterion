module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceCoefficientExpansion
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MultinomialMod
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Trace coefficient valuation reductions (REF-18c2c4-L2c3d3)

The full L2c3d3 coefficient estimate is

`traceCharacterChooseSumRec a n ∈ Q^(s-n)`.

This file proves the no-sorry valuation reductions that isolate the remaining
core estimate:

* if `n ≥ ℓ`, the coefficient is exactly zero because every trace value has
  representative `< ℓ`;
* if `n < ℓ`, then `n!` is a `Q`-unit, so membership of the factorial-cleared
  coefficient in any `Q`-power implies membership of the original coefficient
  in the same power.

The remaining middle range is therefore the factorial-cleared Gauss-period
estimate.  After L2c3d2, this can be stated concretely as a valuation for
the desc-factorial trace sums.  The required strengthening is a genuine
Teichmuller-lift congruence; first-order finite-field orthogonality only
detects membership in `Q`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
