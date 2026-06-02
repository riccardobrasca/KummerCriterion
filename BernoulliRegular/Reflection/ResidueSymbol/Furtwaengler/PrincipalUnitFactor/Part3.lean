module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrincipalBridge
public import BernoulliRegular.TotallyRealSubfield.Conjugation
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import BernoulliRegular.UnitQuotient.TorsionQuotient
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.Part2

/-!
# Principal unit factor (REF-18 Phase 2, sub-piece U)

For a nonzero principal ideal `(α)`, the actual multiplicative Φ element
`Φ((α))` and the explicit Stickelberger principal generator
`α^Θ = stickelbergerPrincipalGen α` generate the same ideal. Hence they differ
by a unit:

```
Φ((α)) = u(α) · α^Θ.
```

This file formalizes the honest element-level U-chain interface:

* `PrincipalUnitFactorData α Φα` is the specific unit-factor equation for an
  actual principal Φ element `Φα`.
* `PrincipalUnitFactorData.nonempty_of_nonzero` proves existence of such a
  unit from the already formalized Φ-span theorem.
* If that specific unit is `±1`, its prime residue symbols vanish.
* `ChosenPrimaryUnitFactorProductSymbolZero α` is the reflection-facing
  chosen-object product condition: the same actual Φ element has locally
  trivial product symbols for `Φ((α)) · α` away from `α`.
* `ChosenPrimaryUnitFactorSymbolTrivial α` is the natural chosen-object
  downstream output from one normalized actual principal Φ element.
* `PrimaryUnitFactorSymbolTrivial α` is the stronger uniform downstream
  hypothesis over the current broad `PhiPrincipalElement` API.
* The concrete U4 endpoint is proved in
  `PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts` and
  `ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts`: for an
  actual principal Φ product, prime-level semi-primarity plus the prime
  conjugation-norm identities force the specific unit factor to be `±1`, hence
  its prime symbols vanish.

What remains outside this file is constructing the actual principal Φ product
from `K2_2SourceData` for every normalized prime factor and proving the
conjugation compatibility needed for those prime norm identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]



/-! ### Semi-primary torsion units -/








/-! ### Specific principal unit factor -/


namespace PrincipalUnitFactorData









end PrincipalUnitFactorData
end Furtwaengler

end BernoulliRegular

end
