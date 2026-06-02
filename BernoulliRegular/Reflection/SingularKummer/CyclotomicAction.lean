module

public import BernoulliRegular.Reflection.SingularKummer.Equivariance
public import BernoulliRegular.Reflection.SingularKummer.DimensionLowerBound
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionIdempotent
public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelCharacterLift
public import BernoulliRegular.UnitQuotient.DeltaAction

/-!
# Singular Kummer: cyclotomic actions on `S` and `A[p]`

This file instantiates the abstract `PrincipalIdealPreservingEquiv` package for
the actual cyclotomic `Delta = (ZMod p)ˣ` action on `K = Q(ζ_p)`.  The output
is a concrete `Delta`-action on the singular quotient `S` and on the torsion
target `A[p]`, together with the corresponding equivariance of the map

```text
E/E^p -> S -> A[p].
```
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Pointwise
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace SingularPair

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
















end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end
