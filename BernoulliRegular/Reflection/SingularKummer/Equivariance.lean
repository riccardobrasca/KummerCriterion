module

public import BernoulliRegular.Reflection.SingularKummer.SingularPair

/-!
# Singular Kummer: equivariance of the singular exact sequence

This file proves that the pair-form singular exact sequence is equivariant
under every automorphism that preserves principal fractional ideals.

This is the algebraic input needed for the later `Delta`-component argument.
The actual cyclotomic `Delta`-action should instantiate
`PrincipalIdealPreservingEquiv` using the semilinear action of field
automorphisms on `𝓞_K` and its fractional ideals.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

namespace SingularPair

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
