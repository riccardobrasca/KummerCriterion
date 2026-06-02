module

public import BernoulliRegular.Reflection.SingularKummer.SingularClassChoice

/-!
# Singular Kummer: representatives of singular quotient classes

This file unwraps a class in the singular quotient into an explicit singular
pair `(I, alpha)`.  The representative automatically satisfies
`(alpha) = I^p`, and nontriviality of the quotient class image in `A[p]`
transfers to the represented singular pair.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]



end SingularPair

namespace SingularLinearAction
namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]


end SingularPair
end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
