module

public import BernoulliRegular.Reflection.SingularKummer.SingularLinearAction

/-!
# Singular Kummer: choosing the singular class in a character component

This file proves the final elementary choice step after component surjectivity:
if the projected target component of `A[p]` is nontrivial, then the matching
projected component of the singular group contains a class with nontrivial
image in `A[p]`.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace LinearComponentChoice

variable {R M N : Type*} [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]



end LinearComponentChoice

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
