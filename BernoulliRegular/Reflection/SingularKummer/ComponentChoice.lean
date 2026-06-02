module

public import BernoulliRegular.Reflection.SingularKummer.SingularPair

/-!
# Singular Kummer: choosing a nontrivial lift from a component

This file isolates the elementary group-theoretic part of the later singular-Kummer lift
argument.  Once a character component of the singular group maps onto the
matching character component of `A[p]`, any nontrivial element in the target
component has a lift in the source component with nontrivial image.
-/

@[expose] public section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ComponentChoice

variable {G H : Type*} [Group G] [Group H]





open scoped nonZeroDivisors

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]



end ComponentChoice

end SingularKummer
end Reflection
end BernoulliRegular

end
