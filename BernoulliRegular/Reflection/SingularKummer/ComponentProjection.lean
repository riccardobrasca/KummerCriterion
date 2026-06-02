module

public import BernoulliRegular.Reflection.SingularKummer.ComponentChoice

/-!
# Singular Kummer: component ranges under a surjective map

If a surjective homomorphism commutes with two endomorphisms, then it maps the
range of the source endomorphism onto the range of the target endomorphism.

For the singular-Kummer argument this is the elementary algebra behind component surjectivity once
the character component is realized as the range of the corresponding
projection operator.
-/

@[expose] public section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ComponentProjection

variable {G H : Type*} [Group G] [Group H]


open scoped nonZeroDivisors

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]



end ComponentProjection

end SingularKummer
end Reflection
end BernoulliRegular

end
