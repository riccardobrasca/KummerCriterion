module

public import BernoulliRegular.Reflection.SingularKummer.ElementaryQuotientComponent
public import BernoulliRegular.Reflection.SingularKummer.ProjectedSubgroupComparison

/-!
# Singular Kummer: integral lifts of character projections

The character projection on `A / pA` and on `A[p]` has coefficients in
`ZMod p`.  To apply the finite-group comparison to an actual subgroup of `A`,
we use the integer lift obtained by replacing each coefficient by its standard
representative in `ℕ`.

This file defines that lift and proves that, after passing to `A / pA` or
restricting to `A[p]`, it recovers the corresponding `ZMod p` character
projection.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace IntegralCharacterProjection

open ElementaryQuotientComponent
open TorsionComponent

variable {p : ℕ} [NeZero p]
variable {A : Type*} [AddCommGroup A]






end IntegralCharacterProjection

end SingularKummer
end Reflection
end BernoulliRegular

end

end
