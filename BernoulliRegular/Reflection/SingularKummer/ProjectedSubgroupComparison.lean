module

public import BernoulliRegular.Reflection.SingularKummer.TorsionComponent

/-!
# Singular Kummer: finite comparison through a projected subgroup

This file records the finite-group step in the form needed for Lemma 2.1 of
`kummer_reflection.tex`.

If `B` is a finite additive subgroup of `A`, then nontriviality of `B / pB`
forces nontriviality of `B[p]`.  Therefore, if the natural inclusion
`B[p] -> A[p]` lands in a chosen character component of `A[p]`, that component
is nontrivial.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ProjectedSubgroupComparison

open TorsionComponent

variable {p : ℕ}
variable {A : Type*} [AddCommGroup A]



end ProjectedSubgroupComparison

end SingularKummer
end Reflection
end BernoulliRegular

end

end
