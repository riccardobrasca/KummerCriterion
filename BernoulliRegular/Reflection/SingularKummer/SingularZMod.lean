module

public import BernoulliRegular.Reflection.SingularKummer.CharacterProjection

/-!
# Singular Kummer: `ZMod p` structures on the singular exact sequence

The singular quotient `S` is killed by `p`: for a singular pair
`(I, alpha)` with `(alpha) = I^p`, the `p`-th power of the pair is the
principal pair attached to `alpha`, hence trivial in the quotient by principal
pairs.  The target `A[p]` is killed by `p` by definition.

After passing to additive notation, both sides become `ZMod p`-modules and the
map `S → A[p]` becomes a surjective `ZMod p`-linear map.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
