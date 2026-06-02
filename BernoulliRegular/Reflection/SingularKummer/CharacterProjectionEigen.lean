module

public import BernoulliRegular.Reflection.SingularKummer.SingularRepresentative

/-!
# Singular Kummer: character projections are eigenspaces

This file proves the elementary eigenspace calculation for the character
projection

```text
  e_i = |Delta|^{-1} sum_a a^{-i} [a].
```

If an element lies in the range of this projection, then the action of
`b : Delta` on it is multiplication by `b^i`.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace CharacterProjection

variable {p : ℕ} [NeZero p]
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]




end CharacterProjection

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
