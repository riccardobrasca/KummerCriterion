module

public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionEigen
public import BernoulliRegular.Reflection.SingularKummer.FiniteGroupComparison

/-!
# Singular Kummer: elementary quotient components

This file defines the elementary quotient

```text
  V = A / pA
```

for an additive abelian group `A`, equips it with its natural `ZMod p`-module
structure, and transports a `Delta = (ZMod p)ˣ` action on `A` to a linear
action on `V`.

The `i`-th component of `V` is the range of the same character projection used
elsewhere in the singular-Kummer argument.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ElementaryQuotientComponent

variable {p : ℕ}
variable {A : Type*} [AddCommGroup A]

end ElementaryQuotientComponent

end SingularKummer
end Reflection
end BernoulliRegular

end

end
