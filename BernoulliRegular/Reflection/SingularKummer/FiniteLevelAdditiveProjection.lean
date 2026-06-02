module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelIdempotent

/-!
# Singular Kummer: exact finite-level projections for additive actions

This file applies the exact finite-level character idempotent to an additive
action.  If a finite group `D` acts on an additive group `A` by additive
automorphisms and `A` is viewed as a `ZMod m`-module, then a character

```text
  chi : D -> (ZMod m)^*
```

defines an exact finite-level projection.  Its range is the subgroup on which
the action has character `chi`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelAdditiveProjection

open FiniteLevelIdempotent

variable {m : ℕ}
variable {D A : Type*} [Group D] [Fintype D]
variable [AddCommGroup A] [Module (ZMod m) A]

end FiniteLevelAdditiveProjection

end SingularKummer
end Reflection
end BernoulliRegular

end

end
