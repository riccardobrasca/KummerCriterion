module

public import BernoulliRegular.Reflection.SingularKummer.ProjectedFiniteComparison

/-!
# Singular Kummer: torsion components

For an additive abelian group `A`, this file sets up the `p`-torsion subgroup

```text
  A[p] = {x : A | p • x = 0}
```

as a `ZMod p`-module.  A `Delta = (ZMod p)ˣ` action on `A` restricts to a
linear action on `A[p]`, so the same character projections used for
`V = A / pA` define the projected components of `A[p]`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace TorsionComponent

variable {p : ℕ}
variable {A : Type*} [AddCommGroup A]

end TorsionComponent

end SingularKummer
end Reflection
end BernoulliRegular

end

end
