module

public import BernoulliRegular.Reflection.Local.Basic

/-!
# Principal-unit filtration API

This file proves the formal subgroup facts about the local principal-unit
filtration

```text
U_n = 1 + lambda^n O_F.
```

It is the REF-10a layer: no cyclotomic ramification calculation is used here.
The lemmas only use the local notation from `Local.Basic` and general facts
about powers of ideals and subgroups.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Ideal

section OneUnits

variable {R : Type*} [CommRing R]



end OneUnits

end Ideal

namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

















end CyclotomicSetup

end Local
end Reflection

end BernoulliRegular
