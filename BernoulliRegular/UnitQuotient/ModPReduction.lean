module

public import BernoulliRegular.UnitQuotient.PermutationCharacters
public import BernoulliRegular.UnitQuotient.TorsionCharacter
public import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# Unit quotients: reduction of the free quotient modulo `p`

This file proves the formal reduction step used in `REF-07c4`.

There is no natural map in the direction

```text
E/E_tors -> E/E^p,
```

because torsion units can have nontrivial image modulo `p`-th powers.  The
canonical map goes the other way after removing the torsion contribution:

```text
E/E^p -> (E/E_tors) / p.
```

It is obtained by sending a unit to its class in the Dirichlet free quotient
and then reducing that additive quotient modulo `p`.  The map kills `p`-th
powers, contains the torsion image in its kernel, and is equivariant for the
actual cyclotomic `Delta = (ZMod p)^*` action.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]






















end BernoulliRegular

end
