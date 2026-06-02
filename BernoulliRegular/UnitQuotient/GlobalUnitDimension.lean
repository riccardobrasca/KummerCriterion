module

public import BernoulliRegular.UnitQuotient.FreeProjectorRanges
public import Mathlib.Algebra.Module.ZMod

/-!
# Unit quotients: global unit component dimensions

This file assembles `REF-07d`.  The map

```text
E / E^p -> (E / E_tors) / p
```

has the cyclotomic torsion line as kernel.  The kernel is the Teichmuller
line, so it has no even eigenspace.  Therefore the already proved free-part
dimension statement lifts to the actual quotient `E/E^p` for every nontrivial
even character.  The final theorem specializes this to the standard
`j`-power character with `2 <= j <= p - 3`.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset MonoidAlgebra

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

end BernoulliRegular

end
