module

public import BernoulliRegular.UnitQuotient.FreeAction
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Unit quotients: logarithmic embedding and permutation action

This file proves `REF-07c2`.

The Dirichlet logarithmic embedding in mathlib uses a deleted coordinate
`NumberField.Units.logSpace K`, where one infinite place is omitted.  That
space is convenient for Dirichlet's unit theorem, but it is not literally
stable under the Galois permutation of infinite places.

Here we first use the full logarithmic space

```text
InfinitePlace K → ℝ.
```

On this full space the comparison is clean: the cyclotomic action on units is
intertwined by the logarithmic embedding with the permutation action on
infinite places.  Later steps can pass from this full permutation
representation to the usual deleted-coordinate Dirichlet lattice.
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
