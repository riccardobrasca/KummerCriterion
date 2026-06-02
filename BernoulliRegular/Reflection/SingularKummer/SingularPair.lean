module

public import Mathlib.Algebra.Exact
public import Mathlib.RingTheory.ClassGroup

/-!
# Singular Kummer: singular pairs

This file begins the formal singular-group construction in a choice-free form.

Instead of immediately quotienting singular numbers modulo global `p`-th
powers, we first use *singular pairs*

```text
(I, alpha),    (alpha) = I^p,
```

where `I` is an invertible fractional ideal and `alpha` is a nonzero element of
the fraction field.  Such a pair maps canonically to the class of `I`, and that
class is killed by `p`.

This is the formal core of the map from singular data to `A[p]`.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

namespace SingularPair

variable {R K}
variable {p : ℕ}

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
