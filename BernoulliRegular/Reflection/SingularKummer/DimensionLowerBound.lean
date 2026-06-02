module

public import BernoulliRegular.Reflection.SingularKummer.GlobalUnitKernel
public import BernoulliRegular.Reflection.SingularKummer.SingularLinearAction
public import BernoulliRegular.Reflection.SingularKummer.SingularZMod
public import BernoulliRegular.UnitQuotient.GlobalUnitDimension
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Singular Kummer: dimension lower bounds

This file records the REF-08 dimension step.  The first lemma is the reusable
linear algebra argument: if a component of the kernel side has dimension one
and the matching target component is nonzero, then the middle component has
dimension at least two.

The singular-Kummer wrapper applies that lemma to the exact sequence

```text
E/E^p -> S -> A[p].
```

The actual cyclotomic component compatibility for `S_i` is kept as explicit
hypotheses, so this file can be used before the final concrete `Delta` action
on the singular group is fully assembled.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace LinearDimensionLowerBound

variable {F U S A : Type*} [Field F]
variable [AddCommGroup U] [Module F U]
variable [AddCommGroup S] [Module F S]
variable [AddCommGroup A] [Module F A]


end LinearDimensionLowerBound

namespace SingularPair

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]














end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end
