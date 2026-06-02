module

public import BernoulliRegular.Reflection.Local.ComponentDimension
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionEigen
public import BernoulliRegular.Reflection.SingularKummer.CyclotomicAction
public import BernoulliRegular.Reflection.SingularKummer.Localization

/-!
# Singular Kummer: choosing a class in the localization kernel

This file records the REF-13 dimension argument.  Once the localization map is
expressed on the `i`-th singular component with codomain the completed local
principal-unit `i`-component, the inequality

```text
  dim S_i >= 2,       dim (U / U^p)_i = 1
```

gives a nonzero singular class killed by localization.  The final theorem also
unwraps that class to a singular pair `(I, eta)`, recording the singular
principal-ideal relation and the `Delta` eigenrelation.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace LinearDimensionKernel

variable {F U V W A : Type*} [Field F]
variable [AddCommGroup U] [Module F U]
variable [AddCommGroup V] [Module F V]
variable [AddCommGroup W] [Module F W]
variable [AddCommGroup A] [Module F A]





end LinearDimensionKernel

namespace SingularPair

open SingularLinearAction.SingularPair

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

end SingularPair
end SingularKummer
end Reflection
end BernoulliRegular

end

end
