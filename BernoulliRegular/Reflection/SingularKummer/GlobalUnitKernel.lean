module

public import BernoulliRegular.Reflection.SingularKummer.SingularPair
public import BernoulliRegular.UnitQuotient.Components

/-!
# Singular Kummer: global units in the kernel

The pair-form singular exact sequence in `SingularPair` identifies the kernel
of `S → A[p]` with the image of the *fractional* units of `K`.  For the
reflection argument this kernel must be written in terms of the actual global
units `E = (𝓞 K)ˣ`, and then in terms of the quotient `E / E^p`.

This file specializes the fractional-unit statement to rings of integers and
records the global-unit form of the same kernel identity.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace SingularPair

variable (K : Type*) [Field K] [NumberField K]
variable {p : ℕ}

















end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
