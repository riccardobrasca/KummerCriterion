module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelTorsionReduction
public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelProjectionBridge

/-!
# Singular Kummer: finite-level projection and the elementary quotient

This file proves the quotient half of the exact finite-level bridge.  If the
coefficients of the exact finite-level idempotent reduce modulo `p` to the
usual `i`-th character-projection coefficients, then the image of the exact
finite-level projection subgroup contains the mod-`p` component `V_i`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelQuotientComparison

open ElementaryQuotientComponent

variable {p m : ℕ} [NeZero p] [NeZero m]
variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A]

end FiniteLevelQuotientComparison

end SingularKummer
end Reflection
end BernoulliRegular

end

end
