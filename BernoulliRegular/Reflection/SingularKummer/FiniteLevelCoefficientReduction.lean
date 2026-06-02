module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelFinalBridge

/-!
# Singular Kummer: reduction of finite-level idempotent coefficients

The final finite-level bridge needs the exact idempotent coefficients to reduce
to the usual mod-`p` character-projection coefficients.  This file proves that
this follows formally from the corresponding reduction of the character and
invertibility of `|Delta|` at the finite level.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelCoefficientReduction

variable {p m : ℕ} [NeZero p] [NeZero m]



variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A] [Finite A]


end FiniteLevelCoefficientReduction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
