module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelQuotientComparison

/-!
# Singular Kummer: final finite-level bridge

This file assembles the exact finite-level subgroup argument.  The exact
projection subgroup covers the quotient component `V_i`, and its `p`-torsion
lies in the matching `A[p]_i` component.  Therefore nontriviality of `V_i`
implies nontriviality of `A[p]_i`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelFinalBridge

open ElementaryQuotientComponent
open TorsionComponent

variable {p m : ℕ} [NeZero p] [NeZero m]
variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A] [Finite A]


end FiniteLevelFinalBridge

end SingularKummer
end Reflection
end BernoulliRegular

end

end
