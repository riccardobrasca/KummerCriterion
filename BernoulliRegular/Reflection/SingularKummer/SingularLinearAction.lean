module

public import BernoulliRegular.Reflection.SingularKummer.SingularZMod

/-!
# Singular Kummer: multiplicative actions as additive `ZMod p`-linear actions

This file converts multiplicative automorphism actions on `p`-torsion
commutative groups into additive `ZMod p`-linear actions.  Applied to the
singular exact sequence, multiplicative equivariance of `S → A[p]` becomes
linear equivariance of the corresponding `ZMod p`-linear map.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace SingularLinearAction

variable {p : ℕ}
variable {G H D : Type*} [CommGroup G] [CommGroup H] [Monoid D]
variable [Module (ZMod p) (Additive G)] [Module (ZMod p) (Additive H)]






namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]



end SingularPair

end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
