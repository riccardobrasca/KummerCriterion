module

public import BernoulliRegular.Reflection.SingularKummer.FiniteGroupComparison
public import BernoulliRegular.Reflection.SingularKummer.SingularClassChoice

/-!
# Singular Kummer: finite comparison on projected components

The finite-group comparison between `A / nA` and `A[n]` applies to any finite
additive subgroup, in particular to the range of an additive endomorphism or a
linear projection.  This is the component-level form needed before connecting
the nontriviality of `V_i` with the projected target component of `A[p]`.
-/

@[expose] public section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ProjectedFiniteComparison

variable {A : Type*} [AddCommGroup A] [Finite A]



variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite M]



variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]


variable {W : Type*} [AddCommGroup W] [Module (ZMod p) W]




variable [Finite W]


variable [NeZero p]



end ProjectedFiniteComparison

end SingularKummer
end Reflection
end BernoulliRegular

end
