module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelAdditiveProjection
public import BernoulliRegular.Reflection.SingularKummer.TorsionComponent

/-!
# Singular Kummer: reducing finite-level components to `p`-torsion components

This file records the passage from an exact finite-level character relation to
the mod-`p` character component on `A[p]`.  The point is elementary: on an
element killed by `p`, scalar multiplication by an element of `ZMod m` only
depends on its image in `ZMod p`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelTorsionReduction

variable {p m : ℕ} [NeZero p] [NeZero m]
variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A]

end FiniteLevelTorsionReduction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
