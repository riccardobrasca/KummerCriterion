module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Equiv.Basic
public import BernoulliRegular.Reflection.SingularKummer.ComponentProjection

/-!
# Singular Kummer: additive character projections

This file records the additive linear algebra used for the character-component
part of the singular-Kummer argument.  For a `ZMod p`-module with a linear action of
`Delta = (ZMod p)ˣ`, a character projection is a finite `ZMod p`-linear
combination of the action operators.  Any equivariant linear map commutes with
these projections, and a surjective equivariant map maps the source projection
range onto the target projection range.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace CharacterProjection

variable (p : ℕ)

variable {p}
variable [NeZero p]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module (ZMod p) M] [Module (ZMod p) N]

end CharacterProjection

end SingularKummer
end Reflection
end BernoulliRegular

end

end
