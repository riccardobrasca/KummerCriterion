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

/-- The cyclotomic Galois group in the explicit model used for character
indices. -/
abbrev Delta : Type :=
  (ZMod p)ˣ

variable {p}
variable [NeZero p]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module (ZMod p) M] [Module (ZMod p) N]

/-- A finite linear combination of the operators in a `Delta`-action.  The
standard character projection is obtained by using the usual character
coefficients. -/
def projection
    (ρ : Delta p →* M ≃ₗ[ZMod p] M) (c : Delta p → ZMod p) :
    M →ₗ[ZMod p] M :=
  ∑ a : Delta p, c a • (ρ a : M →ₗ[ZMod p] M)


/-- Coefficients for the `i`-th character projection.  The coefficient attached
to `a` is `|Delta|⁻¹ a⁻ᶦ`, with values in `ZMod p`. -/
def characterProjectionCoefficient (i : ℕ) (a : Delta p) : ZMod p :=
  (Fintype.card (Delta p) : ZMod p)⁻¹ * (((a⁻¹ : Delta p) : ZMod p) ^ i)

/-- The finite-sum projection attached to the `i`-th character. -/
def characterProjection
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) :
    M →ₗ[ZMod p] M :=
  projection (p := p) ρ (characterProjectionCoefficient (p := p) i)





end CharacterProjection

end SingularKummer
end Reflection
end BernoulliRegular

end

end
