module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import BernoulliRegular.Reflection.Local.GradedAction
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionIdempotent

/-!
# Local unit component dimensions

This file starts the REF-11d assembly layer.  It packages the completed local
principal-unit quotient `completed U_1 / completed U_1^p` with its additive
`ZMod p` character projectors, using the `Delta` action constructed in
`Local.DeltaAction`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

end CyclotomicSetup
end Local
end Reflection
end BernoulliRegular

end
