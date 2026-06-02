module

public import Mathlib.Algebra.Module.ZMod
public import BernoulliRegular.Reflection.Local.Completion

/-!
# Local principal-unit quotients

This file starts the REF-11 local unit component calculation.  It packages the
completed principal-unit quotient `completed U_1 / completed U_1^p` and its
additive `ZMod p`-module structure, using the REF-10 endpoint equality
`completed U_1^p = completed U_{p+1}`.
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
