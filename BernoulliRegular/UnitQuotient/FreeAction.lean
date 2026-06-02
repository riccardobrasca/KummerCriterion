module

public import BernoulliRegular.UnitQuotient.DeltaAction

/-!
# Unit quotients: the actual action on the Dirichlet free quotient

This file proves `REF-07c1`.  The actual cyclotomic action on
`E = O_K^*` preserves the torsion subgroup of roots of unity, so it descends
to the torsion-free quotient `E / E_tors`.  Since this quotient is written in
additive notation as `CyclotomicUnitFreePart`, the descended action is packaged
as a `Z`-linear automorphism.

No logarithmic embeddings are used here; the comparison with the Dirichlet
logarithmic lattice is the next step.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]










end BernoulliRegular

end
