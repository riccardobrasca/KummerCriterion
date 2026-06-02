module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ModPRepresentation

/-!
# Unit quotients: actual free quotient eigenspaces

This file packages the actual Delta and even-Delta eigenspaces in the reduced
free quotient, proves projector landing and decomposition statements, and
records the odd-character vanishing result.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite
attribute [local instance] NumberField.Units.instZLattice_unitLattice

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]













end BernoulliRegular

end
