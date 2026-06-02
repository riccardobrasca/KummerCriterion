module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace

/-!
# Unit quotients: free unit trace comparison

This file transports the augmentation trace computation to the Dirichlet free
unit lattice and records that the free-unit action factors through Delta
modulo ±1.
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
