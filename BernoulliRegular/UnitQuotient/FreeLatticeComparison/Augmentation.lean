module

public import BernoulliRegular.UnitQuotient.FreeCharacterProfile

/-!
# Unit quotients: augmentation comparison

This file defines the full logarithmic augmentation hyperplane, identifies it
with the deleted-coordinate logarithmic space, and records the equivariant
restricted embedding of the torsion-free unit quotient.
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
