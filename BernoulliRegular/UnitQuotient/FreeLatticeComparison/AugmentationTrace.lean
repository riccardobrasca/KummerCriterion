module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.Augmentation

/-!
# Unit quotients: augmentation trace comparison

This file restricts the cyclotomic permutation action to the augmentation
hyperplane and compares its trace with the trace on the full logarithmic
permutation representation.
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
