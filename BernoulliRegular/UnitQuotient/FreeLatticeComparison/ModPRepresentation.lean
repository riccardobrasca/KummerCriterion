module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.FreeTrace
public import Mathlib.RepresentationTheory.Basic

/-!
# Unit quotients: mod-p free quotient representation

This file reduces the free unit quotient modulo p, constructs the even-Delta
representation, and computes the traces of its character projectors.
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
