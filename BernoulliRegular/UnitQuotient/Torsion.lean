module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Unit quotients: torsion and free parts

This file starts the `T040` unit-quotient layer.  It records the part of
Dirichlet's unit theorem used before quotienting by powers: the unit group
splits into roots of unity and a free quotient with the standard Dirichlet
basis.

The actual reflection argument only needs this API for cyclotomic fields, but
the torsion/free decomposition is available for every number field.
-/

@[expose] public section

noncomputable section

open Module NumberField
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K] [NumberField K]













namespace CyclotomicUnitDecomposition

variable {K}



end CyclotomicUnitDecomposition


end BernoulliRegular
