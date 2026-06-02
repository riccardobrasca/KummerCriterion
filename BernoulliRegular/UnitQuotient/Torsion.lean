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

/-- The unit group `E = 𝒪_Kˣ` used in the reflection unit quotient. -/
abbrev CyclotomicUnitGroup : Type _ :=
  (𝓞 K)ˣ

/-- The roots-of-unity subgroup of the unit group. -/
abbrev CyclotomicUnitTorsion : Subgroup (CyclotomicUnitGroup K) :=
  NumberField.Units.torsion K

/-- The torsion-free quotient of the unit group, written additively so it
inherits the `ℤ`-module structure from Dirichlet's unit theorem. -/
abbrev CyclotomicUnitFreePart : Type _ :=
  Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)

/-- The quotient map from units to the torsion-free quotient. -/
def cyclotomicUnitFreeClass : CyclotomicUnitGroup K →* (𝓞 K)ˣ ⧸ CyclotomicUnitTorsion K :=
  QuotientGroup.mk' (CyclotomicUnitTorsion K)


/-- The kernel of the free quotient map is exactly the torsion subgroup. -/
theorem cyclotomicUnitFreeClass_ker :
    (cyclotomicUnitFreeClass K).ker = CyclotomicUnitTorsion K :=
  QuotientGroup.ker_mk' (CyclotomicUnitTorsion K)

/-- The Dirichlet basis of the torsion-free quotient. -/
def cyclotomicUnitFreeBasis :
    Basis (Fin (NumberField.Units.rank K)) ℤ (CyclotomicUnitFreePart K) :=
  NumberField.Units.basisModTorsion K





/-- Packaged torsion/free decomposition used by later unit-quotient tickets. -/
structure CyclotomicUnitDecomposition where

namespace CyclotomicUnitDecomposition

variable {K}



end CyclotomicUnitDecomposition


end BernoulliRegular
