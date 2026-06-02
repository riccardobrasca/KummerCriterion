module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseLocalModel

/-!
# Residue splitting for completed local units

This file proves the first, purely algebraic, part of the local decomposition
needed by the Kummer--Artin--Hasse formula.  A completed local unit has a
residue in the residue field at `lambda`; after choosing a lift of that
residue from the uncompleted local unit group and mapping it into the
completion, the quotient is a completed principal unit.

This is not yet the Teichmuller finite-order lift.  It is only the residue
splitting that the later Teichmuller construction must refine.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The residue ring of the local cyclotomic ring at `lambda`.

This is definitionally the residue field of the uncompleted local ring.  We
use the uncompleted residue ring as target because the completed ring maps to
it through `AdicCompletion.evalOneₐ`. -/
abbrev LambdaResidueRing : Type _ :=
  Reflection.Local.localCyclotomicRing p K ⧸
    Reflection.Local.localCyclotomicMaximalIdeal p K

/-- The nonzero residue classes, written as units of the residue ring. -/
abbrev LambdaResidueUnitGroup : Type _ :=
  (LambdaResidueRing p K)ˣ













end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
