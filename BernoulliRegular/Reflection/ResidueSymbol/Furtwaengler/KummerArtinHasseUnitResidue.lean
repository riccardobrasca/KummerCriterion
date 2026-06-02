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

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
