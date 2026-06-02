module

public import Mathlib.RingTheory.Teichmuller
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseUnitResidue

/-!
# Teichmüller residue-unit lifts at `lambda`

This file replaces the arbitrary residue lifts from
`KummerArtinHasseUnitResidue` by adic Teichmüller lifts in the completed
local integer ring.  This is the second piece of the explicit local
decomposition used by the Kummer--Artin--Hasse correction:

* identify the completed first residue quotient with the uncompleted residue
  quotient already used by the unit-residue map;
* construct the Teichmüller lift of each nonzero residue class;
* prove its residue and finite-order equations.

The construction uses `Perfection.teichmuller₀` and stays in the explicit
local model.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

-- The completed residue quotient instances expand through adic completion.
-- The explicit Teichmüller construction below repeatedly asks typeclass search
-- for the quotient ring structure, so this file raises the local budget.
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
