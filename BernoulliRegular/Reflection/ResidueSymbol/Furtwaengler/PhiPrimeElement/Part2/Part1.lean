module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement.Part1

/-!
# Data-carrying prime Φ-elements

The ideal-theoretic predicate `StickelbergerIdealEquality P` only says that
`stickelbergerIdeal P` is principal. Its extracted generator is therefore an
arbitrary generator, determined only up to a unit.

For K2-2 we need the actual Gauss-sum Φ element, not an arbitrary generator of
the same ideal. This file introduces a non-`Prop` object whose `gamma` field is
the element used in the residue-symbol theorem. The current constructor wires
in the existing `phiPrimeGenDescent S a` route from `CrossRingBridge.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement





/-! ### Bundled K2-2 interface -/



/-! ### Conductor-flexible source data -/


/-! ### Conductor-flexible reciprocal source data -/








end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
