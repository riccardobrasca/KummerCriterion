module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MultiIndexCarry

/-!
# Dwork assembly for the reciprocal Stickelberger congruence

This file replaces the deprecated denominator-cleared digit-vector assembly
with the corrected Dwork multi-index expansion.  The Dwork expansion ranges
over all multi-indices, and `MultiIndexCarry` supplies the bridge from those
multi-indices to the minimal-weight digit-vector survivor lemmas.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
