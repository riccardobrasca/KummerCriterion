module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingTerm

/-!
# Unbounded multi-index carry reduction (REF-18c2c4-L2c3d-4e)

The Dwork expansion ranges over all multi-indices `Fin f → ℕ`, not just
digit-bounded vectors.  This file supplies the purely combinatorial bridge
from those unbounded multi-indices to the existing digit-vector survivor
lemmas: cyclic base-`ℓ` carrying preserves the weighted value modulo
`ℓ ^ f - 1` and strictly lowers total weight until all entries are `< ℓ`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
