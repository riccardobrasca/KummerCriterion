module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingTerm.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Conductor-flexible leading-term surface

The enlarged-conductor REF-K route uses
`ConductorFlexibleFullTeichDworkSetup`, not the old exact
`FullTeichDworkSetup`.  The following definitions and small arithmetic wrappers
mirror the exact setup names so the Dwork exact-order proof can be ported
without reintroducing the pair-cyclotomic typeclass. -/

end Furtwaengler

end BernoulliRegular
