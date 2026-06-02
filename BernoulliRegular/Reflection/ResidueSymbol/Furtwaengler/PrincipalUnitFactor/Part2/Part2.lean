module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.Part2.Part1

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace PhiPrimeElement







/-! ### Conductor-flexible reciprocal source-data facts -/







end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
