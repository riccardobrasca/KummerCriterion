module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part18

@[expose] public section

noncomputable section

/-!
# The corrected Dwork parameter

This wrapper imports the split implementation of the completed Dwork parameter.
-/

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular
