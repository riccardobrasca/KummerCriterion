module

public import BernoulliRegular.Reflection.Local.PowerMap

/-!
# Endpoint local-unit subgroups

This file starts the REF-10d endpoint layer.  It packages the formal subgroup
assembled from the cyclotomic `p`-th roots of unity and `U_2`, and records the
containment and `p`-power consequences that follow from REF-10b and REF-10c.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]










end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular
