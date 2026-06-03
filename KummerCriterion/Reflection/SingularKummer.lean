module

public import KummerCriterion.Reflection.Local.Basic

/-!
# Singular Kummer: localization at a height-one prime

This file provides the localization target. For a height-one prime
`v`, the local units are represented inside `Kˣ` as the elements with
`v`-adic valuation one. After choosing a uniformizer, every global field
class in `Kˣ / Kˣ^p` has a normalized representative in this local-unit
subgroup, giving a homomorphism

```text
 Kˣ / Kˣ^p -> U_v / U_v^p.
```

Composing this with the singular-pair generator gives the localization map
from the singular group `S` to the local-unit quotient.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion
namespace Reflection
namespace SingularKummer

namespace SingularPair

section Cyclotomic

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]

/-- The distinguished cyclotomic lambda prime as a height-one prime. -/
def cyclotomicLambdaHeightOne : IsDedekindDomain.HeightOneSpectrum (𝓞 F) where
  asIdeal := Local.cyclotomicLambda p F
  isPrime := zetaPrime_isPrime p F
  ne_bot := zetaPrime_ne_bot p F

end Cyclotomic

end SingularPair

end SingularKummer
end Reflection
end KummerCriterion

end
