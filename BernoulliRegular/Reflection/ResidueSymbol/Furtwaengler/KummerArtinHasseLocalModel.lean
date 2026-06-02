module

public import BernoulliRegular.Reflection.Local.UnitQuotient

/-!
# Kummer--Artin--Hasse local model at `lambda`

This file fixes the Lean objects used for the explicit `lambda`-local
correction in the Kummer reciprocity proof.  The mathematical model is

```text
F = Q_p(zeta_p),    O_F = its completed integer ring,
pi = zeta_p - 1,   U_n = 1 + pi^n O_F.
```

The current project already develops the completed local integer ring and
completed principal-unit filtration under
`BernoulliRegular.Reflection.Local`.  We expose those objects here under names
specific to the Kummer--Artin--Hasse formula.

This file only pins down the local model that the explicit formula must use.
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
