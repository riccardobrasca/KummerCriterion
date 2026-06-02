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

/-- The completed local integer ring at `lambda = (zeta_p - 1)`. -/
abbrev LambdaLocalIntegerRing : Type _ :=
  Reflection.Local.completedLocalCyclotomicRing p K

/-- The completed local uniformizer `pi = zeta_p - 1`. -/
def lambdaPi : LambdaLocalIntegerRing p K :=
  Reflection.Local.completedLocalCyclotomicUniformizer p K

@[simp]
theorem lambdaPi_ne_zero :
    lambdaPi p K ≠ 0 :=
  Reflection.Local.completedLocalCyclotomicUniformizer_ne_zero (p := p) (K := K)




end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
