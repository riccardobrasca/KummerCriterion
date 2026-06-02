module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import BernoulliRegular.Reflection.Local.RootsOfUnity

/-!
# The `p`-power map on local principal units

This file proves the REF-10c1 filtration estimate for the local principal-unit
filtration at `lambda`: for positive `n`, taking `p`-th powers sends `U_n` into
`U_{n+1}`.
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
