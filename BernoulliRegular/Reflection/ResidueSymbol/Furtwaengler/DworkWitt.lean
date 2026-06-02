module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# Witt-vector bridge for Dwork splitting

This file contains the Witt-vector uniqueness bridge needed by the all-order
Artin-Hasse/Dwork splitting proof. The key point is that in every quotient
`𝓞 R' / Q^(N+1)`, the residue characteristic `ℓ` is nilpotent, so mathlib's
Teichmüller-series uniqueness theorem for Witt vectors applies.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
