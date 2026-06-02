module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import BernoulliRegular.Reflection.Local.Graded
public import BernoulliRegular.Reflection.Local.Completion.Part1

/-!
# Completed local principal units

This file starts the REF-10d3b completed endpoint layer.  The localized ring
`Localization.AtPrime` is not complete, so the reverse `p`-power endpoint is
recorded in the adic completion at the cyclotomic maximal ideal.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local


end Local
end Reflection
end BernoulliRegular
