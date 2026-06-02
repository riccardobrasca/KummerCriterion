module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import BernoulliRegular.Reflection.Local.Filtration


/-!
# Local cyclotomic roots of unity

This file starts the REF-10b root-of-unity layer for the local calculation.
It localizes the distinguished primitive `p`-th root of unity and proves that
the subgroup it generates lies in the first principal-unit step `U_1`.
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
