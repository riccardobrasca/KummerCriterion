module

public import BernoulliRegular.Reflection.Local.Basic

/-!
# Principal-unit filtration API

This file proves the formal subgroup facts about the local principal-unit
filtration

```text
U_n = 1 + lambda^n O_F.
```

It is the REF-10a layer: no cyclotomic ramification calculation is used here.
The lemmas only use the local notation from `Local.Basic` and general facts
about powers of ideals and subgroups.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Ideal

section OneUnits

variable {R : Type*} [CommRing R]



end OneUnits

end Ideal

namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]







@[simp]
theorem one_mem_principalUnitSubgroup (n : ℕ) :
    (1 : localCyclotomicUnitGroup p K) ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).one_mem






/-- The subgroup of `q`-th powers of `U_n`. -/
def principalUnitPowerSubgroup (q n : ℕ) :
    Subgroup (localCyclotomicUnitGroup p K) :=
  (principalUnitSubgroup p K n).map (powMonoidHom q)

@[simp]
theorem mem_principalUnitPowerSubgroup_iff {q n : ℕ}
    {u : localCyclotomicUnitGroup p K} :
    u ∈ principalUnitPowerSubgroup p K q n ↔
      ∃ v, v ∈ principalUnitSubgroup p K n ∧ v ^ q = u := by
  rfl



end CyclotomicSetup

end Local
end Reflection

end BernoulliRegular
