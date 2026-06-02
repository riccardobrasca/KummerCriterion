module

public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Singular Kummer: finite group comparison

This file proves the elementary finite-group fact used at the start of the
singular-group construction.

For a finite abelian group `A`, the elementary quotient

```text
A / pA
```

is nontrivial if and only if the subgroup

```text
A[p] = {x : A | p • x = 0}
```

is nontrivial.  The proof is only the finite endomorphism fact that an
endomorphism of a finite type is injective if and only if it is surjective.

The component-refined statement will require the same comparison after passing
to character components; this file isolates the group-theoretic core.
-/

@[expose] public section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

variable {A : Type*} [AddCommGroup A]

/-- The subgroup `nA` of `n`-multiples in an additive abelian group. -/
abbrev multiplesSubgroup (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) n).range

/-- The subgroup `A[n]` of elements killed by `n`. -/
abbrev torsionBySubgroup (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) n).ker

/-- The elementary quotient `A / nA`, written additively. -/
abbrev elementaryQuotient (A : Type*) [AddCommGroup A] (n : ℕ) : Type _ :=
  A ⧸ multiplesSubgroup A n

end SingularKummer
end Reflection
end BernoulliRegular

end
