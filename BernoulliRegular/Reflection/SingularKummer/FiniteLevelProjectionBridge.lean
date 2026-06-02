module

public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionIdempotent
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Torsion

/-!
# Singular Kummer: finite-level bridge from `V_i` to `A[p]_i`

This file isolates the exact finite-level input needed for Lemma 2.1 of
`kummer_reflection.tex`.

Let `B` be a finite additive subgroup of `A`.  If the natural map

```text
  B / pB -> A / pA
```

contains the projected component `V_i`, and if `B[p]` maps into the projected
component of `A[p]`, then nontriviality of `V_i` implies nontriviality of the
matching component of `A[p]`.

The remaining mathematical construction is to take `B` to be the exact
finite-level character component, obtained from the `p`-adic idempotent acting
on the finite group `A`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelProjectionBridge

open ElementaryQuotientComponent
open ProjectedSubgroupComparison
open TorsionComponent

variable {p : ℕ}
variable {A : Type*} [AddCommGroup A]









end FiniteLevelProjectionBridge

end SingularKummer
end Reflection
end BernoulliRegular

end

end
