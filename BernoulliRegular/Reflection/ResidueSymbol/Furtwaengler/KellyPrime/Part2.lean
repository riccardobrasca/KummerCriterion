module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KellyPrime.Part1

/-!
# Kelly's prime-level identity (REF-18 Phase 2, sub-piece K)

This file builds the Kelly-form prime identity for `α^Θ / P'`:

```
(α^Θ / P')_p = (NP' / α)_p
```

via three steps (K1–K3 in `.mathlib-quality/ref18_phase2_plan.md`):

* **K1**: `(α^Θ / P')_p = ∑_a a.val · (σ_{a^{-1}} α / P')_p` (left-slot
  Galois sum at a single prime).
* **K2**: integer-against-prime symbol formula for `(n / P')_p`.
* **K3**: the substantive Stickelberger-Eisenstein combination
  `∑_a a.val · (σ_{a^{-1}} α / P')_p = (NP' / α)_p`.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]






/-! ### K2 / K3 negation for odd p

For odd p, `pthSymbolAtPrime_canonical (-α) P' = pthSymbolAtPrime_canonical α P'`
unconditionally — the contribution of `(-1)` vanishes because `(-1) = (-1)^p`
for odd p, and the symbol of any p-th power is 0.

Combined with `Ideal.span {-α} = Ideal.span {α}` (since `-1` is a unit),
this yields `K2(-α) ⟺ K2(α)` and `K3(-α) ⟺ K3(α)` for odd p. -/







/-! ### Unconditional discharge for `-β^p` (odd p) -/



/-! ### `KellyIdealIdentity` for non-bot B (special α discharges) -/





end Furtwaengler

end BernoulliRegular

end
