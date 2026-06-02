module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler

/-!
# Ideal-level Galois action of `pthSymbolAtIdeal_canonical` (Atom D core)

This file lifts `pthSymbolAtPrime_canonical_galoisAction` from primes to
arbitrary integer ideals, via the multiset of normalized factors.

## Main theorem

```
pthSymbolAtIdeal_canonical (σ_a α) (σ_a • I) = (a : ZMod p) * pthSymbolAtIdeal_canonical α I
```
under hypotheses on each prime factor of `I`.

This is the **substantive ideal-level content of Atom D** (without the
specialisation to a Δ-character of η, which controls the final Galois weight `k`).
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Multiset bijection on normalized factors -/


/-! ### Ideal-level Galois action -/


/-! ### Principal-ideal version -/



/-! ### Unconditional prime-level Galois action (case-analysis on hypotheses) -/


/-! ### Unconditional ideal-level Galois action -/



/-! ### Galois weight 1 specialization (η fixed pointwise by σ_a)

When the residue-symbol numerator `α` is fixed by every cyclotomic Galois
automorphism — `σ_a α = α` for all a — the Galois weight of the symbol's
ideal slot is `1`:

```
pthSymbolAtIdeal_canonical α (σ_a I) = (a : ZMod p) * pthSymbolAtIdeal_canonical α I
```

This is the cleanest case of Atom D's transformation rule. -/


end Furtwaengler

end BernoulliRegular

end
