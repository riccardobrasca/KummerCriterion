module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolCanonical
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical.Part1

/-!
# Canonical `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` and the unconditional c.3 closed form

This file mirrors the `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` API on top
of `pthSymbolAtPrime_canonical`, and uses the explicit Galois-action
transformation from `PthSymbolCanonical.lean` to derive the
**unconditional c.3 closed form**:

```
pthSymbolAtPrincipal_canonical α h_stick.gen =
  ∑ a : CyclotomicUnitDelta p,
    pthSymbolAtPrime_canonical (σ_a α) q_K
```

Compared to the conditional theorem
`pthSymbolAtPrincipal_eq_galois_sum_of_hypothesis` (in
`KummerFurtwaengler.lean`), the canonical version is *unconditional*:
the explicit `(a : ZMod p)` factor in the Galois-action transformation
cancels the digit-sum `a.val` factor, so the closed form eliminates
both the `a.val` weights and the `StickelbergerGaloisHypothesis` input.

## Main definitions and theorems

* `pthSymbolAtIdeal_canonical α I` — the canonical residue symbol at an
  integral ideal, defined as the multiset sum of
  `pthSymbolAtPrime_canonical α P` over the prime factors `P` of `I`.
* `pthSymbolAtPrincipal_canonical α β` — the canonical principal symbol,
  defined as `pthSymbolAtIdeal_canonical α (Ideal.span {β})`.
* `pthSymbolAtPrincipal_canonical_eq_galois_sum` — the **c.3 unconditional
  closed form** taking only `StickelbergerIdealEquality q_K`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]











/-! ### Negation API for `pthSymbolAtPrime_canonical`

Negation lemmas for the canonical residue symbol. The key observation is
that `(-α) = (-1) * α`, and `pthSymbolAtPrime_canonical` is multiplicative
in the numerator. Since `(-1)` is a unit, it lies outside every prime ideal
automatically. -/



/-! ### Negation API for `pthSymbolAtIdeal_canonical`

Mirrors the prime-level negation API at the ideal level. The `(α^n)`-form
uses `pthSymbolAtIdeal_canonical_pow_α` after observing that `(-1)` is a
unit (`unit_notMem_normalizedFactors`). -/






/-! ### Negation API for `pthSymbolAtPrincipal_canonical` -/




/-! ### Compatibility lemmas: canonical vs. non-canonical

Building on `pthSymbolAtPrime_eq_canonical_up_to_unit`, we record the corner
cases (`q = ⊥`, `α ∈ q`) where both versions trivially vanish, giving an
unconditional equality. -/



/-! ### Derived API: vanishing characterizations

Convenient sufficient conditions for the canonical ideal/principal symbol to
vanish. These reduce to the prime-level vanishing lemmas
(`pthSymbolAtPrime_canonical_eq_zero_*`). -/




/-! ### Derived API: associated and equal ideals

The canonical symbol depends on the ideal slot only through the ideal
itself (not its representation). For `Ideal R` with `R` Dedekind, units are
unique, so `Associated I J ↔ I = J`; we provide congruence-style lemmas to
make rewriting easy. -/




/-! ### Ergonomic API for downstream use -/







end Furtwaengler

end BernoulliRegular
