module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot

/-!
# Canonical `pthSymbolAtPrime` and explicit Galois action

This file gives a *canonical* version of `pthSymbolAtPrime` that uses the
canonical primitive `p`-th root of unity `canonicalResidueZetaP q` instead of
`Classical.choose`. The canonical choice is Galois-equivariant in a precise
sense (see `canonicalResidueZetaP_val_galois_compat`), so the Galois-action
transformation of the residue symbol takes the explicit form

```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • q) = (a : ZMod p) * pthSymbolAtPrime_canonical α q.
```

This eliminates the opaque unit factor `c : (ZMod p)ˣ` that appears in the
existence-form `pthSymbolAtPrime_galoisAction_exists_unit`.

## Main definitions and theorems

* `pthSymbolAtPrime_canonical α q` — the residue symbol defined using the
  canonical primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`.
* `pthSymbolAtPrime_canonical_galoisAction` — the explicit Galois-action
  transformation with factor `(a : ZMod p)`.
* `pthSymbolAtPrime_eq_canonical_up_to_unit` — the canonical and
  `Classical.choose`-based versions agree up to a unit factor in `(ZMod p)ˣ`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Step 1 — units-level Galois compatibility

The compatibility statement
`canonicalResidueZetaP_val_galois_compat` is at the level of underlying ring
elements; lifting it to the level of units is mechanical via `Units.ext`. -/


/-! ### Step 2 — `pthSymbolAtPrime_canonical` definition

Like `pthSymbolAtPrime`, this is `0` whenever the preconditions fail. In the
"good" case (`q ≠ ⊥`, maximal, `α ∉ q`, `p ∣ Nq − 1`, `(p : 𝓞 K) ∉ q`) it
equals `primeExponent` with the *canonical* primitive `p`-th root, eliminating
the `Classical.choose`. -/











/-! ### Step 2b — algebraic API: `_one`, `_mul`, `_pow`, `_pow_p_eq_zero`

Mirrors the API for non-canonical `pthSymbolAtPrime` (`_one`, `_mul`, `_pow`,
`_pow_p_eq_zero`). The canonical version is well-behaved for the same reasons:
in the bad branches everything is `0`; in the good branch the same canonical
ζ is used for both sides, so the lemmas reduce to `primeExponent_one`,
`primeExponent_mul`, `primeExponent_pow` from `Reflection/ResidueSymbol/Basic.lean`. -/







/-! ### Step 2c — bidirectional vanishing iff and congruence helpers -/





/-! ### Step 3 — explicit Galois action

The canonical zeta is Galois-equivariant up to a `(.val)`-power exponent
(`canonicalResidueZetaP_val_galois_compat`). Combined with
`primeExponent_ringEquiv` and `primeExponent_zeta_pow`, this gives the
explicit form:

```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • q) = (a : ZMod p) * pthSymbolAtPrime_canonical α q.
```

The proof is the chain
`primeExponent σq canonicalZetaSigmaQ (σα) =`
`(a.val : ZMod p) * primeExponent σq (canonicalZetaSigmaQ^a.val) (σα)`
`  [primeExponent_zeta_pow]`
`= (a.val : ZMod p) * primeExponent σq (Units.mapEquiv σ_q canonicalZetaQ) (σα)`
`  [units_galois_compat]`
`= (a.val : ZMod p) * primeExponent q canonicalZetaQ α [primeExponent_ringEquiv]`. -/


/-! ### Step 3b — corollaries of the explicit Galois action

Variants and consequences of `pthSymbolAtPrime_canonical_galoisAction`:
* `_galoisAction_iff` — the equation is an iff (one of three equivalent forms).
* `_galoisAction_one` — at the identity element of the Galois group, the action
  is trivial: it amounts to `pthSymbolAtPrime_canonical α q`.
* `_compose_galois` — composing two Galois actions multiplies the factors.
-/




/-! ### Step 4 — compatibility with `pthSymbolAtPrime`

The canonical and `Classical.choose`-based versions agree up to a unit factor
in `(ZMod p)ˣ`. Concretely: `Classical.choose hroot` is some primitive `p`-th
root of unity in `(𝓞 K ⧸ q)ˣ`, and `canonicalResidueZetaP q` is another. By
`IsPrimitiveRoot.isPrimitiveRoot_iff'` the two differ by an `n`-th power for
some `n.Coprime p`, and the residue exponents are related by multiplication
by `(n : ZMod p)`. -/


/-! ### Step 5 — vanishing-bridge lemmas between the two versions

When `pthSymbolAtPrime_canonical α q = 0`, the corresponding
`pthSymbolAtPrime α q = 0` as well (via the unit factor `c`), and conversely
since the unit factor is invertible. These bridge "vanishing on the canonical
side" and "vanishing on the non-canonical side" without needing to know what
the unit factor is. -/




end Furtwaengler

end BernoulliRegular
