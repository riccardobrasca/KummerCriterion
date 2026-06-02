module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.GaussSum
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Stickelberger
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Setup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolCanonical
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import Mathlib.NumberTheory.GaussSum


/-!
# K2-1 substantive atom: Gauss-sum Frobenius congruence (REF-18 Phase 2)

This file builds toward Kelly Proposition 9 (the **prime Φ-symbol identity**):

```
(Φ(P) / P')_p = (NP' / P)_p
```

via its substantive atom **K2-1** (Gauss-sum Frobenius congruence):

```
g(χ_P)^{NP'} ≡ (NP'/P)_p · g(χ_P) (mod P')
```

for prime ideals `P, P'` of `𝓞_K` coprime to `(p)` with coprime
rational norms `(NP, NP') = 1`.

## Strategy (per AI reviewer 2026-05-05)

In the residue ring above `P'` (which has characteristic `ℓ` where
`NP' = ℓ ^ f`), raise the Gauss sum termwise to `NP'`:
* The multiplicative character part `χ^{NP'}` is stable because
  `NP' ≡ 1 (mod p)` (so `χ` has order dividing `p` and `χ^{NP'} = χ`).
* The additive character transforms by `ψ ↦ mulShift ψ NP'` (i.e.,
  `t ↦ NP' · t` on the source).
* Pull out the residue symbol `(NP'/P)_p = χ_P(NP')` via
  `gaussSum_mulShift`.

The current file lays the iterated-Frobenius foundation:

```
gaussSum χ ψ ^ p^n = gaussSum (χ^{p^n}) (ψ^{p^n})
```

a generalization of `MulChar.IsQuadratic.gaussSum_frob_iter` (mathlib)
that drops the quadratic hypothesis. From this, with `χ` of order `p`
and `NP' ≡ 1 (mod p)`, the K2-1 congruence follows by combining with
`gaussSum_mulShift` and the substitution argument.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Iterated Frobenius for Gauss sums (general, non-quadratic)

Mathlib only has `MulChar.IsQuadratic.gaussSum_frob_iter`; we need the
non-quadratic version. By induction on the iteration count, applying
`gaussSum_frob` once per step. -/


/-! ### Character order p and exponent reduction

For a multiplicative character `χ : MulChar R R'` with `χ^p = 1` (order
dividing `p`), `χ^N = χ^{N mod p}`. In particular, when `N ≡ 1 (mod p)`,
`χ^N = χ`.

This is the second ingredient for K2-1: in the residue ring above `P'`
of characteristic `ℓ`, after iterating Frobenius `f` times we have
`gaussSum χ ψ ^ NP' = gaussSum (χ^{NP'}) (ψ^{NP'})` where `NP' = ℓ ^ f`.
The character part `χ^{NP'}` simplifies to `χ` because `χ` has order
dividing `p` (the *outer* prime) and `NP' ≡ 1 (mod p)` (by hypothesis
that `P'` is a "good" prime for the canonical residue symbol). -/



/-! ### K2-1 Gauss-sum Frobenius congruence (combined form)

Combining the three ingredients:
1. **Iterated Frobenius** (`gaussSum_frob_iter`): in a target ring of
   prime characteristic `ℓ`, `g^{ℓ ^ f} = gaussSum (χ^{ℓ ^ f}) (ψ^{ℓ ^ f})`.
2. **Character order reduction** (`mulChar_pow_eq_self_of_modEq_one`):
   if `χ^p = 1` and `N ≡ 1 (mod p)`, then `χ^N = χ`.
3. **AddChar pow = mulShift** (mathlib's `pow_mulShift`):
   `ψ^N = mulShift ψ N`.
4. **mulShift identity** (mathlib's `gaussSum_mulShift`):
   `χ a · gaussSum χ (mulShift ψ a) = gaussSum χ ψ` for unit `a`.

We obtain: `gaussSum χ ψ ^ {ℓ ^ f} = (χ a)⁻¹ · gaussSum χ ψ` in `R'`,
where `a` is the unit cast of `ℓ ^ f` in `R` (the source).

For the K2-1 application: take `R = (𝓞 K)⧸q` (residue field at prime
`q`), `R'` a quotient containing the residue character values mod `P'`
(characteristic `ℓ` = the rational prime under `P'`), `χ = χ_q` the
residue character (order `p` since values lie in `μ_p`), `f` the
residue degree of `P'` (so `NP' = ℓ ^ f`). The hypothesis `NP' ≡ 1
(mod p)` is exactly the "good prime" condition `p ∣ NP' - 1`. -/


/-! ### K2-1 specialised to `residueGaussSum`

Combining the general K2-1 atom `gaussSum_pow_eq_inv_apply_smul_of_charP`
with `residueMulChar_pow_p_eq_one`, we get the K2-1 congruence
specialised to `residueGaussSum`. -/


/-! ### `g^{NP'-1} · χ(a) = 1` form

A useful rearrangement of K2-1: from `χ a · g^N = g`, dividing by `g`
(when applicable) gives `χ a · g^{N-1} = 1`. This is the form most
directly relevant to computing the symbol of `g^p` at `P'`:

```
(g^p)^{(NP'-1)/p} = g^{NP'-1} = (χ(a))⁻¹
```

so the canonical residue exponent of `g^p` at `P'` is the negation of
the residue exponent of `a` at `q`. -/


/-! ### `(g^p)^{(NP'-1)/p}` as a closed form

Since `p ∣ NP' - 1` (i.e. `(ℓ ^ f - 1) ≡ 0 (mod p)`, equivalent to
`ℓ ^ f ≡ 1 (mod p)`), we have `NP' - 1 = p · ((NP'-1)/p)`. Hence
`g^{NP'-1} = (g^p)^{(NP'-1)/p}`. Combined with the K2-1 multiplicative
form, this gives the closed form for the canonical residue exponent
of `g^p` at `P'`:

```
χ a · (g^p)^{(NP'-1)/p} · g = g
```

The factor `(g^p)^{(NP'-1)/p}` is exactly the quantity whose value
modulo `P'` defines the canonical residue exponent of `g^p` at `P'`. -/


/-! ### Closed form modulo `g`-invertibility

When `g = gaussSum χ ψ` is invertible in `R'` (e.g., R' is a field where
g ≠ 0), the closed form `χ a · (g^p)^{(NP'-1)/p} · g = g` rearranges to:

```
(g^p)^{(NP'-1)/p} = (χ a)⁻¹ in R'.
```

The LHS is the quantity whose value modulo `P'` (treating `g^p` as
descended to `𝓞_K`) defines the canonical residue exponent of `g^p` at
`P'`. So the canonical residue symbol value `(g^p / P')_p` equals the
discrete log of `(χ a)⁻¹` in the cyclic group of `p`-th roots of unity. -/


/-! ### Field-specialised K2-1 closed form

When `R'` is a field (or any ring with `NoZeroDivisors`), the
cancellation hypothesis is automatic: `g ≠ 0` lets us cancel `g` from
both sides directly. -/


/-! ### Closed form: `(g^p)^{(NP'-1)/p} = (χ a)⁻¹`

When `χ a` is also a unit in `R'`, the cancellation form
`χ a · (g^p)^{(ℓ ^ f - 1)/p} = 1` rearranges to
`(g^p)^{(ℓ ^ f - 1)/p} = (χ a)⁻¹` directly. This is the cleanest form
for connecting K2-1 to the residue symbol computation. -/


/-! ### Bundle accessor: K2-1 from `StickelbergerSetup`

`StickelbergerSetup p k R'` packages the data driving the Stickelberger
prime factorisation: a finite field `k`, a target domain `R'` of
characteristic `ℓ`, primitive p-th roots of unity in both, and a
primitive additive character. We expose the K2-1 atom as a bundle
accessor `S.gaussSum_pow_eq_inv_apply_smul`. -/


/-! ### Residue field setup: `CharP (𝓞_K ⧸ P') ℓ` for `P'` over `ℓ`

When `P'` is a maximal ideal of `𝓞_K` containing the rational prime `ℓ`,
the residue field `𝓞_K ⧸ P'` has characteristic `ℓ`. -/


/-! ### `phiPrimeGen P`: the Stickelberger generator at prime `P`

For a prime ideal `P` of `𝓞_K`, the Stickelberger ideal equality
`(γ_P) = stickelbergerIdeal P` provides a generator `γ_P ∈ 𝓞_K`.
Classically, this generator is `g(χ_P)^p` (the p-th power of the Gauss
sum), descended from `𝓞_{K(ζ_q)}` to `𝓞_K` via Galois invariance.

We name this `phiPrimeGen` for clarity in the K2-2 chain. The actual
specific value is whatever `StickelbergerIdealEquality.gen` produces;
two different generators differ by a unit, and the symbol identity in
K2-2 holds modulo the unit factor's symbol (which the U-chain handles). -/





/-! ### K2-2c bridge: `residueMulChar` value via `pthSymbolAtPrime_canonical`

For a prime `P` of `𝓞_K`, the residue character `χ_P : MulChar (𝓞_K/P) R'`
(with canonical primitive root `canonicalResidueZetaP P`) and target
primitive root `zeta_R` in `R'`, satisfies:

```
χ_P(α mod P) = zeta_R ^ (pthSymbolAtPrime_canonical α P).val
```

for `α ∈ 𝓞_K` outside `P`, `P` maximal, `p ∤ #(𝓞_K/P) - 1`, `(p : 𝓞_K) ∉ P`.

This is K2-2 step (c): identifies the residue character value at α with
`zeta_R` raised to the canonical residue exponent. -/


/-! ### Discrete log uniqueness for `finiteFieldExponent`

`finiteFieldExponent` is the discrete log of `finiteFieldUnit hdiv x` in
the cyclic subgroup generated by `zeta`. Uniqueness mod `p` follows from
`zeta` being a primitive `p`-th root.

Specifically: if `zeta^e.val = finiteFieldUnit hdiv x` in `kˣ`, then
`e = finiteFieldExponent zeta hzeta hdiv x`. -/


/-! ### K2-2 conditional reduction (status)

The full K2-2 theorem combines the foundational atoms above:
* **K2-2a** (`pthSymbolAtPrime_canonical_eq_primeExponent`, existing): unfolds
  `pthSymbolAtPrime_canonical α P'` to `primeExponent P' (canonicalResidueZetaP P')
  ... α hα`, which is `finiteFieldExponent` applied to the unit form of `α`.
* **K2-1** (this file): `χ a · (g^p)^{(NP'-1)/p} = 1` in target ring of char ℓ.
* **K2-2c** (this file, `residueMulChar_apply_quotient_canonical_eq_pow_pthSymbol`):
  `residueMulChar (NP' mod P) at canonicalResidueZetaP P' = (canonicalResidueZetaP P')
  ^ (pthSymbolAtPrime_canonical NP' P).val`.
* **Discrete log uniqueness** (this file, `finiteFieldExponent_eq_of_pow_eq`): if
  `zeta ^ e.val = finiteFieldUnit hdiv x`, then `e = finiteFieldExponent zeta hzeta hdiv x`.

The substantive open content remaining is the **descent atom**: identifying
`(Ideal.Quotient.mk P') (phiPrimeGen)` with the descent of `g(χ_P)^p` to
`𝓞_K`, viewed as an element of `𝓞_K ⧸ P'`. This is the Galois-invariance
descent of the Gauss sum from `𝓞_{K(ζ_q)}` to `𝓞_K`, then reduction by `P'`.

With that descent in place, the K2-2 chain is:
1. `pthSymbolAtPrime_canonical (phiPrimeGen) P' = primeExponent P' ... = e`
   where `e` is determined by
   `(phiPrimeGen mod P')^{(NP'-1)/p} = ζ_{P'}^{e.val}`.
2. By K2-1 + descent:
   `(phiPrimeGen mod P')^{(NP'-1)/p} = (residueMulChar (NP' mod P))⁻¹`.
3. By K2-2c:
   `(residueMulChar (NP' mod P))⁻¹ =
     (canonicalResidueZetaP P')^{-(pthSymbolAtPrime NP' P).val}`.
4. By discrete log uniqueness: `e = -pthSymbolAtPrime NP' P` in `ZMod p`.

All four ingredients are in place; the final conditional theorem only needs
the descent atom as an explicit hypothesis. -/




end Furtwaengler

end BernoulliRegular

end
