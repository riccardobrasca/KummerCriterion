module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolNoncanonical
public import BernoulliRegular.FLT37.Primary
public import BernoulliRegular.UnitQuotient.DeltaAction


/-!
# Cyclotomic ideal-action support

This file contains the reusable algebraic infrastructure for cyclotomic
Galois actions on ideals and residue-symbol power identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]

/-! ### Auxiliary algebraic lemmas (engine for c.4) -/




/-! ### Ideal-symbol versions -/





/-! ### Principal-symbol versions

Basic principal-symbol API (`_one`, `_mul_left`, `_mul_right`) appears above.
Here we add the power lemmas used by denominator descent.
-/

















/-! ### c.1.0 — Galois conjugate of an ideal of `𝓞 K`

The cyclotomic Galois group `Gal(K/ℚ)` acts on `𝓞 K` via
`cyclotomicRingOfIntegersEquiv`. This lifts to an action on `Ideal (𝓞 K)`
by the standard `Ideal.map`. For each `a ∈ (ZMod p)ˣ`, the conjugate
`σ_a · q` is itself a prime ideal lying above the same rational prime as
`q`. This sets up the indexing of the Galois orbit of a prime needed to
state the Stickelberger ideal theorem (c.1).
-/

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]












section FrobeniusFiber

open scoped Pointwise



end FrobeniusFiber




/-! ### c.1.1 — Galois orbit of a prime ideal -/






/-! ### c.1.2 (preliminary) — Galois transitivity on primes above `ℓ`

Galois transitivity (Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`)
implies that any two prime ideals of `𝓞 K` lying above the same rational
prime are in the same cyclotomic conjugate class. Combined with
`under_eq_of_mem_cyclotomicConjugates` above, this gives an iff.
-/






/-! ### c.2 (partial) — Galois-equivariance of `pthSymbolAtPrime`

The full Galois-equivariance statement
`pthSymbolAtPrime (σ_a α) (σ_a • q) = pthSymbolAtPrime α q`
is blocked by the `Classical.choose` of a primitive `p`-th root of unity in
each residue field appearing inside `pthSymbolAtPrime`. Two unrelated
choices in `(𝓞K/q)ˣ` and `(𝓞K/(σ_a q))ˣ` would in general give exponents
differing by a unit factor in `(ZMod p)ˣ`.

This section provides the **conditional** Galois-equivariance: assuming
that the chosen primitive `p`-th roots in the two residue fields are
compatible (i.e., the chosen `ζ` for `σ_a • q` is the image of the chosen
`ζ` for `q` under the quotient ring isomorphism induced by `σ_a`), the
symbols agree. -/






end Furtwaengler

end BernoulliRegular
