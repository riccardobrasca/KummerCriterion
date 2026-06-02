module

public import BernoulliRegular.FLT37.Primary
public import BernoulliRegular.UnitQuotient.DeltaAction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler.Part1


/-!
# Stickelberger support and cyclotomic ideal orbits

This file continues the basic cyclotomic ideal-action API with Stickelberger
support bookkeeping. It contains support and orbit identities only.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]




/-! ### c.2 — UNCONDITIONAL Galois-action transformation (existence form)

The conditional `pthSymbolAtPrime_galoisAction_of_compat` requires a
specific compatibility between the `Classical.choose` primitive `p`-th
roots in `(𝓞K/q)ˣ` and `(𝓞K/(σq))ˣ`. Mathematically, two primitive
`p`-th roots in `kˣ` differ by a unit power, and the exponent form of
the residue symbol then transforms by a multiplicative factor in `ZMod p`.

The unconditional content of c.2 is captured here as an existence
statement: there exists a unit `c : (ZMod p)ˣ` (depending on `q, a`,
and the global `Classical.choose` values, but **independent of `α`**)
such that

```
pthSymbolAtPrime (σ_a α) (σ_a • q) = c.val * pthSymbolAtPrime α q
```

for all `α`. The conditional theorem is the special case `c = 1`. -/


/-! ### Stickelberger-element action on a prime ideal

The classical Stickelberger element
`Θ = ∑_{a ∈ (ZMod p)ˣ} (a.val) · σ_a⁻¹`
acts on prime ideals of `𝓞 K` formally: applied to a chosen prime
`q_K`, it yields the product
`∏_{a ∈ (ZMod p)ˣ} (σ_a⁻¹ · q_K) ^ (a.val)`.

This is the RHS of c.1's theorem
`(g(χ_q)^p) · 𝓞_K = q_K^Θ`. The actual ideal-equality proof is c.1.3 + c.1.4.
-/


-- (`stickelbergerIdeal_le_prod_conjugates` has been deferred; the
-- support theorem `residueGaussSum_pow_p_support_in_cyclotomicConjugates`
-- below provides the same content via `residueGaussSum_pow_p_descent_to_OK`.)






/-! ### Connection to Mathlib's `primesOver`

The cyclotomic Galois orbit of a prime `q` of `𝓞 K` (above a rational
prime `ℓ ≠ p`) coincides with Mathlib's `primesOver (q.under ℤ) (𝓞 K)`,
the Set of all prime ideals of `𝓞 K` lying over `q.under ℤ`. -/


omit [NumberField K] in










/-! ### `StickelbergerIdealEquality` data

The full Stickelberger ideal equality `(g(χ_q)^p) · 𝓞_K = stickelbergerIdeal q_K`
for q above ℓ ≠ p is the substantive content of c.1. It records a generator
γ ∈ 𝓞_K (essentially `g(χ_q)^p` after descent) together with the ideal
factorization. -/






end Furtwaengler

end BernoulliRegular
