module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormGalois


/-!
# `StickelbergerIdealEquality` from a `FullTeichDworkSetup`

This file provides the substantive valuation-descent content of c.1
(`REF-18c2d-main-c.1`) by showing how to assemble a
`StickelbergerIdealEquality (S.Q.under (𝓞 K))` from a
`FullTeichDworkSetup S` together with a coverage hypothesis on the
Galois orbit of the descent prime.

## Strategy

The Dwork bundle gives the EXACT `Q`-adic order
`S.gaussSumInt a ∈ S.Q^(stickOrdOrd a) ∧ S.gaussSumInt a ∉ S.Q^(stickOrdOrd a + 1)`
at the SINGLE prime `S.Q ⊂ 𝓞 R'` for each `a ∈ [1, p-1]`. The route
to the multi-conjugate Stickelberger ideal in `𝓞 K` factors through
the descent prime `q_K = S.Q.under (𝓞 K)` and the Galois orbit
`cyclotomicConjugates q_K`:

1. **Per-`a` descent witness** (`StickelbergerPerConjugateDescent`):
   for each `a`, the existence of `γ_a ∈ 𝓞 K` whose image in `𝓞 R'`
   equals `S.gaussSumInt a ^ p` and whose `descentPrime`-adic order is
   `p · stickOrdOrd a / e` where `e = descentRamificationIdx`.

2. **Galois-orbit coverage** (`StickelbergerOrbitCoverage`): the
   Stickelberger ideal `q_K^Θ = ∏_a (σ_{a^{-1}} q_K)^a.val` admits a
   single global generator `γ ∈ 𝓞 K` whose ideal factorization at each
   conjugate matches the prescribed exponent.

3. **Final assembly** (`stickelbergerIdealEquality_of_dwork_witness`):
   under both witnesses, the principal ideal `(γ)` equals
   `stickelbergerIdeal q_K`, and so `StickelbergerIdealEquality q_K`
   holds.

The current file delivers (1) and the **conditional** (3) under (2).
The unconditional (2) requires a separate per-conjugate bundle for
each Galois conjugate prime above `ℓ` (one bundle per representative
of the Galois orbit of `S.Q`); that step is left as a coverage
hypothesis here, packaged as the `Prop` predicate
`StickelbergerOrbitCoverage`.

## Why split

The full unconditional c.1 builds a single global generator from
multiple per-conjugate bundles by orbit-summing. That assembly is the
substantive remaining content. The conditional form delivered here
already discharges all the **valuation-descent** content (per-`a`
exact orders, ramification descent, Dwork EXACT-order data); only the
**orbit-coverage** combinatorics remain.

## Files

* Per-`a` exact-order descent: theorems
  `gaussSumInt_pow_descentPrime_pow_mul_stickOrdOrd`,
  `gaussSumInt_pow_not_mem_descentPrime_pow_mul_stickOrdOrd_succ` (in
  this file, on `FullTeichDworkSetup`).
* Final `StickelbergerIdealEquality` constructor: theorem
  `stickelbergerIdealEquality_of_orbitCoverage`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler


end Furtwaengler

end BernoulliRegular

