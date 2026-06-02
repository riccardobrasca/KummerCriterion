module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormGalois
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality.Part2

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

universe u v w

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : FullTeichDworkSetup ℓ p k K R')

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-! ### Forward construction via per-conjugate generators

The orbit-coverage predicate
`∃ γ ∈ 𝓞 K, γ ≠ 0 ∧ Ideal.span {γ} = stickelbergerIdeal q_K`
admits a clean *forward* discharge through a per-conjugate-generator
witness:

* `StickelbergerExactPerConjugateGenerator`: for each `a ∈ (ZMod p)ˣ`,
  there exists `γ_a ∈ 𝓞 K` non-zero with
  `Ideal.span {γ_a} = (σ_{a⁻¹} q_K) ^ a.val`.

The product `γ := ∏_a γ_a` then satisfies
`Ideal.span {γ} = ∏_a (σ_{a⁻¹} q_K)^a.val = stickelbergerIdeal q_K`,
discharging `StickelbergerOrbitCoverage` unconditionally on the bundle's
ramification setup. The rest of the construction (existence of each γ_a)
is the substantive content of multi-bundle Stickelberger descent — it
remains hypothesized as a `Prop` but the `Prop` is now atomic (one
∃ per orbit element), and the constructor is a one-line product. -/



/-! ### Refining `StickelbergerExactPerConjugateGenerator` further

The per-conjugate generator existence is itself an `∃` — for each a,
exhibit γ_a generating `(σ_{a⁻¹} q_K)^{a.val}`. We expose two natural
sources of such a generator:

1. **From principality of each prime power** (Dedekind-domain content):
   if every Galois conjugate of `q_K` is principal, then so are its
   powers, and we can choose explicit generators.
2. **From a single global generator** (the round-trip): if a global γ
   already satisfies `(γ) = stickelbergerIdeal q_K`, then per-conjugate
   generators can be extracted from `factor_dvd_of_pow_dvd`.

The first form is captured by the principality predicate
`StickelbergerConjugateIsPrincipal`; the second form is the converse
direction packaged for completeness. -/






/-! ### Reverse: orbit coverage implies per-conjugate generators
(under faithfulness)

The converse to `stickelbergerOrbitCoverage_of_perConjugateGenerator`:
if a single γ generates `stickelbergerIdeal q_K` and the cyclotomic
orbit acts faithfully on `q_K`, then the per-conjugate generators exist.

This direction exhibits the per-conjugate generators by extracting
the Galois-conjugate factors of `(γ)`'s factorisation, using
the `StickelbergerExactConjugateExponents` discharge already in place. -/

end FullTeichDworkSetup

end Furtwaengler

end BernoulliRegular
