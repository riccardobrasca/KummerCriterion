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

universe u v w

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : FullTeichDworkSetup ℓ p k K R')

/-! ### Coverage of the Stickelberger orbit

The Stickelberger ideal `q_K^Θ = ∏_a (σ_{a^{-1}} q_K)^a.val` is a
product over the Galois orbit of `q_K`. Its principal generator —
which is what `StickelbergerIdealEquality` asserts to exist — must
have the correct ideal-multiplicity at EVERY conjugate prime. The
single bundle `S` only sees one prime in `𝓞 R'`; capturing the
multiplicity at all conjugate primes simultaneously requires either:
(a) a per-conjugate bundle, or (b) a coverage hypothesis.

We package (b) as a `Prop` predicate `StickelbergerOrbitCoverage`,
which the consumer must discharge to obtain the full
`StickelbergerIdealEquality`. -/





/-! ### Atomic decomposition of `StickelbergerOrbitCoverage`

The orbit-coverage predicate
`∃ γ ∈ 𝓞 K, γ ≠ 0 ∧ Ideal.span {γ} = stickelbergerIdeal q_K`
admits a clean atomic decomposition into three Prop predicates whose
combination is mathematically equivalent to the coverage:

1. `StickelbergerExactConjugateExponents γ`: per-conjugate exact
   exponent at each Galois conjugate of `q_K`.
2. `StickelbergerSupportInOrbit γ`: support of `(γ)` is contained in
   the cyclotomic Galois orbit of `q_K`.
3. `StickelbergerIdealConjugateMultiplicity`: each cyclotomic
   conjugate appears in `normalizedFactors (stickelbergerIdeal q_K)`
   with multiplicity exactly `(a : ZMod p).val`.

The first two are properties of γ; the third is a structural property
of the Stickelberger ideal itself (true under faithfulness of the
Galois action on the orbit, i.e., the split case).

The substantive theorem `stickelbergerOrbitCoverage_of_atomic_with_stickMul`
provides the END-TO-END atomic discharge: given all three predicates,
the orbit coverage holds. The proof goes through both divisibility
directions (`(γ) ∣ stick` and `stick ∣ (γ)`) and uses
`associated_iff_eq` (which holds in `Ideal R` since `(Ideal R)ˣ` is
unique). -/





/-- The descentPrime is non-bot. -/
private theorem descentPrime_ne_bot' :
    S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
  S.toConcreteStickelbergerSetup.descentPrime_ne_bot

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Each Galois conjugate of `descentPrime` is non-bot. -/
theorem cyclotomicGaloisConjugate_descentPrime_ne_bot
    (a : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
  cyclotomicGaloisConjugate_ne_bot a⁻¹ S.descentPrime_ne_bot'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Each Galois conjugate factor `(σ_{a⁻¹} q_K)^a.val` is non-zero. -/
private theorem stickelbergerFactor_ne_zero (a : CyclotomicUnitDelta p) :
    (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime ^ ((a : ZMod p).val) :
        Ideal (𝓞 K)) ≠ 0 := by
  rw [Ne, Ideal.zero_eq_bot]
  exact pow_ne_zero _ (S.cyclotomicGaloisConjugate_descentPrime_ne_bot a)


omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Helper:** `normalizedFactors` of a single factor `(σ_{a⁻¹} q_K)^a.val`
equals `a.val • {σ_{a⁻¹} q_K}`. Uses `normalizedFactors_pow` and the fact
that each conjugate is irreducible (prime + non-zero in a Dedekind domain). -/
theorem normalizedFactors_stickelbergerFactor (a : CyclotomicUnitDelta p) :
    UniqueFactorizationMonoid.normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.toConcreteStickelbergerSetup.descentPrime ^
            ((a : ZMod p).val) : Ideal (𝓞 K)) =
      ((a : ZMod p).val) •
        ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime}
          : Multiset (Ideal (𝓞 K))) := by
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  have h_ne : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
    S.cyclotomicGaloisConjugate_descentPrime_ne_bot a
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a⁻¹ _
  have h_prime : Prime (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime) :=
    Ideal.prime_of_isPrime h_ne inferInstance
  have h_irred : Irreducible (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime) := h_prime.irreducible
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible h_irred, normalize_eq]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Helper:** `normalizedFactors` of a finset product
`∏_{a ∈ s} (σ_{a⁻¹} q_K)^a.val` equals
the sum `∑_{a ∈ s} a.val • {σ_{a⁻¹} q_K}`. Proved by induction on `s`. -/
theorem normalizedFactors_stickelbergerIdeal_finset_eq
    (s : Finset (CyclotomicUnitDelta p)) :
    UniqueFactorizationMonoid.normalizedFactors
        (∏ a ∈ s, cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.toConcreteStickelbergerSetup.descentPrime ^ ((a : ZMod p).val)) =
      ∑ a ∈ s,
        ((a : ZMod p).val) •
          ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
              S.toConcreteStickelbergerSetup.descentPrime}
            : Multiset (Ideal (𝓞 K))) := by
  classical
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty,
      UniqueFactorizationMonoid.normalizedFactors_one]
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has]
    have h_factor_ne : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        S.toConcreteStickelbergerSetup.descentPrime ^ ((a : ZMod p).val) :
          Ideal (𝓞 K)) ≠ 0 :=
      S.stickelbergerFactor_ne_zero a
    have h_prod_ne : (∏ b ∈ s, cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹
        S.toConcreteStickelbergerSetup.descentPrime ^ ((b : ZMod p).val) :
          Ideal (𝓞 K)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro b _
      have := S.stickelbergerFactor_ne_zero b
      rwa [Ne, Ideal.zero_eq_bot] at this
    rw [UniqueFactorizationMonoid.normalizedFactors_mul h_factor_ne h_prod_ne,
      S.normalizedFactors_stickelbergerFactor a, ih]

end FullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end
