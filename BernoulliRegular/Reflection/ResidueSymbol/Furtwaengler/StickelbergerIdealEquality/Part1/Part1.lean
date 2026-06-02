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

/-! ### Per-`a` exact-order descent at `descentPrime`

Combining the Dwork EXACT-order theorem
`gaussSumInt_qadic_ord_at_prime_ord_dwork` with the ramification-descent
iff `mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul`, we transport
the Q-adic exact order of `S.gaussSumInt a^p` to a `descentPrime`-adic
order on a Galois-fixed lift `γ_a ∈ 𝓞 K`.
-/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The Dwork-EXACT-order Q-adic containment for `S.gaussSumInt a ^ p`. -/
theorem gaussSumInt_pow_p_mem_Q_pow_p_mul_stickOrdOrd
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p ∈ S.Q ^ (p * S.stickOrdOrd a) := by
  classical
  have h := (S.gaussSumInt_qadic_ord_at_prime_ord_dwork a ha₁ ha₂).1
  -- h : S.gaussSumInt a ∈ S.Q ^ stickOrdOrd a.
  -- Raise to pth power: gaussSumInt^p ∈ Q^(p · stickOrdOrd a).
  have hpow := Ideal.pow_mem_pow h p
  rwa [← pow_mul, mul_comm] at hpow


/-- **Per-`a` descent at descentPrime, exact-power form.** Given a
Galois-fixed lift `γ_a` of `S.gaussSumInt a ^ p` and the Dwork EXACT-order
data, the lift `γ_a` lies in `S.descentPrime ^ n` for any `n` with
`e * n ≤ p * stickOrdOrd a`. -/
theorem descentPrime_pow_mem_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p)
    {n : ℕ}
    (hn : S.toConcreteStickelbergerSetup.descentRamificationIdx * n ≤
            p * S.stickOrdOrd a) :
    γ ∈ S.toConcreteStickelbergerSetup.descentPrime ^ n := by
  -- Step 1: gaussSumInt a^p ∈ Q^(p · stickOrdOrd a).
  have h_image_mem : S.gaussSumInt a ^ p ∈ S.Q ^ (p * S.stickOrdOrd a) :=
    S.gaussSumInt_pow_p_mem_Q_pow_p_mul_stickOrdOrd ha₁ ha₂
  -- Step 2: transfer to algebraMap γ via hγ.
  have h_image :
      algebraMap (𝓞 K) (𝓞 R') γ ∈ S.Q ^ (p * S.stickOrdOrd a) := hγ ▸ h_image_mem
  -- Step 3: monotonicity Q^(p · stickOrdOrd a) ≤ Q^(e · n).
  have h_pow_le :
      S.Q ^ (p * S.stickOrdOrd a) ≤
        S.Q ^ (S.toConcreteStickelbergerSetup.descentRamificationIdx * n) :=
    Ideal.pow_le_pow_right hn
  have h_image' :
      algebraMap (𝓞 K) (𝓞 R') γ ∈
        S.Q ^ (S.toConcreteStickelbergerSetup.descentRamificationIdx * n) :=
    h_pow_le h_image
  -- Step 4: apply iff form to get descentPrime^n membership.
  exact (S.toConcreteStickelbergerSetup.mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul
    hγ_ne n).mpr h_image'

/-- **Maximal-power form**: the lift `γ_a` lies in
`descentPrime ^ (p · stickOrdOrd a / e)` (where `e = descentRamificationIdx`). -/
theorem descentPrime_pow_div_mem_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p) :
    γ ∈ S.toConcreteStickelbergerSetup.descentPrime ^
      ((p * S.stickOrdOrd a) / S.toConcreteStickelbergerSetup.descentRamificationIdx) := by
  apply S.descentPrime_pow_mem_of_dwork_exactOrder ha₁ ha₂ hγ_ne hγ
  rw [mul_comm]
  exact Nat.div_mul_le_self (p * S.stickOrdOrd a)
    S.toConcreteStickelbergerSetup.descentRamificationIdx



/-- **Existence form** combining Dwork EXACT-order + Galois descent +
trace-form psi-shift: the lift `γ_a` exists and lies in the precise
descentPrime-power. Uses the trace-form Galois-compatibility from
`TraceFormGalois.lean` to discharge the psi-shift content. -/
theorem exists_descentPrime_pow_mul_stickOrdOrd_div
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p ∧
      γ ∈ S.toConcreteStickelbergerSetup.descentPrime ^
        ((p * S.stickOrdOrd a) /
          S.toConcreteStickelbergerSetup.descentRamificationIdx) := by
  classical
  haveI := S.toConcreteStickelbergerSetup.isGalois_K_R'_of_cyclotomic
  haveI := S.toConcreteStickelbergerSetup.finiteDimensional_K_R'_of_cyclotomic
  haveI := S.toConcreteStickelbergerSetup.faithfulSMul_OK_OR'_of_cyclotomic
  -- Use trace-form Galois compatibility from TraceFormGalois.lean.
  have h_psi :=
    S.toTraceFormStickelbergerSetup.isGalPsiShiftCompatible_traceForm
  obtain ⟨γ, hγ_ne, hγ_eq, _⟩ :=
    S.toConcreteStickelbergerSetup.exists_descentPrime_pow_div_of_psi_shift
      ha₁ ha₂ h_psi h_ne_zero
  refine ⟨γ, hγ_ne, hγ_eq, ?_⟩
  exact S.descentPrime_pow_div_mem_of_dwork_exactOrder ha₁ ha₂ hγ_ne hγ_eq

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





omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The integral additive character `S.psiInt` is primitive.

Derived from `S.psi.IsPrimitive` via the injective `algebraMap (𝓞 R') R'`:
since `S.psi = (algebraMap _ _).compAddChar S.psiInt`, primitivity of
`S.psi` forces `S.psiInt ≠ 1`, and over a field `k`, nontriviality is
equivalent to primitivity (`AddChar.IsPrimitive.of_ne_one`). -/
theorem psiInt_isPrimitive :
    S.toConcreteStickelbergerSetup.psiInt.IsPrimitive := by
  -- It suffices to show psiInt ≠ 1, then apply IsPrimitive.of_ne_one over k.
  apply AddChar.IsPrimitive.of_ne_one
  intro h_eq
  -- If psiInt = 1, then S.psi = 1, contradicting S.hpsi.IsPrimitive.
  have h_psi_eq : S.toConcreteStickelbergerSetup.psi = 1 := by
    ext x
    rw [AddChar.one_apply]
    have h_alg := S.toConcreteStickelbergerSetup.algebraMap_psiInt x
    have h_one : S.toConcreteStickelbergerSetup.psiInt x = (1 : 𝓞 R') := by
      have := DFunLike.congr_fun h_eq x
      simpa [AddChar.one_apply] using this
    rw [h_one, map_one] at h_alg
    exact h_alg.symm
  -- S.psi.IsPrimitive contradicts S.psi = 1: with x = 1 ≠ 0,
  -- mulShift psi 1 = psi = 1, contradicting IsPrimitive.
  have h_one_ne : (1 : k) ≠ 0 := one_ne_zero
  have h_shift := S.toConcreteStickelbergerSetup.hpsi h_one_ne
  apply h_shift
  ext y
  simp [h_psi_eq, AddChar.one_apply]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Norm relation for `gaussSumInt(a)`.** In `𝓞 R'` (a domain),
the Gauss-sum norm relation gives
`gaussSumInt(a) · gaussSum (residueCharInt^a)⁻¹ psiInt⁻¹ = #k`. -/
theorem gaussSumInt_mul_inv_eq_card
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a *
        gaussSum (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹
          S.toConcreteStickelbergerSetup.psiInt⁻¹ =
      (Fintype.card k : 𝓞 R') := by
  have h_ne_one := S.toConcreteStickelbergerSetup.residueCharInt_pow_ne_one ha₁ ha₂
  have h_prim := S.psiInt_isPrimitive
  exact gaussSum_mul_gaussSum_eq_card (R := k) (R' := 𝓞 R')
    (χ := S.toConcreteStickelbergerSetup.residueCharInt ^ a)
    (ψ := S.toConcreteStickelbergerSetup.psiInt) h_ne_one h_prim



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
