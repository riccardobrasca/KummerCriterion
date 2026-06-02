module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KellyPrime
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiIdealElement

/-!
# Principal Φ to Stickelberger bridge

This file contains the K2-5/K2-6 bridge in the corrected REF-18 K-chain.

K2-4 gives the norm-symbol identity for the **actual** principal Φ element
`Φ((α))`.  K2-5 identifies the symbol of the explicit Stickelberger
principal generator `α^Θ = stickelbergerPrincipalGen α` with the weighted
Galois sum.  K2-6 is the conditional unit-stripping step:
if the actual Φ element differs from `α^Θ` by a unit whose residue symbols
vanish, then the weighted Galois sum satisfies the norm-symbol identity.

The sign is intentionally the sign currently produced by the formal K2-2
Frobenius chain: the result is a negative-convention norm relation.  A future
orientation lemma, if needed, should translate this convention explicitly.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### K2-5: Stickelberger principal generator as weighted Galois sum -/


/-- **K2-5, prime form.**

At a single nonzero prime `P'`, the ideal-level weighted Galois sum becomes
the expected sum of prime symbols. -/
theorem k2_5_principalGen_symbol_at_prime_eq_weighted_galois_sum
    (α : 𝓞 K) {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P' :=
  pthSymbolAtIdeal_canonical_principalGen_at_prime_eq_galois_sum α hP'_ne
    h_coprime

/-! ### K2-6: conditional unit stripping -/

/-- Negative-convention form of the Stickelberger norm relation.

This matches the current formal K2-2/K2-4 orientation.  It is deliberately
separate from the older positive-convention `StickelbergerNormRelation`. -/
def StickelbergerNormRelationNeg (α : 𝓞 K) (P' : Ideal (𝓞 K)) : Prop :=
  (∑ a : CyclotomicUnitDelta p,
      ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
    -pthSymbolAtIdeal_canonical (p := p) (K := K)
      ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))

/-- **K2-6, unit stripping for the principal generator, right-unit form.**

If the actual principal Φ element satisfies `Φ((α)) = α^Θ * u` and the
unit-symbol contribution of `u` vanishes at every prime, then K2-4 transfers
from `Φ((α))` to `α^Θ`. -/
theorem k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_mul_unit
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = stickelbergerPrincipalGen (p := p) (K := K) α * u) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  have h_phi :=
    PhiPrimeElement.PhiIdealElement.principal_symbol_eq_neg_norm_principal_of_absNorm_coprime
      (p := p) (K := K) Φα hB hcop h_prime
  rw [hΦ] at h_phi
  rw [pthSymbolAtIdeal_canonical_mul_unit_α_eq_self
    (p := p) (K := K)
    (stickelbergerPrincipalGen (p := p) (K := K) α) hu hu_zero B] at h_phi
  exact h_phi

/-- **K2-6, unit stripping for the principal generator, left-unit form.**

This is the form usually produced by the principal unit-factor theorem:
`Φ((α)) = u * α^Θ`. -/
theorem k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_unit_mul
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  refine k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_mul_unit
    (p := p) (K := K) Φα hB hcop h_prime hu hu_zero ?_
  rw [hΦ, mul_comm]




/-- **K2-6, prime weighted Galois-sum form, left-unit version.** -/
theorem k2_6_weighted_galois_sum_at_prime_eq_neg_norm_principal_of_eq_unit_mul
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((P'.absNorm : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_at_prime_eq_weighted_galois_sum
    (p := p) (K := K) α hP'_ne h_coprime]
  exact k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_unit_mul
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ

/-- **K2-6 packaged as a prime negative-convention norm relation.** -/
theorem StickelbergerNormRelationNeg_of_phi_unit_factor
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    StickelbergerNormRelationNeg (p := p) (K := K) α P' := by
  unfold StickelbergerNormRelationNeg
  exact k2_6_weighted_galois_sum_at_prime_eq_neg_norm_principal_of_eq_unit_mul
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ h_coprime

/-! ### Positive-orientation K2-6 for reciprocal Φ data -/









/-! ### Terminal signed K-chain endpoint -/






/-! ### Signed Kelly is enough for singular numerators -/






end Furtwaengler

end BernoulliRegular

end
