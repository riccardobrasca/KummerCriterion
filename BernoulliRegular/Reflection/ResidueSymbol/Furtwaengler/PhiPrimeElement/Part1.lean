module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge

/-!
# Data-carrying prime Φ-elements

The ideal-theoretic predicate `StickelbergerIdealEquality P` only says that
`stickelbergerIdeal P` is principal. Its extracted generator is therefore an
arbitrary generator, determined only up to a unit.

For K2-2 we need the actual Gauss-sum Φ element, not an arbitrary generator of
the same ideal. This file introduces a non-`Prop` object whose `gamma` field is
the element used in the residue-symbol theorem. The current constructor wires
in the existing `phiPrimeGenDescent S a` route from `CrossRingBridge.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-- **Data-carrying prime Φ element**.  The field `gamma` is the actual
element to use in residue-symbol statements. The span equality records that it
also generates the Stickelberger ideal, but the symbol theorem must use
`gamma`, not an arbitrary generator extracted later from the ideal equality. -/
structure PhiPrimeElement
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  (P : Ideal (𝓞 K)) where
  /-- The actual Φ element. -/
  gamma : 𝓞 K
  /-- The actual Φ element generates the Stickelberger ideal. -/
  span_gamma :
    Ideal.span ({gamma} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P

namespace PhiPrimeElement





/-- The actual Φ element is nonzero modulo `P'` as soon as its
Stickelberger ideal is not contained in `P'`. -/
theorem gamma_notMem_of_stickelbergerIdeal_not_le
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_not_le : ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P') :
    ΦP.gamma ∉ P' := fun h_mem =>
  h_not_le (by
    rw [← ΦP.span_gamma]
    exact (Ideal.span_singleton_le_iff_mem (I := P')).mpr h_mem)


/-- If a nonzero prime `P'` contains `stickelbergerIdeal P`, then `P'` lies
over the same rational prime as `P`. -/
theorem under_eq_of_stickelbergerIdeal_le_prime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (h_le : stickelbergerIdeal (p := p) (K := K) P ≤ P') :
    P'.under ℤ = P.under ℤ := by
  classical
  have h_stick_ne : stickelbergerIdeal (p := p) (K := K) P ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    exact stickelbergerIdeal_ne_bot hP_ne
  have hP'_prime : Prime P' := (Ideal.prime_iff_isPrime hP'_ne).mpr inferInstance
  have h_dvd : P' ∣ stickelbergerIdeal (p := p) (K := K) P :=
    Ideal.dvd_iff_le.mpr h_le
  obtain ⟨Q, hQ_mem, hQ_assoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      h_stick_ne hP'_prime.irreducible h_dvd
  have hP'_factor :
      P' ∈ UniqueFactorizationMonoid.normalizedFactors
        (stickelbergerIdeal (p := p) (K := K) P) := by
    rw [associated_iff_eq.mp hQ_assoc]
    exact hQ_mem
  have hP'_conj :
      P' ∈ cyclotomicConjugates (p := p) (K := K) P :=
    normalizedFactors_stickelbergerIdeal_subset hP_ne hP'_factor
  exact mem_cyclotomicConjugates_iff_under_eq.mp hP'_conj


/-- Coprime rational norms force the ideal-support condition needed for the
prime Φ symbol: `P'` cannot contain `stickelbergerIdeal P`. -/
theorem stickelbergerIdeal_not_le_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P' := by
  intro h_le
  have h_under := under_eq_of_stickelbergerIdeal_le_prime hP_ne hP'_ne h_le
  haveI : NeZero P := ⟨by simpa [Ideal.zero_eq_bot] using hP_ne⟩
  have hq_prime : (Ideal.absNorm (P.under ℤ)).Prime :=
    Nat.absNorm_under_prime P
  have hdvd_left :
      Ideal.absNorm (P.under ℤ) ∣ Ideal.absNorm P :=
    Int.absNorm_under_dvd_absNorm P
  have hdvd_right' :
      Ideal.absNorm (P'.under ℤ) ∣ Ideal.absNorm P' :=
    Int.absNorm_under_dvd_absNorm P'
  have hdvd_right :
      Ideal.absNorm (P.under ℤ) ∣ Ideal.absNorm P' := by
    simpa [h_under] using hdvd_right'
  have hdvd_gcd :
      Ideal.absNorm (P.under ℤ) ∣ Nat.gcd (Ideal.absNorm P) (Ideal.absNorm P') :=
    Nat.dvd_gcd hdvd_left hdvd_right
  rw [hcop.gcd_eq_one] at hdvd_gcd
  exact hq_prime.not_dvd_one hdvd_gcd

/-- Coprime rational norms imply the actual Φ element is nonzero modulo `P'`. -/
theorem gamma_notMem_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    ΦP.gamma ∉ P' :=
  gamma_notMem_of_stickelbergerIdeal_not_le ΦP
    (stickelbergerIdeal_not_le_of_absNorm_coprime hP_ne hP'_ne hcop)


/-! ### Unit correction for arbitrary Stickelberger generators -/












/-! ### K2-2 for the actual descended Φ element -/


end PhiPrimeElement
end Furtwaengler

end BernoulliRegular

end
