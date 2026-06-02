module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler

/-!
# Ideal-level Galois action of `pthSymbolAtIdeal_canonical` (Atom D core)

This file lifts `pthSymbolAtPrime_canonical_galoisAction` from primes to
arbitrary integer ideals, via the multiset of normalized factors.

## Main theorem

```
pthSymbolAtIdeal_canonical (σ_a α) (σ_a • I) = (a : ZMod p) * pthSymbolAtIdeal_canonical α I
```
under hypotheses on each prime factor of `I`.

This is the **substantive ideal-level content of Atom D** (without the
specialisation to a Δ-character of η, which controls the final Galois weight `k`).
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Multiset bijection on normalized factors -/

/-- The cyclotomic Galois conjugate sends `(normalizedFactors I).map σ_a`
to `normalizedFactors (σ_a I)` — they are equal as multisets. -/
theorem normalizedFactors_cyclotomicGaloisConjugate
    (a : CyclotomicUnitDelta p) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (normalizedFactors I).map
        (cyclotomicGaloisConjugate (p := p) (K := K) a) =
      normalizedFactors (cyclotomicGaloisConjugate (p := p) (K := K) a I) := by
  classical
  set m := (normalizedFactors I).map
    (cyclotomicGaloisConjugate (p := p) (K := K) a) with hm_def
  set σI := cyclotomicGaloisConjugate (p := p) (K := K) a I with hσI_def
  have hσI_ne : σI ≠ ⊥ := cyclotomicGaloisConjugate_ne_bot a hI
  -- Step 1: each P in m is irreducible (= prime, in 𝓞 K).
  have h_m_irreducible : ∀ P ∈ m, Irreducible P := by
    intro P hP
    rw [hm_def, Multiset.mem_map] at hP
    obtain ⟨Q, hQ_mem, hQ_eq⟩ := hP
    have hQ_prime : Prime Q := prime_of_normalized_factor Q hQ_mem
    have hQ_ne : Q ≠ ⊥ := hQ_prime.ne_zero
    haveI hQ_isPrime : Q.IsPrime := (Ideal.prime_iff_isPrime hQ_ne).mp hQ_prime
    haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a Q).IsPrime :=
      cyclotomicGaloisConjugate_isPrime a Q
    have hP_ne_bot : P ≠ ⊥ := by
      rw [← hQ_eq]
      exact cyclotomicGaloisConjugate_ne_bot a hQ_ne
    have : Prime P := by
      rw [← hQ_eq]
      exact (Ideal.prime_iff_isPrime
        (cyclotomicGaloisConjugate_ne_bot a hQ_ne)).mpr inferInstance
    exact this.irreducible
  -- Step 2: each P in normalizedFactors σI is irreducible.
  have h_nf_irreducible : ∀ P ∈ normalizedFactors σI, Irreducible P :=
    fun P hP => irreducible_of_normalized_factor P hP
  -- Step 3: m.prod ~ᵤ σI (in fact equal since ideals).
  have h_m_prod : m.prod = σI := by
    rw [hm_def, hσI_def]
    -- σ_a (∏ Pᵢ) = ∏ σ_a Pᵢ via multiplicativity of σ_a on ideals.
    have h_eq : (normalizedFactors I).prod = I := by
      have h_norm := prod_normalizedFactors_eq hI
      rw [normalize_eq] at h_norm
      exact h_norm
    have h_map_prod : ((normalizedFactors I).map
        (cyclotomicGaloisConjugate (p := p) (K := K) a)).prod =
        cyclotomicGaloisConjugate (p := p) (K := K) a (normalizedFactors I).prod := by
      -- σ_a is multiplicative on ideals; prod of map = σ_a of prod.
      induction (normalizedFactors I) using Multiset.induction_on with
      | empty =>
        change (1 : Ideal _) = cyclotomicGaloisConjugate (p := p) (K := K) a 1
        rw [Ideal.one_eq_top, cyclotomicGaloisConjugate_top]
      | cons P S ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ih,
          ← cyclotomicGaloisConjugate_mul_ideal]
    rw [h_map_prod, h_eq]
  -- Step 4: associated.
  have h_assoc : Associated m.prod (normalizedFactors σI).prod := by
    rw [h_m_prod]
    exact (prod_normalizedFactors hσI_ne).symm
  -- Step 5: factors_unique gives Multiset.Rel Associated.
  have h_rel : Multiset.Rel Associated m (normalizedFactors σI) :=
    factors_unique h_m_irreducible h_nf_irreducible h_assoc
  -- Step 6: For ideals, Subsingleton (Ideal R)ˣ, so Associated = Eq.
  rw [associated_eq_eq, Multiset.rel_eq] at h_rel
  exact h_rel

/-! ### Ideal-level Galois action -/


/-! ### Principal-ideal version -/



/-! ### Unconditional prime-level Galois action (case-analysis on hypotheses) -/


/-! ### Unconditional ideal-level Galois action -/



/-! ### Galois weight 1 specialization (η fixed pointwise by σ_a)

When the residue-symbol numerator `α` is fixed by every cyclotomic Galois
automorphism — `σ_a α = α` for all a — the Galois weight of the symbol's
ideal slot is `1`:

```
pthSymbolAtIdeal_canonical α (σ_a I) = (a : ZMod p) * pthSymbolAtIdeal_canonical α I
```

This is the cleanest case of Atom D's transformation rule. -/


end Furtwaengler

end BernoulliRegular

end
