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

/-- The ideal `q_K^Θ` where `Θ` is the Stickelberger element. By
definition: the product over `a ∈ (ZMod p)ˣ` of `(σ_a⁻¹ · q_K)^a.val`. -/
noncomputable def stickelbergerIdeal (q_K : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ∏ a : CyclotomicUnitDelta p,
    cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
      ((a : ZMod p).val)

-- (`stickelbergerIdeal_le_prod_conjugates` has been deferred; the
-- support theorem `residueGaussSum_pow_p_support_in_cyclotomicConjugates`
-- below provides the same content via `residueGaussSum_pow_p_descent_to_OK`.)

/-- The Stickelberger ideal is non-bot when `q_K` is non-bot. -/
theorem stickelbergerIdeal_ne_bot
    {q_K : Ideal (𝓞 K)} (hq : q_K ≠ ⊥) :
    stickelbergerIdeal (p := p) (K := K) q_K ≠ ⊥ := by
  classical
  unfold stickelbergerIdeal
  rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
  push Not
  intro a _
  rw [Ideal.zero_eq_bot]
  -- Goal: (σ_{a⁻¹} q_K)^(a.val) ≠ ⊥
  exact pow_ne_zero _
    (by simpa [Ideal.zero_eq_bot] using cyclotomicGaloisConjugate_ne_bot a⁻¹ hq)


/-- Each Stickelberger factor `(σ_{a⁻¹} q_K)^(a.val)` divides the product. -/
theorem stickelbergerIdeal_le_factor
    (q_K : Ideal (𝓞 K)) (a : CyclotomicUnitDelta p) :
    stickelbergerIdeal (p := p) (K := K) q_K ≤
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
        ((a : ZMod p).val) := by
  classical
  unfold stickelbergerIdeal
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (CyclotomicUnitDelta p))
        (fun a => cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
            ((a : ZMod p).val)) (Finset.mem_univ a)]
  exact Ideal.mul_le_left



/-! ### Connection to Mathlib's `primesOver`

The cyclotomic Galois orbit of a prime `q` of `𝓞 K` (above a rational
prime `ℓ ≠ p`) coincides with Mathlib's `primesOver (q.under ℤ) (𝓞 K)`,
the Set of all prime ideals of `𝓞 K` lying over `q.under ℤ`. -/

/-- The cyclotomic Galois orbit equals the set of primes over `q.under ℤ`
(as a Set). -/
theorem coe_cyclotomicConjugates {q : Ideal (𝓞 K)} [q.IsPrime] :
    (cyclotomicConjugates (p := p) (K := K) q : Set (Ideal (𝓞 K))) =
      Ideal.primesOver (q.under ℤ) (𝓞 K) := by
  ext I
  refine ⟨?_, ?_⟩
  · intro hI
    rw [Finset.mem_coe] at hI
    haveI : I.IsPrime := isPrime_of_mem_cyclotomicConjugates hI
    exact ⟨inferInstance,
      ⟨(under_eq_of_mem_cyclotomicConjugates hI).symm⟩⟩
  · rintro ⟨hI_prime, hI_lies⟩
    haveI : I.IsPrime := hI_prime
    have h_under : I.under ℤ = q.under ℤ := hI_lies.over.symm
    rw [Finset.mem_coe]
    exact mem_cyclotomicConjugates_iff_under_eq.mpr h_under

omit [NumberField K] in
/-- Pulling back a non-bot prime ideal of `𝓞 K` to `ℤ` is non-bot. -/
theorem under_ne_bot {q : Ideal (𝓞 K)} (hq : q ≠ ⊥) : q.under ℤ ≠ ⊥ :=
  Ideal.IsIntegralClosure.comap_ne_bot (R := ℤ) (A := 𝓞 K) (S := K) hq



/-- **Galois fundamental identity** for the cyclotomic conjugate orbit:
`#orbit · ramification · inertia = p - 1`.
Specialised from Mathlib's
`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` plus
`natCard_galGroup_eq`. -/
theorem cyclotomicConjugates_card_mul_ramificationIdxIn_mul_inertiaDegIn
    {q : Ideal (𝓞 K)} [q.IsPrime] (hq_ne : q ≠ ⊥) :
    (cyclotomicConjugates (p := p) (K := K) q).card *
      ((q.under ℤ).ramificationIdxIn (𝓞 K) *
        (q.under ℤ).inertiaDegIn (𝓞 K)) = p - 1 := by
  have hu_ne : q.under ℤ ≠ ⊥ := under_ne_bot hq_ne
  haveI : (q.under ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hu_ne
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := ({p} : Set ℕ)) ℚ K
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional ({p} : Set ℕ) ℚ K
  have hfid := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (A := ℤ) (B := 𝓞 K) (G := Gal(K/ℚ)) hu_ne
  have hcard : (Ideal.primesOver (q.under ℤ) (𝓞 K)).ncard =
      (cyclotomicConjugates (p := p) (K := K) q).card := by
    rw [← coe_cyclotomicConjugates (p := p) (K := K) (q := q),
        Set.ncard_coe_finset]
  rw [hcard] at hfid
  -- Inline `Nat.card Gal(K/ℚ) = p - 1` proof to avoid typeclass-synth fragility.
  have hcard_gal : Nat.card Gal(K/ℚ) = p - 1 := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have e : Gal(K/ℚ) ≃ CyclotomicUnitDelta p :=
      (cyclotomicGalEquivZMod (p := p) K).toEquiv
    rw [Nat.card_congr e]
    change Nat.card ((ZMod p)ˣ) = p - 1
    rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  rw [hcard_gal] at hfid
  exact hfid

/-- **Split case** (ℓ ≡ 1 mod p): if both ramification and inertia degrees are 1,
the orbit has cardinality `p - 1` (full splitting in `𝓞 K`). -/
theorem cyclotomicConjugates_card_eq_p_sub_one_of_split
    {q : Ideal (𝓞 K)} [q.IsPrime] (hq_ne : q ≠ ⊥)
    (he : (q.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf : (q.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    (cyclotomicConjugates (p := p) (K := K) q).card = p - 1 := by
  have h :
      (cyclotomicConjugates (p := p) (K := K) q).card *
        ((q.under ℤ).ramificationIdxIn (𝓞 K) *
          (q.under ℤ).inertiaDegIn (𝓞 K)) = p - 1 :=
    cyclotomicConjugates_card_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := p) (K := K) (q := q) hq_ne
  rw [he, hf, mul_one, mul_one] at h
  exact h





/-- Every prime factor of `stickelbergerIdeal q_K` is in `cyclotomicConjugates q_K`.
By construction, the Stickelberger ideal is a product of powers of cyclotomic
conjugates of `q_K`. -/
theorem normalizedFactors_stickelbergerIdeal_subset
    {q_K : Ideal (𝓞 K)} [q_K.IsPrime] (hq_ne : q_K ≠ ⊥)
    {b : Ideal (𝓞 K)}
    (hb : b ∈ UniqueFactorizationMonoid.normalizedFactors
            (stickelbergerIdeal (p := p) (K := K) q_K)) :
    b ∈ cyclotomicConjugates (p := p) (K := K) q_K := by
  haveI : (cyclotomicConjugates (p := p) (K := K) q_K).Nonempty :=
    ⟨q_K, (mem_cyclotomicConjugates_iff (p := p) (K := K) q_K q_K).2
      ⟨1, by simp⟩⟩
  -- b is prime in 𝓞 K and divides stickelbergerIdeal q_K.
  -- stickelbergerIdeal q_K is a product of powers of σ-conjugates of q_K.
  -- By IsPrime.prod_le, b ⊇ some factor, hence b = some σ-conjugate.
  haveI hb_prime : Prime b :=
    UniqueFactorizationMonoid.prime_of_normalized_factor b hb
  haveI hb_isPrime : b.IsPrime := Ideal.isPrime_of_prime hb_prime
  have hb_ne : b ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact hb_prime.ne_zero
  -- b ∣ stickelbergerIdeal
  have hb_dvd : b ∣ stickelbergerIdeal (p := p) (K := K) q_K :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb
  -- stickelbergerIdeal := ∏ a, (σ_{a⁻¹} q_K)^(a.val).
  -- b ⊇ product (as `b | product`), b prime ⟹ b ⊇ some factor (as `b | factor`).
  -- Note: in Dedekind domains, `I ∣ J ↔ J ≤ I` (i.e., `I` divides `J` iff `J ⊆ I`).
  have hstick_le_b : stickelbergerIdeal (p := p) (K := K) q_K ≤ b :=
    Ideal.le_of_dvd hb_dvd
  unfold stickelbergerIdeal at hstick_le_b
  have ⟨a, _, ha⟩ :=
    (Ideal.IsPrime.prod_le (s := Finset.univ)
      (f := fun a => cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
              ((a : ZMod p).val))
      (hp := hb_isPrime)).mp hstick_le_b
  -- ha : (σ_{a⁻¹} q_K)^(a.val) ≤ b. b is prime. So the conjugate ≤ b.
  have h_aval : 0 < (a : ZMod p).val := ZMod.val_pos.mpr a.isUnit.ne_zero
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a⁻¹ q_K
  have hb_le' : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ≤ b :=
    @Ideal.IsPrime.le_of_pow_le _ _
      (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K)
      b hb_isPrime ((a : ZMod p).val) ha
  -- Both b and the conjugate are non-bot prime ideals in 𝓞 K (a Dedekind domain),
  -- hence maximal. b ≤ maximal ⟹ b = the maximal one.
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K) ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a⁻¹ hq_ne
  haveI : b.IsMaximal := Ideal.IsPrime.isMaximal hb_isPrime hb_ne
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance ‹_ ≠ ⊥›
  -- conj ≤ b, conj maximal, b ≠ ⊤ ⟹ conj = b.
  have hb_eq : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K = b :=
    Ideal.IsMaximal.eq_of_le ‹(cyclotomicGaloisConjugate _ _).IsMaximal›
      (Ideal.IsMaximal.ne_top ‹b.IsMaximal›) hb_le'
  rw [← hb_eq]
  exact (mem_cyclotomicConjugates_iff (p := p) (K := K) q_K _).mpr ⟨a⁻¹, rfl⟩

/-! ### `StickelbergerIdealEquality` data

The full Stickelberger ideal equality `(g(χ_q)^p) · 𝓞_K = stickelbergerIdeal q_K`
for q above ℓ ≠ p is the substantive content of c.1. It records a generator
γ ∈ 𝓞_K (essentially `g(χ_q)^p` after descent) together with the ideal
factorization. -/

/-- The Stickelberger ideal equality for a specific prime `q_K`. -/
def StickelbergerIdealEquality (q_K : Ideal (𝓞 K)) : Prop :=
  ∃ γ : 𝓞 K, γ ≠ 0 ∧
    Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) q_K





end Furtwaengler

end BernoulliRegular
