module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part3

/-!
# Cross-ring bridge: 𝓞 K / P' inside 𝓞 R' / 𝔭

For a prime ideal `P'` of `𝓞 K` and a prime `𝔭` of `𝓞 R'` lying over `P'`
(in a finite extension `R' / K`), the residue field `𝓞 R' / 𝔭` extends
the residue field `𝓞 K / P'`. This file builds the bridge:

* Existence of `𝔭` over a maximal `P'` (via going-up).
* Canonical injection `𝓞 K / P' → 𝓞 R' / 𝔭`.
* Compatible CharP transfer.

This is the first cross-ring atomic step toward K2-2 path (a):
applying the K2-1 atom in `𝓞 R' / 𝔭` (where `gaussSumInt` lives via
`algebraMap 𝓞 K 𝓞 R'`) and pulling back to `𝓞 K / P'`.

Per AI reviewer 2026-05-05 K2-2 plan: the descent atom requires this
bridge to apply K2-1 in the right ambient ring. Multi-week scope per
the plan; this file is the first chunk.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Existence of a prime above `P'` in an integral extension -/

/-- **h_χ_eval_pow at unit_a from character identification**: when the
character identification holds and `unit_a` represents some `α : 𝓞 K`
with `α ∉ P` via `(unit_a : 𝓞 K / P) = Quotient.mk P α`, the K2-2c form
holds at `unit_a`. -/
theorem chi_pow_apply_unit_eq_pow_pthSymbol
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [CommRing R']
    {R'' : Type*} [CommRing R'']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R'')
    {a : ℕ} (ha : a ≠ 0)
    (χ : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      MulChar (𝓞 K ⧸ P) R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      χ = residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
        hdiv zeta_R hzeta_R)
    {α : 𝓞 K} (hα : α ∉ P)
    (unit_a :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (𝓞 K ⧸ P)ˣ)
    (h_unit_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (unit_a : 𝓞 K ⧸ P) = (Ideal.Quotient.mk P α : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((χ ^ a).ringHomComp σ) ((unit_a : 𝓞 K ⧸ P)) =
      σ (zeta_R : R') ^
        (a * (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) α P).val) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [h_unit_eq]
  exact chi_pow_apply_quotient_eq_pow_pthSymbol hP_bot hp_in_P hdiv zeta_R hzeta_R σ ha hα
    χ h_residue_char_eq

/-- **Natural-number cast through Ideal.Quotient.mk**: for `n : ℕ`, the
ring cast `(n : 𝓞 K ⧸ P)` equals `Ideal.Quotient.mk P (n : 𝓞 K)`. This
is `map_natCast` for the quotient ring hom. -/
theorem natCast_quotient_eq_mk
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (n : ℕ) :
    ((n : 𝓞 K ⧸ P) : 𝓞 K ⧸ P) = (Ideal.Quotient.mk P) ((n : 𝓞 K)) :=
  (map_natCast (Ideal.Quotient.mk P) n).symm


/-! ### Constructing unit_a from natCast non-membership

When a natural number `n` is not in `P` (in `𝓞 K`), its image in `𝓞 K / P`
is a unit. We package this as a constructor. -/

/-- **unit_a from natCast**: given `(n : 𝓞 K) ∉ P`, the residue
`(n : 𝓞 K / P)` is a unit. -/
noncomputable def unitOfNatCast_notMem
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 K) ∉ P) : (𝓞 K ⧸ P)ˣ :=
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem P
    (((n : ℕ) : 𝓞 K)) hn

/-- **`unitOfNatCast_notMem` value coercion**. -/
@[simp] theorem unitOfNatCast_notMem_val
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 K) ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((unitOfNatCast_notMem n hn) : 𝓞 K ⧸ P) =
      Ideal.Quotient.mk P (((n : ℕ) : 𝓞 K)) := rfl

/-- **`unitOfNatCast_notMem` natCast form**: equals the natCast
`(n : 𝓞 K / P)` directly. -/
theorem unitOfNatCast_notMem_eq_natCast
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 K) ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((unitOfNatCast_notMem n hn) : 𝓞 K ⧸ P) =
      ((n : ℕ) : 𝓞 K ⧸ P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [unitOfNatCast_notMem_val, ← natCast_quotient_eq_mk]

/-! ### Specialized K-chain at index a = 1

For index `a = 1` (the "primary" descent index), the K-chain conclusion
simplifies to `pthSymbol (phiPrimeGenDescent S 1) P' = -pthSymbol NP' P`,
matching the form of `K2_2_of_descent_pow_eq` from PhiPrimeSymbol.lean. -/


/-! ### Convenience: `1 ≤ p - 1` from `p.Prime`

For prime `p ≥ 2`, we have `p - 1 ≥ 1`. This packages the calculation. -/

/-! ### K-chain output transferred under unit factor

If two elements `γ₁ γ₂ ∈ 𝓞 K` differ by a unit `u : (𝓞 K)ˣ` (i.e., γ₁ = u · γ₂),
and the unit's pthSymbol at `P'` is `0`, then their pthSymbols at `P'`
agree. -/


/-! ### Span equality implies unit factor

In an integral domain, two elements with equal principal ideals
differ by a unit. -/

/-- **Same-span implies unit factor**: if `Ideal.span {γ₁} = Ideal.span {γ₂}`
in `𝓞 K` (with γ₂ ≠ 0), then `γ₁ = u * γ₂` for some unit `u`. -/
theorem exists_unit_eq_of_span_eq
    {K : Type*} [Field K] [NumberField K]
    {γ₁ γ₂ : 𝓞 K} (_hγ₂_ne : γ₂ ≠ 0)
    (h_span : Ideal.span ({γ₁} : Set (𝓞 K)) = Ideal.span ({γ₂} : Set (𝓞 K))) :
    ∃ u : (𝓞 K)ˣ, γ₁ = (u : 𝓞 K) * γ₂ := by
  -- Span equality in an integral domain (𝓞 K is a domain) implies associated.
  have h_assoc : Associated γ₁ γ₂ :=
    Ideal.span_singleton_eq_span_singleton.mp h_span
  -- Associated means ∃ u : (𝓞 K)ˣ, γ₁ * u = γ₂, equivalently γ₁ = u⁻¹ * γ₂.
  obtain ⟨u, hu⟩ := h_assoc
  -- hu : γ₁ * u = γ₂
  refine ⟨u⁻¹, ?_⟩
  have h_inv_mul : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * γ₂ = γ₁ := by
    rw [← hu]
    rw [show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (γ₁ * (u : 𝓞 K)) =
      γ₁ * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K)) by ring]
    rw [h_inv_mul, mul_one]
  exact this.symm

/-! ### Bridging phiPrimeGenDescent and h_stick.gen via unit correction

When phiPrimeGenDescent generates the same span as h_stick.gen (both
generate stickelbergerIdeal P), they differ by a unit. The pthSymbol
of h_stick.gen at P' equals the pthSymbol of phiPrimeGenDescent at P'
plus the symbol of the unit correction. Under U-chain assumptions
(unit symbol = 0), they coincide. -/


/-! ### Full apex: K-chain output for h_stick.gen via specific-unit correction

The K-chain output for phiPrimeGenDescent transfers to h_stick.gen of
the StickelbergerIdealEquality constructed from phiPrimeGenDescent,
under the U-chain content for the SPECIFIC unit factor (h_stick.gen and
phiPrimeGenDescent generate the same span, hence differ by a single unit). -/


/-! ### Discharging h_χp_eq_one

The K2-1 hypothesis `(residueCharInt^a).ringHomComp σ ^ p = 1` follows
from `residueMulChar^p = 1` (via `residueMulChar_pow_eq_one_mulChar`)
plus MulChar pow algebra: `(χ^a)^p = (χ^p)^a = 1^a = 1`, and ringHomComp
preserves 1. -/

/-- **`(χ^a).ringHomComp σ ^ p = 1` from `χ^p = 1`**: power algebra +
ringHomComp_one. -/
theorem mulChar_pow_ringHomComp_pow_p_eq_one
    {k : Type*} [CommMonoidWithZero k]
    {R' R'' : Type*} [CommRing R'] [CommRing R'']
    {p : ℕ}
    (χ : MulChar k R') (hχ : χ ^ p = 1) (a : ℕ) (σ : R' →+* R'') :
    (χ ^ a).ringHomComp σ ^ p = 1 := by
  rw [MulChar.ringHomComp_pow]
  rw [show (χ ^ a) ^ p = (χ ^ p) ^ a from by rw [← pow_mul, ← pow_mul, mul_comm]]
  rw [hχ, one_pow, MulChar.ringHomComp_one]

/-- **Positive norm powers**: a power of a rational prime is at least `1`. -/
theorem one_le_pow_of_natPrime {ℓ' f : ℕ} [Fact ℓ'.Prime] :
    1 ≤ ℓ' ^ f :=
  Nat.succ_le_of_lt (Nat.pow_pos (Fact.out : ℓ'.Prime).pos)

/-- **Norm congruence from divisibility by `p`**: if `p ∣ N - 1` and `N > 0`,
then `N ≡ 1 (mod p)`.  This is the arithmetic side condition needed in the
K2-1 Frobenius cancellation step. -/
theorem Nat.mod_eq_one_of_dvd_sub_one
    {p N : ℕ} (hp : 1 < p) (hN_pos : 0 < N)
    (hdiv : p ∣ N - 1) :
    N % p = 1 := by
  rcases hdiv with ⟨m, hm⟩
  have hN_eq : N = p * m + 1 := by
    omega
  rw [hN_eq, Nat.add_mod, Nat.mul_mod_right]
  simp [Nat.mod_eq_of_lt hp]

/-- **Prime-ideal non-membership survives natural powers**: if the natural
integer `n` is nonzero modulo a prime ideal `P`, then so is `n^f`. -/
theorem natCast_pow_notMem_of_natCast_notMem
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsPrime]
    {n f : ℕ} (hn : ((n : ℕ) : 𝓞 K) ∉ P) :
    (((n ^ f : ℕ) : 𝓞 K)) ∉ P := by
  rw [Nat.cast_pow]
  intro hpow
  exact hn (Ideal.IsPrime.mem_of_pow_mem (hI := inferInstance) _ hpow)

/-- **Different rational primes stay nonzero in a residue field**: if
`𝓞 K / P` has characteristic `ℓ`, then a different rational prime `ℓ'` is not
in `P`. -/
theorem natPrime_notMem_of_charP_quotient_ne
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    {ℓ ℓ' : ℕ} [CharP (𝓞 K ⧸ P) ℓ]
    (hℓ'_prime : ℓ'.Prime) (h_ne : ℓ ≠ ℓ') :
    (((ℓ' : ℕ) : 𝓞 K)) ∉ P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  intro hmem
  have hzero : (ℓ' : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P) ℓ']
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (CharP.cast_ne_zero_of_ne_of_prime (𝓞 K ⧸ P) hℓ'_prime h_ne) hzero

/-- **Residue characteristic descends across the residue-field embedding**:
if `𝔭` lies over `P'` and `𝓞 R' / 𝔭` has characteristic `ℓ'`, then so does
`𝓞 K / P'`. -/
theorem charP_baseResidue_of_liesOver
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [CharP (𝓞 R' ⧸ 𝔭) ℓ'] :
    CharP (𝓞 K ⧸ P') ℓ' :=
  (residueFieldEmbedding h_over).charP (residueFieldEmbedding_injective h_over) ℓ'

/-- **Residue-field divisibility from the canonical root**: if `q` is a
maximal ideal of `𝓞 K` away from `p`, then the canonical residue primitive
`p`-th root forces `p ∣ #(𝓞 K/q)-1`. -/
theorem canonicalResidueZetaP_card_sub_one_dvd
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {q : Ideal (𝓞 K)} (hq_ne_bot : q ≠ ⊥) [hq_max : q.IsMaximal]
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    p ∣ Fintype.card (𝓞 K ⧸ q) - 1 := by
  classical
  letI : Field (𝓞 K ⧸ q) := Ideal.Quotient.field q
  haveI : q.IsPrime := hq_max.isPrime
  have horder :
      orderOf (canonicalResidueZetaP (p := p) (K := K) q) = p :=
    canonicalResidueZetaP_orderOf_eq (p := p) (K := K) hq_ne_bot hp_not_in_q
  rw [← horder]
  simpa [Fintype.card_units] using
    (orderOf_dvd_card (x := canonicalResidueZetaP (p := p) (K := K) q))


/-- **Proof-irrelevant residue-character transport**: changing the selected
source primitive root by equality changes neither the residue character nor
its proof arguments. -/
theorem residueMulChar_eq_of_zeta_eq
    {p : ℕ} [NeZero p]
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommMonoidWithZero R']
    {zeta_q zeta_q' : kˣ} (hζ : zeta_q = zeta_q')
    (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (hzeta_q' : IsPrimitiveRoot zeta_q' p)
    (hdiv' : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R =
      residueMulChar zeta_q' hzeta_q' hdiv' zeta_R hzeta_R := by
  cases hζ
  rfl


end Furtwaengler

end BernoulliRegular

end
