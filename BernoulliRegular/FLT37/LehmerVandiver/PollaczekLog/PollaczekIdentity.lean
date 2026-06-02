module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PollaczekR
public import BernoulliRegular.UnitQuotient.DeltaAction

/-!
# Pollaczek's identity (LV004d)

This file works toward Washington's Pollaczek identity (p. 158, line 5):
for an odd prime `p`, `K = ℚ(ζ_p)`, and a primitive root `g` mod `p`,

  `pollaczekR p K i ^ (g^i - 1) = pollaczekUnit p K i * α^p`

for some `α ∈ (𝓞 K)^×`. The proof uses the change of variable `a → ag`
in the `pollaczekR` definition, applied via the Galois automorphism
`σ_g(ζ) = ζ^g`, plus telescoping of the cyclotomic-unit factors.

## Approach

The starting point is the existing K-side Galois infrastructure in
`BernoulliRegular.UnitQuotient.DeltaAction`:

* `cyclotomicSigmaOfUnit p K a` is the Galois automorphism
  `σ_a : Gal(K/ℚ)` corresponding to `a : (ZMod p)ˣ`, satisfying
  `σ_a(ζ) = ζ^{a.val}`.
* `cyclotomicRingOfIntegersEquiv p K a` is the induced ring automorphism
  on `𝓞 K`.

For a primitive root `g` mod `p` (i.e. a generator of the cyclic group
`(ZMod p)ˣ`, which exists by `ZMod.isCyclic_units_prime`), `σ_g` acts on
the Pollaczek factor `F_a = ζ^{a/2} - ζ^{-a/2}` by sending it to
`F_{ag mod p}`, i.e. it permutes the factors of `pollaczekR p K i` via
`a ↦ ag mod p`.

## Current status

This file currently provides the primitive-root and basic Galois-action
infrastructure for LV004d. The full Pollaczek identity proof (change of
variable + telescoping) is still pending; see the ticket
`.mathlib-quality/flt37-tickets.md` (LV004d) for the planned approach.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units), p. 158.
* `BernoulliRegular.UnitQuotient.DeltaAction` for the K-side Galois
  action infrastructure.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section PrimitiveRoot



end PrimitiveRoot

section PollaczekRFactorMod





/-- **Balanced division-and-difference identity over `ℕ`.** For
naturals `a, b` and a positive prime `p` with `(p : ℤ) ∣ a - b` (i.e.
`a ≡ b (mod p)` as integers), we have

  `a + p · ((b -ₙ a) / p) = b + p · ((a -ₙ b) / p)`,

where `-ₙ` denotes truncated `Nat` subtraction. The two `Nat`-division
witnesses are zero unless their numerators are positive, so this
captures the balanced form `a + p · α = b + p · β` (one of `α, β` is
zero) for any sign of the integer difference. -/
private theorem balanced_sub_div (p a b : ℕ) (h : (p : ℤ) ∣ (a : ℤ) - b) :
    a + p * ((b - a) / p) = b + p * ((a - b) / p) := by
  rcases le_or_gt a b with hab | hab
  · rw [show a - b = 0 from Nat.sub_eq_zero_of_le hab, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
    have hd : p ∣ b - a := by
      have h_int_neg : (p : ℤ) ∣ -((a : ℤ) - b) := dvd_neg.mpr h
      rw [neg_sub] at h_int_neg
      exact_mod_cast (show ((p : ℕ) : ℤ) ∣ ((b - a : ℕ) : ℤ) from by
        rw [show ((b - a : ℕ) : ℤ) = (b : ℤ) - a from by omega]; exact h_int_neg)
    rw [Nat.mul_div_cancel' hd]; omega
  · rw [show b - a = 0 from Nat.sub_eq_zero_of_le (le_of_lt hab), Nat.zero_div, Nat.mul_zero,
      Nat.add_zero]
    have hd : p ∣ a - b := by
      exact_mod_cast (show ((p : ℕ) : ℤ) ∣ ((a - b : ℕ) : ℤ) from by
        rw [show ((a - b : ℕ) : ℤ) = (a : ℤ) - b from by omega]; exact h)
    rw [Nat.mul_div_cancel' hd]; omega


end PollaczekRFactorMod

section GaloisAction

variable {p}



/-- **Galois action on the unit-zpow cast `(ζ_unit'^n : 𝓞 K)`.** For
`a ∈ (ZMod p)ˣ` and `n : ℤ`, `σ_a` sends
`((zeta_unit')^n : (𝓞 K)ˣ : 𝓞 K)` to `((zeta_unit')^{a.val · n} : (𝓞 K)ˣ : 𝓞 K)`.

Proof: factor through `Units.map` of the induced ring iso
`cyclotomicRingOfIntegersEquiv`. The unit map sends
`zeta_unit'` to `zeta_unit'^{a.val}` (because at the ring level,
`σ_a(ζ_int) = ζ_int^{a.val}` by `cyclotomicSigmaOfUnit_smul_zetaInteger`),
then propagate through `map_zpow` and `← zpow_mul` for the integer
power. This is the bridge from the ring-level σ_a action to the
unit-zpow factorisations used in `pollaczekRFactor`. -/
theorem cyclotomicSigmaOfUnit_smul_zetaUnit_zpow_cast (a : (ZMod p)ˣ) (n : ℤ) :
    cyclotomicSigmaOfUnit (p := p) K a •
        (((zeta_spec p ℚ K).unit' ^ n : (𝓞 K)ˣ) : 𝓞 K) =
      (((zeta_spec p ℚ K).unit' ^ ((a : ZMod p).val * n) : (𝓞 K)ˣ) : 𝓞 K) := by
  set σ_unit : (𝓞 K)ˣ →* (𝓞 K)ˣ :=
    Units.map (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom
  have h1 : cyclotomicSigmaOfUnit (p := p) K a •
          (((zeta_spec p ℚ K).unit' ^ n : (𝓞 K)ˣ) : 𝓞 K) =
        (σ_unit ((zeta_spec p ℚ K).unit' ^ n) : 𝓞 K) := rfl
  have hzeta_unit : σ_unit (zeta_spec p ℚ K).unit' =
      (zeta_spec p ℚ K).unit' ^ (a : ZMod p).val := by
    apply Units.ext
    change (cyclotomicRingOfIntegersEquiv (p := p) K a)
        ((zeta_spec p ℚ K).unit' : 𝓞 K) = _
    change (cyclotomicSigmaOfUnit (p := p) K a) •
        ((zeta_spec p ℚ K).unit' : 𝓞 K) = _
    rw [show ((zeta_spec p ℚ K).unit' : 𝓞 K) = cyclotomicZetaInteger (p := p) K from
      rfl, cyclotomicSigmaOfUnit_smul_zetaInteger, Units.val_pow_eq_pow_val]
    rfl
  rw [h1, map_zpow σ_unit, hzeta_unit]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]

/-- **Galois action on `pollaczekRFactor`.** For `a ∈ (ZMod p)ˣ` and
`b : ℕ`, the σ_a Galois automorphism sends `F_b = pollaczekRFactor p K b`
to `F_{(a · b).val}`:

  σ_a(F_b) = F_{((a : ZMod p) * b).val}.

This is the central transformation lemma for the Pollaczek identity:
when σ_g (with g a primitive root) is applied to
`pollaczekR p K i = ∏_b F_b^{b^E}`, it permutes the factors via
`b ↦ (g · b).val`, giving the change-of-variable form.

Proof: unfold the difference-of-zpow definition of `pollaczekRFactor`;
apply `cyclotomicSigmaOfUnit_smul_zetaUnit_zpow_cast` to each half;
then use `zpow_eq_zpow_iff_modEq` (with `orderOf zeta_unit' = p`) plus
the ZMod p arithmetic identity
`a.val · (b · 2⁻¹) ≡ (a · b) · 2⁻¹ (mod p)` to identify the
two ζ-zpow exponents up to multiples of `p`. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekRFactor (a : (ZMod p)ˣ) (b : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a • pollaczekRFactor p K b =
      pollaczekRFactor p K (((a : ZMod p) * b).val) := by
  unfold pollaczekRFactor
  rw [smul_sub, cyclotomicSigmaOfUnit_smul_zetaUnit_zpow_cast,
    cyclotomicSigmaOfUnit_smul_zetaUnit_zpow_cast]
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set ζu : (𝓞 K)ˣ := (zeta_spec p ℚ K).unit'
  have hord : orderOf ζu = p := by
    rw [← orderOf_units]
    exact ((IsPrimitiveRoot.unit'_coe (zeta_spec p ℚ K)).eq_orderOf).symm
  have hcong : (((a : ZMod p).val : ℤ) * ((pollaczekRExp p b).val : ℤ)) ≡
      ((pollaczekRExp p (((a : ZMod p) * b).val)).val : ℤ) [ZMOD (p : ℤ)] := by
    rw [Int.ModEq, ← ZMod.intCast_eq_intCast_iff']
    push_cast
    unfold pollaczekRExp
    simp only [ZMod.natCast_val, ZMod.cast_id]
    ring
  have happly : ∀ {m n : ℤ}, m ≡ n [ZMOD (p : ℤ)] →
      ((ζu ^ m : (𝓞 K)ˣ) : 𝓞 K) = ((ζu ^ n : (𝓞 K)ˣ) : 𝓞 K) := by
    intro m n hmn; congr 1
    exact zpow_eq_zpow_iff_modEq.mpr (hord ▸ hmn)
  congr 1
  · exact happly hcong
  · rw [show ((a : ZMod p).val : ℤ) * (-((pollaczekRExp p b).val : ℤ)) =
          -(((a : ZMod p).val : ℤ) * ((pollaczekRExp p b).val : ℤ)) from by ring]
    exact happly hcong.neg




end GaloisAction

end FLT37

end BernoulliRegular

end
