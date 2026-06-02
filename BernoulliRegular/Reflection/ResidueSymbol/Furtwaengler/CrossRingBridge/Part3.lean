module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part2

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


/-! ### `phiPrimeGenDescent` as a Stickelberger ideal generator

When the constructive descent generator `phiPrimeGenDescent S a` lies in
the Stickelberger ideal at `P` and generates it (as a principal ideal),
we can package it into a `StickelbergerIdealEquality P` structure for use
with the K2-2 conditional theorem. -/


/-! ### Descent atom (parametric form)

The descent atom — the substantive K2-2 statement — says

`(Quotient.mk P' phiPrimeGenDescent)^((NP'-1)/p) =
  (canonicalResidueZetaP P')^((-s).val)`

where `s = pthSymbolAtPrime_canonical NP' P`. We package the cross-ring
chain (K2-1 + K2-2c + SetupZetaCompatible) into a parametric form: given
the lifted ring identity in `𝓞 R' / 𝔭`, we deduce the descent atom in
`𝓞 K / P'`. -/



/-! ### Cross-ring identity: assembly from K2-1 + character-value hypothesis

The cross-ring identity for `descent_atom_of_cross_ring` follows from
the K2-1 cross-ring cancellation plus a character-value hypothesis
(captured in `h_χ_value` below: the value of the residue character at
`unit_a`, which is the substantive K2-2c-with-index claim). -/


/-! ### K2-2c with character pow

When `residueCharInt = residueMulChar` (typical setup), then
`(residueCharInt^a).ringHomComp σ` evaluated at a quotient class equals
`σ(zeta_R)` raised to `a · pthSymbol.val`. -/

/-- **K2-2c with pow**: applying `(residueMulChar^a).ringHomComp σ` to
`Quotient.mk P α` gives `σ(zeta_R)` raised to `a * (pthSymbol α P).val`. -/
theorem residueMulChar_pow_ringHomComp_apply_quotient_canonical
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [CommRing R']
    {R'' : Type*} [CommRing R'']
    (P : Ideal (𝓞 K)) (hbot : P ≠ ⊥) [hmax : P.IsMaximal]
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (hp_in : (p : 𝓞 K) ∉ P)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R'') {a : ℕ} (ha : a ≠ 0)
    {α : 𝓞 K} (hα : α ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    (((residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
        hdiv zeta_R hzeta_R) ^ a).ringHomComp σ)
        ((Ideal.Quotient.mk P α : 𝓞 K ⧸ P)) =
      σ ((zeta_R : R')) ^
        (a * (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) α P).val) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [MulChar.ringHomComp_apply, MulChar.pow_apply' _ ha]
  rw [residueMulChar_apply_quotient_canonical_eq_pow_pthSymbol
    P hbot hdiv hp_in zeta_R hzeta_R hα]
  rw [← pow_mul, map_pow, mul_comm]

/-! ### h_χ_value derivation: the per-index K2-2c content (negated form)

To use `cross_ring_identity_from_K2_1_K2_2c`, we need `h_χ_value`:

`χ' unit_a · (Quotient.mk 𝔭 zeta_p_int)^((-s).val) = 1`

Equivalently, `χ' unit_a = (Quotient.mk 𝔭 zeta_p_int)^(-((-s).val))`. From
`residueMulChar_pow_ringHomComp_apply_quotient_canonical` we get
`χ' unit_a = σ(zeta_R)^(a · s.val)`. Combining yields the constraint

`σ(zeta_R)^(a · s.val + (-s).val) = 1`

which holds when `a · s.val + (-s).val ≡ 0 (mod p)`, i.e., when
`(a - 1) · s.val ≡ 0 (mod p)` (using zeta of order p). -/

/-- **Order-p exponent congruence**: in a monoid where `x^p = 1`, if
`m + n ≡ 0 (mod p)` then `x^m · x^n = 1`. -/
theorem pow_add_eq_one_of_order_dvd_p
    {G : Type*} [Monoid G]
    {x : G} {p : ℕ} (_hp : 0 < p) (hx : x ^ p = 1)
    (m n : ℕ) (h_sum : (m + n) % p = 0) :
    x ^ m * x ^ n = 1 := by
  rw [← pow_add]
  rw [show m + n = p * ((m + n) / p) + (m + n) % p from (Nat.div_add_mod _ _).symm]
  rw [h_sum, add_zero]
  rw [pow_mul, hx, one_pow]

/-- **Sum of `n.val` and `(-n).val` is `0 mod p`** for `n : ZMod p`. -/
theorem ZMod.val_add_neg_val {p : ℕ} [NeZero p] (n : ZMod p) :
    (n.val + (-n).val) % p = 0 := by
  have h : ((n.val + (-n).val : ℕ) : ZMod p) = 0 := by
    push_cast [ZMod.natCast_val, ZMod.cast_id']
    simp
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp h)

/-- **`h_χ_value` from "single-power" form**: if `χ' unit_a = x^(s.val)`
and `x` has order dividing `p`, then `χ' unit_a · x^((-s).val) = 1`. -/
theorem h_chi_value_of_single_power
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {G : Type*} [Monoid G]
    {x χ_u : G} {s : ZMod p}
    (h_eval : χ_u = x ^ s.val)
    (h_x_order : x ^ p = 1) :
    χ_u * x ^ (-s).val = 1 := by
  rw [h_eval]
  exact pow_add_eq_one_of_order_dvd_p (Fact.out : p.Prime).pos h_x_order s.val (-s).val
    (ZMod.val_add_neg_val s)

/-! ### Pow mod p for order-p elements

Bridge lemmas for converting between natural-number powers and
ZMod p val powers when the base has order dividing p. -/

/-- **Pow mod p**: in a monoid, if `x^p = 1`, then `x^n = x^(n % p)`. -/
theorem pow_eq_pow_mod_p_of_order_dvd
    {G : Type*} [Monoid G] {x : G} {p : ℕ}
    (hx : x ^ p = 1) (n : ℕ) :
    x ^ n = x ^ (n % p) := by
  rcases Nat.eq_zero_or_pos p with h_p_zero | h_p_pos
  · subst h_p_zero
    simp [Nat.mod_zero]
  · conv_lhs => rw [show n = p * (n / p) + n % p from (Nat.div_add_mod _ _).symm]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- **`(n.val · m).val · p arithmetic**: for `n m : ZMod p`, the natural
val of `n * m` equals `(n.val * m.val) % p`. -/
theorem ZMod.val_mul_eq_mod {p : ℕ} [NeZero p] (n m : ZMod p) :
    (n * m).val = (n.val * m.val) % p := ZMod.val_mul n m

/-- **`x^(n.val * m)` for `n : ZMod p` and `m : ℕ`**: equals
`x^((n * m_zmod).val)` where `m_zmod = (m : ZMod p)`. Useful for
converting per-index `a * s.val` to `(a * s).val`. -/
theorem pow_natVal_mul_eq_pow_zmod_mul
    {G : Type*} [Monoid G] {x : G} {p : ℕ} [NeZero p]
    (hx : x ^ p = 1) (n : ZMod p) (m : ℕ) :
    x ^ (m * n.val) = x ^ ((m : ZMod p) * n).val := by
  rw [pow_eq_pow_mod_p_of_order_dvd hx (m * n.val)]
  congr 1
  rw [ZMod.val_mul_eq_mod, ZMod.val_natCast]
  -- Goal: m * n.val % p = m % p * n.val % p
  conv_lhs => rw [Nat.mul_mod]
  rw [Nat.mod_eq_of_lt (ZMod.val_lt n)]

/-! ### Discharging h_χ_eval_pow from residueCharInt = residueMulChar

Abstract bridge: given an arbitrary character `χ` on `𝓞 K / P` identified
with `residueMulChar (canonicalResidueZetaP P) ... zeta_R ...`, the
per-index K2-2c form holds. -/

/-- **h_χ_eval_pow from character identification**: under the abstract
identification `χ = residueMulChar (canonicalResidueZetaP P) ... zeta_R ...`,
the per-index K2-2c form holds. Abstracted over the setup so callers can
specialize to whatever k they need. -/
theorem chi_pow_apply_quotient_eq_pow_pthSymbol
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
    {α : 𝓞 K} (hα : α ∉ P)
    (χ : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      MulChar (𝓞 K ⧸ P) R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      χ = residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
        hdiv zeta_R hzeta_R) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((χ ^ a).ringHomComp σ) ((Ideal.Quotient.mk P α : 𝓞 K ⧸ P)) =
      σ (zeta_R : R') ^
        (a * (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) α P).val) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [h_residue_char_eq]
  exact residueMulChar_pow_ringHomComp_apply_quotient_canonical
    P hP_bot hdiv hp_in_P zeta_R hzeta_R σ ha hα

end Furtwaengler

end BernoulliRegular

end
