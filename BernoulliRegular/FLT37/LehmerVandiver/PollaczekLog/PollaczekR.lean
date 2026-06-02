module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekUnit

/-!
# Auxiliary Pollaczek cyclotomic unit `pollaczekR`

For an odd prime `p` and a non-negative integer `i`, Washington defines
the auxiliary cyclotomic element

  `R_i := ∏_{a=1}^{p-1} (ζ^{a/2} - ζ^{-a/2})^{a^{p-1-i}} ∈ 𝓞 K`

inside `K = ℚ(ζ_p)` where `ζ = ζ_p` is the standard primitive `p`-th
root of unity. Here `a/2` denotes `a · 2⁻¹` viewed in `ZMod p`; this is
well-defined because `2 ∈ ZMod p` is invertible whenever `p` is odd.

`R_i` is related to the Pollaczek unit `E_i = pollaczekUnit p K i`
(developed in `BernoulliRegular/FLT37/LehmerVandiver/PollaczekUnit.lean`)
by Pollaczek's identity (Washington, p. 158, line 5)

  `R_i^{g^i - 1} = E_i · α^p`     for some `α ∈ K^×`

with `g` a primitive root mod `p`. This file only **defines** `R_i` and
gives the basic factorisation API; Pollaczek's identity itself is the
content of the companion ticket **LV004d**.

## Key factorisation

Since `(ζ^{a/2} - ζ^{-a/2}) = ζ^{-a/2} · (ζ^{2·(a/2)} - 1)`, the product
`R_i` factors term-wise into a `ζ`-power times the simpler product
`∏_{a=1}^{p-1} (ζ^{2·(a/2)} - 1)^{a^{p-1-i}}`. Together with the
`ZMod p`-identity `2 · (a/2) = a`, the second factor is
`∏_{a=1}^{p-1} (ζ^a - 1)^{a^{p-1-i}}` (after using `ζ^p = 1`).

* `pollaczekRFactor_eq_neg_half_mul_sub` exposes the term-wise unit-zpow
  factorisation `ζ^{a/2} - ζ^{-a/2} = ζ^{-a/2} · (ζ^{2·(a/2)} - 1)`.
* `two_mul_pollaczekRExp` is the `ZMod p` identity `2 · (a/2) = a`.
* `zeta_unit_zpow_two_mul_pollaczekRExp_val_eq` lifts this to the
  unit-zpow identity `ζ^{2·(a/2).val} = ζ^a` using `ζ^p = 1`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units), p. 158 (line 1, defining `R_i`).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section PollaczekR

/-- The half-exponent `a/2 := a · 2⁻¹ ∈ ZMod p`. For odd `p`, this is
well-defined because `2 ∈ ZMod p` is invertible. -/
noncomputable def pollaczekRExp (a : ℕ) : ZMod p :=
  (a : ZMod p) * (2 : ZMod p)⁻¹

/-- The factor at index `a` in the auxiliary Pollaczek product:
`ζ^{a/2} - ζ^{-a/2} ∈ 𝓞 K`, viewed via the unit ζ raised to integer
exponents and coerced to `𝓞 K`. The integer exponent is the natural lift
of `(pollaczekRExp p a) : ZMod p` via `ZMod.val`. -/
noncomputable def pollaczekRFactor (a : ℕ) : 𝓞 K :=
  (((zeta_spec p ℚ K).unit' ^
      ((pollaczekRExp p a).val : ℤ) : (𝓞 K)ˣ) : 𝓞 K) -
    (((zeta_spec p ℚ K).unit' ^
      (-((pollaczekRExp p a).val : ℤ)) : (𝓞 K)ˣ) : 𝓞 K)


end PollaczekR

section PollaczekRAPI

variable (i : ℕ)


/-- **The integer exponent equality** `2 · (a/2) = a` in `ZMod p`,
using that `2` is invertible in `ZMod p` for odd `p`. -/
theorem two_mul_pollaczekRExp (hp_odd : p ≠ 2) (a : ℕ) :
    (2 : ZMod p) * pollaczekRExp p a = (a : ZMod p) := by
  unfold pollaczekRExp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_nat : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h_nat
    exact hp_odd ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp h_nat)
  rw [show (a : ZMod p) * (2 : ZMod p)⁻¹ =
        (2 : ZMod p)⁻¹ * (a : ZMod p) from by ring,
    ← mul_assoc, mul_inv_cancel₀ h2, one_mul]

/-- **Term-wise factorisation of the Pollaczek factor in unit-zpow form.**
Pulling out `ζ^{-a/2}` gives

  `ζ^{a/2} - ζ^{-a/2} = ζ^{-a/2} · (ζ^{2·(a/2)} - 1)`,

stated using the unit zpow on `(zeta_spec p ℚ K).unit'`. The companion
lemma `two_mul_pollaczekRExp` rewrites `2 · (a/2) = a` in `ZMod p`, and
periodicity of `ζ` (order dividing `p`) then yields the simpler form
`ζ^{2·(a/2)} = ζ^a`. -/
theorem pollaczekRFactor_eq_neg_half_mul_sub (a : ℕ) :
    pollaczekRFactor p K a =
      (((zeta_spec p ℚ K).unit' ^
          (-((pollaczekRExp p a).val : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) *
        ((((zeta_spec p ℚ K).unit' ^
                (2 * ((pollaczekRExp p a).val : ℤ)) :
              (𝓞 K)ˣ) : 𝓞 K) - 1) := by
  unfold pollaczekRFactor
  set ζ : (𝓞 K)ˣ := (zeta_spec p ℚ K).unit'
  set m : ℤ := ((pollaczekRExp p a).val : ℤ)
  have hpow : ((ζ ^ (-m) : (𝓞 K)ˣ) : 𝓞 K) *
      ((ζ ^ (2 * m) : (𝓞 K)ˣ) : 𝓞 K) =
      ((ζ ^ m : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    ring
  rw [mul_sub, hpow, mul_one]

/-- The unit ζ has `ζ^p = 1`. -/
theorem zeta_unit_pow_p_eq_one :
    ((zeta_spec p ℚ K).unit' ^ (p : ℕ) : (𝓞 K)ˣ) = 1 := by
  apply Units.ext
  change (((zeta_spec p ℚ K).unit' : 𝓞 K)) ^ p = 1
  exact (zeta_spec p ℚ K).unit'_coe.pow_eq_one

/-- **Periodicity step**: `ζ^p = 1` as a unit, so any integer exponent
on `ζ` reduces mod `p`. In particular,
`(ζ_unit)^(2 · (a/2).val) = (ζ_unit)^a` because `2 · (a/2) ≡ a (mod p)`
and `ζ^p = 1`. -/
theorem zeta_unit_zpow_two_mul_pollaczekRExp_val_eq
    (hp_odd : p ≠ 2) (a : ℕ) :
    ((zeta_spec p ℚ K).unit' ^ (2 * ((pollaczekRExp p a).val : ℤ)) :
        (𝓞 K)ˣ) =
      ((zeta_spec p ℚ K).unit' ^ (a : ℤ) : (𝓞 K)ˣ) := by
  set ζ : (𝓞 K)ˣ := (zeta_spec p ℚ K).unit'
  have hζp_int : ζ ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]; exact zeta_unit_pow_p_eq_one p K
  -- 2 · (a/2).val ≡ a (mod p) as integers (lifted from ZMod p).
  have h_zmod : ((2 * ((pollaczekRExp p a).val : ℤ) : ℤ) : ZMod p) =
      ((a : ℤ) : ZMod p) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact two_mul_pollaczekRExp p hp_odd a
  obtain ⟨k, hk⟩ : (p : ℤ) ∣ (2 * ((pollaczekRExp p a).val : ℤ) - (a : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Int.cast_sub]
    rw [h_zmod]
    ring
  have heq : (2 * ((pollaczekRExp p a).val : ℤ) : ℤ) = (a : ℤ) + (p : ℤ) * k := by
    linarith [hk]
  rw [heq, zpow_add, zpow_mul, hζp_int, one_zpow, mul_one]

/-- **Factorisation of the Pollaczek factor with the cleaned `ζ^a - 1`
form**: combining `pollaczekRFactor_eq_neg_half_mul_sub` with the
periodicity step gives

  `ζ^{a/2} - ζ^{-a/2} = ζ^{-a/2} · (ζ^a - 1)`,

stated entirely inside `𝓞 K`. -/
theorem pollaczekRFactor_eq_neg_half_mul_zeta_pow_sub_one
    (hp_odd : p ≠ 2) (a : ℕ) :
    pollaczekRFactor p K a =
      (((zeta_spec p ℚ K).unit' ^
          (-((pollaczekRExp p a).val : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) *
        (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ a - 1) := by
  rw [pollaczekRFactor_eq_neg_half_mul_sub p K a,
    zeta_unit_zpow_two_mul_pollaczekRExp_val_eq p K hp_odd a,
    zpow_natCast, Units.val_pow_eq_pow_val]


end PollaczekRAPI

section PairUp

variable (i : ℕ)

/-- **Half-exponent symmetry:** `pollaczekRExp p (p - a) = -pollaczekRExp p a`
in `ZMod p`. Consequence of `((p - a : ℕ) : ZMod p) = -(a : ZMod p)` for
`a ≤ p`, since `(p : ZMod p) = 0`. -/
theorem pollaczekRExp_p_sub {a : ℕ} (ha : a ≤ p) :
    pollaczekRExp p (p - a) = -pollaczekRExp p a := by
  unfold pollaczekRExp
  have h_sub : ((p - a : ℕ) : ZMod p) = -(a : ZMod p) := by
    rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub]
  rw [h_sub, neg_mul]

/-- **Pair-up sign:** `pollaczekRFactor p K (p - a) = -pollaczekRFactor p K a`
for `a ≤ p`. The proof uses `pollaczekRExp p (p - a) = -pollaczekRExp p a`,
the integer-cast identity `(-x).val ≡ -x.val (mod p)`, and `ζ^p = 1` to
swap the two ζ-exponents. -/
theorem pollaczekRFactor_p_sub_eq_neg {a : ℕ} (ha : a ≤ p) :
    pollaczekRFactor p K (p - a) = -pollaczekRFactor p K a := by
  unfold pollaczekRFactor
  set ζ : (𝓞 K)ˣ := (zeta_spec p ℚ K).unit'
  have hζp : ζ ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]; exact zeta_unit_pow_p_eq_one p K
  -- m' ≡ -m (mod p), as integers, where m = (a/2).val and m' = ((p-a)/2).val.
  have h_zmod : (((pollaczekRExp p (p - a)).val : ℤ) : ZMod p)
      = ((-((pollaczekRExp p a).val : ℤ) : ℤ) : ZMod p) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
    exact pollaczekRExp_p_sub p ha
  obtain ⟨k, hk⟩ : (p : ℤ) ∣ ((pollaczekRExp p (p - a)).val : ℤ)
        - (-((pollaczekRExp p a).val : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, h_zmod, sub_self]
  set m : ℤ := ((pollaczekRExp p a).val : ℤ)
  set m' : ℤ := ((pollaczekRExp p (p - a)).val : ℤ)
  have heq : m' = -m + (p : ℤ) * k := by linarith
  have h1 : (ζ ^ m' : (𝓞 K)ˣ) = (ζ ^ (-m) : (𝓞 K)ˣ) := by
    rw [heq, zpow_add, zpow_mul, hζp, one_zpow, mul_one]
  have h2 : (ζ ^ (-m') : (𝓞 K)ˣ) = (ζ ^ m : (𝓞 K)ˣ) := by
    rw [show (-m' : ℤ) = m + (p : ℤ) * (-k) from by linarith, zpow_add, zpow_mul,
      hζp, one_zpow, mul_one]
  rw [h1, h2, neg_sub]









end PairUp

end FLT37

end BernoulliRegular

end
