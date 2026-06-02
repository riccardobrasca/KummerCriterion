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








end GaloisAction

end FLT37

end BernoulliRegular

end
