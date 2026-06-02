module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PollaczekIdentity

/-!
# Factor-wise σ_a-twist for cyclotomic-unit factors (LV005c1a)

For the standard cyclotomic Galois automorphism `σ_a := cyclotomicSigmaOfUnit
p K a` indexed by `a ∈ (ZMod p)ˣ`, the cyclotomic unit
`cyclotomicUnit p K b = (1 + ζ + ⋯ + ζ^{b-1}) = (ζ^b - 1)/(ζ - 1)` transforms
under `σ_a` according to the identity

  `σ_a(cyclotomicUnit p K b) · cyclotomicUnit p K (a : ZMod p).val =
   cyclotomicUnit p K (((a : ZMod p) * b).val)`

in `𝓞 K`. (Equivalently
`σ_a(cyclotomicUnit p K b) = cyclotomicUnit p K ((a · b).val) /
cyclotomicUnit p K a.val`, but the multiplicative form avoids inversion.)

Proof strategy: multiply both sides by `(ζ - 1)`. Apply σ_a to
`(ζ - 1) · cyclotomicUnit b = ζ^b - 1` to get
`(ζ^{a.val} - 1) · σ_a(cyclotomicUnit b) = ζ^{a.val · b} - 1`. Then use
`ζ^{a.val · b} = ζ^{((a · b).val)}` (`ζ` has order `p`) and
`ζ^{a.val} - 1 = (ζ - 1) · cyclotomicUnit a.val` to rewrite the equation as
`σ_a(cyclotomicUnit b) · cyclotomicUnit a.val · (ζ - 1) =
cyclotomicUnit ((a · b).val) · (ζ - 1)`. Cancel `(ζ - 1) ≠ 0`.

This file's main result is the building block for LV005c1b's aggregate
σ-twist on `pollaczekUnit p K i` mod `p`-th powers.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer GTM
  83), Lemma 8.4 (p. 156).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section CyclotomicUnitTwist


/-- **`a.val · b` and `((a · b).val)` are congruent mod `p` for `a : (ZMod p)ˣ`.**
A clean form of the defining identity for ZMod multiplication. -/
private theorem val_mul_eq_val_mul_mod (a : (ZMod p)ˣ) (b : ℕ) :
    (a : ZMod p).val * b ≡ ((a : ZMod p) * b).val [MOD p] := by
  -- Both sides reduce to (a.val * b) mod p in ZMod p.
  -- Use ZMod.val_natCast and ZMod.cast_id.
  have h1 : ((((a : ZMod p).val * b : ℕ) : ZMod p)) =
      (a : ZMod p) * (b : ZMod p) := by
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id]
  have h2 : ((((a : ZMod p) * b).val : ℕ) : ZMod p) =
      (a : ZMod p) * (b : ZMod p) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  -- So the two natural numbers cast to the same element in ZMod p, i.e.,
  -- they are congruent mod p.
  have h_eq : (((a : ZMod p).val * b : ℕ) : ZMod p) =
      ((((a : ZMod p) * b).val : ℕ) : ZMod p) := h1.trans h2.symm
  rwa [ZMod.natCast_eq_natCast_iff'] at h_eq


end CyclotomicUnitTwist

end FLT37

end BernoulliRegular

end
