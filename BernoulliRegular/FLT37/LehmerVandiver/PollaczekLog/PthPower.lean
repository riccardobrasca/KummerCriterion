module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.FieldTheory.Finite.Basic

/-!
# `p`-th powers modulo a prime ideal

For an odd prime `p`, a commutative ring `R`, an ideal `𝔩 ⊂ R`, and an
element `x : R`, we say `x` is a **`p`-th power modulo `𝔩`** if its
image in `R ⧸ 𝔩` is a `p`-th power, that is

  `∃ y : R ⧸ 𝔩, (Ideal.Quotient.mk 𝔩 x) = y ^ p`.

This is the predicate used in Washington's Proposition 8.18 (Pollaczek's
log identity, Washington p. 158) and is the central residue test in the
Lehmer–Vandiver certificate of Theorem 9.5 (p. 176).

This file provides:

* `BernoulliRegular.IsPthPowerModPrime` — the predicate.
* `IsPthPowerModPrime.one`, `.mul`, `.pow_self` — basic closure
  properties: `1` is a `p`-th power, products of `p`-th powers are
  `p`-th powers, and `x ^ p` is always a `p`-th power.
* `IsPthPowerModPrime.pow` — the image of a `p`-th power under any
  natural-number power is again a `p`-th power.
* `BernoulliRegular.isPthPowerModPrime_iff_pow_card_div_p_eq_one` —
  the **cyclic-group criterion**: when `R ⧸ 𝔩` is a finite field and
  `p ∣ Fintype.card (R ⧸ 𝔩) - 1` and `x ∉ 𝔩`, then `x` is a `p`-th
  power modulo `𝔩` iff `x ^ ((Fintype.card (R ⧸ 𝔩) - 1) / p) ≡ 1
  (mod 𝔩)`.

## Mathlib infrastructure reused

The cyclic-group criterion is proved by combining:

* `IsCyclic` instance for `Rˣ` of a finite integral domain
  (`Mathlib.RingTheory.IntegralDomain`).
* `IsCyclic.card_powMonoidHom_range` (cyclic group / `powMonoidHom`
  cardinalities; `Mathlib.GroupTheory.SpecificGroups.Cyclic`).
* `Fintype.card_units` (`Mathlib.Data.Fintype.Units`) and
  `FiniteField.pow_card_sub_one_eq_one`
  (`Mathlib.FieldTheory.Finite.Basic`) to translate between
  cardinalities of `R ⧸ 𝔩` and `(R ⧸ 𝔩)ˣ`.
* `Ideal.Quotient.field` to upgrade a quotient by a prime / maximal
  ideal to a `Field` instance for the unit-group analysis.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer GTM
  83, §8.3 (Pollaczek units, p. 158) and §9 (Theorem 9.5, p. 176).
* Vandiver, "Fermat's last theorem and the second factor in the
  cyclotomic class number," Bull. AMS 40 (1934) 118–126.
-/

@[expose] public section

namespace BernoulliRegular

open Ideal

variable {R : Type*} [CommRing R]


namespace IsPthPowerModPrime

variable {p : ℕ} {𝔩 : Ideal R}





end IsPthPowerModPrime

section CyclicCriterion

variable {𝔩 : Ideal R}


end CyclicCriterion

section IdealCriterion

variable {𝔩 : Ideal R}



end IdealCriterion

end BernoulliRegular

end
