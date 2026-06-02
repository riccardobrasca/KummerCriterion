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


/-! ### h_χ_value derivation: the per-index K2-2c content (negated form)

To use `cross_ring_identity_from_K2_1_K2_2c`, we need `h_χ_value`:

`χ' unit_a · (Quotient.mk 𝔭 zeta_p_int)^((-s).val) = 1`

Equivalently, `χ' unit_a = (Quotient.mk 𝔭 zeta_p_int)^(-((-s).val))`. From
`residueMulChar_pow_ringHomComp_apply_quotient_canonical` we get
`χ' unit_a = σ(zeta_R)^(a · s.val)`. Combining yields the constraint

`σ(zeta_R)^(a · s.val + (-s).val) = 1`

which holds when `a · s.val + (-s).val ≡ 0 (mod p)`, i.e., when
`(a - 1) · s.val ≡ 0 (mod p)` (using zeta of order p). -/




/-! ### Pow mod p for order-p elements

Bridge lemmas for converting between natural-number powers and
ZMod p val powers when the base has order dividing p. -/




/-! ### Discharging h_χ_eval_pow from residueCharInt = residueMulChar

Abstract bridge: given an arbitrary character `χ` on `𝓞 K / P` identified
with `residueMulChar (canonicalResidueZetaP P) ... zeta_R ...`, the
per-index K2-2c form holds. -/


end Furtwaengler

end BernoulliRegular

end
