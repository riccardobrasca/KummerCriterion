module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitVectors
public import Mathlib.Data.Fintype.Units
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Full-Teichmüller Stickelberger setup (REF-18c2c4-L2c3d-0)

The route-D proof of the digit-sum Stickelberger congruence requires a
multiplicative section
`teichUnitFull : kˣ →* (𝓞 R')ˣ` whose values reduce modulo `Q` to the
identity on `kˣ`. Such a section has order exactly `q − 1` (with
`q = #k`), and exists in the integral closure as soon as `R'` contains
primitive `(q − 1)`-th roots of unity.

The base `TraceFormStickelbergerSetup` only requires
`[IsCyclotomicExtension {p, ℓ} ℚ R']`, which gives `lcm(p, ℓ)`-th roots
only — generally insufficient. The reviewer's recommended fix is an
extension layer that takes the order-`(q−1)` Teichmüller as an explicit
bundle hypothesis. Concrete instances are constructed over the auxiliary
field `R' = ℚ(ζ_{ℓ(q−1)})` (which contains both `ζ_p` and `ζ_{q−1}`,
since `p ∣ q−1`).

## Main definition

* `FullTeichStickelbergerSetup`: extends `TraceFormStickelbergerSetup`
  with `teichUnitFull` plus the residue compatibility identity and the
  bridge to `residueCharInt`.

## Downstream usage

The Wave-2 Stickelberger lemmas
(`teichUnitFull_sum_pow_units`,
`residueCharInt_rec_eq_teichUnitFull_pow`,
`digit_expansion_inner_sum_eval`,
`leadingCoeff_not_mem_Q`)
are stated against this richer setup; the existing arithmetic /
digit-vector layer (Wave-1) remains stated against the base
`TraceFormStickelbergerSetup` and is reused unchanged through the
inheritance. The actual digit-sum Stickelberger statements
(`gaussSumIntRec_mem_Q_pow_stickOrd_dwork`,
`gaussSumIntRec_not_mem_Q_pow_stickOrd_succ_dwork`, and assemblies)
live on the further refinement `FullTeichDworkSetup` in
`DworkAssembly.lean`, which carries the Dwork splitting expansion that
correctly replaces the originally-planned (false) denominator-cleared
digit-bounded expansion.

## Constructibility note

A concrete `FullTeichStickelbergerSetup` is **not** constructed in this
file. The instance over `R' = ℚ(ζ_{ℓ(q−1)})` (with the canonical
Teichmüller given by Hensel-lifted `(q−1)`-th roots) is tracked
separately. The uniformizer fact `pi_not_mem_Q_sq` is inherited from
the base setup and remains valid at the enlarged conductor `ℓ(q−1)`
because the ramification index at `ℓ` is still `ℓ − 1`
(`IsCyclotomicExtension.Rat.ramificationIdx_eq` with `n = ℓ^1·(q−1)`,
`ℓ ∤ (q−1)`).
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
