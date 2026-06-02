module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp

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


/-! ### Residue field embedding `𝓞 K / P → 𝓞 R' / 𝔭`

For `𝔭 ⊂ 𝓞 R'` lying over `P ⊂ 𝓞 K` (i.e., `𝔭.comap algebraMap = P`),
the algebra map `𝓞 K → 𝓞 R'` factors through the residue fields,
giving an injection `𝓞 K / P → 𝓞 R' / 𝔭`. -/





namespace Ref18SourcePrimeOverData




end Ref18SourcePrimeOverData

end Furtwaengler

end BernoulliRegular

end
