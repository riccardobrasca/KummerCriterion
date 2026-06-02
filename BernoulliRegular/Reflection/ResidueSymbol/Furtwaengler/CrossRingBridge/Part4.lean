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




/-! ### Constructing unit_a from natCast non-membership

When a natural number `n` is not in `P` (in `𝓞 K`), its image in `𝓞 K / P`
is a unit. We package this as a constructor. -/




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











end Furtwaengler

end BernoulliRegular

end
