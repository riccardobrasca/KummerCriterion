module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part5.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler







/-! ### Explicit unit factor between two generators of the same span

Given Span(γ₁) = Span(γ₂), the unit factor `u` with `γ₁ = u * γ₂` is
extracted via Classical.choose. -/




/-! ### Apex via unit factor extraction

Combining `unitFactorOfSpanEq` with
`pthSymbolAtPrime_canonical_h_stick_gen_eq_K_chain_target` gives a
self-contained apex: the K-chain conclusion for h_stick.gen follows
from the K-chain output for phiPrimeGenDescent + the U-chain content
applied to the SPECIFIC extracted unit. -/




/-! ### K-chain at h_stick.gen for index 1 with unit extraction

Specialization of `K_chain_at_h_stick_gen_via_extracted_unit` at index `a = 1`,
giving the cleanest form: `pthSymbol (phiPrimeGen h_stick) P' = -pthSymbol NP' P`. -/


/-! ### Caller-facing K2-2 wrappers for the extracted Stickelberger generator -/

end Furtwaengler

end BernoulliRegular

end
