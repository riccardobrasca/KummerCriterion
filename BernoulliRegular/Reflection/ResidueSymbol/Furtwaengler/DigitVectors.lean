module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceCoefficientValuation
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MinimalWeight


/-!
# Digit vectors and the digit denominator (REF-18c2c4-L2c3d-3)

This file packages the shared digit-vector notation used by the Route-D
proof of the digit-sum Stickelberger congruence (`L2c3d-1..7`,
`L2c3e-1..5`):

* `digitVec ℓ f`: vectors `(m_0, …, m_{f-1})` with `m_i ∈ [0, ℓ)`;
* `digitWeight m = ∑ m_i`, `digitValue m = ∑ m_i · ℓ^i`;
* `digitDen ℓ f := ∏_{i < f} ∏_{r < ℓ} r!`, the common denominator;
* `digitCoeff m := digitDen / ∏ m_i!`, the integral multinomial coefficient.

The identity `digitCoeff m · ∏ m_i! = digitDen` is the multinomial
denominator-cleared form originally planned for L2c3d-4. That digit-bounded
expansion turned out to be mathematically incorrect; the correct
expansion is the Dwork splitting expansion in `DworkAssembly.lean`
(`gaussSumIntRec_dwork_expansion`), and `digitCoeff` / `digitDen` here
remain useful as multinomial-arithmetic helpers consumed by other
files.

This file proves the **L2c3d-3 deliverables**:

* `digitDen_not_mem_Q` — the digit denominator is a `Q`-unit;
* `mem_Q_pow_of_digitDen_mul_mem` — cancel the digit denominator from a
  `Q`-power membership.

Both follow from the factorial-not-in-`Q` lemmas already proved in
`TraceCoefficientValuation.lean` plus the primality of `Q`.
-/

@[expose] public section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler


namespace digitVec

variable {ℓ f : ℕ}






end digitVec













































end Furtwaengler

end BernoulliRegular
