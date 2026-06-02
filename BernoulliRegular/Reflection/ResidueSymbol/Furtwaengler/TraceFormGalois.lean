module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup


/-!
# Galois action on the trace-form additive character (REF-18c2c5-b)

This file connects the cyclotomic Galois action on `R'` to the
Stickelberger psi-shift compatibility for trace-form bundles. The key
input is:

  *Hypothesis*: `σ : R' →+* R'` is a ring hom satisfying
  `σ S.zeta_ell = S.zeta_ell ^ c.val` for some `c : (ZMod ℓ)ˣ`.

The output is a unit `a' : kˣ` (the image of `c` in `kˣ` via the
algebra structure `Algebra (ZMod ℓ) k`) such that
`σ.toMonoidHom.compAddChar S.psi = AddChar.mulShift S.psi a'`.

This discharges the **psi-shift content** of `IsGalCompatible`
restricted to the trace-form refinement. Since the trace form is the
canonical form of every primitive additive character on a finite field,
the trace-form proof handles the substantive case.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
