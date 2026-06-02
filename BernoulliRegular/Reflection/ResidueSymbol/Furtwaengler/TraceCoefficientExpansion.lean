module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceBinomial
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceMultinomial
public import Mathlib.Data.Fintype.Units
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Trace coefficient expansions (REF-18c2c4-L2c3d2)

This file packages the coefficient-expansion API needed after the
reciprocal-convention correction.  The raw combinatorics in
`TraceMultinomial.lean` expands `(traceSum x)^n`; here we record the
weighted exponent contributed by a multi-index, specialise the trace
formula to a `TraceFormStickelbergerSetup`, and expose a factorial-cleared
form of the reciprocal trace-binomial coefficient sums.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
