module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingCongruence
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup

/-!
# Trace-form binomial truncation (REF-18c2c4-L2c2)

Specialises the binomial-truncation layer of `LeadingCongruence.lean` to
the trace-form additive character carried by a
`TraceFormStickelbergerSetup`. The bundle's `psiExponent` agrees with the
canonical trace `(Algebra.trace (ZMod ℓ) k (traceScale · x)).val` (via
`psiExponent_trace`), so all binomial-truncation theorems for
`ConcreteStickelbergerSetup` immediately specialise.

The remaining mathematical work — multinomial reduction, character
orthogonality, minimal-weight uniqueness — lives in REF-18c2c4-L2c3.

## Main definitions

* `TraceFormStickelbergerSetup.traceCharacterChooseSum`: the residual
  character sum `T_n(a) = ∑ x : k, χ_q^a(x) · C((Tr(c·x)).val, n)`.
* `TraceFormStickelbergerSetup.traceBinomialApprox`: the truncated
  binomial expansion `∑_{n ≤ s} π^n · T_n(a)`.
* `TraceFormStickelbergerSetup.gaussSumIntRec`: the reciprocal-convention
  Gauss sum, implemented with the ordinary character by reindexing
  `a ↦ p - a`.

## Main theorems

* `gaussSumInt_sub_traceBinomialApprox_mem_Q_pow`:
  `gaussSumInt a − traceBinomialApprox a s ∈ Q^(s+1)`.
* `gaussSumInt_qadic_ord_at_prime_of_traceLead`: exact-order transfer
  theorem in trace form, ready for L2c3 leading-term consumption.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

end Furtwaengler

end BernoulliRegular
