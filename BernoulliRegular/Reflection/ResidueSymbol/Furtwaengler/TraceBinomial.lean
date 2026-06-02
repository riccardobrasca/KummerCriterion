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

universe u v w

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- The residual character sum at degree `n` in the trace-form binomial
expansion: `T_n(a) = ∑ x : k, χ_q^a(x) · C((Tr_{k/𝔽_ℓ}(traceScale · x)).val, n)`.

This is the coefficient of `π^n` in the binomial expansion of the integral
Gauss sum, before any combinatorial reduction. -/
noncomputable def traceCharacterChooseSum (a n : ℕ) : 𝓞 R' :=
  ∑ x : k, (S.residueCharInt ^ a) x *
    (Nat.choose (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val n : 𝓞 R')

/-- Reciprocal-convention residual character sum. The underlying character
stored in the setup is ordinary (`χ(x) ≡ x^d mod Q`), so the reciprocal
power `χ^{-a}` is represented in the Stickelberger range by `χ^(p-a)`. -/
noncomputable def traceCharacterChooseSumRec (a n : ℕ) : 𝓞 R' :=
  S.traceCharacterChooseSum (p - a) n



/-- Reciprocal-convention integral Gauss sum, implemented by reindexing the
ordinary character power. -/
noncomputable def gaussSumIntRec (a : ℕ) : 𝓞 R' :=
  S.gaussSumInt (p - a)








end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
