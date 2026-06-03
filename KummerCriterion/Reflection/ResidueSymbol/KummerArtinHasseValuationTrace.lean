module

public import KummerCriterion.Reflection.ResidueSymbol.KummerArtinHasseCompletionMap

/-!
# Valuation-completion trace source for the Kummer--Artin--Hasse `A` term

The earlier local logarithm files are written in the project's adic completed
integer ring `LambdaLocalIntegerRing`. The trace needed for the explicit
Kummer--Artin--Hasse correction, however, is the finite `Q_p`-linear trace on
the valuation completion of `K` at `lambda`.

This file makes the trace-source API use the valuation-completion model from
the start. The old adic logarithm stack remains useful infrastructure, but it
is not the final source of the `A` term consumed by reciprocity.

The `< p` truncated logarithm is kept as a named summand. The active finite
approximation to the full p-adic logarithm for the Kummer--Artin--Hasse
`A`-term is `log_≤p(u) = log_<p(u) + (u - 1)^p / p`; the missing `n = p`
term is essential on the `μ_p` torsion direction in `U_1`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The cyclotomic uniformizer `pi = zeta_p - 1` in the valuation-completion
integer ring. -/
def lambdaValuedPiInteger : LambdaValuedIntegerRing p K :=
  algebraMap (𝓞 K) (LambdaValuedIntegerRing p K)
    ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)

/-- The cyclotomic uniformizer `pi = zeta_p - 1` in the valuation-completion
field. -/
def lambdaValuedPi : LambdaValuedCompletion p K :=
  (lambdaValuedPiInteger p K : LambdaValuedCompletion p K)

/-- The distinguished `p`-th root of unity in the valuation-completion integer
ring. -/
def lambdaValuedZetaInteger : LambdaValuedIntegerRing p K :=
  algebraMap (𝓞 K) (LambdaValuedIntegerRing p K)
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger

/-- The distinguished `p`-th root of unity in the valuation-completion field. -/
def lambdaValuedZeta : LambdaValuedCompletion p K :=
  (lambdaValuedZetaInteger p K : LambdaValuedCompletion p K)

end KummerArtinHasse
end Furtwaengler
end KummerCriterion
