import BernoulliRegular.LValueAtOne.Even
import BernoulliRegular.GaussSum.Basic
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.DetBridge
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Analytic core for the cyclotomic-unit route

This file exposes the proved analytic ingredients needed for the
cyclotomic-unit index formula in the notation used by
`BernoulliRegular/CyclotomicUnits`.

It deliberately does not assume a bundled Sinnott target. The downstream
matrix-restriction bridge from the Sinnott regulator matrix to the deleted
Fourier determinant is proved separately in `IndexDeterminant.lean`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

variable (p : ℕ) [Fact p.Prime]







end CyclotomicUnits
end BernoulliRegular

end
