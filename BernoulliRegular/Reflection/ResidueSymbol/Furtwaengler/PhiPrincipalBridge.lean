module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KellyPrime
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiIdealElement

/-!
# Principal Φ to Stickelberger bridge

This file contains the K2-5/K2-6 bridge in the corrected REF-18 K-chain.

K2-4 gives the norm-symbol identity for the **actual** principal Φ element
`Φ((α))`.  K2-5 identifies the symbol of the explicit Stickelberger
principal generator `α^Θ = stickelbergerPrincipalGen α` with the weighted
Galois sum.  K2-6 is the conditional unit-stripping step:
if the actual Φ element differs from `α^Θ` by a unit whose residue symbols
vanish, then the weighted Galois sum satisfies the norm-symbol identity.

The sign is intentionally the sign currently produced by the formal K2-2
Frobenius chain: the result is a negative-convention norm relation.  A future
orientation lemma, if needed, should translate this convention explicitly.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### K2-5: Stickelberger principal generator as weighted Galois sum -/



/-! ### K2-6: conditional unit stripping -/









/-! ### Positive-orientation K2-6 for reciprocal Φ data -/









/-! ### Terminal signed K-chain endpoint -/






/-! ### Signed Kelly is enough for singular numerators -/






end Furtwaengler

end BernoulliRegular

end
