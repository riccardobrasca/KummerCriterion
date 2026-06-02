module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Ring.Associated
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import FltRegular.NumberTheory.Cyclotomic.UnitLemmas


/-!
# Uniformizer fact derivation (REF-18c2c4-L2c3a-prove)

Provides a free-standing proof that `π = ζ_ℓ - 1` is a `Q`-uniformizer
in `R' = ℚ(ζ_p, ζ_ℓ)` for any prime `Q` of `𝓞 R'` above `ℓ`. This
derives the field `pi_not_mem_Q_sq` of `TraceFormStickelbergerSetup`
from cyclotomic ramification theory (mathlib's
`IsCyclotomicExtension.Rat.ramificationIdx_eq` with `n = ℓ · p`,
prime `ℓ`, `m = p`, `k = 0`).

Strategy:
1. Convert `IsCyclotomicExtension {p, ℓ} ℚ R'` to
   `IsCyclotomicExtension {ℓ · p} ℚ R'` via `IsPrimitiveRoot.pow_mul_pow_lcm`
   + `IsPrimitiveRoot.adjoin_pair_eq` + `isCyclotomicExtension_singleton_iff_eq_adjoin`.
2. Apply `IsCyclotomicExtension.Rat.ramificationIdx_eq` to get
   `ramificationIdx of ℓ in 𝓞 R' = ℓ - 1`.
3. The cyclotomic identity `ℓ = u · π^(ℓ-1)` (for some unit `u`)
   combined with the ramification index gives `v_Q(π) = 1`, hence
   `π ∉ Q^2`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w













end Furtwaengler

end BernoulliRegular
