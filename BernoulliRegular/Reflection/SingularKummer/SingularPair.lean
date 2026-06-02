module

public import Mathlib.Algebra.Exact
public import Mathlib.RingTheory.ClassGroup

/-!
# Singular Kummer: singular pairs

This file begins the formal singular-group construction in a choice-free form.

Instead of immediately quotienting singular numbers modulo global `p`-th
powers, we first use *singular pairs*

```text
(I, alpha),    (alpha) = I^p,
```

where `I` is an invertible fractional ideal and `alpha` is a nonzero element of
the fraction field.  Such a pair maps canonically to the class of `I`, and that
class is killed by `p`.

This is the formal core of the map from singular data to `A[p]`.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- A singular pair is a fractional ideal `I` together with a generator
`alpha` of `I^p`. -/
def singularPairSubgroup (p : ℕ) : Subgroup ((FractionalIdeal R⁰ K)ˣ × Kˣ) where
  carrier := {x | toPrincipalIdeal R K x.2 = x.1 ^ p}
  one_mem' := by
    simp
  mul_mem' := by
    intro x y hx hy
    change toPrincipalIdeal R K (x.2 * y.2) = (x.1 * y.1) ^ p
    rw [map_mul, hx, hy, mul_pow]
  inv_mem' := by
    intro x hx
    change toPrincipalIdeal R K x.2⁻¹ = x.1⁻¹ ^ p
    rw [map_inv, hx, inv_pow]

/-- The group of singular pairs `(I, alpha)` with `(alpha) = I^p`. -/
abbrev SingularPair (p : ℕ) : Type _ :=
  singularPairSubgroup R K p

namespace SingularPair

variable {R K}
variable {p : ℕ}

/-- The fractional ideal in a singular pair. -/
def ideal (s : SingularPair R K p) : (FractionalIdeal R⁰ K)ˣ :=
  s.1.1

/-- The nonzero generator in a singular pair. -/
def generator (s : SingularPair R K p) : Kˣ :=
  s.1.2

/-- The defining relation `(generator s) = (ideal s)^p`. -/
theorem principal_eq_ideal_pow (s : SingularPair R K p) :
    toPrincipalIdeal R K (generator s) = ideal s ^ p :=
  s.2





end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
