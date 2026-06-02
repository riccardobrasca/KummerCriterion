module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison
public import Mathlib.LinearAlgebra.Projection

/-!
# Unit quotients: ranges of free-unit character projectors

This file continues `REF-07c6c2b`.  The actual reduced free-unit quotient has
character idempotent projectors for the factored action of `Delta / {±1}`.
Here we prove that these projectors are precisely the projections onto the
actual character eigenspaces.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite

private theorem LinearMap.trace_eq_finrank_range_of_isIdempotentElem
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : Module.End F V) (he : IsIdempotentElem e) :
    LinearMap.trace F V e = (Module.finrank F (LinearMap.range e) : F) := by
  classical
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    LinearMap.IsIdempotentElem.isProj_range e he
  calc
    LinearMap.trace F V e =
        LinearMap.trace F V
          (((LinearMap.range e).prodEquivOfIsCompl (LinearMap.ker e) hproj.isCompl).conj
            (LinearMap.prodMap LinearMap.id 0)) :=
          congrArg (LinearMap.trace F V)
            (LinearMap.IsProj.eq_conj_prodMap hproj)
    _ = LinearMap.trace F ((LinearMap.range e) × (LinearMap.ker e))
          (LinearMap.prodMap LinearMap.id 0) := by
          rw [LinearMap.trace_conj']
    _ = (Module.finrank F (LinearMap.range e) : F) := by
          rw [LinearMap.trace_prodMap']
          simp

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]










end BernoulliRegular

end
