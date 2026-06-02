module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelCoefficientReduction
public import BernoulliRegular.Characters

/-!
# Singular Kummer: finite-level Teichmuller character lift

This file constructs the finite-level character lift used by the exact
idempotent argument.  The lift is obtained by taking the `p`-adic
Teichmuller unit and reducing it modulo `p^N`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelCharacterLift

open BernoulliRegular.Reflection.SingularKummer.FiniteLevelCoefficientReduction

variable {p : ℕ} [Fact p.Prime]











variable {A : Type*} [AddCommGroup A] [Finite A]




namespace FinitePrimaryBridge

open ElementaryQuotientComponent
open FiniteLevelProjectionBridge
open ProjectedSubgroupComparison
open TorsionComponent

variable {A : Type*} [AddCommGroup A] [Finite A]











end FinitePrimaryBridge

end FiniteLevelCharacterLift

end SingularKummer
end Reflection
end BernoulliRegular

end

end
