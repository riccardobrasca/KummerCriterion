module

public import BernoulliRegular.UnitQuotient.Torsion
public import BernoulliRegular.Idempotents
public import Mathlib.Data.ZMod.Basic

/-!
# Unit quotients: power quotients and `Δ`-components

This file is the `T040b` layer.  It defines the quotient `E / E^(p^N)` for
`E = 𝒪_Kˣ`, records the exponent-killing lemma for the quotient map, and
packages the `Δ = (ZMod p)ˣ`-component size data used by reflection.

The component decomposition is kept data-driven: later files can instantiate
the supplied components with the intrinsic idempotent construction, while the
reflection layer can already consume stable character-tagged subgroups and
their computed cardinal exponents.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p N : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]

/-- The Galois character group `Δ = (ZMod p)ˣ` indexing unit-quotient
components. -/
abbrev CyclotomicUnitDelta : Type :=
  (ZMod p)ˣ

/-- The subgroup `E^(p^N)` of `p^N`-th powers in the unit group. -/
abbrev CyclotomicUnitPowerSubgroup : Subgroup (CyclotomicUnitGroup K) :=
  (powMonoidHom (p ^ N) : CyclotomicUnitGroup K →* CyclotomicUnitGroup K).range

/-- The unit power quotient `E / E^(p^N)`. -/
abbrev CyclotomicUnitPowerQuotient : Type _ :=
  CyclotomicUnitGroup K ⧸ CyclotomicUnitPowerSubgroup (p := p) (N := N) K

/-- The quotient map `E → E / E^(p^N)`. -/
def cyclotomicUnitPowerClass :
    CyclotomicUnitGroup K →* CyclotomicUnitPowerQuotient (p := p) (N := N) K :=
  QuotientGroup.mk' (CyclotomicUnitPowerSubgroup (p := p) (N := N) K)


/-- The quotient map kills `p^N`-th powers. -/
theorem cyclotomicUnitPowerClass_pow_eq_one (u : CyclotomicUnitGroup K) :
    cyclotomicUnitPowerClass (p := p) (N := N) K (u ^ (p ^ N)) = 1 :=
  (QuotientGroup.eq_one_iff (N := CyclotomicUnitPowerSubgroup (p := p) (N := N) K)
    (u ^ (p ^ N))).2 ⟨u, rfl⟩

/-- Every element of `E / E^(p^N)` is killed by `p^N`. -/
theorem cyclotomicUnitPowerQuotient_pow_eq_one
    (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    x ^ (p ^ N) = 1 := by
  refine QuotientGroup.induction_on x fun u => ?_
  rw [← QuotientGroup.mk_pow]
  exact cyclotomicUnitPowerClass_pow_eq_one (p := p) (N := N) K u

/-- A declared action of `Δ = (ZMod p)ˣ` on the unit power quotient. -/
structure CyclotomicUnitQuotientDeltaAction where
  toMulAut : CyclotomicUnitDelta p →*
    MulAut (CyclotomicUnitPowerQuotient (p := p) (N := N) K)

namespace CyclotomicUnitQuotientDeltaAction

variable {p N K}

/-- Apply the declared `Δ`-action. -/
def act (A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K)
    (a : CyclotomicUnitDelta p)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    CyclotomicUnitPowerQuotient (p := p) (N := N) K :=
  A.toMulAut a x




end CyclotomicUnitQuotientDeltaAction

/-- A character-tagged subgroup of `E/E^(p^N)`, stable under the declared
`Δ`-action, with its computed cardinal exponent. -/
structure CyclotomicUnitQuotientComponent
    (A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K) where

namespace CyclotomicUnitQuotientComponent

variable {p N K}
variable {A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K}





end CyclotomicUnitQuotientComponent

/-- The full character-component size package for `E/E^(p^N)`.

The functions `torsionContribution` and `freeContribution` separate the
roots-of-unity contribution from the free-unit contribution; the exponent
formula records the effect of quotienting the free part by `p^N`. -/
structure CyclotomicUnitQuotientComponentStructure where

namespace CyclotomicUnitQuotientComponentStructure

variable {p N K}



end CyclotomicUnitQuotientComponentStructure

end BernoulliRegular
