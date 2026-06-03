module

public import Mathlib.RingTheory.Teichmuller
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import BernoulliRegular.Reflection.Local.Graded
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import BernoulliRegular.Reflection.Local.DeltaAction
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Exact
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import BernoulliRegular.UnitQuotient.Components
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Torsion
public import BernoulliRegular.Characters
public import BernoulliRegular.UnitQuotient.DeltaAction
public import BernoulliRegular.Reflection.SingularKummer.Localization

/-!
# Global lambda decomposition for the Kummer--Artin--Hasse correction

The full explicit local correction is only consumed by the global product
formula on elements of `Kˣ`.  This file gives the decomposition API for those
global field units at the distinguished cyclotomic prime:

* normalize by the explicit uniformizer `pi = zeta_p - 1`;
* convert the resulting lambda-local unit into the localized ring and then
  into the completed local unit group;
* split the completed unit into its Teichmuller residue factor and a
  principal-unit factor.

This avoids assuming that the adic completed integer ring is already known to
Lean as a DVR.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors WithZero
open NumberField IsCyclotomicExtension IsDedekindDomain

namespace BernoulliRegular

open Reflection.SingularKummer.SingularPair

namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The global integral cyclotomic uniformizer `pi = zeta_p - 1`. -/
def lambdaPiIntegral
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    𝓞 K :=
  (zeta_spec p ℚ K).toInteger - 1

@[simp]
theorem lambdaPiIntegral_ne_zero
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    lambdaPiIntegral p K ≠ 0 := by
  change (zeta_spec p ℚ K).toInteger - 1 ≠ 0
  exact (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero

/-- The explicit cyclotomic uniformizer as a global field unit. -/
def lambdaPiFieldUnit
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (lambdaPiIntegral p K))
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne
      (lambdaPiIntegral_ne_zero (p := p) (K := K)))

@[simp]
theorem lambdaPiFieldUnit_val
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    (lambdaPiFieldUnit p K : K) =
      algebraMap (𝓞 K) K (lambdaPiIntegral p K) :=
  rfl

/-- The distinguished lambda prime as a height-one prime. -/
abbrev lambdaHeightOne
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    HeightOneSpectrum (𝓞 K) :=
  Reflection.SingularKummer.SingularPair.cyclotomicLambdaHeightOne (p := p) K

/-- The explicit cyclotomic uniformizer has normalized lambda valuation
`exp (-1)`. -/
theorem lambdaPiFieldUnit_valuation
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    (lambdaHeightOne p K).valuation K (lambdaPiFieldUnit p K : K) =
      WithZero.exp (-1 : ℤ) := by
  rw [lambdaPiFieldUnit_val]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have hspan :
      (lambdaHeightOne p K).asIdeal =
        Ideal.span ({lambdaPiIntegral p K} : Set (𝓞 K)) := rfl
  exact (lambdaHeightOne p K).intValuation_singleton
    (lambdaPiIntegral_ne_zero (p := p) (K := K)) hspan

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
