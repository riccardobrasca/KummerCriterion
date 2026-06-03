module

public import KummerCriterion.CyclotomicUnits.KummerLogMatrix
public import Mathlib.LinearAlgebra.SModEq.Pow
public import KummerCriterion.LehmerVandiver.PrimaryUnits.Part1
public import KummerCriterion.LehmerVandiver.PrimaryUnits.Part2
public import KummerCriterion.LehmerVandiver.PrimaryUnits.Part3
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import KummerCriterion.LehmerVandiver.Primary
public import KummerCriterion.UnitQuotient.DeltaAction
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import KummerCriterion.Reflection.ResidueSymbol.Stickelberger
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.Fintype.Units
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Ring.Associated
public import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.ZMod.Units
public import KummerCriterion.TotallyRealSubfield.Conjugation
public import KummerCriterion.UnitQuotient.ConjugationTrace
public import KummerCriterion.Reflection.ResidueSymbol.PrincipalUnitFactor

/-!
# Trace source for the Kummer logarithm columns

This file proves the honest finite-quotient trace/augmentation input for the
Kummer logarithm columns: the product of all cyclotomic conjugates of the
powered real cyclotomic unit has norm one, hence the finite same-prime
logarithms of those conjugates sum to zero.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open KummerCriterion.Reflection.Local
open KummerCriterion.Furtwaengler.KummerArtinHasse
open scoped BigOperators NumberField

namespace KummerCriterion
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace KummerLogTrace

variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
theorem dworkParameterPowerLinearMap_repr
    (x : DworkCompleteIntegerRing p K) :
    dworkParameterPowerLinearMap p K ((dworkParameterPowerBasis p K).repr x) = x := by
  simpa [dworkParameterPowerLinearMap_apply, dworkParameterPowerBasis_apply] using
    (dworkParameterPowerBasis p K).sum_repr x

omit [NumberField.IsCMField K] in
theorem dworkEvenPowerLinearMap_repr
    (hp_two : 2 < p) (x : dworkFixedSubalgebra p K) :
    dworkEvenPowerLinearMap (p := p) (K := K) hp_two
        ((dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr x) = x := by
  rw [dworkFixedEvenPowerBasis]
  exact LinearEquiv.apply_symm_apply
    (LinearEquiv.ofBijective
      (dworkEvenPowerLinearMap (p := p) (K := K) hp_two)
      (dworkEvenPowerLinearMap_bijective (p := p) (K := K) hp_two)) x

end KummerLogTrace

/-- The concrete logarithm vector produced from the selected real cyclotomic
units by the same-prime finite logarithm construction in the Dwork completion. -/
noncomputable def concreteKummerLogVector
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) :
    KummerLogVector (p := p) (K := K) :=
  fun a => kummerLogFixedColumn (p := p) (K := K) hp_three a

/-- The reduced Kummer coefficient of the concrete logarithm vector is the
mod-`p` reduction of the matching even-power Dwork coordinate. -/
theorem concreteKummerLogCoeff_eq
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogCoeff (p := p) (K := K) hp_five
        (concreteKummerLogVector (p := p) (K := K) hp_three) j a =
      rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
          (kummerLogFixedColumn (p := p) (K := K) hp_three a)
          (kummerLogEvenPowerIndex (p := p) hp_five j)) :=
  rfl

/-- The concrete coefficient matrix obtained from the completed logarithm
columns. -/
noncomputable def concreteKummerLogMatrix
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) :
    Matrix (Fin (kummerLogRank p)) (Fin (kummerLogRank p)) (ZMod p) :=
  kummerLogMatrix (p := p) (K := K) hp_five
    (concreteKummerLogVector (p := p) (K := K) hp_three)

@[simp]
theorem concreteKummerLogMatrix_apply
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a =
      kummerLogCoeff (p := p) (K := K) hp_five
        (concreteKummerLogVector (p := p) (K := K) hp_three) j a :=
  rfl

end CyclotomicUnits
end KummerCriterion

end
