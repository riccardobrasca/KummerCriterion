module

public import KummerCriterion.CyclotomicUnits.KummerLogMatrix
public import KummerCriterion.CyclotomicUnits.DworkParameter.Part14
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

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
