module

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
public import KummerCriterion.Reflection.ResidueSymbol.Furtwaengler.Stickelberger.Part1
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
public import KummerCriterion.UnitQuotient.FreeLatticeComparison.ConjugationTrace

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace KummerCriterion

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Conjugation norm of the actual Φ product -/

/-! ### Stickelberger principal generator under complex conjugation -/

/-- In an odd cyclotomic field, complex conjugation on `𝓞 K` is the
cyclotomic automorphism indexed by `-1`.

The proof compares the two rational Galois automorphisms on the field and
then restricts to the ring of integers. -/
theorem ringOfIntegersComplexConj_eq_cyclotomicRingOfIntegersEquiv_neg_one
    [IsCMField K] (hp_gt_two : 2 < p) (x : 𝓞 K) :
    ringOfIntegersComplexConj K x =
      cyclotomicRingOfIntegersEquiv (p := p) K (-1) x := by
  symm
  apply RingOfIntegers.ext
  change cyclotomicSigmaOfUnit (p := p) K (-1) (x : K) =
    complexConj K (x : K)
  rw [cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal (p := p) (K := K) hp_gt_two]
  rfl

/-! ### Stickelberger norm as the integer norm -/

end Furtwaengler

end KummerCriterion

end

end
