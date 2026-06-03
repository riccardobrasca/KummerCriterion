module

public import KummerCriterion.Reflection.ResidueSymbol.Stickelberger
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import KummerCriterion.Reflection.ResidueSymbol.DieudonneDwork.Part1
public import KummerCriterion.Reflection.ResidueSymbol.DieudonneDwork.Part2
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import KummerCriterion.Reflection.ResidueSymbol.ArtinHasse.Part1

/-!
# Artin-Hasse exponential power series

This file defines the Artin-Hasse log and exponential power series over `ℚ`,
indexed by a prime `r`:

* `artinHasseLogSeries r: PowerSeries ℚ` is `L_r(T) = ∑_{i ≥ 0} T^{r^i} / r^i`.
* `artinHasseExpSeries r: PowerSeries ℚ` is `E_r(T) = exp(L_r(T))`.

The "is a power of `r`" predicate is decidable via `Nat.log`: for `r ≥ 2`,
`n = r^i` for some `i ≥ 0` iff `r ^ Nat.log r n = n ∧ n ≠ 0`. (For `n = 0`,
`r ^ Nat.log r 0 = r ^ 0 = 1 ≠ 0`, so the predicate fails as expected.)

These are the building blocks of the Dwork coefficient sequence used by the
`FullTeichDworkSetup` interface in (the project's Φ/Kelly/Furtwängler
route). p-integrality of the Artin-Hasse exponential coefficients (the
substantive Dieudonné-Dwork content) is proved separately.

## References

* Alain M. Robert, *A Course in p-adic Analysis* (GTM 198, Springer 2000),
 §7.1 Definition 1, p. 187.
* Neal Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*
 (GTM 58, Springer 1984), §IV.2 Definition, p. 93.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion

namespace Furtwaengler

universe u v w

theorem artinHasseExpMinusOneSeries_isRIntegral
    (r : ℕ) [Fact (Nat.Prime r)] :
    DieudonneDwork.IsRIntegralPS r (artinHasseExpMinusOneSeries r) := by
  have hE : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral r n
  exact hE.sub (DieudonneDwork.IsRIntegralPS.one r)

theorem artinHasseExpInverseSeries_isRIntegral
    (r : ℕ) [Fact (Nat.Prime r)] :
    DieudonneDwork.IsRIntegralPS r (artinHasseExpInverseSeries r) := by
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  have hP : DieudonneDwork.IsRIntegralPS r P := by
    simpa [P] using artinHasseExpMinusOneSeries_isRIntegral r
  have hP0 : PowerSeries.constantCoeff P = 0 := by
    simp [P]
  have hinv :=
    DieudonneDwork.IsRIntegralPS.substInv_of_constantCoeff_zero_coeff_one
      (P := P) hP hP0 hcoeff
  simpa [artinHasseExpInverseSeries, P] using hinv

/-- The formal inverse identity transported through any coefficient map out
of the localized Artin-Hasse coefficient ring. -/
theorem artinHasseExpSeries_mapTo_subst_inverse
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) :
    PowerSeries.subst
        ((artinHasseExpInverseSeries_isRIntegral r).mapTo φ)
        ((show DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) from
          fun n => artinHasseExpSeries_coeff_isRIntegral r n).mapTo φ) =
      1 + (PowerSeries.X : PowerSeries A) := by
  let hE : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral r n
  let hInv : DieudonneDwork.IsRIntegralPS r (artinHasseExpInverseSeries r) :=
    artinHasseExpInverseSeries_isRIntegral r
  have hInv0 : PowerSeries.constantCoeff (artinHasseExpInverseSeries r) = 0 :=
    artinHasseExpInverseSeries_constantCoeff r
  calc
    PowerSeries.subst (hInv.mapTo φ) (hE.mapTo φ)
        = (hE.subst hInv hInv0).mapTo φ := by
          rw [hE.mapTo_subst φ hInv hInv0]
    _ =
        ((DieudonneDwork.IsRIntegralPS.one r).add (DieudonneDwork.IsRIntegralPS.X r)).mapTo φ :=
          DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq φ _ _
            (artinHasseExpSeries_subst_inverse r)
    _ = (DieudonneDwork.IsRIntegralPS.one r).mapTo φ +
          (DieudonneDwork.IsRIntegralPS.X r).mapTo φ := by
          rw [DieudonneDwork.IsRIntegralPS.mapTo_add]
    _ = 1 + (PowerSeries.X : PowerSeries A) := by
          simp

end Furtwaengler

end KummerCriterion

end
