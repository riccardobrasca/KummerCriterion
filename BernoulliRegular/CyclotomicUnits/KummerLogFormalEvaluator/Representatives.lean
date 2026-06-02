import BernoulliRegular.CyclotomicUnits.KummerLogCoefficient

/-!
# Formal-to-finite evaluator bridge for Kummer logarithm coefficients

This file is the home for the remaining CU-11f2b work: turning the formal
normalized Artin-Hasse logarithm into the finite same-prime Dwork quotient
coefficient.  The coefficient-extraction API already lives in
`KummerLogCoefficient`; this file keeps the evaluator proof separated so that
the coefficient file stays focused and below the route line limit.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The selected Kummer column index is a nonzero residue modulo `p`. -/
theorem kummerLogColumnIndex_zmod_ne_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ≠ 0 := by
  intro hzero
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  have hk_pos : 0 < k := by
    have hk_two := kummerLogColumnIndex_two_le (p := p) hp_three a
    omega
  have hk_lt : k < p := kummerLogColumnIndex_lt_p (p := p) hp_three a
  have hp_dvd : p ∣ k := by
    simpa [k] using (ZMod.natCast_eq_zero_iff k p).mp hzero
  have hp_le : p ≤ k := Nat.le_of_dvd hk_pos hp_dvd
  omega

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The Kummer column residue as a cyclotomic Galois-group element. -/
noncomputable def kummerLogColumnDelta
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    CyclotomicUnitDelta p :=
  Units.mk0
    (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
    (kummerLogColumnIndex_zmod_ne_zero (p := p) hp_three a)

end CyclotomicUnits
end BernoulliRegular

end
