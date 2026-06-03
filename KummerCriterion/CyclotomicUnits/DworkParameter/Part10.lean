module

public import KummerCriterion.CyclotomicUnits.DworkParameter.Part9
public import KummerCriterion.CyclotomicUnits.DworkParameter.Part8
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open scoped NumberField
open PowerSeries

namespace KummerCriterion
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

theorem dworkParameter_mul_pow_pred_add_p_mul_tailUnit_eq_zero
    (hp_two : 2 < p) :
    dworkParameter p K *
        (dworkParameter p K ^ (p - 1) +
          (p : DworkCompleteIntegerRing p K) *
            artinHasseTailUnit (p := p) (K := K) hp_two) = 0 := by
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _
  | succ N =>
      cases N with
      | zero =>
          rw [map_mul, dworkParameter_evalₐ_one]
          simp
      | succ N =>
          have hfinite :=
            dworkParameterFinite_corrected_factor_eq_zero
              (p := p) (K := K) (N := N + 1) (Nat.succ_pos N)
          rw [map_mul, map_add, map_pow, map_mul, map_natCast,
            dworkParameter_evalₐ, artinHasseTailUnit_evalₐ_succ]
          exact hfinite

theorem dworkParameter_pow_pred_eq_neg_p_mul_tailUnit
    (hp_two : 2 < p) :
    dworkParameter p K ^ (p - 1) =
      -(p : DworkCompleteIntegerRing p K) *
        artinHasseTailUnit (p := p) (K := K) hp_two := by
  have hinside :
      dworkParameter p K ^ (p - 1) +
        (p : DworkCompleteIntegerRing p K) *
          artinHasseTailUnit (p := p) (K := K) hp_two = 0 :=
    dworkParameter_mul_eq_zero (p := p) (K := K)
      (dworkParameter_mul_pow_pred_add_p_mul_tailUnit_eq_zero
        (p := p) (K := K) hp_two)
  simpa [neg_mul] using eq_neg_of_add_eq_zero_left hinside

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end KummerCriterion

end
