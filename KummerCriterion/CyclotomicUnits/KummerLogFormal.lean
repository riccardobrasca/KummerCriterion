module

public import FltRegular.NumberTheory.Cyclotomic.CyclRat
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.Log
import KummerCriterion.KummerCongruence.BernoulliGeneralized
import KummerCriterion.Reflection.ResidueSymbol.DworkFactorization.FiniteArtinHasseFormal
import KummerCriterion.Reflection.ResidueSymbol.DworkFactorization.FiniteLogFormal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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

/-!
# Formal Kummer logarithm series

This file starts the purely formal coefficient calculation used by the
cyclotomic-units route. The power-series variable is `T`; the scalar `X`
lives as a polynomial coefficient, so the formal Kummer logarithm is an
element of `ℚ[X]⟦T⟧`.

No analytic `p`-adic logarithm is used here. The only logarithm below is
`PowerSeries.logOf`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators PowerSeries

namespace KummerCriterion
namespace CyclotomicUnits

/-- The ordinary formal exponential numerator `(exp(T)-1)/T`. This is used
as the low-degree model for the Artin-Hasse normalized numerator. -/
def formalExpNormalizedMinusOne : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (PowerSeries.coeff (R := ℚ) (n + 1)) (PowerSeries.exp ℚ)

@[simp]
theorem formalExpNormalizedMinusOne_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℚ) n) formalExpNormalizedMinusOne =
      (PowerSeries.coeff (R := ℚ) (n + 1)) (PowerSeries.exp ℚ) := by
  simp [formalExpNormalizedMinusOne]

@[simp]
theorem formalExpNormalizedMinusOne_constantCoeff :
    PowerSeries.constantCoeff formalExpNormalizedMinusOne = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [formalExpNormalizedMinusOne]

theorem exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne :
    PowerSeries.exp ℚ - 1 =
      PowerSeries.X * formalExpNormalizedMinusOne := by
  simpa [formalExpNormalizedMinusOne] using
    (PowerSeries.sub_const_eq_X_mul_shift (PowerSeries.exp ℚ))

theorem bernoulliPowerSeries_mul_formalExpNormalizedMinusOne :
    _root_.bernoulliPowerSeries ℚ * formalExpNormalizedMinusOne = 1 := by
  apply PowerSeries.X_mul_cancel
  calc
    PowerSeries.X * (_root_.bernoulliPowerSeries ℚ * formalExpNormalizedMinusOne)
        = _root_.bernoulliPowerSeries ℚ *
            (PowerSeries.X * formalExpNormalizedMinusOne) := by ring
    _ = _root_.bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) := by
          rw [← exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne]
    _ = PowerSeries.X := by
          rw [_root_.bernoulliPowerSeries_mul_exp_sub_one]
    _ = PowerSeries.X * (1 : PowerSeries ℚ) := by rw [mul_one]

theorem derivative_logOf_formalExpNormalizedMinusOne_mul_self :
    (d⁄dX ℚ (PowerSeries.logOf formalExpNormalizedMinusOne)) *
        formalExpNormalizedMinusOne =
      d⁄dX ℚ formalExpNormalizedMinusOne := by
  let N : PowerSeries ℚ := formalExpNormalizedMinusOne
  have hN0 : PowerSeries.constantCoeff (N - 1) = 0 := by
    simp [N]
  have hsubst : PowerSeries.HasSubst (N - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hN0
  have hgeom :
      PowerSeries.subst (N - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) * N = 1 := by
    have h :=
      Furtwaengler.FiniteLogFormal.subst_deriv_log_mul_one_add (A := ℚ) hsubst
    simpa [N, sub_eq_add_neg, add_assoc] using h
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst hsubst]
  have hderiv_sub : d⁄dX ℚ (N - 1) = d⁄dX ℚ N := by simp
  calc
    (PowerSeries.subst (N - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) *
          d⁄dX ℚ (N - 1)) * N
        =
          (PowerSeries.subst (N - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) * N) *
            d⁄dX ℚ N := by
          rw [hderiv_sub]
          ring
    _ = 1 * d⁄dX ℚ N := by rw [hgeom]
    _ = d⁄dX ℚ N := by rw [one_mul]

theorem X_mul_derivative_logOf_formalExpNormalizedMinusOne :
    PowerSeries.X * (d⁄dX ℚ (PowerSeries.logOf formalExpNormalizedMinusOne)) =
      PowerSeries.X + _root_.bernoulliPowerSeries ℚ - 1 := by
  let N : PowerSeries ℚ := formalExpNormalizedMinusOne
  let B : PowerSeries ℚ := _root_.bernoulliPowerSeries ℚ
  let D : PowerSeries ℚ := d⁄dX ℚ (PowerSeries.logOf N)
  have hBN : B * N = 1 := by
    simpa [B, N] using bernoulliPowerSeries_mul_formalExpNormalizedMinusOne
  have hNB : N * B = 1 := by rw [mul_comm, hBN]
  have hDN : D * N = d⁄dX ℚ N := by
    simpa [D, N] using derivative_logOf_formalExpNormalizedMinusOne_mul_self
  have hD_eq : D = B * (d⁄dX ℚ N) := by
    calc
      D = D * 1 := by rw [mul_one]
      _ = D * (N * B) := by rw [hNB]
      _ = (D * N) * B := by ring
      _ = (d⁄dX ℚ N) * B := by rw [hDN]
      _ = B * (d⁄dX ℚ N) := by ring
  have hN_XdN :
      N + PowerSeries.X * (d⁄dX ℚ N) = PowerSeries.exp ℚ := by
    calc
      N + PowerSeries.X * (d⁄dX ℚ N)
          = d⁄dX ℚ (PowerSeries.X * N) := by
            rw [Derivation.leibniz]
            simp
            ring
      _ = d⁄dX ℚ (PowerSeries.exp ℚ - 1) := by
            rw [← exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne]
      _ = PowerSeries.exp ℚ := by
            simp [PowerSeries.derivative_exp]
  have hBexp : B * PowerSeries.exp ℚ = PowerSeries.X + B := by
    calc
      B * PowerSeries.exp ℚ
          = B * ((PowerSeries.exp ℚ - 1) + 1) := by ring
      _ = B * (PowerSeries.exp ℚ - 1) + B := by ring
      _ = B * (PowerSeries.X * N) + B := by
            rw [exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne]
      _ = PowerSeries.X * (B * N) + B := by ring
      _ = PowerSeries.X + B := by rw [hBN, mul_one]
  calc
    PowerSeries.X * D
        = PowerSeries.X * (B * (d⁄dX ℚ N)) := by rw [hD_eq]
    _ = B * (PowerSeries.X * (d⁄dX ℚ N)) := by ring
    _ = B * (PowerSeries.exp ℚ - N) := by
          have hsub : PowerSeries.X * (d⁄dX ℚ N) = PowerSeries.exp ℚ - N := by
            rw [← hN_XdN]
            abel
          rw [hsub]
    _ = B * PowerSeries.exp ℚ - B * N := by ring
    _ = (PowerSeries.X + B) - 1 := by rw [hBexp, hBN]
    _ = PowerSeries.X + B - 1 := by ring

theorem coeff_logOf_formalExpNormalizedMinusOne_eq_bernoulli
    {n : ℕ} (hn : 1 < n) :
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.logOf formalExpNormalizedMinusOne) =
      (_root_.bernoulli n : ℚ) / ((n : ℚ) * (Nat.factorial n : ℚ)) := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hn_ne_zero : n ≠ 0 := Nat.ne_of_gt hnpos
  have hn_ne_one : n ≠ 1 := by omega
  have hcoeff :=
    congrArg (PowerSeries.coeff (R := ℚ) n)
      X_mul_derivative_logOf_formalExpNormalizedMinusOne
  rw [show n = (n - 1) + 1 by omega, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative] at hcoeff
  have hnsub : n - 1 + 1 = n := by omega
  rw [hnsub] at hcoeff
  have hncast : ((n - 1 : ℕ) : ℚ) + 1 = (n : ℚ) := by
    exact_mod_cast hnsub
  rw [hncast] at hcoeff
  have hcoeff' :
      (PowerSeries.coeff (R := ℚ) n)
          (PowerSeries.logOf formalExpNormalizedMinusOne) * (n : ℚ) =
        (_root_.bernoulli n : ℚ) / (Nat.factorial n : ℚ) := by
    simpa [_root_.bernoulliPowerSeries, PowerSeries.coeff_X, hn_ne_zero, hn_ne_one]
      using hcoeff
  calc
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.logOf formalExpNormalizedMinusOne)
        =
          ((PowerSeries.coeff (R := ℚ) n)
            (PowerSeries.logOf formalExpNormalizedMinusOne) * (n : ℚ)) / (n : ℚ) := by
          field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn_ne_zero]
    _ = ((_root_.bernoulli n : ℚ) / (Nat.factorial n : ℚ)) / (n : ℚ) := by
          rw [hcoeff']
    _ = (_root_.bernoulli n : ℚ) / ((n : ℚ) * (Nat.factorial n : ℚ)) := by
          field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn_ne_zero,
            show (Nat.factorial n : ℚ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n]

theorem coeff_pow_eq_of_coeff_eq_le
    {A : Type*} [CommSemiring A] {F G : PowerSeries A} :
    ∀ (m d : ℕ), (∀ k, k ≤ d → PowerSeries.coeff k F = PowerSeries.coeff k G) →
      PowerSeries.coeff d (F ^ m) = PowerSeries.coeff d (G ^ m)
  | 0, d, _ => by simp
  | m + 1, d, h => by
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, k⟩ hik
      have hiksum : i + k = d := Finset.mem_antidiagonal.mp hik
      have hi : i ≤ d := by omega
      have hk : k ≤ d := by omega
      change PowerSeries.coeff i (F ^ m) * PowerSeries.coeff k F =
        PowerSeries.coeff i (G ^ m) * PowerSeries.coeff k G
      rw [coeff_pow_eq_of_coeff_eq_le (m := m) (d := i)
          (fun t ht => h t (ht.trans hi)),
        h k hk]

theorem coeff_logOf_eq_of_coeff_eq_le
    {A : Type*} [CommRing A] [Algebra ℚ A] {F G : PowerSeries A} {d : ℕ}
    (hF0 : PowerSeries.constantCoeff F = 1)
    (hG0 : PowerSeries.constantCoeff G = 1)
    (hcoeff : ∀ k, k ≤ d → PowerSeries.coeff k F = PowerSeries.coeff k G) :
    PowerSeries.coeff d (PowerSeries.logOf F) =
      PowerSeries.coeff d (PowerSeries.logOf G) := by
  have hFsub0 : PowerSeries.constantCoeff (F - 1) = 0 := by simp [hF0]
  have hGsub0 : PowerSeries.constantCoeff (G - 1) = 0 := by simp [hG0]
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq]
  rw [Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
      (F - 1) hFsub0 d,
    Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
      (G - 1) hGsub0 d]
  refine Finset.sum_congr rfl ?_
  intro m hm
  congr 1
  exact coeff_pow_eq_of_coeff_eq_le (m := m) (d := d) fun k hk => by
    simp [hcoeff k hk]

/-- Reduction of a rational number modulo `p`, written using numerator and
denominator. The later coefficient theorems use separate hypotheses proving
that the denominators in question are units modulo `p`. -/
def ratReductionZMod (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p :=
  (q.num : ZMod p) / (q.den : ZMod p)

/-- The Bernoulli factor in the final formal congruence, namely the reduction
of `B_(2*j)/(2*j)` modulo `p`. -/
def bernoulliFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  ratReductionZMod p (((_root_.bernoulli (2 * j) : ℚ) / (2 * j : ℚ)))

/-- The explicit unit factor used for the coefficient convention. The
factorial is a unit in the final range `2*j <= p - 3`. -/
def kummerLogUnitFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  -(((Nat.factorial (2 * j) : ℕ) : ZMod p)⁻¹)

theorem factorial_two_mul_index_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (((Nat.factorial (2 * j) : ℕ) : ZMod p)) ≠ 0 := by
  intro hzero
  have hp_dvd : p ∣ Nat.factorial (2 * j) :=
    (ZMod.natCast_eq_zero_iff (Nat.factorial (2 * j)) p).mp hzero
  have hlt : 2 * j < p := by omega
  exact Nat.not_lt.mpr ((Nat.Prime.dvd_factorial (Fact.out : Nat.Prime p)).mp hp_dvd) hlt

theorem kummerLogUnitFactor_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    kummerLogUnitFactor p j ≠ 0 := by
  simpa [kummerLogUnitFactor] using
    (neg_ne_zero.mpr (inv_ne_zero (factorial_two_mul_index_zmod_ne_zero hj hjp)))

/-- Under the range hypotheses, the integer `2*j` is nonzero modulo
`p`. -/
theorem two_mul_index_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    ((2 * j : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hp_dvd : p ∣ 2 * j :=
    (ZMod.natCast_eq_zero_iff (2 * j) p).mp hzero
  have hpos : 0 < 2 * j := by omega
  have hp_le : p ≤ 2 * j := Nat.le_of_dvd hpos hp_dvd
  omega

/-- Under the range hypotheses, `p` does not divide the denominator of
`B_(2*j)`. -/
theorem prime_not_dvd_bernoulli_den_two_mul {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    ¬ p ∣ (_root_.bernoulli (2 * j)).den := by
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    have : 2 * j ≤ 0 := by omega
    omega
  exact KummerCriterion.prime_not_dvd_bernoulli_den_of_lt_sub_one
    (p := p) (n := 2 * j) hp_ne_two (by omega)

/-- Under the range hypotheses, the Bernoulli denominator is nonzero
modulo `p`. -/
theorem bernoulli_den_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (((_root_.bernoulli (2 * j)).den : ℕ) : ZMod p) ≠ 0 := fun hzero =>
  prime_not_dvd_bernoulli_den_two_mul hj hjp
    ((ZMod.natCast_eq_zero_iff ((_root_.bernoulli (2 * j)).den) p).mp hzero)

/-- The coefficient ring for the final mod-`p` formal Kummer coefficient. -/
abbrev KummerLogModCoeffRing (p : ℕ) : Type :=
  Polynomial (ZMod p)

/-- The reduced scalar multiplying `X^(2*j)-1` in the final mod-`p`
coefficient formula. It is the Bernoulli factor times the factorial unit
coming from the formal logarithm coefficient convention. -/
def reducedKummerLogCoeffFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  kummerLogUnitFactor p j * bernoulliFactor p j

/-- The final mod-`p` formal coefficient polynomial. -/
def formalKummerLogCoeffModP (p j : ℕ) [Fact p.Prime] :
    KummerLogModCoeffRing p :=
  Polynomial.C (reducedKummerLogCoeffFactor p j) *
    (Polynomial.X ^ (2 * j) - 1)

/-- The unit factor in the final unspecialized theorem is nonzero. -/
theorem formalKummerLogCoeffModP_unit_ne_zero
    {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    kummerLogUnitFactor p j ≠ 0 :=
  kummerLogUnitFactor_ne_zero hj hjp

/-- Evaluation of the final mod-`p` formal coefficient polynomial. -/
theorem formalKummerLogCoeffModP_eval
    (p j : ℕ) [Fact p.Prime] (x : ZMod p) :
    Polynomial.eval x (formalKummerLogCoeffModP p j) =
      (kummerLogUnitFactor p j * bernoulliFactor p j) *
        (x ^ (2 * j) - 1) := by
  simp [formalKummerLogCoeffModP, reducedKummerLogCoeffFactor]

end CyclotomicUnits
end KummerCriterion

end
