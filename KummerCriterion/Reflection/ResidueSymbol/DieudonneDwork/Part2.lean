module

public import KummerCriterion.Reflection.ResidueSymbol.DieudonneDwork.Part1
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Data.Nat.Totient
import TauCeti.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Dieudonné-Dwork criterion for `r`-integrality of power series

The Dieudonné-Dwork criterion characterises when a formal power series with
rational coefficients has `r`-integral coefficients (denominators coprime to a
prime `r`):

> For `F ∈ 1 + T · ℚ[[T]]`, the coefficients of `F` are `r`-integral if and only
> if `F(T)^r / F(T^r) ∈ 1 + r · T · ℤ_(r)[[T]]`.

This is the substantive p-adic-algebra theorem behind the Artin-Hasse
exponential's `r`-integrality (`artinHasseExpSeries_coeff_isRIntegral` in
`ArtinHasse.lean`).

## References

* Alain M. Robert, *A Course in p-adic Analysis* (GTM 198, Springer 2000),
 §7.2 Theorem 1, pp. 188-190.
* Neal Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*
 (GTM 58, Springer 1984), §IV.2 Theorem 2, pp. 96-97.

This is a local file; a future cleanup may PR upstream.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

namespace Furtwaengler

namespace DieudonneDwork

namespace IsRIntegralPS

theorem mapTo_pow {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (k : ℕ) :
    (hF.pow k).mapTo φ = hF.mapTo φ ^ k := by
  have h : (hF.pow k).toSubringPS = hF.toSubringPS ^ k := by
    apply PowerSeries.map_injective _ (rIntegralRatSubring r).subtype_injective
    simp
  simpa only [mapTo_eq_map_toSubringPS, map_pow] using congr(PowerSeries.map φ $h)

theorem mapTo_subst {r : ℕ} {A : Type*} [CommRing A]
    (φ : rIntegralRatSubring r →+* A) {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G)
    (hG0 : PowerSeries.constantCoeff G = 0) :
    (hF.subst hG hG0).mapTo φ =
      PowerSeries.subst (hG.mapTo φ) (hF.mapTo φ) := by
  have hG0_sub : PowerSeries.constantCoeff hG.toSubringPS = 0 :=
    hG.constantCoeff_toSubringPS_eq_zero hG0
  let hsubst : PowerSeries.HasSubst hG.toSubringPS :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hG0_sub
  calc
    (hF.subst hG hG0).mapTo φ
        = PowerSeries.map φ (hF.subst hG hG0).toSubringPS := by
          rw [mapTo_eq_map_toSubringPS]
    _ = PowerSeries.map φ (PowerSeries.subst hG.toSubringPS hF.toSubringPS) := by
          rw [toSubringPS_subst hF hG hG0]
    _ = PowerSeries.subst (PowerSeries.map φ hG.toSubringPS)
          (PowerSeries.map φ hF.toSubringPS) := by
          simpa using! PowerSeries.map_subst (h := φ) hsubst hF.toSubringPS
    _ = PowerSeries.subst (hG.mapTo φ) (hF.mapTo φ) := by
          rw [← mapTo_eq_map_toSubringPS φ hG, ← mapTo_eq_map_toSubringPS φ hF]

theorem toZModPS_sub {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    (hF.sub hG).toZModPS = hF.toZModPS - hG.toZModPS := by
  exact mapTo_sub (rIntegralToZMod r) hF hG

theorem toZModPS_pow {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F)
    (k : ℕ) :
    (hF.pow k).toZModPS = hF.toZModPS ^ k := by
  exact mapTo_pow (rIntegralToZMod r) hF k

theorem toZModPS_subst_X_pow {r k : ℕ} (hk : k ≠ 0) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) :
    (hF.subst_X_pow hk).toZModPS =
      PowerSeries.subst (PowerSeries.X ^ k) hF.toZModPS := by
  ext n
  by_cases hkn : k ∣ n
  · simp [toZModPS, PowerSeries.coeff_subst_X_pow, hk, hkn, IsRIntegralRat.toZMod]
  · simp [toZModPS, PowerSeries.coeff_subst_X_pow, hk, hkn, IsRIntegralRat.toZMod]

/-- Freshman's dream for `r`-integral power series: if `F ∈ ℚ[[T]]` has
`r`-integral coefficients, then every coefficient of `F ^ r - F(T ^ r)` is an
`r`-multiple in the localized sense encoded by `IsRIntegralRat`. -/
theorem pow_r_sub_subst_X_pow_r_in_r_smul
    (r : ℕ) [Fact (Nat.Prime r)] {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (n : ℕ) :
    ∃ q : ℚ, IsRIntegralRat r q ∧
      (PowerSeries.coeff (R := ℚ) n)
        (F ^ r - PowerSeries.subst (PowerSeries.X ^ r) F) = (r : ℚ) * q := by
  let hr : r ≠ 0 := (Fact.out : Nat.Prime r).ne_zero
  let hSub : IsRIntegralPS r (PowerSeries.subst (PowerSeries.X ^ r) F) :=
    hF.subst_X_pow hr
  let hDiff : IsRIntegralPS r (F ^ r - PowerSeries.subst (PowerSeries.X ^ r) F) :=
    (hF.pow r).sub hSub
  have hfresh :
      PowerSeries.subst (PowerSeries.X ^ r) hF.toZModPS = hF.toZModPS ^ r := by
    rw [← PowerSeries.expand_apply (p := r) (hp := hr)]
    exact powerSeries_expand_zmod hF.toZModPS
  have hred : hDiff.toZModPS = 0 := by
    calc
      hDiff.toZModPS
          = (hF.pow r).toZModPS - hSub.toZModPS := toZModPS_sub (hF.pow r) hSub
      _ = hF.toZModPS ^ r -
            PowerSeries.subst (PowerSeries.X ^ r) hF.toZModPS := by
              rw [toZModPS_pow hF r, toZModPS_subst_X_pow hr hF]
      _ = 0 := by rw [hfresh, sub_self]
  have hz :
      IsRIntegralRat.toZMod
        ((PowerSeries.coeff (R := ℚ) n)
          (F ^ r - PowerSeries.subst (PowerSeries.X ^ r) F))
        (hDiff n) = 0 := by
    have hc := congrArg ((PowerSeries.coeff (R := ZMod r) n)) hred
    simpa [hDiff] using hc
  exact IsRIntegralRat.exists_eq_natCast_mul_of_toZMod_eq_zero (hDiff n) hz

private theorem coeff_pow_add_C_mul_X_pow
    {A : PowerSeries ℚ} {n k : ℕ} (hn : 0 < n)
    (hA0 : PowerSeries.constantCoeff A = 1) (c : ℚ) :
    (PowerSeries.coeff (R := ℚ) n) ((A + PowerSeries.C c * PowerSeries.X ^ n) ^ k) =
      (PowerSeries.coeff (R := ℚ) n) (A ^ k) + (k : ℚ) * c := by
  classical
  cases k with
  | zero =>
      simp [PowerSeries.coeff_one, hn.ne']
  | succ k =>
      let y : PowerSeries ℚ := PowerSeries.C c * PowerSeries.X ^ n
      change
        (PowerSeries.coeff (R := ℚ) n) ((A + y) ^ (k + 1)) =
          (PowerSeries.coeff (R := ℚ) n) (A ^ (k + 1)) + ((k + 1 : ℕ) : ℚ) * c
      let term : ℕ → ℚ := fun m =>
        (PowerSeries.coeff (R := ℚ) n)
          (A ^ m * y ^ ((k + 1) - m) *
            PowerSeries.C (((k + 1).choose m : ℕ) : ℚ))
      have hbinom :
          (PowerSeries.coeff (R := ℚ) n) ((A + y) ^ (k + 1)) =
            Finset.sum (Finset.range (k + 2)) term := by
        have h :=
          congrArg ((PowerSeries.coeff (R := ℚ) n))
            (add_pow A y (k + 1))
        simpa [term, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      have htop_mem : k + 1 ∈ Finset.range (k + 2) := by
        simp
      have hmid_mem : k ∈ (Finset.range (k + 2)).erase (k + 1) := by
        simp
      have htop :
          term (k + 1) =
            (PowerSeries.coeff (R := ℚ) n) (A ^ (k + 1)) := by
        simp [term]
      have hmid : term k = ((k + 1 : ℕ) : ℚ) * c := by
        have hsub : (k + 1) - k = 1 := by
          rw [Nat.add_comm]
          exact Nat.add_sub_cancel 1 k
        have hchoose_nat : (k + 1).choose k = k + 1 :=
          Nat.choose_succ_self_right k
        have hchoose_rat : (((k + 1).choose k : ℕ) : ℚ) = (k + 1 : ℚ) := by
          exact_mod_cast hchoose_nat
        have hx :
            (PowerSeries.coeff (R := ℚ) n) (A ^ k * y) = c := by
          rw [show A ^ k * y = (A ^ k * PowerSeries.C c) * PowerSeries.X ^ n by
            simp [y, mul_assoc]]
          simpa [PowerSeries.coeff_zero_eq_constantCoeff, hA0] using
            (PowerSeries.coeff_mul_X_pow (A ^ k * PowerSeries.C c) n 0)
        calc
          term k =
              (PowerSeries.coeff (R := ℚ) n)
                (A ^ k * y * PowerSeries.C (((k + 1).choose k : ℕ) : ℚ)) := by
                simp only [term, hsub, pow_one]
          _ =
              (PowerSeries.coeff (R := ℚ) n) (A ^ k * y) *
                (((k + 1).choose k : ℕ) : ℚ) := by
                rw [PowerSeries.coeff_mul_C]
          _ = c * (k + 1 : ℚ) := by rw [hx, hchoose_rat]
          _ = ((k + 1 : ℕ) : ℚ) * c := by
                rw [show ((k + 1 : ℕ) : ℚ) = (k : ℚ) + 1 by norm_num]
                ring
      have hzero :
          ∀ m ∈ (Finset.range (k + 2)).erase (k + 1), m ≠ k → term m = 0 := by
        intro m hm hmk
        have hm_range : m < k + 2 :=
          Finset.mem_range.mp ((Finset.mem_erase.mp hm).2)
        have hm_top : m ≠ k + 1 := (Finset.mem_erase.mp hm).1
        have he : 1 < (k + 1) - m := by
          have hm_le_top : m ≤ k + 1 := Nat.le_of_lt_succ hm_range
          have hm_lt_top : m < k + 1 := Nat.lt_of_le_of_ne hm_le_top hm_top
          have hm_le_k : m ≤ k := Nat.le_of_lt_succ hm_lt_top
          have hm_lt_k : m < k := Nat.lt_of_le_of_ne hm_le_k hmk
          have hsucc : m + 1 ≤ k := Nat.succ_le_of_lt hm_lt_k
          have hsumle : 2 + m ≤ k + 1 := by
            have h := Nat.succ_le_succ hsucc
            simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
          have hle : 2 ≤ (k + 1) - m :=
            (Nat.le_sub_iff_add_le hm_le_top).2 hsumle
          exact lt_of_lt_of_le (by decide : 1 < 2) hle
        have hgt : n < n * ((k + 1) - m) := by
          have hmul := Nat.mul_lt_mul_of_pos_left he hn
          simpa using hmul
        have hy_pow :
            y ^ ((k + 1) - m) =
              PowerSeries.C (c ^ ((k + 1) - m)) *
                PowerSeries.X ^ (n * ((k + 1) - m)) := by
          simp [y, mul_pow, pow_mul]
        have hx :
            (PowerSeries.coeff (R := ℚ) n)
              (A ^ m * (PowerSeries.C (c ^ ((k + 1) - m)) *
                PowerSeries.X ^ (n * ((k + 1) - m)))) = 0 := by
          rw [← mul_assoc, PowerSeries.coeff_mul_X_pow']
          simp [not_le_of_gt hgt]
        calc
          term m =
              (PowerSeries.coeff (R := ℚ) n)
                (A ^ m * y ^ ((k + 1) - m) *
                  PowerSeries.C (((k + 1).choose m : ℕ) : ℚ)) := rfl
          _ =
              (PowerSeries.coeff (R := ℚ) n)
                (A ^ m * (PowerSeries.C (c ^ ((k + 1) - m)) *
                  PowerSeries.X ^ (n * ((k + 1) - m))) *
                    PowerSeries.C (((k + 1).choose m : ℕ) : ℚ)) := by
                rw [hy_pow]
          _ =
              (PowerSeries.coeff (R := ℚ) n)
                (A ^ m * (PowerSeries.C (c ^ ((k + 1) - m)) *
                  PowerSeries.X ^ (n * ((k + 1) - m)))) *
                    (((k + 1).choose m : ℕ) : ℚ) := by
                rw [PowerSeries.coeff_mul_C]
          _ = 0 := by rw [hx, zero_mul]
      calc
        (PowerSeries.coeff (R := ℚ) n) ((A + y) ^ (k + 1))
            = Finset.sum (Finset.range (k + 2)) term := hbinom
        _ = term (k + 1) + Finset.sum ((Finset.range (k + 2)).erase (k + 1)) term := by
              rw [Finset.add_sum_erase _ _ htop_mem]
        _ = term (k + 1) + term k := by
              rw [Finset.sum_eq_single_of_mem k hmid_mem hzero]
        _ = (PowerSeries.coeff (R := ℚ) n) (A ^ (k + 1)) + ((k + 1 : ℕ) : ℚ) * c := by
              rw [htop, hmid]

private theorem coeff_pow_eq_trunc_add
    {F : PowerSeries ℚ} {n k : ℕ} (hn : 0 < n)
    (hF0 : PowerSeries.constantCoeff F = 1) :
    (PowerSeries.coeff (R := ℚ) n) (F ^ k) =
      (PowerSeries.coeff (R := ℚ) n)
        (((PowerSeries.trunc n F : Polynomial ℚ) : PowerSeries ℚ) ^ k) +
        (k : ℚ) * (PowerSeries.coeff (R := ℚ) n) F := by
  calc
    PowerSeries.coeff n (F ^ k) =
        PowerSeries.coeff n ((PowerSeries.trunc (n + 1) F : PowerSeries ℚ) ^ k) :=
      PowerSeries.coeff_eq_of_trunc_eq
        (PowerSeries.trunc_trunc_pow F (n + 1) k).symm (Nat.lt_succ_self n)
    _ = _ := by
      rw [PowerSeries.trunc_succ, Polynomial.coe_add, Polynomial.coe_monomial,
        PowerSeries.monomial_eq_C_mul_X_pow]
      exact coeff_pow_add_C_mul_X_pow hn (by simp [PowerSeries.coeff_trunc, hn, hF0]) _

/-- Dieudonné-Dwork `(⇐)` direction: if the quotient
`F(T)^r / F(T^r) - 1` has positive coefficients in `r·ℤ_(r)`, then `F` has
`r`-integral coefficients. -/
theorem dieudonneDwork_mpr
    (r : ℕ) [Fact (Nat.Prime r)] {F : PowerSeries ℚ}
    (hF1 : PowerSeries.constantCoeff F = 1)
    (hQuotient : ∀ n : ℕ, 1 ≤ n →
      ∃ q : ℚ, IsRIntegralRat r q ∧
        (PowerSeries.coeff (R := ℚ) n)
          (F ^ r * (PowerSeries.subst (PowerSeries.X ^ r) F)⁻¹ - 1) =
            (r : ℚ) * q) :
    IsRIntegralPS r F := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0, PowerSeries.coeff_zero_eq_constantCoeff, hF1] using
          IsRIntegralRat.one r
      · have hn : 0 < n := Nat.pos_of_ne_zero hn0
        let hr : r ≠ 0 := (Fact.out : Nat.Prime r).ne_zero
        let SF : PowerSeries ℚ := PowerSeries.subst (PowerSeries.X ^ r) F
        let Q : PowerSeries ℚ := F ^ r * SF⁻¹ - 1
        have hS0 : PowerSeries.constantCoeff SF = 1 := by
          simpa [SF, hF1] using! PowerSeries.constantCoeff_subst_X_pow (R := ℚ) hr F
        have hQ0 : (PowerSeries.coeff (R := ℚ) 0) Q = 0 := by
          simp [Q, SF, hF1, hS0]
        have hQpos :
            ∀ i : ℕ, 1 ≤ i →
              ∃ q : ℚ, IsRIntegralRat r q ∧
                (PowerSeries.coeff (R := ℚ) i) Q = (r : ℚ) * q := by
          intro i hi
          simpa [Q, SF] using hQuotient i hi
        have hS_lower :
            ∀ j : ℕ, j < n →
              IsRIntegralRat r ((PowerSeries.coeff (R := ℚ) j) SF) := by
          intro j hj
          change IsRIntegralRat r
            ((PowerSeries.coeff (R := ℚ) j)
              (PowerSeries.subst (PowerSeries.X ^ r) F))
          rw [PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hr F j]
          by_cases hdiv : r ∣ j
          · have hjdiv : j / r < n :=
              lt_of_le_of_lt (Nat.div_le_self j r) hj
            simpa [hdiv] using ih (j / r) hjdiv
          · simp [hdiv, IsRIntegralRat.zero]
        have hQS : Q * SF = F ^ r - SF := by
          calc
            Q * SF = (F ^ r * SF⁻¹ - 1) * SF := rfl
            _ = F ^ r * (SF⁻¹ * SF) - SF := by ring
            _ = F ^ r - SF := by
              rw [PowerSeries.inv_mul_cancel SF (by simp [hS0])]
              ring
        rcases IsRMultipleIntegralPS.coeff_mul_left_multiple_pos_right_integral_lt
            hQ0 hQpos hS_lower with ⟨qD, hqD, hqDcoeffQS⟩
        have hqDcoeff :
            (PowerSeries.coeff (R := ℚ) n) (F ^ r - SF) = (r : ℚ) * qD := by
          simpa [hQS] using hqDcoeffQS
        let A : PowerSeries ℚ := ((PowerSeries.trunc n F : Polynomial ℚ) : PowerSeries ℚ)
        have hA_integral : IsRIntegralPS r A := by
          intro m
          by_cases hm : m < n
          · simpa [A, PowerSeries.coeff_trunc, hm] using ih m hm
          · simp [A, PowerSeries.coeff_trunc, hm, IsRIntegralRat.zero]
        have hSubstA :
            (PowerSeries.coeff (R := ℚ) n) SF =
              (PowerSeries.coeff (R := ℚ) n)
                (PowerSeries.subst (PowerSeries.X ^ r) A) := by
          change
            (PowerSeries.coeff (R := ℚ) n)
                (PowerSeries.subst (PowerSeries.X ^ r) F) =
              (PowerSeries.coeff (R := ℚ) n)
                (PowerSeries.subst (PowerSeries.X ^ r) A)
          rw [PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hr F n,
            PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hr A n]
          by_cases hdiv : r ∣ n
          · have hdivlt : n / r < n :=
              Nat.div_lt_self hn (Fact.out : Nat.Prime r).one_lt
            simp [hdiv, A, PowerSeries.coeff_trunc, hdivlt]
          · simp [hdiv]
        have hPow :
            (PowerSeries.coeff (R := ℚ) n) (F ^ r) =
              (PowerSeries.coeff (R := ℚ) n) (A ^ r) +
                (r : ℚ) * (PowerSeries.coeff (R := ℚ) n) F := by
          simpa [A] using coeff_pow_eq_trunc_add (F := F) (n := n) (k := r) hn hF1
        have hDiff :
            (PowerSeries.coeff (R := ℚ) n) (F ^ r - SF) =
              (PowerSeries.coeff (R := ℚ) n)
                (A ^ r - PowerSeries.subst (PowerSeries.X ^ r) A) +
                (r : ℚ) * (PowerSeries.coeff (R := ℚ) n) F := by
          rw [map_sub, map_sub, hPow, hSubstA]
          ring
        rcases pow_r_sub_subst_X_pow_r_in_r_smul r hA_integral n with
          ⟨qA, hqA, hqAcoeff⟩
        have hmain :
            (r : ℚ) * (PowerSeries.coeff (R := ℚ) n) F =
              (r : ℚ) * (qD - qA) := by
          calc
            (r : ℚ) * (PowerSeries.coeff (R := ℚ) n) F
                =
                  (PowerSeries.coeff (R := ℚ) n) (F ^ r - SF) -
                    (PowerSeries.coeff (R := ℚ) n)
                      (A ^ r - PowerSeries.subst (PowerSeries.X ^ r) A) := by
                    rw [hDiff]
                    ring
            _ = (r : ℚ) * qD - (r : ℚ) * qA := by
                  rw [hqDcoeff, hqAcoeff]
            _ = (r : ℚ) * (qD - qA) := by ring
        have hrQ : (r : ℚ) ≠ 0 := by
          exact_mod_cast (Fact.out : Nat.Prime r).ne_zero
        have hcoeff :
            (PowerSeries.coeff (R := ℚ) n) F = qD - qA :=
          mul_left_cancel₀ hrQ hmain
        rw [hcoeff]
        exact hqD.sub hqA

end IsRIntegralPS

end DieudonneDwork

end Furtwaengler

end KummerCriterion

end
