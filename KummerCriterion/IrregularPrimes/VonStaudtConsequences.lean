module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Padics.PadicIntegers
import KummerCriterion.IrregularPrimes.RatNumerator
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Consequences of von Staudt-Clausen

This file extracts the local numerator-exclusion statements needed in the
Diekmann/Jensen infinitude argument from mathlib's public
`Bernoulli.vonStaudt_clausen` theorem.
-/

@[expose] public section

namespace KummerCriterion

/-- The finite correction-prime set appearing in von Staudt-Clausen for `B_n`. -/
def vonStaudtPrimesFor (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ n

/-- Public even-index wrapper around mathlib's von Staudt-Clausen theorem. -/
theorem bernoulli_add_vonStaudtCorrection_mem_int {n : ℕ} (hn_even : Even n) :
    bernoulli n + ∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q ∈ Set.range Int.cast := by
  obtain ⟨k, hk⟩ := hn_even
  rw [hk]
  simpa [vonStaudtPrimesFor, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using Bernoulli.vonStaudt_clausen k

/-- If `p - 1 ∣ n`, then `p` cannot divide the reduced numerator of `B_n`. -/
theorem not_dvd_num_bernoulli_of_sub_one_dvd
    {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hdiv : p - 1 ∣ n) :
    ¬ (p : ℤ) ∣ (bernoulli n).num := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, rfl⟩ := hn_even
  simpa [two_mul] using
    (Bernoulli.not_dvd_num_bernoulli (p := p) (k := k) (by omega)
      (by simpa [two_mul] using hdiv))

/-- If `p - 1 ∣ n`, then `p` cannot divide the reduced numerator of `B_n / n`. -/
theorem not_dvd_num_bernoulli_div_self_of_sub_one_dvd
    {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hdiv : p - 1 ∣ n) :
    ¬ (p : ℤ) ∣ (((bernoulli n : ℚ) / n : ℚ).num) := fun hnum =>
  not_dvd_num_bernoulli_of_sub_one_dvd hp hn_pos hn_even hdiv
    (dvd_num_of_dvd_div_nat_num (q := bernoulli n) hn_pos hnum)

/-- A numerator prime for `B_n / n` cannot satisfy `p - 1 ∣ n`. -/
theorem sub_one_not_dvd_of_dvd_num_bernoulli_div_self
    {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hnum : (p : ℤ) ∣ (((bernoulli n : ℚ) / n : ℚ).num)) :
    ¬ (p - 1) ∣ n := fun hdiv =>
  not_dvd_num_bernoulli_div_self_of_sub_one_dvd hp hn_pos hn_even hdiv hnum

/-- For a prime correction term `1/q`, multiplying by `p` gives a
`p`-adic integer. -/
theorem p_mul_inv_nat_prime_mem_padicInt
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) :
    ∃ z : ℤ_[p], (((p : ℚ) * ((1 : ℚ) / q) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  by_cases hpq : p = q
  · subst q
    refine ⟨1, ?_⟩
    simp [(Fact.out : Nat.Prime p).ne_zero]
  · let r : ℚ := (p : ℚ) * ((1 : ℚ) / q)
    have hr_eq : r = Rat.divInt (p : ℤ) (q : ℤ) := by
      dsimp [r]
      rw [show (p : ℚ) * ((1 : ℚ) / q) = (p : ℚ) / q by ring]
      rw [Rat.divInt_eq_div]
      norm_num
    have hden_dvd_int : (r.den : ℤ) ∣ (q : ℤ) := by
      rw [hr_eq]
      exact Rat.den_dvd (p : ℤ) (q : ℤ)
    have hden_dvd_nat : r.den ∣ q := Int.natCast_dvd_natCast.mp hden_dvd_int
    have hden : ¬ p ∣ r.den := by
      intro hpd
      have hpq_dvd : p ∣ q := hpd.trans hden_dvd_nat
      exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) hq).mp hpq_dvd)
    refine ⟨⟨(r : ℚ_[p]), Padic.norm_rat_le_one hden⟩, rfl⟩

/-- The von Staudt correction sum becomes `p`-integral after multiplication
by `p`. -/
theorem p_mul_vonStaudtCorrection_mem_padicInt
    {p n : ℕ} [Fact p.Prime] :
    ∃ z : ℤ_[p],
      ((p : ℚ_[p]) * (((∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q) : ℚ) : ℚ_[p])) =
        (z : ℚ_[p]) := by
  classical
  let s := vonStaudtPrimesFor n
  have hterm : ∀ q ∈ s,
      ∃ z : ℤ_[p], (((p : ℚ) * ((1 : ℚ) / q) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
    intro q hq
    dsimp [s] at hq
    rw [vonStaudtPrimesFor, Finset.mem_filter] at hq
    exact p_mul_inv_nat_prime_mem_padicInt hq.2.1
  choose z hz using hterm
  refine ⟨∑ x ∈ s.attach, z x.1 x.2, ?_⟩
  rw [PadicInt.coe_sum]
  dsimp [s]
  push_cast
  rw [← Finset.sum_attach]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have := hz x.1 x.2
  push_cast at this ⊢
  exact this

/-- Direct von Staudt-Clausen consequence: for every even index, `p * B_n`
is a `p`-adic integer. -/
theorem p_mul_bernoulli_mem_padicInt_vonStaudt
    {p n : ℕ} [Fact p.Prime] (hn_even : Even n) :
    ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli n : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  obtain ⟨T, hT⟩ := bernoulli_add_vonStaudtCorrection_mem_int hn_even
  obtain ⟨C, hC⟩ := p_mul_vonStaudtCorrection_mem_padicInt (p := p) (n := n)
  refine ⟨(p : ℤ_[p]) * T - C, ?_⟩
  have hTQ : ((bernoulli n + ∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q : ℚ) :
      ℚ_[p]) = (T : ℚ_[p]) := by
    exact_mod_cast hT.symm
  have hmain : (p : ℚ_[p]) * ((bernoulli n : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (T : ℚ_[p]) -
        (p : ℚ_[p]) * (((∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q) : ℚ) :
          ℚ_[p]) := by
    rw [← hTQ]
    push_cast
    ring
  rw [hmain, hC]
  push_cast
  ring

end KummerCriterion
