module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DieudonneDwork
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse.Part2

/-!
# Artin-Hasse exponential power series

This file defines the Artin-Hasse log and exponential power series over `ℚ`,
indexed by a prime `r`:

* `artinHasseLogSeries r : PowerSeries ℚ` is `L_r(T) = ∑_{i ≥ 0} T^{r^i} / r^i`.
* `artinHasseExpSeries r : PowerSeries ℚ` is `E_r(T) = exp(L_r(T))`.

The "is a power of `r`" predicate is decidable via `Nat.log`: for `r ≥ 2`,
`n = r^i` for some `i ≥ 0` iff `r ^ Nat.log r n = n ∧ n ≠ 0`. (For `n = 0`,
`r ^ Nat.log r 0 = r ^ 0 = 1 ≠ 0`, so the predicate fails as expected.)

These are the building blocks of the Dwork coefficient sequence used by the
`FullTeichDworkSetup` interface in REF-18 (the project's Φ/Kelly/Furtwängler
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

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- The precision-indexed inverse-series coefficient lift is the quotient
value of the corresponding `ℓ`-integral rational coefficient times `π^n`. -/
theorem quotient_mk_artinHasseInverseCoeffLiftTo_eq_rIntegralRatToQuotient_mul_pi_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
    let q : DieudonneDwork.rIntegralRatSubring ℓ :=
      ⟨c, artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (artinHasseInverseCoeffLiftTo S N n) =
      S.rIntegralRatToQuotient N q *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.π ^ n) := by
  dsimp only
  let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
  let q : DieudonneDwork.rIntegralRatSubring ℓ :=
    ⟨c, artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩
  let QN : Ideal (𝓞 R') := S.Q ^ (N + 1)
  let d : 𝓞 R' ⧸ QN :=
    Ideal.Quotient.mk QN (((c.den : ℕ) : 𝓞 R'))
  have hdunit : IsUnit d := by
    simpa [d, q, c, QN] using S.rIntegralRat_den_isUnit_mod_Q_pow N q
  exact hdunit.mul_left_cancel <| by
    calc
      d * Ideal.Quotient.mk QN (artinHasseInverseCoeffLiftTo S N n)
          = Ideal.Quotient.mk QN
              ((c.den : 𝓞 R') * artinHasseInverseCoeffLiftTo S N n) := by
            simp [d, QN]
      _ = Ideal.Quotient.mk QN ((c.num : 𝓞 R') * S.π ^ n) := by
            simpa [c, QN] using
              quotient_mk_artinHasseInverseCoeffLiftTo_den_mul_eq_num_pi_pow S N n
      _ = Ideal.Quotient.mk QN (((q : ℚ).num : ℤ) : 𝓞 R') *
            Ideal.Quotient.mk QN (S.π ^ n) := by
            simp [q, c, QN]
      _ = (d * S.rIntegralRatToQuotient N q) *
            Ideal.Quotient.mk QN (S.π ^ n) := by
            rw [show d * S.rIntegralRatToQuotient N q =
                Ideal.Quotient.mk QN (((q : ℚ).num : ℤ) : 𝓞 R') by
              simpa [d, q, c, QN] using S.rIntegralRatToQuotient_den_mul N q]
      _ = d * (S.rIntegralRatToQuotient N q *
            Ideal.Quotient.mk QN (S.π ^ n)) := by ring







/-- Precision-consistent `N`-th truncation of the formal Dwork parameter:
every coefficient denominator is inverted modulo `Q^(N+1)`. -/
noncomputable def artinHasseDworkParameterApproxTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) : 𝓞 R' :=
  ∑ n ∈ Finset.range (N + 1), artinHasseInverseCoeffLiftTo S N n

/-- Quotient form of the finite inverse-series Dwork parameter approximation:
it is the finite evaluation of the formal inverse coefficients at `π`. -/
theorem quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (artinHasseDworkParameterApproxTo S N) =
      ∑ n ∈ Finset.range (N + 1),
        S.rIntegralRatToQuotient N
          (⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ),
            artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩ :
              DieudonneDwork.rIntegralRatSubring ℓ) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.π ^ n) := by
  classical
  rw [artinHasseDworkParameterApproxTo, map_sum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simpa using
    quotient_mk_artinHasseInverseCoeffLiftTo_eq_rIntegralRatToQuotient_mul_pi_pow
      S N n

/-- Polynomial-evaluation form of
`quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient`. -/
theorem quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (artinHasseDworkParameterApproxTo S N) =
      (PowerSeries.trunc (N + 1)
        ((artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (S.rIntegralRatToQuotient N))).eval₂
        (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1)))
        (Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π) := by
  classical
  rw [quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient]
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [map_pow]



theorem artinHasseDworkParameterApproxTo_mem_Q
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) :
    artinHasseDworkParameterApproxTo S N ∈ S.Q := by
  classical
  unfold artinHasseDworkParameterApproxTo
  apply Ideal.sum_mem
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · exact Ideal.pow_le_self hn0 (artinHasseInverseCoeffLiftTo_mem_Q_pow S N n)






/-- Raw denominator-inverse lift of the coefficient of `E_ℓ(πT)`.  The public
coefficient sequence below pins the constant term exactly and uses this raw
lift from degree `1` onward. -/
noncomputable def dworkCoeffArtinHasseRaw
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).num : 𝓞 R') *
    S.π ^ n * dworkCoeffArtinHasseDenInv S n

/-- The `Q`-adic Dwork coefficient obtained by substituting `T ↦ πT` in the
Artin-Hasse exponential.  The constant term is fixed exactly as `1`; in degree
at least one, if `c_n = [T^n] E_ℓ(T)`, this is the integral representative of
`c_n · π^n` modulo `Q^(n+1)`, formed by choosing an inverse to `c_n.den`
modulo `Q^(n+1)`. -/
noncomputable def dworkCoeffArtinHasse
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) : 𝓞 R' :=
  match n with
  | 0 => 1
  | Nat.succ n => dworkCoeffArtinHasseRaw S (Nat.succ n)


/-- Precision-indexed raw lift of the coefficient of `E_ℓ(γT)`.  The
denominator inverse is chosen modulo `Q^(N+1)`, which is the precision needed
by an `N`-th Dwork splitting congruence. -/
noncomputable def dworkCoeffArtinHasseAtRawTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).num : 𝓞 R') *
    γ ^ n * dworkCoeffArtinHasseDenInvTo S n N


/-- Precision-indexed integral representative of the coefficients of
`E_ℓ(γT)`, with constant term fixed exactly as `1`.  The argument `N` is the
target truncation precision. -/
noncomputable def dworkCoeffArtinHasseAtTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) : 𝓞 R' :=
  match n with
  | 0 => 1
  | Nat.succ n => dworkCoeffArtinHasseAtRawTo S γ N (Nat.succ n)









/-- Denominator-cleared congruence for the precision-indexed coefficients of
`E_ℓ(γT)`, valid at the target precision `Q^(N+1)`. -/
theorem dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    (c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N n - (c.num : 𝓞 R') * γ ^ n ∈
      S.Q ^ (N + 1) := by
  cases n with
  | zero =>
      dsimp only
      have hc :
          (PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ) = 1 := by
        have hℓ : 0 < ℓ := (Fact.out : Nat.Prime ℓ).pos
        simp [artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ]
      simp [dworkCoeffArtinHasseAtTo, hc]
  | succ n =>
      dsimp only
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hden :
          (c.den : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1 ∈
            S.Q ^ (N + 1) := by
        simpa [c] using dworkCoeffArtinHasseDenInvTo_spec S m N
      have hmul :
          ((c.num : 𝓞 R') * γ ^ m) *
              ((c.den : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1) ∈
            S.Q ^ (N + 1) :=
        Ideal.mul_mem_left _ _ hden
      convert hmul using 1
      simp [dworkCoeffArtinHasseAtTo, dworkCoeffArtinHasseAtRawTo, c, m]
      ring


/-- Quotient form of
`dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ`. -/
theorem quotient_mk_dworkCoeffArtinHasseAtTo_den_mul_eq_num_gamma_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        ((c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N n) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) ((c.num : 𝓞 R') * γ ^ n) := by
  dsimp only
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ S γ N n

end Furtwaengler

end BernoulliRegular

end
