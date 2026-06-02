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
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse.Part3

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

/-- The precision-indexed Artin-Hasse coefficient representative is the
quotient value of the `ℓ`-integral rational coefficient times `γ^n`. -/
theorem quotient_mk_dworkCoeffArtinHasseAtTo_eq_rIntegralRatToQuotient_mul_gamma_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    let q : DieudonneDwork.rIntegralRatSubring ℓ :=
      ⟨c, artinHasseExpSeries_coeff_isRIntegral ℓ n⟩
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (dworkCoeffArtinHasseAtTo S γ N n) =
      S.rIntegralRatToQuotient N q *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ ^ n) := by
  dsimp only
  let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
  let q : DieudonneDwork.rIntegralRatSubring ℓ :=
    ⟨c, artinHasseExpSeries_coeff_isRIntegral ℓ n⟩
  let QN : Ideal (𝓞 R') := S.Q ^ (N + 1)
  let d : 𝓞 R' ⧸ QN :=
    Ideal.Quotient.mk QN (((c.den : ℕ) : 𝓞 R'))
  have hdunit : IsUnit d := by
    simpa [d, q, c, QN] using S.rIntegralRat_den_isUnit_mod_Q_pow N q
  exact hdunit.mul_left_cancel <| by
    calc
      d * Ideal.Quotient.mk QN (dworkCoeffArtinHasseAtTo S γ N n)
          = Ideal.Quotient.mk QN
              ((c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N n) := by
            simp [d, QN]
      _ = Ideal.Quotient.mk QN ((c.num : 𝓞 R') * γ ^ n) := by
            simpa [c, QN] using
              quotient_mk_dworkCoeffArtinHasseAtTo_den_mul_eq_num_gamma_pow
                S γ N n
      _ = Ideal.Quotient.mk QN (((q : ℚ).num : ℤ) : 𝓞 R') *
            Ideal.Quotient.mk QN (γ ^ n) := by
            simp [q, c, QN]
      _ = (d * S.rIntegralRatToQuotient N q) *
            Ideal.Quotient.mk QN (γ ^ n) := by
            rw [show d * S.rIntegralRatToQuotient N q =
                Ideal.Quotient.mk QN (((q : ℚ).num : ℤ) : 𝓞 R') by
              simpa [d, q, c, QN] using S.rIntegralRatToQuotient_den_mul N q]
      _ = d * (S.rIntegralRatToQuotient N q *
            Ideal.Quotient.mk QN (γ ^ n)) := by ring







end Furtwaengler

end BernoulliRegular

end
