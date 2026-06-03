module

public import KummerCriterion.Reflection.ResidueSymbol.ArtinHasse.Part1
import KummerCriterion.Reflection.ResidueSymbol.ArtinHasse.Part2
import KummerCriterion.Reflection.ResidueSymbol.DieudonneDwork.Part2
public import KummerCriterion.Reflection.Local.DeltaAction
public import KummerCriterion.Reflection.ResidueSymbol.KummerArtinHasseCompletionMap

/-!
# Singular Kummer: localization at a height-one prime

This file provides the localization target. For a height-one prime
`v`, the local units are represented inside `Kˣ` as the elements with
`v`-adic valuation one. After choosing a uniformizer, every global field
class in `Kˣ / Kˣ^p` has a normalized representative in this local-unit
subgroup, giving a homomorphism

```text
 Kˣ / Kˣ^p -> U_v / U_v^p.
```

Composing this with the singular-pair generator gives the localization map
from the singular group `S` to the local-unit quotient.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion
namespace Reflection
namespace SingularKummer

namespace SingularPair

section Cyclotomic

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]

/-- The distinguished cyclotomic lambda prime as a height-one prime. -/
def cyclotomicLambdaHeightOne : IsDedekindDomain.HeightOneSpectrum (𝓞 F) where
  asIdeal := Local.cyclotomicLambda p F
  isPrime := zetaPrime_isPrime p F
  ne_bot := zetaPrime_ne_bot p F

end Cyclotomic

end SingularPair

end SingularKummer
end Reflection
end KummerCriterion

end

/-!
# Global lambda decomposition for the Kummer--Artin--Hasse correction

The full explicit local correction is only consumed by the global product
formula on elements of `Kˣ`. This file gives the decomposition API for those
global field units at the distinguished cyclotomic prime:

* normalize by the explicit uniformizer `pi = zeta_p - 1`;
* convert the resulting lambda-local unit into the localized ring and then
 into the completed local unit group;
* split the completed unit into its Teichmuller residue factor and a
 principal-unit factor.

This avoids assuming that the adic completed integer ring is already known to
Lean as a DVR.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors WithZero
open NumberField IsCyclotomicExtension IsDedekindDomain

namespace KummerCriterion

open Reflection.SingularKummer.SingularPair

namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The global integral cyclotomic uniformizer `pi = zeta_p - 1`. -/
def lambdaPiIntegral
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    𝓞 K :=
  (zeta_spec p ℚ K).toInteger - 1

@[simp]
theorem lambdaPiIntegral_ne_zero
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    lambdaPiIntegral p K ≠ 0 := by
  change (zeta_spec p ℚ K).toInteger - 1 ≠ 0
  exact (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero

/-- The explicit cyclotomic uniformizer as a global field unit. -/
def lambdaPiFieldUnit
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (lambdaPiIntegral p K))
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne
      (lambdaPiIntegral_ne_zero (p := p) (K := K)))

@[simp]
theorem lambdaPiFieldUnit_val
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    (lambdaPiFieldUnit p K : K) =
      algebraMap (𝓞 K) K (lambdaPiIntegral p K) :=
  rfl

/-- The distinguished lambda prime as a height-one prime. -/
abbrev lambdaHeightOne
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    HeightOneSpectrum (𝓞 K) :=
  Reflection.SingularKummer.SingularPair.cyclotomicLambdaHeightOne (p := p) K

/-- The explicit cyclotomic uniformizer has normalized lambda valuation
`exp (-1)`. -/
theorem lambdaPiFieldUnit_valuation
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    (lambdaHeightOne p K).valuation K (lambdaPiFieldUnit p K : K) =
      WithZero.exp (-1 : ℤ) := by
  rw [lambdaPiFieldUnit_val]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have hspan :
      (lambdaHeightOne p K).asIdeal =
        Ideal.span ({lambdaPiIntegral p K} : Set (𝓞 K)) := rfl
  exact (lambdaHeightOne p K).intValuation_singleton
    (lambdaPiIntegral_ne_zero (p := p) (K := K)) hspan

end KummerArtinHasse
end Furtwaengler
end KummerCriterion

/-!
# Valuation-completion trace source for the Kummer--Artin--Hasse `A` term

The earlier local logarithm files are written in the project's adic completed
integer ring `LambdaLocalIntegerRing`. The trace needed for the explicit
Kummer--Artin--Hasse correction, however, is the finite `Q_p`-linear trace on
the valuation completion of `K` at `lambda`.

This file makes the trace-source API use the valuation-completion model from
the start. The old adic logarithm stack remains useful infrastructure, but it
is not the final source of the `A` term consumed by reciprocity.

The `< p` truncated logarithm is kept as a named summand. The active finite
approximation to the full p-adic logarithm for the Kummer--Artin--Hasse
`A`-term is `log_≤p(u) = log_<p(u) + (u - 1)^p / p`; the missing `n = p`
term is essential on the `μ_p` torsion direction in `U_1`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The cyclotomic uniformizer `pi = zeta_p - 1` in the valuation-completion
integer ring. -/
def lambdaValuedPiInteger : LambdaValuedIntegerRing p K :=
  algebraMap (𝓞 K) (LambdaValuedIntegerRing p K)
    ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)

/-- The cyclotomic uniformizer `pi = zeta_p - 1` in the valuation-completion
field. -/
def lambdaValuedPi : LambdaValuedCompletion p K :=
  (lambdaValuedPiInteger p K : LambdaValuedCompletion p K)

/-- The distinguished `p`-th root of unity in the valuation-completion integer
ring. -/
def lambdaValuedZetaInteger : LambdaValuedIntegerRing p K :=
  algebraMap (𝓞 K) (LambdaValuedIntegerRing p K)
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger

/-- The distinguished `p`-th root of unity in the valuation-completion field. -/
def lambdaValuedZeta : LambdaValuedCompletion p K :=
  (lambdaValuedZetaInteger p K : LambdaValuedCompletion p K)

end KummerArtinHasse
end Furtwaengler
end KummerCriterion

/-!
# Local `p`-adic setup for the cyclotomic-unit route

This file exposes the local cyclotomic model from the Furtwängler development
under route-level names for the cyclotomic-unit reflection proof.

The formal Artin-Hasse inverse package records the corrected Dwork
normalization for the inverse of `E_p(T) - 1` and its sign identity.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion
namespace CyclotomicUnits
namespace PadicLogSetup

namespace FormalDwork

variable (p : ℕ) [Fact p.Prime]

/-- The Artin-Hasse logarithm series `L_p(T) = sum T^(p^n)/p^n`. -/
abbrev logSeries : PowerSeries ℚ :=
  Furtwaengler.artinHasseLogSeries p

/-- The Artin-Hasse exponential series `E_p(T) = exp(L_p(T))`. -/
abbrev expSeries : PowerSeries ℚ :=
  Furtwaengler.artinHasseExpSeries p

/-- The series `E_p(T) - 1`, whose inverse is the corrected Dwork parameter
series. -/
abbrev expMinusOneSeries : PowerSeries ℚ :=
  Furtwaengler.artinHasseExpMinusOneSeries p

/-- The formal inverse of `E_p(T) - 1`. Evaluated at `zeta_p - 1` in a
complete local ring, this is the corrected Dwork parameter. -/
abbrev inverseSeries : PowerSeries ℚ :=
  Furtwaengler.artinHasseExpInverseSeries p

theorem logSeries_hasSubst :
    PowerSeries.HasSubst (logSeries p) :=
  Furtwaengler.artinHasseLogSeries_hasSubst p

@[simp]
theorem expMinusOneSeries_constantCoeff :
    PowerSeries.constantCoeff (expMinusOneSeries p) = 0 :=
  Furtwaengler.artinHasseExpMinusOneSeries_constantCoeff p

@[simp]
theorem inverseSeries_constantCoeff :
    PowerSeries.constantCoeff (inverseSeries p) = 0 :=
  Furtwaengler.artinHasseExpInverseSeries_constantCoeff p

theorem inverseSeries_hasSubst :
    PowerSeries.HasSubst (inverseSeries p) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (inverseSeries_constantCoeff p)

theorem expMinusOneSeries_isPIntegral :
    Furtwaengler.DieudonneDwork.IsRIntegralPS p (expMinusOneSeries p) :=
  Furtwaengler.artinHasseExpMinusOneSeries_isRIntegral p

theorem inverseSeries_isPIntegral :
    Furtwaengler.DieudonneDwork.IsRIntegralPS p (inverseSeries p) :=
  Furtwaengler.artinHasseExpInverseSeries_isRIntegral p

/-- Formal right-inverse identity: `(E_p(T)-1)(G_p(T)) = T`. -/
theorem expMinusOneSeries_subst_inverse :
    (expMinusOneSeries p).subst (inverseSeries p) =
      (PowerSeries.X : PowerSeries ℚ) :=
  Furtwaengler.artinHasseExpMinusOneSeries_subst_inverse p

/-- The other formal inverse identity: `G_p(E_p(T)-1) = T`. -/
theorem inverseSeries_subst_expMinusOneSeries :
    (inverseSeries p).subst (expMinusOneSeries p) =
      (PowerSeries.X : PowerSeries ℚ) := by
  let P : PowerSeries ℚ := expMinusOneSeries p
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P, expMinusOneSeries]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  simpa [P, inverseSeries, expMinusOneSeries,
    Furtwaengler.artinHasseExpInverseSeries] using
    PowerSeries.subst_substInv_left P (by simp [P, expMinusOneSeries])

/-- Integral-coefficient form of `E_p(G_p(T)) = 1 + T`, transported to any
coefficient ring receiving the `p`-integral rational coefficients. -/
theorem expSeries_mapTo_subst_inverse
    {A : Type*} [CommRing A]
    (φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A) :
    PowerSeries.subst
        ((inverseSeries_isPIntegral p).mapTo φ)
        ((show Furtwaengler.DieudonneDwork.IsRIntegralPS p
            (Furtwaengler.artinHasseExpSeries p) from
          fun n => Furtwaengler.artinHasseExpSeries_coeff_isRIntegral p n).mapTo φ) =
      1 + (PowerSeries.X : PowerSeries A) :=
  Furtwaengler.artinHasseExpSeries_mapTo_subst_inverse p φ

/-- For odd `p`, the Artin-Hasse logarithm is an odd formal series. -/
theorem logSeries_rescale_neg (hp_two : 2 < p) :
    PowerSeries.rescale (-1 : ℚ) (logSeries p) = -logSeries p := by
  have hp_odd : Odd p := by
    rcases (Fact.out : Nat.Prime p).eq_two_or_odd with h | h
    · omega
    · exact Nat.odd_iff.mpr h
  ext n
  rw [PowerSeries.coeff_rescale, map_neg]
  rw [Furtwaengler.artinHasseLogSeries_coeff]
  by_cases hpow : p ^ Nat.log p n = n ∧ n ≠ 0
  · rw [if_pos hpow]
    have hn_odd : Odd n := by
      rw [← hpow.1]
      exact hp_odd.pow
    rw [Odd.neg_one_pow (α := ℚ) hn_odd]
    ring
  · rw [if_neg hpow]
    ring

theorem subst_logSeries_evalNeg_exp :
    PowerSeries.subst (logSeries p) (PowerSeries.evalNegHom (PowerSeries.exp ℚ)) =
      PowerSeries.subst (-(logSeries p)) (PowerSeries.exp ℚ) := by
  rw [PowerSeries.evalNegHom, PowerSeries.rescale_eq_subst]
  rw [PowerSeries.subst_comp_subst_apply]
  · have hLX :
        PowerSeries.subst (logSeries p) ((-1 : ℚ) • (PowerSeries.X : PowerSeries ℚ)) =
          -logSeries p := by
      rw [PowerSeries.subst_smul (logSeries_hasSubst p)]
      rw [PowerSeries.subst_X (logSeries_hasSubst p)]
      simp
    rw [hLX]
  · exact PowerSeries.HasSubst.smul_X (-1 : ℚ) ()
  · exact logSeries_hasSubst p

theorem subst_neg_log_exp_mul_expSeries :
    PowerSeries.subst (-(logSeries p)) (PowerSeries.exp ℚ) * expSeries p = 1 := by
  have h0 := congrArg
    (fun F : PowerSeries ℚ => PowerSeries.subst (logSeries p) F)
    (PowerSeries.exp_mul_exp_neg_eq_one (A := ℚ))
  have h :
      PowerSeries.subst (logSeries p)
          (PowerSeries.exp ℚ * PowerSeries.evalNegHom (PowerSeries.exp ℚ)) =
        PowerSeries.subst (logSeries p) (1 : PowerSeries ℚ) := h0
  rw [PowerSeries.subst_mul (logSeries_hasSubst p)] at h
  rw [subst_logSeries_evalNeg_exp] at h
  have h1 : PowerSeries.subst (logSeries p) (1 : PowerSeries ℚ) = 1 := by
    simpa using
      (PowerSeries.subst_C (a := logSeries p) (r := (1 : ℚ)))
  rw [h1] at h
  simpa [expSeries, mul_comm] using h

/-- Formal identity `E_p(-T) = E_p(T)^{-1}`, stated without choosing the
inverse: the product is `1`. -/
theorem expSeries_rescale_neg_mul_self (hp_two : 2 < p) :
    PowerSeries.rescale (-1 : ℚ) (expSeries p) * expSeries p = 1 := by
  have hneg :
      PowerSeries.rescale (-1 : ℚ) (expSeries p) =
        PowerSeries.subst (-(logSeries p)) (PowerSeries.exp ℚ) := by
    change PowerSeries.rescale (-1 : ℚ) (Furtwaengler.artinHasseExpSeries p) =
      PowerSeries.subst (-(logSeries p)) (PowerSeries.exp ℚ)
    unfold Furtwaengler.artinHasseExpSeries
    rw [PowerSeries.rescale_eq_subst]
    rw [PowerSeries.subst_comp_subst_apply]
    · have h := logSeries_rescale_neg p hp_two
      rw [PowerSeries.rescale_eq_subst] at h
      simpa using
        congrArg (fun L => PowerSeries.subst L (PowerSeries.exp ℚ)) h
    · exact logSeries_hasSubst p
    · exact PowerSeries.HasSubst.smul_X (-1 : ℚ) ()
  rw [hneg]
  exact subst_neg_log_exp_mul_expSeries p

/-- The same sign identity in terms of `H_p(T) = E_p(T)-1`. This is the
formal source of the conjugation relation for the corrected local parameter. -/
theorem one_add_rescale_neg_expMinusOneSeries_mul_self (hp_two : 2 < p) :
    (1 + PowerSeries.rescale (-1 : ℚ) (expMinusOneSeries p)) *
        (1 + expMinusOneSeries p) = 1 := by
  simpa [expMinusOneSeries, expSeries, Furtwaengler.artinHasseExpMinusOneSeries,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    expSeries_rescale_neg_mul_self p hp_two

/-- Substituting the inverse parameter into the Artin--Hasse sign identity gives
the formal fractional-linear conjugation formula in denominator-cleared form:
`H_p(-G_p(S)) * (1 + S) = -S`, where `H_p(T) = E_p(T)-1`. -/
theorem expMinusOneSeries_subst_neg_inverse_mul_one_add_X_eq_neg_X
    (hp_two : 2 < p) :
    (PowerSeries.subst (-(inverseSeries p)) (expMinusOneSeries p)) *
        (1 + (PowerSeries.X : PowerSeries ℚ)) =
      -(PowerSeries.X : PowerSeries ℚ) := by
  let H : PowerSeries ℚ := expMinusOneSeries p
  let G : PowerSeries ℚ := inverseSeries p
  have hG : PowerSeries.HasSubst G := by
    simpa [G] using inverseSeries_hasSubst p
  have hnegG : PowerSeries.HasSubst (-G) := by
    simpa using hG.smul' (-1 : ℚ)
  have hsubst := congrArg
    (fun F : PowerSeries ℚ => PowerSeries.subst G F)
    (one_add_rescale_neg_expMinusOneSeries_mul_self p hp_two)
  change PowerSeries.subst G
      ((1 + PowerSeries.rescale (-1 : ℚ) (expMinusOneSeries p)) *
        (1 + expMinusOneSeries p)) =
    PowerSeries.subst G (1 : PowerSeries ℚ) at hsubst
  rw [PowerSeries.subst_mul hG] at hsubst
  have hsubst_one :
      PowerSeries.subst G (1 : PowerSeries ℚ) = 1 := by
    simpa using PowerSeries.subst_C (a := G) (r := (1 : ℚ))
  have hleft :
      PowerSeries.subst G (1 + PowerSeries.rescale (-1 : ℚ) H) =
        1 + PowerSeries.subst (-G) H := by
    rw [PowerSeries.subst_add hG, hsubst_one]
    congr 1
    rw [PowerSeries.rescale_eq_subst]
    calc
      PowerSeries.subst G
          (PowerSeries.subst ((-1 : ℚ) • (PowerSeries.X : PowerSeries ℚ)) H) =
          PowerSeries.subst
            (PowerSeries.subst G ((-1 : ℚ) • (PowerSeries.X : PowerSeries ℚ))) H :=
            PowerSeries.subst_comp_subst_apply
              (PowerSeries.HasSubst.smul_X' (-1 : ℚ)) hG H
      _ = PowerSeries.subst (-G) H := by
            rw [PowerSeries.subst_smul hG, PowerSeries.subst_X hG]
            simp [G]
  have hright :
      PowerSeries.subst G (1 + H) =
        1 + (PowerSeries.X : PowerSeries ℚ) := by
    rw [PowerSeries.subst_add hG, hsubst_one]
    rw [show PowerSeries.subst G H = (PowerSeries.X : PowerSeries ℚ) by
      simpa [H, G] using expMinusOneSeries_subst_inverse (p := p)]
  have hmul :
      (1 + PowerSeries.subst (-G) H) *
          (1 + (PowerSeries.X : PowerSeries ℚ)) = 1 := by
    simpa [H, hleft, hright, hsubst_one] using hsubst
  simpa [H, G] using
    (calc
      PowerSeries.subst (-G) H * (1 + (PowerSeries.X : PowerSeries ℚ)) =
          (1 + PowerSeries.subst (-G) H) *
              (1 + (PowerSeries.X : PowerSeries ℚ)) -
            (1 + (PowerSeries.X : PowerSeries ℚ)) := by
            ring
      _ = 1 - (1 + (PowerSeries.X : PowerSeries ℚ)) := by
            rw [hmul]
      _ = -(PowerSeries.X : PowerSeries ℚ) := by
            ring)

/-- The inverse series carries the formal conjugate parameter
`H_p(-G_p(S))` to `-G_p(S)`. -/
theorem inverseSeries_subst_expMinusOneSeries_subst_neg_inverse :
    PowerSeries.subst
        (PowerSeries.subst (-(inverseSeries p)) (expMinusOneSeries p))
        (inverseSeries p) =
      -(inverseSeries p) := by
  let H : PowerSeries ℚ := expMinusOneSeries p
  let G : PowerSeries ℚ := inverseSeries p
  have hH : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (expMinusOneSeries_constantCoeff p)
  have hnegG : PowerSeries.HasSubst (-G) := by
    have hG : PowerSeries.HasSubst G := by
      simpa [G] using inverseSeries_hasSubst p
    simpa using hG.smul' (-1 : ℚ)
  calc
    PowerSeries.subst (PowerSeries.subst (-G) H) G =
        PowerSeries.subst (-G) (PowerSeries.subst H G) :=
          (PowerSeries.subst_comp_subst_apply hH hnegG G).symm
    _ = PowerSeries.subst (-G) (PowerSeries.X : PowerSeries ℚ) := by
          rw [show PowerSeries.subst H G = (PowerSeries.X : PowerSeries ℚ) by
            simpa [H, G] using inverseSeries_subst_expMinusOneSeries (p := p)]
    _ = -G := by
          rw [PowerSeries.subst_X hnegG]
    _ = -(inverseSeries p) := by
          rfl

/-- Integral-coefficient form of the denominator-cleared sign identity,
transported to any coefficient ring receiving the `p`-integral rational
coefficients. -/
theorem expMinusOneSeries_mapTo_subst_neg_inverse_mul_one_add_X_eq_neg_X
    {A : Type*} [CommRing A]
    (φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A)
    (hp_two : 2 < p) :
    PowerSeries.subst
        (-((inverseSeries_isPIntegral p).mapTo φ))
        ((expMinusOneSeries_isPIntegral p).mapTo φ) *
        (1 + (PowerSeries.X : PowerSeries A)) =
      -(PowerSeries.X : PowerSeries A) := by
  let hInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p (inverseSeries p) :=
    inverseSeries_isPIntegral p
  let hH : Furtwaengler.DieudonneDwork.IsRIntegralPS p (expMinusOneSeries p) :=
    expMinusOneSeries_isPIntegral p
  let hNegInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p (-(inverseSeries p)) :=
    hInv.neg
  have hNegInv0 : PowerSeries.constantCoeff (-(inverseSeries p)) = 0 := by
    simp
  let inner : PowerSeries ℚ :=
    PowerSeries.subst (-(inverseSeries p)) (expMinusOneSeries p)
  let hInner : Furtwaengler.DieudonneDwork.IsRIntegralPS p inner :=
    hH.subst hNegInv hNegInv0
  have hInnerMap :
      hInner.mapTo φ =
        PowerSeries.subst (-(hInv.mapTo φ)) (hH.mapTo φ) := by
    calc
      hInner.mapTo φ =
          PowerSeries.subst (hNegInv.mapTo φ) (hH.mapTo φ) :=
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst
              φ hH hNegInv hNegInv0
      _ = PowerSeries.subst (-(hInv.mapTo φ)) (hH.mapTo φ) := by
            rw [show hNegInv.mapTo φ = -(hInv.mapTo φ) by
              simpa [hNegInv, hInv] using
                Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg φ hInv]
  let hOneAddX : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (1 + (PowerSeries.X : PowerSeries ℚ)) :=
    (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p).add
      (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p)
  have hOneAddXMap :
      hOneAddX.mapTo φ = 1 + (PowerSeries.X : PowerSeries A) := by
    calc
      hOneAddX.mapTo φ =
          (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p).mapTo φ +
            (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p).mapTo φ :=
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_add
              φ (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p)
                (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p)
      _ = 1 + (PowerSeries.X : PowerSeries A) := by
            simp
  calc
    PowerSeries.subst
        (-((inverseSeries_isPIntegral p).mapTo φ))
        ((expMinusOneSeries_isPIntegral p).mapTo φ) *
        (1 + (PowerSeries.X : PowerSeries A)) =
        hInner.mapTo φ * hOneAddX.mapTo φ := by
          rw [hInnerMap, hOneAddXMap]
    _ = (hInner.mul hOneAddX).mapTo φ :=
          (Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_mul
            φ hInner hOneAddX).symm
    _ = ((Furtwaengler.DieudonneDwork.IsRIntegralPS.X p).neg).mapTo φ :=
          Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq
            φ (hInner.mul hOneAddX)
            ((Furtwaengler.DieudonneDwork.IsRIntegralPS.X p).neg)
            (by
              simpa [inner] using
                expMinusOneSeries_subst_neg_inverse_mul_one_add_X_eq_neg_X
                  (p := p) hp_two)
    _ = -(PowerSeries.X : PowerSeries A) := by
          simpa using Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg
            φ (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p)

/-- Integral-coefficient form of `G_p(H_p(-G_p(T))) = -G_p(T)`,
transported to any coefficient ring receiving the `p`-integral rational
coefficients. -/
theorem inverseSeries_mapTo_subst_expMinusOneSeries_subst_neg_inverse
    {A : Type*} [CommRing A]
    (φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A) :
    PowerSeries.subst
        (PowerSeries.subst
          (-((inverseSeries_isPIntegral p).mapTo φ))
          ((expMinusOneSeries_isPIntegral p).mapTo φ))
        ((inverseSeries_isPIntegral p).mapTo φ) =
      -((inverseSeries_isPIntegral p).mapTo φ) := by
  let hInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p (inverseSeries p) :=
    inverseSeries_isPIntegral p
  let hH : Furtwaengler.DieudonneDwork.IsRIntegralPS p (expMinusOneSeries p) :=
    expMinusOneSeries_isPIntegral p
  let hNegInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p (-(inverseSeries p)) :=
    hInv.neg
  have hNegInv0 : PowerSeries.constantCoeff (-(inverseSeries p)) = 0 := by
    simp
  let inner : PowerSeries ℚ :=
    PowerSeries.subst (-(inverseSeries p)) (expMinusOneSeries p)
  let hInner : Furtwaengler.DieudonneDwork.IsRIntegralPS p inner :=
    hH.subst hNegInv hNegInv0
  have hInner0 : PowerSeries.constantCoeff inner = 0 := by
    simpa [inner] using
      PowerSeries.constantCoeff_subst_eq_zero
        (by simp : PowerSeries.constantCoeff (-(inverseSeries p)) = 0)
        (expMinusOneSeries p) (expMinusOneSeries_constantCoeff p)
  have hInnerMap :
      hInner.mapTo φ =
        PowerSeries.subst (-(hInv.mapTo φ)) (hH.mapTo φ) := by
    calc
      hInner.mapTo φ =
          PowerSeries.subst (hNegInv.mapTo φ) (hH.mapTo φ) :=
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst
              φ hH hNegInv hNegInv0
      _ = PowerSeries.subst (-(hInv.mapTo φ)) (hH.mapTo φ) := by
            rw [show hNegInv.mapTo φ = -(hInv.mapTo φ) by
              simpa [hNegInv, hInv] using
                Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg φ hInv]
  calc
    PowerSeries.subst
        (PowerSeries.subst
          (-((inverseSeries_isPIntegral p).mapTo φ))
          ((expMinusOneSeries_isPIntegral p).mapTo φ))
        ((inverseSeries_isPIntegral p).mapTo φ) =
        PowerSeries.subst (hInner.mapTo φ) (hInv.mapTo φ) := by
          rw [hInnerMap]
    _ = (hInv.subst hInner hInner0).mapTo φ :=
          (Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst
            φ hInv hInner hInner0).symm
    _ = hInv.neg.mapTo φ :=
          Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq
            φ (hInv.subst hInner hInner0) hInv.neg
            (by
              simpa [inner] using
                inverseSeries_subst_expMinusOneSeries_subst_neg_inverse
                  (p := p))
    _ = -(hInv.mapTo φ) :=
          Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg φ hInv

omit [Fact p.Prime] in
/-- The lambda-valuation exponent predicted for the `n`th tail summand,
assuming `v(varpi)=1` and `v(p)=p-1`. -/
def artinHasseTailValuationIndex (n : ℕ) : ℤ :=
  (p : ℤ) ^ n - 1 - (n : ℤ) * ((p : ℤ) - 1)

omit [Fact p.Prime] in
theorem artinHasseTailValuationIndex_two :
    artinHasseTailValuationIndex p 2 = ((p : ℤ) - 1) ^ 2 := by
  unfold artinHasseTailValuationIndex
  ring

omit [Fact p.Prime] in
theorem artinHasseTailValuationIndex_succ_sub (n : ℕ) :
    artinHasseTailValuationIndex p (n + 1) -
        artinHasseTailValuationIndex p n =
      ((p : ℤ) - 1) * ((p : ℤ) ^ n - 1) := by
  unfold artinHasseTailValuationIndex
  push_cast
  ring

/-- The predicted tail valuations strictly increase after the first term. -/
theorem artinHasseTailValuationIndex_lt_succ {n : ℕ} (hn : 1 ≤ n) :
    artinHasseTailValuationIndex p n <
      artinHasseTailValuationIndex p (n + 1) := by
  have hdiff := artinHasseTailValuationIndex_succ_sub (p := p) n
  have hp_one : 1 < (p : ℤ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp_sub_pos : 0 < (p : ℤ) - 1 := by omega
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hpow_gt : 1 < (p : ℤ) ^ n := one_lt_pow₀ hp_one hn_ne
  have hprod_pos : 0 < ((p : ℤ) - 1) * ((p : ℤ) ^ n - 1) := by
    nlinarith
  nlinarith

theorem artinHasseTailValuationIndex_ge_two {n : ℕ} (hn : 2 ≤ n) :
    artinHasseTailValuationIndex p 2 ≤
      artinHasseTailValuationIndex p n := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
      exact ih.trans
        (le_of_lt (artinHasseTailValuationIndex_lt_succ (p := p) (by omega)))

/-- Every predicted tail valuation is at least the `n = 2` valuation
`(p - 1)^2`. -/
theorem artinHasseTailValuationIndex_ge_sq {n : ℕ} (hn : 2 ≤ n) :
    ((p : ℤ) - 1) ^ 2 ≤ artinHasseTailValuationIndex p n := by
  rw [← artinHasseTailValuationIndex_two (p := p)]
  exact artinHasseTailValuationIndex_ge_two (p := p) hn

end FormalDwork

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The valuation-completion integer ring used for finite trace formulas. -/
abbrev ValuedIntegerRing : Type _ :=
  Furtwaengler.KummerArtinHasse.LambdaValuedIntegerRing p K

/-- The valuation-completion field used for finite trace formulas. -/
abbrev ValuedCompletion : Type _ :=
  Furtwaengler.KummerArtinHasse.LambdaValuedCompletion p K

/-- `lambda = zeta_p - 1` in the valuation-completion integer ring. -/
def valuedCyclotomicLambdaInteger : ValuedIntegerRing p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedPiInteger p K

/-- `lambda = zeta_p - 1` in the valuation-completion field. -/
def valuedCyclotomicLambda : ValuedCompletion p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedPi p K

/-- `zeta_p` in the valuation-completion integer ring. -/
def valuedCyclotomicZetaInteger : ValuedIntegerRing p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedZetaInteger p K

/-- `zeta_p` in the valuation-completion field. -/
def valuedCyclotomicZeta : ValuedCompletion p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedZeta p K

@[simp]
theorem valuedCyclotomicZeta_pow_eq_one :
    valuedCyclotomicZeta p K ^ p = 1 := by
  change (algebraMap K (ValuedCompletion p K)
      (IsCyclotomicExtension.zeta p ℚ K)) ^ p = 1
  rw [← map_pow, (IsCyclotomicExtension.zeta_spec p ℚ K).pow_eq_one, map_one]

/-- The global field unit attached to `zeta_p - 1`. -/
def globalCyclotomicLambdaFieldUnit : Kˣ :=
  Furtwaengler.KummerArtinHasse.lambdaPiFieldUnit p K

theorem globalCyclotomicLambdaFieldUnit_valuation :
    (Furtwaengler.KummerArtinHasse.lambdaHeightOne p K).valuation K
        (globalCyclotomicLambdaFieldUnit p K : K) =
      WithZero.exp (-1 : ℤ) :=
  Furtwaengler.KummerArtinHasse.lambdaPiFieldUnit_valuation (p := p) (K := K)

/-- The lambda valuation of `zeta_p - 1` in the valuation completion. -/
theorem valuedCyclotomicLambda_valuation :
    Valued.v (valuedCyclotomicLambda p K) = WithZero.exp (-1 : ℤ) := by
  change Valued.v
      (algebraMap K (ValuedCompletion p K)
        (globalCyclotomicLambdaFieldUnit p K : K)) =
    WithZero.exp (-1 : ℤ)
  rw [show algebraMap K (ValuedCompletion p K)
      (globalCyclotomicLambdaFieldUnit p K : K) =
        ((globalCyclotomicLambdaFieldUnit p K : K) : ValuedCompletion p K) from rfl]
  rw [Valued.valuedCompletion_apply]
  exact globalCyclotomicLambdaFieldUnit_valuation (p := p) (K := K)

end PadicLogSetup
end CyclotomicUnits
end KummerCriterion

end
