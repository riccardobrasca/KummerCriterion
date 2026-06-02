module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete

/-!
# Full Teichmuller Dwork product setup

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')




/-- The `i`-th truncated Artin-Hasse theta factor at the Teichmüller
Frobenius power attached to `traceScale * y`. -/
noncomputable def artinHasseThetaFactor (N : ℕ) (y : kˣ)
    (i : Fin F.toConcreteStickelbergerSetup.f) : 𝓞 R' :=
  dworkThetaTrunc
    (dworkCoeffArtinHasse F.toConcreteStickelbergerSetup) N
    ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))





/-- The `i`-th truncated Artin-Hasse theta factor with an explicit parameter
and precision-indexed coefficient representatives. -/
noncomputable def artinHasseThetaFactorAtTo (γ : 𝓞 R') (N : ℕ) (y : kˣ)
    (i : Fin F.toConcreteStickelbergerSetup.f) : 𝓞 R' :=
  dworkThetaTrunc
    (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ N) N
    ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))










/-! ### Named exact quotient target for the all-order Dwork endpoint -/







/-! ### Finite Artin-Hasse-Witt Teichmüller surface -/

/-- Quotient-level Artin-Hasse factor attached to one Witt-Teichmüller
representative. This is the presentation-level surface for the finite
Artin-Hasse-Witt character; proving that it descends/adds on arbitrary Witt
vectors is the separate carry-cancellation step. -/
noncomputable def artinHasseWittTeichFactor
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (x : k) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
    (ε * θ (WittVector.teichmuller ℓ x))


/-- On a single Teichmüller unit, the presentation-level AH-Witt factor is
the existing one-variable truncated Artin-Hasse factor at the selected
integral Teichmüller lift. -/
theorem artinHasseWittTeichFactor_unit_eq_trunc_eval
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (x : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x)
    F.artinHasseWittTeichFactor N ε (x : k) =
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε * zbar) := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x)
  rw [artinHasseWittTeichFactor]
  rw [F.wittThetaModQPow_teichmuller_unit N x]






end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
