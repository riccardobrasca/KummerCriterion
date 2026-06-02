module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrincipalBridge
public import BernoulliRegular.TotallyRealSubfield.Conjugation
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import BernoulliRegular.UnitQuotient.TorsionQuotient
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.Part2

/-!
# Principal unit factor (REF-18 Phase 2, sub-piece U)

For a nonzero principal ideal `(α)`, the actual multiplicative Φ element
`Φ((α))` and the explicit Stickelberger principal generator
`α^Θ = stickelbergerPrincipalGen α` generate the same ideal. Hence they differ
by a unit:

```
Φ((α)) = u(α) · α^Θ.
```

This file formalizes the honest element-level U-chain interface:

* `PrincipalUnitFactorData α Φα` is the specific unit-factor equation for an
  actual principal Φ element `Φα`.
* `PrincipalUnitFactorData.nonempty_of_nonzero` proves existence of such a
  unit from the already formalized Φ-span theorem.
* If that specific unit is `±1`, its prime residue symbols vanish.
* `ChosenPrimaryUnitFactorProductSymbolZero α` is the reflection-facing
  chosen-object product condition: the same actual Φ element has locally
  trivial product symbols for `Φ((α)) · α` away from `α`.
* `ChosenPrimaryUnitFactorSymbolTrivial α` is the natural chosen-object
  downstream output from one normalized actual principal Φ element.
* `PrimaryUnitFactorSymbolTrivial α` is the stronger uniform downstream
  hypothesis over the current broad `PhiPrincipalElement` API.
* The concrete U4 endpoint is proved in
  `PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts` and
  `ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts`: for an
  actual principal Φ product, prime-level semi-primarity plus the prime
  conjugation-norm identities force the specific unit factor to be `±1`, hence
  its prime symbols vanish.

What remains outside this file is constructing the actual principal Φ product
from `K2_2SourceData` for every normalized prime factor and proving the
conjugation compatibility needed for those prime norm identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The product of all cyclotomic Galois conjugates of an algebraic integer is
its integer norm. -/
theorem prod_cyclotomicRingOfIntegersEquiv_eq_intNorm (α : 𝓞 K) :
    (∏ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a α) =
        ((Algebra.norm ℤ α : ℤ) : 𝓞 K) := by
  classical
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois ({p} : Set ℕ) ℚ K
  apply RingOfIntegers.ext
  change algebraMap (𝓞 K) K
      (∏ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a α) =
    algebraMap (𝓞 K) K (((Algebra.norm ℤ α : ℤ) : 𝓞 K))
  rw [map_prod]
  have hprod :
      (∏ a : CyclotomicUnitDelta p,
        algebraMap (𝓞 K) K
          (cyclotomicRingOfIntegersEquiv (p := p) K a α)) =
        ∏ σ : Gal(K / ℚ), σ (α : K) := by
    symm
    refine Fintype.prod_equiv
      (cyclotomicGalEquivZMod (p := p) K)
      (fun σ : Gal(K / ℚ) => σ (α : K))
      (fun a : CyclotomicUnitDelta p =>
        algebraMap (𝓞 K) K
          (cyclotomicRingOfIntegersEquiv (p := p) K a α)) ?_
    intro σ
    have ha : cyclotomicSigmaOfUnit (p := p) K
        (cyclotomicGalEquivZMod (p := p) K σ) = σ := by
      unfold cyclotomicSigmaOfUnit
      exact (cyclotomicGalEquivZMod (p := p) K).symm_apply_apply σ
    unfold cyclotomicRingOfIntegersEquiv
    change σ (α : K) =
      algebraMap (𝓞 K) K
        ((MulSemiringAction.toRingEquiv (Gal(K / ℚ)) (𝓞 K)
          (cyclotomicSigmaOfUnit (p := p) K
            (cyclotomicGalEquivZMod (p := p) K σ))) α)
    rw [ha]
    change σ (α : K) = algebraMap (𝓞 K) K (σ • α)
    exact (algebraMap.coe_smul' σ α K).symm
  rw [hprod]
  rw [← Algebra.norm_eq_prod_automorphisms (K := ℚ) (L := K) (x := (α : K))]
  rw [← Algebra.coe_norm_int α]
  simp







/-- Right-cancelling a semi-primary element which is prime to `ζ - 1`
preserves semi-primarity.

This is the λ² modular-inverse calculation needed in U4.  If
`y ≡ a (mod (ζ - 1)^2)` and `ζ - 1 ∤ y`, then `p ∤ a`, so a Bezout inverse
of `a` modulo `p` gives an inverse of `y` modulo `(ζ - 1)^2`. -/
theorem isSemiPrimary_of_mul_right_of_not_zetaSubOne_dvd
    (hp_three : 3 ≤ p) {x y : 𝓞 K}
    (hxy : FLT37.IsSemiPrimary p (K := K) (x * y))
    (hy : FLT37.IsSemiPrimary p (K := K) y)
    (hy_not_dvd : ¬ FLT37.zetaSubOne p K ∣ y) :
    FLT37.IsSemiPrimary p (K := K) x := by
  let ε : 𝓞 K := FLT37.zetaSubOne p K
  obtain ⟨a, ha⟩ := hy
  obtain ⟨r, hr⟩ := hxy
  have hε_sq_dvd_p_nat :
      ε ^ 2 ∣ ((p : ℕ) : 𝓞 K) := by
    simpa [ε] using FLT37.zetaSubOne_sq_dvd_p (p := p) (K := K) hp_three
  have hε_sq_dvd_p_int :
      ε ^ 2 ∣ ((p : ℤ) : 𝓞 K) := by
    simpa using hε_sq_dvd_p_nat
  have hε_dvd_sq : ε ∣ ε ^ 2 := ⟨ε, by ring⟩
  have hε_dvd_p : ε ∣ ((p : ℤ) : 𝓞 K) :=
    hε_dvd_sq.trans hε_sq_dvd_p_int
  have hp_not_dvd_a : ¬ (p : ℤ) ∣ a := by
    intro hp_dvd_a
    have hε_dvd_y_sub_a : ε ∣ y - (a : 𝓞 K) :=
      hε_dvd_sq.trans (by simpa [ε] using ha)
    have hε_dvd_a : ε ∣ (a : 𝓞 K) := by
      obtain ⟨c, hc⟩ := hp_dvd_a
      rw [hc]
      convert hε_dvd_p.mul_right (c : 𝓞 K) using 1
      push_cast
      ring
    have hε_dvd_y : ε ∣ y := by
      have h := dvd_add hε_dvd_y_sub_a hε_dvd_a
      convert h using 1
      ring
    exact hy_not_dvd (by simpa [ε] using hε_dvd_y)
  have hcop_nat : Nat.Coprime a.natAbs p := by
    have hp_prime : Nat.Prime p := Fact.out
    rw [Nat.coprime_comm, hp_prime.coprime_iff_not_dvd]
    intro hp_dvd_abs
    exact hp_not_dvd_a
      ((Int.natCast_dvd (m := p) (n := a)).mpr hp_dvd_abs)
  have hcop_int : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa [Int.natAbs_natCast] using hcop_nat
  obtain ⟨b, c, hbez⟩ := hcop_int
  refine ⟨b * r, ?_⟩
  have haεsq : ε ^ 2 ∣ y - (a : 𝓞 K) := by
    simpa [ε] using ha
  have hdiff_y : ε ^ 2 ∣ (a : 𝓞 K) - y := by
    have h := haεsq.neg_right
    convert h using 1
    ring
  have hone_sub_by :
      ε ^ 2 ∣ (1 : 𝓞 K) - (b : 𝓞 K) * y := by
    have hterm₁ : ε ^ 2 ∣ (b : 𝓞 K) * ((a : 𝓞 K) - y) :=
      hdiff_y.mul_left (b : 𝓞 K)
    have hterm₂ : ε ^ 2 ∣ (c : 𝓞 K) * ((p : ℤ) : 𝓞 K) :=
      hε_sq_dvd_p_int.mul_left (c : 𝓞 K)
    have hsum := dvd_add hterm₁ hterm₂
    convert hsum using 1
    have hbez_cast :
        ((b * a + c * (p : ℤ) : ℤ) : 𝓞 K) = 1 := by
      rw [hbez]
      norm_num
    calc
      (1 : 𝓞 K) - (b : 𝓞 K) * y
          = ((b * a + c * (p : ℤ) : ℤ) : 𝓞 K) - (b : 𝓞 K) * y := by
              rw [hbez_cast]
      _ = (b : 𝓞 K) * ((a : 𝓞 K) - y) +
          (c : 𝓞 K) * ((p : ℤ) : 𝓞 K) := by
              push_cast
              ring
  have hrεsq : ε ^ 2 ∣ x * y - (r : 𝓞 K) := by
    simpa [ε] using hr
  have hterm₁ : ε ^ 2 ∣ (b : 𝓞 K) * (x * y - (r : 𝓞 K)) :=
    hrεsq.mul_left (b : 𝓞 K)
  have hterm₂ : ε ^ 2 ∣ x * ((1 : 𝓞 K) - (b : 𝓞 K) * y) :=
    hone_sub_by.mul_left x
  have hsum := dvd_add hterm₁ hterm₂
  convert hsum using 1
  calc
    x - ((b * r : ℤ) : 𝓞 K)
        = (b : 𝓞 K) * (x * y - (r : 𝓞 K)) +
          x * ((1 : 𝓞 K) - (b : 𝓞 K) * y) := by
            push_cast
            ring


/-! ### Semi-primary torsion units -/








/-! ### Specific principal unit factor -/

/-- **Specific principal Φ unit-factor data.**

The unit is tied to the actual principal Φ element `Φα`; it is not an
arbitrary unit that can be chosen independently at each denominator. -/
structure PrincipalUnitFactorData
    (α : 𝓞 K)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α) where
  /-- The unit factor relating `Φ((α))` to `α^Θ`. -/
  unit : 𝓞 K
  /-- The factor is a unit. -/
  unit_isUnit : IsUnit unit
  /-- The actual unit-factor equation. -/
  gamma_eq_unit_mul :
    Φα.gamma = unit * stickelbergerPrincipalGen (p := p) (K := K) α

namespace PrincipalUnitFactorData




/-- The concrete unit factor is semi-primary once the concrete principal Φ
element and the Stickelberger principal generator are semi-primary, with
`α^Θ` prime to `ζ - 1`.

This is the formal U4 cancellation step: it uses the actual equation
`Φ((α)) = u · α^Θ` and cancels `α^Θ` modulo `(ζ - 1)^2`; no arbitrary
unit-twisted Φ representative is being substituted. -/
theorem unit_isSemiPrimary_of_gamma_isSemiPrimary
    (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hgamma_semi : FLT37.IsSemiPrimary p (K := K) Φα.gamma)
    (h_stick_not_dvd :
      ¬ FLT37.zetaSubOne p K ∣
        stickelbergerPrincipalGen (p := p) (K := K) α) :
    FLT37.IsSemiPrimary p (K := K) U.unit := by
  have hstick_semi :
      FLT37.IsSemiPrimary p (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) :=
    isSemiPrimary_stickelbergerPrincipalGen
      (p := p) (K := K) hp_two hα_semi
  have hprod :
      FLT37.IsSemiPrimary p (K := K)
        (U.unit * stickelbergerPrincipalGen (p := p) (K := K) α) := by
    simpa [U.gamma_eq_unit_mul] using hgamma_semi
  exact isSemiPrimary_of_mul_right_of_not_zetaSubOne_dvd
    (p := p) (K := K) hp_three hprod hstick_semi h_stick_not_dvd

/-- Unit-valued version of
`PrincipalUnitFactorData.unit_isSemiPrimary_of_gamma_isSemiPrimary`. -/
theorem unitUnit_isSemiPrimary_of_gamma_isSemiPrimary
    (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hgamma_semi : FLT37.IsSemiPrimary p (K := K) Φα.gamma)
    (h_stick_not_dvd :
      ¬ FLT37.zetaSubOne p K ∣
        stickelbergerPrincipalGen (p := p) (K := K) α) :
    FLT37.IsSemiPrimary p (K := K) (U.unit_isUnit.unit : 𝓞 K) := by
  have h :=
    U.unit_isSemiPrimary_of_gamma_isSemiPrimary
      (p := p) (K := K) hp_two hp_three
      hα_semi hgamma_semi h_stick_not_dvd
  simpa [IsUnit.unit_spec U.unit_isUnit] using h




end PrincipalUnitFactorData
end Furtwaengler

end BernoulliRegular

end
