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









end Furtwaengler

end BernoulliRegular

end
