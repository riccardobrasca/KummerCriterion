module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.UnitQuotient.DeltaAction
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.ZMod.Units

/-!
# Cyclotomic Galois lifts for the `{p, ℓ}` field

This file packages the CRT construction of the cyclotomic automorphism of
`ℚ(ζ_{pℓ})` whose exponent is a prescribed unit modulo `p` and is `1`
modulo `ℓ`. This is the Galois-theoretic input needed by the REF-18
covariance bridge: it gives honest automorphisms fixing the additive
`ℓ`-root while restricting to the standard `p`-cyclotomic action.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

/-- Positivity of the product conductor `p * ℓ`. -/
lemma pairConductor_pos : 0 < p * ℓ :=
  Nat.mul_pos (Fact.out : Nat.Prime p).pos (Fact.out : Nat.Prime ℓ).pos

/-! ### Source-conductor cyclotomic lifts -/

/-- Positivity of the source conductor `ℓ * n`. -/
lemma sourceConductor_pos {n : ℕ} [NeZero n] : 0 < ℓ * n :=
  Nat.mul_pos (Fact.out : Nat.Prime ℓ).pos (Nat.pos_of_ne_zero (NeZero.ne n))

/-- A unit modulo `n` lifting the prescribed unit modulo `p`.  This is the
point where we avoid choosing the possibly non-unit representative `a.val`
modulo `n`; `ZMod.unitsMap_surjective` supplies an honest lift. -/
noncomputable def sourceConductorUnitNComponent
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (a : CyclotomicUnitDelta p) :
    (ZMod n)ˣ :=
  Classical.choose (ZMod.unitsMap_surjective hpn a)

lemma sourceConductorUnitNComponent_spec
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (a : CyclotomicUnitDelta p) :
    ZMod.unitsMap hpn (sourceConductorUnitNComponent (p := p) hpn a) = a :=
  Classical.choose_spec (ZMod.unitsMap_surjective hpn a)


/-- The exponent modulo `ℓ * n` whose CRT image is `(1, b)`, where
`b ∈ (ZMod n)ˣ` is a chosen lift of `a ∈ (ZMod p)ˣ`. -/
noncomputable def sourceConductorUnitOfPAndOne
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    (a : CyclotomicUnitDelta p) : (ZMod (ℓ * n))ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hℓn).toMulEquiv).symm
    (MulEquiv.prodUnits.symm
      (1, sourceConductorUnitNComponent (p := p) hpn a))


/-- The source-conductor CRT lift is `1` modulo `ℓ`. -/
lemma sourceConductorUnitOfPAndOne_cast_ell
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    (a : CyclotomicUnitDelta p) :
    (((sourceConductorUnitOfPAndOne (p := p) hpn hℓn a :
        (ZMod (ℓ * n))ˣ) : ZMod (ℓ * n)).cast : ZMod ℓ) = 1 := by
  have hpair :
      ((MulEquiv.prodUnits.symm
          (1, sourceConductorUnitNComponent (p := p) hpn a) :
          (ZMod ℓ × ZMod n)ˣ) : ZMod ℓ × ZMod n) =
        ((1 : ZMod ℓ),
          (sourceConductorUnitNComponent (p := p) hpn a : ZMod n)) := by
    rfl
  have h :
      (ZMod.chineseRemainder hℓn
          (((sourceConductorUnitOfPAndOne (p := p) hpn hℓn a :
            (ZMod (ℓ * n))ˣ) : ZMod (ℓ * n)))) =
        ((1 : ZMod ℓ),
          (sourceConductorUnitNComponent (p := p) hpn a : ZMod n)) := by
    rw [sourceConductorUnitOfPAndOne, Units.mapEquiv_symm,
      Units.coe_mapEquiv, hpair]
    exact (ZMod.chineseRemainder hℓn).apply_symm_apply _
  simpa [ZMod.chineseRemainder] using congrArg Prod.fst h

/-- The source-conductor CRT lift reduces to the chosen unit modulo `n`. -/
lemma sourceConductorUnitOfPAndOne_cast_n
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    (a : CyclotomicUnitDelta p) :
    (((sourceConductorUnitOfPAndOne (p := p) hpn hℓn a :
        (ZMod (ℓ * n))ˣ) : ZMod (ℓ * n)).cast : ZMod n) =
      sourceConductorUnitNComponent (p := p) hpn a := by
  have hpair :
      ((MulEquiv.prodUnits.symm
          (1, sourceConductorUnitNComponent (p := p) hpn a) :
          (ZMod ℓ × ZMod n)ˣ) : ZMod ℓ × ZMod n) =
        ((1 : ZMod ℓ),
          (sourceConductorUnitNComponent (p := p) hpn a : ZMod n)) := by
    rfl
  have h :
      (ZMod.chineseRemainder hℓn
          (((sourceConductorUnitOfPAndOne (p := p) hpn hℓn a :
            (ZMod (ℓ * n))ˣ) : ZMod (ℓ * n)))) =
        ((1 : ZMod ℓ),
          (sourceConductorUnitNComponent (p := p) hpn a : ZMod n)) := by
    rw [sourceConductorUnitOfPAndOne, Units.mapEquiv_symm,
      Units.coe_mapEquiv, hpair]
    exact (ZMod.chineseRemainder hℓn).apply_symm_apply _
  simpa [ZMod.chineseRemainder] using congrArg Prod.snd h

/-- Natural-number congruence form of the modulo-`n` CRT property. -/
lemma sourceConductorUnitOfPAndOne_modEq_n
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    (a : CyclotomicUnitDelta p) :
    (sourceConductorUnitOfPAndOne (p := p) hpn hℓn a).val.val ≡
      (sourceConductorUnitNComponent (p := p) hpn a).val.val [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
  simpa using sourceConductorUnitOfPAndOne_cast_n (p := p) hpn hℓn a

/-- Natural-number congruence form of the chosen lift modulo `p`. -/
lemma sourceConductorUnitNComponent_modEq_p
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (a : CyclotomicUnitDelta p) :
    (sourceConductorUnitNComponent (p := p) hpn a).val.val ≡
      (a : ZMod p).val [MOD p] := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hunit := sourceConductorUnitNComponent_spec (p := p) hpn a
  have hcast :
      (((sourceConductorUnitNComponent (p := p) hpn a : (ZMod n)ˣ) :
          ZMod n).cast : ZMod p) = a := by
    simpa [ZMod.unitsMap_val] using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hunit
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
  simpa using hcast

/-- Natural-number congruence form of the modulo-`p` source-conductor
property. -/
lemma sourceConductorUnitOfPAndOne_modEq_p
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    (a : CyclotomicUnitDelta p) :
    (sourceConductorUnitOfPAndOne (p := p) hpn hℓn a).val.val ≡
      (a : ZMod p).val [MOD p] :=
  ((sourceConductorUnitOfPAndOne_modEq_n (p := p) hpn hℓn a).of_dvd hpn).trans
      (sourceConductorUnitNComponent_modEq_p (p := p) hpn a)

/-- Natural-number congruence form of the modulo-`ℓ` source-conductor
property. -/
lemma sourceConductorUnitOfPAndOne_modEq_one_ell
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    (a : CyclotomicUnitDelta p) :
    (sourceConductorUnitOfPAndOne (p := p) hpn hℓn a).val.val ≡ 1 [MOD ℓ] := by
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val]
  simpa using sourceConductorUnitOfPAndOne_cast_ell (p := p) hpn hℓn a

/-- Unit-map form of the modulo-`p` source-conductor property. -/
lemma sourceConductorUnitOfPAndOne_unitsMap_p
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    (a : CyclotomicUnitDelta p) :
    ZMod.unitsMap (dvd_trans hpn (dvd_mul_left n ℓ))
        (sourceConductorUnitOfPAndOne (p := p) hpn hℓn a) =
      a := by
  apply Units.ext
  rw [ZMod.unitsMap_val]
  have hmod := sourceConductorUnitOfPAndOne_modEq_p (p := p) hpn hℓn a
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  simpa [ZMod.natCast_val] using hmod

/-- The cyclotomic automorphism of the source-conductor field whose exponent
is `a` modulo `p` and `1` modulo `ℓ`. -/
noncomputable def sourceConductorSigmaOfPAndOne
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    (R' : Type*) [Field R'] [NumberField R'] [IsCyclotomicExtension {ℓ * n} ℚ R']
    (a : CyclotomicUnitDelta p) : Gal(R' / ℚ) :=
  haveI : NeZero (ℓ * n) := ⟨(sourceConductor_pos (ℓ := ℓ) (n := n)).ne'⟩
  (IsCyclotomicExtension.Rat.galEquivZMod (ℓ * n) R').symm
    (sourceConductorUnitOfPAndOne (p := p) hpn hℓn a)

@[simp]
lemma sourceConductorGalEquiv_sigmaOfPAndOne
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    {R' : Type*} [Field R'] [NumberField R'] [IsCyclotomicExtension {ℓ * n} ℚ R']
    (a : CyclotomicUnitDelta p) :
    IsCyclotomicExtension.Rat.galEquivZMod (ℓ * n) R'
        (sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a) =
      sourceConductorUnitOfPAndOne (p := p) hpn hℓn a := by
  haveI : NeZero (ℓ * n) := ⟨(sourceConductor_pos (ℓ := ℓ) (n := n)).ne'⟩
  exact (IsCyclotomicExtension.Rat.galEquivZMod (ℓ * n) R').apply_symm_apply _

/-- The source-conductor automorphism acts on every `p`-th root by the
prescribed `p`-component exponent. -/
theorem sourceConductorSigmaOfPAndOne_apply_p_root
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    {R' : Type*} [Field R'] [NumberField R'] [IsCyclotomicExtension {ℓ * n} ℚ R']
    (a : CyclotomicUnitDelta p) {x : R'} (hx : x ^ p = 1) :
    sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a x =
      x ^ (a : ZMod p).val := by
  haveI : NeZero (ℓ * n) := ⟨(sourceConductor_pos (ℓ := ℓ) (n := n)).ne'⟩
  have hx_source : x ^ (ℓ * n) = 1 := by
    obtain ⟨t, ht⟩ := dvd_trans hpn (dvd_mul_left n ℓ)
    rw [ht, pow_mul, hx, one_pow]
  have hσ :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (n := ℓ * n) (K := R')
      (σ := sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a)
      (x := x) hx_source
  rw [sourceConductorGalEquiv_sigmaOfPAndOne (p := p) hpn hℓn a] at hσ
  calc
    sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a x
        = x ^ (sourceConductorUnitOfPAndOne (p := p) hpn hℓn a).val.val := hσ
    _ = x ^ (a : ZMod p).val :=
          pow_eq_pow_of_modEq
            (sourceConductorUnitOfPAndOne_modEq_p (p := p) hpn hℓn a) hx

/-- The source-conductor automorphism fixes every `ℓ`-th root. -/
theorem sourceConductorSigmaOfPAndOne_apply_ell_root
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    {R' : Type*} [Field R'] [NumberField R'] [IsCyclotomicExtension {ℓ * n} ℚ R']
    (a : CyclotomicUnitDelta p) {x : R'} (hx : x ^ ℓ = 1) :
    sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a x = x := by
  haveI : NeZero (ℓ * n) := ⟨(sourceConductor_pos (ℓ := ℓ) (n := n)).ne'⟩
  have hx_source : x ^ (ℓ * n) = 1 := by
    rw [pow_mul, hx, one_pow]
  have hσ :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (n := ℓ * n) (K := R')
      (σ := sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a)
      (x := x) hx_source
  rw [sourceConductorGalEquiv_sigmaOfPAndOne (p := p) hpn hℓn a] at hσ
  calc
    sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a x
        = x ^ (sourceConductorUnitOfPAndOne (p := p) hpn hℓn a).val.val := hσ
    _ = x ^ 1 :=
          pow_eq_pow_of_modEq
            (sourceConductorUnitOfPAndOne_modEq_one_ell (p := p) hpn hℓn a) hx
    _ = x := by rw [pow_one]

/-- Restricting the source-conductor automorphism to `K = ℚ(ζ_p)` gives the
standard `p`-cyclotomic automorphism indexed by `a`. -/
theorem sourceConductorSigmaOfPAndOne_restrict_eq
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {ℓ * n} ℚ R']
    (a : CyclotomicUnitDelta p) :
    (sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a).restrictNormal K =
      cyclotomicSigmaOfUnit (p := p) K a := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  haveI : NeZero (ℓ * n) := ⟨(sourceConductor_pos (ℓ := ℓ) (n := n)).ne'⟩
  apply (IsCyclotomicExtension.Rat.galEquivZMod p K).injective
  rw [IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
      (n := ℓ * n) (K := R') (m := p) (F := K)
      (h := dvd_trans hpn (dvd_mul_left n ℓ))
      (σ := sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a),
    cyclotomicGalEquivZMod_sigmaOfUnit (p := p) (K := K) a,
    sourceConductorGalEquiv_sigmaOfPAndOne (p := p) hpn hℓn a]
  exact sourceConductorUnitOfPAndOne_unitsMap_p (p := p) hpn hℓn a

/-- Ring-of-integers form of `sourceConductorSigmaOfPAndOne_restrict_eq`,
matching the `hτ_K` hypothesis used by the flexible REF-18 covariance
bridge. -/
theorem sourceConductorSigmaOfPAndOne_ringOfIntegers_apply
    {n : ℕ} [NeZero n] (hpn : p ∣ n) (hℓn : ℓ.Coprime n)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {ℓ * n} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (a : CyclotomicUnitDelta p) (x : 𝓞 K) :
    (sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a : R' →+* R')
        (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
      algebraMap (𝓞 R') R'
        (algebraMap (𝓞 K) (𝓞 R')
          (cyclotomicRingOfIntegersEquiv (p := p) K a x)) := by
  let σ := sourceConductorSigmaOfPAndOne (p := p) hpn hℓn R' a
  have hrestrict : σ.restrictNormal K = cyclotomicSigmaOfUnit (p := p) K a :=
    sourceConductorSigmaOfPAndOne_restrict_eq (p := p) hpn hℓn a
  change σ (algebraMap K R' (x : K)) =
    algebraMap K R' ((cyclotomicRingOfIntegersEquiv (p := p) K a x : 𝓞 K) : K)
  calc
    σ (algebraMap K R' (x : K))
        = algebraMap K R' (σ.restrictNormal K (x : K)) :=
            (AlgEquiv.restrictNormal_commutes (χ := σ) (E := K) (x := (x : K))).symm
    _ = algebraMap K R' (cyclotomicSigmaOfUnit (p := p) K a (x : K)) := by
            rw [hrestrict]
    _ = algebraMap K R'
          ((cyclotomicRingOfIntegersEquiv (p := p) K a x : 𝓞 K) : K) := by
            rfl


















end Furtwaengler

end BernoulliRegular
