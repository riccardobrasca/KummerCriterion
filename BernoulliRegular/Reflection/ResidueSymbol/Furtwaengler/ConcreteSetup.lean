module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Setup
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Concrete Stickelberger setup (Layer 3, REF-18c2c4)

This file packages the arithmetic data needed to turn the abstract
`StickelbergerSetup` API into the concrete cyclotomic situation used by the
digit-sum Stickelberger congruence.

The bundle intentionally keeps the difficult arithmetic assertions as fields:
the prime `Q` above `ℓ`, the integral element `π = ζ_ℓ - 1`, and the residue
map from `𝓞 R'` to the finite field. Later Layer 3 tickets can strengthen this
data by proving the canonical identification of `Q` and constructing
Teichmüller lifts.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Concrete arithmetic data for the Stickelberger congruence over a
cyclotomic field.

The finite field `k` is the residue-field model used in the Gauss-sum layer.
The number field `K` is the `p`-th cyclotomic field, and `R'` is a larger
cyclotomic field containing the `p`- and `ℓ`-power roots needed for the
residue and additive characters. -/
structure ConcreteStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] where
  /-- The residue characteristic is different from the Kummer exponent. -/
  hℓ_ne_p : ℓ ≠ p
  /-- Residue degree, with `#k = ℓ ^ f`. -/
  f : ℕ
  /-- The chosen finite field has cardinality `ℓ ^ f`. -/
  card_k : Fintype.card k = ℓ ^ f
  /-- A primitive `p`-th root of unity in the residue field. -/
  zeta_k : kˣ
  /-- Primitivity of `zeta_k`. -/
  hzeta_k : IsPrimitiveRoot zeta_k p
  /-- The cardinality compatibility needed for the residue character. -/
  hdiv : p ∣ Fintype.card k - 1
  /-- A primitive `p`-th root of unity in `R'`. -/
  zeta_p : R'ˣ
  /-- Primitivity of `zeta_p`. -/
  hzeta_p : IsPrimitiveRoot zeta_p p
  /-- An integral lift of `zeta_p` to `𝓞 R'`, chosen compatibly with the
  residue-field root `zeta_k`. -/
  zeta_p_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`. -/
  zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ)
  /-- A primitive `ℓ`-th root of unity in `R'`, used for the additive character. -/
  zeta_ell : R'
  /-- Primitivity of `zeta_ell`. -/
  hzeta_ell : IsPrimitiveRoot zeta_ell ℓ
  /-- An integral lift of `zeta_ell` to `𝓞 R'`. -/
  zeta_ell_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`. -/
  zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell
  /-- The uniformizer candidate `π = ζ_ℓ - 1`. -/
  π : 𝓞 R'
  /-- Defining equation for `π` in the ring of integers. -/
  hπ : π = zeta_ell_int - 1
  /-- A prime ideal of `𝓞 R'` above `ℓ`. -/
  Q : Ideal (𝓞 R')
  /-- Primality of `Q`. -/
  hQ_prime : Q.IsPrime
  /-- The rational prime `ℓ` lies in `Q`. -/
  hQ : (ℓ : 𝓞 R') ∈ Q
  /-- A concrete residue map onto the finite-field model `k`. -/
  residueMap : 𝓞 R' →+* k
  /-- The residue map is onto the chosen finite field model. -/
  residueMap_surjective : Function.Surjective residueMap
  /-- The kernel of the residue map is `Q`. -/
  residueMap_ker : RingHom.ker residueMap = Q
  /-- Compatibility between the target primitive `p`-th root and the
  residue-field primitive root. This pins down the Teichmüller convention used
  by `residueCharInt`. -/
  zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k)
  /-- The primitive additive character on `k`. -/
  psi : AddChar k R'
  /-- Primitivity of the additive character. -/
  hpsi : psi.IsPrimitive
  /-- Exponent function expressing `psi` in powers of `ζ_ℓ`. -/
  psiExponent : k → ℕ
  /-- The additive character has the expected `ζ_ℓ`-power form. -/
  psi_eq_zeta_ell_pow : ∀ x : k, psi x = zeta_ell ^ psiExponent x

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')






/-- The integral lift of `ζ_p` maps to the selected root in `R'`. -/
@[simp]
theorem algebraMap_zeta_p_int :
    algebraMap (𝓞 R') R' S.zeta_p_int = (S.zeta_p : R'ˣ) :=
  S.zeta_p_int_spec

/-- The integral lift of `ζ_p` is still primitive. -/
theorem zeta_p_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int p := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.algebraMap_zeta_p_int] using (IsPrimitiveRoot.coe_units_iff.mpr S.hzeta_p)


/-- The integral lift of `ζ_ℓ` is primitive in `𝓞 R'`. -/
theorem zeta_ell_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_ell_int ℓ := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_ell_int_spec] using S.hzeta_ell


/-- The prime ideal `Q` is available as an instance when working from the
bundle. -/
protected instance Q_isPrime : S.Q.IsPrime :=
  S.hQ_prime





/-- The residue map has kernel `Q`. -/
theorem residueMap_ker_eq : RingHom.ker S.residueMap = S.Q :=
  S.residueMap_ker

/-- Membership in the selected prime is equivalent to vanishing under the
residue map. -/
theorem mem_Q_iff_residueMap_eq_zero (x : 𝓞 R') :
    x ∈ S.Q ↔ S.residueMap x = 0 := by
  rw [← S.residueMap_ker_eq, RingHom.mem_ker]

/-- The residue map identifies the quotient `𝓞 R' / Q` with the chosen
finite-field model `k`. -/
noncomputable def residueQuotientEquiv : 𝓞 R' ⧸ S.Q ≃+* k :=
  (Ideal.quotientEquiv S.Q (RingHom.ker S.residueMap) (RingEquiv.refl (𝓞 R')) (by
    simpa using S.residueMap_ker)).trans
    (RingHom.quotientKerEquivOfSurjective S.residueMap_surjective)

@[simp]
theorem residueQuotientEquiv_mk (x : 𝓞 R') :
    S.residueQuotientEquiv (Ideal.Quotient.mk S.Q x) = S.residueMap x := by
  simp [residueQuotientEquiv]

/-- The chosen finite field has cardinality `ℓ ^ f`. -/
theorem card_k_eq : Fintype.card k = ℓ ^ S.f :=
  S.card_k

/-- The integral lift of `ζ_ℓ` maps to the selected root in `R'`. -/
theorem algebraMap_zeta_ell_int : algebraMap (𝓞 R') R' S.zeta_ell_int = S.zeta_ell :=
  S.zeta_ell_int_spec

/-- The defining equation for `π` in `𝓞 R'`. -/
theorem π_def : S.π = S.zeta_ell_int - 1 :=
  S.hπ


/-- The selected prime above `ℓ` contains `π = ζ_ℓ - 1`. This is the
ramification containment available in the mixed cyclotomic field
`ℚ(ζ_p, ζ_ℓ)`. -/
theorem π_mem_Q : S.π ∈ S.Q := by
  rw [S.hπ]
  exact zeta_sub_one_mem_of_natCast_mem S.zeta_ell_int_isPrimitiveRoot S.hQ



/-- The additive character is expressed in powers of the chosen primitive
`ℓ`-th root. -/
theorem psi_pow_form (x : k) : S.psi x = S.zeta_ell ^ S.psiExponent x :=
  S.psi_eq_zeta_ell_pow x

/-- Forget the concrete arithmetic data and recover the abstract
`StickelbergerSetup` used by the algebraic Gauss-sum API. -/
def abstractSetup : StickelbergerSetup p k R' where
  zeta_q := S.zeta_k
  hzeta_q := S.hzeta_k
  hdiv := S.hdiv
  zeta_R := S.zeta_p
  hzeta_R := S.hzeta_p

end ConcreteStickelbergerSetup

/-- Conductor-flexible concrete arithmetic data for the Stickelberger
congruence.

This is the same explicit arithmetic payload as `ConcreteStickelbergerSetup`,
but without the exact pair-cyclotomic typeclass
`[IsCyclotomicExtension {p, ℓ} ℚ R']`.  It is intended for enlarged
cyclotomic fields whose conductor contains the required roots while not being
definitionally the pair conductor. -/
structure ConductorFlexibleConcreteStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R'] where
  /-- The residue characteristic is different from the Kummer exponent. -/
  hℓ_ne_p : ℓ ≠ p
  /-- Residue degree, with `#k = ℓ ^ f`. -/
  f : ℕ
  /-- The chosen finite field has cardinality `ℓ ^ f`. -/
  card_k : Fintype.card k = ℓ ^ f
  /-- A primitive `p`-th root of unity in the residue field. -/
  zeta_k : kˣ
  /-- Primitivity of `zeta_k`. -/
  hzeta_k : IsPrimitiveRoot zeta_k p
  /-- The cardinality compatibility needed for the residue character. -/
  hdiv : p ∣ Fintype.card k - 1
  /-- A primitive `p`-th root of unity in `R'`. -/
  zeta_p : R'ˣ
  /-- Primitivity of `zeta_p`. -/
  hzeta_p : IsPrimitiveRoot zeta_p p
  /-- An integral lift of `zeta_p` to `𝓞 R'`. -/
  zeta_p_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`. -/
  zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ)
  /-- A primitive `ℓ`-th root of unity in `R'`, used for the additive character. -/
  zeta_ell : R'
  /-- Primitivity of `zeta_ell`. -/
  hzeta_ell : IsPrimitiveRoot zeta_ell ℓ
  /-- An integral lift of `zeta_ell` to `𝓞 R'`. -/
  zeta_ell_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`. -/
  zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell
  /-- The uniformizer candidate `π = ζ_ℓ - 1`. -/
  π : 𝓞 R'
  /-- Defining equation for `π` in the ring of integers. -/
  hπ : π = zeta_ell_int - 1
  /-- A prime ideal of `𝓞 R'` above `ℓ`. -/
  Q : Ideal (𝓞 R')
  /-- Primality of `Q`. -/
  hQ_prime : Q.IsPrime
  /-- The rational prime `ℓ` lies in `Q`. -/
  hQ : (ℓ : 𝓞 R') ∈ Q
  /-- A concrete residue map onto the finite-field model `k`. -/
  residueMap : 𝓞 R' →+* k
  /-- The residue map is onto the chosen finite field model. -/
  residueMap_surjective : Function.Surjective residueMap
  /-- The kernel of the residue map is `Q`. -/
  residueMap_ker : RingHom.ker residueMap = Q
  /-- Compatibility between the target primitive `p`-th root and the
  residue-field primitive root. -/
  zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k)
  /-- The primitive additive character on `k`. -/
  psi : AddChar k R'
  /-- Primitivity of the additive character. -/
  hpsi : psi.IsPrimitive
  /-- Exponent function expressing `psi` in powers of `ζ_ℓ`. -/
  psiExponent : k → ℕ
  /-- The additive character has the expected `ζ_ℓ`-power form. -/
  psi_eq_zeta_ell_pow : ∀ x : k, psi x = zeta_ell ^ psiExponent x

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')

/-- The selected over-prime is prime. -/
protected instance Q_isPrime : S.Q.IsPrime :=
  S.hQ_prime

/-- The residue map has kernel `Q`. -/
theorem residueMap_ker_eq : RingHom.ker S.residueMap = S.Q :=
  S.residueMap_ker

/-- Membership in the selected prime is equivalent to vanishing under the
residue map. -/
theorem mem_Q_iff_residueMap_eq_zero (x : 𝓞 R') :
    x ∈ S.Q ↔ S.residueMap x = 0 := by
  rw [← S.residueMap_ker_eq, RingHom.mem_ker]




/-- Forget the concrete arithmetic data and recover the abstract
`StickelbergerSetup` used by the algebraic Gauss-sum API. -/
def abstractSetup : StickelbergerSetup p k R' where
  zeta_q := S.zeta_k
  hzeta_q := S.hzeta_k
  hdiv := S.hdiv
  zeta_R := S.zeta_p
  hzeta_R := S.hzeta_p

/-- The residue character specialised to the conductor-flexible bundle. -/
def residueChar : MulChar k R' :=
  S.abstractSetup.residueChar

/-- The integral lift of `ζ_p` is primitive in `𝓞 R'`. -/
theorem zeta_p_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int p := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_p_int_spec] using (IsPrimitiveRoot.coe_units_iff.mpr S.hzeta_p)

/-- Unit form of the integral `p`-th root. -/
noncomputable def zeta_p_int_unit : (𝓞 R')ˣ :=
  (S.zeta_p_int_isPrimitiveRoot.isUnit (Fact.out : Nat.Prime p).ne_zero).unit

@[simp]
theorem zeta_p_int_unit_coe : (S.zeta_p_int_unit : 𝓞 R') = S.zeta_p_int := by
  simp [zeta_p_int_unit]


/-- The unit lift of `ζ_p` remains primitive. -/
theorem zeta_p_int_unit_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int_unit p := by
  simpa [zeta_p_int_unit] using
    S.zeta_p_int_isPrimitiveRoot.isUnit_unit (Fact.out : Nat.Prime p).ne_zero

/-- The residue character with values in the ring of integers. -/
noncomputable def residueCharInt : MulChar k (𝓞 R') :=
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  residueMulChar S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

/-- The integral lift of `ζ_ℓ` maps to the selected root in `R'`. -/
theorem algebraMap_zeta_ell_int : algebraMap (𝓞 R') R' S.zeta_ell_int = S.zeta_ell :=
  S.zeta_ell_int_spec

/-- The defining equation for `π` in `𝓞 R'`. -/
theorem π_def : S.π = S.zeta_ell_int - 1 :=
  S.hπ


/-- The selected prime above `ℓ` contains `π = ζ_ℓ - 1`. -/
theorem π_mem_Q : S.π ∈ S.Q := by
  rw [S.π_def]
  have hprim : IsPrimitiveRoot S.zeta_ell_int ℓ := by
    refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
    simpa [S.zeta_ell_int_spec] using S.hzeta_ell
  exact zeta_sub_one_mem_of_natCast_mem hprim S.hQ


/-- The integral lift of `ζ_ℓ` is primitive in `𝓞 R'`. -/
theorem zeta_ell_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_ell_int ℓ := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_ell_int_spec] using S.hzeta_ell

/-- The additive character is expressed in powers of the chosen primitive
`ℓ`-th root. -/
theorem psi_pow_form (x : k) : S.psi x = S.zeta_ell ^ S.psiExponent x :=
  S.psi_eq_zeta_ell_pow x

/-- The integral additive character defined by the exponent form
`ψ(x) = ζ_ℓ ^ psiExponent x`. -/
noncomputable def psiInt : AddChar k (𝓞 R') where
  toFun x := S.zeta_ell_int ^ S.psiExponent x
  map_zero_eq_one' := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent 0) =
      algebraMap (𝓞 R') R' (1 : 𝓞 R')
    rw [map_pow, map_one, S.algebraMap_zeta_ell_int]
    simpa [S.psi_pow_form] using (AddChar.map_zero_eq_one S.psi)
  map_add_eq_mul' x y := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent (x + y)) =
      algebraMap (𝓞 R') R'
        (S.zeta_ell_int ^ S.psiExponent x * S.zeta_ell_int ^ S.psiExponent y)
    rw [map_mul, map_pow, map_pow, map_pow, S.algebraMap_zeta_ell_int]
    calc
      S.zeta_ell ^ S.psiExponent (x + y) = S.psi (x + y) := (S.psi_pow_form (x + y)).symm
      _ = S.psi x * S.psi y := AddChar.map_add_eq_mul S.psi x y
      _ = S.zeta_ell ^ S.psiExponent x * S.zeta_ell ^ S.psiExponent y := by
        rw [S.psi_pow_form x, S.psi_pow_form y]

/-- The concrete Gauss sum as an algebraic integer. -/
noncomputable def gaussSumInt (a : ℕ) : 𝓞 R' :=
  _root_.gaussSum (S.residueCharInt ^ a) S.psiInt

end ConductorFlexibleConcreteStickelbergerSetup

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- The old exact pair-cyclotomic concrete setup is a special case of the
conductor-flexible concrete API. -/
noncomputable def toConductorFlexible (S : ConcreteStickelbergerSetup ℓ p k K R') :
    ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' where
  hℓ_ne_p := S.hℓ_ne_p
  f := S.f
  card_k := S.card_k
  zeta_k := S.zeta_k
  hzeta_k := S.hzeta_k
  hdiv := S.hdiv
  zeta_p := S.zeta_p
  hzeta_p := S.hzeta_p
  zeta_p_int := S.zeta_p_int
  zeta_p_int_spec := S.zeta_p_int_spec
  zeta_ell := S.zeta_ell
  hzeta_ell := S.hzeta_ell
  zeta_ell_int := S.zeta_ell_int
  zeta_ell_int_spec := S.zeta_ell_int_spec
  π := S.π
  hπ := S.hπ
  Q := S.Q
  hQ_prime := S.hQ_prime
  hQ := S.hQ
  residueMap := S.residueMap
  residueMap_surjective := S.residueMap_surjective
  residueMap_ker := S.residueMap_ker
  zeta_p_int_residue := S.zeta_p_int_residue
  psi := S.psi
  hpsi := S.hpsi
  psiExponent := S.psiExponent
  psi_eq_zeta_ell_pow := S.psi_eq_zeta_ell_pow

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular
