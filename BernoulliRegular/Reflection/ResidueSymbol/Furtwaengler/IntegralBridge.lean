module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerCongruence

/-!
# Integral target bridge for Stickelberger Gauss sums

This file moves the concrete Furtwängler Gauss sums from the field target `R'`
to the ring of integers `𝓞 R'`.  The digit-sum congruence is measured at the
concrete prime ideal `Q : Ideal (𝓞 R')`, so later Layer 2 arguments need the
same character values and Gauss sum as actual algebraic integers.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- Unit form of the integral `p`-th root, for constructing multiplicative
characters valued in `𝓞 R'`. -/
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
noncomputable def gaussSumInt (S : ConcreteStickelbergerSetup ℓ p k K R') (a : ℕ) : 𝓞 R' :=
  _root_.gaussSum (S.residueCharInt ^ a) S.psiInt

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular
