module

public import KummerCriterion.UnitQuotient.PermutationCharacters
public import FltRegular.NumberTheory.Cyclotomic.CyclRat
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.MulChar.Duality
import KummerCriterion.GaussSum.SignInvariant.Trace
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Unit quotients: the free character profile

This file records the representation-theoretic closing statement for the free
unit contribution. The permutation representation of
`Delta / {±1}` contains one copy of every quotient character. The free unit
part corresponds to the augmentation subrepresentation, so the trivial line is
removed and each nontrivial quotient character occurs with multiplicity one.

The comparison between the actual Dirichlet unit lattice and this augmentation
representation is the remaining number-theoretic input needed to turn this
abstract profile into the final `E/E^p` component statement.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

attribute [local instance] Fintype.ofFinite

variable (p : ℕ) [Fact p.Prime]

/-- For `p > 2`, the subgroup `{±1}` of `Delta = (ZMod p)^*` has order two. -/
theorem cyclotomicEvenDeltaSubgroup_card (hp_gt_two : 2 < p) :
    Fintype.card (CyclotomicEvenDeltaSubgroup p) = 2 := by
  change Fintype.card (Subgroup.zpowers (-1 : CyclotomicUnitDelta p)) = 2
  rw [Fintype.card_zpowers]
  have hp_ne_two : p ≠ 2 := by omega
  rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod p) p,
    if_neg hp_ne_two]

/-- For `p > 2`, the quotient `Delta / {±1}` has order `(p - 1) / 2`. -/
theorem cyclotomicEvenDelta_card (hp_gt_two : 2 < p) :
    Fintype.card (CyclotomicEvenDelta p) = (p - 1) / 2 := by
  have hcard :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CyclotomicEvenDeltaSubgroup p)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    show Fintype.card (CyclotomicUnitDelta p) = p - 1 by rw [ZMod.card_units],
    cyclotomicEvenDeltaSubgroup_card (p := p) hp_gt_two] at hcard
  exact Nat.eq_div_of_mul_eq_right (by decide)
    (by linarith : 2 * Fintype.card (CyclotomicEvenDelta p) = p - 1)

end KummerCriterion

end

/-!
# LV-SIN-C: `L'(0, χ)` formula via cyclotomic-unit logs

For an even nontrivial Dirichlet character χ mod p, the classical
**Dirichlet/Kummer formula**:

 `L'(0, χ̄) = -∑_{a=1}^{p-1} χ(a) · log|1 - ζ^a|`
 = `-∑_{a=1}^{p-1} χ(a) · log|2 sin(πa/p)|`

connects the L-function derivative at zero to logs of cyclotomic units.

This is the analytic content of LV-SIN-C: deriving the explicit form
that feeds the Kummer-Dirichlet determinant evaluation.

## Structure

Mathlib has `LFunction` (analytic continuation), `Even.LFunction_neg_two_mul_nat`
(zero at negative even integers), and `LFunction_modOne_eq`.

What's needed: the closed-form of `L(0, χ)` (= `-B_{1,χ}`) and
`deriv (LFunction χ) 0` connecting to log-cyclotomic-unit sums.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §4.2
 (L-functions and Bernoulli polynomials).
* Mathlib `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
-/

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Dirichlet sum form**: an alternative formulation that directly
relates the L-derivative to a sum over cyclotomic units. -/
def DirichletLogSum (χ : DirichletCharacter ℂ p) : ℂ :=
  -∑ a ∈ Finset.Ico 1 p,
    χ a * Real.log (2 * |Real.sin (Real.pi * a / p)|)

/-- **The norm of `1 - stdAddChar(↑(-a))` equals `1 - stdAddChar(↑a)`**:
direct from `stdAddChar(-x) = conj(stdAddChar(x))` (shipped in
`KummerCriterion.stdAddChar_neg_eq_conj`) plus `‖conj z‖ = ‖z‖` and
`conj(1 - z) = 1 - conj(z)`. This is the even-under-negation property of
the cyclotomic log-norm, foundational for descending to the
`(ZMod p)ˣ ⧸ ⟨-1⟩` quotient convolution matrix. -/
theorem norm_one_sub_stdAddChar_neg (a : ZMod p) :
    ‖(1 : ℂ) - ZMod.stdAddChar (N := p) (-a)‖ =
      ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ := by
  rw [KummerCriterion.stdAddChar_neg_eq_conj]
  rw [show (1 : ℂ) - (starRingEnd ℂ) (ZMod.stdAddChar (N := p) a) =
        (starRingEnd ℂ) (1 - ZMod.stdAddChar (N := p) a) from by
    rw [map_sub]; simp]
  exact Complex.norm_conj _

/-- **The log-norm function is even under negation of the unit argument**:
for `a: (ZMod p)ˣ`, `log‖1 - stdAddChar(↑(-a))‖ = log‖1 - stdAddChar(↑a)‖`.
Foundation for descending the convolution log-norm to the quotient. -/
theorem log_norm_one_sub_stdAddChar_unit_neg (a : (ZMod p)ˣ) :
    Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((↑(-a) : ZMod p))‖ =
      Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((↑a : ZMod p))‖ := by
  have h_cast : ((-a : (ZMod p)ˣ) : ZMod p) = -((a : (ZMod p)ˣ) : ZMod p) := by
    push_cast; rfl
  rw [h_cast, norm_one_sub_stdAddChar_neg]

/-- **Descended convolution log-norm**: the log-norm function
`f(a) = log‖1 - stdAddChar(↑a)‖` (for `a: (ZMod p)ˣ`) descends to a
function on the `{±1}`-quotient `CyclotomicEvenDelta p` via
`evenFunctionDescend`. This is the function whose convolution matrix
on the quotient gives the non-singular Frobenius determinant formula
for matrix-restriction. -/
noncomputable def convolutionLogNormDescended :
    KummerCriterion.CyclotomicEvenDelta p → ℂ :=
  KummerCriterion.evenFunctionDescend (p := p)
    (fun a : KummerCriterion.CyclotomicUnitDelta p =>
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ))
    (fun a => by
      dsimp only
      have h := log_norm_one_sub_stdAddChar_unit_neg (p := p) a
      exact_mod_cast h)

/-- **Quotient convolution log-norm matrix**: the convolution matrix on
`CyclotomicEvenDelta p = (ZMod p)ˣ ⧸ ⟨-1⟩` (size `(p-1)/2`) with entries
`M[ā, b̄] = convolutionLogNormDescended (ā · b̄)`.

This is the **non-singular** matrix (in contrast to the full
`convolutionMatrixLogNorm p` which has det = 0): odd characters are
quotiented out, leaving only even-character contributions which don't
structurally vanish.

By the Frobenius determinant formula for cyclic abelian groups, the
square determinant of this matrix equals the squared product of
eigenvalues over the characters of `CyclotomicEvenDelta p`, which by
the pullback bijection are exactly the **even Dirichlet characters** of
`(ZMod p)ˣ`. -/
noncomputable def convolutionMatrixLogNormEven :
    Matrix (KummerCriterion.CyclotomicEvenDelta p)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun a b => convolutionLogNormDescended p (a * b)

/-- **Generic convolution matrix on `CyclotomicEvenDelta p`**: for a function
`f: CyclotomicEvenDelta p → ℂ`, the multiplication-convolution matrix with
entries `M[a, b] = f(a · b)`. This is the abstract version of which
`convolutionMatrixLogNormEven` is the special case at the descended log-norm. -/
noncomputable def convolutionMatrixOnEven
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ) :
    Matrix (KummerCriterion.CyclotomicEvenDelta p)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun a b => f (a * b)

/-- **`convolutionMatrixLogNormEven` is `convolutionMatrixOnEven` applied to
the descended log-norm**: the specific quotient log-norm matrix is just the
generic convolution applied to `convolutionLogNormDescended`. -/
theorem convolutionMatrixLogNormEven_eq_convolutionMatrixOnEven :
    convolutionMatrixLogNormEven p =
      convolutionMatrixOnEven p (convolutionLogNormDescended p) := by
  rfl

/-- **Character matrix on `CyclotomicEvenDelta p`**: the matrix indexed by
characters of the quotient and elements of the quotient, with entries
`F[ξ, a] = ξ(a)`. This is the discrete Fourier transform matrix on the
quotient, the analog of `characterMatrix` for the full group. -/
noncomputable def characterMatrixOnEven :
    Matrix (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun ξ a => ξ a

/-- **Pontryagin cardinality on the quotient**:
`#{MulChar (CyclotomicEvenDelta p) ℂ} = #(CyclotomicEvenDelta p)`.
Direct from `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity` (using that
ℂ has all roots of unity) + `toUnits.symm.toEquiv` (units of a group = the
group cardinality-wise). -/
theorem nat_card_mulChar_cyclotomicEvenDelta_eq :
    Nat.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      Nat.card (KummerCriterion.CyclotomicEvenDelta p) := by
  haveI : NeZero (Monoid.exponent (KummerCriterion.CyclotomicEvenDelta p)ˣ) := by
    constructor
    haveI : Fintype (KummerCriterion.CyclotomicEvenDelta p)ˣ := Fintype.ofFinite _
    exact Monoid.exponent_ne_zero_of_finite
  rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity]
  exact Nat.card_congr toUnits.symm.toEquiv

/-- **Pontryagin equivalence on the quotient**: a non-canonical bijection
between `MulChar (CyclotomicEvenDelta p) ℂ` and `CyclotomicEvenDelta p`.
Used to reindex the character matrix as a square matrix for determinant
computations. -/
noncomputable def quotCharEquivQuot :
    MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ ≃
      KummerCriterion.CyclotomicEvenDelta p := by
  classical
  haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact nat_card_mulChar_cyclotomicEvenDelta_eq p

/-- **Matrix-level eigenvalue formula on the quotient**: for the multiplicative
convolution matrix `convolutionMatrixOnEven f`:

 `(characterMatrixOnEven · convolutionMatrixOnEven f)[ξ, b] =
 ξ(b⁻¹) · (∑_a ξ(a) · f(a))`.

Direct parallel of `characterMatrix_mul_convolutionMatrix_apply` on the
quotient: reindex via `a ↦ a · b⁻¹` and use character multiplicativity. -/
theorem characterMatrixOnEven_mul_convolutionMatrixOnEven_apply
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ)
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)
    (b : KummerCriterion.CyclotomicEvenDelta p) :
    (characterMatrixOnEven p * convolutionMatrixOnEven p f) ξ b =
      ξ (b⁻¹) * ∑ a : KummerCriterion.CyclotomicEvenDelta p, ξ a * f a := by
  classical
  simp only [Matrix.mul_apply, characterMatrixOnEven, convolutionMatrixOnEven,
    Matrix.of_apply]
  have h_reindex : ∑ a : KummerCriterion.CyclotomicEvenDelta p, ξ a * f (a * b) =
      ∑ a : KummerCriterion.CyclotomicEvenDelta p, ξ (a * b⁻¹) * f a := by
    apply (Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ _).symm
    intro a
    rw [Equiv.coe_mulRight]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [h_reindex]
  have h_factor : ∀ a : KummerCriterion.CyclotomicEvenDelta p,
      ξ (a * b⁻¹) * f a = ξ b⁻¹ * (ξ a * f a) := by
    intro a
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h_factor a)]
  rw [← Finset.mul_sum]

/-- **Square character matrix on `CyclotomicEvenDelta p`**: the
`((p-1)/2) × ((p-1)/2)` matrix indexed by `CyclotomicEvenDelta p × CyclotomicEvenDelta p`
with entries `(quotCharEquivQuot.symm k)(a)`, i.e., row `k` is the character
corresponding to `k` under the Pontryagin equivalence. Square form of
`characterMatrixOnEven` for determinant computations. -/
noncomputable def characterMatrixSquareOnEven :
    Matrix (KummerCriterion.CyclotomicEvenDelta p)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun k a => ((quotCharEquivQuot p).symm k) a

/-- **Square inverse character matrix on `CyclotomicEvenDelta p`**:
`F'[k, b] = (quotCharEquivQuot.symm k)(b⁻¹)`. -/
noncomputable def inverseCharacterMatrixSquareOnEven :
    Matrix (KummerCriterion.CyclotomicEvenDelta p)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun k b => ((quotCharEquivQuot p).symm k) b⁻¹

/-- **Square eigenvalue formula on the quotient**:
`(characterMatrixSquareOnEven · convolutionMatrixOnEven f)[k, b]
= (quotCharEquivQuot.symm k)(b⁻¹) · (∑_a (e.symm k)(a) · f(a))`. -/
theorem characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_apply
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ)
    (k b : KummerCriterion.CyclotomicEvenDelta p) :
    (characterMatrixSquareOnEven p * convolutionMatrixOnEven p f) k b =
      ((quotCharEquivQuot p).symm k) b⁻¹ *
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a := by
  simp only [characterMatrixSquareOnEven]
  exact characterMatrixOnEven_mul_convolutionMatrixOnEven_apply
    (p := p) f ((quotCharEquivQuot p).symm k) b

/-- **Square matrix factorisation on the quotient** `F_square · M = D · F'_square`. -/
theorem characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_eq_diag_mul_inv
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ) :
    characterMatrixSquareOnEven p * convolutionMatrixOnEven p f =
      Matrix.diagonal (fun k : KummerCriterion.CyclotomicEvenDelta p =>
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      inverseCharacterMatrixSquareOnEven p := by
  classical
  ext k b
  rw [characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_apply]
  rw [Matrix.mul_apply]
  have h_rhs : ∑ j : KummerCriterion.CyclotomicEvenDelta p,
      Matrix.diagonal (fun k' : KummerCriterion.CyclotomicEvenDelta p =>
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k') a * f a) k j *
        inverseCharacterMatrixSquareOnEven p j b =
      (∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
        ((quotCharEquivQuot p).symm k) b⁻¹ := by
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq]; rfl
    · intro j _ hj
      rw [Matrix.diagonal_apply_ne _ hj.symm, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [h_rhs]; ring

/-- **Square determinant identity on the quotient**:

 det(F_square) · det(M) = (∏ k, λ_{e.symm k}) · det(F'_square),

where `λ_χ = ∑ a, χ(a) · f(a)`. -/
theorem det_characterMatrixSquareOnEven_mul_convolutionMatrixOnEven
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ) :
    (characterMatrixSquareOnEven p).det * (convolutionMatrixOnEven p f).det =
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      (inverseCharacterMatrixSquareOnEven p).det := by
  classical
  rw [← Matrix.det_mul,
    characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_eq_diag_mul_inv,
    Matrix.det_mul, Matrix.det_diagonal]

/-- **`inverseCharacterMatrixSquareOnEven` as a column-inversion submatrix of
`characterMatrixSquareOnEven`**: `F'` is `F` with columns reindexed via the
inversion permutation `b ↦ b⁻¹`. Parallel to `inverseCharacterMatrixSquare_eq_submatrix`. -/
theorem inverseCharacterMatrixSquareOnEven_eq_submatrix :
    inverseCharacterMatrixSquareOnEven p =
      (characterMatrixSquareOnEven p).submatrix id
        (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p)) := by
  ext k b
  simp only [inverseCharacterMatrixSquareOnEven, characterMatrixSquareOnEven,
    Matrix.submatrix_apply, Matrix.of_apply, id_def, Equiv.inv_apply]

/-- **Determinants squared agree** for `characterMatrixSquareOnEven` and
`inverseCharacterMatrixSquareOnEven`: the column-inversion permutation has
determinant sign ±1, which squares to 1. -/
theorem det_inverseCharacterMatrixSquareOnEven_sq_eq_det_characterMatrixSquareOnEven_sq :
    (inverseCharacterMatrixSquareOnEven p).det ^ 2 =
      (characterMatrixSquareOnEven p).det ^ 2 := by
  rw [inverseCharacterMatrixSquareOnEven_eq_submatrix]
  rw [Matrix.det_permute' (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p))
      (characterMatrixSquareOnEven p)]
  rw [mul_pow]
  rw [show ((↑↑(Equiv.Perm.sign
      (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p))) : ℂ)) ^ 2 = 1 from ?_]
  · ring
  · have h_sign : (Equiv.Perm.sign
        (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p))) ^ 2 = 1 :=
      Int.units_pow_two _
    have h_cast : (((Equiv.Perm.sign
        (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p))) ^ 2 : ℤˣ) : ℂ) =
        ((1 : ℤˣ) : ℂ) := by
      rw [h_sign]
    push_cast at h_cast ⊢
    exact_mod_cast h_cast

/-- **Squared Frobenius determinant identity on the quotient (conditional
on `det F ≠ 0`)**:

 det(convolutionMatrixOnEven f)² = (∏_k λ_{e.symm k})²

where `λ_χ = ∑ a, χ(a) · f(a)`. Parallel of
`det_convolutionMatrix_sq_eq_prod_lambda_sq`. -/
theorem det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ)
    (h_det_F_ne : (characterMatrixSquareOnEven p).det ≠ 0) :
    (convolutionMatrixOnEven p f).det ^ 2 =
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) ^ 2 := by
  have h_det := det_characterMatrixSquareOnEven_mul_convolutionMatrixOnEven (p := p) f
  have h_det_sq : ((characterMatrixSquareOnEven p).det *
      (convolutionMatrixOnEven p f).det) ^ 2 =
      ((∏ k : KummerCriterion.CyclotomicEvenDelta p,
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      (inverseCharacterMatrixSquareOnEven p).det) ^ 2 := by
    rw [h_det]
  rw [mul_pow, mul_pow] at h_det_sq
  rw [det_inverseCharacterMatrixSquareOnEven_sq_eq_det_characterMatrixSquareOnEven_sq]
    at h_det_sq
  have h_det_F_sq_ne : (characterMatrixSquareOnEven p).det ^ 2 ≠ 0 :=
    pow_ne_zero _ h_det_F_ne
  have h_mul_cancel : (characterMatrixSquareOnEven p).det ^ 2 *
      (convolutionMatrixOnEven p f).det ^ 2 =
      (characterMatrixSquareOnEven p).det ^ 2 *
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
          ∑ a : KummerCriterion.CyclotomicEvenDelta p,
            ((quotCharEquivQuot p).symm k) a * f a) ^ 2 := by
    linear_combination h_det_sq
  exact (mul_left_cancel₀ h_det_F_sq_ne h_mul_cancel)

/-- **Character orthogonality at the matrix level on the quotient**:
`characterMatrixSquareOnEven · inverseCharacterMatrixSquareOnEvenᵀ =
(card G) · I` where G = CyclotomicEvenDelta p. The classical orthogonality
`∑_a χ(a) · ψ(a⁻¹) = card · δ_{χ=ψ}` at the matrix level. -/
theorem characterMatrixSquareOnEven_mul_inverseCharacterMatrixSquareOnEven_transpose :
    characterMatrixSquareOnEven p *
        Matrix.transpose (inverseCharacterMatrixSquareOnEven p) =
      ((Fintype.card (KummerCriterion.CyclotomicEvenDelta p) : ℕ) : ℂ) •
        (1 : Matrix (KummerCriterion.CyclotomicEvenDelta p)
                    (KummerCriterion.CyclotomicEvenDelta p) ℂ) := by
  classical
  ext k k'
  simp only [characterMatrixSquareOnEven, inverseCharacterMatrixSquareOnEven,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h_inv : ∀ a : KummerCriterion.CyclotomicEvenDelta p,
      ((quotCharEquivQuot p).symm k) a *
          ((quotCharEquivQuot p).symm k') a⁻¹ =
        (((quotCharEquivQuot p).symm k) *
          ((quotCharEquivQuot p).symm k')⁻¹) a := by
    intro a
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    rw [map_inv]
  rw [Finset.sum_congr rfl (fun a _ => h_inv a)]
  by_cases hkk : k = k'
  · subst hkk
    rw [if_pos rfl, mul_one]
    rw [show ((quotCharEquivQuot p).symm k) *
        ((quotCharEquivQuot p).symm k)⁻¹ =
        (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) from mul_inv_cancel _]
    have h_one := MulChar.sum_one_eq_card_units
      (R := KummerCriterion.CyclotomicEvenDelta p) (R' := ℂ)
    rw [h_one]
    have h_card : Fintype.card (KummerCriterion.CyclotomicEvenDelta p)ˣ =
        Fintype.card (KummerCriterion.CyclotomicEvenDelta p) :=
      Fintype.card_congr toUnits.symm.toEquiv
    rw [h_card]
  · rw [if_neg hkk, mul_zero]
    have h_ne : ((quotCharEquivQuot p).symm k) *
        ((quotCharEquivQuot p).symm k')⁻¹ ≠
        (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := by
      intro h_eq
      apply hkk
      have h_inv_cancel : ((quotCharEquivQuot p).symm k) =
          ((quotCharEquivQuot p).symm k') := by
        have := congrArg (· * ((quotCharEquivQuot p).symm k')) h_eq
        simp only at this
        rw [mul_assoc, inv_mul_cancel, mul_one, one_mul] at this
        exact this
      exact (quotCharEquivQuot p).symm.injective h_inv_cancel
    exact MulChar.sum_eq_zero_of_ne_one h_ne

/-- **`characterMatrixSquareOnEven` has nonzero determinant**:
orthogonality `F · F'ᵀ = (card G) · I`, taking determinants gives
`det(F) · det(F'ᵀ) = (card G)^(card G)`, non-zero for card G > 0.
Hence `det(F) ≠ 0`. -/
theorem det_characterMatrixSquareOnEven_ne_zero (hp_two : 2 < p) :
    (characterMatrixSquareOnEven p).det ≠ 0 := by
  classical
  intro h_det_zero
  have h_orth :=
    characterMatrixSquareOnEven_mul_inverseCharacterMatrixSquareOnEven_transpose
      (p := p)
  have h_det_orth := congrArg Matrix.det h_orth
  rw [Matrix.det_mul, h_det_zero, zero_mul] at h_det_orth
  rw [Matrix.det_smul, Matrix.det_one, mul_one] at h_det_orth
  have h_card_pos : 0 < Fintype.card (KummerCriterion.CyclotomicEvenDelta p) := by
    rw [KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two]
    omega
  have h_card_ne : ((Fintype.card (KummerCriterion.CyclotomicEvenDelta p) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr h_card_pos.ne'
  have h_pow_ne : ((Fintype.card (KummerCriterion.CyclotomicEvenDelta p) : ℕ) : ℂ) ^
      Fintype.card (KummerCriterion.CyclotomicEvenDelta p) ≠ 0 := pow_ne_zero _ h_card_ne
  exact h_pow_ne h_det_orth.symm

/-- **Unconditional squared Frobenius determinant formula on the quotient**:
combining `det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq` with
`det_characterMatrixSquareOnEven_ne_zero`, the squared determinant of the
convolution matrix on `CyclotomicEvenDelta p` equals the squared product
of eigenvalues:

 det(convolutionMatrixOnEven p f)² = (∏_k λ_{e.symm k})²

where `λ_χ = ∑ a, χ(a) · f(a)`. Unconditional for `p > 2`. -/
theorem det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq_unconditional
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ) (hp_two : 2 < p) :
    (convolutionMatrixOnEven p f).det ^ 2 =
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) ^ 2 :=
  det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq (p := p) f
    (det_characterMatrixSquareOnEven_ne_zero (p := p) hp_two)

/-- **Quotient eigenvalue at character `ξ`**:
`ξ: MulChar (CyclotomicEvenDelta p) ℂ`,
the eigenvalue of `convolutionMatrixLogNormEven` at the descended character is
`∑ ā: CyclotomicEvenDelta p, ξ(ā) · convolutionLogNormDescended(ā)`. This is
the natural Frobenius eigenvalue on the quotient. -/
noncomputable def quotientEigenvalue
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) : ℂ :=
  ∑ ā : KummerCriterion.CyclotomicEvenDelta p,
    ξ ā * convolutionLogNormDescended p ā

/-- **Eigenvalues in `quotientEigenvalue` form**: the Frobenius eigenvalue
at the `k`-th character (via `quotCharEquivQuot.symm k`) equals
`quotientEigenvalue` at that character, applied to `convolutionLogNormDescended`. -/
theorem prod_lambda_eq_prod_quotientEigenvalue :
    (∏ k : KummerCriterion.CyclotomicEvenDelta p,
      ∑ a : KummerCriterion.CyclotomicEvenDelta p,
        ((quotCharEquivQuot p).symm k) a * convolutionLogNormDescended p a) =
    ∏ k : KummerCriterion.CyclotomicEvenDelta p,
      quotientEigenvalue p ((quotCharEquivQuot p).symm k) := by
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rfl

/-- **Squared det of `convolutionMatrixLogNormEven` in eigenvalue product form**:
combining the unconditional Frobenius det formula with `quotientEigenvalue`. -/
theorem det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq
    (hp_two : 2 < p) :
    (convolutionMatrixLogNormEven p).det ^ 2 =
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
        quotientEigenvalue p ((quotCharEquivQuot p).symm k)) ^ 2 := by
  rw [convolutionMatrixLogNormEven_eq_convolutionMatrixOnEven]
  rw [det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq_unconditional p _ hp_two]
  rw [prod_lambda_eq_prod_quotientEigenvalue]

/-- **Product reindexed via the Pontryagin equivalence**: the product over
`k: CyclotomicEvenDelta p` of a function evaluated at `(quotCharEquivQuot.symm k)`
equals the product over `ξ: MulChar (CyclotomicEvenDelta p) ℂ` directly. -/
theorem prod_quot_eq_prod_mulChar
    (f : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ → ℂ) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    ∏ k : KummerCriterion.CyclotomicEvenDelta p,
        f ((quotCharEquivQuot p).symm k) =
      ∏ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ, f ξ := by
  classical
  letI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  exact (Fintype.prod_equiv (quotCharEquivQuot p)
    (fun ξ => f ξ)
    (fun k => f ((quotCharEquivQuot p).symm k))
    (fun ξ => by simp only [Equiv.symm_apply_apply])).symm

/-- **Half-sum identity**: for any even function `f: (ZMod p)ˣ → ℂ`
(with `f(-a) = f(a)`), summing over the full group gives twice the sum
over the `{±1}`-quotient `CyclotomicEvenDelta p` (for `p > 2`).

Proof: rewrite `f(a) = f̄(q(a))` via `evenFunctionDescend_apply_mk`,
then use `Finset.sum_comp` to rewrite the full sum as a sum over the
image with fiber-cardinality weights. The image is the whole quotient
(by surjectivity of `q`), and each fiber has cardinality `2` (by the
size-2 subgroup `⟨-1⟩` acting freely for `p > 2`). -/
theorem sum_full_eq_two_mul_sum_descended (f : KummerCriterion.CyclotomicUnitDelta p → ℂ)
    (hf_even : ∀ a, f (-a) = f a) (hp_two : 2 < p) :
    ∑ a : KummerCriterion.CyclotomicUnitDelta p, f a =
      2 * ∑ b : KummerCriterion.CyclotomicEvenDelta p,
            KummerCriterion.evenFunctionDescend (p := p) f hf_even b := by
  classical
  have h_step1 : ∀ a, f a =
      KummerCriterion.evenFunctionDescend (p := p) f hf_even
        (KummerCriterion.cyclotomicEvenDeltaQuotient p a) := by
    intro a
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply,
        KummerCriterion.evenFunctionDescend_apply_mk]
  simp_rw [h_step1]
  rw [Finset.sum_comp _ (KummerCriterion.cyclotomicEvenDeltaQuotient p)]
  have h_image : Finset.image (KummerCriterion.cyclotomicEvenDeltaQuotient p)
        (Finset.univ : Finset (KummerCriterion.CyclotomicUnitDelta p)) =
      Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro b
    rw [Finset.mem_image]
    refine ⟨Quotient.out b, Finset.mem_univ _, ?_⟩
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply]
    exact Quotient.out_eq b
  rw [h_image]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have h_card : ({a ∈ (Finset.univ : Finset (KummerCriterion.CyclotomicUnitDelta p)) |
      KummerCriterion.cyclotomicEvenDeltaQuotient p a = b}).card = 2 := by
    have h_equiv := QuotientGroup.preimageMkEquivSubgroupProdSet
      (KummerCriterion.CyclotomicEvenDeltaSubgroup p) ({b} : Set _)
    have h_card_eq :
        Fintype.card (QuotientGroup.mk ⁻¹' ({b} : Set _) :
            Set (KummerCriterion.CyclotomicUnitDelta p)) =
        Fintype.card (KummerCriterion.CyclotomicEvenDeltaSubgroup p) * 1 := by
      rw [Fintype.card_congr h_equiv, Fintype.card_prod]
      simp
    rw [KummerCriterion.cyclotomicEvenDeltaSubgroup_card (p := p) hp_two] at h_card_eq
    rw [show ({a ∈ Finset.univ | KummerCriterion.cyclotomicEvenDeltaQuotient p a = b} :
        Finset _).card =
        Fintype.card (QuotientGroup.mk ⁻¹' ({b} : Set _) :
            Set (KummerCriterion.CyclotomicUnitDelta p)) from ?_]
    · omega
    · rw [Fintype.card_ofFinset]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage,
        Set.mem_singleton_iff]
      rfl
  rw [h_card]
  ring

/-- **Twice quotient eigenvalue = full-group sum at the pullback character**:
for `ξ: MulChar (CyclotomicEvenDelta p) ℂ` and `p > 2`,
`2 · quotientEigenvalue p ξ = ∑_a (pullback ξ)(a) · log‖1 - stdAddChar(↑a)‖`,
summing over `a: (ZMod p)ˣ` (the unit-group). Direct application of the
half-sum identity `sum_full_eq_two_mul_sum_descended` to the even function
`f(a) = (pullback ξ)(a) · log-norm(↑a)`. -/
theorem two_mul_quotientEigenvalue_eq_sum_full
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) (hp_two : 2 < p) :
    2 * quotientEigenvalue p ξ =
      ∑ a : KummerCriterion.CyclotomicUnitDelta p,
        KummerCriterion.evenDeltaCharacterPullback (p := p) ξ a *
          ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  set f : KummerCriterion.CyclotomicUnitDelta p → ℂ := fun a =>
    KummerCriterion.evenDeltaCharacterPullback (p := p) ξ a *
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) with hf_def
  have hf_even : ∀ a : KummerCriterion.CyclotomicUnitDelta p, f (-a) = f a := by
    intro a
    simp only [hf_def]
    rw [log_norm_one_sub_stdAddChar_unit_neg (p := p) a]
    congr 1
    change ξ (KummerCriterion.cyclotomicEvenDeltaQuotient p (-a)) =
        ξ (KummerCriterion.cyclotomicEvenDeltaQuotient p a)
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_neg]
  have h_half := sum_full_eq_two_mul_sum_descended (p := p) f hf_even hp_two
  have h_quot_eq : quotientEigenvalue p ξ =
      ∑ b : KummerCriterion.CyclotomicEvenDelta p,
        KummerCriterion.evenFunctionDescend (p := p) f hf_even b := by
    unfold quotientEigenvalue
    refine Finset.sum_congr rfl (fun b _ => ?_)
    obtain ⟨a, rfl⟩ : ∃ a : KummerCriterion.CyclotomicUnitDelta p,
        KummerCriterion.cyclotomicEvenDeltaQuotient p a = b :=
      ⟨Quotient.out b,
        by rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply]; exact Quotient.out_eq b⟩
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply]
    rw [KummerCriterion.evenFunctionDescend_apply_mk]
    simp only [hf_def]
    unfold convolutionLogNormDescended
    rw [KummerCriterion.evenFunctionDescend_apply_mk]
    rfl
  rw [h_quot_eq, ← h_half]

/-- **Sum reindex `(ZMod p)ˣ → Finset.Ico 1 p`**: for any function `F: ℕ → ℂ`,
the sum over the unit group equals the sum over `{1,..., p-1}` via the
bijection `a ↦ a.val`. Standard reindexing for prime `p`. -/
theorem sum_units_val_eq_sum_Ico (F : ℕ → ℂ) :
    ∑ a : (ZMod p)ˣ, F ((a : ZMod p).val) = ∑ n ∈ Finset.Ico 1 p, F n := by
  have hp_pos : 0 < p := hp.out.pos
  refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => (a : ZMod p).val)
    (fun a _ => ?_) (fun a _ b _ heq => ?_) (fun n hn => ?_) (fun _ _ => rfl)
  · rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt _⟩
    have h_ne : (a : ZMod p).val ≠ 0 := by
      intro h
      rw [ZMod.val_eq_zero] at h
      exact a.ne_zero h
    exact Nat.one_le_iff_ne_zero.mpr h_ne
  · apply Units.ext
    apply ZMod.val_injective _ heq
  · rw [Finset.mem_Ico] at hn
    refine ⟨ZMod.unitOfCoprime n
      (Nat.coprime_comm.mp (Nat.coprime_of_lt_prime (by omega) hn.2 hp.out)),
      Finset.mem_univ _, ?_⟩
    simp only
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hn.2

/-- **Quotient eigenvalue at the trivial character (sum form)**: at the
trivial MulChar `1: MulChar (CyclotomicEvenDelta p) ℂ`,
`2 · quotientEigenvalue p 1 = ∑ a: (ZMod p)ˣ, log‖1 - stdAddChar(↑a)‖`.

Direct from `two_mul_quotientEigenvalue_eq_sum_full` + the fact that
`(pullback 1)(a) = 1` for `a: (ZMod p)ˣ` (since every group element is a unit). -/
theorem two_mul_quotientEigenvalue_trivial_eq_sum_logNorm (hp_two : 2 < p) :
    2 * quotientEigenvalue p (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      ∑ a : KummerCriterion.CyclotomicUnitDelta p,
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  rw [two_mul_quotientEigenvalue_eq_sum_full p 1 hp_two]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h_unit : IsUnit
      (KummerCriterion.cyclotomicEvenDeltaQuotient p a) := Group.isUnit _
  change (1 : MulChar _ _) (KummerCriterion.cyclotomicEvenDeltaQuotient p a) *
      _ = _
  rw [MulChar.one_apply h_unit, one_mul]

end Sinnott

end LehmerVandiver

end KummerCriterion

end
