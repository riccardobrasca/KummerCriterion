import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part7

/-!
# Bridge from substantive matrix content to RegOf-squared form

The corrected `RegOfFamilySqEqProdNontrivialQeSq` requires the factor
`2^(p-3)`. This file ships the algebraic bridge:

 `(det(A − B): ℂ)² = (∏_{ξ ≠ 1} qe(ξ))²` ⟹
 `regOfFamily² = 2^(p-3) · (∏_{ξ ≠ 1} qe(ξ))²`

via `regOfFamily = |det M_Sinnott|` and `det M_Sinnott = 2^N · det(A − B)`. -/

@[expose] public section

noncomputable section

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

open Classical in
/-- **Cardinality of non-w₀ K⁺-places equals `(p-3)/2`**. -/
theorem card_kplus_ne_w₀_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (_hp_two : 2 < p) :
    Fintype.card {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      (p - 3) / 2 := by
  have h_rank_eq : NumberField.Units.rank
      (NumberField.maximalRealSubfield K) = (p - 3) / 2 := by
    rw [NumberField.IsCMField.units_rank_eq_units_rank (K := K)]
    exact KummerCriterion.units_rank_eq_prime_sub_three_div_two (p := p) (K := K)
  have h_rank_def : NumberField.Units.rank
      (NumberField.maximalRealSubfield K) =
      Fintype.card (NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K)) - 1 := rfl
  have h_card_compl :=
    Fintype.card_subtype_compl (α := NumberField.InfinitePlace
      (NumberField.maximalRealSubfield K)) (p := fun w =>
      w = NumberField.Units.dirichletUnitTheorem.w₀)
  rw [Fintype.card_subtype_eq] at h_card_compl
  have h_eq : Fintype.card {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      Fintype.card {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) // ¬ w =
        NumberField.Units.dirichletUnitTheorem.w₀} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [h_eq, h_card_compl]
  omega

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **`regOfFamily² = 2^(p-3) · det(A-B)²` in ℝ**. -/
theorem regOfFamily_sq_eq_two_pow_mul_det_A_sub_B_sq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) :
    (NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ^ 2 =
      (2 : ℝ) ^ (p - 3) *
        ((sinnottMatrixA p K - sinnottMatrixB p K).det) ^ 2 := by
  have h_card := card_kplus_ne_w₀_eq (p := p) K hp_two
  have h_reg_eq_abs_det := regOfFamily_cyclotomicUnitFamilyKplus_eq_det
    (p := p) (K := K) hp_odd hp_three
  have h_det_eq_two_pow := det_sinnottMatrix_eq_pow_two_mul_det
    (p := p) K hp_odd hp_three
  have h_reg_combined : NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      |(2 : ℝ) ^ Fintype.card {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀} *
        (sinnottMatrixA p K - sinnottMatrixB p K).det| :=
    h_reg_eq_abs_det.trans (congr_arg abs h_det_eq_two_pow)
  have h_two_pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ Fintype.card
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := by positivity
  rw [h_reg_combined, abs_mul, abs_of_nonneg h_two_pow_nn, mul_pow, sq_abs]
  congr 1
  rw [← pow_mul, h_card]
  congr 1
  have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨k, hk⟩
  omega

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **`RegOfFamilySqEqProdNontrivialQeSq` from `DetASubBSqEqProdNontrivialQeSq`**:
the corrected squared form follows from the substantive matrix-level
identity by extracting the `2^(p-3)` factor algebraically.

This reduces substantive content to the rank-1 Frobenius
identity on `(A − B)`. -/
theorem regOfFamilySqEqProdNontrivialQeSq_of_detASubBSqEqProdQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h : DetASubBSqEqProdNontrivialQeSq (p := p) K) :
    RegOfFamilySqEqProdNontrivialQeSq (p := p) K hp_odd hp_three := by
  unfold RegOfFamilySqEqProdNontrivialQeSq
  unfold DetASubBSqEqProdNontrivialQeSq at h
  have h_reg_sq_R := regOfFamily_sq_eq_two_pow_mul_det_A_sub_B_sq
    (p := p) K hp_odd hp_three hp_two
  have h_reg_sq_C : ((NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
      (2 : ℂ) ^ (p - 3) *
        (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) ^ 2 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) h_reg_sq_R
    push_cast at this
    exact this
  rw [h_reg_sq_C, h]

/-! ## Matrix determinant lemma for the rank-1 perturbation

The matrix `(A - B) = U - 1·v^T` is a rank-1 perturbation of the
shifted-convolution submatrix `U = sinnottShiftedConvolutionMatrix`.
Apply mathlib's `Matrix.det_add_replicateCol_mul_replicateRow` under
`SinnottConvolutionMatrixDetUnit` (i.e., `IsUnit (U.det)`). -/

/-! ## Scalar-correction reduction (named hypothesis)

After applying the matrix determinant lemma, `det(A - B) = det(U) · ε`
where `ε = (1 + replicateRow v · U⁻¹ · replicateCol (-1)).det` is the
PUnit.{1}-indexed 1×1 scalar correction.

The remaining substantive content (`DetASubBSqEqProdNontrivialQeSq`)
reduces to: `(det(U) · ε)² = (∏_{χ ≠ 1} qe(χ))²`. This is the cleanest
isolation of Sinnott's matrix-level identity. -/

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-! ## Reduction of squared content to linear form

`DetASubBSqEqProdNontrivialQeSq` (squared form) follows directly
the linear form `det(A − B) = ε · ∏_{χ ≠ 1} qe(χ)` for any
`ε² = 1` (i.e., `ε ∈ {±1}`). Squaring absorbs the sign.

This is the cleanest formulation since Sinnott's identity is naturally
stated as `det(A − B) = ±∏ qe`, and the choice of sign depends on
enumeration conventions in the proof. -/

/-! ## Full discharge from two parametric hypotheses

Composing all shipped reductions, the entire chain `KummerDirichletDeterminant`
follows from just two parametric hypotheses:

1. `SinnottConvolutionMatrixDetUnit`: `IsUnit (det U)` (Dirichlet non-vanishing).
2. `DetASubBEqProdNontrivialQe`: `det(A − B) = ±∏_{χ ≠ 1} qe(χ)` (substantive Sinnott).

Note: the matrix-det-lemma chain `det_sinnottMatrix_A_sub_B_via_rank_one` is
SUFFICIENT but NOT NECESSARY for `DetASubBEqProdNontrivialQe` — the
substantive identity can be proven directly without going through U.
Hence `SinnottConvolutionMatrixDetUnit` may not be needed in the discharge
of `DetASubBEqProdNontrivialQe`. -/

set_option maxHeartbeats 6400000 in
-- The determinant bridge expands several matrix identities and exceeds the default heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
open Classical in
/-! ## Character matrix action on (A − B): matrix-equation form

Wrap the shipped per-row eigenvalue identity
`sum_char_sinnottMatrix_A_sub_B_eigenvalue` into a single matrix equation:

 `(charMatrix · (A − B)^T)[ξ, i] = eigenvalue formula`

This is the entry-wise statement; by `Matrix.ext`, equivalent to a
matrix-level identity. Useful for downstream determinant computations. -/

/-! ## "Diagonal" eigenvalue matrix `D` for the rank-1 decomposition

After the character action, the matrix `charMatrix · (A − B)^T` decomposes as

 `charMatrix · (A − B)^T = D - col · row`

where:
- `D[ξ, i] = (ξ(q(famIdx i))⁻¹ - 1) · qe(ξ)`. (Note: D has row ξ = 1 zero
 since (1 - 1) · qe(1) = 0.)
- `col(ξ) = ξ(k(w₀))`.
- `row(i) = corr(i) = M_even[k(w₀), q(famIdx i)] - M_even[k(w₀), 1]`.

This is a clean rank-1 perturbation structure, suitable for matrix det
open Classical in
lemma application restricted to ξ ≠ 1. -/

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-! ## Restriction to ξ ≠ 1: the substantive square case

Restricting the row index to ξ ≠ 1 makes `charMatrix · (A − B)^T` square
of size (|G|-1) × (|G|-1), and the diagonal matrix `D` (which has row
ξ = 1 vanishing) becomes invertible (assuming Dirichlet non-vanishing
of `qe(ξ)` for ξ ≠ 1). -/

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-! ## Cardinality match for character-matrix det reindexing

To take `det(charMatrix_K_plus_nontriv)`, we need a square matrix; the
rectangular `Matrix {ξ ≠ 1} {w ≠ w₀}` is bridged via `Fintype.equivOfCardEq`
between the row and column index sets (both of cardinality `(p-3)/2`). -/

open Classical in
/-- **Cardinality of non-trivial characters**: `(p-1)/2 - 1 = (p-3)/2`. -/
theorem card_nontriv_mulChar_eq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    Fintype.card {ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
      (p - 3) / 2 := by
  classical
  letI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  have h_card_mc :
      Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two
  have h_card_compl :=
    Fintype.card_subtype_compl
      (α := MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)
      (p := fun ξ => ξ = 1)
  rw [Fintype.card_subtype_eq] at h_card_compl
  have h_eq :
      Fintype.card {ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
      Fintype.card {ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ // ¬ ξ = 1} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [h_eq, h_card_compl, h_card_mc]
  have h_p_odd : Odd p := hp.out.odd_of_ne_two (by omega)
  rcases h_p_odd with ⟨k, hk⟩
  omega

/-! ## Reindexed (square) versions of charMatrix_nontriv and D_nontriv

Applying `equivNontrivCharKplusNeW₀.symm` on rows gives a square matrix
indexed by `{w ≠ w₀}` on both sides, enabling `Matrix.det`. -/

end Sinnott

end LehmerVandiver

end KummerCriterion

end
