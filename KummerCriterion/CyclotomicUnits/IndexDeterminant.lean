module

public import KummerCriterion.CyclotomicUnits.DeletedFourier
public import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part6
public import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.DetBridge

/-!
# Deleted Fourier determinant on the even cyclotomic quotient

This file specializes the abstract deleted Fourier determinant identity to
`CyclotomicEvenDelta p = (ZMod p)ˣ / {±1}` and identifies the `hk` convention
with the existing `LehmerVandiver.Sinnott.quotientEigenvalue` normalization.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace KummerCriterion
namespace CyclotomicUnits

variable (p : ℕ) [Fact p.Prime]

/-- A noncanonical equivalence between nontrivial characters of the even
quotient and non-identity elements of the even quotient. It is used only for
determinant reindexing; the determinant statements below are independent of
which equivalence is chosen. -/
noncomputable def cyclotomicEvenNontrivCharEquivNonidentity (hp_two : 2 < p) :
    NontrivChar (CyclotomicEvenDelta p) ≃ Nonidentity (CyclotomicEvenDelta p) := by
  classical
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  letI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  refine Fintype.equivOfCardEq ?_
  have hχ := LehmerVandiver.Sinnott.card_nontriv_mulChar_eq p hp_two
  have hG := LehmerVandiver.Sinnott.fintype_card_nonTrivialCE_eq p hp_two
  rw [hχ, hG]
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hp_odd with ⟨k, hk⟩
  omega

/-- The arbitrary omitted-row `hk` determinant for the descended cyclotomic
log-norm, with the harmless character factor removed after squaring. -/
theorem det_cyclotomicEven_logNorm_deletedMulAtReindexed_sq_eq_prod_quotientEigenvalue_sq
    (hp_two : 2 < p) (h₀ : CyclotomicEvenDelta p) :
    haveI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
    haveI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
    (deletedConvolutionMulMatrixAtReindexed
      (G := CyclotomicEvenDelta p) h₀
      (LehmerVandiver.Sinnott.convolutionLogNormDescended p)).det ^ 2 =
      (∏ ξ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
        LehmerVandiver.Sinnott.quotientEigenvalue p ξ) ^ 2 := by
  classical
  let : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  rw [det_deletedConvolutionMulMatrixAtReindexed_sq_eq_prod_deletedFourierCoeffMul_sq
    (G := CyclotomicEvenDelta p)
    (cyclotomicEvenNontrivCharEquivNonidentity (p := p) hp_two) h₀
    (LehmerVandiver.Sinnott.convolutionLogNormDescended p)]
  congr 1
  rw [Finset.prod_subtype
    (p := fun ξ : MulChar (CyclotomicEvenDelta p) ℂ => ξ ≠ 1)
    (s := (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1)
    (f := fun ξ => LehmerVandiver.Sinnott.quotientEigenvalue p ξ)]
  · refine Finset.prod_congr rfl ?_
    intro ξ _
    unfold deletedFourierCoeffMul LehmerVandiver.Sinnott.quotientEigenvalue
    rfl
  · intro ξ
    simp [Finset.mem_erase]

end CyclotomicUnits
end KummerCriterion

/-!
# Deleted Fourier determinant for Sinnott's cyclotomic-unit matrix

This file connects the deleted Fourier determinant with the matrix
`sinnottMatrixA - sinnottMatrixB` used by the LehmerVandiver Sinnott pipeline.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField

namespace KummerCriterion
namespace CyclotomicUnits

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Reindexing rows and columns by unrelated equivalences can only change a
complex determinant by a sign; after squaring the determinant is unchanged. -/
theorem det_submatrix_equiv_equiv_sq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e₁ e₂ : κ ≃ ι) (A : Matrix ι ι ℂ) :
    (A.submatrix e₁ e₂).det ^ 2 = A.det ^ 2 := by
  classical
  have hdet := Matrix.det_reindex e₁.symm e₂.symm A
  change (((Matrix.reindex e₁.symm e₂.symm) A).det) ^ 2 = A.det ^ 2
  rw [hdet, mul_pow]
  have hsign :
      ((↑↑(Equiv.Perm.sign (e₂.symm.trans e₁.symm.symm)) : ℂ)) ^ 2 = 1 := by
    let σ : Equiv.Perm ι := e₂.symm.trans e₁.symm.symm
    have hunit : (Equiv.Perm.sign σ) ^ 2 = 1 :=
      Int.units_pow_two _
    have hcast := congrArg (fun u : ℤˣ => ((u : ℂ))) hunit
    push_cast at hcast
    simpa [σ] using hcast
  rw [hsign, one_mul]

/-- The shifted infinite-place indexing, restricted away from the distinguished
Dirichlet place, as an equivalence with the non-identity even quotient. -/
noncomputable def kplusPlaceStarEquivNonidentityShifted
    (hp_two : 2 < p) :
    {w : InfinitePlace K⁺ // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      Nonidentity (CyclotomicEvenDelta p) := by
  classical
  let e :=
    LehmerVandiver.Sinnott.KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted
      (p := p) K hp_two
  have h_w₀ : e NumberField.Units.dirichletUnitTheorem.w₀ = 1 :=
    LehmerVandiver.Sinnott.KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted_apply_w₀
      (p := p) K hp_two
  exact e.subtypeEquiv fun v => not_congr (by rw [← h_w₀]; exact e.apply_eq_iff_eq.symm)

@[simp]
theorem kplusPlaceStarEquivNonidentityShifted_apply
    (hp_two : 2 < p)
    (w : {w : InfinitePlace K⁺ // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (kplusPlaceStarEquivNonidentityShifted (p := p) (K := K) hp_two w).val =
      LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotientShifted (p := p) K w.val := by
  rfl

/-- Sinnott's `(A - B)` determinant is the deleted Fourier determinant,
after transposing and reindexing rows and columns. -/
theorem detASubB_sq_eq_deletedFourier_sq
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    haveI : DecidableEq (InfinitePlace K⁺) := Classical.decEq _
    haveI : DecidablePred (fun w : InfinitePlace K⁺ =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀) := fun _ => instDecidableNot
    haveI : Fintype {w : InfinitePlace K⁺ //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
      Subtype.fintype (fun w : InfinitePlace K⁺ =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀)
    haveI : DecidableEq {w : InfinitePlace K⁺ //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := fun a b => a.instDecidableEq b
    (((((LehmerVandiver.Sinnott.sinnottMatrixA p K -
      LehmerVandiver.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ)) ^ 2 : ℂ) =
      (deletedConvolutionMulMatrixAtReindexed
        (G := CyclotomicEvenDelta p)
        (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀)
        (LehmerVandiver.Sinnott.convolutionLogNormDescended p)).det ^ 2 := by
  classical
  let rowEquiv :=
    kplusPlaceStarEquivNonidentityShifted (p := p) (K := K) hp_two
  let colEquiv :=
    LehmerVandiver.Sinnott.familyIndexAsCEnotOneEquiv
      (p := p) K hp_odd hp_three hp_ge_five hp_two
  let D :=
    deletedConvolutionMulMatrixAtReindexed
      (G := CyclotomicEvenDelta p)
      (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀)
      (LehmerVandiver.Sinnott.convolutionLogNormDescended p)
  have hcast :
      (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
          LehmerVandiver.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ) =
        (Matrix.of fun
          (i : {w : InfinitePlace K⁺ //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : InfinitePlace K⁺ //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
              LehmerVandiver.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)).det := by
    rw [show (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
        LehmerVandiver.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ) =
        (Complex.ofRealHom ((LehmerVandiver.Sinnott.sinnottMatrixA p K -
          LehmerVandiver.Sinnott.sinnottMatrixB p K).det) : ℂ) from rfl]
    rw [Complex.ofRealHom.map_det]
    rfl
  have hmatrix :
      (Matrix.of fun
          (w : {w : InfinitePlace K⁺ //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (i : {w : InfinitePlace K⁺ //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
              LehmerVandiver.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)) =
        D.submatrix rowEquiv colEquiv := by
    ext w i
    rw [Matrix.of_apply, Matrix.submatrix_apply]
    rw [LehmerVandiver.Sinnott.sinnottMatrix_A_sub_B_apply_eq_sub_shifted
      (p := p) K hp_odd hp_three i w]
    simp only [LehmerVandiver.Sinnott.convolutionMatrixLogNormEven, Matrix.of_apply, D,
      deletedConvolutionMulMatrixAtReindexed]
    rw [kplusPlaceStarEquivNonidentityShifted_apply
      (p := p) (K := K) hp_two w]
    rw [LehmerVandiver.Sinnott.familyIndexAsCEnotOneEquiv_apply
      (p := p) K hp_odd hp_three hp_ge_five hp_two i]
    congr 2
    · simp [mul_comm]
    · simp [mul_comm]
  rw [hcast]
  rw [← Matrix.det_transpose]
  change
    (Matrix.of fun
      (w : {w : InfinitePlace K⁺ //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
      (i : {w : InfinitePlace K⁺ //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
          LehmerVandiver.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)).det ^ 2 =
      D.det ^ 2
  rw [hmatrix]
  exact det_submatrix_equiv_equiv_sq rowEquiv colEquiv D

/-- The matrix-level determinant proposition for the `p ≥ 5` branch. -/
theorem detASubBSqEqProdNontrivialQeSq_of_deletedFourier
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    haveI : DecidableEq (InfinitePlace K⁺) := Classical.decEq _
    haveI : DecidablePred (fun w : InfinitePlace K⁺ =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀) := fun _ => instDecidableNot
    haveI : Fintype {w : InfinitePlace K⁺ //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
      Subtype.fintype (fun w : InfinitePlace K⁺ =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀)
    haveI : DecidableEq {w : InfinitePlace K⁺ //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := fun a b => a.instDecidableEq b
    LehmerVandiver.Sinnott.DetASubBSqEqProdNontrivialQeSq (p := p) K := by
  classical
  unfold LehmerVandiver.Sinnott.DetASubBSqEqProdNontrivialQeSq
  rw [detASubB_sq_eq_deletedFourier_sq
    (p := p) (K := K) hp_odd hp_three hp_two hp_ge_five]
  exact det_cyclotomicEven_logNorm_deletedMulAtReindexed_sq_eq_prod_quotientEigenvalue_sq
    (p := p) hp_two
    (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)

end CyclotomicUnits
end KummerCriterion

end
