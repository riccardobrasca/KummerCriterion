module

public import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part6

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Sinnott `(A - B)` entry via shifted bijection**:
`(A - B)[i, w]` re-expressed using `kplusEmbeddingIndexQuotientShifted` (which
sends w₀ → 1). The entry's column reference shifts to
`k_shifted(w) * k(w₀)` (compensating for the shift). -/
theorem sinnottMatrix_A_sub_B_apply_eq_sub_shifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ) =
      convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotientShifted (p := p) K w.val *
            kplusEmbeddingIndexQuotient (p := p) K
              NumberField.Units.dirichletUnitTheorem.w₀)
          (KummerCriterion.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotientShifted (p := p) K w.val *
            kplusEmbeddingIndexQuotient (p := p) K
              NumberField.Units.dirichletUnitTheorem.w₀) 1 := by
  classical
  rw [sinnottMatrix_A_sub_B_apply_eq_sub p K hp_odd hp_three i w]
  unfold kplusEmbeddingIndexQuotientShifted
  rw [show (kplusEmbeddingIndexQuotient p K w.val *
      (kplusEmbeddingIndexQuotient p K
        NumberField.Units.dirichletUnitTheorem.w₀)⁻¹) *
      kplusEmbeddingIndexQuotient p K
        NumberField.Units.dirichletUnitTheorem.w₀ =
      kplusEmbeddingIndexQuotient p K w.val by group]

/-- **Determinant of Sinnott matrix in `2^((p-3)/2) · det(A-B)` form**: the
factor-of-2 extraction at the determinant level. -/
theorem det_sinnottMatrix_eq_pow_two_mul_det
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((LehmerVandiver.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))).det =
      (2 : ℝ) ^ Fintype.card {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀} *
        (sinnottMatrixA p K - sinnottMatrixB p K).det := by
  rw [sinnottMatrix_eq_two_smul_A_sub_B p K hp_odd hp_three]
  exact Matrix.det_smul (sinnottMatrixA p K - sinnottMatrixB p K) 2

end Sinnott

end LehmerVandiver

end KummerCriterion

end

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

set_option maxHeartbeats 6400000 in
-- Matrix identities here exceed the default heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **Cardinality of non-trivial characters**: `(p-1)/2 - 1 = (p-3)/2`. -/
theorem card_nontriv_mulChar_eq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    Fintype.card {ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
      (p - 3) / 2 := by
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
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

end Sinnott

end LehmerVandiver

end KummerCriterion

end
