import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part6

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

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
          (BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotientShifted (p := p) K w.val *
            kplusEmbeddingIndexQuotient (p := p) K
              NumberField.Units.dirichletUnitTheorem.w₀) 1 := by
  classical
  rw [sinnottMatrix_A_sub_B_apply_eq_sub p K hp_odd hp_three i w]
  -- k_shifted(w) * k(w₀) = (k(w) * k(w₀)⁻¹) * k(w₀) = k(w).
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
            ((FLT37.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))).det =
      (2 : ℝ) ^ Fintype.card {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀} *
        (sinnottMatrixA p K - sinnottMatrixB p K).det := by
  rw [sinnottMatrix_eq_two_smul_A_sub_B p K hp_odd hp_three]
  exact Matrix.det_smul (sinnottMatrixA p K - sinnottMatrixB p K) 2

end Sinnott

end FLT37

end BernoulliRegular

end
