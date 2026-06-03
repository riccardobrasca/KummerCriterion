import KummerCriterion.LValueAtOne.Even
import KummerCriterion.GaussSum.Basic
import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.DetBridge
import Mathlib.NumberTheory.LSeries.Nonvanishing
import KummerCriterion.CyclotomicUnits.DeletedFourier

/-!
# Deleted Fourier determinant on the even cyclotomic quotient

This file specializes the abstract deleted Fourier determinant identity to
`CyclotomicEvenDelta p = (ZMod p)ˣ / {±1}` and identifies the `hk` convention
with the existing `LehmerVandiver.Sinnott.quotientEigenvalue` normalization.
-/

noncomputable section

open scoped BigOperators

namespace KummerCriterion
namespace CyclotomicUnits

variable (p : ℕ) [Fact p.Prime]

/-- A noncanonical equivalence between nontrivial characters of the even
quotient and non-identity elements of the even quotient. It is used only
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
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
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
