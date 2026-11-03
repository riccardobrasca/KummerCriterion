module

public import KummerCriterion.LValueAtOne.Odd
import KummerCriterion.LValueAtOne.Cosine
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Even-character `L(1, χ)` formulas

This file packages the even `L(1, χ)` evaluation from the cosine-side
boundary-value identities.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace KummerCriterion

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- `L(1, χ)` for even primitive characters modulo `p`. -/
theorem even_LFunction_one_eq_evenLValueRhs
    {χ : DirichletCharacter ℂ p} (hχ_prim : χ.IsPrimitive) (hχ_even : χ.Even) :
    DirichletCharacter.LFunction χ 1 = evenLValueRhs p χ := by
  change ZMod.LFunction (fun a : ZMod p => χ a) 1 = evenLValueRhs p χ
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hχinv_even : (χ⁻¹).Even := by
    simpa only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_eq_one] using hχ_even
  have hχinv_zero : χ⁻¹ 0 = 0 := (χ⁻¹).map_zero' hp_ne_one
  let χinv : ZMod p → ℂ := fun a => χ⁻¹ a
  have hdft :
      ZMod.LFunction (ZMod.dft χinv) 1 =
        ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 := by
    simpa using
      (ZMod.LFunction_dft (Φ := χinv) (s := (1 : ℂ))
        (hs := Or.inl (by simpa [χinv] using hχinv_zero)))
  have hft :
      ZMod.dft χinv = fun a : ZMod p =>
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * χ a := by
    funext a
    simpa [χinv, hχ_even.to_fun a, mul_comm] using
      (DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ := χ⁻¹) hχ_prim.inv a)
  have hleft :
      ZMod.LFunction (ZMod.dft χinv) 1 =
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * ZMod.LFunction χ 1 := by
    simp only [hft, ZMod.LFunction, mul_assoc, ← Finset.mul_sum, mul_left_comm]
  have hsum_sin_zero :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 = 0 := by
    refine (hχinv_even.to_fun.mul_odd fun a => ?_).sum_eq_zero
    simpa using HurwitzZeta.sinZeta_neg (ZMod.toAddCircle a) (1 : ℂ)
  have hsum_isin_zero :
      ∑ a : ZMod p, χ⁻¹ a *
          (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) = 0 := by
    calc
      ∑ a : ZMod p, χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)
          = Complex.I *
              ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by ring
      _ = 0 := by rw [hsum_sin_zero, mul_zero]
  have hsum_exp :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 =
        ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := by
    calc
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1
          = ∑ a : ZMod p,
              (χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
                χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)) := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  have hneg : ZMod.toAddCircle (-a) = -ZMod.toAddCircle a :=
                    map_neg ZMod.toAddCircle a
                  rw [hneg, HurwitzZeta.expZeta, HurwitzZeta.cosZeta_neg,
                    HurwitzZeta.sinZeta_neg]
                  ring
      _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
            ∑ a : ZMod p,
              χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := by
            rw [hsum_isin_zero, sub_zero]
  have hboundary :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
        -evenLValueLogSum p χ := by
    rw [evenLValueLogSum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rcases eq_or_ne a 0 with rfl | ha
    · simp [hχinv_zero]
    · rw [cosZeta_toAddCircle_one_eq_boundary (p := p) ha,
        norm_one_sub_stdAddChar (p := p) ha]
      simp
  have hgauss_ne : gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [DirichletCharacter.norm_gaussSum_stdAddChar hχ_prim.inv]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 hp.out.pos)).ne'
  apply (mul_left_cancel₀ hgauss_ne)
  calc
    gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * ZMod.LFunction χ 1
        = ZMod.LFunction (ZMod.dft χinv) 1 := hleft.symm
    _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 := hdft
    _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := hsum_exp
    _ = -evenLValueLogSum p χ := hboundary
    _ = gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * evenLValueRhs p χ := by
          simp [evenLValueRhs, hgauss_ne, mul_left_comm, mul_comm]

end LValueAtOne

end KummerCriterion
