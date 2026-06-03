import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LogEmbedding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# LV-SIN-B: Vandermonde-style determinant evaluation

The Kummer-Dirichlet determinant identity for cyclotomic units.

For real cyclotomic units `realCyclotomicUnit k = (1-ζ^k)(1-ζ^{-k}) /
((1-ζ)(1-ζ^{-1}))`, applying a complex embedding `φ(ζ) = e^{2πi a/p}`:

 `|φ(realCyclotomicUnit k)| = sin²(πak/p) / sin²(πa/p)`

The log-embedding matrix has entries

 `log|φ_a(realCyclotomicUnit k)| = 2 log|sin(πak/p)| - 2 log|sin(πa/p)|`

Its determinant evaluates via character orthogonality + Dirichlet's
class number formula derivation to a product of L-values.

This is the analytic heart of Sinnott's formula.

## Foundational lemmas
-/

@[expose] public section

noncomputable section

open Complex Real

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

/-- **Norm-squared of `1 - e^{iθ}`**: `|1 - e^{iθ}|² = 2 - 2 cos θ`. -/
theorem normSq_one_sub_exp_I_mul (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) = 2 - 2 * Real.cos θ := by
  rw [Complex.exp_mul_I, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.cos_ofReal_re,
    Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re, Complex.I_im,
    Complex.sin_ofReal_im, Complex.cos_ofReal_im, mul_zero,
    mul_one, sub_self, Complex.sub_im, Complex.one_im,
    Complex.add_im, Complex.mul_im, zero_sub]
  have h_pyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  nlinarith [h_pyth]

/-- **Norm-squared of `1 - e^{iθ}` as `4 sin²(θ/2)`**: half-angle form. -/
theorem normSq_one_sub_exp_I_mul_eq_four_sin_sq (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) =
      4 * Real.sin (θ / 2) ^ 2 := by
  rw [normSq_one_sub_exp_I_mul]
  have h_cos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have : Real.cos (2 * (θ / 2)) = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      rw [Real.cos_two_mul]
      have h_pyth : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq _
      nlinarith [h_pyth]
    rw [show 2 * (θ / 2) = θ from by ring] at this
    exact this
  rw [h_cos]
  ring

/-- **Norm of `1 - e^{iθ}`**: `‖1 - e^{iθ}‖ = 2 |sin(θ/2)|`. -/
theorem norm_one_sub_exp_I_mul (θ : ℝ) :
    ‖(1 - Complex.exp (θ * Complex.I))‖ = 2 * |Real.sin (θ / 2)| := by
  have h_sq : ‖(1 - Complex.exp (θ * Complex.I))‖ ^ 2 =
      (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [Complex.sq_norm, normSq_one_sub_exp_I_mul_eq_four_sin_sq]
    rw [mul_pow, sq_abs]; ring
  have h_nonneg : 0 ≤ ‖(1 - Complex.exp (θ * Complex.I))‖ := norm_nonneg _
  have h_pos : 0 ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith [h_sq, h_nonneg, h_pos]

/-- **Specialised**: for `θ = 2π · q` with rational q, `‖1 - e^{2πi q}‖ = 2|sin(πq)|`. -/
theorem norm_one_sub_exp_two_pi_I_mul (q : ℝ) :
    ‖(1 - Complex.exp (((2 * Real.pi * q) : ℝ) * Complex.I))‖ =
      2 * |Real.sin (Real.pi * q)| := by
  rw [norm_one_sub_exp_I_mul]
  congr 2
  ring_nf

end Sinnott

end LehmerVandiver

end KummerCriterion

end
