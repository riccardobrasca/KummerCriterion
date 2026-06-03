module

public import KummerCriterion.CyclotomicUnits.KummerLogTrace
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Linear algebra for the Kummer logarithm matrix

This file contains the finite-field linear algebra used by the saturation
assembly: a square matrix over `ZMod p` with nonzero determinant has trivial
right kernel, specialized to the concrete Kummer logarithm matrix.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion
namespace CyclotomicUnits

/-- Over `ZMod p`, a square matrix with nonzero determinant has trivial
right kernel. -/
theorem vector_eq_zero_of_det_ne_zero_of_mulVec_eq_zero
    {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι (ZMod p)} {v : ι → ZMod p}
    (hdet : M.det ≠ 0) (hv : Matrix.mulVec M v = 0) :
    v = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero hdet hv

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

/-- If the concrete Kummer matrix has nonzero determinant, every vector in its
right kernel has all coordinates zero. -/
theorem exponents_modP_eq_zero_of_kummerLogMatrix_relation
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (e : Fin (kummerLogRank p) → ℤ)
    (hdet : (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five).det ≠ 0)
    (hrel :
      Matrix.mulVec
          (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five)
          (fun a : Fin (kummerLogRank p) => (e a : ZMod p)) =
        0) :
    ∀ a : Fin (kummerLogRank p), (e a : ZMod p) = 0 :=
  fun a => congr_fun (vector_eq_zero_of_det_ne_zero_of_mulVec_eq_zero hdet hrel) a

end CyclotomicUnits
end KummerCriterion

end
