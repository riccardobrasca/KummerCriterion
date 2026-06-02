import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.DetBridge.Part1

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]


/-! ## Factorization of D_nontriv_sq: `D = diag(qe) · D'`

The diagonal eigenvalue matrix factors as `diag(qe) · D'` where
`D'[ξ, i] = ξ(b)⁻¹ - 1` (the "shifted" character matrix). This
allows extraction of `∏_{χ ≠ 1} qe(χ)` from `det(D_nontriv_sq)`. -/





/-! ## Substantive sub-named-hypothesis: pure character-algebra identity

Combining everything above, `DetASubBEqProdNontrivialQe` reduces (under
parametric IsUnit hypotheses on `det(D_nontriv_sq)` and Dirichlet
non-vanishing) to a **purely character-matrix-algebra identity**:

  `det(D'_nontriv_sq) · scalar = ±det(charMatrix_nontriv_sq)`

where:
- `D'_nontriv_sq` is the "shifted character matrix" (no qe factors).
- `charMatrix_nontriv_sq` is the standard character matrix on K⁺ places.
- `scalar = 1 - row_corr · D_nontriv_sq⁻¹ · col_kw0` (from matrix det lemma).

All `qe(χ)` factors have been extracted; this is a clean character-orthogonality
identity. -/






set_option maxHeartbeats 4000000 in
-- This composed determinant identity elaborates several matrix reductions at once.


set_option maxHeartbeats 8000000 in
-- The final determinant discharge unfolds named hypotheses and needs a larger heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
open Classical in

/-! ## Summary: PF-1 substantive content reduced to three named hypotheses

`DetASubBEqProdNontrivialQe` (the substantive Sinnott Frobenius identity)
follows from the conjunction:

  1. `SinnottCharMatrixDetIdentity` — pure character-matrix-algebra identity.
  2. `SinnottDiagonalEigenvalueDetUnit` — Dirichlet non-vanishing.
  3. `CharMatrixKplusNontrivDetUnit` — character-matrix non-singularity.

All three are standard Frobenius/Dirichlet-theory facts but require
substantial development to discharge in Lean.

Once `DetASubBEqProdNontrivialQe` is discharged, the shipped
`kummerDirichletDeterminant_of_detASubBEqProdNontrivialQe` gives
`KummerDirichletDeterminant` (PF-1 target). -/

end Sinnott

end FLT37

end BernoulliRegular

end
