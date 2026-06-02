module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceBinomial
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceMultinomial
public import Mathlib.Data.Fintype.Units
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Trace coefficient expansions (REF-18c2c4-L2c3d2)

This file packages the coefficient-expansion API needed after the
reciprocal-convention correction.  The raw combinatorics in
`TraceMultinomial.lean` expands `(traceSum x)^n`; here we record the
weighted exponent contributed by a multi-index, specialise the trace
formula to a `TraceFormStickelbergerSetup`, and expose a factorial-cleared
form of the reciprocal trace-binomial coefficient sums.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w


variable {R : Type*} [CommSemiring R]


namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- The `ZMod ℓ`-dimension of the residue field is the setup parameter `f`.

This lets the standard finite-field trace formula use the same `S.f` that
appears in the Stickelberger digit-sum notation. -/
theorem trace_finrank_eq_f : Module.finrank (ZMod ℓ) k = S.f := by
  have hpow : ℓ ^ Module.finrank (ZMod ℓ) k = ℓ ^ S.f := by
    rw [FiniteField.pow_finrank_eq_card, S.card_k]
  exact Nat.pow_right_injective (Fact.out : Nat.Prime ℓ).one_lt hpow

/-- Setup-specialised bridge from the algebraic trace to `traceSum`. -/
theorem algebraMap_trace_pow_eq_traceSum_pow_setup (x : k) (n : ℕ) :
    algebraMap (ZMod ℓ) k (Algebra.trace (ZMod ℓ) k x) ^ n =
      (traceSum ℓ S.f x) ^ n :=
  algebraMap_trace_pow_eq_traceSum_pow
    (K := ZMod ℓ) (L := k) (ℓ := ℓ) (f := S.f)
    (Nat.card_zmod ℓ) S.trace_finrank_eq_f x n


section UnitSums

variable [DecidableEq k]


end UnitSums


end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
