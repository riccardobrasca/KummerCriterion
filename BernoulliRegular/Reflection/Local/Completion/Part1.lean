module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import BernoulliRegular.Reflection.Local.Graded

/-!
# Completed local principal units

This file starts the REF-10d3b completed endpoint layer.  The localized ring
`Localization.AtPrime` is not complete, so the reverse `p`-power endpoint is
recorded in the adic completion at the cyclotomic maximal ideal.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section Binomial

variable {R : Type*} [CommSemiring R] {u v : R} {q : ℕ}


end Binomial

section QuotientAux

variable {R : Type*} [CommRing R] (I : Ideal R)

private theorem factor_evalₐ_pow_le {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  simp only [AdicCompletion.evalₐ, AlgHom.coe_comp, Function.comp_apply,
    AlgHom.ofLinearMap_apply]
  have htrans :
      AdicCompletion.transitionMap I R hmn ((AdicCompletion.eval I R n) x) =
        ((AdicCompletion.eval I R m) x) :=
    AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := R) hmn x
  rw [← htrans]
  induction ((AdicCompletion.eval I R n) x) using Quotient.inductionOn' with
  | h r =>
    rfl

private theorem mem_cotangentIdeal_iff_factor_pow_one_eq_zero (q : R ⧸ I ^ 2) :
    q ∈ I.cotangentIdeal ↔
      Ideal.Quotient.factor
        (show I ^ 2 ≤ I ^ 1 by exact Ideal.pow_le_pow_right (by decide : 1 ≤ 2)) q = 0 := by
  induction q using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (I ^ 2) r ∈ I.cotangentIdeal ↔
      Ideal.Quotient.factor
        (show I ^ 2 ≤ I ^ 1 by exact Ideal.pow_le_pow_right (by decide : 1 ≤ 2))
        (Ideal.Quotient.mk (I ^ 2) r) = 0
    rw [Ideal.mk_mem_cotangentIdeal]
    change r ∈ I ↔ Ideal.Quotient.mk (I ^ 1) r = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [pow_one]

end QuotientAux

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
































end CyclotomicSetup
end Local
end Reflection
end BernoulliRegular
