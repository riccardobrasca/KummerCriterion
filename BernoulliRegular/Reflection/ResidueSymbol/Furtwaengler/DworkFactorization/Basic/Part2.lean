module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkWitt
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingCongruence
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceCoefficientExpansion
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.RingTheory.Nilpotent.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Basic.Part1

/-!
# Basic Dwork factorization algebra

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w




/-- A finite sum over a cyclically shifted range is unchanged when the
last shifted term equals the first term. -/
theorem sum_range_shift_eq_of_last_eq_first
    {A : Type*} [AddCommMonoid A] (g : ℕ → A) (f : ℕ)
    (hperiod : g f = g 0) :
    (∑ i ∈ Finset.range f, g (i + 1)) =
      ∑ i ∈ Finset.range f, g i := by
  cases f with
  | zero =>
      simp
  | succ f =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp [hperiod]

/-- A finite sum over a cyclic range is unchanged by any finite shift. -/
theorem sum_range_shift_iterate_eq_of_period
    {A : Type*} [AddCommMonoid A] (g : ℕ → A) (f m : ℕ)
    (hperiod : ∀ n : ℕ, g (n + f) = g n) :
    (∑ i ∈ Finset.range f, g (i + m)) =
      ∑ i ∈ Finset.range f, g i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        (∑ i ∈ Finset.range f, g (i + (m + 1)))
            = ∑ i ∈ Finset.range f, (fun n : ℕ => g (n + m)) (i + 1) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              congr 1
              omega
        _ = ∑ i ∈ Finset.range f, (fun n : ℕ => g (n + m)) i := by
              refine sum_range_shift_eq_of_last_eq_first
                (fun n : ℕ => g (n + m)) f ?_
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hperiod m
        _ = ∑ i ∈ Finset.range f, g i := ih


end Furtwaengler

end BernoulliRegular

end
