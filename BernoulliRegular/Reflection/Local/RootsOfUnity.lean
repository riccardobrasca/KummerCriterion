module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import BernoulliRegular.Reflection.Local.Filtration


/-!
# Local cyclotomic roots of unity

This file starts the REF-10b root-of-unity layer for the local calculation.
It localizes the distinguished primitive `p`-th root of unity and proves that
the subgroup it generates lies in the first principal-unit step `U_1`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The distinguished cyclotomic root of unity, viewed as a unit in the
localized ring at `lambda`. -/
noncomputable def localCyclotomicZetaUnit : localCyclotomicUnitGroup p K :=
  Units.map (algebraMap (𝓞 K) (localCyclotomicRing p K))
    (IsCyclotomicExtension.zeta_spec p ℚ K).unit'

@[simp]
theorem localCyclotomicZetaUnit_coe :
    ((localCyclotomicZetaUnit p K : localCyclotomicUnitGroup p K) :
        localCyclotomicRing p K) =
      algebraMap (𝓞 K) (localCyclotomicRing p K)
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger := by
  rfl

/-- The localized distinguished root is not in the second principal-unit step. -/
theorem localCyclotomicZetaUnit_not_mem_principalUnitSubgroup_two :
    localCyclotomicZetaUnit p K ∉ principalUnitSubgroup p K 2 := by
  rw [mem_principalUnitSubgroup_iff]
  let hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  change ¬ (algebraMap (𝓞 K) (localCyclotomicRing p K) hζ.toInteger - 1 ∈
    localCyclotomicMaximalIdeal p K ^ 2)
  intro hmem
  have hπ_prime : Prime ((hζ.toInteger : 𝓞 K) - 1) := hζ.zeta_sub_one_prime'
  have hπ_ne : ((hζ.toInteger : 𝓞 K) - 1) ≠ 0 := hπ_prime.ne_zero
  have hmap : algebraMap (𝓞 K) (localCyclotomicRing p K)
      ((hζ.toInteger : 𝓞 K) - 1) ∈ localCyclotomicMaximalIdeal p K ^ 2 := by
    simpa using hmem
  rw [← localCyclotomicMaximalIdeal_eq_map p K] at hmap
  rw [← Ideal.map_pow] at hmap
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    (M := (cyclotomicLambda p K).primeCompl) (S := localCyclotomicRing p K)] at hmap
  rcases hmap with ⟨s, hs, hsπ⟩
  have hπ_sq_dvd : ((hζ.toInteger : 𝓞 K) - 1) ^ 2 ∣
      s * ((hζ.toInteger : 𝓞 K) - 1) := by
    simpa [cyclotomicLambda, zetaPrime, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using hsπ
  have hπ_dvd_s : ((hζ.toInteger : 𝓞 K) - 1) ∣ s :=
    (mul_dvd_mul_iff_right hπ_ne).mp (by
      simpa [pow_two] using hπ_sq_dvd)
  have hs_mem : s ∈ cyclotomicLambda p K := by
    simpa [cyclotomicLambda, zetaPrime, Ideal.mem_span_singleton] using hπ_dvd_s
  exact hs hs_mem


end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular
