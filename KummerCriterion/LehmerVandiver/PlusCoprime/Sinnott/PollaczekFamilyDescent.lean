import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.IndexFormula
import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily

/-!
# `PollaczekInFamily` — Pollaczek descent to the family subgroup

The Pollaczek unit `pollaczekUnitPlus p K i = ∏_b cyclotomicRealUnit b ^ exp_b`
is by construction a finite product of real cyclotomic units. Each
`cyclotomicRealUnit b` (for `b ∈ {2,..., (p-1)/2}`) descends to the K⁺-side
family element `cyclotomicUnitFamilyKplus (b - 2)`. The b=1 term is trivial.

Hence the K⁺-side preimage `v` of `pollaczekUnitPlus` is the corresponding
product of family elements raised to the same exponents — and lies in
`⟨family⟩` (a Subgroup).

This proves `PollaczekInFamily`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

set_option backward.isDefEq.respectTransparency false in
/-- **Each family element's algebraMap is the K-side `realCyclotomicUnit`**.

Direct from `realCyclotomicUnitPlusUnit_val` + `algebraMap_realCyclotomicUnitPlus`. -/
theorem algebraMap_cyclotomicUnitFamilyKplus
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
          (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
          𝓞 (NumberField.maximalRealSubfield K)) =
      LehmerVandiver.realCyclotomicUnit p K
        ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
          (KummerCriterion.units_rank_eq_prime_sub_three_div_two
            (p := p) (K := K)))) + 2) := by
  unfold cyclotomicUnitFamilyKplusFinRank cyclotomicUnitFamilyKplus
  rw [realCyclotomicUnitPlusUnit_val]
  exact LehmerVandiver.algebraMap_realCyclotomicUnitPlus p K _

end Sinnott

end LehmerVandiver

end KummerCriterion

end
