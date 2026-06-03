module

public import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily
import KummerCriterion.LehmerVandiver.PrimaryUnits.Part1
import KummerCriterion.LehmerVandiver.PrimaryUnits.Part2
import KummerCriterion.LehmerVandiver.PrimaryUnits.Part3
import Mathlib.NumberTheory.NumberField.CMField
import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.SigmaPreservation
import KummerCriterion.LehmerVandiver.PlusCoprime.CharacterIdentification
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.FieldTheory.Finite.Basic
import KummerCriterion.TotallyRealSubfield.ClassGroup

/-!
# Sinnott index formula: structural decomposition

The classical Sinnott / Washington Theorem 8.2 states

 `[(𝓞 K⁺)ˣ: C⁺] = h⁺(K)`

for `K = ℚ(ζ_p)` (with `C⁺ ⊆ (𝓞 K)ˣ` the real cyclotomic-units
subgroup intersected with `realUnits K`, viewed via `(𝓞 K⁺)ˣ ≃ realUnits K`).

This file packages the index identity as a `Prop` predicate
`SinnottIndexFormula`, plus the connection to `regOfFamily` (already
shipped) and `cyclotomicUnitsPlus` (already shipped).

This is **Step (C/D)** of the Cor 8.19 / Sinnott bridge: the analytic
content (regulator of cyclotomic units = h⁺ · regulator K⁺ via the
Kummer-Dirichlet determinant identity for cyclotomic-unit logs combined
with the analytic CNF for K⁺) is encapsulated in this Prop, allowing
the rest of the chain to compose parametrically.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. §8.2
 (Theorem 8.2: Sinnott's index formula for the cyclotomic case).
* Sinnott, *On the Stickelberger ideal and the circular units of a
 cyclotomic field*, Annals of Math. 108 (1978).
* `KummerCriterion/HMinus/ClassNumberFormula.lean` — analytic CNF
 inputs (`hPlus_formula`, `hPlus_formula_of_evenLValues`).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **Sinnott's index formula** (Washington Thm 8.2, predicate form):
the index of `⟨cyclotomicUnitFamilyKplus⟩ ⊔ torsion` in `(𝓞 K⁺)ˣ`
equals `h⁺(K) = hPlus K`.

Equivalently (under the natural identifications), `[E⁺: C⁺] = h⁺`.

The proof requires:
1. The regulator-of-cyclotomic-units determinant computation
 (Kummer 1850, classical): `Reg(C⁺) = (factor) · ∏_{χ even nontrivial} L(1, χ)`.
2. The analytic CNF for K⁺ (already shipped as `hPlus_formula_of_evenLValues`):
 `h⁺ · Reg(K⁺) = (same factor) · ∏ L(1, χ)`.
3. Comparison: `Reg(C⁺) / Reg(K⁺) = h⁺`, which by `regOfFamily_div_regulator`
 equals `[E⁺: ⟨family⟩ ⊔ torsion]`.

Step 1 is the substantive deferred content. -/
def SinnottIndexFormula (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (Subgroup.closure
      (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
    NumberField.Units.torsion (NumberField.maximalRealSubfield K)).index =
  2 ^ ((p - 3) / 2) * hPlus K

set_option backward.isDefEq.respectTransparency false in
/-- **Sinnott formula in regulator form**: equivalent statement asserting
`regOfFamily(family) = 2^((p-3)/2) · h⁺ · regulator(K⁺)` directly.
The factor `2^((p-3)/2)` reflects the index of the squared cyclotomic
unit subgroup `⟨realCyclotomicUnit_k⟩` inside the standard cyclotomic
units `C⁺`; multiplied by the Sinnott index `[U⁺: C⁺] = h⁺` gives the
total index. Composes with `regOfFamily_div_regulator` to give the
index formula. -/
def SinnottRegulatorIdentity (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
    (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) *
      NumberField.Units.regulator (NumberField.maximalRealSubfield K)

set_option backward.isDefEq.respectTransparency false in
/-- **Equivalence of Sinnott formula formulations**: the index version
follows from the regulator version (both encode the same content via
`regOfFamily_div_regulator`). -/
theorem sinnottIndexFormula_of_regulatorIdentity
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottRegulatorIdentity p K hp_odd hp_three) :
    SinnottIndexFormula p K hp_odd hp_three := by
  unfold SinnottIndexFormula SinnottRegulatorIdentity at *
  have h_div := regOfFamily_cyclotomicUnitFamilyKplus_div_regulator
    p K hp_odd hp_three
  have h_reg_pos : 0 < NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) :=
    NumberField.Units.regulator_pos _
  rw [h] at h_div
  rw [show (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) *
        NumberField.Units.regulator (NumberField.maximalRealSubfield K) /
        NumberField.Units.regulator (NumberField.maximalRealSubfield K) =
      2 ^ ((p - 3) / 2) * (hPlus K : ℝ) from by
    field_simp] at h_div
  exact_mod_cast h_div.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Sinnott formula bridge target**: under `SinnottIndexFormula` (step C/D),
the index identity gives `[E⁺: ⟨family⟩ ⊔ torsion] = 2^((p-3)/2) · h⁺`
directly. The factor `2^((p-3)/2)` reflects the gap between the project's
squared cyclotomic family `⟨realCyclotomicUnit_k⟩` and the standard
cyclotomic units `C⁺`. -/
theorem index_eq_twoPow_mul_hPlus_of_sinnottIndexFormula
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottIndexFormula p K hp_odd hp_three) :
    (Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K)).index =
    2 ^ ((p - 3) / 2) * hPlus K := h

end Sinnott

end LehmerVandiver

end KummerCriterion

end
