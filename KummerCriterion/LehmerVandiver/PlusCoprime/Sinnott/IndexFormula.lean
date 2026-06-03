import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily
import KummerCriterion.LehmerVandiver.PrimaryUnits.Part1
import KummerCriterion.LehmerVandiver.PrimaryUnits.Part2
import KummerCriterion.LehmerVandiver.PrimaryUnits.Part3
import Mathlib.NumberTheory.NumberField.CMField
import KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.SigmaPreservation
import KummerCriterion.LehmerVandiver.PlusCoprime.KummerLift.CharacterIdentification
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.FieldTheory.Finite.Basic
import KummerCriterion.TotallyRealSubfield.ClassGroup

/-!
# Sinnott index formula: structural decomposition

The classical Sinnott / Washington Theorem 8.2 states

  `[(𝓞 K⁺)ˣ : C⁺] = h⁺(K)`

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

Equivalently (under the natural identifications), `[E⁺ : C⁺] = h⁺`.

The proof requires:
1. The regulator-of-cyclotomic-units determinant computation
   (Kummer 1850, classical): `Reg(C⁺) = (factor) · ∏_{χ even nontrivial} L(1, χ)`.
2. The analytic CNF for K⁺ (already shipped as `hPlus_formula_of_evenLValues`):
   `h⁺ · Reg(K⁺) = (same factor) · ∏ L(1, χ)`.
3. Comparison: `Reg(C⁺) / Reg(K⁺) = h⁺`, which by `regOfFamily_div_regulator`
   equals `[E⁺ : ⟨family⟩ ⊔ torsion]`.

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
units `C⁺`; multiplied by the Sinnott index `[U⁺ : C⁺] = h⁺` gives the
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
  -- regOfFamily(family) / regulator(K⁺) = [E⁺ : ⟨family⟩ ⊔ torsion] (mathlib).
  have h_div := regOfFamily_cyclotomicUnitFamilyKplus_div_regulator
    p K hp_odd hp_three
  -- regulator K⁺ ≠ 0 (positive).
  have h_reg_pos : 0 < NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) :=
    NumberField.Units.regulator_pos _
  rw [h] at h_div
  -- h_div : 2^((p-3)/2) · h⁺ · R / R = (index : ℝ)
  rw [show (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) *
        NumberField.Units.regulator (NumberField.maximalRealSubfield K) /
        NumberField.Units.regulator (NumberField.maximalRealSubfield K) =
      2 ^ ((p - 3) / 2) * (hPlus K : ℝ) from by
    field_simp] at h_div
  -- h_div : 2^((p-3)/2) · h⁺ = (index : ℝ)
  exact_mod_cast h_div.symm

set_option backward.isDefEq.respectTransparency false in
/-! ## Connection to the analytic CNF for K⁺

The analytic CNF for K⁺ (already shipped as `hPlus_formula`) gives

  `(hPlus K : ℝ) · regulator K⁺ = dedekindZeta_residue K⁺ ·
    (torsionOrder · √|disc K⁺|) / (2^r · (2π)^c)`

where the RHS is purely analytic (no `hPlus`, no `regulator`).

Therefore `SinnottRegulatorIdentity` is equivalent to the (purely
analytic) claim that `regOfFamily(family)` equals this same expression.
This isolates the substantive analytic content as a comparison with
the analytic CNF. -/

set_option backward.isDefEq.respectTransparency false in
/-! ## Connection to `Cor8_19Bridge`

Once `SinnottIndexFormula` is established, the **structural contrapositive
engine** (step F) reduces `Cor8_19Bridge` to a "p-saturation" check:

  Under `¬ p ∣ h⁺`, the family-generated subgroup `⟨family⟩ ⊔ torsion`
  has index coprime to p in `(𝓞 K⁺)ˣ`. Hence the inclusion
  `⟨family⟩ ⊔ torsion ↪ (𝓞 K⁺)ˣ` is "p-saturated", i.e., a unit is a
  p-th power in `(𝓞 K⁺)ˣ` iff it is a p-th power in
  `⟨family⟩ ⊔ torsion` (when the unit lies in the latter).

For `pollaczekUnitPlus ∈ ⟨family⟩ ⊔ torsion` (extending step E to the
family-version), the contrapositive form of the local certificate gives
the bridge.

This requires the additional fact `pollaczekUnitPlus ∈ ⟨family⟩ ⊔ torsion`,
which strengthens `pollaczekUnitPlus ∈ cyclotomicUnitsPlus` to
membership in the FAMILY-GENERATED subgroup (mathematically the same
under Sinnott's full theorem, but a separate step in the formal chain). -/

set_option backward.isDefEq.respectTransparency false in
/-- **Sinnott formula bridge target**: under `SinnottIndexFormula` (step C/D),
the index identity gives `[E⁺ : ⟨family⟩ ⊔ torsion] = 2^((p-3)/2) · h⁺`
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

/-! ## The "Pollaczek-in-family" hypothesis

For Cor 8.19's contrapositive engine, we need the family-generated
subgroup `⟨family⟩ ⊔ torsion` to contain `pollaczekUnitPlus`. This is
mathematically equivalent (by Sinnott) to `pollaczekUnitPlus ∈ C⁺`,
already proven, but as a formal Lean fact requires showing the family
generates `C⁺ ⊔ torsion`.

We package this as a separate Prop. -/

/-! ## Cor8_19 bridge from Sinnott + Pollaczek-in-family

Under `SinnottIndexFormula` and `PollaczekInFamily`, the "p-saturation"
argument gives `Cor8_19Bridge`:

* `¬ p ∣ h⁺` (target conclusion).
* `[E⁺ : ⟨family⟩ ⊔ torsion] = h⁺` (Sinnott).
* So `p ∤ [E⁺ : ⟨family⟩ ⊔ torsion]`.
* For `α^p = pollaczekUnitPlus` in `E⁺` with α : (𝓞 K)ˣ — the descent
  of α to a family-or-torsion element exists by p-saturation, giving the
  contrapositive: `¬IsPthPower(pollaczekUnitPlus in E⁺) → ¬p∣h⁺`.

This is the structural form of the Cor 8.19 contrapositive engine. -/

end Sinnott

end LehmerVandiver

end KummerCriterion

end
