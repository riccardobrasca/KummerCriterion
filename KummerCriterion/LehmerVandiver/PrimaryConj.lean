module

public import KummerCriterion.LehmerVandiver.Primary

/-!
# Complex conjugation preserves primarity

For a CM cyclotomic field `K = ℚ(ζ_p)`, complex conjugation `σ` sends `ζ` to
`ζ^{p-1}`. Hence `σ(ζ - 1) = ζ^{p-1} - 1 = -ζ^{p-1}(ζ - 1)`, and `σ(ζ - 1)`
is associated to `ζ - 1`. Divisibility by `(ζ - 1)^k` is therefore preserved
by `σ`, and primarity is `σ`-invariant.

The arithmetic input
`(ζ - 1)^{2p} ∣ α - σ(α)` (`zetaSubOne_pow_dvd_sub_complexConj`) is the entry
point for showing `[(α)] = [(σ(α))]` in `Cl(K)`, the Galois descent step
toward Vandiver Lemma 1.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* `KummerCriterion.TotallyRealSubfield.Conjugation`
 (`complexConj_apply_zeta`).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace KummerCriterion

namespace LehmerVandiver

section ConjSetup

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The unit `-ζ^{p-1} ∈ (𝓞 K)ˣ` realising the associated relation
`σ(ζ - 1) = (-ζ^{p-1}) (ζ - 1)`. -/
noncomputable def zetaSubOneConjUnit : (𝓞 K)ˣ :=
  (-1 : (𝓞 K)ˣ) * (zeta_spec p ℚ K).unit' ^ (p - 1)

omit [NumberField K] in
private theorem coe_neg_one_unit : ((-1 : (𝓞 K)ˣ) : 𝓞 K) = -1 := rfl

private theorem coe_unit'_eq_toInteger :
    ((zeta_spec p ℚ K).unit' : 𝓞 K) = (zeta_spec p ℚ K).toInteger :=
  rfl

/-- Complex conjugation multiplies `ζ - 1` by `-ζ^{p-1}`. -/
theorem complexConj_zetaSubOne_eq [IsCMField K] :
    ringOfIntegersComplexConj K (zetaSubOne p K) =
      ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) * zetaSubOne p K := by
  have hζ_pow : (zeta_spec p ℚ K).toInteger ^ p = 1 := zeta_toInteger_pow_eq_one p K
  have hconj_zeta : (ringOfIntegersComplexConj K (zeta_spec p ℚ K).toInteger : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) :=
    complexConj_apply_zeta (p := p) (K := K)
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.1.one_lt.le
  have key : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) *
      (zeta_spec p ℚ K).toInteger = 1 := by
    rw [← pow_succ, hp1]; exact hζ_pow
  have lhs_eq : ringOfIntegersComplexConj K (zetaSubOne p K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1 := by
    change ringOfIntegersComplexConj K ((zeta_spec p ℚ K).unit' - 1) = _
    rw [map_sub, map_one, coe_unit'_eq_toInteger, hconj_zeta]
  have rhs_eq : ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) * zetaSubOne p K =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1 := by
    change (((-1 : (𝓞 K)ˣ) * (zeta_spec p ℚ K).unit' ^ (p - 1) : (𝓞 K)ˣ) : 𝓞 K) *
        ((zeta_spec p ℚ K).unit' - 1) = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_neg_one_unit, coe_unit'_eq_toInteger]
    linear_combination -key
  rw [lhs_eq, rhs_eq]

/-- `σ(ζ - 1)` is associated to `ζ - 1` in `𝓞 K`. -/
theorem associated_complexConj_zetaSubOne [IsCMField K] :
    Associated (zetaSubOne p K) (ringOfIntegersComplexConj K (zetaSubOne p K)) :=
  ⟨zetaSubOneConjUnit p K, by rw [complexConj_zetaSubOne_eq]; ring⟩

end ConjSetup

end LehmerVandiver

end KummerCriterion

end
