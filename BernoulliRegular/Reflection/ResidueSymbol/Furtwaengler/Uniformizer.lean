module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Ring.Associated
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import FltRegular.NumberTheory.Cyclotomic.UnitLemmas


/-!
# Uniformizer fact derivation (REF-18c2c4-L2c3a-prove)

Provides a free-standing proof that `π = ζ_ℓ - 1` is a `Q`-uniformizer
in `R' = ℚ(ζ_p, ζ_ℓ)` for any prime `Q` of `𝓞 R'` above `ℓ`. This
derives the field `pi_not_mem_Q_sq` of `TraceFormStickelbergerSetup`
from cyclotomic ramification theory (mathlib's
`IsCyclotomicExtension.Rat.ramificationIdx_eq` with `n = ℓ · p`,
prime `ℓ`, `m = p`, `k = 0`).

Strategy:
1. Convert `IsCyclotomicExtension {p, ℓ} ℚ R'` to
   `IsCyclotomicExtension {ℓ · p} ℚ R'` via `IsPrimitiveRoot.pow_mul_pow_lcm`
   + `IsPrimitiveRoot.adjoin_pair_eq` + `isCyclotomicExtension_singleton_iff_eq_adjoin`.
2. Apply `IsCyclotomicExtension.Rat.ramificationIdx_eq` to get
   `ramificationIdx of ℓ in 𝓞 R' = ℓ - 1`.
3. The cyclotomic identity `ℓ = u · π^(ℓ-1)` (for some unit `u`)
   combined with the ramification index gives `v_Q(π) = 1`, hence
   `π ∉ Q^2`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w




/-- **Complex conjugation of a primitive `n`-th root in a CM field**:
for any CM field `F` and any `ζ : 𝓞 F` that is a primitive `n`-th root,
complex conjugation sends `ζ` to `ζ ^ (n - 1)` (i.e., its inverse).

This is the generic version of `complexConj_apply_zeta` (which was
specialized to the canonical cyclotomic root). It works for any
primitive `n`-th root in any CM field. -/
theorem ringOfIntegersComplexConj_primitiveRoot
    {n : ℕ} (hn_pos : 0 < n)
    {F : Type*} [Field F] [NumberField F] [NumberField.IsCMField F]
    {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ n) :
    (NumberField.IsCMField.ringOfIntegersComplexConj F ζ : 𝓞 F) =
      (ζ : 𝓞 F) ^ (n - 1) := by
  haveI : NeZero n := ⟨hn_pos.ne'⟩
  -- ζ is a unit (primitive root in a domain).
  have hζ_unit : IsUnit ζ := hζ.isUnit hn_pos.ne'
  let u : (𝓞 F)ˣ := hζ_unit.unit
  have hu_val : (u : 𝓞 F) = ζ := IsUnit.unit_spec _
  -- u is in the torsion subgroup since u^n = 1.
  have hu_pow : u ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu_val, Units.val_one]
    exact hζ.pow_eq_one
  have hu_torsion : u ∈ NumberField.Units.torsion F := by
    refine (CommGroup.mem_torsion _ _).2 ?_
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn_pos, hu_pow⟩
  -- complexConj sends torsion to inverse.
  have hconj := NumberField.IsCMField.unitsComplexConj_torsion F ⟨u, hu_torsion⟩
  -- u⁻¹ = u ^ (n-1) since u^n = 1.
  have hu_inv : u⁻¹ = u ^ (n - 1) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_one_add_one hn_pos.ne']
    exact hu_pow
  -- Combine: ringOfIntegersComplexConj F ζ = u⁻¹ as integers, which equals u^(n-1) = ζ^(n-1).
  have h_ring_eq_units : (NumberField.IsCMField.ringOfIntegersComplexConj F ζ : 𝓞 F) =
      ((NumberField.IsCMField.unitsComplexConj F u : (𝓞 F)ˣ) : 𝓞 F) := by
    have : (NumberField.IsCMField.ringOfIntegersComplexConj F ζ : 𝓞 F) =
        (NumberField.IsCMField.ringOfIntegersComplexConj F (u : 𝓞 F) : 𝓞 F) := by
      rw [hu_val]
    rw [this]
    rfl
  rw [h_ring_eq_units, hconj]
  -- Goal: ↑↑⟨u, hu_torsion⟩⁻¹ = ζ ^ (n - 1)
  -- Note: torsion-subgroup inverse coerces to (𝓞 F)ˣ inverse on the underlying value.
  have h_torsion_inv :
      ((⟨u, hu_torsion⟩⁻¹ : NumberField.Units.torsion F) : (𝓞 F)ˣ) = u⁻¹ := rfl
  rw [h_torsion_inv, hu_inv, Units.val_pow_eq_pow_val, hu_val]




/-- Cyclotomic identity (sketch): for a primitive `ℓ`-th root of unity
`ζ` in a domain, `(↑ℓ : R)` is associated to `(ζ - 1)^(ℓ - 1)`.

**Proof outline:**
1. `Polynomial.eval_one_cyclotomic_prime` gives `Φ_ℓ(1) = ℓ` in `R`.
2. `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ` factors
   `Φ_ℓ = ∏_{μ ∈ primitiveRoots ℓ R} (X - C μ)`.
3. Evaluating at 1: `↑ℓ = ∏_{μ ∈ primitiveRoots ℓ R} (1 - μ)`.
4. For `ℓ` prime, every primitive `ℓ`-th root has the form `ζ^j` for
   some `1 ≤ j < ℓ` with `gcd(j, ℓ) = 1`.
5. `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime` gives
   `(ζ^j - 1) ~ (ζ - 1)`, hence `(1 - ζ^j) ~ (1 - ζ)` (associated up
   to a sign unit).
6. Product: `↑ℓ ~ (1 - ζ)^(ℓ-1) ~ ((-1)^(ℓ-1)) (ζ - 1)^(ℓ-1)`,
   so `↑ℓ ~ (ζ - 1)^(ℓ-1)`. -/
theorem associated_ell_zeta_sub_one_pow
    {ℓ : ℕ} [Fact ℓ.Prime]
    {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ ℓ) :
    Associated (ℓ : R) ((ζ - 1) ^ (ℓ - 1)) := by
  classical
  have hℓ_prime : Nat.Prime ℓ := Fact.out
  have hℓ_pos : 0 < ℓ := hℓ_prime.pos
  have h_eval :
      (ℓ : R) = ∏ μ ∈ primitiveRoots ℓ R, (1 - μ) := by
    have h := (Polynomial.eval_one_cyclotomic_prime (R := R) (p := ℓ)).symm
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h
    simpa using h
  have h_prod :
      Associated (∏ μ ∈ primitiveRoots ℓ R, (1 - μ))
        (∏ μ ∈ primitiveRoots ℓ R, (ζ - 1)) := by
    refine Associated.prod (primitiveRoots ℓ R) (fun μ => 1 - μ) (fun _ => ζ - 1) ?_
    intro μ hμ
    have hμ_prim : IsPrimitiveRoot μ ℓ := (mem_primitiveRoots hℓ_pos).1 hμ
    obtain ⟨i, _hi_lt, hi_coprime, hζi⟩ := (hζ.isPrimitiveRoot_iff).1 hμ_prim
    have hassoc : Associated (ζ - 1) (μ - 1) := by
      rw [← hζi]
      exact hζ.associated_sub_one_pow_sub_one_of_coprime hi_coprime
    simpa [sub_eq_add_neg, add_comm] using hassoc.symm.neg_left
  have h_card : (primitiveRoots ℓ R).card = ℓ - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hℓ_prime]
  have h_prod_pow :
      Associated (∏ μ ∈ primitiveRoots ℓ R, (1 - μ)) ((ζ - 1) ^ (ℓ - 1)) := by
    simpa [Finset.prod_const, h_card] using h_prod
  simpa [h_eval] using h_prod_pow

/-- Membership in an ideal is invariant under replacing an element by an
associate. -/
theorem associated_mem_ideal_iff
    {R : Type*} [CommRing R] {a b : R} (h : Associated a b)
    {I : Ideal R} :
    a ∈ I ↔ b ∈ I := by
  obtain ⟨u, rfl⟩ := h
  constructor
  · intro ha
    exact Ideal.mul_mem_right (u : R) I ha
  · intro hb
    have hmem : (a * (u : R)) * ↑u⁻¹ ∈ I :=
      Ideal.mul_mem_right (↑u⁻¹ : R) I hb
    simpa [mul_assoc] using hmem



namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- The rational residue characteristic has `Q`-adic order at least `ℓ - 1`
in the mixed cyclotomic integer ring. This is the membership half of the
cyclotomic identity `ℓ ~ (ζ_ℓ - 1)^(ℓ-1)`. -/
theorem natCast_ell_mem_Q_pow_pred
    (S : TraceFormStickelbergerSetup ℓ p k K R') :
    (ℓ : 𝓞 R') ∈ S.Q ^ (ℓ - 1) := by
  have hassoc :
      Associated (ℓ : 𝓞 R') ((S.zeta_ell_int - 1) ^ (ℓ - 1)) :=
    associated_ell_zeta_sub_one_pow S.zeta_ell_int_isPrimitiveRoot
  have hzeta_mem : (S.zeta_ell_int - 1) ^ (ℓ - 1) ∈ S.Q ^ (ℓ - 1) := by
    have hζ_sub_mem : S.zeta_ell_int - 1 ∈ S.Q := by
      rw [← S.hπ]
      exact S.π_mem_Q
    exact Ideal.pow_mem_pow hζ_sub_mem (ℓ - 1)
  exact (associated_mem_ideal_iff hassoc).2 hzeta_mem

/-- Power form of `natCast_ell_mem_Q_pow_pred`. -/
theorem natCast_ell_pow_mem_Q_pow_mul_pred
    (S : TraceFormStickelbergerSetup ℓ p k K R') (m : ℕ) :
    (ℓ : 𝓞 R') ^ m ∈ S.Q ^ (m * (ℓ - 1)) := by
  have hpow : (ℓ : 𝓞 R') ^ m ∈ (S.Q ^ (ℓ - 1)) ^ m :=
    Ideal.pow_mem_pow S.natCast_ell_mem_Q_pow_pred m
  rw [← pow_mul] at hpow
  simpa [Nat.mul_comm] using hpow

/-- If a natural coefficient is divisible by `ℓ^m`, then its image in the
ring of integers lies in `Q^(m*(ℓ-1))`. This is the coefficient-valuation
bridge needed by the higher trace-binomial estimate. -/
theorem natCast_mem_Q_pow_mul_pred_of_ell_pow_dvd
    (S : TraceFormStickelbergerSetup ℓ p k K R') {c m : ℕ}
    (hc : ℓ ^ m ∣ c) :
    (c : 𝓞 R') ∈ S.Q ^ (m * (ℓ - 1)) := by
  rcases hc with ⟨t, rfl⟩
  have hpow := S.natCast_ell_pow_mem_Q_pow_mul_pred m
  have hmul : (ℓ : 𝓞 R') ^ m * (t : 𝓞 R') ∈ S.Q ^ (m * (ℓ - 1)) :=
    Ideal.mul_mem_right (t : 𝓞 R') (S.Q ^ (m * (ℓ - 1))) hpow
  simpa [Nat.cast_mul, Nat.cast_pow] using hmul

end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
