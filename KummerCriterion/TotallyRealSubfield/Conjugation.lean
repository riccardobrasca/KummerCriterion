module

public import KummerCriterion.TotallyRealSubfield.ZetaPrime
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas

/-!
# Conjugation and unit classification

This file packages the conjugation-equivariance lemmas and the unit
classification used to remove the possible `-1` factor in the descent.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace KummerCriterion

section CyclotomicSetup

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Complex conjugation sends a principal ideal to the principal ideal of the
conjugated generator. -/
theorem conj_map_span_singleton [IsCMField K] (a : 𝓞 K) :
    (Ideal.span {a}).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span {ringOfIntegersComplexConj K a} := by
  simpa using
    (Ideal.map_span ((ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ({a} : Set (𝓞 K)))

/-- Complex conjugation acts trivially on ideals extended from `𝒪_{K⁺}`. -/
theorem ideal_map_conj_eq [IsCMField K]
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K))) :
    (I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) := by
  rw [Ideal.map_map]
  congr
  ext x
  simp [RingHom.comp_apply, AlgEquiv.commutes]

/-- If `(a) = (c(a))`, then `c(a)` differs from `a` by a unit. -/
theorem conj_generator_associated [IsCMField K]
    (a : 𝓞 K) (_ha : a ≠ 0) (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (hIa : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hIca : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a}) :
    ∃ u : (𝓞 K)ˣ, ringOfIntegersComplexConj K a = u * a := by
  let hspan : Ideal.span {a} = Ideal.span {ringOfIntegersComplexConj K a} := hIa.symm.trans hIca
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-- If `c(a) = u a` with `a ≠ 0`, then `c(u) u = 1`. -/
theorem conj_unit_mul_eq_one [IsCMField K]
    (a : 𝓞 K) (ha : a ≠ 0) (u : (𝓞 K)ˣ)
    (hu : ringOfIntegersComplexConj K a = u * a) :
    unitsComplexConj K u * u = 1 := by
  have hcc : ringOfIntegersComplexConj K (ringOfIntegersComplexConj K a) = a := by
    apply RingOfIntegers.ext
    simp [coe_ringOfIntegersComplexConj, complexConj_apply_apply]
  have hu1 : a = (unitsComplexConj K u : (𝓞 K)ˣ) * ringOfIntegersComplexConj K a := by
    simpa [hcc, unitsComplexConj, map_mul] using! congrArg (ringOfIntegersComplexConj K) hu
  rw [hu] at hu1
  have hu2 : a = (((unitsComplexConj K u * u : (𝓞 K)ˣ) : 𝓞 K) * a) := by
    simpa [mul_assoc] using hu1
  apply Units.ext
  apply mul_right_cancel₀ ha
  simpa [one_mul] using hu2.symm

include hp_odd in
/-- An antisymmetric unit yields a square of a cyclotomic root of unity. -/
theorem antisymmetric_unit_is_root_of_unity [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (u : (𝓞 K)ˣ) (_hu : unitsComplexConj K u * u = 1) :
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ = (hζ.unit' ^ m) ^ 2 :=
  unit_inv_conj_is_root_of_unity (hζ := hζ) u
    (lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd))

include hp_odd in
/-- An antisymmetric unit has the form `(-1)^k ζ^n`. -/
theorem antisymmetric_unit_eq_neg_one_pow_mul_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (u : (𝓞 K)ˣ)
    (hu : unitsComplexConj K u * u = 1) :
    ∃ n k : ℕ, u = (-1 : (𝓞 K)ˣ) ^ k * hζ.unit' ^ n := by
  obtain ⟨m, hm⟩ :=
    antisymmetric_unit_is_root_of_unity (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ) u hu
  have hcu : (unitsComplexConj K u)⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hu_sq : u ^ 2 = (hζ.unit' ^ m) ^ 2 := by
    simpa [pow_two, hcu] using hm
  have hu_fin : ∃ n : ℕ, ∃ _ : 0 < n, (u : K) ^ n = 1 := by
    refine ⟨2 * p, Nat.mul_pos (by decide) hp.1.pos, ?_⟩
    have hu_sqK :
        (u : K) ^ 2 = (((((hζ.unit' ^ m) ^ 2 : (𝓞 K)ˣ) : (𝓞 K)) : K)) :=
      congrArg (fun x : (𝓞 K)ˣ => (((x : (𝓞 K)) : K))) hu_sq
    calc
      (u : K) ^ (2 * p) = ((u : K) ^ 2) ^ p := by rw [pow_mul]
      _ = (((((hζ.unit' ^ m) ^ 2 : (𝓞 K)ˣ) : (𝓞 K)) : K)) ^ p := by rw [hu_sqK]
      _ = 1 := by
        let ν : (𝓞 K)ˣ := hζ.unit' ^ m
        have hνp : ν ^ p = 1 := by
          dsimp [ν]
          rw [← pow_mul, mul_comm, pow_mul, hζ.unit'_pow, one_pow]
        have hν2p : (ν ^ 2) ^ p = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hνp, one_pow]
        exact congrArg (fun x : (𝓞 K)ˣ => (((x : (𝓞 K)) : K))) hν2p
  have hpo : Odd p := hp.1.odd_of_ne_two hp_odd
  obtain ⟨n, k, hk⟩ := roots_of_unity_in_cyclo (K := K) (hζ := hζ) hpo (u : K) hu_fin
  refine ⟨n, k, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  have hunit_coe : ((((hζ.unit' : (𝓞 K)ˣ) : 𝓞 K) : K)) =
      IsCyclotomicExtension.zeta p ℚ K := by
    change (hζ.toInteger : K) = IsCyclotomicExtension.zeta p ℚ K
    exact hζ.coe_toInteger
  change (u : K) =
    (-1 : K) ^ k * IsCyclotomicExtension.zeta p ℚ K ^ n
  change (u : K) = (-1 : K) ^ k * hζ.toInteger.1 ^ n at hk
  rw [hζ.coe_toInteger] at hk
  exact hk

/-- Complex conjugation sends `ζ^m` to `ζ^{-m}`. -/
theorem conj_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (m : ℕ) :
    complexConj K (hζ.unit' ^ m : (𝓞 K)ˣ) = ((hζ.unit' ^ m)⁻¹ : (𝓞 K)ˣ) := by
  have hzeta_torsion : hζ.unit' ∈ NumberField.Units.torsion K := by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.1.pos, ?_⟩)
    exact hζ.unit'_pow
  simpa using complexConj_torsion K
    ⟨hζ.unit' ^ m, (NumberField.Units.torsion K).pow_mem hzeta_torsion m⟩

include hp_odd in
/-- The ramification index of `zetaPrime` over `zetaPrimePlus` is `2`. -/
theorem ramificationIdx_zetaPrimePlus_eq_two [IsCMField K] :
    (zetaPrime p K).ramificationIdx (𝓞 (NumberField.maximalRealSubfield K)) = 2 := by
  have hmap0 : Ideal.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
      (zetaPrimePlus p K) ≠ ⊥ := by
    rw [zetaPrimePlus_map_eq p hp_odd K]
    exact pow_ne_zero 2 (zetaPrime_ne_bot p K)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (zetaPrimePlus p K) (zetaPrime p K)
    hmap0, zetaPrimePlus_map_eq p hp_odd K, multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (zetaPrime_ne_bot p K) (zetaPrime_isPrime p K))]

include hp_odd in
/-- If `I · 𝒪_K = (a)` with `a ≠ 0`, then `v_(ζ-1)(a)` is even. -/
theorem multiplicity_zetaPrime_even_of_map_eq_span [IsCMField K]
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a : 𝓞 K) (ha : a ≠ 0)
    (hIa :
      I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a}) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K) a) := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  let f : 𝓞 (NumberField.maximalRealSubfield K) →+* 𝓞 K :=
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  let P : Ideal (𝓞 K) := zetaPrime p K
  let PPlus : Ideal (𝓞 (NumberField.maximalRealSubfield K)) := zetaPrimePlus p K
  let π : 𝓞 K := (zeta_spec p ℚ K).toInteger - 1
  have hI0 : I ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.map_bot] at hIa
    exact ha (by simpa [Ideal.span_singleton_eq_bot] using hIa.symm)
  have hmap0 : I.map f ≠ ⊥ := by
    rw [hIa]
    simp [ha]
  have hP0 : P ≠ ⊥ := zetaPrime_ne_bot p K
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact zetaPrime_isPrime p K
  have hPPlus0 : PPlus ≠ ⊥ := by
    intro hbot
    have hmap : Ideal.map f PPlus = P ^ 2 := by
      simpa [f, P, PPlus] using zetaPrimePlus_map_eq p hp_odd K
    rw [hbot, Ideal.map_bot] at hmap
    exact (pow_ne_zero 2 hP0) hmap.symm
  have hPIrr : Irreducible P := (Ideal.prime_of_isPrime hP0 hPprime).irreducible
  have hPPlusIrr : Irreducible PPlus :=
    (Ideal.prime_of_isPrime hPPlus0 inferInstance).irreducible
  have hemul : emultiplicity P (I.map f) = PPlus.ramificationIdx' P * emultiplicity PPlus I := by
    simpa [P, PPlus, f] using
      Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
        (R := 𝓞 (NumberField.maximalRealSubfield K)) (S := 𝓞 K)
        (v := PPlus) (w := P) (I := I) hI0 hPPlusIrr hPIrr hP0
  have hcount_even :
      Even (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I.map f))) := by
    rw [Even]
    refine ⟨Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    have hemul' := hemul
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := PPlus) (q := P) hPPlus0,
      ramificationIdx_zetaPrimePlus_eq_two (p := p) (hp_odd := hp_odd) (K := K),
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPIrr hmap0,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPPlusIrr hI0,
      normalize_eq P, normalize_eq PPlus] at hemul'
    have hemul_nat :
        Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I.map f)) =
          2 * Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I) := by
      exact_mod_cast hemul'
    simpa [two_mul] using hemul_nat
  have hπPrime : Prime π := by simpa [π] using hζ.zeta_sub_one_prime'
  let e := multiplicity π a
  have hπFin : FiniteMultiplicity π a := FiniteMultiplicity.of_prime_left hπPrime ha
  have hπe_dvd : π ^ e ∣ a := (hπFin.pow_dvd_iff_le_multiplicity).2 le_rfl
  have hπe_not_dvd : ¬π ^ (e + 1) ∣ a := by
    rw [hπFin.pow_dvd_iff_le_multiplicity]
    exact Nat.not_succ_le_self e
  have hcount_span :
      Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = e := by
    apply Ideal.count_normalizedFactors_eq (p := P) (x := Ideal.span {a})
    · dsimp [P]
      rw [zetaPrime, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
        Ideal.mem_span_singleton]
      exact hπe_dvd
    · intro hle
      exact hπe_not_dvd <| by
        dsimp [P] at hle
        rw [zetaPrime, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
          Ideal.mem_span_singleton] at hle
        exact hle
  have :
      Even (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}))) := by
    rw [← hIa]
    simpa [f] using hcount_even
  simpa [e, hcount_span] using this

end CyclotomicSetup

end KummerCriterion

end
