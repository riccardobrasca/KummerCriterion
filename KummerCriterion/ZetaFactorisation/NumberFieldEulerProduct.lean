module

public import KummerCriterion.ZetaFactorisation.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.NumberField.ResidueDegree

/-!
# Generic number-field Euler-product infrastructure

This module contains the analytic number-field machinery shared by the global
Euler-product arguments in `KummerCriterion.ZetaFactorisation.EulerProduct`
and `KummerCriterion.HMinus.KplusEulerProduct`.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

namespace KummerCriterion

section NumberFieldEulerProduct

variable (L : Type*) [Field L] [NumberField L]

/-- Regroup the prime-ideal Euler product by the rational prime below each ideal. -/
lemma dedekindZeta_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun q : Nat.Primes ↦ (dedekindLocalFactor L (q : ℕ) s)⁻¹)
      (NumberField.dedekindZeta L s) := by
  classical
  let below : IsDedekindDomain.HeightOneSpectrum (𝓞 L) → Nat.Primes :=
    fun P ↦ ⟨TauCeti.rationalPrimeBelow P, TauCeti.prime_rationalPrimeBelow P⟩
  have hprod := (Equiv.sigmaFiberEquiv below).hasProd_iff.mpr
    (TauCeti.dedekindZeta_eulerProduct_hasProd (K := L) hs)
  refine hprod.sigma fun q ↦ ?_
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hq : rationalPrimeIdeal (q : ℕ) ≠ ⊥ := by
    simpa [rationalPrimeIdeal, Ideal.span_singleton_eq_bot] using q.2.ne_zero
  have : (rationalPrimeIdeal (q : ℕ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime (q : ℕ)
  have hmem (P : Ideal (𝓞 L)) :
      P ∈ primesOverFinset L (q : ℕ) ↔
        P ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 L) :=
    IsDedekindDomain.mem_primesOverFinset_iff hq (𝓞 L)
  let e : {P // below P = q} ≃ ↥(primesOverFinset L (q : ℕ)) :=
    { toFun := fun P ↦ ⟨P.1.asIdeal, (hmem _).mpr ⟨P.1.isPrime, ⟨by
        have hbelow := congr($(P.2).val)
        change TauCeti.rationalPrimeBelow P.1 = (q : ℕ) at hbelow
        rw [TauCeti.under_eq_span_rationalPrimeBelow, hbelow]
        rfl⟩⟩⟩
      invFun := fun P ↦
        let Q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
          ⟨P.1, ((hmem _).mp P.2).1,
            Ideal.ne_bot_of_mem_primesOver hq ((hmem _).mp P.2)⟩
        ⟨Q, Subtype.ext (by
          change TauCeti.rationalPrimeBelow Q = (q : ℕ)
          rw [TauCeti.rationalPrimeBelow_def, ← ((hmem _).mp P.2).2.over]
          simp [rationalPrimeIdeal])⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hfinite := hasProd_fintype (fun P : ↥(primesOverFinset L (q : ℕ)) ↦
    (1 - (Ideal.absNorm P.1 : ℂ) ^ (-s))⁻¹)
  rw [Finset.prod_coe_sort (primesOverFinset L (q : ℕ))
    (fun P ↦ (1 - (Ideal.absNorm P : ℂ) ^ (-s))⁻¹), Finset.prod_inv_distrib] at hfinite
  exact e.hasProd_iff.mpr hfinite

end NumberFieldEulerProduct

end KummerCriterion
