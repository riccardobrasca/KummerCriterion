module

public import KummerCriterion.HMinus.KplusPrimeArithmetic
public import KummerCriterion.ZetaFactorisation.NumberFieldEulerProduct
import KummerCriterion.ZetaFactorisation.EulerProduct

/-!
# `K⁺` Euler product and residue bridge

Euler-product comparison between the zeta function of `K⁺` and even Dirichlet
`L`-products.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators Topology nonZeroDivisors

namespace KummerCriterion

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The Euler product of the even nontrivial character `L`-values. -/
lemma evenLProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun q : Nat.Primes ↦ (evenCharLocalFactor p (q : ℕ) s)⁻¹)
      (evenLProduct p s) := by
  classical
  simpa only [evenLProduct, evenCharLocalFactor, Finset.prod_inv_distrib,
    DirichletCharacter.LFunction_eq_LSeries _ hs] using
    (hasProd_prod (s := evenNontrivialCharacters p) fun χ _ ↦
      DirichletCharacter.LSeries_eulerProduct_hasProd χ hs)

lemma evenCharLocalFactor_at_p {s : ℂ} :
    evenCharLocalFactor (p := p) p s = 1 := by
  classical
  exact Finset.prod_eq_one fun χ _ => by
    rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, sub_zero]

lemma localFactorsPlus_agree_prime_ne_p (hp_odd : p ≠ 2)
    {q : Nat.Primes} (hq : (q : ℕ) ≠ p) {s : ℂ} :
    dedekindLocalFactor K⁺ (q : ℕ) s =
      (1 - ((q : ℕ) : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) (q : ℕ) s := by
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  rw [dedekindLocalFactor_eq_pow_localResidueDegreePlus (p := p) (K := K) hp_odd hq]
  symm
  simpa [neg_mul] using
    (trivial_mul_evenCharLocalFactor_eq_pow_localResidueDegreePlus
      (p := p) hp_odd hq (s := s))

lemma localFactorsPlus_agree_at_p (hp_odd : p ≠ 2) {s : ℂ} :
    dedekindLocalFactor K⁺ p s =
      (1 - (p : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) p s := by
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  rw [evenCharLocalFactor_at_p (p := p), mul_one, dedekindLocalFactorPlus_at_p (p := p) (K := K)]

lemma localFactorsPlus_agree (hp_odd : p ≠ 2) {q : Nat.Primes} {s : ℂ} :
    dedekindLocalFactor K⁺ (q : ℕ) s =
      (1 - ((q : ℕ) : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) (q : ℕ) s := by
  by_cases hq : (q : ℕ) = p
  · have hq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq
    subst hq'
    exact localFactorsPlus_agree_at_p (p := p) (K := K) hp_odd
  · exact localFactorsPlus_agree_prime_ne_p (p := p) (K := K) hp_odd hq

theorem dedekindZeta_eq_riemannZeta_mul_evenLProduct_of_one_lt_re
    (hp_odd : p ≠ 2) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K⁺ s = riemannZeta s * evenLProduct p s := by
  refine (dedekindZeta_hasProd K⁺ hs).unique ?_
  convert (riemannZeta_eulerProduct_hasProd hs).mul (evenLProduct_hasProd p hs) using 1
  ext q
  rw [localFactorsPlus_agree (p := p) (K := K) hp_odd, mul_inv_rev, mul_comm]

theorem tendsto_sub_one_mul_riemannZeta_mul_evenLProduct :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * (riemannZeta (s : ℂ) * evenLProduct p (s : ℂ)))
      (𝓝[>] 1)
      (𝓝 (evenLProduct p (1 : ℂ))) := by
  classical
  have h_cont : Continuous (evenLProduct p) :=
    continuous_finsetProd _ fun χ hχ =>
      (DirichletCharacter.differentiable_LFunction (Finset.mem_filter.mp hχ).2.2).continuous
  have h_embed :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin] with s hs h
          exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta : Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod : Filter.Tendsto (fun s : ℝ => evenLProduct p (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (evenLProduct p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod := h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring

theorem tendsto_sub_one_mul_dedekindZetaPlus_via_evenLProducts (hp_odd : p ≠ 2) :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * NumberField.dedekindZeta K⁺ (s : ℂ))
      (𝓝[>] 1)
      (𝓝 (evenLProduct p (1 : ℂ))) := by
  refine (Filter.tendsto_congr' ?_).mp
    (tendsto_sub_one_mul_riemannZeta_mul_evenLProduct (p := p))
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [dedekindZeta_eq_riemannZeta_mul_evenLProduct_of_one_lt_re
    (p := p) (K := K) hp_odd (by exact_mod_cast hs)]

theorem complex_maximalRealSubfield_residue_eq_evenLProduct_one (hp_odd : p ≠ 2) :
    ((NumberField.dedekindZeta_residue K⁺ : ℝ) : ℂ) = evenLProduct p (1 : ℂ) :=
  tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K⁺)
    (tendsto_sub_one_mul_dedekindZetaPlus_via_evenLProducts (p := p) (K := K) hp_odd)
end KummerCriterion
