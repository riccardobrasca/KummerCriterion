module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import KummerCriterion.LValueAtOne.ComplexBounds
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Basic
import Mathlib.Analysis.Complex.AbelLimit

/-!
# Cosine boundary values for `LValueAtOne`

This file contains the cosine-side Dirichlet bounds and the boundary-value
formula used in the even `L(1, χ)` evaluation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace KummerCriterion

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- Partial sums of the cosine kernel stay uniformly bounded away from the endpoints. -/
lemma norm_sum_range_cos_le {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)‖ ≤
      2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  let z : ℂ := Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz_ne_one : z ≠ 1 := by simpa [z] using exp_two_pi_mul_I_ne_one hx₀ hx₁
  have hre :
      ((∑ i ∈ Finset.range n, z ^ i).re : ℝ) =
        ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show z ^ i = Complex.exp (((2 * Real.pi * x * i : ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring, Complex.exp_ofReal_mul_I_re]
  have hz_norm : ‖z‖ = 1 := by
    simpa [z] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have hgeom : ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ :=
    norm_geom_sum_le_two_div_norm_sub_one hz_norm hz_ne_one n
  calc
    ‖∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)‖
      = ‖((∑ i ∈ Finset.range n, z ^ i).re : ℝ)‖ := by rw [hre]
    _ ≤ ‖∑ i ∈ Finset.range n, z ^ i‖ := by
      simpa using (RCLike.norm_re_le_norm (∑ i ∈ Finset.range n, z ^ i))
    _ ≤ 2 / ‖z - 1‖ := hgeom
    _ = 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
      simp [z, norm_sub_rev]

/-- The endpoint cosine series converges on `(0, 1)` by Dirichlet's test. -/
lemma exists_tendsto_sum_range_cos_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∃ l : ℝ,
      Tendsto
        (fun n ↦
          ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i)
        atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n => if n = 0 then 1 else 1 / n
  let z : ℕ → ℝ := fun n => if n = 0 then 0 else Real.cos (2 * Real.pi * x * n)
  have hf : Antitone f := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [f]
      · simp [f, hb.ne']
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast Nat.succ_le_of_lt hb
        simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hb1
    · have hb : 0 < b := lt_of_lt_of_le ha hab
      simp [f, ha.ne', (Nat.ne_of_gt hb)]
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      simpa [one_div] using one_div_le_one_div_of_le ha' hab'
  have hf0 : Tendsto f atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa [f]
      using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0))
  have hbound :
      ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤
        4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · have : 0 ≤ 4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
        positivity
      simpa [z] using this
    · let g : ℕ → ℝ := fun i => Real.cos (2 * Real.pi * x * i)
      have hz0 := Finset.sum_range_add z 1 (n - 1)
      have hg0 := Finset.sum_range_add g 1 (n - 1)
      have hsum :
          ∑ i ∈ Finset.range n, z i =
            ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) - 1 := by
        have hn' : 1 + (n - 1) = n := by
          simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hn
        have hz0' :
            ∑ x ∈ Finset.range n, z x =
              ∑ x ∈ Finset.range 1, z x + ∑ x ∈ Finset.range (n - 1), z (1 + x) := by
          simpa [hn', add_comm] using hz0
        have hg0' :
            ∑ x ∈ Finset.range n, g x =
              ∑ x ∈ Finset.range 1, g x + ∑ x ∈ Finset.range (n - 1), g (1 + x) := by
          simpa [hn', add_comm] using hg0
        rw [Finset.sum_range_one] at hz0' hg0'
        calc
          ∑ i ∈ Finset.range n, z i = z 0 + ∑ i ∈ Finset.range (n - 1), z (1 + i) := by
            simpa [add_comm, add_left_comm, add_assoc, Nat.add_comm] using hz0'
          _ = ∑ i ∈ Finset.range (n - 1), g (1 + i) := by simp [z, g]
          _ = ∑ i ∈ Finset.range n, g i - g 0 :=
                eq_sub_iff_add_eq.mpr (by
                  simpa [add_comm, add_left_comm, add_assoc, Nat.add_comm] using hg0'.symm)
          _ = ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) - 1 := by simp [g]
      rw [hsum]
      calc
        |∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) - 1|
            ≤ |∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) - 0| +
                |0 - (1 : ℝ)| := by
                simpa using
                  abs_sub_le
                    (∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)) 0 1
        _ ≤ |∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)| + 1 := by simp
        _ ≤ (2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) + 1 := by
              have hcos :
                  |∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)| ≤
                    2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
                simpa using norm_sum_range_cos_le hx₀ hx₁ n
              exact add_le_add hcos le_rfl
        _ ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ +
              2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
              have hdenom :
                  1 ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                one_le_two_div_norm_one_sub_exp_two_pi_mul_I hx₀ hx₁
              linarith
        _ = 4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by ring
  have hcauchy := hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l, ?_⟩
  have hseries :
      (fun n ↦ ∑ i ∈ Finset.range n, f i • z i) =
        fun n ↦
          ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i := by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f, z]
    · simp [f, z, hi.ne', smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact hseries ▸ hl

/-- The endpoint cosine series converges to the classical boundary value
`-log (2 * sin (πx))` on `(0, 1)`. -/
lemma tendsto_sum_range_cos_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i)
      atTop (𝓝 (-Real.log (2 * Real.sin (Real.pi * x)))) := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_range_cos_div_nat hx₀ hx₁
  let coeff : ℕ → ℝ := fun n =>
    if n = 0 then 0 else Real.cos (2 * Real.pi * x * n) / n
  have habel :
      Tendsto (fun r : ℝ => ∑' n, coeff n * r ^ n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff :
      Set.EqOn
        (fun r : ℝ => ∑' n, coeff n * r ^ n)
        (fun r : ℝ =>
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (Set.Ioo 0 1) := by
    intro r hr
    have hr₀ : 0 ≤ r := hr.1.le
    have hr₁ : r < 1 := hr.2
    calc
      ∑' n : ℕ, coeff n * r ^ n
          = ∑' n : ℕ, (r ^ n / n) * Real.cos (2 * Real.pi * x * n) := by
              refine tsum_congr fun n : ℕ => ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff, hn.ne', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
            (hasSum_mul_rpow_cos x r hr₀ hr₁).tsum_eq
  have habel' :
      Tendsto
        (fun r : ℝ =>
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hzero :
      (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0 :=
    sub_ne_zero.mpr (exp_two_pi_mul_I_ne_one hx₀ hx₁).symm
  have hcont :
      Tendsto
        (fun r : ℝ =>
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (𝓝[<] 1)
        (𝓝 (-Real.log ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) := by
    have hinner :
        ContinuousAt
          (fun r : ℝ => (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)) 1 :=
      continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have hnorm :
        ContinuousAt
          (fun r : ℝ =>
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) 1 :=
      continuous_norm.continuousAt.comp hinner
    have hnorm_ne :
        ‖(1 : ℂ) - ((1 : ℝ) : ℂ) *
            Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hzero)
    have hlog :
        ContinuousAt
          (fun r : ℝ =>
            Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) 1 :=
      hnorm.log hnorm_ne
    convert! tendsto_nhdsWithin_of_tendsto_nhds hlog.neg.tendsto using 2
    simp
  have ht₀ : 0 < 2 * Real.pi * x := by nlinarith [hx₀, Real.pi_pos]
  have ht₂π : 2 * Real.pi * x < 2 * Real.pi := by nlinarith [hx₁, Real.pi_pos]
  have hnorm_value :
      ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ =
        2 * Real.sin (Real.pi * x) := by
    simpa [show (2 * Real.pi * x) / 2 = Real.pi * x by ring] using
      norm_one_sub_exp_ofReal_mul_I ht₀ ht₂π
  have hl_eq : l = -Real.log (2 * Real.sin (Real.pi * x)) :=
    tendsto_nhds_unique habel' (by simpa [hnorm_value] using hcont)
  simpa [hl_eq] using hl

/-- The cosine zeta function takes the classical boundary value at `s = 1` for `x ∈ (0, 1)`. -/
theorem cosZeta_one_eq_boundary {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    HurwitzZeta.cosZeta x 1 = (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)) := by
  refine TauCeti.LSeries.eq_of_tendsto_sum_Icc_div
    (a := fun n ↦ (Real.cos (2 * Real.pi * x * n) : ℂ)) ?_ ?_ ?_
  · have hlim := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_sum_range_cos_div_nat hx₀ hx₁).ofReal
    convert hlim using 1
    · funext N
      rw [← Finset.Ico_succ_right_eq_Icc, Nat.succ_eq_succ,
        Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ (Nat.zero_le N))]
      simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, sub_zero, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs with h <;> simp [h]
  · have hxadd : (x : UnitAddCircle) ≠ 0 := by
      intro hxzero
      rw [AddCircle.coe_eq_zero_iff] at hxzero
      obtain ⟨n, hn⟩ := hxzero
      have hn' : (n : ℝ) = x := by simpa using hn
      have hn_pos : (0 : ℝ) < n := by linarith
      have hn_lt_one : (n : ℝ) < 1 := by linarith
      have : 0 < n := by exact_mod_cast hn_pos
      have : n < 1 := by exact_mod_cast hn_lt_one
      omega
    exact ((HurwitzZeta.differentiableAt_cosZeta (a := (x : UnitAddCircle))
      (s := (1 : ℂ)) (Or.inr hxadd)).continuousAt.tendsto.comp
      Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  · intro σ hσ
    exact HurwitzZeta.LSeriesHasSum_cos x (by simpa using hσ)

/-- For a nonzero residue class, `cosZeta` at the corresponding point of `UnitAddCircle`
takes the classical boundary value used on the even side of the `L(1, χ)` formula. -/
theorem cosZeta_toAddCircle_one_eq_boundary {a : ZMod p} (ha : a ≠ 0) :
    HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
      (((-Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ)) := by
  have hx := zmod_val_div_prime_mem_Ioo (p := p) ha
  rw [ZMod.toAddCircle_apply]
  exact cosZeta_one_eq_boundary (x := (a.val / p : ℝ)) hx.1 hx.2

/-- The norm of `1 - ζ_p^a` matches the trigonometric boundary term. -/
lemma norm_one_sub_stdAddChar {a : ZMod p} (ha : a ≠ 0) :
    ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ =
      2 * Real.sin (Real.pi * (a.val / p : ℝ)) := by
  have hx := zmod_val_div_prime_mem_Ioo (p := p) ha
  have ht₀ : 0 < 2 * Real.pi * (a.val / p : ℝ) := by
    nlinarith [hx.1, Real.pi_pos]
  have ht₂π : 2 * Real.pi * (a.val / p : ℝ) < 2 * Real.pi := by
    nlinarith [hx.2, Real.pi_pos]
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hexp :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) / (p : ℂ)) =
        Complex.exp ((((2 * Real.pi * (a.val / p : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  convert norm_one_sub_exp_ofReal_mul_I ht₀ ht₂π using 1
  ring_nf

end LValueAtOne

end KummerCriterion
