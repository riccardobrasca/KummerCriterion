module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import KummerCriterion.LValueAtOne.ComplexBounds
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Basic
import Mathlib.Analysis.Complex.AbelLimit

/-!
# Sine boundary values for `LValueAtOne`

This file contains the sine-side Dirichlet bounds and the boundary-value
formula used in the odd `L(1, χ)` evaluation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace KummerCriterion

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- Partial sums of the sine kernel stay uniformly bounded away from the endpoints. -/
lemma norm_sum_range_sin_le {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i)‖ ≤
      2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  let z : ℂ := Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz_ne_one : z ≠ 1 := by simpa [z] using exp_two_pi_mul_I_ne_one hx₀ hx₁
  have him :
      ((∑ i ∈ Finset.range n, z ^ i).im : ℝ) =
        ∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show z ^ i = Complex.exp (((2 * Real.pi * x * i : ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring, Complex.exp_ofReal_mul_I_im]
  have hz_norm : ‖z‖ = 1 := by
    simpa [z] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have hgeom : ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ :=
    norm_geom_sum_le_two_div_norm_sub_one hz_norm hz_ne_one n
  calc
    ‖∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i)‖
      = ‖((∑ i ∈ Finset.range n, z ^ i).im : ℝ)‖ := by rw [him]
    _ ≤ ‖∑ i ∈ Finset.range n, z ^ i‖ := by
      simpa using (RCLike.norm_im_le_norm (∑ i ∈ Finset.range n, z ^ i))
    _ ≤ 2 / ‖z - 1‖ := hgeom
    _ = 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
      simp [z, norm_sub_rev]

/-- The endpoint sine series converges on `(0, 1)` by Dirichlet's test. -/
lemma exists_tendsto_sum_range_sin_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∃ l : ℝ,
      Tendsto
        (fun n ↦
          ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i)
        atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n => if n = 0 then 1 else 1 / n
  let z : ℕ → ℝ := fun n => if n = 0 then 0 else Real.sin (2 * Real.pi * x * n)
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
  have hpartial :
      ∀ n, ∑ i ∈ Finset.range n, z i =
        ∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i) := by
    intro n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [z]
    · simp [z, hi.ne']
  have hbound :
      ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤
        2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro n
    rw [hpartial]
    exact norm_sum_range_sin_le hx₀ hx₁ n
  have hcauchy := hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l, ?_⟩
  have hseries :
      (fun n ↦ ∑ i ∈ Finset.range n, f i • z i) =
        fun n ↦
          ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i := by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f, z]
    · simp [f, z, hi.ne', smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact hseries ▸ hl

/-- The endpoint sine series converges to the classical boundary value
`π * (1 / 2 - x)` on `(0, 1)`. -/
lemma tendsto_sum_range_sin_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i)
      atTop (𝓝 (Real.pi * (1 / 2 - x))) := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_range_sin_div_nat hx₀ hx₁
  let coeff : ℕ → ℝ := fun n =>
    if n = 0 then 0 else Real.sin (2 * Real.pi * x * n) / n
  have habel :
      Tendsto (fun r : ℝ => ∑' n, coeff n * r ^ n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff :
      Set.EqOn
        (fun r : ℝ => ∑' n, coeff n * r ^ n)
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (Set.Ioo 0 1) := by
    intro r hr
    have hr₀ : 0 ≤ r := hr.1.le
    have hr₁ : r < 1 := hr.2
    calc
      ∑' n : ℕ, coeff n * r ^ n
          = ∑' n : ℕ, (r ^ n / n) * Real.sin (2 * Real.pi * x * n) := by
              refine tsum_congr fun n : ℕ => ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff, hn.ne', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im :=
            (hasSum_mul_rpow_sin x r hr₀ hr₁).tsum_eq
  have habel' :
      Tendsto
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hslit :
      ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have hre :
        (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)).re : ℝ) =
          2 * Real.sin (Real.pi * x) ^ 2 := by
      have hExp :
          (Complex.exp ((2 * Real.pi * x) * Complex.I)).re = Real.cos (2 * Real.pi * x) := by
        simpa using (Complex.exp_ofReal_mul_I_re (2 * Real.pi * x))
      rw [Complex.sub_re, Complex.one_re, hExp]
      have hsq : 1 - Real.cos (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) ^ 2 := by
        rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
      exact hsq
    rw [hre]
    have hxπ : Real.pi * x ∈ Set.Ioo 0 Real.pi := by
      constructor <;> nlinarith [hx₀, hx₁, Real.pi_pos]
    have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_mem_Ioo hxπ
    positivity
  have hcont :
      Tendsto
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 (Real.pi * (1 / 2 - x))) := by
    have hz :
        Tendsto
          (fun r : ℝ => (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))
          (𝓝[<] 1)
          (𝓝 ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I))) := by
      have hcont :
          Continuous fun r : ℝ =>
            (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I) := by
        continuity
      have hcont1 :
          ContinuousAt
            (fun r : ℝ =>
              (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)) 1 :=
        hcont.continuousAt
      convert tendsto_nhdsWithin_of_tendsto_nhds hcont1.tendsto using 1
      · simp
    have hlog :
        Tendsto
          (fun r : ℝ =>
            Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)))
          (𝓝[<] 1)
          (𝓝 (Complex.log ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))) :=
      hz.clog hslit
    have him0 :
        Tendsto
          (fun r : ℝ =>
            (Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
          (𝓝[<] 1)
          (𝓝 ((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im)) :=
      Complex.continuous_im.continuousAt.tendsto.comp hlog
    have hnegim :
        Tendsto
          (fun r : ℝ =>
            -((Complex.log
              ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im))
          (𝓝[<] 1)
          (𝓝 (-((Complex.log
            (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im))) :=
      him0.neg
    have ht₀ : 0 < 2 * Real.pi * x := by nlinarith [hx₀, Real.pi_pos]
    have ht₂π : 2 * Real.pi * x < 2 * Real.pi := by nlinarith [hx₁, Real.pi_pos]
    have hvalue := neg_log_one_sub_exp_ofReal_mul_I_im ht₀ ht₂π
    have hvalue' :
        -((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im) =
          Real.pi * (1 / 2 - x) := by
      calc
        -((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im) =
            Real.pi / 2 - (2 * Real.pi * x) / 2 := by
              simpa using hvalue
        _ = Real.pi * (1 / 2 - x) := by ring
    simpa [hvalue'] using hnegim
  have hl_eq : l = Real.pi * (1 / 2 - x) := tendsto_nhds_unique habel' hcont
  simpa [hl_eq] using hl

/-- The sine zeta function takes the classical boundary value at `s = 1` for `x ∈ (0, 1)`. -/
theorem sinZeta_one_eq_boundary {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    HurwitzZeta.sinZeta x 1 = (Real.pi * (1 / 2 - x) : ℂ) := by
  refine TauCeti.LSeries.eq_of_tendsto_sum_Icc_div
    (a := fun n ↦ (Real.sin (2 * Real.pi * x * n) : ℂ)) ?_ ?_ ?_
  · have hlim := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_sum_range_sin_div_nat hx₀ hx₁).ofReal
    convert hlim using 1
    · funext N
      rw [← Finset.Ico_succ_right_eq_Icc, Nat.succ_eq_succ,
        Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ (Nat.zero_le N))]
      simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, sub_zero, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs with h <;> simp [h]
    · push_cast
      rfl
  · exact (((HurwitzZeta.differentiableAt_sinZeta x) (1 : ℂ)).continuousAt.tendsto.comp
      Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  · intro σ hσ
    exact HurwitzZeta.LSeriesHasSum_sin x (by simpa using hσ)

/-- For a nonzero residue class, `sinZeta` at the corresponding point of `UnitAddCircle`
takes the classical boundary value used on the odd side of the `L(1, χ)` formula. -/
theorem sinZeta_toAddCircle_one_eq_boundary {a : ZMod p} (ha : a ≠ 0) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =
      (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ))) := by
  rw [sinZeta_toAddCircle_eq_val_div_prime]
  have hx : (a.val / p : ℝ) ∈ Set.Ioo 0 1 := zmod_val_div_prime_mem_Ioo (p := p) ha
  calc
    HurwitzZeta.sinZeta (a.val / p : ℝ) 1 =
        (Real.pi * (1 / 2 - (a.val / p : ℝ)) : ℂ) :=
          sinZeta_one_eq_boundary (x := (a.val / p : ℝ)) hx.1 hx.2
    _ = (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ))) := by
          have hcast : (((a.val / p : ℝ) : ℂ)) = (a.val : ℂ) / (p : ℂ) := by
            push_cast
            rfl
          simpa using congrArg
            (fun z : ℂ => (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - z))) hcast

end LValueAtOne

end KummerCriterion
