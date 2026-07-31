module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import KummerCriterion.KummerCongruence.Characters
import Mathlib.CategoryTheory.Category.Init

/-!
# Generalized Bernoulli numbers `B_{n, χ}`

Let `N: ℕ` be a positive modulus and `χ: DirichletCharacter R N` a
Dirichlet character valued in a commutative `ℚ`-algebra `R`. The
*generalized Bernoulli numbers* `B_{n, χ} ∈ R` interpolate classical
Bernoulli numbers in the presence of a character twist, and arise as
values of the Dirichlet `L`-function `L(s, χ)` at non-positive integers.

This file defines `BernoulliGen` via the explicit formula

 `B_{n, χ} = N^{n-1} · ∑_{a: ZMod N} χ(a) · B_n(a/N)`

(Diekmann Prop 45, Washington eq. (4.1)).

## Main definitions

- `BernoulliGen χ n` - the generalized Bernoulli number `B_{n, χ}`.

## References

- Diekmann, *FLT for regular primes* (2023), Definition 27 & Prop 45.
- Washington, *Introduction to Cyclotomic Fields*, §4.1.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace KummerCriterion

variable {N : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The generalized Bernoulli number `B_{n, χ}`, defined by the explicit
formula using Bernoulli polynomials over `ℚ` and base change to `R`. -/
noncomputable def BernoulliGen [NeZero N]
    (χ : DirichletCharacter R N) (n : ℕ) : R :=
  (N : R) ^ (n - 1) *
    ∑ a : ZMod N, χ a *
      algebraMap ℚ R ((Polynomial.bernoulli n).eval ((a.val : ℚ) / N))

/-- Intermediate form: for a non-trivial Dirichlet character `χ`,
the `1/2` constant term in `B_1(a/N) = a/N - 1/2` does not contribute
after summing, because `∑ χ(a) = 0`. -/
lemma BernoulliGen_one_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    BernoulliGen χ 1 =
      ∑ a : ZMod N, χ a * algebraMap ℚ R ((a.val : ℚ) / N) := by
  unfold BernoulliGen
  rw [show (1 - 1 : ℕ) = 0 from rfl, pow_zero, one_mul, Polynomial.bernoulli_one]
  simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, map_sub, mul_sub]
  rw [Finset.sum_sub_distrib]
  conv_lhs =>
    rw [show (∑ a : ZMod N, χ a * algebraMap ℚ R (2⁻¹ : ℚ))
          = algebraMap ℚ R (2⁻¹ : ℚ) * ∑ a : ZMod N, χ a from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _]
  rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, sub_zero]

/-- **Diekmann eq. 24/27**, cleared form: `N · B_{1, χ} = ∑_a χ(a) · a`
for non-trivial `χ`. Cleared of denominators so it holds in any commutative
`ℚ`-algebra. -/
lemma natCast_mul_BernoulliGen_one_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    (N : R) * BernoulliGen χ 1 =
      ∑ a : ZMod N, χ a * (a.val : R) := by
  rw [BernoulliGen_one_of_ne_one hχ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hN_R : (N : R) = algebraMap ℚ R (N : ℚ) := by push_cast; rfl
  rw [hN_R, show algebraMap ℚ R ((N : ℚ)) * (χ a * algebraMap ℚ R ((a.val : ℚ) / N)) =
        χ a * (algebraMap ℚ R (N : ℚ) * algebraMap ℚ R ((a.val : ℚ) / N)) from by ring,
    ← map_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  push_cast; rfl

/-- The `ℚ_[p]`-valued Teichmüller character, obtained by post-composing
the `ℤ_[p]`-valued Teichmüller character with the natural embedding
`ℤ_[p] -> ℚ_[p]`. -/
noncomputable def teichmullerCharQp (p : ℕ) [Fact p.Prime] : DirichletCharacter ℚ_[p] p :=
  (teichmullerChar p).ringHomComp PadicInt.Coe.ringHom

variable (p : ℕ) [Fact p.Prime]

lemma teichmullerCharQp_pow_eq_ringHomComp (n : ℕ) :
    (teichmullerCharQp p) ^ n =
      ((teichmullerChar p) ^ n).ringHomComp PadicInt.Coe.ringHom := by
  simpa [teichmullerCharQp] using
    (MulChar.ringHomComp_pow (χ := teichmullerChar p) (f := PadicInt.Coe.ringHom) (n := n))

lemma teichmullerCharQp_pow_sub_one_eq_one :
    (teichmullerCharQp p) ^ (p - 1) = 1 := by
  rw [teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := p - 1)]
  simp [teichmullerChar_pow_sub_one_eq_one (p := p)]

lemma orderOf_teichmullerCharQp :
    orderOf (teichmullerCharQp p) = p - 1 := by
  refine Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (teichmullerCharQp_pow_sub_one_eq_one (p := p))) ?_
  have hpowQ' :
      ((teichmullerChar p) ^ orderOf (teichmullerCharQp p)).ringHomComp
          PadicInt.Coe.ringHom = 1 := by
    rw [← teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := orderOf (teichmullerCharQp p))]
    simp only [pow_orderOf_eq_one]
  have hpowZ : (teichmullerChar p) ^ orderOf (teichmullerCharQp p) = 1 :=
    (MulChar.ringHomComp_eq_one_iff (f := PadicInt.Coe.ringHom)
      (hf := fun _ _ h => Subtype.coe_injective h)).mp hpowQ'
  simpa [orderOf_teichmullerChar (p := p)] using orderOf_dvd_of_pow_eq_one hpowZ

lemma teichmullerCharQp_pow_eq_one_iff (n : ℕ) :
    (teichmullerCharQp p) ^ n = 1 ↔ (p - 1) ∣ n := by
  refine ⟨fun hpow => ?_, ?_⟩
  · simpa [orderOf_teichmullerCharQp (p := p)] using orderOf_dvd_of_pow_eq_one hpow
  · rintro ⟨m, rfl⟩
    rw [← orderOf_teichmullerCharQp (p := p), pow_mul, pow_orderOf_eq_one, one_pow]

lemma teichmullerCharQp_pow_ne_one_of_not_dvd {n : ℕ} (hn : ¬ (p - 1) ∣ n) :
    (teichmullerCharQp p) ^ n ≠ 1 :=
  fun hpow => hn ((teichmullerCharQp_pow_eq_one_iff (p := p) n).mp hpow)

omit [Algebra ℚ R] in
/-- **Diekmann eq. 29**: for an odd prime `p`, the boundary
character `ω^{-1}` contributes the exceptional term `(p - 1) / p`, up
to a `p`-adic integer. We realise `ω^{-1}` as `ω^(p - 2)`. -/
lemma bernoulliGen_teichmuller_inverse_eq_p_sub_one_div_p_add_padicInt
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) :
    ∃ z : ℤ_[p],
      BernoulliGen ((teichmullerCharQp p) ^ (p - 2)) 1 =
        ((p - 1 : ℚ_[p]) / p) + z := by
  have hp : Nat.Prime p := Fact.out
  have hp_gt2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  let ωZ : DirichletCharacter ℤ_[p] p := (teichmullerChar p) ^ (p - 2)
  let ωQ : DirichletCharacter ℚ_[p] p := (teichmullerCharQp p) ^ (p - 2)
  let S : ℤ_[p] := ∑ a : ZMod p, ωZ a * (a.val : ℤ_[p])
  change ∃ z : ℤ_[p], BernoulliGen ωQ 1 = ((p - 1 : ℚ_[p]) / p) + z
  have hp_sub_two_not_dvd : ¬ (p - 1) ∣ p - 2 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hωQ_def : ωQ = ωZ.ringHomComp PadicInt.Coe.ringHom :=
    teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := p - 2)
  have hωQ_ne_one : ωQ ≠ 1 :=
    teichmullerCharQp_pow_ne_one_of_not_dvd (p := p) hp_sub_two_not_dvd
  have hB := natCast_mul_BernoulliGen_one_of_ne_one (R := ℚ_[p]) (N := p) (χ := ωQ) hωQ_ne_one
  have hS_coe : ((S : ℤ_[p]) : ℚ_[p]) = ∑ a : ZMod p, ωQ a * (a.val : ℚ_[p]) := by
    rw [hωQ_def]; dsimp [S]; rw [PadicInt.coe_sum]; rfl
  have hB' : (p : ℚ_[p]) * BernoulliGen ωQ 1 = (S : ℚ_[p]) := by rw [hB, ← hS_coe]
  have hpow_ne_zero : p - 2 ≠ 0 := by omega
  have hterm : ∀ a : ZMod p,
      PadicInt.toZMod (ωZ a * (a.val : ℤ_[p])) = if a = 0 then 0 else 1 := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · dsimp [ωZ]; simp
    · have hω : PadicInt.toZMod (ωZ a) = a ^ (p - 2) := by
        dsimp [ωZ]; rw [MulChar.pow_apply' _ hpow_ne_zero, map_pow, teichmullerChar_apply,
          toZMod_teichmuller]
      have hval : PadicInt.toZMod (a.val : ℤ_[p]) = a := by simp
      rw [map_mul, hω, hval, if_neg ha]
      calc
        a ^ (p - 2) * a = a ^ ((p - 2) + 1) := by rw [mul_comm, pow_succ']
        _ = a ^ (p - 1) := by congr; omega
        _ = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hS_mod : PadicInt.toZMod S = (p - 1 : ZMod p) := by
    have hsplit :
        (∑ a : ZMod p, if a = 0 then 0 else 1) =
          (Finset.univ.erase (0 : ZMod p)).sum (fun _ => (1 : ZMod p)) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0), if_pos rfl, add_zero]
      refine Finset.sum_congr rfl fun a ha => ?_
      simp [(Finset.mem_erase.mp ha).1]
    calc
      PadicInt.toZMod S = ∑ a : ZMod p, if a = 0 then 0 else 1 := by
        dsimp [S]; rw [map_sum]; exact Finset.sum_congr rfl fun a _ => hterm a
      _ = (Finset.univ.erase (0 : ZMod p)).sum (fun _ => (1 : ZMod p)) := hsplit
      _ = (p - 1 : ZMod p) := by
        have hcard : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by simp [ZMod.card p]
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one, Nat.cast_sub hp.one_le]
        simp
  have hS_mem : S - (p - 1 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    have hspec := PadicInt.toZMod_spec (p := p) S
    rw [hS_mod] at hspec
    have hcast : (ZMod.cast ((p : ZMod p) - 1) : ℤ_[p]) = (p - 1 : ℤ_[p]) := by
      have hrepr : ((p : ZMod p) - 1) = ((p - 1 : ℕ) : ZMod p) := by
        rw [Nat.cast_sub hp.one_le]; simp
      have hval0 : ((p : ZMod p) - 1).val = p - 1 := by
        rw [hrepr]; exact ZMod.val_natCast_of_lt (by omega)
      rw [ZMod.cast_eq_val, hval0, Nat.cast_sub hp.one_le, Nat.cast_one]
    rwa [hcast] at hspec
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hS_mem
  rcases hS_mem with ⟨z, hz⟩
  have hzQ_sub : (S : ℚ_[p]) - (p - 1 : ℚ_[p]) = (p : ℚ_[p]) * z := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hz
  have hpQ_ne_zero : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨z, (mul_right_inj' hpQ_ne_zero).mp ?_⟩
  calc
    (p : ℚ_[p]) * BernoulliGen ωQ 1 = (S : ℚ_[p]) := hB'
    _ = (p - 1 : ℚ_[p]) + (p : ℚ_[p]) * z := by
      simpa [add_comm] using sub_eq_iff_eq_add.mp hzQ_sub
    _ = (p : ℚ_[p]) * (((p - 1 : ℚ_[p]) / p) + z) := by
      rw [mul_add, mul_div_cancel₀ _ hpQ_ne_zero]

/-- Bernoulli numbers below the boundary `p - 1` are `p`-adic integers.
This is stated as equality with the image of some `z : ℤ_[p]` in `ℚ_[p]`. -/
theorem bernoulli_mem_padicInt_of_lt_sub_one {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : p ≠ 2) (k : ℕ) (hk : k < p - 1) :
    ∃ z : ℤ_[p], (bernoulli k : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : p.Prime := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  revert hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · exact ⟨1, by simp [_root_.bernoulli_zero]⟩
  have hkp1_lt : k + 1 < p := by omega
  have h_sum := _root_.sum_bernoulli (k + 1)
  rw [if_neg (by omega : k + 1 ≠ 1), Finset.sum_range_succ] at h_sum
  have h_choose_k : (Nat.choose (k + 1) k : ℚ) = (k + 1 : ℚ) := by
    rw [Nat.choose_succ_self_right]; push_cast; rfl
  rw [h_choose_k] at h_sum
  have h_bern_rat : ((k + 1 : ℕ) : ℚ) * _root_.bernoulli k =
      -∑ j ∈ Finset.range k, (Nat.choose (k + 1) j : ℚ) * _root_.bernoulli j := by
    push_cast; linarith [h_sum]
  have hj_wit : ∀ j, j < k -> ∃ z : ℤ_[p], (bernoulli j : ℚ_[p]) = (z : ℚ_[p]) :=
    fun j hj => ih j hj (Nat.lt_of_lt_of_le hj (Nat.le_of_lt hk))
  let z_of : ℕ -> ℤ_[p] := fun j =>
    if h : j < k then (hj_wit j h).choose else 0
  have hz_of : ∀ j, j < k -> (bernoulli j : ℚ_[p]) = ((z_of j : ℤ_[p]) : ℚ_[p]) := by
    intro j hj; simp only [z_of, dif_pos hj]; exact (hj_wit j hj).choose_spec
  let S : ℤ_[p] := ∑ j ∈ Finset.range k, (Nat.choose (k + 1) j : ℤ_[p]) * z_of j
  have hS_coe : (S : ℚ_[p]) =
      ∑ j ∈ Finset.range k, (Nat.choose (k + 1) j : ℚ_[p]) * (bernoulli j : ℚ_[p]) := by
    simp only [S, PadicInt.coe_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [PadicInt.coe_mul, PadicInt.coe_natCast, hz_of j (Finset.mem_range.mp hj)]
  have h_kp1_unit : IsUnit ((k + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkp1_lt)
  refine ⟨-(h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val * S, ?_⟩
  have h_bern_Qp : ((k + 1 : ℕ) : ℚ_[p]) * ((_root_.bernoulli k : ℚ) : ℚ_[p]) =
      -∑ j ∈ Finset.range k,
        (Nat.choose (k + 1) j : ℚ_[p]) * ((_root_.bernoulli j : ℚ) : ℚ_[p]) := by
    have h_cast := congrArg (fun q : ℚ => (q : ℚ_[p])) h_bern_rat
    push_cast at h_cast ⊢
    exact h_cast
  rw [← hS_coe] at h_bern_Qp
  have h_coe_unit : ((h_kp1_unit.unit : ℤ_[p]) : ℚ_[p]) = ((k + 1 : ℕ) : ℚ_[p]) := rfl
  have h_unit_mul_inv : ((h_kp1_unit.unit : ℤ_[p]) : ℚ_[p]) *
      ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
  calc (bernoulli k : ℚ_[p])
      = (1 : ℚ_[p]) * (bernoulli k : ℚ_[p]) := by ring
    _ = (((h_kp1_unit.unit : ℤ_[p]) : ℚ_[p]) *
          ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p])) * (bernoulli k : ℚ_[p]) := by
        rw [h_unit_mul_inv]
    _ = ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p]) *
          (((h_kp1_unit.unit : ℤ_[p]) : ℚ_[p]) * (bernoulli k : ℚ_[p])) := by ring
    _ = ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p]) *
          (((k + 1 : ℕ) : ℚ_[p]) * (bernoulli k : ℚ_[p])) := by rw [h_coe_unit]
    _ = ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p]) * (- (S : ℚ_[p])) := by
        rw [h_bern_Qp]
    _ = ((-(h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val * S : ℤ_[p]) : ℚ_[p]) := by
        rw [PadicInt.coe_mul, PadicInt.coe_neg]; ring

/-- For indices strictly below the boundary `p - 1`, the denominator of the
classical Bernoulli number is prime to `p`.

This is the denominator form of the p-integrality statement used in the proof
of Diekmann Theorem 42: if `n < p - 1`, then `p ∤ (bernoulli n).den`. -/
theorem prime_not_dvd_bernoulli_den_of_lt_sub_one {p n : ℕ} [hp : Fact p.Prime]
    (hp_odd : p ≠ 2) (hn : n < p - 1) :
    ¬ p ∣ (_root_.bernoulli n).den := by
  obtain ⟨z, hz⟩ := bernoulli_mem_padicInt_of_lt_sub_one hp_odd n hn
  have hnorm : ‖((_root_.bernoulli n : ℚ) : ℚ_[p])‖ ≤ 1 := by rw [hz]; exact z.2
  have hunit : IsUnit (((_root_.bernoulli n).den : ℕ) : ℤ_[p]) :=
    PadicInt.isUnit_den _ hnorm
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff] at hunit
  exact hp.out.coprime_iff_not_dvd.mp hunit

lemma bernoulli_factor_mul_den (n : ℕ) (hn : n ≠ 0) :
    ((-(1 / 2 : ℚ)) * (((_root_.bernoulli n : ℚ) / n : ℚ))) *
        (2 * (_root_.bernoulli n).den * n : ℚ) =
      -(_root_.bernoulli n).num := by
  calc
    ((-(1 / 2 : ℚ)) * (((_root_.bernoulli n : ℚ) / n : ℚ))) *
        (2 * (_root_.bernoulli n).den * n : ℚ) =
        -((((_root_.bernoulli n : ℚ) / n : ℚ) * ((_root_.bernoulli n).den * n : ℚ))) := by
          ring
    _ = -((_root_.bernoulli n : ℚ) * ((_root_.bernoulli n).den : ℚ)) := by
      have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      field_simp [hnQ]
    _ = -(_root_.bernoulli n).num := by
      simp

/-- For a Bernoulli factor below the `p - 1` boundary, clear denominators to
realize `(-1/2) * B_n / n` as a `p`-adic integer, and detect when that integer
is a unit by checking whether `p` divides the Bernoulli numerator. -/
lemma exists_padicInt_bernoulli_factor {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < p)
    (hden : ¬ p ∣ (_root_.bernoulli n).den) :
    ∃ a : ℤ_[p],
      (a : ℚ_[p]) =
        (-(1 / 2 : ℚ_[p])) * ((((_root_.bernoulli n : ℚ) / n : ℚ) : ℚ_[p])) ∧
      (IsUnit a ↔ ¬ (p : ℤ) ∣ (_root_.bernoulli n).num) := by
  let D : ℕ := 2 * (_root_.bernoulli n).den * n
  have htwo_not_dvd : ¬ p ∣ 2 :=
    Nat.not_dvd_of_pos_of_lt (by positivity) (by omega)
  have hn_not_dvd : ¬ p ∣ n := Nat.not_dvd_of_pos_of_lt hn_pos hn_lt
  have hD_coprime : p.Coprime D := by
    simpa [D, Nat.mul_assoc] using
      (hp.out.coprime_iff_not_dvd.mpr htwo_not_dvd).mul_right <|
        (hp.out.coprime_iff_not_dvd.mpr hden).mul_right <|
        (hp.out.coprime_iff_not_dvd.mpr hn_not_dvd)
  have hD_unit : IsUnit ((D : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simpa [Nat.coprime_comm] using hD_coprime
  let a : ℤ_[p] := -((hD_unit.unit⁻¹ : (ℤ_[p])ˣ).val) * (_root_.bernoulli n).num
  refine ⟨a, ?_, ?_⟩
  · have hD_ne : (D : ℚ_[p]) ≠ 0 := by
      exact_mod_cast (show D ≠ 0 by dsimp [D]; positivity)
    apply (mul_left_inj' hD_ne).mp
    have hunit_mul : ((((hD_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p])) * (D : ℚ_[p])) = 1 := by
      change ((((hD_unit.unit⁻¹ : (ℤ_[p])ˣ) * hD_unit.unit).val : ℚ_[p])) = 1
      simp
    have hfactor_mul :
        ((-(1 / 2 : ℚ_[p])) * ((((_root_.bernoulli n : ℚ) / n : ℚ) : ℚ_[p]))) *
            (D : ℚ_[p]) =
          -((_root_.bernoulli n).num : ℚ_[p]) := by
      simpa [D] using
        congrArg (fun q : ℚ => (q : ℚ_[p]))
          (bernoulli_factor_mul_den (n := n) hn_pos.ne')
    have ha_mul : (((a : ℤ_[p]) : ℚ_[p])) * (D : ℚ_[p]) =
        -((_root_.bernoulli n).num : ℚ_[p]) := by
      have : (((a : ℤ_[p]) : ℚ_[p])) * (D : ℚ_[p])
          = -((_root_.bernoulli n).num : ℚ_[p]) *
            (((((hD_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p])) * (D : ℚ_[p]))) := by
        simp [a, mul_left_comm, mul_comm]
      rw [this, hunit_mul, mul_one]
    exact ha_mul.trans hfactor_mul.symm
  · have hcoef_unit : IsUnit (-((hD_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p])) :=
      (hD_unit.unit⁻¹).isUnit.neg
    have ha_unit : IsUnit a ↔ IsUnit (((_root_.bernoulli n).num : ℤ_[p])) := by
      rw [show a = -((hD_unit.unit⁻¹ : (ℤ_[p])ˣ).val) * ((_root_.bernoulli n).num : ℤ_[p])
        by rfl, IsUnit.mul_iff]
      simp [hcoef_unit]
    rw [ha_unit, ← not_iff_not, PadicInt.not_isUnit_iff, PadicInt.norm_intCast_lt_one_iff]
    simp

end KummerCriterion
