module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceBinomial
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MinimalWeight
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MultinomialMod
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceMultinomial
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitVectors
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Stickelberger leading-term identification (REF-18c2c4-L2c3)

Combines the trace-form binomial truncation (L2c2) with the multinomial
expansion of `(traceSum y)^n` and the Layer-1 minimal-weight / digit-
factorial machinery to prove the **digit-sum Stickelberger congruence**
for the reciprocal-convention integral Gauss sum: for `1 ≤ a ≤ p - 1`,

  `g(χ_q^{-a}, ψ) ∈ Q^{s_ℓ(a · d)} ∧ g(χ_q^{-a}, ψ) ∉ Q^{s_ℓ(a · d) + 1}`,

where `d = (#k - 1) / p` and `s_ℓ` is the base-`ℓ` digit sum.
The setup stores the ordinary character `χ_q(x) ≡ x^d (mod Q)`, so the
reciprocal convention is represented by the wrapper
`gaussSumIntRec a = gaussSumInt (p - a)` in the Stickelberger range.

## Strategy

The proof routes through L2c2's `gaussSumInt_qadic_ord_at_prime_of_traceLead`,
which reduces the goal to providing a candidate leading term `lead` with:
1. `lead ∈ Q^s` (containment).
2. `lead ∉ Q^{s+1}` (non-degeneracy).
3. `traceBinomialApprox a s - lead ∈ Q^{s+1}` (the Gauss sum is congruent
   to `lead` modulo `Q^{s+1}`).

We construct `lead = stickelbergerLead a := unit_a · π^s` where `unit_a`
is a unit in `𝓞 R'/Q` lifted from the digit-factorial reciprocal
`(s_ℓ(a · d))! / ∏ aᵢ!` (with `(a₀, …, a_{f-1})` the standard digits).

The third clause is the heaviest: it requires expanding the residual
character sums

  `T_n(a) := ∑_x (S.residueCharInt ^ a) x · C((Tr(c·x)).val, n)`

via the multinomial expansion of `(traceSum (c·x))^n` (Layer 1) plus
character orthogonality (`FiniteField.sum_pow_units`), and identifying
the unique surviving multi-index at minimum weight `s_ℓ(a · d)` via
`digitSum_decomp_unique_at_minimum`.

## Status

This file contains the main theorem statement and a structured
decomposition into sub-lemmas. The containment and non-degeneracy halves
are still the substantive L2c3 gaps.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- The cofactor `d = (#k - 1) / p`. -/
def stickD (_S : TraceFormStickelbergerSetup ℓ p k K R') : ℕ :=
  (Fintype.card k - 1) / p

/-- The predicted `Q`-adic order of `g(χ_q^a, ψ)`: `s_ℓ(a · d)`. -/
def stickOrd (S : TraceFormStickelbergerSetup ℓ p k K R') (a : ℕ) : ℕ :=
  digitSum ℓ (a * S.stickD)

/-- The predicted ordinary-character order. Since the setup's stored
character satisfies `χ(x) ≡ x^d mod Q`, ordinary `χ^a` corresponds to the
complementary reciprocal index `p-a`. -/
def stickOrdOrd (S : TraceFormStickelbergerSetup ℓ p k K R') (a : ℕ) : ℕ :=
  S.stickOrd (p - a)


section CharacterOrthogonality

variable [DecidableEq k]





omit [DecidableEq k] in
/-- The cofactor really satisfies `p * d = #k - 1`. -/
theorem p_mul_stickD_eq_card_sub_one
    (S : TraceFormStickelbergerSetup ℓ p k K R') :
    p * S.stickD = Fintype.card k - 1 := by
  rw [stickD, mul_comm]
  exact Nat.div_mul_cancel S.hdiv



end CharacterOrthogonality





/-! ### The substantive Stickelberger content

The remaining work is the digit-sum `Q`-adic order claim for the
reciprocal-convention integral Gauss sum:

  `v_Q(gaussSumIntRec a) = s_ℓ(a · d)`,

equivalently `gaussSumIntRec a ∈ Q^s ∧ gaussSumIntRec a ∉ Q^{s+1}`.
For the ordinary stored character, the exported index is the complementary
one, `s_ℓ((p-a) · d)`.

The classical proof routes through the digit-coefficient expansion of
`(traceSum (c·x))^n` and identifies the leading multi-index via:
1. Multinomial expansion (`traceSum_pow_eq_sum_multinomial'`).
2. Character orthogonality (`FiniteField.sum_pow_units`).
3. Minimum-weight uniqueness (L1c, `digitSum_decomp_unique_at_minimum`).
4. Digit-factorial unit (L1d, `standardDigit_factorial_prod_not_dvd`). -/

/-- The selected prime `Q` is non-zero. Follows from `S.hQ : (ℓ : 𝓞 R') ∈ S.Q`
combined with `(ℓ : 𝓞 R') ≠ 0` (since `𝓞 R'` has characteristic zero). -/
theorem Q_ne_bot (S : TraceFormStickelbergerSetup ℓ p k K R') : S.Q ≠ ⊥ := by
  intro h
  have h_ell_in : (ℓ : 𝓞 R') ∈ S.Q := S.hQ
  rw [h, Ideal.mem_bot] at h_ell_in
  have hℓ_ne : (ℓ : 𝓞 R') ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero
  exact hℓ_ne h_ell_in

/-- Structural Dedekind-domain fact: if `π ∈ Q`, `π ∉ Q^2`, and `π ≠ 0`,
then `π^s ∉ Q^(s+1)` for any `s`.

Proof via the `normalizedFactors` API: from `π ∉ Q^2` we get
`count Q (factors (π)) = 1`; multiplicativity gives
`count Q (factors (π^s)) = s`; and `(π^s) ⊆ Q^(s+1)` would force
`count Q (factors (π^s)) ≥ s+1`, contradiction. -/
theorem pi_pow_not_mem_Q_pow_succ_of_not_mem_sq
    (S : TraceFormStickelbergerSetup ℓ p k K R')
    (h_pi_ne_zero : S.π ≠ 0) (h_pi_nondeg : S.π ∉ S.Q ^ 2) (s : ℕ) :
    S.π ^ s ∉ S.Q ^ (s + 1) := by
  classical
  intro h_in
  -- Translate the membership claim to span containment, with `(π^s) = (π)^s`.
  set I : Ideal (𝓞 R') := Ideal.span ({S.π} : Set (𝓞 R')) with hI_def
  have h_span_pi_pow : Ideal.span ({S.π ^ s} : Set (𝓞 R')) = I ^ s := by
    rw [hI_def, Ideal.span_singleton_pow]
  have h_pow_le : I ^ s ≤ S.Q ^ (s + 1) := by
    rw [← h_span_pi_pow]
    exact (Ideal.span_singleton_le_iff_mem _).mpr h_in
  have hI_ne_bot : I ≠ ⊥ := by
    rw [hI_def, Ne, Ideal.span_singleton_eq_bot]
    exact h_pi_ne_zero
  have hI_pow_ne_bot : I ^ s ≠ ⊥ := pow_ne_zero s hI_ne_bot
  have hI_le_Q : I ≤ S.Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr S.π_mem_Q
  have hI_not_le_Qsq : ¬ I ≤ S.Q ^ 2 := fun h =>
    h_pi_nondeg <| h <| Ideal.mem_span_singleton_self S.π
  -- Count of Q in normalizedFactors I.
  have h_count_I : Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors I) = 1 := by
    have h_le_one : I ≤ S.Q ^ 1 := by simpa using hI_le_Q
    exact Ideal.count_normalizedFactors_eq h_le_one hI_not_le_Qsq
  -- Count of Q in normalizedFactors (I^s) = s.
  have h_count_Is : Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors (I ^ s)) = s := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul, h_count_I, mul_one]
  -- Count of Q in normalizedFactors (Q^(s+1)) ≥ s+1.
  have hQ_irr : Irreducible S.Q := by
    have hQp : Prime S.Q := Ideal.prime_of_isPrime S.Q_ne_bot S.Q_isPrime
    exact hQp.irreducible
  have h_count_Qpow : s + 1 ≤ Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors (S.Q ^ (s + 1))) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul]
    have h1 : 1 ≤ Multiset.count S.Q
        (UniqueFactorizationMonoid.normalizedFactors S.Q) := by
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hQ_irr,
        normalize_eq, Multiset.count_singleton_self]
    nlinarith
  -- Combine via `Ideal.count_le_of_ideal_ge`.
  have hcount := Ideal.count_le_of_ideal_ge h_pow_le hI_pow_ne_bot S.Q
  omega

/-! **Uniformizer fact (REF-18c2c4-L2c3a):** `π = ζ_ℓ - 1` is a
`Q`-uniformizer, i.e., `π ∉ Q^2`.

This is now provided as a structural field on
`TraceFormStickelbergerSetup` (`pi_not_mem_Q_sq`), so any proof
needing `S.π ∉ S.Q ^ 2` simply uses `S.pi_not_mem_Q_sq`. The
mathematical justification is the ramification of `ℓ` in the mixed
cyclotomic field `R' = ℚ(ζ_p, ζ_ℓ)`: at any prime `Q` above `ℓ`, the
ramification index is `ℓ - 1`, so `π` is a uniformizer.

The derivation of this field from singleton-conductor cyclotomic
ramification (mathlib's `IsCyclotomicExtension.Rat.ramificationIdx_eq`
with `n = ℓ · p`, prime `ℓ`, `m = p`) is tracked as a separate
follow-up ticket. See the L2c3a board entry. -/

/-- Parametric form of the leading-term non-degeneracy: any `Q`-unit
times `π^s` lies outside `Q^(s+1)`. Builds on the structural Dedekind
fact `pi_pow_not_mem_Q_pow_succ_of_not_mem_sq`. -/
theorem unit_mul_pi_pow_not_mem_Q_pow_succ
    (S : TraceFormStickelbergerSetup ℓ p k K R')
    (h_pi_ne_zero : S.π ≠ 0) (h_pi_nondeg : S.π ∉ S.Q ^ 2)
    (u : 𝓞 R') (hu : u ∉ S.Q) (s : ℕ) :
    u * S.π ^ s ∉ S.Q ^ (s + 1) := by
  intro h_in
  rcases Ideal.IsPrime.mul_mem_pow S.Q h_in with h_u | h_pi_pow
  · exact hu h_u
  · exact S.pi_pow_not_mem_Q_pow_succ_of_not_mem_sq h_pi_ne_zero h_pi_nondeg s h_pi_pow

/-- **L2c3d-6 (stickOrd wrapper).** No digit vector of weight strictly
less than `S.stickOrd a` survives the divisibility test
`(#k - 1) ∣ (p - a) * S.stickD + digitValue m`. This is the
`stickOrd`/`stickD`-form wrapper around `no_survivor_of_weight_lt`
proved in `DigitVectors.lean`. -/
theorem no_survivor_of_weight_lt_stickOrd
    (S : TraceFormStickelbergerSetup ℓ p k K R')
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : digitVec ℓ S.f) (hm : digitWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue m) := by
  unfold stickOrd stickD at *
  exact S.no_survivor_of_weight_lt a ha₁ ha₂ m hm

/-- **L2c3e-1 (stickOrd wrapper, weight half).** The standard digit
vector of `a * S.stickD` has weight `S.stickOrd a`. -/
theorem digitWeight_standardDigitVec_eq_stickOrd
    (S : TraceFormStickelbergerSetup ℓ p k K R')
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    digitWeight (S.standardDigitVec (a * S.stickD)) = S.stickOrd a := by
  unfold stickOrd stickD
  exact (S.standardDigitVec_weight_value a ha₁ ha₂).1

/-- **L2c3e-1 (stickOrd wrapper, value half).** The standard digit
vector of `a * S.stickD` has value `a * S.stickD`. -/
theorem digitValue_standardDigitVec_eq
    (S : TraceFormStickelbergerSetup ℓ p k K R')
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    digitValue (S.standardDigitVec (a * S.stickD)) = a * S.stickD := by
  unfold stickD
  exact (S.standardDigitVec_weight_value a ha₁ ha₂).2

/-- **L2c3e-2: Unique survivor at leading weight.** A digit vector of
weight equal to `S.stickOrd a` that survives the divisibility test
must be the standard digit decomposition of `a · d`. -/
theorem unique_survivor_at_stickOrd
    (S : TraceFormStickelbergerSetup ℓ p k K R')
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : digitVec ℓ S.f)
    (_hw : digitWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue m)) :
    m = S.standardDigitVec (a * S.stickD) := by
  classical
  set q : ℕ := Fintype.card k with hq_def
  set d : ℕ := S.stickD
  -- Replicate the arithmetic of `no_survivor_of_weight_lt` to derive
  -- `digitValue m = a * d`.
  have hℓ_prime : Nat.Prime ℓ := Fact.out
  have hℓ_ge_two : 2 ≤ ℓ := hℓ_prime.two_le
  have hq_eq : q = ℓ ^ S.f := S.card_k
  have hq_ge_two : 2 ≤ q := Fintype.one_lt_card
  have hpd : p * d = q - 1 := S.p_mul_stickD_eq_card_sub_one
  have hd_pos : 1 ≤ d := by
    have hq_sub : 1 ≤ q - 1 := by omega
    have hp_dvd : p ∣ q - 1 := S.toConcreteStickelbergerSetup.hdiv
    have hp_le : p ≤ q - 1 := Nat.le_of_dvd hq_sub hp_dvd
    change 1 ≤ S.stickD
    change 1 ≤ (q - 1) / p
    exact Nat.one_le_div_iff (by exact (Fact.out : Nat.Prime p).pos) |>.mpr hp_le
  have hM_lt : digitValue m < q := by
    rw [hq_eq]; exact digitValue_lt hℓ_ge_two m
  have hM_le : digitValue m ≤ q - 1 := by omega
  have hA_le : a * d ≤ q - 1 - d := by
    have h_a_le : a ≤ p - 1 := ha₂
    have h1 : a * d ≤ (p - 1) * d := Nat.mul_le_mul_right _ h_a_le
    have h2 : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    omega
  have hA_pos : 1 ≤ a * d := by
    have : 1 * 1 ≤ a * d := Nat.mul_le_mul ha₁ hd_pos
    simpa using this
  have hpa_d_le : (p - a) * d ≤ q - 1 - d := by
    have : p - a ≤ p - 1 := by omega
    have h1 : (p - a) * d ≤ (p - 1) * d := Nat.mul_le_mul_right _ this
    have h2 : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    omega
  have hpa_d_ge : d ≤ (p - a) * d := by
    have h_pa : 1 ≤ p - a := by omega
    have : 1 * d ≤ (p - a) * d := Nat.mul_le_mul_right _ h_pa
    simpa using this
  have h_lhs_lt : (p - a) * d + digitValue m < 2 * (q - 1) := by omega
  have h_lhs_pos : 1 ≤ (p - a) * d + digitValue m := by omega
  have h_lhs_eq : (p - a) * d + digitValue m = q - 1 := by
    obtain ⟨c, hc⟩ := hdiv
    have hc_eq : (q - 1) * c = (p - a) * d + digitValue m := by
      change (q - 1) * c = _
      rw [show (Fintype.card k - 1) * c = (q - 1) * c from rfl] at hc
      exact hc.symm
    have hc_pos : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with hc0 | hcp
      · rw [hc0, Nat.mul_zero] at hc_eq; omega
      · exact hcp
    have hc_lt : c < 2 := by
      have : (q - 1) * c < (q - 1) * 2 := by
        rw [hc_eq, show (q - 1) * 2 = 2 * (q - 1) by ring]
        exact h_lhs_lt
      exact Nat.lt_of_mul_lt_mul_left this
    have hc_eq1 : c = 1 := by omega
    rw [hc_eq1, Nat.mul_one] at hc_eq
    exact hc_eq.symm
  have hM_eq_A : digitValue m = a * d := by
    have h1 : (p - a) * d + digitValue m = p * d := by
      rw [h_lhs_eq]; exact hpd.symm
    have h2 : (p - a) * d + a * d = p * d := by
      rw [show (p - a) * d + a * d = ((p - a) + a) * d by ring]
      congr 1; omega
    omega
  -- Apply uniqueness of digit-vector representation.
  have hA_lt : a * d < ℓ ^ S.f := by rw [← hq_eq]; omega
  exact digitVec_eq_standardDigitVec_of_value hℓ_ge_two hA_lt m hM_eq_A

/-- **L2c3d-2 (stickD wrapper).** The reciprocal residue character is a
power of the full Teichmüller, expressed using `S.stickD`. -/
theorem residueCharInt_rec_eq_teichUnitFull_pow_stickD
    (S : FullTeichStickelbergerSetup ℓ p k K R')
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) (x : kˣ) :
    S.residueCharInt (x : k) ^ (p - a) =
      (S.teichUnitFull x : 𝓞 R') ^ ((p - a) * S.stickD) := by
  unfold stickD
  exact S.residueCharInt_rec_eq_teichUnitFull_pow a ha₁ ha₂ x

/-! The TraceFormStickelbergerSetup-only digit-sum Stickelberger statements
(`gaussSumIntRec_mem_Q_pow_stickOrd`, `gaussSumIntRec_not_mem_Q_pow_stickOrd_succ`,
`gaussSumIntRec_qadic_ord_at_prime`, `gaussSumInt_mem_Q_pow_stickOrdOrd`,
`gaussSumInt_qadic_ord_at_prime_ord`) have been removed: the substantive
content lives on the richer `FullTeichDworkSetup` (see `DworkAssembly.lean`,
`gaussSumIntRec_qadic_ord_at_prime_dwork` and
`gaussSumInt_qadic_ord_at_prime_ord_dwork`), which is the bundle actually
consumed downstream. -/

end TraceFormStickelbergerSetup

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : FullTeichStickelbergerSetup ℓ p k K R')




/-! The originally-planned digit-bounded denominator-cleared multi-index
expansion (`gaussSumIntRec_digit_expansion_denCleared`) is mathematically
**incorrect** — the implicit per-`x` congruence
`descFactorial(Tr(c·x).val, k) ≡ teichUnitFull(c·x)^k (mod Q)` already
fails at first order (counterexample: `ℓ=3, k=𝔽_3, x=2, k=2`). The
correct expansion is the **Dwork splitting expansion** with Artin–Hasse
coefficients, formalised on `FullTeichDworkSetup` in `DworkAssembly.lean`
as `gaussSumIntRec_dwork_expansion`. The downstream digit-sum Stickelberger
statements (`gaussSumIntRec_mem_Q_pow_stickOrd`,
`digitDen_mul_gaussSumIntRec_congr_leading`,
`gaussSumIntRec_not_mem_Q_pow_stickOrd_succ`,
`gaussSumIntRec_qadic_ord_at_prime`, `gaussSumInt_mem_Q_pow_stickOrdOrd`,
`gaussSumInt_qadic_ord_at_prime_ord`) have therefore been removed from
this namespace; their Dwork-bundle replacements
(`gaussSumIntRec_mem_Q_pow_stickOrd_dwork`,
`gaussSumIntRec_not_mem_Q_pow_stickOrd_succ_dwork`,
`gaussSumIntRec_qadic_ord_at_prime_dwork`,
`gaussSumInt_qadic_ord_at_prime_ord_dwork`) are stated against
`FullTeichDworkSetup` in `DworkAssembly.lean`. The leading-term helpers
`leadingCoeff`, `digit_expansion_inner_sum_eval`, and
`leadingCoeff_not_mem_Q` are retained above as they remain mathematically
correct and may aid future development. -/

end FullTeichStickelbergerSetup

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : FullTeichDworkSetup ℓ p k K R')

/-- The reciprocal Gauss sum, expressed as a sum over `kˣ` (after
dropping the trivially-zero contribution at `x = 0`). Used by
`gaussSumIntRec_dwork_expansion` (L2c3d-4b). -/
theorem gaussSumIntRec_eq_sum_units [DecidableEq k] (a : ℕ) :
    S.gaussSumIntRec a =
      ∑ x : kˣ, (S.residueCharInt ^ (p - a)) ((x : k)) * S.psiInt ((x : k)) := by
  classical
  -- gaussSumIntRec a = gaussSumInt (p - a) = ∑ x : k, χ(x) · ψ(x).
  -- Split univ = insert 0 (univ.erase 0); χ(0) = 0 kills the 0-term.
  change _root_.gaussSum (S.residueCharInt ^ (p - a)) S.psiInt = _
  unfold _root_.gaussSum
  rw [show (Finset.univ : Finset k) = insert 0 (Finset.univ.erase 0) by
    rw [Finset.insert_erase (Finset.mem_univ 0)]]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  rw [MulChar.map_zero, zero_mul, zero_add]
  -- Bijection kˣ ≃ univ.erase 0.
  refine (Finset.sum_bij (fun (x : kˣ) _ => (x : k)) ?_ ?_ ?_ ?_).symm
  · intro x _; simp [Units.ne_zero]
  · intro x _ y _ hxy; exact Units.ext hxy
  · intro y hy
    rw [Finset.mem_erase] at hy
    exact ⟨Units.mk0 y hy.1, Finset.mem_univ _, rfl⟩
  · intro x _; rfl

/-- **L2c3d-4b: Dwork digit expansion for the reciprocal Gauss sum.**
The reciprocal Gauss sum equals the multi-index Dwork sum modulo
`Q^{N+1}`, where the multi-indices range over **all**
`m : Fin S.f → ℕ` of weight at most `N` (NOT just digit-bounded). -/
theorem gaussSumIntRec_dwork_expansion [DecidableEq k]
    (a N : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a -
        (∑ m ∈ multiIndexLE S.f N,
          (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) ∈
      S.Q ^ (N + 1) := by
  classical
  -- Step 1: rewrite LHS as ∑ x : kˣ, ω(x)^A · psiInt x using L2c3d-2.
  have h_lhs : S.gaussSumIntRec a =
      ∑ x : kˣ,
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) * S.psiInt ((x : k)) := by
    rw [S.gaussSumIntRec_eq_sum_units a]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    have h := TraceFormStickelbergerSetup.residueCharInt_rec_eq_teichUnitFull_pow_stickD
      S.toFullTeichStickelbergerSetup a ha₁ ha₂ x
    -- h : S.residueCharInt ↑x ^ (p - a) = ↑(S.teichUnitFull x) ^ ((p - a) * S.stickD)
    rw [MulChar.pow_apply_coe]
    change S.residueCharInt ((x : k)) ^ (p - a) =
      S.teichUnitFullVal x ^ ((p - a) * S.stickD)
    exact h
  rw [h_lhs]
  -- Step 2: per-x rewrite psiInt x = (Dwork sum at c·x) + r(x).
  have h_psi : ∀ x : kˣ,
      S.psiInt ((x : k)) -
        (∑ m ∈ multiIndexLE S.f N,
          (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
            multiIndexValue ℓ m)) ∈ S.Q ^ (N + 1) :=
    fun x => S.psi_dwork_factorization N x
  -- Step 3: split each LHS term into "Dwork part" + "error", sum.
  have h_split : ∀ x : kˣ,
      S.teichUnitFullVal x ^ ((p - a) * S.stickD) * S.psiInt ((x : k)) =
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          (∑ m ∈ multiIndexLE S.f N,
            (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
            ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
              multiIndexValue ℓ m)) +
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          (S.psiInt ((x : k)) -
            (∑ m ∈ multiIndexLE S.f N,
              (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
              ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
                multiIndexValue ℓ m))) := by
    intro x; ring
  rw [Finset.sum_congr rfl fun x _ => h_split x]
  rw [Finset.sum_add_distrib]
  -- Step 4: error sum is in Q^(N+1).
  have h_error_mem :
      (∑ x : kˣ,
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          (S.psiInt ((x : k)) -
            (∑ m ∈ multiIndexLE S.f N,
              (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
              ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
                multiIndexValue ℓ m)))) ∈ S.Q ^ (N + 1) := by
    refine Ideal.sum_mem _ fun x _ => ?_
    exact Ideal.mul_mem_left _ _ (h_psi x)
  -- Step 5: swap sums on the "Dwork part" and identify with the target.
  have h_swap :
      (∑ x : kˣ,
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
        (∑ m ∈ multiIndexLE S.f N,
          (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
            multiIndexValue ℓ m))) =
      (∑ m ∈ multiIndexLE S.f N,
        (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
        (∑ x : kˣ,
          S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) := by
    -- Distribute (left → ∑_m T·U; right → ∑_x (∏λ)·V).
    simp_rw [Finset.mul_sum]
    -- Now both sides are double sums. LHS: ∑_x ∑_m (...). RHS: ∑_m ∑_x (...).
    -- Swap LHS via sum_comm.
    rw [Finset.sum_comm]
    -- Per-(m, x): both sides agree by ring (teichUnitFullVal y = ↑(teichUnitFull y)).
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    change S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
        ((∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m) =
      (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
        (S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)
    ring
  rw [h_swap, add_sub_cancel_left]
  exact h_error_mem

end FullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end
