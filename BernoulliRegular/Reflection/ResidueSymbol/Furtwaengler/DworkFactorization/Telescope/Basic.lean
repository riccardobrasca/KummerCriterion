module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.WittCarry

/-!
# Basic Q-adic and inverse-boundary lemmas for the finite Dwork telescope.

Split from `DworkFactorization/Telescope.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')

/-- Powers of the rational residue characteristic have exactly the expected
`Q`-adic order coming from `ℓ ~ (ζ_ℓ - 1)^(ℓ-1)`. -/
theorem natCast_ell_pow_not_mem_Q_pow_mul_pred_succ (m : ℕ) :
    ((ℓ : 𝓞 R') ^ m) ∉ F.Q ^ (m * (ℓ - 1) + 1) := by
  have hassoc :
      Associated ((ℓ : 𝓞 R') ^ m) (F.π ^ (m * (ℓ - 1))) := by
    have h :=
      (associated_ell_zeta_sub_one_pow
        F.toConcreteStickelbergerSetup.zeta_ell_int_isPrimitiveRoot).pow_pow (n := m)
    have hπpow :
        Associated (((F.zeta_ell_int - 1) ^ (ℓ - 1)) ^ m)
          (F.π ^ (m * (ℓ - 1))) := by
      rw [F.toConcreteStickelbergerSetup.hπ, ← pow_mul]
      rw [Nat.mul_comm (ℓ - 1) m]
    exact h.trans hπpow
  intro hmem
  have hpi_mem : F.π ^ (m * (ℓ - 1)) ∈ F.Q ^ (m * (ℓ - 1) + 1) :=
    (associated_mem_ideal_iff hassoc).1 hmem
  exact
    F.toTraceFormStickelbergerSetup.pi_pow_not_mem_Q_pow_succ_of_not_mem_sq
      F.toTraceFormStickelbergerSetup.pi_ne_zero
      F.toTraceFormStickelbergerSetup.pi_not_mem_Q_sq
      (m * (ℓ - 1)) hpi_mem

/-- Exact `Q`-adic cancellation for powers of the rational residue
characteristic.  Since `(ℓ)^m` has exact `Q`-adic order `m*(ℓ-1)`, a product
`(ℓ)^m * x` lying in `Q^(m*(ℓ-1)+n)` forces `x` to lie in `Q^n`. -/
theorem mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
    {m n : ℕ} {x : 𝓞 R'}
    (h : (ℓ : 𝓞 R') ^ m * x ∈ F.Q ^ (m * (ℓ - 1) + n)) :
    x ∈ F.Q ^ n := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  let r : ℕ := m * (ℓ - 1)
  let I : Ideal (𝓞 R') := Ideal.span ({(ℓ : 𝓞 R') ^ m} : Set (𝓞 R'))
  let J : Ideal (𝓞 R') := Ideal.span ({x} : Set (𝓞 R'))
  have hI_le : I ≤ F.Q ^ r := by
    change Ideal.span ({(ℓ : 𝓞 R') ^ m} : Set (𝓞 R')) ≤ F.Q ^ r
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [r] using
      F.toTraceFormStickelbergerSetup.natCast_ell_pow_mem_Q_pow_mul_pred m
  have hI_not_le : ¬ I ≤ F.Q ^ (r + 1) := fun hle =>
    F.natCast_ell_pow_not_mem_Q_pow_mul_pred_succ m <|
      by
        have hmem : (ℓ : 𝓞 R') ^ m ∈ F.Q ^ (r + 1) :=
          hle (Ideal.mem_span_singleton_self ((ℓ : 𝓞 R') ^ m))
        simpa [r, Nat.add_comm] using hmem
  have hI_count :
      Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors I) = r :=
    Ideal.count_normalizedFactors_eq hI_le hI_not_le
  have hI_ne : I ≠ ⊥ := by
    change Ideal.span ({(ℓ : 𝓞 R') ^ m} : Set (𝓞 R')) ≠ ⊥
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero m (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero)
  have hJ_ne : J ≠ ⊥ := by
    change Ideal.span ({x} : Set (𝓞 R')) ≠ ⊥
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hx
  have hIJ_ne : I * J ≠ ⊥ := mul_ne_zero hI_ne hJ_ne
  have hprod_le : I * J ≤ F.Q ^ (r + n) := by
    change
      Ideal.span ({(ℓ : 𝓞 R') ^ m} : Set (𝓞 R')) *
          Ideal.span ({x} : Set (𝓞 R')) ≤ F.Q ^ (r + n)
    rw [Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_le_iff_mem]
    simpa [r, mul_assoc] using h
  have hQ_irr : Irreducible F.Q := by
    have hQp : Prime F.Q :=
      Ideal.prime_of_isPrime F.toTraceFormStickelbergerSetup.Q_ne_bot
        F.toTraceFormStickelbergerSetup.Q_isPrime
    exact hQp.irreducible
  have hQpow_count :
      Multiset.count F.Q
          (UniqueFactorizationMonoid.normalizedFactors (F.Q ^ (r + n))) =
        r + n := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hQ_irr,
      normalize_eq, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
  have hprod_count_ge :
      r + n ≤ Multiset.count F.Q
          (UniqueFactorizationMonoid.normalizedFactors (I * J)) := by
    have hcount := Ideal.count_le_of_ideal_ge hprod_le hIJ_ne F.Q
    rw [hQpow_count] at hcount
    exact hcount
  have hprod_count :
      Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors (I * J)) =
        r + Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors J) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hI_ne hJ_ne,
      Multiset.count_add, hI_count]
  have hJ_count_ge :
      n ≤ Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors J) := by
    omega
  have hQpow_ne : F.Q ^ n ≠ ⊥ :=
    pow_ne_zero n F.toTraceFormStickelbergerSetup.Q_ne_bot
  have hJ_le : J ≤ F.Q ^ n := by
    rw [← Ideal.dvd_iff_le]
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      hQpow_ne hJ_ne]
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hQ_irr,
      normalize_eq, Multiset.nsmul_singleton]
    rw [Multiset.le_iff_count]
    intro P
    by_cases hP : P = F.Q
    · subst P
      simpa using hJ_count_ge
    · rw [Multiset.count_replicate]
      simp [hP, eq_comm]
  exact hJ_le (Ideal.mem_span_singleton_self x)

/-- `Q`-adic form of the standard binomial valuation for
`Nat.choose (ℓ^m) s`.  The rational `ℓ`-divisibility supplied by Kummer's
theorem is translated to the selected prime `Q` above `ℓ`. -/
theorem natCast_choose_ell_pow_mem_Q_pow_factorization
    {m s : ℕ} (hs0 : s ≠ 0) (hsle : s ≤ ℓ ^ m) :
    ((Nat.choose (ℓ ^ m) s : ℕ) : 𝓞 R') ∈
      F.Q ^ ((m - s.factorization ℓ) * (ℓ - 1)) := by
  have hp : Nat.Prime ℓ := Fact.out
  have hchoose_ne : Nat.choose (ℓ ^ m) s ≠ 0 :=
    (Nat.choose_pos hsle).ne'
  have hfac :
      (Nat.choose (ℓ ^ m) s).factorization ℓ = m - s.factorization ℓ :=
    Nat.factorization_choose_prime_pow hp hsle hs0
  have hdvd : ℓ ^ (m - s.factorization ℓ) ∣ Nat.choose (ℓ ^ m) s :=
    (hp.pow_dvd_iff_le_factorization hchoose_ne).2
        (by rw [hfac])
  exact
    F.toTraceFormStickelbergerSetup.natCast_mem_Q_pow_mul_pred_of_ell_pow_dvd hdvd

private theorem nat_mul_pred_le_pow_sub_one (a n : ℕ) (ha : 1 ≤ a) :
    n * (a - 1) ≤ a ^ n - 1 := by
  have ha_pos : 0 < a := Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  have hpow_one : 1 ≤ a ^ n := Nat.one_le_pow n a ha_pos
  have hbern :
      (1 : ℤ) + (n : ℤ) * ((a : ℤ) - 1) ≤ (a : ℤ) ^ n :=
    one_add_mul_sub_le_pow (by omega) n
  have hcast :
      ((n * (a - 1) : ℕ) : ℤ) ≤ ((a ^ n - 1 : ℕ) : ℤ) := by
    have hpow_cast : ((a ^ n : ℕ) : ℤ) = (a : ℤ) ^ n :=
      Nat.cast_pow a n
    rw [Nat.cast_mul, Nat.cast_sub ha, Nat.cast_sub hpow_one, hpow_cast,
      Nat.cast_one]
    change (n : ℤ) * ((a : ℤ) - 1) ≤ (a : ℤ) ^ n - 1
    omega
  exact_mod_cast hcast

private theorem factorization_mul_pred_le_pred
    {s : ℕ} (hs0 : s ≠ 0) :
    s.factorization ℓ * (ℓ - 1) ≤ s - 1 := by
  have hp : Nat.Prime ℓ := Fact.out
  let f : ℕ := s.factorization ℓ
  have hdvd : ℓ ^ f ∣ s :=
    (hp.pow_dvd_iff_le_factorization hs0).2 le_rfl
  have hpow_le : ℓ ^ f ≤ s :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) hdvd
  have hmul_le : f * (ℓ - 1) ≤ ℓ ^ f - 1 :=
    nat_mul_pred_le_pow_sub_one ℓ f hp.pos
  exact hmul_le.trans (Nat.sub_le_sub_right hpow_le 1)




















end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
