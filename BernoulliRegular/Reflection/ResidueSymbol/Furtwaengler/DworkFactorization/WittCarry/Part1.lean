module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich

/-!
# Witt carry comparison for Dwork factorization

Split from `DworkFactorization.lean`.
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






/-- The trace exponent in the additive character is the zeroth Witt
coefficient of the finite Witt-Frobenius trace of the Teichmüller
representative of `traceScale * y`. -/
theorem wittFrobeniusTrace_teichmuller_traceScale_mul_coeff_zero
    (y : kˣ) :
    (ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
        F.toConcreteStickelbergerSetup.f
        (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k)))).coeff 0 =
      algebraMap (ZMod ℓ) k
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))) := by
  classical
  rw [ConcreteStickelbergerSetup.wittFrobeniusTrace_teichmuller_coeff_zero]
  have h :=
    F.toTraceFormStickelbergerSetup.algebraMap_trace_pow_eq_traceSum_pow_setup
      ((F.traceScale : k) * (y : k)) 1
  have hrange :
      algebraMap (ZMod ℓ) k
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))) =
        ∑ i ∈ Finset.range F.toConcreteStickelbergerSetup.f,
          ((F.traceScale : k) * (y : k)) ^ (ℓ ^ i) := by
    simpa [traceSum] using h
  rw [← Fin.sum_univ_eq_sum_range] at hrange
  exact hrange.symm

/-- The finite Witt-Frobenius trace of the scaled Teichmüller representative is
congruent modulo `ℓ` to the Teichmüller lift of the ordinary finite-field
trace. This is the Witt-vector form of the remaining Dwork trace dependence:
the higher Witt coordinates are an `ℓ`-multiple. -/
theorem wittFrobeniusTrace_teichmuller_traceScale_mul_sub_teichmuller_trace_dvd_prime
    (y : kˣ) :
    (ℓ : WittVector ℓ k) ∣
      ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
          F.toConcreteStickelbergerSetup.f
          (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k))) -
        WittVector.teichmuller ℓ
          (algebraMap (ZMod ℓ) k
            (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k)))) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  have hsum :
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
          ((F.traceScale : k) * (y : k)) ^ (ℓ ^ (i : ℕ))) =
        algebraMap (ZMod ℓ) k
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))) := by
    rw [← ConcreteStickelbergerSetup.wittFrobeniusTrace_teichmuller_coeff_zero
      (ℓ := ℓ) (k := k) F.toConcreteStickelbergerSetup.f
      ((F.traceScale : k) * (y : k))]
    exact F.wittFrobeniusTrace_teichmuller_traceScale_mul_coeff_zero y
  simpa [hsum] using
    ConcreteStickelbergerSetup.wittFrobeniusTrace_teichmuller_sub_teichmuller_coeff_zero_dvd_prime
        (ℓ := ℓ) (k := k) F.toConcreteStickelbergerSetup.f
        ((F.traceScale : k) * (y : k))

/-- Canonical Witt carry for replacing the natural representative of the
finite-field trace by its Teichmüller lift.  This choice is made in the Witt
ring, hence is independent of the later quotient precision. -/
noncomputable def traceNatCarry (y : kˣ) : WittVector ℓ k := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  exact
    Classical.choose
      (ConcreteStickelbergerSetup.natCast_zmod_val_sub_teichmuller_dvd_prime
        (ℓ := ℓ) (k := k)
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))))

/-- Specification of `traceNatCarry`. -/
theorem traceNatCarry_spec (y : kˣ) :
    (((Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val : ℕ) :
          WittVector ℓ k) -
        WittVector.teichmuller ℓ
          (algebraMap (ZMod ℓ) k
            (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k)))) =
      (ℓ : WittVector ℓ k) * F.traceNatCarry y := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  simpa [traceNatCarry] using
    Classical.choose_spec
      (ConcreteStickelbergerSetup.natCast_zmod_val_sub_teichmuller_dvd_prime
        (ℓ := ℓ) (k := k)
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))))

/-- Canonical Witt carry for replacing the Witt-Frobenius trace of a
Teichmüller representative by the Teichmüller lift of its zeroth coefficient. -/
noncomputable def traceFrobeniusCarry (y : kˣ) : WittVector ℓ k :=
  Classical.choose
    (F.wittFrobeniusTrace_teichmuller_traceScale_mul_sub_teichmuller_trace_dvd_prime y)

/-- Specification of `traceFrobeniusCarry`. -/
theorem traceFrobeniusCarry_spec (y : kˣ) :
    ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
        F.toConcreteStickelbergerSetup.f
        (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k))) -
      WittVector.teichmuller ℓ
        (algebraMap (ZMod ℓ) k
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k)))) =
      (ℓ : WittVector ℓ k) * F.traceFrobeniusCarry y := by
  classical
  simpa [traceFrobeniusCarry] using
    Classical.choose_spec
      (F.wittFrobeniusTrace_teichmuller_traceScale_mul_sub_teichmuller_trace_dvd_prime y)

/-- Canonical Witt carry measuring the difference between the ordinary trace
lift and the Teichmüller Frobenius trace sum. -/
noncomputable def traceCarry (y : kˣ) : WittVector ℓ k :=
  F.traceNatCarry y - F.traceFrobeniusCarry y



omit [Fintype k] in
private theorem witt_frobenius_fixed_of_prime_mul_eq_of_frobenius_fixed
    [ExpChar k ℓ] [PerfectRing k ℓ]
    {d x : WittVector ℓ k}
    (hd : d = (ℓ : WittVector ℓ k) * x)
    (hfix : WittVector.frobenius d = d) :
    WittVector.frobenius x = x := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  have hmul :
      (ℓ : WittVector ℓ k) * WittVector.frobenius x =
        (ℓ : WittVector ℓ k) * x := by
    calc
      (ℓ : WittVector ℓ k) * WittVector.frobenius x
          = WittVector.frobenius ((ℓ : WittVector ℓ k) * x) := by
            simp
      _ = WittVector.frobenius d := by rw [hd]
      _ = d := hfix
      _ = (ℓ : WittVector ℓ k) * x := hd
  have hzero_left :
      (ℓ : WittVector ℓ k) * (WittVector.frobenius x - x) = 0 := by
    rw [mul_sub, hmul, sub_self]
  have hzero :
      (WittVector.frobenius x - x) * ℓ = 0 := by
    simpa [mul_comm] using hzero_left
  exact sub_eq_zero.mp (WittVector.eq_zero_of_p_mul_eq_zero
    (WittVector.frobenius x - x) hzero)

omit [Fintype k] in
private theorem witt_frobenius_teichmuller_zmod_fixed
    [ExpChar k ℓ] [PerfectRing k ℓ] (a : ZMod ℓ) :
    WittVector.frobenius
        (WittVector.teichmuller ℓ (algebraMap (ZMod ℓ) k a)) =
      WittVector.teichmuller ℓ (algebraMap (ZMod ℓ) k a) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  rw [ConcreteStickelbergerSetup.witt_frobenius_teichmuller]
  congr 1
  rw [← map_pow, ZMod.pow_card]

/-- The finite-field Frobenius power attached to `F.f` is the identity on
the chosen residue-field model. -/
theorem finiteField_pow_ell_f_eq_self (x : k) :
    x ^ (ℓ ^ F.toConcreteStickelbergerSetup.f) = x := by
  simpa [F.toConcreteStickelbergerSetup.card_k_eq] using
    (FiniteField.pow_card x)

/-- The finite Witt-Frobenius trace over the whole residue-field orbit is
fixed by Witt Frobenius. -/
theorem wittFrobeniusTrace_teichmuller_traceScale_mul_frobenius_fixed
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) :
    WittVector.frobenius
        (ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
          F.toConcreteStickelbergerSetup.f
          (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k)))) =
      ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
        F.toConcreteStickelbergerSetup.f
        (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k))) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  let x : k := (F.traceScale : k) * (y : k)
  let w : WittVector ℓ k := WittVector.teichmuller ℓ x
  let f : ℕ := F.toConcreteStickelbergerSetup.f
  let g : ℕ → WittVector ℓ k := fun n => (WittVector.frobenius^[n]) w
  have hxperiod : x ^ (ℓ ^ f) = x := by
    simpa [x, f] using F.finiteField_pow_ell_f_eq_self x
  have hperiod : ∀ n : ℕ, g (n + f) = g n := by
    intro n
    dsimp [g, w]
    rw [ConcreteStickelbergerSetup.witt_iterate_frobenius_teichmuller,
      ConcreteStickelbergerSetup.witt_iterate_frobenius_teichmuller]
    congr 1
    have hpow_nf : ℓ ^ (n + f) = ℓ ^ f * ℓ ^ n := by
      rw [pow_add, Nat.mul_comm]
    calc
      x ^ (ℓ ^ (n + f)) = x ^ (ℓ ^ f * ℓ ^ n) := by rw [hpow_nf]
      _ = (x ^ (ℓ ^ f)) ^ (ℓ ^ n) := by rw [← pow_mul]
      _ = x ^ (ℓ ^ n) := by rw [hxperiod]
  have hshift := sum_range_shift_iterate_eq_of_period g f 1 hperiod
  have hleft :
      (∑ i : Fin f, g ((i : ℕ) + 1)) =
        ∑ i ∈ Finset.range f, g (i + 1) :=
    (Finset.sum_range (f := fun i : ℕ => g (i + 1))).symm
  have hright :
      (∑ i : Fin f, g (i : ℕ)) =
        ∑ i ∈ Finset.range f, g i :=
    (Finset.sum_range (f := fun i : ℕ => g i)).symm
  calc
    WittVector.frobenius
        (ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
          F.toConcreteStickelbergerSetup.f
          (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k))))
        =
          ∑ i : Fin f, g ((i : ℕ) + 1) := by
          simp [ConcreteStickelbergerSetup.wittFrobeniusTrace, x, w, f, g,
            Function.iterate_succ_apply']
    _ = ∑ i : Fin f, g (i : ℕ) := by
          rw [hleft, hright]
          exact hshift
    _ =
        ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
          F.toConcreteStickelbergerSetup.f
          (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k))) := by
          simp [ConcreteStickelbergerSetup.wittFrobeniusTrace, x, w, f, g]

/-- The natural trace carry is fixed by Witt Frobenius. -/
theorem traceNatCarry_frobenius_fixed
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) :
    WittVector.frobenius (F.traceNatCarry y) = F.traceNatCarry y := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  let a : ZMod ℓ := Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))
  let d : WittVector ℓ k :=
    ((a.val : ℕ) : WittVector ℓ k) -
      WittVector.teichmuller ℓ (algebraMap (ZMod ℓ) k a)
  have hd : d = (ℓ : WittVector ℓ k) * F.traceNatCarry y := by
    simpa [a, d] using F.traceNatCarry_spec y
  refine witt_frobenius_fixed_of_prime_mul_eq_of_frobenius_fixed hd ?_
  dsimp [d]
  rw [map_sub, map_natCast, witt_frobenius_teichmuller_zmod_fixed]

/-- The Frobenius-trace carry is fixed by Witt Frobenius. -/
theorem traceFrobeniusCarry_frobenius_fixed
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) :
    WittVector.frobenius (F.traceFrobeniusCarry y) = F.traceFrobeniusCarry y := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  let a : ZMod ℓ := Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))
  let trW : WittVector ℓ k :=
    ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
      F.toConcreteStickelbergerSetup.f
      (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k)))
  let d : WittVector ℓ k :=
    trW - WittVector.teichmuller ℓ (algebraMap (ZMod ℓ) k a)
  have hd : d = (ℓ : WittVector ℓ k) * F.traceFrobeniusCarry y := by
    simpa [a, trW, d] using F.traceFrobeniusCarry_spec y
  refine witt_frobenius_fixed_of_prime_mul_eq_of_frobenius_fixed hd ?_
  dsimp [d, trW]
  rw [map_sub, F.wittFrobeniusTrace_teichmuller_traceScale_mul_frobenius_fixed,
    witt_frobenius_teichmuller_zmod_fixed]

/-- The canonical trace carry is fixed by Witt Frobenius. -/
theorem traceCarry_frobenius_fixed
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) :
    WittVector.frobenius (F.traceCarry y) = F.traceCarry y := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  rw [traceCarry, map_sub, F.traceNatCarry_frobenius_fixed y,
    F.traceFrobeniusCarry_frobenius_fixed y]


/-- Each coordinate of the canonical trace carry lies in the prime subfield.
This is the coordinate form of `traceCarry_frobenius_fixed`. -/
theorem traceCarry_coeff_mem_primeSubfield
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (r : ℕ) :
    (F.traceCarry y).coeff r ∈ (⊥ : Subfield k) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  rw [Subfield.mem_bot_iff_pow_eq_self (F := k) (p := ℓ)]
  have h := congrArg (fun x => x.coeff r) (F.traceCarry_frobenius_fixed y)
  simpa [WittVector.coeff_frobenius_charP] using h

/-- Prime-field coordinates of the canonical trace carry, represented as
elements of `ZMod ℓ`. -/
theorem exists_zmod_eq_traceCarry_coeff
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (r : ℕ) :
    ∃ a : ZMod ℓ, algebraMap (ZMod ℓ) k a = (F.traceCarry y).coeff r := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  have hmem : (F.traceCarry y).coeff r ∈ (⊥ : Subfield k) :=
    F.traceCarry_coeff_mem_primeSubfield y r
  rw [← ZMod.fieldRange_castHom_eq_bot ℓ (K := k)] at hmem
  rcases hmem with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hhom :
      (algebraMap (ZMod ℓ) k) = (ZMod.castHom (m := ℓ) dvd_rfl k) :=
    Subsingleton.elim _ _
  rw [hhom]
  exact ha

/-- Every inverse-Frobenius iterate fixes every trace-carry coordinate.  This
is the shifted-tail form needed when the iteration index and coordinate index
are no longer the same. -/
theorem traceCarry_coeff_frobeniusEquiv_symm_iterate_eq_self
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (n r : ℕ) :
    ((_root_.frobeniusEquiv k ℓ).symm ^ n) ((F.traceCarry y).coeff r) =
      (F.traceCarry y).coeff r := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  have hcoeff :
      (F.traceCarry y).coeff r ^ ℓ = (F.traceCarry y).coeff r := by
    have h := congrArg (fun x => x.coeff r) (F.traceCarry_frobenius_fixed y)
    simpa [WittVector.coeff_frobenius_charP] using h
  have hroot :
      (_root_.frobeniusEquiv k ℓ).symm ((F.traceCarry y).coeff r) =
        (F.traceCarry y).coeff r := by
    calc
      (_root_.frobeniusEquiv k ℓ).symm ((F.traceCarry y).coeff r) =
          (_root_.frobeniusEquiv k ℓ).symm ((F.traceCarry y).coeff r ^ ℓ) := by
        rw [hcoeff]
      _ = (F.traceCarry y).coeff r := by
        simp
  suffices hiter : ∀ n : ℕ,
      ((_root_.frobeniusEquiv k ℓ).symm ^ n) ((F.traceCarry y).coeff r) =
        (F.traceCarry y).coeff r from
    hiter n
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      change
        ((_root_.frobeniusEquiv k ℓ).symm ^ n)
          ((_root_.frobeniusEquiv k ℓ).symm ((F.traceCarry y).coeff r)) =
          (F.traceCarry y).coeff r
      rw [hroot, ih]


/-- A chosen `ZMod ℓ` representative for the `r`-th coordinate of the canonical
trace carry.  This turns the existential prime-field statement into a stable
rewrite target for the finite Artin-Hasse products. -/
noncomputable def traceCarryCoeffZMod
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (r : ℕ) : ZMod ℓ :=
  Classical.choose (F.exists_zmod_eq_traceCarry_coeff y r)

/-- The chosen `ZMod ℓ` representative maps to the trace-carry coordinate. -/
theorem traceCarryCoeffZMod_spec
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (r : ℕ) :
    algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r) =
      (F.traceCarry y).coeff r := by
  simpa [traceCarryCoeffZMod] using
    (Classical.choose_spec (F.exists_zmod_eq_traceCarry_coeff y r))

/-- The chosen prime-field coordinate also represents any inverse-Frobenius
iterate of the same trace-carry coordinate. -/
theorem traceCarryCoeffZMod_frobeniusRoot_iterate_spec
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (n r : ℕ) :
    algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r) =
      ((_root_.frobeniusEquiv k ℓ).symm ^ n) ((F.traceCarry y).coeff r) := by
  rw [F.traceCarry_coeff_frobeniusEquiv_symm_iterate_eq_self y n r]
  exact F.traceCarryCoeffZMod_spec y r


/-- The chosen `ZMod ℓ` representative also maps to the Frobenius-rooted
coordinate used by the telescoping product. -/
theorem traceCarryCoeffZMod_frobeniusRoot_spec
    [ExpChar k ℓ] [PerfectRing k ℓ] (y : kˣ) (r : ℕ) :
    algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r) =
      ((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r) :=
  F.traceCarryCoeffZMod_frobeniusRoot_iterate_spec y r r




end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
