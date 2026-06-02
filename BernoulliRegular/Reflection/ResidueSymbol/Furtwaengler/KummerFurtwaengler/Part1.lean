module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolNoncanonical
public import BernoulliRegular.FLT37.Primary
public import BernoulliRegular.UnitQuotient.DeltaAction


/-!
# Cyclotomic ideal-action support

This file contains the reusable algebraic infrastructure for cyclotomic
Galois actions on ideals and residue-symbol power identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]

/-! ### Auxiliary algebraic lemmas (engine for c.4) -/




/-! ### Ideal-symbol versions -/





/-! ### Principal-symbol versions

Basic principal-symbol API (`_one`, `_mul_left`, `_mul_right`) appears above.
Here we add the power lemmas used by denominator descent.
-/

















/-! ### c.1.0 — Galois conjugate of an ideal of `𝓞 K`

The cyclotomic Galois group `Gal(K/ℚ)` acts on `𝓞 K` via
`cyclotomicRingOfIntegersEquiv`. This lifts to an action on `Ideal (𝓞 K)`
by the standard `Ideal.map`. For each `a ∈ (ZMod p)ˣ`, the conjugate
`σ_a · q` is itself a prime ideal lying above the same rational prime as
`q`. This sets up the indexing of the Galois orbit of a prime needed to
state the Stickelberger ideal theorem (c.1).
-/

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The Galois conjugate of an ideal of `𝓞 K` indexed by `a ∈ (ZMod p)ˣ`,
defined as the image under the corresponding `cyclotomicRingOfIntegersEquiv`. -/
noncomputable def cyclotomicGaloisConjugate
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  Ideal.map (cyclotomicRingOfIntegersEquiv (p := p) K a) q

/-- The Galois conjugate at the identity is the original ideal. -/
@[simp] theorem cyclotomicGaloisConjugate_one (q : Ideal (𝓞 K)) :
    cyclotomicGaloisConjugate (p := p) (K := K) 1 q = q := by
  unfold cyclotomicGaloisConjugate
  apply Ideal.ext
  intro x
  rw [Ideal.mem_map_of_equiv]
  refine ⟨?_, fun hx => ⟨x, hx, ?_⟩⟩
  · rintro ⟨y, hy, hxy⟩
    rw [cyclotomicRingOfIntegersEquiv_one_apply (p := p) (K := K) y] at hxy
    exact hxy ▸ hy
  · exact cyclotomicRingOfIntegersEquiv_one_apply (p := p) (K := K) x

/-- The Galois conjugate is multiplicative in the index: `(ab) · q = a · (b · q)`. -/
theorem cyclotomicGaloisConjugate_mul
    (a b : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    cyclotomicGaloisConjugate (p := p) (K := K) (a * b) q =
      cyclotomicGaloisConjugate (p := p) (K := K) a
        (cyclotomicGaloisConjugate (p := p) (K := K) b q) := by
  unfold cyclotomicGaloisConjugate
  apply Ideal.ext
  intro x
  rw [Ideal.mem_map_of_equiv, Ideal.mem_map_of_equiv]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨cyclotomicRingOfIntegersEquiv (p := p) K b y, ?_, ?_⟩
    · rw [Ideal.mem_map_of_equiv]; exact ⟨y, hy, rfl⟩
    · exact (cyclotomicRingOfIntegersEquiv_mul_apply
        (p := p) (K := K) a b y).symm
  · rintro ⟨z, hz, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, hy,
      cyclotomicRingOfIntegersEquiv_mul_apply (p := p) (K := K) a b y⟩

/-- The Galois conjugate of a prime ideal is prime. -/
instance cyclotomicGaloisConjugate_isPrime
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) [q.IsPrime] :
    (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsPrime := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_isPrime_of_equiv (cyclotomicRingOfIntegersEquiv (p := p) K a)


/-- The Galois conjugate of `⊤` is `⊤`. -/
@[simp] theorem cyclotomicGaloisConjugate_top (a : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) a (⊤ : Ideal (𝓞 K)) = ⊤ := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_top _


/-- The Galois conjugate of a non-`⊥` ideal is non-`⊥`. -/
theorem cyclotomicGaloisConjugate_ne_bot
    (a : CyclotomicUnitDelta p) {q : Ideal (𝓞 K)} (hq : q ≠ ⊥) :
    cyclotomicGaloisConjugate (p := p) (K := K) a q ≠ ⊥ := by
  intro hbot
  apply hq
  have h := cyclotomicGaloisConjugate_mul (p := p) (K := K) a⁻¹ a q
  rw [inv_mul_cancel, cyclotomicGaloisConjugate_one] at h
  rw [h, hbot]
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_bot

/-- The Galois conjugate lies above the same rational prime as `q`. This is
the key compatibility for indexing primes above a rational prime by
elements of `(ZMod p)ˣ`. -/
theorem cyclotomicGaloisConjugate_under_eq
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    (cyclotomicGaloisConjugate (p := p) (K := K) a q).under ℤ =
      q.under ℤ := by
  -- Translate `Ideal.map σ q = Ideal.comap σ.symm q`, then merge nested
  -- `comap`s via `Ideal.comap_comap`. The composite ring hom
  -- `σ.symm.comp (algebraMap ℤ (𝓞 K))` equals `algebraMap ℤ (𝓞 K)` by
  -- uniqueness of `ℤ`-ring homomorphisms (`RingHom.ext_int`).
  unfold cyclotomicGaloisConjugate Ideal.under
  -- Any two ring homs `ℤ → 𝓞 K` agree (`RingHom.ext_int`), so for any
  -- `n : ℤ`, `σ (algebraMap n) = algebraMap n`. From this the membership
  -- condition is equivalent on both sides.
  have h_fix : ∀ n : ℤ,
      cyclotomicRingOfIntegersEquiv (p := p) K a (algebraMap ℤ (𝓞 K) n) =
        algebraMap ℤ (𝓞 K) n := by
    intro n
    have heq : ((cyclotomicRingOfIntegersEquiv (p := p) K a) :
        𝓞 K →+* 𝓞 K).comp (algebraMap ℤ (𝓞 K)) =
          (algebraMap ℤ (𝓞 K)) := RingHom.ext_int _ _
    exact DFunLike.congr_fun heq n
  apply Ideal.ext
  intro n
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_map_of_equiv]
  refine ⟨?_, fun hn => ⟨algebraMap ℤ (𝓞 K) n, hn, h_fix n⟩⟩
  rintro ⟨y, hy, hxy⟩
  -- `hxy : σ y = algebraMap n`, σ injective, σ (algebraMap n) = algebraMap n,
  -- so y = algebraMap n; then hy gives the goal.
  have hsy : y = algebraMap ℤ (𝓞 K) n :=
    (cyclotomicRingOfIntegersEquiv (p := p) K a).injective
      (hxy.trans (h_fix n).symm)
  exact hsy ▸ hy



section FrobeniusFiber

open scoped Pointwise

/-- A cyclotomic conjugate fixes a prime above `ℓ` exactly when its
`(ZMod p)ˣ` index lies in the subgroup generated by the Frobenius class
`ℓ mod p`.

This is the non-split decomposition-group form: the right side is a
`Subgroup.zpowers`, so repeated conjugates are kept as a Frobenius orbit
instead of being forced to be distinct. -/
theorem cyclotomicGaloisConjugate_eq_self_iff_mem_frobenius_zpowers
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ))]
    (hℓp : ℓ.Coprime p) (c : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) c P = P ↔
      c ∈ Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) := by
  have hstab :
      (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) =
        Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) :=
    IsCyclotomicExtension.Rat.galEquivZMod_stabilizer
      (n := p) (K := K) (p := ℓ) (P := P) hℓp
  constructor
  · intro hc
    rw [← hstab, MulEquiv.mapSubgroup_apply, Subgroup.mem_map]
    refine ⟨cyclotomicSigmaOfUnit (p := p) K c, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      change cyclotomicGaloisConjugate (p := p) (K := K) c P = P
      exact hc
    · simpa [cyclotomicGalEquivZMod] using
        cyclotomicGalEquivZMod_sigmaOfUnit (p := p) (K := K) c
  · intro hc
    have hc' :
        c ∈ (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := by
      rwa [hstab]
    rw [MulEquiv.mapSubgroup_apply, Subgroup.mem_map] at hc'
    obtain ⟨σ, hσ, hσc⟩ := hc'
    have hσ_eq : σ = cyclotomicSigmaOfUnit (p := p) K c := by
      rw [cyclotomicSigmaOfUnit, ← hσc]
      exact ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm_apply_apply σ).symm
    rw [hσ_eq] at hσ
    rw [MulAction.mem_stabilizer_iff] at hσ
    change cyclotomicGaloisConjugate (p := p) (K := K) c P = P at hσ
    exact hσ

/-- **Cyclotomic Frobenius fiber theorem.** For a prime `P` of
`𝓞 K` above `ℓ`, the fiber of `b ↦ σ_{b⁻¹} P` over `σ_{a⁻¹} P` is
the Frobenius/decomposition coset generated by `ℓ mod p`.

No residue-degree-one hypothesis appears: if `ℓ` has residue degree
`f > 1`, then the `Subgroup.zpowers` condition records exactly the
collapsed Frobenius orbit, and the Stickelberger product must count the
resulting repeated factors with multiplicity. -/
theorem cyclotomicGaloisConjugate_inv_eq_inv_iff_mul_mem_frobenius_zpowers
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ))]
    (hℓp : ℓ.Coprime p) (a b : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹ P =
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ↔
      a * b⁻¹ ∈ Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) := by
  rw [← cyclotomicGaloisConjugate_eq_self_iff_mem_frobenius_zpowers
    (p := p) (K := K) P hℓp (a * b⁻¹)]
  constructor
  · intro h
    have h' := congrArg
      (fun I : Ideal (𝓞 K) =>
        cyclotomicGaloisConjugate (p := p) (K := K) a I) h
    change cyclotomicGaloisConjugate (p := p) (K := K) a
        (cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹ P) =
      cyclotomicGaloisConjugate (p := p) (K := K) a
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P) at h'
    rw [← cyclotomicGaloisConjugate_mul,
      ← cyclotomicGaloisConjugate_mul, mul_inv_cancel,
      cyclotomicGaloisConjugate_one] at h'
    exact h'
  · intro h
    have h' := congrArg
      (fun I : Ideal (𝓞 K) =>
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ I) h
    change cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        (cyclotomicGaloisConjugate (p := p) (K := K) (a * b⁻¹) P) =
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P at h'
    rw [← cyclotomicGaloisConjugate_mul] at h'
    have hmul : a⁻¹ * (a * b⁻¹) = b⁻¹ := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [hmul] at h'
    exact h'

end FrobeniusFiber

/-- The action distributes over ideal multiplication. -/
theorem cyclotomicGaloisConjugate_mul_ideal
    (a : CyclotomicUnitDelta p) (I J : Ideal (𝓞 K)) :
    cyclotomicGaloisConjugate (p := p) (K := K) a (I * J) =
      cyclotomicGaloisConjugate (p := p) (K := K) a I *
        cyclotomicGaloisConjugate (p := p) (K := K) a J := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_mul _ I J



/-! ### c.1.1 — Galois orbit of a prime ideal -/

/-- The set of Galois conjugates of `q` under the cyclotomic action
indexed by `(ZMod p)ˣ`. Always finite (image of a finite set). -/
noncomputable def cyclotomicConjugates (q : Ideal (𝓞 K)) :
    Finset (Ideal (𝓞 K)) :=
  haveI : DecidableEq (Ideal (𝓞 K)) := Classical.decEq _
  (Finset.univ : Finset (CyclotomicUnitDelta p)).image
    (fun a => cyclotomicGaloisConjugate (p := p) (K := K) a q)


/-- Membership in the conjugate set is exactly being a Galois translate. -/
theorem mem_cyclotomicConjugates_iff (q I : Ideal (𝓞 K)) :
    I ∈ cyclotomicConjugates (p := p) (K := K) q ↔
      ∃ a : CyclotomicUnitDelta p,
        cyclotomicGaloisConjugate (p := p) (K := K) a q = I := by
  classical
  unfold cyclotomicConjugates
  rw [Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, _, ha⟩; exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, Finset.mem_univ _, ha⟩

/-- Every element of the cyclotomic conjugate set is prime. -/
theorem isPrime_of_mem_cyclotomicConjugates
    {q I : Ideal (𝓞 K)} [q.IsPrime]
    (hI : I ∈ cyclotomicConjugates (p := p) (K := K) q) : I.IsPrime := by
  obtain ⟨a, ha⟩ := (mem_cyclotomicConjugates_iff (p := p) (K := K) q I).mp hI
  rw [← ha]
  infer_instance

/-- Every cyclotomic conjugate of `q` lies above the same rational prime. -/
theorem under_eq_of_mem_cyclotomicConjugates
    {q I : Ideal (𝓞 K)}
    (hI : I ∈ cyclotomicConjugates (p := p) (K := K) q) :
    I.under ℤ = q.under ℤ := by
  obtain ⟨a, ha⟩ := (mem_cyclotomicConjugates_iff (p := p) (K := K) q I).mp hI
  rw [← ha]
  exact cyclotomicGaloisConjugate_under_eq a q

/-! ### c.1.2 (preliminary) — Galois transitivity on primes above `ℓ`

Galois transitivity (Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`)
implies that any two prime ideals of `𝓞 K` lying above the same rational
prime are in the same cyclotomic conjugate class. Combined with
`under_eq_of_mem_cyclotomicConjugates` above, this gives an iff.
-/

/-- For any prime `q` of `𝓞 K`, the cyclotomic Galois group acts
transitively on primes of `𝓞 K` lying above `q.under ℤ`.

The Mathlib instance `IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K)` is derived from
`IsGalois ℚ K` (which holds for cyclotomic extensions). Combined with
`Ideal.exists_smul_eq_of_isGaloisGroup`, this gives the transitivity. -/
theorem exists_mem_cyclotomicConjugates_of_under_eq
    {q I : Ideal (𝓞 K)} [hq : q.IsPrime] [hI : I.IsPrime]
    (hqI : q.under ℤ = I.under ℤ) :
    I ∈ cyclotomicConjugates (p := p) (K := K) q := by
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := ({p} : Set ℕ)) ℚ K
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional ({p} : Set ℕ) ℚ K
  haveI : q.LiesOver (q.under ℤ) := ⟨rfl⟩
  haveI : I.LiesOver (q.under ℤ) := ⟨hqI⟩
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup
      (A := ℤ) (B := 𝓞 K) (p := q.under ℤ) (P := q) (Q := I) (G := Gal(K/ℚ))
  refine (mem_cyclotomicConjugates_iff (p := p) (K := K) q I).mpr
    ⟨cyclotomicGalEquivZMod (p := p) K σ, ?_⟩
  have ha : cyclotomicSigmaOfUnit (p := p) K
      (cyclotomicGalEquivZMod (p := p) K σ) = σ := by
    unfold cyclotomicSigmaOfUnit
    exact (cyclotomicGalEquivZMod (p := p) K).symm_apply_apply σ
  unfold cyclotomicGaloisConjugate
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K
        (cyclotomicGalEquivZMod (p := p) K σ) =
      MulSemiringAction.toRingEquiv (Gal(K/ℚ)) (𝓞 K) σ by
    unfold cyclotomicRingOfIntegersEquiv
    rw [ha]]
  exact hσ

/-- Membership in `cyclotomicConjugates q` is equivalent to lying above
the same rational prime as `q`. -/
theorem mem_cyclotomicConjugates_iff_under_eq
    {q I : Ideal (𝓞 K)} [hq : q.IsPrime] [hI : I.IsPrime] :
    I ∈ cyclotomicConjugates (p := p) (K := K) q ↔
      I.under ℤ = q.under ℤ :=
  ⟨under_eq_of_mem_cyclotomicConjugates,
   fun h => exists_mem_cyclotomicConjugates_of_under_eq h.symm⟩




/-! ### c.2 (partial) — Galois-equivariance of `pthSymbolAtPrime`

The full Galois-equivariance statement
`pthSymbolAtPrime (σ_a α) (σ_a • q) = pthSymbolAtPrime α q`
is blocked by the `Classical.choose` of a primitive `p`-th root of unity in
each residue field appearing inside `pthSymbolAtPrime`. Two unrelated
choices in `(𝓞K/q)ˣ` and `(𝓞K/(σ_a q))ˣ` would in general give exponents
differing by a unit factor in `(ZMod p)ˣ`.

This section provides the **conditional** Galois-equivariance: assuming
that the chosen primitive `p`-th roots in the two residue fields are
compatible (i.e., the chosen `ζ` for `σ_a • q` is the image of the chosen
`ζ` for `q` under the quotient ring isomorphism induced by `σ_a`), the
symbols agree. -/






end Furtwaengler

end BernoulliRegular
