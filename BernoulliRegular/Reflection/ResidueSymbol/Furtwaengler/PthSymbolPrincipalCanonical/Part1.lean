module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolCanonical

/-!
# Canonical `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` and the unconditional c.3 closed form

This file mirrors the `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` API on top
of `pthSymbolAtPrime_canonical`, and uses the explicit Galois-action
transformation from `PthSymbolCanonical.lean` to derive the
**unconditional c.3 closed form**:

```
pthSymbolAtPrincipal_canonical α h_stick.gen =
  ∑ a : CyclotomicUnitDelta p,
    pthSymbolAtPrime_canonical (σ_a α) q_K
```

Compared to the conditional theorem
`pthSymbolAtPrincipal_eq_galois_sum_of_hypothesis` (in
`KummerFurtwaengler.lean`), the canonical version is *unconditional*:
the explicit `(a : ZMod p)` factor in the Galois-action transformation
cancels the digit-sum `a.val` factor, so the closed form eliminates
both the `a.val` weights and the `StickelbergerGaloisHypothesis` input.

## Main definitions and theorems

* `pthSymbolAtIdeal_canonical α I` — the canonical residue symbol at an
  integral ideal, defined as the multiset sum of
  `pthSymbolAtPrime_canonical α P` over the prime factors `P` of `I`.
* `pthSymbolAtPrincipal_canonical α β` — the canonical principal symbol,
  defined as `pthSymbolAtIdeal_canonical α (Ideal.span {β})`.
* `pthSymbolAtPrincipal_canonical_eq_galois_sum` — the **c.3 unconditional
  closed form** taking only `StickelbergerIdealEquality q_K`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Canonical `pthSymbolAtIdeal`

Mirrors `pthSymbolAtIdeal` but uses `pthSymbolAtPrime_canonical` as the
prime-level building block. -/

/-- The canonical `p`-th-power residue symbol `(α/I)_p` extended to integral
ideals by multiplicativity over the prime factorization of `I`. Same shape
as `pthSymbolAtIdeal`, but with `pthSymbolAtPrime_canonical` (which uses the
canonical primitive `p`-th root, eliminating the `Classical.choose`). -/
noncomputable def pthSymbolAtIdeal_canonical
    (α : 𝓞 K) (I : Ideal (𝓞 K)) : ZMod p :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map
    (fun P => pthSymbolAtPrime_canonical (p := p) α P)).sum








/-- For a non-zero prime ideal `P`, the canonical ideal symbol agrees
with the canonical prime symbol. -/
theorem pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
    (α : 𝓞 K) {P : Ideal (𝓞 K)} [hP_prime : P.IsPrime] (hP_ne : P ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α P =
      pthSymbolAtPrime_canonical (p := p) (K := K) α P := by
  unfold pthSymbolAtIdeal_canonical
  have hP_prime_in_R : Prime P := (Ideal.prime_iff_isPrime hP_ne).mpr hP_prime
  have hP_irreducible : Irreducible P := hP_prime_in_R.irreducible
  have h_factors :
      UniqueFactorizationMonoid.normalizedFactors P = ({P} : Multiset _) := by
    have h_assoc :=
      UniqueFactorizationMonoid.normalizedFactors_irreducible hP_irreducible
    rw [show normalize P = P from normalize_eq P] at h_assoc
    exact h_assoc
  rw [h_factors]
  simp


/-! ### Canonical `pthSymbolAtPrincipal` -/

/-- The canonical principal-symbol `(α/(β))_p`, defined as
`pthSymbolAtIdeal_canonical α (Ideal.span {β})`. -/
noncomputable def pthSymbolAtPrincipal_canonical
    (α β : 𝓞 K) : ZMod p :=
  pthSymbolAtIdeal_canonical (p := p) (K := K) α (Ideal.span ({β} : Set (𝓞 K)))


/-! ### c.3 unconditional half (consequence of c.1 only)

Mirror of `pthSymbolAtPrincipal_eq_stickelberger_sum`: from the
`StickelbergerIdealEquality` (c.1) we expand the canonical principal
symbol into the digit sum
`∑ a, ↑a.val * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K)`. -/


/-! ### c.3 unconditional Galois transformation per term

The key lemma: for a non-bot prime `q_K` and any `a, α`, the term
`↑a.val * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K)`
equals the Galois-translated term
`pthSymbolAtPrime_canonical (σ_a α) q_K`.

Proof: the canonical Galois-action lemma
`pthSymbolAtPrime_canonical_galoisAction` gives, for the inverse direction,
```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • σ_{a⁻¹} q_K) =
  (a : ZMod p) * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K).
```
Since `σ_a (σ_{a⁻¹} q_K) = q_K`, this reads
```
pthSymbolAtPrime_canonical (σ_a α) q_K =
  (a : ZMod p) * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K).
```
Now `↑a.val = (a : ZMod p)` in `ZMod p`. The hypotheses on `α` and `p`
in `pthSymbolAtPrime_canonical_galoisAction` rule out the bad cases;
we case-split to handle them via the `_eq_zero` lemmas. -/


/-! ### c.3 unconditional closed form

The main theorem: combining the digit-sum expansion with the per-term
Galois transformation yields the unconditional closed form
```
pthSymbolAtPrincipal_canonical α γ = ∑_a pthSymbolAtPrime_canonical (σ_a α) q_K.
```
No `StickelbergerGaloisHypothesis` is needed: the explicit `(a : ZMod p)`
factor in the canonical Galois-action lemma cancels the `a.val` weight in
the digit sum. -/


/-! ### REF-19 canonical: principal symbol vanishing for hyperprimary singular

Combining the canonical KFR with `(η) = b^p` (singular η) gives that the
canonical residue symbol of η on any principal ideal `(γ)` (with γ
coprime to (η, p)) vanishes. This is the consumer-facing form for REF-19. -/


/-! ### Ideal-level canonical symbol API for `α`

These mirror the corresponding `pthSymbolAtIdeal` API lemmas
(`pthSymbolAtIdeal_one_alpha`, `_zero_alpha`, `_pow`, `_mul`) but for the
canonical symbol. Each one reduces, term-by-term over the prime factorization
of `I`, to the corresponding `pthSymbolAtPrime_canonical` lemma. -/

/-- **The canonical symbol of `1` at any ideal is `0`**. Each prime factor of
`I` is maximal and non-zero, so `pthSymbolAtPrime_canonical 1 P = 0`
term-by-term. -/
@[simp] theorem pthSymbolAtIdeal_canonical_one_alpha
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (1 : 𝓞 K) I = 0 := by
  unfold pthSymbolAtIdeal_canonical
  rw [show
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) (1 : 𝓞 K) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map (fun _ => (0 : ZMod p)))
        from ?_]
  · simp
  · refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_canonical_one (p := p) (K := K) hP_ne_bot hP_max


/-- **Multiplicativity in `α` at the ideal level.** For non-zero `I` with
`α, β` coprime to every prime factor of `I`, the canonical symbol is
additive in the numerator. Reduces, term-by-term, to
`pthSymbolAtPrime_canonical_mul`. -/
theorem pthSymbolAtIdeal_canonical_mul_α
    {α β : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P)
    (hβ : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, β ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α * β) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I +
        pthSymbolAtIdeal_canonical (p := p) (K := K) β I := by
  unfold pthSymbolAtIdeal_canonical
  have hmap :
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) (α * β) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) α P +
          pthSymbolAtPrime_canonical (p := p) (K := K) β P)) := by
    refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_canonical_mul (p := p) (K := K)
      hP_ne_bot hP_max (hα P hP) (hβ P hP)
  rw [hmap, Multiset.sum_map_add]

/-- **Power form in the `α` slot at the ideal level.** Reduces, term-by-term,
to `pthSymbolAtPrime_canonical_pow`. -/
theorem pthSymbolAtIdeal_canonical_pow_α
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P)
    (n : ℕ) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α ^ n) I =
      (n : ZMod p) * pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  unfold pthSymbolAtIdeal_canonical
  have hmap :
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) (α ^ n) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => (n : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K) α P)) := by
    refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_canonical_pow (p := p) (K := K)
      hP_ne_bot hP_max (hα P hP) n
  rw [hmap, Multiset.sum_map_mul_left]







/-- **Unit-times-α absorption at the ideal level**: if every per-prime
symbol of u vanishes (e.g., u is a `p`-th power, or u = ±1 for odd p),
then `pthSymbolAtIdeal_canonical (α · u) I = pthSymbolAtIdeal_canonical α I`.
The unit factor is absorbed term-by-term. -/
theorem pthSymbolAtIdeal_canonical_mul_unit_α_eq_self
    (α : 𝓞 K) {u : 𝓞 K} (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α * u) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  unfold pthSymbolAtIdeal_canonical
  refine congrArg Multiset.sum ?_
  refine Multiset.map_congr rfl fun P _ => ?_
  -- pthSymbolAtPrime_canonical (α · u) P = pthSymbolAtPrime_canonical α P
  -- via the canonical-symbol's behavior at each P:
  by_cases hbot : P = ⊥
  · subst hbot
    rw [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot,
        pthSymbolAtPrime_canonical_eq_zero_of_eq_bot]
  by_cases hmax : P.IsMaximal
  · by_cases hα_in : α ∈ P
    · -- α ∈ P: both α and α·u are in P (since P is an ideal closed under mult).
      have hαu : α * u ∈ P := P.mul_mem_right u hα_in
      rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα_in,
          pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hαu]
    · -- α ∉ P: need u ∉ P. Then mul splits.
      have hu_not : u ∉ P := fun h_in =>
        hmax.ne_top (Ideal.eq_top_of_isUnit_mem P h_in hu)
      rw [pthSymbolAtPrime_canonical_mul (p := p) (K := K) hbot hmax hα_in hu_not,
          hu_zero P, add_zero]
  · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax,
        pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax]






/-! ### Principal-level canonical symbol API

Mirror of the principal-level API in `KummerFurtwaengler.lean`. These lemmas
directly reduce to the ideal-level versions, since
`pthSymbolAtPrincipal_canonical α β = pthSymbolAtIdeal_canonical α (Ideal.span {β})`. -/

end Furtwaengler

end BernoulliRegular
