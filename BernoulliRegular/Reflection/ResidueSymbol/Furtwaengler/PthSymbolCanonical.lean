module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CanonicalResidueRoot

/-!
# Canonical `pthSymbolAtPrime` and explicit Galois action

This file gives a *canonical* version of `pthSymbolAtPrime` that uses the
canonical primitive `p`-th root of unity `canonicalResidueZetaP q` instead of
`Classical.choose`. The canonical choice is Galois-equivariant in a precise
sense (see `canonicalResidueZetaP_val_galois_compat`), so the Galois-action
transformation of the residue symbol takes the explicit form

```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • q) = (a : ZMod p) * pthSymbolAtPrime_canonical α q.
```

This eliminates the opaque unit factor `c : (ZMod p)ˣ` that appears in the
existence-form `pthSymbolAtPrime_galoisAction_exists_unit`.

## Main definitions and theorems

* `pthSymbolAtPrime_canonical α q` — the residue symbol defined using the
  canonical primitive `p`-th root in `(𝓞 K ⧸ q)ˣ`.
* `pthSymbolAtPrime_canonical_galoisAction` — the explicit Galois-action
  transformation with factor `(a : ZMod p)`.
* `pthSymbolAtPrime_eq_canonical_up_to_unit` — the canonical and
  `Classical.choose`-based versions agree up to a unit factor in `(ZMod p)ˣ`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Step 1 — units-level Galois compatibility

The compatibility statement
`canonicalResidueZetaP_val_galois_compat` is at the level of underlying ring
elements; lifting it to the level of units is mechanical via `Units.ext`. -/


/-! ### Step 2 — `pthSymbolAtPrime_canonical` definition

Like `pthSymbolAtPrime`, this is `0` whenever the preconditions fail. In the
"good" case (`q ≠ ⊥`, maximal, `α ∉ q`, `p ∣ Nq − 1`, `(p : 𝓞 K) ∉ q`) it
equals `primeExponent` with the *canonical* primitive `p`-th root, eliminating
the `Classical.choose`. -/

/-- The canonical `p`-th-power residue symbol at a prime, using
`canonicalResidueZetaP q` as the primitive `p`-th root. The hypothesis
`(p : 𝓞 K) ∉ q` is what guarantees a primitive `p`-th root exists in the
residue field; if it fails the symbol is `0`. -/
noncomputable def pthSymbolAtPrime_canonical (α : 𝓞 K) (q : Ideal (𝓞 K)) :
    ZMod p := by
  classical
  by_cases hbot : q = ⊥
  · exact 0
  haveI : NeZero q := ⟨hbot⟩
  by_cases hmax : q.IsMaximal
  · by_cases hα : α ∈ q
    · exact 0
    by_cases hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1
    · by_cases hp_in : (p : 𝓞 K) ∈ q
      · exact 0
      · haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        haveI : q.IsMaximal := hmax
        haveI : q.IsPrime := hmax.isPrime
        exact Reflection.ResidueSymbol.PowerResidue.primeExponent q
          (canonicalResidueZetaP (p := p) (K := K) q)
          (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
          hdiv α hα
    · exact 0
  · exact 0

/-- Symbol vanishes at the bottom ideal. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_eq_bot (α : 𝓞 K) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α (⊥ : Ideal (𝓞 K)) = 0 := by
  unfold pthSymbolAtPrime_canonical
  rw [dif_pos rfl]

/-- Symbol vanishes when `α ∈ q`. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_mem
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∈ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  unfold pthSymbolAtPrime_canonical
  rw [dif_neg hbot, dif_pos hmax, dif_pos hα]


/-- Symbol vanishes for non-maximal `q ≠ ⊥`. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal
    (α : 𝓞 K) {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : ¬ q.IsMaximal) :
    pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
  unfold pthSymbolAtPrime_canonical
  rw [dif_neg hbot, dif_neg hmax]





/-- In the "good" case (all preconditions met, including `(p : 𝓞 K) ∉ q`),
the canonical symbol unfolds to `primeExponent` with the canonical zeta. -/
theorem pthSymbolAtPrime_canonical_eq_primeExponent
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hp_in : (p : 𝓞 K) ∉ q) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : NeZero q := ⟨hbot⟩
    haveI : q.IsMaximal := hmax
    haveI : q.IsPrime := hmax.isPrime
    pthSymbolAtPrime_canonical (p := p) (K := K) α q =
      Reflection.ResidueSymbol.PowerResidue.primeExponent q
        (canonicalResidueZetaP (p := p) (K := K) q)
        (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in) hdiv α hα := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hbot⟩
  unfold pthSymbolAtPrime_canonical
  rw [dif_neg hbot, dif_pos hmax, dif_neg hα, dif_pos hdiv, dif_neg hp_in]

/-! ### Step 2b — algebraic API: `_one`, `_mul`, `_pow`, `_pow_p_eq_zero`

Mirrors the API for non-canonical `pthSymbolAtPrime` (`_one`, `_mul`, `_pow`,
`_pow_p_eq_zero`). The canonical version is well-behaved for the same reasons:
in the bad branches everything is `0`; in the good branch the same canonical
ζ is used for both sides, so the lemmas reduce to `primeExponent_one`,
`primeExponent_mul`, `primeExponent_pow` from `Reflection/ResidueSymbol/Basic.lean`. -/


/-- Multiplicativity of the canonical residue symbol in `α`. For `q` a maximal
non-zero ideal of `𝓞 K` and `α, β ∉ q`, the canonical symbol satisfies
`pthSymbolAtPrime_canonical (α * β) q =
  pthSymbolAtPrime_canonical α q + pthSymbolAtPrime_canonical β q`. -/
theorem pthSymbolAtPrime_canonical_mul
    {α β : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q) (hβ : β ∉ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (α * β) q =
      pthSymbolAtPrime_canonical (p := p) (K := K) α q +
        pthSymbolAtPrime_canonical (p := p) (K := K) β q := by
  haveI : NeZero q := ⟨hbot⟩
  haveI hqK_prime : q.IsPrime := hmax.isPrime
  have hαβ : α * β ∉ q := fun h => (hqK_prime.mem_or_mem h).elim hα hβ
  simp only [pthSymbolAtPrime_canonical, dif_neg hbot, dif_pos hmax, dif_neg hαβ,
    dif_neg hα, dif_neg hβ]
  split_ifs with hdiv hp_in
  · simp
  · -- Good case: apply primeExponent_mul.
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : q.IsMaximal := hmax
    exact Reflection.ResidueSymbol.PowerResidue.primeExponent_mul q
      (canonicalResidueZetaP (p := p) (K := K) q)
      (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
      hdiv hα hβ hαβ
  · simp

/-- The canonical symbol vanishes at `1`. Follows from multiplicativity:
`s(1·1) = s(1) + s(1)` forces `s(1) = 0`. -/
theorem pthSymbolAtPrime_canonical_one
    {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (1 : 𝓞 K) q = 0 := by
  haveI hqp : q.IsPrime := hmax.isPrime
  have h1 : (1 : 𝓞 K) ∉ q := hqp.one_notMem
  have h := pthSymbolAtPrime_canonical_mul (p := p) (K := K)
    (α := (1 : 𝓞 K)) (β := 1) hbot hmax h1 h1
  rw [one_mul] at h
  linear_combination -h

/-- The canonical symbol of `α^n` is `n · symbol α q` in `ZMod p`. By induction
using `pthSymbolAtPrime_canonical_mul`. -/
theorem pthSymbolAtPrime_canonical_pow
    {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q) (n : ℕ) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (α ^ n) q =
      (n : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  haveI hqp : q.IsPrime := hmax.isPrime
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact pthSymbolAtPrime_canonical_one (p := p) (K := K) hbot hmax
  | succ k ih =>
    have hpow : α ^ k ∉ q := fun h => hα (hqp.mem_of_pow_mem k h)
    rw [pow_succ, pthSymbolAtPrime_canonical_mul (p := p) (K := K) hbot hmax hpow hα,
      ih]
    push_cast; ring



/-! ### Step 2c — bidirectional vanishing iff and congruence helpers -/





/-! ### Step 3 — explicit Galois action

The canonical zeta is Galois-equivariant up to a `(.val)`-power exponent
(`canonicalResidueZetaP_val_galois_compat`). Combined with
`primeExponent_ringEquiv` and `primeExponent_zeta_pow`, this gives the
explicit form:

```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • q) = (a : ZMod p) * pthSymbolAtPrime_canonical α q.
```

The proof is the chain
`primeExponent σq canonicalZetaSigmaQ (σα) =`
`(a.val : ZMod p) * primeExponent σq (canonicalZetaSigmaQ^a.val) (σα)`
`  [primeExponent_zeta_pow]`
`= (a.val : ZMod p) * primeExponent σq (Units.mapEquiv σ_q canonicalZetaQ) (σα)`
`  [units_galois_compat]`
`= (a.val : ZMod p) * primeExponent q canonicalZetaQ α [primeExponent_ringEquiv]`. -/


/-! ### Step 3b — corollaries of the explicit Galois action

Variants and consequences of `pthSymbolAtPrime_canonical_galoisAction`:
* `_galoisAction_iff` — the equation is an iff (one of three equivalent forms).
* `_galoisAction_one` — at the identity element of the Galois group, the action
  is trivial: it amounts to `pthSymbolAtPrime_canonical α q`.
* `_compose_galois` — composing two Galois actions multiplies the factors.
-/




/-! ### Step 4 — compatibility with `pthSymbolAtPrime`

The canonical and `Classical.choose`-based versions agree up to a unit factor
in `(ZMod p)ˣ`. Concretely: `Classical.choose hroot` is some primitive `p`-th
root of unity in `(𝓞 K ⧸ q)ˣ`, and `canonicalResidueZetaP q` is another. By
`IsPrimitiveRoot.isPrimitiveRoot_iff'` the two differ by an `n`-th power for
some `n.Coprime p`, and the residue exponents are related by multiplication
by `(n : ZMod p)`. -/


/-! ### Step 5 — vanishing-bridge lemmas between the two versions

When `pthSymbolAtPrime_canonical α q = 0`, the corresponding
`pthSymbolAtPrime α q = 0` as well (via the unit factor `c`), and conversely
since the unit factor is invertible. These bridge "vanishing on the canonical
side" and "vanishing on the non-canonical side" without needing to know what
the unit factor is. -/




end Furtwaengler

end BernoulliRegular
