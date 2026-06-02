module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.GaussSum
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Stickelberger.Part1

/-!
# Stickelberger-style prime factorisation of `g(χ_q)^p` (REF-18c2c)

This file develops the Stickelberger-type theorem for the residue Gauss sum
`g(χ_q, ψ_q)` raised to its character order. The classical statement
(Ireland–Rosen Thm 14.5) gives the explicit prime factorisation of
`g(χ_q)^p` in `𝓞_{K(ζ_{Nq})}`, with exponents controlled by the
Stickelberger weight. We work in stages:

1. **Galois invariance of `g(χ)^n`** (this commit).
   For χ a multiplicative character of order dividing `n`, and a ring hom
   `σ : R' →+* R'` that *fixes* χ (`σ ∘ χ = χ`) and shifts the additive
   character ψ by some `a ∈ Rˣ` (`σ ∘ ψ = AddChar.mulShift ψ a`), the `n`-th
   power `g(χ, ψ)^n` is fixed by `σ`. Proof: `g(χ, AddChar.mulShift ψ a)^n` is
   `(χ a)⁻ⁿ · g(χ, ψ)^n` by `gaussSum_mulShift` raised to `n`, and
   `(χ a)^n = (χ^n) a = 1 a = 1` because `χ^n = 1`.

2. **Application to residue Gauss sums** (this commit).
   For `χ_q` of order `p` (residue character) and any Galois automorphism
   `σ` fixing `K = ℚ(ζ_p)` pointwise (so `σ ∘ χ_q = χ_q`), `g(χ_q, ψ_q)^p`
   is fixed by `σ`.

3. **Prime factorisation via Stickelberger weight** (deferred).
   The actual Stickelberger formula `g(χ_q)^p = q^{p-1} · ∏ σ_a^{?}`
   requires the explicit Galois-orbit computation and Jacobi-sum
   factorisation. This is the core of REF-18c2c and is left for follow-up
   commits.

The Galois-invariance step is small but essential: it shows that
`g(χ_q, ψ_q)^p` *descends* from the larger ring `R' = K(ζ_{Nq})` to the
fixed field of the appropriate Galois group, which in our application
will be `K = ℚ(ζ_p)`. This is the key feature exploited by the
Stickelberger formula's prime factorisation.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

variable {R : Type*} [CommRing R] [Fintype R]
variable {R' : Type*} [CommRing R']



/-- **Helper.** If `d` divides every term of a finite product, then `d^n`
divides the product, where `n` is the cardinality of the index set. -/
private lemma Finset.pow_card_dvd_prod_of_each {α β : Type*} [CommMonoid β]
    {s : Finset α} {f : α → β} {d : β} (h : ∀ i ∈ s, d ∣ f i) :
    d ^ s.card ∣ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ,
      mul_comm (d ^ s.card) d]
    exact mul_dvd_mul
      (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))



/-!
### Modulo `Q^2` reduction (REF-18c2c4 — Phase C precursor)

The Taylor expansion of `x^n` near `x = 1`: if `x - 1 ∈ I` for some ideal `I`,
then `x^n - 1 ≡ n · (x - 1) (mod I^2)`. This is the key algebraic input for
the modulo-Q² reduction of the Gauss sum, which feeds the exact q-adic
valuation calculation in Phase C.
-/





/-!
### Combined ord_I = 1 statement (REF-18c2c4 — Phase B + C synthesis)

The combination of Phase B (`g(χ_q) ∈ I`) and Phase C
(`g(χ_q) ∉ I²` under non-degeneracy) gives the q-adic valuation `= 1`
statement at the abstract level. In a Dedekind context this is exactly
`ord_I(g(χ_q)) = 1`; in a general CommRing it captures the same content
as the conjunction `g ∈ I ∧ g ∉ I²`.

The bridge to the Stickelberger weight `(q^f - 1)/p`: the value `1` here
is the f=1 case of the weight; for general `f`, the weight is `f`-times
larger and requires recursive application of the same modulo-Q² argument
(or alternatively, computation of the Jacobi-sum closed form). -/


end Furtwaengler

end BernoulliRegular
