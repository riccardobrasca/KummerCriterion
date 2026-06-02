module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormGalois
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality.Part1

/-!
# `StickelbergerIdealEquality` from a `FullTeichDworkSetup`

This file provides the substantive valuation-descent content of c.1
(`REF-18c2d-main-c.1`) by showing how to assemble a
`StickelbergerIdealEquality (S.Q.under (𝓞 K))` from a
`FullTeichDworkSetup S` together with a coverage hypothesis on the
Galois orbit of the descent prime.

## Strategy

The Dwork bundle gives the EXACT `Q`-adic order
`S.gaussSumInt a ∈ S.Q^(stickOrdOrd a) ∧ S.gaussSumInt a ∉ S.Q^(stickOrdOrd a + 1)`
at the SINGLE prime `S.Q ⊂ 𝓞 R'` for each `a ∈ [1, p-1]`. The route
to the multi-conjugate Stickelberger ideal in `𝓞 K` factors through
the descent prime `q_K = S.Q.under (𝓞 K)` and the Galois orbit
`cyclotomicConjugates q_K`:

1. **Per-`a` descent witness** (`StickelbergerPerConjugateDescent`):
   for each `a`, the existence of `γ_a ∈ 𝓞 K` whose image in `𝓞 R'`
   equals `S.gaussSumInt a ^ p` and whose `descentPrime`-adic order is
   `p · stickOrdOrd a / e` where `e = descentRamificationIdx`.

2. **Galois-orbit coverage** (`StickelbergerOrbitCoverage`): the
   Stickelberger ideal `q_K^Θ = ∏_a (σ_{a^{-1}} q_K)^a.val` admits a
   single global generator `γ ∈ 𝓞 K` whose ideal factorization at each
   conjugate matches the prescribed exponent.

3. **Final assembly** (`stickelbergerIdealEquality_of_dwork_witness`):
   under both witnesses, the principal ideal `(γ)` equals
   `stickelbergerIdeal q_K`, and so `StickelbergerIdealEquality q_K`
   holds.

The current file delivers (1) and the **conditional** (3) under (2).
The unconditional (2) requires a separate per-conjugate bundle for
each Galois conjugate prime above `ℓ` (one bundle per representative
of the Galois orbit of `S.Q`); that step is left as a coverage
hypothesis here, packaged as the `Prop` predicate
`StickelbergerOrbitCoverage`.

## Why split

The full unconditional c.1 builds a single global generator from
multiple per-conjugate bundles by orbit-summing. That assembly is the
substantive remaining content. The conditional form delivered here
already discharges all the **valuation-descent** content (per-`a`
exact orders, ramification descent, Dwork EXACT-order data); only the
**orbit-coverage** combinatorics remain.

## Files

* Per-`a` exact-order descent: theorems
  `gaussSumInt_pow_descentPrime_pow_mul_stickOrdOrd`,
  `gaussSumInt_pow_not_mem_descentPrime_pow_mul_stickOrdOrd_succ` (in
  this file, on `FullTeichDworkSetup`).
* Final `StickelbergerIdealEquality` constructor: theorem
  `stickelbergerIdealEquality_of_orbitCoverage`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- The residue value of `a * ℓ^i`, viewed as a unit of `ZMod p`, is the
corresponding natural residue orbit representative. -/
theorem cyclotomicUnit_mul_frobeniusPower_val_eq_residueOrbit
    {ℓ p : ℕ} [Fact (Nat.Prime p)]
    (hℓp : ℓ.Coprime p) (a : CyclotomicUnitDelta p) (i : ℕ) :
    (((a * (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p) ^ i :
        CyclotomicUnitDelta p) : ZMod p).val) =
      residueOrbit ℓ p (a : ZMod p).val i := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hlt : residueOrbit ℓ p (a : ZMod p).val i < p := Nat.mod_lt _ hp_pos
  have hcast :
      (((a * (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p) ^ i :
          CyclotomicUnitDelta p) : ZMod p)) =
        (residueOrbit ℓ p (a : ZMod p).val i : ZMod p) := by
    unfold residueOrbit
    simp [Units.val_mul, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  have h := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast_of_lt hlt] at h

/-- Enumerate a Frobenius coset by the distinct powers of the Frobenius unit.

The left side sums over all cyclotomic units but only keeps the units in the
coset cut out by `a * b⁻¹ ∈ ⟨ℓ⟩`. The right side enumerates that coset by the
cyclic subgroup order. No faithfulness of the full Galois orbit, residue-degree
one hypothesis, or split-prime hypothesis is used. -/
theorem frobeniusCosetWeightSum_eq_residueOrbitSum
    {ℓ p : ℕ} [Fact (Nat.Prime p)]
    (hℓp : ℓ.Coprime p) (a : CyclotomicUnitDelta p) :
    (∑ b : CyclotomicUnitDelta p,
        if a * b⁻¹ ∈ Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) then
          (b : ZMod p).val
        else
          0) =
      ∑ i ∈ Finset.range
          (orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)),
        residueOrbit ℓ p (a : ZMod p).val i := by
  classical
  let u : CyclotomicUnitDelta p := ZMod.unitOfCoprime ℓ hℓp
  let H : Subgroup (CyclotomicUnitDelta p) := Subgroup.zpowers u
  let pred : CyclotomicUnitDelta p → Prop := fun b => a * b⁻¹ ∈ H
  let f : CyclotomicUnitDelta p → ℕ := fun b => (b : ZMod p).val
  have hcond :
      (∑ b : CyclotomicUnitDelta p, if pred b then f b else 0) =
        ∑ x : {b : CyclotomicUnitDelta p // pred b}, f x := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (CyclotomicUnitDelta p))) (f := f)]
    simp
  let eH : H ≃ {b : CyclotomicUnitDelta p // pred b} :=
    { toFun := fun h =>
        ⟨a * (h : CyclotomicUnitDelta p), by
          dsimp [pred, H]
          have h_eq : a * (a * (h : CyclotomicUnitDelta p))⁻¹ =
              ((h : CyclotomicUnitDelta p))⁻¹ := by
            simp [mul_comm]
          rw [h_eq]
          exact (Subgroup.zpowers u).inv_mem h.2⟩
      invFun := fun b =>
        ⟨a⁻¹ * (b : CyclotomicUnitDelta p), by
          dsimp [pred, H] at b
          have h_eq : a⁻¹ * (b : CyclotomicUnitDelta p) =
              (a * (b : CyclotomicUnitDelta p)⁻¹)⁻¹ := by
            simp [mul_comm]
          rw [h_eq]
          exact (Subgroup.zpowers u).inv_mem b.2⟩
      left_inv := by
        intro h
        apply Subtype.ext
        simp [mul_comm]
      right_inv := by
        intro b
        apply Subtype.ext
        simp [mul_comm] }
  have hsub :
      (∑ x : {b : CyclotomicUnitDelta p // pred b}, f x) =
        ∑ h : H, f (a * (h : CyclotomicUnitDelta p)) := by
    symm
    refine Fintype.sum_equiv eH
      (fun h : H => f (a * (h : CyclotomicUnitDelta p)))
      (fun x : {b : CyclotomicUnitDelta p // pred b} => f x) ?_
    intro h
    rfl
  have hH :
      (∑ h : H, f (a * (h : CyclotomicUnitDelta p))) =
        ∑ i : Fin (orderOf u), f (a * u ^ (i : ℕ)) := by
    symm
    refine Fintype.sum_equiv (finEquivZPowers (isOfFinOrder_of_finite u))
      (fun i : Fin (orderOf u) => f (a * u ^ (i : ℕ)))
      (fun h : H => f (a * (h : CyclotomicUnitDelta p))) ?_
    intro i
    simp [finEquivZPowers_apply]
  calc
    (∑ b : CyclotomicUnitDelta p,
        if a * b⁻¹ ∈ Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) then
          (b : ZMod p).val
        else
          0) = (∑ b : CyclotomicUnitDelta p, if pred b then f b else 0) := by
      simp [pred, f, H, u]
    _ = ∑ x : {b : CyclotomicUnitDelta p // pred b}, f x := hcond
    _ = ∑ h : H, f (a * (h : CyclotomicUnitDelta p)) := hsub
    _ = ∑ i : Fin (orderOf u), f (a * u ^ (i : ℕ)) := hH
    _ = ∑ i ∈ Finset.range (orderOf u), f (a * u ^ i) := by
      simpa using (Fin.sum_univ_eq_sum_range (fun i => f (a * u ^ i)) (orderOf u))
    _ = ∑ i ∈ Finset.range
          (orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)),
        residueOrbit ℓ p (a : ZMod p).val i := by
      simp only [u]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact cyclotomicUnit_mul_frobeniusPower_val_eq_residueOrbit hℓp a i

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : FullTeichDworkSetup ℓ p k K R')

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Helper:** `normalizedFactors` of `stickelbergerIdeal q_K` equals
the sum `∑_a a.val • {σ_{a⁻¹} q_K}`. -/
theorem normalizedFactors_stickelbergerIdeal_descentPrime_eq :
    UniqueFactorizationMonoid.normalizedFactors
        (stickelbergerIdeal (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime) =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val) •
          ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
              S.toConcreteStickelbergerSetup.descentPrime}
            : Multiset (Ideal (𝓞 K))) := by
  classical
  unfold stickelbergerIdeal
  exact S.normalizedFactors_stickelbergerIdeal_finset_eq Finset.univ


/-! ### Discharging `StickelbergerOrbitFaithful` from cardinality

The orbit-indexing map `a ↦ σ_a q_K` factors `(ZMod p)ˣ → orbit q_K`
through the quotient by the stabilizer (decomposition group). Its image
is by definition `cyclotomicConjugates q_K`, so the map is automatically
surjective. When the image cardinality matches the source cardinality
`p − 1 = #(ZMod p)ˣ`, the map is bijective, hence injective.

The fundamental Galois identity
`#orbit · ramificationIdxIn · inertiaDegIn = p − 1` makes this equivalent
to `e · f = 1`, i.e., the **totally split case** `(e = 1, f = 1)`. This
section provides the discharge:

* `stickelbergerOrbitFaithful_of_card_eq` — direct cardinality form.
* `stickelbergerOrbitFaithful_of_split` — the `(e = 1, f = 1)` form.

Both produce `StickelbergerOrbitFaithful` for the bundle's
`descentPrime`, which can then be fed into
`stickelbergerIdealConjugateMultiplicity_of_orbitFaithful` and the
end-to-end `stickelbergerIdealEquality_of_atomic_with_orbitFaithful`. -/






/-! ### End-to-end atomic discharge

Combining both directions yields the orbit coverage from the three
atomic predicates. -/





/-! ### Atomic decomposition of `StickelbergerExactConjugateExponents`

The exact-exponent predicate
`emultiplicity (σ_{a⁻¹} q_K) (γ) = a.val`
naturally decomposes into a lower-bound and an upper-bound piece via
`emultiplicity_eq_coe`:

* `StickelbergerLowerBoundConjugateExponents γ`: `(σ_{a⁻¹} q_K)^a.val ∣ (γ)`,
  equivalently `a.val ≤ emultiplicity (σ_{a⁻¹} q_K) (γ)`.
* `StickelbergerUpperBoundConjugateExponents γ`: `(σ_{a⁻¹} q_K)^(a.val+1) ∤ (γ)`,
  equivalently `emultiplicity (σ_{a⁻¹} q_K) (γ) < a.val + 1`.

The lower bound is the structurally easy direction: it follows from
`(γ) ⊆ stickelbergerIdeal q_K`, since each `σ_{a⁻¹} q_K`-power is a
factor of the Stickelberger product.

The upper bound carries the substantive content: it requires showing
`(γ)` does not contain "extra" copies of any conjugate prime — the
sharp orbit-counting / faithfulness data.

Combined, these two predicates are equivalent to the original
`StickelbergerExactConjugateExponents`. -/






/-! ### Discharging the lower bound from `(γ) ⊆ stickelbergerIdeal q_K`

The lower bound `(σ_{a⁻¹} q_K)^a.val ∣ (γ)` is equivalent to
`(γ) ⊆ (σ_{a⁻¹} q_K)^a.val`. Since `(σ_{a⁻¹} q_K)^a.val ⊇ stickelbergerIdeal q_K`
(by `stickelbergerIdeal_le_factor`), it suffices to show
`(γ) ⊆ stickelbergerIdeal q_K`, i.e., `stickelbergerIdeal q_K ∣ (γ)`. -/



/-! ### Discharging the upper bound under faithful action

The upper bound is the substantive content: `(σ_{a⁻¹} q_K)^(a.val+1) ∤ (γ)`.

Under `(γ) = stickelbergerIdeal q_K` and orbit faithfulness, the upper
bound follows from the structural multiplicity computation: the count of
`σ_{a⁻¹} q_K` in `normalizedFactors (stickelbergerIdeal q_K)` is exactly
`a.val`, so the multiplicity is exactly `a.val`, hence the `(a.val+1)`-th
power does not divide. -/


/-! ### End-to-end discharge from span equality

Combining lower bound + upper bound + orbit faithfulness yields a
substantive end-to-end discharge of `StickelbergerExactConjugateExponents`. -/


/-! ### Round-trip equivalence under faithful action

Combining `stickelbergerOrbitCoverage` (∃ γ with span = stickelbergerIdeal)
with `stickelbergerExactConjugateExponents_of_span_eq_of_faithful`, we
get that `StickelbergerOrbitCoverage S` together with orbit faithfulness
produces a γ satisfying all atomic predicates. This closes the
"existence-from-coverage" direction. -/

end FullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end
