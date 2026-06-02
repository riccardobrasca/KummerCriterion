module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-!
## Dwork splitting layer (REF-18c2c4-L2c3d-4a)

The `FullTeichDworkSetup` extends `FullTeichStickelbergerSetup` with
finite-precision Dwork splitting coefficients `λ_{N,n}`.  The target
precision `N` is part of the data because Artin–Hasse coefficients are
naturally local at `Q`: a rational denominator prime to `Q` can be inverted
modulo `Q^(N+1)`, but need not have one globally integral inverse working at
every precision.  The bundle stages three properties of these coefficients as
hypotheses:

1. `λ_{N,n} ∈ Q^n` (so the multi-index expansion lands in `Q^{|m|}` without
   needing a separate `π^{|m|}` factor);
2. for `n ≤ N` and `n < ℓ`, `n! · λ_{N,n} ≡ π^n (mod Q^{n+1})`
   (leading-coefficient identity, used to recover the classical
   `π^s / ∏ a_i!` form);
3. the per-`y` factorization
   `ψ(y) ≡ ∑_{m, |m| ≤ N} (∏_i λ_{N,m_i}) · ω(y)^{M(m)} (mod Q^{N+1})`
   for any truncation `N`, expressing the trace-form additive character
   as a Dwork-style multi-index expansion.

The eventual concrete construction (Artin–Hasse exponential over
`R' = ℚ(ζ_{ℓ(q-1)})`) is deferred; at this layer we only stage the data.
-/

/-! ### Conductor-flexible full-Teich/Dwork API -/

end Furtwaengler

end BernoulliRegular
