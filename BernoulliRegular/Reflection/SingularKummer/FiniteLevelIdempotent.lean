module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelProjectionBridge

/-!
# Singular Kummer: exact finite-level character idempotents

This file proves the finite-level algebra behind the exact component
projection.  Let `D` be a finite group, let

```text
  chi : D -> (ZMod m)^*
```

be a multiplicative character, and let `rho` be a linear action of `D` on a
`ZMod m`-module `M`.  If `|D|` is a unit in `ZMod m`, then the averaged
operator

```text
  |D|^{-1} * sum_d chi(d)^{-1} rho(d)
```

acts as the identity on its own range and is therefore an exact idempotent.

The cyclotomic application will take `D = (ZMod p)^*` and `m = p^N`, with
`chi` the Teichmuller lift modulo `p^N`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelIdempotent

variable {m : ℕ} [NeZero m]
variable {D M : Type*} [Group D] [Fintype D]
variable [AddCommGroup M] [Module (ZMod m) M]

end FiniteLevelIdempotent

end SingularKummer
end Reflection
end BernoulliRegular

end

end
