module

public import BernoulliRegular.Reflection.SingularKummer.IntegralCharacterProjection

/-!
# Singular Kummer: idempotence of character projections

The character projection

```text
  e_i = |Delta|^{-1} sum_a a^{-i} [a]
```

acts as the identity on its own range as soon as `|Delta|` is invertible in the
coefficient ring `ZMod p`.  This is the algebraic fact needed to recognize the
torsion in the range of the integral lift as lying in the corresponding
projected component of `A[p]`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace CharacterProjection

variable {p : ℕ} [NeZero p]
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]

end CharacterProjection

end SingularKummer
end Reflection
end BernoulliRegular

end

end
