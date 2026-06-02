module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Power residue symbols

This file defines the finite-field and prime-ideal pieces of the power
residue symbol API used in the reflection argument. The ideal-level API keeps
the coprimality predicate explicit, so later reciprocity statements can record
their exact local hypotheses without hiding them in typeclass search.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace ResidueSymbol

namespace PowerResidue

open UniqueFactorizationMonoid

variable {k : Type*} [Field k] [Fintype k]
variable {p : ℕ}


















section PrimeIdeal

variable {R : Type*} [CommRing R]
variable (q : Ideal R) [q.IsMaximal]










end PrimeIdeal

section Ideals

variable {R : Type*} [CommRing R]



section IdealFactorization

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {p : ℕ}





end IdealFactorization

end Ideals

end PowerResidue

end ResidueSymbol
end Reflection
end BernoulliRegular
