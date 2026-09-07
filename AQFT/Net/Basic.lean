import AQFT.Spacetime.Region
import AQFT.Algebra.CStarSubalgebra
import Mathlib.Order.Hom.Basic

/-!
# Isotony for nets of local algebras

An `IsotoneNet M B` assigns a norm-closed unital star subalgebra of an abstract
complex C*-algebra `B` to each relatively compact open region of `M`. Every local
algebra inherits a C*-algebra structure. Isotony is the order-preserving property
of Mathlib's `OrderHom`: inclusion of regions implies inclusion of algebras,
including the case of equal regions. No Hilbert space or representation is chosen.

The local algebras share the unit of `B`. The region type includes the empty set;
no value for its algebra is prescribed. This definition imposes only isotony.
It does not require the local algebras to generate all of `B`.

Reference: Fewster and Rejzner, [*Algebraic Quantum Field Theory — an introduction*, §4]
(https://arxiv.org/abs/1904.04051).
-/

namespace AQFT

open Spacetime

/-- A net of unital C*-subalgebras of an abstract C*-algebra, satisfying isotony. -/
abbrev IsotoneNet (M : Type*) [TopologicalSpace M] (B : Type*) [CStarAlgebra B] :=
  Region M →o CStarSubalgebra B

namespace IsotoneNet

variable {M : Type*} [TopologicalSpace M] {B : Type*} [CStarAlgebra B]

/-- The first Haag–Kastler axiom, expressed as inclusion of sets of algebra elements. -/
theorem isotony (A : IsotoneNet M B) {O₁ O₂ : Region M}
    (h : (O₁ : Set M) ⊆ O₂) :
    (A O₁ : Set B) ⊆ A O₂ :=
  A.monotone h

/-- Any two local algebras are contained in a common local algebra. -/
theorem directed (A : IsotoneNet M B) : Directed (· ≤ ·) A :=
  A.monotone.directed_le

end IsotoneNet

end AQFT
