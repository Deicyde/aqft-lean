import AQFT.Spacetime.Region
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Hom.Basic

/-!
# Isotony for nets of local algebras

An `IsotoneNet n H` assigns a concrete von Neumann algebra on the same complex
Hilbert space `H` to each open bounded region of `MinkowskiSpace n`. Isotony is
the order-preserving property of Mathlib's `OrderHom`: inclusion of regions
implies inclusion of algebras, including the case of equal regions.

The region type includes the empty set. No value for its algebra is prescribed.
This definition imposes only isotony, not the remaining Haag–Kastler axioms.

Reference: [Algebraic quantum field theory, Haag–Kastler axioms]
(https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory#Haag%E2%80%93Kastler_axioms).
-/

namespace AQFT

open Spacetime.MinkowskiSpace

/-- Local von Neumann algebras on one complex Hilbert space, satisfying isotony. -/
abbrev IsotoneNet (n : ℕ) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :=
  Region n →o VonNeumannAlgebra H

namespace IsotoneNet

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The first Haag–Kastler axiom, expressed as inclusion of sets of operators. -/
theorem isotony (A : IsotoneNet n H) {O₁ O₂ : Region n}
    (h : (O₁ : Set (Spacetime.MinkowskiSpace n)) ⊆ O₂) :
    (A O₁ : Set (H →L[ℂ] H)) ⊆ A O₂ :=
  A.monotone h

/-- Any two local algebras are contained in a common local algebra. -/
theorem directed (A : IsotoneNet n H) : Directed (· ≤ ·) A :=
  A.monotone.directed_le

end IsotoneNet

end AQFT
