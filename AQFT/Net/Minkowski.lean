import AQFT.Net.Causality
import AQFT.Spacetime.MinkowskiCausal

/-!
# Minkowski specialization of Einstein causality

The general Lorentzian causality axiom recovers the Minkowski formulation:
operators commute whenever every displacement between the two regions has
strictly positive Minkowski square. The equivalence uses the proved relation
between regular causal curves and displacement squares. The region type agrees
with bounded open sets through `Spacetime.Region.boundedOpenOrderIso`.

Reference: [Algebraic quantum field theory, Haag–Kastler axioms]
(https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory#Haag%E2%80%93Kastler_axioms).
-/

namespace AQFT.IsotoneNet

open Spacetime Spacetime.MinkowskiSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Lorentzian causality axiom specializes to the displacement criterion in Minkowski space. -/
theorem isCausal_minkowski_iff (A : IsotoneNet (MinkowskiSpace n) H) :
    A.IsCausal (lorentzianMetric n) ↔
      ∀ ⦃O₁ O₂ : Region (MinkowskiSpace n)⦄,
        SpacelikeSeparated (O₁ : Set (MinkowskiSpace n)) O₂ →
          ∀ ⦃a b : H →L[ℂ] H⦄, a ∈ A O₁ → b ∈ A O₂ → Commute a b := by
  simp only [IsCausal, spacelikeSeparated_iff]

end AQFT.IsotoneNet
