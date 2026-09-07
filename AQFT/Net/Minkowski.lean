import AQFT.Net.Causality
import AQFT.Spacetime.MinkowskiCausal

/-!
# Minkowski specialization of Einstein causality

The general Lorentzian causality axiom recovers the Minkowski formulation:
elements of the two local C*-algebras commute whenever every displacement between
the two regions has strictly positive Minkowski square. The equivalence uses the proved relation
between regular causal curves and displacement squares. The region type agrees
with bounded open sets through `Spacetime.Region.boundedOpenOrderIso`.

Reference: Fewster and Rejzner, [*Algebraic Quantum Field Theory — an introduction*, §4]
(https://arxiv.org/abs/1904.04051).
-/

namespace AQFT.IsotoneNet

open Spacetime Spacetime.MinkowskiSpace

variable {n : ℕ} {B : Type*} [CStarAlgebra B]

/-- The Lorentzian causality axiom specializes to the displacement criterion in Minkowski space. -/
theorem isCausal_minkowski_iff (A : IsotoneNet (MinkowskiSpace n) B) :
    A.IsCausal (lorentzianMetric n) ↔
      ∀ ⦃O₁ O₂ : Region (MinkowskiSpace n)⦄,
        SpacelikeSeparated (O₁ : Set (MinkowskiSpace n)) O₂ →
          ∀ ⦃a b : B⦄, a ∈ A O₁ → b ∈ A O₂ → Commute a b := by
  simp only [IsCausal, spacelikeSeparated_iff]

end AQFT.IsotoneNet
