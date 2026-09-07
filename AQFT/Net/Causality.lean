import AQFT.Net.Basic
import AQFT.Spacetime.Spacelike

/-!
# Einstein causality for local algebras

A net satisfies causality when every operator in one local algebra commutes with
every operator in a spacelike separated local algebra. With our sign convention
$(-,+,\ldots,+)$, separation requires strictly positive squared displacement
for every pair of points in the two regions.

`IsotoneNet.IsCausal` is a property of an existing isotone net. It is equivalent
to inclusion in the other local algebra's commutant and to vanishing operator
commutators. Covariance, the vacuum, and the spectrum condition remain separate.

Reference: [Algebraic quantum field theory, Haag–Kastler axioms]
(https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory#Haag%E2%80%93Kastler_axioms).
-/

namespace AQFT.IsotoneNet

open Spacetime Spacetime.MinkowskiSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Einstein causality: observables in spacelike separated regions commute. -/
def IsCausal (A : IsotoneNet n H) : Prop :=
  ∀ ⦃O₁ O₂ : Region n⦄, SpacelikeSeparated (O₁ : Set (MinkowskiSpace n)) O₂ →
    ∀ ⦃a b : H →L[ℂ] H⦄, a ∈ A O₁ → b ∈ A O₂ → Commute a b

/-- For a causal net, each local algebra lies in a spacelike separated algebra's commutant. -/
theorem IsCausal.le_commutant {A : IsotoneNet n H} (hA : A.IsCausal)
    {O₁ O₂ : Region n} (h : SpacelikeSeparated (O₁ : Set (MinkowskiSpace n)) O₂) :
    A O₁ ≤ (A O₂).commutant := by
  intro a ha
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  exact (hA h ha hb).eq.symm

/-- Causality is equivalent to commutant inclusion for spacelike separated regions. -/
theorem isCausal_iff_le_commutant (A : IsotoneNet n H) :
    A.IsCausal ↔ ∀ ⦃O₁ O₂ : Region n⦄,
      SpacelikeSeparated (O₁ : Set (MinkowskiSpace n)) O₂ → A O₁ ≤ (A O₂).commutant := by
  constructor
  · intro hA O₁ O₂ h
    exact hA.le_commutant h
  · intro hA O₁ O₂ h a b ha hb
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp (hA h ha)) b hb).symm

/-- The commutator formulation $ab-ba=0$ of the causality axiom. -/
theorem isCausal_iff_commutator_eq_zero (A : IsotoneNet n H) :
    A.IsCausal ↔ ∀ ⦃O₁ O₂ : Region n⦄,
      SpacelikeSeparated (O₁ : Set (MinkowskiSpace n)) O₂ →
        ∀ ⦃a b : H →L[ℂ] H⦄, a ∈ A O₁ → b ∈ A O₂ → a * b - b * a = 0 := by
  simp only [IsCausal, commute_iff_eq, sub_eq_zero]

/-- Empty-region observables commute with every local algebra. -/
theorem IsCausal.empty_le_commutant {A : IsotoneNet n H} (hA : A.IsCausal)
    (O : Region n) : A ⊥ ≤ (A O).commutant := by
  apply hA.le_commutant
  rw [Region.coe_bot]
  exact SpacelikeSeparated.empty_left _

end AQFT.IsotoneNet
