import AQFT.Net.Causality
import AQFT.Geometry.Lorentzian.Isometry
import AQFT.Geometry.PseudoRiemannian.IsometryTopology
import AQFT.Spacetime.RegionIsometry
import AQFT.Representation.Unitary

/-!
# Unitary covariance under Lorentzian isometries

The third axiom is stated for a faithful representation of an abstract net on
a complex Hilbert space. A strongly continuous unitary representation of the
metric's self-isometry group transports each represented local algebra to that
of the transformed region. The abstract `IsotoneNet` retains no Hilbert-space
parameter. `IsCovariant` asserts that such implementing data exist on `H`.

We use all self-isometries, with compact-open convergence of maps and inverses.
This is the full-isometry variant requested here, including time reversal;
it is stronger than restricting covariance to the identity component. No
positive-energy, invariant-vector, or point-norm continuity condition is imposed.
The covariance law concerns local algebras. It does not require conjugation to
preserve the whole represented ambient algebra, since the locals need not
generate it.

Reference: Fewster and Rejzner,
[*Algebraic Quantum Field Theory — an introduction*, §§4.1, 5]
(https://arxiv.org/abs/1904.04051). Their standard Minkowski formulation restricts
the spacetime symmetry group to the identity component of the Poincaré group.
-/

open Manifold
open scoped ContDiff

noncomputable section

namespace AQFT.IsotoneNet

open Spacetime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Hₘ : Type*} [TopologicalSpace Hₘ] {I : ModelWithCorners ℝ E Hₘ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace Hₘ M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [LocallyCompactSpace M]
  {B : Type*} [CStarAlgebra B]

/-- A faithful representation of a net with a strongly continuous unitary
implementation of all self-isometries of the Lorentzian metric. -/
structure CovariantRepresentation (A : IsotoneNet M B) (g : LorentzianMetric I M)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The abstract observables act as bounded operators on the chosen Hilbert space. -/
  representation : B →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- No algebraic information is lost by passing to operators. -/
  faithful : Function.Injective representation
  /-- A unitary group representation, continuous on every Hilbert-space vector. -/
  unitary : UnitaryRepresentation g.IsometryGroup H
  /-- Isometries transport local algebras by unitary conjugation. -/
  covariance (f : g.IsometryGroup) (O : Region M) :
    representation '' (A (f • O) : Set B) =
      unitary.conjugation f '' (representation '' (A O : Set B))

variable {A : IsotoneNet M B} {g : LorentzianMetric I M}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The third axiom: a faithful covariant representation exists on `H`. -/
def IsCovariant (A : IsotoneNet M B) (g : LorentzianMetric I M)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  Nonempty (CovariantRepresentation A g H)

namespace CovariantRepresentation

variable (R : CovariantRepresentation A g H)

/-- The local algebra after applying the faithful representation, as a set of operators. -/
def localAlgebra (O : Region M) : Set (H →L[ℂ] H) :=
  R.representation '' (A O : Set B)

/-- The represented local algebras retain isotony. -/
theorem localAlgebra_mono {O₁ O₂ : Region M} (h : O₁ ≤ O₂) :
    R.localAlgebra O₁ ⊆ R.localAlgebra O₂ :=
  Set.image_mono (A.monotone h)

/-- Faithfulness identifies membership in a represented local algebra. -/
@[simp] theorem representation_mem_localAlgebra_iff (a : B) (O : Region M) :
    R.representation a ∈ R.localAlgebra O ↔ a ∈ A O := by
  constructor
  · rintro ⟨b, hb, heq⟩
    exact R.faithful heq ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The covariance equation in terms of represented local algebras. -/
theorem localAlgebra_covariance (f : g.IsometryGroup) (O : Region M) :
    R.localAlgebra (f • O) = R.unitary.conjugation f '' R.localAlgebra O :=
  R.covariance f O

/-- Conjugating a local observable places it in the transformed local algebra. -/
theorem conjugation_mem_localAlgebra (f : g.IsometryGroup) (O : Region M)
    {a : B} (ha : a ∈ A O) :
    R.unitary.conjugation f (R.representation a) ∈ R.localAlgebra (f • O) := by
  rw [R.localAlgebra_covariance]
  exact ⟨R.representation a, ⟨a, ha, rfl⟩, rfl⟩

/-- Every observable in the transformed region has a preimage under
the represented conjugation of the original local algebra. -/
theorem mem_transformed_iff (f : g.IsometryGroup) (O : Region M) (a : B) :
    a ∈ A (f • O) ↔ ∃ b ∈ A O,
      R.unitary.conjugation f (R.representation b) = R.representation a := by
  rw [← R.representation_mem_localAlgebra_iff a (f • O), R.localAlgebra_covariance]
  change _ ∈ R.unitary.conjugation f '' (R.representation '' (A O : Set B)) ↔ _
  rw [Set.image_image]
  rfl

/-- The covariance equation written explicitly as multiplication by a unitary
operator and its adjoint. -/
theorem covariance_mul_star (f : g.IsometryGroup) (O : Region M) :
    R.localAlgebra (f • O) =
      (fun T : H →L[ℂ] H ↦ (R.unitary f : H →L[ℂ] H) * T *
        star (R.unitary f : H →L[ℂ] H)) '' R.localAlgebra O := by
  simpa only [R.unitary.conjugation_eq_mul_star] using R.localAlgebra_covariance f O

/-- Causality of the abstract net gives commutation of the represented operators. -/
theorem commute_of_isCausal (hA : A.IsCausal g) {O₁ O₂ : Region M}
    (h : g.SpacelikeSeparated (O₁ : Set M) O₂)
    {a b : H →L[ℂ] H} (ha : a ∈ R.localAlgebra O₁) (hb : b ∈ R.localAlgebra O₂) :
    Commute a b := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  exact (hA h ha hb).map R.representation

/-- Implementing data witness the existential covariance axiom. -/
theorem isCovariant (R : CovariantRepresentation A g H) : A.IsCovariant g H := ⟨R⟩

end CovariantRepresentation

end AQFT.IsotoneNet
