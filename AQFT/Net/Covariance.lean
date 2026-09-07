import AQFT.Net.Basic
import AQFT.Geometry.Lorentzian.Isometry
import AQFT.Geometry.PseudoRiemannian.IsometryTopology
import AQFT.Spacetime.RegionIsometry
import AQFT.Representation.Ultraweak

/-!
# Covariance by automorphisms of the abstract net

Covariance asserts the existence of a faithful representation `α` of the metric
self-isometry group by star-algebra automorphisms of `B`, with
`A(f • O) = α(f)(A(O))`. The action is weakly continuous in a chosen faithful
Hilbert-space representation `π`: every matrix coefficient of every observable
orbit is continuous. The equivalent strong and ultraweak conditions are stated
below. The net itself remains independent of `π` and its Hilbert space.

This follows the automorphism formulation of Haag–Kastler covariance, with the
requested full isometry group and injectivity of `α`. All group elements,
including time reversal when present, act by complex-linear star automorphisms.
Faithfulness concerns the ambient algebra `B`; the local algebras are not assumed
to generate it. No unitary implementation or norm continuity is required.

References:
* [Wikipedia, Algebraic quantum field theory]
  (https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory#Haag%E2%80%93Kastler_axioms),
  for covariance and its automorphism formulation. We use operator continuity
  relative to `π`, rather than the point-norm condition in its categorical section.
* Fewster and Rejzner, [*Algebraic Quantum Field Theory — an introduction*, §4.1]
  (https://arxiv.org/abs/1904.04051), for the action on local algebras.
-/

open Manifold
open scoped ContDiff

noncomputable section

namespace AQFT.IsotoneNet

open Spacetime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Hₘ : Type*} [TopologicalSpace Hₘ] {I : ModelWithCorners ℝ E Hₘ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace Hₘ M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  {B : Type*} [CStarAlgebra B]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Covariance: a faithful, weakly continuous automorphism representation of the
isometry group transports each local algebra to that of the transformed region.
The faithful representation `π` specifies the operator topology. -/
def IsCovariant (A : IsotoneNet M B) (g : LorentzianMetric I M)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  Function.Injective π ∧
    ∃ α : g.IsometryGroup →* (B ≃⋆ₐ[ℂ] B),
      Function.Injective α ∧ Automorphism.IsWeaklyContinuous π α ∧
        ∀ f O, (A (f • O) : Set B) = α f '' (A O : Set B)

/-- Strong operator continuity gives the same covariance condition. -/
theorem isCovariant_iff_strong (A : IsotoneNet M B) (g : LorentzianMetric I M)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A.IsCovariant g π ↔ Function.Injective π ∧
      ∃ α : g.IsometryGroup →* (B ≃⋆ₐ[ℂ] B),
        Function.Injective α ∧ Automorphism.IsStronglyContinuous π α ∧
          ∀ f O, (A (f • O) : Set B) = α f '' (A O : Set B) := by
  simp only [IsCovariant, Automorphism.isWeaklyContinuous_iff_isStronglyContinuous]

/-- Ultraweak operator continuity gives the same covariance condition. -/
theorem isCovariant_iff_ultraweak (A : IsotoneNet M B) (g : LorentzianMetric I M)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A.IsCovariant g π ↔ Function.Injective π ∧
      ∃ α : g.IsometryGroup →* (B ≃⋆ₐ[ℂ] B),
        Function.Injective α ∧ Automorphism.IsUltraweaklyContinuous π α ∧
          ∀ f O, (A (f • O) : Set B) = α f '' (A O : Set B) := by
  simp only [IsCovariant, Automorphism.isWeaklyContinuous_iff_isUltraweaklyContinuous]

/-- The covariance equation can equivalently be expressed by membership:
`α(f)(a)` belongs to `A(f • O)` exactly when `a` belongs to `A(O)`. -/
theorem isCovariant_iff_mem (A : IsotoneNet M B) (g : LorentzianMetric I M)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A.IsCovariant g π ↔ Function.Injective π ∧
      ∃ α : g.IsometryGroup →* (B ≃⋆ₐ[ℂ] B),
        Function.Injective α ∧ Automorphism.IsWeaklyContinuous π α ∧
          ∀ f O a, α f a ∈ A (f • O) ↔ a ∈ A O := by
  constructor
  · rintro ⟨hπ, α, hα, hc, hcov⟩
    refine ⟨hπ, α, hα, hc, ?_⟩
    intro f O a
    change α f a ∈ (A (f • O) : Set B) ↔ _
    rw [hcov f O]
    constructor
    · rintro ⟨b, hb, hab⟩
      exact (α f).injective hab ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  · rintro ⟨hπ, α, hα, hc, hcov⟩
    refine ⟨hπ, α, hα, hc, ?_⟩
    intro f O
    apply Set.ext
    intro a
    constructor
    · intro ha
      obtain ⟨b, rfl⟩ := (α f).surjective a
      exact ⟨b, (hcov f O b).mp ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact (hcov f O b).mpr hb

end AQFT.IsotoneNet
