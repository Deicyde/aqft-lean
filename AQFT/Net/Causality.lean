import AQFT.Net.Basic
import AQFT.Geometry.Lorentzian.Causal

/-!
# Einstein causality on Lorentzian manifolds

A net satisfies causality when elements of local C*-algebras assigned to separated
regions commute. Products are taken in the abstract ambient C*-algebra. The
regions are relatively compact open subsets of the manifold. Separation is induced by the Lorentzian
metric: no regular C¹ causal curve connects the two regions, and they do not
intersect. No global time orientation is needed for this symmetric condition.

`IsotoneNet.IsCausal` takes the metric explicitly. For the installed Lorentzian
manifold structure, use `LorentzianMetric.ofManifold I M`. Causality is equivalent
to inclusion in the other local algebra's relative commutant inside the ambient
C*-algebra and to vanishing commutators. Covariance, the vacuum, and the spectrum
condition remain separate.

References:
* Fewster and Rejzner, [*Algebraic Quantum Field Theory — an introduction*, §4]
  (https://arxiv.org/abs/1904.04051).
* Bunk, MacManus, and Schenkel, [*Lorentzian bordisms in algebraic quantum field theory*, §2]
  (https://doi.org/10.1007/s11005-025-01906-3).
-/

open Manifold
open scoped ContDiff

namespace AQFT.IsotoneNet

open Spacetime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Hₘ : Type*} [TopologicalSpace Hₘ] {I : ModelWithCorners ℝ E Hₘ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace Hₘ M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  {B : Type*} [CStarAlgebra B]

/-- Einstein causality for a net on a manifold with Lorentzian metric `g`. -/
def IsCausal (A : IsotoneNet M B) (g : LorentzianMetric I M) : Prop :=
  ∀ ⦃O₁ O₂ : Region M⦄, g.SpacelikeSeparated (O₁ : Set M) O₂ →
    ∀ ⦃a b : B⦄, a ∈ A O₁ → b ∈ A O₂ → Commute a b

/-- For a causal net, each local algebra lies in a separated algebra's relative commutant. -/
theorem IsCausal.le_commutant {A : IsotoneNet M B} {g : LorentzianMetric I M}
    (hA : A.IsCausal g) {O₁ O₂ : Region M}
    (h : g.SpacelikeSeparated (O₁ : Set M) O₂) : A O₁ ≤ (A O₂).commutant := by
  intro a ha
  exact CStarSubalgebra.mem_commutant_iff.mpr fun b hb ↦ (hA h ha hb).eq.symm

/-- Causality is equivalent to relative commutant inclusion for separated regions. -/
theorem isCausal_iff_le_commutant (A : IsotoneNet M B) (g : LorentzianMetric I M) :
    A.IsCausal g ↔ ∀ ⦃O₁ O₂ : Region M⦄,
      g.SpacelikeSeparated (O₁ : Set M) O₂ → A O₁ ≤ (A O₂).commutant := by
  constructor
  · intro hA O₁ O₂ h
    exact hA.le_commutant h
  · intro hA O₁ O₂ h a b ha hb
    exact ((CStarSubalgebra.mem_commutant_iff.mp (hA h ha)) b hb).symm

/-- The commutator formulation $ab-ba=0$ of the causality axiom. -/
theorem isCausal_iff_commutator_eq_zero (A : IsotoneNet M B) (g : LorentzianMetric I M) :
    A.IsCausal g ↔ ∀ ⦃O₁ O₂ : Region M⦄,
      g.SpacelikeSeparated (O₁ : Set M) O₂ →
        ∀ ⦃a b : B⦄, a ∈ A O₁ → b ∈ A O₂ → a * b - b * a = 0 := by
  simp only [IsCausal, commute_iff_eq, sub_eq_zero]

/-- Empty-region observables commute with every local algebra. -/
theorem IsCausal.empty_le_commutant {A : IsotoneNet M B} {g : LorentzianMetric I M}
    (hA : A.IsCausal g) (O : Region M) : A ⊥ ≤ (A O).commutant := by
  apply hA.le_commutant
  rw [Region.coe_bot]
  exact LorentzianMetric.SpacelikeSeparated.empty_left g _

end AQFT.IsotoneNet
