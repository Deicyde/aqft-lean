import AQFT.Spacetime.Region
import AQFT.Geometry.PseudoRiemannian.Isometry

/-!
# The action of metric isometries on regions

An isometry transports a relatively compact open region by its underlying
homeomorphism. This preserves inclusion and defines a group action for
self-isometries. No auxiliary metric distance or boundedness estimate is needed.

Reference: Fewster and Rejzner,
[*Algebraic Quantum Field Theory — an introduction*, §4.1]
(https://arxiv.org/abs/1904.04051).
-/

open Manifold
open scoped ContDiff

noncomputable section

namespace AQFT.PseudoRiemannianMetric.Isometry

open Spacetime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  {g : PseudoRiemannianMetric I M} {h : PseudoRiemannianMetric J N}

/-- An isometry induces an order isomorphism of relatively compact open regions. -/
def regionOrderIso (f : Isometry g h) : Region M ≃o Region N :=
  Region.mapOrderIso f.toDiffeomorph.toHomeomorph

@[simp] theorem coe_regionOrderIso (f : Isometry g h) (O : Region M) :
    (f.regionOrderIso O : Set N) = f '' (O : Set M) := rfl

/-- Self-isometries act on regions by direct image. -/
instance : MulAction (Isometry g g) (Region M) where
  smul f := f.regionOrderIso
  one_smul O := by
    apply SetLike.coe_injective
    exact Set.image_id _
  mul_smul f h O := by
    apply SetLike.coe_injective
    exact (Set.image_image f h (O : Set M)).symm

@[simp] theorem smul_region (f : Isometry g g) (O : Region M) :
    f • O = f.regionOrderIso O := rfl

/-- The underlying set of the transformed region is its image under the isometry. -/
@[simp] theorem coe_smul_region (f : Isometry g g) (O : Region M) :
    ((f • O : Region M) : Set M) = f '' (O : Set M) := rfl

/-- The isometry action preserves and reflects region inclusion. -/
theorem smul_region_le_smul_region_iff (f : Isometry g g) (O₁ O₂ : Region M) :
    f • O₁ ≤ f • O₂ ↔ O₁ ≤ O₂ :=
  f.regionOrderIso.le_iff_le

end AQFT.PseudoRiemannianMetric.Isometry
