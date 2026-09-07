import AQFT.Geometry.PseudoRiemannian.Basic
import AQFT.Geometry.VectorBundle.PseudoRiemannian

/-!
# Pseudo-Riemannian manifolds from fiber structures

Following Mathlib's Riemannian bundle construction, first install a nondegenerate
symmetric pairing on each tangent fiber, then assume that the resulting section
of bilinear forms is smooth. A bundled metric is a constructor for these instances.

`IsPseudoRiemannianManifold` is an abbreviation for this smoothness condition.
The indefinite pairing supplies no norm or extended metric on the base.

Reference: Mathlib.Geometry.Manifold.Riemannian.Basic and
Mathlib.Geometry.Manifold.VectorBundle.Riemannian.
-/

open Manifold Bundle
open scoped ContDiff

namespace AQFT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- The installed tangent pairings form a smooth pseudo-Riemannian metric. -/
abbrev IsPseudoRiemannianManifold (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] [PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x)] :=
  IsContMDiffPseudoRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)

namespace PseudoRiemannianMetric

variable {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- Install the tangent fiber pairings supplied by a bundled metric. -/
@[instance_reducible]
def toBundle (g : PseudoRiemannianMetric I M) :
    PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x) where
  fiber x :=
    { form := g.form x
      symm := g.symm x
      nondegenerate := g.nondegenerate x }

/-- The fiber pairings installed by a smooth metric vary smoothly. -/
instance (g : PseudoRiemannianMetric I M) :
    letI : PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x) := g.toBundle
    IsPseudoRiemannianManifold I M := by
  let : PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x) := g.toBundle
  exact ⟨g.contMDiff⟩

variable (I M) in
/-- Recover a bundled metric from the installed smooth tangent pairings. -/
noncomputable def ofBundle [PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsPseudoRiemannianManifold I M] : PseudoRiemannianMetric I M where
  form x := pseudoInner (V := TangentSpace I x)
  symm _ := PseudoInnerProductSpace.symm
  nondegenerate _ := PseudoInnerProductSpace.nondegenerate
  contMDiff := IsContMDiffPseudoRiemannianBundle.contMDiff

/-- Recovering the metric from its installed fiber structures returns the original metric. -/
@[simp] theorem ofBundle_toBundle (g : PseudoRiemannianMetric I M) :
    letI : PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x) := g.toBundle
    ofBundle I M = g := rfl

end PseudoRiemannianMetric

end AQFT
