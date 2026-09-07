import AQFT.Geometry.PseudoRiemannian.Bundle
import AQFT.Geometry.Lorentzian.Isometry

/-!
# Lorentzian manifolds with installed tangent pairings

The manifold has a fixed indefinite pairing on each tangent fiber. Smoothness is
recorded by `IsPseudoRiemannianManifold`, as in Mathlib's bundle construction, and
`IsLorentzianManifold` adds the index-one condition.

Unlike Mathlib's `IsRiemannianManifold`, this class contains no compatibility with
an extended distance: an indefinite pairing does not define such a distance.
For manifolds without boundary, also assume `[I.Boundaryless]`, `[T2Space M]`, and
`[SecondCountableTopology M]`.
-/

open Manifold Bundle
open scoped ContDiff

namespace AQFT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- The installed smooth tangent pairings have negative index one at every point. -/
class IsLorentzianManifold (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] [PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsPseudoRiemannianManifold I M] : Prop where
  index_eq_one (x : M) : (PseudoRiemannianMetric.ofBundle I M).index x = 1

variable {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]

namespace LorentzianMetric

/-- Installing a Lorentzian metric equips the manifold with the index-one property. -/
instance (g : LorentzianMetric I M) :
    letI : PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      g.toPseudoRiemannianMetric.toBundle
    IsLorentzianManifold I M := by
  let : PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    g.toPseudoRiemannianMetric.toBundle
  exact ⟨fun x ↦ g.index_eq_one x⟩

variable (I M) in
/-- Recover a Lorentzian metric from the installed fiber structures and their properties. -/
noncomputable def ofManifold [PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsPseudoRiemannianManifold I M] [IsLorentzianManifold I M] : LorentzianMetric I M where
  toPseudoRiemannianMetric := PseudoRiemannianMetric.ofBundle I M
  isLorentzian := IsLorentzianManifold.index_eq_one

end LorentzianMetric

variable (I M) in
/-- The isometry group of a manifold with its installed Lorentzian tangent pairings. -/
noncomputable abbrev LorentzianIsometryGroup
    [PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsPseudoRiemannianManifold I M] [IsLorentzianManifold I M] :=
  LorentzianMetric.IsometryGroup (LorentzianMetric.ofManifold I M)

end AQFT
