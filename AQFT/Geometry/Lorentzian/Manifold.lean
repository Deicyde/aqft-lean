import AQFT.Geometry.PseudoRiemannian.Bundle
import AQFT.Geometry.Lorentzian.Isometry

/-!
# Lorentzian manifolds with installed tangent pairings

The manifold has a fixed indefinite pairing on each tangent fiber. Smoothness is
recorded by `IsPseudoRiemannianManifold`, as in Mathlib's bundle construction, and
`IsLorentzianManifold` adds the index-one condition. Nondegeneracy makes this
equivalent to signature $(1,n-1)$ for total model dimension $n$. Signature here
is ordered as (negative directions, positive directions).

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
  sigNeg_eq_one : (PseudoRiemannianMetric.ofBundle I M).IsLorentzian

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
  exact ⟨fun x ↦ g.sigNeg_eq_one x⟩

variable (I M) in
/-- Recover a Lorentzian metric from the installed fiber structures and their properties. -/
noncomputable def ofManifold [PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsPseudoRiemannianManifold I M] [IsLorentzianManifold I M] : LorentzianMetric I M where
  toPseudoRiemannianMetric := PseudoRiemannianMetric.ofBundle I M
  isLorentzian := IsLorentzianManifold.sigNeg_eq_one

end LorentzianMetric

section Signature

variable [PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsPseudoRiemannianManifold I M]

/-- The Lorentzian manifold condition is exactly the pointwise signature $(1,n-1)$. -/
theorem isLorentzianManifold_iff_signature :
    IsLorentzianManifold I M ↔
      ∀ x, let Q := (PseudoRiemannianMetric.ofBundle I M).quadraticForm x
        (sigNeg Q, sigPos Q) = (1, Module.finrank ℝ E - 1) := by
  constructor
  · intro h
    exact (PseudoRiemannianMetric.ofBundle I M).isLorentzian_iff_signature.mp h.sigNeg_eq_one
  · intro h
    exact ⟨(PseudoRiemannianMetric.ofBundle I M).isLorentzian_iff_signature.mpr h⟩

/-- The installed Lorentzian tangent pairing has one negative and $n-1$ positive directions. -/
theorem IsLorentzianManifold.signature_eq [IsLorentzianManifold I M] (x : M) :
    let Q := (PseudoRiemannianMetric.ofBundle I M).quadraticForm x
    (sigNeg Q, sigPos Q) = (1, Module.finrank ℝ E - 1) :=
  (LorentzianMetric.ofManifold I M).signature_eq x

/-- The signature formula directly for the installed pairing on each tangent fiber. -/
theorem IsLorentzianManifold.pseudoInner_signature [IsLorentzianManifold I M] (x : M) :
    (sigNeg (pseudoInner (V := TangentSpace I x)).toBilinForm.toQuadraticMap,
      sigPos (pseudoInner (V := TangentSpace I x)).toBilinForm.toQuadraticMap) =
        (1, Module.finrank ℝ E - 1) :=
  IsLorentzianManifold.signature_eq x

/-- The installed signature with the total manifold dimension named explicitly. -/
theorem IsLorentzianManifold.signature_eq_of_finrank [IsLorentzianManifold I M]
    {n : ℕ} (hdim : Module.finrank ℝ E = n) (x : M) :
    let Q := (PseudoRiemannianMetric.ofBundle I M).quadraticForm x
    (sigNeg Q, sigPos Q) = (1, n - 1) := by
  simpa only [hdim] using IsLorentzianManifold.signature_eq (I := I) x

end Signature

variable (I M) in
/-- The isometry group of a manifold with its installed Lorentzian tangent pairings. -/
noncomputable abbrev LorentzianIsometryGroup
    [PseudoRiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsPseudoRiemannianManifold I M] [IsLorentzianManifold I M] :=
  LorentzianMetric.IsometryGroup (LorentzianMetric.ofManifold I M)

end AQFT
