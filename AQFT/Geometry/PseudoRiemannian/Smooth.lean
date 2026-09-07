import AQFT.Geometry.PseudoRiemannian.Basic

/-!
# Smooth evaluation of a pseudo-Riemannian metric

Pairing two smooth vector fields with a smooth metric produces a smooth real
function. This connects the metric's Hom-bundle section to scalar evaluation.
The proof specializes Mathlib's smooth evaluation of bilinear bundle maps.
-/

open Manifold Bundle
open scoped ContDiff

namespace AQFT.PseudoRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- The metric pairing of two smooth vector fields is smooth. -/
theorem contMDiff_form (g : PseudoRiemannianMetric I M)
    {v w : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x ↦ TotalSpace.mk' E x (v x)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x ↦ TotalSpace.mk' E x (w x))) :
    ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ g.form x (v x) (w x)) := by
  have h : ContMDiff I (I.prod 𝓘(ℝ)) ∞
      (fun x ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x (g.form x (v x) (w x))) :=
    g.contMDiff.clm_bundle_apply₂ hv hw
  intro x
  have hx := h x
  simp only [contMDiffAt_totalSpace] at hx
  exact hx.2

end AQFT.PseudoRiemannianMetric
