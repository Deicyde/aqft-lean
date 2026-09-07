import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Smooth pseudo-Riemannian metrics

A metric is a smooth field of symmetric, nondegenerate real bilinear forms on the
tangent bundle of a finite-dimensional smooth manifold. Smoothness is expressed in
the bilinear Hom bundle, so it respects changes of tangent coordinates.

No fixed signature is imposed. A prescribed index, and in particular the Lorentzian
case, will be a separate condition. Hausdorffness and second countability may be
assumed on the base when needed; the metric construction does not require them.

## References

* Bernd Ammann, Differential Geometry II, Definition 2.1.1:
  https://ammann.app.uni-regensburg.de/lehre/2021s_diffgeo2/Diffgeo2.pdf
* Mathlib's `Bundle.ContMDiffRiemannianMetric` supplies the bundle smoothness pattern.
-/

open Manifold Bundle
open scoped ContDiff

namespace AQFT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- A smooth symmetric nondegenerate metric on a finite-dimensional real manifold.
The auxiliary norm on the model space defines its topology, not the metric's signature. -/
structure PseudoRiemannianMetric (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] where
  /-- The continuous bilinear form on each tangent space. -/
  form (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- Symmetry of the tangent pairing. -/
  symm (x : M) (v w : TangentSpace I x) : form x v w = form x w v
  /-- Both radicals of each tangent pairing vanish. -/
  nondegenerate (x : M) : (form x).toBilinForm.Nondegenerate
  /-- The metric is a smooth section of the bundle of bilinear forms. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (form x))

namespace PseudoRiemannianMetric

variable {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  (g : PseudoRiemannianMetric I M) (x : M)

/-- A vector that pairs to zero with every tangent vector is zero. -/
theorem eq_zero_of_forall_left (v : TangentSpace I x)
    (h : ∀ w, g.form x v w = 0) : v = 0 :=
  (g.nondegenerate x).1 v h

/-- Nondegeneracy also holds with the test vector in the first argument. -/
theorem eq_zero_of_forall_right (v : TangentSpace I x)
    (h : ∀ w, g.form x w v = 0) : v = 0 :=
  (g.nondegenerate x).2 v h

/-- Pairing with the metric distinguishes tangent vectors. -/
theorem form_injective : Function.Injective (g.form x) := by
  intro v w h
  apply sub_eq_zero.mp
  apply g.eq_zero_of_forall_left x (v - w)
  intro z
  simp only [map_sub, sub_apply]
  rw [h, sub_self]

end PseudoRiemannianMetric

end AQFT
