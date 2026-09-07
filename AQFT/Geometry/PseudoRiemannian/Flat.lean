import AQFT.Geometry.PseudoRiemannian.Basic

/-!
# Constant pseudo-Riemannian metrics

Every symmetric nondegenerate continuous bilinear form on a finite-dimensional
real vector space defines a smooth constant metric on that space as a manifold.

The smoothness proof follows Mathlib's `riemannianMetricVectorSpace`, adapted to
arbitrary signature.
-/

open Manifold Bundle
open scoped ContDiff

namespace AQFT.PseudoRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- The constant smooth metric associated with a symmetric nondegenerate form. -/
def ofBilinearForm (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hnd : B.toBilinForm.Nondegenerate) :
    PseudoRiemannianMetric 𝓘(ℝ, E) E where
  form _ := B
  symm _ := hB
  nondegenerate _ := hnd
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := B)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

/-- The constant metric evaluates to its defining bilinear form. -/
@[simp] theorem ofBilinearForm_form (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hnd : B.toBilinForm.Nondegenerate)
    (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    (ofBilinearForm B hB hnd).form x v w = B v w := rfl

end AQFT.PseudoRiemannianMetric
