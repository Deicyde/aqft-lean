import AQFT.Geometry.PseudoRiemannian.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Lorentzian metrics

A Lorentzian metric is a smooth pseudo-Riemannian metric with index one at every
point. We use the convention $(-,+,\ldots,+)$: the index is the dimension of a
maximal subspace on which the quadratic form is negative definite. This uses
Mathlib's `sigNeg`. We record signature in the order (negative, positive), so an
$n$-dimensional Lorentzian tangent space has signature $(1,n-1)$.

To describe a Lorentzian manifold without boundary, use `[I.Boundaryless]`,
`[T2Space M]`, `[SecondCountableTopology M]`, and `g : LorentzianMetric I M`,
along with the finite-dimensional smooth manifold assumptions below. The metric
API itself also permits models with corners. No time orientation is chosen.

The index-one definition permits dimension one. Spacetime applications that need
spatial directions should additionally require model dimension at least two.

## Reference

* Christian Bär, Lorentzian Geometry, preface:
  https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf
-/

open Manifold
open scoped ContDiff

namespace AQFT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]

namespace PseudoRiemannianMetric

/-- The quadratic form obtained by evaluating the metric twice on a vector. -/
noncomputable def quadraticForm (g : PseudoRiemannianMetric I M) (x : M) :
    QuadraticForm ℝ (TangentSpace I x) :=
  (g.form x).toBilinForm.toQuadraticMap

@[simp] theorem quadraticForm_apply (g : PseudoRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) : g.quadraticForm x v = g.form x v v := rfl

/-- The quadratic form associated with a pseudo-Riemannian metric is nondegenerate. -/
theorem quadraticForm_nondegenerate (g : PseudoRiemannianMetric I M) (x : M) :
    (g.quadraticForm x).Nondegenerate := by
  apply QuadraticMap.nondegenerate_associated_iff.mp
  change ((QuadraticMap.associatedHom ℝ) (g.form x).toBilinForm.toQuadraticMap).Nondegenerate
  rw [QuadraticMap.associated_left_inverse ℝ (g.symm x)]
  exact g.nondegenerate x

/-- The positive and negative signatures exhaust the dimension of the tangent space. -/
theorem signature_eq_finrank (g : PseudoRiemannianMetric I M) (x : M) :
    sigPos (g.quadraticForm x) + sigNeg (g.quadraticForm x) = Module.finrank ℝ E := by
  let : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := g.quadraticForm x)
  rw [(g.quadraticForm_nondegenerate x).radical_eq_bot] at h
  simp only [finrank_bot, add_zero] at h
  have hdim : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  exact h.trans hdim

/-- A pseudo-Riemannian metric is Lorentzian when its negative index is always one. -/
def IsLorentzian (g : PseudoRiemannianMetric I M) : Prop :=
  ∀ x, sigNeg (g.quadraticForm x) = 1

/-- For a nondegenerate metric, index one is equivalent to signature $(1,n-1)$,
where $n$ is the model dimension. -/
theorem isLorentzian_iff_signature (g : PseudoRiemannianMetric I M) :
    g.IsLorentzian ↔ ∀ x,
      (sigNeg (g.quadraticForm x), sigPos (g.quadraticForm x)) =
        (1, Module.finrank ℝ E - 1) := by
  constructor
  · intro hg x
    have hn : sigNeg (g.quadraticForm x) = 1 := hg x
    have hsum := g.signature_eq_finrank x
    have hp : sigPos (g.quadraticForm x) = Module.finrank ℝ E - 1 := by omega
    exact Prod.ext hn hp
  · intro h x
    exact congrArg Prod.fst (h x)

end PseudoRiemannianMetric

/-- A smooth pseudo-Riemannian metric with one negative direction at every point. -/
structure LorentzianMetric (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    extends PseudoRiemannianMetric I M where
  /-- The metric has negative index one everywhere. -/
  isLorentzian : toPseudoRiemannianMetric.IsLorentzian

namespace LorentzianMetric

/-- The negative index of a Lorentzian metric is one. -/
@[simp] theorem sigNeg_eq_one (g : LorentzianMetric I M) (x : M) :
    sigNeg (g.toPseudoRiemannianMetric.quadraticForm x) = 1 := g.isLorentzian x

/-- A Lorentzian metric on a nonempty manifold has positive model dimension. -/
theorem one_le_finrank (g : LorentzianMetric I M) (x : M) :
    1 ≤ Module.finrank ℝ E := by
  calc
    1 = sigNeg (g.toPseudoRiemannianMetric.quadraticForm x) := (g.sigNeg_eq_one x).symm
    _ ≤ Module.finrank ℝ E := sigPos_le_finrank (-g.toPseudoRiemannianMetric.quadraticForm x)

/-- A Lorentzian tangent space has all but one dimension in its positive signature. -/
theorem positive_signature_add_one (g : LorentzianMetric I M) (x : M) :
    sigPos (g.toPseudoRiemannianMetric.quadraticForm x) + 1 = Module.finrank ℝ E := by
  simpa only [g.sigNeg_eq_one x] using g.toPseudoRiemannianMetric.signature_eq_finrank x

/-- A Lorentzian metric on a model of dimension $n$ has signature $(1,n-1)$. -/
@[simp] theorem signature_eq (g : LorentzianMetric I M) (x : M) :
    (sigNeg (g.toPseudoRiemannianMetric.quadraticForm x),
      sigPos (g.toPseudoRiemannianMetric.quadraticForm x)) =
        (1, Module.finrank ℝ E - 1) :=
  (g.toPseudoRiemannianMetric.isLorentzian_iff_signature.mp g.isLorentzian) x

/-- The same signature formula with the total dimension named explicitly. -/
theorem signature_eq_of_finrank (g : LorentzianMetric I M) {n : ℕ}
    (hdim : Module.finrank ℝ E = n) (x : M) :
    (sigNeg (g.toPseudoRiemannianMetric.quadraticForm x),
      sigPos (g.toPseudoRiemannianMetric.quadraticForm x)) = (1, n - 1) := by
  simpa only [hdim] using g.signature_eq x

end LorentzianMetric

end AQFT
