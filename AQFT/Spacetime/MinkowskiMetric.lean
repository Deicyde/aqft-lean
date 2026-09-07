import AQFT.Geometry.PseudoRiemannian.Flat
import AQFT.Spacetime.Minkowski

/-!
# Minkowski space as a pseudo-Riemannian manifold

The constant form of signature convention $(-,+,\ldots,+)$ on $\mathbb{R}^{1+n}$
defines a smooth pseudo-Riemannian metric. The numerical signature calculation
using Mathlib's quadratic-form API is a subsequent milestone.

## Reference

* Christian Bär, Lorentzian Geometry, §1.1:
  https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf
-/

open Manifold
open scoped ContDiff

namespace AQFT.Spacetime.MinkowskiSpace

/-- The smooth constant Minkowski metric with one time and `n` spatial coordinates. -/
noncomputable def metric (n : ℕ) :
    PseudoRiemannianMetric 𝓘(ℝ, MinkowskiSpace n) (MinkowskiSpace n) :=
  PseudoRiemannianMetric.ofBilinearForm (bilinearForm n)
    (bilinearForm_symm (n := n)) (bilinearForm_nondegenerate n)

/-- At every point, the Minkowski metric is its standard constant bilinear form. -/
@[simp] theorem metric_form (n : ℕ) (x : MinkowskiSpace n)
    (v w : TangentSpace 𝓘(ℝ, MinkowskiSpace n) x) :
    (metric n).form x v w = bilinearForm n v w := rfl

end AQFT.Spacetime.MinkowskiSpace
