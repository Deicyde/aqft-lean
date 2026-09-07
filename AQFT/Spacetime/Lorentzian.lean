import AQFT.Geometry.Lorentzian.Basic
import AQFT.Spacetime.MinkowskiMetric
import AQFT.Spacetime.MinkowskiSignature

/-!
# Minkowski space is Lorentzian

The smooth constant Minkowski metric has negative index one and positive signature
equal to the number of spatial dimensions. Thus it defines a Lorentzian metric.
Its usual Euclidean topology is Hausdorff and second countable, and its manifold
model has no boundary.

Reference: Christian Bär, Lorentzian Geometry, preface and §1.1:
https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf
-/

open Manifold

namespace AQFT.Spacetime.MinkowskiSpace

/-- The quadratic form of the smooth Minkowski metric is its constant model form. -/
@[simp] theorem metric_quadraticForm (n : ℕ) (x : MinkowskiSpace n) :
    (metric n).quadraticForm x = quadraticForm n := rfl

/-- Minkowski space has one negative metric direction at every point. -/
@[simp] theorem metric_index (n : ℕ) (x : MinkowskiSpace n) :
    (metric n).index x = 1 := by
  change sigNeg (quadraticForm n) = 1
  exact quadraticForm_sigNeg n

/-- The constant Minkowski metric is Lorentzian. -/
theorem metric_isLorentzian (n : ℕ) : (metric n).IsLorentzian := metric_index n

/-- Minkowski spacetime with its smooth Lorentzian metric. -/
noncomputable def lorentzianMetric (n : ℕ) :
    LorentzianMetric 𝓘(ℝ, MinkowskiSpace n) (MinkowskiSpace n) where
  toPseudoRiemannianMetric := metric n
  isLorentzian := metric_isLorentzian n

@[simp] theorem lorentzianMetric_toPseudoRiemannianMetric (n : ℕ) :
    (lorentzianMetric n).toPseudoRiemannianMetric = metric n := rfl

end AQFT.Spacetime.MinkowskiSpace
