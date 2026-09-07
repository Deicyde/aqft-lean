import AQFT.Geometry.Lorentzian.Basic
import AQFT.Spacetime.MinkowskiMetric
import AQFT.Spacetime.MinkowskiSignature

/-!
# Minkowski space is Lorentzian

The smooth constant metric on `MinkowskiSpace k` has ordered signature $(1,k)$,
with the negative count first, and total dimension $k+1$. Thus it defines a
Lorentzian metric. For total dimension $n \geq 1$, use `MinkowskiSpace (n - 1)`;
its signature is $(1,n-1)$. Its usual Euclidean topology is Hausdorff and second
countable, and its manifold model has no boundary.

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

/-- The Minkowski metric has signature $(1,k)$, ordered as negative then positive. -/
@[simp] theorem metric_signature (k : ℕ) (x : MinkowskiSpace k) :
    (metric k).signature x = (1, k) := by
  change (sigNeg (quadraticForm k), sigPos (quadraticForm k)) = (1, k)
  simp

/-- Minkowski space with `k` spatial coordinates has total dimension `k + 1`. -/
@[simp] theorem finrank (k : ℕ) : Module.finrank ℝ (MinkowskiSpace k) = k + 1 := by
  simp [MinkowskiSpace, Module.finrank_prod, Nat.add_comm]

/-- In total dimension $n \geq 1$, the Minkowski metric has signature $(1,n-1)$. -/
theorem metric_signature_total_dimension (n : ℕ) (hn : 1 ≤ n)
    (x : MinkowskiSpace (n - 1)) :
    Module.finrank ℝ (MinkowskiSpace (n - 1)) = n ∧
      (metric (n - 1)).signature x = (1, n - 1) := by
  exact ⟨by rw [finrank, Nat.sub_add_cancel hn], metric_signature (n - 1) x⟩

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
