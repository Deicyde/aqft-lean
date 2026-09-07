import AQFT.Geometry.Lorentzian.Manifold
import AQFT.Spacetime.Lorentzian

/-!
# The Lorentzian manifold instances on Minkowski space

The constant Minkowski metric installs indefinite pairings on the tangent fibers.
Their smoothness and negative index one provide the manifold typeclasses, following
Mathlib's Riemannian bundle construction. With `k` spatial coordinates, the installed
metric has signature $(1,k)$, ordered as negative then positive. The auxiliary
Euclidean norm and inner product remain available separately.
-/

open Manifold Bundle
open scoped ContDiff

noncomputable section

namespace AQFT.Spacetime.MinkowskiSpace

/-- The standard indefinite tangent pairings on Minkowski space. -/
instance (n : ℕ) :
    PseudoRiemannianBundle (fun x : MinkowskiSpace n ↦ TangentSpace 𝓘(ℝ, MinkowskiSpace n) x) :=
  (metric n).toBundle

/-- The Minkowski tangent pairings vary smoothly. -/
instance (n : ℕ) : IsPseudoRiemannianManifold 𝓘(ℝ, MinkowskiSpace n) (MinkowskiSpace n) :=
  ⟨(metric n).contMDiff⟩

/-- Minkowski space is a Lorentzian manifold with its installed tangent pairings. -/
instance (n : ℕ) : IsLorentzianManifold 𝓘(ℝ, MinkowskiSpace n) (MinkowskiSpace n) :=
  ⟨metric_index n⟩

/-- The installed Minkowski tangent pairings have ordered signature $(1,k)$. -/
@[simp] theorem ofBundle_signature (k : ℕ) (x : MinkowskiSpace k) :
    (PseudoRiemannianMetric.ofBundle 𝓘(ℝ, MinkowskiSpace k) (MinkowskiSpace k)).signature x =
      (1, k) := by
  change (metric k).signature x = (1, k)
  exact metric_signature k x

/-- The installed tangent pairing is the Minkowski bilinear form. -/
@[simp] theorem pseudoInner_apply (n : ℕ) (x : MinkowskiSpace n)
    (v w : TangentSpace 𝓘(ℝ, MinkowskiSpace n) x) :
    pseudoInner v w = bilinearForm n v w := rfl

/-- A unit time vector has negative square for the installed fiber pairing. -/
@[simp] theorem pseudoInner_unitTime (n : ℕ) (x : MinkowskiSpace n) :
    pseudoInner (V := TangentSpace 𝓘(ℝ, MinkowskiSpace n) x) (1, 0) (1, 0) = -1 := by
  change bilinearForm n (1, 0) (1, 0) = -1
  exact bilinearForm_unitTime

end AQFT.Spacetime.MinkowskiSpace
