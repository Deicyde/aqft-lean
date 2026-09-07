import AQFT.Geometry.Lorentzian.Basic
import AQFT.Geometry.PseudoRiemannian.Isometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Lorentzian isometries

The differential of a metric isometry gives an equivalence of tangent quadratic
forms. The ordered signature `(negative, positive)` is therefore invariant under
isometries. In particular, being Lorentzian is preserved by an isometry.

Lorentzian self-isometries inherit the algebraic group structure of
pseudo-Riemannian self-isometries. No time orientation is imposed.

## Reference

* Christian Bär, Lorentzian Geometry, Section 1.1:
  https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf
-/

open Manifold
open scoped ContDiff

noncomputable section

namespace AQFT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

namespace PseudoRiemannianMetric.Isometry

variable {g : PseudoRiemannianMetric I M} {h : PseudoRiemannianMetric J N}

/-- The differential of a metric isometry is an isometry of tangent quadratic forms. -/
def tangentQuadraticIsometry (f : Isometry g h) (x : M) :
    (g.quadraticForm x).IsometryEquiv (h.quadraticForm (f x)) where
  toLinearEquiv :=
    (f.toDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  map_app' v := f.map_form x v v

@[simp]
theorem tangentQuadraticIsometry_apply (f : Isometry g h) (x : M)
    (v : TangentSpace I x) : f.tangentQuadraticIsometry x v = mfderiv I J f x v := rfl

/-- Metric isometries preserve the negative index at corresponding points. -/
theorem sigNeg_eq (f : Isometry g h) (x : M) :
    sigNeg (g.quadraticForm x) = sigNeg (h.quadraticForm (f x)) :=
  QuadraticMap.Equivalent.sigNeg_eq ⟨f.tangentQuadraticIsometry x⟩

/-- Metric isometries preserve the ordered negative and positive signature pair. -/
theorem signature_eq (f : Isometry g h) (x : M) :
    (sigNeg (g.quadraticForm x), sigPos (g.quadraticForm x)) =
      (sigNeg (h.quadraticForm (f x)), sigPos (h.quadraticForm (f x))) :=
  Prod.ext
    (QuadraticMap.Equivalent.sigNeg_eq ⟨f.tangentQuadraticIsometry x⟩)
    (QuadraticMap.Equivalent.sigPos_eq ⟨f.tangentQuadraticIsometry x⟩)

/-- A metric is Lorentzian if and only if an isometric metric is Lorentzian. -/
theorem isLorentzian_iff (f : Isometry g h) : g.IsLorentzian ↔ h.IsLorentzian := by
  constructor
  · intro hg y
    rw [f.symm.sigNeg_eq y]
    exact hg (f.symm y)
  · intro hh x
    rw [f.sigNeg_eq x]
    exact hh (f x)

end PseudoRiemannianMetric.Isometry

namespace LorentzianMetric

/-- An isometry between Lorentzian metrics preserves their tangent pairings. -/
abbrev Isometry (g : LorentzianMetric I M) (h : LorentzianMetric J N) :=
  PseudoRiemannianMetric.Isometry g.toPseudoRiemannianMetric h.toPseudoRiemannianMetric

/-- The algebraic group of all self-isometries of a Lorentzian metric. -/
abbrev IsometryGroup (g : LorentzianMetric I M) := Isometry g g

variable (g : LorentzianMetric I M)
#synth Group (Isometry g g)

end LorentzianMetric

end AQFT
