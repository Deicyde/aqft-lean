import AQFT.Geometry.PseudoRiemannian.Isometry
import AQFT.Spacetime.MinkowskiMetric

/-!
# Isometries of Minkowski space

Translations and time reversal are smooth isometries of the Minkowski metric.
Their metric preservation is proved using their actual differentials. Time reversal
is included because the isometry group has no time-orientation restriction.

Reference: Christian Bär, [*Lorentzian Geometry*, §1.1]
(https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf).
-/

open Manifold
open scoped ContDiff

noncomputable section

namespace AQFT.Spacetime.MinkowskiSpace

variable {n : ℕ}

private theorem fderiv_addLeft (a x : MinkowskiSpace n) :
    fderiv ℝ (fun y ↦ a + y) x = ContinuousLinearMap.id ℝ (MinkowskiSpace n) :=
  ((hasFDerivAt_id x).const_add a).fderiv

/-- Translation by a spacetime vector is a Minkowski isometry. -/
def translation (a : MinkowskiSpace n) :
    PseudoRiemannianMetric.Isometry (metric n) (metric n) where
  toDiffeomorph :=
    { toEquiv := Equiv.addLeft a
      contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
      contMDiff_invFun := (contDiff_const.add contDiff_id).contMDiff }
  map_form x v w := by
    change bilinearForm n
      (mfderiv 𝓘(ℝ, MinkowskiSpace n) 𝓘(ℝ, MinkowskiSpace n) (fun y ↦ a + y) x v)
      (mfderiv 𝓘(ℝ, MinkowskiSpace n) 𝓘(ℝ, MinkowskiSpace n) (fun y ↦ a + y) x w) =
      bilinearForm n v w
    simp only [mfderiv_eq_fderiv]
    erw [fderiv_addLeft a x]
    rfl

@[simp]
theorem translation_apply (a x : MinkowskiSpace n) : translation a x = a + x := rfl

/-- The differential of a translation is the identity. -/
@[simp]
theorem mfderiv_translation (a x : MinkowskiSpace n) :
    mfderiv 𝓘(ℝ, MinkowskiSpace n) 𝓘(ℝ, MinkowskiSpace n) (translation a) x =
      ContinuousLinearMap.id ℝ (MinkowskiSpace n) := by
  change mfderiv 𝓘(ℝ, MinkowskiSpace n) 𝓘(ℝ, MinkowskiSpace n) (fun y ↦ a + y) x = _
  simp only [mfderiv_eq_fderiv]
  exact fderiv_addLeft a x

@[simp]
theorem translation_zero : translation (0 : MinkowskiSpace n) = 1 := by
  apply PseudoRiemannianMetric.Isometry.ext
  intro x
  simp

/-- Composition of translations corresponds to addition of their displacement vectors. -/
theorem translation_add (a b : MinkowskiSpace n) :
    translation (a + b) = translation a * translation b := by
  apply PseudoRiemannianMetric.Isometry.ext
  intro x
  simp [add_assoc]

@[simp]
theorem translation_neg (a : MinkowskiSpace n) : translation (-a) = (translation a)⁻¹ := by
  apply PseudoRiemannianMetric.Isometry.ext
  intro x
  rfl

private def timeReversalLinear (n : ℕ) : MinkowskiSpace n ≃L[ℝ] MinkowskiSpace n :=
  (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).prodCongr
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))

/-- Reversing the time coordinate preserves the Minkowski metric. -/
def timeReversal (n : ℕ) : PseudoRiemannianMetric.Isometry (metric n) (metric n) where
  toDiffeomorph := (timeReversalLinear n).toDiffeomorph
  map_form x v w := by
    simp only [metric_form, ContinuousLinearEquiv.coe_toDiffeomorph, mfderiv_eq_fderiv,
      (timeReversalLinear n).hasFDerivAt.fderiv]
    change bilinearForm n (-v.1, v.2) (-w.1, w.2) = bilinearForm n v w
    erw [bilinearForm_apply, bilinearForm_apply]
    simp

@[simp]
theorem timeReversal_apply (x : MinkowskiSpace n) : timeReversal n x = (-x.1, x.2) := rfl

/-- Applying time reversal twice is the identity isometry. -/
@[simp]
theorem timeReversal_mul_self (n : ℕ) : timeReversal n * timeReversal n = 1 := by
  apply PseudoRiemannianMetric.Isometry.ext
  intro x
  simp

/-- Time reversal is a nonidentity element of the full isometry group. -/
theorem timeReversal_ne_one (n : ℕ) : timeReversal n ≠ 1 := by
  intro h
  have ht := congrArg (fun f : PseudoRiemannianMetric.Isometry (metric n) (metric n) ↦
    (f (1, 0)).1) h
  norm_num at ht

end AQFT.Spacetime.MinkowskiSpace
