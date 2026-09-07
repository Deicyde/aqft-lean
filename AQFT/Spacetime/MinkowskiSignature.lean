import AQFT.Spacetime.Minkowski
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Signature of Minkowski space

The Minkowski quadratic form has one negative direction and `n` positive directions.
The proof uses Mathlib's signature, defined by the maximal dimensions of definite
subspaces, and the time and spatial coordinate subspaces. It includes `n = 0`.

Reference: Christian Bär, [*Lorentzian Geometry*, §1.1]
(https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf).
-/

noncomputable section

namespace AQFT.Spacetime.MinkowskiSpace

/-- The quadratic form associated with the Minkowski bilinear form. -/
def quadraticForm (n : ℕ) : QuadraticForm ℝ (MinkowskiSpace n) :=
  (bilinearForm n).toBilinForm.toQuadraticMap

@[simp]
theorem quadraticForm_apply {n : ℕ} (v : MinkowskiSpace n) :
    quadraticForm n v = -(v.1 ^ 2) + ‖v.2‖ ^ 2 := by
  simp [quadraticForm, pow_two]

private abbrev timeSubspace (n : ℕ) : Submodule ℝ (MinkowskiSpace n) :=
  Submodule.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))

private abbrev spaceSubspace (n : ℕ) : Submodule ℝ (MinkowskiSpace n) :=
  Submodule.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))

private theorem finrank_timeSubspace (n : ℕ) :
    Module.finrank ℝ (timeSubspace n) = 1 := by
  exact (Submodule.fstEquiv ℝ ℝ (EuclideanSpace ℝ (Fin n))).finrank_eq.trans
    (Module.finrank_self ℝ)

private theorem finrank_spaceSubspace (n : ℕ) :
    Module.finrank ℝ (spaceSubspace n) = n := by
  exact (Submodule.sndEquiv ℝ ℝ (EuclideanSpace ℝ (Fin n))).finrank_eq.trans
    finrank_euclideanSpace_fin

private theorem negDef_timeSubspace (n : ℕ) :
    ((-quadraticForm n).restrict (timeSubspace n)).PosDef := by
  intro v hv
  have hspace : v.1.2 = 0 := v.2
  have htime : v.1.1 ≠ 0 :=
    (Submodule.fstEquiv ℝ ℝ (EuclideanSpace ℝ (Fin n))).map_ne_zero_iff.mpr hv
  simpa [QuadraticMap.restrict_apply, hspace] using sq_pos_of_ne_zero htime

private theorem posDef_spaceSubspace (n : ℕ) :
    ((quadraticForm n).restrict (spaceSubspace n)).PosDef := by
  intro v hv
  have htime : v.1.1 = 0 := v.2
  have hspace : v.1.2 ≠ 0 :=
    (Submodule.sndEquiv ℝ ℝ (EuclideanSpace ℝ (Fin n))).map_ne_zero_iff.mpr hv
  simpa [QuadraticMap.restrict_apply, htime] using sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hspace)

/-- Minkowski space has exactly one negative direction. -/
@[simp]
theorem quadraticForm_sigNeg (n : ℕ) : sigNeg (quadraticForm n) = 1 := by
  have hlower := le_sigNeg_of_negDef (quadraticForm n) (negDef_timeSubspace n)
  rw [finrank_timeSubspace] at hlower
  have hupper := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := -quadraticForm n) (V := spaceSubspace n) (by
      intro v hv
      have htime : v.1 = 0 := hv
      simp [htime])
  rw [sigPos_neg, finrank_spaceSubspace] at hupper
  have hdim : Module.finrank ℝ (MinkowskiSpace n) = 1 + n := by
    exact (Module.finrank_prod (R := ℝ) (M := ℝ)
      (M' := EuclideanSpace ℝ (Fin n))).trans (by simp)
  rw [hdim] at hupper
  omega

/-- Minkowski space with `n` spatial coordinates has exactly `n` positive directions. -/
@[simp]
theorem quadraticForm_sigPos (n : ℕ) : sigPos (quadraticForm n) = n := by
  have hlower := le_sigPos_of_posDef (quadraticForm n) (posDef_spaceSubspace n)
  rw [finrank_spaceSubspace] at hlower
  have hupper := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := quadraticForm n) (V := timeSubspace n) (by
      intro v hv
      have hspace : v.2 = 0 := hv
      simpa [hspace] using neg_nonpos.mpr (sq_nonneg v.1))
  rw [finrank_timeSubspace] at hupper
  have hdim : Module.finrank ℝ (MinkowskiSpace n) = 1 + n := by
    exact (Module.finrank_prod (R := ℝ) (M := ℝ)
      (M' := EuclideanSpace ℝ (Fin n))).trans (by simp)
  rw [hdim] at hupper
  omega

end AQFT.Spacetime.MinkowskiSpace
