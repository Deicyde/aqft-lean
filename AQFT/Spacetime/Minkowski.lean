import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Minkowski space

Minkowski space with `n` spatial dimensions is `ℝ × EuclideanSpace ℝ (Fin n)`.
Its bilinear form is
\[
  \eta((t,x),(s,y)) = -ts + \langle x,y\rangle,
\]
with signature convention $(-,+,\ldots,+)$. The ambient norm supplies the usual
topology; the indefinite form does not define that norm.

This file proves symmetry and nondegeneracy of the continuous bilinear form,
and records timelike, spatial, and nonzero null examples.

Reference: Christian Bär, [*Lorentzian Geometry*, §1.1]
(https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf).
-/

noncomputable section

namespace AQFT.Spacetime

/-- Minkowski space with one time coordinate and `n` spatial coordinates. -/
def MinkowskiSpace (n : ℕ) := ℝ × EuclideanSpace ℝ (Fin n)

namespace MinkowskiSpace

variable {n : ℕ}

instance : NormedAddCommGroup (MinkowskiSpace n) :=
  inferInstanceAs (NormedAddCommGroup (ℝ × EuclideanSpace ℝ (Fin n)))

instance : NormedSpace ℝ (MinkowskiSpace n) :=
  inferInstanceAs (NormedSpace ℝ (ℝ × EuclideanSpace ℝ (Fin n)))

instance : FiniteDimensional ℝ (MinkowskiSpace n) :=
  inferInstanceAs (FiniteDimensional ℝ (ℝ × EuclideanSpace ℝ (Fin n)))

instance : CompleteSpace (MinkowskiSpace n) :=
  inferInstanceAs (CompleteSpace (ℝ × EuclideanSpace ℝ (Fin n)))

instance : SecondCountableTopology (MinkowskiSpace n) :=
  inferInstanceAs (SecondCountableTopology (ℝ × EuclideanSpace ℝ (Fin n)))

/-- The Minkowski form with negative time and positive spatial signs. -/
def bilinearForm (n : ℕ) : MinkowskiSpace n →L[ℝ] MinkowskiSpace n →L[ℝ] ℝ :=
  -(innerSL ℝ (E := ℝ)).bilinearComp
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))) +
    (innerSL ℝ (E := EuclideanSpace ℝ (Fin n))).bilinearComp
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n)))
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n)))

@[simp]
theorem bilinearForm_apply (v w : MinkowskiSpace n) :
    bilinearForm n v w = -(v.1 * w.1) + inner ℝ v.2 w.2 := by
  change -(inner ℝ v.1 w.1) + inner ℝ v.2 w.2 = _
  simp [mul_comm]

/-- The Minkowski form is jointly continuous. -/
theorem continuous_bilinearForm (n : ℕ) :
    Continuous (fun p : MinkowskiSpace n × MinkowskiSpace n ↦
      bilinearForm n p.1 p.2) :=
  (bilinearForm n).continuous₂

/-- The Minkowski form is symmetric. -/
theorem bilinearForm_symm (v w : MinkowskiSpace n) :
    bilinearForm n v w = bilinearForm n w v := by
  simp [real_inner_comm, mul_comm]

/-- A vector orthogonal to every vector for the Minkowski form is zero. -/
theorem eq_zero_of_forall_bilinearForm_eq_zero (v : MinkowskiSpace n)
    (h : ∀ w, bilinearForm n v w = 0) : v = 0 := by
  have ht : v.1 = 0 := by
    have hw := h (1, 0)
    erw [bilinearForm_apply] at hw
    simpa using hw
  have hx : v.2 = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hw := h (0, v.2)
    erw [bilinearForm_apply] at hw
    simpa using hw
  exact Prod.ext ht hx

/-- The algebraic bilinear form underlying the Minkowski form is nondegenerate. -/
theorem bilinearForm_nondegenerate (n : ℕ) :
    (bilinearForm n).toBilinForm.Nondegenerate := by
  constructor
  · intro v hv
    exact eq_zero_of_forall_bilinearForm_eq_zero v hv
  · intro v hv
    apply eq_zero_of_forall_bilinearForm_eq_zero v
    intro w
    rw [bilinearForm_symm]
    exact hv w

/-- A pure time vector has square $-t^2$. -/
@[simp]
theorem bilinearForm_time_time (t : ℝ) :
    bilinearForm n (t, 0) (t, 0) = -(t ^ 2) := by
  erw [bilinearForm_apply]
  simp [pow_two]

/-- A pure spatial vector has square equal to its Euclidean norm squared. -/
@[simp]
theorem bilinearForm_space_space (x : EuclideanSpace ℝ (Fin n)) :
    bilinearForm n (0, x) (0, x) = ‖x‖ ^ 2 := by
  erw [bilinearForm_apply]
  simp

/-- A unit time vector has negative square. -/
theorem bilinearForm_unitTime :
    bilinearForm n (1, 0) (1, 0) = -1 := by
  simp

/-- A spatial coordinate vector has positive square. -/
theorem bilinearForm_unitSpace (i : Fin n) :
    bilinearForm n (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1) = 1 := by
  simp

/-- A nonzero vector with zero Minkowski square in one spatial dimension. -/
def nullVector : MinkowskiSpace 1 := (1, EuclideanSpace.single 0 1)

theorem nullVector_ne_zero : nullVector ≠ 0 := by
  intro h
  have : (1 : ℝ) = 0 := congrArg Prod.fst h
  norm_num at this

@[simp]
theorem bilinearForm_nullVector : bilinearForm 1 nullVector nullVector = 0 := by
  rw [bilinearForm_apply]
  simp [nullVector]

end MinkowskiSpace

end AQFT.Spacetime
