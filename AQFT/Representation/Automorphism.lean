import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Operator continuity of represented algebra automorphisms

For a family of automorphisms of a complex C*-algebra and a representation on a
Hilbert space, weak continuity means continuity of every matrix coefficient of
every algebra orbit. Strong continuity means continuity of every vector orbit.
These conditions are equivalent because the family preserves multiplication and
the adjoint: the squared norm of an orbit is a matrix coefficient of `star a * a`.
No continuity in the operator norm is required.

The definitions apply to an arbitrary topological parameter space. In covariance,
the parameter space is the isometry group and the family is a group homomorphism.
Faithfulness is a separate condition on the representation and group action.

References:
* [Haag–Kastler covariance]
  (https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory#Haag%E2%80%93Kastler_axioms).
* Mathlib's `ContinuousLinearMapWOT.continuous_iff` and
  `PointwiseConvergenceCLM.continuous_of_continuous_eval` give the operator topologies.
-/

noncomputable section

open scoped InnerProductSpace Topology

namespace AQFT.Automorphism

variable {X B H : Type*} [TopologicalSpace X] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every represented algebra orbit is continuous in the weak operator topology. -/
def IsWeaklyContinuous (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (α : X → (B ≃⋆ₐ[ℂ] B)) : Prop :=
  ∀ (a : B) (x y : H), Continuous (fun f ↦ ⟪x, π (α f a) y⟫_ℂ)

/-- Every represented algebra orbit is continuous in the strong operator topology. -/
def IsStronglyContinuous (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (α : X → (B ≃⋆ₐ[ℂ] B)) : Prop :=
  ∀ (a : B) (y : H), Continuous (fun f ↦ π (α f a) y)

variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)} {α : X → (B ≃⋆ₐ[ℂ] B)}

/-- The matrix-coefficient definition agrees with Mathlib's weak operator topology. -/
theorem isWeaklyContinuous_iff_continuous_wot :
    IsWeaklyContinuous π α ↔
      ∀ a : B, Continuous (fun f ↦ ContinuousLinearMapWOT.ofCLM (π (α f a))) := by
  simp only [IsWeaklyContinuous, ContinuousLinearMapWOT.continuous_iff]
  exact forall_congr' fun _ ↦ forall_comm

/-- The vector-orbit definition agrees with Mathlib's pointwise operator topology. -/
theorem isStronglyContinuous_iff_continuous_pointwise :
    IsStronglyContinuous π α ↔
      ∀ a : B, Continuous (fun f ↦
        ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (π (α f a))) := by
  constructor
  · intro h a
    exact PointwiseConvergenceCLM.continuous_of_continuous_eval (h a)
  · intro h a y
    exact (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H y).continuous.comp (h a)

/-- Strong operator continuity implies weak operator continuity. -/
theorem IsStronglyContinuous.isWeaklyContinuous (h : IsStronglyContinuous π α) :
    IsWeaklyContinuous π α :=
  fun a _ y ↦ continuous_const.inner (h a y)

/-- Weak operator continuity of all algebra orbits implies strong continuity. -/
theorem IsWeaklyContinuous.isStronglyContinuous (h : IsWeaklyContinuous π α) :
    IsStronglyContinuous π α := by
  intro a y
  have hnorm : Continuous (fun f ↦ ‖π (α f a) y‖ ^ 2) := by
    convert Complex.continuous_re.comp (h (star a * a) y y) using 1
    ext f
    simp only [map_mul, map_star, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _
  have hdiff (z : H) : Continuous (fun f ↦ ‖z - π (α f a) y‖) := by
    have hs : Continuous (fun f ↦
        ‖z‖ ^ 2 - 2 * (⟪z, π (α f a) y⟫_ℂ).re + ‖π (α f a) y‖ ^ 2) :=
      (continuous_const.sub
        (continuous_const.mul (Complex.continuous_re.comp (h a z y)))).add hnorm
    convert hs.sqrt using 1
    ext f
    simpa only [norm_sub_sq (𝕜 := ℂ), RCLike.re_eq_complex_re] using
      (Real.sqrt_sq (norm_nonneg (z - π (α f a) y))).symm
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_self, norm_zero, norm_sub_rev] using
    (hdiff (π (α f a) y)).tendsto f

/-- For algebra automorphisms, weak and strong operator continuity are equivalent. -/
theorem isWeaklyContinuous_iff_isStronglyContinuous :
    IsWeaklyContinuous π α ↔ IsStronglyContinuous π α :=
  ⟨IsWeaklyContinuous.isStronglyContinuous, IsStronglyContinuous.isWeaklyContinuous⟩

end AQFT.Automorphism
