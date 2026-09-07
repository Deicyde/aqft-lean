import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Strongly continuous unitary representations

A `UnitaryRepresentation G H` is a group homomorphism into the linear isometric
equivalences of a complex Hilbert space `H`, with continuous vector orbits.
Thus continuity is in the strong operator sense. No operator-norm continuity
is imposed.

Conjugation gives an action by star-algebra automorphisms of the bounded
operators on `H`. It sends `T` to `U(g) T U(g)*` and can be applied to the
image of an abstract algebra under any star-algebra representation.

References:
* [Haag–Kastler covariance]
  (https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory#Haag%E2%80%93Kastler_axioms).
* Mathlib's `Unitary.linearIsometryEquiv` and `Unitary.conjStarAlgAut`, used below.
-/

noncomputable section

namespace AQFT

/-- A unitary representation whose orbit map is continuous for every vector. -/
structure UnitaryRepresentation (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends G →* (H ≃ₗᵢ[ℂ] H) where
  /-- Strong continuity: every vector orbit is continuous. -/
  continuous_apply (v : H) : Continuous (fun g ↦ toMonoidHom g v)

namespace UnitaryRepresentation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance : FunLike (UnitaryRepresentation G H) G (H ≃ₗᵢ[ℂ] H) where
  coe U := U.toMonoidHom
  coe_injective U V h := by
    cases U
    cases V
    congr
    exact DFunLike.coe_injective h

instance : MonoidHomClass (UnitaryRepresentation G H) G (H ≃ₗᵢ[ℂ] H) where
  map_one U := U.toMonoidHom.map_one
  map_mul U := U.toMonoidHom.map_mul

@[simp] theorem one_apply (U : UnitaryRepresentation G H) (v : H) : U 1 v = v := by
  rw [map_one]
  rfl

@[simp] theorem mul_apply (U : UnitaryRepresentation G H) (g h : G) (v : H) :
    U (g * h) v = U g (U h v) := by
  rw [map_mul]
  rfl

/-- The unitary for the inverse group element is the adjoint bounded operator. -/
theorem map_inv_eq_star (U : UnitaryRepresentation G H) (g : G) :
    (U g⁻¹ : H →L[ℂ] H) = star (U g : H →L[ℂ] H) := by
  rw [map_inv, ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
  rfl

/-- The native star-algebra action on bounded operators induced by unitary conjugation. -/
def conjugation (U : UnitaryRepresentation G H) :
    G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :=
  (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H)).comp
    (Unitary.linearIsometryEquiv.symm.toMonoidHom.comp U.toMonoidHom)

/-- Conjugation agrees with Mathlib's automorphism associated to a linear isometry. -/
theorem conjugation_apply (U : UnitaryRepresentation G H) (g : G) :
    U.conjugation g = (U g).conjStarAlgEquiv :=
  Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv (U g)

@[simp] theorem conjugation_apply_apply (U : UnitaryRepresentation G H)
    (g : G) (T : H →L[ℂ] H) (v : H) :
    U.conjugation g T v = U g (T (U g⁻¹ v)) := by
  simp only [conjugation_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    map_inv, LinearIsometryEquiv.inv_def]

/-- The usual formula `U(g) T U(g)*` for the induced automorphism. -/
theorem conjugation_eq_mul_star (U : UnitaryRepresentation G H) (g : G) (T : H →L[ℂ] H) :
    U.conjugation g T = (U g : H →L[ℂ] H) * T * star (U g : H →L[ℂ] H) := by
  rw [conjugation_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply,
    ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
  rfl

@[simp] theorem conjugation_one_apply (U : UnitaryRepresentation G H) (T : H →L[ℂ] H) :
    U.conjugation 1 T = T := by
  rw [map_one]
  rfl

@[simp] theorem conjugation_mul_apply (U : UnitaryRepresentation G H)
    (g h : G) (T : H →L[ℂ] H) :
    U.conjugation (g * h) T = U.conjugation g (U.conjugation h T) := by
  rw [map_mul]
  rfl

/-- Inversion of the group element gives the inverse conjugation automorphism. -/
@[simp] theorem conjugation_inv (U : UnitaryRepresentation G H) (g : G) :
    U.conjugation g⁻¹ = (U.conjugation g).symm := by
  rw [map_inv]
  rfl

/-- The trivial strongly continuous unitary representation. -/
def trivial (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    UnitaryRepresentation G H where
  toMonoidHom := 1
  continuous_apply _ := continuous_const

@[simp] theorem trivial_apply (g : G) (v : H) : trivial G H g v = v := rfl

end UnitaryRepresentation

end AQFT
