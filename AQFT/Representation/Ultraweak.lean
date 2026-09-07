import AQFT.Representation.Automorphism
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Ultraweak continuity of represented automorphisms

Ultraweak continuity is defined by continuity of all sums of matrix coefficients
over pairs of square-summable sequences. This is the usual series-test definition
of ultraweak continuity on bounded operators, applied to the represented orbits
`π (α f a)`. It does not choose or construct a Banach-space predual.

For every fixed `a`, these operators have norm at most `‖a‖`: star-algebra
homomorphisms are contractive and star-algebra automorphisms preserve the norm.
The uniform bound makes weak and ultraweak continuity equivalent. The forward
implication uses uniformly summable bounds on the coefficient series; the reverse
implication uses sequences supported at a single index. No separability assumption
on the Hilbert space is needed.

Reference: Jacob Lurie, *Math 261y: von Neumann Algebras*, Lecture 5, page 3,
[the ultraweak topology](https://www.math.ias.edu/~lurie/261ynotes/lecture5.pdf).
-/

open scoped InnerProductSpace

namespace AQFT.Automorphism

variable {H : Type*} [NormedAddCommGroup H]

private theorem summable_norm_mul {x y : ℕ → H}
    (hx : Summable (fun n ↦ ‖x n‖ ^ 2)) (hy : Summable (fun n ↦ ‖y n‖ ^ 2)) :
    Summable (fun n ↦ ‖x n‖ * ‖y n‖) := by
  apply Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun n ↦ ?_) (hx.add hy)
  nlinarith [sq_nonneg (‖x n‖ - ‖y n‖)]

variable [InnerProductSpace ℂ H]

private theorem norm_matrixCoefficient_le (T : H →L[ℂ] H) (x y : H) :
    ‖⟪x, T y⟫_ℂ‖ ≤ ‖T‖ * (‖x‖ * ‖y‖) := by
  calc
    ‖⟪x, T y⟫_ℂ‖ ≤ ‖x‖ * ‖T y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg x)
    _ = ‖T‖ * (‖x‖ * ‖y‖) := by ring

/-- The coefficient series defining the ultraweak tests always converges. -/
theorem summable_matrixCoefficient (T : H →L[ℂ] H) {x y : ℕ → H}
    (hx : Summable (fun n ↦ ‖x n‖ ^ 2)) (hy : Summable (fun n ↦ ‖y n‖ ^ 2)) :
    Summable (fun n ↦ ⟪x n, T (y n)⟫_ℂ) :=
  ((summable_norm_mul hx hy).mul_left ‖T‖).of_norm_bounded
    (fun n ↦ norm_matrixCoefficient_le T (x n) (y n))

variable {X B : Type*} [TopologicalSpace X] [CStarAlgebra B] [CompleteSpace H]

/-- Ultraweak continuity of automorphism orbits in a chosen representation,
tested on every pair of square-summable sequences of Hilbert-space vectors. -/
def IsUltraweaklyContinuous (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (α : X → (B ≃⋆ₐ[ℂ] B)) : Prop :=
  ∀ (a : B) (x y : ℕ → H),
    Summable (fun n ↦ ‖x n‖ ^ 2) → Summable (fun n ↦ ‖y n‖ ^ 2) →
      Continuous (fun f ↦ ∑' n, ⟪x n, π (α f a) (y n)⟫_ℂ)

/-- Weakly continuous automorphism orbits are ultraweakly continuous by a uniform norm bound. -/
theorem IsWeaklyContinuous.isUltraweaklyContinuous
    {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)} {α : X → (B ≃⋆ₐ[ℂ] B)}
    (h : IsWeaklyContinuous π α) : IsUltraweaklyContinuous π α := by
  intro a x y hx hy
  refine continuous_tsum (fun n ↦ h a (x n) (y n))
    ((summable_norm_mul hx hy).mul_left ‖a‖) (fun n f ↦ ?_)
  have hbound : ‖π (α f a)‖ ≤ ‖a‖ :=
    (NonUnitalStarAlgHom.norm_apply_le π (α f a)).trans_eq
      (StarAlgEquiv.norm_map (α f) a)
  exact (norm_matrixCoefficient_le (π (α f a)) (x n) (y n)).trans
    (mul_le_mul_of_nonneg_right hbound (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

/-- Single-term series recover every weak matrix coefficient. -/
theorem IsUltraweaklyContinuous.isWeaklyContinuous
    {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)} {α : X → (B ≃⋆ₐ[ℂ] B)}
    (h : IsUltraweaklyContinuous π α) : IsWeaklyContinuous π α := by
  intro a x y
  let xs : ℕ → H := Pi.single 0 x
  let ys : ℕ → H := Pi.single 0 y
  have hxs : Summable (fun n ↦ ‖xs n‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [xs, hn]
  have hys : Summable (fun n ↦ ‖ys n‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [ys, hn]
  have hsum (f : X) : (∑' n, ⟪xs n, π (α f a) (ys n)⟫_ℂ) = ⟪x, π (α f a) y⟫_ℂ := by
    rw [tsum_eq_single 0]
    · simp [xs, ys]
    · intro n hn
      simp [xs, ys, hn]
  simpa only [hsum] using h a xs ys hxs hys

/-- Weak and ultraweak continuity agree for represented star-algebra automorphism orbits. -/
theorem isWeaklyContinuous_iff_isUltraweaklyContinuous
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (α : X → (B ≃⋆ₐ[ℂ] B)) :
    IsWeaklyContinuous π α ↔ IsUltraweaklyContinuous π α :=
  ⟨IsWeaklyContinuous.isUltraweaklyContinuous, IsUltraweaklyContinuous.isWeaklyContinuous⟩

/-- Strong and ultraweak continuity also agree for these represented automorphism orbits. -/
theorem isStronglyContinuous_iff_isUltraweaklyContinuous
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (α : X → (B ≃⋆ₐ[ℂ] B)) :
    IsStronglyContinuous π α ↔ IsUltraweaklyContinuous π α :=
  (isWeaklyContinuous_iff_isStronglyContinuous (π := π) (α := α)).symm.trans
    (isWeaklyContinuous_iff_isUltraweaklyContinuous π α)

end AQFT.Automorphism
