import AQFT.Geometry.PseudoRiemannian.Basic
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Isometries of pseudo-Riemannian metrics

An isometry is a smooth diffeomorphism whose differential preserves the tangent
bilinear forms. This definition applies to indefinite metrics. Self-isometries form
an algebraic group under composition; no topology or Lie group structure is asserted.

## References

* Christian Bär, Lorentzian Geometry, Section 1.1:
  https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf
-/

open Manifold
open scoped ContDiff

noncomputable section

namespace AQFT.PseudoRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type*} [TopologicalSpace H]
  {H' : Type*} [TopologicalSpace H']
  {H'' : Type*} [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold K ∞ P]

/-- A smooth diffeomorphism preserving the pseudo-Riemannian tangent pairings. -/
structure Isometry (g : PseudoRiemannianMetric I M) (h : PseudoRiemannianMetric J N) where
  /-- The underlying smooth diffeomorphism. -/
  toDiffeomorph : M ≃ₘ⟮I, J⟯ N
  /-- The differential preserves the metric on each tangent space. -/
  map_form (x : M) (v w : TangentSpace I x) :
    h.form (toDiffeomorph x) (mfderiv I J toDiffeomorph x v)
      (mfderiv I J toDiffeomorph x w) = g.form x v w

namespace Isometry

variable {g : PseudoRiemannianMetric I M} {h : PseudoRiemannianMetric J N}
  {k : PseudoRiemannianMetric K P}

instance : CoeFun (Isometry g h) (fun _ ↦ M → N) := ⟨fun f ↦ f.toDiffeomorph⟩

@[simp]
theorem coe_toDiffeomorph (f : Isometry g h) : ⇑f.toDiffeomorph = f := rfl

/-- Metric isometries are equal when their underlying maps agree. -/
@[ext]
theorem ext {f₁ f₂ : Isometry g h} (h : ∀ x, f₁ x = f₂ x) : f₁ = f₂ := by
  cases f₁
  cases f₂
  congr 1
  exact Diffeomorph.ext h

/-- Every metric isometry is smooth. -/
protected theorem contMDiff (f : Isometry g h) : ContMDiff I J ∞ f :=
  f.toDiffeomorph.contMDiff

/-- Every metric isometry is differentiable. -/
protected theorem mdifferentiable (f : Isometry g h) : MDifferentiable I J f :=
  f.toDiffeomorph.mdifferentiable (by simp)

/-- The identity is a metric isometry. -/
protected def refl (g : PseudoRiemannianMetric I M) : Isometry g g where
  toDiffeomorph := Diffeomorph.refl I M ∞
  map_form x v w := by
    simp only [Diffeomorph.coe_refl, mfderiv_id]
    rfl

@[simp]
theorem refl_apply (x : M) : Isometry.refl g x = x := rfl

/-- Composition of metric isometries, in the order of `Equiv.trans`. -/
protected def trans (f : Isometry g h) (f' : Isometry h k) : Isometry g k where
  toDiffeomorph := f.toDiffeomorph.trans f'.toDiffeomorph
  map_form x v w := by
    simp only [Diffeomorph.coe_trans]
    rw [mfderiv_comp x (f'.mdifferentiable _) (f.mdifferentiable _)]
    change k.form (f' (f x))
      (mfderiv J K f' (f x) (mfderiv I J f x v))
      (mfderiv J K f' (f x) (mfderiv I J f x w)) = g.form x v w
    rw [f'.map_form, f.map_form]

@[simp]
theorem trans_apply (f : Isometry g h) (f' : Isometry h k) (x : M) :
    f.trans f' x = f' (f x) := rfl

/-- The differential of a diffeomorphism cancels that of its inverse. -/
theorem mfderiv_apply_symm (f : Isometry g h) (y : N) (v : TangentSpace J y) :
    mfderiv I J f (f.toDiffeomorph.symm y)
      (mfderiv J I f.toDiffeomorph.symm y v) = v := by
  have hcomp : (f : M → N) ∘ f.toDiffeomorph.symm = id :=
    funext f.toDiffeomorph.apply_symm_apply
  have hd := mfderiv_comp_apply y
    (f.mdifferentiable (f.toDiffeomorph.symm y))
    (f.toDiffeomorph.symm.mdifferentiable (by simp) y) v
  rw [hcomp, mfderiv_id] at hd
  exact hd.symm

/-- The inverse diffeomorphism of a metric isometry preserves the metric. -/
protected def symm (f : Isometry g h) : Isometry h g where
  toDiffeomorph := f.toDiffeomorph.symm
  map_form y v w := by
    have hf := f.map_form (f.toDiffeomorph.symm y)
      (mfderiv J I f.toDiffeomorph.symm y v) (mfderiv J I f.toDiffeomorph.symm y w)
    rw [f.toDiffeomorph.apply_symm_apply] at hf
    erw [f.mfderiv_apply_symm y v, f.mfderiv_apply_symm y w] at hf
    exact hf.symm

@[simp]
theorem symm_apply_apply (f : Isometry g h) (x : M) : f.symm (f x) = x :=
  f.toDiffeomorph.symm_apply_apply x

@[simp]
theorem apply_symm_apply (f : Isometry g h) (y : N) : f (f.symm y) = y :=
  f.toDiffeomorph.apply_symm_apply y

@[simp]
theorem symm_symm (f : Isometry g h) : f.symm.symm = f := by
  ext x
  rfl

@[simp]
theorem trans_refl (f : Isometry g h) : f.trans (Isometry.refl h) = f := by
  ext x
  rfl

@[simp]
theorem refl_trans (f : Isometry g h) : (Isometry.refl g).trans f = f := by
  ext x
  rfl

@[simp]
theorem self_trans_symm (f : Isometry g h) : f.trans f.symm = Isometry.refl g := by
  ext x
  exact f.symm_apply_apply x

@[simp]
theorem symm_trans_self (f : Isometry g h) : f.symm.trans f = Isometry.refl h := by
  ext y
  exact f.apply_symm_apply y

/-- Self-isometries form a group, with multiplication given by function composition. -/
instance : Group (Isometry g g) where
  mul f f' := f'.trans f
  one := Isometry.refl g
  inv f := f.symm
  mul_assoc f f' f'' := by ext x; rfl
  one_mul f := by ext x; rfl
  mul_one f := by ext x; rfl
  inv_mul_cancel f := by ext x; exact f.symm_apply_apply x

@[simp]
theorem mul_apply (f f' : Isometry g g) (x : M) : (f * f') x = f (f' x) := rfl

@[simp]
theorem one_apply (x : M) : (1 : Isometry g g) x = x := rfl

@[simp]
theorem inv_apply (f : Isometry g g) (x : M) : f⁻¹ x = f.symm x := rfl

/-- The self-isometry group acts on the underlying manifold by evaluation. -/
instance : MulAction (Isometry g g) M where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
theorem smul_apply (f : Isometry g g) (x : M) : f • x = f x := rfl

end Isometry

end AQFT.PseudoRiemannianMetric
