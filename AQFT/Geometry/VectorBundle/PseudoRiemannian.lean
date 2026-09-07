import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Pseudo-Riemannian structures on vector bundles

Each fiber carries a continuous symmetric nondegenerate real pairing. Positivity
is not required, so this includes the indefinite pairings used in Lorentzian
geometry. The existing topology and real vector space structure are retained;
the pairing does not introduce a norm or a distance.

`PseudoRiemannianBundle` installs these fiber structures through the `Bundle`
scope. The general theory uses the fiber structures directly. Continuity and
smoothness are separate Prop-valued classes asserting regularity of the section
of the bilinear Hom bundle, including its changes of coordinates.

This follows Mathlib's `RiemannianBundle` and `IsContMDiffRiemannianBundle`
construction. The term pseudo-inner product here means a possibly indefinite symmetric
nondegenerate pairing, rather than a positive semidefinite inner product.

## References

* Mathlib.Geometry.Manifold.VectorBundle.Riemannian
* Christian Bär, Lorentzian Geometry, Section 1.1:
  https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf
-/

open Manifold Bundle
open scoped ContDiff

noncomputable section

namespace AQFT

/-- A symmetric nondegenerate real pairing on a real vector space with an existing
topology. No positivity or induced norm is required. -/
class PseudoInnerProductSpace (V : Type*) [TopologicalSpace V] [AddCommGroup V]
    [Module ℝ V] where
  /-- The continuous bilinear pairing. -/
  form : V →L[ℝ] V →L[ℝ] ℝ
  /-- The pairing is symmetric. -/
  symm (v w : V) : form v w = form w v
  /-- Both radicals of the pairing vanish. -/
  nondegenerate : form.toBilinForm.Nondegenerate

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

/-- The pseudo-inner product, as a continuous bilinear map. -/
abbrev pseudoInner [PseudoInnerProductSpace V] : V →L[ℝ] V →L[ℝ] ℝ :=
  PseudoInnerProductSpace.form

/-- The pseudo-inner product is symmetric. -/
theorem pseudoInner_comm [PseudoInnerProductSpace V] (v w : V) :
    pseudoInner v w = pseudoInner w v := PseudoInnerProductSpace.symm v w

/-- A vector pairing to zero with all vectors is zero. -/
theorem eq_zero_of_pseudoInner_left [PseudoInnerProductSpace V] (v : V)
    (h : ∀ w, pseudoInner v w = 0) : v = 0 :=
  PseudoInnerProductSpace.nondegenerate.1 v h

/-- A family of pseudo-inner products on the fibers, preserving the existing
topologies and vector space structures. Open the `Bundle` scope for fiber instances. -/
class PseudoRiemannianBundle {B : Type*} (V : B → Type*)
    [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] where
  /-- The pseudo-inner product structure of each fiber. -/
  fiber (b : B) : PseudoInnerProductSpace (V b)

end AQFT

namespace Bundle

/-- A pseudo-Riemannian bundle supplies pseudo-inner products on its fibers.
This instance leaves all topology, norm, and vector space instances unchanged. -/
scoped instance (priority := 80) {B : Type*} {V : B → Type*}
    [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
    [g : AQFT.PseudoRiemannianBundle V] (b : B) : AQFT.PseudoInnerProductSpace (V b) :=
  g.fiber b

end Bundle

namespace AQFT

section Bundles

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [∀ b, PseudoInnerProductSpace (V b)]

/-- The fiber pairings vary continuously as a section of the bilinear Hom bundle. -/
class IsContinuousPseudoRiemannianBundle (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
    [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)]
    [FiberBundle F V] [VectorBundle ℝ F V] [∀ b, PseudoInnerProductSpace (V b)] : Prop where
  /-- Continuity in the Hom bundle topology. -/
  continuous : Continuous (fun b ↦
    TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (pseudoInner (V := V b)))

/-- Pairing two continuous maps into the same fibers gives a continuous function. -/
theorem continuous_pseudoInner {M : Type*} [TopologicalSpace M]
    [h : IsContinuousPseudoRiemannianBundle F V]
    {b : M → B} {v w : ∀ x, V (b x)}
    (hv : Continuous (fun x ↦ TotalSpace.mk' F (b x) (v x)))
    (hw : Continuous (fun x ↦ TotalSpace.mk' F (b x) (w x))) :
    Continuous (fun x ↦ pseudoInner (v x) (w x)) := by
  have hb : Continuous b := (FiberBundle.continuous_proj F V).comp hv
  have he : Continuous (fun x ↦
      TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b x) (pseudoInner (v x) (w x))) :=
    (h.continuous.comp hb).clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hx := he.continuousAt (x := x)
  rw [FiberBundle.continuousAt_totalSpace] at hx
  exact hx.2

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B] {n n' : ℕ∞ω}

/-- The fiber pairings form a `C^n` section of the bilinear Hom bundle. -/
class IsContMDiffPseudoRiemannianBundle (IB : ModelWithCorners ℝ EB HB) (n : ℕ∞ω)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
    [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)]
    [FiberBundle F V] [VectorBundle ℝ F V] [∀ b, PseudoInnerProductSpace (V b)] : Prop where
  /-- Smoothness in the bilinear Hom bundle charts. -/
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (pseudoInner (V := V b)))

/-- Smooth fiber pairings are continuous. -/
theorem IsContMDiffPseudoRiemannianBundle.toIsContinuous
    [h : IsContMDiffPseudoRiemannianBundle IB n F V] :
    IsContinuousPseudoRiemannianBundle F V :=
  ⟨h.contMDiff.continuous⟩

/-- A pseudo-Riemannian bundle of regularity `n` also has every lower regularity. -/
theorem IsContMDiffPseudoRiemannianBundle.of_le
    [h : IsContMDiffPseudoRiemannianBundle IB n F V] (hn : n' ≤ n) :
    IsContMDiffPseudoRiemannianBundle IB n' F V :=
  ⟨h.contMDiff.of_le hn⟩

instance {a : ℕ∞ω} [IsContMDiffPseudoRiemannianBundle IB ∞ F V] [h : ENat.LEInfty a] :
    IsContMDiffPseudoRiemannianBundle IB a F V :=
  IsContMDiffPseudoRiemannianBundle.of_le h.out

/-- Pairing two `C^n` maps into the same fibers gives a `C^n` real-valued function. -/
theorem contMDiff_pseudoInner
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    [h : IsContMDiffPseudoRiemannianBundle IB n F V]
    {b : M → B} {v w : ∀ x, V (b x)}
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F (b x) (v x)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F (b x) (w x))) :
    ContMDiff IM 𝓘(ℝ) n (fun x ↦ pseudoInner (v x) (w x)) := by
  have hb : ContMDiff IM IB n b := (contMDiff_proj V).comp hv
  have he : ContMDiff IM (IB.prod 𝓘(ℝ)) n (fun x ↦
      TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b x) (pseudoInner (v x) (w x))) :=
    (h.contMDiff.comp hb).clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  intro x
  have hx := he.contMDiffAt (x := x)
  rw [contMDiffAt_totalSpace] at hx
  exact hx.2

end Bundles

end AQFT
