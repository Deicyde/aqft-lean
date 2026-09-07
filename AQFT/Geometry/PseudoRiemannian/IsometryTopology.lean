import AQFT.Geometry.PseudoRiemannian.Isometry
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Topology on pseudo-Riemannian isometries

Isometries carry the topology induced by their forward and inverse maps in the
product of compact-open continuous-map spaces. Thus a family of isometries is
continuous exactly when its forward and inverse maps are continuous in the
compact-open topology. Inversion interchanges these two coordinates.

For a locally compact manifold, composition and joint evaluation are continuous,
so self-isometries form a topological group acting continuously on the manifold.
Hausdorffness of the manifold gives Hausdorffness of this group. This construction
does not assert a Lie group structure or any topology involving derivatives.

The compact-open composition and evaluation results are supplied by Mathlib's
[`Topology.CompactOpen`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CompactOpen.html).
See its `ContinuousMap.continuous_comp'` for the composition theorem from
Bourbaki, *Topologie Générale*, Chapter X, §3, no. 4, Proposition 9.
-/

open Manifold Topology
open scoped ContDiff

noncomputable section

namespace AQFT.PseudoRiemannianMetric.Isometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  {g : PseudoRiemannianMetric I M} {h : PseudoRiemannianMetric J N}

/-- Forget the differential and metric-preservation data of an isometry. -/
def toHomeomorph (f : Isometry g h) : M ≃ₜ N :=
  f.toDiffeomorph.toHomeomorph

@[simp] theorem coe_toHomeomorph (f : Isometry g h) : ⇑f.toHomeomorph = f := rfl

@[simp] theorem symm_toHomeomorph (f : Isometry g h) :
    f.symm.toHomeomorph = f.toHomeomorph.symm := rfl

/-- An isometry viewed as a continuous map. -/
def toContinuousMap (f : Isometry g h) : C(M, N) :=
  ⟨f, f.toHomeomorph.continuous⟩

@[simp] theorem coe_toContinuousMap (f : Isometry g h) : ⇑f.toContinuousMap = f := rfl

/-- Forward and inverse maps, each with the compact-open topology. -/
def toContinuousMapPair (f : Isometry g h) : C(M, N) × C(N, M) :=
  (f.toContinuousMap, f.symm.toContinuousMap)

/-- The compact-open topology on both the map and its inverse. -/
instance : TopologicalSpace (Isometry g h) :=
  TopologicalSpace.induced toContinuousMapPair inferInstance

theorem isInducing_toContinuousMapPair :
    IsInducing (toContinuousMapPair : Isometry g h → C(M, N) × C(N, M)) := ⟨rfl⟩

theorem isEmbedding_toContinuousMapPair :
    IsEmbedding (toContinuousMapPair : Isometry g h → C(M, N) × C(N, M)) := by
  refine ⟨isInducing_toContinuousMapPair, ?_⟩
  intro f₁ f₂ hf
  exact Isometry.ext fun x ↦ congrArg (fun p : C(M, N) × C(N, M) ↦ p.1 x) hf

instance [T2Space M] [T2Space N] : T2Space (Isometry g h) :=
  isEmbedding_toContinuousMapPair.t2Space

/-- Forgetting an isometry's inverse is continuous in the compact-open topology. -/
theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : Isometry g h → C(M, N)) :=
  continuous_fst.comp isInducing_toContinuousMapPair.continuous

/-- The inverse map depends continuously on the isometry in the compact-open topology. -/
theorem continuous_symm_toContinuousMap :
    Continuous (fun f : Isometry g h ↦ f.symm.toContinuousMap) :=
  continuous_snd.comp isInducing_toContinuousMapPair.continuous

/-- Continuity of isometries is compact-open continuity of both maps and inverses. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → Isometry g h} :
    Continuous f ↔ Continuous (fun x ↦ (f x).toContinuousMap) ∧
      Continuous (fun x ↦ (f x).symm.toContinuousMap) := by
  rw [isInducing_toContinuousMapPair.continuous_iff]
  exact continuous_prodMk

/-- Inverting an isometry is continuous. -/
theorem continuous_symm : Continuous (Isometry.symm : Isometry g h → Isometry h g) := by
  rw [continuous_iff]
  simpa only [symm_symm] using
    And.intro continuous_symm_toContinuousMap continuous_toContinuousMap

/-- Evaluation at a fixed point is continuous without local compactness. -/
theorem continuous_apply (x : M) : Continuous (fun f : Isometry g h ↦ f x) :=
  (continuous_eval_const x : Continuous (fun f : C(M, N) ↦ f x)).comp
    continuous_toContinuousMap

/-- Isometry evaluation is jointly continuous on a locally compact manifold. -/
theorem continuous_eval [LocallyCompactSpace M] :
    Continuous (fun p : Isometry g h × M ↦ p.1 p.2) :=
  (continuous_toContinuousMap.comp continuous_fst).eval continuous_snd

instance : ContinuousInv (Isometry g g) := ⟨continuous_symm⟩

instance [LocallyCompactSpace M] : ContinuousMul (Isometry g g) where
  continuous_mul := by
    rw [continuous_iff]
    constructor
    · change Continuous (fun p : Isometry g g × Isometry g g ↦
        p.1.toContinuousMap.comp p.2.toContinuousMap)
      exact (continuous_toContinuousMap.comp continuous_fst).compCM
        (continuous_toContinuousMap.comp continuous_snd)
    · change Continuous (fun p : Isometry g g × Isometry g g ↦
        p.2.symm.toContinuousMap.comp p.1.symm.toContinuousMap)
      exact (continuous_symm_toContinuousMap.comp continuous_snd).compCM
        (continuous_symm_toContinuousMap.comp continuous_fst)

/-- Self-isometries form a topological group under composition. -/
instance [LocallyCompactSpace M] : IsTopologicalGroup (Isometry g g) where

/-- The natural action of self-isometries on the manifold is continuous. -/
instance [LocallyCompactSpace M] : ContinuousSMul (Isometry g g) M :=
  ⟨continuous_eval⟩

end AQFT.PseudoRiemannianMetric.Isometry
