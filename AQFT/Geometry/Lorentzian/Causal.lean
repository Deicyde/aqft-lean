import AQFT.Geometry.Lorentzian.Basic
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Causal curves and spacelike separation

We use regular `C¹` curves on `[0,1]`: their tangent vectors are nonzero and have
nonpositive Lorentzian square everywhere, including the one-sided endpoint
derivatives. Null tangents are allowed. Requiring a nonzero continuous tangent
excludes reversal through zero velocity. The values of the curve outside the
interval do not matter.

Two points are causally related when they coincide or such a curve connects them
in either direction. Sets are spacelike separated when no pair of their points
is causally related. No global time orientation is chosen. We do not identify
this curve convention with piecewise `C¹` or locally Lipschitz conventions here.

Reference: Bunk, MacManus, and Schenkel, [*Lorentzian bordisms in algebraic quantum
field theory*, §2.1](https://link.springer.com/article/10.1007/s11005-025-01906-3).
Their smooth-curve definition uses nonzero causal tangents; here the stated
regularity is `C¹`.
-/

open Manifold
open scoped ContDiff

namespace AQFT.LorentzianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- A regular `C¹` curve from `x` to `y` with causal tangents on `[0,1]`. -/
structure CausalCurve (g : LorentzianMetric I M) (x y : M) where
  /-- The curve is represented on the real line and used only on `[0,1]`. -/
  toFun : ℝ → M
  /-- The initial point. -/
  source : toFun 0 = x
  /-- The final point. -/
  target : toFun 1 = y
  /-- The curve has a continuous first derivative on the interval. -/
  contMDiffOn : ContMDiffOn 𝓘(ℝ) I 1 toFun (Set.Icc 0 1)
  /-- Regularity excludes a zero tangent, including at the endpoints. -/
  velocity_ne_zero (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mfderivWithin 𝓘(ℝ) I toFun (Set.Icc 0 1) t 1 ≠ 0
  /-- Each tangent is timelike or null under the `(-,+,…,+)` convention. -/
  nonpos (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    g.form (toFun t)
      (mfderivWithin 𝓘(ℝ) I toFun (Set.Icc 0 1) t 1)
      (mfderivWithin 𝓘(ℝ) I toFun (Set.Icc 0 1) t 1) ≤ 0

instance {g : LorentzianMetric I M} {x y : M} :
    CoeFun (CausalCurve g x y) (fun _ ↦ ℝ → M) := ⟨CausalCurve.toFun⟩

/-- Coincident points or points connected by a regular causal curve in either direction. -/
def CausallyRelated (g : LorentzianMetric I M) (x y : M) : Prop :=
  x = y ∨ Nonempty (CausalCurve g x y) ∨ Nonempty (CausalCurve g y x)

namespace CausallyRelated

/-- Every point is causally related to itself. -/
@[refl] theorem refl (g : LorentzianMetric I M) (x : M) : g.CausallyRelated x x :=
  Or.inl rfl

/-- The unoriented causal relation is symmetric. -/
@[symm] theorem symm {g : LorentzianMetric I M} {x y : M}
    (h : g.CausallyRelated x y) : g.CausallyRelated y x := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

end CausallyRelated

/-- A causal curve makes its endpoints causally related. -/
theorem CausalCurve.causallyRelated {g : LorentzianMetric I M} {x y : M}
    (γ : CausalCurve g x y) : g.CausallyRelated x y :=
  Or.inr (Or.inl ⟨γ⟩)

/-- Reversing the pair of endpoints preserves causal relatedness. -/
theorem causallyRelated_comm (g : LorentzianMetric I M) (x y : M) :
    g.CausallyRelated x y ↔ g.CausallyRelated y x :=
  ⟨CausallyRelated.symm, CausallyRelated.symm⟩

/-- No point of one set is causally related to a point of the other. -/
def SpacelikeSeparated (g : LorentzianMetric I M) (s t : Set M) : Prop :=
  ∀ x ∈ s, ∀ y ∈ t, ¬g.CausallyRelated x y

namespace SpacelikeSeparated

variable {g : LorentzianMetric I M} {s t s' t' : Set M}

/-- Spacelike separation is symmetric. -/
@[symm] theorem symm (h : g.SpacelikeSeparated s t) : g.SpacelikeSeparated t s :=
  fun x hx y hy hxy ↦ h y hy x hx hxy.symm

/-- Subsets of spacelike separated sets remain spacelike separated. -/
theorem mono (h : g.SpacelikeSeparated s t) (hs : s' ⊆ s) (ht : t' ⊆ t) :
    g.SpacelikeSeparated s' t' :=
  fun x hx y hy ↦ h x (hs hx) y (ht hy)

/-- One causally related pair prevents spacelike separation. -/
theorem not_of_causallyRelated {x y : M} (hx : x ∈ s) (hy : y ∈ t)
    (hxy : g.CausallyRelated x y) : ¬g.SpacelikeSeparated s t :=
  fun h ↦ h x hx y hy hxy

/-- Spacelike separated sets have no points in common. -/
theorem disjoint (h : g.SpacelikeSeparated s t) : Disjoint s t :=
  Set.disjoint_left.mpr (fun x hx hy ↦ h x hx x hy (CausallyRelated.refl g x))

@[simp] theorem empty_left (g : LorentzianMetric I M) (t : Set M) :
    g.SpacelikeSeparated ∅ t := by
  simp [SpacelikeSeparated]

@[simp] theorem empty_right (g : LorentzianMetric I M) (s : Set M) :
    g.SpacelikeSeparated s ∅ := by
  simp [SpacelikeSeparated]

@[simp] theorem singleton_iff (g : LorentzianMetric I M) (x y : M) :
    g.SpacelikeSeparated {x} {y} ↔ ¬g.CausallyRelated x y := by
  simp [SpacelikeSeparated]

/-- A set is spacelike separated from itself exactly when it is empty. -/
@[simp] theorem self_iff (g : LorentzianMetric I M) (s : Set M) :
    g.SpacelikeSeparated s s ↔ s = ∅ := by
  constructor
  · intro h
    exact Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
      h x hx x hx (CausallyRelated.refl g x)
  · rintro rfl
    exact empty_left g ∅

end SpacelikeSeparated

end AQFT.LorentzianMetric
