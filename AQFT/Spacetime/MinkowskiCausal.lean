import AQFT.Geometry.Lorentzian.Causal
import AQFT.Spacetime.Lorentzian
import AQFT.Spacetime.Spacelike
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

/-!
# Causal curves in Minkowski space

A regular causal curve in Minkowski space has endpoints with nonpositive squared
displacement. Its nonzero causal velocity has a nonzero time component, whose
sign is constant by continuity. The fundamental theorem of calculus then bounds
the spatial displacement by the absolute time displacement. Conversely, a
nonpositive displacement between distinct points gives a straight causal segment.
Thus curve-based separation agrees with strictly positive displacement squares.

Reference: Christian Bär, [*Lorentzian Geometry*, §1.1 and §2.1]
(https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf).
-/

open Set MeasureTheory Manifold
open scoped ContDiff

namespace AQFT.Spacetime.MinkowskiSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

private theorem fixed_sign {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (hn : ∀ t ∈ Icc 0 1, f t ≠ 0) :
    (∀ t ∈ Icc 0 1, 0 < f t) ∨ (∀ t ∈ Icc 0 1, f t < 0) := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  rcases lt_or_gt_of_ne (hn 0 hz) with hneg | hpos
  · right
    intro t ht
    by_contra h
    obtain ⟨u, hu, he⟩ := isPreconnected_Icc.intermediate_value₂ hz ht hc
      continuousOn_const hneg.le (le_of_not_gt h)
    exact hn u hu he
  · left
    intro t ht
    by_contra h
    obtain ⟨u, hu, he⟩ := isPreconnected_Icc.intermediate_value₂ ht hz hc
      continuousOn_const (le_of_not_gt h) hpos.le
    exact hn u hu he

private theorem endpoint_norm_bound {γ : ℝ → ℝ × V}
    (hc : ContDiffOn ℝ 1 γ (Icc 0 1))
    (hn : ∀ t ∈ Icc 0 1, (derivWithin γ (Icc 0 1) t).1 ≠ 0)
    (hb : ∀ t ∈ Icc 0 1,
      ‖(derivWithin γ (Icc 0 1) t).2‖ ≤ |(derivWithin γ (Icc 0 1) t).1|) :
    ‖(γ 1).2 - (γ 0).2‖ ≤ |(γ 1).1 - (γ 0).1| := by
  let v := derivWithin γ (Icc 0 1)
  change ∀ t ∈ Icc 0 1, ‖(v t).2‖ ≤ |(v t).1| at hb
  have hv : ContinuousOn v (Icc 0 1) :=
    hc.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hd (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt γ (v t) t :=
    ((hc.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hT : (∫ t in (0 : ℝ)..1, (v t).1) = (γ 1).1 - (γ 0).1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc.continuousOn.fst
    · intro t ht
      exact (ContinuousLinearMap.fst ℝ ℝ V).hasFDerivAt.comp_hasDerivAt t (hd t ht)
    · exact hv.fst.intervalIntegrable_of_Icc zero_le_one
  have hX : (∫ t in (0 : ℝ)..1, (v t).2) = (γ 1).2 - (γ 0).2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc.continuousOn.snd
    · intro t ht
      exact (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt.comp_hasDerivAt t (hd t ht)
    · exact hv.snd.intervalIntegrable_of_Icc zero_le_one
  rcases fixed_sign hv.fst hn with hp | hm
  · have hbound : ‖∫ t in (0 : ℝ)..1, (v t).2‖ ≤ ∫ t in (0 : ℝ)..1, (v t).1 := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards with t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        simpa only [abs_of_pos (hp t ht')] using hb t ht'
      · exact hv.fst.intervalIntegrable_of_Icc zero_le_one
    rw [hX, hT] at hbound
    exact hbound.trans (le_abs_self _)
  · have hbound : ‖∫ t in (0 : ℝ)..1, (v t).2‖ ≤ ∫ t in (0 : ℝ)..1, -(v t).1 := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards with t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        simpa only [abs_of_neg (hm t ht')] using hb t ht'
      · exact hv.fst.neg.intervalIntegrable_of_Icc zero_le_one
    rw [hX, intervalIntegral.integral_neg, hT] at hbound
    exact hbound.trans (neg_le_abs _)

private theorem space_norm_le_abs_time {n : ℕ} (v : MinkowskiSpace n)
    (hv : bilinearForm n v v ≤ 0) : ‖v.2‖ ≤ |v.1| := by
  rw [bilinearForm_apply, real_inner_self_eq_norm_sq] at hv
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs]
  nlinarith

private theorem time_ne_zero {n : ℕ} (v : MinkowskiSpace n) (hv : v ≠ 0)
    (hq : bilinearForm n v v ≤ 0) : v.1 ≠ 0 := by
  intro ht
  have hb := space_norm_le_abs_time v hq
  rw [ht, abs_zero] at hb
  have hs : v.2 = 0 := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  exact hv (Prod.ext ht hs)

/-- Endpoints of a regular Minkowski causal curve have nonpositive squared displacement. -/
theorem causalCurve_endpoint_nonpos {n : ℕ} {x y : MinkowskiSpace n}
    (γ : LorentzianMetric.CausalCurve (lorentzianMetric n) x y) :
    bilinearForm n (y - x) (y - x) ≤ 0 := by
  have hc : ContDiffOn ℝ 1 γ.toFun (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mp γ.contMDiffOn
  have hvel (t : ℝ) :
      mfderivWithin 𝓘(ℝ) 𝓘(ℝ, MinkowskiSpace n) γ.toFun (Icc 0 1) t 1 =
        derivWithin γ.toFun (Icc 0 1) t := by
    rw [mfderivWithin_eq_fderivWithin]
    rfl
  have hn (t : ℝ) (ht : t ∈ Icc 0 1) : derivWithin γ.toFun (Icc 0 1) t ≠ 0 := by
    have h := γ.velocity_ne_zero t ht
    rw [hvel] at h
    exact h
  have hq (t : ℝ) (ht : t ∈ Icc 0 1) :
      bilinearForm n (derivWithin γ.toFun (Icc 0 1) t)
        (derivWithin γ.toFun (Icc 0 1) t) ≤ 0 := by
    have h := γ.nonpos t ht
    change bilinearForm n _ _ ≤ 0 at h
    simpa only [hvel] using h
  have hb := endpoint_norm_bound hc
    (fun t ht ↦ time_ne_zero _ (hn t ht) (hq t ht))
    (fun t ht ↦ space_norm_le_abs_time _ (hq t ht))
  rw [γ.source, γ.target] at hb
  rw [bilinearForm_apply, real_inner_self_eq_norm_sq]
  have hs := (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mpr hb
  rw [sq_abs] at hs
  change -((y.1 - x.1) * (y.1 - x.1)) + ‖y.2 - x.2‖ ^ 2 ≤ 0
  nlinarith

variable {n : ℕ}

private theorem lineMap_velocity (x y : MinkowskiSpace n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mfderivWithin 𝓘(ℝ) 𝓘(ℝ, MinkowskiSpace n) (AffineMap.lineMap x y)
      (Icc 0 1) t 1 = y - x := by
  have hd : HasDerivWithinAt (AffineMap.lineMap x y) (y - x) (Icc 0 1) t :=
    AffineMap.hasDerivWithinAt_lineMap
  have heq := hd.hasFDerivWithinAt.hasMFDerivWithinAt.mfderivWithin
    ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
  refine (congrArg (fun f ↦ f 1) heq).trans ?_
  change (1 : ℝ) • (y - x) = y - x
  exact one_smul ℝ (y - x)

/-- The straight segment between distinct causally displaced points is a regular causal curve. -/
noncomputable def causalLine {x y : MinkowskiSpace n} (hxy : x ≠ y)
    (h : bilinearForm n (y - x) (y - x) ≤ 0) :
    LorentzianMetric.CausalCurve (lorentzianMetric n) x y where
  toFun := AffineMap.lineMap x y
  source := AffineMap.lineMap_apply_zero x y
  target := AffineMap.lineMap_apply_one x y
  contMDiffOn := (AffineMap.contDiff_lineMap x y).contMDiff.contMDiffOn
  velocity_ne_zero t ht := by
    rw [lineMap_velocity x y ht]
    exact sub_ne_zero.mpr hxy.symm
  nonpos t ht := by
    change bilinearForm n _ _ ≤ 0
    rw [lineMap_velocity x y ht]
    exact h

/-- A nonpositive Minkowski displacement square gives a causal connection. -/
theorem causallyRelated_of_bilinearForm_sub_nonpos {x y : MinkowskiSpace n}
    (h : bilinearForm n (y - x) (y - x) ≤ 0) :
    (lorentzianMetric n).CausallyRelated x y := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · exact (causalLine hxy h).causallyRelated

/-- Minkowski causal connectivity is exactly nonpositive squared displacement. -/
theorem causallyRelated_iff (x y : MinkowskiSpace n) :
    (lorentzianMetric n).CausallyRelated x y ↔ bilinearForm n (x - y) (x - y) ≤ 0 := by
  constructor
  · intro h
    rcases h with rfl | h | h
    · simp only [sub_self, map_zero, le_refl]
    · obtain ⟨γ⟩ := h
      have hq := causalCurve_endpoint_nonpos γ
      rw [← neg_sub x y] at hq
      simpa only [map_neg, neg_apply, neg_neg] using hq
    · obtain ⟨γ⟩ := h
      exact causalCurve_endpoint_nonpos γ
  · intro h
    apply causallyRelated_of_bilinearForm_sub_nonpos
    rw [← neg_sub x y]
    simpa only [map_neg, neg_apply, neg_neg] using h

/-- Curve-based Minkowski separation agrees with the direct displacement criterion. -/
theorem spacelikeSeparated_iff (s t : Set (MinkowskiSpace n)) :
    (lorentzianMetric n).SpacelikeSeparated s t ↔ SpacelikeSeparated s t := by
  simp only [LorentzianMetric.SpacelikeSeparated, causallyRelated_iff, not_le,
    SpacelikeSeparated]

end AQFT.Spacetime.MinkowskiSpace
