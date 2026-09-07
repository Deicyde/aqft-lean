import AQFT.Spacetime.Minkowski

/-!
# Spacelike separation in Minkowski space

Two sets are spacelike separated when every displacement between their points
has strictly positive Minkowski square, using the convention $(-,+,\ldots,+)$.
Strict positivity excludes coincident points and null displacements. This definition
applies to arbitrary sets, including the empty set.

Reference: Christian Bär, [*Lorentzian Geometry*, §1.1, Definition 1.5]
(https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf),
for the sign criterion on nonzero vectors. Set separation here always uses strict positivity.
-/

namespace AQFT.Spacetime.MinkowskiSpace

variable {n : ℕ}

/-- Every displacement between the two sets has strictly positive Minkowski square. -/
def SpacelikeSeparated (s t : Set (MinkowskiSpace n)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ t, 0 < bilinearForm n (x - y) (x - y)

namespace SpacelikeSeparated

variable {s t s' t' : Set (MinkowskiSpace n)}

/-- Spacelike separation is symmetric. -/
@[symm] theorem symm (h : SpacelikeSeparated s t) : SpacelikeSeparated t s := by
  intro x hx y hy
  rw [← neg_sub y x]
  simpa only [map_neg, neg_apply, neg_neg] using h y hy x hx

/-- Subsets of spacelike separated sets remain spacelike separated. -/
theorem mono (h : SpacelikeSeparated s t) (hs : s' ⊆ s) (ht : t' ⊆ t) :
    SpacelikeSeparated s' t' :=
  fun x hx y hy ↦ h x (hs hx) y (ht hy)

/-- A nonpositive displacement square prevents spacelike separation. -/
theorem not_of_nonpos {x y : MinkowskiSpace n} (hx : x ∈ s) (hy : y ∈ t)
    (hxy : bilinearForm n (x - y) (x - y) ≤ 0) : ¬SpacelikeSeparated s t :=
  fun h ↦ not_lt_of_ge hxy (h x hx y hy)

/-- Spacelike separated sets have no points in common. -/
theorem disjoint (h : SpacelikeSeparated s t) : Disjoint s t := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact not_of_nonpos hx hy (by simpa only [sub_self, map_zero] using le_refl (0 : ℝ)) h

@[simp] theorem empty_left (t : Set (MinkowskiSpace n)) : SpacelikeSeparated ∅ t := by
  simp [SpacelikeSeparated]

@[simp] theorem empty_right (s : Set (MinkowskiSpace n)) : SpacelikeSeparated s ∅ := by
  simp [SpacelikeSeparated]

@[simp] theorem singleton_iff (x y : MinkowskiSpace n) :
    SpacelikeSeparated {x} {y} ↔ 0 < bilinearForm n (x - y) (x - y) := by
  simp [SpacelikeSeparated]

/-- A shared spacetime translation preserves and reflects spacelike separation. -/
@[simp] theorem translate_iff (a : MinkowskiSpace n) :
    SpacelikeSeparated ((fun x ↦ a + x) '' s) ((fun x ↦ a + x) '' t) ↔
      SpacelikeSeparated s t := by
  simp only [SpacelikeSeparated, Set.forall_mem_image, add_sub_add_left_eq_sub]

/-- A pure unit time displacement is not spacelike. -/
theorem not_unitTime (n : ℕ) :
    ¬SpacelikeSeparated ({(1, 0)} : Set (MinkowskiSpace n)) {0} := by
  erw [singleton_iff, sub_zero]
  erw [bilinearForm_unitTime]
  norm_num

/-- A nonzero null displacement is not spacelike. -/
theorem not_nullVector :
    ¬SpacelikeSeparated ({nullVector} : Set (MinkowskiSpace 1)) {0} := by
  simp only [singleton_iff, sub_zero, bilinearForm_nullVector, lt_self_iff_false, not_false_eq_true]

/-- A pure unit spatial displacement is spacelike. -/
theorem unitSpace (i : Fin n) :
    SpacelikeSeparated ({(0, EuclideanSpace.single i 1)} : Set (MinkowskiSpace n)) {0} := by
  erw [singleton_iff, sub_zero]
  erw [bilinearForm_unitSpace]
  exact zero_lt_one

/-- With no spatial directions, separation holds exactly when at least one set is empty. -/
theorem zero_spatial_iff {s t : Set (MinkowskiSpace 0)} :
    SpacelikeSeparated s t ↔ s = ∅ ∨ t = ∅ := by
  constructor
  · intro h
    by_cases hs : s = ∅
    · exact Or.inl hs
    right
    by_contra ht
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hs
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr ht
    have hspace : (x - y).2 = 0 := Subsingleton.elim _ _
    apply not_of_nonpos hx hy ?_ h
    erw [bilinearForm_apply]
    simpa only [hspace, inner_zero_left, add_zero] using
      neg_nonpos.mpr (mul_self_nonneg (x - y).1)
  · rintro (rfl | rfl)
    · exact empty_left t
    · exact empty_right s

end SpacelikeSeparated

end AQFT.Spacetime.MinkowskiSpace
