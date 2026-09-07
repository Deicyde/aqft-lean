import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sets.Opens

/-!
# Relatively compact open regions

Regions are open subsets with compact closure, ordered by inclusion. This
definition uses the existing topology, so it applies to Lorentzian manifolds
without choosing an auxiliary distance or bornology. Mathlib uses the same
compact-closure condition in `TopologicalSpace.Compacts.openRcNhds`.

In a proper pseudometric space, compact closure is equivalent to boundedness.
In particular, this recovers all bounded open regions of finite-dimensional
Minkowski space. The empty set is included; no causal convexity or nonemptiness
condition is imposed. Finite unions remain regions, so the region order is directed.

Reference for the Minkowski indexing convention:
[Algebraic quantum field theory, Haag–Kastler axioms]
(https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory#Haag%E2%80%93Kastler_axioms).
-/

noncomputable section

namespace AQFT.Spacetime

/-- An open subset with compact closure in the ambient topological space. -/
def Region (M : Type*) [TopologicalSpace M] :=
  { U : TopologicalSpace.Opens M // IsCompact (closure (U : Set M)) }

namespace Region

section Topological

variable {M : Type*} [TopologicalSpace M]

instance : SetLike (Region M) M := SetLike.instSubtype

instance : PartialOrder (Region M) :=
  inferInstanceAs (PartialOrder
    { U : TopologicalSpace.Opens M // IsCompact (closure (U : Set M)) })

/-- The region order is inclusion of the underlying sets. -/
theorem le_iff_subset {U V : Region M} : U ≤ V ↔ (U : Set M) ⊆ V :=
  Iff.rfl

/-- Every region is open in the ambient topology. -/
protected theorem isOpen (U : Region M) : IsOpen (U : Set M) :=
  U.1.isOpen

/-- The closure of a region is compact in the ambient space. -/
protected theorem isCompact_closure (U : Region M) : IsCompact (closure (U : Set M)) :=
  U.2

/-- The empty set is the least region. -/
instance : OrderBot (Region M) where
  bot := ⟨⊥, by simp⟩
  bot_le U := show (⊥ : TopologicalSpace.Opens M) ≤ U.1 from bot_le

/-- The union of two regions is their least common upper bound. -/
instance : SemilatticeSup (Region M) where
  sup U V := ⟨U.1 ⊔ V.1, by
    change IsCompact (closure ((U : Set M) ∪ V))
    rw [closure_union]
    exact U.2.union V.2⟩
  le_sup_left U V := show U.1 ≤ U.1 ⊔ V.1 from le_sup_left
  le_sup_right U V := show V.1 ≤ U.1 ⊔ V.1 from le_sup_right
  sup_le U V W hU hV := show U.1 ⊔ V.1 ≤ W.1 from sup_le hU hV

@[simp] theorem coe_bot : ((⊥ : Region M) : Set M) = ∅ := rfl

@[simp] theorem coe_sup (U V : Region M) :
    ((U ⊔ V : Region M) : Set M) = (U : Set M) ∪ V := rfl

/-- Any two regions lie in a common relatively compact open region. -/
theorem exists_upper_bound (U V : Region M) : ∃ W : Region M, U ≤ W ∧ V ≤ W :=
  ⟨U ⊔ V, le_sup_left, le_sup_right⟩

variable {N : Type*} [TopologicalSpace N] {P : Type*} [TopologicalSpace P]

/-- A homeomorphism transports a region by taking its image. -/
def map (f : M ≃ₜ N) (U : Region M) : Region N :=
  ⟨⟨f '' (U : Set M), f.isOpenMap _ U.isOpen⟩, by
    change IsCompact (closure (f '' (U : Set M)))
    rw [← f.image_closure]
    exact U.isCompact_closure.image f.continuous⟩

@[simp] theorem coe_map (f : M ≃ₜ N) (U : Region M) :
    (map f U : Set N) = f '' (U : Set M) := rfl

@[simp] theorem map_refl (U : Region M) : map (Homeomorph.refl M) U = U := by
  apply SetLike.coe_injective
  exact Set.image_id _

/-- Successive changes of coordinates transport regions by the composite map. -/
theorem map_trans (f : M ≃ₜ N) (h : N ≃ₜ P) (U : Region M) :
    map (f.trans h) U = map h (map f U) := by
  apply SetLike.coe_injective
  exact (Set.image_image h f (U : Set M)).symm

/-- Transport of regions preserves and reflects inclusion. -/
def mapOrderIso (f : M ≃ₜ N) : Region M ≃o Region N where
  toFun := map f
  invFun := map f.symm
  left_inv U := by
    apply SetLike.coe_injective
    exact f.toEquiv.left_inv.image_image _
  right_inv U := by
    apply SetLike.coe_injective
    exact f.toEquiv.right_inv.image_image _
  map_rel_iff' := Set.image_subset_image_iff f.injective

@[simp] theorem mapOrderIso_apply (f : M ≃ₜ N) (U : Region M) :
    mapOrderIso f U = map f U := rfl

end Topological

section PseudoMetric

variable {M : Type*} [PseudoMetricSpace M]

/-- A region is bounded whenever the ambient topology comes from a pseudometric. -/
protected theorem isBounded (U : Region M) : Bornology.IsBounded (U : Set M) :=
  U.isCompact_closure.isBounded.subset subset_closure

variable [ProperSpace M]

/-- In a proper pseudometric space, compact closure is equivalent to boundedness. -/
theorem isCompact_closure_iff_isBounded {s : Set M} :
    IsCompact (closure s) ↔ Bornology.IsBounded s :=
  ⟨fun h ↦ h.isBounded.subset subset_closure, fun h ↦ h.isCompact_closure⟩

/-- An open bounded set defines a region in a proper pseudometric space. -/
def ofIsBounded (U : TopologicalSpace.Opens M) (h : Bornology.IsBounded (U : Set M)) :
    Region M :=
  ⟨U, h.isCompact_closure⟩

@[simp] theorem coe_ofIsBounded (U : TopologicalSpace.Opens M)
    (h : Bornology.IsBounded (U : Set M)) : ((ofIsBounded U h) : Set M) = U := rfl

/-- Bounded open sets and relatively compact open regions have the same inclusion order
in a proper pseudometric space. -/
def boundedOpenOrderIso :
    { U : TopologicalSpace.Opens M // Bornology.IsBounded (U : Set M) } ≃o Region M where
  toFun U := ofIsBounded U.1 U.2
  invFun U := ⟨U.1, U.isBounded⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

end PseudoMetric

end Region

end AQFT.Spacetime
