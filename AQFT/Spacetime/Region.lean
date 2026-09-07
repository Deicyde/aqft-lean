import AQFT.Spacetime.Minkowski
import Mathlib.Topology.Sets.Opens

/-!
# Bounded open regions of Minkowski space

The local algebras in the Haag–Kastler formulation are indexed by all bounded
open subsets of Minkowski space. Boundedness refers to the usual normed-space
bornology, and regions are ordered by inclusion. The empty set is included;
no causal convexity or nonemptiness condition is imposed. Finite unions remain
regions, so any two regions have a common upper bound.

Reference: [Algebraic quantum field theory, Haag–Kastler axioms]
(https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory#Haag%E2%80%93Kastler_axioms).
-/

noncomputable section

namespace AQFT.Spacetime.MinkowskiSpace

/-- An open bounded subset of Minkowski space with `n` spatial dimensions. -/
def Region (n : ℕ) :=
  { U : TopologicalSpace.Opens (MinkowskiSpace n) //
    Bornology.IsBounded (U : Set (MinkowskiSpace n)) }

namespace Region

variable {n : ℕ}

instance : SetLike (Region n) (MinkowskiSpace n) := SetLike.instSubtype

instance : PartialOrder (Region n) :=
  inferInstanceAs (PartialOrder
    { U : TopologicalSpace.Opens (MinkowskiSpace n) //
      Bornology.IsBounded (U : Set (MinkowskiSpace n)) })

/-- The region order is inclusion of the underlying sets. -/
theorem le_iff_subset {U V : Region n} : U ≤ V ↔ (U : Set (MinkowskiSpace n)) ⊆ V :=
  Iff.rfl

/-- Every region is open in the usual topology of Minkowski space. -/
protected theorem isOpen (U : Region n) : IsOpen (U : Set (MinkowskiSpace n)) :=
  U.1.isOpen

/-- Every region is bounded in the usual normed-space bornology. -/
protected theorem isBounded (U : Region n) : Bornology.IsBounded (U : Set (MinkowskiSpace n)) :=
  U.2

/-- The empty set is the least region. -/
instance : OrderBot (Region n) where
  bot := ⟨⊥, Bornology.isBounded_empty⟩
  bot_le U := show (⊥ : TopologicalSpace.Opens (MinkowskiSpace n)) ≤ U.1 from bot_le

/-- The union of two regions is their least common upper bound. -/
instance : SemilatticeSup (Region n) where
  sup U V := ⟨U.1 ⊔ V.1, U.2.union V.2⟩
  le_sup_left U V := show U.1 ≤ U.1 ⊔ V.1 from le_sup_left
  le_sup_right U V := show V.1 ≤ U.1 ⊔ V.1 from le_sup_right
  sup_le U V W hU hV := show U.1 ⊔ V.1 ≤ W.1 from sup_le hU hV

@[simp] theorem coe_bot : ((⊥ : Region n) : Set (MinkowskiSpace n)) = ∅ := rfl

@[simp] theorem coe_sup (U V : Region n) :
    ((U ⊔ V : Region n) : Set (MinkowskiSpace n)) = (U : Set (MinkowskiSpace n)) ∪ V := rfl

/-- Any two bounded open regions lie in a common bounded open region. -/
theorem exists_upper_bound (U V : Region n) : ∃ W : Region n, U ≤ W ∧ V ≤ W :=
  ⟨U ⊔ V, le_sup_left, le_sup_right⟩

end Region

end AQFT.Spacetime.MinkowskiSpace
