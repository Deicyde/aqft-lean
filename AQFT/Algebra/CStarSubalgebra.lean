import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Closed unital star subalgebras

`CStarSubalgebra B` consists of norm-closed unital complex star subalgebras of an
abstract complex C*-algebra `B`. Each local carrier inherits a C*-algebra structure
from Mathlib's `StarSubalgebra.cstarAlgebra`. No Hilbert-space representation is
chosen. The local unit and scalar inclusion are inherited from `B`.

The commutant is relative to `B`: it contains the elements of `B` commuting with
every element of the local algebra. Mathlib's star centralizer is norm closed,
so it again defines a `CStarSubalgebra B`.

References: Mathlib's
[`CStarAlgebra.Classes`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/Classes.html)
and [`StarSubalgebra.centralizer`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Star/Subalgebra.html#StarSubalgebra.centralizer).
-/

noncomputable section

namespace AQFT

/-- A norm-closed unital complex star subalgebra of an abstract C*-algebra. -/
def CStarSubalgebra (B : Type*) [CStarAlgebra B] :=
  { S : StarSubalgebra ℂ B // IsClosed (S : Set B) }

namespace CStarSubalgebra

variable {B : Type*} [CStarAlgebra B]

instance : SetLike (CStarSubalgebra B) B := SetLike.instSubtype

instance : SubringClass (CStarSubalgebra B) B where
  zero_mem {S} := S.1.zero_mem'
  one_mem {S} := S.1.one_mem'
  add_mem {S} := S.1.add_mem'
  mul_mem {S} := S.1.mul_mem'
  neg_mem {S} {a} ha := show -a ∈ S.1 from neg_mem ha

instance : SMulMemClass (CStarSubalgebra B) ℂ B where
  smul_mem {S} r _ ha := S.1.smul_mem ha r

instance : StarMemClass (CStarSubalgebra B) B where
  star_mem {S} {a} ha := show star a ∈ S.1 from star_mem ha

instance : PartialOrder (CStarSubalgebra B) :=
  inferInstanceAs (PartialOrder { S : StarSubalgebra ℂ B // IsClosed (S : Set B) })

/-- The order on closed star subalgebras is inclusion. -/
theorem le_iff_subset {S T : CStarSubalgebra B} : S ≤ T ↔ (S : Set B) ⊆ T :=
  Iff.rfl

/-- The local carrier is closed in the norm topology of the ambient algebra. -/
instance isClosed (S : CStarSubalgebra B) : IsClosed (S : Set B) := S.2

/-- Each local carrier, with the inherited operations and norm, is a C*-algebra. -/
instance cstarAlgebra (S : CStarSubalgebra B) : CStarAlgebra S :=
  StarSubalgebra.cstarAlgebra S

/-- The whole ambient algebra is a closed star subalgebra. -/
instance : OrderTop (CStarSubalgebra B) where
  top := ⟨⊤, isClosed_univ⟩
  le_top S := show S.1 ≤ (⊤ : StarSubalgebra ℂ B) from le_top

@[simp] theorem coe_top : ((⊤ : CStarSubalgebra B) : Set B) = Set.univ := rfl

/-- The relative commutant inside the ambient C*-algebra `B`. -/
def commutant (S : CStarSubalgebra B) : CStarSubalgebra B :=
  ⟨StarSubalgebra.centralizer ℂ (S : Set B), Set.isClosed_centralizer _⟩

@[simp] theorem mem_commutant_iff {S : CStarSubalgebra B} {a : B} :
    a ∈ S.commutant ↔ ∀ b ∈ S, b * a = a * b := by
  change a ∈ StarSubalgebra.centralizer ℂ (S : Set B) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h b hb
    exact (h b hb).1
  · intro h b hb
    exact ⟨h b hb, h (star b) (star_mem hb)⟩

end CStarSubalgebra

end AQFT
