# Mathlib audit

Checked against Mathlib `v4.33.1`, commit
`0df444a360eaa60ab8c11dca51a86af692955474`, on 2026-09-07. These findings concern
the pinned release, not every external Lean project or future Mathlib revision.

| Area | Existing support | Project use |
| --- | --- | --- |
| Von Neumann algebras | `WStarAlgebra`, `VonNeumannAlgebra H` | Reuse for the later algebra/net layer. |
| Smooth manifolds | `ModelWithCorners`, `IsManifold`, `TangentSpace` | Reuse the manifold and tangent-bundle structures. |
| Smooth bundle metrics | `Bundle.ContMDiffRiemannianMetric` | Follow its bilinear Hom-bundle smoothness pattern; replace positivity with nondegeneracy. |
| Bilinear forms | `ContinuousLinearMap.toBilinForm`, `LinearMap.BilinForm.Nondegenerate` | Reuse existing algebraic nondegeneracy. |
| Signature | `QuadraticForm.sigPos`, `QuadraticForm.sigNeg` | Reuse for the next Lorentzian milestone. |
| Minkowski / pseudo-Riemannian manifolds | No definitions found in the pinned Mathlib | This repository supplies the initial definitions and flat example. |

Relevant source files:

- [Analysis/VonNeumannAlgebra/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/VonNeumannAlgebra/Basic.lean)
- [Geometry/Manifold/VectorBundle/Tangent.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean)
- [Geometry/Manifold/VectorBundle/Riemannian.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean)
- [Geometry/Manifold/Riemannian/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Geometry/Manifold/Riemannian/Basic.lean)
- [LinearAlgebra/QuadraticForm/Signature.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/QuadraticForm/Signature.lean)

`VonNeumannAlgebra H` is a bundled star subalgebra equal to its double commutant.
The module explicitly lists the equivalence of abstract and concrete von Neumann
algebras, and the topological bicommutant theorem, as future work. Having the
definition does not mean all AQFT operator theory is available.

The ordinary Riemannian metric requires positive definiteness. The physical
Minkowski pairing must remain separate from the auxiliary positive-definite
structures used to give model vector spaces their topology.
