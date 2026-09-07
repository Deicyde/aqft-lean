# Mathlib audit

Checked against Mathlib `v4.33.1`, commit
`0df444a360eaa60ab8c11dca51a86af692955474`, on 2026-09-07. The operator APIs below
were checked in Lean using focused imports, `#check`, and instance synthesis.
These findings concern the pinned release, not external Lean projects or future
Mathlib revisions.

## Abstract C*-algebras and the current net

Mathlib's `CStarAlgebra B` supplies a complete unital complex normed star algebra
with the C*-identity. `StarSubalgebra ℂ B` supplies unital star subalgebras, and
`StarSubalgebra.cstarAlgebra` gives a closed subalgebra's carrier its inherited
`CStarAlgebra` instance. These classes and instances are in
[CStarAlgebra/Classes.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/CStarAlgebra/Classes.lean).

The project bundles the algebra and closedness as
`AQFT.CStarSubalgebra B := {S : StarSubalgebra ℂ B // IsClosed (S : Set B)}`.
Closure is in the norm topology of `B`. Each local algebra shares the ambient unit
and scalar inclusion, and has a native C*-algebra instance on its carrier.
`IsotoneNet M B := Spacetime.Region M →o CStarSubalgebra B` then expresses isotony
by inclusion. It requires no Hilbert space or representation, and does not assert
that the local algebras generate `B`.

`CStarSubalgebra.commutant` uses `StarSubalgebra.centralizer` and the closedness
theorem `Set.isClosed_centralizer`. It consists of elements of `B` commuting with
every element of the given local algebra. This relative commutant supports the
causality equivalence `A O₁ ≤ (A O₂).commutant`; no bicommutant condition is imposed.
See
[Algebra/Star/Subalgebra.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Star/Subalgebra.lean)
and
[Topology/Algebra/StarSubalgebra.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/StarSubalgebra.lean).

## Representations, operator algebras, and continuity

The following APIs support later representations of the abstract net. They are
not prerequisites for its isotony or causality definitions.

| Area | Existing support | Project use |
| --- | --- | --- |
| Weak operator topology | `ContinuousLinearMapWOT`, written `E →WOT[ℂ] F` | Express weak continuity by matrix coefficients. |
| Strong operator topology | `PointwiseConvergenceCLM`, written `E →Lₚₜ[ℂ] F` | Express strong continuity by continuity of every orbit map. |
| GNS construction | `PositiveLinearMap.GNS`, `gnsStarAlgHom`, `gnsNonUnitalStarAlgHom` | Reuse the Hilbert space and representation induced by a positive functional. |
| Von Neumann algebras | `WStarAlgebra`, `VonNeumannAlgebra H`, `VonNeumannAlgebra.commutant` | Use for later represented local algebras and their operator commutants. |

For Hilbert-space-valued operators,
`ContinuousLinearMapWOT.continuous_iff` identifies continuity of `T` into the weak
operator topology with continuity of every function `a ↦ ⟪y, T a x⟫`.
`tendsto_iff_forall_inner_apply_tendsto` gives the corresponding convergence
criterion. The adjoint has a `ContinuousStar` instance in this topology.
See [InnerProductSpace/WeakOperatorTopology.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/WeakOperatorTopology.lean).

The general weak-operator API also uses continuous dual functionals in place of
inner products. `ContinuousLinearMapWOT.ofCLM` changes the type of an operator;
`continuous_ofCLM` and `ContinuousLinearMap.WOTofCLM` express continuity from the
usual bounded-convergence topology into WOT. See
[LocallyConvex/WeakOperatorTopology.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean).

For strong continuity, use
`PointwiseConvergenceCLM.continuous_of_continuous_eval` or
`PointwiseConvergenceCLM.tendsto_iff_forall_tendsto`.
`ContinuousLinearMap.toPointwiseConvergenceCLM` supplies the continuous map from
the usual operator topology. On Hilbert spaces this is the strong operator
topology. Continuity into the usual `H →L[ℂ] H` instead uses the operator norm and
would impose a stronger requirement on a unitary representation. See
[PointwiseConvergenceCLM.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/Module/Spaces/PointwiseConvergenceCLM.lean).

For `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]` and
`f : A →ₚ[ℂ] ℂ`, Mathlib constructs the complete complex inner product space
`f.GNS` and the unital representation
`f.gnsStarAlgHom : A →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS)`.
There is also a non-unital construction. The representation acts by extending
left multiplication on the pre-GNS space; the lemma
`gnsNonUnitalStarAlgHom_apply_coe` exposes this action on its dense image.
The input is any positive functional, so normalization such as `f 1 = 1` is
additional data for a state. The module still lists construction of a normalized
cyclic vector as future work. Reuse the representation and prove the required
state, cyclicity, and symmetry properties around it. See
[GelfandNaimarkSegal.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean).

`VonNeumannAlgebra H` is a bundled star subalgebra of bounded operators equal to
its double commutant. It has an inclusion order, `commutant_commutant`, and
`mem_commutant_iff`, useful for a represented net's isotony and locality. `WStarAlgebra` is
the abstract C*-algebra definition using existence of a Banach-space predual.
The module lists the equivalence of the abstract and concrete definitions, and
the topological bicommutant theorem, as future work. This is a specific missing
bridge; the weak operator topology itself is already implemented. Connecting an
abstract net, a chosen GNS representation, and local von Neumann algebras remains
additional project work. See
[VonNeumannAlgebra/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/VonNeumannAlgebra/Basic.lean).

## Spectral theory

Mathlib already has `spectrum`, continuous functional calculus through
`ContinuousFunctionalCalculus` and `cfc`, finite-dimensional self-adjoint
diagonalization, and a spectral theorem for compact self-adjoint operators.
It also has joint eigenspace decompositions for commuting self-adjoint families
in finite dimensions. Relevant checked declarations include
`LinearMap.IsSymmetric.eigenvectorBasis`,
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`, and
`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`. See
[functional calculus](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean),
[self-adjoint spectral theory](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Spectrum.lean), and
[joint eigenspaces](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean).

The AQFT spectrum condition needs a more specific bridge: a joint spectral
measure for a strongly continuous translation representation, or a proved
equivalent formulation for its generally unbounded generators. This audit did
not locate that complete bridge in the pinned source. Existing spectral theory
should be reused; finite-dimensional joint eigenspaces alone do not establish
the required infinite-dimensional statement.

## Geometry

| Area | Existing support | Project use |
| --- | --- | --- |
| Smooth manifolds | `ModelWithCorners`, `IsManifold`, `TangentSpace` | Reuse the manifold and tangent-bundle structures. |
| Smooth bundle metrics | `Bundle.ContMDiffRiemannianMetric` | Follow its bilinear Hom-bundle smoothness pattern; replace positivity with nondegeneracy. |
| Bilinear forms | `ContinuousLinearMap.toBilinForm`, `LinearMap.BilinForm.Nondegenerate` | Reuse algebraic nondegeneracy. |
| Signature | `sigPos`, `sigNeg` | Reuse for Lorentzian index and Minkowski signature. |
| Minkowski / pseudo-Riemannian manifolds | No dedicated definitions found in the pinned Mathlib | Supply the geometric definitions and examples using the existing APIs. |

Relevant source files are
[Tangent.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean),
[VectorBundle/Riemannian.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean),
[Riemannian/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Geometry/Manifold/Riemannian/Basic.lean), and
[QuadraticForm/Signature.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/QuadraticForm/Signature.lean).

The ordinary Riemannian metric requires positive definiteness. Keep the physical
Minkowski pairing separate from the auxiliary positive-definite structures used
to give model vector spaces their topology.

The checked dependencies of `PositiveLinearMap.gnsStarAlgHom`,
`ContinuousLinearMapWOT.continuous_iff`, and
`VonNeumannAlgebra.commutant_commutant` use only `propext`, `Classical.choice`, and
`Quot.sound`, as reported by `#print axioms`.
