# AQFT Lean

Foundations for algebraic quantum field theory in Lean 4, starting with
pseudo-Riemannian manifolds and Minkowski spacetime.

The long-term target is the concrete Haag–Kastler framework: a net of local von
Neumann algebras on a common Hilbert space, with isotony, locality, Poincaré
covariance, a vacuum, and the spectrum condition. **Isotony and causality are
formalized**; the other AQFT axioms remain future work. The geometric foundation
includes Lorentzian metrics, a proved Minkowski signature, and the algebraic group of
metric-preserving diffeomorphisms.

## Implemented

- `PseudoInnerProductSpace` supplies a continuous symmetric nondegenerate pairing
  on each fiber, allowing indefinite signature. `PseudoRiemannianBundle` installs the
  family without changing any fiber's topology or auxiliary norm.
- `IsPseudoRiemannianManifold` records smoothness of those installed tangent
  pairings. `IsLorentzianManifold` adds index one, following Mathlib's separation of
  fiber data and geometric properties.
- `AQFT.PseudoRiemannianMetric`: smooth symmetric nondegenerate bilinear forms on
  the tangent bundle of a finite-dimensional smooth real manifold. Smoothness uses
  Mathlib's bilinear Hom bundle and its coordinate changes.
- Nondegeneracy lemmas and injectivity of pairing with the metric.
- Smooth evaluation of the metric on smooth vector fields.
- `PseudoRiemannianMetric.ofBilinearForm`: a constant smooth metric from any
  symmetric nondegenerate continuous bilinear form.
- `AQFT.Spacetime.MinkowskiSpace n`: one time coordinate and `n` spatial coordinates,
  with pairing `−t*s + ⟪x,y⟫`, symmetry, continuity, and nondegeneracy.
- `MinkowskiSpace.metric n`: the resulting smooth pseudo-Riemannian metric.
- Negative time squares, positive spatial unit squares, and an explicit nonzero
  null vector in dimension `1+1`.
- `AQFT.LorentzianMetric`: a smooth metric with negative index one at every point,
  using Mathlib's `sigNeg` and `sigPos` directly. Its signature is proved to be
  `(1, n−1)` for total dimension `n`, with the pair ordered as (negative, positive). This signature
  condition is proved equivalent to the metric and manifold index-one definitions.
- `MinkowskiSpace.lorentzianMetric n`: Minkowski space as a Lorentzian example,
  with exactly one negative and `n` positive directions.
- `PseudoRiemannianMetric.Isometry g h`: a diffeomorphism whose derivative preserves
  the tangent metric. Self-isometries form a group under composition.
- Minkowski translations and time reversal as explicit metric isometries.
- `MinkowskiSpace.Region n`: all open bounded subsets, ordered by inclusion.
  The empty set is included, and finite unions supply common upper regions.
- `AQFT.IsotoneNet n H`: an order-preserving assignment of local
  `VonNeumannAlgebra H` values to regions. Mathlib's `OrderHom` expresses isotony
  directly. The resulting local algebras form a directed family under inclusion.
- `MinkowskiSpace.SpacelikeSeparated`: every displacement between points of the
  two sets has strictly positive Minkowski square. Separation is symmetric,
  passes to subsets, implies disjointness, and is invariant under shared translations.
- `IsotoneNet.IsCausal`: all operators in spacelike separated local algebras
  commute. This is proved equivalent to commutant inclusion and to `a*b - b*a = 0`.

Minkowski space has default instances of these manifold classes. The explicit
metric structures serve as constructors: `g.toBundle` installs a chosen metric
locally, and `PseudoRiemannianMetric.ofBundle` recovers it from the fiber instances.
`LorentzianIsometryGroup I M` is the isometry group of the installed Lorentzian
structure.

For example, after `import AQFT`:

```lean
open Manifold AQFT AQFT.Spacetime
open scoped Bundle

example : IsLorentzianManifold
    𝓘(ℝ, MinkowskiSpace 3) (MinkowskiSpace 3) := inferInstance

noncomputable example : Group (LorentzianIsometryGroup
    𝓘(ℝ, MinkowskiSpace 3) (MinkowskiSpace 3)) := inferInstance

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : IsotoneNet 3 H) {O₁ O₂ : MinkowskiSpace.Region 3}
    (h : O₁ ≤ O₂) : A O₁ ≤ A O₂ :=
  A.monotone h

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A : IsotoneNet 3 H} (hA : A.IsCausal)
    {O₁ O₂ : MinkowskiSpace.Region 3}
    (h : MinkowskiSpace.SpacelikeSeparated (O₁ : Set (MinkowskiSpace 3)) O₂)
    {a b : H →L[ℂ] H} (ha : a ∈ A O₁) (hb : b ∈ A O₂) :
    a * b - b * a = 0 :=
  sub_eq_zero.mpr (hA h ha hb).eq
```

Both orders in the isotony example are inclusion. Every algebra acts on the same
complex Hilbert space `H`. Boundedness of regions uses the usual product norm,
not the indefinite pairing. Isotony alone does not prescribe the algebra of the
empty region or impose locality, covariance, or a vacuum condition.

Causality is imposed separately through `A.IsCausal`. Strict spacelike separation
excludes coincident, null, and timelike displacements. The empty region is separated
from every region, so its observables commute with every local algebra; this does
not by itself identify its algebra with the scalars.

All committed proofs are complete. There are no proof placeholders or added axioms.
CI builds with warnings treated as errors and audits dependencies on axioms.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/Deicyde/aqft-lean.git
cd aqft-lean
lake exe cache get
lake --wfail build
```

Lean and Mathlib are pinned to `v4.33.1`; `lake-manifest.json` records the resolved
dependency commits. Start a Lean file with `import AQFT`.

## Geometry conventions

The construction follows [Mathlib's Riemannian manifold and bundle API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Riemannian/Basic.html#IsRiemannianManifold).
Here the fiber pairing is indefinite, as in semi-Riemannian geometry. Mathlib's
`PreInnerProductSpace.Core` requires nonnegative squares and cannot model a
Lorentzian fiber. We therefore use a distinct `pseudoInner` operation that can
coexist with the auxiliary Euclidean inner product.

We use the Lorentzian sign convention `(-,+,…,+)`. The auxiliary norm on the model
space supplies its usual topology; the physical metric is a separate, indefinite
bilinear form. A nonzero vector can have zero metric square.

The general pseudo-Riemannian metric definition imposes no global signature;
`LorentzianMetric` and `IsLorentzianManifold` specialize to signature `(1, n−1)`
in total dimension `n`. We list negative directions first, consistent with the
negative time coordinate. `MinkowskiSpace k` uses `k` spatial coordinates, so it has
total dimension `k+1` and signature `(1,k)`. Isometries preserve both signature
components. The metric API permits Mathlib
models with corners. Use a boundaryless model, Hausdorffness, and second countability
when describing a Lorentzian manifold without boundary. Minkowski space has all
these properties. The index-one convention also permits dimension one; applications
requiring spatial directions should impose dimension at least two.

The isometry group is currently an algebraic group. Its topology, Lie group
structure, and the proper orthochronous Poincaré subgroup remain future work. The
full group includes translations and time reversal; no time orientation is fixed.

Mathlib's `IsRiemannianManifold` additionally relates the metric to an extended
distance obtained from path lengths. That distance condition is not carried over
to the indefinite setting.

See [the roadmap](docs/roadmap.md) for the remaining geometry and AQFT work, and
[the Mathlib audit](docs/mathlib-audit.md) for existing APIs and their limitations.

## References

- [Wikipedia: Algebraic quantum field theory](https://en.wikipedia.org/wiki/Algebraic_quantum_field_theory),
  the motivating overview.
- [Ammann, Differential Geometry II, Definition 2.1.1](https://ammann.app.uni-regensburg.de/lehre/2021s_diffgeo2/Diffgeo2.pdf),
  for smooth pseudo-Riemannian metrics.
- [Bär, Lorentzian Geometry, §1.1](https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-Geometrie/Dokumente/Lehre/Veranstaltungen/WS0405-SS08/LorentzianGeometryEnglish13Jan2020.pdf),
  for the Minkowski convention and Lorentzian geometry.
- [Fewster and Rejzner, Algebraic Quantum Field Theory: an introduction, §§4–6](https://arxiv.org/abs/1904.04051),
  for local algebras, representations, and vacuum assumptions.
- [Brunetti, Fredenhagen, and Verch, The Generally Covariant Locality Principle, §2](https://arxiv.org/abs/math-ph/0112041),
  for a possible later curved-spacetime extension.

Licensed under Apache 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
