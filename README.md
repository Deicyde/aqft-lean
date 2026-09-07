# AQFT Lean

Foundations for algebraic quantum field theory in Lean 4, starting with
pseudo-Riemannian manifolds and Minkowski spacetime.

The long-term target is the concrete Haag–Kastler framework: a net of local von
Neumann algebras on a common Hilbert space, with isotony, locality, Poincaré
covariance, a vacuum, and the spectrum condition. These AQFT axioms are **not yet
formalized**. The first contribution establishes the metric definition and a
working flat example.

## Implemented

- `AQFT.PseudoRiemannianMetric`: smooth symmetric nondegenerate bilinear forms on
  the tangent bundle of a finite-dimensional smooth real manifold. Smoothness uses
  Mathlib's bilinear Hom bundle and its coordinate changes.
- Nondegeneracy lemmas and injectivity of pairing with the metric.
- `PseudoRiemannianMetric.ofBilinearForm`: a constant smooth metric from any
  symmetric nondegenerate continuous bilinear form.
- `AQFT.Spacetime.MinkowskiSpace n`: one time coordinate and `n` spatial coordinates,
  with pairing `−t*s + ⟪x,y⟫`, symmetry, continuity, and nondegeneracy.
- `MinkowskiSpace.metric n`: the resulting smooth pseudo-Riemannian metric.
- Negative time squares, positive spatial unit squares, and an explicit nonzero
  null vector in dimension `1+1`.

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

We use the Lorentzian sign convention `(-,+,…,+)`. The auxiliary norm on the model
space supplies its usual topology; the physical metric is a separate, indefinite
bilinear form. A nonzero vector can have zero metric square.

The general metric definition imposes no global signature. Specifying a fixed index
and proving the Minkowski index is one are the next steps. The metric API permits
Mathlib models with corners; later spacetime definitions should require manifolds
without boundary, Hausdorffness, and second countability. These extra topological
assumptions are not needed merely to define a metric.

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
