# Roadmap

The first target is a mathematically faithful geometric foundation. We will then
state the concrete Haag–Kastler axioms. Each step should add complete definitions
and proofs, with examples that exercise the definitions.

## 1. Pseudo-Riemannian foundations — started

Completed:

- A smooth, symmetric, nondegenerate tangent pairing and separation lemmas.
- Fiber pairing data and separate continuity/smoothness and Lorentzian manifold
  typeclasses, following Mathlib's Riemannian construction without its distance
  compatibility condition.
- Constant metrics and smooth evaluation on vector fields.
- An index-one Lorentzian metric definition using Mathlib's `sigNeg`.
- Metric and manifold conditions proved equivalent to signature `(1,n−1)` in total
  dimension `n`, using Mathlib's `sigNeg` and `sigPos` directly.
- The Minkowski signature: one negative and `n` positive directions, including
  `n = 0`, and the resulting smooth Lorentzian metric.
- Metric-preserving diffeomorphisms, their identity/composition/inverse laws, and
  the algebraic self-isometry group. Isometries preserve both signature components.
- Concrete Minkowski translations and time reversal in this group.

Next:

- Develop the metric duality with cotangent spaces and pullback under
  diffeomorphisms. An arbitrary smooth pullback can be degenerate.
- Prove local constancy of signature, then constancy on connected components.
  Do not assume a disconnected manifold has one global signature automatically.
- Equip the isometry group with an appropriate topology, then develop its Lie
  group structure under explicitly stated hypotheses.

Levi-Civita connections, geodesics, and curvature belong to the geometric library,
but are not prerequisites for a first AQFT net on explicit Minkowski space.

## 2. Minkowski causal geometry

Completed: spacelike separation of sets using strictly positive Minkowski squares
of point differences. Separation is symmetric, passes to subsets, implies
disjointness, and is preserved by shared translations. Sign examples exclude unit
time and nonzero null displacements and include unit spatial displacements. With
zero spatial dimensions, separation holds exactly when one set is empty.

Next: define the remaining causal-vector predicates and the future cone, stating
which include zero. Prove separation invariance under the relevant Lorentz transformations.

Completed: open bounded regions using the existing product topology and bornology,
with the inclusion order and finite unions. The empty set is included; no causal
convexity or double-cone restriction is imposed.

## 3. Local algebras and nets

Completed: `IsotoneNet n H` uses Mathlib's `OrderHom` to assign
`VonNeumannAlgebra H` values to open bounded regions on one complex Hilbert space.
Isotony is stated as operator-set inclusion, and the local algebras form a directed
family. No algebra value is prescribed for the empty region.

Completed: `IsotoneNet.IsCausal` states pairwise operator commutation at spacelike
separation. Equivalent formulations use inclusion in the other algebra's commutant
or vanishing commutators. Empty-region observables commute with every local algebra.

Keep abstract C*-algebra nets and concrete von Neumann nets as distinct
formulations. Connecting them through a state and GNS representation requires
additional theorems. Treat additivity, time-slice, and other optional assumptions
as separately named conditions.

## 4. Covariance and vacuum

Construct the proper orthochronous Poincaré group and its action on regions. The
existing full isometry group has no orientation or time-orientation restriction;
identifying the Minkowski isometry group with the full Poincaré group is also
future work.
Specify a strongly continuous unitary representation and covariance by unitary
conjugation. State a normalized invariant vacuum that is cyclic for the global
observable algebra; distinguish existence from any additional uniqueness axiom.

## 5. Spectrum condition

Audit joint spectral measures for strongly continuous translation representations.
State that the joint spectral measure is supported in the closed future cone, or
prove equivalence with an appropriate formulation using translation generators.
These generators are generally unbounded. Ordinary spectra of bounded operators
do not suffice. Do not insert an unconstrained proposition as a substitute for
the missing spectral theory.

## 6. Curved spacetime — later extension

Develop time orientation, causal curves, Cauchy surfaces, and global hyperbolicity.
Construct the spacetime category with metric- and orientation-preserving embeddings
having causally convex images. Then formulate locally covariant AQFT and the
time-slice axiom following Brunetti–Fredenhagen–Verch, §2.

Sources and links are listed in the [README](../README.md).
