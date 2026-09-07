# Roadmap

The first target is a mathematically faithful geometric foundation. We will then
state the concrete Haag–Kastler axioms. Each step should add complete definitions
and proofs, with examples that exercise the definitions.

## 1. Pseudo-Riemannian foundations — started

Completed: a smooth, symmetric, nondegenerate tangent pairing; separation lemmas;
constant metrics; and a smooth Minkowski metric in every dimension `1+n`.

Next:

- Relate smoothness of the metric section to smooth evaluation on vector fields.
- Define the index using Mathlib's `QuadraticForm.sigNeg`. Define Lorentzian metrics
  by index one, with explicit dimension assumptions for spacetime applications.
- Compute the Minkowski signature: one negative and `n` positive directions.
- Develop the metric duality with cotangent spaces and pullback under
  diffeomorphisms. An arbitrary smooth pullback can be degenerate.
- Prove local constancy of signature, then constancy on connected components.
  Do not assume a disconnected manifold has one global signature automatically.

Levi-Civita connections, geodesics, and curvature belong to the geometric library,
but are not prerequisites for a first AQFT net on explicit Minkowski space.

## 2. Minkowski causal geometry

Define timelike, spacelike, null, causal, and future-directed vectors. State
explicitly which predicates exclude zero; the closed future cone includes zero.
Define separation using differences of points and prove invariance under
translations and the relevant Lorentz transformations.

Define bounded open regions using the existing Euclidean topology and bornology.
Record whether additional restrictions such as nonemptiness, causal convexity, or
double-cone shape are imposed. Prove the inclusion order and spacelike separation
properties needed by nets.

## 3. Local algebras and nets

Reuse `VonNeumannAlgebra H` for local algebras acting on one complex Hilbert space.
Define a net indexed by the chosen regions. State isotony as monotonicity and
locality as pairwise commutation at spacelike separation.

Keep abstract C*-algebra nets and concrete von Neumann nets as distinct
formulations. Connecting them through a state and GNS representation requires
additional theorems. Treat additivity, time-slice, and other optional assumptions
as separately named conditions.

## 4. Covariance and vacuum

Construct the proper orthochronous Poincaré group and its action on regions.
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
