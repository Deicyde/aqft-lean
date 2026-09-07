# Roadmap

The project develops a geometric foundation and abstract C*-algebra nets for the
Haag–Kastler framework. Each step should add complete definitions and proofs,
with examples that exercise the definitions. Covariance acts directly by
automorphisms of the abstract ambient algebra; states remain future work.

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
  the self-isometry group. Isometries preserve both signature components.
- A self-isometry topology induced by compact-open convergence of maps and
  inverses. Group operations and evaluation are continuous on locally compact manifolds.
- Concrete Minkowski translations and time reversal in this group.

Next:

- Develop the metric duality with cotangent spaces and pullback under
  diffeomorphisms. An arbitrary smooth pullback can be degenerate.
- Prove local constancy of signature, then constancy on connected components.
  Do not assume a disconnected manifold has one global signature automatically.
- Develop the isometry group's Lie group structure under explicitly stated hypotheses.

Levi-Civita connections, geodesics, and curvature belong to the geometric library,
but are not prerequisites for a first AQFT net on explicit Minkowski space.

## 2. Causal geometry

Completed: spacelike separation of sets using strictly positive Minkowski squares
of point differences. Separation is symmetric, passes to subsets, implies
disjointness, and is preserved by shared translations. Sign examples exclude unit
time and nonzero null displacements and include unit spatial displacements. With
zero spatial dimensions, separation holds exactly when one set is empty.

Next: define the remaining causal-vector predicates and the future cone, stating
which include zero. Prove separation invariance under the relevant Lorentz transformations.

Completed: regular C¹ causal curves and metric-induced separation on arbitrary
Lorentzian manifolds. Tangents are nonzero with nonpositive square, including at
interval endpoints. The relation includes coincident points and is symmetric;
no global time orientation or transitive closure is imposed. In Minkowski space,
causal connectivity is proved equivalent to nonpositive squared displacement, so
the curve definition recovers the original strict spacelike-separation criterion.

Completed: regions on arbitrary topological spaces as open subsets with compact
closure, with inclusion and finite unions. In finite-dimensional Minkowski space
these are exactly the bounded open subsets. The empty set is included; no causal
convexity or double-cone restriction is imposed. Homeomorphisms preserve regions,
and the self-isometry group acts on them.

## 3. Local algebras and nets

Completed: `CStarSubalgebra B` bundles norm-closed unital complex star subalgebras
of an abstract ambient `B` with `[CStarAlgebra B]`. Each carrier inherits a native
`CStarAlgebra` instance and the unit and scalar inclusion of `B`.

Completed: `IsotoneNet M B` uses Mathlib's `OrderHom` to assign these algebras to
relatively compact open regions of `M`. Isotony is set inclusion, and the local
algebras form a directed family. No Hilbert-space representation is chosen, no
algebra value is prescribed for the empty region, and the local algebras are not
required to generate all of `B`.

Completed: `A.IsCausal g` states pairwise commutation in `B` for regions
separated by any Lorentzian metric `g`. Equivalent formulations use inclusion in
the other algebra's relative commutant inside `B` or vanishing commutators.
Empty-region observables commute with every local algebra.

Next: construct representations from states using Mathlib's GNS API, and connect
represented local algebras to local von Neumann algebras. These are additional
constructions on the net. Treat generation of the ambient algebra, additivity,
time-slice, and other additional assumptions as separately named conditions.

## 4. Isometry covariance and vacuum

Completed: `A.IsCovariant g π` requires the chosen operator representation `π`
to be faithful and asserts the existence of an injective group homomorphism
`α : g.IsometryGroup →* (B ≃⋆ₐ[ℂ] B)`. In the representation on a complete
complex Hilbert space, every matrix coefficient of `f ↦ π(α(f)(a))` is continuous.
The automorphisms transport local
algebras by `α(f)(A(O)) = A(f • O)`. The representation specifies the weak
operator topology, while the net and its algebra automorphisms remain abstract.
Since the locals need not generate `B`, faithfulness is imposed on the action on
all of `B`.

Completed: weak, strong, and ultraweak continuity of these represented
automorphism orbits are proved equivalent, giving equivalent covariance axioms.
The weak and strong definitions agree with Mathlib's operator topologies.
Ultraweak continuity uses coefficient series from two square-summable vector
sequences, following Lurie, Lecture 5. The series are proved convergent, and the
uniform operator bound proves the ultraweak equivalence. No separability or
operator-norm continuity assumption is imposed.

This uses the full isometry group, including time reversal in Minkowski space.
It is a stronger symmetry convention than the identity-component covariance
used by Fewster and Rejzner, §4.1. Faithfulness is an explicit requirement here.
Orientation-preserving subgroups and antiunitary symmetries remain future work.
A later positive-energy formulation must account
for this choice of symmetries.

Next: construct unitary implementations in GNS representations using suitable
invariant states. State a normalized invariant vacuum cyclic for the represented
observable algebra, and distinguish existence from
any additional uniqueness axiom.

## 5. Spectrum condition

In a Hilbert-space representation, audit joint spectral measures for strongly
continuous translation representations.
State that the joint spectral measure is supported in the closed future cone, or
prove equivalence with an appropriate formulation using translation generators.
These generators are generally unbounded. Ordinary spectra of bounded operators
do not suffice. Do not insert an unconstrained proposition as a substitute for
the missing spectral theory.

## 6. Further curved-spacetime structure

The net and causality axiom now apply to arbitrary Lorentzian manifolds. Develop
time orientation, Cauchy surfaces, and global hyperbolicity. Relate regular C¹
causal curves to piecewise C¹ and Lipschitz conventions. Construct the spacetime
category with metric- and orientation-preserving embeddings having causally convex images. Then formulate locally covariant AQFT and the
time-slice axiom following Brunetti–Fredenhagen–Verch, §2.

Sources and links are listed in the [README](../README.md).
