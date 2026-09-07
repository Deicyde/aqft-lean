# Agent guidelines

This repository develops proved foundations for algebraic quantum field theory in
Lean 4. The first milestone is pseudo-Riemannian geometry. See `README.md` for the
current status and `docs/roadmap.md` for planned work.

- Search the pinned Mathlib before adding definitions or notation. Check candidate
  declarations with `#check` and use focused imports.
- Use Mathlib's manifolds, tangent bundles, bilinear forms, and operator algebras.
  Express smooth tensor fields as bundle sections, with the correct transition maps.
- A pseudo-Riemannian metric is symmetric and nondegenerate. It need not be positive
  definite, and a nonzero vector can have zero square.
- Use the Lorentzian sign convention `(-,+,…,+)`. State dimensions, signatures,
  orientation assumptions, and causal-vector conventions explicitly.
- Cite mathematical sources in module documentation. Clearly distinguish established
  results, definitions, and future work.
- Every committed theorem must have a complete proof. Do not use `sorry`, `admit`,
  new axioms, or `native_decide`. Do not encode unfinished mathematics as arbitrary
  proposition parameters or trivial definitions.
- Build every changed module with `lake --wfail build Module.Name`. Run
  `lake --wfail build` before publishing a commit. Inspect `#print axioms` before
  reporting new results as proved.
- Keep mathematical text concise. Update the roadmap when completing a milestone.
