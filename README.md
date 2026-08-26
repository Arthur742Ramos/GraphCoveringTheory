# Finite graph fundamental groups: combinatorial and geometric models

This repository formalizes the spanning-tree computation for a finite
connected graph. A graph is represented as a finite directed multigraph
(Mathlib `Quiver`), so directed parallel edges and loops are allowed;
connectivity is imposed after symmetrizing the edges. For a chosen root, the
combinatorial object is the endomorphism group in Mathlib's free groupoid on
the graph.

The main result is an explicit group equivalence:

```lean
Nonempty (graphFundamentalGroup root ≃*
  FreeGroup (Fin (edgeCount + 1 - vertexCount)))
```

The proof constructs Mathlib's geodesic spanning tree, turns every non-tree
edge into an explicit free generator by the universal property of the free
groupoid, and proves the complement has the displayed cardinality from first
principles. The `E + 1 - V` expression is the truncation-safe natural-number
form of `E - (V - 1)`; the repository proves that these coincide under the
connectivity hypotheses.

The reusable API also provides:

- `graphFundamentalGroupBasis`, the actual non-tree-edge basis;
- `graphFundamentalGroupEquiv`, an explicit equivalence rather than only an
  existence proposition;
- root-change equivalences for the combinatorial vertex groups;
- cycle-rank positivity, the tree-edge criterion, and triviality criterion;
- the corresponding abelianization and free-abelian-group equivalences;
- `graphCoverProjection`, a path-lifting quiver whose star and costar maps are
  proved bijective, hence a Mathlib quiver covering.

The geometric layer in `FiniteGraphFreeGroup.Realization` now defines the
standard quotient realization: one discrete vertex for each graph vertex and
one copy of the unit interval for each edge, with interval endpoints attached
to the corresponding source and target vertices. It proves the endpoint-label
invariant and injectivity of the vertex inclusion, constructs the edge and
symmetrized-quiver paths, proves path-connectedness under weak connectivity,
and proves compactness for finite graphs. It also constructs the canonical
functor from the free groupoid to Mathlib's topological `FundamentalGroupoid`
and the induced homomorphism
`graphCombinatorialToTopological`.

The `FiniteGraphFreeGroup.TreeContraction` layer proves the geometric tree
lemma needed by a universal-cover approach: the quotient realization of any
directed arborescence is contractible by an explicit continuous cellwise
contraction, and hence is simply connected. The contraction is kernel-checked
through the quotient topology; it is not an assumption about the realization.

The comparison homomorphism is deliberately not advertised as an isomorphism
yet: proving surjectivity and injectivity requires a separate topological
normal-form theorem for arbitrary continuous paths and homotopies in this
finite one-dimensional quotient. The repository therefore keeps the proved
combinatorial rank theorem and the proved geometric realization distinct.

## Repository map

- `Challenge.lean` is the small, human-auditable statement surface.
- `Solution.lean` exposes the same theorem and connects it to the proof.
- `FiniteGraphFreeGroup/Proof.lean` contains the proof development.
- `FiniteGraphFreeGroup/Consequences.lean` exposes the basis and structural
  consequences of the computation.
- `FiniteGraphFreeGroup/Cover.lean` defines and verifies the path-lifting
  covering construction.
- `FiniteGraphFreeGroup/Realization.lean` defines the geometric realization,
  its basic path geometry, and the canonical comparison map to topological
  fundamental groups.
- `FiniteGraphFreeGroup/TreeContraction.lean` proves contractibility and
  simple connectedness of arborescence realizations by an explicit quotient
  homotopy.
- `comparator.json` records the declarations checked for exact correspondence.
- `formalization.yaml` records scope, provenance, authorship, and review status.

## Verification

The project is pinned to Lean 4.32.0 and Mathlib v4.32.0. The checked-in
manifest records the complete dependency closure.

```text
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

`Challenge.lean` contains three deliberate proof holes; `Solution.lean` and
the library development contain no proof holes or custom axioms. Comparator
checks all three Challenge statements with both Lean's kernel and NanoDa.

The repository follows the
[Palomar statement/solution workflow](https://palomar-registry.org/how-to-submit).
When this snapshot is ready for registry review, submit its immutable commit
through the [Palomar submission form](https://submit.palomar-registry.org/).
