# Schreier and Kurosh subgroup theorems via covering graphs

This repository formalizes the sharp finite-index formula for free groups on
finite generating types. For a finite nonempty type `α`, a subgroup
`H ≤ FreeGroup α` of finite index `d` is proved to be free of rank
`1 + d * (Fintype.card α - 1)`:

```lean
Nonempty (H ≃* FreeGroup (Fin (1 + H.index * (Fintype.card α - 1))))
```

More strongly, the implementation exposes a `FreeGroupBasis` for `H` with
exactly that finite index type. Its generators are obtained from the edges
outside a certified geodesic spanning tree in the finite coset Schreier
covering. The earlier `FreeGroup (Fin n)` theorem remains available as a
specialization, including the truncation-safe statement valid when `n = 0`.

The regular-cover consequence is formalized too. If `H` is normal, the
automorphism group of the finite Schreier action is proved equivalent to the
quotient group:

```lean
GraphCoveringTheory.finiteIndexQuotientDeckGroupEquiv G H :
  G ⧸ H ≃* GraphCoveringTheory.SchreierDeckGroup G H
```

Thus every deck transformation is a unique right translation, not merely an
element of a quotient action.

## Kurosh expansion

The new Bass--Serre development proves Kurosh's subgroup theorem for an
arbitrary subgroup of an arbitrary indexed free product. The subgroup acts on
the explicit Bass--Serre tree, and a locally bijective universal
graph-of-groups cover is used to prove the normal-form map is an isomorphism.

The factor-only public statement is:

```lean
GraphCoveringTheory.Kurosh.kurosh_decomposition G H :
  Nonempty (KuroshActiveProduct G H ≃* H)
```

`KuroshActiveProduct G H` is the free product of the nontrivial quotient
vertex stabilizers together with the free group of the quotient graph. Each
of those vertex stabilizers is proved to be an intersection
`H ∩ g G_i g⁻¹` for some original free factor. The preceding
`kurosh_bass_serre_decomposition` theorem retains all quotient-vertex
stabilizers, including the trivial central ones, and is the direct
graph-of-groups form of the result. The quotient-vertex indexing avoids
choosing duplicate representatives; it is the canonical covering-graph
version of the usual double-coset formulation.

The proof follows the Bass--Serre covering-graph argument. The free product's
explicit tree has central vertices and factor vertices; after passing to the
`H`-quotient, its vertex stabilizers supply the graph-of-groups factors and the
quotient graph supplies the free part. Explicit star and costar bijections,
path lifting, and the tree's unique-path property prove injectivity of the
normal-form map, while the factor loops and quotient-graph generators prove
surjectivity. A final factor-removal equivalence deletes the trivial central
stabilizers. The finite Schreier construction above separately proves the
truncation-safe statement

```lean
Nonempty (H ≃* FreeGroup
  (Fin (H.index * Fintype.card α + 1 - H.index)))
```

and derives the usual formula when `α` is nonempty.

## Repository map

- `Challenge.lean`/`Solution.lean` remain the small Schreier Palomar surface;
  `KuroshChallenge.lean`/`KuroshSolution.lean` and
  `comparator-kurosh.json` provide the corresponding Kurosh surface.
- `GraphCoveringTheory/SchreierCover.lean` defines the finite Schreier graph,
  its rose projection, explicit star/costar equivalences, and the
  generator-preserving free-groupoid instance.
- `GraphCoveringTheory/IndexFormula.lean` proves the spanning-tree count,
  exposes the resulting finite Schreier basis, and proves the subgroup
  identification and index formula.
- `GraphCoveringTheory/Deck.lean` identifies the deck group of a finite
  regular Schreier action with its quotient group.
- `GraphCoveringTheory/Kurosh.lean` defines the free-product Bass--Serre tree,
  quotient graph, stabilizers, and graph-of-groups factors.
- `GraphCoveringTheory/KuroshTheorem.lean` exposes the checked Kurosh
  decompositions; its supporting modules construct the universal cover,
  path-lifting normal form, and the trivial-factor reduction.
- `FiniteGraphFreeGroup/` is the reusable finite-graph basis development from
  the preceding project.
- `comparator.json` records the exact Challenge/Solution correspondence.
- `formalization.yaml` records scope, provenance, authorship, and review
  status.

The repository does not claim the full classification of all pointed covers,
the general normalizer formula for arbitrary (not necessarily regular)
subgroups, or a topological cover classification. The regular quotient case
is proved for the finite Schreier action, while those broader statements
remain natural follow-on modules.

## Verification

The project is pinned to Lean 4.32.0 and Mathlib v4.32.0. The checked-in
manifest records the dependency closure.

```text
lake build
cd docbuild && lake build GraphCoveringTheory:docs
cd ..
lake env lean --src-deps Challenge.lean
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

Each Challenge file contains one deliberate statement-surface proof hole; the
Solution files and the implementation library contain no proof holes or
custom axioms. The two Comparator configurations check their respective
headline theorems with Lean's kernel and NanoDa.

The repository follows the
[Palomar statement/solution workflow](https://palomar-registry.org/how-to-submit).
When this snapshot is ready for registry review, submit its immutable commit
through the [Palomar submission form](https://submit.palomar-registry.org/).
