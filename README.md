# Schreier index formula via finite covering graphs

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

The proof follows the covering-graph argument. The coset action of the free
group gives a finite action groupoid, viewed as the Schreier covering of the
`α`-petalled rose. Its root endomorphism group is identified with `H`; an
explicit generating quiver has `d` vertices and `d * Fintype.card α` directed
edges; and a Mathlib geodesic spanning tree leaves exactly
`1 + d * (Fintype.card α - 1)` free generators. The implementation first
proves the truncation-safe statement

```lean
Nonempty (H ≃* FreeGroup
  (Fin (H.index * Fintype.card α + 1 - H.index)))
```

and derives the usual formula when `α` is nonempty.

## Repository map

- `Challenge.lean` is the small, closure-safe Palomar statement surface.
- `Solution.lean` proves exactly the Challenge theorem.
- `GraphCoveringTheory/SchreierCover.lean` defines the finite Schreier graph,
  its rose projection, explicit star/costar equivalences, and the
  generator-preserving free-groupoid instance.
- `GraphCoveringTheory/IndexFormula.lean` proves the spanning-tree count,
  exposes the resulting finite Schreier basis, and proves the subgroup
  identification and index formula.
- `GraphCoveringTheory/Deck.lean` identifies the deck group of a finite
  regular Schreier action with its quotient group.
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
lake env lean --src-deps Challenge.lean
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

`Challenge.lean` contains one deliberate statement-surface proof hole;
`Solution.lean` and the implementation library contain no proof holes or
custom axioms. Comparator checks the headline theorem with Lean's kernel and
NanoDa.

The repository follows the
[Palomar statement/solution workflow](https://palomar-registry.org/how-to-submit).
When this snapshot is ready for registry review, submit its immutable commit
through the [Palomar submission form](https://submit.palomar-registry.org/).
