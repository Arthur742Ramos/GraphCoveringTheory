# Finite graph fundamental groups

This repository formalizes the standard computation of the fundamental group
of a finite connected graph. A graph is represented as a finite quiver, with
connectivity imposed after symmetrizing its edges. For a chosen root, the
combinatorial fundamental group is the endomorphism group in Mathlib's free
groupoid on that quiver.

The main result is an explicit group equivalence:

```lean
Nonempty (graphFundamentalGroup root ≃*
  FreeGroup (Fin (edgeCount + 1 - vertexCount)))
```

The proof constructs the spanning-tree basis and proves its cardinality from
first principles. The `E + 1 - V` expression is the truncation-safe natural
number form of `E - V + 1`. A topological realization is intentionally outside
the scope of this repository.

## Repository map

- `Challenge.lean` is the small, human-auditable statement surface.
- `Solution.lean` exposes the same theorem and connects it to the proof.
- `FiniteGraphFreeGroup/Proof.lean` contains the proof development.
- `comparator.json` records the declarations checked for exact correspondence.
- `formalization.yaml` records scope, provenance, authorship, and review status.

## Verification

The project is pinned to Lean 4.29.1 and Mathlib v4.29.1. The checked-in
manifest records the complete dependency closure.

```text
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The repository follows the
[Palomar statement/solution workflow](https://palomar-registry.org/how-to-submit).
When this snapshot is ready for registry review, submit its immutable commit
through the [Palomar submission form](https://submit.palomar-registry.org/).
