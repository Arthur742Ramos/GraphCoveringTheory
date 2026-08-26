# Contributing

Keep the advertised theorem in `Challenge.lean` small and independently
auditable. Put substantive proofs in `FiniteGraphFreeGroup/Proof.lean` and
expose the completed result from `Solution.lean`.

Before opening a pull request, run:

```text
lake build
cd docbuild && lake build FiniteGraphFreeGroup:docs
cd ..
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

Do not add custom axioms or replace completed proofs with `sorry`. Keep the
checked-in Lake manifests and metadata synchronized with the source, and
preserve the Apache-2.0 license.
