# Contributing

Keep the advertised theorem in `Challenge.lean` small and independently
auditable. The Schreier proof lives in `FiniteGraphFreeGroup/Proof.lean` and
is exposed from `Solution.lean`; the Bass--Serre/Kurosh proof is split across
the `GraphCoveringTheory/Kurosh*.lean` support modules and is exposed from
`GraphCoveringTheory/KuroshTheorem.lean`. The Kurosh Palomar surface is
`KuroshChallenge.lean`/`KuroshSolution.lean` with `comparator-kurosh.json`.

Before opening a pull request, run:

```text
lake build
cd docbuild && lake build GraphCoveringTheory:docs
cd ..
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
./scripts/verify-comparator.sh comparator-kurosh.json
```

Do not add custom axioms or replace completed proofs with `sorry`. Keep the
checked-in Lake manifests and metadata synchronized with the source, and
preserve the Apache-2.0 license.
