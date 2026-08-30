import GraphCoveringTheory.IndexFormula

/-!
# Schreier's index formula through finite covering graphs

The action groupoid of a free group on its finite coset space is the finite
Schreier covering graph.  Its vertex group is the subgroup, and the spanning-
tree basis computation counts one free generator for every edge outside a
tree.  The development exposes that finite Schreier basis as well as the
resulting index formula.  The public theorem is
`GraphCoveringTheory.schreier_index_formula`.
-/
