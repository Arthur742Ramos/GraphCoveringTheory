import GraphCoveringTheory.Deck
import GraphCoveringTheory.KuroshTheorem

/-!
# Schreier and Kurosh subgroup theorems through covering graphs

The action groupoid of a free group on its finite coset space is the finite
Schreier covering graph.  Its vertex group is the subgroup, and the spanning-
tree basis computation counts one free generator for every edge outside a
tree.  The development exposes that finite Schreier basis as well as the
resulting index formula.  The public theorem is
`GraphCoveringTheory.schreier_index_formula`.

The companion `GraphCoveringTheory.KuroshTheorem` development constructs the
Bass--Serre tree of an arbitrary indexed free product and proves the Kurosh
decomposition of every subgroup.  Its factor-only form retains the nontrivial
quotient vertex stabilizers and identifies each with an intersection of the
subgroup and a conjugate of an original factor.

For a finite-index normal subgroup, the companion `Deck` module also proves
that the deck transformations of the finite Schreier action are exactly the
right translations by the quotient group.
-/
