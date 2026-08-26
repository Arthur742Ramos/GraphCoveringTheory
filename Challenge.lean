import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import FiniteGraphFreeGroup.Consequences
import FiniteGraphFreeGroup.Cover
import FiniteGraphFreeGroup.Realization

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

/-!
# Fundamental group of a finite connected graph

The graph is a finite directed multigraph represented by a Mathlib `Quiver`.
Its geometric realization has one interval cell for each edge, with the
endpoints attached to the corresponding vertices. Connectivity is imposed
after symmetrizing the edges, so orientations and parallel edges are retained.

The challenge asks for the standard topological statement: the fundamental
group of this finite connected graph is free of rank `E - V + 1`.
-/

namespace FiniteGraphFreeGroup

universe u

/--
The topological fundamental group of a finite weakly connected graph is free
of rank `E + 1 - V`. The natural-number expression is the truncation-safe
spelling of `E - V + 1`; weak connectivity supplies the required
spanning-tree inequality.
-/
theorem graph_fundamental_group_free_rank {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Nonempty (FundamentalGroup (graphRealization V) (graphVertex root) ≃*
      FreeGroup (Fin (edgeCount (V := V) + 1 - vertexCount (V := V)))) := by
  sorry

end FiniteGraphFreeGroup
