import FiniteGraphFreeGroup.TopologicalComparison

open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

/-!
# Proved solution

The comparator-facing theorem is stated independently in `Challenge.lean` and
proved here from the explicit topological/combinatorial equivalence.
-/

universe u

namespace FiniteGraphFreeGroup

theorem graph_fundamental_group_free_rank {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Nonempty (FundamentalGroup (graphRealization V) (graphVertex root) ≃*
      FreeGroup (Fin (edgeCount (V := V) + 1 - vertexCount (V := V)))) := by
  exact proved_topological_fundamental_group_free_rank root

end FiniteGraphFreeGroup
