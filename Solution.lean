import FiniteGraphFreeGroup.Consequences
import FiniteGraphFreeGroup.Cover

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

universe u

namespace FiniteGraphFreeGroup

theorem graph_fundamental_group_free_rank {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Nonempty (graphFundamentalGroup root ≃*
      FreeGroup (Fin (edgeCount (V := V) + 1 - vertexCount (V := V)))) := by
  exact proved_graph_fundamental_group_free_rank root

end FiniteGraphFreeGroup
