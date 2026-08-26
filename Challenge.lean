import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Combinatorics.Quiver.Covering
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

/-!
# Fundamental group of a finite connected graph

We model a finite directed multigraph by a quiver with finite hom types. Its
combinatorial fundamental group is the endomorphism group at a chosen root in
the free groupoid on the graph. `WeaklyConnected` means connected after
forgetting orientations. The statements below expose the rank formula, its
tree/triviality consequence, and the associated path-lifting covering.
-/

namespace FiniteGraphFreeGroup

universe u

/- The finite-edge hypothesis is separated from `[Fintype V]` so that the
   graph model also supports parallel edges without extra coding. -/
class FiniteQuiver (V : Type u) [Quiver.{u} V] where
  finite_hom : ∀ a b : V, Fintype (@Quiver.Hom V _ a b)

@[reducible]
instance finiteHom {V : Type u} [Quiver.{u} V] [FiniteQuiver V] (a b : V) :
    Fintype (@Quiver.Hom V _ a b) :=
  FiniteQuiver.finite_hom (V := V) a b

def baseTotalEquiv (V : Type u) [Quiver.{u} V] :
    Quiver.Total V ≃ Σ a : V, Σ b : V, a ⟶ b where
  toFun e := ⟨e.left, e.right, e.hom⟩
  invFun e := ⟨e.1, e.2.1, e.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

noncomputable instance baseTotalFintypeInst [Fintype V] [Quiver.{u} V]
    [∀ a b : V, Fintype (a ⟶ b)] : Fintype (Quiver.Total V) := by
  classical
  exact Fintype.ofEquiv _ (baseTotalEquiv V).symm

/-- Connectivity of the underlying undirected multigraph. -/
class WeaklyConnected (V : Type u) [Quiver.{u} V] : Prop where
  path : ∀ a b : V,
    Nonempty (@Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b)

/-- The number of vertices. -/
def vertexCount {V : Type u} [Fintype V] : ℕ := Fintype.card V

/-- The number of directed edges, counted with multiplicity. -/
noncomputable def edgeCount {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V] : ℕ :=
  Fintype.card (Quiver.Total V)

/- The natural-number cycle rank used by the solution. -/
noncomputable abbrev cycleRank {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V] : ℕ :=
  edgeCount (V := V) + 1 - vertexCount (V := V)

/-- The combinatorial fundamental group based at `root`. -/
abbrev graphFundamentalGroup {V : Type u} [Quiver.{u} V] (root : V) :=
  End ((Quiver.FreeGroupoid.of V).obj root)

/-- Vertices in the path-lifting cover over a root. -/
abbrev graphCoverVertex {V : Type u} [Quiver.{u} V] (root : V) :=
  Σ v : V, ((Quiver.FreeGroupoid.of V).obj root ⟶
    (Quiver.FreeGroupoid.of V).obj v)

instance graphCoverQuiver {V : Type u} [Quiver.{u} V] (root : V) :
    Quiver (graphCoverVertex root) where
  Hom x y := {e : x.1 ⟶ y.1 //
    x.2 ≫ (Quiver.FreeGroupoid.of V).map e = y.2}

/-- The path-lifting projection to the original quiver. -/
def graphCoverProjection {V : Type u} [Quiver.{u} V] (root : V) :
    graphCoverVertex root ⥤q V where
  obj x := x.1
  map e := e.1

/--
The fundamental group of a finite weakly connected graph is free of rank
`E + 1 - V`. In `ℕ`, this is the canonical truncation-safe spelling of
`E - V + 1`; connectedness supplies the spanning-tree inequality.
-/
theorem graph_fundamental_group_free_rank {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Nonempty (graphFundamentalGroup root ≃*
      FreeGroup (Fin (edgeCount (V := V) + 1 - vertexCount (V := V)))) := by
  sorry

/-- A connected graph has trivial combinatorial fundamental group exactly when
its edge count is that of a spanning tree. -/
theorem graphFundamentalGroup_subsingleton_iff_cycleRank_zero
    {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V]
    [WeaklyConnected V] (root : V) :
    Subsingleton (graphFundamentalGroup root) ↔ cycleRank (V := V) = 0 := by
  sorry

/-- The path-lifting projection is a covering of quivers. -/
theorem graphCoverProjection_isCovering {V : Type u} [Quiver.{u} V] (root : V) :
    (graphCoverProjection root).IsCovering := by
  sorry

end FiniteGraphFreeGroup
