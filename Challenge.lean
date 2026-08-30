import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

open FreeGroup

noncomputable section

universe u

namespace GraphCoveringTheory

/-!
# Schreier's index formula

The challenge asks for the sharp rank formula for a finite-index subgroup of a
free group on any finite nonempty generating type.  The statement is therefore
independent of a chosen enumeration of the generators.
-/

theorem schreier_index_formula (α : Type u) [Fintype α] [Nonempty α]
    (H : Subgroup (FreeGroup α)) [H.FiniteIndex] :
    Nonempty (H ≃* FreeGroup (Fin (1 + H.index * (Fintype.card α - 1)))) := by
  sorry

end GraphCoveringTheory
