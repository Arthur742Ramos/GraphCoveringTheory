import GraphCoveringTheory

open FreeGroup

noncomputable section

universe u

namespace GraphCoveringTheory

/-!
# Proved solution

The comparator-facing theorem is kept as a tiny statement surface.  The proof
is supplied by the finite Schreier covering construction in
`GraphCoveringTheory.IndexFormula`.
-/

theorem schreier_index_formula (α : Type u) [Fintype α] [Nonempty α]
    (H : Subgroup (FreeGroup α)) [H.FiniteIndex] :
    Nonempty (H ≃* FreeGroup (Fin (1 + H.index * (Fintype.card α - 1)))) := by
  exact schreier_index_formula_fintype_proved α H

end GraphCoveringTheory
