import GraphCoveringTheory

open FreeGroup

noncomputable section

namespace GraphCoveringTheory

/-!
# Proved solution

The comparator-facing theorem is kept as a tiny statement surface.  The proof
is supplied by the finite Schreier covering construction in
`GraphCoveringTheory.IndexFormula`.
-/

theorem schreier_index_formula (n : ℕ) (H : Subgroup (FreeGroup (Fin n)))
    [H.FiniteIndex] (hn : 0 < n) :
    Nonempty (H ≃* FreeGroup (Fin (1 + H.index * (n - 1)))) := by
  exact schreier_index_formula_proved n H hn

end GraphCoveringTheory
