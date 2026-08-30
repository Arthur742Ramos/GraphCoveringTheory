import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

open FreeGroup

noncomputable section

namespace GraphCoveringTheory

/-!
# Schreier's index formula

The challenge asks for the sharp rank formula for a finite-index subgroup of a
finite-rank free group.  The positivity hypothesis keeps the standard
`1 + d * (n - 1)` spelling honest in `Nat`.
-/

theorem schreier_index_formula (n : ℕ) (H : Subgroup (FreeGroup (Fin n)))
    [H.FiniteIndex] (hn : 0 < n) :
    Nonempty (H ≃* FreeGroup (Fin (1 + H.index * (n - 1)))) := by
  sorry

end GraphCoveringTheory
