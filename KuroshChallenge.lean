import GraphCoveringTheory.Kurosh

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

universe u v

namespace GraphCoveringTheory.KuroshChallenge

/-!
# Palomar statement surface for Kurosh's theorem

The challenge imports only the Bass--Serre data layer.  The normal-form proof
and the factor-removal corollary live in the implementation modules imported
by `KuroshSolution.lean`.
-/

theorem kurosh_bass_serre_decomposition_challenge {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (Kurosh.FreeProduct G)) :
    Nonempty (@Kurosh.TreeKuroshProduct.{u, v, 0} ι G _ H ≃* H) := by
  sorry

end GraphCoveringTheory.KuroshChallenge
