import GraphCoveringTheory.KuroshTheorem

noncomputable section

universe u v

namespace GraphCoveringTheory.KuroshChallenge

/-! The checked proof of the Kurosh Palomar statement. -/

theorem kurosh_bass_serre_decomposition_challenge {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (Kurosh.FreeProduct G)) :
    Nonempty (@Kurosh.TreeKuroshProduct.{u, v, 0} ι G _ H ≃* H) :=
  Kurosh.kurosh_bass_serre_decomposition G H

end GraphCoveringTheory.KuroshChallenge
