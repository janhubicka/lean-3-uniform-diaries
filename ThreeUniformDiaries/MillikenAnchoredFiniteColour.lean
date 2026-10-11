import ThreeUniformDiaries.MillikenFiniteColour

/-!
# Fixed-stem finite-colour Milliken via the standalone library

The first `n` *source* levels of the chosen strong subtree are fixed.
This is a downstream use of the verified homogeneous theorem, not
yet the manuscript's variable-degree synchronized vector theorem.
-/

namespace ThreeUniformDiaries

open Milliken

universe u v

/-- Homogeneous fixed-stem Milliken, delegated to the application library. -/
theorem anchoredHomogeneousMillikenFiniteColouring
    {ι : Type u} [Finite ι] [Nonempty ι]
    {κ : Type v} [Fintype κ]
    (n m : Nat)
    (A : StrongEmbedding ι)
    (colour : StrongTreeSpace.Approx ι m → κ) :
    ∃ B : StrongEmbedding ι,
      StrongTreeSpace.le ι B A ∧
      StrongTreeSpace.approx ι n B =
        StrongTreeSpace.approx ι n A ∧
      ∀ X Y : StrongEmbedding ι,
        StrongTreeSpace.le ι X B →
        StrongTreeSpace.le ι Y B →
        StrongTreeSpace.approx ι n X =
          StrongTreeSpace.approx ι n A →
        StrongTreeSpace.approx ι n Y =
          StrongTreeSpace.approx ι n A →
        colour (StrongTreeSpace.approx ι m X) =
          colour (StrongTreeSpace.approx ι m Y) :=
  Milliken.Applications.millikenFixedStemFiniteColouring n m A colour

end ThreeUniformDiaries
