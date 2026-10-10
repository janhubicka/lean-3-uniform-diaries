import ThreeUniformDiaries.MillikenFiniteColour

/-!
# Anchored finite-colour Milliken from the checked lean-milliken theorem

The manuscript uses a Milliken statement with the first n levels
fixed. The checked lean-milliken library already proves the full
basic-neighbourhood form of Milliken's theorem, not merely a
conditional pigeonhole lemma.

Here the fixed-stem homogeneous-tree corollary is made completely
explicit. For any strong embedding A and its genuine n-approximation
a, and any finite colouring of m-approximations, a stronger embedding
B below A retains exactly a and homogenises the m-approximations
among all further strong refinements which retain a.

This is the correct fixed-prefix homogeneous-tree interface.
The manuscript's synchronized three-coordinate vector tree with
level-dependent finite branching still needs a representation and
transport argument.
-/

namespace ThreeUniformDiaries

open Milliken

universe u v

/-- A directly anchored finite-colour consequence of the fully
verified Milliken theorem on basic Ellentuck neighbourhoods. -/
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
          colour (StrongTreeSpace.approx ι m Y) := by
  let S := StrongTreeSpace.approximationSystem ι
  let a := StrongTreeSpace.approx ι n A
  have hne : (S.neighborhood a A).Nonempty := by
    refine ⟨A, ?_⟩
    exact ⟨StrongTreeSpace.le_refl ι A, rfl⟩
  obtain ⟨B, hBA, hhom⟩ :=
    RamseySpace.finiteApproximationColouring
      (Milliken.Chapter6.milliken_onBasicNeighborhoods (ι := ι))
      a A hne colour
  refine ⟨B, hBA.1, hBA.2, ?_⟩
  intro X Y hXB hYB hX hY
  exact hhom X ⟨hXB, hX⟩ Y ⟨hYB, hY⟩

end ThreeUniformDiaries
