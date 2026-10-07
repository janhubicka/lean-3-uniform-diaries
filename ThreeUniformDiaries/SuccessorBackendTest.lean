import SuccessorTree.ShapeFiniteRamsey

namespace ThreeUniformDiaries

open SuccessorTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Smoke test that the current verified successor-tree Ramsey backend is
available together with the Milliken development. -/
theorem successorRamseyBackendAvailable
    {κ : Type w} [Fintype κ]
    (H : SMTree S) (n k : Nat)
    (colour : SMTree.AM H n k → κ) :
    ∃ W : SMTree.ShapeSubspace H n,
      ∀ a b : SMTree.AM H n k,
        colour (H.shapeActK n k W a) =
          colour (H.shapeActK n k W b) :=
  H.shapePreservingRamsey n k colour

end ThreeUniformDiaries
