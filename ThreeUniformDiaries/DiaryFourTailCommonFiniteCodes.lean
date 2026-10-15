import ThreeUniformDiaries.DiaryFiniteThreeTailShiftATR
import ThreeUniformDiaries.DiaryCommonFinitePointedSource
import ThreeUniformDiaries.DiaryFinitePointedEnumNode

/-!
# A common genuine finite ATR source for two three-tail pictures

Two finite auxiliary-type-respecting maps out of the same
prefix-plus-three-vertex graph give exactly the common small
finite-source certificate required by the already verified I3
stabilisation theorem. The two maps may skip arbitrary target
enumeration levels. All statements are restricted to the genuine
finite source; its infinite zero extension is only an encoding.

The four-tail gadget application will use this theorem twice:
once for the original positive source, and once for the shifted
negative source. Both maps are first postcomposed with the same
generic aux-type-respecting embedding of the four-tail amalgam.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Two genuinely finite ATR embeddings from the same three-tail
source, both fixing its entire protected prefix, constitute an
actual common finite pointed source for their last two vertices.
No infinite-tail or convexity hypothesis enters. -/
theorem sameFinitePointedSource_of_threeTail_finiteAuxEmbeddings
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat) (i : Nat)
    (f g : Nat → Nat)
    (hf : FiniteAuxEmbedding H G.graph f (i+3))
    (hg : FiniteAuxEmbedding H G.graph g (i+3))
    (hfixf : ∀ t, t < i → f t = t)
    (hfixg : ∀ t, t < i → g t = t) :
    SameFinitePointedSource G i
      (f (i+1)) (f (i+2)) (g (i+1)) (g (i+2)) := by
  classical
  let A : EnumNode (i+3) := H.initialSegment (i+3)
  let S : ProtectedSource i := threeVertexSource i A
  have hp : S.penultimateIndex.val = i+1 := by
    dsimp [S, threeVertexSource, ProtectedSource.penultimateIndex]
    split_ifs <;> omega
  have hl : S.lastIndex.val = i+2 := by
    rfl
  have hf' :
      FiniteAuxEmbedding S.picture.toOrdered3Graph G.graph
        f (S.k+1) := by
    exact hf.of_initialSegment
  have hg' :
      FiniteAuxEmbedding S.picture.toOrdered3Graph G.graph
        g (S.k+1) := by
    exact hg.of_initialSegment
  let e₀ : S.Code G :=
    FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding f hf'
  let e₁ : S.Code G :=
    FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding g hg'
  refine ⟨{
    source := S
    source_small := ?_
    first := e₀
    second := e₁
    first_fixes_prefix := ?_
    second_fixes_prefix := ?_
    first_left := ?_
    first_right := ?_
    second_left := ?_
    second_right := ?_
  }⟩
  · exact threeVertexSource_mem i A
  · intro t ht
    change f t.val = t.val
    exact hfixf t.val ht
  · intro t ht
    change g t.val = t.val
    exact hfixg t.val ht
  · change f S.penultimateIndex.val = f (i+1)
    rw [hp]
  · change f S.lastIndex.val = f (i+2)
    rw [hl]
  · change g S.penultimateIndex.val = g (i+1)
    rw [hp]
  · change g S.lastIndex.val = g (i+2)
    rw [hl]

end ATRFiniteDecoder
end ThreeUniformDiaries
