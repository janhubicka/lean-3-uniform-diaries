import ThreeUniformDiaries.DiaryUpperBoundCertifyGenuineMarkedATR
import ThreeUniformDiaries.DiaryUpperBoundFiniteFrameZeroExtension

/-!
# Track A: package an actual finite diary ATR code as a marked Ramsey source

The concrete leaf-meet support construction in a countable diary
gives a *finite* auxiliary-type-respecting code for an ordered
graph H with a bounded finite full-diary frame, and a marking of
all of its leaves. The already verified finite Ramsey theorem
expects a `MarkedFiniteSource 0 a` with a `ProtectedSource 0`
of size k+1.

The conversion between a general positive finite size m and its
successor presentation k+1 is elementary, but must not silently
identify an arbitrary infinite-tail graph with its EnumNode.
The frame/EnumNode identity from PR #1009 supplies exactly
that equality. The genuine marked-shape certificate from #1026
then supplies precise membership in the cutoff-free finite
diary-type family, without postulating source-copy inducedness.

The conclusion preserves every actual finite code image and every
prescribed mark. It does NOT rely on countable diary unavoidability,
a missing global diary-existence theorem, or the final big-Ramsey
degree statement.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A complete full finite diary source with an ACTUAL finite ATR
code in generic G and a correctly labelled, exhaustive marking of
its leaves is represented by an element of the canonical finite
genuine marked-diary family.

The original finite size m need not be presented in advance as
k+1. At m=0 the full finite-diary frame is impossible; otherwise
we expose its successor predecessor to fit the finite ATR API.
No imaginary tail image is used in the colour. -/
theorem exists_genuineMarkedSource_of_actualFiniteDiaryCode
    (G : GenericEnumerated3Graph)
    {a : Nat} (A : EnumNode a)
    (H : Ordered3Graph Nat) (m : Nat)
    (D : FiniteRoleDiaryBlock H m)
    (e : FiniteAuxEmbeddingImage
      (H.initialSegment m).toOrdered3Graph G.graph m)
    (marked : Fin a → Fin m)
    (hLeaf : ∀ i : Fin a, IsLeaf H (marked i).val)
    (hCover : ∀ u : Nat, 3 ≤ u → u < m →
      IsLeaf H u → ∃ i : Fin a, (marked i).val = u)
    (hCopy : IsFiniteLabelledCopy A.toOrdered3Graph G.graph a
      (fun i => e.image (marked i))) :
    ∃ S : MarkedFiniteSource 0 a,
      S ∈ allGenuineMarkedDiaryShapes A ∧
      ∃ c : S.source.Code G,
        ∀ i : Fin a, c.image (S.marked i) =
          e.image (marked i) := by
  cases m with
  | zero =>
      have h3 : 3 ≤ 0 := D.prediary.frame.length_ge_three
      omega
  | succ k =>
      let S : MarkedFiniteSource 0 a := {
        source := {
          k := k
          picture := H.initialSegment (k + 1)
          cut_le := by omega
        }
        marked := marked
      }
      let c : S.source.Code G := e
      have hFrameEq :
          (H.initialSegment (k + 1)).toOrdered3Graph = H :=
        D.zeroExtended_source_eq
      have hDiaryS :
          FiniteRoleDiaryBlock S.source.picture.toOrdered3Graph
            (S.source.k + 1) := by
        change FiniteRoleDiaryBlock
          (H.initialSegment (k + 1)).toOrdered3Graph (k + 1)
        rw [hFrameEq]
        exact D
      have hLeafS :
          ∀ i : Fin a,
            IsLeaf S.source.picture.toOrdered3Graph (S.marked i).val := by
        intro i
        change IsLeaf (H.initialSegment (k + 1)).toOrdered3Graph
          (marked i).val
        rw [hFrameEq]
        exact hLeaf i
      have hCoverS :
          ∀ u : Nat, 3 ≤ u → u < S.source.k + 1 →
            IsLeaf S.source.picture.toOrdered3Graph u →
            ∃ i : Fin a, (S.marked i).val = u := by
        intro u hu3 hum huLeaf
        apply hCover u hu3 hum
        rw [← hFrameEq]
        exact huLeaf
      have hCopyS : IsFiniteLabelledCopy
          A.toOrdered3Graph G.graph a
          (fun i => c.image (S.marked i)) := hCopy
      have hMem : S ∈ allGenuineMarkedDiaryShapes A :=
        actualATRCode_mem_allGenuineMarkedDiaryShapes
          G A S c hDiaryS hLeafS hCoverS hCopyS
      refine ⟨S, hMem, c, ?_⟩
      intro i
      rfl

end ATRFiniteDecoder
end ThreeUniformDiaries
