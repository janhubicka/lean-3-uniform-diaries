import ThreeUniformDiaries.DiaryCappedPreembedding

/-!
# Exhaustive leaf-pair full two-type meets: one marker-1 obligation

The complete source diary axiom S2 classifies every full 2-type
meet of increasing pairs of leaves into three cases:
(1) the cap at the lesser first leaf,
(2) marker 1, and
(3) a genuine 2-split.

The actual witness-chosen target map already preserves (1) and
(3), by verified capped-target and I3 two-split witnesses. This
module proves the complete pair-meet equation under ONE explicit
hypothesis for precisely (2), without assuming a general type-
respecting target embedding or meet preservation through gaps.

The still-unproved mathematical content is exactly the global
marker-1 orientation synchronisation. A separate role-based
reduction relates it to equality of LexEarlier orientation bits.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

variable {H : Ordered3Graph Nat}

/-- All leaf-pair 2-type meets are preserved by the actual
candidate pre-embedding once the marker-1 case alone is
supplied. All other cases follow unconditionally from the
complete source diary V/E/S axioms and genuine gappy I2/I3
stabilisation. -/
theorem chosenPreembedding_preserves_all_leaf_twoMeets_of_markerOne
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (hmarker :
      ∀ a b c d : Nat,
        a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        H.twoMeetLevel a b c d = 1 →
        K.twoMeetLevel
          (stabilisedSource G K F ψ a)
          (stabilisedSource G K F ψ b)
          (stabilisedSource G K F ψ c)
          (stabilisedSource G K F ψ d) = 1)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) :
    let φ := stabilisedSource G K F ψ
    K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) =
      D.chosenPreembedding G K F ψ
        (H.twoMeetLevel a b c d) := by
  let φ := stabilisedSource G K F ψ
  rcases D.pair_meets a b c d hab hcd ha hb hc hd with
    hcap | hone | htwo
  · rw [hcap]
    exact D.chosenPreembedding_preserves_capped_pair_meet
      G K F ψ hψ a b c d hab hcd ha hb hc hd hcap
  · have htarget : K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) = 1 :=
      hmarker a b c d hab hcd ha hb hc hd hone
    simpa only [hone, D.chosenPreembedding_one G K F ψ] using htarget
  · let m := H.twoMeetLevel a b c d
    have hCap : m ≤ min a c := H.twoMeetLevel_le_min a b c d
    have hNotA : m ≠ a := by
      intro he
      have hs : IsTwoSplit H a :=
        he ▸ (htwo : IsTwoSplit H m)
      exact ha.2.2 hs.2.2
    have hNotC : m ≠ c := by
      intro he
      have hs : IsTwoSplit H c :=
        he ▸ (htwo : IsTwoSplit H m)
      exact hc.2.2 hs.2.2
    have hma : m < a := by omega
    have hmc : m < c := by omega
    have hChoice : D.twoSplitTargetImage G K F ψ m htwo =
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) :=
      D.twoSplitTargetImage_eq_any_witness
        G K F ψ hψ m a b c d htwo
        hma hmc hab hcd ha hb hc hd rfl
    calc
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) =
        D.twoSplitTargetImage G K F ψ m htwo :=
          hChoice.symm
      _ = D.chosenPreembedding G K F ψ m :=
          (D.chosenPreembedding_twoSplit G K F ψ m htwo).symm

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
