import ThreeUniformDiaries.DiaryOnePassIndexedRankOrder
import ThreeUniformDiaries.DiaryOnePassRealSiblingRankDistinct
import ThreeUniformDiaries.DiaryOnePassTwoSelectedLexPreservation

/-!
# Source-to-target lex preservation for TWO actual selected siblings

The actual indexed event scheduler gives weakly descending ranks
for every selected singleton event pair i<j (#627). Actual source
sibling germ codes of the same old parent have strictly distinct
binary ranks (#626). The weak inequality therefore becomes STRICT
for two different selected sibling events with realised source
leaf representatives.

Feed this derived strict rank inequality to the already verified
source-target LexEarlier comparison (#625). No scheduling/rank
assumption remains in the exported sibling theorem. Source S1/S2,
target V3, synthetic rank injectivity and a completed diary are
not assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Earlier of two TRUE selected singleton events with equal
source parent has STRICTLY greater rank on actual source leaves. -/
theorem onePass_twoSelected_siblings_rank_gt_of_index
    (H : Ordered3Graph Nat) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hgeti : onePassEventAt H m i = BlockEvent.singleton m g)
    (hgetj : onePassEventAt H m j = BlockEvent.singleton m h)
    (hij : i.val < j.val)
    (hparent : g.1 = h.1)
    (u v : Nat)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hug : oneGermCode H m u = g)
    (hvh : oneGermCode H m v = h) :
    oneGermBinaryRank m h < oneGermBinaryRank m g := by
  have hRankWeak :=
    onePass_singleton_events_rank_ge_of_index_lt
      H m i j g h hgeti hgetj hij
  have hneq : g ≠ h := by
    intro hEq
    have hEvents : onePassEventAt H m i = onePassEventAt H m j := by
      rw [hgeti, hgetj, hEq]
    have hEqIndices := (onePassEventAt_injective H m) hEvents
    have hVal := congrArg Fin.val hEqIndices
    omega
  have hSourceParent : oneCode H m u = oneCode H m v := calc
    oneCode H m u = g.1 := congrArg Prod.fst hug
    _ = h.1 := hparent
    _ = oneCode H m v := (congrArg Prod.fst hvh).symm
  have hSourceNe : oneGermCode H m u ≠
      oneGermCode H m v := by
    rw [hug, hvh]
    exact hneq
  have hSourceRank :
      oneGermBinaryRank m (oneGermCode H m v) <
        oneGermBinaryRank m (oneGermCode H m u) :=
    onePass_realSiblingGerm_rank_lt_of_le
      H m u v hmu hmv hSourceParent hSourceNe
        (by simpa only [hug, hvh] using hRankWeak)
  simpa only [hug,hvh] using hSourceRank

/-- The actual one-pass embedding preserves genuine LexEarlier
for two selected source singleton child germs, with their true
event index order i<j. The rank hypothesis of #625 is ELIMINATED. -/
theorem onePass_twoSelected_preserves_sourceLex
    (P : RolePrediary H) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hgeti : onePassEventAt H m i = BlockEvent.singleton m g)
    (hgetj : onePassEventAt H m j = BlockEvent.singleton m h)
    (hij : i.val < j.val)
    (hparent : g.1 = h.1)
    (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hug : oneGermCode H m u = g)
    (hvh : oneGermCode H m v = h) :
    (LexEarlier (onePassRawTarget H)
       (onePassOldImage H u) (onePassOldImage H v) ↔
         LexEarlier H u v) ∧
    (LexEarlier (onePassRawTarget H)
       (onePassOldImage H v) (onePassOldImage H u) ↔
         LexEarlier H v u) := by
  exact onePass_twoSelected_preserves_sourceLex_of_rank
    P m i j g h hgeti hgetj hij hparent
      (onePass_twoSelected_siblings_rank_gt_of_index
        H m i j g h hgeti hgetj hij hparent
        u v hmu hmv hug hvh)
    u v hu hv hmu hmv hug hvh

end DiaryLeafPriority
end ThreeUniformDiaries
