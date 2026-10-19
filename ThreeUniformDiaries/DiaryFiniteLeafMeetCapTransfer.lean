import ThreeUniformDiaries.DiaryFiniteLeafMeetPrefixCompression

/-!
# Exact preservation of capped full pair meets under finite compression

For ordered pairs (a,b),(c,d), the full meet is capped at the
smaller FIRST coordinate, min(a,c). An increasing finite support
enumeration preserves the relative order of those first vertices
and hence preserves the cap.

The safe one-directional full-type transport theorem says that
agreement through the old capped meet survives every deletion of
other earlier test vertices. Because the new full two-meet cannot
exceed the corresponding new first-coordinate cap, the two
bounds coincide. No retained distinguishing edge is needed.

This completely handles the capped S2 alternative in proposed
finite leaf-meet extraction and works for ANY ordered ternary
source graph; it does not require V/E/S diary hypotheses.
The proper marker-one and genuine two-split meet cases require
separate explicit retained witness edges.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {S : Finset Nat}

/-- If an old ordered-pair meet equals the old image of the
smaller first source index, its exact compressed full two-meet
equals that same smaller first index. -/
theorem finiteSupportGraph_capped_twoMeet_exact
    (a b c d : Nat)
    (ha : a < S.card) (hb : b < S.card)
    (hc : c < S.card) (hd : d < S.card)
    (hab : a < b) (hcd : c < d)
    (hSourceCap :
      G.twoMeetLevel
        (finiteSupportIndex S a) (finiteSupportIndex S b)
        (finiteSupportIndex S c) (finiteSupportIndex S d) =
          finiteSupportIndex S (min a c)) :
    (finiteSupportGraph G S).twoMeetLevel a b c d = min a c := by
  classical
  let H := finiteSupportGraph G S
  let k := min a c
  have hk : k < S.card := by
    dsimp [k]
    omega
  have hka : k ≤ a := min_le_left _ _
  have hkc : k ≤ c := min_le_right _ _
  have hSourceAt : G.SameTwoTypeBelow
      (finiteSupportIndex S k)
      (finiteSupportIndex S a) (finiteSupportIndex S b)
      (finiteSupportIndex S c) (finiteSupportIndex S d) := by
    rw [← hSourceCap]
    exact G.twoMeetLevel_agree
      (finiteSupportIndex S a) (finiteSupportIndex S b)
      (finiteSupportIndex S c) (finiteSupportIndex S d)
  have hTargetAt : H.SameTwoTypeBelow k a b c d :=
    finiteSupportGraph_twoType_of_original
      (G := G) (S := S) k a b c d
      hk ha hb hc hd hab hcd hka hkc hSourceAt
  have hLower : k ≤ H.twoMeetLevel a b c d :=
    Nat.le_findGreatest (by simpa only [k]) hTargetAt
  have hUpper : H.twoMeetLevel a b c d ≤ k := by
    simpa only [k] using H.twoMeetLevel_le_min a b c d
  change H.twoMeetLevel a b c d = k
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
