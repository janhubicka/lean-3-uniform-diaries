import ThreeUniformDiaries.DiaryUnconditionalPreembedding
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Track D: E1 and E4 incidences are not independent successor constraints

A checked full diary pre-embedding fixes the three marker vertices,
preserves actual leaf/one-split/two-split roles, is increasing, and
preserves exact selected-leaf singleton and pair meets. It already
preserves every triple consisting of THREE genuine leaves (E5).

The raw E1 marker-to-role tests (0,1,z), (0,2,z) are also automatic
from preservation of actual roles.

More subtly, a source one-split s = oneMeet(a,b) is a genuine strict
predecessor of both distinct genuine leaves a<b. The manuscript's
lexicographic comparison of a,b is *exactly* the right E2 bit
edge(0,s,b). Since the pre-embedding preserves this singleton meet,
preserving those E2 one-split/right-leaf bits forces both E4 bits
edge(1,a,b), edge(2,a,b) to agree automatically.

This is a useful mathematically exact reduction of mixed-incidence
work: among the five permitted diary edge shapes, E1, E4, E5
require no independent checks once E2 is preserved. E3 two-split
edges remain a separate genuine obstacle, as does finding actual
relative extensions and meeting the S1/S2/order reserve tests.

No countable diary unavoidability theorem is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An arbitrary full diary pre-embedding already preserves both
raw marker edges recording the leaf/one-split/two-split role. This
needs only actual source role coverage and forward role preservation
from the pre-embedding, not inducedness of arbitrary mixed triples. -/
theorem DiaryPreembeddingSpec.marker_role_edge_bits
    {H K : Ordered3Graph Nat} {f : Nat → Nat}
    (DH : RoleDiary H) (P : DiaryPreembeddingSpec H K f)
    (z : Nat) (hz : 3 ≤ z) :
    (H.edge 0 1 z ↔ K.edge 0 1 (f z)) ∧
    (H.edge 0 2 z ↔ K.edge 0 2 (f z)) := by
  rcases DH.role_valid z hz with hLeaf | hOne | hTwo
  · have hTarget := P.leaf_role z hLeaf
    exact ⟨iff_of_false hLeaf.2.1 hTarget.2.1,
      iff_of_false hLeaf.2.2 hTarget.2.2⟩
  · have hTarget := P.one_split_role z hOne
    exact ⟨iff_of_true hOne.2.1 hTarget.2.1,
      iff_of_false hOne.2.2 hTarget.2.2⟩
  · have hTarget := P.two_split_role z hTwo
    exact ⟨iff_of_false hTwo.2.1 hTarget.2.1,
      iff_of_true hTwo.2.2 hTarget.2.2⟩

/-- The E4 pair-marker incidences are forced by E2 one-split
incidence agreement, given the already verified literal S1
singleton-meet preservation. There is no additional E4 choice
or extra orientation hypothesis in this implication. -/
theorem DiaryPreembeddingSpec.leaf_pair_marker_bits_of_oneSplit_bits
    {H K : Ordered3Graph Nat} {f : Nat → Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : DiaryPreembeddingSpec H K f)
    (hE2 : ∀ (s b : Nat), IsOneSplit H s →
      IsLeaf H b → s < b →
      (H.edge 0 s b ↔ K.edge 0 (f s) (f b)))
    (a b : Nat) (hab : a < b)
    (ha : IsLeaf H a) (hb : IsLeaf H b) :
    (H.edge 1 a b ↔ K.edge 1 (f a) (f b)) ∧
    (H.edge 2 a b ↔ K.edge 2 (f a) (f b)) := by
  let s := H.oneMeetLevel a b
  have hs : IsOneSplit H s :=
    DH.singleton_meets a b ha hb (ne_of_lt hab)
  have hs_le_a : s ≤ a := by
    dsimp [s]
    exact (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
  have hs_ne_a : s ≠ a := by
    intro hsa
    have hOneA : IsOneSplit H a := by
      simpa only [hsa] using hs
    exact ha.2.1 hOneA.2.1
  have hsa : s < a := by omega
  have hsb : s < b := by omega
  have hTa : IsLeaf K (f a) := P.leaf_role a ha
  have hTb : IsLeaf K (f b) := P.leaf_role b hb
  have hTs : IsOneSplit K (f s) := P.one_split_role s hs
  have hMeetK : K.oneMeetLevel (f a) (f b) = f s :=
    P.leaf_one_meet a b ha hb
  have hSourceLex : LexEarlier H a b ↔ H.edge 0 s b := by
    exact DH.lexEarlier_iff_right_split_marker
      s a b hs ha hb hab hsa rfl
  have hTargetLex :
      LexEarlier K (f a) (f b) ↔ K.edge 0 (f s) (f b) := by
    exact DK.lexEarlier_iff_right_split_marker
      (f s) (f a) (f b) hTs hTa hTb
      (P.strictMono hab) (P.strictMono hsa) hMeetK
  have hLex :
      LexEarlier H a b ↔ LexEarlier K (f a) (f b) :=
    hSourceLex.trans ((hE2 s b hs hb hsb).trans hTargetLex.symm)
  constructor
  · exact (DH.leaf_marker_one a b hab ha hb).trans
      (hLex.trans
        (DK.leaf_marker_one (f a) (f b)
          (P.strictMono hab) hTa hTb).symm)
  · exact (DH.leaf_marker_two a b hab ha hb).trans
      ((not_congr hLex).trans
        (DK.leaf_marker_two (f a) (f b)
          (P.strictMono hab) hTa hTb).symm)

end DiaryLeafPriority
end ThreeUniformDiaries
