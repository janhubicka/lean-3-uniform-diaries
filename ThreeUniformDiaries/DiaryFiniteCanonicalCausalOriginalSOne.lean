import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOriginalOneMeet
import ThreeUniformDiaries.DiaryFiniteBlockProtectedS2

/-!
# Protected S1 for every original source-flip leaf pair

The complete finite V/E pre-diary has been verified, but that does
not by itself make its full leaf geometry satisfy S1 or S2.
This module establishes the restricted S1 statement actually
needed to protect an original source-flip copy.

Every two distinct genuine source leaves have a source singleton
meet at an actual one-split, by the finite source diary S1 axiom.
The exact original singleton-meet transport theorem shows that
in the final Nat-ranked causal sign-rooted graph their meet is
the rank of that same one-split. The source-role/target-role
reflection then makes that numerical rank a genuine target
one-split.

No global S1 across different branches is assumed. In particular
this cannot justify calling the finite causal pre-diary a full
finite RoleDiaryBlock.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The singleton meet of any TWO DISTINCT source leaves,
in any canonical source-flip branch, has the genuine 1-split
role in the ACTUAL completed causal sign-rooted graph. -/
theorem finiteCanonicalCausalMarkerGraph_original_distinctLeaf_S1
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (u v : Nat)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (hNe : u ≠ v) :
    IsOneSplit (finiteCanonicalCausalMarkerGraph DA)
      ((finiteCanonicalCausalMarkerGraph DA).oneMeetLevel
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i u hun)).val
        (finiteCanonicalNodeIndex DA
          (finiteCanonicalNodeAt DA i v hvn)).val) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  have huF : IsLeaf (F.graph i) u :=
    ((F.flip i).role_iff u hu.1 hun).1.mp hu
  have hvF : IsLeaf (F.graph i) v :=
    ((F.flip i).role_iff v hv.1 hvn).1.mp hv
  let s := (F.graph i).oneMeetLevel u v
  have hsF : IsOneSplit (F.graph i) s :=
    finiteRoleDiary_s1_unordered
      (F.flip i).target_diary
      u v hun hvn huF hvF hNe
  have hsn : s < n :=
    (F.flip i).target_diary.prediary.oneSplit_lt s hsF
  have hsA : IsOneSplit A s :=
    ((F.flip i).role_iff s hsF.1 hsn).2.1.mpr hsF
  have hBound : s ≤ min u v :=
    (F.graph i).oneMeetLevel_le_min u v
  have hSU : s < u := by
    have hNot : s ≠ u := by
      intro h
      have hBad : IsOneSplit (F.graph i) u := by
        simpa only [h] using hsF
      exact huF.2.1 hBad.2.1
    omega
  have hSV : s < v := by
    have hNot : s ≠ v := by
      intro h
      have hBad : IsOneSplit (F.graph i) v := by
        simpa only [h] using hsF
      exact hvF.2.1 hBad.2.1
    omega
  have hMeet : G.oneMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val :=
    finiteCanonicalCausalMarkerGraph_original_proper_oneMeet_exact
      DA i s u v hsA hsn hSU hSV hun hvn hu hv rfl
  have hTargetSplit : IsOneSplit G
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val :=
    (finiteCanonicalCausalMarkerGraph_branch_roles_iff_source
      DA i s hsA.1 hsn).2.1.mpr hsA
  rw [hMeet]
  exact hTargetSplit

end DiaryLeafPriority
end ThreeUniformDiaries
