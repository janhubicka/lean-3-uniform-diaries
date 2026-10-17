import ThreeUniformDiaries.DiaryOnePassFreshLexOrientation
import ThreeUniformDiaries.DiaryOnePassOldSplitWitnessTransport
import ThreeUniformDiaries.DiaryPrediaryRoleNextCut

/-!
# Preservation of source lex orientation at an ORIGINAL singleton split

For two actual source leaves whose proper first singleton meet is
an existing source 1-split m, the source V/E successor-cut identity
forces the bits E(0,m,u) and E(0,m,v) to be different.
The one-pass map copies these two source edges exactly and preserves
the old 1-split meet numerically. Hence the actual source and target
mixed pair meets are zero and the paper's literal LexEarlier relation
reads the SAME right incidence bit before and after the embedding.

This checks the original-1-split V3 case with no S1/S2 and without
assuming the target is already a diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- The original 1-split case of genuine source-to-target LexEarlier
preservation for two source leaves whose singleton meet is exactly m.
The statement is valid in either enumeration order of u,v. -/
theorem onePass_oldOneSplit_preserves_sourceLex
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m < u) (hmv : m < v)
    (hMeet : H.oneMeetLevel u v = m) :
    LexEarlier (onePassRawTarget H)
      (onePassOldImage H u) (onePassOldImage H v) ↔
        LexEarlier H u v := by
  classical
  let G := onePassRawTarget H
  let e := onePassOldImage H m
  let a := onePassOldImage H u
  let b := onePassOldImage H v
  have hSourceBefore : H.SameOneTypeBelow m u v := by
    rw [← hMeet]
    exact H.oneMeetLevel_agree u v
  have hSourceNotNext : ¬ H.SameOneTypeBelow (m + 1) u v := by
    intro hNext
    have hBound : m + 1 ≤ min u v := by omega
    have hTooFar : m + 1 ≤ H.oneMeetLevel u v :=
      Nat.le_findGreatest hBound hNext
    rw [hMeet] at hTooFar
    omega
  have hSourceDifferent :
      ¬ (H.edge 0 m u ↔ H.edge 0 m v) := by
    intro hSame
    exact hSourceNotNext
      ((P.oneSplit_sameOneType_succ_iff m u v hm).mpr
        ⟨hSourceBefore, hSame⟩)
  have hSourceLex : LexEarlier H u v ↔ H.edge 0 m v :=
    lexEarlier_iff_zero_middle_right_of_bit_disagreement
      H m u v hmu hmv hMeet hSourceDifferent
  have hTargetMeet : G.oneMeetLevel a b = e :=
    onePass_oldOneSplit_meet_exact
      P m u v hm hu hv hmu hmv hMeet
  have huAfter : e < a := (onePassOldImage_strictMono H) hmu
  have hvAfter : e < b := (onePassOldImage_strictMono H) hmv
  have hCopyU : G.edge 0 e a ↔ H.edge 0 m u := by
    simpa only [onePassOldImage_zero] using
      (onePassRawTarget_edge_image_iff H 0 m u)
  have hCopyV : G.edge 0 e b ↔ H.edge 0 m v := by
    simpa only [onePassOldImage_zero] using
      (onePassRawTarget_edge_image_iff H 0 m v)
  have hTargetDifferent :
      ¬ (G.edge 0 e a ↔ G.edge 0 e b) := by
    intro hSame
    exact hSourceDifferent
      (hCopyU.symm.trans (hSame.trans hCopyV))
  have hTargetLex : LexEarlier G a b ↔ G.edge 0 e b :=
    lexEarlier_iff_zero_middle_right_of_bit_disagreement
      G e a b huAfter hvAfter hTargetMeet hTargetDifferent
  exact hTargetLex.trans (hCopyV.trans hSourceLex.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
