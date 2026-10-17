import ThreeUniformDiaries.DiarySourceSiblingRank
import ThreeUniformDiaries.DiaryOnePassTwoSelectedLex

/-!
# Two selected singleton siblings: rank order gives source-target Lex

The already verified concrete target theorem compares two actual
singleton event positions i<j. This lemma connects that *target*
orientation with the genuine *source* LexEarlier relation, provided
their realised source ranks are ordered in the same direction as the
finite scheduler. The separate scheduler/rank theorem will discharge
this numerical premise globally; it is NOT postulated as V3.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- For two REALISED selected same-parent siblings at events i<j,
the schedule's strict source rank inequality implies preservation
of the literal LexEarlier relation in both orientations. -/
theorem onePass_twoSelected_preserves_sourceLex_of_rank
    (P : RolePrediary H) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hgeti : onePassEventAt H m i = BlockEvent.singleton m g)
    (hgetj : onePassEventAt H m j = BlockEvent.singleton m h)
    (hij : i.val < j.val)
    (hparent : g.1 = h.1)
    (hRank : oneGermBinaryRank m h < oneGermBinaryRank m g)
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
  have hParent : oneCode H m v = oneCode H m u := calc
    oneCode H m v = h.1 := congrArg Prod.fst hvh
    _ = g.1 := hparent.symm
    _ = oneCode H m u := (congrArg Prod.fst hug).symm
  have hneq : h ≠ g := by
    intro heq
    rw [heq] at hRank
    omega
  have hSourceNe : oneGermCode H m v ≠
      oneGermCode H m u := by
    rw [hvh,hug]
    exact hneq
  have hSourceVU : LexEarlier H v u :=
    (onePass_source_siblingGermRank_lt_iff_lex
      H m v u hmv hmu hParent hSourceNe).mp
      (by simpa only [hvh,hug] using hRank)
  have hUVne : u ≠ v := by
    intro heq
    subst v
    exact hSourceNe rfl
  have hNotSourceUV : ¬ LexEarlier H u v :=
    (lexEarlier_swap_complement H v u (Ne.symm hUVne)).mp hSourceVU
  have hTarget :=
    onePass_twoSelected_lex_orientation P m i j
      g h hgeti hgetj hij hparent u v
      hu hv hmu hmv hug hvh
  exact ⟨iff_of_false hTarget.2.1 hNotSourceUV,
    iff_of_true hTarget.2.2 hSourceVU⟩

end DiaryLeafPriority
end ThreeUniformDiaries
