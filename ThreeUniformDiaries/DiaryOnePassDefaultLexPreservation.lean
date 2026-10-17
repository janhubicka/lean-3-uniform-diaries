import ThreeUniformDiaries.DiaryOnePassDefaultRankMin
import ThreeUniformDiaries.DiarySourceSiblingRank
import ThreeUniformDiaries.DiaryOnePassFreshLexOrientation

/-!
# Exact source-to-target Lex orientation for selected/default siblings

The minimum-rank actual default (#621), the strict source sibling
rank/lex equivalence (#622), and the exact target fresh selected/
default orientation (#609) now agree. This is a true source-to-target
V3 preservation result for this concrete sibling case, not just a
proof of target orientation.

All hypotheses concern actual realised source leaf germs and their
real default sibling; no source S1/S2 or target V3 assumption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- A realised singleton selected germ must be strictly GREATER
in rank than its distinct realised default sibling. -/
theorem onePass_selected_default_rank_strict
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hParent : oneCode H m u = oneCode H m v)
    (hDef : oneDefaultGerm H m (oneCode H m u) =
      some (oneGermCode H m v))
    (hneq : oneGermCode H m u ≠ oneGermCode H m v)
    (hu : IsLeaf H u) :
    oneGermBinaryRank m (oneGermCode H m v) <
      oneGermBinaryRank m (oneGermCode H m u) := by
  classical
  have hg : oneGermCode H m u ∈
      oneGermFibre H m (oneCode H m u) := by
    simp only [oneGermFibre, Finset.mem_filter]
    exact ⟨by
      simp only [realisedOneGerms, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u,hu,hmu,rfl⟩, rfl⟩
  have hle := oneDefaultGerm_minimal_on_realised_fibre
    H m (oneCode H m u)
      (oneGermCode H m v) (oneGermCode H m u) hDef hg
  have hUVneq : u ≠ v := by
    intro heq
    subst v
    exact hneq rfl
  have hRankReverse :
      (oneGermBinaryRank m (oneGermCode H m u) <
         oneGermBinaryRank m (oneGermCode H m v)) ↔
          LexEarlier H u v :=
    onePass_source_siblingGermRank_lt_iff_lex
      H m u v hmu hmv hParent hneq
  have hRankForward :
      (oneGermBinaryRank m (oneGermCode H m v) <
         oneGermBinaryRank m (oneGermCode H m u)) ↔
          LexEarlier H v u :=
    onePass_source_siblingGermRank_lt_iff_lex
      H m v u hmv hmu hParent.symm (Ne.symm hneq)
  have hNotLexUV : ¬ LexEarlier H u v := by
    intro hlex
    have hbad := hRankReverse.mpr hlex
    omega
  have hLexVU : LexEarlier H v u :=
    (lexEarlier_swap_complement H v u (Ne.symm hUVneq)).mpr hNotLexUV
  exact hRankForward.mpr hLexVU

/-- For actual selected and default sibling leaves, the source
and target LexEarlier comparisons coincide (in BOTH directions).
The source comparison here follows from rank MINIMALITY rather
than from a hypothetical target V3 marker. -/
theorem onePass_fresh_selected_default_preserves_sourceLex
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g)
    (hdef : oneDefaultGerm H m g.1 = some h)
    (hparent : h.1 = g.1)
    (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hug : oneGermCode H m u = g)
    (hvh : oneGermCode H m v = h)
    (hneq : h ≠ g) :
    (LexEarlier (onePassRawTarget H)
      (onePassOldImage H u) (onePassOldImage H v) ↔
        LexEarlier H u v) ∧
    (LexEarlier (onePassRawTarget H)
      (onePassOldImage H v) (onePassOldImage H u) ↔
        LexEarlier H v u) := by
  have hParent : oneCode H m u = oneCode H m v := calc
    oneCode H m u = g.1 := congrArg Prod.fst hug
    _ = h.1 := hparent.symm
    _ = oneCode H m v := (congrArg Prod.fst hvh).symm
  have hDefSource :
      oneDefaultGerm H m (oneCode H m u) =
        some (oneGermCode H m v) := by
    rw [congrArg Prod.fst hug, hvh]
    exact hdef
  have hNeSource :
      oneGermCode H m u ≠ oneGermCode H m v := by
    rw [hug,hvh]
    exact Ne.symm hneq
  have hStrict := onePass_selected_default_rank_strict
    H m u v hmu hmv hParent hDefSource hNeSource hu
  have hLexSourceVU : LexEarlier H v u :=
    (onePass_source_siblingGermRank_lt_iff_lex
      H m v u hmv hmu hParent.symm (Ne.symm hNeSource)).mp hStrict
  have hUVneq : u ≠ v := by
    intro heq
    subst v
    exact hNeSource rfl
  have hNotSourceUV : ¬ LexEarlier H u v :=
    (lexEarlier_swap_complement H v u (Ne.symm hUVneq)).mp hLexSourceVU
  obtain ⟨hNotTargetUV,hTargetVU⟩ :=
    onePass_freshOne_selected_default_lex_orientation
      P m i g h hget hdef hparent u v
      hu hv hmu hmv hug hvh hneq
  exact ⟨iff_of_false hNotTargetUV hNotSourceUV,
    iff_of_true hTargetVU hLexSourceVU⟩

end DiaryLeafPriority
end ThreeUniformDiaries
