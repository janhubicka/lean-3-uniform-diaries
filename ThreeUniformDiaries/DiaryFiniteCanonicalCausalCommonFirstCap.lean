import ThreeUniformDiaries.DiaryFiniteCanonicalRankedSameBranchMaskLeafCut
import ThreeUniformDiaries.DiaryFiniteCanonicalRankedRawVTwo
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVTwoCoherence

/-!
# Exact common-first-leaf full meet in the causal sign-rooted completion

The manuscript's exact S2 alternative includes the CAPPED case:
the ordered source pairs (a,b) and (a,d) have twoMeetLevel exactly a.
The source vertex a is a LEAF, not a 1-/2-split. Consequently the
earlier split-only mask-coherence lemma cannot transport the full
pair type through the numerical cut corresponding to a.

The new verified arbitrary leaf-cut mask coherence fixes this.
Source full type agreement through a transports to the entire ranked
raw union, including off-path nodes tied at source level a.
The first coordinate singleton type agrees tautologically; the
second coordinate b,d uses causal induction and equality of their
genuine marker masks before the actual rank of a. Auxiliary tests
remain unchanged since both ordered pairs are on one source branch.

Thus the completed full pair type agrees through rank(a). Since
both compared pairs have the SAME first target vertex rank(a),
the capped twoMeetLevel cannot exceed rank(a). Equality follows.

This is exact preservation of the common-first capped S2 case for
the designated canonical source branches. It does not assert S2 for
new cross-branch pair combinations or universal flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The common-first capped source two-meet is preserved EXACTLY
in the final causally completed canonical sign-rooted graph.
All numerical predecessor tests, including off-path tied-level
vertices, are covered by source raw type transport and the
arbitrary same-branch marker mask theorem. -/
theorem finiteCanonicalCausalMarkerGraph_original_commonFirst_twoMeet_exact
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (a b d : Nat)
    (hab : a < b) (had : a < d)
    (hbn : b < n) (hdn : d < n)
    (hb : IsLeaf A b) (hd : IsLeaf A d)
    (hSourceMeet :
      ((finiteCanonicalSignRootedFamily DA).graph i).twoMeetLevel
        a b a d = a) :
    (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b hbn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i d hdn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  let G := finiteCanonicalCausalMarkerGraph DA
  have han : a < n := by omega
  let aa := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i a han)).val
  let bb := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i b hbn)).val
  let dd := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i d hdn)).val
  have hSrc : (F.graph i).SameTwoTypeBelow a a b a d := by
    have h := (F.graph i).twoMeetLevel_agree a b a d
    rw [hSourceMeet] at h
    exact h
  have hRawOne : F.RawCrossOneTypeBelow a
      (F.node i b) (F.node i d) :=
    (F.rawSameOneTypeBelow_iff_source i a b d
      hab.le had.le hbn hdn).mpr hSrc.2.1
  have hRawAux : F.RawCrossAuxTypeBelow a
      (F.node i a) (F.node i b)
      (F.node i a) (F.node i d) :=
    (F.rawSameAuxTypeBelow_iff_source
      i a a b a d le_rfl le_rfl hab had hbn hdn).mpr
      hSrc.2.2
  have hRawBD : R.SameOneTypeBelow aa bb dd :=
    finiteCanonicalRankedRaw_crossOneType_at_shared_cut
      DA i i a b d han rfl hab.le had.le hbn hdn hRawOne
  have hRawAuxRank : R.SameAuxTypeBelow aa aa bb aa dd :=
    finiteCanonicalRankedRaw_crossAux_at_shared_cut
      DA i i a a b a d han rfl le_rfl le_rfl
      hab had hbn hdn hRawAux
  have hAB : aa < bb :=
    finiteCanonicalNodeAt_index_lt DA i a b hab hbn
  have hAD : aa < dd :=
    finiteCanonicalNodeAt_index_lt DA i a d had hdn
  have hMaskBD : SameEarlierMarkerMask M aa bb dd :=
    finiteCanonicalRankedOffBranchMask_sameBranch_below
      DA i a b d han hab had hbn hdn hb hd
  have hLater : ∀ x y, M x y → x < y :=
    finiteCanonicalRankedOffBranchMask_later DA
  have hFinalBD : G.SameOneTypeBelow aa bb dd :=
    causalMarker_preserves_parent_oneType R G M aa bb dd
      hAB.le hAD.le hRawBD hMaskBD
      (by
        intro x y hxy hyl
        exact causalMarkerLimit_formula R M hLater x y bb)
      (by
        intro x y hxy hyl
        exact causalMarkerLimit_formula R M hLater x y dd)
  have hFinalAux : G.SameAuxTypeBelow aa aa bb aa dd := by
    intro x hx
    have hI := finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
      DA i a b hab hbn x
    have hJ := finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
      DA i a d had hdn x
    exact hI.trans ((hRawAuxRank hx).trans hJ.symm)
  have hFinalType : G.SameTwoTypeBelow aa aa bb aa dd :=
    ⟨(by intro x y hxy hyl; exact Iff.rfl),hFinalBD,hFinalAux⟩
  have hLower : aa ≤ G.twoMeetLevel aa bb aa dd := by
    apply Nat.le_findGreatest (by omega)
    exact hFinalType
  have hUpper : G.twoMeetLevel aa bb aa dd ≤ aa := by
    have h := G.twoMeetLevel_le_min aa bb aa dd
    simpa only [min_self] using h
  change G.twoMeetLevel aa bb aa dd = aa
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
