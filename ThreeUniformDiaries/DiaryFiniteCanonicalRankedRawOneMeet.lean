import ThreeUniformDiaries.DiaryFiniteCanonicalExactMarkerRanks
import ThreeUniformDiaries.DiaryFiniteSignRootedRawTypePreservation
import ThreeUniformDiaries.DiarySourceLexFirstAuxBit

/-!
# Exact original singleton meets in the Nat-ranked sign-rooted raw graph

A source flip branch is induced in the ranked raw graph, but that
alone does not preserve numerical singleton meets: there are now
many extra earlier off-branch vertices, including vertices tied
at the original source level of a split.

We prove exact type preservation through the RANK of every source
cut s. Earlier raw edge tests split into three cases:

* Strictly increasing source levels below s are covered by the
  verified raw sign-rooted type theorem, including off-path nodes.
* A pair of raw nodes tied at their original source level cannot
  support an edge (raw edges have strictly increasing levels).
* A raw vertex tied with s, but placed before its branch split
  node in the level-first order, lies off the branch. All raw
  edges ending on either compared branch terminal are then zero.

Thus the ranked RAW singleton types agree up to the rank of s
whenever their original singleton types agree below source cut s.

If the source singleton meet of u,v is exactly the proper cut s,
its known first differing edge at source column s survives
inducedly in the ranked raw graph. This proves the exact equality
between the output numerical one-meet and the rank of the source
split, with no assumption that source levels are consecutive in
the enlarged carrier.

These results concern the RAW graph; the causal marker extension
must still be applied using the verified ranked off-branch mask.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Source singleton-type agreement below s lifts to genuine
Nat-rank singleton-type agreement below the rank of the
corresponding original source vertex s, including all inserted
off-branch nodes and all source-level ties. -/
theorem finiteCanonicalRankedRaw_oneType_at_source_cut
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hsn : s < n) (hsu : s ≤ u) (hsv : s ≤ v)
    (hun : u < n) (hvn : v < n)
    (hSource :
      ((finiteCanonicalSignRootedFamily DA).graph i).SameOneTypeBelow
        s u v) :
    (finiteCanonicalRankedRawGraph DA).SameOneTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let S := finiteCanonicalNodeAt DA i s hsn
  let U := finiteCanonicalNodeAt DA i u hun
  let V := finiteCanonicalNodeAt DA i v hvn
  have hRaw : F.RawSameOneTypeBelow s (F.node i u) (F.node i v) :=
    (F.rawSameOneTypeBelow_iff_source i s u v
      hsu hsv hun hvn).mpr hSource
  intro x y hxy hyS
  have hyCard : y < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    lt_trans hyS (finiteCanonicalNodeIndex DA S).isLt
  have hxCard : x < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    lt_trans hxy hyCard
  obtain ⟨X,hXidx⟩ := finiteCanonicalNodeIndex_surjective DA
    (⟨x,hxCard⟩ : Fin (Fintype.card (FiniteCanonicalSignRootedVertex DA)))
  obtain ⟨Y,hYidx⟩ := finiteCanonicalNodeIndex_surjective DA
    (⟨y,hyCard⟩ : Fin (Fintype.card (FiniteCanonicalSignRootedVertex DA)))
  have hXval : (finiteCanonicalNodeIndex DA X).val = x :=
    congrArg Fin.val hXidx
  have hYval : (finiteCanonicalNodeIndex DA Y).val = y :=
    congrArg Fin.val hYidx
  have hXYrank : (finiteCanonicalNodeIndex DA X).val <
      (finiteCanonicalNodeIndex DA Y).val := by omega
  have hYSrank : (finiteCanonicalNodeIndex DA Y).val <
      (finiteCanonicalNodeIndex DA S).val := by omega
  have hBeforeXY : finiteCanonicalNodeBefore DA X Y :=
    (finiteCanonicalNodeBefore_iff_rank_lt DA X Y).mpr hXYrank
  have hBeforeYS : finiteCanonicalNodeBefore DA Y S :=
    (finiteCanonicalNodeBefore_iff_rank_lt DA Y S).mpr hYSrank
  have hXleY : X.val.1 ≤ Y.val.1 := by
    rcases hBeforeXY with hLt | ⟨hTie,_⟩ <;> omega
  have hYleS : Y.val.1 ≤ s := by
    have hSlevel : S.val.1 = s :=
      finiteCanonicalNodeAt_level DA i s hsn
    rcases hBeforeYS with hLt | ⟨hTie,_⟩ <;> omega
  have hRawMatch :
      F.rawAmalgam.edge X.val Y.val U.val ↔
        F.rawAmalgam.edge X.val Y.val V.val := by
    rcases lt_or_eq_of_le hYleS with hYltS | hYeqS
    · rcases lt_or_eq_of_le hXleY with hXltY | hXeqY
      · exact hRaw X.val Y.val hXltY hYltS
      · have hBoth (Z : FiniteSignRootedNode A n) :
            ¬ F.rawAmalgam.edge X.val Y.val Z := by
          intro hEdge
          obtain ⟨j,a,b,c,hab,_hbc,_hcn,hXa,hYb,_hZc,_⟩ := hEdge
          have ha : X.val.1 = a := by
            have hh := congrArg Prod.fst hXa
            simpa only [F.node_level] using hh.symm
          have hb : Y.val.1 = b := by
            have hh := congrArg Prod.fst hYb
            simpa only [F.node_level] using hh.symm
          omega
        exact iff_of_false (hBoth U.val) (hBoth V.val)
    · have hYneq : Y.val ≠ F.node i s := by
        intro h
        have hSub : Y = S := Subtype.ext h
        have hh := congrArg
          (fun T : FiniteCanonicalSignRootedVertex DA =>
            (finiteCanonicalNodeIndex DA T).val) hSub
        omega
      have hOff : Y.val ≠ F.node i Y.val.1 := by
        intro h
        exact hYneq (by simpa only [hYeqS] using h)
      exact iff_of_false
        (F.rawAmalgam_no_offpath_edge_at_terminal
          i X.val Y.val u (Or.inr hOff))
        (F.rawAmalgam_no_offpath_edge_at_terminal
          i X.val Y.val v (Or.inr hOff))
  have hRankU :=
    finiteCanonicalRankedRawGraph_edge_iff DA X Y U
  have hRankV :=
    finiteCanonicalRankedRawGraph_edge_iff DA X Y V
  have hBothRank := hRankU.trans (hRawMatch.trans hRankV.symm)
  simpa only [hXval,hYval] using hBothRank

/-- If the source singleton meet of u,v is a PROPER cut s, its
numerical meet in the ranked raw graph is precisely the rank
of the old source vertex s. The raw inserted nodes create no
earlier type distinctions and preserve the old first disagreement. -/
theorem finiteCanonicalRankedRaw_original_proper_oneMeet_exact
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hsn : s < n) (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hSourceMeet :
      ((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel
        u v = s) :
    (finiteCanonicalRankedRawGraph DA).oneMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let S := finiteCanonicalNodeAt DA i s hsn
  let U := finiteCanonicalNodeAt DA i u hun
  let V := finiteCanonicalNodeAt DA i v hvn
  have hSourceSame : (F.graph i).SameOneTypeBelow s u v := by
    simpa only [hSourceMeet] using (F.graph i).oneMeetLevel_agree u v
  have hRankSame : R.SameOneTypeBelow
      (finiteCanonicalNodeIndex DA S).val
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA V).val :=
    finiteCanonicalRankedRaw_oneType_at_source_cut DA i s u v
      hsn hsu.le hsv.le hun hvn hSourceSame
  have hSU : (finiteCanonicalNodeIndex DA S).val <
      (finiteCanonicalNodeIndex DA U).val :=
    finiteCanonicalNodeAt_index_lt DA i s u hsu hun
  have hSV : (finiteCanonicalNodeIndex DA S).val <
      (finiteCanonicalNodeIndex DA V).val :=
    finiteCanonicalNodeAt_index_lt DA i s v hsv hvn
  have hLow : (finiteCanonicalNodeIndex DA S).val ≤
      R.oneMeetLevel
        (finiteCanonicalNodeIndex DA U).val
        (finiteCanonicalNodeIndex DA V).val := by
    apply Nat.le_findGreatest (by omega)
    exact hRankSame
  let q := (F.graph i).auxMeetLevel s u s v
  have hDiff :=
    onePass_source_mixedAux_first_difference
      (F.graph i) s u v hsu hsv hSourceMeet
  have hqs : q < s := hDiff.1
  have hqn : q < n := by omega
  let Q := finiteCanonicalNodeAt DA i q hqn
  have hQS : (finiteCanonicalNodeIndex DA Q).val <
      (finiteCanonicalNodeIndex DA S).val :=
    finiteCanonicalNodeAt_index_lt DA i q s hqs hsn
  have hRawDiff :
      ¬ (R.edge
          (finiteCanonicalNodeIndex DA Q).val
          (finiteCanonicalNodeIndex DA S).val
          (finiteCanonicalNodeIndex DA U).val ↔
         R.edge
          (finiteCanonicalNodeIndex DA Q).val
          (finiteCanonicalNodeIndex DA S).val
          (finiteCanonicalNodeIndex DA V).val) := by
    intro hEq
    have hU := finiteCanonicalRankedRawGraph_branch_edge_iff
      DA i q s u hqs hsu hun
    have hV := finiteCanonicalRankedRawGraph_branch_edge_iff
      DA i q s v hqs hsv hvn
    exact hDiff.2 (hU.symm.trans (hEq.trans hV))
  have hUpper : R.oneMeetLevel
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA V).val ≤
        (finiteCanonicalNodeIndex DA S).val := by
    by_contra hNot
    have hGt : (finiteCanonicalNodeIndex DA S).val <
        R.oneMeetLevel
          (finiteCanonicalNodeIndex DA U).val
          (finiteCanonicalNodeIndex DA V).val := by omega
    have hAgree := (R.oneMeetLevel_agree
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA V).val) hQS hGt
    exact hRawDiff hAgree
  change R.oneMeetLevel
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA V).val =
        (finiteCanonicalNodeIndex DA S).val
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
