import ThreeUniformDiaries.DiaryFiniteCanonicalRankedRawOneMeet
import ThreeUniformDiaries.DiaryFiniteSignRootedRawTypePreservation
import ThreeUniformDiaries.DiarySourceLexAuxReduction

/-!
# Full pointed auxiliary meet and LexEarlier in the ranked raw tree

The ranked canonical sign-rooted union preserves each original
proper singleton meet at exactly the rank of its source 1-split.
To transport the manuscript's literal LexEarlier, it remains to
preserve the mixed POINTED auxiliary meet of (s,u) and (s,v).

Let q be the source auxiliary meet for this pair. Among ALL
ranked nodes X preceding the old source node at q, either
X has an original source level < q, when exact raw source
auxiliary type transport applies, or X is an off-path node
at original level q. Its raw edge tests ending on the two
source leaves are then both false. Thus the ranked auxiliary
types agree below rank(q).

The original first-difference witness at (q,s,u)/(q,s,v)
survives inducedly in the ranked raw graph, forcing equality
of the auxiliary meet with rank(q). The manuscript's exact
lexicographic comparator is then transported by its own
first-difference formula, NOT by an artificial lex-order axiom.

The result is about the actual ranked RAW graph. Later causal
marker insertion has already been separately checked to retain
its proper leaf meets and LexEarlier values (#906).
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Mixed auxiliary meet (s,u) ∧ (s,v) in the actual
ranked canonical RAW graph equals exactly the rank
of the source mixed auxiliary meet q. Extra off-path
vertices and original source-level ties do not affect it. -/
theorem finiteCanonicalRankedRaw_pointedAuxMeet_exact
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hsn : s < n) (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hSourceMeet :
      ((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel
        u v = s) :
    (finiteCanonicalRankedRawGraph DA).auxMeetLevel
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i
          ((finiteCanonicalSignRootedFamily DA).graph i).auxMeetLevel
            s u s v (by
              have hq := onePass_source_mixedAux_first_difference
                ((finiteCanonicalSignRootedFamily DA).graph i)
                s u v hsu hsv hSourceMeet
              omega))).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let q := (F.graph i).auxMeetLevel s u s v
  obtain ⟨hqs,hDiff⟩ :=
    onePass_source_mixedAux_first_difference
      (F.graph i) s u v hsu hsv hSourceMeet
  have hqn : q < n := by omega
  let Q := finiteCanonicalNodeAt DA i q hqn
  let S := finiteCanonicalNodeAt DA i s hsn
  let U := finiteCanonicalNodeAt DA i u hun
  let V := finiteCanonicalNodeAt DA i v hvn
  have hQS : (finiteCanonicalNodeIndex DA Q).val <
      (finiteCanonicalNodeIndex DA S).val :=
    finiteCanonicalNodeAt_index_lt DA i q s hqs hsn
  have hSourceAux : (F.graph i).SameAuxTypeBelow q s u s v :=
    (F.graph i).auxMeetLevel_agree s u s v
  have hRawAux : F.RawSameAuxTypeBelow q
      (F.node i s) (F.node i u)
      (F.node i s) (F.node i v) :=
    (F.rawSameAuxTypeBelow_iff_source
      i q s u s v hqs.le hqs.le hsu hsv hun hvn).mpr
      hSourceAux
  have hAuxAgree : R.SameAuxTypeBelow
      (finiteCanonicalNodeIndex DA Q).val
      (finiteCanonicalNodeIndex DA S).val
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA S).val
      (finiteCanonicalNodeIndex DA V).val := by
    intro x hxQ
    have hxCard :
        x < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
      lt_trans hxQ (finiteCanonicalNodeIndex DA Q).isLt
    obtain ⟨X,hIdx⟩ := finiteCanonicalNodeIndex_surjective DA
      (⟨x,hxCard⟩ :
        Fin (Fintype.card (FiniteCanonicalSignRootedVertex DA)))
    have hxVal : (finiteCanonicalNodeIndex DA X).val = x :=
      congrArg Fin.val hIdx
    have hXQ : (finiteCanonicalNodeIndex DA X).val <
        (finiteCanonicalNodeIndex DA Q).val := by
      simpa only [hxVal] using hxQ
    have hBefore : finiteCanonicalNodeBefore DA X Q :=
      (finiteCanonicalNodeBefore_iff_rank_lt DA X Q).mpr hXQ
    have hLevel : X.val.1 ≤ q := by
      have hQlevel : Q.val.1 = q :=
        finiteCanonicalNodeAt_level DA i q hqn
      rcases hBefore with hLt | ⟨hTie,_⟩ <;> omega
    have hRawSame :
        F.rawAmalgam.edge X.val S.val U.val ↔
          F.rawAmalgam.edge X.val S.val V.val := by
      rcases lt_or_eq_of_le hLevel with hXlt | hXeq
      · exact hRawAux X.val hXlt
      · have hOff : X.val ≠ F.node i X.val.1 := by
          intro hOn
          have hXQnode : X.val = F.node i q := by
            simpa only [hXeq] using hOn
          have hSubtype : X = Q := Subtype.ext hXQnode
          have hRanks := congrArg
            (fun T : FiniteCanonicalSignRootedVertex DA =>
              (finiteCanonicalNodeIndex DA T).val) hSubtype
          omega
        exact iff_of_false
          (F.rawAmalgam_no_offpath_edge_at_terminal
            i X.val S.val u (Or.inl hOff))
          (F.rawAmalgam_no_offpath_edge_at_terminal
            i X.val S.val v (Or.inl hOff))
    have hI := finiteCanonicalRankedRawGraph_edge_iff DA X S U
    have hJ := finiteCanonicalRankedRawGraph_edge_iff DA X S V
    have hBoth := hI.trans (hRawSame.trans hJ.symm)
    simpa only [hxVal] using hBoth
  have hLower :
      (finiteCanonicalNodeIndex DA Q).val ≤
        R.auxMeetLevel
          (finiteCanonicalNodeIndex DA S).val
          (finiteCanonicalNodeIndex DA U).val
          (finiteCanonicalNodeIndex DA S).val
          (finiteCanonicalNodeIndex DA V).val := by
    apply Nat.le_findGreatest (by omega)
    exact hAuxAgree
  have hRankDiff :
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
    exact hDiff (hU.symm.trans (hEq.trans hV))
  have hUpper :
      R.auxMeetLevel
          (finiteCanonicalNodeIndex DA S).val
          (finiteCanonicalNodeIndex DA U).val
          (finiteCanonicalNodeIndex DA S).val
          (finiteCanonicalNodeIndex DA V).val ≤
        (finiteCanonicalNodeIndex DA Q).val := by
    by_contra hNot
    have hGt : (finiteCanonicalNodeIndex DA Q).val <
        R.auxMeetLevel
          (finiteCanonicalNodeIndex DA S).val
          (finiteCanonicalNodeIndex DA U).val
          (finiteCanonicalNodeIndex DA S).val
          (finiteCanonicalNodeIndex DA V).val := by omega
    have hAgreement := (R.auxMeetLevel_agree
      (finiteCanonicalNodeIndex DA S).val
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA S).val
      (finiteCanonicalNodeIndex DA V).val) hGt
    exact hRankDiff hAgreement
  change
    R.auxMeetLevel
      (finiteCanonicalNodeIndex DA S).val
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA S).val
      (finiteCanonicalNodeIndex DA V).val =
      (finiteCanonicalNodeIndex DA Q).val
  omega

/-- The manuscript's LITERAL source LexEarlier comparator
on an original canonical source-flip branch equals the
literal comparator in the Nat-ranked raw union. This
includes all proper singleton meets without guessing
a new Devlin orientation. -/
theorem finiteCanonicalRankedRaw_original_lex_iff_source
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hsn : s < n) (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hSourceMeet :
      ((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel
        u v = s) :
    LexEarlier (finiteCanonicalRankedRawGraph DA)
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val ↔
    LexEarlier ((finiteCanonicalSignRootedFamily DA).graph i) u v := by
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let q := (F.graph i).auxMeetLevel s u s v
  obtain ⟨hqs,_⟩ :=
    onePass_source_mixedAux_first_difference
      (F.graph i) s u v hsu hsv hSourceMeet
  have hqn : q < n := by omega
  let Q := finiteCanonicalNodeAt DA i q hqn
  let S := finiteCanonicalNodeAt DA i s hsn
  let U := finiteCanonicalNodeAt DA i u hun
  let V := finiteCanonicalNodeAt DA i v hvn
  have hSU := finiteCanonicalNodeAt_index_lt DA i s u hsu hun
  have hSV := finiteCanonicalNodeAt_index_lt DA i s v hsv hvn
  have hOneMeet : R.oneMeetLevel
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA V).val =
      (finiteCanonicalNodeIndex DA S).val :=
    finiteCanonicalRankedRaw_original_proper_oneMeet_exact
      DA i s u v hsn hsu hsv hun hvn hSourceMeet
  have hAux :
      R.auxMeetLevel
        (finiteCanonicalNodeIndex DA S).val
        (finiteCanonicalNodeIndex DA U).val
        (finiteCanonicalNodeIndex DA S).val
        (finiteCanonicalNodeIndex DA V).val =
        (finiteCanonicalNodeIndex DA Q).val :=
    finiteCanonicalRankedRaw_pointedAuxMeet_exact
      DA i s u v hsn hsu hsv hun hvn hSourceMeet
  have hRight : R.edge
        (finiteCanonicalNodeIndex DA Q).val
        (finiteCanonicalNodeIndex DA S).val
        (finiteCanonicalNodeIndex DA V).val ↔
      (F.graph i).edge q s v :=
    finiteCanonicalRankedRawGraph_branch_edge_iff
      DA i q s v hqs hsv hvn
  have hRawLex :=
    onePass_lexEarlier_iff_mixedAux_right
      R
      (finiteCanonicalNodeIndex DA S).val
      (finiteCanonicalNodeIndex DA U).val
      (finiteCanonicalNodeIndex DA V).val
      hSU hSV hOneMeet
  have hSrcLex :=
    onePass_lexEarlier_iff_mixedAux_right
      (F.graph i) s u v hsu hsv hSourceMeet
  exact hRawLex.trans (by
    rw [hAux]
    exact hRight.trans hSrcLex.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
