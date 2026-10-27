import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVOneCoherence
import ThreeUniformDiaries.DiaryFiniteSignRootedRawVTwoCompatibility

/-!
# Rank-cut transport of full ordered-pair predecessor types

This module lifts the RAW sign-rooted shared-source-cut one/auxiliary
type comparisons to every predecessor of the REAL finite numerical
rank cut. The inserted off-path vertices and tied original levels
are handled directly, without a source convexity assumption.

For singleton tests, equal original levels give only false edges;
at a tied shared split level, earlier off-path raw nodes cannot
participate in any edge ending on either compared branch.

For auxiliary tests, a predecessor at strictly earlier source level
uses the previously verified raw comparison; a different same-level
node is off both branches, so its pair-edge tests vanish.

The source positive V2 parent-code theorem then yields an actual
rank-cut SAME FULL TWO-TYPE predicate, including both singleton
coordinates and all auxiliary ordered-pair edge tests.

This is the RAW precursor to causal-marker V2; the fully completed
graph is a separate next theorem. No pre-diary or absorber is
asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- General rank-cut transport of raw cross-branch singleton
type equality at a SHARED sign-rooted source node. Works with
either a 1- or 2-split and does not require source positivity. -/
theorem finiteCanonicalRankedRaw_crossOneType_at_shared_cut
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (hsu : s ≤ u) (hsv : s ≤ v)
    (hun : u < n) (hvn : v < n)
    (hRaw :
      (finiteCanonicalSignRootedFamily DA).RawCrossOneTypeBelow
        s ((finiteCanonicalSignRootedFamily DA).node i u)
          ((finiteCanonicalSignRootedFamily DA).node j v)) :
    (finiteCanonicalRankedRawGraph DA).SameOneTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j v hvn)).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let S := finiteCanonicalNodeAt DA i s hsn
  let U := finiteCanonicalNodeAt DA i u hun
  let V := finiteCanonicalNodeAt DA j v hvn
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
      (finiteCanonicalNodeIndex DA S).val := by
    simpa only [hYval,S] using hyS
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
          obtain ⟨k,a,b,c,hab,_hbc,_hcn,hXa,hYb,_hZc,_⟩ := hEdge
          have ha : X.val.1 = a := by
            have hh := congrArg Prod.fst hXa
            simpa only [F.node_level] using hh.symm
          have hb : Y.val.1 = b := by
            have hh := congrArg Prod.fst hYb
            simpa only [F.node_level] using hh.symm
          omega
        exact iff_of_false (hBoth U.val) (hBoth V.val)
    · have hYneqI : Y.val ≠ F.node i s := by
        intro h
        have hSub : Y = S := Subtype.ext h
        have hh := congrArg
          (fun T : FiniteCanonicalSignRootedVertex DA =>
            (finiteCanonicalNodeIndex DA T).val) hSub
        omega
      have hYneqJ : Y.val ≠ F.node j s := by
        intro h
        exact hYneqI (h.trans hShared.symm)
      have hOffI : Y.val ≠ F.node i Y.val.1 := by
        intro h
        exact hYneqI (by simpa only [hYeqS] using h)
      have hOffJ : Y.val ≠ F.node j Y.val.1 := by
        intro h
        exact hYneqJ (by simpa only [hYeqS] using h)
      exact iff_of_false
        (F.rawAmalgam_no_offpath_edge_at_terminal
          i X.val Y.val u (Or.inr hOffI))
        (F.rawAmalgam_no_offpath_edge_at_terminal
          j X.val Y.val v (Or.inr hOffJ))
  have hRankU := finiteCanonicalRankedRawGraph_edge_iff DA X Y U
  have hRankV := finiteCanonicalRankedRawGraph_edge_iff DA X Y V
  have hBoth := hRankU.trans (hRawMatch.trans hRankV.symm)
  simpa only [hXval,hYval] using hBoth

/-- Full rank-cut transport of raw cross-branch auxiliary ordered
pair type equality, including off-path rank predecessors tied with
the shared original split node. -/
theorem finiteCanonicalRankedRaw_crossAux_at_shared_cut
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v w z : Nat)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (hsu : s ≤ u) (hsw : s ≤ w)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hRaw :
      (finiteCanonicalSignRootedFamily DA).RawCrossAuxTypeBelow s
        ((finiteCanonicalSignRootedFamily DA).node i u)
        ((finiteCanonicalSignRootedFamily DA).node i v)
        ((finiteCanonicalSignRootedFamily DA).node j w)
        ((finiteCanonicalSignRootedFamily DA).node j z)) :
    (finiteCanonicalRankedRawGraph DA).SameAuxTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j w (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j z hzn)).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let S := finiteCanonicalNodeAt DA i s hsn
  let U := finiteCanonicalNodeAt DA i u (by omega)
  let V := finiteCanonicalNodeAt DA i v hvn
  let W := finiteCanonicalNodeAt DA j w (by omega)
  let Z := finiteCanonicalNodeAt DA j z hzn
  intro x hxS
  have hxCard : x < Fintype.card (FiniteCanonicalSignRootedVertex DA) :=
    lt_trans hxS (finiteCanonicalNodeIndex DA S).isLt
  obtain ⟨X,hXidx⟩ := finiteCanonicalNodeIndex_surjective DA
    (⟨x,hxCard⟩ : Fin (Fintype.card (FiniteCanonicalSignRootedVertex DA)))
  have hXval : (finiteCanonicalNodeIndex DA X).val = x :=
    congrArg Fin.val hXidx
  have hXSrank : (finiteCanonicalNodeIndex DA X).val <
      (finiteCanonicalNodeIndex DA S).val := by
    simpa only [hXval,S] using hxS
  have hBefore : finiteCanonicalNodeBefore DA X S :=
    (finiteCanonicalNodeBefore_iff_rank_lt DA X S).mpr hXSrank
  have hXlevel : X.val.1 ≤ s := by
    have hSlevel : S.val.1 = s :=
      finiteCanonicalNodeAt_level DA i s hsn
    rcases hBefore with hLt | ⟨hTie,_⟩ <;> omega
  have hRawMatch :
      F.rawAmalgam.edge X.val U.val V.val ↔
        F.rawAmalgam.edge X.val W.val Z.val := by
    rcases lt_or_eq_of_le hXlevel with hXltS | hXeqS
    · exact hRaw X.val hXltS
    · have hNeI : X.val ≠ F.node i s := by
        intro h
        have hSub : X = S := Subtype.ext h
        have hh := congrArg
          (fun T : FiniteCanonicalSignRootedVertex DA =>
            (finiteCanonicalNodeIndex DA T).val) hSub
        omega
      have hNeJ : X.val ≠ F.node j s := by
        intro h
        exact hNeI (h.trans hShared.symm)
      have hOffI : X.val ≠ F.node i X.val.1 := by
        intro h
        exact hNeI (by simpa only [hXeqS] using h)
      have hOffJ : X.val ≠ F.node j X.val.1 := by
        intro h
        exact hNeJ (by simpa only [hXeqS] using h)
      exact iff_of_false
        (F.rawAmalgam_no_offpath_edge_at_terminal
          i X.val U.val v (Or.inl hOffI))
        (F.rawAmalgam_no_offpath_edge_at_terminal
          j X.val W.val z (Or.inl hOffJ))
  have hI := finiteCanonicalRankedRawGraph_edge_iff DA X U V
  have hJ := finiteCanonicalRankedRawGraph_edge_iff DA X W Z
  have hBoth := hI.trans (hRawMatch.trans hJ.symm)
  simpa only [hXval] using hBoth

/-- Source V2-positive ordered pairs at a common canonical
2-split have the SAME COMPLETE pair type through its real
finite rank cut in the indexed raw union. No E3 side
orientation agreement at the current split is required. -/
theorem finiteCanonicalRankedRaw_sharedTwoSplit_positive_parent
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v w z : Nat)
    (hs : IsTwoSplit A s)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hsu : s < u) (hsw : s < w)
    (hu : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) u)
    (hv : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) v)
    (hw : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) w)
    (hz : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) z)
    (hPosI : ((finiteCanonicalSignRootedFamily DA).graph i).edge s u v)
    (hPosJ : ((finiteCanonicalSignRootedFamily DA).graph j).edge s w z) :
    (finiteCanonicalRankedRawGraph DA).SameTwoTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j w (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j z hzn)).val := by
  let F := finiteCanonicalSignRootedFamily DA
  have hRaw := F.raw_shared_twoSplit_positive_parent_compatible
    i j s hs hShared u v w z huv hwz hvn hzn
    hsu hsw hu hv hw hz hPosI hPosJ
  refine ⟨
    finiteCanonicalRankedRaw_crossOneType_at_shared_cut
      DA i j s u w hsn hShared hsu.le hsw.le
      (by omega) (by omega) hRaw.1,
    finiteCanonicalRankedRaw_crossOneType_at_shared_cut
      DA i j s v z hsn hShared (by omega) (by omega)
      hvn hzn hRaw.2.1,
    finiteCanonicalRankedRaw_crossAux_at_shared_cut
      DA i j s u v w z hsn hShared hsu.le hsw.le
      huv hwz hvn hzn hRaw.2.2⟩

end DiaryLeafPriority
end ThreeUniformDiaries
