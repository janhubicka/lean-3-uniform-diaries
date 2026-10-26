import ThreeUniformDiaries.DiaryFiniteSignRootedRawVOneCompatibility
import ThreeUniformDiaries.DiaryFiniteCanonicalRankedRawOneMeet
import ThreeUniformDiaries.DiaryFiniteCanonicalRankedOffBranchMask
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalMarkerGraph
import ThreeUniformDiaries.DiaryCausalMarkerTypeTransport

/-!
# Concrete V1 positive-parent coherence at actual finite rank cuts

The old source-level sign-rooted raw V1 theorem handles genuine
positive leaves on two branches sharing an original 1-split.
We first extend that equality of predecessor singleton types
from ORIGINAL source levels to every numbered predecessor in
the level-first finite canonical carrier. New tied-level
predecessors either give impossible equal-level raw edges
or are off the shared branch, hence have two false raw tests.

The concrete Nat-indexed off-branch mask then agrees on these
positive successors below the shared split rank. The previously
verified CAUSAL marker transport proves the corresponding
singleton types of the completed marker graph agree at the
ACTUAL numbered split cut. No globally prefix-uniform
orientation or unverified V1 axiom of a completed pre-diary
is assumed.

This proves cross-branch V1 coherence for all genuine
positive original source leaf descendants of a shared split.
The separate census of all target positive incidences,
split witnesses, V2 and full finite pre-diary remain open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- RAW cross-branch positive singleton-type equality extends to
every actual NUMERICAL predecessor of a shared source 1-split,
including all off-path raw nodes and tied original source levels. -/
theorem finiteCanonicalRankedRaw_sharedOneSplit_positive_parent
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hs : IsOneSplit A s)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) u)
    (hv : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) v)
    (hPosI : ((finiteCanonicalSignRootedFamily DA).graph i).edge 0 s u)
    (hPosJ : ((finiteCanonicalSignRootedFamily DA).graph j).edge 0 s v) :
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
  have hRaw : F.RawCrossOneTypeBelow s (F.node i u) (F.node j v) :=
    F.raw_shared_oneSplit_positive_parent_compatible
      i j s hs hShared u v hsu hsv hun hvn hu hv hPosI hPosJ
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

/-- GENUINE V1 positive-parent coherence in the FINAL causally
completed sign-rooted graph, between arbitrary positive source
leaves of two canonical branches sharing their original 1-split.

Unlike the earlier PR #892 reduction, the orientation is ACTUALLY
the final graph's literal LexEarlier, not a globally prefix-uniform
predicate assumed as an external premise. -/
theorem finiteCanonicalCausalMarkerGraph_sharedOneSplit_positive_parent
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hs : IsOneSplit A s)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) u)
    (hv : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) v)
    (hPosI : ((finiteCanonicalSignRootedFamily DA).graph i).edge 0 s u)
    (hPosJ : ((finiteCanonicalSignRootedFamily DA).graph j).edge 0 s v) :
    (finiteCanonicalCausalMarkerGraph DA).SameOneTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j v hvn)).val := by
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let m := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i s hsn)).val
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u hun)).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA j v hvn)).val
  have hma : m ≤ a := (finiteCanonicalNodeAt_index_lt
    DA i s u hsu hun).le
  have hmb : m ≤ b := (finiteCanonicalNodeAt_index_lt
    DA j s v hsv hvn).le_of_eq (by
      have hEq : finiteCanonicalNodeAt DA i s hsn =
          finiteCanonicalNodeAt DA j s hsn := Subtype.ext hShared
      exact congrArg
        (fun T : FiniteCanonicalSignRootedVertex DA =>
          (finiteCanonicalNodeIndex DA T).val) hEq)
  have huA : IsLeaf A u :=
    ((F.flip i).role_iff u hu.1 hun).1.mpr hu
  have hvA : IsLeaf A v :=
    ((F.flip j).role_iff v hv.1 hvn).1.mpr hv
  have hRaw : R.SameOneTypeBelow m a b :=
    finiteCanonicalRankedRaw_sharedOneSplit_positive_parent
      DA i j s u v hs hsn hShared hsu hsv
      hun hvn hu hv hPosI hPosJ
  have hMask : SameEarlierMarkerMask M m a b :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i j s u v (Or.inl hs) hsn hShared hsu hsv
      hun hvn huA hvA
  have hLater : ∀ y z, M y z → y < z :=
    finiteCanonicalRankedOffBranchMask_later DA
  change (causalMarkerLimit R M).SameOneTypeBelow m a b
  exact causalMarker_preserves_parent_oneType
    R G M m a b hma hmb hRaw hMask
    (by
      intro x y hxy hys
      exact causalMarkerLimit_formula R M hLater x y a)
    (by
      intro x y hxy hys
      exact causalMarkerLimit_formula R M hLater x y b)

end DiaryLeafPriority
end ThreeUniformDiaries
