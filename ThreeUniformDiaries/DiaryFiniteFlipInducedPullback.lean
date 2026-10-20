import ThreeUniformDiaries.DiaryFiniteFlipInducedReduct
import ThreeUniformDiaries.DiaryFiniteLeafMeetCapTransfer
import ThreeUniformDiaries.DiaryFiniteLeafMeetMarkerOneDisagreement
import ThreeUniformDiaries.DiaryFiniteLeafMeetTwoSplitDisagreement
import ThreeUniformDiaries.DiaryFiniteLeafMeetFirstDisagreement
import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# The exact finite induced pullback of a leaf preembedding is a flip

Assume a finite diary A embeds as a LEAF preembedding into a
countable RoleDiary G. By the verified leaf-meet closure theorem,
the selected image of ALL source vertices is precisely the
leaf-meet support. By the verified increasing-reindexing theorem,
that support has exactly the source number of vertices and its
index i denotes f(i). Its induced restriction is a genuine diary.

Here we verify that this pulled-back diary is a genuine FLIP of A:
roles and induced triples of leaves are unchanged, and EVERY
singleton and full ordered-pair meet of source leaves agrees
numerically. The last assertion is checked at the actual retained
first-disagreement vertices: one-split zero-marker bits, two-split
auxiliary bits, marker one, and the genuine cap case.

Crucially this is ONLY a finite diary flip and an induced
RELATIONAL pullback. No assertion is made about preservation of
split-containing mixed numerical meets by the original map f
into the countable target G. Those can change under target flips.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A G : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}

/-- Exact singleton meet at a pair of ordered genuine source leaves
after extracting the full leaf-generated image support. -/
theorem finiteLeafPreembedding_orderedLeaf_oneMeet_exact
    (DA : FiniteRoleDiaryBlock A n)
    (DG : RoleDiary G)
    (P : FiniteLeafPreembedding A G n k f)
    (a b : Nat) (hab : a < b) (hbn : b < n)
    (haLeaf : IsLeaf A a) (hbLeaf : IsLeaf A b) :
    (finiteSupportGraph G
      (finiteLeafMeetSupport G (finiteDiaryLeafImage A n f))).oneMeetLevel a b =
        A.oneMeetLevel a b := by
  classical
  let S := finiteLeafMeetSupport G (finiteDiaryLeafImage A n f)
  let H := finiteSupportGraph G S
  let m := A.oneMeetLevel a b
  have han : a < n := by omega
  have hSplit : IsOneSplit A m :=
    DA.singleton_meets a b hab hbn haLeaf hbLeaf
  have hmn : m < n := by
    have hh := A.oneMeetLevel_le_min a b
    omega
  have hmA : m < a := by
    have hle := (A.oneMeetLevel_le_min a b).trans (min_le_left _ _)
    have hne : m ≠ a := by
      intro h
      have hs : IsOneSplit A a := by
        simpa only [h] using hSplit
      exact haLeaf.2.1 hs.2.1
    omega
  have hmB : m < b := by
    have hle := (A.oneMeetLevel_le_min a b).trans (min_le_right _ _)
    have hne : m ≠ b := by
      intro h
      have hs : IsOneSplit A b := by
        simpa only [h] using hSplit
      exact hbLeaf.2.1 hs.2.1
    omega
  have hCard : S.card = n := finiteLeafPreembedding_support_card DA P
  have haS : a < S.card := by omega
  have hbS : b < S.card := by omega
  have hmS : m < S.card := by omega
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 2 (by omega)
  have hOldSplit : IsOneSplit G (f m) :=
    ((P.role_iff m hSplit.1 hmn).2.1).mpr hSplit
  have hOldMeet : G.oneMeetLevel (f a) (f b) = f m := by
    change G.oneMeetLevel (f a) (f b) = f (A.oneMeetLevel a b)
    exact P.leaf_oneMeet a b haLeaf.1 han hbLeaf.1 hbn haLeaf hbLeaf
  have hIa : finiteSupportIndex S a = f a :=
    finiteLeafPreembedding_support_index_eq DA P a han
  have hJb : finiteSupportIndex S b = f b :=
    finiteLeafPreembedding_support_index_eq DA P b hbn
  have hMm : finiteSupportIndex S m = f m :=
    finiteLeafPreembedding_support_index_eq DA P m hmn
  have hExact : H.oneMeetLevel a b = m :=
    finiteSupportGraph_oneMeet_exact_at_retained_oneSplit
      DG h0 h1 h2 a b m (f a) (f b) (f m)
      haS hbS hmS hab hSplit.1 hmA hmB hIa hJb hMm
      hOldSplit hOldMeet
  exact hExact

/-- Every singleton meet of source leaves survives the induced
finite pullback, including diagonal and reverse-order comparisons. -/
theorem finiteLeafPreembedding_leaf_oneMeet_exact
    (DA : FiniteRoleDiaryBlock A n)
    (DG : RoleDiary G)
    (P : FiniteLeafPreembedding A G n k f)
    (a b : Nat) (han : a < n) (hbn : b < n)
    (haLeaf : IsLeaf A a) (hbLeaf : IsLeaf A b) :
    (finiteSupportGraph G
      (finiteLeafMeetSupport G (finiteDiaryLeafImage A n f))).oneMeetLevel a b =
        A.oneMeetLevel a b := by
  let H := finiteSupportGraph G
    (finiteLeafMeetSupport G (finiteDiaryLeafImage A n f))
  by_cases heq : a = b
  · subst b
    simp only [Ordered3Graph.oneMeetLevel_self_eq]
  · rcases lt_or_gt_of_ne heq with hab | hba
    · exact finiteLeafPreembedding_orderedLeaf_oneMeet_exact
        DA DG P a b hab hbn haLeaf hbLeaf
    · have hOrdered := finiteLeafPreembedding_orderedLeaf_oneMeet_exact
        DA DG P b a hba han hbLeaf haLeaf
      calc
        H.oneMeetLevel a b = H.oneMeetLevel b a :=
          finiteLeafMeet_oneMeet_comm H a b
        _ = A.oneMeetLevel b a := hOrdered
        _ = A.oneMeetLevel a b :=
          (finiteLeafMeet_oneMeet_comm A a b).symm

/-- Every FULL ordered-pair leaf meet is preserved exactly.
The proof separates the only three source diary alternatives:
the first-leaf cap, marker one, and a proper genuine 2-split. -/
theorem finiteLeafPreembedding_leaf_twoMeet_exact
    (DA : FiniteRoleDiaryBlock A n)
    (DG : RoleDiary G)
    (P : FiniteLeafPreembedding A G n k f)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (haLeaf : IsLeaf A a) (hbLeaf : IsLeaf A b)
    (hcLeaf : IsLeaf A c) (hdLeaf : IsLeaf A d) :
    (finiteSupportGraph G
      (finiteLeafMeetSupport G (finiteDiaryLeafImage A n f))).twoMeetLevel
        a b c d = A.twoMeetLevel a b c d := by
  classical
  let S := finiteLeafMeetSupport G (finiteDiaryLeafImage A n f)
  let H := finiteSupportGraph G S
  let m := A.twoMeetLevel a b c d
  have han : a < n := by omega
  have hcn : c < n := by omega
  have hCard : S.card = n := finiteLeafPreembedding_support_card DA P
  have haS : a < S.card := by omega
  have hbS : b < S.card := by omega
  have hcS : c < S.card := by omega
  have hdS : d < S.card := by omega
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 2 (by omega)
  have hIa : finiteSupportIndex S a = f a :=
    finiteLeafPreembedding_support_index_eq DA P a han
  have hJb : finiteSupportIndex S b = f b :=
    finiteLeafPreembedding_support_index_eq DA P b hbn
  have hKc : finiteSupportIndex S c = f c :=
    finiteLeafPreembedding_support_index_eq DA P c hcn
  have hLd : finiteSupportIndex S d = f d :=
    finiteLeafPreembedding_support_index_eq DA P d hdn
  have hOldMeet :
      G.twoMeetLevel (f a) (f b) (f c) (f d) = f m := by
    change G.twoMeetLevel (f a) (f b) (f c) (f d) =
      f (A.twoMeetLevel a b c d)
    exact P.leaf_twoMeet a b c d hab hcd
      haLeaf.1 han hbLeaf.1 hbn hcLeaf.1 hcn hdLeaf.1 hdn
      haLeaf hbLeaf hcLeaf hdLeaf
  have hGLeaf (u : Nat) (hu3 : 3 ≤ u) (hun : u < n)
      (huLeaf : IsLeaf A u) : IsLeaf G (f u) :=
    ((P.role_iff u hu3 hun).1).mpr huLeaf
  rcases DA.pair_meets a b c d hab hcd hbn hdn
    haLeaf hbLeaf hcLeaf hdLeaf with hCap | hMarker | hSplit
  · have hminBound : min a c < n := by omega
    have hMinIndex : finiteSupportIndex S (min a c) = f (min a c) :=
      finiteLeafPreembedding_support_index_eq DA P (min a c) hminBound
    have hSourceCap : G.twoMeetLevel
        (finiteSupportIndex S a) (finiteSupportIndex S b)
        (finiteSupportIndex S c) (finiteSupportIndex S d) =
        finiteSupportIndex S (min a c) := by
      rw [hIa,hJb,hKc,hLd,hMinIndex]
      exact hOldMeet.trans (congrArg f hCap)
    have hT := finiteSupportGraph_capped_twoMeet_exact
      (G := G) (S := S) a b c d
      haS hbS hcS hdS hab hcd hSourceCap
    change H.twoMeetLevel a b c d = m
    exact hT.trans hCap.symm
  · have hGMarker : G.twoMeetLevel (f a) (f b) (f c) (f d) = 1 := by
      calc
        G.twoMeetLevel (f a) (f b) (f c) (f d) = f m := hOldMeet
        _ = f 1 := congrArg f (show m = 1 from hMarker)
        _ = 1 := P.marker_one
    have hT := finiteSupportGraph_twoMeet_exact_at_marker_one
      DG h0 h1 h2 a b c d
      haS hbS hcS hdS hab hcd haLeaf.1 hcLeaf.1
      (by simpa only [hIa] using (hGLeaf a haLeaf.1 han haLeaf))
      (by simpa only [hJb] using (hGLeaf b hbLeaf.1 hbn hbLeaf))
      (by simpa only [hKc] using (hGLeaf c hcLeaf.1 hcn hcLeaf))
      (by simpa only [hLd] using (hGLeaf d hdLeaf.1 hdn hdLeaf))
      (by simpa only [hIa,hJb,hKc,hLd] using hGMarker)
    change H.twoMeetLevel a b c d = m
    exact hT.trans hMarker.symm
  · have hmn : m < n := by
      have hbnd := A.twoMeetLevel_le_min a b c d
      omega
    have hmS : m < S.card := by omega
    have hMm : finiteSupportIndex S m = f m :=
      finiteLeafPreembedding_support_index_eq DA P m hmn
    have hmA : m < a := by
      have hle := (A.twoMeetLevel_le_min a b c d).trans
        (min_le_left _ _)
      have hne : m ≠ a := by
        intro h
        have hs : IsTwoSplit A a := by
          have ht : IsTwoSplit A m := hSplit
          simpa only [h] using ht
        exact haLeaf.2.2 hs.2.2
      omega
    have hmC : m < c := by
      have hle := (A.twoMeetLevel_le_min a b c d).trans
        (min_le_right _ _)
      have hne : m ≠ c := by
        intro h
        have hs : IsTwoSplit A c := by
          have ht : IsTwoSplit A m := hSplit
          simpa only [h] using ht
        exact hcLeaf.2.2 hs.2.2
      omega
    have hGSplit : IsTwoSplit G (f m) :=
      ((P.role_iff m hSplit.1 hmn).2.2).mpr hSplit
    have hT := finiteSupportGraph_twoMeet_exact_at_retained_twoSplit
      DG a b c d m haS hbS hcS hdS hmS
      hab hcd hmA hmC
      (by simpa only [hMm] using hGSplit)
      (by simpa only [hIa,hJb,hKc,hLd,hMm] using hOldMeet)
    change H.twoMeetLevel a b c d = m
    exact hT

/-- The induced finite diary pulled back from the countable
target along a leaf preembedding is genuinely a FINITE FLIP of
the original diary, in the exact manuscript sense. -/
theorem finiteLeafPreembedding_support_is_flip
    (DA : FiniteRoleDiaryBlock A n)
    (DG : RoleDiary G)
    (P : FiniteLeafPreembedding A G n k f) :
    FiniteDiaryFlip A
      (finiteSupportGraph G
        (finiteLeafMeetSupport G (finiteDiaryLeafImage A n f))) n := by
  classical
  let S := finiteLeafMeetSupport G (finiteDiaryLeafImage A n f)
  let H := finiteSupportGraph G S
  have hCard : S.card = n := finiteLeafPreembedding_support_card DA P
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G
    (finiteDiaryLeafImage A n f) 2 (by omega)
  refine {
    source_diary := DA
    target_diary := finiteLeafPreembedding_support_is_finiteDiary DA DG P
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu3 hun
    have huS : u < S.card := by omega
    have hIdx : finiteSupportIndex S u = f u :=
      finiteLeafPreembedding_support_index_eq DA P u hun
    have hRoles := P.role_iff u hu3 hun
    have hLeaf : IsLeaf H u ↔ IsLeaf G (f u) := by
      have hh := finiteSupportGraph_leaf_iff
        (G := G) (S := S) h0 h1 h2 u hu3 huS
      simpa only [hIdx] using hh
    have hOne : IsOneSplit H u ↔ IsOneSplit G (f u) := by
      have hh := finiteSupportGraph_oneSplit_iff
        (G := G) (S := S) h0 h1 h2 u hu3 huS
      simpa only [hIdx] using hh
    have hTwo : IsTwoSplit H u ↔ IsTwoSplit G (f u) := by
      have hh := finiteSupportGraph_twoSplit_iff
        (G := G) (S := S) h0 h1 h2 u hu3 huS
      simpa only [hIdx] using hh
    exact ⟨hRoles.1.symm.trans hLeaf.symm,
      hRoles.2.1.symm.trans hOne.symm,
      hRoles.2.2.symm.trans hTwo.symm⟩
  · intro a b c hab hbc hcn ha hb hc
    have hTarget := finiteLeafPreembedding_support_edge_iff
      DA P a b c hab hbc hcn
    have hOld := P.leaf_edge_iff a b c hab hbc hcn ha hb hc
    exact (hTarget.trans hOld).symm
  · intro a b han hbn ha hb
    exact (finiteLeafPreembedding_leaf_oneMeet_exact
      DA DG P a b han hbn ha hb).symm
  · intro a b c d hab hcd hbn hdn ha hb hc hd
    exact (finiteLeafPreembedding_leaf_twoMeet_exact
      DA DG P a b c d hab hcd hbn hdn ha hb hc hd).symm

end DiaryLeafPriority
end ThreeUniformDiaries
