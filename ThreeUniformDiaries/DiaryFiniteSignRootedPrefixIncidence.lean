import ThreeUniformDiaries.DiaryFiniteFaithfulFlipSignature
import ThreeUniformDiaries.DiaryFiniteGlobalE2ColumnRigidity
import ThreeUniformDiaries.DiaryFiniteE3SplitWitnessRigidity
import ThreeUniformDiaries.DiaryFinitePositiveAnchorCompletion

/-!
# A root sign and earlier S2 bits determine all source incidences before a cut

The verified faithful finite flip code has one GLOBAL marker-one
orientation bit and one E3 witness bit for each genuine source
two-split. Here we prove its crucial chronological geometry:

For two genuine flips P,Q of one fixed finite source diary A, if
their global marker reference bit agrees, and their selected
genuine S2 witness bits agree at every two-split s<m, then
EVERY increasing triple (x,y,z) with x<m has the same edge
incidence in P and Q, including all nonedges.

The proof uses the E1--E5 permitted edge classification:
E1 role edges never change; E2 is fixed by the global sign;
E3 at a two-split s<m is fixed by its S2 witness bit;
E4 Devlin marker edges are fixed by the global sign; and
E5 leaf triples are invariant under any genuine flip.
Role reflection gives the nonedge direction.

This is a NECESSARY structural input to a sign-rooted flip tree
or another geometric absorber construction: with the sign
chosen before the chronological E3 bits, corresponding source
types agree below every shared split cut. It is NOT a
cross-branch edge completion, an amalgamation theorem,
or the general second finite diary flip property.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Agreement on a SINGLE ordered source leaf-pair marker-one
bit implies agreement of ALL marker-one and marker-two Devlin
incidences between any two genuine flips of a common source. -/
theorem finite_two_flips_all_Devlin_markers_of_reference
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (FP : FiniteDiaryFlip A P n)
    (FQ : FiniteDiaryFlip A Q n)
    (r t : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t)
    (hRef : P.edge 1 r t ↔ Q.edge 1 r t) :
    ∀ u v : Nat, u < v → v < n →
      IsLeaf P u → IsLeaf P v →
      (P.edge 1 u v ↔ Q.edge 1 u v) ∧
      (P.edge 2 u v ↔ Q.edge 2 u v) := by
  let K : FiniteDiaryFlip P Q n := FP.symm.trans FQ
  have hrP : IsLeaf P r :=
    ((FP.role_iff r hr.1 (by omega)).1).mp hr
  have htP : IsLeaf P t :=
    ((FP.role_iff t ht.1 htn).1).mp ht
  have hM1 : ∀ u v : Nat, u < v → v < n →
      IsLeaf P u → IsLeaf P v →
      (P.edge 1 u v ↔ Q.edge 1 u v) := by
    rcases finite_flip_marker_one_global_sign K with hPres | hRev
    · exact hPres
    · have hReverse := hRev r t hrt htn hrP htP
      have hFalse : False := by
        tauto
      exact hFalse.elim
  intro u v huv hvn hu hv
  have huQ : IsLeaf Q u :=
    ((K.role_iff u hu.1 (by omega)).1).mp hu
  have hvQ : IsLeaf Q v :=
    ((K.role_iff v hv.1 hvn).1).mp hv
  have hMarkerOne : P.edge 1 u v ↔ Q.edge 1 u v :=
    hM1 u v huv hvn hu hv
  have hP1 := K.source_diary.prediary.leaf_marker_one
    u v huv hvn hu hv
  have hQ1 := K.target_diary.prediary.leaf_marker_one
    u v huv hvn huQ hvQ
  have hLex : LexEarlier P u v ↔ LexEarlier Q u v :=
    hP1.symm.trans (hMarkerOne.trans hQ1)
  have hP2 := K.source_diary.prediary.leaf_marker_two
    u v huv hvn hu hv
  have hQ2 := K.target_diary.prediary.leaf_marker_two
    u v huv hvn huQ hvQ
  exact ⟨hMarkerOne,hP2.trans ((not_congr hLex).trans hQ2.symm)⟩

/-- Two genuinely flipped diaries sharing the global Devlin
sign and one SOURCE S2 witness bit at each earlier 2-split
have LITERALLY IDENTICAL edge incidences on all triples whose
first vertex lies before the cut m.

The two-split witness pair at each s<m is taken from the
common original source A, not selected independently after
seeing the two flips. Requiring equality of the full E3
columns would be equivalent by the already verified S2
positive-anchor reconstruction, but is not assumed here. -/
theorem finite_two_flips_edges_agree_before_cut
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (FP : FiniteDiaryFlip A P n)
    (FQ : FiniteDiaryFlip A Q n)
    (r t m : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t)
    (hReference : P.edge 1 r t ↔ Q.edge 1 r t)
    (hEarlierS2 :
      ∀ s : Nat, IsTwoSplit A s → s < m →
        ∃ a b c d : Nat,
          a < b ∧ c < d ∧ b < n ∧ d < n ∧
          IsLeaf A a ∧ IsLeaf A b ∧
          IsLeaf A c ∧ IsLeaf A d ∧
          s < a ∧ s < c ∧
          A.twoMeetLevel a b c d = s ∧
          (P.edge s a b ↔ Q.edge s a b)) :
    ∀ x y z : Nat, x < y → y < z → z < n → x < m →
      (P.edge x y z ↔ Q.edge x y z) := by
  let K : FiniteDiaryFlip P Q n := FP.symm.trans FQ
  let L : FiniteLeafPreembedding P Q n n id :=
    K.identity_leafPreembedding
  have hDevlin :=
    finite_two_flips_all_Devlin_markers_of_reference
      FP FQ r t hrt htn hr ht hReference
  have hE2 :=
    finite_two_flips_E2_columns_equal_of_reference_marker
      FP FQ r t hrt htn hr ht hReference
  have hE3 :
      ∀ s u v : Nat, IsTwoSplit A s → s < m →
        u < v → v < n →
        IsLeaf A u → IsLeaf A v → s < u →
        (P.edge s u v ↔ Q.edge s u v) := by
    intro s u v hs hsm huv hvn hu hv hsu
    obtain ⟨a,b,c,d,hab,hcd,hbn,hdn,
      ha,hb,hc,hd,hsa,hsc,hMeet,hBit⟩ :=
      hEarlierS2 s hs hsm
    exact finite_two_flips_E3_column_of_witness_bit
      FP FQ s a b c d hs hab hcd hbn hdn
      ha hb hc hd hsa hsc hMeet hBit
      u v huv hvn hu hv hsu
  have hAtShape :
      ∀ x y z : Nat, x < y → y < z → z < n → x < m →
        PermittedDiaryEdge P x y z →
        (P.edge x y z ↔ Q.edge x y z) := by
    intro x y z hxy hyz hzn hxm hShape
    rcases hShape with hE1 | hE2shape | hE3shape | hE4 | hE5
    · rcases hE1 with ⟨rfl,hy,hz3⟩
      have hRoleMarker :=
        L.role_marker_edge_iff
          K.source_diary.prediary K.target_diary.prediary
          z hz3 hzn
      rcases hy with rfl | rfl
      · simpa only [L.marker_zero,L.marker_one,id_eq] using hRoleMarker.1
      · simpa only [L.marker_zero,L.marker_two,id_eq] using hRoleMarker.2
    · rcases hE2shape with ⟨rfl,hOneY,hLeafZ⟩
      have hyn : y < n := by omega
      have hyA : IsOneSplit A y :=
        ((FP.role_iff y hOneY.1 hyn).2.1).mpr hOneY
      have hzA : IsLeaf A z :=
        ((FP.role_iff z hLeafZ.1 hzn).1).mpr hLeafZ
      exact hE2 y z hyA hzA hyz hzn
    · rcases hE3shape with ⟨hTwoX,hLeafY,hLeafZ⟩
      have hxn : x < n := by omega
      have hyn : y < n := by omega
      have hxA : IsTwoSplit A x :=
        ((FP.role_iff x hTwoX.1 hxn).2.2).mpr hTwoX
      have hyA : IsLeaf A y :=
        ((FP.role_iff y hLeafY.1 hyn).1).mpr hLeafY
      have hzA : IsLeaf A z :=
        ((FP.role_iff z hLeafZ.1 hzn).1).mpr hLeafZ
      exact hE3 x y z hxA hxm hyz hzn hyA hzA hxy
    · rcases hE4 with ⟨hx,hLeafY,hLeafZ⟩
      have hMark := hDevlin y z hyz hzn hLeafY hLeafZ
      rcases hx with rfl | rfl
      · exact hMark.1
      · exact hMark.2
    · rcases hE5 with ⟨hLeafX,hLeafY,hLeafZ⟩
      exact K.leaf_edge_iff x y z hxy hyz hzn
        hLeafX hLeafY hLeafZ
  intro x y z hxy hyz hzn hxm
  have hShapes := L.permittedEdge_iff x y z hxy hyz hzn
  constructor
  · intro hP
    have hShapeP := K.source_diary.prediary.permitted_edge x y z hP
    exact (hAtShape x y z hxy hyz hzn hxm hShapeP).mp hP
  · intro hQ
    have hShapeQ := K.target_diary.prediary.permitted_edge x y z hQ
    have hShapeP : PermittedDiaryEdge P x y z := by
      simpa only [id_eq] using hShapes.mpr hShapeQ
    exact (hAtShape x y z hxy hyz hzn hxm hShapeP).mpr hQ

end DiaryLeafPriority
end ThreeUniformDiaries
