import ThreeUniformDiaries.DiaryUnconditionalPreembedding
import ThreeUniformDiaries.DiaryOneSplitNextCut

/-!
# Local edge incidence controls for diary flips

There is one actual branch bit at a 1-split and one actual
auxiliary-pair bit at a 2-split. If an incident leaf (respectively
ordered leaf pair) is chosen on the positive side, all other
positive incidences are characterised by a strictly later
singleton (respectively auxiliary) meet.

These two facts are derived from the genuine V/E/S axioms, not
from a synthetic binary flip action. They are the reusable
ingredients for checking that two flips with the same initial
control bits agree on early triples.

At leaf-marker edges (1,a,b) and (2,a,b), the bit is the right
1-split incidence at the genuine leaf meet. This gives the
correct Devlin case of the manuscript's flip reconstruction
without its incorrect self-inequality.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H K : Ordered3Graph Nat}

/-- An incident leaf at a 1-split determines the positive
branch exactly by the strict singleton meet comparison.
This includes the case where the second leaf equals the
chosen positive witness. -/
theorem positive_oneSplit_edge_iff_later_meet
    (D : RoleDiary H) (m a w : Nat)
    (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hw : IsLeaf H w)
    (hma : m < a) (hmw : m < w)
    (hpositive : H.edge 0 m a) :
    H.edge 0 m w ↔ m < H.oneMeetLevel a w := by
  classical
  constructor
  · intro hwpos
    have hsame : H.SameOneTypeBelow (m+1) a w :=
      D.oneSplit_incident_oneTypes_succ m a w
        hm ha hw hpositive hwpos
    have hbound : m+1 ≤ min a w := by omega
    have hlevel : m+1 ≤ H.oneMeetLevel a w :=
      Nat.le_findGreatest hbound hsame
    omega
  · intro hlevel
    have h0m : 0 < m := by have hm3 := hm.1; omega
    exact ((H.oneMeetLevel_agree a w) h0m hlevel).mp hpositive

/-- An incident ordered leaf pair at a 2-split determines
the positive auxiliary branch by the strict auxiliary meet.
Only V2 coherence and the actual ordered edge tests are used. -/
theorem positive_twoSplit_edge_iff_later_aux_meet
    (D : RoleDiary H) (m a b c d : Nat)
    (hm : IsTwoSplit H m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m < a) (hmc : m < c)
    (hpositive : H.edge m a b) :
    H.edge m c d ↔ m < H.auxMeetLevel a b c d := by
  classical
  constructor
  · intro hother
    have hpair : H.SameTwoTypeBelow m a b c d :=
      D.two_split_coherent m a b c d
        hm hab hcd ha hb hc hd hpositive hother
    have hsucc : H.SameAuxTypeBelow (m+1) a b c d :=
      (H.sameAuxTypeBelow_succ_iff m a b c d).mpr
        ⟨hpair.2.2, iff_of_true hpositive hother⟩
    have hbound : m+1 ≤ min a c := by omega
    have hlevel : m+1 ≤ H.auxMeetLevel a b c d :=
      Nat.le_findGreatest hbound hsucc
    omega
  · intro hlevel
    exact ((H.auxMeetLevel_agree a b c d) hlevel).mp hpositive

/-- If the identity map is a diary pre-embedding between two
genuine diaries, the marker-1 edge on a pair of leaves agrees
between them precisely when the right 1-split edge at their
(common) singleton meet agrees.

The statement makes no claim that arbitrary mixed pair meets
are preserved by a flip. -/
theorem flip_marker_one_agrees_iff_split_bit_agrees
    (D : RoleDiary H) (E : RoleDiary K)
    (hflip : DiaryPreembeddingSpec H K id)
    (a b : Nat) (hab : a < b)
    (ha : IsLeaf H a) (hb : IsLeaf H b) :
    let m := H.oneMeetLevel a b
    (H.edge 1 a b ↔ K.edge 1 a b) ↔
      (H.edge 0 m b ↔ K.edge 0 m b) := by
  let m := H.oneMeetLevel a b
  have hm : IsOneSplit H m :=
    D.singleton_meets a b ha hb (ne_of_lt hab)
  have hma : m < a :=
    D.leaf_meet_lt_first a b ha hb (ne_of_lt hab)
  have hmK : IsOneSplit K m := hflip.one_split_role m hm
  have haK : IsLeaf K a := hflip.leaf_role a ha
  have hbK : IsLeaf K b := hflip.leaf_role b hb
  have hmeetK : K.oneMeetLevel a b = m := by
    simpa only [id_eq] using (hflip.leaf_one_meet a b ha hb)
  have hH : H.edge 1 a b ↔ H.edge 0 m b :=
    (D.leaf_marker_one a b hab ha hb).trans
      (D.lexEarlier_iff_right_split_marker
        m a b hm ha hb hab hma rfl)
  have hK : K.edge 1 a b ↔ K.edge 0 m b :=
    (E.leaf_marker_one a b hab haK hbK).trans
      (E.lexEarlier_iff_right_split_marker
        m a b hmK haK hbK hab hma hmeetK)
  constructor
  · intro h
    exact hH.symm.trans (h.trans hK)
  · intro h
    exact hH.trans (h.trans hK.symm)

/-- The Devlin marker 2 is the complement of marker 1 in
every genuine diary. Thus agreement of marker 2 between
two flips is also equivalent to agreement of the right
1-split bit at the actual leaf meet. -/
theorem flip_marker_two_agrees_iff_split_bit_agrees
    (D : RoleDiary H) (E : RoleDiary K)
    (hflip : DiaryPreembeddingSpec H K id)
    (a b : Nat) (hab : a < b)
    (ha : IsLeaf H a) (hb : IsLeaf H b) :
    let m := H.oneMeetLevel a b
    (H.edge 2 a b ↔ K.edge 2 a b) ↔
      (H.edge 0 m b ↔ K.edge 0 m b) := by
  let m := H.oneMeetLevel a b
  have haK : IsLeaf K a := hflip.leaf_role a ha
  have hbK : IsLeaf K b := hflip.leaf_role b hb
  have hH : H.edge 2 a b ↔ ¬ H.edge 1 a b :=
    (D.leaf_marker_two a b hab ha hb).trans
      (not_congr (D.leaf_marker_one a b hab ha hb).symm)
  have hK : K.edge 2 a b ↔ ¬ K.edge 1 a b :=
    (E.leaf_marker_two a b hab haK hbK).trans
      (not_congr (E.leaf_marker_one a b hab haK hbK).symm)
  have hbase :=
    D.flip_marker_one_agrees_iff_split_bit_agrees
      E hflip a b hab ha hb
  constructor
  · intro h
    apply hbase.mp
    have hneg : ¬ H.edge 1 a b ↔ ¬ K.edge 1 a b :=
      hH.symm.trans (h.trans hK)
    have hpos : H.edge 1 a b ↔ K.edge 1 a b := by
      tauto
    exact hbase.mp hpos
  · intro h
    have hpos := hbase.mpr h
    exact hH.trans ((not_congr hpos).trans hK.symm)

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
