import ThreeUniformDiaries.DiaryFlipLocalIncidence

/-!
# One-split flip bits really reconstruct every incidence edge

The manuscript encodes a flip at a 1-split m by the existence
of a leaf on which an edge (0,m,-) is removed. The code appears
asymmetric, but its value is exactly the choice of the positive
successor branch at m.

For two genuine diary flips of a common source, equality of
this single Boolean bit forces equality of EVERY edge (0,m,w)
to a leaf w. The proof uses the preserved singleton leaf meets,
not any false preservation of mixed meets. In particular it
handles leaves in other, unrelated prefix classes: the V1
axiom excludes their positive incidence automatically.

This is the first actual case of the flip-prefix reconstruction
lemma. The corresponding 2-split and Devlin cases are separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {A B C : Ordered3Graph Nat}

/-- The source-positive part of the manuscript's 1-split
flip indicator, restricted to actual leaves. The permitted
E-edge shapes make the leaf restriction automatic. -/
def OneSplitRemovedBit
    (A B : Ordered3Graph Nat) (m : Nat) : Prop :=
  ∃ w, IsLeaf A w ∧ m < w ∧
    A.edge 0 m w ∧ ¬ B.edge 0 m w

/-- Any chosen positive witness for a 1-split detects the
whole asymmetric removed-edge bit, even when the target
flip reverses the two successor branches. -/
theorem oneSplitRemovedBit_iff_chosen_positive
    (DA : RoleDiary A)
    (hAB : DiaryPreembeddingSpec A B id)
    (m a : Nat)
    (hm : IsOneSplit A m)
    (ha : IsLeaf A a) (hma : m < a)
    (hpositive : A.edge 0 m a) :
    OneSplitRemovedBit A B m ↔ ¬ B.edge 0 m a := by
  classical
  constructor
  · rintro ⟨w, hw, hmw, hAw, hBw⟩
    have hLater : m < A.oneMeetLevel a w :=
      (DA.positive_oneSplit_edge_iff_later_meet
        m a w hm ha hw hma hmw hpositive).mp hAw
    have hMeetB : B.oneMeetLevel a w =
        A.oneMeetLevel a w := by
      simpa only [id_eq] using hAB.leaf_one_meet a w ha hw
    have hLaterB : m < B.oneMeetLevel a w := by
      rw [hMeetB]
      exact hLater
    have h0m : 0 < m := by have h3 := hm.1; omega
    have hAgreement : B.edge 0 m a ↔ B.edge 0 m w :=
      (B.oneMeetLevel_agree a w) h0m hLaterB
    exact fun hBa => hBw (hAgreement.mp hBa)
  · intro h
    exact ⟨a, ha, hma, hpositive, h⟩

/-- Equality of a single branch incidence at the chosen
two-leaf split witness forces every other leaf incidence
to agree in two diary flips of the same source. -/
theorem oneSplit_edges_agree_of_witness
    (DB : RoleDiary B) (DC : RoleDiary C)
    (hAB : DiaryPreembeddingSpec A B id)
    (hAC : DiaryPreembeddingSpec A C id)
    (m a b : Nat)
    (hm : IsOneSplit A m)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hma : m < a) (hmb : m < b)
    (hMeet : A.oneMeetLevel a b = m)
    (hAnchor : B.edge 0 m a ↔ C.edge 0 m a) :
    ∀ w, IsLeaf A w → m < w →
      (B.edge 0 m w ↔ C.edge 0 m w) := by
  classical
  have hmB : IsOneSplit B m := hAB.one_split_role m hm
  have hmC : IsOneSplit C m := hAC.one_split_role m hm
  have haB : IsLeaf B a := hAB.leaf_role a ha
  have hbB : IsLeaf B b := hAB.leaf_role b hb
  have haC : IsLeaf C a := hAC.leaf_role a ha
  have hbC : IsLeaf C b := hAC.leaf_role b hb
  have hMeetB : B.oneMeetLevel a b = m := by
    simpa only [id_eq, hMeet] using hAB.leaf_one_meet a b ha hb
  have hMeetC : C.oneMeetLevel a b = m := by
    simpa only [id_eq, hMeet] using hAC.leaf_one_meet a b ha hb
  have hOppB : ¬ (B.edge 0 m a ↔ B.edge 0 m b) :=
    DB.oneSplit_witness_opposite_marker
      m a b hmB haB hbB hma hmb hMeetB
  have hOppC : ¬ (C.edge 0 m a ↔ C.edge 0 m b) :=
    DC.oneSplit_witness_opposite_marker
      m a b hmC haC hbC hma hmb hMeetC
  have hOtherAnchor : B.edge 0 m b ↔ C.edge 0 m b := by
    tauto
  intro w hw hmw
  have hwB : IsLeaf B w := hAB.leaf_role w hw
  have hwC : IsLeaf C w := hAC.leaf_role w hw
  by_cases hBpos : B.edge 0 m a
  · have hCpos : C.edge 0 m a := hAnchor.mp hBpos
    have hOneB : B.oneMeetLevel a w =
        A.oneMeetLevel a w := by
      simpa only [id_eq] using hAB.leaf_one_meet a w ha hw
    have hOneC : C.oneMeetLevel a w =
        A.oneMeetLevel a w := by
      simpa only [id_eq] using hAC.leaf_one_meet a w ha hw
    have hMeetEqual : B.oneMeetLevel a w =
        C.oneMeetLevel a w := hOneB.trans hOneC.symm
    calc
      B.edge 0 m w ↔ m < B.oneMeetLevel a w :=
        DB.positive_oneSplit_edge_iff_later_meet
          m a w hmB haB hwB hma hmw hBpos
      _ ↔ m < C.oneMeetLevel a w := by rw [hMeetEqual]
      _ ↔ C.edge 0 m w :=
        (DC.positive_oneSplit_edge_iff_later_meet
          m a w hmC haC hwC hma hmw hCpos).symm
  · have hBposB : B.edge 0 m b := by
      by_contra hn
      exact hOppB (iff_of_false hBpos hn)
    have hCposB : C.edge 0 m b := hOtherAnchor.mp hBposB
    have hOneB : B.oneMeetLevel b w =
        A.oneMeetLevel b w := by
      simpa only [id_eq] using hAB.leaf_one_meet b w hb hw
    have hOneC : C.oneMeetLevel b w =
        A.oneMeetLevel b w := by
      simpa only [id_eq] using hAC.leaf_one_meet b w hb hw
    have hMeetEqual : B.oneMeetLevel b w =
        C.oneMeetLevel b w := hOneB.trans hOneC.symm
    calc
      B.edge 0 m w ↔ m < B.oneMeetLevel b w :=
        DB.positive_oneSplit_edge_iff_later_meet
          m b w hmB hbB hwB hmb hmw hBposB
      _ ↔ m < C.oneMeetLevel b w := by rw [hMeetEqual]
      _ ↔ C.edge 0 m w :=
        (DC.positive_oneSplit_edge_iff_later_meet
          m b w hmC hbC hwC hmb hmw hCposB).symm

/-- The EXACT one-split reconstruction case: if two flips of A
have equal source-positive removed-edge indicators at m, then
ALL their E2 leaf incidences at m are identical. This proves
the local step from the original flip code, not a conditional
synthetic action on arbitrary edge predicates. -/
theorem oneSplit_edges_agree_of_same_removed_bit
    (DA : RoleDiary A) (DB : RoleDiary B) (DC : RoleDiary C)
    (hAB : DiaryPreembeddingSpec A B id)
    (hAC : DiaryPreembeddingSpec A C id)
    (m : Nat) (hm : IsOneSplit A m)
    (hbit : OneSplitRemovedBit A B m ↔
      OneSplitRemovedBit A C m) :
    ∀ w, IsLeaf A w → m < w →
      (B.edge 0 m w ↔ C.edge 0 m w) := by
  classical
  obtain ⟨a, b, ha, hb, hma, hmb, hMeet⟩ :=
    DA.one_split_witness m hm
  have hOpp := DA.oneSplit_witness_opposite_marker
    m a b hm ha hb hma hmb hMeet
  by_cases hPos : A.edge 0 m a
  · have hB :=
      DA.oneSplitRemovedBit_iff_chosen_positive
        hAB m a hm ha hma hPos
    have hC :=
      DA.oneSplitRemovedBit_iff_chosen_positive
        hAC m a hm ha hma hPos
    have hAnchor : B.edge 0 m a ↔ C.edge 0 m a := by
      have hNot : ¬ B.edge 0 m a ↔ ¬ C.edge 0 m a :=
        hB.symm.trans (hbit.trans hC)
      tauto
    exact oneSplit_edges_agree_of_witness
      DB DC hAB hAC m a b hm ha hb
      hma hmb hMeet hAnchor
  · have hPosB : A.edge 0 m b := by
      by_contra hn
      exact hOpp (iff_of_false hPos hn)
    have hMeetRev : A.oneMeetLevel b a = m := by
      rw [A.oneMeetLevel_comm b a]
      exact hMeet
    have hB :=
      DA.oneSplitRemovedBit_iff_chosen_positive
        hAB m b hm hb hmb hPosB
    have hC :=
      DA.oneSplitRemovedBit_iff_chosen_positive
        hAC m b hm hb hmb hPosB
    have hAnchor : B.edge 0 m b ↔ C.edge 0 m b := by
      have hNot : ¬ B.edge 0 m b ↔ ¬ C.edge 0 m b :=
        hB.symm.trans (hbit.trans hC)
      tauto
    exact oneSplit_edges_agree_of_witness
      DB DC hAB hAC m b a hm hb ha
      hmb hma hMeetRev hAnchor

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
