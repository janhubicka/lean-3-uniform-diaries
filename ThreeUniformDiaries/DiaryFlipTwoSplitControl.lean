import ThreeUniformDiaries.DiaryFlipOneSplitControl

/-!
# Two-split flip bits reconstruct the entire auxiliary branch

For a genuine diary, two ordered leaf pairs have their
auxiliary meet equal to their complete pair-type meet. Hence
an identity diary pre-embedding (a flip) preserves ALL
auxiliary meets of pairs of source leaves, even though it need
not preserve mixed pairs involving split vertices.

The E3 edge at a 2-split is a single branch bit. A positive
ordered leaf pair P has edge (m,P) precisely when its
auxiliary meet with any other pair is strictly later than m.
A pair of witnesses meeting at m has opposite E3 edge bits.
This proves that the original asymmetric removed-edge bit
p^A_B(m) controls the entire E3 edge family.

In particular the proof uses only the actual V2/E/S axioms
and exact leaf pair-type meets, with no artificial labels.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {A B C : Ordered3Graph Nat}

/-- Leaf-pair auxiliary meets of two diaries agree under an
identity diary pre-embedding. This is a valid restriction of
the meet condition, not the false mixed-pair preservation
claim rejected by the earlier audit. -/
theorem flip_leaf_auxMeet_eq
    (DA : RoleDiary A) (DB : RoleDiary B)
    (hAB : DiaryPreembeddingSpec A B id)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d) :
    B.auxMeetLevel a b c d = A.auxMeetLevel a b c d := by
  have haB : IsLeaf B a := hAB.leaf_role a ha
  have hbB : IsLeaf B b := hAB.leaf_role b hb
  have hcB : IsLeaf B c := hAB.leaf_role c hc
  have hdB : IsLeaf B d := hAB.leaf_role d hd
  have hFull : B.twoMeetLevel a b c d =
      A.twoMeetLevel a b c d := by
    simpa only [id_eq] using
      hAB.leaf_two_meet a b c d hab hcd ha hb hc hd
  calc
    B.auxMeetLevel a b c d = B.twoMeetLevel a b c d :=
      DB.roleMeets.leaf_aux_eq_full hab hcd haB hbB hcB hdB
    _ = A.twoMeetLevel a b c d := hFull
    _ = A.auxMeetLevel a b c d :=
      (DA.roleMeets.leaf_aux_eq_full hab hcd ha hb hc hd).symm

/-- If the capped auxiliary meet of two ordered pairs first
separates at m (strictly before both first vertices), their
edge incidences at m must disagree. -/
theorem auxiliary_split_edge_disagreement
    (H : Ordered3Graph Nat)
    (m a b c d : Nat)
    (hma : m < a) (hmc : m < c)
    (hMeet : H.auxMeetLevel a b c d = m) :
    ¬ (H.edge m a b ↔ H.edge m c d) := by
  classical
  intro heq
  have hbase : H.SameAuxTypeBelow m a b c d := by
    simpa only [hMeet] using
      (H.auxMeetLevel_agree a b c d)
  have hnext : H.SameAuxTypeBelow (m+1) a b c d :=
    (H.sameAuxTypeBelow_succ_iff m a b c d).mpr
      ⟨hbase, heq⟩
  have hbound : m+1 ≤ min a c := by omega
  have hlevel : m+1 ≤ H.auxMeetLevel a b c d :=
    Nat.le_findGreatest hbound hnext
  omega

/-- The positive part of the manuscript's flip bit at a
2-split, with the necessary ordered-leaf-pair conditions
made explicit. -/
def TwoSplitRemovedBit
    (A B : Ordered3Graph Nat) (m : Nat) : Prop :=
  ∃ a b, a < b ∧ IsLeaf A a ∧ IsLeaf A b ∧ m < a ∧
    A.edge m a b ∧ ¬ B.edge m a b

/-- The asymmetric 2-split removed-edge bit is detected at
ANY source-positive incident ordered pair. -/
theorem twoSplitRemovedBit_iff_chosen_positive
    (DA : RoleDiary A) (DB : RoleDiary B)
    (hAB : DiaryPreembeddingSpec A B id)
    (m a b : Nat) (hm : IsTwoSplit A m)
    (hab : a < b) (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hma : m < a) (hpositive : A.edge m a b) :
    TwoSplitRemovedBit A B m ↔ ¬ B.edge m a b := by
  classical
  constructor
  · rintro ⟨u, v, huv, hu, hv, hmu, hApos, hBneg⟩
    have hLater : m < A.auxMeetLevel a b u v :=
      (DA.positive_twoSplit_edge_iff_later_aux_meet
        m a b u v hm hab huv ha hb hu hv
        hma hmu hpositive).mp hApos
    have hAuxB : B.auxMeetLevel a b u v =
        A.auxMeetLevel a b u v :=
      DA.flip_leaf_auxMeet_eq DB hAB a b u v
        hab huv ha hb hu hv
    have hLaterB : m < B.auxMeetLevel a b u v := by
      rw [hAuxB]
      exact hLater
    have hEq : B.edge m a b ↔ B.edge m u v :=
      (B.auxMeetLevel_agree a b u v) hLaterB
    exact fun h => hBneg (hEq.mp h)
  · intro h
    exact ⟨a, b, hab, ha, hb, hma, hpositive, h⟩

/-- Equality of the incidence of one split-witness pair
synchronises the E3 bits of all leaf pairs between two
flips of the same source. -/
theorem twoSplit_edges_agree_of_witness
    (DA : RoleDiary A) (DB : RoleDiary B) (DC : RoleDiary C)
    (hAB : DiaryPreembeddingSpec A B id)
    (hAC : DiaryPreembeddingSpec A C id)
    (m a b c d : Nat) (hm : IsTwoSplit A m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d)
    (hma : m < a) (hmc : m < c)
    (hMeet : A.twoMeetLevel a b c d = m)
    (hAnchor : B.edge m a b ↔ C.edge m a b) :
    ∀ u v, u < v → IsLeaf A u → IsLeaf A v → m < u →
      (B.edge m u v ↔ C.edge m u v) := by
  classical
  have hmB : IsTwoSplit B m := hAB.two_split_role m hm
  have hmC : IsTwoSplit C m := hAC.two_split_role m hm
  have haB : IsLeaf B a := hAB.leaf_role a ha
  have hbB : IsLeaf B b := hAB.leaf_role b hb
  have hcB : IsLeaf B c := hAB.leaf_role c hc
  have hdB : IsLeaf B d := hAB.leaf_role d hd
  have haC : IsLeaf C a := hAC.leaf_role a ha
  have hbC : IsLeaf C b := hAC.leaf_role b hb
  have hcC : IsLeaf C c := hAC.leaf_role c hc
  have hdC : IsLeaf C d := hAC.leaf_role d hd
  have hAuxA : A.auxMeetLevel a b c d = m :=
    (DA.roleMeets.leaf_aux_eq_full
      hab hcd ha hb hc hd).trans hMeet
  have hAuxB : B.auxMeetLevel a b c d = m :=
    (DA.flip_leaf_auxMeet_eq DB hAB
      a b c d hab hcd ha hb hc hd).trans hAuxA
  have hAuxC : C.auxMeetLevel a b c d = m :=
    (DA.flip_leaf_auxMeet_eq DC hAC
      a b c d hab hcd ha hb hc hd).trans hAuxA
  have hOppB : ¬ (B.edge m a b ↔ B.edge m c d) :=
    auxiliary_split_edge_disagreement B
      m a b c d hma hmc hAuxB
  have hOppC : ¬ (C.edge m a b ↔ C.edge m c d) :=
    auxiliary_split_edge_disagreement C
      m a b c d hma hmc hAuxC
  have hOther : B.edge m c d ↔ C.edge m c d := by
    tauto
  intro u v huv hu hv hmu
  have huB : IsLeaf B u := hAB.leaf_role u hu
  have hvB : IsLeaf B v := hAB.leaf_role v hv
  have huC : IsLeaf C u := hAC.leaf_role u hu
  have hvC : IsLeaf C v := hAC.leaf_role v hv
  by_cases hBpos : B.edge m a b
  · have hCpos : C.edge m a b := hAnchor.mp hBpos
    have hABAux := DA.flip_leaf_auxMeet_eq DB hAB
      a b u v hab huv ha hb hu hv
    have hACAux := DA.flip_leaf_auxMeet_eq DC hAC
      a b u v hab huv ha hb hu hv
    have hBoth : B.auxMeetLevel a b u v =
        C.auxMeetLevel a b u v :=
      hABAux.trans hACAux.symm
    calc
      B.edge m u v ↔ m < B.auxMeetLevel a b u v :=
        DB.positive_twoSplit_edge_iff_later_aux_meet
          m a b u v hmB hab huv haB hbB huB hvB
          hma hmu hBpos
      _ ↔ m < C.auxMeetLevel a b u v := by rw [hBoth]
      _ ↔ C.edge m u v :=
        (DC.positive_twoSplit_edge_iff_later_aux_meet
          m a b u v hmC hab huv haC hbC huC hvC
          hma hmu hCpos).symm
  · have hBposD : B.edge m c d := by
      by_contra hn
      exact hOppB (iff_of_false hBpos hn)
    have hCposD : C.edge m c d := hOther.mp hBposD
    have hABAux := DA.flip_leaf_auxMeet_eq DB hAB
      c d u v hcd huv hc hd hu hv
    have hACAux := DA.flip_leaf_auxMeet_eq DC hAC
      c d u v hcd huv hc hd hu hv
    have hBoth : B.auxMeetLevel c d u v =
        C.auxMeetLevel c d u v :=
      hABAux.trans hACAux.symm
    calc
      B.edge m u v ↔ m < B.auxMeetLevel c d u v :=
        DB.positive_twoSplit_edge_iff_later_aux_meet
          m c d u v hmB hcd huv hcB hdB huB hvB
          hmc hmu hBposD
      _ ↔ m < C.auxMeetLevel c d u v := by rw [hBoth]
      _ ↔ C.edge m u v :=
        (DC.positive_twoSplit_edge_iff_later_aux_meet
          m c d u v hmC hcd huv hcC hdC huC hvC
          hmc hmu hCposD).symm

/-- Complete 2-split local reconstruction: equality of the
manuscript's asymmetric source-positive deleted-E3 bits
forces agreement of every E3 edge incident with that split. -/
theorem twoSplit_edges_agree_of_same_removed_bit
    (DA : RoleDiary A) (DB : RoleDiary B) (DC : RoleDiary C)
    (hAB : DiaryPreembeddingSpec A B id)
    (hAC : DiaryPreembeddingSpec A C id)
    (m : Nat) (hm : IsTwoSplit A m)
    (hbit : TwoSplitRemovedBit A B m ↔
      TwoSplitRemovedBit A C m) :
    ∀ u v, u < v → IsLeaf A u → IsLeaf A v → m < u →
      (B.edge m u v ↔ C.edge m u v) := by
  classical
  obtain ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd,
    hma, hmc, hMeet⟩ := DA.two_split_witness m hm
  have hAuxA : A.auxMeetLevel a b c d = m :=
    (DA.roleMeets.leaf_aux_eq_full
      hab hcd ha hb hc hd).trans hMeet
  have hOppA : ¬ (A.edge m a b ↔ A.edge m c d) :=
    auxiliary_split_edge_disagreement A
      m a b c d hma hmc hAuxA
  by_cases hPos : A.edge m a b
  · have hB := DA.twoSplitRemovedBit_iff_chosen_positive
      DB hAB m a b hm hab ha hb hma hPos
    have hC := DA.twoSplitRemovedBit_iff_chosen_positive
      DC hAC m a b hm hab ha hb hma hPos
    have hAnchor : B.edge m a b ↔ C.edge m a b := by
      have hNot : ¬ B.edge m a b ↔ ¬ C.edge m a b :=
        hB.symm.trans (hbit.trans hC)
      tauto
    exact twoSplit_edges_agree_of_witness
      DA DB DC hAB hAC m a b c d hm hab hcd
      ha hb hc hd hma hmc hMeet hAnchor
  · have hPosD : A.edge m c d := by
      by_contra hn
      exact hOppA (iff_of_false hPos hn)
    have hMeetRev : A.twoMeetLevel c d a b = m := by
      calc
        A.twoMeetLevel c d a b =
            A.auxMeetLevel c d a b :=
          (DA.roleMeets.leaf_aux_eq_full
            hcd hab hc hd ha hb).symm
        _ = A.auxMeetLevel a b c d :=
          A.auxMeetLevel_comm c d a b
        _ = A.twoMeetLevel a b c d :=
          DA.roleMeets.leaf_aux_eq_full
            hab hcd ha hb hc hd
        _ = m := hMeet
    have hB := DA.twoSplitRemovedBit_iff_chosen_positive
      DB hAB m c d hm hcd hc hd hmc hPosD
    have hC := DA.twoSplitRemovedBit_iff_chosen_positive
      DC hAC m c d hm hcd hc hd hmc hPosD
    have hAnchor : B.edge m c d ↔ C.edge m c d := by
      have hNot : ¬ B.edge m c d ↔ ¬ C.edge m c d :=
        hB.symm.trans (hbit.trans hC)
      tauto
    exact twoSplit_edges_agree_of_witness
      DA DB DC hAB hAC m c d a b hm hcd hab
      hc hd ha hb hmc hma hMeetRev hAnchor

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
