import ThreeUniformDiaries.DiaryFiniteGlobalE2ColumnRigidity
import ThreeUniformDiaries.DiaryFinitePositiveTwoSplitAnchor
import ThreeUniformDiaries.DiaryFinitePositiveAnchorEquivalence

/-!
# One genuine S2 witness bit determines the complete E3 two-split column

Given two genuine flips B,C of a common finite source A and a
genuine 2-split s, choose an ordered pair of ordered leaf pairs
P=(a,b), Q=(c,d) witnessing their FULL pair-type meet at s.
In every genuine target flip the E3 bits (s,a,b) and (s,c,d)
are opposite. If B and C agree on just one of these two bits,
they agree on the other. The common positive witness then
reconstructs ALL E3 incidences at s, using numerical full
leaf-pair meets preserved by the flip.

The chosen S2 witness pairs need not be positive in source A
and are fixed from the source, independently of the target
flips. Their orientation is ONE constrained bit per genuine
2-split. No free Boolean cube or arbitrary-source absorber
is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Agreement at just one member of a genuine S2 pair of
two-type witnesses forces agreement of every E3 incidence
at that split between two arbitrary finite source flips. -/
theorem finite_two_flips_E3_column_of_witness_bit
    {A B C : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n)
    (G : FiniteDiaryFlip A C n)
    (s a b c d : Nat)
    (hs : IsTwoSplit A s)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d)
    (hsa : s < a) (hsc : s < c)
    (hMeetA : A.twoMeetLevel a b c d = s)
    (hBit : B.edge s a b ↔ C.edge s a b) :
    ∀ u v : Nat, u < v → v < n →
      IsLeaf A u → IsLeaf A v → s < u →
      (B.edge s u v ↔ C.edge s u v) := by
  have hsn : s < n := F.source_diary.prediary.twoSplit_lt s hs
  have hsB : IsTwoSplit B s :=
    ((F.role_iff s hs.1 hsn).2.2).mp hs
  have hsC : IsTwoSplit C s :=
    ((G.role_iff s hs.1 hsn).2.2).mp hs
  have haB : IsLeaf B a :=
    ((F.role_iff a ha.1 (by omega)).1).mp ha
  have hbB : IsLeaf B b :=
    ((F.role_iff b hb.1 hbn).1).mp hb
  have hcB : IsLeaf B c :=
    ((F.role_iff c hc.1 (by omega)).1).mp hc
  have hdB : IsLeaf B d :=
    ((F.role_iff d hd.1 hdn).1).mp hd
  have haC : IsLeaf C a :=
    ((G.role_iff a ha.1 (by omega)).1).mp ha
  have hbC : IsLeaf C b :=
    ((G.role_iff b hb.1 hbn).1).mp hb
  have hcC : IsLeaf C c :=
    ((G.role_iff c hc.1 (by omega)).1).mp hc
  have hdC : IsLeaf C d :=
    ((G.role_iff d hd.1 hdn).1).mp hd
  have hMeetB : B.twoMeetLevel a b c d = s :=
    (F.leaf_twoMeet a b c d hab hcd hbn hdn ha hb hc hd).symm.trans hMeetA
  have hMeetC : C.twoMeetLevel a b c d = s :=
    (G.leaf_twoMeet a b c d hab hcd hbn hdn ha hb hc hd).symm.trans hMeetA
  have hOppB : ¬ (B.edge s a b ↔ B.edge s c d) :=
    E_twoSplit_pair_aux_distinguishes
      F.target_diary.prediary.permitted_edge
      s a b c d hsB hsa hsc hMeetB
  have hOppC : ¬ (C.edge s a b ↔ C.edge s c d) :=
    E_twoSplit_pair_aux_distinguishes
      G.target_diary.prediary.permitted_edge
      s a b c d hsC hsa hsc hMeetC
  have hOtherBit : B.edge s c d ↔ C.edge s c d := by
    tauto
  intro u v huv hvn hu hv hsu
  have huB : IsLeaf B u :=
    ((F.role_iff u hu.1 (by omega)).1).mp hu
  have hvB : IsLeaf B v :=
    ((F.role_iff v hv.1 hvn).1).mp hv
  have huC : IsLeaf C u :=
    ((G.role_iff u hu.1 (by omega)).1).mp hu
  have hvC : IsLeaf C v :=
    ((G.role_iff v hv.1 hvn).1).mp hv
  by_cases hPositiveP : B.edge s a b
  · have hCPosP : C.edge s a b := hBit.mp hPositiveP
    have hBcolumn :=
      finite_positive_twoSplit_edge_iff_later_twoMeet
        F.target_diary.prediary
        s a b u v hsB hab huv
        haB hbB huB hvB hsa hsu hPositiveP
    have hCcolumn :=
      finite_positive_twoSplit_edge_iff_later_twoMeet
        G.target_diary.prediary
        s a b u v hsC hab huv
        haC hbC huC hvC hsa hsu hCPosP
    have hMeetBC : B.twoMeetLevel a b u v =
        C.twoMeetLevel a b u v :=
      (F.leaf_twoMeet a b u v hab huv hbn hvn
        ha hb hu hv).symm.trans
        (G.leaf_twoMeet a b u v hab huv hbn hvn ha hb hu hv)
    calc
      B.edge s u v ↔ s < B.twoMeetLevel a b u v := hBcolumn
      _ ↔ s < C.twoMeetLevel a b u v := by rw [hMeetBC]
      _ ↔ C.edge s u v := hCcolumn.symm
  · have hPositiveQ : B.edge s c d := by
      by_contra hNegativeQ
      exact hOppB (iff_of_false hPositiveP hNegativeQ)
    have hCPosQ : C.edge s c d := hOtherBit.mp hPositiveQ
    have hBcolumn :=
      finite_positive_twoSplit_edge_iff_later_twoMeet
        F.target_diary.prediary
        s c d u v hsB hcd huv
        hcB hdB huB hvB hsc hsu hPositiveQ
    have hCcolumn :=
      finite_positive_twoSplit_edge_iff_later_twoMeet
        G.target_diary.prediary
        s c d u v hsC hcd huv
        hcC hdC huC hvC hsc hsu hCPosQ
    have hMeetBC : B.twoMeetLevel c d u v =
        C.twoMeetLevel c d u v :=
      (F.leaf_twoMeet c d u v hcd huv hdn hvn
        hc hd hu hv).symm.trans
        (G.leaf_twoMeet c d u v hcd huv hdn hvn hc hd hu hv)
    calc
      B.edge s u v ↔ s < B.twoMeetLevel c d u v := hBcolumn
      _ ↔ s < C.twoMeetLevel c d u v := by rw [hMeetBC]
      _ ↔ C.edge s u v := hCcolumn.symm

end DiaryLeafPriority
end ThreeUniformDiaries
