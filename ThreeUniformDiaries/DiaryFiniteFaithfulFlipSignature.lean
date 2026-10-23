import ThreeUniformDiaries.DiaryFiniteE3SplitWitnessRigidity
import ThreeUniformDiaries.DiaryFinitePositiveAnchorCompletion
import ThreeUniformDiaries.DiaryFinitePositiveAnchorEquivalence
import ThreeUniformDiaries.DiaryFiniteUniversalEdgeCode

/-!
# Faithful finite diary flip code: global Devlin sign + one E3 bit per 2-split

For a fixed finite diary A, any genuine flip preserves roles, the
induced leaf ternary graph, and ALL numerical singleton/full pair
meets of genuine leaves.

PR 863 verifies that a single reference marker-one bit determines
ALL E2 columns of any genuine flip; PR 864 verifies that the E3 bit
of ONE fixed S2 witness pair determines the ENTIRE E3 column at
that split. Combined with the E1--E5 permitted edge shapes,
these bits determine the COMPLETE finite ordered hypergraph,
including nonedges.

This is a faithful INJECTIVE code for genuine flip families:
one global marker-one bit (if two leaves exist) plus one selected
S2 witness bit for each 2-split. It is emphatically NOT a free
Boolean cube: source V/E/S axioms impose compatibility constraints,
and some bit combinations need not correspond to ANY diary.

No finite every-target-flip absorber for arbitrary sources is
constructed, and no general lower-bound conclusion is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The identity map of a genuine finite flip is a complete
leaf-only preembedding; mixed-meet preservation is NOT assumed.
This is the direct bounded form of the paper's flip definition. -/
theorem FiniteDiaryFlip.identity_leafPreembedding
    {A B : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n) :
    FiniteLeafPreembedding A B n n id := by
  refine {
    strictMono := ?_
    marker_zero := rfl
    marker_one := rfl
    marker_two := rfl
    image_bound := ?_
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro a b hab
    exact hab
  · intro u hu
    exact hu
  · intro u hu3 hun
    obtain ⟨hLeaf,hOne,hTwo⟩ := F.role_iff u hu3 hun
    exact ⟨hLeaf.symm,hOne.symm,hTwo.symm⟩
  · intro a b c hab hbc hcn ha hb hc
    simpa only [id_eq] using
      (F.leaf_edge_iff a b c hab hbc hcn ha hb hc).symm
  · intro a b ha3 han hb3 hbn ha hb
    simpa only [id_eq] using
      (F.leaf_oneMeet a b han hbn ha hb).symm
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
      ha hb hc hd
    simpa only [id_eq] using
      (F.leaf_twoMeet a b c d hab hcd hbn hdn ha hb hc hd).symm

/-- A COMPLETE constrained flip signature:
* agreement on one genuine ordered leaf-pair marker-one bit;
* at each genuine source 2-split, agreement on the E3 bit of
  one member of an ACTUAL source S2 witness pair.

Then two flips B,C of A are the SAME ordered 3-hypergraph.
The E2 part uses the global sign; the E3 part uses the exact
V2 positive-pair reconstruction; the final induced pass uses
the already verified E1--E5 shape reflection and mixed-meet
completion. Every target edge AND nonedge is determined.

Although the S2 witnesses are existentially displayed here,
they can be chosen ONCE from the source, independently of
both target flips. Thus one bit per genuine 2-split suffices
for an injective finite code, with no surjectivity onto an
unconstrained Boolean cube asserted. -/
theorem finite_two_flips_eq_of_global_marker_and_S2_bits
    {A B C : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n)
    (G : FiniteDiaryFlip A C n)
    (r t : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t)
    (hMarker : B.edge 1 r t ↔ C.edge 1 r t)
    (hS2Bits :
      ∀ s : Nat, IsTwoSplit A s →
        ∃ a b c d : Nat,
          a < b ∧ c < d ∧ b < n ∧ d < n ∧
          IsLeaf A a ∧ IsLeaf A b ∧
          IsLeaf A c ∧ IsLeaf A d ∧
          s < a ∧ s < c ∧
          A.twoMeetLevel a b c d = s ∧
          (B.edge s a b ↔ C.edge s a b)) :
    B = C := by
  have hE2 :=
    finite_two_flips_E2_columns_equal_of_reference_marker
      F G r t hrt htn hr ht hMarker
  have hE3 :
      ∀ s u v : Nat, IsTwoSplit A s →
        u < v → v < n →
        IsLeaf A u → IsLeaf A v → s < u →
        (B.edge s u v ↔ C.edge s u v) := by
    intro s u v hs huv hvn hu hv hsu
    obtain ⟨a,b,c,d,hab,hcd,hbn,hdn,
      ha,hb,hc,hd,hsa,hsc,hMeet,hBit⟩ := hS2Bits s hs
    exact finite_two_flips_E3_column_of_witness_bit
      F G s a b c d hs hab hcd hbn hdn
      ha hb hc hd hsa hsc hMeet hBit
      u v huv hvn hu hv hsu
  let K : FiniteDiaryFlip B C n := F.symm.trans G
  let Q : FiniteLeafPreembedding B C n n id :=
    K.identity_leafPreembedding
  have hOne :
      ∀ s : Nat, IsOneSplit B s →
        ∃ a : Nat, IsLeaf B a ∧ s < a ∧ a < n ∧
          B.edge 0 s a ∧ C.edge 0 s a := by
    intro s hsB
    obtain ⟨a,haB,hsa,han,hPosB⟩ :=
      finite_oneSplit_exists_positive_anchor K.source_diary s hsB
    have hsn : s < n := K.source_diary.prediary.oneSplit_lt s hsB
    have hsA : IsOneSplit A s :=
      ((F.role_iff s hsB.1 hsn).2.1).mpr hsB
    have haA : IsLeaf A a :=
      ((F.role_iff a haB.1 han).1).mpr haB
    have hPosC : C.edge 0 s a :=
      (hE2 s a hsA haA hsa han).mp hPosB
    exact ⟨a,haB,hsa,han,hPosB,hPosC⟩
  have hTwo :
      ∀ s : Nat, IsTwoSplit B s →
        ∃ a b : Nat, a < b ∧ b < n ∧
          IsLeaf B a ∧ IsLeaf B b ∧ s < a ∧
          B.edge s a b ∧ C.edge s a b := by
    intro s hsB
    obtain ⟨a,b,hab,hbn,haB,hbB,hsa,hPosB⟩ :=
      finite_twoSplit_exists_positive_anchor K.source_diary s hsB
    have hsn : s < n := K.source_diary.prediary.twoSplit_lt s hsB
    have hsA : IsTwoSplit A s :=
      ((F.role_iff s hsB.1 hsn).2.2).mpr hsB
    have haA : IsLeaf A a :=
      ((F.role_iff a haB.1 (by omega)).1).mpr haB
    have hbA : IsLeaf A b :=
      ((F.role_iff b hbB.1 hbn).1).mpr hbB
    have hPosC : C.edge s a b :=
      (hE3 s a b hsA hab hbn haA hbA hsa).mp hPosB
    exact ⟨a,b,hab,hbn,haB,hbB,hsa,hPosB,hPosC⟩
  have hInduced :
      ∀ a b c : Nat, a < b → b < c → c < n →
        (C.edge a b c ↔ B.edge a b c) := by
    simpa only [id_eq] using
      (finite_leafPreembedding_induced_of_positive_split_anchors
        K.source_diary K.target_diary Q hOne hTwo)
  apply finiteDiary_graph_ext
  intro a b c
  constructor
  · intro hB
    obtain ⟨hab,hbc,_hc3,hcn⟩ :=
      K.source_diary.prediary.frame.edge_support a b c hB
    exact (hInduced a b c hab hbc hcn).mpr hB
  · intro hC
    obtain ⟨hab,hbc,_hc3,hcn⟩ :=
      K.target_diary.prediary.frame.edge_support a b c hC
    exact (hInduced a b c hab hbc hcn).mp hC

end DiaryLeafPriority
end ThreeUniformDiaries
