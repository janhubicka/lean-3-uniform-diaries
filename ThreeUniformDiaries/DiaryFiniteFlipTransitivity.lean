import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# Finite diary flips form a genuine equivalence relation

Unlike strong FiniteMeetEmbedding, a flip preserves only
marker-defined roles, the induced leaf hypergraph, and singleton
and full ordered-pair leaf meets; mixed split-containing meets
may change. This is exactly the diary-preembedding flip notion.

Reflexivity and symmetry are already checked. Transitivity is
proved directly using the intermediate diary's leaf roles and
the literal numerical leaf meet equalities.

This supplies the correct API for composing flips when
pulling arbitrary target flips back to source flip words.
It does not imply every-target-flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A B C : Ordered3Graph Nat} {n : Nat}

/-- Composition of two genuine bounded finite diary flips is
again a genuine finite diary flip. All intermediate leaves
remain actual leaves by role equivalence. -/
theorem FiniteDiaryFlip.trans
    (F : FiniteDiaryFlip A B n)
    (K : FiniteDiaryFlip B C n) :
    FiniteDiaryFlip A C n := by
  refine {
    source_diary := F.source_diary
    target_diary := K.target_diary
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu3 hun
    obtain ⟨hL,hO,hT⟩ := F.role_iff u hu3 hun
    obtain ⟨gL,gO,gT⟩ := K.role_iff u hu3 hun
    exact ⟨hL.trans gL,hO.trans gO,hT.trans gT⟩
  · intro a b c hab hbc hcn ha hb hc
    have han : a < n := by omega
    have hbn : b < n := by omega
    have hBA : IsLeaf B a :=
      ((F.role_iff a ha.1 han).1).mp ha
    have hBB : IsLeaf B b :=
      ((F.role_iff b hb.1 hbn).1).mp hb
    have hBC : IsLeaf B c :=
      ((F.role_iff c hc.1 hcn).1).mp hc
    exact (F.leaf_edge_iff a b c hab hbc hcn ha hb hc).trans
      (K.leaf_edge_iff a b c hab hbc hcn hBA hBB hBC)
  · intro a b han hbn ha hb
    have hBA : IsLeaf B a :=
      ((F.role_iff a ha.1 han).1).mp ha
    have hBB : IsLeaf B b :=
      ((F.role_iff b hb.1 hbn).1).mp hb
    exact (F.leaf_oneMeet a b han hbn ha hb).trans
      (K.leaf_oneMeet a b han hbn hBA hBB)
  · intro a b c d hab hcd hbn hdn ha hb hc hd
    have han : a < n := by omega
    have hcn : c < n := by omega
    have hBA : IsLeaf B a :=
      ((F.role_iff a ha.1 han).1).mp ha
    have hBB : IsLeaf B b :=
      ((F.role_iff b hb.1 hbn).1).mp hb
    have hBC : IsLeaf B c :=
      ((F.role_iff c hc.1 hcn).1).mp hc
    have hBD : IsLeaf B d :=
      ((F.role_iff d hd.1 hdn).1).mp hd
    exact (F.leaf_twoMeet a b c d hab hcd hbn hdn ha hb hc hd).trans
      (K.leaf_twoMeet a b c d hab hcd hbn hdn
        hBA hBB hBC hBD)

end DiaryLeafPriority
end ThreeUniformDiaries
